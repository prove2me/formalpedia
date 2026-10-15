-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:19:39.717983+00:00
-- url     : https://prove2.me/submissions/be37e1b6-79c0-4a8d-9128-826ac7b7f1f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 721762589 ≤ n < 721942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 721763839 1250 721762589 721762603
    0x908010608030f030c0d0504050102070308061819090203100501082e15080d030609200d0902040b030f0d020c2706030c0d030c15020c0d03090312050408031009020309 73
    0x1030f4801e480400010f40103803218055a00d0544850000d210720714283c40d10078000e6000e100d04402040309140411035a00b00000921000540140070290316100c60ba0844601004000e000c01100d454035035440045e1814002c000f041621803070049410b5040c0a80d16041a41d0040e88040c0204194040311005204480000045c42d0040f0001a08003020010264500450b04120b16510486490800003a0b2690140e01103400002e0708028801088000c800568520b104500c58600d06010411081c1001d41c4008a403606c001c1000480000050101c1e044c810b001c40e50311403603086000c0c10b00c120307601440440d07038034901190700602e443d05403140c20816103215801c924201880030000b690b00d88041001040d103040003000449202018a0000c10840740a5800c481410030f0441248466000d8003d55280303c4c60700001c1c00ba42000008218002c09440740f06408100c043d00350b05035003040d14481e040c003417400390140559074076040b800c13018448940d80c041d144c6640b04004000b21003001040320 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 721765089 1250 721763839 721763857
    0x10e0604020913020309010603120c030801050405060a05040f1409060f0705130303211a03070f0f03260a0309061d0705060d150603060f0f0f0b03040f0b0106050901090801060803 78
    0x45c3c03280c80e000f080754010704107038000a00c2c40400d200d080703c006403c802d07000c030706612998901199a80b0307a0305010544005a170095005600c0d10010303c2503252941000d240e940c108140012a0000d848800009500545900310180c10010030703c16110540d90307525900000078200640341025042d501035500300184000723420040900314006407049414820034189920000074003030348103000911900440b0351140710348240b24600700082c07400702da841700708d0803a450194058800e0385140c44200e001a4190b50051304118ac05c0511241d1008003006042452542d580000300d00c0c800b4601501114900c0c40c03058420840e841140d191102c0014600080d03840981d0302c0703600d6807030301d4040030003404107110b001c0007464a102c0041034a60740340d40f11008407070b99000d485403074039501d01d14680c480c089405050034200590100344184200070000b03580052140d403000300c032000d0303940b079206c02c0f02000c0e00a64001440082c4508481d070b07101c10800090200f90703000b04220351500045644e0ba108200304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 721766339 1250 721765089 721765091
    0x10212090108061507060c031512021807021002040b090103111c0b12010e1b1e0411090402070c170d0c1707020a180c08130f1514010e0604020913 64
    0x601500c81d400702c425180c4142e44246c0c103015603900020054003420b00c1e901d0f41d40d143c085500d0002401120419860f0380f49801410900b69021100308426003440001c0c1a1000e510586003465860902803004000030a244c5691a86900c0d1072000102668084490400504418040c0d510301480032110052410100030300080e0340503014004c220504445086090b8070b52910380d1042c00c070400420ba01e030051846140008003520540101300801d400000a9001d007407135903000c0000e03800c0c80d03880319800c26480c0e103100d03041ca1407400c0020b0a91784041e00444030915480030400c6509a032114100b11050200094000380303042c903100074042c01c80d000c80540b94130986004910000301b00c80848a10399005004d400c02d0a0725142c1302c0d610000c040340a94103603481c1581101503107101d00001800707001c2002d8040030544090700c4400e00e43c100e03020103585d0442a08900c401e0400280315042c4400b18483d0304004541c0340c86904108158014040d600540c010404610503a0b10030003840d080f0010548 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 721767589 1250 721766339 721766359
    0x705100b0d0515040312091401180f11010215091c0f12091a0709060e27090f030d09060e0c28030204094e1701060e01021209010806 58
    0x804544d090362a18008003264600501c003000d2000c4288d10509112506009020030701d2001300c1078422100d0b43c80098401c0c80804980130028a0a24140d07000850500c119111103c0007070703085c3c600309016520181700d6480040480584042c400e50f1a106820b2030a028818000e849006800f881403101d10311403c039640c10f8500304018071400342c21544111550b944e0a10301c0c1244014200f003055001d0300022880401d40f282c0c452030041258503200840e04d03604001c0d0b141840034079001010203001c090241c0119840d000200d2010400b034901d805a2107000325110456080c640c08075401341601c041c0381d0f00004e0041c1a191150341c5840c900d851400b004001200c0c01c2090903480000c580c00095009060400d1807041c0080c0c8000300410500300001c1001100390302d51091003c00403c0040f46c6500c4204102c5000e0600a000c0d801290740131f410310710040303003682d00080034008003600700c6000b040c801c41d4464100c0d43d04214502c034901d02c5a80c80c5107090ac50000180064000030412071061107002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 721768839 1250 721767589 721767593
    0x7021f020c030d09050d180305030703030b06121f0801060308181311031e09150c0c0703080a02070b0f0f070309030506180607090b09060706110705100b0d051504 71
    0x220303625880f2481c01085580c64030314215483e24625000c150025000d4806003002c486240c1c1900b044950140c003c520700ba26580d400e901801a2406066010a06000f4180b020442941c924800c00c0c3c0ca0b0160703017521225100a0b0480101034220b1500b03a03142810502c00195103404545040200c5503508060815010029440f202d603142d00038800b5003008181c081e4a1000340255024070030408041c442c4210622850b01040d00803580e0107000c0d44028110303a509203095000c241c0058651803100c0c134000101501c1442c0281030382c0119210a23000500380c001c0c90b818040030000d8040d440aa03031402082440750740e040d01440c000c0312414500040c016003094088c100e12401580e000059601c2c6180182032040d0a81c108807101030140202c00000302420320441202d4180c0303401e00000d5081c00114400d000c415045090106d820564440510600f032808101400165110780007c205541d1044501c0095600340d0341c00600460000c0c24030f00c0001c5000c1124001c25075110100507143d6240c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 721770089 1250 721768839 721768843
    0xe09040b1005031c1d0d03080c040f031103010e0a21090e01081608161a0f120405010e010510060807140c0c040b1509090709030b0c09010807021f020c 66
    0x140c0c401c6034144604016081c00b003039002c405048400b295180d0b60381c030f004600345c0e284c011040c00c8481903102c09030401e03010019018440f1260000a125115030805869510481d119022600309480c1030744070900c1141c1914090080c0c01801041a01070286400582d94a400706040420750804030755400c6140a0f185104000080c024141420740c83d000e965034404141c1c43e242c60340c041100041040c0c002142c04840001c003403080c6d82c040154007901c503140a044e0729400c40c041d4001c00816008010751440380414401a1411140c4644080000e0030a031528608603460140d048450341d040004114170100c5491940084801908119211f6a6007800840b400201c1301c2890801a10108103070405840000da588000102a00c0c10000c4000890400ca10301c20404034502070040100004005810280ca00a410407114140400c0842d1a03030b90780001c505007181c01440c0c0c180c000c0b843c1040c0390b80c07109160b074201c0054009020318031074485010540a0740000a42c01c00c9800090f03c004030141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 721771339 1250 721770089 721770121
    0x418110403060605180103080306120309030102070b1815060f130501030516081b0d150f02031009020c0c011b0b0903120912070f03031107140d0e09040b 67
    0x20180486588a489180c0303080204160302503a030040d0210342c48008600980403000d4103903078024484a0a6550b01d5013007000c00b84201160348401e01092041d11a03586003400600155441038001260b9840c00382080401e0511480c006107203030b40150700c009000c440b50500140c200006452010403c05d03a01c0218010f070411607519200286000b000009009021914140340104c0f9a035905e449542c3c0c901a40c0c0e00c2c50288200c0ba007034201080c44d40300340d2810f00b04001001d4410061442c50440003070340b9200302c804241c40800c100d074001041008074440d04000c000071309103444046060031000c03e0401c0c0d0300c55282080c0c03414005a86111884504040780e481c0e0301c168481004022031902a890a07140d401403080d80d00c800c0c0d4400b010030b0060320701207950810007a500d80500e040c05000c0d141e00b007946220801c01d82c1416911004920342107203000c0203044042c0500707424034007442c2c802d10040c07402410080000c2005401d0024110950340d0304003003600b207508a031013590030382c492880c1d030300c04000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 721772589 1250 721771339 721771361
    0xb0402120a0309030308060d031b0203150a0501060318050607120621021e10080411040c032f09090c0d140f09030708071b0b0d020717040b0418 63
    0x1240150410400d50f00c600c0480a4a2081c1e5400d00c45403148024072081d0101c071040100826021404c4458030181c500c07884210074001421240440020a100742c80184282d510101c81c0ea01c0d440180f103140e030103020304807070b10a45012481c0624a50b03107802d80c1390b1801401c901c00b0445000400d010602c13094000314007900450310100034000a07000c10704005c600100c0704070f0051403118000c41c05003608801d12015050007900703185690300c04483c21260600010f02c02c0301c055005450840c2e45454501c41e1056411058070001036103004102404c50181c0f1006d401c8001d403155843d10500c0070380320f20503a8001c0e601600c584229454640c0d0100090007055800801c813884c281400c805000e0020382e540c019412000d60340d4503038031039511080d241d1041c14401b17070280e4001c000c0040003c280102124002484580046403940c96440c611090382c0f020b0186038070389402107444d02c24840700540d11802c200301000b61918152808044000cbca00440c410301c40c02013000d0070241141c401e140c000503c0c040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 721773839 1250 721772589 721772593
    0x6032103090708030c0109170301081213120f032003340615150c2306010305010509012d0207020102030d0f050a05010e060d02041503080d0203090d0207030309030b040212 75
    0x5c03942441c0c0c02d00804d080e9000b035a0f121251074207402d41d2440d0608603410f90f0a40c0000e03148101e42040404010b138081841d4040c2034901040002c1c04000d03280750307190401c2c4210900348040a2609004003040e0000301e203800440c4030100d120b290010000222107441e0803800480d84140c890031018800a642c4200300400107400f0b100d00001c2160700d0380403101e0347c41c0e015442d010154990504d194000e030b240345044046100e1800f80000702d0b28241da495135914862100000084041d150117003407000a91045509039103c10500040031020b0150740c8090a00d1030f800b1080450041f1140c51003201001080001d6900091800a6920038000c480aa040c68107082c0800300e03408000f80002d1801b1100c64020902c0d0400118005d814100ea460060000801040801c0099000c100081c40b55050380b81081d12410030020020345401d001e0000c28814450041e120b02c3c0400d44a41030a41010302c0b803085400444080c40040d800115001c02c0c0c90300100d6030b610316a074600c0400e06c80313070003861040301d54 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 721775089 1250 721773839 721773847
    0x8070810031a041b080c13060902070b090c04110d02030403110a0809011211030f09030c01150e010609050105030103112707020c040204081e0a0602030709030b0603210309070803 78
    0x600700307980342d0034011441500300f211a0010b02d00c013052034000c036006040d00d54020307110703d070801d29001d00286d1210f400c04100096260352101d1000807a48010011150010500204030b00c2c03281c180300003501404156020302c21381a180811280c42d10031403c0d900394869002c8086010b0602c100d2100144000e004105c40c506001c50408001e075030007070342e21903000074210915241840164010030341080d0000c00e0139411a111100c6c1018140001425041507110030b10030015440024010128140c401c42800090359007482c40c04140b4020507040310040c0714100200304102e0364810100ca0450b84c1120580c2ca50101c0701700006e00312101d10f40b0304d815102c04a000c0036807c10102110340d018280c16000c48440c40582c0c0705000580c00b8078810030071141c2100403001031602e4000d510034026103000054a40b20b2031180da980742241c005860700e00000f000e1550500030040401c203480c0d040481240103015141241da01d58500399004074040c401941c02201080010b0810070a400c003500c02c0c3c00c03d40c2e4507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 721776339 1250 721775089 721775123
    0x40c0e012d170106030612061805160512030c0a03080a090c0b03071d030d11100e06011701090506160c0f060e0d030902030304030b0c12070e010807030209010807081003 74
    0x8400700895140d030082e0039000010b000d4003c0c4640e4045541c00380f072104090741c5c95102e40000b400102180882d51a074034800d0000540148801c4000701c000480d102e004a04290a00c0b5030b00f10107000e1003032140d000700b00380500d80f43d0005000500da64117140c9102e00b41c0c0c60380c0f0b070030014041c411401020228000c0d070114149850b0405144034407601d5a6010840c00581c19030340c0100b04002d03242e41c050304582500740e03945100b0f043c010a142541e504490b100641020030b0004c0f9131003074442070780e40d402420040c4000421303281d030788000c8035101c0f00a000b10b40d195100c01341c0360071001d0700300d40040301c1e6440e1840b1140c0c0610000000035402c010850562002e0f41460000340400601840543c092030b0544000140a4404c0c4004d80d0380145c004e504240c2195500315070381d40041c091824000083c03149600d10781c0744c5070880780300d0f00301039891b404900c108100260113840003030066070901d40140007440051740c1c800707491175212149191030201501c2d080c1022104150030340002c0c000108041e040704d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 721777589 1250 721776339 721776347
    0x4050d080d110918041203020f09120c1206010b160f140604030305070c0b0c0c0a12030c0e0603011404110f0406020a0506090a05100b04020d020c100b040c0e012d 71
    0x1041d80001d50769900e9180a100e404d12208808503002401180e02201c503035249442507000c0c3c5240700c07152440ca883c05241e44000744a1030705450800c1125840841d030720115081892051320051400001002d055040111001c824003030269180c0c5440c0401051000f44818400c0940003150006180c900c0000040003140e00c0c2e0104540c1900401d04000c0481c8101d441940382422483c0c200700d0348035680d114441c08421603030207070f0301c0c02c22240316842c41d80000c07400007902112580134540b8000b48001c4000c42c0a4400d903005c1e00f86034490700f800e000401240c418081451887c040c122000600c001411504000380d0003102d90324080c1d01c0011401041d555000207200c0902c6000304220b0320240e5420f1100c941d2054401c000500380d8201e543d0b035280300c41742c03600008282c0303000410142c242584600c00c0720480c3c020901812103688015005110b0314201c0c4210b100004050b9000d0241c00c0c003150700074100080da5007006040001001540703201e40400756880b003026404407080fa4696822000c014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 721778839 1250 721777589 721777597
    0x9050907081608090a0206030405070b0c0a030e010e0d0f062d0f020a170702030403082115030607120b310603020d0f1b082a0604050d080d11 62
    0x3155040b040280c50700c0c203000f400c480384500c0d003003401403800070050303401c0c002c03141c001130800c03a103521500c200403510629101c050021455400010050303003605040c0141290441100d5a0600c804500a07011688421018a0000da005840340041c0005807500384c0c000c0954002140f082c8901e845044201e012426200c100420b821606011350030030180303100e049110300c440200215a110032600d942503000040e666201400d0f0041d41e0070641d4a0702c2d01c4500d6440030840442d0345040042801907030158000e0642c110240441c045821030100300071a41e40c001c00f800810074000401d2284a11041e95000401c0c0c000018100841c1050a0402020645011030380c0c5020b006110711092102c0140348039584c03c6a40050501513030312403c1d101c1d02280320780d1400c25140100c81c6410703070302e403000b00400c6d01d07006019000041c602d01850040983c404800d904413001c48030100068907841d0f81c1c1c2ea00607a015182d0451b038051004c0c41d50301e4080e8051041a03407205a06051804003a00304901e41c01070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 721780089 1250 721778839 721778851
    0x406030e0105060603041209091505090f070c0605100f0b09101d0906040b1c020a080f120c15070801060816050307030b04020409110408071a040b07030905090708 71
    0x180a56800c4003155801d0700c404841d0180c11000520018012503130b14050b5015145080c200038003010744030111201910318030b502000402e90400c0b41006182002100c9683c003d51120240c12b5605080c02c000300400341d140c130081d142c00d48602c00300352002640c0c480000204064201d00010585e1141c203610203030070008009200b258103070429481075004000c2d076604203d24027020414283c0c80c1e020060f0681d405800560001c0d56098100305548554024401800e007404000010703900c140b040002401d00c40d04100b45a80140d40080080e460001d209001c1092014026882c0e0884802161400c001c02c0e203c0d01d4101415801c2c4483c43e5000103030781e4166011642e40710856034030070140e840090244060300c00007030010400103224500c650300c0090001c00080c800752509075a08001c03000c1e0344290b41d0755010240300082c200280c130300c104000f800400c2c0d14044411032088540c0c10807558004d6109643c549000041c004007058410304416000d010014041d505504002000038a0b540049542d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 721781339 1250 721780089 721780091
    0x10150f090e011a010f08130b091c02121611150a03060b0405090c0304020406171f0903080c0d020f04060302090118050a0501031e020d05040c0f24180308040603 70
    0x10004500c3c66412000160b801a15070344440c10740010215414070000b4116000c4e80114020040012078100c0f0341c5010300e0f5000010595503035032144140c0c03065210401e500039580104a000001100841641c41c207180045034a01210151706140400d82e00d24a4000c1d0300c6040c0c00c403080316000801d0003a1214983c283d6040080e030342c0300d075601c0381503120700e00441d81d00606050015450b005030100031948288040c0c0301181031503564039807220310407003c00140d58079080052020080c00103d0754050040d020313503030305102c0d282c1552005424104040d100200e120000101c20080400d10b80440340080100c80b565070751550b44038070090082d00f00c0a080c0c2d00054180c1c0440c46108219100a815a00000c2c104103555241c00d006600074841c0d40c0d80200907040070090030002e1407042c4050b01003010542004a05450146401d08880d109900660610065407009000d2a0054000c1c031505038241c2008a0150300d946205494020f240c84a6844030300c100351012081041403000fa004540542d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 721782589 1250 721781339 721781351
    0x30c0108070e1e102d1d03211c05060a050d0f05071d01060f120c03090f08071a0702060c030c07020409030e040e07080c1306120605060a05011110150f090e01 69
    0x50340340300c0c891548148000644100c1400b04806650b038008900c0d000c003d0460301110345008d0111001e1414802c1000034030400b0030303240d055000324200b00c1000c94002c0c0c0100030500c0c01e0fa00040a460b00382c090103002d07203901c010607001c024205041c0341d0f14542000481e000c03142d0300c041841c5804150848a035424803c64000500980140c05e034101042090311800324001c221680b05000740100d0305200100740c3c44694001c0810380300c1d54101c0342280109030203503a130006030415101030a80a10b02e9610600c1a40800c8000d036400304d140758002c20464034281e920386074a8040c00c135a003d0008060350091808a40004041d00640c9207a10030409984c144005403040c2c0f140c0e525403119114108440c0c110080e070300303818600203803601c240c408001c400103011900c035040b031646596a00d5080b03c41c165103000744000b81c0f400000040040c002440e01e8041700c401501081c1d02d40810840c3c0e052125100d4003d2078000f8079101d4414007030500c031109480c103241e585040070701504061584603ca546041d0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 721783839 1250 721782589 721782647
    0xe01140d030e240d1401150503040b04020a15050702040c1e0503090313170c04020f0403030804051f0f0b0307050105030105120106090203100302030c0108070e1e10 72
    0x3a210241198054a03481502c218141c248460600c0c0c1c0d4008a00846200f160401c002048030003030168000018000a04010300010b20980301c50180c00c81c840902e641c040304c9034216400380c03c0303c0d4429448034840d00161540d2000c5001040b86400c5481801030410f2440d46440e801405030045034002c48041c400340008150545140c1c03e80c40605c0041100d02c0114142140514011a044a0801d04881c075005010207401c0d88409540c12000b2814403404071658103a50800820300e010904540c11460602c0032034125203180715500c001418008064002020320000740014600da00d60311500307545005001c5229001400d04180107604c80d45001c4103916035040018202e015280d045e110103203541d0030322080220000012260031100d40d2501804a030001c185e001335030186500d030b80700d10556400c510406060144400c1344604208400c0200400c00b94048040c00d9080c40c1501c0c07006000f0044400340040885240c8110340101c2d0030364211120542c865582c544841034607145245030130050b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 721785089 1250 721783839 721783849
    0x703060212070e0d02130c3e060708060405060103020d050403051e090a030209061f02070e01060f0807030c0e0306011202091e0a0f06031208070f0507050a06050402031203010e0114 79
    0x1028019400003c0d03a107011081d1403040d4840716951085d402d11231940c81041103801c00444d002401c82c0d4000d5118106e2003010500c1c0703140740314550301d040060901031805880051000703070000c1c5054403907501c80b404100241d01070f0f0b040b03a40080d02c280c0c0902180c0360a050203805035000e90f40500b036100d181c14040b21040542000d40d480d04500510b4041034a03c0d513002c001d6801c0b8041c240e20760001045100b4040c0401c0e02e10641c100c0351440e0041c203401854401c46010a080503880041407040803c03007804100ea000d00f4460b0f00c2002c500b0700040c5400c900c04111007000030b10815039014454580080b4040c0e20455001740c2091088a401016a880c030405424554000e00c540c4842c03d001804600000504d8001901181078284d0000300d0036625200c40101182040b24100820303d18020301503026030000d00c50903e42524180b40740b030498241d0318542d8484038010094102c41e903810121f001c540d81402003100015800d40443d4907541c6810318124208000e101d5030480d0344e061040a0214148 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 721786339 1250 721785089 721785109
    0x504032909150606070219061e0801050d0b0403021609020d0c020c030a0305220e0406060f0503030d020708090a32090606130e0709090e060412110703060212070e 71
    0x110b205030b440070b901d40d50f00b8003506820450701268440b282d08416228640c111420341e0041c03800740d07a126507251400d444022043c2c0101272072420003159000601840e1030340350446407020317845484460b80d43c0c0e0b5414124100601141202180c0141d0b00c400256003519030041e0200c0c0401440030080c01c2140d15090381d44462468a5581640101c2407607400f285c040c50143c1440300000100d00310b220200540c1500140194200e10710303050440c8184400c1c064240f049901501007425007580041c241000242c0d01e01804080088081c0c0000d6017034204280d6905907004200080d22aa41035034591000ca43e0b8007240c0302039469034244681640e00d0b0b15000321826105054041c00800b01c5807500e0040c4941e42c1d1002100040b160003c0c000000d42101032601140302e21520342d0380301081801c021900f002e4640340350710704903183e1003581030102203a902480c5100251007411f10030500d0804411090800b07d1662000e04114404900803080c6800340c100d81c0e104081c250b444840446505c800c106c0641c070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 721787589 1250 721786339 721786363
    0xf0222080102131e080102040e1e1005060d02070c0303020d0809010624020a02130617070803030606090d1e060b1e060306030c0d05101d0a120504032909 67
    0xc0400c2d04004036401070444011440d03514200e013074015100d84281d0b003668003680c0035881c281043d10820400840007400d000304134051010711180e42c200b2142e01a02052a8050700344140c100007640449966150304490600c0e60040f00d419006580303041c065100c0b03101040b608003260500307002403007800d410310500064a0045a0086040070103c00c500d44c0d000b041075003841075214103043c0d100560342e00c0503100701c01400044080b840302c3c00c2644405130710700d13a1211007503aa400181c00b0701550001000352030b4000c5090b59115140c40500340092035007548400068030740f15455100501c0c5c07500d1007084034140c0307005075410b0102c03058113018030006060600c6440b0000c0701001d0800781078613011004540103000142140c01101070036000806941c900001150b096204002001c000380b540e0041c0b4281c444401c0c200c041b00d0350000099600e030000000002c26185140d004c0700800c40c041d0041c0c1e8043c54222243e5a0441d50840038241c404c00521070085000341c031200040c080c1003000400e102000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 721788839 1250 721787589 721787617
    0x150306061f0f03021b010c0e010905030a02040f1d100507080402010804020d260d0f0b0d06021608070609050f07050d17040305152a03040210030f0222080102 69
    0x3000c40707407084952a0b0820410010150200245c000642c0302030144204910b0b00400007600b049105000b42245100c0482c00341481003e41040005603400300c0c05102031070301542c022a00d6404e030302c20300008000c1ca2122140303c240c5003807114000d110014403c1140c60b01440200160f4480e82010341d948902120000d0000384408002001803c1032030381c40b88000d10a460703c2c101c2c0c038444403240408100e06880031440f4a00403a56901e0f1034828019284c0103440418108200002440490000c942d0400d0292601c0c2c0c0018000f100800e1850080b08442e42005901c0d444030524985407014080d1044155400d126110120b11451004980c46048610080c02e09200c14495076500c0d000e21a0f4090607007101c0070038032002001c240c052004d0008442c8022800c2c3c518a080c1e0851500421400702c402440b1440102105403043d414084981040e0100c440f404400c80c101c40440140070706003640c050483c00403440ca41c1d007465126800c020845406403001c005a01c0d503a00341d00702c1c012083d0701602c01c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 721790089 1250 721788839 721788889
    0xc050d080a09090b1e040608250f0e1303050c16090f05190b15040603021c0902010207030b1909060e0d080f0604050402012003031b090a1a0403050615030606 69
    0x400c0100c03502c5100504044c1010424a230744c1c42c0c05c1801c010059519003038446000381c0401c00100d20400314000f80021034028410799040c41c00c0200706500003031040c0904120460300c40240740c001c01c15280311040f100200c0340c40c01200f90b140e03514202140310310403d1a04000ca180c196041501820748078140c07030140490402d44400100f4003401c03445e21440d030802401d000680304a003401004101501680c0c130003699a4140780003842180a00c4a00049028a850108001030780c1c08909030b4102da40225015500f911001c01c0305132030707140b1240d40f6400c3d03074034145000c420003059410a0191030800000e0b1032480144601c1901c0c0040304441c045468400038002601600d400d034440d40c0c1060045c13400c20703810b03609000344c00c171498686200008640d20200400c00200d00003020b90024108801c6c05504040081e0302040808825025800d8050800340c03c41e0002d004000c203650003140c0141c103c1d00c2c6400c221100001d100f0b013007810301e070080c010031740000d5a90801d90140985e840350400519a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 721791339 1250 721790089 721790119
    0x2030910020f0d050f151906030c200706081003030e061809130507050604060c230a030507050628230403110d0305150d0c050d080a09090b 61
    0x2e6100208100100340103104462a600d0f00c0d20a0f107109004c003460042c00381c144481c83c070026582c0c8101040c4030b1450b800081200d01001418407084518505011032003640e080c4042c0d0798030381203100071106a420200c19900f14a00050904200d450303c0d22001216103074040f403c2000202d030700024000c11052100741348c607402e10800510114030000b0191505009141c0000c0da49842506d410350529110710191041c0442480311000a0500701d5110789003924100c00501618540d910141284102800580709036a2081d80d203072140c00d04c0c4094480c0c0108619014146412101003510180300d0a030009070441d11250810038002e520a8890f21142c3c00c3c0100200075001d130310109894107880510740c0d020400c0007003800f4092482030301c0342c000e04160300110a1808103c00481c2040600700418051003c103907007c1d902da1450159050341c42c154141c1400306000e11281d1001c0c0d00300b0781c120f000909202948010f4146241c45075103d92000765a541044245c85909815507441200e030307602144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 721792589 1250 721791339 721791341
    0x1603022a062a0712050606010302180f1216030c080102090d0f111302030411030c10110a050f010e1605030c0d020d02150d1401080a0f330b01020102030910 68
    0x5941d0000b69014456a100b068041c107268841c0c0c484400ba8002c00c584400308101406840d038070007001c0ca021070404502400700070005007120aa68001c0b285422a031415444001c540400c040c0440d00725421030310b90b407581120103441813205580441e000300d004207001030103000301c514100c0000e003030902003210350f19915071350520001c0c2100c008074403183d181400d031903003006a030388090001c2c0e0050b268505801c0003108803107502c600354800e800880c80c28003107548140c1402c041041394034106108481c107807a0303140b0304142194040c02a00c190340121001c240d05402c640c0c0380d4108034042e65103e002c2a4030040512456000d10b583c07642010404008034105070181c000e4440c001021044040c2c010340104203514007181761182c1c05640011b0003281d028890042c100500c0030b654011003503600d040c20300307500c8016028000b403400c04246544014003d1a80702503100c0042501d4411082001c4070780703412001440700c02075040d00d0805013803540700c0d8010309c2a640b241505030050308110320095a0a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 721793839 1250 721792589 721792627
    0xb0d0b01181e1505070c050303121501030e160609050d050a1709060a0c020306010b0405060415170108070612092a0f0e0402120a080f07081603022a06 66
    0x40d5810740d4440c00001c0b43c00040414202c8140103840e07060b69110942400c0e18620940c3e0040c40c065842040070b2598454400303c0180d1100708240000c0c07041901030012805043c5003000380c15140300d0704501d43c800901c1c4651500440c1c0c0e150712090407031aa40d0041c00f4001ca00780c3c2010b03205030403411005001c5113006c20101c881c0700401e01414500244000041d64980142c0700e9075000420803070a84045003401c210f124013400100d4071b002d08003452301e8000b5145111f00d000c0c480084041103000012035004848013415801189015110303980c551034400e556039824030440000401019400741403540910442c9480340c0c0012a4214982c403983c1c07040300745c0e44003016452407940603440002d101c0100c000e559024000c00441340c0450706240c01008006110300b8814a031030340259010b40d000032000c1048803400c0c1340603000c3c035480d05480c0c1451308441c0255086002c0c143c21031946041015800300315001c40302e0001c65403440b072650f0b6200b07030099002958103090b0440c43c10800083c1c01e4480c40500c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 721795089 1250 721793839 721793879
    0x9031209010b13091202060903070f0611120411100f0c15021306020c0f0d020d08070c030b18070501210e10060810020c060127060b0d0b0118 62
    0x3080401052010507010945a00300820f0f484d642d007080004c00101c0e91565a400746244024801424415041c6440344a004801042507910201d02420082caa03007110800e20f000d411000d0301c403c00b101c000500c250007120126100720b40b412400c10300740341c500140f42228a181d55000e610801e070303101c103594209280300182c650380446400812995041e000a040c80c65924045015031072401e20041d01d410742c002d002c94804c40928150581a0300c940d800c000b0240d4044460034001010390034031003094868803601800b02020340074088103020054094034040d500f401d160306002d106248e0b11075141d00c400d000e054001071041d503840c400b43e0705141c52544000c00419000941504c40307854507243c040100d030b04006882d10f030038040140013001e02028240c50700c80a01589408002440d6a4403030405005950020b05804600440c941041070301402a41010308100081603d51b04000016002451903003820343c103050402e14954400e046103584001d41c2e400b84103000c0e00f070941c14a01c2410a9a030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 721796339 1250 721795089 721795091
    0x7031109250504140603061003051012050705010f051602100210240806010b030c07080f0c070905060d03020303010e090102210907091a1e0d110f03060903120901 71
    0xa04281016415076101ea406110b4560540d55407500160f441e40f0915003070050701c111828400c10140e9180c014045811305001c0c44e00203120758607491000305040d06c60b00052200140c40074880f041050004080741621400d0300c8010200c14401012640d40c49012141503d15141840000050070101c02040c00d1043c2801030700e0400c04803030354500403299043c49500c104448042a28040b403041d03a01d6a001e009032401525056051020160080c40050b0a4204c0d01000042840601100009880c10080b52006c11945c49161035804ca90780c0c0307024080d00034201d10f800045030300e074030344003140f03584451740364000c0e5045a107014071103002044001c00c0f90307802c0c0d50200301c0301c00c031401c802d046248003040f0040184404c1c1000b0510310324022041d0000c1c102d85182c19284154901e140000b003546d00b0003101c0012007450021694110380c0c1c0841c800c2c640000b00d8074083e4080100d151210010340308140ea442c042c804001c3d003019610b0000362045000e80c0c00030020543e1b43d081c005200d40d03101d209040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 721797589 1250 721796339 721796371
    0x105070314040f02310917030c2b020f090102010c0318030e0409080f0406120603211206060c02030c06041514090a060503160f08010501050c0c270907031109 69
    0x10074404100d1000c2c040000565130b03003401d0003040800f61030812600420201f03d811340c900306110417220300c10206038034401d00120f15a94100580030140c0031800a0064003952500150b542e109050340100001c5070265003081c09840c1c1c124443c0c411142c1d004204241e014602c9000e440990f0180d00d4241d0903500191104ca006010403004170041c103904004a144035a502c1c03400f40010480d06003101407102003402d100c1e080011403120203a42c1c032401c11141d40f00b980084441c4040c0c401401ca4852014014245403000605a4001d0880c0020500a40507211076168400030440144140e006200c41443c02030407a6034075074410424099588942240c0c00d10744035004001484201c110385c091400200000100400c070f003039030301100d5115219418821400c500000e0b02400001c01409602d04000020402c1d0041107410403007a0340056014016488000c0062031032400091404a14152074000e8030101d0710841c0f0000e0031404032a00f14a60b010804610780402401200103050441c41c80c001e88 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 721798839 1250 721797589 721797649
    0x9020a030e0f0c0a06030b0306180a0f0605160302120c0304020a0308040e0105010e0306070905060306010e04090b0a0e0303130204020a110102130f08010b0607060b0d080c0105070314040f02 83
    0xea0080c0100c0e0780c000f040c20307454000800c040103442e40c01100402d420540c9108590300c0010350030350002c001d074a010582108000046151902c02031020b4106001e5451440501c410b5900c41c41c028444001218800307000010181c041c0d105203413030303a030180303100c000000e0304c1c56443c1e0301554200d84000c0412542c50b42c0c98030303109107603041604030f0030701c01040030b0040000e980c0190319040240002d5026040a181200000d03001924070f1040500540300000025440ea202d100101441180100104482d4001d8103081200d4078040760001e203124a0208104200d00d400010f4920032000f8840c080034803e402d600340006900110040c409205104194100426083c005803680c02c40c803a1003803140302d02c0e042d4540c2d088811030344500c40d03a925080124020b40c81e9203080301e0849410030340109103000032001140110b91075a0008c3d000000205403410311550640042c0e009400c2540c080c8101d000c041610040284140c034020b04282048094074014184600702500d510213a08100318101c0d08070b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 721800089 1250 721798839 721798843
    0x40c030206031e01052d0406081002071e0506070c03020a060501080d090e090a0b040c0905010b12101401031508010e010c02010f0c090e0405010f020d050a1a0a09020a030e 75
    0x3602c140300c82031240d5404880500d194115140180350807a14080b40039040c004c1c520201e400d003040c161000720440c1441c001b0b501c0b282c02c0200204644400c80300340b0400000141d00a41022004440c160344801c003070b0003c00b6404c2c021441d0070b034010f00a450180c803800320585811441c460104c095008000100c0b000c07590780d00c283c030f000300084405002e003540796090003070841c10b00fa00285c03e07032040302e400d04c80001000a1619001503000c030007246503480d241071511043c007482e0301c10301845051200105420541e000030300216040d442c915132258641400315440645070b405104034040f200d4001d45202c1d846a0005c0d90404106002414400d03282e906c0c0a007900c00e40810758480381c1d185c100d1400034550910603e40d2440300c1c04410003440b65604d8005000c5055845080030502d6410081000d0020030343c8a500c05003480402107548103840141c103400f1303000450340c0402d03441c0b801842860a10000d01030705201798005081403141400d1012520094000c7d0200d4010199500300002c280901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 721801339 1250 721800089 721800091
    0x6090204090c0303110f07050f06071506051302040e0f06040912020309130b0a15120f0b101d1903050729040b070605041a0a0b090a020918040c03020603 67
    0x4140c6084820f065003400350881c0c645988145032036000002410803c100400d0340010f82e0402c60304501481e096100064441c010b01c0005055119400510300f4403001d079074010760840c0c0c0c040d0b40c0ea003201000050004202d02441c4140c8051920f8074000500c8000c00d22802c95001400900001e4040b0003911840c03501000b400254015a1000452030f88610f841d490501c01c175614444144421411080860400540e520030500d095a2000e002c145031401400346480e0300c5079405003001000f000c50110809807852800041c014402141c141c80320501c10034007030490910074900c40510070140001e02c9904001c0060881c214280300da800f1000440c1803080e5401030100600c1c005546440f0102c4c200340d0080303074490b812502010081001502c140c2c20a5a01c100c5d00240001000c1c0c1d00c9080500100301d000180c40b2424011000b080017604440e4000d620f00d0105842c000042c0d0303940308ca00c02c01ca202d2030030015130292800c20100c1045a200d0350340380e1f100e84201441a0b1155490703000c40c1c3c071500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 721802589 1250 721801339 721801343
    0x224070302070602060c0c120306030a080c0a15060e040f020a051809101b141c0c0908010b0616020303160c030506450d020304030b1308030609040609020409 69
    0x121003c11400c0e5042100c50f400c0340c0d41721440c40c0340000140505540d0300c1074045460100c000800061410b075030620602c2d002c541c1080d42c4030b0745d4407400c1b8032041d200c080541c4110380340c18403002403200b4440380d0701c9440c05540c070807841700035141c9442c0c6410000c4806028102ea010010303800116040e210139164460030049501445000c1c00c282c501ca6007458500b60621180e1807410300c21f00301c0d0f1110812074004040441c00e00c903d21210400c01030340c0520414034002c4507100340044000f00b1303005552003482c54040680da408400f64542d034a107400d840415030801c0d0300c9002071005484c040380c0810910b00171072000341164130303103007109503080402c200d1140c0903150740103d40810000e2100a00c4003951025550b0110156120402c80c1c0c0c1140400c6100d035a0311012882c01c1e040c1c0d01485084160080241d400229100d800e0170150085d41c0b03500c03138082201d139407085002249441540f4818900074680c05a2060b045503942803d000840a008000f929196110348031200035071540d1213284c0040e4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 721803839 1250 721802589 721802593
    0xc0b0c0708030c010c09091a190317030f0702060106090b09011704060905120f0a050d0b0901080d0e01030504051b1302042c040308160507050105010b131d040224070302 74
    0x11090001070034100702d0360321001c0c0e031509040d04154580c1c07681500d2080b444080b9254420740b8009e00e126823619030580c00090858101e0f004c00c0300040c0140001d18404d070f20220342600d09907101d45080303071111000e208203c0891048842444002800c7c405443c542070185060b8404044080c50340c60000d2094509980c050341d2401c500f02404401d009038002c41d00202c0d8a01d10b0500c00c094600550700c140c0204030b04100e004112031149140c540c0040481000c0184240b032503584440c461500d03807103000301c2000402c60700c07050022303554000c3c00f41c1c070320854104005d44414084161810111751020f11210b034880d512950303c89514550b44041c10140c120b0700c02042c504542d4008141c089514140d1410b401c07204800ac00c40040e6000811f90b9001d20b504244007035040321514203071841d000f02c40d0024800d5007000004a0005502c0300900041c840364800032440666444140a001040b0042a07588030440d00015001d4140209500407040724007202c01804210150340d01340c0c5400c486000c030010f03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 721805089 1250 721803839 721803851
    0xc0d06090b011e05160c05040c27060c0b2206060602160e0a0e070911070209060613090b0d060e0c09060f0a05011d100c0b01060305040c0b0c0708030c01 67
    0x756800f9400c80340382e0354202c040d0540955052000781c501c2c00b5642140b0303010b5545140000800c0041400c000007820040c0060041c81c04408002d0600d5403180d2001206099051740000b1160701d0500200032500320380c5030103004410715142c0072002c55006004010752150b000c0401608020311003080410750060310009106414508028200845000b00c01c90001600c3c07014807102c1001d9413995000100090f0010b041045080842c1c20b001180c2d0082d4525460a0008005030324010f004004440c8204d0b9400b250b90303180f0040000c14000c8140d100009140e00009025040d05548914906c0c0300060100381c0b042016580c1c03c0584031051800b080c2d07a081140040040d0600e5610b458201c40b0803030f140390480c2d13a000041801c0351083d2007800c1c101300e007a6401910a11800203c0c601e41d0f0005408032290b01403240c3d0260516407a44021900c00c003040c000003511601c00e01c540c5006179070004117100f0040c0340035401102c60300b2403403048203240950080010840703410001054111140b000118139 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 721806339 1250 721805089 721805111
    0x10507020a1703030106090e0c0d0f0b04020a03060e0f0411100e2d092a12100302030f010504080304032d1d19050904210305010504050903210c0d0609 66
    0x1140700da2300c288100c50f500e8050001e0005510b042d00c401184034400007800055912a40d0090505500c0c05600b00c4d00c0014031780819035054002d6416100214041d00440d250b401c1d024203422401c80c0c4c0074094030a0541c44080c1481c1000440324910700e18584105182e1070000054113110b41c1c1c580701030354111110440b03910300b1a1102040c40451040b01c00c080140750144c0c00d00e4540c403161440c5000741c5070700d002c0c5852031180001914a140c01d90100d00f103082c6043e82444000b00c1031404260720910a600443c3e10788901401103d1180b54030100c61800c5843e07075039003500c0b40c0601c0a0348820b1075540d400b600d08284611a0401a0240c155030390640708840c005804440e242810103641c003500701c088114402c4100131a91300d00300c1e00b094890503990340d2a418040f4074030100b24100314086150312441281c1c1d9505800080c10780c0c1c000c4904019944072208005d5507840f818145e020501c1c0c0302007480c215248001a503d500004100d40c1c6454103484045000480f18903030484d102c0310799910034039a8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 721807589 1250 721806339 721806347
    0xc080610080f06011206080f0c190f2106050403020c091308120c0705070b0a0306050604140d061b021c020105010602100906230613110405010507020a1703030106 71
    0x2816006418659180d0034002c8080248241c020501414001415400b6103d45a140e02440040001300c040c0e6909103280d40206480d16102c0142500c90708070b503000b40b00c0810040d4484400ca88000b25144255032818480c100c00b9007002520711800034402c010800810a640140b600c0385100b503001c1e11015440b40c08005450b540909003c80c0300c0c0d00c0e6200040040d130150b04a030440c000c650180b110315940c20003a54810710890200800c0d5014655002540e170521101422100c0519202403018581316000c4c0010f41c09207125000306d41d1480c0003404140c3c01c02c41c40207045540110008600d2030180b0b416150441e03800311481005a00c03400f0408080078060050054000703030391001f84019498107100130b6403040c5034a14820b440b03a80d010300c0401c00c95030746d20040d440c100c04021400b901420b4103140d1403c100860700f45005410600b211040701255104030071100c3c608500407803c1030b042400464550f00842e20423a0011003003600800d000c2400c2c03815010040c0c00400440d40ca40c18140024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 721808839 1250 721807589 721807609
    0xc060106050406140d0e070e0f0108061e0901150b0c0712032f07030303060e0601090605030703110f030a020702011b0c150210050903190c022b060c0806 67
    0x40c0030440c0911040c006030740d0003440350380d040c145410700c503846030f4001d0514402081b04d0b40f1803109921a00031300107041850001e44610410b200b120315000c5a030b0302c46245440d148125010707109901503401c2804800340d8192226000f1103820300000383c604285c1007140c407140071604480010318020801c80e000d888200f02c10300c0a450700d04842d0004960581d409042d0714610201d079140f20200c9142c0902d0b942185080e0038010003500200c0e06456540e0070040c00074a62809415285881607001400c1940504580401c4403901e0382c0315441c4d0740c0c0344081180204003926443c403108004100501d405074a103009140904d600030300040c0d0300c2e8940d1002618030f5103564030034500340b1040c0c134064000c42c41101d03140c001c8034210103030f0b40001d19155074101d080c808290308800055140c401803154981c00013016003034070084200c0c07503154544940c1050b10300c050035a034025400207104040c03102c40c507124900e00351441d05520001c5a07481d65039403100280e44403203061303000255024007004202e25103d0340d10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 721810089 1250 721808839 721808849
    0x2102041806030b0a090201021f02040e07050a080114030304080307050c0f090c041202220605030f0f03041503090f0f0314030609070e03070f0f0503010c0302040b0d0905160b0c0601 79
    0x200700d214070b1556400c1c410403005103850b800980d50100101036900070b00c4000c9a5540c031070f50014010340e4142e9803000942060041010984600e000552071078080d4048428030046512940f10300d80c80d058100c1341c8940b4469100307406010074000000c9a503401c00c06006111f00c50400b40200040000a120b0b524a404800301c2c410040c01c0300380480300104608880590f240128507509540d81400415a4044242d03003106082d003d840b80c40441c3e501d603900074015200100c0549003502c80c01c1408940c1c2381e01d407c0e41c5520640082004101c464029241e40d0181c2500c0e04001c070305090380d40c640081c0c000310a27000b61151034002d0107010805502040442d80c44400e01d040747d0440c2441004540a0400104031034207002d00c07948a0190756a08228a1000f40403108900c4401502d40090103010380c014843c0c18007960915101f040304034040d00942d17064170f000041c507504064070710b1004000703440c02260070365240c0a502d100122681c540c40c100d801800000c0002940e40c0c00c0c8040083c9040e80503441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 721811339 1250 721810089 721810091
    0x50a0f0e010b1204022e03091e080a03200c100b041b21020c0d030606180e06120105011401030b040204061710030b15011707080a020d060b07030c140a02011e21020418 73
    0x50381d0010752b03600b0130303254050300d6403070001004101696003c40b010074108623004600c5010646284c8802d000460311075003042c80c54280030703812651041c402500c80300e8002c4c11a1070700c50040c490702c0501c100700d00c800b0608000c21f40f48100003403a24030000c80c0d104416968054000c600e8a070103803901406000000d0981c1e140141e002c030010507901448540380e00500c201d80c580759000c076410b030f500c909511410312170700c03c003c01055942d00340030000c1c0d0745100d903400d005c00e00f0260280514a007900c02e0f5402c8449684500a40540d242501528031000408101901031480c0000c004141582d846034420f90200390300c4140c0c2100e600c00904080980210310200b10251010005102ea0202610341c1001d040c04016881340c0803001d04101811040d00503011003080803422034141a03106000240c003d0207050408004002c0e007505685503030302c4120190100e08030012500b0b01d22000c20b013140c484042c42c50714506a1641e00204016061000311190700c054011a040c4907142c00c050b001c0c4081d074400c0d07078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 721812589 1250 721811339 721811393
    0x308070e030709020d1b090501020c0a0f1a070506010905250905151b25120f02180907090f0b0108190204050a0f0e010b1204022e0309 59
    0x80007907074601840c040c01500a40101740824400c00d2608185107014800f1880b0001c01c101d210020141d22040c070483d401446118440f4a15081c40011030b020740307101c00c840c420083c2c01c12000101d401500745810400c00805c101c4007011400910003140030341030140b404140b506182d145c10408850a82d5002c9420346608110f030348864000146030304503203060303c0c0044038200402c45106113028412101d00d0a82d22030003803168070500403c1c1035103480c2080705a41c40f4041e12580c1c0d000481d0403801a980c11000750780020002c10400300c1c055030058401050303410086030004481121282c10b8070384940c1540600e800b4040e0311120300640310306c54212041000b105e640500000d1422501802002c1039500c50000c1e070710b25042e40d030110341c003a14010b0b140001250380d8403004501d540591040c4884d07032103e0b10010a0150001080703486440c403a8103074841d1901c0740c0d020009174520341080c40405150b1080c003051512017488081c00307040003949000801401b070341050310703180d6050b541c2100d40f004509 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 721813839 1250 721812589 721812617
    0x1080603060412020709060b04090f0905030a03090615090e01050711280b09100624081509010b0711032803030b0a090903030c02010b0a1406091903030807 68
    0x100c00d80d025400a00d180c01940f4000010f909081c2243c0002a2490034000c0101c0d0380100d14000f0000c49420080401400c02c41d040c1d140225050341d68018803030707001007003060807851107500640305003030040d03c000810381215900c10400011903800700580e542c440000d098005400c1c81425801201420103042c0c40419440894440003039111f5140340b0754046203807880380c01c070144c80400d00550144540f465402c1000e0718076519880c041c00d0480c1d240c1081000704801b4201c05034854224003400c140002c02804410a84840b10000c121626418a03403080350700c0b59a5440805008003036a440307855462681d03091030302d441c1600c044503034001c1c2d0114200c0d510241a0b10105d102c1d803851002030120101040c034044020b001c0501c03500b68082041207012804440c194050700703140b40310b92130422813210f8540042c0d00340c0c1d4103a180c203984500c1c2100204484000c0b00002005c100000b45001c2c5003200c1400003a00701c00400071034025070744017003c0c207000709034005100680200c80b50501c0e440100d86c2c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 721815089 1250 721813839 721813843
    0xd030e06071110050106080f090f030f0322062003010503060402190305250e070c120201090c030b040b1308090607140a0b07030c03020901020c12032b050601080603 72
    0x340111003000300c0c1107042e00c440d003001d00002e400c2100380d0009015a5a5031070004054031803d603000702440c80c4290200d05100300c0000c8162081000001840c00c5c440c844480070503a0b080104500310000c40b0182d03d040000090040030300a0348510300c0002c1c038010002246410341d03c88802c2501449042006103d42da800158140e4410741c11600581c00c13501d8031005402341e5059a100034213920400980810003039080f1580012941e12044000500d5590008a40000c10945000e400308958441c3c0401180945c440382c0e8001e0103900000c10110041d58a08680901c1035200f9180300d2400b01c18442002120146590006103c040c00c00f040000c54403034031307000d104400f85c26215000010b151010031880100300c0c0c594401c2c650507103080c2c0520341440e040403401152400b00207890100c508500c14041d109031031290380180c0c010300722001c60305c042c084007002034070029010344000d21080c00070600500290744902c030600d91245070301d0038552410b019900d0107040d4038144000d031000c0010704c3c0c0300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 721816339 1250 721815089 721815091
    0x30f01141617130503030a020d05070309020d021002240402120a0c17010b0603010611060105332b0501080105071e0c122c01170a1b110d030e06 63
    0x462840c0c05281d44502454a0b030074986000010005d000c013000300070401c48154080c068004502d5410b100702d03611a6000c81c00c41c0d00040c4004d5000600b01061030150506121120803920280112a904003c42d00c520b0020211000c4c4445401519400c000441c24540c00342580040c00d0002400041c80690303a03507032060464050858040121440c0c186648001d420810302250054032281d585c1d6180c1038010202e6610a020001c00e00c06d0100004031820129044064a0740f2003480f2407110f0f213031001040b80700842c1c065541c0400c00a1049482c083c2517008044202240103602c0171205001c0342000080e0f032016400341c0020391403c403c02440d160406007194456044205051380502d040c0e00035180c5201007030780903103241030040100c1c903140c3e080072a02180d8007410006412034030110000082d0030b00c0e0700c40036500041902015184e03002441154070f800c040f420300007013424004019520880224035a219000502001803072416403024001103415103018034003482000f4600d20709680d1880 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 721817589 1250 721816339 721816367
    0x1a01030803130303020d0204060f080f06130902190b070b0a0e071503020d0f051009061d220b0709080115140d061b02060f0907120809030f011416 64
    0x40b0404000d01010311950480b4414841e0150454845480d001c0c014181d01c105091080410f4800ac041804800c01c404000d00c10070000300a842ca00140d02e035108003914042c80c00301e80104d40c0d2074003a44121864014030000e0008109102c0c1c82d00c48a091406990201816214120345004502c1c8050307480425914150364191480d4842d0654621040b402441b030150b03000102883d00e049030403242229041540251104404201d623942c5424030030044541c1c0b88600c121a41200c101700d001002d400d0b5032160b202d0901c0261207104e10844080d04420705100000b1a1541d00e1881000040f82e0010507250144c036214000b00141c1c400e400c000c0c0440c003450b00a4095540161910815580d548007640d050b10360b01100510844001e400d29480355450782d55254050b0041400203004c80b07180b1800148682003a0008110091424112950700f103507082c800d41d05001c0030041e0308243d89081011810f110142c000006000280d52901011400083e04070400203580f5008003850342c1c0d0100010011003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 721818839 1250 721817589 721817611
    0x151806160b041505070801050307090b010909050a09050307050f07120302210c1605031005060a0e0624030603010e070f061d0a170114041e0f0b0907031a01030803 71
    0x1403980d0500071070750120308040d1510f080c1001c08000049074003e0300b003412100b09804886059450350000d03c1519141d020b503500151400c5010410041d164024503000000c0d00706c00a44c645007500c0381c43c1580d2000307a06640711b82c84040c500c8036100c2c08001c008000e000f4403006009103802c07a50700941f69030712500302c6584031024810200c6454103d20881c0d80400041080350102100d40380703800e001102c00d00c100e038400d02075121080c00d6030a1501895115503c0205031007007140c14040d003a09036440c0500900d0b040810003104042e078484980c25109181c940c280101c0c1c90345420310415003510389407500900190041c0d001000345111601d4030b80c080c1c45441c10203c0b02201c2c00103405204550a143c1103a2111821100158041d2403244901002c8080710013804401012580d0b00c0c01a141914000c044100854090352030311201d0405070011031041110140c00301c0d05441c0ca204005081da0383c000b0541080c03408108002c0030550800f08031895043c0d4603d03c0d85540c0350300e09903000c000e000c21081c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 721820089 1250 721818839 721818841
    0x10308120c0412060f290103050109020c1f1e0902040c09080d0509030114070f022b0804061517010b04110a140712031b02030c070b18151806160b 64
    0x750403400802086d507900e02000009507038404e88050b410141240440e01e4000003051440060080720b02c40c401e400010800c100400360b00c9248601e081600c815a0740e07807008181606181e852007010780c620303422000310b0b28551900410044403d02111101801000c80c400c0114840c00f0490b4110501181003880d242c3c070420300402d001d0826803185031444c0703143e0030802c40030680002c41442c0180c0306908485580404901c2882c40d04845c5200601d054082c0a03c01840c074890900d090b4070500c10480030500242c0401c1c040001d84035138205090618803038110f00203040003445071640c031403000c450a111510074038140c528181b007000d41200400050701740031170100044d48101c2c1c808540c88042c0c2110303000ca03c00010020050380d0340d880312031781301400003490302440003003074440a119280281448074548041e05289074082c40003408102c1c003031254204955610300045944a07002071101c0c1d511700c22031841041840c640c0c60207521a520509c4810b003c1c0ca5903a1004002c141d010003840c6031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 721821339 1250 721820089 721820111
    0x40507050402030c092e090b030604020d0204050301020c072115110702030f0312010b030106120f1506080412050f0a08040206072f0a15030b06090306010308120c041206 74
    0x4d504c102c4d8902900304280c400c14000c0d0182c8140c503402d04c07035000002860f002600f0b0b20115410905071080300b1103244240041600c514099008201500c0ea0f82c40c0103203855034800c003103426a041171155a5158204960401030b0041d810700c0c0c68031410903e25480c0b1070032450750340c1d08415411602843d44142e035a50502d806d00091508480c1c0c41c6800500711940780402d920f02983e41d034408408200035000360000000c0f400074a5054906890381d644400c01c45201e011100d200174186140b00036030190b21520304d4440510841046000b5240981e01d840032850300f42800046100c00700c8011041081c1002502200080441036a0140e10a0320784a6401e4480b4000240c20f4042c1c503001620300003085402004142c0c0e841d6215140820100c131000c034010a035030801400165511070707016103510783d110310304040e4400c0c4d21100f840e40c002032405041044010200c1d207008002d800c12a845a80003803001c050460b400404c41e4044909008246801d0400060f40d040c0102c600c4002c000e55152102455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 721822589 1250 721821339 721821361
    0x17070f182a0534060b010801050d0605060321121303020705060a09330206060f0409020a03050a030e0a0b070c09110c01050702060121050c0d260a090e04050705040203 73
    0x9010310703c416540c0300c101d480c0542c99592440310842182d0041c5801c3d50f03d007465018084240c102c030801048402d0201454603a01c0240200420003507041c003131912040880f940d40c0f00c0080e41c200ca220440c0d5244d00c002c40310b894840501825210326a030b080080c0c40b0000c2d0740003501d04240c60090b10090b80f00c4294900c142d80c41112900001c0e040441043c9000b126440c480c400000e40414402d014a00c010f130050a0742c07100c1d010340ea841c2d0880e0f0211204409418160081d40f100c0d4030203401c01032140e0781d9443d040c0c00d01e0400d400481c001001020b444155240501014010304506e124540c41e00d8281d56851002c1585d62140162594032131030030007104000c20080c0c46202411030001d001038906602d0081d1100024081c0402004895003107000300c42c8040010042c442e40800100782d43c11125080010856020908071190345200358020340070000303400c00d04007070301c0704001c542d8440660500141c110304003908420800c0e0200070030403000c0b038000207484044500503500160f403038503000b030514 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 721823839 1250 721822589 721822627
    0x2030409020a0c0201030b0f1318080d0605090601020607020d080709090903080405010513050a060e1905070501020c060a08070807050c030f130509010f17070f182a05 73
    0x1003180e01c0400c1144002c1d4105004450f0180700b42e9081100d1190141003003100c400c042d80d13654000c08821a03d03100503240c1c0c0c1c0301c282c182c9034a0740d0300010b000e519910000c1650000c190440000e407290020403e42c24002003150304500700340090101840d240324000d507160211001c01081003d4100824800d80c00380fa0014085c00110400703006000260034007810703c182c1600c0c00c0301d0f50342c0313840c0024601c0782c03090810644c0c0960100240289426589a400113040100c40c03101050151031030303a004880494800c0aa414407980c06004070300d2500380064100020180860300920040000c1c5000a07849074250781d01914604180c0540c0c0c840c12021280ca01407809a50903a220000f54101c42569180c007404007102940b403200700060b100c1080c003c0610080c0b08604681e18145001e02986011501828031903881000300e5550564a051280d10302038183c1c0540303100c014100302580e501c2442d028504010840b0007124600304920301f050040818410b00c0c003010004042003102c09001c07800011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 721825089 1250 721823839 721823849
    0x50415051e04080a0302120408070902030a1d06070f02030a050a0c170310050a05032107240b10020a0309051c060c030203071e0221280917060c0703020304 68
    0x3080c0c403141c8460f8540c1e03503864001c8064001d88914180c920006c000c11040342e094a0103440a8003006140403890006504054503031403000c6d465241145c80746482460044d8441540001440d06052102c4081c00c00c29400b910007085400811030202c020760480704132501948d0516103900c0e0b450803810440c09100b000b4201c400030520020901010120690130303401035801c21502d80d880183d45508061380c0d80201d00c00180ca541c0d8121100051441500261a04c036000f411500d20100040c02607200b5a10851140059650380e07081d88286805d101d002d85060507001e0000f4031a5034215100508404014420688201c2945d0401c80405030604100301415610120920199030b8120f4003801030b420071641c01d0000740c0190a00e56141445040b4107101a074581c01404030300c0c0030305541540f1551500700320703007580c4802c00c146840180364481d0400d80740212071500d000008400001040c0b80740380d030301100c00902a55500f0b82a880041000c1c1c1e00724100303002d41982e610081c80c0586c2035010325884 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 721826339 1250 721825089 721825147
    0x9080a080c0703080606072303090127030b0c0408120316110c04051302130b0906010504180510031406040b1e180f06010f080607050a0e01030f0b0423010605041505 72
    0x40408d100300000c080d028031842602c0b4580c82c400128400c8180810003840386800300d032020002c002040d501e604064009d10400ca02c1e85c40c243d100c5845520388040b40420810100c5c00104000d6003141500ca040100306440c41e2021800040004032a070710521100c400d4807172796460000c03940d10700400224508656000d45601031001070f542c40c60008007030a585040c020f440d40400552158468001c8606450307c0001c2c2d580b120351022144001400028200710110300e11010110204205021014481c0588001440070386017518010f0701001d0040c21606009410488890807961510f100e241d0010411547d0000d20000040081c5416407a900c0034003140185000403d00300401e80c98041680d1504085400a03181e0000c00c840d6480740150300c07030020342c03a107501c40c0c050741c80781c2c0101c0c2010100d080c0229050a44100050441d20550400c11a01d15000c1038003041c9a242d201d00350042245061071801d107446c000d00c0c4d203600102c0c0880031080240019682041c119181041943c0c5034140304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 721827589 1250 721826339 721826393
    0x12030409090b0103170c06040b071407110a0501050918061c030f020615010801060e04061809170702061c0608070306050601180f090e0f0109080a080c070308060607 72
    0x42c6181081400e0209a680b41084c1c80600d42e10740810301142c0015030b424006141c99076a58940088107840030f0404404c00c1000d0204426040c202d030013401d01940151030480740300066004111346004540e00050500605000c142220b0755204240342c10280b80c0c6016607a103946450018140d01c0074001034a00003544114140c00b4160f03c1085243c2450098084847c04e4580407007030503002e030301c101d410350010700040018801a40f04800c0c0000c400d10140001c200d039a101c0d18400080441c1901d0890300560303e880c8071044c031100d02240a9154a00510b503454641e240e004510903204641c0e11444034034903209003070705060a580c404402032044405480090f40c8920b02a0080c000560341d840c0007400d040c5481c40402c90341f200d0707401244e03415207080402924018000c03000e0710344041c5404203800303560743d503000c81c032428011404030314030800002d540c40003620350150088001030301100c1c4120080c40200300080d003000240ba0014011104243c546441c1c2c0303050b01000c090010b00d08403501c0110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 721828839 1250 721827589 721827593
    0xb2416061119031b05070201031503060c0e010504031a100e07050706060e06090615120903040e070906080a090c0308070c0314120f0702031c090905010e0c091203040909 74
    0x20307010b400d403400044030014891020030700403404d441c0da5050907040505020b4080501601460082c8031851040c100401ca2070701204110001180711361058035034503280d103011401c60764800300519a0050908040742494115100c10041c2c10140144608107001d10010a048c0b1b060f961051000340a019503090307103807809003001456500000c01c21601d050078800d0100d180c03071001003114850840501074400b036030f40341c4007081041c1001f41d407100d6080001300000e1100c0102050700500c90b1208400a5903100e240140450002600600b600c0420019410500205030710607070aa030030900149c2c012801002500f808204850254402072000304006005000c0212070b000340350440e0301403950b03243c04184640806072030303a45105841c400754008105e03481f8080c01322405041480d0000d01200d540c080041a00e03e4806501c0d801040492900d44c000c11071401940a8103014104508581656003400980d954a6014170403009100d249a101d220710482c02c10820380f002486000d000b8491a8070714 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 721830089 1250 721828839 721828871
    0x20d0215042d03030c0f15090606051203030907171018031103041404091106030408030907080a030e013c08010e0f0c03070207090213090b241606 64
    0x806a50702224084008402a85400c0d15034500316034140d01da0121885d404d03070324611181e03182482218465030a140c1a03200c05018810010200d03c180d20003d1403505000411022508601c4442c620f5841042005254403010455a00302c03a1000090400d84403c010154201001000504840b07441d100420400424044521000c40d00984440719040c100c60f104a440f0301c07490086400110031400c4840305810141d12100800d8011420001300422140020b40d0030b0b40103480649000c1004024840404014000c040003003000000408d290101550080e001c81203080c0c00d2410300c0701007607890441d48059030340c4a4180304c200040703104a00100400304c08000800c480c48001030200c00000c101512103e47c00781c0503c000e003050101da03076100b80c0e06003a40c0d0b100801078001c40c01103c40010b880b90340345c0041c11400381b84181c18030701c19090020004c100c0708043c0309a4400d00b024080c100d888441c41400b15200302c00e0001040e51840f11199004034031060240c000c045912700b02c10101e1841807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 721831339 1250 721830089 721830119
    0xc120c05370e090106060207060e13150608090a0b0f07171906080c1c170a0c020f090f0403050309121b0c1210200304110a170604020d021504 62
    0x1180340040b0250f15125040c03800c862982c05558050f84c07011405202060007601800d03441c500060020161910004600003a1514003403071559410407a1014030a254001c174110340c3c8030b00f10000400d500d007100c1d115001c910300701030800b9884007245004246170503c240108445c0e8a004000c001041c1040008440c4003224070b809025080d180100c04128070740d01140800c051840101400b004000c2e002201d0520003602c84125528141500c3e1034078040103080c050026a809a02d490a84100600610183c503003442895440390521b41e080201155400b0841504190103140454880d40d9000880c0d2400004050300d0044000c0404d15100c82c03a401c81d8110072070382c46401981d2191500e0018002594410003060310359030800046002e0182d00795001c0110740e108540850100d100d6100000529482650196000b4250040d840c09909101c0c100600815510803804442c1c002110615100c10000e0402440b0341480c000601c03d555884c030b110050708490260a039503c07036071400c0c49404114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 721832589 1250 721831339 721831349
    0x21e0924041404080f1c020405031009050303130203010e03040801020d140405030d24030609060b1e09090a050d0c0c21030e0a030c0902070c120c0537 66
    0x12620498801401d042c05480074000a84400d45020b480700d0383c4550068100791000510080c0a10800920400c41072007020029103642005030703114144018503040c420450503001000d030810b401c140000b8400802c07139611603101c414580006100c0e1001074090314240c4011400c2d40720104002c21180810340c0101098540c010040242e18508003244501c19400c03070340a00701d60802d02c0203451880e80385d0001140c3c1c80340c0d00c0c0312124814903041103520225183c1c20603600c0319903600401d010845640f094050b400000c46113002100c10f81b0140810b5030b028096a00d00074000c1d5404115441d800b00800784c10075501c501501c1040304020001008618a0401134407500b40d60311000518058940c42d2040200d18500e024402d1101914286c1e08040c02141094010341f506200101080d580f00c0d601015002c80d1102580d58401c1d414400750300015500700c00c89921800c995000060340409000301101d07410780b6003060041c0742c4100d00000c20804040d080e460090365004090700f0030000d0241080d60 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 721833839 1250 721832589 721832641
    0x1060f0813030903081c05012d0f0b09031614090c0307053109050106020115050a05012105040b01092a11191406060d0b0103021e09 58
    0x754681442a40c1e0451000d0041e0200d522542e042c0085101a030042c500c4040788803111003c807817100b03c82011a6070907400103c5480202414136011110450303d0b81c12000051401410941011406608021648240030307003030100040820181d1000d01482c01035203d40c0003040c0c00180d64815001103441004280340c4076042c0740c1c001a03021150304007960b00403240c0d55181400c0c280c10381c4c40f148000d0b49001d420340d0740d511911a000c550400c800300250241105440100b580d51401d00d010307080d07841c404010310455824600610090300d80341002d170300b2a00d007441c28903003150940020003c54455040c080782c0030360800c001c0005104c50207138400d0495102c0760301000801c07442e003006a4a2744440341c0c00f82018404046480d4076074410420f08420194080541d41c104110a1201081031007860040360080c0014002c58010401440103e41c0440284e0383c1c16000c140e0303595151030122050200900c1100c003c0140f0200e40402ca007642c20014000e0100101c41c00c1c40c407118101c100841c1d0841d0007403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 721835089 1250 721833839 721833841
    0xd18081c110a0803040f0807140f0105090705030303040209100803030c041401050f1b0c03031309050106080601090b032d060a0603021c0203090c0406061106010906350601060f08 78
    0xa62000180220260f80011025055854a98501722440f00418080d103c050040c0136002c041a02c41e8a09010342103c000244882d0b4200007891342074400050010002d90460030342001a610040201d0368815411142407a25a880940002240d00311350004116480040100300200d0303050f1000340282c0d25081301c1e40c5000031654004403880c0c071680c0120075203488140805640c40519030180903400603980240d0f01c15401a90109107940c10030a1100c001c00c01403c400c116204407845001d024105078070f8039a6040c50141c0018001900d544980200c800300000003440e010b64030541120180a203105000071002c0103071510b02c178100155019441000041000a0003601a10031690840ea82c00001c0c40101c1e903a0b8a100300941008000c00d40b18044c0c100c4d100c040d07503140d00c15203010300450b80310110441d0b10341d50610300d030610503000440c00074030b050300910a0003c00d03120302448040d20109001001e5500c41200c100c05c0280d07804060714410680041980d82d0042401600d030401541d80c2003403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 721836339 1250 721835089 721835117
    0x90d050d020304181509090f020303160b0c07050d05070302070e0703050a0f05090d050d0902041b08130b04021e090f090d020106031106070c030803010308071e050d18081c 75
    0x8661800c02d4030f541c1071781e040104120060a680040c4051401021030062105040c1c001c00e0441d07008000030f4100d942c1c51548241009400d805943d00500781340d46490610700b40740e4034a0740d0b4003600c01104040c45800b24008003010f00c00c00112000c1d0025400d03a5800d800c2482d8080c000d0720b000e94458100c01d05005003040790440c14441c4500c1600c01600500c0d0344140204251120350003210321801d47c64030f8801c130740301684490141000b120010400d0360803405416000070022880644840810b000d64100c00d0301044000200541041c1c044a48400c40c000070180d181105007000c5000713420200c505c0800034855480c1d04480c0c407038940e00043d55450b1420304c0302207080369054040100b0300791983c40d010203541440c101403d031803840341c401c9040e215105d0303d0320300294000340d004440001000035801c042080504401a850081e0064005150010f03600c0c20380300c040d042d00d04000c21018200039a540d45600c0080d000401c04036094070202116540e001c07034240c00d044510380100f082240c070300d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 721837589 1250 721836339 721836341
    0x30f020406091b180906080f0c0d03121802102723040605130603020f060c03030a0b0105191706150406030902030c061911071406090d050d02030418 65
    0x402c43d07050241c0754002800f1500b03a9952584800b0313885950b45642e0003086034191071044601600c03901008004108685a80f1858414414011070055000160400c00603400000c1d1004019416001142d6892080d465003d44210342a000c1d6000c0200ea030f026408980141d00d0b511800d089241095208044043c8000308525500c02c007c00b03140f1440700d440d052401100b41241105005001284860f0384800090907990001d100d0306490355245810421450b1580c0d00142c05c1d481660b0840c10700000c5008151603000062454000d0303515060f84401d1680301e00101c44621011091010000e0318601c801808034400b402c130100f042480b0400310f8801d18140c02002011556020380034900346c00e10702c00b18060481d00348200d805214a580345101030b80c03064050102e842e01841c0449400d0324100c401002d0b01c03500d40481c00707583c00422041c040b107412903c031542015800d9403915a510081008a40210024100904680140c50108804a0703010000780b04590300c00d00c00703119040400741001c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 721838839 1250 721837589 721837601
    0xa140301030b0f100b1b150907061101180201030c030f150608010e0402030304030215120c0c010b0a050a0b0a0c051c080a0213030b130c06030615020309061e040906030f02040609 78
    0x2011642e024001001c460000000101d0005540011f907401404e0040c2003440d100410b40d5500c0180d04a52820b0000d1030b0710049030b4040040c658000c1c0031220300c40d0f03059000110101006410551900e856a02c100c0c001d03003000b00244000c40042001241807800740141d4070701d5020b03403000503014600008451046500c0305024640080103180b500c0e02e103600f0802d90500c40d000300c7c4c00c200000c1c8281010b0701d050b84240d0740304245115020b69101e5045000c5821154291203551103929001c80900450b12204289002d0f0740d85001030703603a5041c0c0c03d00151125038808500401e107100d40d100a940c4a200c00400700c2c84600681c03613040c3d240d1a8a100f141c141c1c0207400d22542c0e0406030380810404101e03c0032a8a4010840c4528070b50240816111003a19400980140021980f20201008013070b402e10001d02640004c0c0c4055410310310560002100b512920440304151420281c101c1c0b0f4034081002210018801000708008841d903a14120b24201c2005405900c00c9180110014001145024103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 721840089 1250 721838839 721838849
    0x1a0a05090609131502090907110604080c030d020c0102090301140405120a0302211902040b03010b0a170a150e190c050d0e0715051e0a140301030b0f10 66
    0x200d426070780d45424003860342c400802c0d403d9842e03840c64015002c82c074002c94140e03a508215402503034600105003444019a0041c2042d020040c07400070b903808820010402ca41c009074000da410399100d0010410074a103000f1303180d0045e507541c07000034400d00c203850543c0145103200040d030003030082c03100190a80c0c1c0c9850088401415a8102c40016203140310344400a1058211606005040820002402c1e6001242c00000040000b911080c403688900c25031b81e071031048040000a501c0d01c0e08003500d040080c00184510100b002002c5100c0070002d005400720710440040803018041841e0240c0004040e01c0201142034113000350b444040780821204582611881c40c100c002c1c640c40c00079030ba2090080c00b0031254042000401e02011020b140c440c0a0309001c00a40f100400142e8101181290030038812b4041005005003040070009000040044a019841030255151203440c07242d000c1d540c0d104039140d49006d110000001200300241e0051042c052446046600450780c1c80700b100d00741d001040c1c025 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 721841339 1250 721840089 721840099
    0x40201050a030b2403060108150622080a0515060316060503190e1506030d090612020403150608160b220e01080c090a0506010f0c1e061a0a05 62
    0x128041c0e00400b03824007000d410040ea9019221081100040d007a42608412500006110096902003c0290005050250307198400c0103000000c03c54490760305000740816100004041c0c03d2f00098a20b001441041c05590204055260003911001c1c0000540100025107020070f034a030a00050302c0d0320801d0400d071070924260414105407100d40008012450024040003061008201405101c141c00b2041009060122901c05500c80e5000c00402c254044e510001c284540d295005414004445032814000e100303402c6800c0d10f8000e48075940006d055000b80c250301c0d51304910280d015204481e501d20903600c80e501c6903600e4004901071481441a500028030000001d0032160f2a0840d02610000700500c80307964900c03d2200692003640851140d4000004510803410004803095101c007400381c08000500d011380000c1d08114240c07402104001c8580031034020000c0000e000d1a4085084a04002000c40341c641100030b0840016980401b20880200032914202074010070160783e40101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 721842589 1250 721841339 721841347
    0x170901241a030a0b0d05030a030b0d1e14010e0d080a020c060115030207060f0c11070e0403120b041e0c020f0307060c02031201230604060206041506170f100504020105 73
    0x180a00141d00050410059682d0f6840c480900d0783d2620100017902e40704e90069500d641451002508490b56101e4450040c124401c2103000210300300480260604025110141c0d0070b882d00b440703803140c1c4014640c48000c0d0300e09511140e031150001008031645100e65241030159482150300c806a00404034155443d610190052118144090482c0001100b5213401410891603480700003d0f5642c02d41051102c1e99110042070b1046d50190790955684250300c000c206041c940100034615000050028003003007204905901c180d11550814603403003100400a0207504d200407043d118078602e00a11a000c01c0c9003c251034507070f500114280400c00c40380e0001d5414280e050b26000090300c001c0c0002c10442c00100101700c440300030722003018060300e609800e240303501a1a40c4c0051003510303e11800791003084c00f8042004610360015203207602641c00161300b25042c0001040101034011604442c400c0b40002c920b40a125100007504515402d0040840e0003140c20302c0d16007000c846050347c001c0d00040e4104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 721843839 1250 721842589 721842629
    0x304050622020d11370e150103020f041706160c110d0803010602300706020c0114090c19050f0603180a060e1c05160317090124 56
    0xc00700d407000c00e00035a41d220044c001c030400500d005040b600d03075a4101901802065507110564800320480c018910b8050002e402d00000400c0844010080800c0101014210100da4480d40507a00034071303904032503e52103a845110250304d250b001004200d1502c20b0300001101508540495040681c1e00d44441c4150031954071a41130369031201406a40007504a0f120300300040320b55000f50700804d0550301518028034001580d040403d07035100d4801c02c2004800c001c03000070002c5002c84202d0342e0300203030043c0c0e5160f1003000a40900742e034840415400c1c2207070f400c016a078040070520901c002012610f00001001e4035a413010b0340056401115002007000070b01d070f07116045ca200156000b0400c038040202c4d00a842a040349040840351040314056180c0e401541c0c1035400f003029421301007103018070212800d00d90100600b070740181c1c0e40b1410032008108240b411706014504507804000d100000814510380410210b000c3c00c0d00200440b61001d404965450390280007409105507940c414107600344610007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 721845089 1250 721843839 721843849
    0xa030207022e03060e270303011d0705070302060a0c120c050a1106040c0302010c0c09051e1e150f03031b0f070303050d090215070b10050a1d1f0803030405062202 71
    0x20121500312840e046c8242e09096200700051402064001070852141402c001c0b15801d203003000d80108180b000a00c0524006600400d5a6038004081d0100207038203502c80c80200c031901124405401d1007858848042501d9a1000081140c22035544550950051881c1e501b55a001c0c200c07005004003150207802d1006601c42c109150126000b1203803070310b0b15525075240e0380c1240d600b0756a480c0d054280160700c0c140b014440d500c196002402c0317107000482d56900c0104184220000b4124142c0300803240c1100000d584442d46110700700000b0b0300700ca44410301a103002c0c0c4c0c02c2031114100d01081c4282c100c4004091800030300c07002940d0303042da00c05040c440604420b4000e0002000c00300d83c40540c2d845c804425104850262811900030301ca45181400c1004410082d0030040d0840350107071860700828015a000340f0001c01700681204240708480d40c0b40740301605103248041d02c8520210100d00001008000000a12b010764017550a8442079100d03800d028040307080040040070f00b00c00d0310411102520704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 721846339 1250 721845089 721845121
    0x6011d0102060a0f0207050d050301140603360f07050a050303070f2d110a060305062d09131e0b040f060608010f06080c091b0a030207022e03060e 64
    0x102c6130f025040c0812956074074107298092007140c0010740301100400080010049801d52440240c1ea038a140d8104039182c0744a910070980c0b0a10041c215400b00b24a80008450742c0c02100c00240a039000c0c0e100ca0007456460355610b2045a00c40c0c040140041514174000c0100c46ca0301e41c1c0f0054030303661b6a1300c0c0e94854030702c0c6150b06024000a62082c2064040c00030b10034000c14070341d1248062a140b072142608100c44c03904650402c03404c02d4904001c0000315107604210030301e0f001c554070f4084000c080d060100c044407100300342000d07000034106007840340036500e0780b001c0000745228844070816985843c1c18051000c0d01c10201030710f10301c1e500003c2400b0505161800c084240501c401248440e2500f03602800d43d898404c01e0b01100f50b803201c0c2004000b03c20301c030681e0001b0381110b04490380d0803c1d20b42201006600030703001d100000000b40f0705070403034026070403900d01941c040e04081e0803000c619042410344c203d40c003e5006420761080c2d00001c0d1440707449a102a210b00382603030300c0b03642c07141c0300f28211002c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 721847589 1250 721846339 721846361
    0x3200606010c1506060302070209090703030207140d0c060915020313090b0d0c14030f060c0f031e0903041a0304020a09020306030102040f090b0406061b030c0c050d05010506011d0102060a 82
    0x600c0d9a61a00f1406003405a540a88030f10f4031301603a24141d07441030000f20b03c0000d040000b60b4102d83c0c0b0a10019038085503800440ea40c0250f102206410080051104c5404040003094440c43c2c50780040da160304401c0110440b41c0140035501d030210a00c0c0240e84900c5409650704490740324203000d10004500c0da0084107035100152004010b80c07043d81e07070001c0c001410340007401ea20080d200c0d00800e130b00d01040044e4142121001a0115042c01324012455004001c502641c5c104e0100004081e9080c12041400000381d801140b0428103204180c951642c0c4075008043d43e50660303101607400a003141c81183d0080d90b010300a040024641640440290006001603626540800c0006810301c00001a140501008440060744485140c204001c6584640c84903060001c548281040f210305010350a009075054201400c240300759280075403640304281c12082d0311030003190483e401e2020541c0064441c034070a0320740980705a003842082e54108200e40315580180d1040d00024440b91050300507000d041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 721848839 1250 721847589 721847603
    0x120f07060c060212071806030605150f091e010f0f05030604090615170105150a0e0415020d020d0614030a0303020c0307080703120b0405010515031801020c0a03200606010c 75
    0x121030984c01c4e00e40703da09550f007000140d18030f101b410b0070100c6410414010001400c04100c3c142c030b41004036010704000455818002e0340032560b5045451851704031100140c0040c144820055606d411011044510b19280d001840b00c4004020060003030f10307290740c80c0c6801d86405045070340c0d0108000103001001d204940564441c03025000c040c03800b0fd100d00c060802ea0141669074078000ca5024219071004082404105086060003002d8403001000300076600401c10950385a525808c00c0e43c000f58401c0c0e281300e855480014600c03080101a4080d00000c0c81100382442943d944895180010b00d44d000c0c5940d05422104034400042d0081d402080101c0070340c0c00f524144942134548c01c500b500015420350110b120a40700012440c2644980b00d210302c0d00300d400300802d505020206400c40c07002110a070300c0a8001011808004403084e580701d040d54508000c1d543c640c20b10301e00c2511400c400200302c0120703403100e07031550814104101054096200000030511540c0e0580112a41142e001080e5070708 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 721850089 1250 721848839 721848847
    0x10c08092d0316050108010326030a0506041d03030c0a091502030a020f060405100906180c15080c18010c1a01061b0c05090709090e010b120f07060c0602 67
    0x1607120021007488103500031106107641c1c41203001c1c1800c000300315055808580b06100c0610480c6c1e00419000d0540b90410320b001c004042d240d604000b2041c1e100b40245002c4000700400c10b00151942015100b0701c4292802c0c810f00b24080c0100502516a2010f000940c100388001040640c094014040c0d025075445c1030500903a40d41c206400d40b001c45410713a0016000010715070f280300c0e0104904801ea207101c400a104510302074407500d840380781503403148068a8550382d4031810b0004903081608110110349001881da6075500e00395488501c10311800494048906450700440d0041594502c01c0a40c010064900f210b8290855100700644440b18103200d50341008201243c031140340120001c60325000c00c2c0d1031794100794002e0054011038803280c018450b98013250b000241e4004500084034030690b0620342c2c64950041c1a9004181030b0041c80c201441c0ca0810500728005412510005d01d0550f021240c051010035190344854809402440c10341c86074904100652142d82041c400c1c602030303a001824 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 721851339 1250 721850089 721850119
    0xd0c030305091908030c0c010f050f0315130b090604140f090114070c0308060607150c11010e0715081b0c19030c0516080705121002120a0e030702010c0809 68
    0x40f600d584c001a00680c4041341d4409045410483c03144c10840900301401c20b000c0500c0c00030f08a1092048595058030b01001068144c1c040d05615a0403e100900423006c44100403c00b2008120759411140304403503010114480d07061500c81d00413900f0654401450640c0d54580c0d9600c00c0c02701503d0f04929658880c070300c141803004807104c54040c80c0940d4400d0714840c41404c0c01400031001809451040201700002000100d4000b15100e11301c1d01140b02142e400c2c805001075400080d520907441c1706509000c001c003d1500d01140c02c509442c0000440b80b101503401c402101d08060480c3c100038044d0030705410030781c65510300c070203004845580012515a50022051000d028014400850100b050300060f181080300501401c103210104c0e010354540c0a10705415556103898500c03485000f4551040d100311f5030f510a0210780a441900e0748103550b20260000c082180c10802c440b000d0b800f13854200c040101040102c2101d05a036016501c0d00d55580560b125240703030b9070120300c40980c005a04041014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 721852589 1250 721851339 721851379
    0xf091a12131203020306210705030313081006053a0b040308060f0604050409030c0f030512010602070510030b040e01140a150503061612060e10050d0c03030509 70
    0x489112950105441c0070010710708490034000c10b0440034141070041c802c001c100e0707d88200402401280164100d00c450034005a603040c404030b9000316805000000341d401700748401e50301010031103589604861103503813010a80710441e01903015a507402403104a0202607a0340001c0d003581540c0321003e0880044103200003d081e0000403000840d0001c02031410481456003101e040769210f0015502441100d001e540050941c0c0700c2da00a29114559404040d000d25118805122100d0780c04041005582000e060103010390f040003081182014072040045012407000c110702c821500050280300089440e001d01350301400c003107401c19070000d645d000c81c10400c400900615024000c05004243c050a0002c41380303040d9016500035001e00843c018003000f9513100001d040e54801e42d02e501500e5080041c0004442c02642600e40148032030038007e0200c2d8040a081425008018100b010340d40c0540e40c0040c88101002260040c02c0d0034400030042000c00c1c01400200300d40000203148004540142203416 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 721853839 1250 721852589 721852591
    0x190302150c0109230a03092c0c130b0726090418110105090303040521030301080c01021c05180a050a0b0d240b090d0b180d0f091a12 58
    0x501c0d22500d041c130703045100c040b500100d0350380c8542401406000310a51000b605059607441b5032552459291a86402038442c500d122070420f52180061016013002a203051150300049c56010030352800c00340005900311b00e4012102916401003040c11440c0001c0300442c0c0c004170240d58401d01c100100998401030f50707103100707219000c0c0c00c01e6107046481005081418980742030000c6507052001c01c00102a00d5900041514115542181c844800034078080d00d0140511224032506210310020001040c80300300440c80d5252420280d08451408202e152520b11000b1b4010703503080412010001040c0b284403007501d001c90444040e150b01320f2155904007140020545600200d041800800c040c507410340c05009508030b035184048580322000c0552441000c0c02854030890640640008014176a51540c0c0002482550000c01d40d01c100c1c5041d0545038040c0100c412320b100709006000154460501480785081120402d42e50b40c05000e007000034540d802c01c01440420301d8001e0520080d081c00110204032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 721855089 1250 721853839 721853843
    0x290106030504110303160602131205030a020c061809060f0909070513110927040b090d03060e0115050d020406020c0109120b0f0a020903100e0c190302150c0109 70
    0x19291505041011007200c42e4003c03c3c2c0300340c204000c0079207243d68070402501c0b0035400041c01691459490740c210b0203040b059220617241e14140c0c1d00c00d01441008130203000909400d0302583e50324410b1804000c29440344035141c0e1680d10301c42c01e203841d06041c240c2d070256000e90080c140f2070240440e04006008031104031004030881e80201401e00c031078100b12405400b141220030041c084220b034610101a1070080c522428050316102e48280c040c0c0d0480d6100340515088800c01d80940c1c1060b090001a40070100c0301034078140306074984400400d1281c0b080100f16007201d1160030081c0d082041003010059280b10301c0041140a102c100115079071440204000e080640050039804519000900700401e03981c84600c4100e000c40d0700c40c01240b010031441d40d100720704220740107440c1c2d00d68200c00001c0c007528102b580c143c0b04440007040900d083c1d0b80440410140a412103030201080b82c00c001a202c0b108007070800c108001c080410050030400b14210405260480e410f08003250503ea56086401e40c1c002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 721856339 1250 721855089 721855091
    0x60d14010e1e01060806010806161b0503130e060f0103020309150a090c0f080d12020f37021209040b15070204150b0a0c060209031204150801080a29010603 68
    0x109002107400348074000042c0b605c04098a840d62406c0942611032600900d040c0605140c0c4501010062160304161044000c62201c2e2060145505001d41d8135041015841d01c20754000c04c0220f11200c001000500c00c4d44c00409103030030544481c0044020750000740c80c80c0c0c0c89200b04107200354032407840c000c8140b04030120440020040200d0800c02040300305a8030007241420003002c07d200034800400c04403404200d50800b911000803441990009120710b180507801010041849203080607118100e40d80d83c9410f031529109a5074034514101b030b409990028001503400020901c030144064030103020b8490300240300059210b40300300480d4150702c030402070740c12140e030000324501107141500c541c0c002040c41c0c00c107025070310703040400d42c4190303202c0d000800c2d05001da46003d8104012441c0c0480720003900140c1035413494000d01106000540060140c810400895055180002d11031792220b4100c0d4110802040d0b8014240ca828503491035490380d0b001c14110210b01805001c00e18000a4000c103101e60b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 721857589 1250 721856339 721856383
    0x5061c23010911090601081f0905160306090209010507110a0302030316150204050109030222020c0a020112090308060d05030d060e1801090201050a050f0d06031b06030203060d14010e 80
    0xa410440402c0700c01c01c0520030304201c82401700d01d0764047c2d80b540d40b20805400c084003652594913404810211540240c070b40e94200010004910514074040071600d5150303e05001031a25481c24106a000340840d05001540a100b00400f02d41d40c0e42039140100e002030165050240c482d00480e0465018940742004003003501c1807501002200b030f80c14580485050701c110300741400d00000074201c1e091440040c1c07184030347d04010b01007012007080203d5a26401007046544d09a2192200c2c2c4501c0040d10990100b0541d83c21004041082c0c09641005a410358502c6c0302a40d81804020325603807511819074040c0b1081c03080c4c0115040d85d1103010050510300e110702080b0b2901d6156a41030381c810342580f40a41c1d040884080040c2d82101c1914890011400c05540340c26003500c0400c064014000c210100e103080050000c28850480d58a00ca03062100c0000d10030242c03201025020782c4802d030740c0140c101c510130700c0e45404250b46401c4604036008100000c100b50513410400340c41c7c5166903c1700c42500068030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 721858839 1250 721857589 721857593
    0x705060702070e130b0403050c0d08010501351008010c09030c091b0509030312040c03050d140904111c060e07090503100e070305190c0905061c230109 66
    0x100c0e50041501c44000c0e402850204265140c1384c03c562002003264200001041c06c060143c0c05644084004008440305002e6820006107400d800380305e046d001c40e000344a05040c5507074240301c92024030001c1210b00c11415100522645181c0000c100c14040043c2e8000071513107030000e00818802050325511140540e00b5410701c0c2941110315446410914a091a460a149070302000d20402c2c02041c1000c9490306400c2d40820304500c6843c3c1910141d41d0b058081104200205803c4015240114104d41c604e0403004410340e618600b00040341107018041c408106c0c01e2074282c101018503601c11181031305207a0b81440c2842e051010b840003402c400c0d1210000e116100c00c4180ca1680845140b51105840c0d1805001c60b451b0841c15045c2e00e5082c1d100c032014a000c880404c42e41d0011580a03080b14402882c01103180c2c5c12842048080b100e4410503200001d04d200c450207017a002e01e400400e6180c5c1008a101c1580d40503000c103404507803d04d01140114641050300c101c01c0c0c00054100008168201a8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 721860089 1250 721858839 721858843
    0x40501030501091802041109030d030207060b0f0913020d0b0708091614090402030c150d0e06100e0403090f080106080705400213292208030705060702 66
    0x160000f50070b01c0e290009840f0144149590445401d8041e6000103900440c4c4413405010702c20340c2d0f252501031050b80403403650251325a004001442c004c0d502000410340792010440e50103030f80b41000760310007044c6010600c8840001d01e94147d0510003071480341070b01420b544113800c021040707071420045159030040241c5440203000c191008071501c8040c8207030030f05084038810800350000f2070074050002080081d00b1902c08120400c1103490040c1642c94504203944203c2c500d0388202d0304000706601304090180145000164903020f0000803030020200d42c18880f410030f801c103004109408018540c4030010b400e0807035814480252141400104050342041d1031103240482903800b16020b10321145400c14248540d10680904884500000540d1560380390703a03c10b0914013000030000c0a01c0007980200c0b0840d140c400f0030441c0d40c9100043d010182074610070210b900c0e02c041c551480c0303604103c209c1045100c0003085031400d07420324007104030b25101d035000c178a1034100000403251940f0603001d02c0205901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 721861339 1250 721860089 721860091
    0x105070e0102190b0a020f070b04080306130e07170a0b0903030603010c1707051c0c0518040507080402100c0c0f0321170a092907140316020f030409020405010305 71
    0x140003054500f62085680303111a0a4004100704c20541d400f1589050b980768000440381c5680d0001c018500303d05090500111651041d00d041348a145040413844a59910b1f0041264400b101c201400d8004c1c81e01c0401d6032030319400ca1415019000d605c1c88040000d0446040c00c0c02194102d008603120715000c0c1c280b5003140e80707140002090041e6101c0008030b41c400503070380c947d2004451800c26202d440c0508000706030a194000c10030600d00b00440038180640c400b015003490f24110081151210f8441c06000484605640c0c0d4000511300c0c0c00000d01604202c409011030340400d24014080040c940c44184000c150784d000241d025284600400c1130041d41c40201018a0000000b40c400111300c840181604440e603200070315456044000a81c01c0880d5805411000d070080b2018890f5240c88003403005080241900c0307981018000c010540107445000d401c1c0100c040840141c1ca561511000c4152414008081030214403540c2c0045440e80341c240301601c0180103200d409620b0714140703000074043e200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 721862589 1250 721861339 721861363
    0x50f010315022b1d0307030905010525150e0f060f010b030123060c2113050418061d0c060702060414030c06160507050a0803030c0d020c0105070e0102 66
    0x401480301e0180f0102d5080c000b00e114070b0b02d103d180900c01044039190080d05580d0502c00c1e00e0800781c1080031800b00c001c401060094880c1e51030251543e01c40340103540300d000d52054020400d0158020340d0302c2c510741500035071685005103981e00c20710a00b00600019181900382d107500a400148a60a10038001c03c02d0a41080700d07508103c50f69814282c513070100b4001403040c40d18a090114560458460049901d000014081d011541c6c0d185032400d1250340e218840c444011101d800d200042e0211090415580115075002c01d00c80ca0b130b464001040058100003480700083c07101c0c0c185200018442d44101d02d021407114200098211030980030230309103d0b980c84076034003540b000c00010005a46200840d002e8403003801250031048120408649008801c03840700307402c2040050320309250074031020300500d0244203408403040310361907400340b10075840644100e00f0300d544140040380d900403a6034090501c002100d60700600f41b9103071106440c299002036821101003081c00700844203950b03060000d02e03420705c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 721863839 1250 721862589 721862591
    0x9020613030611040b0a0f0504030236070807030b060409020a030501150c0b063106080106080714010305090a2009072c03160305070e090d0c030f0e04050f010315 71
    0x6181542d803030702c01c4c401c101c10002004440f40c01f00040e14010002c0c0c0c1e020316005007200001c41da0070440e900120aa4402804510800e15480c072219a607041d0312a1058005d55a02804c0380c65461060740508141c90400750300200601c00800c0c00f0010384003a1002c00d1241d40d010850303515040e00c07040780c00d00c007001c08000c0000380010b001c0403842141382c00384c0082080d12046905c404000d064042c45148000c0c1d1000c070f441300100311381c600200c2c0d0002829503550070000c00c2015610400d1030b5480b00144500450301c250502c618000358001c0d4403080d8001c01c0081600c2c0c0d140390543c0c1d96500300151800b908025941000304400300e0820f8072105612640d1401c01e05a4500c40f00c29142c0000507070b01480e80296402004a02c1c140c90500002180780c1d410b20303118004644a160464484415008103019001282d00144824100103030318807118415413030b800304211060f01d00711100e12202c0103007024003101420051030754690388200341c03041c01540880000c0f541146040c0d0401c40f03c61401e5041c03d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 721865089 1250 721863839 721863847
    0x1170a030507260304060903110a0c0b031e09010207060c0c080304110a05060a0302030f090a03090b13030f05010c0806060306031b040f060e190606081303020109020613030611 77
    0x40e40050884604907080090761601d0b0300f41c0c0010050050214051103624403021050004101c201c0c0c2040034031764440c7e12400642182101d200d0754811080718090060b01410000b001442405402540c106404465258594000b100c3d25000d003203061755641c1150b0750000f054010721803035100d910b90b01107940c42d01100403281c50701c038000039000c080c00141c40740d150820705140c6e41d5606802000180400f420040d1100301c4090050005e401c21120b0602031014a4001b40411001052404982d5455152004031904142004009402154a504000040c20000310108000d0401c5804c214031441c0081414260300400030403070900500703054003404040c400d10009603400b0400081c10400038201c0140b00d079604001a01410011656001c5c480c600040814141d0041c0c00092007681c1841004e462906c4615036001211345920440000540c1480032440043d140c05504100b10301a200100e0030000540009030b6950140c502d00c4580c0703902420800801180d07025500001c2901c520b00780c14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 721866339 1250 721865089 721865093
    0x9140d03141006110726060a02040614070326250e040b010323060319020603041e1b0501020c030a0b2d07050423010903020105030a0908030c0301170a 66
    0x40b000710f00540082c03180c8048400e0800104008103002024400d5000c05001c8450f00c034114961000c0000c56803030b00071a0001025160b66000f168111440c07582c5440242d0300c8101030071095000a40d04074204800341c070302c4058010401060045200d41c18803045460b00b003800085070815072001e14840c000958800c841d042540003000302c0c540c1c18040e0b401080340080200101e006017511103d05181101c0a00d14114a440d45020b06106480035411103140131200003000e80200210000254003410030000540094461142c8580d600c3c4d030820f0740c0413100b8196444800b02e070600001c04000c801880301c00c0000d50780c100b0100c4001803044c1c0281c0007004c41c544031240c40100061220202400d2461441c4881d40141450f440101d20b1411038040e605203c00020060342c0180304609124000c404503d4071b141d01d40c005507585090503183c643d072140c81c690040d40d00d900001c00e980c54842d620b8134032802264031000250321810b03200c103000d6034075030500f40014102c540b40302c15915070345d009c07508000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 721867589 1250 721866339 721866361
    0xf08060907030509070f080703020a0803180607030302090d0f0204241403070312080f070e030c040e0c040222080a05150901020702100f120c0c0803040609140d0314 72
    0x50881c40ca898040f40c00d5540d4904180382032401da000101d0702070001c03030016905101103480c8007070301d00c00c49256a02c1640c1e03240c07003640c0b40260003082451403400c00001c401ca14107500103141452003414094200b80600300010083c940c07101c0b007039034443c80501c181411454a8441d400803503299084d0040742c1407400142c070980322031a0080707a40baa903c2c010301c42429502001860011a403041c080710385444440d6004110349800d54010201124007004101100e000c0c040740c036149140a001044003e0010702080042d14112404200b140201020100c040c6c64500040a05179021101240e03442190300702c165004007540c0c850300064000ca141d074000140041110414420311460050054441d4400a4020712440d4030081d4000c1c4501f1130140c0b41600004802004101d980383c624003500742e40e0500e003d071042d081382000061a1900007200240f04d5070045c5401034000c00c0e0014102c4004d41c1e690401403008010b01281382e000d00174001007a0740c5801808140a410800c1403107030f0610b1120f00c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 721868839 1250 721867589 721867591
    0xb030d020d021002070501140c0c060106020c010c03030c210c09080a0807140f0105010f0509060a0501020613030c06020301090b130c080c160b1f0902070203030d0216140d0f080609 79
    0x1e60751913000180501801000d4009080414520f0b80f03d426904142007510000d41c000c0c1941d0002c5e00a04000107030290000c6036403811010103031140c0c0c0c40c100d50340c0d43c204c00415011012005016091000b20010807862502d000d1001c41c80000141080000e00e0142c074010303244d40020020b5010101d03d4000a60010551b200781d5031010340300c1030211090311810b04080c00c041c0601da89600e000000219440002d480750b04840c41615501101d444a2042c003403205454021180581e10580c085000c01c03880c01100e095041c0217250240104800703545030b2080e83c1c420b0340458002511642900414a02882004401c6140b20010400e4205018018142d03210013414002c071503101069080000e484008c22100141d070068900116181c1a6000d01e00041d400071154102a070403e40032a030381d035036031080b206903e400800071824445d49034401c1e406540032110001c084d0307205410650005400e01d00c5035500c1101480030b0604d840c441d4000604594400240c10b0030440d0a00038810240c488095a03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 721870089 1250 721868839 721868863
    0x207080718110f070c1d1326040e040507120f03032a02010504053702010203090306070503010603180b070c1b0311030d020d050307050c0c090a0b030d020d02 69
    0x81060201c48980ca911800340740440300a03008000344c2c1c02e0070000803500900c2500c0741d080c0098004655025424064001143c181e194880b54510314404113030011800d05086410b210740c0c3c03841107107456100b031641c3c001340e102441c403161180521040020911462024041d00407003442041c0042c0c54102044013001030203018180c0d640c2112000340f00090184050380b068100482024020382c80003070080c0b0084030251040d00400003880303e00035409400303403055070a01210380ca211064055104540e03000c4401207043d4481080100c0d0903403014000a442008a511490703203e40c50108003800b03541300f050803016055000030311708002401001c45c41d500080c0724609a10003404a00d441c0c0e0010500c0d2281e54800302480d140041000a420b680e9011000d0690548207032861310f40059036078020a664040202d1401c0c80000c0c48188264082c00c0c00040c12001c860702e2085c4440400d144d40380541c0e030326003201d450743e44920b807900b020846ca0642e00c031188000c003005c00702580d009448135184012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 721871339 1250 721870089 721870091
    0x150a031e020c1209150412120203032e08070e01150c0803040f021912110a0305060106121e0504031d06030a090c0306020a02010903081b0d0e2104060207080718 70
    0x40303107540c40d081c5a04241c1d641703404442d5135546d00c500c100e46105c101c0110403180c1e8002c418207207600d1403002c401d40c1e005035500044807a0740350030a8418000d03070903d4884211300000c500d20014541e1020441400100750202044503694100080e4049055a0352041d05c117000640605031300041d0f003c41140e504c0b40d00020040051030003840001c481c8e09042030020030300c400070130300803030300c03e043d4460030200074425a00004029407600500c003c1c0340f140d2201918541120b001000100d006000c0c0005007000c4603000103494000e090440131070504000c101070390301d03690000c1204140d00807141c030540307025018902c0c0180c0c40231800202188001080500300580302c0c890941000b04071607880e0f000d1a07000130195216648080001d00030035460304c0c150700085400d00400c0001800e5003280d5650380416550741e103040540c00c6010050103254800da404c0e4401c0b0403e0090b20042c2e15050b0303140014000000e075685190a100134a04445504054040d4001303a40c01c0008031401c01c0c1d86403c003865408 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 721872589 1250 721871339 721871347
    0xb070305031513050118050415050405030f0403050106060e121e010f020301030506060108061005030c03070e121507050c0a120e150309011503020102060f06150a031e020c12 76
    0x402000c0440c91071501c5400c403c80c2203403640c601802d90800c5040e40c2584805210610100c410442581e0007554003030481c006560f8000000d045640010341d00c58051000c503841e015080d44049040d074003e601c2a83d10703954880c424055160b0100c10702204d010212042590941c01a0b40d503511102d020442016030034591040d409040b02c01c0d00101c600c00c0d2003440c210345075070303407400c1868031540c0480341140012000c1d00082e1081c40d01c52601d000502440e40c5040c00d55030340c481900c05079032019152906202040c0041c04155640c40103400b00c130b0340340340098151003d141c1e0803442013170000751050007404400d020650151000107054001d05800031854802c03034600b030b08282c1d040f8945241e40c1d600301c0920f48004403041c889000647c007590520008120340048c2c066000f0055141d80402401600f01c000421043e9120b9501540c02c964000e00c0c2002184030101101121703403003c40e41c0c4000c642c072455410010590940340350400507036000c055140412800c0c0c9075850b200d21000c0c1d0320304514042 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 721873839 1250 721872589 721872601
    0xc0b0c1c031b08060f15130b0a0210050c04150e010806030615010c082214040506010f120f020a02011d061308030405010b062b060612020a02030c0109140d090b07030503 74
    0x81e074070b0129a000980b00f041620b4030050800503d50014141380c2034801d0480c2c00107845640d00003142c0881c4410b90103030240c00d00000c00f1801030080370748045a42c49040c04045002e4803000034403003103180b050711000c110200303400014050000040c81a48650003060820661421a0031440354400003480c1601405141d45084515401068010003050081d650465041c41031030f10080e043d6a61525100c0c400403c5c001040255030301100e40c1400524200c031088100381c010f460380845020035020109450040f14103104c202d0304031807d4000103079101c07420640c41142d501072001803110b00c64007078015468141e40c051000701e0b00c688000c02011001000809100c1d0070751140c210482c000741040d5a4240002804c059006400e8000004030004a00c100041801d031040e07108544c2e0a032103080102c1d4410300000000e400858040095010400c14021a00022310500035207621500212031442503140e140d900c2d100c1241200c2c414405444814031442c0908005e4588950341803171300e6944c950b0340c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 721875089 1250 721873839 721873849
    0xd0e0321040501051b01060305060403112a0f0d08041a090a051c050a11010908190618060504080712051602060703140310080c0a120f0c0b0c1c031b0806 67
    0x2041001c5c413107501e40b600103c10000c0201e003682c09603001c1d1743c52044451061091644644071515030740c4800000071345013840c01d00c600002d5106100001e06114000d22180003040701101c0c00c00c0304590b411b01c00101400b9403042200003805104603500d00d42c1c1000d00100200d0044480c50180d00d01c551100c245032440102131060980d036050b800402e403000c1c00c81915204080d07040c01140305010514940d40440d1481e0000783d074240c2d0343d038080c8a4029200e1282c6a210041a4111858491144c0542030f100400c2c40760091078000d9100d42d2400d075403103405091900395044408480030030048108500c0515000014034840c5076074049030788650303484c17852a0584045c03030030241c100c5281c0c80110403c0300b9038100c10100710484040b4400d560000355403104001301034609008401d00c000b0b03d518000c01090500d100da0302d000d0303c150520703092a512650204202d800100e180c100c643c0c00444910f2625076030756001c40405407207007420302c00c240c3c41c26545c41c000c11307843d02d001c000c00c01d80c0c0c030018140e503a070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 721876339 1250 721875089 721875127
    0x20a18090f0f020102190506040b0c0d1103010302040b0603010602030a050d02041a03040b15240f03010b070c050109050d020607231b0d08040611010902030d0e032104050105 76
    0x200c01c03140300088003180707440032840c4490038082c3e0150040c40700c40c43c0041710b15940c8a01d12a4000c0c080d0145035280e5a41d03c06a15001e0701c1c010549000f07120820200c45944074940d0001591030200761698035610400082c0e50510b00d1450042d10180300400c00140c0010a03035020311090308115072505c3c0c0f4004008000d0140d54030450032280d4203003094411069410045005034001c00d1019142d640e01203c14010901208906800594199aa8407011032615800c0d0305e00c0b03080c01c0c40da441c0100140e1804031640080e0041d04e489a030009802040010b0043c1c4940103040c01e08118481ca4035002c001a03000721141000390144070700064600400000c20301c4031468140c1c513494a5000c401300c0014135643d0495882d5104181b941c5c00402c544e500d842004051110780c094007407807815081a9048407030107402040c0030703265921407200d113005a45c1440b212194840c3c559030780070141c0710082014600203d030031144032645c603078010402c0b2a2885400b184c080d56001e00345aa40e030744084440620b03c104d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 721877589 1250 721876339 721876343
    0x10e07052106040e0609030d0b040b030708030c0d030b010210022521030e06070e19091a040b0102100b030c0a090537110c0a030201150909020a1809 65
    0x1059503020302440003051600c42c000c03641036600b000500b00c49508595901004e64484000340d000307200700026491a60415020700002070800b02e283c01b0321340d001c2490328640b50495031098001040d80d031510f5004216a000c8408286000c0c4100380c00480040c0d110850301c5480d941250700012103448024107140203080d00c0329150b180002d400e03403e040000b80170b01c0c1242c2c0c9503d040282c00c944101c2c58401d0180040c0030f803145c00030302101d4460385400d480c0900c1c50039425400282480c061120980c0c1e0600c800020400f1090100d1504040407442030704406440030345108602d480000040e07641e0001c1c1100091643c0f0303200280380014180060715040810b40c50351f50081f200300c0f0200324048641c01c032601034080ca16190055009041c1071100031120301074425a5444500503207071201a05400050b11034202d040c00074035184070510714500380310024809402513174541e0b11400007000340520646c01000244420000f1120581c00100046103c0c403c1e4800716003c003040c410079103403951107140299 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 721878839 1250 721877589 721877617
    0x3060103021c05010f080d05030112050c060304060219210f06050d0303091203022805070b0405031209071d150432040c15020a1211070504060806010e0705 68
    0x310701078200b000a80000d020302110402400d40000342c162000440c00100100da440702c0d0b04684c01c000041344152802d40050f40d1511440c220b442c2e090322100001c601560013510701590f81c0b518441400d81042c580c0c2e81c0c2e9010010f0400100b519100500ba9003410720090b800301003501101d801c08080038280540005a1200303500b0307822400c058140e481103041a04c9007040c48030a40d41d00da0700f50202d00480c030041003408002061208100046031004041c0880d41c02c140f4140400c94541e00b5030803034111000c4445600004d00c000c07440108012007a4812843c500a0403103904043e4410703007a6092800c600180c4d80e804000c15031003e60f0700c0000d600040040c104001100324844002803203d48800c03405907441d4068181802d001075010310b544116084441d00488518100841c0900d0031810500d40442c00348400c00c500007100e020140064a01c00c0e906d21010720087c4040c02d050003002c1d80024815440c1003410003c8560210361203044611403031300640b107965400701c25a086d100d80000840d0003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 721880089 1250 721878839 721878877
    0x30a0905120a1e0201031104050d080a11030d09050105090a05030901031503121707020106231309080a09090e06150a03060905070f0501020c0f041a120703020f010c0b06060306010302 80
    0xc0081c0004080c03c03076000b66814403a800c0540f82c044aa80300f280241900300221000850105003483c00401b026201483c0c81d40c1c40e10150303049141180c021145132151240c51b4013515081c44024001e9a80040010015025001d100c0d5521540c034814054464181a01c452291000c0640306a840000b15040302c2c4070100a02c00e004024082c11002c4402a00205d1a4000c9624940b05215103000c0d1034030348448800d1a11280b1206c02c442c9110003909a00002200700d13001003104502400c00442d2185002944400c1c440318050401c81c0d8540085a141c0d1824002c3e00500100044440d080a01c000d91101008501e070003180014045400c090885803d00782d456003000340c00074082084540172214620213a4441c03004a84071802048070541c042c0411920756924030f071551062003c849420703105045034a00002003200850741d2000d04100d03030031100b02007003541005d000d164030960013440d060340b031149242c2c3e4008000101508007405080040300103109a4005d9044509030708041e0850b14003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 721881339 1250 721880089 721880123
    0x180112020903060a0c1b1e08090618090106020a0209010e040c170a0b1509150307260106090506091504090605010e06120d0210020304150c051209030a0905120a 70
    0x60174283d40400d002900c410800b0115200e54450b0503091580040c40000c0c2045814010784070700c450071b1080c1c4050208011a850a6071038400400790940307544409902030029108000c803015050344002e003036400a0143e040140e40d0101c06038191440b18082c0c41c0180c4490038184145078541e0080301d401c04065010342c030a000c001030074000c000e104003c10881590366901104001c200c182102d40c001e0550400710701d0583c50a031040c80c0824020701254003035560f40c0c184849082118620441e4801884410f0f05000300a01401014240f0202c080c443e41c01c040c070215007145d4005260760104050008410403540e182c0d0002c1c0c0c1086c2d00004140120750b141d110141c900c40003034524a110302103007813a03034440c20740c082505101d40e00260054164111541c24400195000130b00480e80ca104144c7c55640c800b074684035482500740303103a403030548a24001c200080c00001c05400e000c07940d403043c0081c503802d0390300520000a4410650700701102d2800141a0f03841e1491420004100541583e130b2454 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 721882589 1250 721881339 721881341
    0xd0b06120a0c0f0c14150a0e011a030d050c10110c06070c080d27141014160e04050708070f090e070807020f07080a02010e06180112020903060a 63
    0x20080c0e407510020000c0000502e01924580d500c181d11001113103030401104045141c1081400303080c041c030f4059504094007a603840f400c80d0005c5134035140c02c555464a80b411403800b446043c0c1d40080340100a0490541480000e5880d15098452000c0240016108401400501c100b000c00010b01400784048064040750740099041646126500d2003a01c1c0054041c9100e03e81420109811818840c074200344030309a4400750608116092602c048540d041318250103880c0100c59490040e02c26402e24201c10343d603a0b081c20b05030305200b007049051414003a0181c3c4174000f425040b1028480c103107500b24080b081950006030f184007007588249020108101203401c1284988907002c0703640e42c0f0072411840c900c00e0f01e14005c180200e000840f00b010005402c1c5005040306034128501d40121860160000c01d000e01d005015000b0000580020311180c085503000147e004000004990b40c50038908840c1c801c40c201174490a1050402c1040c40d68030700da0110790f5040714060900503060b500c80d4600300d44010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 721883839 1250 721882589 721882591
    0x8280306090e1f0e012a020c1f030c200706031805120a0c050607021f060605270d032a050601090b03010219080403020d1d060d0b0612 59
    0x5141506000700c0c0380180901143c445200708291a280250680c91014400101141c18408603d5980c50f000441c6d21802c05152a20f0104250648001c10309403040003802c0c180306001039405409460742501002100c80041032481d07001d4680051241481c101c1140c4007140640d1890160700d00c1a2002c024510201d0040241c407a00c0d02c06112503400b480780191140710102000c2c046030050341d41581102d80755401400048441d01c0c00848462443d1281c904001041c0c032018007683c450800d90410b030480c00401b9003440418441000600e25000b000b900e244114401c298001d50b090058541d00e40302103161003011900a041040050101c0c600900070b11404006052010300c480b124114040d01a406004060f51080241c03a40303034a0184c00801801d040d070110ba0307241d5001c1c007002c01100b980300141c0000d0783c110b0360342c81a18106414040d0500800b100c402c0300300b00031109014038204070700c80320440c50b050a641d03141c3e55406082108000b00541034516900004c006020300381401c0000d001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 721885089 1250 721883839 721883849
    0xb060c1c080112020118030209011806081b0d022d01080a061202090408160303020909060a0e070507020604030507062316020d080c0604060516020705060708280306 72
    0x40410200801900c4160703092065441c011038081c0307518019445040b44140f40c032400f400401c1d02d00d03101d50003c0c803140c8003600910a400903490520f0040d03079003800f58100910b00f0320041c1212000807850300d24150100001c05010b5507c200307150045407206006246d03030b003e90008e9007141040d400c004880c08003c52140300d0008059401098000f049846039404682c9108012030342280c4590a0251000c0c004100b43c4400d10305001c0d054820300441d074000c80a034400e5030011303640c10358003003044403180c4080d0215000c0d031400070080c804c01c0803c0d060341c1c0d0046081d0030071030307210217040c40010700902c00c3d03800c010454050785400094854204500c0890305140c01004100707226040e07611161400760403010f00004800002030750241c11b118811004060103402403038600600c52920301c0c909641500c1c22910f05545504004100006141e02d00c400c500500c003801110b46002d00140081c00b540714044d100b1800000e4102c1c25000c040c0c0440b022400282c0e0200e104800100c014008003424420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 721886339 1250 721885089 721885123
    0x20405190b030411030f0102040803040e071107140d0501090c06080f0f01120f05010c0c031209021e0a050d030804061109032a030a0b09011404020d03080a0b060c 71
    0x10301440c29400045003040c0c1e0201090242181d031039440c1c0080b0480640c0b5115054001c4603000c0702920030a00092018080e420011503445141012800e40000c004210b00204248490442925000401d04c00c0031038082d040318810b000018000147c48414104cad001b002c0e5031918114104205400034200211615600c07543c416a0703c031250881d4a00b42280c2c2005401c80c030340f00600182c00340084000346107000b0080d29008202035503559085030403030b841141c0482e06201900e801c1642c00000c0d00e039844070301041071201060075404100c11043c21101ca00c100325013682811110748420000e0801031000030100c2c0d00c80d90391070070098107071a400e0b41d017a1030060034050f050000000d0780b0b048508000c0041c0061800300103030a01c2e141201c01c2200c5181240810140c2d45025640070484015840c3c01020740000904041440508541d41003641854002010b820030025035200c498207a0000c0e01420300380c180b50350740003444008006000800f54000e10105001c2420340000540030585541021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 721887589 1250 721886339 721886359
    0x2040e04020f010816031a04020403140705061602130902030a08030406050a0911090601021626010c050f07080403060c0804030f0801030c180f0e0307032312060d0b0a020405 76
    0xc01162900b13822a034a984c2e0319120001c81404910039400114900031640810b445140c010300014113aa0041e8401d40f00145c021495003a203102c20702c1504010b2104644840c90500f09410341d000300040f400000c0d21410703401914814246003504003925641d4000e041c2c42d0b0420441c5000c00c4142c0040c0d8065945510302000250107180a208403440d1130f4009001204046030f000030840da81000611090441c028612021800c544051030340307019001001c00082d880503003884149013115801e12120107681040e030000f1203150008102d1b035a5562880e2000c2c2d8038485da05011013284100d43c40244503500d40003503003400d554004031940c0224804e0356000d52403401d9660456100380c00b80005000b24050b8078040003080019064810300340c01138940070420f54101007850b82151110380c054601504009140002c040d480720310b42d41a010941703840940026146090b01e214060182940c05080ca444081a0250b461031040f0f00e52507406030089500c0c2c60280b0710307240690000d200700ca00800c400c84c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 721888839 1250 721887589 721887619
    0xc03050d021b030c04050c070606150f05070c09090201020f0d05030f0109020304021018080a0f0b0f25051621030e1002180307060815060304050c0904020f0402040e0402 74
    0x15100503600742d0001c00400301d00c3c000d0303400c10005107806003c005031848200160750019520f40a854020302c07410340c070b240b144240410040e0195040c03201d40c10803c0b10401004000840003108031007503803a100c10000f04034079907200607898801c1007281c0c82c6443c4202000000c417a83e000d030055106002081400400ba41d8500052059000c240c3d4029881f8a44100c02100188964001651880c00c0384200030005d0351528440d0625119407002da56440f00009500207014454011523000450500820014507120780d078404003150601c000a844c2029405040240f4800e20903100c00e01c10000c91841c6480c03a504c2c1c880180f40d00c00140e00d030000210080c1e2030484d402841005944451140a072950800240074a0001c1d03000b050301201d103043c800e01600c60741d1020883c5002030a0325440c0e0405a080080c81103600d065443d2299104180130800c2000103400813a944074101d00c00c6c5d54981e125151480000c1c04503190509040d005440440c000a004041c0040103003e41d000b81c1d6070103040070300f030707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 721890089 1250 721888839 721888873
    0x60102010605120a0b2d01051008010608010e07020307081c0f15091d0a141615050a090e28090201170705040302060d090614091f0204030c03050d02 65
    0x1c1000380c03e140c0c0042d0841000b04420f80f2229500084400410035040d034154241070501502c030300f0260500350b1343e40040c0711314102800c00401c800c2407401c1070b41e40ba6144c040010b100c48014000c40320703107460010110302030a0080069a44080d480126942c440080315040e081001c0c50b00301110016040400c5c001201146201c4d43c2404140400350248003820000c01d50301400c034000100301d10081901041440c3c00c002e001c1039a07190310844201440305030306400b0070700d0300c0110204458032100c0d041040210b508440d50400c2c1180302c509104d030b04e850300c080f029117800368154490302103000080100080800001021a801103a0b01c0151518408001409003200c60300d44000340820700451601c4440044035481d10b5000420307150031494542c17207070702041e03207034005200c03d032038a540314a121400c0042c02d0080009240d044140c0150300d14100c009166a949480d0f0351640c106001604092840c40c40d404840142d5040031a40d25099600d2500703d135220340b20f18000006000b0030030015001c02c12 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 721891339 1250 721890089 721890109
    0x606100206061c0503030a0204260304090e031209060a0c020705030c01050922020403060605060306090a0507020a1a0a06060503070c0b060a030b0a0b0405060d021c17070506060102010605 82
    0x5038001c081ca0b55400c4140b14540b0901e843c5404080c40000d540000a401080150722604210071f025131954a0404031150303680300700d4400c80c9440003001c0c41d10301a100010684040b55039039940841c0c28240200c145045115481c11980d0f10001601000080e55000850030b01075555520104101c4c95440d00407078481c0d0f103038080c1545c990401d00001c0b04561150307000e400540c1c4000c0c214038a11311980ca0702c2c03000704d4840303036500141a00410200300788441407007010300414041d60f84d0741c07071071424800082200c074004002c40c2c8425a075001141c6214801c20015003a694400d0611950302550300c24040c140d001100d02400a905103c1c1c01700e00785101d9000d480c09140d06885890305101da41d030700d203040400c0051000d0b40150340302c400000840c9064a00c64003822100100146050b2810140020b4440003030031580610000010740c4010703203c846492218420508940144603454503115102d52540b602c480303c0101c01240c0b0703c0c180a0301080d154022502600200b01c00c90340c0e141407041ea650303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 721892589 1250 721891339 721891369
    0x9021c02100f08011e230f06180103050a15081005010f060207092a030207030305060303181c17030f1005131503170a03050f0c07141219020606 63
    0x40314900400594a05c0c0c10102e8515000c108081c0a064039000200120b9601d844000c5c181c0ca007901d0054203506040991852580c1c080d90740c1c03850140d4118000c00804042c4c2c2c4a14100365998000406401540d805000030030034101c0001207180d07032244c42c07654450745040700300d62403072414000007080c203443c082c02c0707080310510307005800c0d000d15282c858001444010500f4070714943c031105600351041032030800691303002715450040e12001c46050040c11514003c0c0860300a600403c060b01c00c8920000c440200404100c8102d50040c220080766407040340100c2005151400f00c5104003c0b4111030000756109000307400d00c4044a690f080a8043c0451642c411160800c4d640c45080d842c92849402c6241d9451030b5050410000d562550f44030007800520103110081c28010480e808c1043c2d0600817160481c011110442550400c40d00300051441342c440010a0320b026624000b49200041c40b04103041d84c04039200c00c1e25204c3c06181051140311005224005000b6140001c041d49894881108020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 721893839 1250 721892589 721892597
    0x91a030f0c0105070f0f0b04060e010b090a230a0b090a051510031d031c0e07060804020a0b0310050901080a0c0302101206080102220e061309021c02100f 67
    0x84030a50041d180c1e540005411760300d800f4421240008101d04090b605201c600c2811504124036140c105042219003002003650903904088a80d0035540e10000501d8002c00c540c00700103141601c2c0080d1a688100301c00c82d040040c10000308000400d0b820f5800303420081c5040e1400b9120759942400c26048038011200c40703442e140c031800916a10304025074415250055400c00191982880600300c44100300c010301c6640551000850504444015000c14000e0040d004144102c0041d0b4544c0b43c1c640915011340020030004400003010340d500d800c03400c801061610040e80d6641007043d44e68121481900400b40170310964800011202070016215500035081041d001c80e003030070344c0d01b0440381104550f00e11080281c0f00d0503100d015105c6c3e00c80d200051084e500016907030120401f850325880c25992440404041c01203042008174040308a1503840401222003456401c60607100200410705c142d4042e4001c000b00c07062125660a406081080d00d0003211020095000c84004035180011248000001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 721895089 1250 721893839 721893853
    0x1b08010b12100e040b0a0b0f031009030905100c060b06090105092101020a1211030f01172806110f04030212010207060207120f030c14130f091a030f 65
    0x3680c414803041d4025240e91444659030350f079202c000e4039440f01901c0944d101840c17035041c01054041d034400c844002400351650a56041c00a00003a16a84030000d03015689440742c81c0c290400d8420000d003006490010240c59105c4203070f0308010300100d0490350480701d00b464404140542d144c05000c0d904014816504d0a2801c0314030380a000c2c1a10464404007248000003140406148007030001e0004008140c3d500c9280d454030180900580d100380c840c08219502c1001444058903c1700211030540700140d044002c480194044c00e4a400700c100c5040e0f59002028148039080740500001580746070003550248000b20015030032940301d200e950303034203202e001c01000101700606002d251013101145440c001420b120442d145c600903a4404a012101138049120b0104090340108201d00b001c91a0301e006c0010b02d05000300900801112540112010340c0855004c00200040300b0501c00b52070420001c1e80460707036503219000540103d20f9070702000b044042e0138480609002644801c16032a840050030301c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 721896339 1250 721895089 721895107
    0x608070212160807060908030a0b13060b0a0f1e0804150506030c040e03071b05180609070e030c12070602012a0309020a091401030204050906130228091b08010b 70
    0x1951101c4d400b142e0f00c9803980e0144022990140145101d5001c0240214800211030200003003900521701130210f0500c1c008052050310061000e0310726400303090400b440312000b51801501c0042020241010502003400301e861030540c48100e05004038490300150b0203194a101d0204180c50044503801e40590004032588290701c0c054001164546100040d20b00e00003030350b152204610007031101e00565107000c11040105007040c10f290507448141d050002440c1c2030403000606205000740c500d00411400c505880c00f599010f00c109200d84030024007002c480099449a00d8958000e8403884c000345d4680401c2031412103a030945a1400c48a500d8200e495080100043c3c00412510380281e0b0030203c000c2d00403500c0300c2e03d440344542600b00010324290640c5548100410340704010321951880d00701c1c1003400070102ca21781d9240c0c8880c0e4100c42401e5031728501041c8404441d1303d200303411040300f503000c4002850070603a4171464030108803501f544903501c600320003540d08000c2071150b0740714600b0411440768 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 721897589 1250 721896339 721896353
    0x604090302060423061005030f03071709040f0513230304031209080d030b03061003020306040f02490c09180b0a02031801110403031b0606060807021216 67
    0x510b1444614032400b4030329601300142d241100c2143d021945000c4100240540d207001c00980c0c1844100c0001903281c041d0307a0359170655810620320341d4131903007001040800c0d017695150008281e045d0040c10400aa01e084041030340ca80f90f00307400580e166423455445c10341c601d190242418454410f00021442c203451969142d103c04000301003001040894580070806020902040301c1c006155940030490740700c0542018100880905140240c120000c41000142c0300429960b90080c2c00244501034181c0c9400403030326101c18142a20a070742c0001c01c1000d111034601680d681c5102030741c03e01c458420380320b03814580c41d072002d844c000d000c41d00c02d0312041002080035005000c614407047e800701c0115150355241503908a0a5902c20480c540200c10800341c204c400f10140c0103602c543c1c0c024032104103542103048c6584520301010301007008000c140c805207000d130902c0c601e91b030b40e00100c1084001d40d41d142c010500402603501c1e10050155010304024041070b0425920042d2035034800c2c0300682041da41d551 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 721898839 1250 721897589 721897613
    0x609030708031e01060216080622020f1201060311031204050909070b030f06040b0a0b0406140c030c03070302060f010e010e042603011a070c060c0807120309060506040903020604 78
    0x94003c0814804186010f841610342c020701441d001084c01c3c554100010030a60314076001450117921140070410b903580141e00d0504003007440d1000a80e0aa1140041140c04d584c001485400a41a0500b000e0400301580424210703030003051403c107401045000c0541303030075480348440e544540a0105110916255507540d4101c10002c04403076000f039590400c408035401c11030705600082c0d402401c00c55981424091a2901501200c049120905100440c03d5901031350050500304441120340003000040c900440782d040c40c200046070303102c08045540307603940e60208104400500955001ca84120a88003e140c1607410101145c0300310f80c2801e201444604000308150382d800050012507483c503480600f00b605c1403000c4000e040e92503060000c540600c0c9011030309103550b24420001031000c21400300c401c10a41d400d6280c40c0210140382d081c100313624050800040c04c00c25007903500304c00245e0150b122781c08040c0b00742c50501213999004100030864074201e03405000341e00682e0004002a101c1e6000d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 721900089 1250 721898839 721898851
    0x3040209150d06050a02071a1308030a0920040b0109150f05071406100f03080d05070e120a03090b0f0318030d11030f010e0c1804020405040f140702060903070803 71
    0x4091002c41503d4150a561040d01c440c06169030000d1550f0030300c00c1003446500c0301c0030030580110745030610b400d2920a9a90b200c01c0a803c5100120101e403031410f49800000c0f8060b008806c0800d0170303010105407400c00c0903211a042c4103618200c0b8038001d43d409480a03d007100c02050381e400314196020420b03100e0844020b045c0c3c04200d0100109400a04c4040c400b41c0000910802000c8034508003118090114594200c80341154800108000080d04071046968640551a01144a0b2512401034445030180d6000692000c0c00d0510698107039400200403827030502076690016038698900542009125401c118802c0c25810000a040c43d0303060010b940344143c11a003124900030f09515644121100210a0b80310303007900006006406545020b1540900314800c2140450b041c51f1140d400944966580b9114800c2d192111100c1030340c455054030001d0401074000d000009840c00c20900402003650101d401d8060100895412413001407450700c1101540b00851400d0b52030b859034519a0802008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 721901339 1250 721900089 721900099
    0x40b070201050f07050a02040f1104030611040e0c0c120f0a030b19080d080a14011e0806070c031d0f040b03010e0f030c0712030507020103020304140d051306050304020915 75
    0xa0400e48043e81c0303005191060080d07018000145152041009541c2d1844a1100003810321040b042c4043c2d417a41124110303944101c000885128419400e0210f002c0d660207115419100001c0220084101c001040401e501c00141c1e017480800d014112110f0164039011100c0c01c06c1403001d0031010380642d2108140c0f01e4000e00c0c0ca500b0550044005880e030340f0503040032501d6000b100c0d40c03c13000c0d5007081c132940c0c02c080307151410303c0203980d4a0303105400175205101d04100c2802d40c104100200062550502c003070304403201070343e0702e52400e580060a8611614400c0b000122250585c03045420021800c00c420340700141501e0150b0424410400900b4019003101d615541c0c80b081807003426800c11418040d0400100a19150604c40d1038407418950305030b0140c1c910804035592100025480f4040b01d140c183c2c24200141c6a84450800305001404184183c40520400003c101c4098201c0041d2280760400b00b0b8134100700351180b2003100e81d4002074400135000300d40f1901003403043c40c002c419111820ba01401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 721902589 1250 721901339 721901347
    0x61609091e0f020d0b01091208070212030c01090314031b0a181206052206050705190e1207230102030f0f040e073e0708070905060312040b07020105 65
    0x1c42d02c880700d56140341d81d400100d002c0800098003800540400c00d081030349599280c0202601d00030448031004201c0c0c580080d07410115507410800440c0408040100c94864040480c014001d1881c83c0d0260007082c02600d01448240b1001c0840c0d102d030002c08400e8240314484001180b20790081e208040510152a00ca2412103240c00c10f910002c01110000317262a66090502c0d0045800180c401a9508564186507802803151101803955644c002000561650340c50011513650003004000107a00340d03500d001c00c100d1540807080242c0301c50102ca885c180407240700001581c0780001e00c2814540c0f80301c0c204103500c8541403041d540441d08180166072803e20000202c051981c400040e80021900106080c0300310142c2c0b5020507070010301424844450f01c0f0700740c000440360b048440f5481d5034084c008502481c500228501120511804045510690700c07003071040d80381c04141c0a2204c8039031600f00092101d103000102000183c012075041d5161a040082e03003840340e48040001c0c1d041c000108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 721903839 1250 721902589 721902641
    0x1a04030e120619060503031228050f06030c01170a020d0c08100f0f0e091606110c030601030807120e09250305010e0a1805030d090506160909 62
    0x22014150303529111024100a1400f0030000d5900000c21035511031a41c07074800c0c14031076030701c0010491f00d54980507110300c0099030703c11a0400c8224848030000320348425407001a0100f05598105601075455880068016034924040c590b0315165129481d00003501c030310360756041c003840346a2140c00041e1888007610784618961910107403051042e2030800203000c80304100e2030840303000c4950054001a40c07030110b8039151012401c244030365405404811051701d8003040481c081048080e4110110101900b449a6102c00180290345180c000d04141d000c3c1e4200104135107808a08603041c2e0364070900c40760038a15203840d201d20002c248400d81f0140504204039080581d9007018582c4620380c0b6600801000c15000c8151800030f034510200c00c1494249001030120000014001f54400c91001d00004d103401d0440f001910b0140308080980b2034080000c4500f41c550203034001000040c040c000b110b14940380c0290520842d41c2c0c00c48102c0004a024405018402d02030f00201c6840c0015242203c10b88249 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 721905089 1250 721903839 721903849
    0xd0302180d0f050f010c09090f09051204090e0708031222050307060e01020a08011701060315060e0c1c2003090106060f140405040c021603060f050604091a04030e 71
    0x1c481c0550b400c00c40c05800d00b0400200708070ba209960300200c000d00c02e00664000150030510b05014640c2c52513120380c00c50140f42000d07400400a1600141151000740c21504800500d42c03080c010703540c0d02424007a0343d103200c0350b0000300c040460740814021464160512250410101c001d0300c0c0e02c000c0c1005140a4031038001d140200c4400902039009980e480fa81c6141100031901e41200303802c8240d005100c5036410a800c8411b49044030a002817400d5807046403190540101002c0d04002c01c1e08050458500c082d000c2c0c1c3d44074805171805456181065162501900c103603000701101d020900e0881640244604503d821049008000c41002400051030b041c07820446e40003110b0401060b9543c400801c625640b1880c41d051680e040d080c55000903102805048141c41940103550090b6100c0c89420000f510820090f200070148004480105459103030640c0134000c2e89190000c00350910000c1002c83c50944201c0d0344e01903004000803424102c99000c520f004000500a07070034045001d41c80c888a44903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 721906339 1250 721905089 721905109
    0x24060706230f0f0f01080c01080603010e0d0503010f0503060c1c0f06060e041529040b03180f011103011403070803031509010b0c210c03120412110d030218 68
    0x6401044968a01410f10880301c141c010031035468425000c1c010000000003140b100316054007864807003540d0b903400300424054200700c010455540314403003400c00300651000295069030a4140000d042d0381da11030400d5901c0b142541ca4440c160300422800c0b07280140962500f001484074803000c41d4814036075050100302c805c1548400040b8001c032030001002e20700341c4200950300c103002d10758582d442c0c100f82ca40c5201038407400c1c10403100d50b01411400c9605c610b81d426907006100c0c03503407616503034542220080c440f282d0716800c251881c031400e0605000300358113000e0904000c070b0025116003580e03e0658100740d807445160244e9014002d07124041882c00050005500c1501000f0300200c14645070003d01002c18016800000204002d00403000d5650380495400c0001190540d002d40750035074250030000c94800e030900588107210028010a02000d06101da5100c1c83c01035143e6040e0341c244e140c05440c2c1c846200d00c0310196400000070f04264078025409040c7c28410707800c03000d0360303104104003054075050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 721907589 1250 721906339 721906351
    0x6081b0a0c0b0a0e0d0c020d0b0108150c030c0f1c090b060a050d050c1009080712123209060c0708060c1c0c17040b2406070623 56
    0x150548400e01c0038560106400a030f5000c401c20200790040599625101c00d40c00a07820083c180c0041829962610200302816810039110540341d41c0d1502001c3c2e88021040d414900360141000080f08a813070f240c1074030f00c07400c0f0300201545880300003900410a5440b080340101420380200201102d2025482880c031840d01c1074407010403d0500d4010480e400d055035000782e115400788200800040c0c404519688100810b54a041c140d0086080a40b100300c05031b0000681c0c4e100d485000191400424236130280f00e4060000c00c8070a29140380b08842c0d02d905811400c0056000444000100003526643c0c0441080c5501c3c60b4185030720306000a6556100c00c0302000c19a005550900880405100007604081d06003042803500340710b2035800d902d440c44041c0079110a503440d04080c92042c010625105045049444e180562a01c1d150039211902c058a0402070460b080442d0102e80703000c03040008580074010401414007800d50342c0c01014003032816091018170400d00304104410320228880380924 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 721908839 1250 721907589 721907597
    0x1111b01201507091215090501020909070c110a0b07150608031305130204060801030b0408040909080c060c0c15060d1403031b0f0910020f0d030e060a0e0706081b0a 72
    0x10505400081c8030488a0f00f0807222940e100c805c640005051460001c86c030051400086160001030070310301d009015003851650066448010004040d601120454803070b441501c48010891021052060741d44d194042c10219050030410f4a002c60301e000c059908458902e172011881070b480745915429508001d803c4585880c003294280101d00d491001507200da00c0020085042c0b91411030700800390b0070180b00103090480a40003080a1000c040115000b6014103202403114440324a40311003140d0140181048501404010070700c4c0400c5282121000c4281000501a8100441e008030003c4d40242032242c2c0210300c4c0100f5800581c00c1e5009284030541103014544038900009035600f45108d03403886800c2d40720100700b56070400840380b00751030395240c0a8580c44100348103044240d2900403404a4441c1c58481c4484034030700d15a05801020741240c1c42019100e068544070200001d5501405083c500d50700709480a0208902c10148540e02000f100b0903140c140361003559400d43d590110700b80174000707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 721910089 1250 721908839 721908841
    0x60d0c091503060e030901020703120e030d05120a05061e0406030209160f08060a090e1f0c02070905060d1419030305060a050303070c0303140d110901111b012015 71
    0x300000c0e00c907003803111341e070078024600d00342039400000e48541e914040180305511107040404c01521034600d1400321000070381111911982100090200e400841080e0624180640011a640c1a0340070359406050050031000001c1d404910800c0c4000c250807030283c00070360f40d000c004050390700d2030162401221044241c02ca043c50a03140205070414501c1d01c40b041c40250b00500c281c039207640d10540200d40701a0400541ca9040180d050b0811146101e11419001d541610001080e4298049942264950203c9148a9640e9105002c1d02d80c00c6481982c0040d4080070340c0c0c0031a00c102c0c2c03800d0140c400d10b002d4030858038100401c291000b072a10000d030b00080d6550104105414180629005403504800a6042a02d40d41c3d902d000c0a040c6e00004080010f0880102400884407003070b80d580f1950850180b00120301c400c4400140d03000301181d00c3c0040d1140c24404082640840e0f104144030b060703901019442e44040056800041400910124448112807a00d594406005111110b0300030803e881d82 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 721911339 1250 721910089 721910093
    0x306010e0108090705060715020c0c09280b04060b1b060705090907120f090510061d152e12020a201002070503071b0e060d0c091503 58
    0x46098650390840c10b2088040502c030005200207504022150201c0341d041e555901ca1400300e1a1405d0303070401c8103441c4c0c00441e14119888001c40d04901007070303083e25421400c1e66040c000e010442d000701540d03800041c00307503245401c1f005540c104005104000e0404286a9541d1186540381c3d4000f6070421401c4d5020600d0010001e414460150800c4a5250041c207000041000440300c0401405c89400e0002d5540c8400e04d80301e050f081103003030804800040002002c1410820348804a4030b030000021480ccc18404250b03082c0540c20510000350b1200301344415910844822110b209107092107501a41d084100e40101c01480070410040a502031b00c2402e04003500d0307000d000301d0189083c8410840c0180010186140d020000c12500207860001010b4010f608010505001844510401c940c2c000034522040c0000000141012842442a4030340f07000c004681c1051440d0b280224044140d0b900d0118815192488403804a03a019100000c0001d94586190089a200303044245540c40480c804100b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 721912589 1250 721911339 721911347
    0x30f080c010b060a051c0b130608060f100611121801020f280f0204020f030105090a02070b13030e0a060e03100612021c060212181504030806190b030601 67
    0x1402c1d2400da6945050016604005d00140281022650a079401e264441201412034121400300c2034082e180b03550b80c90030f03609843c01030031031401203802c1441103a002c00c882160701c00b015403086101001e40e00c42d140c1030035021215016600c100c07200700e2003400000800320840c64000d0509501441c0015054045440064202100c019042d0a00c0e00040b072202d42c805249071600102c0d210040c2c024104c82240d140c058800c80c61094043e4100d032000c102516002c800d60000e5040e5001101e00c03600a6848a50740400d03445030320401042c03019882e000c140d04800d80b800c1c001c1c01a109080c00080c1101e00008100d80818940c881c20009201e4510004071f803c083c0030014402c11194001d000701410a190f08070107501c810310080c001e44a000804100d859400c100c11030f443d0b88050107641c2c400c400d41018130790704416903100e0b450a000c201d00d051503c0000440856120315800c0003915a981c1d600c06a038481001400300390004149804984400408214040a042050212900c80c180400014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 721913839 1250 721912589 721912601
    0x60203040e0c031312051c06050414161b02280506093307060606020c01031a0f060409060306060e1503060a02071a190c020c10030b0a030f080c01 64
    0x140702e100e040044c803d032001e01c2c3d0403a1814a402049000b0040001d86040700c0602c130390307c0c1d00700b901414188001c5110290f6045001241c02c00c40d41800b0541e808041405510410303561011080100c42d41c2c1d00c1c185000b8090049950001104a42e81d08a640c0200e1309085494400400d0346955040b03407100558210320407006003000743c81270fa0030084040c0214180c0903417060300d0724609144600020a02c40c0d9504502e5000001001013a150700b8503180000107803a46015210140c0a044440802d80d482481400c10100c40340071200122444038083c80001c180e5403040c1d5401035010040890421024041c040066205603c0016940d181041004403c04007900150120184002100c041e07940059256049100c000d00103903140103602d0010214800324080010030038034101003100180c00c00e03510510000c0c071604140700d9030250030003c031703210b05400080680c000941041c0c4001c00c1c0c440d9110f10400e4002801528485880742c441a40e07c4c00083c20845940c4030004480301508400e0180b0307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 721915089 1250 721913839 721913851
    0xf03050f010c02070807060503100f17280204050426180607030804120c0606030c0521060c09031f020a090603020a170a0f05010b0c07081617070b04060203040e 70
    0x11381005810901100e40710a0b0510889040013004000302c1c03079034012001c03000002c1c06801d080090140e5640203c2c12046441848c3c1807441c010801c612403c0381c0110030300d030840d806814994190103055400c1000405c40907109a5900c00c1031101010413071b00350354000300906100c006503600d0300d640400b40641c48094190050180c0d00501c11800021307044a001c86c0c1160340003020041d5035454a8007150351404251010f004141001000002c0c80204660102601c03802d458800b8100000704180d2200700d0b135503900050030360000000414148201000d0035080500034180c1d003c84400282c0000080808102e103085582d0001d550400c558116020301c00501e072a007015414000c0740344000c0c2c00c0d031291200001da241140740000e42c0d0404103038445050407941600070002561105c1e1114881d810043c2e60501620034038030086114200018009000750702d43c20200196410714a00c60507102060450f00080d100300c01c008554514860003400151103294010340d01d580c03030140c0c00303901c48001500e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 721916339 1250 721915089 721915093
    0xc0e210c0f0306221502091503042001140c0c01080603070e160e030d120f06050f0d02060c1506100807080601030b0604120c03020f04110a180f03050f010c02 69
    0x24661041d1400f1407120351260f0700350741184a01d940d40311134103488500480002c0200300030421407201115607034050001401b003a280e0403055640c07196040b036148001d0710081c3c1210380b0003110b45906a0703001c00d90b266408061411384000e0840d02e41d0503c5a4010318207056480d00406115405540d2195000760f001104500900e20385140a24440c1d0380000540381c0310a02082c51903910a042c0030b00080c801e10800501107452445402c20000e00311000035000050850404d60882110f2116005503c01e403130b0014001c28403100c81c0010420b014030410022a013040c1d086c00709900450051025001001074100003d510f460720381c00304074034a0389090b03460061007007110500c0802070340410030a07440802801c000625040c4840010214003443e80b000640e80b00c82c2d07000d00100641c901800301200d00c00c0d40d00760a200c81400c03c02058441d180a41c1a03544424458011114400c40002109281600d1031440c0719444a041100300348040d003060300c1c41d610544001501000c04d12540d0024001480 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 721917589 1250 721916339 721916359
    0xe0a03081305030f0403030e0a0906080d031d0109232a18010f09060f03120c0609050307060203220804150201062102030601080705060403060c0e210c 66
    0x5005401080040c101008501d41d01000000b0030400308129140c003481544d00b55141c030f40e2480c000380701e0304c0c044550740e01604178002d0014464429000d6082694520b9024110081442c1e00c00ca000304081000321034250000e000c00351024000703218017250070340512244202e143c0e0314041c0b80c4000070076100030352090703000b1000c241c14190b111091652000c161080f45001e60b14403400a03c401c040300e1000c0156441040c00050889185c11000c0c0480340f50400a0000035178458215600d030401c0d10007d010400104450440e944c8140360f038030700300b40c82a00c00040c4151142c455603d19003000c038044a089500006024004011075800206141d401d0800003400a10f030b07403901c165004170321480c1020080464500c1c1020b000b0b40010b0044c2c080c00d04101120707007500607104004904060168080d014100000c221140003003488030075150701078105458207144d03070b84460003054030b52070b0b110820204412101e40d50307582407901601300b4000417080b050700300503948444c20030141c880328500c0782040030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 721918839 1250 721917589 721917593
    0x10b2107050618040501080d090618150c1e1a0907052709060105191401050a0c1a180102120f060111030409020a020706030203190908130b030405010e0a 67
    0x25030042074400c2940e0305900c94803801450075071540c1c410001c0c0d03030007030910300080b648040000e41d050011b07110799580980150b80d00d0094030080300d100944401076880003000c0c800980164144074202c680f500e0802000b4511f5280c1840780d40208045a10040300501c02030140418074041030b81c9101024252407190500a0031541c0e6100b5501c112801200d212548d910361844100b04400d1a0b41c125609400d00d24041d201c3c29106d100c00d0150600c120b1781e02c40710340c01c00307110070440b030054400030f6a030303140c0340104803005440c160800c403104010001d0943c500380002d025443d500313405290700092260641405103051060741c0750042c00c4c1c3c0d00c903841440034001c40081c040300181c008603c2d640c001e009407506d500403580d100300181416907504c00024006002015036008040d005000c0c0e007500ca180c1d8448a0407402c0c2d102c160341c03050050984441000c800c03a0260700c01c0c0c880c0d62080b08054681880301720440440d5009078000020000c0200410062007801e0040080c10b412103405042031001607 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 721920089 1250 721918839 721918843
    0x50f0d0906021308070518160c081c05060a061805040f0608030c1c020c0f0105220602030702010809010212160903020607060204090b030a050304230d0302010b21 71
    0x40a112a05586580214041c419242d0441e144904089008000b140c1c8403808203076909603506c06c180c0124019111010000480880b00d0b00500411101c0910000c00c403904179072a80e154001a18995400c0091604030003160001ca091000300c4c4a001c1220f14200c0100300301d0502c250700000500001c500300c0c0da00700c070502400d4020750710700301d80000c2c3d600d900240d454010300964000110903c00040c0141140303200090540000c164101c3c460031020f00703440c0883e02e0350800001340790000c06a41d40241150b0081026280e0403902042009010320908045803034125950300800c0540c10000f0000290350784190304542c81919500294580002441c81040c0740000400030024902c0c0480c4000c82c0c01d00c101403d50040d80c004209039198030031820900000e5200b4851221528541158400c842c1400320706c140d40650804060750810707140240300d4499803034800d1507039030100300351031640303050b540d100c601107080c601a0f03000141e1a08004140b0801c60702020070503004110000e1560000040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 721921339 1250 721920089 721920097
    0x610030b0105060703120603030c1412040e0a09021005032d0a0b0d0f061407020c0f12011d06100519140a2c010515090904080c060405150106050f 64
    0x81910700584e900964202142d580d881c0d075880031101c3d0306000c5c00001307056005600c0f080560051110940402342c0200198bd50f000c49a0303030a920580a000801501011b4040598442c400104c00710703160170341c1d038000794241440d4116407000c0f40010040c4000c0781110010720a1581c00c011080e441444c069140c8901410018034200f00c0d6911182e0a1100b42c40c1d0900703000141c0d42c002805104545986498809481600c02c080e0800707049000180110744009440303042150041d081200c1d89080782c0c02c0c00090038240301b038200030b507407101c074400302e02c01c08081c120710b00c000c204000c0c046a0412808441c41402c195000c14400c02d500494000a0554503010508a0380f41c07400e02d841140c031040c0854505c81c8e41394441070541c509684824580d031014003010301c00c500341584420342a030301c4034208003107150251410b014202051111482d00c0c1080d141180e00176005484031410009074001c06460308404990484268000306105d03040141001c12042c003500503424101e0420498050310501405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 721922589 1250 721921339 721921349
    0x302041e0b032a010c12050d1a011d030718020c010b0114040e071209120e0a06270306021b0c060703080f1315150e0105060703050304170301090b030610030b01 70
    0x20b404050f1200c00c4e8014449125485c0c0d0100c1000d6602d0400d1101501035000343c02e81450302800c094000d688030030070f030f160450f12078016103e00400710100c0c80c0b080c03002c1c07054039065a014407507042c1c003007020011404044100544590091b945008100c9102d0954585107101c0b4184400b001e54080c0d110311100c151410703100310b1403191102c0e503a10402121580d07002408035000a29041450f810310620b101c84007040c80d9103807070b0030f200101e22400b4452141c002d072003020002543d40740f0004422902c28842c038082151030840720ba4180d225240ea40032a4080c0303a907240c0c100c0641c240c150465505203d54440c80c8001c4405a00300741840c3c8000c1d000310401407550640442e0b150010380480c0bc00c5c00d41c0c540343c541003c00d29052410150010b001443c0110340303c031000042c4440090628124400181600d2002d4602818003080c1d503019911500003400490b0000140c1070980d4901003040082c6000709401c1d00c2c08030300807018600b81428103801610401c0745409010040c03001c030700c0c0a00340340d045607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 721923839 1250 721922589 721922653
    0x1021306050307090e040f030206150303160311060703050618040302060f070c12121103091c0212070c0f08030a020c1507050106031103061e011208040302041e0b03 72
    0x941c420004a84c10001500414506001c80741400144a001450000100e00c41d408440c800d44664050880e00c0340601c00c81da074158401c0041011145100800c0300d0464480d00305a40409800300c60142060700c12190503000956410411920b440d280c6040f6022503e8201c42c0701e00c178107141c1c90003900d50741e0091030080031114400110701c145215444075900030b03400c07003061044400c1d00c0c60000c045a02c40b041004010782050001402802c440d41103a0160384035200800c81c3c1d21002c480d03c3d24040701504200150b001e640c0e01c990750380b92840000c0485030720640068407010b00300078a0b00e07904d403071b250070082e5198008e10820401d96000205000f0740503040350f403000d1620080740801094416400000c0041d42080310020030840048221582c0d808111f003661aa07580300a140780d03150828015030190007000c0c01c010040c2c01d0580424944807800707814500d240c96100d801103010758079201c0c1400300700300003025124510401842940c50103c421005041d082141d60346045800303444610090200c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 721925089 1250 721923839 721923841
    0x21060a0e09071e03050a030806090a06210305130311041a0f09150315090d0f0c140c040e0303150108010503031b0a05160305100c0906120e0f031b010213060503 70
    0xc1a1880b034201c020f40c0e0017021655a10700383c2c54020b1400405507945402145810007064400841c0e00408060b20000c84411550b03042d5071040500b000c0c4080810703010304c18100115203061480c81030580146000c2c7c030032070071140e85a1050004490203103082000d40001003902041c0ca5441499141407048112200520760300c888840040000384d00740510ba1501c0307100303440500d804102d00708910801c002d0043e1030500c3e40b092015604c0c4103010840c1d0002610000c02400001c4a00c0141d804002c005c3d0100c03242e40300c2100216040ba00600c503904181ea101100b0810101d0541224486800782864040c006500d4480826980c3c018880ca200c540303052034088000b00700e01003026080f25904402220342c40306032160110142c440c00d0005803110302451410785080e040a0003030602d0310701a6502c0c8114145064000c682020320880c2c0841c18584070480904a04010850800c00380d07500c00c05907984450950412201000b00381c64040d1a0b401440400c04076450845004110f070140d080955803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 721926339 1250 721925089 721925129
    0x40c030f240b03090a0f0507080d0c050115030503180f0d0b071e080604050705070b0f15010c0c0b0f0d0603050721051f0221060a0e0907 60
    0x14010300d0004480e45460071a06000003418255101601d00e425140484003a4a840c0b90200300e1104450001caa030f84440c3c5028001190400c100074058021800d407000345454620740c40c1010448a10400003501c0c3d090b010041c41428070451200c600001411582c03d071035503440949a00030300c0c070010800b0a0a01c045015600c4500c008107038050010940495500186400c03805060140c0700c0c14001084183e4811b090540c59070480c00c00b5003d511403280641c1e842c401c00002c0d00c0020145010400280302d201c0000d003050007003034025494043d201a69183ca00c2003806122100036600d81003041c2841200c010480a134100d03020380707420351003480c0e07101da5981c02d401042c41250b01c44050f00745841c41c000180000814420162500c840e03215054030a1150f4010702c1c80030509001d0030603009098020020040c04011020424098002600700107101c0d010028822808092070504c5c0350803020040c0718589010400050101300e04030001a040030060686c1d00c545038020f4200f400e41000346024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 721927589 1250 721926339 721926341
    0x209091509070305010e06220201140304030207060e03071214030f070c0e0117030d050603120a2f0d050c0102090a0605070c05100e04020306120a0f0302240105040c03 73
    0x41900c08206a0800340e040c0000595921500d0b031205454a51900c0964840d610b004515a030080d014030b4050301c140440710301610b00340c20604204030305024014010b001d00c3c80706000a0352086000c0e80161a0107032401401400d03114049026a101e40c0150105009411031442884584c6401c41d041100d440c4d400d00706246188164040740807008400715101040185d046840000da8002000780442660b0b1200c0a410807000c08082110b290800d00c070b01c13584180503a00617588034030700a048423500e0700485800d0340d580d032105480c1c1000036410001c0c20640c1106070104c24070045840740d5010003a02d0003504944403241d41c580302d010410006010b07145031209406441d44284000d10030f814840d5103e8002d0b2882d80428002c40313480201a00c005902c0c9000003d0020350200c5031500d00d00e45040804100003548020145540710001c01c0308c1003500c801c00c020880c2254810700080c000c184060901a18014940400450000042c88802d0304407034000c0215046507401c1e14040703000085401c040d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 721928839 1250 721927589 721927603
    0x5070605060d0b0f07090803040f0510020a2a0e1e1f0e07020c030d1b0602040b07080403051506010c030c050a0b0f0718030c0b2a0d0906030902030a020909 68
    0x180005a41c4828410403c440c144414098170040d02c80841080c0d948110303507240d008038031903040340c1d0845040404c150304040700c2e010701480441c41a11880c00c03403640c0d40289002c5954041d010500201d0500c944000d0f5901d115019201156100d42246000340c00341e607a81c0707041c032507028500e81800003017030440031003c080801032078070014040c2401e40c4406000106003421901d807401807090031501e40d92422b000c42c803221050381980d1014104514001000030100c1d4038203080f1160350b42000001120300542d4068100c09201c1c0486a03a200d2071030078420b1511360000010b922210303441042c40b045a03001100c01c040e45070b1604020500b1501d6050060400000400c040c2400d00020308000700b0104080c3c1162003231900c2d4454801c0030400b0601c69999050300c1c00f004200e284407040c01e011240d900c0c0054507146401c0c50700e00e2440945501005d044c680350b00c0034003200c3d5215801c540702c0d0070b810101034130140000e45020040c1c0440b07a000a0303074070044850081d00030034407200802d44041e0144102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 721930089 1250 721928839 721928843
    0x51509090a200304050c0108010e0402130510050a150906051602040911030109030e01140c0312090a12050406030506060c03030403200703080306270a0c05070b0f0f1605070605060d 79
    0x1140d140c1c6400d00b001d58848000911b01400116020008510180140720080c00b8580140109564603001d0b54820000e000180070100c0400c07140b400040d481d901e458041e0b02421030303900d01d0002e400d40e08202401300d00c50794001380203100052024400c507031110242d102809404660204021200b07080040d0030741c2c5075110490701035080511a42c1810f412101d0152100020f1362006580080304540850a0240032041400d83d00f0030000075591400c0b000c00359801a0340c050554070f444985990f440b8250240000e60f60118001003003c1000d150180b00d04c0783e0101060b42e2452410100c0581a03450740f00c001c00007400e00880d80307003207014103807550141c1803508058821948069280c2c10004200c6d042121011721a59100d070585001d04481618084d2001c500481d81d00c95440e41001040a0010364042c0c00c00c010b01441500042480b904445010300c503503480e0741d01d21b41406491802c014600411314036a05031041c5010b0780850f800012a5105030b04440e0002d95600c90300d0001e40d02c00780c41040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 721931339 1250 721930089 721930151
    0x8040509090a03020606011d0d150e06011a1309180503030106210c0c03080711150405010b0108040209220f1209170a0308090c040510051509090a 64
    0x3040703031840300000e0703405541c0d0080d02151850781d0343c4401110032150300d80c490502107219001014075414000e51282e07050344202c0202051b05828141c00007111a01058490030f6840300c030040100660384c034003070300401c140345a00c28135000400200d203450151510a248800b503940a160020042400c81c1d48003081d0300400381c96595039a100010704e8138011981010310414064440400c0f12071900c1142004800c13901e03502482070b084c1d10262814400285001e05002403080c1003e2010420b001031014011990300246540c00e00d4104103084900c81e01c200e6043c4188201448007603914880403a030b001005200100000940295441c20a02080700040013659030071140c000700704408042c40e44000c490f0f41c0d60708a8a0352820106c0400e45207030725068082e005170b564000401e1048a1103688401d00c842281c02120f010b00218048410848500345043c183c04414009842d01403020303803680d040f0849041c200071a20000507130008010380a02c4210399192066500c141c12007507002114070030b40e20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 721932589 1250 721931339 721931341
    0x31d100f0507050d05130608010e0c0913090534180b06030a02090f0a06050d0c05091c030f09081e07210b100311130605060c0a1202070602100908040509 67
    0x8005e001e0740c10050402d00c851440c8240402e000e0310500e1001e040303481c04196034095441b4400702ea08194002c0b42c030703190400950080c035200b840f00c1d4002c0381c66032481440140f0312100f140300720007000050303511440d010040c121029403d40c01400c60318410f030f95030806000c03071202035400b0b21002090303030b410311a8011034007204005c2840901e5014140030340301a80d01550000c0d501c400c100f00000e0b1800b500c40480c0b0180a040d40d60f03801ca602c811141c1209003851441c090014000944c0c5d0703c44102120202240c07640050200342c0d000c0c8a41d03501a405040c071020046c28a03142c181c942e41c10b0041c0342c02d0040034cd0b51822005404004003401050414144d04113250744110390002c000801d8015500c84500c4000b02d100c412008803288200c9400c0201102002e0142c001c000c46142a80000c0c00c1042e10b13136402040d1559000018941c106000c40245566201460044544c1d64010504010344d0030042040154640202d2050250218800e00081d80502c13860021494011354106da0f8120300c0e044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 721933839 1250 721932589 721932613
    0x100203040503011409010e0708060c0304060209060301094a030708040f030302011404080f0c07080d0f1706010206061318030c06200d0b0103021b0307031d100f050705 73
    0x880d90314024840c805c024031100303141c0361403d5a139a04521030603100758490800141250b0300740c00955005407107464058680302c014800900c45800a800010485a456100c0d540840d003602080c011005180381b07065480000741c2030315000a030f802000412422120280b006c08030307401e0088451700780e4401011502da84d10f985541b0014090790008802542c600304690710b0b9101e5040c48244a141d0003130a4a00c2e104d0400e4143c241c540080c802c5a480d84204000850f00d001c0a01405044401681e20100d0191280c0f900421001100f000c2c2524003148a081c0401d070390340402c0701d50340000c1c02e0b00d002440445030211070b4000c3c800030005103d01048003040c0d50070541c0c48444104440e004c1e11052242d00e071122040c00c1d0954a04207180600c0204005560040c442a04004403581050400500b01402d0b04c03804081101201030003521a00300044190805d0307048050b583c80025408030b4420034400b060046489410100d5040f0300b4449105c4503103514512400032100e100b07920406032100c0b40c041e6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 721935089 1250 721933839 721933871
    0xc020306040b010f230f0112050a0507120b09060909190c030308090c210102091306030611030c0a05030a0617060f0a151203030603081b0c1c0210020304050301 70
    0x70b0042400101001200180d1700880c072841e005403400f03d151050000c00b0540c00c1019405884c2d14107414400c1041194a0301c98a030b2064501c240b2500304041103a10b4410750080941c903449101c0e0f00c11514191000c0c0c80794890450250788140c082d10282142e40792028542c0c81d14219501126021440c20003a10800194000c68802c8038400e8466a100780c4512040c140c90302581120300d500014a1802c68214086405002e0f1101480c170700010716004035803000c640859248402d80c0c00080c0c40350310410030003810b4428401074041021100d420b606150006121070301c80e400f1032000300030b004404200e429840b540014018640d12000c8404003162150198903003508071110916840c400c03000680c00b840341c0c090a0964581d003400b2000c2035050850a12030761341040e000740c003090342e0798801200003002c49001f400b20303c906407040304c403103803d4410507032070940e1154011740030389019460100c40155a4000c4407150794100d0709070b00d084906030380403440c50049038049a8550300700000c3d01000d1410b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 721936339 1250 721935089 721935091
    0x301060504021e0d1b02014106130f060305070605030f0a050603010b130c030c020d05070206030406270606050a0506160609200f0d05150702101a01170f0601050a0c020306040b 77
    0x100b03421102e4502600c1c1e04116400b40000082c660980c50010200000c03030312231400e030702100040c1002880e0640fa012a0b00325000307100e600e9080d9603034010030700c2480420009103000b41810f2403e1813441c07400c0d4401b031b0b8041038003402000001e074403000030a030540e50030341200150403006011b80c0724458104440c40c0180200180840200b813400d058181118130116243c04900ba682c1c0302c40d49080c01cbd980c2400800c0d400103006550ba1655002d12880384029506060307068100400f0b01d601d004800d042610031915a548903034815001c101c4104800e4880406aa9811501131880004183ca90178083c02030402000010700490209581e51061560380419481c500b005131141400142e050090007408408010007810383c0c0c1c0303c981e1400001c00c080d00300980c0441a481919900d502d0062550306840c335140c20a1001c1d100031988200e60f580c00000102c0c0001041200c501a0516511040d0544c2c2d010f065541003000c00206201090301500c00e07071440c950b001c0c04403841413a250400d1030031500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 721937589 1250 721936339 721936361
    0x5012007060509060108070605090a12030807110f060606070302190c08104d070b070c0314160c030b041101050a0509010315031a060301060504021e0d1b0201 69
    0xb25100100b00c01e00ba0024000d41030350018002080414180603065074190060220554010041140440c680d2241103003442d27018401d4890320183d04000d68080c200141004c085007256100c84e44e4035108040014060390000780035603440d507071403419080c224280201c2c4213602020842c4035407001c00300141c11007400100e88214058461400c115851601568800c80c0c250300d85e66a08000b0081184020b10f00003064500c00c3c004561150f8072554000c2c1d03017201ca80301255a190003007540f82c00e000783c00c40c1042c2e0003080c1303140500850005940140441c9210510481981c4010440100c0c2920902c600100c95400c150784081c450707600d240440146e44101c03011a58004640c0d801d022550280c400e40715001b01a0326030b2403c00b00140011001000c4d00010082440d1b07180100101085549a101800c1c00032040020507a02d0102d00303040c01e43c0c21560200d07015a104100d2800204048081603070055181020035988040030103002e0040d0510003540080991800940030301c080d015800003c4d600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 721938839 1250 721937589 721937591
    0x613080f060615070302030d0509030715050703180f0609032007090b030102090a0e090a020d0510050f09070e060a0f0609060914060304080d090c0906170a1a040501200706 75
    0x403610340f41c0d03110340e0180100007400b50780280311078488605590400740e40300b80d4143c1220b0519a07251100d08c0034078103042c81c50b03445503520014404440c0d4140140f01c034148410560090400c01640c41c1c4404d00440c150203400c0d03d95070340510f0b0804d81b0980d0074003200d03044e201400c0c0c01d402d007100803142c84601130b20400c180186030070700c84e03015403c060003076400c50000186040e0840b0314000064581c41801495000b946c0615403007200107030b56920082440303a00400c001e06010007d51030340821120007070181440301a42804020080b0000280a070551b001c01031071203031588505010400102050700281052441e035100400c09d10380c0050841e0858140d5500c000990341c1d9a10b41c05116914a24034503000b00c01040080c0218000c02d00820f02515000c800240100c0c09403105002c200031908150000c81d1911810851160004081c4500320b00707072805403c000c1ca00b50390b40300358103502c200f464001e80c00050010701030100a51102c800902944800d40c0b603d103030394203c03011a91001c0c0c0229612 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 721940089 1250 721938839 721938859
    0x6020106170a140a0503030c0403232a09130b010605030c04030f02130f0605010201140903070b09070f03050d141201050f0418060f0c0c030e0613080f0606 68
    0x1038444035214034914402009000c54002c0c41e121041c1072200d40030700103400c1c4100e031200000035004000440c895010401d51a48860030340c40e044042c82d03460300f1010802e02d14904011000131000c100b841070580320b40d8040d1720018028440140055640c501300f039110042c9020084000074001002c00780910880c1000301c00e0b0f0301d400041e00e1502080e140e01080c01d074280410310020384d448244c4075441e030005040201490410780c008050300c400b10002403995494480c00c0155503024061000c407424000030301f10325464070040041c0d580c010b008000d00381c11000004110820780a00c0003201400840a4059009880e4117022750b9070740b1410b0181c4001120320700c0b0710445621a6065485042e0f400c210820700b03920301810040c00c80703145482203600ca45c0d601d45140040103c0180300064610440d40032402620518444088400ba06250014000440b90326070000e60311400c0104101411507400da121a41426121285255a004460a03104014540e102d0810009040303210729411506140a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 721941339 1250 721940089 721940099
    0x210a0203030c1b030a080910090803070609110328031403070203040302032e0b06090415030c090902090c0c0c130e100204180b06070f08040303110d090308072a06020106 74
    0x1d44c1174095009402c4500c2400041e05510b01300c0c0e22030050b0406441c2030f00e00316444101d410304503804440708840c80395440721201c04104242581703807410102107002d418100c664103400c404081c0c2c4c00800110070000340551100b01401488424081581c0c2d880c416202d1403c0b00e00a0360766482408168424400c070700541003481d2020b402041030200650111003401640e00c0160003500c40410001d82c842c000380b0050724103803141d200e0106a00c4a8003010b4001720300d10709180035002020f4000028041c00c26109c0d0000d41c4a21403e290410000c0002c15510305209000a00b051045d14205511410b189034009010f04260088244c0f6a80072341581d9046a020032014100d1080b846200300440240c031000408001991040c042204040c201c00d191900300e03603502868410302c00c0200d48554002c01e0600603d0b5101084012001741d0b0300c0208810b80c800e450182204106200040c10f817440003a40c101004400400381c407a00050324003d04121000d861003088207039150050000540c60a140024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 721942446 1107 721941339 721941343
    0x30603020909070303030e03040b07030c03031e091a04200d081b0f03040b0d0515030d030507030c08160503060a210c05040506210a0203030c1b03 64
    0x5445013949409800c54105d400c034103038240d006010501c801d80310b00040b18491a0075040510104449203412000340015440418020a592400c1c080c18851500b1807003605220b541c070300f811442c001c4d811150300d0100300c6c0d01614620403080140001c0d0034180100c0390b1a600039050030f003040c90a885e0786080e9403082d82001c24400544c3d07240c5071001810f0140c64070b491040c40103546014541240044580038166440c0010be648030040340914482a41c0d030380d00440068140c0e00c0c80c032304009001e0010b2000311911400f19042100c41c4c0398451140019a2194103111512000360000740c0080b101c1c0d0304001c3c080ca80020403400f0201c0c24421107290100001105c150303554011400c2d281c000c000903410343c403550041307080505102c01c5030ba07880c625100480b0080445c0c8014100040424a04514004040e40500000400500301c41020581074400b035032002d0603010990290003415 = true := by decide +kernel

theorem cover : BRFrame.Cov 721762589 721942446 := by
  have h0 := BRFrame.cov_init 721762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 721762589 ≤ n) (h2 : n < 721942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
