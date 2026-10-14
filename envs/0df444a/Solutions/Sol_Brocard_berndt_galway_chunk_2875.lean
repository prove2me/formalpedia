-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2875
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:00:01.223904+00:00
-- url     : https://prove2.me/submissions/72c3af7b-6914-4fa6-b88f-c1a0e16cf0c4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 516906474 ≤ n < 517086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 516907724 1250 516906474 516906521
    0x4020906042405130507020d1d0406032405010e070f05131502010516050405060d0b030a150506030c0109030b1807090b0312030103050c120a0605010e01140d050c04 72
    0x2001c00c2c080442c0007507240801c54092819060004481c10b1403180d0001520b1714041044058010409400d08a2a840d00c1d0b05024031a41c03a950f100d580040d811030300603203411000b02c2004210f007030002924500c002c0c060485480300e060701c030070b80741c2c2400741d0413442d4041360208602500411a4010540c41410704d6800c0c00d0715003024100d80e142c280d1103104a0501d801c1c07050321880d020303c5072940000328100b1071100b060383c061019120344610700c26035000380000500003007500042c0e17000c5a0302c02c2c6c5c000c0545942c1e0f42141407003025007043c05011441c003850400410014030340024000004041038585503020392541e103422280520042c000000080d12454042102e0014001f00700034007089040050540c20100c14507140810b03c42c58139905820400052022034000100c24600302811504072558407940740e1070500f00f030390002c002001c580c200780000c83c1c0307521100c0182d03060ba000d0000d90884607103202c0400800b1105030201401ca60460300b44640ca5040507009815906c441c800032000249 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 516908974 1250 516907724 516907751
    0x5130312080117061b0c01110a0309120503060306190b030a0501060611070f0b0708040f0b04050f1009060806270a0b120309010c15050412110102120402090604 70
    0x40e02580000c00103402400610085005070480944008500014113603850000b4000e00c0d2004114141e0070b0150002c111600040d409421091001207a610501c3c3c40344100d0502a0181510100440e0034451130078050b40230622650580c3d2280030024010a070503154030092505002020b83c0f00b894040d01c8048000703060701d042040726040c501c0384000040b418901701004015081003103030590725070407804042100314a101031a1068402407040103998205503d41960b02c0c3c82581e0061002c400340035030010b648003007440a8003c0395000e54007004001c0755602000300b10420132040313102083d03040005104070f9102d40000c07903001038068803140180700d602c100b500d0310845164034411100c2c0550100040c0c4c0d000c0e4002c0800748c8a0655511841d2200e4a0400d5100c1c0a004a01410082c01159110521541c0540c6058561201ca810020390405003800d591001e21100504007040002c01034500c0500148200d88070b400b40c62880c440b40b40c581c0ea0802581d20000f4100e9075105840fa02d6540c942c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 516910224 1250 516908974 516908993
    0xc0212071e150203070e0a12020108040803090102090d0807020a06031107060b01050903010e030d0b01020309030a0b0c190305060307061404030303020c1204080a0b090d140702210c120d020c01051303 87
    0x165100c4e10f403141c080486000300180007c0325001000c03040303102c051440050342c0000034a900664000801c3d5200e035074600780c5500902030420310350380c80b5003482150024029148002d040c8140252612024a5201c200c1902510220103203040d18210810482e004560a540020852001450181e24110162000900351420220301d0b40d1642c000186400b500c04c43c030b11522000150038000b440c10007801e880000d88a1030094009807031240503d00090001140008403400c48001d0b114144109107914002001000c048400030b02030b200346100450f00d58003030141101070141a480043c50182550307012000703500a8500b2100b181303d0000e0b0031500d01e540c040584050040c140041c01c1041641c100f1041103000603020342140d4010311030074103001d07600208801d142d400c1030007c656500c1032880030035903020f103805d00c6100d4101c038201c50040032034001c03842c40041d501c00c60324413041d508040216515050b41d224a030700981d004100181c4554028070150100c2c1240d420f807841041c0c0d0300c0c0c4651544 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 516911474 1250 516910224 516910231
    0xf060f170601090e0a03050a090803030406060e10030210050a03020405060433080f060105191e0e0f0f19080a12021b09060409150c0212071e150203 65
    0xc000c1588603990100004102540c018907480c6018403241c41600551500ca51030001c01800704840000c40c2200e0302d00542c001001051040e017160395034601406e00302c4c001c01003402480d03014800314020070080322061000200fa240c00608402c01d441c1074034810380702d6901c504000070605400317110024896031180040c0c001083d1404004610140074000c14440946454642500b20818041103030041c1d400b0490950200303002c2070304956900c41d140141c17002d0041c20842c0300407440f08000d904c46142c0c031080c200c103c0c0028410b031410845000c102a0759014143c1c6040340c01c80505040440315140c5403d0212605201410700703c103000700d4280810302076000341c000300815841264120100000020040c84103002c51010b04000100340890000c07543d4102e80c564480d0240501090a43d42c0300e0740092451988168804000c0c164810078030050500942600b016001d40c00e0001c24141c940004c440905520214075099410502c0b202c1d50705040014003541c180740104000c0c076505145d0b1005500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 516912724 1250 516911474 516911489
    0x460926060702030f0904050705121e100812030709120309031a0603101a0d030206060f09101208040b04030308040204061e0e040213111b060114040f060f 67
    0x2452544580040c0303000c00182240c0219030040000c00b44030310a0105840b1141c104507008586911120b8003102c55000ea4034180c408805040c0070b21024003050400580142c2c4001003407101a0b68600d1100341c14400e238070079819540c0184600c0b04041030890011503000d18203050510b082074540d6206c414004851004402045d00c0d0042801408035500103201c0c10701c4500444140ea18050b40881e4850010380408844280c407500d0703984c7e6000c0d145030f00d204ca071038002c0c1001a01081d07a040003561584151500703405110090745052040c10040120b501c1080e0905181082920b00141c103001c14040c1039064800000034807000c0703881b0300d846005000550107030b9580c0c0c1c1e480c105401007004503101c940c0503484007a00c0708001d090000d155030080e400c94007150b01112095542d80003142c0c1f0038218649041c0c01c585407131100e0300e13103030130010280101065150020722465440701d08155030711800e008a00e0400020304410b08640390680002c40e170320012071008a2980c6d131705e0b19070304504032042d04400d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 516913974 1250 516912724 516912779
    0x2090a0e090703031d0a061d04021801030605120303040b09031201090b01030b1f0c0804080102030f0117071d0403120e0609010b030115030206031b0f4609 68
    0x13810381c000a202d072503c030036490250980360004000b41110805116000500203050508624100548141002a40090410b6650f210581951401818031089840c0030a10348031012405041c01880400706c1c41014008500e16181c98a4010264030001c1422515200400c400c00d0580001461a4020405a000414808070b07500000d030a46020704000e50181525105811288581d400701001c128010300700100415110b0910760a18030843c0c00003042c5600010900c0311310000940007a04981010640c0004180818120750700c50b0002e20414160f4000540a03c20b002c45e007202c0903410520034101a8502c0c0482d60080b8240d81c3c03480d07103440d41600914100a40da032400c1c0540700501404600801c0b107a035820385a5a440d50007404060f01500d03000c8002501c0c07043c06c1d415040311081020b903030740d00d0345101c0d154024194410400381d40c1c0040001c1070700050941c599210400070030000120b040c0d4510b60309411011141141c031000820032000c00c0007604c5030b01e042181034503166891090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 516915224 1250 516913974 516913979
    0x2307080f0703020909030c100f060b0c0a03020105011d010b0a17100503061605030f090a02090907090f02070b0a0902042909100b03040f020a0e0a0222061202090a0e0907 74
    0x1319800200400480064000304400b0b40420808244440345d4040803034002402e0b000d0b591504024030360743e0440c0c4441080003900c401403800010b01401454441c0d8000d009683c0c840300720304884c250980c118050202000d00601c609070189014214418481ca400e042c8003a01d038442c0d078803219007900c800c03024410b1a14140000d08040c0082540190014580301521103440307802407162000911111007290004003082c0000400d128654036540c00605111060810051482c3c40710707074034800c01204514054000100388840d000782d425158005150544541d9201c80c0d80d0041c2c04600c0c405c9074000e42e20a0003182541d00c038000340409256004ca001841c0007403100b03100c2081805441c18413400e00c200c50030085000c4030f030122680309501040a4007100484d20101c2c3c4950959004091040d03078400411560061990103010040c0e04582440400d5010504000000740b80380034100000d2200391480d800f1a060350020000404080e0a4001e41a41c0d5040c207004800300b41c544465a800001d000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 516916474 1250 516915224 516915229
    0xc01021e0a17060a03170f040e070f0f0c030f0c0206030c0a2012130b120a0b0a03020a090222080102031008281b0605090114072307080f070302 63
    0x5050b16121445070584180c00c0600020301c1d00e608a1000a01d41d6107103034100e03c4c2c068240c40a603110000d80400482d1a103459804400c0d082e80e084441f040003071024900c1300700c0248100b541d40c0e0440306648525640e13aa498804a9030031940484100901641e28012401070321404015031142c4681c907800764a5400501c0001d200c0d51a40600c01056012840002210301002c5041c1a40540d4100c255a0318104505070190006480d4407841c0310703c00108803c041c14056030015881024850000c0108081001c10415003c3c1c4600010390001074040c801e00c20804503a00400a40818000705050038410f0310040d01c510405802003143ca94010040c00402d10001e52108090801c0901901d00c80000410249410240c050305815901d0100025824048100440188503d4004404d00401d4035000047c0035130340007400d0203000900c0c85080c000941d83c00c5045d1900e066001044500955802c01040c00c4000e1005a2032018058090001044c00c010050a0714003143c03c0042c1c4480740c50b5004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 516917724 1250 516916474 516916487
    0xa03060f0f0b0609061e04081608010e0c060c01060305030309032503020c09060a120f03080a02040e0c0a090f0e0a0b0409050a02010305070311070b18120f0c01021e0a 73
    0xc01c01212800e190441c5103559a0809a50903880141c5006840d40c600d03a5520002c05411406401175410000303012524001c00b14543c440c02c0d91210001d50340c5a41c030b110a030b0880d0040c03c06c100068001c0004500585001c0008240c1c104600c0001300366541ca0303480701419940240e8810440303510002d1511590042103005180401c5807914110055206803130113034940b0b41528a0904c00c3d04102d0000d8210b40d124405d940207840092980c0304000251701c0c1200aca14001c000680100e803001d00020351002e19402103070241c40205896070416201c503055003055802c1041d5540921070400c10228400704404200300080940c00010b402506007035071a003048904240010740110309280c401004544001880c2101c1035081c613000501e40d41d507035011002080f00041d0250900300000d5244240140406032900607900b05001d10490321382417075540d0350b681e0301544d012213110301806418049026031000d000c2d210b0001001503d440e110302202024242c800401420800b0042403c41b0282d80c40903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 516918974 1250 516917724 516917741
    0x16050a0e1f1701080f060f130609030806040e01050907031524062304140a080706030c020c0409030905060a050405030a06020c1009150f06080604030e10020a0b0106110c0a03060f 78
    0x801742c0280c02014181d6900c0e034000500240c0c91281301c0020810700040c540852076004e402410405c195411854010f2031a08180c50707140c80369052880c0c1916400040c4503d9000e0b0321100020b20449286550386001c080c2950803000080c1d0303580786100e2014001086c100449070642608507601030030004c0c003510380541102400e5403d441030b8400348002c10345131300f00e030242c40b1200e160310006402c50b000a0040710060300512814010300788001307021342c0c141c0c00c1b0b005882c1140d0240e400c50380c4030400344412591402e10140000b200510101b1090802c02e00600758102245001c514064494006c09c1c90310b60b149108556035a80000d0a002183c400e000440002410395401c0c03009100da912414002106041e15808003507440c5085141ea880e29403241000303010780f105a0788c01d481c00707003800340982c5800a2814040c01c0780c050b20403a62407000c03030480c00705580080001042e9080c290226118034550b100c405a6128404440c142039542038841c00095221340e0300820001441e003070354003d691106 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 516920224 1250 516918974 516918989
    0x907180e0303060618030f07090b12061501110f0a0c09290d150617031c0f0e0604230c010c0605060d0c0909020916050a0e1f1701 57
    0x822620803203012084036005032003111440e490712004040c1c0c1e42440061413a0507898418078442d00c030207170f1020514000b15000403000b045034041140502c0010f00400d018100640c04c070074002141e044012009980104062502018425112440c1881d1240c010300302002c6074400925082008103106081e00036041301441440803034110800d0840284041139401180d0812801303c20301506c4403c0043d4035139421401182c04014400442e0300103006c0303400381940003d04200a02c4100c0c40c00402c50f040311903005034900065600001c00001840c040c00404086516110043d07604001081240e003d14011521440880074a00c80301070401c240c0341c517200301d40e04030014004542ea0004001c1c3d01240e048500480d40d55120400110035400200d0010034558024102180c3c556030fa601c4001154425100d04041d600d9501d0b07202e402c2c0c0e00e46044070300004c40402446944611442c08006c40c2040904a103040b50040105100442404d03540030b0b002400019441c5a0414007204160040061 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 516921474 1250 516920224 516920231
    0x70e031209041a180712020a03020309070602070605030406051b03010b03070905030d20010e03070c03140a0f0204023402190602210712080906060f03030a0c03030212090718 76
    0x40404548450716051341e45202018081c000352806004402d540d9409040440840d507504103008060020b41003550381d41110b20070b544e008900180000b5654080e00c0d2140c8a01c1d003190341381d640d204040c10005180061312541101c82424000e20b44000d58060b080d21015545c0741d14218000810141196004038400e610a080c9202101e42141812003130044040ca81c180754440e45500501510002100024030f1000207445c40500c046114041c003924452541141e1020990450950328209924042d01d400c8006003032070700600c0c15500805801402c1c15042e001414503c0b03038500c0c528030880129465525a04400e01145400b03508080f001d0000380b107081029040000081d07441c805600c20415100715001a40103241e4400161607046030312029456595890101c01490f02e0703819a002007191241c200850964545901490195040a8019410700144030821900341c004036806405140c1c5c20001c4040c280c180c070b00e82070301c200ea1120040c40128580725800d1001e180010040115030318 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 516922724 1250 516921474 516921521
    0x30c1b07030809060901020703051b01091a0414030c3601030b06010c021c0819020f1b04060906090605030f0607080406200d0f051f03060203070e03120904 68
    0x805010344107045410f0b02c0158440c1d20905c0141d103030500a40024043e44038812600c0884940c43d00540c4682000782d03120b400c080c0c0c1d503a10105007818041c0074200701c86e40602c01030100c820401002132a6500050444958003c03034400b041315500d1040325180c00c0e1040c1641078502c1c401c0340210074041300f80404440110740c9161a001c42d550401741000741004861040346d41590350342094042941c498048179800380c0750516000003079502410282c2c0d450007400400c081d1040c000703e054626491020054a4940040c0d001c40341c1c54600e40040d0b175840b0746d89510226080c520380c80340802400b60b0700c400169440c00c10040600d800c0c035100880c1d24a6100388200411242d1206480350041d0b400000450703042070401031440c840c4410342c64007210031400f20f1140c03d001903540000c0100c000d504010881507c800b5020762400340681c0c00141d0402c030781c407401c00c009401a40110381c4240c0364900784661003030030000203040c60400e0800c868020400704180105140c20300c2a882c1c0d9140601c1542c00804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 516923974 1250 516922724 516922733
    0x122d060605090102190627050705300118030509040e1615020102040302060307030504030908031e090a05040903080109050f01030c050607050c04150f05091e07030908030c1b0703 78
    0x1d001c42d07942011703581080c0002080120715080044a54807150034580400710300c0000c031014060040c01900d40344a040400680760400c86140c101e07200d10000100005030740240c00c01081030001c3c1300390899645e980035070320124900ca90003061a9209039101ca82d59000c107820001071395004800e1084a4001143c103e2540d0360140c0014221013002245110005002209900900507944041c2d0069000002c0000c00d541c55407283d4403880c82510740041c1c9688400116581c4c1c006d4901d685260803030a180c070305d00414403034058000c0900c01000814850f0b1a00007040c10340b02030401c03c5001c9614900140050070303090040b2a804110850f01004030340c5551105003002c29a4482c0600034040040c000b002e002e000d004c1400c4e4188090018030002c0c0810703001d01003e02c6640724181c00c140c150a07000c1707020301d0040d09550003500003c0d0b1138168050107200105041d040640f4460525a85031105800a0386c4440654861b01d101410507807038055519141800d081000845e1100d5040101d00b400040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 516925224 1250 516923974 516923983
    0xe18011707150e0d150507050405040e06070527060d090b010801050601020c0402031f0e090c18011509030f0c060f0e180a0608100f1b0906122d060605090102 69
    0x90845604000444c507090208201003d90420184241400c041000054000d4024402c070350098808210f103d00003c600380d00d030b01040d02c411700003800422680454204460391040c2e110a00c3c41c0b80b0401304a400006000303944025004001142c80750154414002c402e4481801003000c240240120314203040000c1d11900001c001603c01c580c04004070364101400c0d1103008042031b14400c5071600c03546a00c038042c040e00d01219140f2032445500220072442c10415001507042604c80000d61059080c41c0100e4452808030240e10308001400300000040b4071000d0800d4000f83c01003814194441c04c2038001080840b034502080c0c180f0148000001054039840729602b81c5184000e180b50440e184d0246902c003901c5e4640c00605248a94075070880f1400d030302e5012148600b10041c08104035641d440201c0c040c6a00008804041008000100403135030183e0990380e15248004c000240d0440c900649290814442e1030800c00004001c0740d50200070104c0c82040040c01260802a08000395840000e684 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 516926474 1250 516925224 516925247
    0x81507030c030b030d1808010b0a0e0406110d0203010812030106020a0318150905030114010b030f04050a020d0501052a0a120207080a050a1209020906010e1801170715 73
    0x806039100a0700c001a0b1181c0d100c00000007004003660040040068001e103890202101d0403083d02813503d0001d11890140308001d010100545020300140c070b8210307031031454070000700161401030b00d460360540c100301c1c80b00c010455100c1c5504010b80325410003080600d400040300e035414600320200b006102040e0001960b0060a6241c80c011003c030031492070307910340140141d12810303105180b25040c0141c2c9030091030100903648180d00800003101d501c203148a44100038480e04a0100d420404100308900e090030b201c0c2c2c01400b40e01103944003201c650128601c00041d00044d1440e942d5402408414158070b204642048150b05010501290600c0e02c90994481c4410f02030500207080e50003a484031281c0c058900c2d05400512040e16900a4200601140d01c2290707282c001961004821103c203066100701c0b00c480740c000e48000c902e0380d0f8140040d0b0351141809059a88102811040562200303140c2c540703030203040301803c0068218265100c1c68941142500030750351000750901070228035540142031045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 516927724 1250 516926474 516926477
    0x8030f03041e02120d020f0307110d0f0206030f04060e010504081614010c02030c06090106080303040807020f090106030e01230c07020607050106092307020c0103150e04120801081507 80
    0x41c4620651a0048a00d0b030340803000750000900f18039400880004110b03119a10459000e0f2240b42c1140249643c0301c0c4110700c4020521621071b440c0d103d07642045000c0c01d6a0030321507044001c02a116400090030768008458803c40030a0410401c42009840e00800301010140002449141003680c0d99041130300522080c926800c407080d50b02c80600c900c01e2880d80801d540c4000804c011b807a11f0000039141d0f8000390002d0102d100d9000402c4014905224107821200c0341070280d401c41d10f4030b58a51006034015142640c0c40400e0081001283d994030155a000780116100082c0320172107140e01c00c0c00d440901c041c03031071060004000703640c082442c406065403180495444540d1580c0a100041d414060042c02401541c038000003c02d0070f4000361b0101b0002c4a48a05004070744018904c0b100000004031a10001a0001244040300394001d8004240e4a0380c07120700404080d44804510884010460341501e83c0800c00035214141c0b9000780b4000d0160002401401446545400e00c420b84480070f0410030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 516928974 1250 516927724 516927743
    0x130c060305070c1704090203130204060e070c03030b0609031b040f0603081204030311160507151b03090801020c01091506060504060f030b1809120a14070602250c08030f0304 76
    0x1020031301100c1c0601780c143c41c210740b00c3c10240304c1a440303d070a10f04101d0003140340078008180841110507891080c011640c4c0c400c2d00e18150354040300034100c007612590b017100302400798042c0381e40d0600c0b03038030304c22a01041942800385a070001c20042d40e0b400c040303450809180c10380620100d03d24404a4000750851b001421aa41702d618040700101a220341c02800258080303004801040361a00301d8000328012011035000c59141d4440b0111445e0482d00040031580c800c81c1000108102c07048508214020b040844155545d480c1190a80e4480c00100e4900d942d51800901041800e16000798880800d85041100500b061405030a501c901e0140005210780000740c92100d520a810544c0401c00151880b4000c0e154080f01e41c1b243c0805480ca45424001e64190003100c00d052810356006507426551102d000005586040300c40e4802d000030b0b20800d800308002d44c42900b40c40146118495846941c682c0003c00c1d0500c0020409903401400711600204200d029400c880420b990300300b03401400740c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 516930224 1250 516928974 516929003
    0xb0604060311040b040806010f050102031809090c04050702011e0b09070804061b0504051c0507150c0506010b030402010f1b0201030209040f05161805090705030915130c060305070c 79
    0xb502d40d000e158841d485803100080d020510400100c0c03068101c454510968a00603200c2c0010381e142c1c01140c00c0c0020140a205410806180c1400c1d016080090f1600340d541454103100480c003550811a0f00b600903039100d440b80d0003a5805941e01041c1850088001c00c030204040000540440c00640318104011a44000c5014401540c0c8031140d100c1c0c40324202ca006408400001c0c04940103841464890b450400462042840126880101580c041e010701040313401d1101d40401d1240d05446c140411496803d6400020400c020041c060709003c02c4441c0c0b43d00c1c251000400d0100c00c0780b10901001601d80d1411207005104c0c0441c01e6882d42407d01688501548001c5002008242c6032101305500b031609210005a00d0070384451514015a110700ca103540d00040000420240d119564110003c48000750f000f030f126902960700540c581e0240d60b00301c0490301e541e559800041d11080c03039200c10b401500c41000102d503d100d00414ac1c60400340000c1c078112601070309031200300602810102e40141c0ba0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 516931474 1250 516930224 516930251
    0x6031506030f150f060402070210050f1309050114030f0606010c020f06070b010509090a0b010312180b130e0c1c020919261002070201020a15050405060a0b06040603 72
    0x4000c010414070b000c846a80c0503510042d01004070030b85000d013000d41d110020440c0c1d41030034000c0300c0f0195000350030240681c04052084460307602c448048429680c051215040c40070001d01890000e00b08501c1c086519410110a49901e90036801c0c2d0030b219500403105d0400301040403840c4ca074080001d08020505104500106200c41c50350180742c5d07031083c4c002a150003001601c0108a0507030b502928201c0880d0f4401c48840c1d901c0000b4440a404040da0900400c001144003030060302c120650316080e1852555200240b48122040d00310f10444400418590440360002100c04003d014109202c2c0721400c1549004c0164480c40c440004200814120f6080e104a80e0301102c0465501501382c2c500d0380900160405800a580a0b115400d100458030098819103403c00000315503100015020803c0321040c20002980401030486c194024103800b80f01240f0b04001c074103d40020044007040341d01d00b514001d1700340b810003000d031800f0710b26001511115868410640d0181e030194100000c1202c1202c1c1c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 516932724 1250 516931474 516931483
    0x1514010c060204172808090a08120409110306090609060a0e10080709050c0405011b05010c0e09100e0c1c06121a010e0606030703240f0503060603150603 67
    0x401400d41d40c000100003590703411070841e144a100321481504c2c0c65005040c2800100d480b052031600d00c004005440001091494008141412000b0700d40300c4100c2d5188621410304400c040200206d420100c0c003041000014000c14100d281600d54417495860401c0c00035218081c00351285011302c0c0001e000590a03110340c045403020b0034004070544458074191103240c9001d007660260048902070304400290304001d03401682e010342e405c407424609107070a15004403680ca01100c081129400100010301c040b82082c8a98a4501010303035643c240250010240408940c024200c800c1c40400007108118a003203401d0880d401c0111840419a6000340300c1284044031100180e13104220b10301440000c0c1c0414884000708a1840b5031030b403146600c030500b5498a054409d1141e0850600f200b00020737120b1512400441c0d208072503050019103003240f00e9142c5400011440c0d0440300140750354041c00a0304e81c1d000110f00804c400c400800b05440c0c10b0340403a40319105402c0100c11200000701041641c3d0702840f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 516933974 1250 516932724 516932747
    0x203280b030a06060f061e0305071202040906260723090c0403050111030c03070c0c0305150907050a03050c120c0d03050d051602030a121d010b030c04151401 69
    0x5040311520005402e00700004d00c1e5902c1500d1580070303005800540f2901075890340c0e0306070200c1418054101407040741075001d000010b00e03d8041020a41240803a92907920203400600010f6100140c140d003401003444104d080c201003e050002184490400003000085800545104c425050700d042c4c1d000a042520030081c42649900810700010081d1600402014200301c90041000384484164078055020b40d200035541c40c0310507c82040000c040a01409000b01c14501c03d0b84090701d004c2d0389417070b02401d10710751110042a52540c0c00034041540001c01c100e101510040715441842c520316924981d84284803104280240c4040f507e0700824802800780d1b605080001c0c01029465040b40303801403142e44030507400c116051818000c104074180030741c0c0f80d08010056030011880d01d458008160b0b5012032501e18440090340b9640f5914036130101e210300f0485c1c908610004103500300c03c4020142080b02c15140356018902c1d1805101480b030500c045442160420100c0389034002d1040700482c0d201c54081c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 516935224 1250 516933974 516933979
    0xc011422080312190903080c09010210020c010203061203030c16020f0a061e0e300f0309090c09060f0a0201060306050408070b090d120b1f030905100203280b 69
    0x200e483c102c0241c00340c000da8402c4a0303080707031046030303500c03e80c2c0c0281103600101001d8002a50400010140c1414000909d08990140100e80550070b4501c0b6100680c3d001581c00440c5035000320501019080000c401341a22a4100181d4210701d04104034030f8490013141e03803048100e9804800a015034640300090506024080c0280c0301c848c0c1c54150240c4a0b114040340c3c200e0201e6858035110300c152080d683c19035550f400401000d4522003130781c00c0c5c81c40c0603035228101210f05003c04000c0200c0342d041020b091340d4900480036544405a960400a244000a007049a5050100103106d80c65444508447d02200040d811a80b0741107440412801441c843d08024407180c581801c0c0001d100c02100540380c07840c030a00303c01400d90341e000161601e81482581410100d1031468611144502c1500144203039900a0000d0500280b40f4034082000c0711800b10100201c0d54582110040c0a4140a1b54800001d12a81940f8505201c0115000c043c00f0701800229242d190380000e0030032680340c00c22452541300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 516936474 1250 516935224 516935227
    0xf020d050a02030103030908190803060303280f020c0306131401050705040f06110c0103052a0a03050c030702120703032a0f030902130c0507021e030c0114220803 71
    0x5100600c003d50003070005401159030808005006d803000100b41124070550046c0c0d58843c078942d91414a650409024150705010905c010701c101c1c00c104a160030300d07010142216034155007101d4064100b0b0704400d081000c5411070000d00c113250318000ae1103500f1a103101c04a8160400c1424814000b403120741c0b114500d54206028030140c264010050301c10788183c0283c401600f5660320090300c00803d881521f000f9a0000030080501e51b0007540086d030710400401c440488d101c102d940191000d004401058140f0002081d50f00f0007a60612840d0340c094600b4100d1499410083c10207907036203901c5c0081034208500014000201842a080700070544c1060751414009404240c401c44040300c0300f400000000d6040411808a40c8a401a041d80b01d8000e4010031500f001001c0c100c003d0000060091305006e0304100520068958407868030320070b44c1d100300c9000020450801c00d401c08103076611190400024010246495000400b19182c003944c850030300400c420440075030150000145d0100c1000d000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 516937724 1250 516936474 516936481
    0x7180e0c1909030201120207020906090405010b1315090917031f15110601050d0204020906120408120609010e0c0d090503040b04050301060902160314070c0311010e090411040f020d05 80
    0x1040b08800d400e8a1003600d4080b000d04a07070301c5880403401204006940a040c05000c6045824050001307500300d809036001040409055010a1100c407080390b641c84010b5a5040880c500300d0079080800c042d0403100424443c190300f544510868409041c000d081d001000004a11402411074000e034402c2920205114000c1e5940c02005460300c0012100010400414010544150204036941aa103006140504c05e1210b5000e01000707402c02141755801032800c026164124400d400b845214070b11950340f580d40c03026002940e5400c51000703071806000d07807410801402060100007006500441544160384c540002c00142c0c8050040c0c001c01400b640030000307000c5410090701c0c008200765035054000384034080d5a5480340302244184aa05c1181508400074200040d20550001103020442d110301410a006900d0743c03550b040017680b04440080f0004104441942c11880b00852024111440701480c0340a8481c001c3d030480c400100c603c1283d503090006c0c84080c0f0742e410798a401c1c00381c0c58104410726 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 516938974 1250 516937724 516937727
    0x40b0708180301090f020111120301060c06090639050a36090b0a03050c011407150903030c0c030801030b0c0408060901061e1208180603090106050907180e0c19 70
    0x83d007501701603002403081407850441d12400241c00152000c20507089245a103000021590120550401c445030740e1203281c600c0110b00540980c10402004030745240741c6081d51155250444c0c012801042e00628820783e040100d6000401e1f00c4400c046801c1c5082980c00f55003882458000c038030301c90f034280c5076890321100e40d1000511045054400c0b0883c00c02c03c0114100c02c204c0303011040d100080c05a40003803401d00155200e4640905500180000c035410300340130b070791640348289007002070151141d075400c6140c1c10f150341802140b000051508207452078581a880007010500140405003424420388081480704001c8800c913001000c0020a0301d0290501d07c1025000c0d005d1485892907d0480003a40750640407800c0f4900c088a0103120300665510095640b21140d4001d243c42801380c0341c000c0c88480054980728004d52003020301c000000b51090400040142c6d030200a0100b400700100303a44049003543c00e800d109400e480101d5200a00c81e501d4008181c1c06c0c1c400c10402d00b1880c0e1101c81281307480c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 516940224 1250 516938974 516938993
    0xe09070504090c0e131103011103040807050c0d0312150302010e12420702031b010f230a021606090f0c0611060702030a0503280204140405060303040b070818030109 72
    0x1500c1b030001c0aa00c01442000c01d0709070703031003500059100c18040000c06c001601150042c4105c42c440c00c140d5005c02c000130001000342c460103209501299108840001c011058816404203030803071642100c8a41c00c540000b420181003154803801071002161909820b04104840c40550001c1d040340f610342150b804000342081405000309900a0444203030710901d4280221452047c1c060754019820082e00c4150304090aca5002c403071051075540c900d0060300b005103502400d880d4800301402000901008140c041150344014103403808580b040c0300028080072004c0079000c05070380104000c1842080350034031040200100d00010320001e40d034a000100070b60410a500700c40841c50003034500d107540e0b80a0603602c17880303201e0186002580070400513030701c0f203607822241c006903000c1e04c00062000742a0712103400302d0380180c101d00790000c20103080780c14514160140991100e030a070051410b00385490380b907185901138414010709104001c10842c0500d02e0010001d511204014007d01403040c503401e102004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 516941474 1250 516940224 516940261
    0x611011512060b040209100c0303060803032401020c0114090312040f05031005091507170907080c010e0307030201081905010f060e032e0f240e09070504090c0e 70
    0x4042c141580d0b0145442c4c82e100343d8040c10b1002c0e0040450b0058141c01301c89001d04807070100c040c140d50342e01c00300c3d03100e1f004c00c0603500c100807000a01e082401b2100180700561030107070103507046603c041c0720340026036440080184c4801081d00c0e0a611029a400003904003011071500711082c02000c1000580300480d202042d00b102c005400b5207103408503100c000400c0d01d4086030b01c600280d00031003508281c0391035042c41e268011501d207889040c0801c00e6007910b610002c11f035806180c41d400030109110118050105400004003401c000802c0e1500074040b0740c5503000c0307102c040d05101b0544001340b0807032120341c82910b8215800310104034540e15841501600351039400398900003004076003030400c0c5003000074242a00e410513038104400105040640900600c56024070b10a06848003002c2e24828824094211008128000081503030769000342041c40903000e43c841480303a2044800c2c401e08401c08a00c450640e18207aa001c04c21405a083c511140040f0382e00c41d949a50107441007001d4011150100080d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 516942724 1250 516941474 516941483
    0x80105040f02120d0c0f0309030b090f160602070b0a02010204050d15050606120f0402040e07091b03020a08011e050604091a03121b0a061b0314010f0611011512 70
    0x645200c2955141d9600c40c003a4000c4c00b1810700700c02e06000c03424058040000034880d2401c1c005a6442380d68056500c0020380d0110b40c6648a15044030f5480c1085c40003006850705035080f26007203454000025070b1544c440c815080d114400140e060001c0b4400e4040320f015200c00f9209001840301450301c4041c04c01d0001d40c4401c00c0c3e18007004201c1a151210494810801c80d4070b11640d40d072218400090b20490142040740d100c0e681307c01241007200244150001845c80a078009484810200000d250300690542c0204041c410804c4044841e00885800d0540302a446480e406844000000b205080c0641129070702840c045400a8000c00d03a4200810f0130014008036412100d012040c140c2e10340030802803824961040c4022074881304800010514241c03210200c684203103280d110035003101c16000088030205180d8010880c0c1036050b0045244a4004600c9e100c00c6600d051f13440e00c14804130340191400c000680d203004e041d40c0d400750003144072a00303002c0302d140003651385490680401d4021103041320b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 516943974 1250 516942724 516942739
    0xd0501060330032a1229031513170417010c020a0209010b13030b010b0405011e090311061201090e01060902030408031f0e0a0f050a051003080d06080105040f02 70
    0x1200715100b8050324000142000e130076a0002003100c007501c0c0034006482013004100d00032aa0b00b0600305030780140591180d041250b05031980c409022019003c01d6458814000c1d80585480c4c2007072a5a2214194003038a088098100b023005490000d02810882118102c40784c40800e0100d520951a04280100051903000f00841c8110000c141e840e000b011201079488841c40e03004112012102c030003001d455569002603801d00d80c5980e5031100b190b00c00c0c0c1015401c054080b9007801a56000401a680403003541d051881c0f080303090000030044040b6000003004280d007000300159580b44d0100340c5e2511984004800100e40e11514410003d12081d680121107600b00b060000d150005403017182d0185030070210052540c2ea0710900007500751160202d0000405810f04000381c1c00f00795488117801110740703000101c0c40c0711005000d0070603100b014040010391803400c1c042c08100003080000c82c1c02c495002e5500c540f0303003401b010400c00500007640030340c07115400d0404000800c528503540044052088801d40d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 516945224 1250 516943974 516944063
    0xd05030c0c0a060c150f02090a0902040306060e0907060e060910031401090c0225031208010504050a0605010c0b06030f0a031e020d09060e06090402070b04060e06070e0d05010603 78
    0x4558021000c2c2d400781c4501510310b400010b18200303401031b610340814580054589146100492001c0711554040500e00c2d60125050040058070b01036040282800c419400590804d03541c50390b25064a4843d54043c4400e2060300f2006403102015109041c10042c2001c02c10445000c0c045c021b041140c0c0e44159070b0003050004918000d0b14032407003104580d030b0350082001c0c200843e550100d44840f0280400220040079000001602c020000101c14010350350b840c0095160030b0500c0b00f5180003400701c43d00982000f07030074005641d1000d9240c1c1e9031a0031807100c0c071060304c0d01e80109051403c4409ca0340d0080c01003000d0300061540007102e65101c92050f800048000104e035030100c0c0c841c0f094100c0b03000001d075407081c10070486126580740110140000c00301480d1403210300018080ba8881103045030b01d08001c00c1008144000c62103600030130039a00c405440c482c0b41854005003c4803858a0292080012188442c244202580140003035a4024121904131020741c50b071208210407051044032620015506 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 516946474 1250 516945224 516945227
    0xd0f030c09050d02030f0d11070b090105090d02040b12010903140c190515010f061106070807030e01020f0408011b0201110409091103070b0d0b01080103020607020f0d05030c0c0a06 79
    0x1561140d81881e07507298251420304080002024201034266814441d52811101011044c005410054801c1d20b5103a80021003210642c00c051950b4021001d0b600d0a01c0030244690300003007111040c160403a140d4514441c6480060002d2003405031680d04100c001c460f035100b00105601000403140282c4403c074203226100f0206e000d510880c41281c1640c2c20503034015115462525800141c03610400c103461418000000d0a014104240d10662754207a09880c100f000300d0b0050391603007068564402518180c0342041c00a040424054084402c1551f16801458115800c3d81540e291400318001e107540c883e691008507000e0411444d858441e00101c0c020550200d00500c100007040301c040d0001070401d841e1400d000020400c625058845002111031b01c00a030360107011003c00340807208440307625190b220341c1b054110f5000280c428144800d01005202682e500d0042d510390301d40c1142d060040410800210f64541401d1000400314840440c01c42956023000c203900301c0c44041965074202c00c82d0780c1c440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 516947724 1250 516946474 516946481
    0x70c0f0801110301050a0e06060c031201050f0d030f050918010b070b061002101a1207030c0807060804150e060c03060f010c080a03050414030705030403211d030705120d0f03 76
    0x90170307038414500c2074100015007070300803200c1d030245008000e1400c050550460908681c8102801c405c100e0a007c018002d6103020603040d0410313401900c0c0c8000780e900682d00030740b0390100c000020040c48404504a49565204440118004149052020305503910200380340c041c1c10905080b902c0780d20350700000d126804c281c19441542507441d4001c194980c0102d024a00030402414041d02c0b10341410394406903622603d6444956886010043c03440600c1d6083c8640e4201c9581c000710182d800c011020400c40358000034841d0002c0e048076000030060f850003810002412a02d4040c200f43c000c8508104040541e01c2c00b540c4101c1c002c2e9500101c0e030000500444200443c46002131861030140014106a44a680403980c05803196490002c00c00030060307030710b01d990400e81c41201e055100007010b10030000c50500c0e403000d551a044840c451b50b510700b00040c1540c0b0a020300400d559580418845445c0d82c20416403008003c060503034920041051441c0d615410b0315121080451611140d10300c03c03511034031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 516948974 1250 516947724 516947729
    0x10e06060a081605070210020604050607030b0d2a17010e010c2f030c0a0317040b07050c03040f03080a0e0a1406070203070803030f16080402130e03070c0f0801110301 73
    0x10746107060b80e620200400c5183c1c5a007190704080100c1440700c40f0050f154a07948144015082d00141114546484c08914180005102074101400c0403024011a12050703007490328241d01c160070600c0041010310300d1049850140f940228114030741e40c0055002d18210091120740ba824000344844a9480001801c0c2c40440d280300e40000c0c0080300082a04968140381500d0543e881440c1055000d141c40c1b1a1a6803c0740043c01200d400900c44101007580080880a6062501e043d101c450314140d00c070140f001034010041000d00500251401440805100320b4003d452605080c41c0100d440381094103040d04103060340004500c3c6008254034a02e03051007200c046400411540710811007240601030590005030007280c040c42441c00c0406d074020140069440340003461a445114603100ea40040e504014181d070f0420301a1241c00d0002680381d92103403032603000f8113078400320b110382498141601d1071068580180c81d2002c256408103034520403c0c030700d0085800c000003d00040b400d13103c1d00041da110a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 516950224 1250 516948974 516948977
    0x6031b12170901170106030209012015100f0b1905093109061505061c090f051e0c0609030307020906150f0702010305070e090604090c150206010e06060a 67
    0x1260625005154900910b080981032401300c400040c3d103042c10800980a802c150b021030380100740b58243c0d503400899000c115044400c1680314415100f082e64440d440c41c0e04041089141e02c0000b002081c8601613580180802c0300b100420b96079420400c0000d8000c0b810740f40030805a1510751002038071038002e0350340c1c140e0000c00e0028000c092880300361000300011482a4250050b01417841c00312058031819941600600c0003003140d07035200f4554074801e03001d41c0049e845000240910314030320043d24100762000b003030b003900000d01733640314103103013500c0594500001d06606c034581c400401c0140c2c0107048000742c60488111030000f05018108140350082c00a15030301648284010300251509a071004d41054011b00803e003080640d030230868503540016005900694006020011941c0c144a466405680c6241c0f006400f094a000686c20b1b11000d84041c0c416601c03520034a0500c6058a00030f4028200c90443c00608800d580d4080e444410034400e280070b40c100b881c00601682481c60460f00c3c0080d25 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 516951474 1250 516950224 516950243
    0x2030a14060f10180b04050310060b0409090c12120908061b0f0903010504050a0b0a0c08010308030406060b130e10081c02030c031219111b01090606031b12 68
    0x10043c4414014400e01d60350400c030511203145040c4003018910b0016060029031070381e80d1820310301890328102184441c004500d10701102088012031030826142a10341c0d000d40420904018141112108400c1d001011401800c040300343c208852a031410100c03580c95114048145c2c0e44000f0349458060032504142000c2c5505842803040804070003c10100500c80442800c08410601080c211142124115030952004031004c0a03c0702c1c00710800e1b80606052814000308021610003459401c06210080030024080041070420000d40c110f00040c101001145803100844240b1040d203920074844c40f90700705621008500004c0400141d0707015035404400901ca111a45002d600084c101d05540c14214002848031000034107041c0300901480382061f5840802d41001090005074090007501c5825880c81c080c151000364000c2d406031a8808900d1400414606607000d603035000d0f11800d2001402d40303150040100400a81d03100b074500d0031110307001e40340000e9100c000006602c840135001a046121 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 516952724 1250 516951474 516951499
    0x170109080a030e0f01051e090c030c0f04180c210203030a0809190609060608010c0f051806221a07021519090e07050f07151e02030a1406 60
    0xb83c00540e00c91074100c0845641c41980a101803c540e41a181d05940f5002c101018985202c000105a04801e5081c00b0340070304204200060360700d0301e20301d444c0350080e4485503034070059542d07a034000c0100100b842090544002e0b00d28045003029141d000e001100600c881c0103040107181e08400d0101035030b010300194904100140d0a40310010000d110b0301c0c0d00e10031014003881401604034402d5500e80f0641c0c000c18854400e00e0020240c4100d50000f82e020303850103884004042d801048201c2c80e00f0355007040790340c0e20310400c1c1e0301e038604985444803a0441000907400c00d40c0385040100480000011a9001500340c0b0b031880e541007200c680140118999044c06080003502c0d00801c000310040d0030400043c5003120048003022400fa500c84080d01040b20050301b0048107070b02107221980070486181491500c441010711800b02c0c0070703050002d400070301c0300d6003c9800360b0007540c01800d00d400040400c2e40f4a41c900600000a5070007129542c0e255401c0241002c1d0304050000341c1e03401070300c00070000c1c00d10a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 516953974 1250 516952724 516952727
    0x302030f0a15150317120a09021305150307060e0a09141f0e070c05060606162301020c0604063b1e0d23030f0403090801050a06170109080a 61
    0x3c0d01c01d0748415030710f81c1440004006020314014461100500c10302c90344613001900c01c043c141c2c00040c12a09440c0c200200c0c0342c0166120301e0100d18141e19540d00141035121f40c03246400c00700005200c907401d4030601c0300100d0090f803c00710f00c46003103800316188503455448581e0401a00d00c6480504828001c0c20b0201d55080302c091f410001848550f030002c1d20050707031540c011311540010b481041c0464008089032040c00014061641d20400a07561035281600707918070314032042d41c0410090207054403010084060900740ca82c4081c9079429200a546035912074003010703100c0509031011200c0501d0441a1070031140362020346240c0b007002c118010550040003400c0d0024512010145d845809102d0b0a118104c00c0c0f00f10040301c43c801c42008045c455815200a0803020808885801c0c9100444050084e030713141c1c00880390310070b00354500225503456514080d607000035260440e10041d4205410850b07246501d9016000f281e9442c4036a94084042813601070888444000c00b90040008210040c0801d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 516955224 1250 516953974 516953981
    0x130f05030a080a1202030c0405120705130218030d0224060a0b03060f0d0803090f060411040902030304030c03080306100f140f0702040e0312091507082805010302030f0a15 75
    0x12009081c032407008110031300e03544100e80c0122145140300a0125042c0900d007030442501904040c050000c2c04081c0c244000540c00c480d1a6a5203e040c640000e05022410f00040d48180c1d003030b00180889a22010303c8801039100c0980032400c008406034600810310f015580140076003e03074800f82c420751146042401e0a5920350005048a400103068201c800c3e007038640082d02c4c20300b02d000c0d50300ca94403410301c0030841e42840203003030301c550b0715070b0054080c0030100b0284484481d20650480300090344600134070229065004681c80030700a400328110000074000b249005601ca01011540f000c1d291082c64410344813007211104400005008200c140040c0554400412000000c03840d85420408150700090664a0b52032420364540c102041d15595141c1500341581c01a0603400070301240b000d440340c5104040c2000301072204100320300000c280c5e1403144e030354151182c1c1c04a0071b0071100186910042d0010700001e101c200e01034811809001500d20020820b100b07035079402040702002807070201d02d13100034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 516956474 1250 516955224 516955237
    0x203071103070f030f0203070803061e06030c0408070b0c060a05190f090506010902090d060b060d02210106090b1204020a05120d08060306041a090a0611130f05030a08 73
    0x40c030055441512803024100068202d161041400e080c1c41901868024500b04450040c041035500c24094240010254010740b9841003082d05c00d4098084a1107030600e4044408100c16049107002080c001c460003032100500c159600c2c50102c80c505035454440d2040c5215980b201d580302d4201e0740100b240e000301600515001440d11708001070800650b69141c007241c1d18000e0104d4450f544460410801805000440c01080203030021800c100403000400c104145000008041c0b95968406031803682d05c0d103050b42c030a10411070303086448440d505212203d950306000b8007496801c003503000080c0c2500c1880b4110036a2a001129401c0451180301c2c1820702c030b0301400490f40620031480114550715010500069034583c02c0c02000b0702c0c01d403104060014100a016107000c0c0d0400300c1040081460134069002810720008032a85d607940310901d05060181012005102a003440c0d00711800c0040c440243c078001c2074036540f241125580d64003800c8808514810250107400010b106000309000c40080c004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 516957724 1250 516956474 516956477
    0xf03150e160f060801080c031c05071e0203011410270e010507180506070f0204090b0a050a0e01020c120708220f08010b0a05091008150403031401060e0103020307 71
    0xa07441000060403403a60140e005410480d1104030108030b0507500c252203d0042c04000050410301c03211002081d215480e48141490396120300d100d00c1ca0341803161088030580c9400c102800b546043e81d080c100380c0401c034440c059100e03608003800c0d2140c442420340300c94003802d142405034001510302180748942c501403102103048a03447d21a04030326001070f80200385100d07140030000206442d140748003620098074500344420001d200d103030602c001c0d00c0384011a007542e9040149036444074440e100007409440180c1c0010b151540090074401c03a5009500a28040c0001010a0201440c4442c0c85405c030702800c0249022903100e111800079010820005000450144030140c0c80c01245114403841801d0303140c03080c2003940760650704100d80d840314060343d000f43c602c060091000f03d0111001030106a100e0080314441e20081c40071651100319043c504000b0300050040c0c0748020118022622405011502a00802d040a045c064050345000c107003410b8074030310349403040302c4400a00114001d410045c00e1a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 516958974 1250 516957724 516957733
    0x3090108182404020901060804150b15070521070506060f01030e03041409060604030b0a0f15060507141911130e0307120e01020a0201180f0f09060f03150e 68
    0x2198a6160806070b81d4104204140d000f0305191040c000c41c5a8164020400c10810100384000100300060000900030003840115000200100040e48140d400029070242c58000035800c0401102081d200b10164042d084103c0111114101b600544a0188000c01e660030040009019141000c1c5199507010103140000307100000d856402d286600981106d0291240c0b0740d04401c16207040003180d544084244d8800b420f242c034558031a011034002529034582e060f19a111264152180e5004115410450710300c2503000c0c4d40c452029140394031421064801902e403400d0026070201c0001ca4400c5a941c0c004030202a02654950f0008400425030542e03010b55000301c2c07030b00502e59900a0161111700724016564400c414501100c2c40c100c078940400c18405424018a600c0e80c01007805006981c081c240b203907004484026070354210740c1c90b40040700074070100e800110380c0c2c0e082d4140c140156512600100b122580b11a02d81c103c1e0b1847d403000400c0c1030078880c54103a0340c04030384e00a0110340e075001e4100d4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 516960224 1250 516958974 516958993
    0x1c080c0a05180402040b07110102010b130911031605130c1b06140c0c01150807170703211407050604140a02032a040615180e070306030b090309010818 66
    0x4013a60300c180e00010714088085002814401000c181c40000031090001b0445010031101141880190300307420039001303564031a201c0a00040c00000d0a10707070b00c020140c400c8544114455800a6002c1c0100c078016000c1c0a81f00c2d0503142c051060614084941e240c03464403203e402070802d024442c007281207030f00c2515410032518120b104051103005e0788400c905140c031059801542802c441c0f42203420804d000000c0e0040111403000f144441c03c0d03940140500c8020354030042090310307001c40d41e40010008201d03c9410002040440081d4114001c2c03682d508640c40d03005003e903040303800f6101c00940603030004004a80011101c0383c580c01024108400d0f50001d900d29000a030900442c2c400340303543c000d1141d1542d02907141c1d00f004103140c030f00c0c219800c00950307050862060114001e98412014458100081c2003200300d92829a0000c1030303500c00c00d403400e14004034020049d1065200840d00001d000002c00d4000a0110949031203540607510a08150f0710084080d001d4500002251101d000b0708204 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 516961474 1250 516960224 516960229
    0xc0c0a0c0905011802090d02040b01020f070806060a05010f1209030309080304152f030402030f07030804150f0c02190f0303080612010504020105031f05121c080c0a0518 74
    0x240300040441420008496251004c515078000d29002480f505070b04c10010310304150344541011840d5a015100010049500300043c0d2418801d1902704840303108101000900340b100194881c40f070340040e0f902101c03040d41c0d040195010302e8205441d80110740c0814040780d0b5412107078071079400d050181c640030410080329290000540c0c030a5500381c401071444d03444804134070034501401d0074210100c00090b211101490b103110094034884407030b521602c0000040340a40d0707010050285512183c000707a44c10143c0d2443d1040841c6c1c8240304040380c240e1010181344555001e800c000811414585565424501e161308100062605440812a00e9910400421620030310b031250703000396100341c403038141c00e003845001c0100103858411050790503810481040f0050740c1c008246c982140480301b1030b0003003052500300300c958032405401c441e4200110984c0301480f09030014008401c0f108802c1101c8080600e11300448811380222480d42c2c48030405c104804e2a11f204d0750041c800f0a40b0404502c00d4030480000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 516962724 1250 516961474 516961493
    0x40c0302060d1d03180609152b09170702041e0b190302150d0902090c090108060301050403080106050c07090204080109020108010801020406090e070e090702072108030c0c0a 76
    0x24001403103039071192040380000390102000701c07190f2030800560034054032000030b20b0b031500400542c030b025100c0844e40c407001d0b07215080c0c0780210a40400b4010380314502103990488840c0c442c481e01c548038140c042d070708032454000c2c071a034007105401020b424065841240e03c405598481e4100702d0300542d54502c1c1908a17000c5ca00780d2011030b110b1250114060282c03404014400c00808070328010380503948000c00041e40d45440c07444051800d01062510380014071108002891441806500600060104408420008002d001c1602c090300c82103400d440305402c0c5400c80d030040b80c00802103080400140030007805003000d03107000380b091402c0701e01060f101e6039914140c0c0c200398041700441e9150a092002c40d80c1010b5410301411422008604151402500401001d814403550a8116840000c262554480c2c000391400b00e4000e407684640c0d051842c4e00942d00c60b071901c00c40b041c0360242c1d006400d0415429080014081c1c11194890a5458103903d5094030383c0300c540e100599228506030318002840e0004c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 516963974 1250 516962724 516962737
    0x90f0210030e0c0a0e011e030c120308090105060904080306040f0603050d03050717070f11251502060a051005130204080606060702030a12030b040f15060e030312040c030206 76
    0x1d9022460241e011015460004070030010781c8130302d141030000d205c06100503009904444601110461400844075440a0054580c01c003a0501d4010300c400f0504030004600d103480c25105c2e50318074101e540c402500c60b080300c10681d0490f500901c50310200d000f00b0103020145420120080c00002c0c5400001203101c2120000e51040340d8542003241d0fa00d40403501f46c0324290b40050a824840315240d0000c0705030b5540840106500f040c0000b042590300721501c0b42000018030b83e90a41200c1c0400011201640c9850411600400c40420f01e500441c01c21078145e95004119601e07002042c080e19011307007120282c04d004100d040c0307092200d038001419580d000c00f0024100c0040c28010313510f038104819103080610080015001d09400c0102e4001a100040c580301401d0308480f00c80c0f0064070270141140949916005168000d05045406a800e6200c0c2e000303000b48007a0100c1055060703910310341510000c003900c1220380d058100b4411002d2443c1c040881c16032007403050491200d001d849500146842d01b101c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 516965224 1250 516963974 516963977
    0x30c050c0d03090501051509040f1a070816030c0c17070501020f030405060a05010501210b040e010e161a0309251d091b0120010902100e060d090f0210 66
    0xc10250042c0002071084a03000500c0c42c1610301d4010384400450408c080250000b040065074004590500281001c5041400e00d0101c809040d8208560000c0c4549401e45400c1050501912003841050103440784443e006440c0d140e040300140e80382c541400303402001403080d041603410003a0344000b520a200414600e29818482c40e200c1c03d05082c0245040c1000380450f82c55031401c0c1c01400b46d030b80c001c50b0720b02d00039203606c09040101c1ca203c244840034121401c00c45421a082520b006103a070010b42051491b800c0e00c10448109001100c0c6078030381c0341c0c6d25210302081189080f01140a40e16070138015648810f0403001c4a2030b0807040c1108002c0c440030a490344280c0b004180e010b00c45180503440c41000071801c9080c0c9801400c158a00a4039600e5200846000014105240203a40d005104030044080b500720150542a15050468040d01180008034410020400365400290050050341c1b40f00c1c1c4091300c010b090591580c1d000c401881460010354421100d0042c013001640c0340e85041c0503a0f5401d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 516966474 1250 516965224 516965231
    0x1b0a0305030c0114090102040506030f0703020c0d0e1201051b071a070c021f1d040e0a0507060807050a0c060902010509040905160b070305071214040303030605090a0e0d030c050c0d03 80
    0x200d0400284c451010b0444500c6900401041003107540791001c1c4c0790070415040c4490b01c140c46400c003e800922070500350310003900910b400f081590750082811552800c0540b5448064540c0e64209030032180100e455400100c01c0300c0704641c0309400d000103008041c0c8100058032a03c1030800c050341d8004421114000007500000801045041c0218201c00c03c041d85664411036010070035000d0300003c004485131034140100440058035545540051181810450a030b80c1214241d040c11516042079001d84030200c0c4820003c035404038410b10840d0711708442691f034503607600d21685d5400e01500500388243d0402009024507400384c1d50b144074100c2082c0c070520007000007040c40e20603030a6001e40c03903102001c4480d0074401c41c17004c2a0480e040310441c80d07006100e0005040402c0c41902d8020304041c1c1c0500410300030074007004168042e4011010345100b102d003c03955981e0070040e4000d8448003e003250719034006002e000c44460107a003140c0f0b000085420142d04002c0c24082080c5455100b20001000949 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 516967724 1250 516966474 516966491
    0x60102070e090a05070e06090402091909210c05100e070b0301060f0306080606131107050f0a0b090304030c0303030b040b0613030c1d0f0717151009081b0a0305030c01 73
    0x1001c21840004244480301c6c44518a812070000700c200300c00801c06401803000c4030018a902d449032000f411030801c00c2d10704001d07042c12400c1c01140d0a42c1001860701104401c403a82c00d103517019a1040060760b501000501040c001c5001081c041c10b840341d401c044c07a11822002084194444000d14080c086c3c41c0e4440050910300440141170b0740c1d180c0d0210840760007260074004251214031418400c1c6c61200408603940110303001d000d070940725640001d13010780206900d1092944007c12041e6000b805075030340040c9a1100c080d03644c0c030f900c01c1e840020040902c2820401c0002e0003604103840300040100b0000d0080c0500c00410915400160b044030301c950220f0080c0204841900c0920250545817030350100c1101e81181008600c501030861272440080400251040c1e1107040c600295540c2c004103000142081c441105504aa84500510400801c2d0040e50568410700340e0208681c0240020600e245240c07420b00c2910f01c1601003250000300c00038010001c10410402050600c2c078900c0000b96559 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 516968974 1250 516967724 516967733
    0x270e070f110309010c020307180501031407140108130209010602010e12070503070215160b10080f07150908060c030a06170715090312030507021204050117060102070e090a 75
    0x8500d11420060151036a6150030028002040d00c2980c5800c1c01d04084952041c000245454007650192056044071800c008542c62141c000c541220300c141d001c03410510082c402680c88910500a032040402e0600c6007c40d0b0350701c10030039240c00603c0d841c8000864082d03600401e44422090300240f000d030f9100d408140c01903e04200604160000c030224508181c2c90b503440380d880388580c0c10701a106110710303000060115401c00841d464a4075403600e014046000d45040c80015000b2140303015400e040d080d000078200c101003290718480e00d84201400c1043d0030b014901502000c1da0340000c04100b201c00c1c02040c0c85c20104071890003403000000031504d0307180421380b002c00d032003154000e056612060030040003401400141101a01c07120803281e18180e01c7c41c94202c17111496035001402c6a00e80d00300300701502c2d8141c3c2c0304a0080c00c182d801d44d01160003031001227603903110f075110f20760005611041d03e101002d2501c00d0f1540040051043c0c2c1c9400d5551243da090504058640300c019810001000c000c20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 516970224 1250 516968974 516968987
    0xa050d0b15150715110a09050f04050118050903091e040b010e01020706030c02011803031505040e07120602190f0f02070f05060304020414010807050103050105040615270e07 76
    0x441107a98102c8040c2c2000645560b0040240040c094080007013076001c1d155080c3c002e03c10a4542c1104182c44080e00c980040111445104140c000d0b03c40318040c4a80e0308144c00360314143e50182a100c410903c0011966004000083c516801404144090b003d00d0707a0710b0b440d203d0580318450300d8681070b6600004000031106003442d0103041c0261201041d0469070085074a40c12075816090004000508650513409066050058403035000d00f80085010145c0503449440e481c4003000f9141c4409441c0c5e01408102d4002c420303100c0960744040e44c100400d02181c102102c0140c818500507091248175651024030803642e600c1d02001c034824640400044d50721890307502d100c9100d0300c0200034180c074040c0c000c200702c03100707020b69170240303c00000180654445410080c51403141c012400100d40e0b644a440d03803100c05a000d0280003c2c00d280000a1610f030078060b2000340c2c1c2140d004082000001d80e01510700903003c901d0f8014040b5403108140d40c40440d49a1440207004480e01302441d443c180b140203150303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 516971474 1250 516970224 516970261
    0x90a0b03040b0414070b1612030905100902061b0c01020f0c0105030a2c0c040f021206061e04030602041701020705070512070902190905030318040b0a050d0b 69
    0x12000d108000114996071182034102d60082140403c0c2c00e0100328043c14100035400405000340009003076a94859805c20154800c0d009020b208030542810004805503800801c01034002c0c1e0000e44030002802542d44541c50003031004007010328001d40c0090001d88180b004050391004d403c1602140000d5805006001035030b807010015003d1401d0440c0040c103070b808081c01400c00c0c0d030381d9008a00d605035002209c100e00205071042c0c0a41c60420b0040e01940c50f142c110129001d5801c0c07a400c0007400b0164029119080440007100c66142d0781e0001740410354101e86100b1240755881904600029001002007000d0340c0200c0d0301694072070828880020301061200e250100b68810071403500460008070300139007980c0c000c4680c01c14224a500d803582c80d02869400c0300d5a001d00c000b903610b8030182e800b01e585024801c50380b03900300303030513590805c041d224001c01003900054032144c01400c00300e2415500c100e018074002030002544580340c00100d4550546d510302200c04001c100300b071100441415409442 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 516972724 1250 516971474 516971489
    0x302061b0a39091109040f05010302010e10080c0310051503220206070312021308210a08010e09120a022b02120d02040305061e1f0311010309020301020f090a 69
    0x800c070302e1108260141414071804000540d22031211003500088030881d5402d0400500038043c504a060344400109000c0c03104a021640403201c60601307090581c40161004d00e1038035003140b10740d0740315aa0340041d800200303c0300c04480c1c54840412699558410215200e10b0040c03030035100c0c5420706032240394540b43d2008080d6501c0100b000c0c40183e5504041351001a030518024031222035400e28000a4001c0407002214442000c0700440c03c00b07000540c000108a03009104c1c0d50b515030700c254078184d5204000740e80c000695901c0c0140001c0360303007070706464101c07082d5403c43d40b00b8809000d2100e0290080d504040060b0084101c2109060401e901104160306100024105041e080c10113580d40240c08590082c0aa01140030034400120780d0585000355000b5003039a01d0f600d000c4c810081e040300001c0c900610702c10000c004c11012541e04001540741264522035108490868456a070703102100203030f40781015100d54086005031001c0c0050400307612411852a15003540c0d50420190080c0e0b03401400c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 516973974 1250 516972724 516972803
    0x9050607052d0a0309020a0e130b010e0609040209070c02100504090b0a050105190c0803040b0f0c090d030e190e07031a0f04020c15070c110111070302061b0a 69
    0xa44100b01d0002c4a89441d0307281400103600d1814030102e8803041c0c003a072010498007007680c100440c8c5030800001c8442548642ca0302c2c80740742c2e00c80441c445032980070340701260818a400005001800d00034400d03a00440c0c1814040760411003540018402c10b0300110420002c1d4010504101c040c400303006d0b207800c103001103486c451700c0c60400000074094050640c000400d8442240401070981c002e4800c140c9554116182c5130781d07450030703082a00b8528401c2d41d881ca503503482c2c5c0000503115451a000c0c0e4a203031000409100764855203803022642c021198946950200c9901d02d918030f80c0140704820710040c501c100043c102442c0c60794014044800c0120318032541098884003040707550303a41c0090380480004550050316010480c1d5030a1400d9200300100030f000e40303850b05120a450300480074800e214412107581d015001004e004640b840002140d040455128100510052402101424803070b4032080a5220520341c8514075803800c0c91442c03054410700d250320b28040d0030700000011070700581241015003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 516975224 1250 516973974 516974047
    0x6030605060d0f1707020312090a0b030108030316031803020a021c031b0c0308181306030302480306010609210309050a1e081b0d02040905060705 64
    0x301c0010303c0180004280c1004c060101400d40d0840042d115055006401c813518198820450442a407290601a07c00c0501c41d8002401600e050210381c140c41c8008095421034441d015054800c41d04035041c0e00c141921484080c80c04007080e480c01341c25501a074010a100001c5d4010b10040c9481008400c59000510010b040480d07000702075400701841c80c00c4095903000c1c0e1414800c4096513203800081c2007000c0001c1e55090115204084070322075170b0881d1840074458204003111308450840c80000c000d80c00411210b0702c00103005490000701c0d42c08a500c04540748400c014100b01c081502c001d100c0d400b08400300c2001606041000b14050103407030511484e81400c10000e03d244118510523440b8006101040404040c0700f001c1d00340c014000070340820a0291500180f90925a2601526089c50805440015001c0300050ac81e840444034010400c941c0e11080d0a00101140d2120140c0e00140c0300e5048000092040003031501c60b0460340e660540b0f506c4503a0201e400750b416852068601006101103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 516976474 1250 516975224 516975233
    0x9060d2307110a020d17030c130b04030f020415051009091b08040209070918020702100c1101051e0301061710060801380406020d0201050f0a0b060c0105040606030605060d 75
    0xf50021a4044030b07005145110f038504566441800441e044007401c02105000d001031000e400351207031004410b50b11603003d444d4050700d0154040c1d4030010301201d05d00ca0030300340507043c41c0d40801108103421200c0e0802c81c0e110004030b1540840300501000042080c0c070308000f02c19040c030407140ca18482410b1240c2c48503030810010506400903001034899800c80c004203880030301035001c4400501001d02004081d0170109040300080d00310070001c0c2e010f011090812104c49128410600103543c3c001100341500c18890011540c640007c9003586c0304240d80c03006800030a020301e0185000b000300783d580f0403100a4000e403918510303401810000442d056810140101600000c400381950410f00c1172546507210ba201014a204035110350300310881c229022010a143c0b200020029202c09408445070780c01c0c803010032030882c1c0e42150654016002540070071522140b6400c1010400c80040c002c1d420500103203449400c461041da0102e680c40d030b4900c000c10421a06003d80369020100726628020000075455 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 516977724 1250 516976474 516976483
    0x60e090405070504181b1706041a0c0705030c0706110a1a040f1209030b09191509020a14090c0c0331030803090115050a090209060d230711 61
    0x7a5a00c255111440b034030f00d100d0705c0f00060110a8204505480c2c500e125000f98905424074080c2152000501c0003d0f444040005255402079030f00c550311041c082c842802c2c04041503c00741a050400c0d00c1000382102299041001d482909541c40207030a2492030004060a0b10103502e12681036900514001030104024184e0010300095100e4601e2081d0b0700d52400588544c0c5d074401c001c0101e01d09030344500503560b220660005403481400161419150310300140c0e0340c0c22004510b6015450b41c80794560015180d212034034200c21610f103000c650b040b5968000307078a0f444150451051104e10105411f0a8641a4105904507003010b4242e0702e0070300c0340302443c1e1300c03841303058a0070340f500b03c09800d03001c4c204d4041c205001101c0000c150b0402d58a440b46030403c07896006803220394642d801c00b81050b1040304c10001d85011a0001040d0098242c50010750340c0182d00581312056005006005a41c42900d0600800091f2110403c00313122080e01c085245c0001c8101408603010002071482030724840c080080e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 516978974 1250 516977724 516977729
    0xa0602030418061a090f061312260a02010f050408030c070c09020c0d02060912092e0e100801050f130603060c09081b10140d090507060e09040507 64
    0x30100b04040405900034000f5000c1c541c442c1100314506240c00744407000e564040c0c1a840e00032a10480f5040e00c0701d0801c0407900820703610588002806d182080301c0758000012000c041e00c1040c0208444c01440c20581c51500d1440c20785001400003d0400c400d0740c2d080c410104590040d0302d0420203030030651070740000360000405030003e400000921070103020300c1e4034844000380350b9040d05654541e0f4190130540c0301d08142402002510588000c100401c1d00854110940949031103020b0511940c5420032048162200c1a0551040c698903045181c00803406107520744400c0e074454060080c14141170150484a400e43c10701040f2080005010310754441d012245483c0040741e040d0020301e0f140700c2c50340c000c009503400207120b645400e01c0300980761b070004403040c21141080180e680341c00781130500c02c842c2d07101400c0036513024882d0f00750070701c03902d021f00040000c100485030700c40e044c1100680600c04692642c8000d8429038040c0d02d04201059100b030030400e000100391040c60300d070b09051351480d07950100b90 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 516980224 1250 516978974 516978989
    0x6180f031e05090609040228110304080a11180708011a120103081b07030c050a08030f090427030306080c040c021b28050112020703020a170409060807050f0a06020304 73
    0x100c030344903a5071b250181d512401741010382035444040384010004140801c040c0c0e001107440120a02d60010021042e50219100030001d441c28164542d250344a5144007219540e000307000a0308040c001030044507142c0b041400391148091541008800780d004401d210107803080b100100079207d14a041140900e04580d8000c813295242c0c3ca1001030b21410200c0610b4244440c402c0d21000000c1c01010800c0204540c0241c41030f58850391a00411522449001e080420380b0400304200c1d5002e05090f405850710880004002030017030640c8110f510703600504d510550010341c640340240320029081c0010400c0d070804440405c0540302840c0d0280d01d464120424014080200d0345281403a101ca00e00154444ca0070070f03840000103044003204201c00f104c0d0043c14001035000442c0144030030503208503850103400d600280b02810703165603000114410592071042d441e03c24003001075008418020007024084240103080d041e03041030140603001c01c081210500c01d4507180c03c01c1107025008070850b4166090b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 516981474 1250 516980224 516980227
    0x70309050f03070209060a0312080a0e1207020a0b3402100f0207060801080a03030e0124082a09060d02120106090b031617031603030615031a010c06180f031e050906 72
    0xc2f00c0b2080010200002c0101d103d01456941a0340b80005500500c5054400c039611940d8640320078014450380500c00002003868809200302ca204a040c000205681e00c8180703054112035980d078007094a40044070344900204904c100700d100c0307664061000b031000d06041d04c2c150340c2d55807510b911566195a03600011301030541c2c1d85000480c1c00b100b034000d5598200c03d0a0100daa020499605000741d1032603100f42901030003201c5004410706044400a1951014803140c104501080001c0004146010340b800c0e902c030707403103602d6940142c4400d18002042e85004c1c00002c1c00d51b182c948a40d068642e0f01d58541d200c0d40008081c144e260444041190981e82064545540707107442403480d40c654480c4211611a00103400c40d500101a41608035034161003800c8440d15030300700344090507010341790314140403284400c1d4a10030084552040d80d842c2c42d250301a0b40003142184100d0b040c0c020350106440142c0752544020744d05401c0c50f42002400c8402065004c003440142030095006120f4058038605502c503150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 516982724 1250 516981474 516981481
    0x1060e010c0f03080105011d0d062d020910090503030d020a170c0319020a090e0601030f02030108061e04050703020f0d020907180803090a0905070309050f03070209060a031208 77
    0x1007006442001580140540302c40005410090814003003441039a001030080081525004104c5003034031580c11000c1c05000b03001c0c6c81a40c440c0060241003443c00000919001070220000728140c40743d9100c02180c0c801650b512138441484200c0c4242004201400052031041066490010484071940003000d00141c807502c4105040b10001600d54846003104941414002c1c44151300380194090420103842205100c42c5d98a0300081e401801071030008600c2d03c00301000042d6051862550080341454002080388050303004000320f80003a0040c080e81da004004001041d1200d10940700301d802c08842c4500186025503509a032000e035800b000b030240441d2801d43c006a00c4001008036820f03801016590079113001d85000300803800752580c0184201c0f51000010b9a498040304448550350058000e0012a00308449000a021701a00003002c02d07940e12480390100b141070112088100c45000515500c81e42030041201000d006460715108140d0340c031042000030f10b0707a505109110020b0a100d01c0700e68 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 516983974 1250 516982724 516982727
    0x20f1c11030a0f08030702060703050c070b180d0504050901080604022b060c030510140d350406080a060b07060515090a0c0215010b22090906020d05090a0b01060e01 72
    0xa0442802010400001812820401001c016606c1650940c0c2214400c0d81d034a03401310f0946030261442c0e11100410050040071661901d07250341d00c03400070f44000d80c884c1e996640007440e22038400d49000c00208045414031180c540800d440d401029000d00805507070400e074000940c9074818200703224121266006160444038619003540080d40c00030020004c0f0000d0b40e801801800040b5143c4007c00f201402c045410503030000d9282403040301401c80112111542e0703d400c080c7c2d052001100b200c0351550020804406074044004500d24100d802688840c640480a0300c9540040c000d00043c0d41424014071a02800304c0903100d0300c5805c00c80c00318840e11400007d60040041c00f04064001840004100c040020340d008000900001e034210703005001d125100100c02c050a00a0100d25801001204110381021000c040745408826183c03e07165a503044a0085030708001003111302a40105100c9810101e5201306a408000300303010f00210740180c0d6814420f260140159402c1c0043d6508502c0c059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 516985224 1250 516983974 516983983
    0x10050a2706210c050402130e13051b010207030807050109170403050a020607080d050907230a0501030c0504170d0f05071104110417210c0a0f030302070b13020f1c1103 73
    0x4c210103801150b95403c1c80b9010b0710050301500908062170020001704a08071080c0721680030040d0001c0c090200300b140306190445940090140504503c503402002c804620710900801d070442c460030000440f03100c3c0740340400d042c3c0845020010801c00c00c3c803042002c200d01168619442c0da04030340c42c1e603540d40390786805961401400c1003401e03024500820480c800780c00103040e03015115242e010490240e034481001e4110b0b10740c5010300703400c030000c2501000154000c0d04480312203030080c105039003040c0d107926019100c0b0f07460b40c100000d654841101403040540080158040d54501d00d0014a00102501c85207100d0690b40001409140d640052503e000429000d450241001c0c0d4011002440b04580c281d903220600680c03030009580441c0e28076041c2061701d00701d0304541d201401030200c2c1e0405031294000600c0d0018154213054080282b84006001507003c5445249454498007040302a80103000c1140449803503903001c0c22001d0402001000400405030032544d101080450800c410310129080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 516986474 1250 516985224 516985229
    0x708040c0902030a2a0909021615020702100c121d060d020c060601050301050d24020703030e0d0201060602071206092f0612010e10050a2706210c 64
    0x703061002c07080c0320010010750003060f842141186a0425a11051103803544103441c4403071310700825003d0074100081c01580e00076040841c0103400d000c15030f0b0030301c1d21002138640b4598041001c1c0381e400070381c00c0114600114458402c040314a0a9a01d01e4030580e94040c8041c00b550010003845240ca60304140b03994400950003120102820803074031107120806860103504484428030640c000c410001d0364035445002527a0488030001c0c5040c00c00442c03519500103811841031800b002820303c0a1031110038810b8002005010700c40d9074009a10044421201c0c101150b10700740108590400c2d02c200919030b80082d5403c1035500c0c15060401079510343c60480010450020001c105066410402540007030490042035120868030000540442d21002c01c00c003407080a4008030030302800801445482c2036500d0f0f036540148406d0004007101e881c0e90001e901401241c0c014102200240e0070480e2071103525280c1c00311081c0b044020300502d410036104015150024038030709000a0310b84c4030070301400005402e5000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 516987724 1250 516986474 516986489
    0x130c0b030c121f0f08010f020306060f0703050d06030c06020f01090323120c090a1502060a09080705010f050106030e030306100e0102070f080a020f06121b091e01170903030708040c 79
    0x40c0155281e20340100c104c4580b00340c5842d035107490740e00c68040e80907000b01da2003560003c00c0149450b0441840855541207a501602000414008004417a440f40301e80c0c4080d60080d9050f000c1e20340752000003860103591590740c85240e410641c110000a8000004205503121014040c08404280090181600072514010b0518050b50140180c0e060706000908002c2c10617140403282e0703900d139010400d05004188000c4010f030300400c001908102e4a41c860741c28944600b42d168940542d07920340c42d00350b4100700f01e001d038072564441c0100000c0d50540f042c4005200381601940c2180350500000d50034040c4411a072062150844c1458400c0e0300c01d2104401610042084410507170307e94a6082e0380701c2c003142e0128050f61003414800c0f29131811405582c281030718a0140d00065544500212289100f60030307483c1202d41c00d0041d052075607204000507804180750103041c0070700900300340010080d2240a03c1880e40a0042c070512442c1680030040700c2c1d1042c02420820007540300e510309800c1400741d80e40f0010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 516988974 1250 516987724 516987781
    0xc030c0c060b0f04180201030b152a0312060a090e120a030e100c0e06030405210c03040b0d06150822060c110d0201020903030a030e0a020306130c0b030c12 68
    0x140f91038203c00417124000c1c0da040000b0181041840352500c01c07264122011402400f8031859103c1c40315401c5440141e10100008a0260000c0c0038690b8001010480500052008000041c10501c000034010201c150741448201108000c9503201c0f400740c8026102050000741260199009810800c07031018018100d03049420514640e100420181040704002031060454140c20300d480740c03e481c0110380200140c80c0b08030407012410f5566025078122800d140c000d1207030900e680c03404d0020304014041744e00d20540d40c200c512402412146280c2010817161584248a800d15500010165124a40c00c01c002011700c0300a005000580c01150003d0040382080120740c01c2541c040381d04105080010f0844030314000d000e6080c2e00340d0080301c031455050b51040c021800414420703004907220b407004070107031800c02440380c0100341000c0d4203d41d4200c0030b40748180b04c40b04000c1c81117440f40080000c0c2502c2815410001112050b074400c036250900014003440109918480d24600405240c0e041d8584030b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 516990224 1250 516988974 516988991
    0x5131703131805060f010e010815040c2d09050105160f030c1506140d020d080f031605030405060402010804140f061e0103081204140f010b040c030c0c060b0f04 70
    0x92a10150301e08585002c10b052102082090805078000325041c00140c4034041c40782000c60044400c210002c0500c04469920004003500780c0f510f115000e0131182a42c2c0380681d42804200200840d1240c2e02d101425051408448107202e91040820040c4c2d042481c10541e20008005120342c196a0f20700301500350b13024000100105a009050129100c1c403e03030500400718007101c05c120803602c0603c100b01800f42c43d50899901881e0000a08220134030041110780c11a445071184c0e00190044856034401d0030002040c444a008440e07200000c16109241152035440c0c40da440f07a480380d43c0600002d0600c03240c40302240400032040604080c065102040b1251100f65036900d42e82c44c60140c0d1103d4007090450b100441c25a64401d1690503240c001c006070f490480320079048500110010800d8400c007140c081e100d088440700340302d41011500100700204100b01e440041104944440880038245032130042d00744040c030380040c0c2003840c898000c6030004412114a000c00c0b07103600400b0846501c2881e21114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 516991474 1250 516990224 516990239
    0x140a080a030b0f040e070303030209030f07090501082514010c0b040308010f080307020a0311030c030607090e070f0f0309060f060b0c1203040b04060209030c1305070f0513170313 78
    0x1020349803400c840035030105007a0401d010441700035180090403500119806d0000c207020707400130701c0c030b211015044543d10341c840c801c4a41820f011750400200c26464030300400210398108091441c40705243d032202d80b0406a5171070352088400910507100c1240f041099510140c2c0540b904801c015040145010146020301d40184038041c01d0003211320b0840c034520702003049000002524900c4e83d0281000316818110303240e101d400701121112551620407090703407403810348060000c20300418840d110000d10038100481210110401001c80017040108400481000d0303105410079010030b0039047c0000d27801d1a0741001d00141c49a5450082c45c0c0d41081000200080660b0041c9404811081a52242d1038030150440302d0703200555020b44007070360007030100d0b0100392190300034002d020004080326012054440410744240c0c401c221020790079a030343e0402840c140c00002051441d42076141092800000c008070742c240d01400c2c000c0001e40d1050142c81000482c0400403140c1424040c1486080c89a60340603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 516992724 1250 516991474 516991481
    0x10050103080c0601082e020403050d08090f01232a0c0c0d0503070201081f0b0304061d0d1d04020d0e07060306031509020402160c08010606021207140a080a03 69
    0x102d0301c1c030740d100d440d00000b4151400b0440781c84500288644100d5540c0d10b4082056500c0000d0300c01c01c03015420000000050700c2044450f40707081740b5031100f42261501030802c50900c010f014058146904000c802c624540740b11545154004807a04142220385440c03c0107840310051103005182e050302e200800261002e100b010300901e1081e0f85c1103906081c6a0028002002e10408000b8842e40c8148070400056002e210b03000e85c048070410b0726504000f1036034000c5903070305081d501007007070007030000140030512002c2d00542042585155041012644042c0900e80c1c885200d10b05000f0040c40814034100c80640a82c8064030983c018825526104506c01c0d05000702007105144520b0705c210000082d001e4000c3c0035a408a0f504000c007414007040d41011800680540c1800300c0e0b00503820030034211500b1940301240c21040c02412140e10581c1054012421110389401c1075040d13501112a284024541600302d070345903540501c3c101c1a4a40d0b03106610310300360b21000d00a0031000d0112381f2503a6658580d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 516993974 1250 516992724 516992737
    0x9140c22081b04060e0a091511091c02030a2a0f17070e0a0c05120a1e0b0303030411150c0303310b0402031002040f0e0a02030708181005010308 63
    0x941c1c00c00c1c1c1d1030400c000031990544218079035010070f80f0010700246c1560340702400c841e00440c80481c000b5080032943c2d00322003100d084c9040354440807842c80c0080c02c01454600b03a90003a0307051030707030380c1c1540d600003070b6a454600000410410f001c08c07042c58000c001040b82c50b1070003055800070a00644a445050801c650340c0038200303054920700c5180d82a0713400040c4030300444a010708181c01c3c6843e41c55980c4080c060a0445509100d41040100301d006808030101e881020544070000b061059031a10580c00c24280c24020b21035030400c81c1074a1150350200403690070a80c8100703203001505003040400c0a6441860703070310080980106020303c66101c040011881000c85040400300d005c407160f24505d0004c07044000d0011401400700c03d20024004040041e017080c00107007221001030458200c030050741e102e50400000d034540da0f00d0403c4034114020b442c64201400420a43c11854030341c600410007007000b07104852918400075040300790081849241400d48008400740419a140e0030038590952219 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 516995224 1250 516993974 516994003
    0x5010e0907090909060b09090c10050c070b0a0201020703020c121b03070803070b0a0c170a05150301050109020408060f0408190504260f0a050601260d02010c0909140c2208 75
    0x2000140740684007040013945c2990091042b540906010821903264201240f070039820b2042500200e0076069800c06400d011015a00169807944070b450020308250784820450300034a04805207401c44000801d90440f40100640500c0f040c3e4041000030f445c0040c2588110a603000015542c0e081c0262040e21501c901003250003030081b941000b00c111042d107000080d000b0fa8040340b1020070f83e600129004180c000710385194149902450500003400c641d03080e4000156a9800102085504000d1096030b50206a5480700c400351314042c3c58101c0507214040e5407030918905810140c0d517032409007068402400b03c0d6400a6030480b0f10441c903603000c0400c4640070415110b22880410807040028501c6000e0394003001401c44c0740d10300280c0c1c80050342d54004401d240c3d180132121240300703482040070002e01000359002055125a000c40a0302980309074012862032405c2c0203138160041c1102c0803032500a042000200d540d40360745034101c020322004842541d43d0700c0c42e60000003805040055008200304a8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 516996474 1250 516995224 516995239
    0xb010f051203030403020a0f0201021608100c09080c0411130308031005100e060309010b0607052d0309060703050f0c0d080a0c021e0708100c090f05010e0907090909060b 74
    0x70a980542d40d000454008005a11201d5450002800c018914045c180b040c0101d81501e00b811420614003a40d541214030141e2040c400304061003d01d010b90710b1011800e04081010380d0814a6090b11042d42c450b0860145131908954224002c3c0d6008540c848182c108103110455103038549410b480d130007550604076034605814003007003900e0080e034216045076040d00e84040604440e401c0c0401500003c1ca40e44803956610714400d8070740c84076401040060f00c5003001d81007940544da0941c010440346036080f104c0400d848840070717003400d0000440d1407064086070569216006490100c40c107104a207203008141c400480c181f00001350004095000059a0f00c0341d130f040340d483d0001c02048881d40d007042c4006900004c1d200d00128050348140c000e01449406444606449038421440c0522201c2580d01c210b07500c01c44a4503142d405140c80005d0001420181c114034603041c00200388166000036140308001103004a00841d009840d203400409821400b4007010035541000c030028489010707114003440d0f0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 516997724 1250 516996474 516996499
    0x609031e030d150506120c0d090b06090901093906110c04180f0204020f1c0501120b0a020d060f090c1b0519050309090421110d0f05070b010f05 63
    0x6043c002601591005000307141400000380826000d40009410002074801c03c000440406416000d54030b6803d015202943d01d03030070000c0a00075001c4004100c98080d900d00034225000400d201c4440312200041646081c4652011001001b0030001203103092700005801c2c40081c0ca19001003940300c180350000280c0d00c5280c1d040d400d00040d40d01c500b00790850783c03100f05a45000a52019803001d0b4860000d8001401d03c1184d42e4107a4055000645900303189490300b034070460341c02c081d0080d203000d00b03121000d8036080f002a0f5a000e44202015080003142c5e030300402c00305100541c2c1d90190001b0302e019148440c0541c1d84070f41c4000100084441100000d140701c203d525102c60a062160320954040000c0800d00700700300148500200f84c120840b0306000800150b081561a00103c5008502440c0c00303000310100b01068460b41d405102ca248103101e08042c0650703804001103210050000d050a1007101c0d0255000122032601c680d0b10004e00c80c811100001ca01d8040c8212042d05403041694099031070039 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 516998974 1250 516997724 516997751
    0x1404091506120c0e010f0e041a09090a080d051f06030e07060905060403031b081c05130c09051003060525021b01030b0105120a05040308070c0507050609031e030d 71
    0x200300010f004049604c424a00c00079500c10f0184a242c04041c1c82d1140d030103004500040c0c02d03502108014110114000300f820300510f00301044a8000c09190000c1c40300c5070899a44107607501540040d40e8819945200007403840e00b21410300240700e040d9a029201d501d886d000d01800030a090310b0f100304141b00c0d5100104681d801044260103440c40100034030704051a60350100c9446141c80e000e4031000ca0885214000203074407201070008804841809002c808015030032104490008040c40c018000c07021034800429410303038050040e070395a0130700802e8030b5403200340103513012005610040149103001c080015072104110b01c902c040c050540501c40030041c600049a03100407030401d512500a442c801d00c8240d42c081d40c0700c200600e40c181401c6080c14207422400c014a50216060300100b82c90314104010584d00c007400700e501c868142441001960075072225640c5d00118005c403030041100007080c0401da03034104241c85682101c0c11600c41d1032042000d0040d00c070740004c80040c180c10706080c061070042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 517000224 1250 516998974 516998981
    0x30f090105060f0112050414030a02030903101122150815150d0507030f0c080702070504060f0905040519031806080403080c1602090a061403060f07140409150612 71
    0x8a0580d1005e02d5120140400801010080e100311029180c00c0e04140b4a008240042d017481c1003d80c01545d2591781c0720781403504002805d402e402d4258680a0b508848465160542d03009000941031000800c0540d80f404e2160100c50308594071480c904420041080d034030120f1648184070105c14502c18281031002d2111030b00500301c520f601d002c0f0501081042c2c2c24568000f07540b00880c3d11700410740450f40c8111f002120f0010002d00000780c2580200320486170100043c1009040a407010003149260000d040e0151403140260124a40c440e4086070512a08118000310b5042940340503000d070f5507500d0044c0c410b4080c041440742032410a04e00007086409085018031940d010f440f40d4003179644059155001d40e11120007070031901035410140000d40c80c0e6043c954481c09001a0000311141443c14000c8104c418000c030622a61046003081200c0f50420a01c40d0402c0903400c00080070010003075822054061900140c00407403515903207880c0c2d000352262480444105450310714040496040403400d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 517001474 1250 517000224 517000249
    0x509010509040201050a0e0901090c081f050103020c10060923070815030a14030a022503081303060e010504140a0512090409060f0603110306040c05040209060d02030f09010506 77
    0x104000c0070005001d540a913009214211862602061032143c40c400940d074031700c0a030405015190313102e10000c002a0440034440e00300101d0701030311a83c8074140c040805030384d1007802002c0c105070700404d84545221080201180f5007000400601c0043c1d1030340d001c90014095180300300804048124200301e1010000240ca0040346150303104a4035561304c9051203401d800500e022a01881070050b454081104400e03807811000506003c2d55a41d01c000c0402031805480c0b400e42002c84c02e0f10405040c041074010603200c201c980c090b00d1181c440254034854160601c1503403014124604101d0b402d000800b065000500c200d1003600803080842c908507080b5a038010b400c1c0c0c01070096210f01041c0400d06400340103000787d05002400401c03050400d81d10344054414070000800400c0d111203060081104001c40000d0718241a0010460343c40c0645170111044810301c40c041c000c55001455062076156002101c02c08224034000790340e41e040055040b50701400480307009040c0c1d440e11303001c55070754034040e8a036161 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 517002724 1250 517001474 517001479
    0xb040e2b09030602130306020c010f0c02030a09031203022104020a09060503060a09080c0a0f050c061903020d0212040b0411040b010c0303181e03080f06011e11061f05090105 76
    0x1c201c0c159036541009511144130500ca502041d070000001642600040c003040c0f03025000454412120160380b4203483d400ca0310350066410900860381110350002446089942050001406070f543c0b4500740d009200e008009000c10a03188007503001065243c0002c0e0140784265141000c00c1c2d582d880c0802121a10f0080c1ca0b415003120b80801d044002c0707034210428041c040c4901e83d107043e080008203803a00e800c40300300f102c403000d40ca90b000080c0315051019030740759401525240c1c40e010743d2212402c1c0300380c00211500c0c207159000c034074000f69403800d605071050080c04480011450500342040a015039080703608440910502084451904050055400e203c5068488084108266800380c010b0188848402021081c0510220100b00c044551680c0c10340d001c41070300017405c050300300100b842c480141085180f10465042c402c5a0340d000c0c01c210301402c0d00100b06901c04681c80b20840d5501420201d60303c840c0326010038420311a9404402a0200003034440090b0303295550403e21101440c01d11a0300d5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 517003974 1250 517002724 517002737
    0x31006021506061602041e0f050105040507090e09030705070608091e030906090409080a080619060c17130f05010314040b010b03090304082d0a02030d11010b040e2b 72
    0x1031311003510350305078070f500c01040490071000844401140d8040d00846d200f54a484a0f182812104248581d0740901b01c150b0302404280b8112070041d19841c420b214801030300701c1d21400038000d69014415140c2c000e6003c010741d1503269a482c2d004165050503980904a80900140704c8031a100313401c940345840c04108007a5017044001020843c050300031401d9560000c0e1241c1516000904250017007142e801180c490f5805400e005080c82000040c0c03118180084e00d01c05030030304c00f1b503030004100080a90300182075084000e80c500500041c0c081c00b0040d04102c000390707a0110709203598441c04405d458003a41c0030400034088081101c0144810303a03015280580342d5005000a20200340110b40c070020181c112440c01d80d480b0754503850700306814803406502610031301f00c55402c86258801d141020890b4020300440000c0e400098a85600b041070702c09200c800c4c0d4103014408004e400208040790000e100b0022000300300c42c1c0a480e0000d2020b0a60f202003204a02c90400c00480e030b001029800d5940c692 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 517005224 1250 517003974 517003987
    0x12030302090f0619120209060d1b1d09060d080705060103050606041406060a020a050d0207031505070f0e030c030a052d03030a020c0a0803010306020705061515090a0b03100602150606 80
    0xa8600c12017250a140000360200040445916050002c1007070010010740040c201c0140e50800070704c030603894040c0c820460f0b00f80741014400a50404000100021144804541c071210005041100307039040092010402060a009010000c503450b8100c1c0e0091042c0d07038144e070f01c12041000b16001708000c0700628640401107038403406c1039405800c42414600445682030400d84813140340a5542a040c40141e005003020310030801600f00351859034800940c14801802c0c00d070340280070790503000541400c01288500319411a41c040080017040c21015095030860000350400c103880c0c8140302c5504400d00d51030f02c1c1c0240040ca1600d60603a003088410003441c01c545030189800083e41c40010104074522483e00c1d6a0003280058000b1070007540314202c01680e608940c50711a04060f0010100f00181240780790014440e1200001f0354400300680c0341c07040c0c0d0780160000194280000d6003108400700c8012040100c40c0c11403241c04000c0c1e07000c80d000c03900d94080001011f82131200c2102e0b010f4001c0700a1058 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 517006474 1250 517005224 517005227
    0x2040f0c051209030c030f1c0204060905060a0c06111e03070f110307060510030201020c0f0604180906020f09011e0918021215010f08040b130c12030302090f0619 71
    0x1655000240f0380240c03031a100013022000d03e90b03000599004100703040040d0030404285440c079540d1601e0241c0b00107606003854981d0280c421240791091038060340c00026404d84040c410740051401c1e075400402000011064107403400242c1003084810110340e141c41c6000039403407401c400d9a100e0840d99a4408140ca40d804086030700406041d40c035030481c4024000e00300010024003c251003000640c00315104e151640c000246007042c8840c0c4240914084481e0380710f1070326500115010b459203078103042d0301c030340801045000610b0030030070141c506031011a0101200c1c00010081c01c05a07000d81c0e4514507807028210086480740c0f282446800320f44400070800419401a20741c48413010301000060500c0407000c5504114603080341c5011101d40042816a415070300b20700e084003500650701c0e2045d850b140c5036039000d4020070081c1030620498034447d24402000740300000040a002c0692489000e40c00c0c034540540a0b41048034514403894005520a285041240946400b100490400c0340a001c00d40e00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 517007724 1250 517006474 517006507
    0x3010b0d0c050f0102031b0d08010501210c020709061811030106020705040c03061509060f050c1911030d08060f04181b150203210c04060302030718030b0402040f0c05 73
    0xb40d20713045d0b000501601c0480030790b003280415001d01040c09003410100307124008204203c141c002a0500030700380c20804c0340c048640c0c3c42d01900140d0a5000501000600e426031802000c0d51045003200d0030000c000c182040900d076042d44d2100c5480c420721041007e81d02c09025030009000b44001a4400e00d030400461800b42c1180b00c02038014100007480a4481c0b8060980d201e48440c0c1101280311030108015141d4810140308400d2018a4600d0508881000c1c641d120071000010003401c0c517050b202d403070510801c2c400c0e20110803002411116007641411b00900072500480d003003031082113101140c0300c01d402e00f8064030380180d890f4900721780008100d5503840d641d00c07501110703517009410840020418070030311400043c5a07000c9400035a11180e1440c2800d1b00f501400d82c0f820200e110303400074890300c1e040440a48041c1e4010b400c002d85c41c1d1751f40784002c80c3c07000c8102c0410341c82004400c0c000428450084000d500481c02030b40d06001560700b10907000d05990b01320f110800042e4042109100030300c3c0108 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 517008974 1250 517007724 517007749
    0x30c0102121e0d14060102010203070c030c080f03010f08010e06040c17010b030102040602150a0605090f07180b0a11060403200f010c0306151403220204090b0603010b0d0c05 76
    0x181d02d82840d4030440c203092150407000c44400030070754400e0b04e69a0880c54400c8076521403024402940385140048001f400c40a540ca0020180210710651104101f2908240d130b031701c0001e01640d540c6a44e5a0b03120521204203d20658545520708111500b6111012031000c0c402c40d08400d11841062400003041e070075044018070034417103541c0e4094030f00700c1d55400c1c00200010003480d4001c0a0800304041090b103096005402c081c3c24a2401d4070801c1a070300c9040301544e2050300000401d0b031942c3c40d0401520000002c0c012656210061b0802180c07142c41840540400c41c00d5680741e50503801c0180c000d44c1d40d10000c1d034000e07012814142400115480c91100720540a562800703550360002c3d00c2d5455800d507440d61001c1070100e0f8031020140201140d40d458064400b41910303203c117090441d108402a103200107000102103840d24540ca8070541100080400000c7d405441009144a02d051111840400751807292007542040c2c001e9846c0d1514002005007a500310307008264092401041180d10762058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 517010224 1250 517008974 517008997
    0xf0c0114072f031c030605040209150c07120506040c060e030c1203040e0c12060a03080702011211070b010311010306031104050a090c080307022103180a05190f05030c010212 76
    0x2c0028000c1c0e500e040c421290040d20954001495945051300602551881c1c3c0080b8001d40c4140401016540c8802103c0b41d60300003a8507031987c0d90301d110142401c042041c2c20400994041d07101110400a00082702032056000321508250301d51100c0c0101e48124a240400382e2541c009a5000c079240b510900380100c0484280c1228030382669070503070b8a10f0f498100d4072b010090030042281032520000d0302c0c40c540c0c0f15400312003400c1c50f541165200c0401c0d00900b48064100180301414000e01d01569100382c4020742103501682d1240d60b1071522031982c00702400102d0b10f05180c50301506a80d4020f00079141582c1d40f0a00d002804c1900d5028800280f20041c2001c91080d1511540b074042902c2c47c501a000d0501072014540e00e40035401404200054408074980c414940c0a041c0143d10002c03058030002540006c801403080c8a250000d40c26100c141c0040e61706c040b102889010607002d440d03031002100c0070603914100301c550324010161601d03d0f0340da5190158200c3e90061200c40d020303600402c280e40e0b0f00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 517011474 1250 517010224 517010303
    0x100e040212100e01020913020a120b0d060216020a0501020f0a0b220302030c010b0a030f1b0b0c070f12050a0b0a15030b040312110415110f0c011407 65
    0x5440c210742c1510b094004640a40e5400151302c00541050b400846040d00d05040540ca0300b04107500040000038600c80002c84150303104112409950380d000c2c112203982e0455270035501c03128440d180b212a2140844100c1c0309190071a030000c0c01d9400402e1100000904034060010911691a503403101d560080141421100c1c1e450386210594a280344e0702030a90199009503100c20280c00e60608582950894034070403644607100704006900c101c015107002e61300680d040344829100078030740c00c21a40c54000c080604804603150440d08000070b190300484004c1c81f9041001d03952001c0c3c81c0e014441414000e0306c9900b140c60760b4004a42000100d64000c0007030040010604120b07207180f020300c0000c3e00111006c80442e07041c001410762281c0169004d01840608124103c44036290002501c118400c00540c402c1d010b101208480c0a03018036205001190180c030613200e06100200c0e02e403014920f41c54003081c50401c00c1030401c4841e90030303a0512580302d102a1014040790080090340d43c02d14100d440f00044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 517012724 1250 517011474 517011493
    0x8130303060e07090305060108010e0705040e01022710080105211501060906030b030c01020c01030b06211e070509041a040c0f032f03060d12110105100e040212 70
    0x2403140c40c802e207030384d903140d20320b81d811403800a080080682c0b2146c59681811a0701d05185404942d003021560f00b198001401054000d109019000b44500019240d0f540d0b108c030010712980a1034401c01403030450f403460307620103102402c1d50750354070a018481d00040c0c100700e109076003801c880f00c1c035000c0c0f2080000c0307500e4806601c410038881c0409030170400001d140c200381000040d030140031744c25810008902600c0d580303680b440001d40c0c802540160300e0406440c2c0c40040100d03103884086031100e4030105005000b6803041d01c00c3e420003075829105030000b224149962083c0e05003e01c0300901039034031903560f146456500700800014020203007815505008000c2c8101e0255140e10906813444842d80352116485800c80014080755042081c0071a0104000c0034088154100c5c0000b04281c2100c550b182c1e00c0c0c0d10783c0e1000c07460032064168001c04c01c1010800341e40d5440d03049a80c040300b030381d5a02d0090000e0703912454001880e08051013a0000440c0701ca001c07400500c1c01c01c204000004e803400c1110031261 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 517013974 1250 517012724 517012739
    0x507141c230403031505040b090f18030a0914010e011b080d18061505010903060e0c03030a0c060f060b12070c05191e0506060904030207050603011409160813030306 72
    0x1e03040d201100460768842c0c1e5281c0e0040800425002031400b1242044000c01c440b0125607141c1008004084000b90f000010346e0320340c2410700f82c0e00402d0b01341d003c0744e8940000c030314003900c0c200d880d02810101e100000074108c52076100e01d00b19084020306039a000c0e9800710305401c8000c605040d24007141d420343e080c07281c01c0b0382c0482d512a116038515180c03ca41c4c040d01050410b40300310340814941c101900181803051041da40c000c010f030310031254000000141c1100d110300160400c2d41144416a1600000903170700001680103500c414118060903041140d5001c55031800d0440f10305100e41a0803e40c2400340041c2080083c4007180c0c03200040c141320b080e060b03590b590a41810340c2c00003402c401080d0301a01070180901c4040590590b41207824918800400f52501c0340e80740c6008120380e02c5045058002420580b0900c200c0c8010f1002a00894403541c49113290f0030b81c603240b08015801140e010f800a608a0705a002d80c0c3c2c0003a01c84e0f2101c24550722030f08041001c4600c1d1040c01d4050684490300007990b01c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 517015224 1250 517013974 517014041
    0xb031303053402102c030c060a05130902070201020a060c030f0504050105010609050102060405151b070515070302120a050c04051f0206091605010e0d060f0507141c 72
    0x284000c002e84100b1060703c100441030110442e0f110400540c0790381c00060040506030604101c4c0180c2c0c1000040804100213450107803490841d9801c00800f0458244081c0c004024058070b030204880c010901c4e481d0300c4613000720300420401074010b9120440e4180880c50b142d100301100c070814a00807a01d440a121072805031601900c040314203030b54a0004000256224601034080c0c0800d00c050b01007400d050321070590300d441800d134150000e0603d0021074502000503c4004421054145a94542c5840c3c14180e481e15a4142c94900015101000415440c80f80c422280442c901c0104c125490b1121001f50700102070040416640501c03c00000c90300c0d42c0d9034943d0140114a0551100c4c90340000c050007401d016000d041614540e02000b00074000d495200b41c3c00095640a2920143c880165000207400c2c111618002c0c240350700c0c1c030101d0400c1e100740380c01152044426480baa0f407d00002203021220740b040c200078107900040c0c48038403030f00d080c4907400c00d009485091032070f050720448907a940c0110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 517016474 1250 517015224 517015297
    0x3020d0b041a12010b0603180f0d0f03051501080a0b120102070c0503070504020f1813090605071701060210020c010f0c21061212360b03130305 63
    0x40910b82c0036403524501e0180700e100d001205610003406200100d00110704240005000120325a4101c000c1680c002000c000c0e50044145000459840d44801e04014240700301141080380081e00b000300240f03058038000d2043c402058182d59010780303581e80307010900040111b50900e9a2100c0c1c100c03e02d4542100034005040c20703d0092041d140c000f441c2c0000c052600550303030b0100e406180188400b42c0440e2889055681160b0b07010642170f002000000000e45070450310744032020152800704004140815607004910898050302d40100d400345070318581004040900c0b8280059210a0070030000200c207030040d104c540c51a00011034900c14141408084d10711100c1c0d0f150000d416114002e4541780b0801500340d8034410964100846410000c200345440004903010300141303e08198428428450301c1502881030041001500107010340d050403226207190020345032840440e190104808031703a081102d0190311001812900246259415503c90700030084403000144801c41d0740d0602980c00080900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 517017724 1250 517016474 517016501
    0x130b03040b040f23150603060c07021c021e1c050d03090335130203060615070b01081014090d1809020d1b1e1101020c100b0306061903020103020d0b04 66
    0x5c09848400e4414241d6500400452195101c03205001c08903260034100c40403250140c0c0c81000b00c4000d0b280c862200401e0400003908803004642c03c8450740d2642c191550703ca04115031000c41240645404007440c08a403c2c094010380144100042c581d02942c0101002403080c1003060400311060b4440030031048000800409103201c946901aa42c070f18056150300814030014040f00c401d0580119940340c030001e00081c0200400c0300440c0030100b48806031074150f54848510102581c4405c421a203170071080070104901820541b0300118440201202c0f84200c030764100070000d02045a01c00c9500b41c440f00c030149480c00d5160b102080000d8180001c04079130030382840202d200540c41c0180300121100035504420071444220840b1a0007440d204500d89030242c0c03521006103064000050b00a108850004a40f88280311010921803095001044100421010b8801136601c290900840813403540800207103440062081c001503000364042e10701460800000207080684178042030444164100c482d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 517018974 1250 517017724 517017733
    0x1e03090c12010e060906040308040305090f0409050c10110c1c12030903080c04080309010e060f070c030b06040615111006120203120a09030f02150f130b03040b040f23 73
    0x582000204131071900b181465000300f02c0341c07915841c02081d01001610050400c140010110119a1109007200541600900030413916090f460003559031401084020702882c0000003101c0018014100f20280c1081c00c4054a00c1940d61800c21900d10340551011106145207407a5401043c1e440198604900d8117460021384000b01e401d01500548000381180d00c09441000705104030030010040d02e905d14002e0a1203405282c0b9000000d0785809060001c0740c00385008503020b801d00c503c03122450201c0c0c2c01030201405545412090205580003800361120100928100c099a244120180100312950360103840c3c2c0607035480071100a850782070740444440744501f000102549014005006040c0c030404840d0b103000d01c081005000c0c0e981d94403005d841006160a03010075034a491246035001320700d00c425503076070300a0840b02c10f44581000210b031080c0d15089502042100c0d4903401c81c1d00951b0400003028465a039640c84130110051004102d910780e5480303410880d02042104c02500c1c5801d04009003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 517020224 1250 517018974 517018991
    0x306060e190e09060711030910030507020f030307020c040b06091f090e07080106170f15060f040b040609060305010b0f0f09030d120e06160804050f1c030506061e03090c1201 76
    0x40245034448540f0401e6081000604101d9550056488602c291818042f8090b690700c5000c2c0c3c140b18800700e0f809500d020000410507400e034081450003003070608450400c8001452002d11200c0d0149a2885030005211110003107002a800d00c86e001080e22494601c2e81c040c1c84480120504205a0714440031036059001400869000802d0500541030100f101c50107250107921484500c1026026050708a112040300140b074079480215480000c40c2c86000780c0d02c0707684628142143d402445803000240c0d800b140441d1691090007814101c0d200c0300400c9040c0104181e140d00154400d2405c204055010090621a510b00b130120185452468643e44150943c0d61000c100791440210700321000e41100702000140d480c85210403405e001e15140440300ca940c1c5142ca1854003400342450f21113880781440c1204c3c1d880311021203601c80780d0280c0e0f0501503612144180080f070f0040c03601100c0c09420a52000e8104c0802001555200308100110b403d004001c202090f05403402d0700d1011400c0e51a6100c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 517021474 1250 517020224 517020227
    0xe1b070b0f070e0d140a0b011d060102071d07090314070f0801111c090b1906150c0f020301061d04120e030a0816080423010306060e190e090607 63
    0x7650010b00343c01c208111410842c001240c441c203c0000512803c444844103452041c01c00c036010090741e1000e100c0c101940c4030420700807281e100c500d0100c221261080000c00d60351000c03407098121903880000e80544600c1c648040e0000400500a004001840c4800804546120310029141c640003001d00102418a20035849141e42604025050317070414980011240680701107c1020311040d00761007650202d400d410004d00b0418001404407040c01d0184600e84180d4802081150140b90003009019515044000000206615a000f080d180c00e407a2000c00c80d540144401c9500c01000011130701d4461040d031041042e4200c0c04e00c1c0300a0030707001b000108503290007180034241142c2404c5040700d8810001030344ea590510310041c07901401054980201103c4003401d964a54041c082c15291381d21113402801d900c100c2005e821178440346204031202940240314140070f441d950760780c0c407010306264024443e22441404004206802e400b5001610710115048079002d44901d80c050102414101e10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 517022724 1250 517021474 517021501
    0x210d110904050a1802060904020702100801061205040f0308070903211d03071a0d0501090b031006050f04021c020c0708060702060709090504020d390806010e1b070b 72
    0x2000303404503e00b80184e04801c808001d0500705a03411542c8075501c00000c0c000c41c0c068050000003e400595141c2500b881d5500b05a846040e50041d940340c0342d15082d50008001500c0e801d0340c001d0a40900101c0c9080400c0c45526107a0f84001541017668216960343e6a5200b5141d18a42d40c1079002203c030714590070300740e00500c610054103010400604480d41940000d441c0c460034411145111407410031900d94002d00c0d400d540140040f43c000700155030f561004c4070040d0000c400c00d548280503d4514200340312003440380800f42d890250203000030120500030b02c00203510a407004203d00c81010031184806881d80020602e0b01e079104041d0481034641102d451505c4400303840394055420000422149540c03058060045810060340030410761514004210a02d1440b40b0151220010400300424540102200d802c41c102e07d00741030059544c0503581490500a0703000c2d1030b403150445c1c001040780d4071a6801484e0040d208215010201c41c14449090041c1c0c445041128500b8000c42041030382e004910 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 517023974 1250 517022724 517022731
    0x90c09050303120f1023090606070c031b12050c0102070e010e04110616111528170106030519060b31090e011a03210d11090405 56
    0x107008604045200c1e108607002c003001000085107140320070020744107000c0c1c0e00703a0360020056600c005a1848401048001c00f4500c442c0381806107000038042406814070394200d9171000d070010118200e40f41140d0301c030303002000c4444012141400d80714003c0340c0e00400060110708240700c0d0004088100c0c0080000e410300c82e8130b40c80408144e606e0b0004102031400c0301d40c100c1c1d200f1380c002c0c0c81c034a221101100003203807406842400700850b0840c1a0487c204850340702030000c025411914520149054803d5503030724468000810442c2c8408015010030400001e03000d50103601a0524101804580990100e0400241d210748002500e51050091007000580e103220300031019441031003100d0074003100806a10904d01c40d24102d8208030740b000c1107040c182e1480d80365460902c400c100c1c00755071b80d8100030140c0702c5c0340840b248952802c09455107049450b140454400b601801801c40d0070382d41200e20340c1050b2041c1e0301070f52500303040001030b4000d1000d11a031008002610741c0d480d16401c00341c0030301c4102c40006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 517025224 1250 517023974 517023979
    0x405090705040f031401140f1008191412032701111c0f0e01060518060a0b030a0f02070c03050606010c08030a0f020d090501230f060409020402090a090c0905 69
    0x200b1043c4440d401140f0054140c0303410208690f0040c100781d9400d4014400f8208403c0414181c000380901030300d085400500030555601c40c07080040e220030129440d1a00040b00c4a042922503101c800050700300020b0702681d01c1c1d0321090340c0b510700f0ba44c142e0f0030907540216106242c103414840344403140c12103a104042c4402c0818020406040c0414140480d4850b03051541182c0911032482408040190080009401000814822441c1840c0d505001c3d00c801c1c0541841a9903c00030104690b0704514220b00c43e032002030100a516241c0100d0020a900c0900845d60a40d290004019480c0041c00240135807445418125440c902d1410301a0030300c84050328070340c10009014001c60100c1c126600356130300b0071035040c00000c8031641800c2c0400207105400c42c004a4500b40459a414001c0650040c03115004401000296445140b81445070f0101201e8150000d05a4801715115003403a9000302c2001d48050001032404001d840001c44400312a0302ca1107605855a141041e041e510002c80c0e1300400c0705 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 517026474 1250 517025224 517025227
    0x40c0b0405010806060c0c04152309072001090305030a0e1b040b010e0a0801020309060c0a1b23012901020a02040507050f0706021201050f01022a03120405090705 71
    0x1000002059010302070f204c1c0e842a1404241c1c002c02c8002400048a0408024000c101c030002c5d1301413100300022a0720650075071603424280c404110018070035900034508001c100d4203039544d03800810750384040d683c0b20710100000403100012100c00248a05404c0750301903101c090302c1f842c0c00c81c215015504c00b0013102d01c068001400008a8541c040031444402008460202d804801b02c00101d4100c4481c02c1c0559000726241c40020780341c0d006500550242c00d00a06131092a0b80301010b80d8480e10500d1409070015941440a20450440c440c900c5d0f0f44078400c00580b41500030303040e01c11100e030020001e841890b954813008107680b0080c20312800710102c0c2c08054407181d4400b402c0041d40710908484064081e503101e40015021501c40d1080310100302091119544586007070030510025001400c3c0e144a46180c24004121440c02d6031500503c60f00c141d0003090203c1400704c2004042a005d020000031100c4050300580665091003801b418030700044050381c5540c80c00080044600e406058030042c0f190 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 517027724 1250 517026474 517026479
    0x60c090302030607030902040e070618050d051009170a0509090601021b060904090618060b010203030c030c09010903120f03141b07030e0613060f080907180f050103030305040c0b04 79
    0x18003061080d1301c101d85040004481e10580003150140541020888550103010000f2440d00c0d00810002c03d00419082d545200c2074032a010310810154901c0054101d41c8042e403007420b803049075048580c03114841c0040c101d6901d81a03e500d46e00c1d410001c000c038041200425000e1881c10107512095000d00709100030040003100e10f410503000001c01240501403030000a000ca520b4495170416031141d644041d0401002c5c1c09618544280c012106c0c040743e5a83c01c0411800840d0301c000203071f81c05962076401851850715001403e810507803101040707605104440000001140c40466151441078054480b880e15481081c001403c982d004211103e20588200030310101c40b030341030000d04509954800c1250340d6059818142c034121512500107034003090000300701c003007005400d941034125142525820081d00d181e06058400100898000038141d0040c83d0804c6060041c206d0750920800001000811103205078048044e190240c2041d00030980315020f03c8100201d2482c1180240422441030341400d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 517028974 1250 517027724 517027729
    0x10f030209151f030b1c021309050316060e0709051006030501080a0b0709091e1a03340308031005120c0918010c0804050c040b010c0807050a08120103060c090302 71
    0x10b4460400f020007051024030402d14001d07800143e520600910400c01c10b4035036098520706018a0700c0c200c0c0150305c054140d0111141c0c40c0110782240d64000051030030b100c6590304460b134035600d02c1170690b4000d80700c021402500c001402900301600d8840f074041580c0c605120702ca406500a5800681050701e04401086031040c0031503a00003240d4032898240e019100e005040361710b8102a0401d40c00a89010081d1608206122031030060710310411040c4a591348600180140c030504800c1c064150b0001d124034130b10f09a5414400740003140707038408100da1200f8202c600c5041a40ca41040300c2a1100100f4447c201040c5071104000302412100c3d80c1101040c0c1803c1a03c910340c02030b205004050100225504114011a0703072045400400208038500341c8140c014082e91003600c1c00d071034030300940001c0303507481c1058000e10a4101c7e040c1c495004900c02c0356651140c59021000907929402400c10359800551030303400a20b12141c64500c08802941142410011604824545000e001e1003150410058 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 517030224 1250 517028974 517028989
    0x60601090311130605090c0a030b0603040b0a0c0210090b0f010e04150e011b05071205030c0403200405040b071202130b0c12030c1209030405031c020a0b010f03020915 73
    0x20402914942e1003210f203007852030090036140d04616800910038041161004000780500101c243c0c99505100c43c061003024406140b20907203000e046003e0034000180d480b020b03600f00d41000c10040c41202c00540040c40b8200480783c0000089485107165428810000d01c907a03281805051180311040e001e0400350f95952184c40c1043c14901c00640301c10441075417440a500603030a83c840601c000c0c10a44240744010102c0c1d005039400c40d103001401c0400d440701481401030b02e205001891a00f880d10381152202c48400014580410884200702440300654650340941c50080c3d10602241c2500e00f009c0d04044e0ae101c03010003444800e18811f01c10040707004a24440c5a003194000b2520540d90b41c140d010381802c00304040b041070800d000001c1802104481d040090000c05412054200c0030307210041141e89a204510909a0540c404a180800415600e00f906c40b1200640100c5074145000d61754043d000c5401da00440541810321401c00640c1080401954403c005040321040d265003a00042c159 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 517031474 1250 517030224 517030253
    0x31014041413030e060d0501060f030516050d0f060b0c060705070203030301140d060c020714060f0906090604090606030f11130b092b1a09060403141611030606010903 73
    0x2010303900402d0340501d40160300c280440c04024000d40c1c1d64240c2400c090340509400e05c10030001922244010380d260b4828072a0303602821408038100841e43c81c0c004111000c0e00003840d00e9402d41e03514107480d0341e0200c0c14428140100103100790030351204060404181400001072401080c041c04114560059401004880c103540d41d020009c014000b0b03210200350144d00340c82c0001c0c082c62800d0141c440d080d40004103801150560810524034002103802d10003240600c0c0350001340614103200000c02e0f0b242020262410203009401c031410f182c0e440340c0da00c043c0c41442e071080f000b00355280e03080c0c0d5a0141c903015000359a04a013440601d040c03240c030012980c8084611074400b15000105140183d40e588241c2140c0351480484400903c5040c245080290540420f045a0311a0003907011480303483c8000f0b03041d01c00c1000c440a40610360300c5440c00d075511f080ca080c101d100010304103c0741c10046507058004000078018004810007080e110141854820080d0941d8180403517440300300300103103040010144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 517032724 1250 517031474 517031491
    0x10501090b1c02071a0405070501210518031201050306061e041d0f010509150702030a080a060909121101020315040207062a14030c2a01020310140414 66
    0x14030704000b000d00c80080c05130700401080c4c0080300107003059000101124078001e0340107106892090342c0d04c1e401540d0302d15611403581040048141407007841c1ca0700740d00046e84410300203500d04800da002c90110b82154813981201180e400e0b00c400610442c01c04101c2d0b907a001405507080102203110f18000c00345041c2103014103200e00d03111079501007600440c81c4072408031001c0404440c1314440107550103000c1d1504490681d1207105050b0941081103929441034060b5a058020307503c1c1800380c50781119002c00c014100e00c15075848003400501544144144240903010f02e10303c511401030b0707907001409440303107078139060040e8014000c8c040703030394401d11168406003012100180d4612292421201403c00001e80307210b001843d40307d00b440000c0500340c0d41a90710680d5204a004d90508017890050701007696111613101d400e2000c11b12000f018030303052a41d9040160700c074801d03a18900c0310707d003640d00880f072446030500119000c01030140c46031240c800c0c240e01198140310104450965807502c4800030041c40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 517033974 1250 517032724 517032757
    0xc02060403110d08041202120a082a0a080d051320150a08040212070311130219020304050f030a082b0c05030f07020d0818030421030305010501090b 65
    0x40d580c1c0f002d14442e5591001c0042c2d1261307600c0090030b4110140010a90041c00140141d030496600450842c005d682d0182205003002440c5022540e4000548016248096601c50100000c0001c200d249a8035128003c01f80c0c1c1c4060075000340c42a600c0c040c00f000c2c0f030001c14140880000e20000e200d0029214014114072900740c0510005600b280020003c5000c0c08000864014080d84082d070a4131030b5000742d13540603218229440099451085200181540c2c0041203628200c0c90410452041401e002c04050b040c00007107510601101815580b84001d40d0001400b0802820103640810604070100e001d440800700c00d44481c1c1d210310610903440844c000c92251601c000e0b45941a081c18a00341030010014030318180c0e80030340140d01c01d4440c02c0c10315510310005810148000394a0725280346980c2c0d49412600d0b403402c003130001492601507641c280001d20011403212a0030034642560f8030154111004050581009400c681060b000141040007500f01448414070724070445000b24102c04405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 517035224 1250 517033974 517034003
    0x6040c0b030a0b0402040b040e0f040b0c0a140c0105040b181009080c030c010c17060f150904110304061a0901030f020a030b010308070b0a06081e15040b09010506010c02060403 77
    0x10010143c104401d50f20070b20200d00402e618050320302401c207480310f1098083c500c1d01e55004c0c042103140b0440e4005e2000c4c03490300020305c1e01c40882d00980f4500c6423a051020b500ca21210380301c0d0883c0c1107502108500d80d0345404000a03c442c900c40c1e650090740c4003045440f10f90a00b07000a40341d6230724610300508030740c039404140204516181290030154000c8162a1106186404d0fa400b910710380510000042800c05641015400d00d50003a00a22008080c501a00d040c1000d001481613036000352103c658051169804603101d9000741403040c0c0551a070316a50789481e2400301c0c1241d070101507420050710112980b28042d20f8450203035055039005400559050002e1000440325400c6401c01032115403041c00000420007a80054070403035100702c07407440050ba07441c007e12040b40c410b446809050703441030301500c541c441f02000040505040c407050301c0761004002e40c03504040381d0907242160440d50040410000413020320855030003007424070740148142c01e1900029483d016902001c0d10300203603004034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 517036474 1250 517035224 517035241
    0x140a081005040516030f060f030b06130606271d1812030105031b010e2e020309190e01030b09010f060611010c0509090c090d15061706040c0b03 63
    0x40c000301801401405a440c00c0d0700310702030705220b40d10200701283c140780c1850428503042c050401990000554405114516259501c88100141070590800d440e050140c14103145806290f0290426884400c0b00005c039240403a1030490120045c840149e80700c0003408006080340c804d145c0a45081c1e9000c03840c0c0c07540001d40d41c4460060110000a10906071f203c0c42c0c4c4800000a035040710000c07016548944140b01c00d84200f5155500034a0024102c0700350510305144c486110500240304800408422006405002c1118045410000942d01c041440d2142d807400080030b41000d20503489581c401803030a1012110800306000080034012100e0001e40700590960002c140c400c0b5000301400303080e0b40d0782c4018149115003480b0140c55428000d20b400242d00603000c58181d0640540700a0240e41c4030600000305070010394030703d80e00050305582707180895207081c1c142d50001e550079000500d803450180f1040e942c08400c018140d60340c00200400c0081240080848112282d0030401c41c2d480d0b460f0107a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 517037724 1250 517036474 517036501
    0xc030103081e070f020109050d031709010e031804050907030c030209045a140114010b040806010504060e0a0921030501030c090908270406031a07140a08 67
    0x242d00c0510700104004051000e800c582e8112507000ba2160307030629481d4420320503800c000310400b6011070302100e1400301c4442c84610755503212600b10000242e20020000275410355000344083c0e00442c803070340c146041c01e03e028032601c3e800600e82c00040c0040c80c51a03a40f80501941484080c1c03041c01214001811310a02d00342c18094582d442c400d06055030395282880d02c01c010040101c407400d106488480b40d25403650500109103a0300c159001d1165400d0342c0d07400e04603204075801d0410075520b0b440920081c04507403400501030003075400c07800d031160705020b4504d141020581c4214802e50800d401000b01000d031803c0c41d40c100c8042c0c40f0115091400381002000710603080c82c424001e10390315084100709030741135000c20305030703442a00c1d02003250307a5034100141610100c039800b410036441088404e04100010040305051507038000d07151301c0d0fa01044001341c100d5606a0040d6004800000360180f01c840c0403420541c01445824440f04100509900c00308500030100e1070400d1200107004030b1208152000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 517038974 1250 517037724 517037767
    0x70c021c1103070f0810020f0f0703050a021c1b1401020c0303190b090f060d08030109230103030516030905030709090501050a1a040b060702040c0c0c06080112171b071d0c03010308 79
    0x3c0c00b271a40e4401529001741030354400401100180104949900c140c80c058144803200e06580d96044d40c0c0c3c0f5401400648141e503107010480e040e43c00140340f03c2200d0428000741024084c0400610b86a20f020b440c1c0c1400802d00c40416003c4c81e1510000084c2d658501c074020ba0417400c010071040c4103517940c0000c1485036242041c0079020b048040000a508041c4c1d400c00b19008140400c032441d800c01e00c1d042441c0f90503003800003c000c154180022004003007450f4100ca040e9010b45004645144e94102207400c001260300042131182e01c840c011018003909002d4185c0100070980b04100000074400b101000c00059042580700d00e45603030f4040401c1e40c0d0079080d02e83da03680041007080459100807019000b6101001c0482d80e040891500050780c500950640703040761407034065010071600d40d13900d0030302c038964000410070301d0300e010f1200311600591016030905090b0390300300906ca400d00f03041205051140782d041c2c82004030462001c01500610322001d8904484d40000480d0301c81007040070703540c0c2070380400303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 517040224 1250 517038974 517038997
    0x60903180111011401170a020f04021c090b060a290a0c41030711310b040603030e04050c04030f15061508070c021c1103070f0810020f 59
    0x413002e0359806540030301150486210004041402c038140b40302c4c90301c0b0f0341180740207540607800c1560000b550415070001c1c9901c00e8242c0040d8445c4000e480c0a208694400c0c0c42a2079010f8414200f01403403c1464105c0080e0040000d9404e00549017404540c1049100d041201d0074000880d6040da42c0f801120154103650707110181001d0f1180e820300740120384045049918850420b42851500303148001007225007003002201552400c001038407542d52140c016010107400c54925400c07040716a20441c400340501c0d59880c14141e1b049034054004094481c6030810900c1149001001c000003600312008103003410007554042241c2d80d59405402542c041d41d4005480343c555100d441c000c004c500c102020703110b980d60104100c03994503450180350420b101406400802c01c645d0102d82100c1c000d0b100d05d00300c5440100280c24402501d0b000c0c83da200d8005404803103d0245d07c06a282514042c003d04000d8100070311f5002e8200d2402c0440c46d69040000041183c0590014061071002c011750100d07204007460 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 517041474 1250 517040224 517040231
    0x71d1003020f0f07020a0506040807030807170301180e0c0d1412030106201902090a0b060a0f090b120c2d12060a050f10110d110d0206090318011101 65
    0x50600c0c103d584d42c0018012031040c55440c0002c10a854801c0c00d48081d981c048000b88401c43c00e65603028801d40c86044155542c155180340c10144407041c10045001c1c00c0c0b150042028511280b0306142a90303180c5000c0500c0d40c0020848802d00c0c0c50b0540304a0460790800980d03141c0034034898006041c070044c03100c0e85201010000000c00c08070340280381c02070200f281fa40760401400c00440c1d25515418981882d080c184165401e11025182c400140c507040a5181c10018440394a0000a0300b154010102980821401c003480c080c0190007030029801000c2d01c1005503c2c08560026070002500014480845000045103d820404400d0b0140b40540e005404944048400c1c20504010750800309022034540d0000001400b10304020074441c044030300160002c0500c10043e010060f410420b0f50007081045014041860300000400048036100307a0340e15003d514050415001d070600c442e840c030190643d8090414021411000012117200913810701d00015011281c400407074100c1c03004000f880282d8203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 517042724 1250 517041474 517041487
    0x3181903080a090b03060102030d0b040209040507091a12270f070e060301020a210207060516030513030903020f0105040302040c210b01050711040e0307060e06071d1003020f 76
    0x1a504010b0612004640303e143c01550b85049444040c0310459009005070828010300b07086000303603048540c07019401000035080c80070324404a0100d40d400c9032000002502d4100401a07241102407240780026407003502d0b40b600010700c00c141d08400b006400c030070421590348106014540358000c41304500c4030030000e90340c1c0c4905040032196074034401d020f03640c55070241d4030224a0900d41442242c80303a0441d61a01c44107040014800700c0c4044032510748180f400e03003c022000c0002c0365441400c2c414074000380c1500720146250030003000c484006184052031b01034060801e0210381c0003041c2d082160f0f0704407041c0b0000341244004880710301a5501c0250090b05004030201019009002058555180c1c03955100000301404010182d5901c0d82916003c40c004100420200b0042c8120382e8803203c0141000c20503904500703146242d40e021050540da25956403010074045403050003000d80000e4180f0340444503070811445c010440e0b4405c50010b20601d03203404120342990098042d21080312081410755160034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 517043974 1250 517042724 517042733
    0x705100506100f0c0f050f0a080d0c0804081c2003060405061914030703080a050c0d081b09040e01050709081c08180307020402030115080a0501050303181903 69
    0x80180d03581c9108807280b030111184548640300d100c000f100c0076590081e8020154650145078032112806891900465044d4900c100d010404100c1e4148a880050358034000411020110794485404004025120b824840070503209015078521104031074501c1d46140010f6160002042920900f00c141c0404440300086602400055882500280c038140440d995560030491158180c218181c0d0503030300c4007002d01c2480701c2e846004244140c041c0480301c40c00c1d01c90301c9051458015031101c4000030b4000812000781d00090021190200450030410546e0900e0340b0440340c944902e881000c07002101180f10011035503030780c00540036032882800820050605000044c0b10301000e0166100c0e510848039403403040ca4001c0e1051000d03005554407915142c640210050034001c2505030341d203981c401407080c4030250f41d9602c019402841c48001950742904444400340030020000d003980b40540ca01001007107161000310032110450320205c401140e01c512000000e0041815014054040244010110400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 517045224 1250 517043974 517043981
    0x161b0303091509120e030120210112030c030201090b0f15031c0f050c030a05091e030a080a030f0e07050411040311010806040207080307020a1106040f050d0206070510 73
    0x9501491141d5403106152012205951030480010301c22003104c000c001000c0c2c03141048070826000280003146a00c20400b400c1180c168110000c211202300007040c2404284043c052803400e020307000f1401107585005003002140e04419409020b10403600d80c1e21003014800e50281003495405218528141403d1600080501c002c948415a00b417603201140300a140008401e011600c6000d98003107100d1500c0030488513000f160300d600082c00b00034459072610344801e00107441c03914032540e076042c0c545a00c5400c10068110410707200303c0103c80b0819908154502040a2852680010480d43c1d900c9080c0402c80c0101140c080c000829403808a03032217400e103404100041100c8040381c080c081103010514041d402c0c81a4070004041c0102c1c80c0c40141294000c04090b64015002413005050a01640320042c59a10132116107005810400b25801008840c070000c0c10000c4c0281c8046003054106120036800e00c003140100752140c906020381d9001c655440080b9041d05901c1130590781c2140814441e480603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 517046474 1250 517045224 517045241
    0x90b0a050f03271203190b1203030403020d0e13050c130e0412030b090a05070c120e0108100b0f030619081f11030a09020f04050702030403060e030a08161b0303 70
    0x1c91400001540c06007800044c00d914900741c0c0c25881d480d54403450a0f500a1240303a101868445865031585e8055a4503218030110030100340010b159245010b107802410408030208180620500340c1c1400f10741e4030b41003900030345e501e8442800031345074480201c00a900d0050b038945005448002d400411510b68079186035000d00c0c802ca0f00700d03103d48034404042e030a40301d108044941121074400020041846500080e41107011406c2c03940d415100c680b92240c00010807840d0740041100c034500d1041b1960312100c1e2039130010034400e800b5800760030800c0d000c06d184038907883c6082c0042c0c04130200e40d40d561a81e0410b804441e9844103c0009a5581425515440b0305a440004660034065401c0e456403030780184488071641d202c1c0e403459540c038540c940b0001e140210060780c1202c0350511611072620345204007030003017171320390007e41e01c2e54958a0501e040d906094418816500140a000c01050b0850361041c1c02c194045c4014030b042c890385034200c90044142c4c42c40140d546044014606058250f80b00404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 517047724 1250 517046474 517046521
    0x102010e03130f05090103110607030c0c0e1501030905031e0d2c0a02030706030504110409030816030207050d0f021006061d09091e0f06011403071203090b0a050f03 72
    0x1503103543e40e420044902c03002d1001a08d01c2e2400c1c0710302c050518024009000c80c2d4882e040c98101222182c41c0e80ba611406030704154060354100c1c00f8400490244604644004002d01e02401800740319940c05031640200b51620240b00ca07200500104009008280c903043c80d030007481002030000740c03042c4110b031400c02a11000c900c810116070f981807602c04558a1021a0094024000b003071400c4812070081100401c00d540c40d09030240c40080319a210302030208464000c2c0d480240905007010060380c80d6041c42950360516204101d4900054008569040315401030b051070030041d052608180d00b491034000c0c1222069241000106045400c0758449240e51003a0b020b90180c40c44030018000c00c04416101030784140c2c401c80c5228076032003400c510340110444840a44e400b20030150200c07440d224003170700312800390300c105101e80c01b1a041c2040700000a10010b1a5448001c8258030050034041039406260b0001c20f0014a0701a254003850450f800d01260550b03890360391415115846091120604800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 517048974 1250 517047724 517047749
    0xa090812120906070815151306120e12030711060709080d080c1c06080a0c140306060d060f0204051f0201050c1801120e06100f0e0f0c03060102010e0313 67
    0x2990b08200240d141e1144911703490340f00f02e42d1500340000c030030391801e040081d0b441011a00d94599900710000644540c03015090304991090816402400c0d0200601c0940c2d1040d20303080c107601c05110005180c000700038491040b20b54a8844400840c1c00c80500304d0703211003c0c03044070180310010398046940e41c203d0342c0c154290344805114450490703038600e05656035080040140408200882d0050b80c1c0c082d0b21071440c200043e03550f40d079500320f4104080140141c4400031807200c104003100d003100300790800450850103012945080e0001074840d0401036006040141d43e00d4440e22110f110340c0c11540502001440d06680301c036025400301c3c2c9244890310340d80040d400d09002c1a031583c105029180d407a1100c00c50040c0d03988220004440f1540d110958100540d12580300300b0196038103110b401d01844103022035807803039800c2c152004011400d40e40a40c00310048a8100901c0302c66052495421425030039100380d503034a440004030b02508458508400f2800300148010000c00c514031040d048031500d16a42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 517050224 1250 517048974 517048981
    0x203130c050f0117090703060e0c0103150b070f0c0e010b0306030c100e0d02130204060c051b0105030609190c020606040608070308071211070f14091009020a09081212 73
    0x2820040000300c00e0216a1025a9284d160072040f003843e44080b2010440f819540d60340c880740240d070400f006950940e04401d4103c00340d56450302520421042e0910801c501c103281802076080c6d4810000080d0070030315803120304020061005404002401d8035444400f665856105814084e801561003d220f88500c21004649083c00303072451100703010585031482c1e6249200c05102800c01d000e8400c1b6407050818040c6801e0300310b030344040c1010342081d0780d4088480525240151030700c005103000e0404100455180c2e0349680c1d1000c100c039032010b070607504901192605000350562000c2c0010059005060100c254046a030014080344500c40c00c035014172a095481402035102e841c01d02018013089801c000001c08924541c0f4502c103407000c2e41c46c0c2242c0da414900d1701c490424610f608210700c03a5440d2441004460403a111300445450100c6883c58203042c4074842c0c0000c0e14040c4030303604a164011455219071402103107108018040001a82d00000780c1400c040d406500c4004010405004040031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 517051474 1250 517050224 517050229
    0xc040b0a1d011106060f040e0a05062d010603020f040b070b0a05010b0a020709050c1213030215131416060c0506010b0f0f130f0305031216020d120f0203130c05 70
    0x45034502a0070f8030103004951604424030400100036a00d19401c641ca500b10180c51510401c1903d40c00d5010700e000d030078981090108c80703022206115900e1080b8480c1541e07204e002004120b900d04690290138016940c0e00b1000c0785651600895104000e00c900105601040c803140341504c81c41a8000c400c2000260f884c0d4060032040d0090012450059114100c140450030a80d44096006240c0d100700794108521803200c0c4030340d044201c501c92049005600020300301a0100308a034041c0c10051070926071844d140c0001043c50b1035424001e010301c800b41164010001090042064156240c07400b00c5d12580c980304050004106410111054424070700005492008802524044401c6007001440c2c03541c00040c0417899003004003262070f070581282c00081c24560003500c91000710720400255450303200b210410384034004000c210411812301282d281c0007150740818a480d9080300c6092400e00c1c09428400d080061a603100f43c00c0e4803901c000709100012904140d0600340360301ca100c644403025100c105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 517052724 1250 517051474 517051487
    0x6030606051e04080111040305010c09061713120309020f0406050a0308030a0b09040311150f0703110c0a03031e02090604030209090a0b0f011a030415050c040b0a1d01 73
    0x40d9030000390060114041c100e40044030440c1207108140001e05003521130107803608450a42c1c80e0030700e080c1e50026042003000028041e0504a049038200001c003940f811201400a082e0b4180755031a0000da0000541502c074100795540b20079030001410f000303c1007510400307401000e40302420b0703200d0300f0102003030b00300c5203410f02a1000340c4401503c290b404178510f66030b03180c4070307040544070444868490307018004907120010150b00ca18002d40d100c03d605d460188d0400d080c44001a50410441d04410030070204c088248a117a821003114540002c0d002c241920b030340b00d03e000d60b004042c0d0781e01594800100f03040e8075810142c0b00c0c0001ca06090b180d040ca1402000491184144854202d0014030041000d49080303020194400144001d991100700c2555440105480480b1002c010a4000c0010302225071168444900f11240380d145500c1e40c1851b480c0c0401d5042c02600080c051a210310020754050b0025098400800d09140300075110680440701603c4a0000b01008801c000e404601c440c00b0341c4141c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 517053974 1250 517052724 517052729
    0x705041505100c0b040b100b070c0b090402040302210115240c0f031211090306040f03090810020705010f110d0c020127020f27190501090b0406060306 66
    0x600560001e103008140108a0070380e50700501070101c00d2203842c000c03403001d4100620440c03290346007010034540f514040480340400d410540165a06201590000d019420740100391510482ca164440d0907560004029201c2d64000a411411042c100b038400c6130380c1103620940c60302043c02440705501440b0569130b10309691003802e04404c20749121540c0c0e4100325444084036403103440c001070303c103c140e115030541c200c802c0e008900084500c0e24599a9403618170800401d40c400010040c80c0910510010b507079840c01030b10241000300d0070446c0c81d08050045d1310500c001c10420043d0303400074880d84031040082d000740d0810740741c0d54240141314200d1036041c41450180f0058100c1981000d1030590200300800048a500040d590707200041d405108542c04110f1a00d8a102d1054a0060052040c80781c038030900741c5003034000c0072561a4030122408501c408407900146107030300e494a586881580c0300c105c0f0b80e50203441885241000105085c00716800c08899039105690910905907545821400c50764240b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 517055224 1250 517053974 517054001
    0x150d0c0b0706230601030608060106091403031b030a0305090706050304080a090816051302030705160c0e1602060906061e0d021324080606040c03090609050c0102070504 74
    0x8410602004203040050104036000756000650020100c64100c0455200c989552018103031408126440d0f9150007071102030000d50024124551600c1800303001070100d4000d120307590001d1003040809880c00c00a550789038581d030b07001100350703004039007856141e038081c00320140040d04000c0040c07041500059148203c6001341e0794580f840e6550b4441c0001904050402410400040000036403110200700fa21000356200d06050365891402007002480b8460306110700d0241d0050042120741d9401c0030640e001c4403040c51180d40010040d04d096000420150071507443e40c8074110603c6180d10390345244a00b00901c45d0203c0708103889400b14250b40c1c01d0300301c0e5820b500040c0c03840301070b600c0043c00b0a640d03080800034000c000b94505d96130024075030001c4007440c030341c443d03586001900300e82400081e003100c40340b000c0c0751320068a81000c0c884d40d250b2500801050145444000c00c524952090344007102c425009070301080007180e0ba1611a8aa201400c00d0343e0061140a2004c51603281911030203138405a003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 517056474 1250 517055224 517055243
    0xa050c070f031502210601050d090b0105130513060b010c05031c05090309031f183507020409030c080c070e060415090507020a050d020f061b0d05101d150d 68
    0x310311100b800d0174001040281000801d0001c0f0346611154010030201c46c0c0704030400e072503960410040c0300c0800d103d01240b03061241050280030009031030b441c0c42d00a0640000010502403105c1006072004180300030001e110b0b1100140c0d407680c070a844920305d4034082c5180028406174481f003801a583e4010060019807607041000000356150305095410050041c0c110042107103038035004030001c1421610b00546400442890200d00a05410281e524440c54620385580003540e4450031400d40c024084000d000310b40d248a12002d050150210340d010542c0180519a42c0010728091520388000c1d1146800030740861011404030710741030040d40202c2240d9000401d010786040043d0001d0705014006500750f001e21490703400419010f1040510038002a0018101001c201e5280d901d0503000030038140001181442c1d06600200c0f40c0b00b1145043d121090101b46522846903d07080381000307901c866403101d400304203c1007151a0f600020700c142899007001e1400400c2d4401d105141c00d541c81e0062500c400b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 517057724 1250 517056474 517056517
    0x10061418040e010207110a0501080c0a1d1201090c09061809060e03030c0c071a0a08181f0f0501050904080307051306030603150912050a050c070f031502 67
    0x114000e110218040007070021803216415120341c0d0882c0d0042d4030985030222a800000910f0900c036103800b006100a2900741264900312529050600681216004120034820300f602c0701b41450344075500a090081441c10540c60708a665802403c4842007100c040460100010b40e21b012485140d04a6640c0085001901d031118010001044060f502b202c8040d5681c82c1034030320711400c0024500c02e0311a2212070703540e00030902003a8a00805540010405148417030000040c654a405446004840e42800038290310b80364500c40c00c008805518040c00d1050540c6410740f0120388103c0582640080701c01c01c078075030883d04850183c030000d02031203400c80c40003408600060160801154000000c0c0340c06410110060303030010303001c9140d03440100082d46480b4240b0502c00d949420700c5060f0702005080000e04000e42c0d802c08202c201c00040014008045420b64640c3c0c00f81d0308840018210740180d178002916210701904a408038001600c1408111b21980202c02562003100c1c0503548204042601e6030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 517058974 1250 517057724 517057747
    0x40b150603010b07081210030b090601060e040e1f02030a0605011b11060d0e0a03080f06130506030f24090f0c04020a090e07020604030e030c0a0b0d23100614 69
    0x902c0031130201c50624003085005880c03c80390411038041c101c9104101c0781e032850343c18114081800a481109550005801000703080d0300144c04610003041a9070200d0741090101046090a0444031440c09060340309613078590101c403a0f03000394807030000700303600300441ca850302e0046503200045040d60a04028440004021509a2004425020005089502d00034800c81920103448800c00030307580552107009075200b0550441100d5074081c2e0003d0842d5400d10b48100007900700c10703500b551a0b80c07103680d41c0e010421a072001d00110012070b41510440e040c07951a001c580c0c0b07032061a010381c06005070116000c0b4012a1000c10083d481c801d074400100504040d00b0104002540071103114814041641000660385c112031602d01e1058582d600580614078080c1400390596441141c40361007904010054125541c9020031760054419002000b51504240c80d0440020b00b2000b8024241c00403001050042040c181801c074450380030b4004017101d06540304d170141d40d060303001004034031010030030311815180c0c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 517060224 1250 517058974 517058977
    0x1e05060f2d010509100b0c1006060503061305090106120c0f06020309061c06051315091b030e030c01020324031b04090201230a030501050a08070e0901091208040b150603010b 76
    0x40031020f17640140750360b01d0948071103d40c45511400c10580068210303400310031061150f04000c00190070710b40d00c2c500c0d0100001d40c440d8800c41030659081d03560004544000e00961018025000512980084040038100132001c810f1920504060300b1031110b003c92210310100549040c0180540841d00300b540c071801c2503000700040c031f004403a220360300c543c00980c40e511040c0340b4500c8001d52000251082403801b0900022000d50801c111041c01c14104c071100541020030a5020b0481d450300040c48042400c0d4141544145894400c0350760000c000d0108290810030001d40501100d0320380d25841900c181495100c800305411800b142c00e00c03030803071045030038a90481003007140705251105015010300e80784d5048502c2c1420503c4010400306030840825014401e01e4090401240c0140c091403800300314640d215518003d81c2120310080c00440c842d2602500b02328600ba5004103043c50680c20481c000340f241070100e4007a00c452085802291020079107d50f00d0b030381502c0c0644664070b140e086c040310385500d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 517061474 1250 517060224 517060231
    0xb10080c0d060b15030a0b01020a03050f0d060b0c0f07080a05060112080c010609023703230c0d05160c0201050306010908030c01240b04031e05060f2d010509 69
    0x1c0781d1a0f05543c20169290a00010b04085945030285c403801c20003c00d00c201c8008403402815503000c2c103200e00100741c010381a40d0501d4000140203644605140c01e51019050660000d00311000204031040e055101085150820310b04c1e2080b1862141d50307684080d52420000f02c094459044500180300074075003221100400e5000d40ca44600c1c00c040c0724038843c00c5485035401600c07410303404144c01103002d03201d542c000c207030703080035180ea042ea0741c0c29200703003903082c160f1512100501d5950301c03100381c4000340404040d10380d080c0c15407880050702d01070456111540c006600520041d140000003141c60040e01c010640ec214182e5500304a40110f600648a507400541400d043c00200000010a41b00030001044080c85000012543c0c0664401c9101072001c3c503c400c81561541000a006451146050b94212030f0800b80290190840304002c075812600798501134554041c8000b000280c0171551801c03800346062190300d98148040307036109403000050202010b00c0c080c801c1c0040290b840d19411a680 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 517062724 1250 517061474 517061483
    0x201030605120604060605030d021b0d0507060906020d0503012402010f020d090c12151a09091515180c090d030804030f0f0801051210180b10080c0d 65
    0x40154076100020101140032044046560105080004000c6035006401c01404140c00400c00e0107141c04003c1c0d1103009070390000003402041c81080380107503503014801c1100c80e08003090340d0b010354071140002c003264054040c1602510407640990b03d06480303041100e040394070000c108104022505224888018151801011903417100f4143e003090b0744510041007240014800041c92640c10300d0131880400196200c1c070001c800602c1c800011401c85215a0580c401182c00051040c68007000386240c7c0e901c05c0c00c900c2e048008c41082085000c2c0c0002c03c180403511815415a9a540b500040000482403011082c0c00c25445102c4401c640411910160803c000d618440d09080034030011444a480e181025400141c9039010300080c0340e040100302c10500c03694500302e01040c4040c0000b41c0280418030995005039903000000e211800305020320300c1c61b059404824405c0300442c600b0010070401c3c0f4401a52544245d1000c45c07072045040c0c0c2d29804842041c0081c0403954100c40c100000000d20110545 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 517063974 1250 517062724 517062731
    0x50a0c0e06013e0a0302011b053c03400204060803030f1e01051f030905070f080c040b03070e0903070b0406020a0e01080f0414030c0a050a050c030303011a07020103 72
    0x3100310740d89803403521010560007040c0b61986810020309548e254198401d40c1906c21010211683d880303c100c911030010421583d800c0021002c220545020302c1c0f402d032200c1d52441e98000d00b9216107100940c000d04400074440e00c00e61400c52410308444681c00e030380190391080c41c16012801c448400340015180000c20009040390745406079400c640c804c03141d42d415200c0744010031203a102200740c5030313a0300c0c1c0014080002d40c1d0b043c003000c50032086501c2a503808010020b058240b41c0ca1098100c680001d034400141e9946a0741d40c0500e00c42d01802d4041e404041c0201180d038070031401d1a104035042d40d01d008000b400024507003003103d5a25a40503240418030701042140901080155802c9402544a0760006955002c1c003c00100000712000c0542d04120b5680240700076004d40840290b0419040f84444054140c1003040b5403851049008030340c1c546c050802428180000890040c112030f010300300356510b04034804205a2a07202c00d0041d42002584144d200b20344450b11005003c4041c410b05001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 517065224 1250 517063974 517064057
    0x1e07024b0a0e090118200d1209081c1d0303040e0f06130c020d080603031306111002161407050a03060509011a060f070507050d050a0c0e0601 62
    0x10200d0109400c0b0100c240d00346414002d00c01000d2240c280205c020b0b02404034514216501d034285000040c403010200400d41c02d0001499032030042a0310410780c040c00c8004181d001c0030300a802d21030310344a440e075240500d29005c20103000c0d101c0e400c410300b0f4084c4d07201066414440c880030b568241196045415100c10702002c180258021406400703010348032640340366407500d1402c0080022381040312420780c50821021440803070300003800c8400d42040342013107072081e0f5551002c80d20358010f280c2c440b02038a10f102400907e01d41c20040c240a00400e41d0180d45022100820354000c1e4880c80c8280e43c09400303080c0c0c1500219034038050241000a4000a4610495561000404241440d0001d40d40b99a95506001000300c0900c60045000d24003446008900c40210015125000d1500b0181d03429000050140c200f240c00d000540103404008c1100400c5861810129075546150700d0484800030f09a00116002e25507107181445640165102881c0d41d007240080c10b1030100318650940030031811070b1030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 517066474 1250 517065224 517065229
    0x140f0a20030f0d0c05130303050307210b030c0f090708090708070e070e010309080a0c0206041a130608010315111201061d0901030803060f01051e07024b 67
    0x1d081d40c1e090700030b280d40c40e1242c110b042001c41d8154090003007880000c20107414410020180c0c00210f0f030301410036617100c6d510024250b03000d400555044c10207403980c203181c2481c00700c65404488044420b03011034030a0208001408130040002101c1c0d60300000590010f010b030307481058102c1d40a6003000c29074000fa035440c201c0740e280940395081401d869001c10100510260301141000b4842001d180034880101a0b4a0b00c030003511984c0300e464100042c1348a42c005640f68641104c0c000c0030003400b101422942c1d0001c0c0c03da6500860b140c24210100c4e10000580035128031130b024141c0f0f4120400b0901200d0b015107480003040300f071004400008092140c80100b6044429050080c8010748801c1d0b4400e51039090801e51880440000d0712801410005101148501c810360764080400d442d85406c40c845400184c070306001c0c810701c00455400300130500303000520240150075414800e0310080c65a503d0949080551960320208030050f002090b800d03480040c1d001c1041c00c1c00c003d40032008940d2002e0001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 517067724 1250 517066474 517066477
    0x1a09150703022415041107050f061b0403080d02030411101101150812070f0f06090204050105040c0f1d1305010e060307031203111204060c140f0a2003 66
    0x4040c0c1c0960403e50058884405907002124041000c03200c4503214a00710303421803110003890384410b00603590384841809169010044a0400303070000304031003010b81d95680c4070f556440d040341c03251003007074443ca90401d4180ea43ea05031016251300085942c200310601c510360b0001d42001300181c405000724405051151105041913400d203200b6520011041c0c0074100c1c41c0e00b51a028008400f100038201800c0002040109030550032a035217604040c1d4a00d01424222240030b44003401424058040030440b080081c01e50008440a100b900c0038401d5030fa80e04204400c44606409003004510350101c0c2d507101d644914920061411806402c080403150342004c03810320764101b03000c49890b41d80e401c01030194400c070340610f5034031a0341200202001e5040d9030300c0c16440001691800c0605485508804040c14010151007035031044242c031031407500c0c040c24408050241054594003284101601c0180d94216104586a19040c10354951800e16200760072030350401900881ca100150f03400080203506010300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 517068974 1250 517067724 517067737
    0x7020604091a0307080a17071b090e03031e1902030106020f06130201090302060c12030a060608070338181e060102072105100c030f02041a0915 63
    0xd00002c6803082c5541926050300d240740024071a13400b011040120800000314201d4107a8800701c8a401c002000c180d00c515401040c10040c10340751420f4562036014840c0c004030045034441d2100340050076000c5243c82d102c0c801500c2c8440c2c42c0820f40040c3e42021500c40b8540c0d00401d01e550300d00b41100c801a080002c80e0403c0e0016401038000700210f141d03401041010b6604038951029183e100d540660000c0d002040e1440020f000d1380c0e001c50480c0700e00c42e09010701080710070480383c1c1590f80d140803a2200300a244900a00d000700b507240c808108198403a01c0b03010003005d04010200910001c1910070452207008280c2c0c000b40da000c2020000c11501c403021144806d200d407101403c620304015103c02c040b0344c808100342e110300e0305110400800341c0c0e001401604a401580307044822a5448081100d841700c4c00e540a0101d100f00083c0301150300495001c3e5074891043c1c0da00f0030000414000d4402a40300d82d02c611030030101c400180281e80d201c0c4000500852000405149034407584207032100c4560000e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 517070224 1250 517068974 517068989
    0x8010b0a200f070f0512070519150507020a080303072012040f030b0106140d0b120a120306080109021305061804050303060406060c03080403031d071719080406030f0207020604 77
    0x3108100000f0034551202c07006850101c1b14071140c6246015101d64480540c864140b16415100c0d0032140058540c19507005803200455032401011090030141095002040403805800004070001d96000d001c001e580c0103030050355031031441c18030304240304441250050b401c0e01c50f13010b42c044899240001e50014002400200c003030003820352642c200542e5005050f0701c8101071181c2d140300e04451240c00821100030001c040c000092003282880460041403094080380b40c02d100f01c230b6807801481044040f540103a1115a02401142c1c1c030340d8851401d84240540083d041800c0700c0390340c14002d40f55044158030410240181c80d0300a05000784840880040d102600c00d030b0000001e00c901403c1900800c00a840f040c20704454030800c0d030fa40203041501c020000b908050750743c8500e40891a800250011410a04d0308442004d520351030400c5100c0314030031280030b1511900c804481e210480214a0080d65040340c401420071380ba1800039030140c41c1441c102c961342e55003040710200503a04d031000b410180400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 517071474 1250 517070224 517070233
    0x6011e090f060e03010606050c0a1b0914100f0810021804050403050a120b091303120509070503150c0307050a02030405030a06021c09020a05010f050c07060f02060708010b0a200f 78
    0x70710050500310303030b80b903002034003003120420103840302201c001100011305034013040d00400c001e0322240700e2034a01070bc0e40091303100c5d0341403d0840038100040408280516070200000000540e02c7c022510041250303c280304d52a0004080100c41052a034050032420010420b041c2c40740400100080880740c044804401080021070002902540700d0445000761503100030030044601c1d13241c00200e84c410018800c1241c24400c080003801c00d88200c41c055440b0743c0c0204c092003107040100005848505502882d0702902c230701c1c5400c504032490115050701032011044401e245880d4114100c489510915a2506600c0f04000004142c5c40c20010034103180d0165200580f1042203102d174040041403000d105001c1c6050440b542e0240e40d40c62010411a1002d08044405000a903c00d440b9401144026a50740c014114005641c0d900110b000f031000e10b05600b0b40745941d40c1c26170103071203d060a015500540206200070b00300b01d40500601544054055501d080300d0150100d0584ac00710381780c9a20642d03401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 517072724 1250 517071474 517071497
    0x120f0c0503041401020a050f0c0109060c030e0111041d1806072003090a06030515060301150306080d050403020f1507030905030c2b03090305150603100506011e090f06 73
    0xd1012107840090f880000d41c64180b085038018118046c1e00003080c115500051403c07a00c103002d5221b0304c5001d40c060400d00405411b484050014036100c184107c0550a058802000420090448040d41c40c9401c80c440c0c3e4500d03082008150450040010301070140544501c2400f68003089000e00c100c000c2d564032a101c00500181e501e681241d0100740229900a10400b05030f0340d00c0400703c8043d15194600080c4540d14082094440c660720445079030044e40000020401000a002c81e1281241e2502c2c28400250390341c50b03295032094503159130702c00110140014001072518074600c1c008008005c0102401c801c00440020307a40d40a20002c402040780c3c41e1003003045080c140800391040030102d5005030142c01c1c2c440006074811588040b100210f0f4082840d5081600604c0c181001d140c02004407000300965600038054544141c0e41c081c0309200740342e4103c0001c06640901391080300181e4400350750f030000c1c2407446002007070b4042407400e12480d9140440ca07030000e049110010070203562180c14146 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 517073974 1250 517072724 517072733
    0x3051e09120d18030b041b1505180105030615070218070e04060602070602030d0b030f0d120b19050904050a050d03090c2c0a0608060a0209010e0a030b0601120f0c050304 74
    0x40c0d01c1c80844202070083c481000420680b60500380d0050704108100340c0302d81c0c44418140d441c07025400c2010450421401c1c075612940c0306024024196044020000348106040103540c2400200c4030313107500038400b00d043c1e0690082d010103801c03060302c003508a2820b5801400d86122421040318644002401305054040c1850f041c0170302d0000700407600181c5801c40c18081d00a46030b100300c031041560340e5281c00700f00c2c102c0d840410010301480d0102043d181da0f030f00719200003001c40d0102e500300764196003040c194000d2441c18400820034480e0180070f441100b4582030620502d050002c105803000d001d01070a50000c1242840100c20f07054941d40c00003609403151412507290f58241e00408110507040642400001c0442e2480c50702c01800b000c0003081c0d40d1784000c100007500316500100303494020355086c00455130440d0040c20030518242c907042009003102c01445804640e0748405007500329420b01150940d4016610110041c0e1001404120031894141c04019a01d1038504200000c200100700300501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 517075224 1250 517073974 517073987
    0x18180b0405010602061f030507030813090501120f030216032607020d0f020604180b010f031505210f03040e0702060106081627050a0503030703051e09120d 68
    0x4031410003681d414420020360760000107150000c00c5022800c02c01d1202810b00c112002550320504480d03100d51a442c0c02c030501d4000003042c1c6141c0d14066004078148515004050580359403c482030b60300a406d0312031010040300d24800745d040d4020003001046960340788207400003440c00b58481160151044000d60240583c5000c080c010003402e208840040c2e17520316114900c240c01020300307452010395000180ea5886150f1140c05016034016141e8403400c001e8108004004007621880c2034040401c20580503107540700c00c00c0800841c8040d040c4202c1c58a10480c002440b19040c03058880250038010502d41005046204850b604c0424104003503650003440c60340c450b4491003e012994580b03180580341500280041c07103511403441400d403a1600c20ba1800300c800c8c2118803680d51450070311000d90410401c0b0b0150034090302c0c00da2808200350400200300c82070716515658291a0510340204101c0301c4e0021500204c400c40100205111540c1d0712000006e00c20404014107400d01100c18050f000c1e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 517076474 1250 517075224 517075241
    0x13050c010e0a09020a030b0303181c020d0605100515030f010f0803030c03091f050402030d030515011d120d080a0c0c1103010f06080f10050121031818 66
    0x402840e03407201c2409403140340380307031040381c1c0324810141c3c0307446220320190040c1a01481c0700c0e0700b51202042d00d44220280f403068030a642c41c2a10400310040300c03282d004a0001d03900c0c40c080e41001d01c68080f50005803503030f800b8a60000c0286001d207a240e8581c80001d002c1c0c01a4800a22038550100622040e040c0c40c000b01e80c01030429560370300f00c0c2d0b450720001d15240e0000a201122001c00440020032060040c0b108038180700645e410b90101c00900010301005020541d01603000780f250b14a0031903124080e1144a002c0c0700304810076144082c050004413070140e8000700c5004100241007403540b0350344581c04041605085030000d001c03850803e2000802030100180300028960070200d805800c0d0350050443c80740942c01407500905100042c001c24090150001112a01864481d0014640402141c2007464050243c2980c40018240c00c1a90035a80c0030b00aa1101d0300e08000440c80a041f134040d039000a03442401c000c4c20301e6000d0319000500c9050f42c4d012440040d000503e004418080d482480c05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 517077724 1250 517076474 517076477
    0x304150908030a0e0607060f050a09031d1c02030a150b01110102070c03080a17100501110705031b180a1b021c1202070f080c010b0a150c0c0b0313050c01 67
    0x203080c0c0d40c04008009881c842d0a050140d1000074100c030500409412014200d10148c0d018030990030030003800c80082c0024023080d00041c18000581e5070328526418031100441008000e40e600c04003010003191a00d4402c04100d034584961400c000024000c05940c40050030055800540caa220f0000035014108900d880d40b0b007a44104546400941000b0401c0207483d040540c8075190700503404165400f1203104000c0725902c40303400c104054140c030f03428582c0907610281c0c1c54000707010321010055030721100c50080301d9040d00300180d0800100c4da066006249858002c0002950104410b00c20040b103405660b01a842e544441801c0c004005021644008502c03520041c0110a00b1640f00c049160207200410b040110307141c80c1038944180c640694201542003210092544c0e414644050341c4d5000d2048501d155003410002110741c40c1018058003121603820100c504010b40110031944160b040384203c8403240c001300045120003555000d14403440380e001c0000310100c0c260401910700359024480c0c4d030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 517078974 1250 517077724 517077727
    0x2d0f0906010b0403060b01050c0312150a0803041419080c010f052110080f0109060f09050304152c01110c061e0403020405070c0b0609060d020120030415090803 70
    0x440c01c0810b04507021260802800100e03485910012200c41c0b00700d54403403640e071002041c1c4a94400c0061003050041c06500a05002d101c545018070010301c1e003901c160b030120f0f04140020070404d00c030210030310441c00e00140f030000d9901941c940c9400d0000503400c0366219603c0304507444078658010507902403142035824000d00b0304d403d024180c0401c05038102c64140b901d8442e004240b000b00c498220402800720a000d1700e1402c01c201440070b001340119082650402e00f450703410701d4043c0e5948150b000a507005009985458101385080c00141d10320352800d01000460064400c035025841c403404c070350200045c4009004500800010400104103101c130700b1907000101822400c1ea40c11085802d61800d1201d0040e400c5003865107900c00d40665400603401909000400c003d182c0e20001840c40300c1d100310f0300c110581d124035090252685044603555000850b50701003801541c014900f402ca0310640000201664401400c5c850843c0c00651004005e607540c034121140440d080180000609020750055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 517080224 1250 517078974 517078979
    0x150e070806040510091d032110030201091214030301060806030c09162f010203100f030c030303540c090519091b0501031a0402032d0f090601 62
    0x10000013441d2081c4c6249a507900002c0f45105055655800e0f450060004d0302d0721207000d00e0302540011680b4500040c0c6103125000201084548805001929010b0b500e4640c0642011018080c400e42c100c005d4802c2d00120031100c44004003080150f02034a056980c0c2c00703c60800505161400b281e52061314442e1124200f00b20003600180030329170010320140390800d20640104040c0c0c01e4413170600c03000100d04003c0c03541814030040540045009000d0310300f410207150303030300c4001c20095101800010045014924200702280c841d1700140f45541c4459007980341e0003c942a0400c9442000651751718461402410b06c2032800110812000344400074404420300200796a074000d503004501a0019090f038540c041000f205400d040f203403244a08280800a16156043c00071b208117001c030328402c00140300e11000c42c0c254801e005a000d00e0071400500c040c000640c0c400c00020b90401480218011a406c00030340112070021004100300b031902c450002d0317a0a01c01c244032040440207080b030419a101d03c004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 517081474 1250 517080224 517080241
    0xc12030e151306020c010c0e060c060106030f0608030324061204020d0c15020705091803090f13060308090a091b08040507050a03140105070206071d04150e0708060405 73
    0x407103011821441c0e495400b9034503042c0c1c1154030104400c01405040c408152144003c40c158450f070605001502c2e160b8942c0c0500c020811a84220b0b000d03842250016401000301c0c80c0640c00c081380150300309801265254441e0003217481c540048a41d001226610440314003640403404400c1240c4000b41c61981c98a221449010968032024000900034484105d4200a1000312a07103080034128081c0c0002c0c1e4500e0703001000f561948180241441400ba12000c40c0d0b407440040146070b07514117940b02031402c1042c0340d4200004880700b82c52480d04088200381ca03407000b9405100f4000514480c80d849910780d01d9480a000c99140c0c00e80020b4800351800d056040350715201180b0490080c000c0c500546030f0381d12480d2090410010f03501441c1c1082c2001404020443c40c2c0c40541900405800200919520b080080380c0c0c5820643c5c040000c00d032440007402c03410406503c000500d80e130140011801e910245010845000280d0265141c03c042ca4180724005601c00560703508100105c505210303d00b01a4203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 517082724 1250 517081474 517081483
    0x302012a050f1c020a020a0b0609070f120e0d05040306060e04080301030f0609050102040e06100c080405010c03020c03100c080c0a0e1e10050a09170d0503090a060207030c12030e 78
    0x140e42c0c140500451200340d143c410340381480c000aa0f252080d5211020b490003c0c4d5a080030a030211059182040044c91a0600c00c80c4c3c9031080303c807952554056100070400342c840e101120000982692501c600010300c000c201b007606181492552031a648901c1d5003800421141c041d0400c01d80451220107110101f4184030030b0b2419641c001d04008074503030540c5003080c020040b51400600300d50001c5000118503150395205840b400b803d0f907a00941002c4400100c500c0303511031000900a1a09101c141700da544964001c009140c4240121035503810300c42c000a140840c102e8072008280d413903004001035660701c0407113103800c004070f054140c3c1828081d0a000d01808491030758940200c80500c00f190807007a03100c9208881c1c0710081c0940c500e040c602c4100400d01d910408080e80803849440c00001c45240b24015920040c0703185014000c403002c80030048569030301c0900000b10700e02c00d103243d80e80030442510050415600c2a115507450703a80350714001400e03404d02d046030000d040c030b4420201c044460204 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 517083974 1250 517082724 517082737
    0x702210a03021b010c0306090b0405100603020d061706060109061818020f0a1812150902030a020315070201110301031a0c0d061205010509031c15030b040302012a05 72
    0x1c0140e00e96545512031400d03203141503e01c07203207903003000661100c10780c05900c6241030b1110f04109103c0b40f10960b00340408c9e10070648031004160907066003008064801c0e405480c5075180316401082d900d035102450304e8612040030151a103a00100c05010b4a5a0000c0000c0e00802c5282419680100e0449000c00080890b22400f03408103d00c4203d83c60510380e076070460b08003e102c0064140c550b4140d4034020800180c2c1e125446900c81441400304508008400340b40d40307a070713000b103c01001002c0400c00101521003024120382503c199084072b00142d60600050441c040d04409a03601450015802401d49942000c6000504403c1005001081c03d2046004240c0c400c030000c09503030f444e43d03e0b502403548100e003035107a1171b5460000301041400740e4465460700b4074040c0c0001e00103078581c420281c0d240e12403081c1c40119090a44060300c070030443c0d5008042d40c91a06106050146d55a489204030003034225400c90050750b40712a200d10043d40c5040e8041078031224058440482200e1401600c0b070310079103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 517085224 1250 517083974 517083977
    0x123a0f0c060204030c06050c0d03180f02060403021c062a0507210f11070e0402090c0c0a030519020f0d0e0303090d0303060515131703070b0108060702210a 68
    0x144025041c80041d8048800559201d200642402d42d140300082480e04a060180010701030441ca00003098130034082e00911040300c001d00720950000c0d503070350a04001c22003c02c903002070381070100002580d19409003080f201c280e0144030240510504d002c02c111448120142c0c0e0780d840002039140d058a0310914140e03800c0a03410159510401403c003103204082184000780d52100b03e29001c00e0071944180b00104917034030f0b074442100c1e8000340c9202540310001e0740660007805001c5400031340545080c220300c40e00004c2d1200503d01d80384001040740e082080b9a01b003a0013107a030024207418142402c00d01c42400c0384d02440a040c01c0080c0b409500d4403075020080e4041009219602507000e991306008030b9080c1100100000c03016082071170090050040d078410715104d00e50564692403081d406500300c50440d940c0b040204250340c1040416131550450308a0890140710a01003100007411104415010b458140d00030031146c070301490000c0c07800c00d40400c0f041c00001090b001c4020362405005032034840840703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 517086330 1106 517085224 517085237
    0x1006030e0309060901030c090f0e15030c100513050307091a1c080322110321161b06050c0d030c020318123a0f 49
    0x1400b500c20381004003004010440e41c843d910082c400d09107400c21100c555240c12001e8140782c002d0704550b0303454a840d07041c4464072107920301801c0e52440440c001c00d904150300012503840000c0071044001d115000c24885403004906840c2c1c005801d020b4100e5131125558141e903005064040c1030301406800a060211450800b901d0098018011070400c40e90302c0c500d5621f00c0700c2c691000300808a4504d52401841c0c3c01610000414400790042d22a0078400707030180100350170010400760841412104503007203203400084c2015166100001c000410899005003071220100785500046510038100010200b002900f000140c2800e96912007240e0f02a61207280139402c4490740000790006d42d206100741c0600f402c00001110300740130083c082e000a04880000289001034640071000041b054210200c002c1c2031019168580a0b9038422003440c8406c1c92201800c611150070400f01013001 = true := by decide +kernel

theorem cover : BRFrame.Cov 516906474 517086330 := by
  have h0 := BRFrame.cov_init 516906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 516906474 ≤ n) (h2 : n < 517086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
