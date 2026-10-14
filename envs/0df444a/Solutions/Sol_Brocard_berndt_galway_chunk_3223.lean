-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3223
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:01:39.001172+00:00
-- url     : https://prove2.me/submissions/9d6805c2-63d5-4014-947e-c32c14dfc41f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 579496402 ≤ n < 579676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 579497652 1250 579496402 579496427
    0x10f030203090705040e03030708070c0b040b062b111009090e01060512070311060405010815060c070806180609060a150e010627080a03050c011b0906030509010606 72
    0x1809030301c0b91140c00c01c1e1410300b00e659010561191400008010860021025511480c015124101903a903026820344010100308001403038104074000040020791408030180e00306501030045a03640b400c40e40c0580da02c071012549141c2404250707000c001003003500e0400b906440702c29220514040c1d0584000b41034801140203500340c04e038a9251000b4050401d510403001040020001203c024143d02d21544842850000703039802c141085003a0f8a9003040b804031400c03900180d5030200303103a49080d00ca0420110121805a02c500200704c1420071140c2008000007402d00b900142026040c00c10903000340411045450f21140c01c07040400c807503070324003054240d8000d040312008600040052102c82c20000305401c81c0e0074680d483d1700045500703984400c0c65454052400c1444104034000c001140160011b4843d6141540c40800000002403068001d0f1842c1c541200c00411020030303661403070005c224080c01d03200016034005c100304441caa040c000d96410448002c0200300440c00d156000300041003402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 579498902 1250 579497652 579497657
    0x106030b0f0f030c18010e0a0911040b0d05030a110c030d0219050a050610030302010b040b0906060705150a0b10110d03020304560f0601120519061202010f 68
    0x521090ba81e84050000301da004200602d049000d003000900f0540406085c050183c0810b140000100c17076510910921012030b411503040500a10401c040001803d025007005401c01688081140050000c2020f08080005d9803203900403024a03c1c0260701e84001901007a05c240d104a843d01141c41c0c010403201c1801c020503080400d9080d0f41d007400c6e482c0c44d002541c004c0c028441c59003001200e0441480780c13002c0e01e01c02e50090048400e00002c04c8140c8141c01c1c03c003680141000c0200300c0910780f40f4018100c00303200e6000e83e2211211b41c102c0f1400b011040310084400c079101c1607800c20500c3c1003c44d0f440040121305000904452845402c2d540d0035194001e88140341d4004007080500401c004010340c41911140c0c425880449942240402c0d480c1c0d5071201c0d912410010364201c65084541448600e1140208141c0142d40d03007a25421254800f41c06141130042a400b0030b1070b95900c81c041c0d64443e084100340010b0250f1001d02101c103c410700e43c0a0002842c20b4441e0f0401030f0703840141c541c0e9824592 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 579500152 1250 579498902 579498919
    0x910050f040e040812070e120f0c131d01050601140703020c040209010c050d090321050f0a0302041d090709061412010b0d0c03060b010c020307150203040306230106030b0f 75
    0x2894803626505c10500da000c00c0010724410031035550b60096030181241c60a0354455044441c900109990b11040c0801e25666001104004205d0070101e0200d0311110020901045090348516400354085216000b8034441e5164820801596003002e8000a1955065080361a040701501e00a490700c05055040e0321644d00004d03040075030f07849a403402d6910b0303800c8402c2d0b504480c0c00355405008102c42c2d100c00c40343e445c6003500014400f050044201c486a100740c48092500c100c503005580300303074401200581490707800e000128186003030b04c5120051391404580400700d403d044480d02d140c16425400360b02c100b4200070041c85003510001011420340400e03642c080b0349032070451410303015000f494207640d00078200445100600c0305c10035042e81101c0c0140c1c010040b46460f0f02c01100c5101c1041d001941641c04154208100280286500360744401403040c2c070700b4961aa5510000c0c1d5603000700c1e190702d0782285007144106842082006004001c942070801010b111030000c0350160501001c7e591050492 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 579501402 1250 579500152 579500161
    0x702060d0608010b0102152202060403120f09090501060f0813120201090212060106020a0305181c0201030c021605060d09060f020403050607091217070c0b0910050f040e 74
    0x820040d1012040300020a120560700c1d040041d0080c0150403c4c1e500501c90040030501580000b42006d0103800c2c0042d241000c0a40c43c42c444c160060076020803a0030000c1000000046490041d039406a4000390350b9180641c104400024948a2a5040695401e01d0a0b004020103504882c0c20358613044a820040b00560740c000400d02580c0d10b110002e400013881d4040c22000550650140341d015108803140800558540851681c4402c24011440542d2020b150303000481e000d031001d81900008511a403000c08255004144401e00c0380c1c048588440b10845907808540e05401401034440756840103012000359034a1040c501c03540d5100e26401500006850000702490340c1060811a030080c1c4140040180b5102c2c401c001e61041c4400c3c1c1d5240a40e8011452951141c1030600c1180c8000454039020440303611604031101d1020b030303045a002d5042103d007002071001e01c51500108201503d0320b449413024424010312880041c3c0c104c08000c410010b607040d03402c1c00c000342c90640f050001c104242d071b0f54 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 579502652 1250 579501402 579501409
    0x20f0705010c0201050c070603230c0d0b03071205030324030604170909130b090316030f03061502210a0c060902030a020901090b0a0b07021f021c1d0a03170702 70
    0xa13002c10306d2013900440f07a01281090700740e0803c041d04600d10704c88650a20803075030300030071001c1e0a03103040800c0305080080302003416041d0003100c180d080060607192040e039105101d0110303c24120b82100c43c1d07040413081250240c00140c1092240381210300c04c0d04621880e8000030f860b03900042000380b02070200804d01c921058800e003a41c02d03c05000e840000203040000d4401c040824100d01110740e0840300e400503204410100541c0c1c0e0400c00254041b4007102e1301e94044c1d490000b034a820100301969842c00003640c19507030b0007607042925550040c00104030385c4180502400ca40441c5a03840883c10401c1020841e070140403540120b40110000401e01c100344006400c005d00c00201a500c80043c0740003052030381c1c40b6030141104940071102228201d680d0070840780c29014030034010f03500c800c01d5201610880b0018041001101da5881900e504502d00c4610101071141c80010b04001400c0e4006041030340c4155042c401e000008072800e440c0c1c24595510140b910343e010241c6d1520101c0030889004646 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 579503902 1250 579502652 579502657
    0xc0a1d100b1b0d050c1e1615031b0203070f060b0d050d03061a03190b060a1d0d2102030c031b163804090615020f0705010c020105 57
    0x101c0c00c1071040d0380e180240316040c1030305641880b00360640200b00c03401000d140a1421078a9100012000e0142c01004c4802c66503c0041c00088000781d0040d8505481c81000c001e116402034125040c2a4090444801c8003e0880e1419903050708a5814240f4002041c1c0d0004180e911a680c0013050822020b0130b0301c0c085014010030f843c1c0c2500300e500d816000c0208040420160207142d0381d40d81c100251a991000d281c005a000020001703c0182000499042c41c0903840c0da860303060465202140c5102c5a002195066000d03810100001d400b000303c40031942a012520740c0c00703010481d003c40d0b00c1651500d03401c41e01900d0100701840b645030f01840016540c001d100351202004e1201c2a07940b144c42d0803500e0048140d54008900c0c080c00362004030841001ca510304a000d0354001ca00405645441314150030045500500c010b902c004941089181c1804050041c00903090071000814114540344c140c00c800380c42000c58030255000f038500a0f07042c400000d00d00d002c449091034400d0b101c03101d5000507101071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 579505152 1250 579503902 579503909
    0x61a1e060903100504052401120201030c05160803220218090a1212060602030c070b0f0d0e030405010201050601020a260d1409060606130e07031d0f0c0a1d10 69
    0x80c04c04d000c1005020001c205008109010b05114a0314114034010390300780303082401102c1c00d100f0582920005544079520400783c1214a0800c2c51400247e00401e02078040455811500640c0000400c12110707001d1842194198107050701c1c001d600419400140001003c0c905085412502000610030a004000e00840c407134110165007010140d0480003440c42c0c40c2c1c00405403851741005400101e01c4e1000003154810001d040103801014240422192a5800300410f044280418401a42d0841c1184035a42c2107102d00d00055a4940c9483e0001e400e481c8003c15072410b6401183c60580031920711409081d003000740600e0601081c440b03602501c031074000c0c038035012207840c5001f101350b206041e00c0380a24041d00321007040358a0b9070f032a88108104e510600036642d00100749014200405440740700391640001d960b080100d500071103a0030700b003442d00202c8003003145940301109603100c4404c2030001ca1194081136800312043c1d42000c00106043e52419104c049002d0a0700c00070340401c1d480c20040018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 579506402 1250 579505152 579505183
    0x40f05190807030318030f031a030316120318060b060403060905010b030609070b040e0903040816180b0a1206140106020d09082e090609061a1e060903 66
    0x410050070640c826070445801200031a00c2c1103003190006a07a1040403811550640e1101340c4440f440c44120050040d500704104092012585c0301525a0706102903e0722a800b10841c0c501b6074480d003010a5200703000200e40050601c0c18041c8542c14190002035080190010408920300700c070703540400c403a44519480549070750f180c524214104007064005004600c0300710101c80c1142c81c3c80c2e02280d2038181a01c038403581c40c10200070401c5042c00400c241c2d42e01c94050300a40382443d03501c004090030304490302006611600c104009002002e044002e014005a92220400c522006400802c041c3c4000c1d01806d4541102e01d5400000c014a40e0084103203464020031680c3d484d42c2d04c0700d0207035492000c248040041900101d0110b5250000500c4040032641000074072a13400d990800200009035080b00d6807021a15005001d02081550140c400d505200f0200010f07102912054402640b034640d0345144030b04d0440983d807005284513203010030810310485800c0c0c2e5a40b40940000d24101c0101103d003003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 579507652 1250 579506402 579506443
    0x42105060109050421021c09030203030403080c1002040b0d0506220e0114060604050d0302120703021c020a0f080d09060609241a13091b0912020603040f05 68
    0x403030a100340c1000307019510840e1302d6240b0510790f80c01038030f0403443c402280005034088207504010348000302c400e407c0e42005003070581c9516182d8010a0665206030003e540858002840c00300d42c1d5802c01003a109400b10900031402c09040410440303c0d07200c0e160405c240d00d512030021500b656140c08003031352080010000b03030103254610110580584400b6001383c509500c0e006403100c001d2498290300b84500360044c84145814200000c002c1400d04a60302a801c42c0300b002900e1000d42c24410003051880d00a800812134500c3c1c00d002244040c8108660308215045840d01c400095a00001c10080c40d41c8400d10315200d07920014040c0040081c1000500068109100016091280d80c0512034001e42a6415640c00340c0650241f141000c03284214440d03036501c14000300e820b00440024117044c52452141c1e00c071a076070700d000c02000c3d14509104040030185002d0080c1c03080b600071644500030051507100101e0701125800140c480d0000800103400e41003540143c1007004003d010102c0c51050360361039000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 579508902 1250 579507652 579507659
    0x2090d0c05120c180a0b120105040c050a0312030c230c2107030f0309121710140609030304150504090506060f042c1504050c0f0421050601 61
    0x4a1100d00c0c0c4111402a210b66006410084001c1500c0e2841030000c1e0a00324804140f5400e901403d10080c51400c1e0356564118100c0c0c0e6a6414040e07490070b903240c01c00829142454107101d0314084169101700c0c810a0038010802c005081d11002c803001510b5810f000503080c803000800e40340060325100d454150400c0f40f0014440707900000160556008200c102e41c9403030b01d01c040c10000e030782c81000017082c40c08082c09500002403080b07040308507060180c076001c2900b0b803056490b40c020700303010002000800c5105c59141c41884845500301d0307000300710101e0300701e819260001005104149803411401000d0000c2d4238036841e107040007100c0090092021a010300048030750002c1190304903028681c616414007010032040e290400a403040c0040001541c0d18040c079121038400c0c94010103030b0044c00c4511800c80c920b220b5000301c0c05035201d0300c25449200c0003160001d0800c4211000203203444211081402092a004d00c148240d40540b85500369080850901000e2091389010081004003035204800010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 579510152 1250 579508902 579508913
    0x120608070609030605010e0403020c1c1e0311010b060a031508030f120901021213060914060a0b06180d05030d0501090207022722020306041407060f050a1202090d 71
    0x10307080f00d000d02c504124603601c980d42d01c0014142910064016840000703409800d1610300b10580510420340405a21000c240d6607510304100c1c00c001c024401ca0044211500740350308a0a0000000025002003003a502c107100041d642e40036100c1d90108040c0c0e02c0b503122910380c1e510004e0401074031600040b2901d842d6460342802095107c0c0c9060803501014002281521005000f96107885804002030700c13580d910241c1d00c01c1c1d22151000103072521912005e814001c645070080290300c0346242809000c2916020741081701341c50000074010700a50003040842d80c581c1d0955080514000308465811441c452414200d10358050b00b5a200b80580c03410000081200710350740206112031007620903403580310388000541072845a048007044003030240030001b00b008071016103000c0209445441456207491070f40101e86000c00c101c4d41192514440b0007480f004020410804004041d80d14100701418104a001400707402a495014103000100003c040105402d80644c2d050f140040c0c01103002c4001400e01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 579511402 1250 579510152 579510167
    0x204020f0307030b01180b2b090506130c14010311040806010e0703020705100e0321100e04120e010c02150304060f0b0312160c0e341206080706 63
    0xa25010034941402083c295003e0390740c410009101d04801c2c0c06c003910b089040ca0161340320329407543c4661a103d4443c500305d038906101d00c820f801040d80c00140c0761103615105180c65805414154109000c01c1044001028564140142c4003000c6840c012480c84200607800741404031a5100328902c04038000c5040c0c500001d9540c1222110082c507000c40d100ca40c003c0c3c00701d01c5110b1001c1e156400c207065180404000781c0008140711414000c0301d103003803410810f150540340d8000940c0750b8040048140078014080c604000e020308500c501102013420683d40d11404e485150300840113104c40e0145003016a8007407000d4006c00e0340c014185480841a000444280d60b1044400b1100c2504d481402c8850502d030348a001e1340000d001e402800c5000d50712132103070110380105001c00c10300180c03240058002240b0303c910078010445814001d465042c8034404c40c0b94504c0c0c4140b8111203010710046040200540014060300c0907035414003510202100e10020054650740d00415198420b250b000a5072a80c49400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 579512652 1250 579511402 579511411
    0xa030b04060614181305070b09091006230d022110080c010509040e07080f07090b06040302040b271501020601141519050a1416140106030204020f03 65
    0x410030009031903445100b58590420703080d0b13800100ca10155004290a402e90031340101c0c09614000220b880d0f5952549010626084084d2000300071681c10524208180c400c0e400050103014204e0721418420003c00b00342405440e004214a000600c5200310307910400c40d00503a1040b0801d5540e00d201038a92040c0040002c6812207160300c007030025100318002e4400c2c0e004c0d140701c000030340044c038641f5004441c0c84d000171400d9581f00f5907480800c1c400b20310030442c0c8401070810802404101d40305d00607460070300710b25601c000220750821030f8845256036200c04560980f581201c0001e00001e0400c0070400003600b02c21400b100c03207503840c48007513007001c0020a544503032040e401d603500c0146001c0c01241c46107030030b01c208205000c40981140c0540392803070344d1414400d1407840041c10604061520181e00d00c5a0a0030408035100003100007500e035004544015441200c5561441d2043d404688030405054220242041450385e00302000380a00390000b00c01180c0041c415900c1c0c0001c44602c1c075290b8016078 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 579513902 1250 579512652 579512663
    0x90d0f081e070b0c0d140108210c030307080403030b0913110406060816050c240a020c0c0f1309110307050306010506191b05100f110a050c0c0a030b04 66
    0x900e0070114512080440342c840390f01550002c190f407035032004500590440551242d0303940c0c40c3d0740c444440406401d0014024100c0070010079000b02c0f0b006c0e5100b1025080c180881074507508000d000b00d11b1100108070707600008980780520b51641d46003011001400c2d00348641e944401100709100950007490305e90680c0c01e000e000381d808100d80100c200000c60301075101d04c40c04110040005070320703070200d0b07050285006014100f00e807402c216070607020300b8600e40b4a00c10004000e0318500b02a108110300009901c81c00c0c00600b1071505a100c20019a101194507185100700c0020203150940c1d00c40b0034400f040300102e05800c0c0f00e070b4101c1c1e2031320702c602886c507001c0c0f5402440b58100000d414900040c0d26070407100c010302254074000101001c01c0164611030108024810b0740100c0b00b1404500102003400c0f640180040c003124a800b004510640700346110342200c0c0350030b040d190320f8000404003c580c031040311401c0c8195100d40041102d0f0038440420b404581c4201c10303520000601c000c040e02c0c5072142d8400d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 579515152 1250 579513902 579513937
    0x160608151e1509030c04020304021c0803150f01080f0709090f1d010b15160506071106070c020105190908060106020c0909120304020f0414070e010207060c17090d0f08 73
    0x41c282c40414000c2c1d0a40b540e040d4070000d00c101c410300b4180d000b0341e041400a1302084407001c10501c1080040a000c8084076204000010000101d50543c220485241c0c116200d085941000c4002040c0300d0b0083d004126080c00c420100342250701a0440714001c02645a05114141450341081c0003486142041032014001902030300a11b10180320706402c00100900001c0601190342803203802e034110444841030503a0441c84e01d00815000c00004d80b2440381c9584262254088813844c5050a102416003014009090313070103c01070780c0043c107582c0325400c1c6070340701548502100002c544070100c582c041c4015015010010030b1090340072503960001682600c6001d565268007913480e035102c00603100507140c04810300224005151003900141040c10050010074030480c20781684882c05000e0350b2a80110341402c440140658050003404000c190030b05008420202d0f5499401c050348894480c2104000000381e44d00c1240e50f03040c072002007190400b0100c0b0044011f40b4040c0d8560780301100320000000e15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 579516402 1250 579515152 579515179
    0x70203010528050124050f0c0606010e040c09031421070605090d050708090a080105070903020f010c03020a080d09050d020d140f070312020d0f0207110102160608151e 73
    0x601841e070403130310610040c03620600c6031903130344500300840c06846007001b07020030194880f000c40e4406020188108006002c00f828040000f501032680c5c0043c03140114241444000d1b0355030401a40012283c002d00d40c642a40c02c0508044c1c1001030540009006031a081580941b000e1554050701d400e03840f80d1020000c0f5220b0a900c0c40d602c41450640d0310000e0010013403800040d40748030140c115040c01402440286880700341e842d09407841114454000790007824204103518090b007901210600c282001c902055603520020f4a4402841c3e0140500d04002859044a285c99114005251300302007a60a510030798000203490712680120f450001e0102845500400c1c815012a401c50580c01708003071420b082a0340549203445094100e840b855400c0c0710000d01c01c503241c080d40040c4000d01c280103035100041e141c08206c0c54050b0060038110741c00002111901401c0c00346890540c1c80324109a2100d81d9098444031110410000907600450b0f40e0f40d925407004031703c204d4030652400c226020031810a1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 579517652 1250 579516402 579516481
    0x111030705011b0228060603060e06060118050109050904050a0c06080403180b0306012712200904020d06020d0213060813030f0311192a02030604110301020702030105 73
    0x69a00e5003401700c104402c040580c4255030040050b240e4410400861041d542c0e413070750340448908903440c01c0300350009410854103680c00780c00c0085198201c030700c4411550170300000030802800b9008503070281d0240404241886001c00500440c0d0f0b070f021109240d25030311254010038a0000381c8044004c102c04114043c89070b1b000d409010182c800184400c1c1c10b55a50f00011506091008001c5402103c03080401c0d4003890301ea41c890014114410181c10205c000b40392812582e60a42c05200043c0d00703130001d04030180d440c28a07030354202c0d4044411071403503a25418650000c0c4240d0104c0300b02c8034800504420b02007091a16401210440e07120b50341199114010200d00e00e50400c00140000d01714060030034498040d0b407020304181041006241050340c6151550407100c1e0318a902d90109007501c00300c88071541480c0042c80580702e6074188040321062980440d68850300035000034a10b03a280c000841c40c2c2e840c04d40c1511201c9400500900040c18403d80603249840d148035815400f40c00095203519490 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 579518902 1250 579517652 579517663
    0x1a0a02070b150d1a0106140306030d050705030f0304030801420c0c26071a0702010e0d0c08010f0207030519090803030f160c0b040b060111030705011b02 67
    0x94018055024036590b554501c03824044601c0c06903402401d014002d800b04044000c1c942c5410407410700303109554142030015055046c41c10384100b00c15010003c0200645010400c44410f00321802c143d40c6911a51608034198003503901c6240d00c001c000f01c2004203048d03100e441c0f9812100105140b04041030074030030150340300d40b0030a080c4491840c0610f00c050030303100022580c81d04007407503d040700d0202080d070354044000003941c1c00b0b2108040d5007110b03d10010400d039a000c0710404588020300c07a203498245014244c00400a0342619076102042034005c0d640145004401800014800c0212080c5441c000c03011110744d0003419100e6107401189404e11206208480035203415455460501c07440d0b001300c0c01030b4000307021600c00704008060001900f52003000038601485141c001311000f81780c442c4c15051030b192002c0001781040300058541021030a04e860580d00103402243d0410503583d180d00590741d001000b0f41e40380880c803000400c001403100c10740c4409881d2050031070030007600081250072aa140b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 579520152 1250 579518902 579518917
    0xf050c07020904021302040303020a050606010809071502190f0506060402030601120f0212040308010e0c04061d01110d0306080106051f0507110301090f05100507091e0f031a0a02 78
    0x18104004036400741c64211034660b0301c0b80c4014015100c450b144080c030410703030f001035000700c002d82d0140d0b40140401100b8010b81303620400038604400c181c6400d2002039540e0302d0900c60812490100c2d0301c2c28071141c0c42030194071810a441000d801604c141e505c0c20b00c81e1410130308016103844c0503800210b13120f49040d00031240650740580d6007615031442e1001150043c0459011400c08a03420803c01c07042d80707401a001c0d840340f400733503c0c0d80d07101e0741c50010407264125000703026207214001040300b8010150010100640402c4c107000c43c0c48400780f140c0050f41c1d030030606010005244107620130b0112403540350300140d0030740b0300040c002e02043d0780e1401030084104000d01104190554003088030103542c4124007400d80e9900a4030390132000c00c55a03000c81e0071140e18803c1900d0390700340d4a00c1502400b508100480040c404031808000340d00d080305000b0701c540e4440c0516284110718800d4135840703840d9680030390050400c00400c0f100ca90380e2803034524000c400700d9451210100758640090034503c1240f082c0d0340301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 579521402 1250 579520152 579520171
    0x504060b12150f1003060302030105040f0506010b0306132705010e010b04060503070501030915060803040e06010f020d1b02060c010606230a1202040305030a120513030c0b0604022206030f05 83
    0xf02c0d901500700078440c00700c051a0002c041c0e81c2d0b400000980c0c1c090050300c1c0210701480400800f40507a08240e0b08005050704013078034115041080c07001d103841f10880315030290342400c2d00041c582e01390404050391154084281c482c0280d814840018010194498091840b100c40200014602d9800f4403003600c1062007501d915400040c0700300f12950180e00710541c01845070704c000000504503e103e004440c42904800c669074030100b0144500860000d84a401003000d00740802c0c1d050701618001d5a032403c40080204111304016547c150400142041c100c1b1940107081c06d071511048070070b650080050707108100004100030104000030a00b0220044161610814946800f0000d00141c070701d400c071329209680c259420800000407500500c0606407000055640c0c000d10511302d28140d0640b40b01034121446003040202450019400034425800180d011600185654656000500a0140064840a03c1115003203249a036054004050940303281d51010172800454075a400d08450040760511507 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 579522652 1250 579521402 579521419
    0xc040b13020d02190309020f01030204030f060b120a030c0605060a060503070302091311030a0f0b100e06070c030b040b2d0604060302040614130c08070807090504060b1215 75
    0x240c1050340040800c0807401001524044030807692450340c0a040900c00c000075038a500000031440c1c00750120b0303010102444c0a41c18503096440e40c407a107400d690802010030350b84040c03100741626181c8480700c000d1102400d85500c14150308014107030015a00c400c840d91458000047c00c0392408410303a005551103540c440d4290341c3d842401780c000b980300502455004e0b540b010b11405101c042d010b11b11040361170042e2a6120304111091400355500012001905420201e207c03101e41c650360f580c1000500b9601d00812103c03458402329080344502c40d4045d000103d0a0004000d02000c08070060040c1e2041141401d155240312001355030740b5208c9560408120f02c00c5035030361140701c0c42d09002e405c003400034000200a81c2d650f000404032042c50b802492100c003c050100c1c428030303203071400d04440c2406800c10b010484403c23500514900000745054148910030000c07400c428858507040001e0840540100301d8640c0f5019166460341000700c4c1400c2d0b41141f180003c201110004400100f20f00c013510810 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 579523902 1250 579522652 579522679
    0xf0408010506150714011404030c060c0815040c12061502120f1b19060609060501021504062a050712030903020d26010b09040c020d020709020706020c0d020105090c040b 74
    0x9005c800f2005640342da04041c0c00104414a8900692080d02d8200404a0360300d4480c0560383c45800c8481849208001c01a02050805900b440031000315000600380502c03040564400301ca8401002d015880c4c0040480c0c0c50884541d224507031b400580072200504c015010350b482600c51090342c070003881c6040c03051001c0b07860a148001e103914016015a020525055031040b1017011000342070703540b291540010044c0040c13621070034000d80002c0c03015001c4802000d00e0803482c1d032809400201107540c0c4021040841c4000c40c588003946084c2600804c0c01151070b0001040c030780040000f943d440400c44800d00702c9a003e8400c3d810b1156041c1c018000e158074009064a01d11407030b000d00344204000c42c010780380b1a006885810301070700707803c0903094640e00700c0424801215500210035081d5840140f80d441d689030002401411541e0b0307084050391700d41061070301070081d0007000d000b500a0b11840e1601e400d000d406400442c85402142c04445a82061004200c02c0c1c030305205080b034100510701c5105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 579525152 1250 579523902 579523913
    0x2030a06032604140d020301020a090e010f051f021f02190306030b04170f040806011503020301031502030c040911030f06030c13050901090b01080a0c0803031b0c0c060f04080105061507 81
    0x700c0c81c0e1040109070000d50174803500482e099900620b0080c0000c2c4240106012140c4034819060260414030a4001400d0400d03010a000c0e1003452000d105d18540310410040c018420000443c44524440c12600d10f0149040220065000b140c03205da010280c0702050404d1038400e202e54403c681d00882c110815844603142e40c1440303c110500203074001c0c001c003e0524500c120780011f000425040c00200829850041c091000021040c051420140104010804103d10f5211500314079031314000141d40c1d07181c1c1005801140b02d10b5011a0503d07040070b41b03c0d000c056210b00590311030058508810712560700c4804254940001140c455400000c88054a940c90031990105501203c2034000040c000b999031030390700c20301c1001d901c10000ba41c04038a1070000c0081e508030800003000300d14011400c50420750341c55118056042003107500034102090840d0410403c000302c11a81c0f02c05451103036903040b1030745041c0c1944c1c0300d07000d542d01c190b00f81800b2501d05c1c246a11001c80340601040c18a0501d0720b01ea860 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 579526402 1250 579525152 579525179
    0x40c0603021c0e0a0c090902060415180b09040e010905190305160f1502070512030a0914030a02070f030507210507141806010909020307050c0102030a06032604 70
    0x900c514030260386054498510540304281e02043c89000520700020a45002c080100040c0c024183c418101030b1120300503145c0d0300540342980c518034180284c2081d841c0302121002c0c00100503400100300004009241600300004291003081a90140004607a0110315030036210725040c002c00960250602c810640c100d050341d1003555109203016460000d400b20710f0088140303024000c1d240350041560031410019082900540188402030641c18002d0b16141c0036121b1040c2c09407180a608008000780211a265109503555075002407242240c480180380701c1d580b90400c0c0010030241c400c84102095900c1c40d042d101d412658000d0042c1602428540e0704403121180c15080300e9280d00403080c03000021418001c000107403840c000d10903043d031030f1141004900d61802c680d03180001c1141003400403e0741c0c8a00700d0710aa0303c5460015980740c036410b00464080c40340701d2090020703502c0072040c00042c07a02070704448100d0340103002445105141d107807695807013101d4142e082c90b4110100000c12900d26210f42 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 579527652 1250 579526402 579526417
    0x120f02010b04020c01020c060618040303050402010e060d05100906180b0406050904031d0609060a14040815042d0f061503032006060f04021806040b041a03040c060302 73
    0x8a1118405000b040c2642c0160400c10000d94010610007903444007000590750140b030464485501282280e9610344074a00074002034101622400000c09690081d20481e030700c07250103030045a83d02c00e8407101d280100001da589010800882d00f000900c80500d001d05000e540001041c0c0750300c0300403900d0b510020a1a4034600b80c00c00c0d124480000c0075611082c00b5807085010f83c9601f5080c0b40d001040f4544d0030b00ea480103501c100701c103000320003441d20b070f58040d1010941d55007411780320340c0a03051300c01040e40150760103544c20b8803520180d841e05080050348680150b200c3e07424405164803034040e003079180316102805030002c400d10f84654041a02607103881062400b0b1540000c2e802c0140c00103a0900707611750415400702d401c2c4002d0101408280c0c00c454104010400940101e007000400104080f02c2c41560607c15030300414a8104c8140d1181300c0f844500009198994840d0b840740032400a800c40d00c1681c4180c0c8014041001e0009000101ea1060741d00c4003c0409603401c002d410703002500f000310b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 579528902 1250 579527652 579527657
    0x1141b10091a31030309020603070201020d0e070e0402090a06030501050f042001050315060904022215141c0e0f0f0a0f12020a1e03031107120f 63
    0x144650100990311070086160700500c405036200e000d07010000c0d101c5001611120030200c281c10300850400b6a00c0c03612078031480d1024007a240c448a4102100070f03042c410406544580b0000034401d41c40d80540c0201480d140154003880259128850181c0360126486443d80d0382050303000081c010f00c0c1c5440080c2d403001d03000000080141c1c5a03103d040c2150012980101c1100c0e0020034001441604001d82008441c214010b10040c0c1d06080000c2c0680005484688460300035030b0500000d5403401e0680d280008068400c5498a940c5500e140c08500310301c070010300f04501d1601c00b0500300103a041c0b52603e84401c0d20380c045c1080b510700d54200766510103004200d01c007135100d4080b8000403c030b004401c01840c8550050880406940034141050b0503105550314591142e01c910001070240b640310711800750405000340045200705416030400301c1200b0006e00460750011071115464401115240050280d40c00304100304010f00850010321402401070f003030001c019980002184030b008052004c0c0b01c82e2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 579530152 1250 579528902 579528913
    0x908012d0902061c0c110303041a0612060a020304141212040804081603050d0513090b060913051504111c061502010204030b0c040b1b01060e04080a0e01141b 69
    0xa0a0000b50000c180c12821191512469410005d503408100910883d0543e4041e40c6181003584e680c07103c0c01d8450880119804c5048005500ca5540b04802940e209a0505a030f4040c90f050212100a40c42160100d508070b500840da000303075400c00034054081440554445160071034144142c82d220400030002c6a41c080e0810000c10b88040920030f0000410516011450031421880e110703013040780d0110034800300300090140da0205400580b881e401c03a1140c41c00010f50503940e4000c5042440b500e000150082c1581503480c1c000700c215480346204241c590f854140c222147d40402054400805c0c0c00c4090240031300c411042142e842034443d1040070041e0f0001100c60359908070301245003001c2000390140c0d5012604000f4400b00b001030b550302c418100c002c586071a0030240611500c0c01189040c8241c2e44c012000c95488440943c0501c01600c06042451014500741c40d2602456101c0014030700090740b00100541d195000d0031a00c00000003e00ca810b040c600315540702001c15420900b21308961186 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 579531402 1250 579530152 579530167
    0xa02010f14040512060610020607210e0f060702010c0311070312090b090a0501050a0b0d081e13180b01121a181b0a020604030305060f100908012d090206 67
    0x1302e0b80c2c02c1d49116005000f0300070500d0700c40100b0400704d02020b20321302550030103002c100c0c00a83c866006800a2000c5180d850000718a1054030001c0245021060151240a03a40405408001080c81c440d00a0b42e00034469008021408c4040c0c50f00d1551044080405002c00d5002900a00c00e070b0b0080e0200400c0058801e50303e031a40849501c054a1400c03041d000421303c0c1007882070070b001e480c0d4015991a014065040d22001141c0c21010000c4050018003021503088540c0c080c40c10305500e00052040c1c0d4980301c40920301010340c00e010a114000900918210a2410701554040c1c8030000300c0507110340003441010030400000e803001900b043c000d000580da2000543d590f10f510b400b8040800007038640540342004a0600078544080010b00000040c0445582603500140e5030b41e0107645441d02250980b43c16010506c5000c83e040c0345a40084160300d004601c0b03501151480466103081d001b03008c00b11a180c00f4030f01c4111901071000010541c4400a89001001d4025070185403001d000ca03841c2000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 579532652 1250 579531402 579531409
    0x207050115081f0f3b070b040e091608241603020a022d07080f030f0a030612060e070b0f0d0c0c0212010c170c0a0815040c090f080a02010f140405 64
    0x1114040c4044000d0503510541e407108030105d0f03403c180b150001816803d0a014503003810b07000f1803241c00c034820a0700002076402002800031140c80c40042000f0150a40c0300c42107551542d02030301c40480c920300c0199143c0c103100f0b40c241001e0701a9986017841030b590b401d4868114069403002200c84e003544101100340d050b2402c0c2d0041c14042c034500c1e401c1e4902c18580f100c1d0b4142820800d17030092070181d10401c061113003050088100d4840361142e0a00c19030f85e07100d21406070090446980f1094084022161502c244200c075080601c2881c0d08500341c0d010b05441c0c2c1c1501c074440c010104107905818041c4903408645030564480040c250032030501c001c60f903000d940050307120710480540c3e01c0e0300d0b511a0035080c0101d4002c00c01c0c40c924500c4031074003882464104003072220b500a40e9a280c041040c0040403400390145101c00c2d501c0440040c000344510141150040c0c0340b4400c3d0f1007559185c06004030001004000800d06e011020b07816510181d0902520a0490700005518800e80c40d0781c0781004001055034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 579533902 1250 579532652 579532691
    0xd03021213170d1b080907180f060306050402190609050108090f01050c0d050a140a0903030605040213030218100b0c1015290a030905010f0207050115081f0f 69
    0x100394402c00b207410b600849644c08844428101c100a101c408001c2c0504000e0124002003510f40900c03005154041120320301001d0000000c0d1138003814602200481801403980086220301c1c02994400500d204081c450703210803695101c0c0c900003843c0460140095032048101ca40c00c80011011100f103c0003003400503084400584104004800001d402c2c89141c030749010701c03540500c0c44001003140e48001d0340304040001d0001e11001109540d00c07103a07003c15000c0da2018014200141086440f140f03c45448c59480c40c0c14003080c0c0c451003440c03640c07076150b000b522081803160302c4c41000c004030f4a18160790030890b0340100e010031520703015014240780c20560300d00c164403120041081401c0385501c1e005104407140c14000c204894891502951305990804d10100ca040d0b514900d00017940c10b0700f6041c21401080c034045081016800000c0160031702c8815003280030b002541d40038843c01265201030844d601d50a001c103820000e943c46a980740f00000f91b9100640d0301c0d0002c54040b031249000c1000c01c8070702 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 579535152 1250 579533902 579533917
    0x60906010510080105010e060a02010e150105040f1e0216140303010f0503010b010917070509040c030515040b010312090b030a0c03050606040f090209040e03070507080d0302121317 79
    0x950120004000614103451074401400c0342e41070070816541410002400b1100a54801d0702807400001d01e4036071a413003544500032040c2c10360150ce01540e8011120846203a081c49007900c07a84c209200005042c3d120312540600c18511321020801034072590407000650098019040d203444000030701404541042d44001030505204045c0da52581000c020700c1c82958580c00031030081e8540710341d002059800c8009035091310480900180b0501d18015420b29000c80d5070419500510800140410045221103050603684200d081c4c6a00712960031038101d512101300c1e00982145140801040800e10a01c0c00c0400883c092800c52140c0703845000003010359105542044007a40d41d0780783c441c1403e41c0340c80341582040d02159110f103094501004402c02e03420300d00580d5402070b40004c2c140490f543e141c1c48000c81c011100e0640fa110f400d18100a91220200d1241c1d0740c2902030080392101c45131103442104e0070020900c400011685400c2c0c1c99040d2101044000c880b1000b5400b910503c0c900e02c40b010b000d41d17 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 579536402 1250 579535152 579535171
    0xb0604090b011d091b041a070b060118030b04050a0b040525081e0102071212051b0403030c03120617190308011e0506040306060504150e180f06 63
    0x898000030001414a25034025180341c032910f101c2d10940641c1d0f4008007a4105040084503d10060141c142480c107100d81d5004ca060b403202d1046102e4501303000c402030506903018051009856441000550720610005407001d032814000b4070600002d103c20b04450340142c020000c0382c5040f0385580c1d918001d1038040e18280e8241e1710041800c018510707100760752844100b40006683e001d916104441e0365814150030315030103442d5480509503d1010940c1540d80180d0403151840f0702a40150010f0f100015101098484500308000200c8141e40740b503401015140300b80045203402d15544048a02d0451500110100701c966161616811810301400020f0100c0b00004803140516403503952419200100320300c140c1c1280904e90002c00e400020040c1160000c4001da800c0c1d00a10300250385454180e04910b9000300041004403d010b8140c0c0a9010303510282c4003000491711f03a0754924101d440c00d02c2941c6d4461420000150740340074510184000410030300844620006c00f1250070700f030507012204240c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 579537652 1250 579536402 579536411
    0x1060519080c150a110a0b0f090f070308090904110a090506010228030c0213020301060512130f1e0c1d060d03170c1b0604030f02070f180b060409 64
    0x903082400b001c0b030046801c43d03800c04024072818400e500750241000c04401e0000708031142580310414071800b130241e503000b11103070b1171464407500004030031805071034040180c45011941c0480010009002041d00d0304028041e0405846500f00420307944020001c580c03022a030b0300903144689030020110b0252403401380200705d5182040c002440c002c10210201d040d2041d41c1d0014040060103980c80341115098079228003138070034078000300745c0c0c40c41070510320140c1c14400400007840300d40c40b201415080032180c00c4458103840707c0748405022905020007400000244030000b002030314098100810801310004e41101c4d01d815141d09021105c0c55100040011003030346151054129003401552014003112100d480100e00c4e1002084050304640c40d03642e4528800200d010300c1000401e551081410b140104803214005288980390b034000c3d0303021008075400382c8a804c10f01e8000f103090416901135803c120039080c903010070608581101c1d1402c1c07600b295150040540381d25500c008001034107000d0760205 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 579538902 1250 579537652 579537659
    0x6040b19020c0a05010c141204050102070203160515120a0c270f0605030c1608131d01050901060509041a03160317090f01030903110d0e04150503120a0201060519 71
    0x303003990100c411000070403c0d032202d40c264a0700c8580c00d4890342808c10601c0286540c80d0f00c0c1c814024421b00502a5161241ca64001841615110484c1c140d5038103481d014418148000c11082c00d0041103240002240480c001072064003169100102d100e509140c144400740785c0c012042580508501c048008d4683c0c1341047c0300c1c2d01c84180b09030000b003101d03203030151542c40c0005c030341c500601490005007061050800c440c01070000c0d01381a1000f1811030078030428002d85e00d48a05440e101c403c003a254203400500000606490714081c1d25040321704d680c071100d140c9800d40c420080240f04002408100c0005604186038a48080050342140c440b03c0890b02c8889056080c41110501c03443c0500210031b44c02c00c5603c1164461f448801080c010a00700828407840500e000e884005d80f0510381401c0307204003481886800d600c5030800e0b0700140142c1e800c0141000d802000003080206000f0303160103907c07104504c0e422950107001040c455600b8400010000c2d20754000031a014403840404400082080303060 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 579540152 1250 579538902 579538913
    0x204030501270f110402130503011a0f040b010504261c0c0803060616060f0c0c020d080903030d0e010b0406170a020f0d02061b0d0c0506040b19020c0a 66
    0x1440700440d080c2240c400b0702c5941c0c1c180b84030700d11541e1000300303041000141041001603121000b081500c004205644840044a50403106501441914425800e02d420090000034164032180b00240c0600940d2403411840b0902020b81101603c150400008200c0045c0303001d2001000c40240040c06204514480c07102c5a407450320850141241c80c20708554214944150800c2c2541007141d84201d00c69160b5489000107149130041402d184c00c55017503181c0701c81c104a5035602a00484031092010021503146d20000c0724501c1004100941020121403600041003003680644451040107040701d00e07000000e01c03000c4c150b41d40010000403503034444152040d18502400303448080e103a4600c80444610801d10000d0f03a130800314134082c1c02a000d48804241e640c46a074001614107802400c000e9552030803659440400960801030b815a018145945458030310401c8031404031600f21005094644441d100c0c040f00711800b42000d10600c02c0d00c055010707441c20364006450324100300006070031100c070340d0700f4807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 579541402 1250 579540152 579540161
    0x41205010c090b0a0c0b151206070930050a0f030306150f051801110d0810050303090102070b0c15090c01032d0213080102120103050705010813060b0d14010204030501 73
    0x202c18654401d1200313031469031303103d9110f440054201c0c518206c0c41d118091080340308981c0b588100d80151545950706c0700c04e00700158460140036643e60305603407640d86200d0b4104040c03240c00c8001c2640754000402506440001c141500035000c0c6080c1c0f0090540c0d595042c41540402c403040700403c0c1c4030031040107c14101c940c0d000030300c441e500b02010040a00d070300003080c9105042d425852800c000b9090b074400e0b4401d0403919204d9048004841184036461030180c1017000440780c54544500d10784012071b880c240403055480144041c2c00401440741000c003c1c020030341043c0c0081c0802e208161105001041c0300743c02a000b8081e078000741880e02c001100040560745c51024a00407003040c0c010300c80017200d0403142a00260000d000c01a22016030081002101009510443c410341c0017281c214030129a01604504880c032405c05c481c03000d0340d9000191507011040701d01c00d51984148a814021801d0b170b4100c40c44001004000440c0301d02107a80e500498482c6440540c4c0581d4003003000c0c010040240714 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 579542652 1250 579541402 579541409
    0x30909091e0d68040b040902010203121b0f090102060901090302120703020f1606110d120921081f0f030f03120f02270f15041205010c09 60
    0x50b180c0c911000500007030226000202039241c3e201c600441555180d250082220800180d041c0c80c900007440707900c1602d01001c08000280728070325029200d10545003611503051203e506070091814100c100111441c04400144609005a0580340e260340000700b40c401440b41883c54013505846108003000280340c03020080030100c1583c5814030074400700e42c0025030741085000c03a03e940b595500380c0e031170100d0400d5040d5440050504c2110300c1e080b00458000ba030403003a6810303584c032090b49101c07004c85a941c41c1004800d04000c244011400e4080b064550002402d6034000d841c0814441e04d201607004c0100007643c2d10b03d0004402100380203908503901c070001c403005003003410858150300303148076020220203d220013801daa04040204007010301400d40c4141c80001c0342401c201c0c048018540a0103035115210b500d900138a6070451100b4203c0f031820700320744143c014000c0030390509208140320408038881203044580000380300000b28040c9151148001c20310440c0080345500c46000d0180c100881c542 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 579543902 1250 579542652 579542687
    0xb0403051f090512030601020a150605100507120305041109040b041e08030a0203060a0314060105031501150c0302011107141203090a06180b16090e0108030909091e0d 73
    0x1910801240c00000c1318030b1a07066800c0820340d262034010060b0301e0016090030050104c440ca80c1c0300854030381c0540c000c070126402514046142403c02104403410b02c56004020540c90f0340c401314800c200d120f82d00c071a45c170521907a48018101c03145000228413881c1294110b40d40401c50041108010807012102402d15035007044402c0800c0f169680c40303e5000041c02403c3d983da000c0002010307a03443c0f0b54100c0045070001c012038902d2141d0801c041d1175135030034010140644034050a01e0071000c00054414121a11003000000341c0178104001c80388840700f46015400c542d26071a4002c8107503862001040940d02c10400002c490350309800b900d060100d8a05448003000c002d0040182c1d0900c04940a4121644404009400240500303180d514100c14000640a883d9120411064540404e1108080c484c00d446120a6030341d07401400074040d03824000c0d00920b4206028040f0301b07050400e182034000e41144140c0742c4880d0506076000d01d10300d010165805682c028508082c04030b0308003d4020744c218011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 579545152 1250 579543902 579543911
    0x702120d0906090b0901080a0b04020f0408060f070917010e03220503010e0703080310030b16030e060606040501030207171303020108090703170307020a06091104270b100b0403051f 79
    0x1508480f15018045c110f41c1030000840000740c4960641d400b1311920713440248119240d000c001ca8a00158000e0b0041c00c81e180f1030176011407108540101200e12a011a0352043c0025040103402409120301c142111001d64854481c0611040c0a0010303040417284420301c014032031002c0c007541d03240743c0d102e0740070324002d91609801c001a00408a0404240c03600010165569210200d900360001025440034100038020018041c180501980c1c4010324480d035034050101444440099031220801d403803c540c01380c0c0401c010400e95010350050900c0d2030051400e03000c01902c01500d90800c0c0d200320b400d4109004640c4003401150381048545070440d58140003058880d00315681c2c2660310407843c610b850796107004000954a0342c400c20011040984c0700500340590900fa00d4004044002641524440c5081140490020034801c1c40c0c184104100300c2c003808004c609496000c0e8810001e8030242500035400800b003042070360b0a00800045104e5401842c0c1200b40e24104d0740f200f00c001b44051101c6081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 579546402 1250 579545152 579545159
    0x7081b040b03150a080a050a030923040c051b0a061d0601060311211b18061608040e161d0411210f060d08040e09030702120d090609 58
    0x500c040d2540198650035801c2003d62030000103140c0c0308240c0c0140220700c50320040004110000c1849030380715210380c43d542c0d480354550104080f0150074010501d5100e40d621080003592400303800ca134410382c216040103464014010380c0005d1802c4044400d29260703006220000810040d03102e4000420311540b2030b810a880c6005145813129410702c0741c03404050300c45002d481842c21250449007100002c007502035000502d0444002c0110086402d840340b00380714804150015940b03002c680700700d029040d44081c5008080200b10003a00701c1e5050b5094281c40440305000070b0109401400034110540c5030520600e13000b0340c00000e0f80c001f01c00d0340003044801143c0c5d000c1454864135404047c8021200032a406e050000d02d40001d0017181e0300449489107014100c910340407081441030007000c1041118078103994030424030070610b00940c0000c1030100100010040d0041010050390072480d00410360b454545140c0005a4441c01034143d0742c815044000c0e08428039800c40710150042036181080442c0e1441c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 579547652 1250 579546402 579546419
    0x50f010605030901021312030905060406020304050108041a04140c01020d050301060507060f050a0b010221041e090c080105010206070c0308180106030c1d0a020304020901050d050c030607081b04 85
    0x610400052100100214010740f40a4065442d52074032180c0d0400880c0d40d85200c04001c440400e400c0e00401c1d075045011410b41440c2c1e080310252400c0f600214076040c5844011103011000030b000740c40340c103200682084d0740b1075000d0482d4015401040c40340c000c4101003541031308043d1102c0d0024107540c80094032003545034012090301d045070070505180d6100c4010703083c408058550940c4000d0014503190802002c160554010051000c0030707401c42e08034410303405040c0d12111604008015040d0240f00c02c00480302a89400030f803220418480b1003c5580d140c01072402d56007400da0340b1000c2015400107120740d5074100041548410390f464950740c2e1101d542c074094100040940100380e07102080000d104090f02c2500700400855000c0094030f0081d07600c808414905141411240c401d450180200381203031280c0c020350380079a800500c0f0f500107910b002c0402c010f0b44212541190300340544840b4074140e650600c206803040704141c03a01d0700d4501e40111140c460030041040c69041182c00c4c4014040e026 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 579548902 1250 579547652 579547681
    0x521060a03030804110301240803090622080607030b0405070512070503060d150609141b090a0b070c1403010c05120c120108012004050f101e110606030105 68
    0xb605800d2411503038403642004420f00022500d203503003540c00d00c088205a44400e1000d0b500070b41102e041425529107860f002a01c91003401c0c02ca03a4401c0040c441040c1d481500000081c0e80d0700814241241d1743d0b6aa8450350038371104540700ca02107507980810a001d41040d020300342c0e010155141251901510582200a042c80a40710300c0800c180400040e044ea101c00c0c02080050b0703042011400a5001c15584501614090190303070000d5081001203a15840d90152041c000c1004081c1401c4505805c1c001800380c0c0c0100c240b05521484410001603880b41010040c090745001e0782c0300250709070070400321012a0088080311802685072000c080034850b0309c2010798400c4522104403c039107881e00c04001e11b007401840c03103000c2034105820000814510551150080c0840d0141e130b840e03800c1880842502a005a21642da04581842403801851034100d81c1d84c0f01110701c60410b07203032102e0150400c804480c144146000803600c0d08a981e0f2080a0400010b6400042200280614900702d0070b1060300f003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 579550152 1250 579548902 579548909
    0x6130c0b07032106050a0e06031c020d0807120e251a0f04080115080705010903020a151206060f031103131709041b0e0d08040605160804060521060a 65
    0x30b04801c485403420390011340109004002c020a00140e051f146c290507400108242d418a102e8812404850401100940c0000c503081064000c0d200800c54070f601614582401005402000091040d130741090307045100d0840c629203650000c060f052519071601400b40440c82240c10880410a070400240e004014079102c0500307505802500e03192201c62011036070141307070000283c43d400e00d9103001590070804200c00448240c141124030559507480151040003803070101030342080c0c50080500c00700b60100401c1c026494586030804020004061081c11202150003203000241c02100c0d600f4441d034140100b40d9506a5010401e1071801c1c0b045a80c3c50303411016800070044608015084102d148804c00e556080102030810f0000245803207580913689200004032000c00c60240f896041c07410142414050b499211100610705414000261403903000020b40d06035403a80c2c2a0304600040503e0003800080c1155251142c451100290444881800c24403c910341101541000080d5441080c0702046 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 579551402 1250 579550152 579550187
    0xd0c0f020f2e0f0908070c23010c030c1a011a0408070608041e0f170a08010918021f0e030a0b0c16052b170c0f070506130c0b0703 57
    0xc040402c40d00c80040c110032860510102d01d8880000c0030301810304001c00d0310600c585503a590301c2d81c45000d101180c508518112911101503031200d4043e5000f1000c1030040c6001e401d00383e803600d06603134840004038029000143c0c0030220400401c059540d8451102000c2044200d180c2403030308050721180c0c0d80c0d0003441a01c0030070a491021070244910030a94041e100c0b525440545c0e032a5442c100207d50401c0c5c0301c01140c48003031084044a4050106e0192a10507540e507482e440642d18240c00d80c000b80c0740f000c02c0322031b4100507100c2d03040050350f81d806942c03240c3c1c000303448000030311800440c0034001c3d0703405841e000e0198200c0051040042d09001020741d1082c00800540d4580c69440c0090301410690b0030b005006102d122a0780c0142088010b101000004148001c00985c0d07034460111840e4404808500d4002c0d8080081154419003038080e14130154040c2919040c403c940d1103c40c5004416522000d00e48486030030038061001d1050340030060b000441000b0715111103a40c00404450505108580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 579552652 1250 579551402 579551473
    0x150506010f0c0213142d060d060b1f030501030b0f1911040b0c03120124110307020a030b10060513050636011d0307030305030a020d0c0f020f 62
    0x800800742d404442d00b62241c00e540e071003900c0c02c0d5050941054003141b52076141801515010b0718440800c18041c4a058043c096904c2400103070b8489000e0b000d44e00c1800e6003e040c140c40180c0115023108610043d42c403031740c1c02107555451414100503046018021095070101a810045588007005990300049105403000545080e181d01c0300b8910b0180760010a80f0000c005202e030318940002024080c00605003800350140d036030f250380c4403001100142d0341d0550019880005c622160094010210b041c1c0d0302c00640345000c1c02a0b0006040022541044551008520074069010740400420000c3c0c10707070f07061040ca44002c5210540d81042e441c490580f06000005051a6440f510410300d801401c00070010720300c90410f41c07000f00d209000c4602050020b80c0319200d0305c1300b60301c0315504a1003040b000b030301500301036080d03407001c031a2580700510711040306808002c005540e20311381c803c00a8841c8180c2d104014158081d000904080ca0758606194940c440c1002c0c00e00715135081c0c080d52a1400040b40c128 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 579553902 1250 579552652 579552679
    0x301110f122d04030e060d050901050f090715050702060d14070f020303181606020c01110106030b010509100f030303020a0e040203060108180a05030c030702010f0c0f0b0a0902030a150506010f0c02 86
    0x39101005c8800d21a0006404100c1c5000d0142d50342016002d03c1c2124000c2c401ca603a096a2500c05480440344020070340e004401c00c00c804004061410360b0b411141c03914924203601500891002c0d0301000381c5403903031666105286c4559464043c06508a00d6914010b02d01903000403000703589005c09421941d0b8600d602c08030154a0130100218907910700712808000c00550f44000203501c680b800240240440d641044010003107106101d50402c0c0c0342e00c00b081414590030725040c00700020000700080a806209071000c201d070544000c010000358480c0e80c016a80b00e8544100904401c07001c803180e8015070041c810701c01142c1e001882c044d4802c0480101c1c01665030310610305072030104200c1029001d8040001c1c0c14019220210044c41900d0003a2108a04110f4160702155003605520000d04041c0c6840f800e480040c959240a5030002005a804101d03074070207070000303030420920b490704940040300100403e810420f20700602e680f02109081030b00140c89601c00140c82c0d80b1591034001c2c40b03010004d5075907 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 579555152 1250 579553902 579553907
    0x1003081b0d03061e12320f01060906050d060b0102010b04021803120c1b012a02011103040b07110604030605010803040609080102090604030602090301110f122d0403 72
    0x4060110814044945181c6501c2015006200a00404042003148400b5071040070110103603804407009424903100944054480c2c80d00070310030b041d03084402c2d10902e80c4110f20364191040070b42841e034074401038011890310f41ca001e0f08481c5154401100030741000e4040241d6a14800c894400d00d40042e03010803005078800040f4010048504081d50152021130010349060032500180c0480d4015812140399100f1741020031030501820394030700c40079403059810301160140c0c801d000403119010f04195808200713045c0602c48403400c4041500d00e00000703503803450a540e0b01c000d400c0700c1d442d585800b85240604101212040d4801d00c100500005207102000429466000440e00103642208040015513100e0714460340f01e51107842500c0000c0c6c4141320202c0c801e203040c4221a5041d20080105161620795590900690041c0d10400e40c5950381320410b0b1603031603154000741300c0301644c11412551001d014808020300c03100903000070b0001c002034200c0c0003500d9407005039010100b0303400300c0b001c40d9a490385800c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 579556402 1250 579555152 579555187
    0x1603020705040e03090109050405090c1e090a020a0e12032d0325110715020a0b090d120516030504020a03080c100513020108061504050402041e05010206100308 70
    0x50790300a440c0c88032070201d03c030700030001c0e2000c1c01d0301346d9420700055511000c000c1078410554540d0600d41004c5480011807900624100b03c003003400c0b0414030a005d00c0400240e00300b0007285c4110f241600000c0e20482168021103412661404444c1d40e090300000041e850307a80d01a47c0b41c01c240b18034580300c10082d03807000b4039182602d006183c101c1664a02c0e008042100d0b100c0c10066411101c0b1150314605003103030107898003440707400c0a4401081001d03e0803816804450503000c000003903006841c031000128090580b91841151f114008100c40003050b10014146024000c2003000a85810144130504544000010300b40c0100c1c41c021a00d610ba5000003074004085610051041600007983c51504c04c0228440714005000c030001c20a6660320400c070403031079241190090004000c000012810310b0540001000d40b00005030450505441c1c2001c68100d82c01500501282d080300c40036003920300c50741c0b0402070281071300f82301424650800c105050304020342408000c058150101b81070f55280840d00e807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 579557652 1250 579556402 579556409
    0x1f1e0906030606150908030d0216021003090219031e111221030f1906080f1509010606021b0118060e0a0e0603101802300c0616030207 59
    0x14104003407540c0340350040003403c3c188100150034052a502c00750071401703416030504486041025501d0640c0400d02d8000a5100c64000e0b80c9a5035084d00324400368a8a135020b1035103100e103032000520785245004124042c00034518001150700e0114041c40055601041619a40301c0710f00204152001c910303280d4184070524a440b604200d42080d21058160006407503c10503a41190440750034090303001032901403100315011565a8880b901003200c0000c074410505030752a40d200001aa1b541300d0800070b040490649080030240c0c400c4801c499918042000180c00c804282c00821000e860500c004c0e4507150740142d6850003111164101e15680d0007800d00700c0e401488018903040440d100c1c5005801d00105088a41c0100c0350b0710000310301c0031403041c0600e004131001030080c0a020802d111400c05410140326018140301103284210058440000309050180401000344c2c042e04100c0b511040b00800c503401d038459500c840c94108280d00c0b040c00311200040314601c548604440740c1005da1038481c09a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 579558902 1250 579557652 579557669
    0xc0b060307080d18140a0b0d110a020304060e03070e04120302130e01090b040501051507020303070212010b120601030f0237380310090915051f1e 64
    0x841c102a000d501c00424940d1325610b06100340c40b941c0b111898079504000c0f080c9140c12202910b0144104214000941060700c15400c0c0071505914011000425422490903800580d1001c14140003003500101d0880b01c0e494254003c2126600d0481c09241540b009800030300407401007854070240e2803184c1c0440d400b0441c02281941c00f00d54911031000040c030b09114254842d0310345400e12446241600515048440007004072032850610074040071554407031b035812070749480200720020050b01c07482c0d038070282c0002200000600402c13a1040c4920000400d130003250940002c001400041d051340c4825840540540307019030150100144200345c807004202c00314016410f0090340e41c03100c04c14500702c0f00b51418031894491080c6110480c480029019642d110030180a030f10304c2031041164005103600030020031300e102016584203591700032a42c5010040d1100d0445074481c0c0701d0100e45000322600140c2d041484200c080c101c206c0c4410030112401070500c989103108044004500c0040200c000d8000c85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 579560152 1250 579558902 579558913
    0x603120c1e150c19050c150109020403020a080703050d050906040330052a01140a0504060518030d0504050f0717010f020f070f0501090b2a0a0c0b06030708 68
    0x8000389580340a400c0c00b8106036440000020004000203081e10f0a400b41e03181022180c09000109071400c1d0002ca41c5c15030f1510880e450300040d030403444082802481401c038016562421401401016040341d04042c50342c0c1d000c01400c000144002541e8411082240b42040e11440c007980010514402c0d5071010304200983d01c121002030441e001820031946640e00601c603410700400041d501c50040742c00d0107644541d418848400080790b84011550185071400005182003c202c0c10454600c0030b40b48503018680d10010081004114800d2940003d2014000b90a41b00e010b407031203a507881807440b0300d14255252800b250411404000894084481d0000d8522542d190541e40c001c0d041019003107a802d60070300020080c8070400b4400c03550700a2100d83c0c400e2801c00d1545618400c01c011903403c5035259130328010300c0702003520a52494041d1050304000324280700500041010803032102011130300001e04000240c901500401c040300700e254460031112081d9181b6000070b08201c0340d9032103400b150150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 579561402 1250 579560152 579560203
    0x13140303150103060f0509090a0501020a020a05160509060f03101806200403030804141209010810050105190c080d0b011d060f0d1515170603120c 64
    0x8405180319844946000803a4003201004400b520340340c2c41120400d06080302c0510960074840f03010340d44542c40e58111941000c40307540f11400c81e408485441c0041c1c202a0750341041103814400344104a9a105c80c1c04000e600304400640c006201620341d5210721141c0c4420000c40c0c8045c0100d81e042c0545120030854400381040c0d000080040d4001100d2241c07400000b00d507014240f581e081c0851600c001d80c80d08090440d5800e0700d0644001c1c00c1650040c404003600e8480d43e008001136041ea25688600c9070700e41140d100007610019000c2c0c8001c14540b503109040c8200d0340c0c000140d811000d1300365080000f01d20410310589a090b0321a0000d464040002240c4076107038a103030000c2c10400800e03a11003400071007519500300280d10350801680c0c0b00800b0481c02c8039001d203c4001c0c0c0001014000c00155600e40401c0328035035841240d0045980121601c001300340da42d0400d0401003007141498401c0d20b180b404000183d1210f09055280d002d44501188213405080200720003150a40c429100c200380c0b204 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 579562652 1250 579561402 579561443
    0x3070512070c12031a03010504050706080903161b0b1e0f0409060308180604180c0e030f0d02010e24040602070812010510050703050313082a0f0715050313 68
    0x485d141c00764901034808208158101445454803e680060141481c2801d1410031500044041c1c29940303a844180b020304800d0480e0f15411803081d02c130b960340300e41c08040400da0040c034140075441650a0134041c400301c15015451628801f0b5032000314019070382c1b5851080c07221100d000300e802c60800146025004030030004401d00401c0c52941000301005c5008003081044024400c60086085540340410300c41d000701c5198001701d10404407400c004c0d520f1007038940030a141c10000c5c1c0d020b030025840008003036045602880b40074800040080075003404034086c0842490f48034007143c0207800800c0c90001a05105440d03050340c00a503070003c13000343d8030074941c2040d400268007030060034880c03904105210380423402001258405945921030701c1c00c1d40c0e144018031080c1000700c1d0f02510380580c01c0013100d000307075050111000f21004002c14041c2c03503042c40451a140001403042c8010540c413001c424030000000d0440c0c00c0e440030862501a07500d59a08109800ca9606108010302381014801c0c10341c0442c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 579563902 1250 579562652 579562661
    0x60e130804090608100f020c030a051e030405060610020615060c010b04150303030c0215040602090a05061c0e0606030a0b070e030a03080f0601230a021e160b03070512070c1203 77
    0x102c2d400001e02501460345e480c4400ca215140c1c452307003194010450070b40f42d00d015070003030100c10700c1404840034101e084001d03218840d40103c0301164076412000070421185404001020f18100910080540e407074400c1c99010011845200c4511507000414102460342c02500102c03070310b0780d001c2d00178800c0440c81040440c0a204034001100800c0c02d02c000303188401c0c030000340450100f0003d418206142c88a8442c0d9000398818030215800c41c12246010501d529000000e2103515455480c944c6100254078075001116a108043d0041e0b41041c011f004142e030b80003401004080c0c004045007030a8490203000c0d1200188040c00c1034041c050a5413520600da04005058480e408141d0090000d031790300e100440d1aa8034490b40d1382c12034540c02580750781c002101005002d40c10b5203401140ea291401c410341000c2110075001c2e40003c0e40c050b020030000a842009240010540300700751a0950070400e5020301580281c0c80c402d07005440a070001036000f0b100d840b0800029070000011080318000700c40c01000350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 579565152 1250 579563902 579563923
    0x90613060206091c0801060c05030d0515100c080702010f0c150606111603060c200f011d19151a04060609232704110103060e130804090608 61
    0x2070048848001d00213260310f421a5080c4866a00c1c59000da003014410f0b43c2c03003141007000f51110b01c8103201c42c0340d659007144102c5014074403005200b0401266082000034901c400618801000290120f00b000594020305854403d0f609003486580f0407203501b81114252200340c1d019049d00719140b207842d201406680120103440c1e95a90f072044403034142418a6136100c1404150f4a81401200204042003559100504160151902101149104407407404510f01c44910b00602d411020b08504103200911801d06100c40c6104242184548200742c0d5844400100180c20300001c0301c160304040040b0964500e00398401808100314040c51040c40a00e20320f0620400c1703000f145007000100c5c2041c0540031100c21118048142682c42030f00e14030003541c1c1c408000a41d500055120130800001582c1400700303a0075000e0304c00145140c80c03c0e0900c04090011168901d05140c50305400340843c49a03014030030383c0014440d85a078800b1186d413400c080e2510559010080e240d207070010114120310003140ca8000b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 579566402 1250 579565152 579565171
    0x2010606080c070b04080f0706060503061f03080a030b041e0506030613060f020f16030801060e0f220e150108010212060120121b06040b0a02090613060206 68
    0x91588031030007900c00c00001d542038400c00406000400c00203280760441a070051107003120350300300b80f0b154280041580068108403003980d290f13003041c0014103041103055403041b0024031038503542504000009461046000c040c0a41400203000b400c410700070f8006855a610207401000810414050464042c0046421140040c2402e010500c40c0c5000038400b40204949800240302e041643d440c02d00070101442c1c0482140e030203002c07002c0b80c800d40714060712549a40754000c0150031194a000bc01e43c1e403058205506010303503400050050344545542c4c80761120b090f21275000e04042d111000d690b460801908400081c14001201c2d090900450488a40c50303c020312803e482c0d0325058090b090340103640b003040c1501041d80000d0555031041211400c4000d0350100600c42c245034401755810f10004000c00000880c00142208044030320f4101c2445182614000c2d142d64106aa40e098440801400b441c1c203882e00030071311b000e45558410454180c0f8401c1000010195070710040a500c40c1d8003101c05400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 579567652 1250 579566402 579566411
    0x1509050d0c020616020406050604081c02070b091003240503070b0309060f10090920060c070302010521090616090e01030219150e03010606050913050618010b0702010201 74
    0x100307405800c841c40401d0340100340a090840304085500e20403000d000c00d0340d01c10703161000029140c542ca402040034020440c05400f12100c40c1d40c0c00110320710001704200841d0f0114908210304e031400b4040d200280d10441e40c2465401c005c00c002c4001e81141c00d50446401000c0c0e140c0a1245140c00745901280c5c005d40c2940c04c5503540d0300410000c1d0104071000556030701320b000001c052504141900d903000907071450003480540c0b42c004d0384080f21032503c0b00716480c084110701081d0310302e40c5100c0302d4205041191482d10b0b00c900d07c1c401c41d0300c5e100b09210003414800042404600d0703c481424950b0615036140ca01d680c40d10b025822195141025182d2040240c200d03240c015616120b41d8400069480b00d03200192181d00c0e680c24041c80300d4032544140e42310240c1820100d2044e5400207174078526a0769030398004441d54100201421212240c0c408014820b08200d180059114101c1c0c429009170f02c2d240002e0f990352580c0204111007298522000c1c8503144400114840601702c01070b00c2d825000380d00800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 579568902 1250 579567652 579567673
    0x9300306120308180325060b1f030f0204120605150604030503030103030e0d06060608060a0503011e0203042303040f0b0f0301030b041103010e030c010f0b01090b0a0c150905 76
    0x100e005030201c010700043c140c0000950802c0313101228403494640344044902c2e0444021a01003581d1006031090743c04450003001c0001e203c0c40d4000c00502c6501240c184001e0180601c01c00c82d18800030301280d0515481e52111103006020794140c800074400f0443e1020009070602d4040700030442141d4099020348501210300030303820000180d90649074080010b42ca9a421510700703403442c455405240d5485069914002e000400390b0042800401e5152140d005608050041146481c5603400c41c9009030b144c03c55034020020404014803113040c0700d0400603504e84440c18152071050611754004052180355150225020000004104481015080402345a01e0f0140c4242a101c0d159030340600400600040c404078240100c0d844d040743c0710311950b410b5040881c0100e8207540c518689820b1036040800c1068084000380a03100507042c50213001c1100f19500d000103081d0700810f004410081e400882d0a10011740900c80071a161500800032000030140c2c0101880900140441101c0038090040c600 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 579570152 1250 579568902 579568919
    0x30f01150e0c04120507090911010f0807081b09090f060901080d020604020108073c050415052a160e040308010504050603030f0301030614010f0b0a0309300306 70
    0x254050310304000014070b8180341220306000c403541828242c3d0075010318400012804250b00c50000d40b0703441101170980391208000050303d0000d0002f806414890b44800308050310340e011186070f81c0081c1c1c2c812400720780800c20010f10f40b980914607490303400c02e44000074010040c2c80790050620401e030440304084141c0c1c07940c400d1074403403c00402e510301503805880071900640c06081c41503071012244c504503200303102d4803141c3e28041c10100c08074910a44140d1510703002c008844c440c0085031030107081943c505132819984044511800c69151704200c4049545800100440c0004000403450840000d0a0340c003106459180e0408005012103041c10780c0c0005400144105000d224640503102d6080310781c81d02c070501c0058400141a6a454003041203403440850034034025501850044100107516588808410344c00710040c0c00401420b041d1540030000750021104481b1300388041d1402141c10100d600c0c10340f182a1a0080d03035291140000303040c02500d03c807000118107520981c2d4091010f56036a400300f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 579571402 1250 579570152 579570179
    0x2090d0c0819031d0d0602191d031b010e03060403020601060f140306090703020c01020703021612021f12060305060604050f071407052107121b060b0a0302030f0115 72
    0x2000704180242120200020301c903404c2200201034000c0074454280c0e03440400303e80c00103110740300701c0050426204d461540900c52a180380c1803145104204069180000da40c4c000854142c942c0a013402c503045803e0344a15000d0070b0408010301254030b941840d02c3e0194840809001c5c0500040c807001800300514850320301448100d110041441c44d40d194401846008a001000c000906800b0085800500c03802d100038110309001c0d1303007d001110b0b00203001551203642c580c45401161340a03220b00016070344070b004800100342d40e4441a0f0a40e008650180c0d8080059146000142d140c06000002c1c42008582588125021a41000280c3e100d0002d4401440300391034800019580a1400c0103480012004001007802042100c1800c1285200301d002c0c0340304203005c020720040108141c2c08009440000301c1d580b1140341028111100c0ea038a884807108811003000d0700b05510345090340d9040d11003a04e120040d54014080c0d46000c0d0b42030b2000d40c060407042980c050031f1180054000f83d022400841d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 579572652 1250 579571402 579571453
    0x51212041505310c06030b01090b13050d110307060e0112200903030f0301140328021302070b0a05062d22020a0905040c0305060916020102090d0c08 65
    0x18001112040003d080300640341e80608a8840110040301030108a420b030b4140014855a40c01254069800000400f0b162013a03105003a0305074140040c0ba0005030910340241501c3e01a144482c1e80311071404e0400c0300c5a1003c0d00107806020301c2002041d481e90007800101c1c440e80a813103103130070404c40220322402c4415404840c60341e004540104106180310303200901c50b0781c0c0018222810400342001000146e0b000ba8845c1081d0038602c5107060541c1014028160130a1043d6400e03c10555400340000e0045c03000396009114038031003078003400a1501507050300c20030794001e40000c049240c9520504020242a9501e038490306441900300300c44071a040021206980b1001004818500300f403d00081180c0c0c0b01d459180c00c1c802020702c548554031440036026120603951044061440d00d424402100c180b00046800c050800040003015100c5860640d0031000c1d07a04146058000c4d41c604030300a0281100f81e681c40304400c8007403024803608503254002d079261042a00c00d105d03001054080107403883c42 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 579573902 1250 579572652 579572671
    0x61706011a0f160506090f0c1302070f110910081207030c1208070801060e0f010c030210020703110c030a031409041103011502060c0a1b051212041505 66
    0x10041c0940c02502045110348106a03068a08004900540c400203402030b01c0f0518070909424818028000d0030041c10350041400000342030581110070940d5191800e002815004207842510f42c440101554100d0b41703c0c82d00100100c0c00c071a00c61502c0d0141c0523517040c033300d8482e044400c0464000d1805a10820840b42540010043c0c2a800700b029451500455015000d119942c055080400c0c072004004e40c280450383c1c1d520000b131070318402c0079100c1e4070b06800080802c890044001200c0d150549241400d030340c02d0074611051107003444c0c00c900e0000346596070300440d800425180c0070036401c88454800d034001c001c243c0718051881001d142c4c0d6a5110a4003a00180e8000c2c40344d206d0302e641e0b00092012050141012407890004524000541e10a0b400390858451710303040032402da94180416500005404030039803624030401c400800c1ea4003903034004e2132410300140c002010800308004580018a605c000c0d607485400000c0b403412210402ca81c01c0e946442c800800b00c0c1c50b1205403060a00c08d0b00000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 579575152 1250 579573902 579573913
    0x2030403020108060a0e09100c0f0c0321020c0a020a05031203130c030f21091421160f080d200f060907090b03030903030307050c1c0207090617 63
    0x181c004540c8918003401c1c1c540c00400c4d1300f0005c64440c3c0d031101400c1c8100342c910300602c500390402c10003070101d0711420f10003003c22000001c1000090342c000101c0900755098034000b541099045465070382c0a0410804100ca0b44c80000c0410042c8408503c1a031194000ca588180c01640c4806058071075040e5506039203041e0b42040001c8200720040e00980d6814000c070315100760300761250b4030920704001014084c1c903070014840c9012901c180300b541c000006d4100e850100e0440d80707002ca109041218001030984038606050000341400d034a51603181c400c80400d4101c3d040c100082e54081c0101d14640514034170500c204a001c00c0c5200d00184400d00410b580e503400000e5203030307039140454954079030b440240c190054000700c0d0101103082000c203005204a5000d07014851416440d01c0450b410390254a000350418011116181da020055075404281810900da882d03090000726420001040c0305030842c0562006d0018102d81c0c005084c50541d203038040704000e400d4540e01c0780d11301920008081c60071503001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 579576402 1250 579575152 579575159
    0x211807180504050f390f0603060d020a0b0408010e0d080705071e11091005060d05060a120c030b10030809010e03070b040e100e100e1f09021306050a020304 68
    0xc1da120360b034494040c0003581d0035030340751480305820112000d1000e01d241c5610742c552001008504030100c221004031108082e03064000002c19001942c07100307403a00c5240007000048803521504001010a80d000f027807010b48589075090a01c0f00e400600074450f2941c80c2c407201211aa41c00905180300b00c580f0744481c80305607640032088525501c415412102400d114407101c000c00c4078012070030b214510600c00038001c42c3e4000144401d450b4010300c0810040321208042003241c445c0011514091000c141c04030741d941e40d01022a042403803581c003c04042c8014494075040c0280e51440c0030a5a01ca1202498140c0f645041e8042802c20b9000281c4201000c1200950710b46c003865800a1282c00607040d1031046a556881d5007007078000c1d80c0301c900d00d80220010021424015051980a062050880041070411305150080b503000342c02001d0400c4081c6022401904a101014080301e2004c880e20b0130840e20f40c0b0a0f10065040b80b0108400c15604003004222540200142d480f070725050342c02103051519 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 579577652 1250 579576402 579576449
    0x1090e06073e03070311010b0a091a100215060f090601030f060906080a020108100b03010b1803031c1808030712110d0b09010b0c15040305211807 64
    0xb00300700c29414201c41220a01e800d415019007403510302101402035515000c480c100600b010340940e01c07560059160a100000640ea061507075401d881c00f002c07001a1a081007145655807464070b400c815440358000d84e5141d461035001580d00750128038913140c0d01490b00e841052103400403103000c1d16070f4003d95410000c0c4a40d48264000640301c0094800840c8103580c80508a048070307429000000030341c001a640006558002050907004600c003034081c1c02d4503203001c444003003500041c081c040c0440b80000b01c1c0000d1914a01e00100c1c1c80c40c0041c15246d84182c0c550003014101e4803801100001810300c03404c0c0e032070300c883d0010180e0760301e070840040b41c0355076560704c411900500c0355400452280e5076203140448044c540c00150050100d2503800180c2074980c003041094145050780030354501c0702c2c1000002422600032030264184020300740c8600700d83e1510710701500e0a00a00034400e0140f03809a0348110b610802d40c4205002d040442d000e2441c00c5001d8805030744400b2075005031003554407070340c41e030800480 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 579578902 1250 579577652 579577697
    0x90f050f01052203081306140904020901090b0d0b0901150804080c1207080705060603030412080304170c0d0e030c0307170c03060403050a12090f060f0b040f0501090e0607 75
    0x1c2d040b0007584504202500b10b8031003e149078000703490498001c9000343c040100481e01e00050501c500b4108011514035600d8090743c8110b6070303154026a0042140d031496405030310450042d00400002a03100d001600c10b02d40242000040d807880740c881c00d00001060070900d402200d18121310758443c80300380e4072506c90b100c0d5940000c0c3c04109a1043e800000640c08140c4007034240544a04603240d950810b03030501e145480005461a84680c000b0003003000f0110303911072845401a03100070b031140c59076a9418421219201c0203807100d250640040c1c0300081840206460707041d80317060703100d90350000705c158181503840c03c18421031a0103a000c1c0b203040c000142c1c0220031541001403141111401c51081010030300f424000e880032404280042440c5002d05c0c0c0184445c180b00080349070800c00130742c054903003003004140b940c4044c10860765000c2e03086407102a03070000d040c510b034042c005200058a44c00b03260001c1009100f001880e81c5030441d0b440d405200860058083e5102c1c1e42d65403840250f25a1603407118 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 579580152 1250 579578902 579578917
    0x30904110418020c0706022409120d0f0e07121b32090c07060e07170d080606041203051c05071d121f09050a080a090f050f0105 56
    0xc414040041e000900142c1410200440d0001503100c0f000131004902e0f209158202506640040d0b80d40340d400c291aa11b84a0514102464400e41c1d8441c0d06100c2d00307040316070084240c100c000061601c03580305075070401c010b05003801d14100080401c0156140d12004140107000c0315207104403512021a00500390120b403403616000d801c00f800e645001250a05100c04103c1c540f100b8810050750300c600c0a5042e41d0340c003500658111074030b0714140341c1c44122807042090041449070b441c49440c88a81080120744098200354091040780e00603103103030035030b116203007884440018200781c00106507082450a0340c0c02c403000c42800800c202500c0c0e405a0b02d039000022030340c12810a001030340c002c601c060b004407401045103032280040500814080040d408200d94000e0017044c200c0c1c404038182500260300c03082c100005040e0101030300da912070040035241800002d441882608141401c1c000c640000f40350520041d04c2c0e44c00007680e10b2640341c0350f1802c0c9211382c40e4007424113000e04085501580c02032080b07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 579581402 1250 579580152 579580181
    0x3120901020c0a1212020106032d02030d021b0d020f09060312030406150602060402030d1d04241a070303090c0b0a030606020111131401020307080f031e010503030904 73
    0x60401080441c06024580d130020400c0001c2004060500c2600450502d1100b12840284891421034803516108400d0040c4041c440c4204000642d032018480310203004039070f0080540e100c2d00c8689000a64400340c201001085000385071482410745807210b549010140c0c05029403005040042c20070460520003000c05800d4003c449030412020b80300f5008520483c403e40000440c0a42c9039000c0304d990b042c90b001311040d54006000e010141c0d40000f400c40c0c080041e0320340305140010060f0101c10002181003480e03040f5051035801031069400e5003201091043c200f21420045644203c0340d407600c2c01e0150041c4812400700100000b00b8400d4110181352030103101d08422607035441c810010280e0001a001e40041da48031001c4c00b50545c2805a66000e400107c4c02e9420144034140e12907103032241e07115141403000c1117a04038500d03074002d005071507409e5003040007542c0700c0362801c03481c858590080f03501e41d50103202c3d01c600502a00f10703255820b059800260007107050030b2a950a02000b001c010000080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 579582652 1250 579581402 579581413
    0x10c0b07030e030a03060e160c02041104091103060f15120c070f080d0647030708041110090504090c0305100603031202030c120709081506010f0e0312090102 69
    0xb2078010401089004415600003809518203920ba04001c0401b1b422072072509500140b00d110150f00c05c40300c403d4240c045400050b83d40072210408100d200c0e90344080b500310b04003044243c0384d041d8100903611418003070300c0341c02640d500f60003000307200390280005040d140303400c0c0318460803c1c003211445a400b100f00070703101d07107042c0a40e01e50750001c03044c8040c2294040e400050301100342010f07008040041000e50b44808040460180045041000300f41c45c400760074601001812440819032840004800032031615602c0c00e00210080c0320801c00ca80541e20030024070800e08960500701d401d650a91190364981d11024200020070000d001580d0040c3e400101070400480403ca082c400c5c2075400c00044c80c00101ca07407544c03030050400d500d41e0020032801841482000f480c444c503007040328442042c020b481c46c5244c0d103040c41034900180d030b500401c405104295944a01107040302c0f00724041c3c1803d1701d0315030701200111b0040b03800c60a5120502c0c0c160300f104118803401007900c070191a811105006481 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 579583902 1250 579582652 579582671
    0xe130b0c130b0409051602010c0504140307050a08010c0f02031216050706060602031803070e07050f04090e0d0e040510050120120d0b060c211204110103050a0b010c0b0703 75
    0x70321a040760f0010407284d5628010300c0201014201100d441c0206800240b0141041c441e01426074040d511410900242c00385c01d030300107550280500e90160000030240c042540d240c102450090624204c0030010a003030016542c0c42d01d0000050f00e055248100c0241d19542e103c3c4c01d0805100350480c06801880024001c42e03001800b140504800b03040e03103500035502c5503c0d6a114465001d001c0080d5402608060000e10000110281541d442a0141880c560301c0c030f18810007414520440c0d000c2c601582c80c1c00c000c7c0003039150205079488055856a0307140c440c0070b0790703004000444806482c42c80040ca840784081001d94059464190700c286100c08420270810040d01c3c050900c0d048072400c06840c1c0002403421614440b91180b990340900c10340d24942030105c6000c481e60b488038883c131108001c4070701241c9618800d103010200d41c04c2c0c01200c444036203d030800d0315001e28900310200c009400b283c1001c00041e0f0004540c0700301a900c0e40c050352050061085900c0d031883e2010080e090030201070b11a160304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 579585152 1250 579583902 579583919
    0x1120312050f04120c0201120b0a0305190b0a0e0a06090204110c061006050c03030f101203080708090309060702010302211303080109060b0d0b0414010f0e130b0c13 72
    0x381c03103403252207242d60051820345003110380c581c00c0b4810350b001d1201400080c130260b40e1020101941e40e0102100064400010000071104a506d92009003a0320815415018550050f4100950948542c040f07000f40d8441c1c1800b80141c408816407006180d101545081c042030040e013003040024000342000500c241c1a221080a5900c40020510198800740c14003051254483d8004020201c0e4a081804e01c4001550140c413480042c140c01c040c11a400c02060003d200d0281c2c000051004886290403c2281d260160142d4401c444910209001d070000501d0765001100b01d400d10a001080725244c1846940190000d400030b101194500f880d21030346a480c64031454032035001d49001084c8404541307003458000c2844005070071a0094a08203e010810203d4520580712240003118000c2171940389070303007c90b0041609002d15607665540c08000236030030a04280c20b2041e0f5462420820241da070707401c00010200d51107500180000058030000b260190000007410b11044480d602924559a64500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 579586402 1250 579585152 579585161
    0xf0603060f020c0c04020a051b03040914180a03090b0a030e030307110d030905120904200904061202060304080310031703150d021f0512090c030c011701120312 70
    0x9000350540c00203c58140f5081001010b03614030046405600e4000400b41c020000d00544403c0348051038000a1381450a10600c1641d010b016107a00400694000c0c40c2c0d141c0340141d041d620542021640c240341010071002048924a4542607207030502ca0354648584c001c20ba6204060107000c05a641007074121003041440254001d200c5ca61b0b0710451454125099401c0000c121004410716107894134000010b100440d035005010000440c0985401290300458044d181110706e2034484056106d040e0f12120291024007440201034808110306510f820300ca06145203030440295000d6418070014000409074002594040e94204c4200076a0741d4940e204c175140c00c2e1800e521080e004000c800c100820721f41d0a030b105030480c0100d801707641110a54001c9040340c8000c1003c9084c40d1480c04004141034060005c880511801400f0118207140c10000180c9507450b804616100e405400c40c00d108a40c1305500918000c0b6007400c0464807a4a0006100601c04024000702c0902041248119425590f80f04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 579587652 1250 579586402 579586421
    0x30a0b0103030e1806010302160204020a0827030f0a11120a171e0405010b120c190e011202010216030809040615051821030c0c0405070f030f060306 65
    0x910626541503103000340c01d04000300c00f258003c00d103524918444950b61070385543c02c04000e00340180d0790100405c0c2d10707512185084001c1e410600008038403514546c007482e424822600d0701001c40041d4108200c05400c0010000784500a03801441051910941500188070b80180c034201485206600e21150303003000c82c469541491301c50041270005c0456044014080b10001019840c0050f1070201500112a070b03503100044014548030300040c0401c4025130100b440c02d40010301070151844230404081d80c0780d40c0c25081e6070180480260102c41e034058070402c101900c0d0940b21107481a8205000d903004208410300590440c80b404414002d601443c0c5001300c044e60040f03604a5455401c0d07000d02069030895403004003e81d03c4004480c4030321741c0c803c058503d0198425010866007041e03e001070040010452281c1e4101080b100300321060b42c00000030400190a4400e8803c0d00e0072080400088810444401020a00010411000350b102c1c3d8440c5862080c600400500913440e9298101150306180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 579588902 1250 579587652 579587663
    0x60723010914010c03020a050a0c030e04020c07141c0b07050f0409050105010f080c0a0c261209070806060108040519051f090f080304150f14010509070915030b030a 72
    0x40312200d03074401c4c060408202c00701c1c1015450a030f803004008100744620799028080180b90131110702003501c2510326000012005009648030f0103007030080383d154146841859126400440e010480707041c1000c00e00e4494050040f041110411500c0c0c032504c000004001d0b204015041040041440079140544058103110500007a5581000000b4000c030307964045c02828400000208219210900304035500c0072628500055070030f5171403070242084210481503042d40e241c0410440b01d81c0c8100740284c80b03c01024030707801c049512001011501c2d1146e80c0145252a0071010014016500941180b50458406c104684100641854141c140c40000000701d503590050307410340c180c140195412000008a0450801101d40d50744d55440d0f9601400f10700501d0f880d03011000405100c203402d81e0007070803803800d80c0901c00052580c10034802000c5201c00d01e6214810385e40041554205904207510480365074907060341aa0600581c02040301080a21200701a105d170b5900030252410b0007a52141c0744505c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 579590152 1250 579588902 579588923
    0xe1203070602090d12090e060d15020903120418180b0106050f040e16021c080402120111120108010609060509060103050402031e030d0c0804030c0f030201090605040b0403080601020c0607230109 85
    0x382920560034005404144281c42c02c0c40c2c050085100c18980b6081c078880a42b0040c0d8914640010908202d5039040c4140240801708000405405015101d0401030101404100e2506000f1a80d103100c111220040c0a1000d080010b00241703000300e005050a0708000c2c1c10302cbc14196030304074080d482402103400041c0c0c131142c1c10140070290b404011200d682914501d21041d031140758a40200000b1000f00042e10941e010303590b64281c10700c29030000300fa0850300070000e6030b034041000091000079400e1048039a05e618100f40010f04201d28826803080e00c10041c1050030030780302ca000460240402074070603a854010703140404111401c2c2c4001c21162800000a562141c4001c41c14000301d401e804d600c202404440000c02002a600849a0400b107a224a00c4403a09400c0c1c00d007207005082d100c00041545141800b030200307100e40071308042d2107980309540f01d03a010750741e000c0126110784813500995000318040c01000300281403500254800c0550108201e101c9018080ca03500b074503a501026034120302035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 579591402 1250 579590152 579590159
    0x1203240801021210051806060408071e0b0a05040909020a0e1305061501051e0f07150b2d010201020c0d05090117040c030809031f0204060e1203070602090d1209 70
    0x200340090340c1c4030422100801003185030202190544050700c6403019280c02c6c1d9030009640356100030036a0003510b201c00407102d4142d10ba0450401c900001c0444990f50b0064081c009005031030f5200322045030407070b659036074202450400a00042d2403040000ca0f4850100300c0f0100f10301500a800a1040281a140110700000750408070b090803c09032a41315155080484c09801e660008100c0d10440b00e9448000b00c0c1402e600325a1403a401150040759194030300191150622464811101a4a031100380c204142921f01081010821078524110000b24000070406815070400c0749150740444180009445d0284201e800c17410104880f0b5150040354012490708400d59000ba207132410990016280407142c1090745401a41880030b10000309480d20024189449880501000480031035001e600d024865849085002a4007c0e000c0c140c0092850100504a490144110621050781c5c2c400707586050042e44070030010750301c201d0741c0070780041801745d450340041d103080c0344c0c44801403050340c0c1e07241000d04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 579592652 1250 579591402 579591427
    0x60c030e03010c02010b0a0902030c030f040c0e01030320160621050c182421040b04120201290103140a06080105250305100b0720030a120324080102 65
    0x82c7d9001124451300c144104a580b41ca82e004480d00700d542100201c0e82c40d07403130b80b80043c01260280c000903103100341c6000000070140c2100044810040c0205400c5490460f42c4840c4e65410f040101c030000e540640e0700c00c0013283d00950360701030074024400146090325801001c800c10f440c01903441c100140300005001d40230080c03039503494602d2401200d54107051050b10054034484044000f41030501c0c00c0000311a0131008810307580d49100301a85810150628140c1800c05551078125000d82e8001000030059050038410303c00c11f4511075814004200c6100e0000a05103403228114125040c542c1c0c40c03080c00603454920540500c40ea80d804000314503035007004103560940e100035101040c1103501000741001c24212440a81d084c103d2071a0000c1e2540c0c841405c2113580c130b400c0d48000c42d4240b00168101c00e02001c00c0c075003441e02e800b51520311440c0e90300c0700906a60350b0f444000903003107007038400011040c244290032100c0f05507c60000006030f00c080f1401c5032850034840e8080d25042c2c0d400201400c0b00310 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 579593902 1250 579592652 579592669
    0x3111e010f09030527090703020a02010e0c2d09011e050102070605040b130e090a050f060103020604150e19080d0804050622120e0127060c030e03010c02010b 69
    0x3840c0c810038804102c10ba034020389903000780c1c8109140880722240001407003855403068054400014480519401c004002030000c0d031080f04806c0055003031110f115500c01c40001c000488060107400b0341ea1405040c91210a4004030149070401d0010080740c2d0101542c4540c2054040c200d44003c07041c120f160020710741c00d046076940c0464159080b0140821a40703400000b554100d5080401d180c0c0d58052582d40762880180541020102c403141c0b60a00851220004002440c41e1003041101c07801c0da11079154a07501e1000340700003580480d0410040c0306c1020b100c03034090f000f04041e01704981d0031894480052205000405418498614421b003002003000801482240c44400e0030140201e0410381c4a00b5141d07080101100b411110340c1c98000003060358202402c0703086801980d448140c0a110f100101410030a0303c4080c00121170000c0018044070168610501ca0341e56110000040d14080e03081da440c8001d58029401e20181030030034526500c0a0180818020039a030000400c00d030f070a4108032420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 579595152 1250 579593902 579593921
    0x191703040609140a06050901170705180906100530040309150c02120a02130b09010b16020d0201050d140609010602162d09020304020411090d030c03111e01 68
    0x1142e400c00090400c1c0c844011903815174126190142d9200591001070720081c03407000c5803180804881c0c0402907144c0e80000a410304d242005076400d01300b11020100400c05030b050f21000e07400b046a40d03100300c0c8135000360000e100c080030944031a041240c60018100c010141074403ea242281d21100704002c041e80031b000035020f040140b008040ca520483d200822003010104000e00905e00d1031090b0ba200c607400c000c454060b9500802d00760102520030080e07070241000341080383c01850301d100003143c0c40e01d04400b0340700c80c5001c012046810004940800101d400300510580c14440304100e40d950001250140ca164804d6007c2c1107106410402c09200110300305903c50002c6400854214145c4403080c40c21004071605014059502145200000c401c80c444021034550800500c100042050f600e4009d18032441c02290100301c00541c52402e0700b03043c4100784400d6401104200c0c4140024003d100703c0e44800d0180c500b07032842c1410040014030f8021010300100a404003d554102e00c00c209010b03107801e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 579596402 1250 579595152 579595169
    0x7030203030603240403080403090f0621060e04080f04090207050105160504150815120a060629160203030c15090a050705011d10080f060f01080105191703040609 71
    0x10b5450900513051100d0302400c01800c0003400c0000c0707814144034a10601c080c0c0740400d0b0400000340e65582c040c2a001c502520030905664060001300d4282c4203100329400c407101080040100ea0356551401003551000c200d103d44100203010110743c200061001c0c049a5204500015407420711205500c0c3c100200c103000700400030104410f001540300240c0c40742c4280d1060034103c1c843d03207c5c8030014802c242e07805c4149420027009040450a00400544075240a0168404100c6d030f649500c41c1c0c0c003100d171826012034400c44105080d608522003800003440000300c02c003802e41f925180ca6001a056510602030300c80c1d594440301002005880403c1c80581100c082c4000b010b03410b00d6070f03a406407550158425a030600442c441104c860b52000c1100e2140400001e040404058009402a008540694917a102d03055110300060050900000146041078144c49014090380b0701410404140c2b80070240c0c8001c3c0315008c030001a210b0200c410003031415195400b458846042c090010070115456010105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 579597652 1250 579596402 579596443
    0xc0501051503010e07150309140f030a09090213141908030c0d0c2006040b03360703060b1302040801061509120f08251106090a120f050307030203030603 67
    0xc446440e0360340540d0041b2400c4c0881c9590702d0341000c1101c21101c40d0005800d0050a40c00d41940c1f0010000b000590040e8840400c002d845080d0343d0101d0180720440e058410411034180001042d2050080c0004d000038122440076080300b031559080206075004030451707132000c5403495481e201030000100b1a0042e10344114800195203c80204101c01114801001300309074100d002c5840d1081110041c1c84036642c01c590324100503030a40310329072000d0710707400d06100c10f00021a02d91001c4841c4140601c02d180040c00c2660070341c0c5540005280300b11065502810354440301031601654005040185403000000455a00d4a07480d000c1404d070118241c001c11011040510844000e14006521660401003103402021180381c1030b80d2a05c16180c82115514505000d400c07213844903101002d007180b180c6440d806e8847c09105009a50042da200b80354091001c91090021400364848000c0182c082c901117002440141c171901e00310b9010440a43c010380001040180034101001a61030442c1000342c0e08030f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 579598902 1250 579597652 579597659
    0x90d031a1c05010506180a0f0e0607110105060d0503030f18010c1205010b0c070303110307080d091110090b0708160c0303030e03040501051b010f06080f151003120c0501051503010e07 80
    0x203d07505004104a001f29501c01c3c6006011071203502080b100c81c00d4100f10f80720790a19201c041d0000e402c20402403815800d040000d685410901320580d85035a22000541c00c5880d1030451a0f00100018003140c15841603864226840c03409001f202e01d01c81d020f4440131400340ba0010b00c4e00541d0016042002840810032403031108030000136605003100c0d01440c148412982c000e4001d4250310490102900400002c1140344ac820307072070350201443d03a03c140008040c5075400c0303043c070500320000090300001c80d144401c10403101c450343c00140100b500c590107c9282c02c09034000035016403155503003903441032003c0e4401c0c000c06815108025240d03034008002d500301803400000820903c14007000c0040320003c2d03d40d004250409400050074104000340034000c660711500c10300e42d1041c0034110801c80703210f540c2c500300d09003070314001290141c0e200126034504541180c9401e12182e650490100410003c1c1c10100d011410a1050f41e02440c080c41c030001c5141c2c2c0b01e1042609485046a50038100d420550041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 579600152 1250 579598902 579598939
    0x10f031b0803070308070504031b051008160e0a080a1a18031806091e18010f170703051501090b01110d030e0307080c010207031106090d031a1c05010506 67
    0x1200d0f07035503040c85c01d41059076490000320707400e015507030000340350101c1494180c61000380c0c44981c0342590780507070300704100c107060803003c44800605a4648081c04402e494003004548500900300c03440b400074000381d01a03556503100d2803510782042006d4840c0d40b03101003ca0a64110341d48005c2c4c100131002d030350384030120034180d5150700c6e0b1260041000c5182d600c0720354225583c07959400d442108000420101501c030b200d5564a81d0090806145807107058040c00c4c03c4419654035280a042e108896444148035084c4500c60b640488031100d259254428080d000001036820001030a54440e9105c80040039454402c0c81802d0300d07a041e40300e9050103180d000b114041c500020300010014041d240200d503500380111358034214420f0f16070180c80d0010005800034109015001421410b209070342d800805000305c1d0425032121800c0c1c4551040390030000510b9420f500c80d4000910103c82011800c1c40d44400c480041c00040903c10401c151041049040b0305103c400c0c82400c0d40f0800c150344d101c0714902000c501c0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 579601402 1250 579600152 579600157
    0x7050a080d120b03010e0a0506060d20010513170d0807020607080423030915070503070f05010212070e0108100b071e05030403080c0d021207020607021503010f031b0803 74
    0xc1400704600342940b0095003410360404210701c01d0250080181034016820b1580302d402000094840d44100408146c3d44d0510240d078108850700b01c1400079a00e41308140c0e410b02c50094641090403c0f0062001c1811400203035480c00c000c140320302034403401c15002d014003414034440481000c01d00c01410b08004845402191443c0e01c03041924200c01e107039a40c0e1402170030020b541c80c42c1c0140e04194900e1003598280000040c00000b6040b40c00104036000140030601502c5403110081880d0414401c4a0000d2955841c50002d81d1040300054107018140b9440b00d04078000b00c4141000541d20144104c43e03581140105400403100030200d003503035013882e2180d6494464000000d1520311400710105134202000741c503001c1c00d036010003581c0d074580d56410700201c213030080740c03c480f614040c00520014a07800010030889020090481d030341400456000c0044a4202441c1644c000310f1012030703001d1755032200d002035000c0e01c7d881402c588414110b04040340c0d212048813043c004100841000d01071080d00005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 579602652 1250 579601402 579601423
    0x10612050402011e020a150614041503120e1503041e0506010605070f050609010209033c0f1e0c12100c090e010b0409240510020c1801060207050a08 65
    0x1d070903955100e00304c12454151007003000381c8040c2e410600380e40703010110b070820800c030b9044512000c00c284e2103904220865503140005848902036410410004030000c07007800141155043c00c0004c510502d020400000504500d612000f00000800041000f09803011194501d0040707040b1800d646a80c0710780e6280c3c0c041c06203006101c2e002c102141045101c40b52800d01613441016241d042c1820070089010b500304401c0c02e8400d0180c00d510f00a144034191a80025480400306c000109443c0b1609103440300c01012140d40b07c3c0070ba030640401058003003024440c89240264041c82200c1040212414880c00114042c80740090544441089000241d8510860307a025000141c4086201c002e8540204590000e83e603020f04400005507103130f848001e402201c8800c0c600388200c10030302c44040010071541011641d05000c180003130069080c003220300520782c1c0f11030046410203030110000844d0704606000007960311120304014007627a54180301c035800811090303072019001d5041c240c030740717444401000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 579603902 1250 579602652 579602687
    0xe0711150a020f1b0c1009051e0409050c0118081e1e03031e0609040f080906040e011703031b0705120c0d08070503060f280b0301061205040201 63
    0x80100e410301c00542d040f10402034022420903034440d41c2545a4011600101160120340100300c0c140e00345042c140f4440051114542d1950005421302c403c014122001c14403002042ca41c0d0510143c00b0f4031580304400c0d460b802a4020140e43c2e010400042144001045080d003110320640c00308405880052540d0b0140d003090700803032400c40a000c0c1e062070004d0b4031000040e0b11108074901c601c9007038040011806020241402d4400b200c40c00c0e80e020160702c00ba01c2440d00110103c0001e00404d04281c984c504d8648a90f01d03181c540002e80d40001d04a40083e00214961000c40c00100f25552482c00e8040303501590801031421031400081325405800c08249003100c1c0b01d8000343c0e40c2d0030410140180014440c034130018a4881012490b95940ea000d0103c0c81d03400b00b088007011070b49060140054034407030040180400c000345d00030b0042c441200d042c680c40d03003608600311041e01e03141814140820b01400c81015000d449600d13081009103004941a0f00c10603243c42c03c001e020150740c3c842c07203400385440c420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 579605152 1250 579603902 579603943
    0x10f1b021903030503090d08070e06030612010c03020c070905060108040f08070f0b06010305090a0b0a0e0304080d481a090c040c020f031206010504030804060206010e0711 75
    0xd00201e1500c0c280c1000e18010800411408810144c01501950180081000b01c1c0d040c0c2c2d982c100160b442210550320a000305501200b1a01d00d454100c1c011a44120068003001d2103071480c0c0c1c90035080d24a50541100429000701e0400d0040c1810030540000704003400f030902060802c40000b80889002403c05442c10741e16090800520000e401291400ba0380504e2103c056003960511043d145000d03074400b400a4100303000314031510740000d2403c8103160400034900461710768203070380c030002d12840c000b4007854081404002803045003804003403d80301c0349840c3e821088006280741c496a41d4000b0700642e504215010000c5219580c41d1002907400c9040080e0320301d5540c03070605a03101c4411690303030140c8441d5041008144480812121403100c0196414011105040c100381e17101d01307140e140e802c0c003644240210020b540c1c030350300c10700d80040c0181041c5180545a450f60890790740203401c05000b59205400401210007035510080e4044c0701ca15119854510f4074101d00e8880300c4000d403044441d81c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 579606402 1250 579605152 579605207
    0x17070305060a0e0a020418050609150102070f0e040b010b030f0a0b0f06030a090506130f081b030f2206170709050a08060f091c0815150c0705010f 64
    0x2941c02c2100505080400d12001d4a009203003207020b0350050042c0c0d4980c1203040d0200021040c14042c030380c00380d20002c141020b5a030f65040440341c401c511a0703100f41184608040000e13105402800341001d03140350900d44246107050300b0000e001c90b4040c0d0000a42c003000b0420880c2800070003c43c036810010818011807004101800582d440000d0009141e0000002007404411001703a404500300f10f03c40c42c25290940d484c5000441002507500d806082d05448a07000000141302d0401080040180d10b00000d00c0190f105001d0301d1070308140c00024201400054168664403030010405070615002400180c20f420200010903900d82c012540da2a9000711010410403402420064003600010304490006561009000c0d512031080e40c80c64080b00c0300c8004503440b0b20300442d01d01d50303254486504020f03980d01c4110440e4820b000402543c0d089094181203110b0f541d4800e5200000d4152542d800e032111301d00140c0900f0032180b40d002a040c001c400350815050f43e003249040e007022420f00c2c0b0a446181c3c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 579607652 1250 579606402 579606409
    0xe01030207060c020a051b0d060213080f0a0c1215020307120c030c230708030417030a0218191a04080706020a15050c16051e0f0d1707030506 62
    0x225407004101030300346103003040032990004240d203080f400b800c200c0718030041c1021510304440783c0007c9660040c000e405114085811a00104042c1c0e0708040e40d107900c242d40e04549400d02d052182030011a801000d040020300a030b03068003c014082c0703240511410140b030b58a05041502686501d201240c0200004030070034042d0031008d000c02d88a8405208400114600130020080081c00710041410000e13200041d0740f1f800e501c907041030046c240107490711701140c6a010603500b004004031140d041e8501d8104a075407910300950b000300a01440507882d9820b1600450030610030b48003180c02004500212021041580084421900341002c2c5070803056034451140280d21498200c86c140388192940000d6455002641e182500c0c02180d50041000702d031000e60017526070595906d681c3c440140a42030f088081034030b680d50500d1040d4103c8422803d000040021400000282501d40d0040e0320300c1d00c00c0c404188015084101c680c9040c205400700300d00022080c80707020340b6a4003010b0ba03500002d861600e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 579608902 1250 579607652 579607657
    0xf041e02100e10110c2107060e0a062613020a0b0d05010b0708091306051309050123130302160e06040c05070b3111040b0f0d030e010302 60
    0xd40140c40c020381d500c49460054a4001060881d41c01855025038000c03103648604403010300400e805015006810000c4c0822402c0c503100411080c4d4064102941005450100414001450707162180040055071004021a41205a21410070300c500300e542030f000620b000048d08544400340040e6040c50710707001c0b0760080282c03465000a40090404d20042207414209002d0914040d072440103000b1aa2159030449a50155503001885490306000410300e40c40e1015410070300e200070034400a01136a0310000070380703800385a4540c100b5156482c4d2006080c01001e0240c0102c8010f00303042c0c00f13426000020180d0b2406001841c0c41080045407503481c0401d4030a20074801c00301120760000b00b0150b01c2c2c0c101d0312610310301610036901c198a02402105d8035402103090fa40401d4100b41d003004036590b8903006074108840702c4181e41801503607070a9103041040e4120702514480c0242460451845800240011a50024003680c0b04690b03010310481540e5070aa4101c03030381e07581860a520441e0100300160042e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 579610152 1250 579608902 579608963
    0x70302061f150503040b011403100c031514040506090601050702150c0105090d02070617070e010909020f040918210203070203070311010e0103060f0b0c1509150f0f04 73
    0x66503480440c1c1c1a440f00c06140100c0c0116000721a5903a02c1c811002041e0307400b058250141c0040010100503000356101e204400050304000c50311007880150802c0c1600543c120f680140c10b10100d00d1604d0805100303450380040c3c140c590000c1820f00704006465406603020003407254024803040509507075120292144c41c0202c500070300880c00c00904041e2140780c0c00e04248014440c554000540d94498028904640c45001e0000781680b1a5081120780882207503001c1d051041c0b81900045c0145513100404280310030f19104d54846050410403026148040c42c600307400d4544450050219a81d00c8200d480c06101102c0c50b040710386e00d5034041c1d082d409408030280d418028440c00009200103940300842c1d86a099941d0100710300f0840064048030910300030000b030510307000320a00c4121444e100400343d0403040c04c212169201d040340300025040048803100350b144c101242842d03401e01ca0302d140c650400001f246039600703854092409000748400400140800c20360017624022805c8172000700504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 579611402 1250 579610152 579610169
    0x102070c03060e0f030901050703052809150306140f01170a060906090c0f0305100b07050724050315010e0409061d0a0f02090c0c0303070c0201021002070302061f 71
    0x801c0d500d06200e40100054048403802d03006140e9420958140801110344091050311600e05014054404888a400004e1401c61700c1d110420051840c13000003003106d860407501c0d510304520034213001e25558814a100d0390390040c103040c18800d1126081c1607401485140050f5031512039840342c50012508130301c40900503900100d0038001e000c0441e88540220064540b40d407000c0c003c450f528000d00342251000c03000c080c0011103015900c842240300e600841c3c1c10101c2e501034480c042d605ca150381d5082e64854a411115540710740d03406c100310011a4080240541040c11800302e900405038050329a00c0010210f4100800018050009a0190032080d2000901074401c0100315840e10380304005002ca01d00303140b0840000c0d03014159204001881c2c5c01016031100240000b214640e0a06c500400090441c01e00440c01b8001c1045c0010200041c1d881600d80c0e50303580f60360340041c0c00064280100040c1010302e19004200280100c0e4000070300d5500200c010412010090312040a04908081500088031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 579612652 1250 579611402 579611423
    0x2131e09031704061506050304031e0905150306090907050a0603110417010506030618121c090c06080609010608010e1b0a020c0a0b0a020c12030d0606080a0f0b06040b0705010207 78
    0xa00040703030b0080114a2404001c5d000340c0d030711050181d46500085a009000803058002e0301074440c0e051004000c00b4000d07090905c942a00e400c0052001d55040c01411080c071000700c10030a00b841d281251581284c0140003a00c130050900e0049040c80d070080c000c403024552036401780103006006100319402080c0110802d40340170800b580e41d81c0607190507260248284690008640c800355228000c00000c400c1c040189000d1418082c3e21030182c1051602c2c0042c01100e0421500705c2d9414040d800890703100f98480e03e1000e0600b50003503c40d04002d0072280c02009828014000f664005410b5070650b1400c0e21803c90f25508c5003031039408a200d118462221803004141078142c141c000440002c140c038111f51101c10a5140c66003510b850003002c46820050b40070306820300c120b050600d00c0d61212450b0b24144c07483c20011000600944246600100c000340c041410000300c02050703c07070020222883d200a1190802010000d10306000b10b001340826508001000e01c00c100007581100c25040e030141240c80c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 579613902 1250 579612652 579612661
    0x31320060a08010602010f0510120606030b0903031b0702100309080c010e01020d0b0409050c100507240e190201140c01050903041a130e0c091c02131e090317 69
    0xc2c000d0784288100390240d800c3c815001624122030007040d10540c500039131840e1440c40c2170304e5150303444071050301503455994400010011600f0552020320490300d900041d5503a0810b4007824089810340101062500c2051004c980166207204514501e00030714580881c0d100700504107820248182c00c0b4003140f40d0728000d0020b0030341c5010b4019000d1082c103910708201141d1280c1c103000646812000050043d0480c0036046444d144c18001180007181d1841c1c02814114240d0300e0030841d0381c404c00c031074a00c0b440460040b0161002401a0500380740d80201500780002c0d030002d0004250305000009040c410310b00111040c0f5010103007a60020480ea400034062400d041c2d81094699001d03014585a9251140e103101c00b0032421012034882d4116141e401d040240791003040f00e0500380103000342c800003100f0013003110b4030741d244200328400e01c0380103141c1c03590807169104110101e1051341002c200b40341041e280050320401424402c900e41e040c0c2c00c0114650016140171100c8000c142907003200b5503d1407040c003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 579615152 1250 579613902 579613907
    0x203101e03062f030a061d0f0a0b18060127080708160e0402010318031710060c150209090f070f02010b210709021605070506031320060a 60
    0x1402140c2c01800100300c0d03d1000c414003410065180250300c410008019000380b022014401142c1c44241c907000001d0a507220300d151002d00e030b203101c00002d0340c02c4040244194020b189200741d800c8041c0391070030030030100c0c40c070040f60182d1482c01036000c0c9422410300040e8644d0103518130040d05a248001504458242142c1190010890059048900c40d00902051b00c02c000105205174051082300f4103209807901a0004007034100034005c030704140d110800074004592001240c03030003e20035102c1c5022031a221901c41c505040080c50b24403600d0300001d040001c1508062030001d410b07081204001c00c50707907220185029125a06656402460113002c10181c80641d031803042c0190702d195a400b01001c03011004030700366002c800102750f0094018441200980d61001c0122607506884252182150b550118000320303004001c1d500e130510707000040c0d441040070078002c60029141c11141c1d9411414080c10325200c0142c0c440006040784d2040110b09518500700c501c107902c000d8001d200d69601d10905000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 579616402 1250 579615152 579615209
    0x3020a02060d090c0e090a0b1e01150f03091104020d110a0305090d02030712122003060a0503070311011b06051612050403081f0503070306060f06020a030c06020310 72
    0x1ea840c01800c1c44c020688010f542005030081007020b00034540440c4540b03480002c1d61000e404e1001588002a80040b4a040314050314000c080b051110a800360710940e0141000840e20854020107107070131040c10004600c04808000800141c50041c2c0b503010588600c0000c00300010040101c0501141041130a40d0641140d8461881141551038005815106036500d00540d031004001954585271044940d10500382180c0485090308082811580c10402503019050079141510117000001002500d00740900c6c58401424183c0040403550b00d903884001d10000070004442c100441c640880090200b880c440c40d054070342084040107a400d00150ba8404072480514160100e500d10320103a4040c005803082c0d9110b5070b00350f12604030076921a03100344540c26440c041c40406401c0780c040403c480c0ca042201402551181800240c118140504d001e9001c84a0740001c0c11940542d1035030740026840b02180107142c3c0d0140d405a1680c07919152428501140c1d042001c5410842c1d00c00c0b010703403090504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 579617652 1250 579616402 579616421
    0x21507090302130507091a1e07140c100c08031f0f06081005060307120b0105130b120901020c100207050307021003020d0e010516080a0b060f040609060507150903020a02060d 76
    0x455603444e5a07180810407d1000015140c42c03895001e000c41c1d01c40042e030414104020015002d594500390940c0d80b600082080e641c100303e415481602c01e09400c0c101a00000480326060402c428240c46a5841000303c0c0f0000300a064404159240072040d0344451030005c002d003034042c81c2d4903002c0380c603028001e21104080b2400518800c1750500040e250034080103e900688950380c4000301014140c4000300030b03288151070141000300401c001c001c060070404101f4094055902c400b17a032144180ca03000f82001d0058000303426a48100081c5c1a007040000b9006001c0c1101100980c4400860401c9030440c02200400394000106041038100b0310b0780b550041000002d0b100e1300300300301e41680c03100908855048074001901071100d040128464000e0300c0c50381d0f0003052003202140c10a0468042000740c0c1240070046074094011034103000190700000d40e1000361419191640c1000741540700c2090142510702c160070180c1d038400410f42894070030302003060030580240255540310170406910006280108 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 579618902 1250 579617652 579617657
    0x705090c07060929070216030b0105010c0218091509030306030c12010204091e0f0c021209190603020a091212050705104104140708010908091002030a021507090302130507 75
    0x4404c1031224030911fa0365002c0d203400940e10b01c2e4680c02c0c01f00540741c8039034003d01a80d00c188880300c426001000000001e205080841c09400c1a041c94401d4210680c000350403951240c0043c03042041a0702c000524107649501110000350106081c11040d0080c0300d284c00510205d0b080694640c40244103441c03180d03e8400d43c1008000d051345582c001d1040750203059405005070464100f040603e4281005840c145c2402010b12082d500c03140440030f20701c1e0140e4400c402007038000c07800703000a58120099500034a240f00810403540110b0351581e0200e1054002c0c5002e100012640c10300707000081003044a0b07001c640a04106041e20141205800c1050b0350454011041120b0500d0100300c02c0108050003490044007003071141c50302d5450480c41240507100c803000d8450848001907040090041840c090701600030650303903082c841c0c203202059200e030166009652003001140b00b2141c2c0000c442030070b03401c0404403180c1500c1e614011900000e280d070010303500034000308005509c00400d0b0310907401940d054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 579620152 1250 579618902 579618913
    0x150d0b0a081f0c0e0a0311012006010b030a0e060708250c02100e060a031a040e0c0405100f180b09070c0f0f14010e0705090c070609290702 61
    0x1c035103003980c1d40c2182282071840038003140c040c1100301003a0040d0782a000d2600305450b8091000000c9880c085950740143d880d615246015510355800c0703000c2d8043d03020f450b0070078401e01c0d0b60b110160303559030010300c500c4001020020010b00c40034a40d40c80340c4409804030054990a00380014010244001a00c0700c5100b03483c45181c01403081c031302d00d03080d10b01c0b14a10348400404000f641c003000140c0882080703440074816040d040c0c801503a03c6200501e84800e0039240050103d507040c0408409080e07525905010b13929000c0c0d0288020380c0001d421740703007880458000ca41691001702e05d42a6403440c1e4490590700c10446401b007880c1c804246000760b00c09500740f082011422040400041b020181c8030b03540492902d800c500f01040381d0a002c121b049000d602d40a84a864990b80c82c0901d5003031610303100d9542d40d14484000b002c18107220450043c44100c4115050303013032038076421406104900c1e00804071541e80c0614410009600d5841360716154007a110066054070b001c1d008540342044038144e0050188 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 579621402 1250 579620152 579620159
    0xa050f0d050c1c06080705060304050f1c0e090c07020d02041b030902030c0a0f050105030903120106050d0f060501050d0e0a020310051b04080a14031e0c0106090207021c02150d0b0a 79
    0x44c840c590485903e00003c0215901d44030500509a0014100780d45c0781c0240e1525040d130290800907042440107082655048034009140207059030038260301140b00e28078400c03d00c0f40c1c0201802c03c2d00c108030b80480300342d907030003c2c0782c030010b0001c2000e07a100e0100707514402204280160154001000c15000f40c1c15962024040d504200e00c040ea103000343d203910a407520003803149522a1000e940d001000b001100c1c9042c42c1c10b103849440c40400da21900015200141c4001020ba00307029100984d0f110090600c0b03600d040c140041c14134014208459002d940d508100c4503140b00c00c000301483d90b5000b5007510b0300c0052341d595840c09841c00b240c40201c0c003d94482501008203a04088404035034450000c1c003000f5000c0d0f40e07442c0300e030305c140c50194800e031006001c1403004d101820f2081c005142c44102d02c56858a042c1d0f411030940300c1c41d0b031001d034445106001d10030150702ca581045100411500d14105e000000d44009640f500810701c60950b01c400c0800c0e0707210020340310344c0070721400341c2c0403100345845665 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 579622652 1250 579621402 579621457
    0x709090b03031303080702010903061a100305090607050f07021302030a05090325240501030b01120c05060a03140108010c09170c1e03010c080f0a0204030203030a050f0d050c 76
    0x2d03003000c20f005110762003001c00226000c0e03000b0302142c0f071051408680300d40d40c4c0c0e254401920072000640f0b40c948032a50102ca024034041c00b02d40015211170905115518040030283d443d004010194410301000090700c03a2098208021102070079030013000c881c48004070000358002900100c81d40c1025525140110701240c40000558001495a648074031010145020b00440820341100071100400c43c0da1000424082d41c0841004281d1400d40c0010b8540c5941440c9154090607800414a0910f60006030041141c040c1d40405491050303420955a02d526a4110014406e852614203101152400400d150206410000c4d00c40c08640d140380c0201e8444500c44007000c411b2289403041d500240b020780a5080008a024013000f0300890b03007907079089420103e030075251840600800100230008003d4040b1103140e646c0d40198110404500b010300b19800309560f0300c614003c900500c40085040781c500c4030440c0448d0300c28100d80105004505250840642d2500800c6100ba801c040502604d8000754 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 579623902 1250 579622652 579622657
    0xb031006020601080a1104020409022106011407061d070807030506060901050a150c050609010c02070815010e130f030c060f05061c1104020a02070501090b0712081e0709090b0303 78
    0x424150180840c000c40707580300c83c0c1101e0003207951b40d082502030100007030281c4036101615403940452001e6144424002d43d0300e03020040100041c1c10320103012070078100f4072000c0c0144ca05041d4808130000740005800b079544040d4180014441031403040d01c0000c07a40040106540e01140e20900c1110305070f4440781c2c2002196242402000c2c4c0100119500300b28189440310710209504090a00d0704140140741c449908001d4121103440e01691211584400c481c2c2c1040480c2c010302002014180020300c440b0403208030601032041c43d04c1c006401c0c001c0b038160601d07001c840fa042940420003441051540c036016060341c200400c01c0c2d412600d407101c0c40d0480b0b03c0078040d441c8515002089401480d00e01c00e005c1c40300450708103080c0c1c1d842c0c042d8423080c0300b130751a0340c401858003400540040100c11324045c00140382c04000e4101200b100e80a20121002420b908416004400ca030704105829035549442e03070900700c007402418889040c9030014000d400340c001d001c06090b5422490300b4080d0250340c0040c50f80d00d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 579625152 1250 579623902 579623909
    0xa02091b03060411090301050a1b0306030b0601230304050d09060c02011e122c0a0c0e130f030909060909150911030609030307080709030302061b130b031006020601 72
    0x880c0400024210b464194060301c139025248410324246609100881c0c2101c03412251401055500d0303000401024411994400382510b5190500440382503540b039a07015000644131506000e04480c041c51000844850500c9031034440310001d86078500340c1005581c5030f5882c82c0d410046000da42000c41d40754070503c1e07a403d0b2190180c42d1b11030700000e0f107824446140742a0350348201700700f801c60034520040414003948242c0b041c05101c040c4814003084010280c0650005807200302c0d03002d0309a0310001403c00e401d1400b02c40c0a0311241030345544001c130503003456070b9810300102610101c54101d820190450348a00aa03000c0460400a02d44c65603852401c607580840c0140141c039101e00e0030b2201c0006900300c16101ca1140c0c0341031440080b00070110386403000c05d40c0e0000240e00048108218264802d16859000455181426906117151400f03034136400040c10031640312003403250101c1d10600c1501216154140030003800700141e681d650065081d00300341e0b5101030301c94001c000000c0d03a83c0b0000b00a41038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 579626402 1250 579625152 579625201
    0xd05060910062c03070609050301181e030903080c0307060510080a14161517060d110f060408010c02070f060801052101090b0f060a0303021f020403050a050a0209 71
    0x5458100f006085501529885030304640208001c09007584041c0000c10061001c1d440e180601400e01c03042509444020f483c0580d8400030000702404151424980041c0d4900c0c1e40c810b1004040c54101140d85a404d80c00150840200141076480458000000e09682d07001c3d00c800c101d5a00e0750740d1148451081131003140010f6000042c20f5011444140c1c24502c8110300c3d40444044c0540d15840051502082c1e2040030303c0707000c0710020901917800080c0b0841031a80d01c82000000d10306100002c02510b0780050142860700d40311100202511054985c00c200c82c0000e105980355640c0b2031460340607050440c4080c005026070080000e4140320001480141c0c0e42e03945071400181c2c24a4203204958503003005c0801855608450010442c5086c4074542100d40528682c2450f0720300a41c403401041005002c0b01c1c0204075550040021a0380407500c01840701c407245042c00c0c1d01d0f070207110a1001c1d01480c0c0028015004003030609013045070010300000b40610980d0401000d60311003001d2017000250f41c100c00030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 579627652 1250 579626402 579626417
    0x30c0203070f1508061f020a021906110a020102100c020a06050c04060e0f180402010207090204090b12030a020a0b0714120402040b0d0f0b04030306080318010e0d0c09110f0d0506091006 81
    0x240e01c403141c0d4015003a0381244125408c1c2100c6030001080103103921200350001f0a00c050500c401c507800f1301c034016881b018a00810f4104c6890740000d65a24a9a9000007883e82d02c000080413140709100c8c100c00c00350030001c180490f0800b005240e006a000d4820798010510034203803804103041c80703403250fa88900001d007410452808144001005940180101c2c1107005000000c2405845031020b00701401e00d200c00000c0c0c8090000a01c1111003102c407410150794414017500c2c02c81036002600c85291a40301c8091501903d4062040da01d000401d8501c1000e06c50101d9a00c201f03104401d222441580211018001c202c0c0013802d018000b60690b02c0038100300e0080440700e011510f140307070f01c0c0d4000e0702c00e00c0c001441950796103031181140c00011402c0b24020781e4000d2400d856a0200404400910869a1540c15600c903654003030a10311520400240948032501000c21540c84800d5031004c0c400101695590405503035032030b000300811515980b00b44c061001040c0d503503a841500c83c09448042d1110341 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 579628902 1250 579627652 579627679
    0x606181a04020325110c0604050d030f02030f18090f1003200a03140705120c130b100807030e010b0f060c0a021507020909030f03070c030c0203070f150806 68
    0x60343c0018103004040c03128140c14400c0140b00198207071140c06503500c000e0021400c2c081c035400c00c02d6018940c0d1162009000034003280d0341b025408042a40d250500c7c1107903110104040e4114001e1a810000c44400800c643c0260316025000480b06c038030841d5105820740c1da25124078035070882500d144420800b9010184006482112030030b10001c9610700e0403071b1680d51600007800e030480d02d40044035502c4d050748840e148400d0822407071002c1d003001c4941d10010f000a1030f942d582c80006000c80d512544074481000c0d0300c01c3c032917805604c041710060038900340a100c0741c5000c2d2410341c065505000003881c149000d080c1c0c94041c800c00c94400c40082c41c142001c40018100141d513000151940d81601030703075000c140140d444940c17449403101d0409a0315100c0302c0314010002c50640091008049070002c01c200e0f0042d540c40030443c3c7e4481c0a600b072130942c4800c14181242c00207000140250548140d2002080d42c081000507002103899400301417180b481e4000080341e81e95415038142d0f420110502401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 579630152 1250 579628902 579628909
    0x2190f0b091204030606030519030f03090318060203040609271a041e0c08010f15050c060109050109110c0c06030c07020a030f0c0819031202040b070606181a 69
    0x1600070320030004840e000740003011421507a60040d80100c0d09943d0300c48040003006010300090740e14015113940068082c03032075100901a1412010b040c001c15a8800c140003c05014100d909038031a9040f02c201a056114180a1365907805805020701041d40000b0004541c840304141984540d2034180301188106481b248a028020309102000c4443c1030382c03190070383c944491040d103580c6040c80b1401c00d10110402140012940d65000841c100704043e001840740c00c0e0b0300703042003048070780070405050b106e0792412080320503001303c5441002c1801940000510007074035420890582d0740303881c0104000409880a084188076031103140034160404000c403030403850305002440c0c1c40010031201d545000140c1c1e0006050f0b4404d03420881e074031120480000c052080504104004e444010001e240a00100004400c80c0100180c0141045240c08000c4082c1b03013182c054500514003500071507260b04807440d0480250050303005260b030f14016000164200740040c050405001c1c1488504c181996241051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 579631402 1250 579630152 579630173
    0x140f06060319050c04080a0c1509210611030906010311010323040c081207061107020306041101051215010305070905061b0f0717060a02120f060d0c0605070302190f 72
    0x40130034883c018000012040018800803403030078419000b00c001a41061480400d000c000c1040d40e040164010050107080b508020082c0c3c01445020942c1c03161070280f5003003010300350b40094070350120008005d000c03501500045590599101d4030751190800d4804004404690140310022560b0728065441020700070100849904240144a400b040f542c03100d8080c0d280c0b030510504007885a41c0000c040301400701074841c41c1c1000b0200b03552640f400000d0780000c6d546a1014102038001208503111030b840b42e002c0c100302c58200e2400000c09880349440f01200c2c3c000c80e06001418003103814200056006849100d2210503a40000c1c1030300d0400a20745907a5803540348540030f12980e0300c209690788012000c108405801840c0504070300b0500015007205608000c8040d185088080c0184003115005020440e007a030b03c000310a0f45400c8583c3c8000001c3d0533160f001902410702c0140320404101da55004c0010401d1601130340842e0802400c0d081d00c0540300400b494044d14000002005500145035100c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 579632652 1250 579631402 579631411
    0x140f040e210a080a0c02070b0a0306150306090b040524060f04090b01182303011b0203030a0605090f040f150c090f080303100e0a0f140f0606031905 65
    0xc8810412410051a00c07101103001c484000490100b0040719550b845681d195204036000da0600c010121490043d640d40d03100d000d9072840000100741c03800000c2c440d601c00e000801e05183c00341c20079022420042c00a100d64054201a20300b0002d246803141458098035000c4d0407684520000c0340c5401c0344100c4501d121540715035018008100085d89482184c000e08080c0c40d12660018491140d880050410340e0000ca41c2c400000c0341d142c0030018030082c9104d45400d03c05049005040081c0da0300040d0042c4030030500801d8194950180c00030050b0700001661084014032820054036481714100060003a003203804100000940001a0000d207034509801e2800d071048c80410070540030004900c05440284200b040020b0742101e00f04003a1818800c42002850010003842c59824071a03042c02e600c006d42d0103208008207240e00030912414040d40420f420f4142c084040003807004a40c8440c05901d81074824490071449040806e0b200d1400c003003224020035981403a13250304101a075030701010b85001003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 579633902 1250 579632652 579632681
    0x41103030d06140f09091203060a080102120403140408060a0903050c07080c130c0807180504110c150c12060f0a0b03070216050f0402161b0609140f04 66
    0x801200c81c070981c01018080d00c40d080d900c001c0b40182000f40800641e4030f41c1c0140c85446250244100c60302c001c20300e40720364004000a599070f43c0da00f002041442201e90300a007035640c030004007030050070200e444850003940700350f40328002d41024600c0004103000c0c1e401084801d411041c00f283c19075055501c4101050f104c2d09000e410034081c42c1c641c604086140e400366070303160071803014104945050001c0c80ea810f900080c0400c043d18060b0310040000b42d00401c07120911079044501d1007249007109606005101c0100140304072030b0400100180d0b0741280502101d1381c41050b031111350198001c60b031248501c0411401fa403c04811032001621644c01508203900010340e50354aa0641d2191800000a080483c1010399a401d06420003450300d4100c041101034844446000c4c0b01541e0b61144203201d0010407540942c45d116030750a0840b001240030401400045104000500c150204110208031080c2e51a42202c1030364810100300d200c0c2c60400c0d29a80040441d014006038030340ba501a500305034508 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 579635152 1250 579633902 579633907
    0xf060c1a010b180603010e0f1024140322141507121418071e0e0c2b0e0a03120c09050901030b091f09020a050f0904110303 54
    0x1806000c03039040003a0016150742030006400e103008106003c0440c02d088050359498a190302d44032031011025000f40c10300c0c50721074200b00403602141e0701a005402808480820142400e005807000360410702d12107108003c0313928004015240b0644109403881000540c81d1301030349021851902128541c490401c40700041d41004250315060708200c05600018000b5400c80c0a0800280181107034603030a03280d0b046641011843d208d04a4802040e503000750116043e1400e13903540700106803c00b107540d008080c409003c0f14415004422404d01d0f001200c014030080c402035214401c000145100d07132110140c3c40c0029421581c0061030140844162360861880081d084d81c00d031130a81c0c10810400c00941c000f60383d032000800f0b54021031140e184055103074100405503618160201c2da01040c144809420704c0703100f5000409a03d0301b031001c84104244030020044403280b65048000401031548140d000307480c0303503002181c54100020512103004008100f0101940c981c0e5540d91002d850114558050205 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 579636402 1250 579635152 579635183
    0x2061005010c21030501060306051210050c071415070f05090d060b130b0405010f080c0f030a05030409140703020c1c030617060a0f0c09031209030f2a0f060c 69
    0x41d07251641e0f0400595008030b46945811801410354615070003041c4550007001000000701000142c0d40301d4034048101c04113455403042201103648c0a4581c0180881c00f850b542000755038400b00c1c062014a4159605410a4590080440d510082141d07070101080040050440301d10302040340600d00f034866900410341403205e00c04100340c0064010012141504c0d81c0025195292a0050f035014102d260501a111454101c0300d56071141e18445160207a01030784a10811f54078240044100d0359001300441ea5078541c0c81a04a00805d481c000b41c4c0c0d840c0d0071140104407224070034002c4480c00c003a10001402000070604943c108148280c02c5c000601d50f481c107002507034410754102c0000440c0214068210361a2112005041d00c401c014400388191500e800700381319a070003103586001e48e80c100b055031424044d1041c0507124402142c1018007030a240c00000d00c01c000c2d40041d5004e4512250f9040b8140069900f00c0c0130040c6601e01864a0501030900180801c9100d03107040816103003d507410805083c41e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 579637652 1250 579636402 579636443
    0x212191b020a0215030c09060c012c010506030109030543030e06070f2405040c051c080f09190b0901140c030702090603100606021c02061005010c 64
    0xa10354842409a0070950789001940780128000f000f1020501586140d89000e2000d1222803086010b11403248401103503010035810254000c1c9900001503c00310b18820100705041e5071183d00d08501d4034190b0a02c400a40c407030a040c051650b480e40e0546501d41841140c140d052880b5400d8082402c0c889280d003d00c1c03d01c1d42400c07046030007255040421807622801420010401281c5040c45401488200030b64000541400114141250000b030032441030121841551480241c1401c0d64071001e060206100138041000800cec4116241200e003c64220840340a00a803004100d20280070540d0030b008e00c1d801803000d00c00502035004018848038500341c1032403070b4600080d4190090300c84004082034060265030000d0f45010400496000a800c1840c440102a036070300c614031000f07000d40c1124001c142e131130700c081100441659040c0400d1011a0315104004d544400e0f5010b0000030550084846406900100d0001e00a96240c410310181c242060015201c040703a1000c1100c0b40c00c0031480e40ca00011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 579638902 1250 579637652 579637691
    0x30f03071b1101030f05090d050c0a1b1d150402160203070305010213060206190903030204090518010b010c021e0109120c060201051b0a0e13150e0a021219 68
    0xe00c210080b801c1c00b16080001403c8510741c010514000d45040c003803020741d80d00059000c803213080624000e0307038604103610790904040e05d0398070040c10200c260611914140081a0440030703141990410180740c110310142d91007844054400b44008404401081032600b41078006248a4004c07200080362a10b89501180c075142c00c550060b50030341d6003c40c1d00e9001161045001c8001e010a02c01080f05060076600c0c4c0c0c140d85420344600b05d510340e40c2e11084c8100740c001e805503402000c1002c4104038502d4000704288400344941c8220546510b401380100e00d81d070017100344052568001e4604900c82c1d0380580c00b8004081040314090500c401e04c0c50010f1548402141c00203d40d10509074202ca2501d400406425103501030894110500001c2c105442d6002c180b0548200042d140f500b19541c3c1144800302d9020703a010031154240d5400c003040d011100400010060446800c01c4000c078482e51204000012809115501c50781c540504003c02c07068100c1a40c0b40074505002c03107002554198402d02d03c1c02c1c85 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 579640152 1250 579638902 579638957
    0x6090a08010f1a060d02130504020f070302010e01020a090314070305031308060105010c150b12070815060a120f030302090301061719120c050109080301080a020a17030f0307 76
    0x1a0344072015420103002d07501030f24803451030703101400070501c0c04038001404070b00543e001c89107450b501080c4241c804002450308801040094801c41d91004000f2000c0f2641d4080c460a07030240d82459150510302c1014800c48038101c0382070740c0344c400e00d03030455440c0044800d00b01c9540c54148911203001c00860001e00041003d08a0768648410b82481c0031066810442d050f44014144104c0d00282c101040807001001d0803140180000580f9501601c001910f1007030860201c0010700c111000421070750310009280c0c808420001c02c1c40c40565038442080b060141a0282e01d000740f000da515100054041503540c2c8045200c1c2c14003605041c0c1c49001319084039a84e5021034504203e014840b48440402d2000707030a40b100400003414048242d0700c0d0403410f0580b100014040004000c0d001080c404c081d4000e83d0303070b10b61000340240e5035603403002c40c95604d46a10303005070303c610040d00307000802ca4803a041070107504500c20003542c14120780d030381704003210b4000510210520214105060618038541340c4030701c00d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 579641402 1250 579640152 579640169
    0x30a0e04090b13140c13020702120604230a26070f06020405280e0c0d091202012403030c1106070303090b100e0117032502030d0503010b0d0b06090a 65
    0x140c070070031308000050305400c69007041c55800866603241d454440480308004140c440e480960fa031806480451424000b040303201e24603014082c20f010411001500c2c6040e45860b46071a50b8901c05280c008980f10381031144000c100b100c4400c000003070001c41082c10b21070380c2402c4100c40c0c1003010b103840b10821421700c1d43c41120040e0380007030107020310b00d00805072084501e9000c9000040c11f0483c60a549049900d000314107480f0320794000505041d40000445a603160520002d111940356460842e80f01114250340b140594248007040301d2140001d001d40002c0c01d83c4850707000c146032440d10301392100150224181c614102c01c2d045c040c3d050301d6000080c1544c600c80d9a000640c4100307402c00a10500c3c020389030355190850a00c0410586039820f5005054a02c0070800c41c07041c0020b003000ca4614411001c06030310b5107201401186c90901d0141544001a0082c2c096410710b0009140031507182c03000340035200721014280900c1c6102a0290b00c504a01d58001e030140c1d01c0c0c1b20305240060790340c1d2002e9001818 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 579642652 1250 579641402 579641431
    0x140d0f050715061a190306050d060906110c1006050306040317070509101d06210910060f1403060709090b010e040f1d01020a090e040c05041401060f020609030a0e04090b 74
    0x4000004184405d403c1d1703450304111403410400012a0b10713100b05006032010751660030410a04c2400d40c00340d00b040c04400b515a42d20345511941d640c5804e0b840745041040d07403600d200014207045c04145580714a40c5a50748022144ae0050038503076800000d41510b003003000a20904019444401d61007400c40301a880d001106901400c29003012071782c00350224001e9801f03000b00c4040411019131504a01d401a2903440e02d903850590040c68500307807843d400d6142c3c0c00e010303002400844c00305d01c080039103091420301415a0b5121051613039030345050301d07200009006407400300503207002070b40583c008541c1490524107040054000a080d10192942d00c0f80d91a681c01850101c0035080d010f410440e00a03500031341c24511095405031400c001442080c2031044060002420031080801aa01038000244104424202420f054500e05407d00415020034030078011082024000034005105103c540000c41c0703001d091b49012030302800c0c07080c111600181c403450800009006440114400c0c40300e05140f99 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 579643902 1250 579642652 579642667
    0xa09080f040905070237200909010216031119050106051201060f0306050c0c0a0b040b061c0210110f0c0a060906020a030305060f0d140d0f050715061a 66
    0x45441c06070105007951b0207991103200480c03602402010201580070602c00c80e05e004050400c404030040d400511041c03846000d402030104407aa1045401401d44618115603525942c1500700c0c884e80e200c044c068500d120039000043d214080c414528043c10040d0b602c042001c04100d04a022a85400c03511a5100c2c242032095003021051100c07054003410080c081c4600e8001441c01404c99400f0150400303480e000000e8420041004640c425030904003140c07000720050500b10242c01c0292001c0700c0306000c050115200b46400c80a00b116900d0141050700081880d5003013058880300c1030710f150184071520144860014046c0300406001c104107001c2c00c43d034003c2e41d08004a025283c0c00c02400c0c001c07142820b1210030f038000f840d64900359050030700040a403511000595010380340c030f50320359100e00c101450700100409240e02103000c0e07400c1021541d10700640301042d5134080511558200041040c00907002054402254004419803000b000a00c562108450500a4549803e11058040024140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 579645152 1250 579643902 579643919
    0x5100302120a14160308090d0c060f140319200a090e06062d120c090405090105090a0303020f04050904141219050c0c032e060302060a080a09080f04 65
    0xa41c10302000301c026050b03c05113515204240c000c0703400041d01040022078000301c5a15400340000703100703070003491010000340d03965001010354240506503000628070101008541d1010701c1500e018000002001d1210001e01001e1801400d20f55420200c1c4a0201c4001c10300401103c01491805560b1341d8184660b405c00071010417000024044034001c402c1000403005840c5e501550341420701075455851183c048284004c03245000d841802c550510251050010b600e00303500042101d0364040d14240015035441050074200d030310481d1584803c0c1c0007402c41000107482070b4000c2030700b9403002000c181040e8444c8040b45041d08222411500020408005c201c1d0310000c010f5100e61203c10380d166031a088032804401030f03903171000110700f084c0040410300e20700441051280c03000114010302240d1303140a0f8850b8206450190750301c28503541c0341601c9100080d120798000d403429250064072035840c0c6509440c0484607400001c0c00e180d008c90381c1d9040d400010765503000a1550a900003002ca0303e490420ba40f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 579646402 1250 579645152 579645173
    0xf0e07051e010206070c0c030b0106030b0f03070614090612130201171017151005040e01020306031b0613080604030f030b0a05150c030d020a030e160905100302120a 72
    0x400c0d900008040c0c000907141c0e40001c0c5139602c00f80915140c400008203290030004040300da00000c10003c1400700100e000c5074183c0c0302c844d12a008444600042c481c49050544503107c41c040c07030380018081d4941070100102c890082004540c0600310610304050384491000c0f4000690301e11000c04881582c3c01d086d9a80183e400a803c41c100c04004082d050103100c0c1825511144140700c1d441404020710901800240030aa40b88002507021406501e04a030f02c030714415007180900e40c400d074501842030b09801c03414801e1701d10915001d0000c003200410307841c000d40240859884550300c002c0811000740900003203802c00f0b0091171110010980c2c0e083c62b24002c4d100d14544800401007603c0e01150301c002d592060000002c9034801d5801d40000d00f0004904180d6100d8042444440c2c84001032020302c5c80966070042c0104003050fa402c00c40d004c000364100d9214685d04809002c0c12030b541d041400030700c5056000c2c0d0f800080a2404102d116580e5010501d00344502e403a0f070400e43c01c03000e0040d080c041125207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 579647652 1250 579646402 579646429
    0x60801090b011a1207030209130501080609010608190c031a2a09041a042a11060406020c2d071712091903050f0d052a010f0e0705 57
    0x3c44000c41140d0414029010381d5814202c0c1034910b80201d510503009904541401e8030143c504950641884a031070041d01b030a20514909201d44030000305c0d805c0040c0304103402d454142015205c0050342034182003001a0200b4240d400410048000002462407482116007880305111159245004141c1c080310407880c0741400660802502b0041081c20400f007100c0040c201142d0001300c4209017500f50746040402840590007501d0464102c3e000c24081100d00d07035448420004a9030203583d00401c40d02d400d0380500f400125406000498000f403a117801510f8121219002c844488241030b100c0240a400b42c0c040303100300002d03a610b032031003108217103d080042c0400e00b00081c901c800d4142c120390349400700c024101414402191000d156682c00c00609400460303c141c441d0021703203034208940c50b940e401e02c100e2545d110700340c101580300340904103607201c2d080b00e001d540d0309e031920000012138018400d040d40d0100d0355035802c0003804c039a0503124400f12100c4040c01409400e01789018002203400e10403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 579648902 1250 579647652 579647669
    0xb0a080709080a0b061e120109020405060f0904030f180909060e060105010503220f11090f040816141b03010f1802151204060f06061715030c04060801090b01 69
    0x1070f190804a030820140c0c03074000d1015244182448800e180040800b4507020103560700c8908118490640c2c1c0054001c00a5607008a07810881a00c440c8100314052080a225680010f00200060082070040e18402045071070f030b003819036481c00702c968028200c1b8080e0b08004002c0d80d0300d9020005002c044e02c214480d15140000400080d41014000792007400000d0180c0004254004460140c0540c1054010304580c08108410242200d1601a0074500d003007603268010041000003401500307400288030301854200340b240345080484880e0940002c5a81c9044d00c00d000d42c10700b415001c070010084405c4104001c031040c0700400c407180802d404d554102030419111404d060816807800d0000c410484ca85504035121900a4040e8034103002074025111b65021000140b0b08010502c0715981121200180b00348081000680700da1068451500c3c10b1203c2c6002d1203c2c40000d1008101010803031071201c0020111503440e034101c03001400f566026000f06c40740d65102c2d01c0d00010000c0c256411409000d0b0403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 579650152 1250 579648902 579648913
    0x30705031623070e2a1e04030807150605030a11091503100b0f0901090902030d050711010305150a0b040e0606040b1e040f0e100e071d03070b0a08070908 67
    0x480c85035030f0fa071041e00071410219001000b183e5855012031817902c900c20824110f2903004c08465900324103801071001001002c248440301d8112503001c004603001c0d80d6100c20600e080c2080d46e2903009041881103910303415955078460104c1d05540400569034128071031000d00b41410544024410b460b2400352264048200c0401042d501d9500130500c40c5002c5900c54002076558001c90006030302d25000030146403c61111000401d0768411600080840c03402581102c82c0d030000c419049035203110303d441c0641440700c0a00c244030b01351b201e5080150420501c402c1441c407a40290000380303c041c2c0f60340c0038074600784000074204481a001810a0380c80380e811181c182c14107103050303003100303103171042d804e00343c0c1d80e42c1410700c0440c0f5061080702500c014003510015080d43c55220300b003a5108600603900640d581c0200366000a803c444480724504c6440300d0760303400400315104091183c040b00075125403a81801208004102600c0e14006800f11b80d0320355a40403001c0c108950050144074044c0c00807840ca4204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 579651402 1250 579650152 579650213
    0x120109110307050d031407060e16140d0b0a20071b12030503040c180204050f04090305040b1614060f1b030412030f06150f03050f07050304050307050316 67
    0x3250084004136801d8200410550b04c45d50351001c00b80f058507001010103160504c000035402002030701c9c0007581001001750300e940361503201c1403841c0700c01403c20640c0301c184080c401c030018140a842e56000000c03d000802e0800c0780e200156004404644040100040031030303a4010b0001c0e4000364620032940703505009445041a000c14015160410060188107000011808001010017024002c0000c098116006540c006140010354403502c10030707100d4030000c80d840b5900d140030b2140381262a41511110300d014500042906150420312184401840c190074030f0020500c04c6551041e001004d0f005848903140c2220900104600a000c0d40038100c642d10303400030200b0b083c000f02c941094111543d0680700ca00c814007100541a040280c1503030074201440090400c016000c0828451000c1d2120658010810422411a5401c8a0704910f001103e0040340a841c01200250b401a0148044d83c0c60440a40c49107485e50b0301091105d840900c81d00303001c90902c41814a40d114005040c0601c0820640 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 579652652 1250 579651402 579651409
    0x109050415060f12060806040b09010b030606040e0c090c070c0b04030f030302030a0b120f100c020a1101090f0311091308120c2205030708010606050406030b010e12010911030705 78
    0x1d550041034184401d1408441d20f240c029800d041c000711111209200140d141d54400b901c070f14042c0d404171140752090021400c4510103010740303041241d024004145640c4c502c0c00b000040c0c40d06001a000381c0c00740c00c0b203402a0303407500304050707216546400c0200d0f80e404880c41d02004914040e0b211120110040c0014000a01c884151404076509841c0150305c03a110030740c0c050000c0800942165000710f490b4110987c5010120310750181c10514810f4541d6000c07010140c3c400c1e03940c190040f100503080703070441c480050100206121409010b140240005444010000958141d40c200791000f0303074051098085850310800c0f40350b2050403100e50f081026010380d203021950041203500024000900e00160030800e110007034030100c1110a25190312658500060203443c4454040d1074020b0240e5900840c00c0001409407008a400310342c0c50514041c9040300c00c400921401041c541040712010005c450350b65003401c41e2181c42c01d01707070000440c0d940d2403401045041240036018042e0300900000c0001d41c0c3d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 579653902 1250 579652652 579652691
    0x4031e030f1103040504140a06050415050118050405100f08281104050c0a090b04051f03020412080306040c0e0907030c02100203180607020102190e03011e0b01090504 73
    0x611820620720815a03041d14600750301130380e00320f503070070502d80015403080168045060f801145c02400402c1241d0311134003480103031078140c40004030342c07200d9410810082d403080480403a5540d020010415180e00d40d0700003000d40d40252401c5042813081070040c0207a84102641d00028120f5000920100c1c0c10500c0140d1040c03041b400321590101008000c609000d000683c0e9108407034010010030451070325001a803600c0c1c00446031200010320001c0045070040d80a000c64060302d000a114400d04c080e0f0381d468a0700c80c81c0b280700603400c04d502130000003030a140c4d4403101200d8074881c02d00740c1e0f107a18003101884101da41351340180080011603501002503444940b50706811500c10700d008a00081c42c07110a03854070842d0042d00070054400010410713241c01003135141040c000d00c00241c4401c3c0e01c03480b100300e09074000c1e45a07501c00d662800d4444144c15001d00c10b0114681c1020b000850002610f030642d8022082101200c40c80c180c6801030a203c035a070002c00b0b13801130007080304d0400140c4c5084214102c03c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 579655152 1250 579653902 579653927
    0x3030105012c0a0303092610021b240c0a0c0602130b0c0f06090d020325240b190b0304061e020901030b0d0b070e060f04080304031e03 59
    0x1c590048000320645114003042e4020207040c0c02800d0f5924500101618802c2c0710b204440346070003c10b603e040200c425801107003444400104507484941c0a8131009600404d03980300c0003400307400d8622010300184844500044400108800054002c0500150040080c2406120003040200d040440c0d080440c0e0b110481d00140c0058a481c0442d464060881e242c2d0810740a00b0310104102c038004900042c041820303e5403106940454843c4080d10303559000382d44032500580c0041c04828400440f07600340c4d0520300702c0402c60820481683c0c542c2804c4841d0f6000e03100b007030b24841401c20095580e0740509032001c04180c902c4c440120055260320924002c3e03014021143c3c000001141c2440f00d10f40004c071314940e5000103900c844c0c90a00c60440203600404400340840c1c01d1000d81c02c19441c10b818000b4105400846440065407114002c841541e050040680d100c2c10a110341c164048141016101031f00b40c00c00255640e81c1541003d10424100b01042a030a01c0ca4119080c0004d5104074101c008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 579656402 1250 579655152 579655187
    0x120d050f0609271207020a050901030c170a0b07030e0c011e0e030102190206010608070504032004270b0912121012110f030109030801120309030b1608090303010501 72
    0x1600703115980043d41c80c000100a00320302c580c1440d400c0c82c0fa225401400340305d10850f642e07032280365a20107020244c41c2c01d00c005804400048c008001128080d0b6541c00300d10380c1101030350300c50b500035a50002140c4094804400199444c0c00c5440121410000c102204509003491602c010703140003020700c0544409244410080c03180140c03961034500b50143d60003d513014428105000030000003d40c0e6480034422200014800c10205502c24000c02c03c590a9070382020080c4405940c0508034041d440302114040c0d0090794607d04c00e801103400002d0010440d80006410f2203051840c00c0000190101800c10081604020710301e00d0564462000c46550303401c0c0038103085d5141e40c0c025005c07001001c1ca501c40700380240b055006904101c9111007000705a4412104031320226040414107080320f40b88400200810a104018010114047d000040c12032091426030116500d9584603406180c00380ca0501d41103031446440007045030844d0609521130030030030045041d903250900003030012540c030661802 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 579657652 1250 579656402 579656431
    0x306070201110a03150f030605160305070c0b041a090319110601060e030a0507030b070801080d1d0f031b0127050906120607020a0c0801020c0c130e120d050f0609 71
    0x815081702604030005101011071804080ea8030304105020346801c80b80415a944803070000c2a81070f0092003980d028841d680d80301d02d101c03540c41d900c0b40c54804c0701070415508042c0302c2404100000880040500c10424200507688400484051504d00d801c210802024020000c68112203000300050040c1101c10929040600a02c20b101107410100304071000b50550013405408014400b0703110415004005c2962240d8407607a1341c062854481c0c04100092001403658036141081d044600b0148118640051481da07011458400180c0703000248402c90040074101010702045607080040c13100708050b1400703c0d0100248141e01585101d40900400d072180e181c40b00801c030300e030700e40c1c40c0700040400e41c000440300c8030304050307101941e02c2503a40c070100d80c0d8903540240440d4014060090320071080d4908004c1c10304220311f60030000e00900751110790407017a80d0b031f14401614490230054001e000c26940340d1260345080024150342a181c0081c100c001a003180d07c10300074a80c580014a9a10a10f000840e02 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 579658902 1250 579657652 579657671
    0xc01021b0603150612060a0506030603032212050c03060708060d08030c07020a0305150c041401030b060d060f031406040c0b0c0a120f030515061c0f020a0305060306070201110a03 78
    0x407180d2064801c1a001303440842c00701c10103500f158405000780000c803800c0d0000b030b9484042040c148030403214503805070001c0c00001264800e60800200380410b44944040b40c60301c0f03401c1c800f0000c400c60804e03655507100182410450900380f10780c0342c0140261801751224682180440c00038184804000d250f4240000007e0704d60780384200343d401d0542c1c028100c45215599007051503072410540c018031403c0d41c154000c500719400714411502180d00d4070000d45454201ca0300154028041c0880340c80c0c2080c410000082c15810034841ea001401003030315900c2007981035060080c100d003140d9a03540c480da0b1000307041c00007045004201c40d00300c1c0c00e45079502356280840855141411403801c8010b00351080b00070310035001900000c4081c0c2003050b03a41c0410159491300380e04400212114815600300c0da04110799810258400740b00e05003122000004a09600e5189201d4202e80c42007003e200082e6940f020302c40301d0701c0c09004071030708035410744000d001c68a4030011110951281c0c1c1080c6050680e00c2c609003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 579660152 1250 579658902 579658921
    0x3020609062101140906011d0f0319061401090204080604020d1a0127061211012001050a0c170a15050d050a0303060602060c04030303020a0e09040f02030c01021b0603 73
    0x1c1e042e0001144144040f07594641c4040f0f0003000c00c20f002c6200f8103042001995551140d032010408801030384402c0c4001c04400e051010304e41c8000241c54040c05462062828048451049a4028801c68000a84091442d8420032009041e000401100c1c0100010040100b00284007a007140d0102c60f8404040c1151030004203002124112581c64800340c80001840514030304c4844050051100c40f5150480070482e41088034a940242e6418400e011494400300d007001050303448159040c1841441a00c082203108000a203904201d401030307440d80c04003c3d096615000e20090004c40c1d0505201c0100301c05c0c80c00305010002490141820b54034040d192851140141e00740040002800c80d07110034040f810002c1d01ea07a903007542a40843c0c1800d1000881d40d2000940364415401d0300c04150904e0304590702100a9401107100380104a4030605801d141d503152001c45004e10b00c00d20915100340d105106044c24141090381550540d0030401c07000c540c40505070140500d01001b101c40350781d2685c8a42a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 579661402 1250 579660152 579660187
    0x17070c061512050d030609140a0e011503060e150103080a0806150c0304030b0609040c0b070501060306061508010f06020318040f11132c0a140c220302060906 69
    0x20300b0404820b01d64881804000b0454600d0502c2996092046c0c680310904034080d90501101e080c80111760754000740400c4110351001000718500d10001c120204210104601041c242c2c000351a81660f45c05000c04113402007148030044460b5440e00301c010b62454842903264003450600d40240030510340011455a600740d2000109054040c840f603c8119142c5a107a03260020b0100700c4081d004040845c0c8070b40b03002e9032058030650344100022401f5007000c0103004035401c0f03000c08031680c0d0340790207004c00043c00da0300a80b4060014501d4440b07000e4502a030091a0401c182d11000e84254443c1003402900d0b402300c200d900d0004d6100403c87c10f02d0380800801c00a010256000050381c0c0751070000051882403000814410034010b0340201c000340c803480c02c00304c81c05007044401280d00c0c1c541c0081584000b050201580000c0310303200003410440404500030317520742c101c48460020100250321107c8580030a285800c401007804190011425680420910300c1818401481650041405d44c81820107020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 579662652 1250 579661402 579661409
    0x6210609171b0f0115051005090411120f0103170915030a06080d050310090e100c0305060a0e16050f0d06030302010b1f080a0b0a05180717070c0615 65
    0x2200e40e070316992182c918005075006840241079000c0c41c0011418207070140503044000c82c0500d4410a45031400e001c001001c00c503072881c00c00f03000c8107000082e01a40c40b0320074050031120385080300b0361385d100305061008140c000400806054403054010700124206034003042c0c980c000440c10a54600081e40051000c04000400c0c490287c400400c100303c05101c1d0b080342045601210848001c08084041034805010440e2850310441e865581040160466040100d0781075800080c0d40c40352141c0c0702e0f40415240003040c2d100102c0e4890041c4445401c003044400014004c0c804c10304280d05120941008020502101104011007c50208060360a080450304018403840040007055aa4540a80608100c174001032081400980ca402d021003a2183c4011000b5159161001c07651004522001010300d01106900181c0c00345010071a034503070f0362468a0b07402d41880c0c0c0d6551231a0620000301149072000151648405950a0102407600814104550b6500100209500c0001c0c006000820f25561 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 579663902 1250 579662652 579662693
    0xb040b120c15070b241005090108040f0609051f0c0e04020f04170703120305091c140a03020415051903090203011b180602120901050304170f0a0306210609 68
    0x203044c00f1100302030b02402c0354179580d680402e03042c200c241001c101581109040030f5002c01c41c20094540e05600c206486a8400c0c4651481c840c00c01719915a107045401051040b211940500c40d2004034010041c04030400089005042c017080b00d09850080c1440c1b89a240d4600507500030070001e056807882d00941e0040d00c0840c8241d00700c0c1d180d036040070341c2d60b460b80e10042e40c1010b940c82c61011128402d000380c078810030104000f0006000e60703100d00602c1502c0844141c0270000c1c0d5500c0d00a03138043c4507004103000420f030395000d6100c50409001245041015925500380101080408007182140e2b00400c849222801c1c001068030241c00030a024001b4a08095503c03007207140b80c9180303240c00c02e8000ca500403000f0312403400d440c2c4407242a6a581303022241809100380c00c0c000703200705620883c0116030051250340c29440949041e03040300240c1e0060840c241e440c1301c01040700500703a54144100c0b00140105e40c8100c0741c0001944040301000286480a40803645a20646092180e2482c2d40c034a00d5604c0d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 579665152 1250 579663902 579663923
    0x14070804050409291b0c0a0b0702010b1203040305060c0c010f0f0c020f0714120c0a3002060301031716050319080402030607050c0715030b040b120c1507 67
    0x103241050414820821110700007034040700310700c1da0054045000d0300c110305c060b180c0c40000c0039410500c0450b4010040152051095440010005400040c6680540b032660004a02c1c88c040604004804c10043c0c5c1d54038555205100400200d540010100c0c2c00406a0000d42c3e9100c071a1410030740034088040500550034101090b005452046511490651520b6806d4a80011f810141c3c5629415180b1512030880090440e906d81c43ca13007200000001050402129444104103020819601803a0701000d60352201c0d00d5140506101000400c0072802680340c580100d10403036000403800d02040c00050080380e01c6a0744071030910310a000300c4d02e46040f400c1243d0100606031400b250760398001c0081d43c800c03182d014200b5503103600581c1800c1c007480d4010301900440c0e850500c00c0711280c0006182c01140c0c881c402000030700c0c1ca45000c581900440303c0d640803401040d24014401500c5c8540030140c0504074200e08018040c0300450220707030045048421040c3d1214007014140640600940a00400100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 579666402 1250 579665152 579665171
    0xf01090c0c120512061206010e061c1a010e190902060403061a031e0318011b030503040b01120f0605150402040905060a1d0115121e0f0c140708040504 66
    0x50701920413420a4142c80600e80d41d13110512a00400da50110700142e8000300042c0044464034104a9010340050b11803181141c89501c4401c01c0c04000405440940d04000f4121180541880003800b411016503110158248229035045031160020900c0c50f16a40b500740d0b9046545003803c41c0e00075a00007909001e1001040c160452482c3c0000140c1c0c0b0174402d0032049a01d03c2d4040d101c0e024501450030240d410010300701d4044040070311403400141000284481d207100c1d1004c07c031074002141c0c003a07617400752a450315160881420074180c110388a040d03444200807002480f501c00102003554420f07004582610740c5000412910103414600c2d43c043c3c004100441c0c694015401548189411201150520394844460008544220502c1542c1d48208014441036a0304101c42400c4000361418002038203003241762004998590900d10035414210705e060045292070f02449170180003241d81046036045610000c0e0404c0101c0040044584002c200e407424400144290b8004020280050005081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 579667652 1250 579666402 579666407
    0x201140117160513020d062105011503020906040e162d03020108180f150a150501081620060106180302060306010c08220512060f01090c0c12 62
    0x7011540c40001d10070504005680301080185804803000500110100d80f1060721110103580903038018007250303449030000901d845001d010542403940b41c2e10158110031741490300d6425901c6400d81c0062070381c43d0b6a42400965a40310549410103030848001501001008002d07042c01741100703200c1440c0d0719440000030900c0300c01c3c55199a43c440d59800070b022143e00810303518031003030724000030b03000500700b0700022404400081364030f00d5942010100d075060b0805003001442c00d1480c40c06080d007a4442001d003e00920180607588044030407000d40300c0c050b410a000200301920007440b009924100d0116005880d0044e145020800c1245503458000c0c1d8842c200c15a40310700030701c00c1800107000310b800c21600d01c00300b06200003540d500800c100c0c610f03141c0c2401141d8003a0880d030180c5070006d080040c2c200c0c2051281122403100020741d054804545032204000a100f03864140c00025000241040100d0b008288490f055807041040000c221542c01c80403502c1c0ca10860740181510100560f21040a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 579668902 1250 579667652 579667679
    0x901030b03011d210406050c19030306030b0c0a0e1311041e1703070803100e090f0c1519020c10031a0a03020121110f0915190c0302011401 61
    0x40c19442140c981e0401c0072290000c0c030707004c1528500c2d40e46081c40107000440c80b600003072205555800031902c03c08a55201201c06000c500412004a991480c0402c1008645c0078219403140f443c1c40d2250904000300005481e8900c05040c403481044c8440517640c801e010303940140c070048000b0501940311034480400d030f0601010b2128080000d015188000b820944e02c185c07101c07072025004051801d241a81d075608005420290800c0715030b1b00c600c90041170301803518060300c0c0318940f100700420801c2004481e0318180340005032000e00407d5164140340c11810010300311807412104201450352081c00740e000700e0074690b075252a0340c4c0c0501c03a29441c0303034101d82c16001090025501c124541507812101d0030404806030b00e2000a003c6008008051088036214140040c2c400100101040038201910042d0251340401c25991140e2004500860300d4103002ea80800481046d540719890884102c880440800020202d101000175241104040610030f4008001442c00e40440c3c542550b10358100d6242003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 579670152 1250 579668902 579668951
    0xf03120a170a06050a0905090304091b090803032e08061602010507020c01141e0a030e190804030f1e0c030308130b071b020d03051201091a060901030b0301 68
    0x45110118402c07008502c6050100c820052500c10345610300854140909001029403005000601c0005907112007406074011642d404955035499000040300a440d20507990032026a590042c02000b4000c1001d40c154410700b40e0401e02c800050030390054008030b200c6150042c03506030080301c007402414480100c18180b03001d07441c1c000b0b001960304d4120881e0344000a031003a07800220200161a248240030303000704040f08001420300c0440ac14641100c0f0542d0044001c00002035035408904031820b003d0103d0b4903894038207040d00c0c02e01c0c0415204c10300746010350301002e0858044200754404100d4007029548040740b40e55615810042d4a00b080054280f50b0300c0300382c000c150680002407207510380424011503946d00c0300310810192100f4104070f070314401c1d4800b405014000c140c41c2c0030159440c28041c40c1c4942c0302e50755503070f0703106100d281085000303034182d100843c03160800015403428181c500d00c40c4107640058505c10345070256400120041c003030030900d60f6010352030a181c0640c0a1491101509007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 579671402 1250 579670152 579670187
    0x90e01020919081203060117060102011b0f0905060405060f160f05010605040e2b020a0203010e030c12070807060f06090203090c090601051305060f0f0a0f0f0906020a020f03120a 78
    0x30300540e08200440c881141c4047c0062080c059a0a4800020318000d030400810301c0001400c4c0314440981c02c0d001c10404000011074910030340b044095501c10000030150100352a8070b4105881d01001c1642800f0302c00c04429004000700740d8007011020644010141c03604450070400040c07441c18035500078900c50051078012820140d0803031442030001800318101c90440c1440080f01c14840c9180c0f05a44002003010450241e890035001507070303007401002e107008408000f03940d03a061031820441c5061101e50f030038085400d0602c02d0f0004551080103a03000e076078001e031001c1804146a03101c10000c15460300070000c103e1011080c00048100040c145800107001d80d80b130107440d102c49006480900030840c2041440100b402c01340314500300400500701c5032540480311400c10118004101240e049020f09400041240d440120307002d80c0001030180000b400d040c120006410510002d4507029418400380c001c01104400b0110f45d00e040186440c180f08400c6d15031303109d4044400082001c06140814140c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 579672652 1250 579671402 579671413
    0x31b0d1406040c170405030904020a030515030a05071703091003090b10050f0d08070b010e070210110a030203061503010f1805090a0b09031201060905190f090e0102091908 75
    0x1090800388519183d00e19540c44000388410032014a010303500e001001118940001d210551154440380040d260000c520f8030081498508807401543d000e2141804610950248000341c01184010400304183c1d001c00301b903503078001074021406c0e165100e51480c442d041001e08601c0c2c03188aa00d03900401000307103d09400d42042d00d40038044100c2c042c441c003070030754810601c01c03520619282c010b1500d188184114401800e205943e00c8540f52003d013640007442041c40386007044501c580c18000300d1000700f09000104007582c075101b1099094041e03410160141540040440c01541d6290188000840b142040ca641ca41c0c4038542440d983c00140304002112007044c03807142514580d0f00420b03200d920007400170040001710740c07a064407001c005040e00049000400071400b20141906005019204680b104074009191100340304440040c0c100884040402000600481203010380300700c2100e40300e04d0082552000d80d1a4540280709180c5441d174000101e1800426409403d1881012104554155034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 579673902 1250 579672652 579672661
    0xb01060f02102705010f020c03070201020d0201020f031315090503090a08070812070201050f0d0911010201020711060906210402030c09130609060e0d0305061905030c06031b0d14 78
    0x9507542003104055414282d4840c0c1216002c0d02c580c0c1402c0344c01040041b40160740b5142010403030344034900500d034035000020240150f580412018291a846200031031802c0c8003c0b1403030389a0b00010f413080c2000c000a140b64014844030003101144030f00c00901c00c0081d00400c1c40d08903501c0c0d11070103005005282030600015441c40c0818448122141840038124044090109540740d90000c0342c12814064148048000c0ca400200642a21a40307200f00085daa041c5090074000c0f80440d48085045a00400440c00002d50001c1e10b11003403501614101c0d1290500000a581406000103413640c0020108075070849078207204170207001c1d500a8095aa10149034414020100021500306401000c050703a41303030024041f0b40c00708040501444000810018104485080591580d401d10000f9121824820140340240c840d5913040703200000d000c6114603000201342c0751440030041a21540307010000541000c0c054101101c808090b0002d41e41d03481400b064900103100e50300321004004032190015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 579675152 1250 579673902 579673933
    0x60f0d0f15030201020304170a05030403050601050103110f190e040c080609060406030c1404021b0607030b0f1818010905070f060201063c1d0604020a08160c0b01060f02 74
    0x1d00c190b0360113901075480c1a08201802e042078482c242c070481203200d09000382c80852000d0010300081c43c4501b004d00382c1549000e00050a0b00c00c03120300006035010800c0801c86a4652100b01c42d020b4044c1001038440c1d061411041d00c2c2c0820b401c9005401c0350a021002070003e42c05444a4800e285c1199038405a0f124001403100322207a038080100101459003090100c0008040342d00f031000801030000d0b141c254003400310300e4a42d00c84058060a42c1c085010b1001640c0c06010b07801ca0504166030307110301c0c10005000101d00707d4507040c1c101c0701d25a1f10000714040c05075a40c83c24800298040003800103400d1850070719a1041c440c85625040c034604000400c02610600402c42120744c1e0b00c0d942e04080c0321120001c405a20304c1a409422000000070b0800c0c0485100030a0b0300800340480c41c42205040103103002800103000b42201e100302d03c10403015040c80c0d0000e031030b16002603c0880034610050380e5034094a50b00f13802c480140030030274030500000725160b00411001d0070f02600d50030b440140f1030300300c0c08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 579676258 1106 579675152 579675191
    0x3020301060305090a020a14010c1407030516080a02010503190e030408010f150e04050307080403080d0e16030303020c16031a0f0f0411060f0d0f 64
    0x1008116054410359601c44c201c503000d801c0000c829400240e45280c1da005412442ea41c201d005580769205102c0d00b080701d9400742c03001404440095890380d64491511003210684a4050480800302010140d442140c3c03846000b84004004d95006480a0300000c0450546186411400703100d20558002e900881c1519400b03169030301e0030040c140c0c2c20345100045d002d10755402c001c144c0c3e5001c4040c509490484a00116a22090711945810303030031445040405404520b010402200741b2580100400500e107980c0b008010000d5940740e407640700e1421050300340000d6940f08041022038000d0f0000c00121842500340c03982580c59043d00c21102445800a840701101c000349503400c44907408456401c0455510000e40c07600d48aa80824030000040c0010500440718800083c50384445065901d5090a400030342d469240c4459810020104411116034540c10242c9101d40088008038 = true := by decide +kernel

theorem cover : BRFrame.Cov 579496402 579676258 := by
  have h0 := BRFrame.cov_init 579496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 579496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 579496402 ≤ n) (h2 : n < 579676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
