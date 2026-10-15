-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4595
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:07:45.699731+00:00
-- url     : https://prove2.me/submissions/cb990036-aca4-40e4-8769-868eb9fd5fe1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 826258992 ≤ n < 826438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 826260242 1250 826258992 826258997
    0x151008102a1b150f0e250e15060310170d091202120d05092701060f0c0203030a03060513110306060711040e061602010606050f0d1b0221120106 63
    0x203607042d61030b001c440d450401402c44181c0341004109003070404107038003040d24400035206032250391031440075a50407103070110441c548002a44006100ca80b1181100592000f0503074200c1104005900000d00a50801c071540d42c42040642c0040c4170300664002c81c0000a003510000b02983d0544c6480030f85a03801d64060804021124100c000555541140d20f030702c1c0300405401c0d114100313480741000704554005445540221500c50751428021080c2d100d810902c45078680d032070050390a0000c11101c070590074900800308180d03440b003400903075400d1005140c215060b80b0001880c9250005022404041400b180000c51404107060486261501100e0780300c035048440b15510340603803820040030140d20b150b0a4001d4030744451110a0040001d60502826100748144420459500d00b2400c0e5486401001d001030700c18030120f004217052601034500415240382c0030420341c010200501080a0b40455800140d12004060788010000f072907200c0352380d109450040c584026105105034071101031245008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 826261492 1250 826260242 826260287
    0x5150a0b0c0c15090a060e0f010801030f0f030c30020a15022d0c011b02030909130f1109060103090506060f063a0b03151008102a 57
    0x70f02200c0305044810400c001048200b030a900c0707204c000e00c2c5003007841d1981e004078501118041c2c698000c052080c100d80d80a44080c0c4528029501d5030b4405180b8007045092003070007450b82c0e00203050a20040c044042c07c0c00814010040001b4416071a8920b040940c1550020b608030000302d84480d800d0f90b207440f5070350005a91500c112000340c4041e11741c2d54402840940782c040c0d44284039000030007020900e26150086c4021021783c1d00f401a440383c42140100582d20030080e4007100c2c109008001d90202c3e4282c0d94511045143d01c445182140c042000c803542c0c000940b0403621483c0a0203604e400600a03e020011289242d1b150b50f56001c0c00341c912403040f807100c0c540e16415503c0900b02c4000550860007a80b030660054000c3e01400010300300740c45c90500c0da044441103c420361045c0d0001c4e6900900034442c11006c180c2400314100c02412201036007403034210101c1c4a078400c201403003040340c8034200094215118210542104003903002d4811300155542403e55003607208010004071840513640e0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 826262742 1250 826261492 826261519
    0x905150907090c030608060a021201031203180303020a081b0a0305090106080a080409050a0209060a0c02010c02040c27080607080702100c030506130e120a050c0105150a0b0c0c 77
    0xa261500a03400105800c1c1842c0303c400083d03078160403e1048408440032545191510780c03031071041e40205d030b1041c14920401c400400102d002c603000030038810031605000074006a102e00d00f84528138a04426400302c0d400240f40a00c4650104501d64004440083c0c4814401c9040c40e031541445680292410143c40c0c1d00404d4820100b9030040c402400b00d001101c0c51048a03240450315a041440f0700e901c1e881c5000009441000d590088030b02045008118500c3e10194190664030000031060603410003680d0035000c40184c45610494100032810345610f42c5011800150300c81420406242071514a0f43c01010000d80744000342c9543c0110709401e00d007880350f40d0450700700e203071040340e01d4500d03500b40c108a0f402c0101909944150b000d8142968881c111002a990041c02e9610452414841d913200d40802c103d2894400040c10508c00030749001380c81d280c83ea41003c0d0035960240c0711241c00358254000e1151074a015600007000b07000074664141840b103180b1000391241703140d8140307901034404c0c5003808 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 826263992 1250 826262742 826262761
    0x103060608181203010305070602210702012717010e03071208041a0a06051005070c03060c1206090b1216060c03031b030b0406061b110a1a090310090515 67
    0x943c1c040c400074070381e03100d41c2d503414620f64034045845420058001c0b1407400019100b044540070206200c94182450810180c0c011549003c00503108542c2d008060544c000307540c44040d07110020710358071016a040d03100b681d844908541d01c40d2500016580200016070024140140b0345842881500708070034259620306140740f0150501e60540403c3c60344108200d00808542d00c0181900c506445603031544070b1101c0251018860790030080c0c0896000d050130400100c0355040048000c0581c03030403804078000c04907000159140f5800400d6503035222083d03a000f604040c102c4404400c4014001c00e411022101c004811600c07034001c1034100188003180310241030182d00140e04290004500a10400980d48001c004107111034140384034500382440000e8803407080a88511032598118000c000c03404035502c4200310604009800e4010240500004040c0c0d000d00c005d0072030b68a00c000b4283d684020000b014200b20b41e01180c0d1008516103020a008290000b07030040c3c80e01c48400c3e5a1100c1e44644030032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 826265242 1250 826263992 826264003
    0x901120216050a060204030c050105030601053c0c01150e040f020117090a030f1416060603081914040e04110a091a04050108211303080301061d010306060818 69
    0x42c1a41c401d050109041092683c024411a402a00c41c4440d06883e40c00450b1584015125680090018418120200c411080c16000c60030020448070603d4440d0100180110400f81380d40d0107a500490700c46c064500c207028100103030180e880300c14180da0170008810043d15020b40301616140e0307003118010442e4003800554400c503001101c0b5032040d01d006d242e030580d9551000411800075210030082c0c101240240880c4d544c40590f9150903003400844403411102d003102800c2074900c292038000c00000b01da4000028031502109002e409241440c0680282000c203808160390b1008404000030004080c0202c0b840c1e41003584404652210000c55000032500d04140d0004520b991910b4441c4a02445015503110340c00d0041e00e05111300c2c2e0341d070003e541d140d60f11030048400c48240803400b1401114030030000c0054055007106441c00c2a181e4a07100c003141c00036006000460032a030702c3d1880e00c0c0c1c0341408a0380d1202c024641882034900f0494002d00d142c4018102c2c1558462030f44a020360b00d1740031300a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 826266492 1250 826265242 826265287
    0x6100e07050d0f09030e01020a020a171509060f01081507120e061005010f021b09090307080f1c1a010e04060b1c0e06012706080a0f030807020309011202 67
    0x41c240300f0700c0c940e142104014804008101c0120f4045a555455075002043d03030000c05800502c140c00051400f403040d07001d0481e45848480501038030600d00c00701e910301348645001d40c0c0010000c0a240ca001c0d84d0070000b442040e00300c00030070b80c0006144215443c904a003107501c001c42c3d1070300c000b4000c86c0c011f10401600700a080080c03035000f0901004070144a03403a40c07008550303003665070b81d800504906060340c865920344800c4817401080030415666041409299420440c1c4030704a030b01d03007011600c6040300703504005120855842d00207040c0c5a10240ca40240c2040f0000040402c03040c2d482200000301c1d01c00316103480d41845440e140c00e412a0355250300400090925880e0300307584400e013a00a2081c078001d2229000b00c0d600d030503c00c00c00940c1c0003d209059860303403468a00d01c2c0b40c06104502040b11000d1a15001c00e40b00c02003c2600c0c40300b800803144039803041180e105000054513010b404050020041c80842d4820310207500c0c10703039021034094004560044010ba0f00c0c084040b0f50b9140644c100c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 826267742 1250 826266492 826266517
    0x80f0f0a050d0e010b090f0c070b15030c0a1802091f0c0c061404030b07180305010603050706080f0f040213150509010b0705100519060e07020f0d120b040b031207050606040207020d08280201020d0e06100e0705 91
    0x2c04000110381108035025010311911300070810700d0b240c101c103440140300c2034100580302c5410f000a00008140500c0c0c0d540111803820034604106f10420701a01c1002550000c85269444510820410404211410150040341003c1e0950301c0c1906101000c0c000040013158102ca5980202d801d540310302030105018000020144031160383c1701300c1030080100034400d5034043c0300820000954403072400c0565180b16889409849640d00561039000540400740a590301a800d14482c020144c569100700c0d4010041c5600780d048624013200301904049000c2c032020020f82110000300e44007507100d40b484000d500d000c58001544004071011900901215601c150180300e0300d040701d000111410050310901740f042d8101c81e03140c4d44100900081c0d001d0094003e40080340c0410140c00a080d680c06001140010b41d01e9900c02400312215050305072100f15444050b03540020b020303a0039200d900407a02d1031942c5c0701c0201850f040204003011029024440c1990b40e10001c80801c519610400441c2c001c0b580c03d6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 826268992 1250 826267742 826267789
    0x6080f060612060f09091b060406020601290d0b0126010b0f0705061f090608030337051005031603080f0f0a050d0e010b090f0c070b15030c0a180209 65
    0x5100140d031061f840036120b601d9480000544207525169040301e080e40d21550250500381d19100314a0f44080c1e07080d203c0d01c44c80c00e50055950090008101410207018680c03004a400c00d14000007602001320000351490540e6200030255519686d44200d82c11208900c01e580d940f101c900e44164043c2c02030401c018010b000e00c9061046415403400da04220a0210101e80d80b941e507900c103443c044680c41e11400f1119002400010280900154225404c28240e030f801d540d02e810014681810420079400c4080c2c0310ba40d0014850000700716840340003c1c0405074020300502007204044151201984002030507400000f46001400b90904203440e4200a08440d058403039580fa0300c0500f868121903040040e580c6040ea0160503040140100030b0b100c600030b44102030b6500c07203003010b103100040108600d4881d40c08100a800042c4030b01030180c40340703505080f1080802182010142481540d00d0410311400070050306002c000c00c2c1c00302c1d00c00222108a03006a88002c1c4601050700c6600c9540c402e992203800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 826270242 1250 826268992 826269001
    0x41b0f03020f19020f070e01050f0a03060e07141c0609020a0f030804030201080c0f031b04080a0308010f29030907050604030506090607030e030406081e040c06080f060612060f09 78
    0x4100030f840c10b1083d41c080d80d207402c4000201690380c0f0300340d104031140d007901d520040210f401e0800000c0c48080380a003400181503101d4581206552503000c500170154480c00c41004034946c59100300216030012642c104080e5200c400907569401400c5019011607515030109003150368213520030004209199202d07011507904c0c1400001c1e03030014071090303010403d5040043c69885a580498640c111076100540c11034a402d441c580360340407800d802c0d0a480344200400300c0d450000300000b0203418400d079a41d41096040c4880c032202c0c85a40d51001030741d1200244000300c0801c19800d40d40100542e424055120703984da002440c9032644503440681c000100140205c00d10002050892044400c82c0889a29885241d002c40031500b0350041909240c01c20310007031001510488007142c114a4404800c215038100015032007008206840450301108807101c1040b0307494000300030f42d500254880c0161013914107000452541d105008025203000648000900b00e50307603c50041c003603018007500c220301c075150 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 826271492 1250 826270242 826270267
    0xe0408030702010c05071e05010f051008480a0e040317060a06050a090b041202090106030510051210090303020406030b0319120507050a050714041b0f03020f 69
    0x200740e40280043d400d00444d01c0a490141c400c441a6590041c3c02c1c03814007000301c2218820040704503088480b5503e1340303442c980d00302c01400b07224003482861440810261170281e060340b41c001c1400002c1032291300030204a00c548480003c0041c40e0356800c1d0343d072810100c41c0707410340107014800810795400008580701060039403610307003850710a81c403a403922600703403034080c1c08030135a01012242613602c50580d02d001e1128521603009807022803c0e134100b0104058071800c41d40c10350b8000307400c0345a4400000034058154a890803000b801445207080400160500030000d0030794103940e000d81c0d030040200302d00c0b84610850800542d244208418401c00c0710010a280060103903206128640c00281000c980e10054a000b250b42e0801d181066110364071459159901400c1003e9103080c001802814482c03c0c01068090100402040c40340028185103805c14a69142c480500c0c0540c80c0901d180100c04070f007014812440b254410f03658140215400110301c02203019100d20a5152100240031403003403401c90 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 826272742 1250 826271492 826271497
    0x30d050109140609012106050c0c160803030103060209060c010c08010f0f05012012040303050d1404050312060307090212040c0806040507060c030519020d110c030c09100e0408 77
    0x44400c01c00b444140c002d0035840b040420b058543c2940181c0c03480c01000300c0324031a2104083d080e004c0100e8804030f0782686a0b18112803003280c03c1c2d0000100020041641801401207806005402c08854280790030440000c6d03881c081400700801c2c1540c0018040f0070380e41c514040d2032403406414004c0c040c0c5844038000800c42142886005000b41084c040810003130705075a4040e00f92641a0344180f8503410114030f5403c0514218018101409000303a100090103554005002650094552030ba9030003030040300304200e4500d084041c0100f0807400031b01c00040c4010081320980c1032041e4054800c0d44079400080e0a040407035100808040c8002403001036a0003407030507144070b103004203503000001b66507003040c0342c442004850040254100300410300c20907005280092645003e46892130034404903036040d200d202c180c548028096441850f18030445d0342d10148174604840984040c150148d00000400c1d6900030551420707120b40080e074002944034000d0317180200200340d4107901030884c1c106030034904840d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 826273992 1250 826272742 826272749
    0x50706060602030a121107060203040809060c0a0c051005030610020c0a0906091103041a090a120c06050912030a270605010e011202130e010209031509161401050702010c05030d0501 79
    0xa00d0012a100b0201494401c145c40c02e1b00c000401803074240541d0b54a00250b0008104175103108050250410750b485038400340c490404210300800c9802c0382414030007980070301e5034080343c402c5419100d5500c12a5003d01580d030072034404c2d90014903544440c07400f6810440304451142d00101d0348070b00000d2112040c0c0000c0d08940b202c0e4810005008180248010340c03000300c6002d042900c40d00005594820300d42125a4400f07480010340700d81001c55a81d903e003003050300c0314520000b280390034a80700b0310540c0d00c04c580c0c02681400c000e107080340103e1000c440710b001c0205a0071305199034401a031004540400a0407202020000c2c20039940000c0c070307140004040c00c2c0a0074064062100002c12031072f190003500f0794180d030024a22840510a0b0755101c01501c1d03240607003c1d070780d50203200d281c01940341040802058443c884403541c052404090301440e260003421582e9501090050800004c80c40000200c0e0300c2c502031801d140d0b148140c1c001a15207410310700d4005d0140c40000740c00c00080c2c100f9407011707058 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 826275242 1250 826273992 826273997
    0x40507090c0e03010525110c0f0a03150504020a0501020120030a090c170607210b1828020f0d0c05071a150d120305041b03030e211b01050706060602030a 67
    0x6402003030858510f5400ca407251020743c070000b400023640c9041d0301c82c0c1204400080a2200942d03d035039580074401c1c1207404485036192524184000c5152000e40c01010705401c6c8000c01015040001000b0441d54601e40c44001441c00800305000038a903412083c0c10a422690312500d207940ea10349140c0f21104003496913598007030800458040c9114100319500c1c00d01d003100000449880045c0d0200426441c601c00d6480003034010b50f0b0124200500807548203810705000c012201a82c0030b0b4078079186c40100c4440304c03440e10420a071030f01050040c1c1076400502c122640024268101241501c42e407050410141204940c00304d1482034600d98210144101580300504d41e0988080060006c42140c20300001c1038001c0e0848080ca40507c2588000da225010f070300785002d83c42c07081c040300c1c24450030303504103500051801d4109401400c0c806004050442d222015262058000102c07a0715618002000010050800d4090381142e02c51070603500d03200d4005404202d180e60f0707120065501c4d403002c0046c401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 826276492 1250 826275242 826275301
    0x71511070909080f0a0201150612060f12110a03050114180d0c11151606060b0304112202040f06020c0d080a05070206070609061401090203040507090c0e030105 70
    0x5544019010b205415584018010b080c12480030a490b61380d042414030798119940d59003035240002c108408000280390b10b031075101400c4082142001550025000440080b0740c0c050f040021100c0d00c4041c4984540103580140c105018400007110103032150701c042c100b90b09000701c0641509500d00860300601c00d01840080500160052540f00d0700c0307601914000c20141c1c800758000c40c50034174040d01500c10081c8010042d01c9000d40f0044280c0002d116000c0780b40c40036084e030007000541d12a00c3c01034240303401e9003801c40c0b405a5440c00c051074601040f0340100c8503001c95228131b19607414410026891302d4000d6440c0d98485110795000d108038410701c4c0061142c40c8003075140e0b05103081e032603034003d400c981d2452400544400580b9150300201d4204d801010400c902c0340814a244949040c6504c1000d002c51018081c000d0780e1b00780130040c0c002c058418810400c0c0400100b00092840c12111035042c0840c84c1015218203640c960605a0703425095400e200410240407800700c079000518080000756203 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 826277742 1250 826276492 826276499
    0x20c030913063809180406050a1109280f0e04060b01030510140d02030f01021e12040308040206040b030412030c0314060f120f06271e07151107 63
    0x10700040281d44209a604120b41c90f000240c0598008024805005d0540002051308103c440d510020442c0e007681c50a90310420b100386404a4040c00342400f01300880c1b141050460000255070000304244080c2031a00803060840b100003c503602402403522114200c103013995010080c122001c1190216492440c0c590307040d00c650b01906c501c900400c2d00301d080100c0030b828420f034440012001c1c040190710560320100440142d03410010170104003014800540c9076a04c0510000703800b04079039003100c100e5105210440843d980201ca1a902c02e17010b14142c003068603240040307146481540c20047c0e9101002081100340401c24a148030a03c0840d03504104605658038110111000f03040a8031035085628081055490043c0118441d4a00109001c5084aa045d40c0354034000041071391941940000040212000d110081a01a00d00c0000ba512a5086969001d600c4001502d441028000c216848540810040004ca00075040000341c202c02800d040002a001d07458048209411348504240030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 826278992 1250 826277742 826277789
    0x1030f11160b010501030e120c19060f0c0c1e020102070504180b09030901020312190216050706050f0d23010312090e011a070c030203060a20090a150c17070510050106050d020c03091306 81
    0x2d1000c550825010343cfe41e450700c1c4900e064103151310350050b41140704028002c24999100d110301c07407a003940e03c80d4410264410380ba009c0e14488004200071f50342c0d042031207180040d98001c0101c42c0022045d00560310b060781c0d49041d850407d0301426200403003c0c808209448980070001c505200140240200d85201da07980100301c2d002d105031142c842c010501404001c801d5040780d04020a1010070240703c165520084400045540090f44140d510707010100c50140c03a0358100030309030040c008410a0031180d40c14008a00180c42d150910b2801c15000060b0100500810107080806107900400b03072401806d0200744100500300900151103d01d48103840e13801e482400c4404c44540c20340103880c000d5140d01e0400400041c136000980318050080d6800303c140022502500e6618258103a01810745131812810064501408416140140340c9400d0050082c1500801a10701c2102d0140c009a030780d800103640c060660003030f0090b03035800070600c100905022001d80c21010940e00c0200c1c014041c80381c61450b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 826280242 1250 826278992 826279007
    0x81e040201120e07032915010f0806030c030a050c01270326120f0601020607090b0f0d020f0901020f070f0501030f11160b010501030e120c19060f0c 65
    0x3404030b44460009500711040b9004501c1400d003540a50300481ea0b203480304c44508003480c07000d45681401c5800d030380121030b41c0b00e4140d0304400e40080821f0100c0d095030020f0284025080c055091007402000901260b80070440703c40c0351440036086e02d2500c031440c9015503548082c00380c83d0340032401c0059508070440c209107050203050400c600c1c1680c0985151502a1091240021415a564030225009400001c58014103004210000058081c5840c1d1140004010040d00450444d0444e0040c441d038036034040b0340c4070b0580b0212000b450b5980700194403084988982c814ac08410303800400c2110000c0c48002c003405020360280c080c1c070404100c0c20f64594a9600c0c0b03000c0d05d1044042118240312a51190340400d8449240900004944242401c004050340061120350070a1280401c482d08209a40d100240100028201444811007286403d52208007001410700301c03071000708401c00c1d5000208840c0000c40b28100410081d0100c5007010310250000180d10015503041c83d1072244910302c01d011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 826281492 1250 826280242 826280251
    0xb01020d0c14070815010905070516032d1106010e040b07110a0602040b0d0f0204150c020f0909030706051f1701090b01060e091303140313050d081e 65
    0x4940d00c00e9071081d6a40740494036010558092841480808103100130100800107121040e07028044e11580346c28140c5065910040148081007000d100b20305211030548212600345a0505127154140d086102c0e803010441420070361200d44003401c0c01501129009010038100c54160030540b0f1003aa21104203030110041a9001441500080c000802c030302c0c17017002d008041e000c480c4140c0b40c0720140354441c802643c100760006a800b000005100f803a0030300f1803095a034008100030301541010f10307000c012840584124140018454214000301c21560381101c2c10780300010042031000d66090a0200b1650382d00048401c461a61604000c81c1d03041002c41c405400741c80c1c20007a101d90300750411180c45038881003145219825901c078066a030000780307024000e078003826942c2d81e244110481902040154900507000c8a01d140d03284d9030074000f0079808120f80c1215888100c3d226900c0d04c0b01d1241038080940c0c0b2102415600410502e0b982d401d07400712a050280303000a041d07414881c1d000c00f03944113065092300c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 826282742 1250 826281492 826281497
    0x200703080f0c1e0d05101404060e150105121344072a051f0c022101020703090806060102060406050c040e0a060303081f120204091a04060b01020d 64
    0x49080843c2548640c0142030b040c007141c0f00d081c00040442c41058070070aa944a4840c03c444006129402103010f9903000050304a40c05d0101d145440001b01d0461005095010380c03595204c00f40700a640194129641211080d101c05120f241c0f0351022281045200700c00c6070221401500082c2c44122030303141700446510034802544540c0d2069403030b180c0d42004141000703250001c0c4180c84c082030f80b41c01d282e084a1140440310640e04440145845a540690003183c410780a040030031130032100c00d6616011015590070190340d121024000101800108000c050f22169224201c6100c108103401030120107100313860710141c454075110344c6a1500d40856455005a0101c2d0026010034055040950007107990b81185252036103650000c03d014074201c51403000c05440b000200300305540300c408290301200502c0500c00c01d540b1100a4403c0308030700d00c40c0c06040c0e01c20101810955503154400c024079030340a0341d807a405404000b81291090f00448003500e2062030414803c14a5001207401010401940d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 826283992 1250 826282742 826282747
    0x207060c150209010c08070507061b08040b07020627041103061003090618140708010e0a080a090506070f0b090708190c0509040336060f0201200703080f0c 68
    0x305001c000940008484904001301000e681012502039001000c0182c000d0b8060810241055005080100002c054140340c1c0b40d501c1400000c03039141d500355025a03040818480d50303030340b444c00050080d0083c0b075800e414400c080041d06030711000b88a954802040e0943c4e00348546d003080e42c0c0b080d0071030008860a0340c2202081e43e040000c248250701900c1c60b580700344000183c0c101d0315046041e50601740c00080301c0c0001e20030340201018404100e10001483c01c1e4000b8040055102c29072a124080b01d40b000300f0480c0d020821201040c0a490301d000030381406010301c0d40f40d0352182030104100030103002c15103600b102e040c0403801c01c00c80810044c0607600f0300d50003000d65061400304054550520700003502d0107080f40c0c0000c25641e44a1201500550295407413003842e00b0129480b0080d2404800758020b1841003811108e14900043c03510300840d001410f0040a03a048071200342d01601daa02882c410807040c445a811443c548a005020120300917501d07249a81d884608a1041d20410707104000c140209 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 826285242 1250 826283992 826284023
    0x1b010507020f0f1f030c02010e030c0a0206030c0d0f0b19050901051c1e031701050d080a050c0106080d0210020301120b040c080d030b01080c031605090d1b03030207060c 74
    0x43c031901100100c02501c40725250030404030003007019808401042c0065151010000c00c075609004085064145002461424010b07220b00b90b6140381c40c0b040280034240100001d11003c440c3c200307a6075008415036050140004042145c0300501072011700511484400640c600642c1c2110040720039070390003a01d41c0ca49a404c3c0030070083c0091320580c070340000c200142003840020710100090352002012480c40000c0e440f10346000350810b0459400d2010044a00004022958402102c091456000350340380b80d8a10301800112014480d00d00f0803240c660900c880005d05035030005010182000643c00ea5400e0104004113100344d00c000c0c071031b201c8064202c090000c04034903580c6002380c010b44a150000070b510b40e5503100318181100c01d0004804a51354503003084031560031014072a070224000403010301e07524000c1e0103e0044400001c5030010010003289850650f01c42200400c00c041d0020004183c4031041144581a80024001200180644040014164010000c400b84107600034100c0060582 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 826286492 1250 826285242 826285249
    0x2192418090f090f1a0c030417211015031401051c02031221040209130203012c0c090405070b1c021611122505030f1b010507020f 57
    0x4555a07150000e40d89000590004a210103c5010035100b540713a244404002485100c6907240240100360189003001003100084001005854440c1e401c1c42c42758554904004c00b200d1a0f4942040398001004041800f0302c481d40401c015040b61081c90540343c5551600c1c074100d007501c003c8407510045040300c0b401401a4035290408100010000600c1c228121b02ca80010303280044603000240e01e1840003c1544c194942c50000c80b4101c90a00c6150042e41455070100da262040280140c01020a2948080440d9000c7d00710809400384060621005c0b94501e0070039141c5228031819845e14030640e060021789050203c8900d00c101d800c01c0141004d01c0c6400c600c080380744d00801d09001111103c51158903040308903c003800300c6a02c980c40c0d009005429107801450900c1e0b10511078411109000a50118032001464002c00c2c000c044c80307410701c034400e001080240c4415400c100d901d40585030111412040000f071034981c052032491030180b01c088250065590748940d08020350000c1c051803021400e800c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 826287742 1250 826286492 826286501
    0x31e090e0103031110022b0f1409070909080a180b0a03020c190201021207030210110405030d1d1002071502011b0801060801030b090a02030a060b0a06050f160219241809 74
    0x2d8a001010423601000000642154400198101550014028051800002c11040d0003414070303408200280450341c1c9402016000b0360444004201c8540b03000008003002c900110000c1c1405184aa15084280b80150203500003010542e05803140f5000c6540c0c001d038444104070380607010b07009080d003122201c0301710072130b43c3c4401030541c254802c13031805498020780c910810780300255041e5501d03240c0d07007003508240c14201d442d0040410040d266940150f181c42e00c84050325100d03c121070031941200340c1c92090382401e86541c00030038204600341a0590050701904154401402080540f141c1c82801600340c078640801c0c0213980008201c1070041c030000d000c195880c2e4101c6c100714101c3c0e00d00c88903580040d103001c045407802c480381a264a2041c6071030410380d408002030182030404c1c0341015a039002e075420078002da4505031003a850701c1b034860083d522403025941c422140140450f540607184d80350145007020341c1807607041c8a07030140e00407594107100c0c0488801525808034401c80c0d1900d030691850140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 826288992 1250 826287742 826287817
    0x150403080322050a03090e10051306050904060e01050609040f030f27060306080705010215060609060729060108060f15120603060a09031e090e010303111002 69
    0x840b03420040501e9100984141d420440c40392000f003c0082c00b51800404116169211031141c10514003440f0440303081880820a4460560314910725400b01c42916010b40802d90000780c010b00c00c2d00c240b01c1444442d0700700902c15070500000344283e840310024800010802c50300903207003c8090749000000391082d0803100d200c4081d403401c2e02000000c0040c0c9480d500c4c00c444040c081484a034020454103070035014510081c00788502034030703140385000c1c0040c1d00d03580e80140c1e01e00c0c025090000195165034860680c1e0000c140903040340e407500c985240c1180101400341d5010351440b04101c100c4c0e10114803051483c410141a99940305c0340d01c40105211064207a0036846030710a122030400612041d110001d000019445201e440603403e1000c00e05051880181440503030074106110400840d400151400c4c86000100e001c80c2010342c0e0020403180c0c2900358212a01d082d502000010606503c20007015540060805403030328071070352a031110224410910041d1301248920801c40c40c000480c0c5600668 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 826290242 1250 826288992 826289011
    0xe01050d0207060212070507140616080405152403011e0905010f050a02130b041a0c1c170601030e0705120109080304050f0d2a150c1d1504030803 64
    0x14110b017642c043c1908002114078000082012a0074414049200c5980e841103540744050052824201d6800d6150200311010741c0c00c0c03015810121f410840d0400c503144c00c2e0160308114130001d08103001e21041000f040045440460401c5401c14040c0c40d040c8200f440b0422040c0a4003041006806644090310360520305403003d5580720b00c1c400702e0070750034000ca51140b644503c0040c4d55400d403501c010800702c0603030442047c50000740424405c4030510104040210008941140c80f5200c00c0c080c50300d8481aa41c0702807010369270301ca01203004e43c0c022108202044036881320380300d95034400004408540032420541026070240c042004142010701c0b00340d00250000700003180c0945030f03032904601c50b4410784013150b1943c44448440c90b0301c03c00b0f00000c4080402c914040842610084019104254410843d03802124241c401e00c1041942a400d4100070501c0d802444200050032001e48a002c0c2c504880082020038118805946082c404c400300706002c29000074185411034968500f240c10082c0f040c0030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 826291492 1250 826290242 826290247
    0xc0f07030c26091801031509052803030c110d0305070903060501120203060f0403051206010e090a0b03070909020105031b120a06080d0305070e0f270402040c0e01050d02070602 77
    0x1c07402441c00710002c02540801c0e541c0e00e0311100140405582c0455030926521080401400010708290403240552042d040100d9440700c50705040b03080c040c2c1d8070300b2210301640d425640315030600820070700010395020392820801d1940d046010344248400341200c8005401004160501c24004d030700003504100d030303480e040d80003039103e54844085610071703000080c105510301400400c43c40e04019407540041100c0b1b11844506050340e018001d0301842c42840000c070700600000c0c10b03591040942055560700200740301814102202804001d00c800d00316140207004504002c60400018010314144540c180d547e0340c51a56a800088020280c9000c01401d55404214103078007203004103106401074803603102c0080c0c1e0030b18003001d00703242194103c201801c0c903040200704030402c1d401004401003000c064404501d000c4050000400d6035580c800e11000f245926a10058207070b070110b83c41446148291010010440c3e204000c0e5041401c200149000507810080740407004d0071034004d010b8484c4522000760 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 826292742 1250 826291492 826291523
    0x209040311011a04050a0b1c1712041103030307170a0e03040303080a1401050a14120d0f110a0b07300c12110901050a020709090c08060c0f07030c 64
    0x2803d6a10607100032610340300e03101000d60585864855030341c04c0314107840c04110300034200d030100d15200f460240300408a13100d41c2c2d103442806500850400c0d694922120b9507611111446502001e0070f090300c085c0d80010f0120422040c80c2000022030380102d840d61100310354000c50f00c13070000c0e101000800007070b500c80d05c4100074000444100090030142d071003921001d90760710784610384004807401e10f1260480c20340b480c0c1c01004952203966510381502e030201160481c000d0900c001c5052800031080d4040e1500c0f501103200020f130391103081c6045c4d0110076510302d405005038a90040d0364410108010b03040c03030400c0010030711036405445420a116070580303640e48003020583d030040003544400707010510691500301c1981c000d54056291801c010f4000b204209609064115881e24061520318605000000850451160007004032900074011900e090060b9003a61410700c00041c0c0038450b8250500c12000070403107120114058810b2101c0c401540c0d801c18200341c80840d100700e0034040a6403c0c0c040b115080c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 826293992 1250 826292742 826292777
    0xf0d02040e0f010c0f1b0605040206090d050601080f0a05150907090c02101d0c09100306020c01060518070807050904060b0c1b011103040905090f0d0e03011a0d02090403 74
    0x1640ba505015000103054400074401a2541d4203841620f4100302c804034000c11a101c0c040d21160710160003440010361540c507840420118800c40010356402001d0440f1201004000207445058034120b8050750042c20b4082190390307650841f83c1c0014000e4100207005101c14800d0f840c110350040d1040c0c22038030416510780d610b50855031042d07040ba005800a500c0301e0320f89095405542444c43d0251203521452104075001134403603110f00c40c5940705105550214450a11003500c91014503000384e821581d03018401c410310b000b0b00040c4a80740c050190342002405010200400a1041e40c0315228000544e07280d140842d00c9510500400d9445541c6041c080b944e203950030090620b240d0894000e04c01414500006140311a09903036036410080d414100d003161810200968084401050010980b601d6081030315081c00403500070300030385100e1548400c60884d4020184010014250020003000c0d40514a2801c258074207801c3c00d0300112068012801030400030a0030354080d0191170445194880010607 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 826295242 1250 826293992 826294003
    0x604120506040b10290d0f051e01120602092b03111c050904090b09070303090f030b06010c051501080c190e01060c031407210903020f0d02040e 63
    0xd680c81c0d0320210800c81000000030019400000000c44140503520f040e010700180c0d42c5541c12100d841034890761156015010300300303071100e6078070b01442071150081c01a1518000c1004940c4005000030307079002d07510300405c03400c0303403c4c103031410715000d10446122600c0380406544800703e02900180d42c0540d2061014100c03461015900041050b034032000f00c04d040003005a0030b9442d565400350020314184280d024820035058030038080d81001a1180600700006005101c2c1c410060101c0c60744400b000f03030180011a503001078038031030344403d40480e0320340d14000c4007045a400024903403a80403022449560203a001c0a00d030f03911400c01c07102008014a51656505c40070703072007200071354003031040c2925a150280003100340001202e030450049160021a141017881031040780203000445a0760801d040c400c07001e0391540391074a24507235502c1d15240360941024281c41d50f0040b0740011245c4541582d486448039000b00c039001011001460f00c424100806070081d5181203a00ca80e654a13644d401e03180a001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 826296492 1250 826295242 826295279
    0x3161104110a1412240108090327060a02030903061501120b0d12081501020309030601061b0506010e01030606090b0f1201060e09060402040e0f0604260d060302120102070b0a0b0604 79
    0x28080000c01500f003901d10310101c2c1840c0745d410310403031004010b64064000144c500510514490802989035091f0301c0384441d80c0101020380001000030807034070745078000000b030981503c01c2e42150041e0b655620425032101014846a00058070140607450b010440d400002000b18000c0224070302020951380c001c0030400300038a03000442c504004010468a5004c90001d5147c001e002844c5007092035400030f91582d0050080d84248240218240c13110b04850040704504c9900c2011103400d961076800f41c1050303680034401103540d5410030b0070100320380510340558800c1e081c01400c030040324007510082005522811100c10101d42d41c950300000c0c40c506082030705006a060002400c171a041500510058030150003440304a544a03400c503041381c000000c0c240c0c2d480340d000241c5804008110f02c0f2400d2a080c81c0c50300110541021070100c040515039809082120b108540361400b030f500c201209420f0340a01034028201411560008090351865082012486001068140f4103a10b40441c030b4807002d0604d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 826297742 1250 826296492 826296511
    0x17090a090c02070504060909050304180e15040b060a1409070e0a060806120c030316031e12050f01051e0f03071806051c02100207030503161104110a1412 67
    0x43d010081c0e800d040c0300780400b038500e051741881036000e13685038182d0f00c6c480e600c50f0075803a1020300715180b5001060f071300c01c0b4503200482d01900c1180386a6442d840c5a020f00342c1e816500320507031801180403440d200445100311051f64200c089200e03a444100012444000e1400007031010729001203103550b561103040c001070308181c0c4582115050450600416803c0c031070541e40668450030141d2003a0b40e000080e10080101000940b05225540c50110381c144000265510390030307a000310784a5596004507800c60741c3c00404208004079512011850585402841100d412034504514900107140311010380208982c0a0550786030000c41e000800d1624500da0f001d640c074422a00003a16a500ea980101c0c07000782422280c0c85003007181220090101904078030300a00c0344141540440c0c0260003400f841c402581c202081d00c1c1c840d81c1d80040c80000a00d0000111024903d0303030328440c86460700b807040360140e4542489050400c904076205582041100340ca0f003180c41014820350001d0541c1c484014032070358000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 826298992 1250 826297742 826297753
    0xc040e10050a0c090b0d0b0a0b0318060f0c09060c06010609170706021e010b040f0b1002070305030910050f0703020d0905030a0f02060901110102030a0902100c17090a090c02 76
    0x54904000c40d40d024080e29841e500f420800c0101d641d00c01c0008050361202505541d41d6400f80c040700c2d0007801503002064025401400018103100010081c40c40f0702541e8000150404000b41c4103500d50034102d9404007102d01d00b101281d410080d00700600f41800b40070703000900d8400030300d00302850320b0000d034010790004003561018046d01c801d40c1200b64645507910000c103401b0303050140c081d403188007281901d4184001428403c0c2c03440801d401c4070407004c1d00503204115002e000100d400113800310703004003806116035180d01543d441c400078181041781d03006809036007003200003001c00c184149140b40d0f003420030809000728481c0803076040040180903c030380c00078440d5906804c1d000d030000003e40e100b54400c0c1c0007060b60308085021402480c0c9541d9040b43c181e640c40108000503107403c1088040408950b10200801641c2900781e800205a0340c000c917080114140307010f00c1120440b401c4c80c0000e16215008071210340c140340d1400908580742c0000e00c007005c0c0c2c640350030800c0101c41c0584000e60050780038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 826300242 1250 826298992 826299013
    0x140d020307091b0f0e1014130302011b1a0c0c0d020d031a01050304030c060e071202031b0117070e06070305070605070306140f030c04020f18010e090604050403020c040e 74
    0x3c00180e1000f801960070214102c1c00800c0c0041e0040c0e0804142a02448004100c9408103102e20f0b4100e99099540c81c065443e8000c0050b103e44000450100b01e0109000485c80f00600c4041416400890340c414003000001c46c00c90000352102a01409a5407844410701882c0c80c0c4010503c906d8403400c1c143d80c0117200260805000900340c5140d181903504101d040e19103034130f450342d1000490354450f8042c1000085000c151619074014840240b031003c00e0300a44201044601749026030030300740d038002c4084440303000f24200c62001141201100c580822000c08842c000e2400c030390381c070b00e51000e00740c10301c9211003c0b000701081c0c0740c0d070140504800050001a5450401a60303119868000c0760f10329040210703a040001080c0d02907503d4100512541d4030f080000e400d41c0d003c11401c200840060000d5440d00070018a50107660407200080c03103869100111010170303501c62654501c40d0007006000795a00d403200740a00000300700180c020f40031801402e80304a15a01e44c0c4c007641d10306121036002001c0c01d030700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 826301492 1250 826300242 826300271
    0xc08040b0c070320100218030114070503040b04050c10050d050f09060a0f0e0708070f0605090f0d060b04090c15090b07120c0c0b090109120c140d02030709 68
    0x1d00c814041c440600c29400800d6021844010740d1640180b00c160702d078511010ba0349005003420301c0c00e11050000450301d685100301c414443d040c0100f80e00034803c0390ba01060b01d1001200c00c072400400a0800c1c4002401304008488440d0002c4c0500c003501c0e01141c0070390200c0d00f13403496144004081240010141c0d119451485090380c808100303400024a8104000f08546445000e0700c40c90400f915054192007a075120b9100014580e8150200c4403019079980c1016102ca00c240b052019550b0301c0d030070005401c3c0c00341c400c543c03203498010220160100542d01b08421801c28a000f41c0b01d06580e04a24021760300e440c80760461290042c8142d01c15203103030070400f03110100d550a003182004020a810804a0310b114181e441c4540d00c85d4003080c2d2150800011140c9004140001c0c3c840c8214080010382c0d8034681004080082c0c7c280c0c2d80401260b11386070700440c500e07200344004044082d0300e80c04128010260b075101c000340d0b000810b58183c56540341c00003460304000e504004125950f8200b1103480c0c85 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 826302742 1250 826301492 826301513
    0x1106010b04170606090103021314150108100b09100e10080612070806040821130614090a1401020f0d050a0507020a0503030a20030c13090e07060e04020405040c0804 72
    0x41c02e0402030502d860494046450f403041032100038041e4a204800c081d20b140d9540040e500f442c500c070311890a601c0c04110070008181000c50700c0380410007820105003114454000f42c0103403032001e0043c030314212203507050040c0c01800b01c1035141001400800130455030b813407051a02403c642c030765684070141007000410149241d00810402070b17602080d020054410301054495000780c0000159841d0726082080d094800e841426903031600d20a43c04120306034400415005143e8094281000807512013000103d0030b0748103a0f4918a1644213480e408001480c0765a0b80d00902240030016040c4049207403600243c0d08528100f02080b500c400400500c6191886980e0f8443c004d407001300090b01441d294a5220720001e002c80e0441a00c404488580300300341c5400000805060038525a0391424444005441d005603410340c410b0756401380c0000306401d10340100c2981150035000740003900c1c90403070195044041041c0700b0303030000d0702400000b8281d0360f9842002c071131a0072500d5841c124545854104c2c1c801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 826303992 1250 826302742 826302779
    0x30f1602061618090e03181503191d010c230910090b0a030b041505031f0902060408010605310e03070f1b0603021c0b011106010b04 58
    0x55000e04100500c40361070b200c03101c0d09505681002d8500d800039040d58400705500b5001840e542c2d0410588286402d400401024111407280c85003440240c5401000071940211100d10805282817021400c4812185100364201c0043c440c0003440005040b10324a06d40c080c49000b904a0750350300c86400c07515400407420314030750800707041e8400c0081051910041900410442600401d01910313041044e0b40605e5071701c405000030000c220344901d00408000e01500d0b50010081c02642844044c0c048004210b80140c2920710040103402c51a10140c8422940499145000582500c0c0c109940158407190024809080d400001081da07030706050501c540566800046006496090740c0842600140da000024044000070007082c4035803040c0c0c6c1c051541c01040300180244d104030821008110955404450089010300660046680c901c0260203c1c024000c00709051244400042103074032040d8880e12581505040150200c4440039541e4500b40c8260004480c1e00c0c030005051024801c0d24500a04c038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 826305242 1250 826303992 826303997
    0x5150115090f0308090d0506010902070c05010e030a03030e2e0c02030406090e060411120702011a060d051003080f040504060b04030213153b0105090403050304050111030f16 76
    0x40740d24100300240c00140c54031018101d4000803542c040d040d0b807110001e0790015080401c8039680d503100c0c5002d40082d4808134048464800d82c07040002c1369400b038030002200e07101c001c0141071603440702c4d141940640140304036800d0501940f810361544050440e50203805e45900f12001c10030700c00c0b1030702c0541200c11a00c2c0030b03000e56005100800480d030340110000305441011301014215141e80340410090020341e80b04669580d0085010980b82d03c0310401d181c4200000d60003400446810744088820340c00303090030f240d0018403c000060712a441074010350f820803c11800710301403558903100c030718807a040364005415038a40001c00b000070b49000d014000161a0b1004064a480d14550004200f88a071007510b40341e258803070712501048410745c0d00c50b170024080410742c0800c84044405020040404a40e1145c0d8600104140c0c20303c00e51181c070305416150043d05000c8942c807962402c0c3d50a80005004440319901c0d10909440052407001841c06044c0c0c0c0f1140002c01e041c980741c03100c00f040302001c00604 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 826306492 1250 826305242 826305257
    0x120a0b0301111321150f060305030904151404052d0403081b0a08060109050301060b04060201050f010312270303080603061303020c01110106050a03050a1412091c05150115 75
    0x1000310502c2c03041001c4961194001070204000400070001d080c0210f06e10703040c28a440300000a120012008201e10b41c0103c03801c00c000c2603681c000314003d130814020190310409210801e1030b00d0429500054002e02c500b0004440c41c441023941d6500318055060b9840ca22001c10306000030141c0003032010b074110080c4c1d02c01184074034040d0030051441c080c010907642006440030104060364051350994014000240c024440d507030311101565613680c40b80c42110b00543c6031200084007515080d0409047c0c82d4001a007180d481c44602d000c0300d07007404038668070420405600c0301204041c54a03522500651103900c4010071441c2c12801c041c10090010720a4101c88000303044240066804181076030003076024203200c41d01060003440c0b5401801c05401841d0000707074908010003802000908400c0c000d1059020802044034115901d458188480b810204041e060000032075515281c840800270b2005480c002c003d042054503800d280120701c100d40c039500c0d40107500505c0b81d030039003601c1d15031121010304220b00d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 826307742 1250 826306492 826306529
    0xc0d2a0209040f060e0f0102041a07211202041d01060c030f031104090e21040b18130f090204111e090301021201060f0219020303120a0b03011113 64
    0x30030800000b00002c0943c0d114034182820420b290707110051450a0800312021a071818004d24001d5205000d100c6c00554001001c0440c60002030443e400660b00101d1541d00410f0f01c0304c00c1c03003040342004502c003e210ba00c6c0d52003141c90085102510050030300e07882a49140c03c03510140802440180c1280b001c02c00f1550a45012076000742c09190700540a01d400690a0449a078080c05400b940c1c007c400d4050a00002007c0303000006a0245804119003408100855440e0401c400b4032440c030599450b4007040c000050004045881c081250b40003a0030b40324003c14145550081384d002c1c00d4140003450b5100011001c0d810075119601090020010603441d00c80352104081c038000c10721011001401e000104070030340391400c1d01031704d0400302081e0380f174001d558440e04044c1c10303009000d10220051003100386c14000055010f040c044140c0d000740145207004507254444130070010060039070100a0300c130000340030952001d00c00d000c60381e01c41415241d101d8020b40c002d44800320280d0b10810a8500013030552 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 826308992 1250 826307742 826307749
    0x100306240e1012110405121501030303021305060c0a17090d0b0402060f030423160b0c0703082209060f0e1302040507051c060b0a050f0c0d2a02 63
    0x198800181150784900181c0c90100859803480b032401d43e01e24041c00e0016044c00b82e90043d025100352441245c0e89042040003002d81036446801842952060108100400100380a03900500c4021641c40d404800c40d9110703000710300242e02903803c1c21419070150300c10005016812408040200208007400d00d407150110004810406070381010b012082039a005c1002c41d030b16401112640507030b81d00320640384d00d080d06049920184a59030b8070010000904200744070100407450b00610540c040501d200c2a0030b00003540e801d5007050704003503100d200d400740c0403002c81e12810240040c41c9000e00960f004511020300904081841d6000ca45103c0c1044800d000390004d00e1401010b803900114055074a9890590554805030fa11001a400c01d03c0d000911544a5000004041c0c140d042400e000220540c022800308a03910361082c440343d07540900914001910800003490201101150745060449141503541031001049080001ca03224207105070b4200224203405c2c0b174000e42c02c0036021440c0030a8010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 826310242 1250 826308992 826309007
    0xe01090c06120b09040b04020a0e0408042d0f060f0215060103020a2003090f0303190509241b03040807050415090903080f060418020405040c0510030624 67
    0x384018000712502c8070001c94256800204020750040184900e0705240c00c03d07072802041910240d001e010000d60115004a8210341580142c0c0d1080101e4681403030018002d403900644030b907012142c02c608200580c7c0411040c46100540413840c4003c0d4410319110303024010300c60102d44c41040d500403a4041d10303280c0c600700308154810400c1c03d0259840140b28000c4804000b80c05800301046030300c41d80d000010000101800308035005a580c0c241c000005800c042d50382c0a200c1c130300d034400000c20b0400150548904058060361402601040c041103084408542d8101c80c098444204000864564500751000720900b801001035005940340c1070a02c1005515506280100c84c02151540602401821201d21210091101040030801f4048920300104801c005a45d40b1360000380001c0486d0701450184640404285a40307101c0d10030186c6c0b40e091201610004105482036a900f4400003110344811051a41c150040e54000a0403420080001301e200004424500440d80205503c0041d82d0080315 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 826311492 1250 826310242 826310249
    0x30403091511120a0504051c0506010b0423040209030703050a15060b0d090804030b0a05041a1003110d02040c020708060f100b1c0f0b090c0906160314030f07030e01090c 74
    0x1159564001c4c00c4020f4800e4817640d4041b607007002da40f20100c402140c41c40c0d146c0070090703c0b49007944c40990340c0300c0d07012005000b00d0040030803844070441d11100d01c0c06200f500c80c181c00070142c009403c020b07006000a084c490130b81e005903100d40002188804202d14001d072200d02a18100c0204061824031182411070301072045211101c13562401c0c800d0911040009903030007594070000440c0c8500d041403d800280600f03a408407041d000c0d036014071031149440c00b400b92146c4103d50a01280c245981c540318200c07c40c0304815904020402c01204c00750300da500400c0781a6210360001d022180c41c04078040e01c0c10300001c2a02c0020f000803014000c041e8021070600d8101c0700c814401c55200d8188502d08410404142c09080420740b0704071106601200702d80010380817078070454107a103040e5035200c2e10f2a003901c80c4141080c1e00003010041c0e01a2081c0c11417a0004040c040e103488c0404581d151324030a4203500c203584044002c854074081121943c0c1c98054012040c83c803000038010303002a9034079409850602d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 826312742 1250 826311492 826311523
    0xc080109020f12031204050c090a1406010c0305030c0d020d06030f03021b09040f02031e0f0d030905120708041208030a0e010b0102070e150a140906031501180f02030403091511 77
    0x40c082021f21204100d21003a155000740102400d04049820a0041c540303172411200104110b400982d071980140981400150182c440724599542e001c0200300c02e900c080041c4026643c00e019a00d0102c08522400000e98400c0d80e80ba0302e4441c040c00c020349004111020341803120000303014040740e82c9502403417a0700a64441d030304800c114064030000c0e0801c042c0c807041d070940d01001040d01e0017500000958040e0304440c0800d840541200120440640b4408070004e000f80c0d2201d440304405446010041085038040c002c0b490034261104212008403c00f080c058420300d1001c800c1c000d00d1040e61040c1404000d00c40001c2100d201080c0c000703521190307a88120b41d034010100b400030b881d50b101800101e041881c02000f0750201901c928141d03406130122a159400b8001020000d01d41e414000381d80c1c60451009544030f61943e2800f4a40d00c0a01d401017a022101c030b4030340611070a144581d00185004510940301c04003018105484080540b500708050030800c156864845024940840c20894501d45079 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 826313992 1250 826312742 826312777
    0x80706020406091a1206061c0b120120070204021201030803010906050d120e06090a0b0309061005220b040612050f030f07080d1107051018080d0c0c0c080109020f1203 73
    0x190840c002d00c001c0b80c4618990a00c8030882009a52020507110400c4410102d81d07403069280701d03301c5801c04d80002c0e00201002d41c4002c043d0094029041c0b141c402807000d480c00c419100e050301054020323403040325010030110042c485000140188805080d0540e4481c901c445282c4032109200085001107003403080d494070400d003903207172502103d00307568000d842c040589039074113800c540660086540340b81c1801a00040b5099003109803400d0104e540c02056960000c022081d00207140354138402c00302d16541d0b1800c2c00842030710b4034000c01c0e00404182032810005c802d00d0401ca0704081684142e0238152300200700134600711404209441c4000e4001041e1903d6545182d8148010310440051140c48840440c560080100001f50b0860113110070b07005000c204c40e02c18042c40b244210340c1c401808103c0512000c501c05403180d06c012100c0c8103528140001b40899200c1c0d00b0389064a801080050b515040140d06604140401446400d416111100900701e030101081c0c0b00d0140c0710b034108a40809 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 826315242 1250 826313992 826314001
    0xf130b070308161403270f060105060309011b0f12060b0f0f0c0312071205040c05061804050106020f151003020f01020a140102040617040c170a080706020406091a12 72
    0x28103402c4004c01d5a40840c184d403401e0110600480005000000000001401e85040c41c40c5000c5460030101b620f0300000c044c40d034200000c212007038100600030003c940da100c0e03103a10b021005803031449402003151a01f8035041903885000700f0415101e054192241c0c2015002c010035541c8100315000f81c2d5180c01850b848900145510115206685041105100205180752a05a400c510703234001c0203151108212104000782c0c1d481a26001c6034050300c4014000c80c104039034100304000b4280603031111000c0b5241d081d440005400c54200b03800c542e0041c0c2c0284822042400100400400f0640554000304a860200380640304030070140402806085804c400805603402007005540895010b5401c056084003c030419000750454812940040e103600410300001203207070b00690249821400460180d400c280713660105815200c2a0b8140340708450700d18000c00e2712040904403251140c00c0140c1e9891078510b00070700701149078005550120250094005d034942d00d20886000d140001200e012595a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 826316492 1250 826315242 826315247
    0xb0f09070e091008010504150e06040308040204050c04090c11010c110a080a0302040e010306022a060a1a0d03080a05011401050a0c0213050103050313090b1c020d05030f130b07030816 80
    0x1c481d4000003556003860b00384010803a1000084c8c0303902d2540d101c01c2004a2101403034959402040d00c0180c08030b1000400300d805820b05400055104021455203031a0581c3c0783e002c40101c036031402c003660004a0000880303a40341c0003030184030300010191030303c65460079020303006030707203901c10620000c1046a0000e109107030140207406450040401020840c429a500d040400c0650f000ba20700c50012000c100a030101d03081d10480691103501c0c200002c002945d100d11885000703058100352185415441002403419a840382c0f4452000c91203681d900d01c040c1419080c3c60152041a0001e0390803440d03188969503036990140c1901c0c042c1c03200b4600002e40b07450301e0011034514a4421a450100d0381000004001c0c010000014981c0d0340038600c1c4001c0c002d903685140310446030110401640071a1291203482e07850039200c0400300407800103128107070440090b580c5610316807060b02000c00c01500480d4125a1340360a07080c041c010401e02e01c1c090316100450f50000e10103c0001c10002002d040e4a141c00710280c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 826317742 1250 826316492 826316521
    0xa03020d2a0e210f0709020f07080d1104171902100f112a0d08180402160b07081513180c06020f1015030b1b0a030b0f09070e09 56
    0x3c1c0e6600c46180c1d0010f03404001500e07004150511402442244800a004441c0f40b003112890a0b0480386d842c00c000159031424020392211b00c1c20307010a5141c1c070317034032200016441c01080144500d00c0b0f078282d6400340d020381030705010701c41d0340308100d00d504040c40e01b0158480c0403017006205d50b0786c5000c84840d80344030340036079018010300c0400d01070b80f10320030740c1485002090702c80c0950807520034400d10080462000b0130021004141000302943c506101e00d09015a07824007040d03804000410240c00d14101c08408808000c20f0724003170340c0c0c4107118001e0000a0703800880c1c00303070029408a00d40d0400000c0c40081010034503200302d01c800c0d01d50b40d8080042d0000d07c1d64940c0d02515442101e06012031341e102c0e4025030380c00d40d020320140c0704d0040000c000940c181520801d4001e51448001d1180645183c0703981c04550001440520208050f84c008501c103030049008110040360b0b910002001c04c3c000080c04940128540814052028441800220303034200302e48149040088030015041d03a1804a548140c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 826318992 1250 826317742 826317769
    0x506070f1e08040311030a0903060b0406030614010512061509040f08070c06121a10170406060e01060c050c0d051212011809020a031e080a03020d2a0e 66
    0x441c080d40300001a19801558240500d000741e0b83c003031404400340d031407031745900c555200300e130115488400c2000041c415800c2126048002040080e0362a42c9443e81e905a4100c1800394020030b0b00380005014500c2d004140e03200e218a00d8009100a14100005041d40c125641c90148034413212000038040066012628a645034031440741d81e03d07000c1501c0c0140d10b0000c280101c5000c100d54800f154455400c61280690369003402600200c00325840741440451040f00d4494010001d5400e82c1450516a1152090080380310703c40000b40585020880b00c7c810360181c01040c00c100116041001207200001c403800036045c2116005207841c0da03440c0907032502e440f100f041e144504020400120f02c0076403588060480d64900200f940c4001d80c40441d81c100d600009000b981711803248001c0c0301180c0082070fa840c1140d0140c0802680c0c0d07281d900c40b540b983d0404a000d41c002600040d0546420403207008a416400e600204c0f0050483e507440c0c051509004a504070b810000155040016607955900300720f040d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 826320242 1250 826318992 826319027
    0x3041b09020a05030601120c020706111507120b0d02060706022802010e010605030c01020618072301022103010902160602040f031b0308032205060a0b0112090506070f 73
    0x20b801c100d5a016202e60012588035001c04d8005514440c0000c05000e400071081d05540901642400d201c802da8152240201c103080c24451099988510384074029002d0080302d554990b80400c5081135525001d40707090184007401214007a4961005171240402d0b81c040310791103400903845036240840301c980c13440d042a28030390101c03100c603400c1c1c031558041d40150244010000288503807074039401070694500b414010301340164840f80000d0344200c4200800a680d0043d41d0550b03071a00d1352200605c50310076101c4414011400c01302d100003100e603010803103141103d410b59440401c6c00e01c9085070042f0b6000c14403402d10030f950001201d02271448840078610040340e2149007103403a0341d106c01e04c0640006240c0021103000524035504d0402e07210a825100c01c0340d5004c040b0a1441c2c0d9010130000e55400a02c90380302c4d0b8080e20300d541000080043c00007a200d070b0103042c070004078440b80314001404103004040468150b8a08000d00006c28408201c03144d0003038181c280b6907820300c44005c084070307400b0801c440c4000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 826321492 1250 826320242 826320247
    0x5010e1c030908010e030c030d152c0a0e07150c15140906090a030c170304062906192001050601030c08070c02090603160807050418020603041b0902 65
    0x8154002240710242d078180c2000f0404251076402051b500c0c450a178a0850303a500500480e8401c1a01e6000204201d0786407001015441e5501d4071140c00401036496012903001503810104000c09400800740e0101845005100301101d4061060301d6076880d0040242554106444090142c0600e240c6070003143d00190241c80b1540e40007070740c0f00511070f14028002c1c00081102042c4c45c0680060100c2c0220700e2000581050403d640d015100c1341c000c040f007282c00000390f090642000f107007503000c0c602c954001c1001007040b0403800981f60000f81c0403c0361030046c82e045e80000142ea1a40c205513030150681d1071021514036043d10083e41c1d60341c000c2205050702001c25903100a4564103401040c05a242038030180882032283c6c4040e0340d1075070200e41d49d10025074200c0f47c0390090725100d075419810501c081d0958905826503a6600d03018500c50f0007002c0650300840d0108801c3c2450302c03c0c000e206214181424008402d54005400c62001420203440c034900c1e2510028004010143e95004005a00c011075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 826322742 1250 826321492 826321549
    0x7050c070b04170706051225050a03060509010f030605130807030c0c090209150703030b061611030303040503031f08100501060e0315061207051512010b0408060105010e 74
    0x20258840c0c000d64403042c82d01c418400c0d0f005400207043c0244d800a44500f801c01240c1d05c00881d600b00300500341000320454000c5100c03445402d8821400102042d610fa44c3c0da4100083c0141c1511555800f00c0c0c01020b00b0001041104281208001603951015022860751034180c1082e43c04e600400303000d080342400140c00c1041640141d103010801e0f114100f5040c605640b00400000c03030050301201d0342c1103240e04803030000300c0c24040c00400800307100c0d0800280e80890b540104699412041424164601c4e440001040c00360800ca61380078032070110700442c990f184c1139442d191a0b00000c0d0080300206034501521703450450f5031b003100d406042880110340314207404501d80c501a080a01c03400703011546107101e0824504001c15048070481c484102d10360702c0d4489005000e00f15521980840d400d01034501d02180f0341e80c4244c10880b240088071805501ca0720307139000e000310002061740006400c8108010400040b400800c4c0e03181180d00908084030415692400310342c2141d084402c407411441c80030b0307031003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 826323992 1250 826322742 826322759
    0x60a0903020c0a090903080108030406050412050a0609060510050405040f0201140c010c080a0e1b0913060509070314070602061f033e15030c0c07090e2b0807050c07 72
    0xc00c5940245d1f0b0300c580c42c0e641c2d01105500c920407070040d0400150b04020510210000012240c4c1c400d10a0003140d00500d955141d81007200c210003c100d90241c4c0b40d07828003c006401e40080300c06003000715410040c6050581e00e0001c0c24240c114024180b204444d8844001c1002c88162480c403880d610003448174460807000205410411640c0d0204145051403885140310001030000315902c100700540a00d03003112081261400006003501c0e81d02c204032115074009041e03030103128000c945e503000806040e425031034815200d002c484d03200d840740e80c07005604000f980d07400030351250048010132990000060804040c45480500d070406007107912284944803010103007131f01c0e811512510400540010030484409000c0c07008124034180d00c5000b541709946c907440e82100840e0000500d4004500e001684180203051040701d90284a04503a01d000307540704079400b4008840700006111134a4445906103250700c000810040c516420000e2200002c1e04041c020030480b075207c000e80080340c02882d41d42c4d80c01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 826325242 1250 826323992 826324001
    0x405031c020d1b060e0f0a0803150d02060301170111042702030709090203130218311101090f0f0503011a1c060f0603151409060a0903020c0a09 63
    0x8040051003410281e0b00c07124400c4005490100e40c20318086030840c501d46a040241106100c05482c5009115a0400c030120404c081c92000e031141202c2522031034851282001c00078240841801600900303540e400581d40d99013106e0540b074100004451100b215504503005203804090800d882000003804205000c20082d03024213100c0031070320803840b00300d480c05d282c1c180e000075115403000c80c100703280a12134002c0e103401950340003020500c65808800305400003440c016071103102d401c10241010074416248100d4200068007007140944911800100ba40e081c2c035046258406404034403004080b07031540e80700b07422203801030025003040c0700f2254881d5a0100742441610400748a503280c80395504929002c446008001c0d00000d201b14210040360000343d4621a40303c1c03040302d480750703640116000c4618074480d00c405103001d100c2e0306c0c071484900d5401f403085902c140c840420441d8240300300903640384002038090f4803103480340c0007150084140c54241c1c42c01c1007015000da40301580b4070003c5000ba004d64070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 826326492 1250 826325242 826325293
    0x90c041401110309042d060f140f090a140f0702010c02010b0a03080918090a0317090606010318020d051b09010b0f1e07150c050a0c17040503 62
    0x3959140401400010341e5003500c44a945002504148042011072903d41c0c08143e4040369060110003070408445801e2844112511141c3c41650350402400441000e0040c1406032140851850304401003800048000d146820640e1081580c2c400107640c1c10690303044104400c01e080c1409903036041402c14400741c46d030308031900700040d071030440d1440a02d8414050450400005803507042c1d81400c54031403201c5a400f42c4620f40d0499070b55000345011050400c00b162082902c1d002a0000c0000ca00e0014220301c081c0e060301e020707100304c80240050254080340181c3c1144090034000342503a500e50445030341c1d400c4204040d600c00c4203d0018018420003044104006001c0080000c107084c68408105001c2004e00034441e606c4400d21000c00310280c032030020112030700c22001d48086010440150007a6900880381201e030481001c16408415000d4095025000c03003d081c06070601c0c070740c040c0c001e04401003000c000e06200ca4421500e0110004e42044401401018050700c124a1001c221400c50110303a02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 826327742 1250 826326492 826326509
    0x140f09040903121a0a050607020117012705070e040506120a08070b010902070b0c0309330a110f09130507050c0d050901050a0e040615091806120308090705090c04 71
    0x40b120100f04e00d040c505012540401050511510304103030138400a6001004c08906000703403d5020090f503202e6880072402421600841d200304039901201d18048110f10a000c075a09003020180f010494102c0a41940004141d4001402d56248400241042e864909035070700e50140403560b10600c00006c00030140540500903020903a643c541d2100120f1088042c0600b0440300d4501080035601214019904401050219040c042840c40c01c003506000b00b603025506032019204500b013601032580c4c0a90700052410081048a00a283c0350f80c03680300f0001c081c03d40c00000114918290754003608100305900c2c85608002600e01104040c0c80ca5100101a520621030405141e818038401c03001c032a807821041c0e451a0a00c50403000941d0380801240300160b1140d103812002c2540101540340d2501070906645a855152401c1c201d00c03845140448900c05c03181c1040d1080c0004207400e2804522a681440c10400c0f036a03c0100791414444680c200c41e40c400d5240041c0296005c404014200b500c2070326 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 826328992 1250 826327742 826327751
    0x90213080d091a0708030a1a101e0909020309031c02130909061803021b09010e1305071205010b040c051804021806070804080705060a140f0904090312 66
    0x801456585809480c0c40300c00040e40310b00c05011140e01c0110165003040486107180c02c1c90519503d41005410407113802c1c618955035145e403002810000c6980404a0064402e12810245594001c02014502c65100904648450409002c41c880c80000000304100701086480707042062646860380e00c41c0b1382d0710140f1140804584107160326442240c85c007980400c0700d0300f10b103840c2c65800b101403c0c140c0005e40f4019920080d0054084420410201451003a800b50220f10540d546846640141a81007800340d101940140400c88407844c103140c0240500301c0700e0b0700428213490710502c5d200407a04014880c00100d4100340810405400c84220520120760910620b5003503541205d46010340308110108603210403200549041c00da00520030200c101c09a241c010300c560003c1402984060401c4502c01700001d4100308400c800c0c807109015000480300c0601e23006005000510040f0200d00e5072000f800009200e0149000000c1107403031b030510241c8240b0060409040281c00c000e0800911821142003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 826330242 1250 826328992 826328999
    0x606080c0a06021f1815050a150305101a0307080609100c08042604170705090735012402010606050a08091510031101030525140301090213 61
    0x4543c84c0068003041d4084000d01c0c1c01c40e02040c02a05840c107000441504091004003c83d10100900300000091400440e10f410b052680d10201e44290b100201c03030001c81c2400388009180422074240c0603101070000300c1d1800224080743c2049210303005032680740c807072448001414900401c1c40c1d44181c0c0000159440f0801c0e002c0c0010a541c0101d15410001e959400014000380c17100242440d14020000c0e40c0035010280c4a195043d41d0041c0c201622803100c8006850401c001000002c000c1c1c107058550180c0e50420501c043c02110b51404040303005c4800102c050841c05581c85042d0300c160048048610740e503920020340e500100c6424500400e14512261004802d0050165100725916a503e50b49401c103c003e0456079003002510003000740c0115943c18280725800c201e11801201c50a55401c41580303145414842c5e1070720704424134181030510301000341400581d001414095001e580940c441007100804582068003504403030500308001c00081a40c003415400f03000d0749002e054025910684 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 826331492 1250 826330242 826330247
    0x3031103090a030b0a0e030409020403140312040b1905010b070201020f01090201090510030605030a03050a0206011a0f1804090c06110a05030d020c1c05120106170a05060d0606080c0a06 81
    0x5204186500324280350002c00010f604804e041d0b5008403444000118044041803080c00c2d03910136400600360a402180c10b009000603d070014206000321b0b8011031a000c0e452a0040d003010b401030015169803039041c00511a0701c4ca0000c201464804240700300055038480d13001d85096044070b20240e006100d00e090b001400e043c1441101c140d16016100d900da92450300301046003204007000000105a2038203c00569a00e0070400324000e00d100c1e40360340b43c40e4038503881c0c02868110b059100e62011001d1507585040080c0034021a446800540c0601d903440e5100101c41d01d42040c24100ca40d0003904e001c083c1c1081c800309100c201c082c0d6845a6429108400e20000e035a0342d00b003100750244c91a0410407685c1e160741105d03402002801c0340300c000e640000820310f048041843c0b028582c1d2000c214001960714046140b0b00060340034103520f08090240802e0344413080d1045a00030504503070382ea5514042541542e80a805042207544040c05010040e120b4107400c1d20b5024941000e03008540c5d6a401060450 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 826332742 1250 826331492 826331497
    0xd03140906040b06040b12071a0a0504120606030b070822030806040b031c080714030415090c05061602030c01081311060f03160210020a020d0507060b041503031103 72
    0x10940c1004150700c1e1516260103c4140d00582881e9100e69183c882e8002521000c0c1d20025980000c0c000d0007949180402c1401055030036807204088440030070410211a8005040d1707000ea0701030080c00c1c440900e85180c031038000c008a8001415502850381008010b65200f01c2c80b034803a2522041c800070010a0003001e04001028560090100da0880005205410140e00000c1010b000a044a40c100d10069103901c442001c0c000f09000100b0107003c00c03a030681c1044080c5010110705110a03e9841d16444071095001ca2030000c180040d103580001c4180110035644401614000702010750b50001e10b2308614103138003111006c81c0a409480100280b0350b01401c0c01900c203040a841d400c413000b5007543c0d607a0058a2403500316a20500038864440c4042d0b003400610300c554000389290051a040369800b905d0851074003c282e800714010082c045042e980030031600307016903844c20160f0312150030b450810050b10000c00c2c01d139003245c80d141e06402251361030303002001202e0080d25070000300050a92015101d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 826333992 1250 826332742 826332751
    0x406050301022d1b0a0c0503120d2c01090c0f140d030203070615230303190309060e0a120801050306060d0614070f0e2b0f140d0314 58
    0x1421194401010010090381261400d9082c0d00302625061342e01480701507034050424259944c2c0c0c41318910408101310401d8080c09010308030010f081a2594000e00b0003144a10180742d18030903150201a481e50781103501800240583d021040c40c02c80384038514a000307040e0310a00359150000740b440000c501d030107120642e007500d414210f48100001c0758030500030040036a030011800c6120030440007020030f8081c0704080001400c04036595041d40742200181500c01c04a88071034410034034035000b50040d6000422035070140c5001e00d008282083c01117003034001301218900545443c0c1058505103000c8000f0401c0b90791188107800c2110140d00c4403c0440d04402d0034040c4507015441040812800e250510700d07480c0252250001082d0303400d42034001610483c00b0340380380011600764100a44002e40100700340803284c400b580e00710001d035200010407020100000c10b0300b1416029060784424008210101401c068100d0a404070345a03943c18030b82d989100d0f038070711b2400291600c2c1041040400d180c0045000c0e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 826335242 1250 826333992 826334017
    0x7090b03061003090f0c2603190809010b0904050d08010602061b0f0f07110f0d0305030a05090309060705150a02270f04090602070b0609010f2d09050402040605030102 73
    0x21100e0600b401d90082c085401c0135034400d1038190081e4001010f201000d006030403a00c0c03a250b1030046240a1100100a0103c1d1414640003031003941080e16017101a68020701c8945060001074480814003030051100460042c0c008450008100a1010000f000c3c00c00000340d81d211602d0340c0c1d903010201c0e1151029156a6070078801e0802085641404001030100784c80650203452a00210701c03260900e55005038011200034080001006103407401c009550552131041c2c42603070400100785d40080c898400107043c038010555034004031f48400c604000b52140c4e0303900504075a543c0c000c0347c201150790303400000c4000101c04900000500c128014001d95044d04503000c1180c1c0101404c0640344800003204800c0d94110701c01c20001d60040d5107500071050100e00410b401379541c0b0460429140f03020000b4619402000034100400540000003014800c131400031480d901841440c00b900b4481c401e01340542002c15085150110b4803c50a511260155200316010044e00359100f0030b0500342c0c004c0f82c02e010074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 826336492 1250 826335242 826335259
    0x261009090f02031b010918020f1803010c02011e021602030109050303010e10030b15010210021321050a140a0b0a0518150c0d0e01020a0201020a12050c04060c0f0507030b07090b0306 79
    0xc1f010002a040b4035180c0840160408400e0022109981c01c1100c520610085200480040d41030078821101c4000880c4024000740203070300502c8002a100c15101000d9503030000760061464041c880210345580c1c018000d0280d5801428100c0d80c0780c10170f005101c01da1000b2030100d0380141c1121715109c01c803580040c00c0d9040e41e03641102461195050f481c004c0c154002d121000886a1191005210750543c0d2545444101d062140c80c07152a01420344880e00d101c4036000c001c01080300003c4444a180e40004902d500e003006985860620035203e2004040f81d600200f403185600c940d400c854410a042c040c0d10b01c0030462090b845d0350759035510f29605130101030075004c9440026041d0080400c1040590082502459075012a007243d228000b4680140d40c003141d9071009651007044040040c1c0710407003d00490400c0c200c89402c0784141e119801c1030200100e440f5040003510720f0b2110600d0b403c0700c03c0d10f9425580b414081c0e40744900711100000284040c9001c00e40300040000c0d02e00604001c3c10401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 826337742 1250 826336492 826336499
    0x4081009150203090a0b0103050609010f020c12030615070f02130506010f0e060912100b0604030b010501080601110102030f07110a110d03031e0b10261009090f02031b0109 75
    0xd5001030030084807030017040c44000228183c50b001d10b00844c8998020007480c83d00403402402c441c810a000c1030340c0f500410060080e00700c00540084d80c84d05800c10a07560391900000074081e80c111a894120100300400c050050042840e4007420b568001c0c0d03220900c0325100c155000460300b04441160108950005c2100034501c184540e049420f4054035482c40c2c0380901c40003c164401e400500403081d8889039042003c100603025117041c1d03503815a00e40d400c050465644950f0400c0500480341044124000280c2580c880c42e0040107014502c0002c40d540c1c2080c0c10f60705d44009088a4500206407962010322480300001280c095054100c40e83d801c84403200410003140c500d20000a0b801c050f25280b5218400c2042400b891136818164800281040d020307040c44440c2941100c40c0c001d2090701c11544440035a03034502038505a00c070f81c1901c40c07107075280c8035008221640c41e04521b400b2803601c1d420004204a54101d908410300840881d600704450721040c8140008000d01c044c009100c420041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 826338992 1250 826337742 826337783
    0x70210030225111806040e0a0f0b1b07210e0303040302010c0501020f0a020a1a01061205090a06060902090405010503030906040b07030c0f0b011715152404081009 71
    0xe0701140c45500e62500c0f050500000420320400c13420300d000030100c40d4090012030b1500340710b02038080050300081c103004040c644078106050744100d0003a25603124400000c140851010b04a1010580090400d40314811418041d60554810341c08c500324401c02c49070703145a14005d1498640c01040100214942400d55004503900507101c201150b166409000c80d917044071083c00982110714082e40284907074461820140800d504801c581840c8440390801413000b41e60200f030540800c14400c00c0803486071910401e0500d007171400c102c00b4007000d191180104400f0070325002802e46031401c84051056980f1901010380344c1c801c00c840c056110030704000401004c002c58010f4544e0764020704007103501d0320540c2c41c4c00202c0c0600c4c8400700c40c0e001146006114558040381c510000e0341250f0024482480d01c4c80c1400420540500381204080c006280501d441d96420f01c80c0d86103071450001c15440c1031080002410980207806051390354010003000445c10001413140e99046a00605104802c0c52800340c0b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 826340242 1250 826338992 826339057
    0x7081902070c090603050303061c11040c0c120518060903030a0305130b0f07110307020f0123040e01030c170c150706020a080726190b090109020702100302 68
    0x45490031103803003001850642038802e1800840c06440030359600c0c079006040241d2590742d41500e4648048ac0200c2030702042c9400c8118070101c0013034400050280305002d0a65204020b0300004250b107844a4008820036440005018115110030314000c0c0c0f4110b00303040011038040c030f00c48140c16038010302551114070b00c00d410083e00101014200b4844440a8031114940001100c42100c040d84182c2401071f0540d1280d1142806040e61000d141070580c02d600084a28600104460411040c8001e00311010b5204040101c2003100001c019030700c69441c506641903180c244020394581640c5000021080454040542c01d00c46a0300506803186d0380d1410000d00c0c0141400301c0010800610803880052214401049405038075102e8500c54a0840c0300101645d508009110320031141c0400c7c8020318030b176911010741140c00f00d420003d10138107013030406000381840e0201e560f1140c440704c000210000e40d9402003410a009540030345210016210a40581c480c0c40d0080a40101d14104809481d03a91201c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 826341492 1250 826340242 826340257
    0xa050706050a052502030d030209030c060304240f0c020106080f0f0d2a0b10050a060504091d12040306060f0501050901110c0910090f1404020603040f0807081207081902 74
    0x8496800019a00481e02d807c481c52000408207500040da07640a184c00c1045101142c0300310f94652461034141e0700c20b5001c580c1d901a41e10500c070102408181c1c42070641025101c1c2c13014160800c000100540000e0190089204c0c170310ba14020070003442c4103814041941c2c3e17492284e0f00c008000780720340c821048844600c0480d131590b044609104406180d049014000c40c1c142c007a1241c0826810044008a0019100d1b03200500c540c907001030410820740c01500fa5001c40310800750004241905115161280c40c0c100c02024580c01160010083c1003804805841503a000d1300013042042d803039400c0804400d085010302804103a040c007500b00c0641c41010f50590540c4c2e18400c3c1e0f002d90480c1c4000c6000c4001c01d44000490950744501800341c0103680c4a10310340460888000c1c081000c0b050070204c00c1c2c0c4806031000c1d004000000006d0240003104540e460b066901801d015030301d002d00c0c28070340340c00d4003c00100420b01c103024001c03803646072144050314055038405150344644140100544020343c001107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 826342742 1250 826341492 826341547
    0x90203160f0e03010c09140307051e06071b03050607030903080115120c0519021209041d0607120605091b0a0e1c020901050a030b0a0203041e03020a050706050a05 71
    0x5005082c592800e0007880044800c54450a0f601420801c6440b04a00d078941c000e07000340d00c91942080659140300800c4002c1e22000709010311030b4101800710b0030300c4c8140ca1026204442c090015010208407880040c21680190151b4001e40c850307260807001d17940e6006028001581140052014051940f501740c2400c60a0500ba280c049850400200740d840310350841c00400e07000702d002502001da440c2e210000002e14409001c01d00607905a0300c0190241c40c2000d4040e903520702200c08801c0314014803061809010b011031744079140100c0000e2000d0030100b48009a2403c1140000d043d0410085c072900403140981c505002440101204500740c000329031000401800c100700e00b0460320345000654010403a04292681076a01d0b0051025680c81a404075002e00b040143c1000071642800c00c180d00072420030b20250340d070740703440c1844000210140303c0b000c1c05030029040001055000298140b0242c86801980d110b0f0f6602d400985281c06010440d0010440c00c000044144043c40b48034010407040c0b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 826343992 1250 826342742 826342757
    0x70905100e0c0d0e0a0b1506040815060607141b1f030e070f0b09120606011d040207022e0219030c0501060f08060f0606070c171005160306090203160f 66
    0x1680702c079241081c6141c042e06e01c2840e030003d00c102c241d4020a070080e01d00d001d03250145418603001000756036111005803801c4038030101c00402d009a45000403900015040004804030140751442e0f0350300c60803426a414035600d1984d00d041c50508000460072001c8034484623a03082038000c400294050511101e62403c20300507440086200301e14141020043c3c07505403400c0c0e480d50704d11802e0004500304048102010381c0f04000300030081e0703408a101c02c031800d082d01e103032282d03070300c580c404280a4050004001d40c462104004402540c18010724043c805401c010441390200d10a40c0c00d03a00c91200024183c0d00c02c55a5041802090054a06030880c0d445880005402c40e62100700042d1850207820071b4045402890501001d0304a111069802840440303009103000c9055039800720300107503413003156211101c210341740d0155003061042802c0c0c2d41e42d001080c031280ca410761340b40d03800020001d0784c0030100f0b00d0700c2030104020091f0710980703210b8a1380203501000300105180958480030090f04000803c56035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 826345242 1250 826343992 826344011
    0xa03050d02070302010806042a0908010c08152b020f060415091a071514090102190305150616080f07060b0603040c090c11010e070905100e0c0d 63
    0x10031664612040550180c0305060562000400035070b00580220311881c1410081c016140c3c00c564803c070010254001c000c02c0721034118042d2903a0169502c41d14055103004001c84642d0f400c1100c00d80b05002005036407449403d440100314181c040d180729102a441d1034910f45c20a03010780c002c1100c2c1e0701d00040c0514082180d03400000c07415030003500001609100ca4003541d40d40e81d0032050f9100940009200610322441000d00d080c4d0502610070042c4c54081e8170074070b070541d0b8100383e44101d104003007414400403980b5240004070b005c0d5110411090aa91480b444580200d2003846028080c16161948070364810004040010300d401903a524015917000050706400038900d14000c1400c0c42d50002c03125241d5600b400c04000b1a0340c03003840705001ea9004c0040000144a452000e0f00383c4184c2840001e00d4241c580003203070071180e00c21001091398138094407442032440028126040341d2442e10244500e9032072103e401e081191034418856800b044002059402c1c200c0c40c05450199000000020385440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 826346492 1250 826345242 826345253
    0x6010609230906150309010b1c08091516110a0f081f060509011706060f210c061201150c03141e03010308030a050f0720150408120a0b1305060a03 64
    0x5c2592622105d039928074444049003810750610315080c050b10b24080d280070868403604c0d07140c450882500e200740309404090021401c3c80b410f440605c8024042d1140d41c549900d4150740c0c405c0c8540c12203210b0a800701d80084c03100312000620003a600c0e200040c105081c1070300642d00111000840441d91340c0e444210208050300c0c2d080700c072030080907002074411000440714607090500b000a000240245048000c03c009500c904540c05c0d5030703107648441e610240108451690401a11404155001e130002580314244080307041e000d4181c1d20301440c204115840309505035051500310700014085240702c070400c00c0020b403400103000e101c04902c10b030303640c10003e101c20120554800d0b00112141c07000801030080709001c07449041c0e403000741060840c4003070802e03041c081c08001d1000202e05601e4040052000c10b04803d00038089081100c140c2c5006a080a150038010342d0005404079140c1c02520000490025003401000d02180000c2d140350f4180c4100d0303040c08041c2c4801000c00b908502000780001c00920b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 826347742 1250 826346492 826346497
    0x30a1707050d02071701020a0507151e0f0e0109030e091008030304060905150709180204051207170a020603071409120102091005070b2a03090601060923090615 70
    0x10403e40c0039003426400c1525600103100040149121a8814401103403050380000403940101d802100c490079a8000a2449006d810441e40240283d0b2480100c3c0d451214190012b02010800c0740d0207010b92026071450a0882c2d0904402500060380501c0411036030800e04141c3d44c22a00013015411359613181d42481d0b1035580291000c4030000d503904981014803109200740c0d41c0c440e624100b074441d0b03030a0031900208130302e6190007a01c2c2c58031941d40303e0b5026090594111002044094a142c4c03a0b515070059080c0ca800f800d01c80c0e001130301545114284600400f00d06110803990080c0342c00d0864407885821100c0070400814204092070070000c4910594525840d8803c105420002590f519004400d201800141010410a00406000360742c001120165000d5010040c400c0000b600c3c40300c14010400302c0c26643c2c41c208548400410b02c41074210101d030f1390f03040c2c0301251204525980c0e03425540000a48100c01c1c803101561001e0f00c00d4885c51704000c0c45402c4407004214129444007401d0140096 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 826348992 1250 826347742 826347763
    0x5010c051504080301060305010e190c0504080a3203030a021602030f01060305010b06160807020a0e010e070323180709060f0f12050d051606020301090b090a020306030a170705 77
    0x200f408401000201c0d81405000d02400140396004030600b4034200c060f01d070701d450f058000281d03612450b02c1184103200380240e4004140001c111001d089480c241284c41402c1a10015564a880501219940e04203100c00b080c0c03002c030300000c51075aa070b2890f006000b500b0401284101e180618001c20160b03408111032400c1d0807209000040c4289035241880c00c5032804d07066540a80000d008203540c1903403800000f40c041e40c1041806907900f0003440010100c46554000d0010003810000200b41c104016418070321405581d1410030001d400c140c000791000d00811108020020840002010b0340304070348200741140c078035800701c800300e5403142d1113041070702c01c03641149a0300a540e42080201044a000190081482800081d0580900d458840c0c440180d450f54030203015000541104220210b00030790010303500180110b4581d6121a6103402504201a290344180c1200c030115030560014422a4000c03e401030040894038030941c0d44410f0000000c810743d18054050201c100414018010400031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 826350242 1250 826348992 826349003
    0x201021e0a020405090327030c0d06020c0a0f050d140d020c0109020301110a020705091e13150506010305062b050c060406210e03040608091c021b090f0105010c051504 73
    0x4a2002e540c0180847c1481540e070307820140756542c0420603440120742e05500340f070181c5da00e00716a501ca0034030700007038821416041803501c548040c0b60306210502c0d80c2c148105201d9019100350151401040340d4290f51040e8045c0040350401203050201c4456000f84040c044d00c00010403284030540003c0e00b116039a040c41a00d1640004001e41c421341e0501c0b458010f00000c8401d0841c1e414141c0d003000d0001ea0803100b0804242914000c540c3c0005c10094204805510200380700600744210a0784010385802c0d10014082410900440e41d14500000402d982c03582c480f54951007825a58a01070070301c40c100009031082d02943c10031440c162900b5004102130861a1210442100320014600302074803034030150f803c0e00341b9000841d90941404001c5070200d40c0750f03150a003c0c0d92142c001142c2402034400000f40c0320f076050748400c14180d4001c11034084100c100d028204800001e078050080f03c0d00d013222070b04850008440180015030042800804540c040d00c11103c50400c2c2104510030340741e050790180c42 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 826351492 1250 826350242 826350247
    0x914010606091a18040903090f0603060603050f06010c020603190203040602090102250e04080412061506030606230c0d05070b070c0308060f0301020d0f09020f0306040201021e0a0204050903 83
    0xa04400b82048143c0b082000d40a403a0080034035610309520b0340c071030081384640c0d00c9542480501d44204402c0b03000c0c0680380482003050750384010103801044c1510501300420304010006101c2070501107540e10644068444004e504102d0f0708203d55a40000d01c050701d01d03070800001c088100701d5072010310311652081d00010380c1c5550181c006458080b00304000245d4455415440c8260b2200491220484950340d0010480391a145440c50340f60003680c11032020344c00c000b2110024494103411409900d09034030641043c0c241c035071500710251f46103030103842c004c0364001540035a00700300c150040007000600d444090034201082c842c241003900c41c4407510700040022440005201c3c0c0c1c5040160040d085080c0882a05015500074000c2c01009000078880c0c8400c601016813074a0a40445403080903a0000700518501e0301010710091a600c0d8050717001301c84070f458541c1641000616240190740507001000200c10f0100c1c07182c103c0340710310104011802091000710068855000f0700d03005d001e10502035038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 826352742 1250 826351492 826351499
    0x50403030608190c0b04060912170f090406141005030a11070b1f0e01030803060d020a08340e19020712080a090206030c0a0512070c050616080109091401060609 70
    0x144084820782017600071040402041204a4001182d0000c503595030803c210310884508041e00207200040b01203c01c086e001030040c940b03825030b4000700860360b01110108959501d404170f002c0c003030100c1114560006488452441c005000b0405598802d02c05080030442e125400c00101041d0802c181c03c81e00000c40009001103590107420001e0701003202440d042c3d010b0300d06200390310345200c10310014145090000201d07880d901c400140000e080c5d0041d044014084d82d9607011036881003004949500b108103031034840c034001d1000342c50f15206422000c800e640315042c2001258440d4001d03249609043c3c203421a090f5000c01800900702040c05920506a800300d03002c009030041a005042410840c5408820f00051783e409083d02d800500280344552a5108800103030340c14490360300224100701e1940b08100c030041d03001101e481740368420003c0c0c0d01291113541c0014070840004980e0030101c0c100b42c005006120155102e2202c0e2401003449941003840c0d0164103084030026003000d00040d1070301c1c0061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 826353992 1250 826352742 826352753
    0x9341d10060219080c010917040f0e131202070e04050c0a050103021e0d090503070f1103061014010302190806040c050f161a1f14031005040303060819 66
    0x100041065001070072400e18112070118031820f40000c01020031002081004c280f1909501441da5240c0c0412106da1a024448089885400a1052001540a846001c13400b0202c0c5110305004610030000e060400c6c0280e564400041005002141148a61880019641c0c211010580558044d0026180c0e09007a50203100c4d40c005150044e82c10300d401000f0110746658105200d0f4810701380c0c00030b05c6403140307500c20000c809808100c01c0602603120100d41170003400041c400401c0018424070906a800d072014082c1900c802d001c40310303100e040744801c41c20020111b100c0000a600c0c00c0501d4014500070013000b0741600071003000d420800007070a207020030810f400c161040c0c240e11007c5041060606517080841805489406501e032108000e090740711042288100481400700386845610400e03181c65076614500d0318864542e1550240206000543d000310401200f03000c0c1405009080030320410581480034001c0944100d08260b9151000102014144240039064a200c845c00c1524400e60502 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 826355242 1250 826353992 826354021
    0xf041e05012408071d03031b1006180b0315090d0207081b01120605180f0109050606071e0b010f09140603031611030604031709341d 58
    0xd8219501e640d030b40740941d80c024400d507a211900b440d0104610340c07081c1003020080395030100c3d035030584000302d0048040c403030801400d5040003030a03084441c18180051610140e035002d1180000e90400c00c1703030340040203100c4d80101c09074000c0541200e03d1002c1c540c203c1403084070216071502694104100400700564144041001001e40e200140024034007200b40942d80c00e52400354034140110b0382e000415030043d07900725100a00004126030a0005400010b2442c0c030411103410010a1004002050701c800c50302c1a40d010741d1001d441d16080451640c2e2b001e0079004961107034003d1031104452400040c036141400c5010300740310300340102600c0c5001200b200f66140c403103105103c041594204045520000f00350340d0045e03160000421811f41c581800d100b0601a0003150b50140544030402040c15006038643c60520f42c0d1500400380342e60b69450780f0340c9400301c100c2d0403d803001c00945070420002a0461540041c03000303018000f8080e540708090002d02e018007011400c0904032104005420b40c84212 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 826356492 1250 826355242 826355279
    0xa0c02090f01210c05040c0207092a0c0c03120309060903050903010b040204030b27070909120503041a090c041b0813030503040807080d1d07050f0604050f041e0501 72
    0x3501c1c000074400760740c4c690b280001401824002c564500b0020784551007000510000c0000080800801100c0c150824001c5c480b02110380f09a1540b001540f012403240c050b01c82e403c3d0704000808800d0341155207807440946462030b25010182c4902c01080400c926204030700c4510701c81d484a0b40c1e07400c1c0c2c403010303d03083d940031640091085205100030000300b00030540940e0301c42d0060031301e003412010156085030610032100c48a5210300c2884c030085040c2310203501095020f40140c428800020100c1001c0311a0b10080b0b4000388288000344400c1654084074103000d811003900401c1e5495480654042011683c04450103128181110604451160010260344d0099420700c00140452002e8130040c0407440050070040400500181e0702047c0080f60007556030400040006000f8168002d801c441c50188220056116004448002440346444506400c58a0018202d54205482d0408200310381541c550390580041c0c41c1d03180c840c4010400d26070080c10107184000060994140412040c90111407030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 826357742 1250 826356492 826356539
    0x9080105060f1302031b0309011a040204080d12020f0c010504110301020309070e0a060905040b0601030f1a01030e150106090905090309060f0304020a050303031008101506050a0c02090f01 82
    0x800145180c3c07070702d0650001c110b06101c00540e89031600c12601903a1001e03040f052429079004001d0150416040d080081d00070000c0803600455040e80c0c04120480c400c600c1070700038990181098543c0301d40502072003192803085200c01420b000304481d45070b400e41d01001a080703081c0d540300200410030044034042d840344101500214158a031041490b82c1d05c035240d00a544045007500001080a409900010040c100c110300922060a080c44c0180d055042602c6490200b0b0500745031101010740790bc00c1e1061000714203540360761100c0c0e14005400031301c145001000f0074050104c25420407414102c00900800140d40c820341100d1a11501904a84000c1c1c0b1403d01c98000300807020140d52032800ba214044d003803500090b96034541e440003401350b210960003680c2600012041000303100c181c0c400c0200716030400d81500c02c0b5200c4c008101003210b040441d518000c0340308900170b204940c864005000200082d0074a0701c5d41c6089a00001c200c3c031011a442c1030400701e00c000500c8504003414000c0c01160110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 826358992 1250 826357742 826357759
    0xc1101020c0c13090606090b01020c0108040b0606090d0822090506060409110702030d02010b100e091303020f1912020a020d1b18020307031131080d0908010506 70
    0x22508039242ca494010061084540800c80f83e00300315154002c0c0c3d07800780e009030104443c40d0b440b6007103809004080150781c094042c1403086043c650080d81003600c102c0c1e000e640308400359108020041c594120300c02e0150094a0354886c02c0c0003c511000410040c3c880030030016041d11140c15910800b81260400e68030709083c00148950750312941c0680d410f84011540103c4c80040c1030791044454000e29001030740c540300d10b540649800e81c065008085003d4180c0d101d12030720401031000c3d83c3c2040d8500b11a90048000000a29041c07208034075007130a5803080c41035900203140c06100c186401720074058204110602440e910800013055440c0d4110541e40c0058025581e0580001c3c00c03450300c0340e0000d044e000c4e000e11019280f002071160500505040d8840e080000508010030000b50400c80742180801c0ca01045640054090f100b518150040311000700b4107440c0c0d03007295000c40c941c04040500c0303c00000304042407190003030102e410762088a6480c40f082c240352003080c0d0300f036680103840030b8000c0348035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 826360242 1250 826358992 826359007
    0x1107050721031b060209040218090105310b03070b0c0616120e160905011802030f0a0b0a120f05062a031003021519081006030911090a0c110102 63
    0x440410032030801140414001c0144505204004e4801d400c0601d42c000d20004528482741040d80c4090a041d000791112492a0388a10a200114035000041240c6e02076012070368070303400c20b8a21149030a4030340345400b146118002d00424901695034028503c032100108000550403000c21600f030b407105034005100000714032820041d06440340c404900c680c1035202c880101104804104801c242c99010003a94043c80da500302c1c00e0001c0c8428001e441c00c5041c090319070f03200072109009980c000d10424001003440d4543d40103801c010810310580782d0b0410a0801c2c0084c0a0807840c400d851017501502d100416488580340c000e007420340091030502c0c0b490000c01514902c05010203c40c03400c44011602d581e1307035101c00100000ca01800d07803000707603c044040450080e045110010708401c890b12110304015010468054880d48000c48174000300c00302c810070030000d080c0300c0d401a0802600443c08660500000c0e404610004811140e981038203403114034503403640350300c0008404100c0405c0001c6040c10036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 826361492 1250 826360242 826360247
    0x13090f03082509150c051b030c0d080901110c0a09050f07080106050904021e0f070b1005010c0f02120a0c0f0605130312140c070614160b0901110705072103 68
    0x10b8001c290a80316032000d0042468059011005e00e00d8100c03044854030300070a140101000000020f40b4001e00651250071040e0520894005c1c0c1ca0798081d031144e0801c502d0000441e101b05043c03070403400d584940520900c282c2c8a0b000c14030083c0201607070106040c41d04a80000c0308002c0036001408001350b0000410445a22000359121540d0454000d07955548412011b070703007170111042c0c0d2025100001050301140000d04010100b030f034403c1c10f020703003941d540029110002d603403841180d01184002c800100055405900c0c0c0384028030080c4110307540c5075a0141c062a00010714030449800b030410805015058080030008010b00c40c1b0f18140745800d07066000f440c075402c01448001c00c1603408034540d9085078010040e006c042e40c0004455030302d801d40013100d42e943e0f090030b00c580b101003940c80401c50040030740700044130640c0803408822200740900c1c0d92000c040700c00c01042c04109558070b09000014108088c02030000500a0009100c124242910340c022814140a0461540c3c80c0003030390b1001a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 826362742 1250 826361492 826361507
    0xc1c0507080c09010f051305090108030304050d050c0a03051303151d0c03100b0102010e031201090609060501051207051605060108071d160e090c030907090e0c13090f030825 76
    0xc5ca250042d25840852504082400f06400007035100c07403141e001280c521400030280d841940900104c5e000b100074054240c910b8801c0d10b400004a801100289010a02501c014640c0300c10448903000425a603031521099051040b0f0406400ba440e160070360302c60843c0300c40a13480c01d04008040e241c41040840002d545900310040758440f547c40320980c078600da000307600c0302e0700442403841a265610400d0140138a20705090044115052401401280b081c90380e11982050387c030103840f07452401090396010052418010b101d041040400c01002c0e0f01070700c41d43c4594540d01e110380c0041041d54101505130381000c500ea000480340c0d0b00d5811301d1642400100942035000b032024445c880354032444880c1114030074295011580c008501c001404030040b4844003c0d4807403981e04d03090781c41040c2c0b64070760441074581e80d410885456010610407034007031034545903c02e402001d141c1d00181030100c0342d40c0d8400d003100c1510160081007240081004c050200f00c0c00351004a000c064881121044013809840003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 826363992 1250 826362742 826362767
    0x10501050d140703020303040e10060e090109022212020a08011109121005040b070201050906090d0509040e100212010f0b04030b070e19060e0102030708040b030c1c0507080c0901 78
    0x10b00c00c002401440a1003204061600a004c0d2651103403030392400c80d0b0b8151f0070b5072119041400e4000005425101e01d1090301d0380d000c0244520102e910b0000c4490194001d02504034003142d5074400d001e25a500806040300509480500d0509010580100301004001d588516126414210340740003030700da10030849060800440c0c084440500c81c1d90007903e081c41c802040c0100c68a0802030200f0700600c0a0300d581b00320025070003405142e4800484075103921098941d040254064545040303407a0103040505081c0c00064000070350842001042840c100d80190382c82282a40043c084841c010b105403c0b5000d0000c410003410300902e004080340c2c2d507203e180300c090040108000820000ba11842400d8041c000c01044046401218085075914101303511403040451460050052039500100580c1d901030f070800c2000d41002d2404420068991004005150460041007a900000482c003101048100c41081c0020036151215004d0301d8030b80080c00e0070400e03150500481c00c03682e901c9900c900c1c0c170 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 826365242 1250 826363992 826364003
    0x610030204082e18060c111c0e06030f01030c0602030a020d0e18150a06030e030334080a05070509092a0c0615120601030f05120409020a09050102010501050d 69
    0x3107181e0f5003040118200000e070322141442c02d00f04490850080449400032a034050304081140300f04c0c003101a58010300702d0343c10183c0c1c0c1d04298090740c41502c481d808811014070600345000141c2c0050300040c0d542d4022141038056400141c014170a01c21003065a80141c0f4403400103524055400d10007039074a220034042e80b0200604050341402644a03041d030b018110500459034902410483c0d03c0c0110000141d07100ca015101030300c00010040c0c444c1c0603030891070140102071031440e00d441c8024945210900455608428902d42c40c2510a003182001c40b40d91500e42d85414141c00d10303107112010788802400400800030140280c01556031031030103494102e10000d405078a60080c0c603400019481085000e08018100850441c0c0d404d00301144a5115446900400428400000c00c00a01101c1c8601526030303640180014000120440da9204502d406181100c115110001d44100c2560260b002581829000710f5580c0003260001301c80805400240002e10281d81040003003030824500c2c0c0c501812 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 826366492 1250 826365242 826365283
    0x803040503042105010506100e1e06120f16090b0c0a080d02210c040e0705090301050114091303050d09020105041205010204170703080417010b090f061003020408 71
    0x108403042003114020400c454000c940352001c03030020310307900d60f90041c01d558950a10740021418a80381d1104421002c070350712580748041a840900c0b10810000506409118040702109036654406014040106040b040e405003840c00c4000c1c10a0510060452801074055482080d100c5411400f140c00b501d02481480d6111201a01001d00d0140f81180182400c840081c00c000c2c031001540061643d440c0602c1544012800c0c51011204071900316075440459105000074400340802d22a410b81081c1c1030725103107040c2040c80002130b003154001c1e840383e444201128501e0145042c240c21059105c0c0003d5401c0c0000450358601402a102d60942982256906d40d030311011680a00140c40141001c1060b001c1800460300e801c80c000e6000b409074908000007003072030312501900001d250342600e50002d00c1d1410702d40340c07500749807880031040070f11019075407216a40b901d1750725204405485920180d8014046041c008140410b04200241003002c050040000b8008040001510480450552100e41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 826367742 1250 826366492 826366501
    0x5030405150405011d07180b0312030a051618091e1b03061e0902070602090904050d08090a2d0c17150402090601110c042901090e01030803 61
    0x50600d00d0703400e29580c1c540d000c002403200740302055100d258000039440c0b00c2901c040c0c1d03498080f80d03a101e41c0d1150404000e0081d06442c2d03a5140b54100c4241c0a40150454602110510040019810881d81090400d994408000400403050709610082c0300900302420301110800e0101d106032107900405180a07155080001c44030702001c000d000b40310b0740c0942003052032000e4030b040b0301005c112403603680001e040c03810110741c010a049942e5203403c604c2c500e51010615100740c00000c1e4001442c180c902c41d50a024159850f03c1e1000b0383d40c031451058025000d4121001c1015011017009484960181c0c82a48104005000c260350f442d00b442652480e09685030380244060840d54007402c0c000c01c5602d1140000518100300000c10700087d81040986a1210505400a07070081342141c02a40c08138000010800550050410100f00da2251040d10302a00c42c0d4000305042c3d507a040101c18520482d80842001401032035191101c0b00740034a00100d2407854025544410355040c003000e0883d820000209 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 826368992 1250 826367742 826367753
    0x20d030533150d020309010b0901060203041e120302010507121e09050a02061306020601121a0703060305010501080d120902010e1005040f0b0316110d03110c0105040f0510020712050304 81
    0x208180c500b02c0c141c141d0782d01c40900600780650030654040403c4c0d828400008000e01d003882c4800d0684400c1d0340110700f401c1c6820f8840200440346c2c000c0d0407804009010102d2005a0b206a24151038007035000800d183c28907250040c404480180765007401403401c80c0076540211082040c1084c2815800040b0303410019042150401441c00f10003940600f0000e418005c8010603040c11082300d040340c00381d54150b80e0f105c1004c0e10800c0000002000742c2442034800f032440e00b1410b0550b401030014900060502e031070750b4425013100d00c02c0e04204a25072014030b101010319409950381c90342075107003402804004030f1540081d101100340c1658603c00c68400c0a1880214130a4083ea4001c003400c49401d4080750b41d512002000f54002d4491100b114441c840c0d80d0f2580780541c01c01d43c600c02e0303800c0044c0102114440110020000c0d4030b0341d400300560401560003104c80901946004038025041e44034201258541286415003400e4000d026500502070f280c08502001103164508078142000f82e9030360340d1458074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 826370242 1250 826368992 826369009
    0x2130c0e1e040b031f0b010908010e100c0c0203070f050f040608062a0a050301063e01020d1406012003040608060409050a0b0f0114060706020f0405060406020d030533 73
    0x196810060070a1207266602298001c0d0000301b20a0b03e03460006601c40d0b200600307a83c002c00411445900500b00044007907040c5c1c0c4000600c1c0d009107488104420030781c0c0003070305005440e800f24064001b500018030030352903c0765100e042520204e40410010f840c0103a40d90724bc510040240d000a010240c4200703140500c4c10001c0103c420380190507980301418100900035820038090308000528075004100e0884c842078a80d024800e4040420002c0303030a00710588481c000488490710a55003c4c005850034541c1401801549050483c0c00d42c21413030120001841c2c1280c00c000b110402801c0b14441001c02408003c40301994003620308100a03030b0744c2e0000b080143c403190300010240d1150780308180c18008688400380c015007010000c50780d1642c0e035540121030050301000310360b030005003002448005032140d402021001221003640b400c00d541c035030015000d030304554401e0703000d6044a055051313103035414800c2030ba01001201d80071045c48645400781c000c4a4030016000d10005c0d2488402d407955a51002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 826371492 1250 826370242 826370263
    0xa0c1e02120f06090c010c060c0e2d061216120e070810060f140114400608060301061a0c0f0105010f121505240a060c0f0f02130c0e1e040b03 62
    0x45500032f22612190107400c40001e4401002c1c04201c42d0200c4500d880011621680100c82c00c0c038801d6200c10424410f01d403983c046050512540300c0b400c240c5c074804c40c09140355400c2a0740140000510301407040342001c40c50303243d40c0c00891410b042031000000b4004c142017a542101010320010813481c00507183c0311940e001020000002181e01580001d190118403114219030101d0640c8000e00b0791450403188011581c401d0107411b0640c103000280c492070140b03170302000003000820300380c4c0d4840e01c8811600d49500d02e040c00042c0060b44004d8417401b0007242d202c0c00a000004c01c4558034202280d1015540d5016040b00588401d107076405203c0f90148804405009520801450604644014070001d8041c92012200032242000a252404a030305200701e030525140d00820035559640c3c40314040c0412001c42d02d005a400c544070158031620480c46042c2d00d490b10000c1e41e0f1701b0540d00070301400702c01e601103882042e4004c41c9000f031240a07211a101c2c0d10003560003080210360100081c1c00e00d0f60114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 826372742 1250 826371492 826371499
    0xb010509100e040312050f06010201150f050613030803040b04120c0b0f0703021b070f050301090503040918060207050d0e0319140f1006031101050a0c1e02120f06090c010c060c0e 78
    0x41c00e007d1000e4208158502441090f0020081c0b040c10541d0003104034001c2c450390424482c0301d030003000701d42800e000400505252901c01c1c3d55041d2a0f90b524522600203403000e44466803a1010041085062210081014420300b050307000480c42d95951003165400400760b02481000d0008180154000d406070f1707449684801c503101101c5507a99031180d07240ac0a1080f9007811a04440004d503d040c180701780c080842d00103014510301410220354a01801c0c540d100030981c04059440000468501c4c0b01400a03588248003500702c04003801c400400001000340f080f842600010f003a0382d40540f64009940185510000c1003901c13040354182a82443c640040c4401c0318020300d000c00183e0b0b1075a03441207056900c155038a00c0741301c285100450340f42c01f50502ca44e01003011012540c000c225081c4c55903015411b40c0d56240b144200b140c0c08102d03038504040406180b54070001c8006403040c030502200758400403410091620725007040000b800507002d11005065036584450b1480214401d10026044c00300c003a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 826373992 1250 826372742 826372751
    0x1602030d0c020906040614040b01020f1603030306090e03031501120e03030f0703020f0304030c050703170c10020a020309060c010e070303020a03020d09120210021015030b010509100e040312 83
    0x1102410554660000b03d129030000400124140303082c0c4074503400d4075a40c210007001d500f00101444000d160280b0340b107041d8031079003491000c10441044a210403042080350300703000602c2d6103006810740b40603400921190741442281241002c00006032644201034004108502440c4001a03810071000c8601001c0d00d41010703c1900e030f100d07001000394010504402107101a5032016412001c90151440300401084100041000300344a21259290386020344103603241140d4a54810484c00841140c11548080104580c40482030038840ea00c24008510700039807800c078130f58030002d407284103401c2484e21401c400301d45041c40301b80952052400d800c40d03000310394009840c2c3c1400303551411811002c80044c8100f080414450f031003554170300200c0b101004404803050351982005008a203d0300407030214480c44418480027031803400380e001154541994012401d0a5040c55000c0f1107058202038001c2080300c0900c850302d084070481500315448184624060346403890100c0d810038016400000c05c5081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 826375242 1250 826373992 826374013
    0x140a150803191106011401180e0f070e121e0a0209090c032b05071e12110615060f220504050112020d06051b070501060e181002160203 59
    0x4010010244220342c07a0f003103103140303000c0c001941c0700300074042d0080000096002e4012540141d00e00424070f007040c101003e0054440b07030f0800c40d429048480f9514007410000f8418640d0f005500d100783c1000a5404944003455084480e0391281e8030800380703224130414000600c00b12014020f000d440ca03402000c6c2942030511a460f1039849101060079842402040301440918541d910004015402e0f110308401c9038030340403001da80c0b17900200d000f6150080340012200c0d42c2a05445004002c504c100e900940100c9034480007802c5050060140180d0381c09002404000d0402202030060b16a080f680c4a0756861800c0b8440028010240b203000b802045008070f500e038443e03080c2805c0031703544180c0d4204040c0e0780e40d000d18000300c41901c102942201e2102c0140000c0380954200d00d50100c100e05e00b504410404000c94603003a806800c095885940d103e82c00d20030b941c42041025089180714040340c001c3c482805206488c0c2041070014000264000f034208103c1007016420f0201c1030b00142650504002c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 826376492 1250 826375242 826375267
    0x1011010f09170c060a020702040e06090609071e031407030507090b1503010302090a0b27040c050102030f0a0c0f02060417060c0a0c11030304090e07090b0103140a150803 74
    0x1900d000803101400c0b82414100c42121003001e6a0b014140b10f0010540c545455503d5002503200710b00698020341c40d611b8011082408120a60249a80c00700500641c606103000741d043c5010f40d045140c41070148141c400ca040d100e0b044250076030340c102e0f25a60510020030002441c200241d03000818900403075000243c03003410365021140e042ca0039515000008640c6c809840d0500c42408000c1d4130605440102e0004140c5a2000040440280c0115030056104800f0751034840c103001c10480140d8103070104001c2015420b1410000c000a00041d420096540384881060050000550408c0741c00d011302400c1c0815100039100964002c1d20107540d4036142c60403201c111141188881c621b03c80c11010a441d40d940e00211540b1075243c2d0744204045d80c03550b4880c07419030003034145180d05100c24000819281828032542c090044860000d002251629150000303440c4860711040c180b62410a4202ca416200000d0fa0385c046481d403000160200603d015050000b51078201c50482d200c00320314403c41c0b00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 826377742 1250 826376492 826376501
    0x408060f1503071a0c01290414010b0306010807091503020405031515060a0e03100b010215060306010e06190602010f11160201081b03090d0f18051011010f 68
    0x1d00c5103106540c4000e07200c05043e9250440c0c0725482c5050b807402d81a10343d4600c00001740051085080001c5015284010100801002104103000d90801155003200c94581032060b10a001880d00c604d00e419807425412410502000345524148600640002c0500c4c1c81141c03018040d01c42150340403804500050000c00a41050041902a10440070100070982d5540c03041c81c070030489580341503d425140310900c130094103c2c40c2d0310000d02c0318641e2400901d0741c09000e022408046100005505050b9000080c9010200000180d0342d0380120148202d40d1804503259042d2442c1001e004100e40303508000c54500700d414002402d000302c50002c04501c8c2541900101d403013401e4581c052061350500e410108492003a0344042e503040383d03006442e80c015401510302940c408110032040c43c0c051400d4141440f00ea0045641e080c082e080b2019054880d6004075402d070050b85a8035001d9014071500c94003d41810380c500400f403040701e10300110a42c040c400d40d100d015490917480244a001240c0031080081c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 826378992 1250 826377742 826377751
    0x11802090d0c261b040209010c170c0105060d0b0f060f030a03080405070512100e03070c1403010c08090a14030f0406021606020d080c0f09091e0c16170408060f 70
    0x81c12040da0f0500d5400140c001140c02507482400e42c1852002d003040007e6028524150502104298441c08203405070392424040711182e60445c0c1e20645040e0035801c440c0010a9107201d80e41c102c403048082030118118a50140c0310440c003500c1511020000788000c1c180351a40c43e0303d441f4401c24001010f9000c440c0b1405248282c4c00c90b03409036140c0040001c91103000001000710750080301e250101e0001d9820800d20014100c05413454002c071515035190400302c2d500201c0c107140a540d4444110b0409200c2c903071b01958207103011140d03820000811919161504d10151203507420b141003500c401000d001f03c542050b44000c103150764640c0e80ca0080d440c0d0409241000c0c0703c03861100001421070000ca00b42e500c40e8806d40d01c0c0d003829035404c4900000341c1c02c0102c084219000500001c0d09a4584510750380c01206240c5515803482e55030b407c0810310107002031072444080d90900c403000003080303444010003406600400038100c0302d04040400740f244c01540d1024640b44a0710081c00801c802c6066514080c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 826380242 1250 826378992 826379039
    0x20f0f070b090c010e1e190e16080406020705010b031006050406140325050406090209090a110426010f0b01020706050307020607031a0d0804051206011802090d0c 71
    0x940c2d00c1c551402c0e1249191400e503030201c0d15070184000c2c1ea14000b4100e18048036240d4100040d50b11950205183c88a604418800003150365401d00c0010b0724200c0c0f850307000c200f0840210701e8490980c0010162100548002c0c2015008203817402082020342160300c1c503480c0901107611458118050310b003d440644a110b004501d41000030401c542032420000250601400514560038942021100500718000d41c0745086a03003c0046140d82ea070340200002081e40c3c900150b141c0300351508000c803900e00944004115031900318241c1c41c0184a02c1079604403840c0d80e05d500300d04141006440048403000808444c10f5107080c030480c0301c1c2500d550040e0791440707081c0d080342c503800d4541710160780c103101c20b640341400359004c3d000040240c6c5c0f098008841080d200c095a10704100c8200114000da200070408440c560004282440b99042552030321100e0003064004000b40e5141100b001141c2400d4454140519000502103017151149c03403520400652040a50340c25965600d5400c20317945400c0d1513902c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 826381492 1250 826380242 826380263
    0x140604060509090307030e1c03121a10050c030708041211060f0412080903010c030501170a030e06070201050405090a0c1202210a0f02180a05120601090b0301020f0f07 73
    0x111418201100743c070031400080118078006040c5c07400d0f284481c110703400c95800200c000c4d00901c0000c4881442c40150702c2503c810503406110154001a240e20147c48501c0075801d400902040c1e9590515014000700c90400131fa0324440c145e4070f18210b21a00c080504000c1380002d00050f1080b0f0825414a05409040032101a241c40c1041240781d111f000c2031410782030070600050124664085809100500c035204062030040d500c0c01081c203596880915a0200e903403407004002e046840f01c1c031013042c02140e9010300008051568040e020032a0f40401038060b550110390082164051000c40e00940720083c4800c0700740c50906040409401031680850003e00c40f0801c00e61275030058020344a1030104041d48842c0544214582c9451000040805d070a43d5210743e406080c6004600c020080c8945000b03c1e82d10480300c8400f4002510301c141c3c13055000e240f006020001445000c01c1290540b000140c02144081c0d01100003806070160140d2002c821400041810260b0081c00092a88900c501201507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 826382742 1250 826381492 826381499
    0x21c23030c0d021c260a0204120f020a06050910122c01060501051204141f0b0a1a03011217040b120a060506030109020d0212090703141b150d14060406 66
    0x120b6810117040700003103001d011981c034012070107100c00b0250700403404400142005c0c0c2e103060741c0381c0d99060424140d818007803200c4000c00394105142c422025210b17074280312b440d108062011a45001042203605e0400440b032007001c0c5490425009552410381c04001c10040120001c103000c640d00380d80c0383d208000d610308100042e0650081060358080410101900900d41c0c3c5d0381c68046440d90030700004101c50041250b95801d680c9014080c070302822406100003250340c4001c0c02d019180c0702640104500d010304800d0b03803061242200841e0705440c0e005d01150b4028000749886500d01c0c00031784080400c1c04000c600800e080e101c01018185030b01d080e0400c4040c503120000750314100c030300c1c0707005003908100200014817060917950000c01c0d032580688801850100507514442c60220265084041600204002c105001c03404200c05015a54000070701b4200030382c549030f00068003440400500a40c00a4a00200003403180306944501000b44c509100300703030f4280001c074021141298608e11840c035040000c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 826383992 1250 826382742 826382747
    0x608070306050102070306050a0f06091a0910030609030207030602030c0306040621080a051612020f0f07050f12030d050402040e0d211107060207021c23030c0d021c 72
    0x500842d1010303005081e4141c116107812010f0180100b0010102da10b82008180c1c515640c442c42c001070180d20b1000a10007225103072145420340321040c59100c1d1040c0414801d41a69000c844011240d1018000030300c82e042c2d282c180e040c81216880601058030102c200101e0100c4d1100952182c20103c078200401929020941c03544c0d0fa9504084c00030000ca00c445800141c1320f10002c10704050070f400c10700c3c242460301c841303c0d4030001d0960701180d001c1ea0300313040c0182164040100c8103003000254007170490348400c11403055448a080c03041c03900c6108001c0000c5031039200c2e514800f0000e8011800da079502e08800c192240a00810f44040340142e02c2c0200b02c14424402003460708205400c0d0ba0303140350500c045421070400342c0350340d5a0180b0480d0781d03842c1905512580c4c00140042403140e01c1c007580302c0f0028010400c24a5810150400c003000c45442c0100090701104081401000400017004442075141f10900e18041c1c0d554001452003003410720500180c00040640a204424a101c000d500400404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 826385242 1250 826383992 826384001
    0x110307050a081f03110f0904050312061305070f0e10020d080910020301080601182a03090203010c09030b011e03120203130f05040c080c0f071e03050406080703 70
    0x10600203401444410360003032198040e5500560307803544041904050601c19650315910768002c0314034000515182c0e03000e0412401140030440111098400341c94291104e5442e032040c101c540c00d5041c41c580c00940145d9800032002c407042c0210784100000e1802000140c4180c0301d400d00840800c070840b580a0144c070340720300079162603601ea40c09009440309032641520032420142c6a010360b0b0103100280a200e40706440954020441e400003009194582144120011070950f1aa20040c2c02c011224122107040312124407004081544c010781e1180b400021001812000c03c000e6241d42880e1188200d2a8080095002e4034007a8004a100e0390340c64048019500794007484440264400a042011405241d510b081008190040e20301e043c4128a00545034103aa400450f00b082801d41c045c8414101403040c081061000c0c20310b0780d250306241e0070104160180d501001d46003840040d40d141006a500d008004480d004110142080010716004c2c003a03410500881c1c1c0020700107000070b40900e209005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 826386492 1250 826385242 826385251
    0xf031704050706110f0d051c1a130207020307030605072d181a1e090d06050c0c060f040b070918020d060e1003140114130c0b0a0809011103 61
    0xc0880b01d1420a0565400c00c980701c0318007144c00b5608800010810500121424003113035035445546e8404405070a88401e100b016040050b86881d600c81551655040e0b401c52100003200c1840c07400c40406100e00103489400c0e80250140a00c941c00001c20032590049801201d0039103580d4070051041802d04c9241e0b051295010945104800f03a4020720b006e410300441d20443e00e0b40044601d511408140040d9142c00d0100380548030000720421500080090045130100e130345c22251078130040400207018802c07078080250105a171500850742c40d004017030454075401d041c407056034041c0c074120755100c00300c2004580545028810701c001030045842490284191030800c0721a032200c510551002000350000e220b00012103644000120300d0200721541644208c01c0c04108403425419490712049010036a4240b81c0036038100460150f04c611206e00c078603804028602650032006081c01c1521020f005503108104506001401d40500c0e42d1000d14544201003aa000f4054642d0680e076031042480100c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 826387742 1250 826386492 826386503
    0xe0d1209260307060908120112020f0a060e100203040f06090e0615040b070629150c030d09050a0f1a240f04060312020a05060a020301060c080a0504120f031704 70
    0x11404000030001e80c0483e107001d000d8511941451985072400d84647c0080c0c00ca00e4003807500345c400e0411803405a011201d440c50654640d01810b00c0d00d8000743c074a0489502c4640301303500710300c0b05130340444c400c0043d030b402080300c0b58180c0303c2c2c1039640d82c000e01416941c1c02401c05900c01c513000204182426600130640ca60480b1020b89407502d413a6503145560000e00f42100c284d07460b2024800200030b1550454080c203600c0f01c1c034001e407184100400c0f80d0640901ea9001c0710310b0b0b05104047c030034100402654030940c402403000ca4a958985070042c00c02c0d0b0702250042594a6070720000c806d02000319084510881e0224103500c007a101d180032101c0c0e44450340303a0101034040c10101c0b501142040c52016491000292000c078500e5265904d18a5010300500d4043c01a0b00a030010740912808119480d0064030b8038004515550509400819000b020031000e018410006034000c0c8003403080c1c003220010301c10400b44020780001031811903404031340c02c001030300014441d480108902c0340c41640b4502035036000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 826388992 1250 826387742 826387747
    0xa020f09071e2708151008060103140d0f23040b030a05071206080a030e040b12010b0a0e01030c0b031b03040c050406090c090e0903070503070c080d0f0f0e0d12092603 73
    0x50644880044000d1888421407a1b1000016011108200c0280a035101d40c0c0c00d820b52140055070381d46442d40303400d121420055000c1401c036103d1b400c039140c0c10b0541d134110145140c0c2100312000440c144034550010096480010402107010400c0d4031039400b0380944d0b9549125080003080e86015100c0700e004840306900a507a0000010303005251410b4801c0024001190244038000081c2d400c02e841e4114600e2a5159141501b00f850035540b250090708007845141103e50554070780000da401170307015480781c0440005c04289525195004004200c4100e518140d03689000e1411186504081c80303010b01540c10060b011841c250240640e40e8040304565031020b005141c1050a144a807020b001841d15001c100003803004568144014032065004600c500d00807450320f00d0a80c42c01c0d001c00346020422940034940090aa4051762007800c000d610310342143e4a080d0a00050080105030030002d10f120348003038400c0300d1a84c0003a2608211440409410b8501040703003800c2c10102c00712903690b5a950000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 826390242 1250 826388992 826389013
    0xf010c051504031b11040605030a0510050a06150e010201060b19030c03060504020d0615030b151e031305010b040501150c08041d090c01020a020f09071e2708 69
    0x280201c1c142e001e4000d02d0104c60045603c0c0558100054243d415542c01e642410103000d02d0525000c0d440040100f0340003000d007940240c90b40f5403244a205480000540c80b203001c510848890f40140019002210035070341060b01d000c1d4041e04806c4080a40c60245d420b02d440011240c9000050b2540ea45200e4030511280010f814110000c0c074120f4210410f050350b41c03a021909858910280c203008005440008416081c10018540b0b120f0f442c514000305820b01c00d43c50f610340c84542030101130300300b603107032043c1ca820740c1544c4540307460401007029140740c5010081211414134000070900c510b010760020000c0303945c01024801a2102401103100c80c13007681e0394070340c101841801c4500d041070081c80c0585c1010380303030110350503101000c50038a00d084006206200622805210b05284080c1c00d000501003403c00c0e50116800802c0b040605104003454400a040c450007080041b015605e040d022405041c1c4600340a0540d07103241a9070500b0b10702002000d4002800303070011405640c0420014101e8144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 826391492 1250 826390242 826390273
    0x5011811060c0f1c02010e06100302220903030207021306060509120f06100f06090303210915050a060b130b0c160902190c0221010e0307110f010c05 65
    0x100c00c100380c2d0984100c1143e460000002c0c022142c5003000681583c58140020b2402402e5444101c8095419001101481002c0d10041d030300b0b0301240d5058a0700d61f0b841d603542034440c0c00b03503131001d804142641c20002d0150030558507038000d00b5298422113103280202e24403000e000c1200e50500506c0c01007603041001140c0b500d006105d589100380000100d0703a2a0040c0a940307030a00800391441d042c58024032000b80000340c1455282c90290800f4500280d9142c51620014034144c0390031201c3ea40c0f10f081200750341c4c03004080e03000922059004420002e882440d00c0c00c0c10f0042c501141c0000020340b8082020909003610800c5642d000644074099441e0f9040234212102c1c2e90041040a01e580704842102110741d140e940160024240c02c080140c41d4088103024440003403400100da002c20100d031010000581c1c641159000c84287c0440039a1f0172401d00039800d00600c1ea02100060318840440c800782082030508942c1e031001810b403404200d0307002850054a0070000408001d1054000380b9110101a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 826392742 1250 826391492 826391497
    0x80f22080c0307170d1103090d180509041b090b06070204050a0e120a0306051002030d051012060605030d020604031e0c0602030103030f110316030e0d0c120501181106 73
    0x3460003568501045130f0f5440080803002c01e0600058140414803500c4290750f841420b541d5520000c03254a58540f2134846034507940101a0a018082c40c044071030603a0b4a9078a082c07001d440d01a004c590241400e081c20085844001e6000082c020052800700750349640d801403800031100900800c0c20b1041030b80c02c01003c0c0400404041d2086ea5800c88074046100c2001900344124401011036580c0404d101e0080a031348854000c580980940800b4004d1168004211101510407140000d4992684c0a070000d2500403035000e040380a002c8401c040602209074010802c81e07408a007203e404a101d2001139848000442d03001d404541d41454204440f8802ca00301d44500c0d542d46821010400181e517444c040380c04c00e8005600251902c01007a51103030b0407200c09002c01c0304040040d81400c802416490010202003c01000c202c0052154101c0d5142c4890031301400ea80101e0150740c43d9124440c2d034000b000920707002d6503103600380b400c51910350b2840482800381c00c1c0c0005101c00c04108a8040c002e455 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 826393992 1250 826392742 826392757
    0x60f0504170c1c0b1b0904240801020a0e040b061c06030b070806010e09240a08100209130921110f071a2502130507080f2208 55
    0x10700410a214a40e039441c1c007030000420940e40003d60300155035082c200c0c5403080043c45141e0396650f02d00401140844c2d1801d580c074040d402c460114480d818a0b180400c04140315a11951080c42c084e070224121a041d006403c51142d65950a01c41100203820813003075540300400d05801c441c04100a03840c00d80043c01ca070465600c8606d000ca80b481d5241d0b1541110f004c06c84000c0c0025005c60217001c070541e071021344280d490504403104002414a199002e00400480800950011002d00400c895859080a40b8020300c40c0b14141c810700d40154a140f0040e500049900303102e02000c503996400c2e04010702c030313004615800c044014501a03030b460304d60300d521014110401c1404480c400b860603150b4100003030180c2980c010083c202d654600034824807121141706011045140500c4a40c9024034507003640e050b03200c0340303180c0c130b6503280014008220034010078401030741d20ba81018104440320b5004505140180c01034a1600c03070f250391b0260f500301c61070010510701d0110303601d00c0c2e4007801140c1c0410261211 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 826395242 1250 826393992 826394039
    0x152c0d030c080a0c0b0106031a010f020a0b0a020309120a120f09060906090b0c070b0f071403010b0a124b09110609031906021c020d06060f0504 63
    0x4281c01622115541d8210440c2040014114504902004810403810303004103030605083c81144021300d1703000030300203000d840b580c100300c400380c0d07417503421407080103c140c40541080d006c0704a4240040b60101079401120307034003000c2c4214440c84011501460481e652501c003a03403a4801400f205800f00c01402d030030780620a02d251030380c0300d16011915520410f14807a10440c0b000450080c1464545204c1400420882c401d0109001000205d05180c41c1c8982c080c0d02d44402440640d12494140e49444007038105030700300355002c4000716510003074000030145440c094035001850325104000c94184c070300c01100c903205144058500201b60118412886003d012230000130a01100c0030501c0220681d107403080a0607985510288083c0321000d1101d010401c001c2e21410b180644c8200425074030362010454a035803001c1c681c950010b0240325410380e0303820350302981e49407e0321a4500c0750714065000b16404100f0b09141031300c0006c10501a00140482c0c3c0d4140d11018106460062500500030f80c501c0d203140c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 826396492 1250 826395242 826395257
    0x1b1e1f092117010b1c0504080415050c0c031f1505030d0e041107050601060507170301030309170109052d010c080417030603100902040b0a152c0d03 65
    0x1030040c0380d201d2901c009141996455081d64980001210b0030106900c4a46504010001c0c140309280c070b40700001d58848580004255a150b5241059440c8625403003035810100d641009a11a94000c000784000c66000c1b089402d05074031482015122a03500f01c8880405c2400401390b450706129811403034001c1e4580f0500c114066540020a003024450000710340050010a0040220b14141c4240803c0320341c180e103040d041c0451540c07029035680c81802250280240845c90380304101c2852010200d50506228060b00c95070369140140800e44180620030b09002842d0320b0910751001440fa46140a81100c018003520101c3d88041041608800042800e40080441078074402000d000d000031500f800d40e101802e5260500b000300340b01c000040040380001003001407012994001848240780d407031141000540e02542d00c0094001e119500d0728980007150b881e0f00003100855403a00c0f50b151201900c814194003a580d152940d25605041040d55210340e8060f8482282881090780322a50b12a0800d0803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 826397742 1250 826396492 826396523
    0x1a0306120a0b0a0606120504053007060c0809010509060105090c04030507080606040b061c021b0a030207031407030b0c0a03020f0d200a1b081b1e1f09 66
    0x12010a045481c043c1c00c640b01c403000c1203042d03030240151000d40360308842045207080699075a078031034070091900566813030b003400c1c1110324141104100d5289424207090541d20700e410319242c2d014140e40701140000c152900c1c0024410070041c042c2e13038400c0948070044d003000e03070a120070000c400c4805850301118000a10000c000950b0070440300029203016801068a441c2420400042e201004c4440d80202001d0100009180b03060311078980f4098119009a103490301c01e000b40481210b9814880c0891041442400c141600812040c0550740140c0b441040021449ca000307030f48074810b04c00100103500c150001681903540b0f8020b010805818a0b0152070246010064030702600140000b81382e865841c68400d0310f02c50b988090581c1400c40101e01030a1208480c400b4294021080d0403900700f19400024108010911044402910a485403241c4140c402e4409035903c0a0040c1d5446448003606c01089c100e200c002142821a4a40180c0790410880c01080310083c03c1d581c042201c40b071041030844e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 826398992 1250 826397742 826397753
    0x306010b03331c050c06190f2307050c01080c0703030b180f1501030501030b0106030b1305150a050307050d381e190c0c020306010f0305071a0306120a 66
    0xc03e804880b9002107211200d0f43e06143d8100003051500520030b80c41000302071100c040c0c800d000c4484c107889003000d4a54466440007038480504001075422090f0b201202c140101c100200901142402002187d0000305908019164204142d51480131034100b4008100020b10907006880814400740245403203140d10369a050110700706481d40380c202c2c4405000c0180301410324030300b103007803800910f003d200a52650b114516100d0040c06006e0403d5103640c0b13980020344481c40001d003c403000880c02c01a502d040a42902442050201d40f03202c0e220702c00e400600b500d400108032041c0e9400600403000d82009a84080408200550312020b110314540161108946007040010004074001d82200c2c81c42d00d48035600350907818103000042d10390320f0800d100b8100d0b040e003030741c1071000d0064500242d100045030003922400c80350382c1c0c000c0d8140300c1c200001c030751014101d060004a0b44140c1c103c4100d1911400100d072040003074032142004110610000c0d15903c1d00c076071030803c82c1d02c015064400c0d81000d40c41307a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 826400242 1250 826398992 826399009
    0x3030f031305060a0b09010909020d0f0809010f021f151505070605090f0607141b070603140723090303030f071d030c150405030f07050306010b0333 65
    0x882003241a01e1260038803105000031544a80240b8042010600c0840080c00581060003280480c5540e80c0c01d08085456483c99a111560050090740091545103403d040d113500144500c1e0008180707048040e0703420700000308070039041414280c03000081000d0700394400401c0d43d0b01e452202d4448444000031500101c900c51038a64180b9a1080e07641e00700c6042ca4800d49401901440a0ba800891142c181000204080c1d41007540c1d4070740000a00450f00d4045c401c1e0203440e1034500007010030ba8442d034100d4130001e00002200c085407001e002d5089038a5000484da401151100b002c82c81ca02081144110701d10802180c41150804c040c3c20300718104040f0f071035504222244501c02c150031043c02282d54100c03072190b1030007141c40b8461980001100c0032a80b40c25040342c00d940a40d0341451011103c44615060b2001350034050101c4505d00c0d41c480707001c0e9454501d80b003001c1c083e008481c008540402803200f11303841004008405009441c80003443c1107600c00c00140c11100b95495a40c21100355a0000e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 826401492 1250 826400242 826400251
    0x60f06080105030705060c1b01140c0616050301150f09150309060b090601020c04050604090203011b1e0813060f020a05090a092a02150f0403120e120903030f03 70
    0x19102203940c100000e1500d0601e060b041544a1a001d2008140c2d40d0400654040f4041000200c40c0307149195000694008141e205501442007000c01c50312501140000c04030300c103840000500199030691202a00c0c40c2c0300a00a8508110004003c943c545000760700290440540307280100149a90b580000303c1c440c00811140300080e2920800c07018001c140c051204681011580a8000e04244002039910707643c01c900d05000350344640000f050f960b1264410100c00303401800170b10007001c01d04c1c03142e89920a07a000403008514a8112604880480f00113701d00151a07160068240c454603503019031540781000880c1d401ea254000c070241030000e4000307081e02c0191303500c40076101d072080020882d0710802c07a000925500d2808242c80660100b5044d003c103140a0340d40342e07004a40b0941030490402d1441c8851407520700105080c451401109a100380c400e5012f603603040c41403000c0f002c03420140ca090569440b020740c00b068a955032410700c40c00800c80242c0041c01c40e86040c40c2e09010345040c0e0007c58 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 826402742 1250 826401492 826401497
    0x1050703020a110705090105010c150f02070b090109020f01080c1e190309050703030804080c120d140402130509150103110f1507110406030503030f06010f020705060d0b0103060f06 79
    0x110b403030040340c2080701444482c0c0d030040902102e03030500e000300300c04e402c05111340350404c40b4078990141840b0210510f40103140c030031002071008481701182007010758031090041303c4401654000543d081018807500c5c2c0129801480003418021450045600b514040c0445406603000c12109800710780b00e0000c02520b000c2405c800762282016000c108040c40c0c4440c41005050408107010005030021134004141d90345828203204980b04ca0400000b1406824035213502d83c810203601c0b0000701140b0000d0035200622603428000480d0020800003049000c2d40c00035040078001001d0f8094a15039004036038401500d2085503081d85000c880440407000a0344181c40b00c184c400b09000b039070704209404004d090000d0b20441030003607039118828114402c21a024088115101024480361f4071500100000e40d000400c40380c49041c003041e28443c0b4601503a4090200304407a00404095001007125001c88000a0484d400e006007000c5141c00b410059007458100b542c0d07203d01003000d040c42c041500c0034040c0e55 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 826403992 1250 826402742 826402747
    0xd1103010f0b0f030102040f05060f0405030643201e060a1806091728031803120e0610030b01080303250212040b0705060a0207050712030e030105070302 67
    0x181c091108082060f501076000c2e034010003051200099101281c41111800d588490b41c5000700d083c00c1c1414080c2d074200b40c0d0b050058200f0b01c50000e6854101d000f41403002a40c03091001c5045a071003198000c00c0c00f006c00c3c4250b07800003c4510b580a80c089104a001d000407240c0304001d2000c0c198281718004104070f008268242c4000f000039030400c2641c1d401f44010b071080004a9400440d501c80ca8141800100b00c55180c0c1074000030803500c84030044c15007400c141550340341c51103030340c0c410300030b410fa45240801c000d540c1e120005100c0c405c1c018203840c00d443c0100840500d040d87c400711401c0e4030080300401c4442e260003140d0320090080181c54461401da096400d912821403501081c01c00041e8007100d02d6034014030500241020001740c2d04054241c1c08001c0b0b030700c880501410782c24000002031540b1784803c081030024108480320700818100e131045098441542d09e03042100704034007070344902818a034000340c400e2150400031440c0c020018000d04091844001000010b82900d03001c0701c1142c000f07070b0007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 826405242 1250 826403992 826404011
    0x160903060203010f0819020f21031201050f0109210c030b04120f0f050901210c030f0b4510060f0e180a180f0506180c0d1103010f 57
    0x6004070f01c042921a140d00083c1b001580000d02c0c2149004c0034148942c00c00200075613003645181421080701c1503c000c1c0d0740c82d80812004012806800d106040c001e84040906c82580d40c800d640800035a0300b80f00c5e858000c1565903640d24500484810200c405514400000c40422a03200c40b807032045114a90f800f80b004020039004001e4808090b0035014005511001e41030903810001356210074100b0703e00b01c0e40329040c0e07040c010304c507101800303604011300d180619811744280e1540002d1080b48411030140076515864080c020200305104450302a400020f03002070114085186d041031002040c05c0d50006074210312480440305500f07503011484078081440c104480e40d0410303412814091a4140410181c0305500030800c5145841d002c0c00c03081d42c0d020006200d0010702d91000d410520310031010300801590346012003080450102c165110701c82c03007000840c05001031004030300d04030704000035000c503001c01401d01100c10300c0c12104888000f1441d08170b507071540b1309103e042c070705020350302011030039142 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 826406492 1250 826405242 826405259
    0xd1a0411090106020307150f0c020d0f0912060f0b100c1b1508041e030201020409180f030c032c1f050702010806030a12091401030212160903060203010f 67
    0x59480c2107020300c1440c1e0041100d982c01005445132160004044280010701817a180e0040c0401400000f6a45c9413241042e00d03550300094942d00381c40b964541c9086040100400d503200e6003030b4801e0070302c0822000c01000000f21241c01c041045034078240040b600751507040010b040303c8001c42d111070000d403502d0041d4007800748501c154982e40c984030741464803040c1401249001c0c240b03c00b50400c113002c032000100d001c000084620840c00ca441c0009c644031048035140c028081c0d4480e1064003003840c01c0c90050741034400845800c5003083e5002d1881410710b20960b0301500d0351008014194144141e041d841911070100005086040a65524040220082d10200000041307141d414642e40c0c0c1c100303981401102d412108603005a602424140d20941d80c40d0b0020380b52001044004090b40389130401c86603042d030271440080035100300c0c6075041828813035000118100c0c0a4030820719541c0d19404081035054031184104811050355143c0940c445890340c4403441aa882030703114100041684404015600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 826407742 1250 826406492 826406513
    0x70f0b0f09010b0f01051210030203060a0b040501050f030601031412040f031a04111c06020a0206060109060806100f0c02120c040f140106030c17011e0803130b03060d1a04 75
    0x100c030000d10302104e2200007040c41c080c20350b81d46006000ca1001c81c3c9001e86030b0410100856000b030884469180101801000c1c021080089000e18200800401d0340d10b4850320b10042d81d01c0280040450340e180d6112506a9170403100c4254840c080d03131244c1410300c06c0c0c5900a0025201402034050580d146240038440217031005010b0b030b880e01c0418240400a0b141440380070441604407040c207819200d0070f9548003103201c03100d40145540c5c80041c5072211150041186440b9102c241ca8141c00c15035500404d461071070080b81e0403a4020710411100e0003840c002d050740d030310f0440146000035070303100d003a0b02080c0d40c0c41464130705100d1a40410323007003c1d00307107010300441440324101e100501690340c82414004480c40180036145c149900c44400780c02841c0b08002ca5403821110317200380c40341035039240c950b0300341551001c03188224403103d1040440c00a000000b114207207058203ca40d600a0f02e882131404890b000501080e9012000410313080108914040c0711200f01d802030244480e90600c4d20303006500c213 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 826408992 1250 826407742 826407761
    0x806010e091c03020903120d150503060408191b0f061a130c0e090a020a26062206260a030801090b010519050307030e01060f0605070f0b0f0901 63
    0x90b4800c0007084400d01c407418010025142d9400c0150b101d4030340300d002a0030009141c000803a03900c40841e031603441903003a400034a01d000300080c110702800e4964060545480040745e000e011101c4c10006083c03100c4480080d40d0b10004030b0b1400000301c2102c03909000e001e910131041500e035100c542c02128280700d100d104501d045500c641074200520511000302e00c03200207070195503030110f54a20380910010f02601641c0b04e49a002400318420740741004c003520094100c18002000900300400c000f40c0c2c0007000d603159030521407079102104140d6840040140070805240c10071000c0c2604030662058050f1801440e020700b09082401504070b94042101c88031013005214610668000344001c00840d403c43d03200d13415941c414001107511500d68005170340520501e64521036191202d440c03016000c3d440406103015950581d01802020b000d140d9030b500fa582d40e40103a040485620b0707020008140070b03500402400f84541c101003004c041a1f1151604036808a03a0100000400d60811280007070a10804001c0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 826410242 1250 826408992 826409011
    0x306010602190303050a02090406120b06030604080403021003060522050f0f0412181508060a03081b01090f03020601030c060f0f0e01020c10091a18010e13060806010e 73
    0x180e840d0b69034a40e0109a10014050580d59004680d0240c5190101c03801d40d039028205101d0315944541e0614030b10950319090341c1301100100811854a0003086d820b004640000704103040ca4115020080600c0d0000035080c00e241c1d95102c00100d903280d12000464031650100941c41d4407920140f140c0030f40304014120401c80078490200101c044460b0f100d1904a0f0700044a440c0b58500d00500340c0308003e04500041c640310040900142c0001450341d0721240241940d40c010f00c4e0b488031070a00030b4500060000600600f410702c402c0c24079080000940160a00d0380001245a0086484203684c2d01151402500160420700c018002e001031401c5070300003041c0cac0e4540314451800c3c0b88802000c00000e80200010041109a4440315a10030450141e5501c40248000c0200d03000d0b82c40a0720003c802c1c03044403a034607000c03281c4c55803013914501903421044041b143c011406501d00e004507100f40072841c22030f0303000741c2c3e40c1c104000089103413103202c000d850100001d100c2d03541460f60800f8403480c0141003400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 826411492 1250 826410242 826410253
    0x603010f060503060a021b1906110a0f140d020c0307060507050304050a1121070801050c040602030301150c0f050307060f0218210d052106061b070b0304060b0306010602 74
    0xb0079100000c0d00d0794000010400107807600c1040c0303007800d40d41200000d8044984110005900140d075a6010420094031075001004410380326880003242e40940340800c1c0206a4883c1c05000c1d0f42d0041008262030812300060740d1030030f820307035504108a80003d4014001c40d0310108030700041010074800d0580000040c10214118507056481c40e50740d6841c00d00c010a440700000880c0c29030b03210003005054071048182c00500740b9440b11a80380d0380e145540304030300066080c5408580059100b100311010b45426078007462a60382080c0c0702e9102c125481c102001049003624900001c80e404048215200f44900c001e180d96100605240065a200b00c90140182c0d104008040080090b000c01a9952200341d0301034234410703000f5280a80500300684214010f0045d14540392065070321070014a210784400020780e05c115010b24145d080d002f42250a150030200c00c11104c0340e280600303001480050300e58000c4481e11501d03943d44002c59042a238080b94242c1c0c45121507102858148000c07409041c1c140300805c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 826412742 1250 826411492 826411499
    0x1c020c0d141e040504020d050702011b39030c1b0b090d02010314070207210c0e150301020d06170d1b050703120e12010c0206010b09120d080603010f06 66
    0x2801c0d00c6010b0b284201e401035241e040c0760031080081074900502c1c0050045403502c032901406070240400300c482100551a00d4501e400c00d00c110340390342507a07849036982c6164111249005000c405404204410207401070303509070000c180358040c500c6a0307038466038811440c2c02036840d201410742540810b001c0c0e10080c0344401d0025600700c03030581c4c0b01a4401c036400c0140750014001a001084130f030103480503012120007008031258001400d44225114450365120706030f56600c4058210108000007015040018000c1250740c07008420140c00c6900442c40801c6009280002422640f064402c61140782d2100020800358001240202d140c1503007401a11a500b00700d02c00030400810f008030182e078002c4ca041c8540a01000304442c1002d107910824a905c05d51000e40b001d40180048843c05200c1c104100d81d5a001c4074040c0500302120409800401c002d900b40182d03070744150800103800d901302030480043c0d03013a0b150800204e04258100d03210071003241424010305007514401c00074444228140003042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 826413992 1250 826412742 826412777
    0xa121b050a0c061d1311070212010501060e0d0b0a0e100c08072a0206030a0f0501030c080f0f0c0105030a02270f0321031008030705101508031605031c020c0d 69
    0x300b403010a1420010384c6d1448088080402c0c020407034065040581500f9420640c44154082c0e8180c0c0c61070b441359003451004000300200b00c5d030416001480d5144040200e043e5040300d400454540780070344103840809014003407040880301d01505080010f141042804034140d003140075000482500600810102942c4083c10034020b1120070013400f6540000000310300c140d039079205030400481010207010302d580d00e00700b00c081309005000b2803c1d13074001c00c0c0302007840000000c0c46100d040c045002410242c01584010760315500024051009185c08001d011000c460480540010020088184000ca01c5650074092000301c40400103000b40d20468030450182500740060b0402103094500583da0f40c4d8805400002d0803156120448510020456404100e00850303960355001c2d540900700441d881840c0c0080508403284901d48154004001c92003a0074580b03540500294000e001700ca15085840c005007031040380100b01c15141135804219804409400d0140c54004d201b1031800c03600e80100030001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 826415242 1250 826413992 826414009
    0x3280e03192d20031005040203190c0e041a010e0910060602031222050a17120613090c120309090522060905061005040506030a121b050a0c061d 63
    0x207000b0003550400d0b4900e080c03e9030030020049201409460703111502c16010405000c1c142c400703c0c031074001c0001002d030013289285120100c641040e26480801c3ca815100b010000c000340043c0c500414000c554071440b03036000a183d00801540c61210958a00800c0850521074540920817a60f800c10b1420010154000150b40d04200d05030050889501c3c0d0310841810149020250b10344c0b00c1526401106019000c50b0700107d850081c1400c40b0020410303c85403d452180300c0000902820340c0001c103d95040c4074420600d410750b034150002d60141711307442e54071161806910080d031070018041681d04250b800100b800090109000a01c454184801d41840c42c84031a645042c024403156204024090306420050201790000150780e641d040c64440f10302540c0700341c00303468003441c2402d0208a4608001800c01441500001300640e40280450700310342410740100000804500341702c0c00001b050040c003800071030504c15091240094601380016044844005910150151880c0070030b80d95220442c0c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 826416492 1250 826415242 826415333
    0x301200d15080609150c070503070308040812090304060219020a0509100f090b010915170c3001060c0b04060c1e0201060503060903280e0319 62
    0xc19034000400000714100c15a42c400001c0b0f224240030710211840c0426405d0f14103101c046032280c281e5171540c0f0040f00788200301c0010070a0744108069070200e0b20a4050980091003200607500c1c0072a0301140c1c6214071002d0382c2140407908002000c000307990b010000c0c60440e8002140080c5c8030481600024038004c5188180340c052144100000c51001a5452000160100200f4075280a131609446002448140300b02401724903403034000b01d07400808803035400328a1400d980d1030702c0c2c1d103d100700114070060000d40004030004061140115141c94102e01c02003040c4842140f82844c0c402e004001904c4c04180d100d04144101c07409520080b40041078082e5004ea002000410414142c800458402001c2c070301d41c1c620400002c2c03a4031103442d41034002d002100d808508030b940d0744e1204030801d40c42e44a0f518003032a094404000000682c00159240c464021040c104004848802c0d40860f085c00d8485111503241112403800c00704110291038120154031144880300d4100c000060349034101d400c2c00700d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 826417742 1250 826416492 826416517
    0x72c0103180f020d02060f0a1106010504110a120b100206060a0e04080a050c0304030c06080906010e091b0406050303130e0705090f06030612030a030c030e0c060a05030a02090a0e06030120 82
    0x103150b50640d280da0084404140e840341c5202e48d52855880004c281000c90030007950350b405590300005032840c0c10f008540104100c2c3c0f058501e440b05425058034030040c0480e100b040d00c1c2d250302c0030240554840008040700302c8190054901464210304000d400030b400e401901b41101e0110902010400242c15224082003904246a48600c43c00303826146008645c0002c1c544041060040303a050380c00002c8901070b48000f007c41e2080d90b2182c5c100700314428101c44050300fa40c0302220120b9a19512040c40ea000308015100040180d250004241560311071003298500792280c0e0b004002806280c4411607000703949162243c03c01d4600da0010b0043c0c0c0421a40504c03503680880800c40d140d0700c0c18110350540308054102d030781e1181e0429010f07015051806610010030310702000b10408481c040b84a103d8036900400040c41c01210140075151504040c01c01ca864550074455054203454520311103029240b42c40308517100340b400c00d0405080d22000d050508070038003400140303600d0000b00d1003515800880e14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 826418992 1250 826417742 826417759
    0x241216090b070f080f070302060604090b060f01180905040311030a21020c1b0f091b07151505120109030903111503100f0e010f0e072c0103180f02 64
    0x14140503000901c920b001030b001004c0000d0182e52114014001c22a03640700f6026200d0650350b1f24100011a0354800e0090f00000c5108001916880d10810900752a0414101303500d56600310013032000896940c0c0c01030280c4a03074400c02c1c0801d064102c07031101e50341e02a071402540340a14104009006070a05800458010f0b1707140c19401c4441403d030140c4850b00591003c031403500d40010040d07030405446007207c0c0d0281c3d5000311038a41e5810414082c030300c1fa090150440641c0e405407000660b0b0382e8000c14045d501d021401d8401c21380c3c8003d074020119210313110904030047c2d60502c0200400c08401c0c91030281e03568904003a900009410920610849400c00c080c6000d02850602040365284840000b01401c04008200080c91010b0003030039090b00c2d4142c001c203403403032f0326034000305020381d800e001d003014110b8041000c0204c1136902040781d500001c2071410030011441c0750741c0c0074a11501d40545002e00000c1c0350100d003107544d15200f4a8044640900c1e18500741100c0d444102e40f4404101020740641ca90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 826420242 1250 826418992 826419007
    0x90c19050408030705100f060803180d1202071e050907030e030405040c09240c082508180f0f0d0c170610050103090c060e241216090b 59
    0x40c1003035800610105003034030782d9a0050300d0419107414014605d081e840380b81400203400c1c00d08921950381511885e10003035203032240b180000e6506c0ea801d401203e9020306040050700000d0401c00000d06451b00c0d41e0002c0c45090b00f005040f824006c40b0b241c0d0f034136000d901840d0800143d03442500c1d540d04226141800074aa4a00624007400d610458200303c0d0040d040901c1c0c1c04030309904c0019502101c01c1d103502c401e16070b2000382ea80180f084100401e1000a00d2164070380c00400c0542c8014005040c19014460b0160010045200804010315040e500400082624050070348107501c00d1303010406c100c90702e0700c1681d403100001d18140031100d4110300817118403c046082291591845001d4031103802d25180580e00114882d40e40c480c121000a54990a890006a154028054182c0c0598040c5008140310705154049851b155581340c2c0b07aa12002c0244015505400103170340c070402c0400a007440d9511080c042e81002c8084c0060070b42100100b00e030b0b24246607076601c40609010344010900444e6100407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 826421492 1250 826420242 826420247
    0x1c211b020c032d1c0c030905090103050a080c100c0512060114041a0906130314010510180b0d14010e120f030c0408010c0801060e09150918030c0109050c090c19 70
    0x142940c4a0907040c0720240342484054000c4d00503450310b40301c7d5540c50382d11602c0340c060104102e0203200003002507004050304800241881e000d018004a030004940c00100c8140300c5000383e92101c1d0318480401c0e4001825200790001080c001d50006003030808920390580d03500807040780d21a600c62200980d041811849509961034111060120b004152a0301c0c2c40382d181c1074403002c3c000ca21007120710100d40c0284c2091801c060050500c6110303036007014a0746ca2700c0c0500744410105c20b82420346d80341d5661912030944e0f035140b08101076042e000389011502030010b001c28030708642d4001c0c0e0684c0198411024202c00801140450795260b20350300310942c0726141c40340c0d1012140501d4001c076003294280b09101e21900d901006550407210701e50b0f0703039441e56080c800602195070410f80c1d501007100c440780c0300d2810a040c92000980c01543e503026148980e8200c4880d2821900480714454259450350420418810100715a10204808680b140058144941c0c00b51040c07041c902c1ca1025200014102c03843c2c0c0c1e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 826422742 1250 826421492 826421503
    0x7020708011b030c0207141e091311040204120f020f09041214040b0909090c120601090f05060306070822080307111c211b020c032d 58
    0xc4158002c2c4900e680d0141d901c400a42c0407054240001d29150040c03214a200150070b504580b18111044d00b448181010301101c00c00070342901b1001c020300c640d0444280c0783e01c204903200d80180680c8000c410303070503e4402c110168607402a0700c12030040c4004e000041d03080c2c0016400950103120600000941c0c4081442180f10135080c3d0b5000300715001700018040192401885040311790b46100340d006201e030251080e4090f502441002407414018a40c82c1d007002441590008481c108503603190f022040090343c8030140500700c0031030303030441310040080d40c1181c054080c4a021481c01401580b44c150007003540d89200a2040e420041e076100881c4e405166600e11011040c8031070280300701c5884504000c180c40d03100340c4045c0c0005006907000bc40504010440d48811800119884a80c039107801044610010300d04400b01a03e43e0039960103189c01251098662220f0103128903081d580080b000603042c01204485180a0b4003d04031030b04901c003c507a1301141e03a60403510102c55242801c9041454403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 826423992 1250 826422742 826422749
    0x8061009021e27090f18010b04020f070b0c0a051e0d1a090915070e0f040204030303090309060c050d200703050f100e060a0905100906020d0b0402070317070207 70
    0x108006030583d089901030b81d0702c46010000071503800c1c564524105002182108030b0301640b55843c07840c0400c005403a9000501c05010417100045465203602c0000b50480c2d00a41c0302c0da02c222400120380c1e0802041005082e4040c134086903041c02c3c08215540900300303204030900e210f020b001100384210385540b00800d640302911505410802c3c2c800d40b1081980190010b120710344181d0034403002810401d00024cc1c140d507a950100c0f040b815440301c040a4490030030740c040c810342c84020b40c007075003c042d1954405000251f00035517000c50500340324140900b003812950030080802012241820108200043d0904802000d1600d0811680200c4010464441c10307000c240f07841c00b600a000081c801c0015041c400980c1c003006956100c100c00c3c51010498000184107000e90f0803007000508450150352000c0480b030b0044098030030903c0954016804c903190307450102e079030b298081629901c40c007552140d0b207044103003924118070307055158902401d080380308201d12125004100001e003190b842800031800070b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 826425242 1250 826423992 826424047
    0x31103150d05100612060b0607020f091509090709050903180607030509130606020f1f091e150f1109040c030605061215040207020d0f08040b12040201090806100902 72
    0x105171103040c00c1980e8042105c00b80c901501f080901c141515004c822908010340c0140340501c84200305060243d0803a0003001c030121007481c07999030500c5481e54040c1e144584408000361500d0780c140117181c42120130140c81c00200b035205000c01c0129405c0594413448800040324003949489461030200c0d030b90f03c500a40c050b00301101403180b004440140e00030320f00f41d1760b590b000d1b40c86680d0300c0d902c000d80d98031f1143c20101646105400302c0310400020350040d80300d907016094000060145280c600f030842080c10044500d0704010403000180810344c4070381945038500311814801003850001d0780b0498010090981d129642c0c0c0ca148110b4140240e020304005c09029160f2621100b4041c1c0c01c4032042800ca41020310340070f005951038140e1a1a208940e05154020992202c0c02656104c0000304480c0080c00c980120040001084031910035001e4107500c3c0c2c5102c00382c540362805100041c4080a15417108017181d01800900c10100c040c00040801d451148100584480c4404007041c10040b241510601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 826426492 1250 826425242 826425251
    0x30324050d061505060d1a0f011215050409080406171e09100e160509040f3c031106010803090d060b0a0e010501110703050a080d0b1906031103150d0510 67
    0x107580c6c505e400150700c12080742c070b07a41d1a503101e0a00b40815071200c400c241e40091490014920004903907405400d0100542da07410100b551104041011180001d4054501d0f44010508114590340f046c540c403e10307010070841c442d103030a2901c13100998032240c600c94003a0045000020391400c0042014901c3c00c40b1f5000c040c840f0301c10054080351512034000070111410021070011559003006c40000c0e0203a90b0040c2150b05a03201d03900c545080e1014a540341d51038601107418000c12034084442032801554001540c0030105140c80d000c1d00f00021910103c0083c1c000f040100052440802520707440300040e2074100c4580c0305440c0070380c010300b051401154800009040801c00d08100041c49059580a803105503142000f06103081d5a0780180c44001c10301c0d03000f081c100c03001651030301c064201d4541c00c1d000800d190f20726200051030b60f168000003000d060701901013005405c0d4580106c140d0764545141051035030a05580c10120000e444400a00840841002d081000b100300110b0050105d00300e020007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 826427742 1250 826426492 826426507
    0x10c06050916090e01060b0403020d0311120c03030601030605032b02030f040b03010e0105030a1707031707020c040c110604081608160c050f01021506030118030324050d06150506 78
    0x10010584c035440007407298a40080132480003c1c84040b90103594005140b0540341041d030341c0481f001010b500110805002c1e0010103035129040740301904041032600080c5480380380c058001030031035440d6031045201c0d81c0130b10f002d1600400c0600ca00800441404403c011284000500b47d1540c0b084108540301080001000103150701d001000d541603800441075095180d0340d41c01016603690f5900c202034000304c00000020f2079003038840001c1c04054400d04101c042005480aa5001020112044000740e0080d2059920a04d81842031440c0c3c0d013007904189100c4003032035590a6a41c0c00050008021b0780000074444051000c0341c1074003e1240d407110195695102d0381c0c00f20386150101080407a0410140507004c100c91400009144031240181d0082c00003852407580e116100b1009841141c055507188250710110300719420f0032500500a440c041450343d0500f10b0345070700c2c80e07040400000c1c92128a0052289030340d241e8642201d190880f602007040c41800c0024191b00c83c0d9684803940c02000001c072003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 826428992 1250 826427742 826427759
    0x5030c07121407061a090f0703020d0f020f0a090b0c1509010e030325080c190c1202010903091d070507030306120c05100e060f07030203040f0617070e010c06050916 72
    0x203541c04444640ca100c040c01c5c0c0414440f420740e05076110000c01e002d403000240303103900c20740c06091440041800402e40e40e9260080d2400c0382d0025002404100700054181046600803100700c00900c6010300700b44c9810718607000c150310380c44400e4800107444a0280400c0d00c00c81e094008110201c840710035240d40781003000c485141d044070f41c000804c44546603811018101d000e4840c46101d11001c416191034244c45600321010246c500c00c1d80c41c2802034070230500021452844001c12201c42c65000040c0400c0c1504002e0310040d940d034455403504010340c00b81e545c415030b01c5100b15000880e40c204a0340307031030f0726207400e50151115400007894202d500180380f06000340c0320800f108031503083c0c403824910040010120303020611000c0440c6c2000c000c101c050415807008008202090091041c0d90601d900c41d03000d81d800000660111000401000840c940d0918034030034103401c4000c80c01c1c80400d905615001030054010f05034040c10280e5500c000030285032040c0180400390180c030000048003038403080807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 826430242 1250 826428992 826429001
    0xc0106030c141c05030405040b06160b1b07020a05010c1e05060115020a02031e07030507080f0f060403080a15030218190c0e090c090909070503010c05030c0712140706 73
    0x880c4182c1c40030b01c00342c00c2c09000076865040213401001540c5440d0500c000e01c006401424080c540080003040718040900324900000f501900c0317107001c0c000c00d0408414040440300c44020352841030b181002541c005a88a03c2c11404441017030900085a00c2036040c1040c0707001b0320301100e105408504401d003003000400700b0341c90f0690f0000002c01c00c1010b85084202d94070142401c0084d0103500c142d00d51208101c0c1c02612005c40c5800d07a01305c0e400315480b43e0700c030f604000c00e55001d1600c59010151030900d1000030300040c1610b982c982c0041c880c0b8034103a10001e00d160740242c01d030041d1f540e0b18907880303507500c85c001c0c40c01000d5034014158282802400c031b184076801d10100c424130410301000e0f00017042c540450050030303c034245590f542c0b011064980204010b00c14003420381c40d0000d01c100024505626140f004910a8607074201408003e0710384030505081d58094544d0804000f410130030000c404414030251105150400d10000114503949003e0b43e41c4a0080702c4502c540801180120410256401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 826431492 1250 826430242 826430279
    0x30303040b070c170909010b07050d031d030703020a0c0503031914071a06121903030519061e0603020a0917101a030c040203010501052508190f0c02030d050c0106030c 73
    0x5051b8541c0e070b640e5150321054001c110005045070000b003000c00310745200f40c104440d148582686c1d45940b02080081d0b174a0740e4050101103002d0b80100b001d440074400301402d41001007a040e400383d46000e8901e0500460900000000010300600e0194206000700084c1038880d03450388800270800702000704110412281089550502c260200a444c65145a01003a8081c500150011003480301100c1d540c26000780100812209202d820019860340c68203c6003d9180100b402c8a080034095405444907001b001c1c00760401801d05004101d100501c642c045c003070f0012595082040d10000c5c4103003284d20704040c50002940301440c103100056500445030565143e401808404485860086d402880182e010910a41e80072800c28010601400c04402c44000c1001d1000151410300719941d82c0c0101503084646004c2c004500400090b0000380c00c1800072134030400505165101d02703003503030000740da03104100c03104000c00202240018940ca000d410800c042c50703015040180300750701c40c41070f030014412450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 826432742 1250 826431492 826431499
    0x1030c080607020c130c1827060609030f15050916090e030a08060604080a031d04330b07050c09100617071403040f03110c030303040b070c1709 63
    0x41c00b1075210b83c00002c0010080030058482c80351002d541000000a01442c5890303400d05c5110042c1c0e40062034100c84c204007815003840e10100d4a04000c911140b0314051042e202502c6281a206204064102403a50200e030381c096444000091103250001101004006d0b1111050411043c8135039000c000c110048801d560806032080690303202a580e080d6903904d06545140d800410202c5034142c400c502c0103900c04000383c41036180650703401740c1c1860420100029000500c0080314210401001448071303a115004940034040b0289440e2000b490054108031002035142150020804814448540006001444240e911441c0c0e600300f01d900d8940b07480200d07100b2250a0001960051080c80b00801e0320340b20f0740ca00c50075050b80c40350800b00e10000782c102414807280b155440d01101c2014020351049106444045401803036190180001000c0c10820089421442010203540c130b00005a80d441508209030384610b8503107040680d003800c05034501601e44a160000100701c0e03c408002400d103444d0030f8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 826433992 1250 826432742 826432753
    0x504060219021c020102040303080109151502060105010801050d080909040309050a06020a021f08150d0b0a1b0206011208070609080c030c070803030c09061e04090f0b030105100e0903070b01030c08 86
    0x3031401300c0c01c0344502c0c040100441c42400060109001d00c1d4402c20ba40403c010000c4400707070311085000303c100d816040e0480103030b1028006002c01d5910901e030b140140300a44840e40345501540d290603d5006d1072410324029038040001a06242c41075410300010103000d0b00c0c4402e4a03071540340003501c3d41810402039028642c18140c280400643c1010940c0341842a13648481503140c8542200315440514522540465204900f1010444410015000740480500003841c4510b4105030002448448009803c4d500000e00411154101c8562000c0040e4481c035140da0700c0c429480c0500040c41e6010300942070300b2000c10b1066020500000821542203000110740010340d80c0c204280c0c2d64841125256650002400181d02a0414001500d024200c020b090300c405840440741d100f464020394400c40710903407a0a11015881d500384680000180150024419481c100540302c0500099104005008510000180b03d500c018000d071002139500c100c40351160b5a50b814402141100c1d4020b00d41c0c03a0262 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 826435242 1250 826433992 826434043
    0x15240305130309060c0804030605010b0301083009030f010f020720100302070501020c0607180e24030f0d0905100c0c170a060615020105070504080c04050406021902 72
    0x1070780c030140003107605a840100250804400b10382030351126200b01e6140000f0b101c040006181801020b02070202e13488031640301c0d850b102646240214088142a038030781c40b4414691a048445440104549a00b551a84c1c0e2107204000c03901c0e210418600140b194a0310728035a007954804d80003884241d0040e0807140381c00340109652140307034950f03038009a4411440d26250b602a8002d801412352240501300043c288155030381641d0424908480b04e00004040000c00c035040c101c110f0904020b450013230309204092a107041180b202422440125941c418032010b056015075041110030010860081500e001c215802c802a0840100b40501442890080800c0c0300300c034840c3c403550340d42c2600004c00000144c0341c6000d00714031a59040031041c10b40a035009020114005004400040150b4014550707031100c1304034001d003191360103091041000020031080201c82000520f0b4001c80c2da00700d8000074140c03600d140c014000d101c0c11541451200e80c040514a03400d8001c1145902110000a1080804c40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 826436492 1250 826435242 826435261
    0x206030420031b01180801090b010303080a27060908040e0609070311030a09172106090402100f030204090f02070605010611030a11070f150e0315040615240305 70
    0x1103180c0c80074000010743c420b011584140c03a1510200102122070640d184c071948550700356652000d082e074003820104010820942c0c0074a00950000520004001c02c942000c0740c81d600c1d20a0280c1c0c0d2070202102030001c0d0500c41aa4042010240d000d200181e6441d0381c0c03480c0340c07407068003141d030345105540050015103054000c0c040d44840d282c080001500e55680c1d091240d000f081c4034442581d4401442e0b00c90245821440001e14100500da21000c1c2000e02102860810a0004040c01d001e12010414400107807144801040039107005d0502030440125403504074024000d035400b1120071810300e00034626028055001302015400781005000036a00e91b0420307210381910607217942c40c5500411400110728400c080c0a40642d0300c40b0140d402080d41c03800c4000c1201825040800000d07038450a400f615904064100c618076410350190a14424940d400e00d100003004101804240d20b43d10a07440720006400c001f8050090390b8402e90f0390f480c4035581c08540354145800300c0013003454100451550030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 826437742 1250 826436492 826436503
    0x905012d080412020303010518100b03070302070605160c0201050f0d1125030801120303060510030b03060708010b0f0a0c15050702010c080609150114040e0714031b090a03020603042003 81
    0x1d00180c400703a1070290ba11003816034004020030407410002c124001242f07103901d2100850240d4010b580250b00c035100c5081c414100c44010300043c11581115410003003480d0052803882d0400c0d024208140c44201a007102000d034814070b0f09400f082c0d4034007030565814054100281100c3e00c200346000c400898a9112540ca100c2e03180300140c040381d00b00004006070f042408080c41c44a2081c0b90108070503a450b80416000c0d401121311001080d00c2d00200304a40c20204400355019005203000c1a841d403510a42100314419008000a80c40000440c2d5800301d0149890102559100032022420301524119600600c4280d608200550a185511703c4840c070441c1344a000310b000808030810350f21250b600c240c1ca030069403200340c188660074543d0a840606c03417000e04010300011085c16000d1514003030003004601c4099260440307250500500c0f206d210703100d040ba640c101c0c0c09401981c1d540c0b080070025942e502a640001c0d40000c001041004120000e61618195148444400d44e8450a4800c05da2140b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 826438848 1106 826437742 826437749
    0x270b180a051b0f16020a080d0c030e06070c090506040605060c0102040609121a0c0c4c050403140c0d08060603070905012d08041202030301 61
    0x15903019400ea09010b0000d44500c0c40e20441c0340e515100360007100003103046100c00a01310421503c890344e010b4050301041040b81c03951231780ca2100400c2100f42013000c0380000c0b0070b101910040d0502c0800c0da5071580e801207403e012141008031b49001000000c1980d54000d8455200003030684a01d002007516403643c40004da035650a004003d010080241c0c00308082d0301da18201ca0000c107003a45890010341c1d9a00418a206441f541c0e810006800381c6010400b55000710030044500201043d600400b0f06501d03909504a400444001044114000c8071060b01000748080c0071207030395003548a03c1d07009101c1e04147c001c0c2101c0450000094101010240361940540c031500c40c919002003100c1c0d800402210302d18550b14203000c0091040c0510310445051120000040d00b07015054480103240c03d255460f13003071840094000c0100320174029181502c41001c0218001c22182c4040201d0303059 = true := by decide +kernel

theorem cover : BRFrame.Cov 826258992 826438848 := by
  have h0 := BRFrame.cov_init 826258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 826258992 ≤ n) (h2 : n < 826438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
