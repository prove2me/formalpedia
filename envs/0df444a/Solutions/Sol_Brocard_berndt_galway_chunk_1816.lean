-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1816
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:46:45.496979+00:00
-- url     : https://prove2.me/submissions/da076ee2-5734-46bf-b23e-cb2acbd7b3f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 326438848 ≤ n < 326618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 326440098 1250 326438848 326438857
    0x1a0108070513020903010204240c030f03180605010b030709050303040e040201031119020703031e09060e0303160602130605280c050a1b060f05070602180904060c080a020906 76
    0x40b0380700c1400100e1200040e02a001c0c0c0680281e040d440442d0010f4034820b03100c00e1524804401082135806a00d55400b0740300002d2064000d00004c83c0c2e840381000d15400fa50103505440c000210112500070345030342c0c583c2540c4c400d030401e0200c40002700c148140c194001142d003000d00001c4002e182040d08011084543d80c10080029040544406d10003100c03840000c1103400320410b12003000c0c00c0b030f061031902944e107100500c4100c002542e6180380036507850301c0400d0300000312846c2d6126140341c2e1508000701d40d002c0184030200d41c036000400030110800c0380c038607241e5602c074454000076845814034100002c001d0482c0d40135005000b0200a4100000140d2081c00000391240340401d100b40c6200074200c4a209035800b0052451158010b610144070980c5020b0346004003001c0b110841d5a122203044501400d080603480104409106041c00201c3d240c000d13080c0c4044804540070700c90190310004241d8101600d0542d042a600d210007202e00d540482241e030310200d0000c055207480e48407000f1803014030a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 326441348 1250 326440098 326440109
    0xa060e090402041401080a02030d09030308040209060301020f040f0f050910060c050c04050403080405300304150203041a0921090f0909030a0e030a0201140d02040305191a010807 78
    0x1010300040d0031592a0307807000350041d0054280102940e114a20561348260f4603405038800e01c600480e0b02c524500c51401e0713400b680d604d940c604056031529403c1c4410124041c020035030554003407103c041030304007443c00741000305107032443c1410503032900342c0845c45000203030003250182400307604000c04080a03241207000c4130442c0c0f511001c01c0c2071505201c1d00700307190b000b0300e5903010741081c1c10301c414141d024040b2030007113000c1e20644841ca00420042e0021410071038032035102d044062190700320807210802559003e0301070044800140c801c000540100c0c0e001b180c049594010711500c54050054140c5190741c0200309000a044018030b080b0f00b409203c81503a400f08941d50002010300460301c4500c0011403c50029016890700d00740031100365200d0b0028449880050f4003a0310400480c54006030000c0103a40684914000700510880345080740e1180f00c050300301c1ca808001c00400140b080103000d1030184200c0e640050f041d024a0f007005c0000703201408040040c0b1040042c03200c4140414048210340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 326442598 1250 326441348 326441359
    0x91a030c0a0201020708120103030e0d0c0b0c0a05060f27030d0b0f040c0306080d0203030f06040216050a030503010e01050306040201122007110f030303070930030306060206060a060e 80
    0x429070308a019105900e4000c0ca0050b02241c44400b0070350354140385040e00d11a8580c0c0308903c0c03004040c4405916410400751910207062400c1209407003260017404a5140d220a0b100039400944070546461815500401044000e4003001841200c11072510008005e0291003600c007514894803d0b5680a01c00203450741c1ca80e1519045100e135a15255203d040700084c106101c40060f045003d030003031100b4810440c0c01d02072180c0700011188080300300d91140d00704401d42c0096840c2c201c1400000e4110542c0e081c00821284034650100d031007040152001d5100ba070765141d482d070404400f8120000c040e84528000e5020b8801c1c0b10042c0c0c0c00c580c01141040d5031400000709604007201c2c00e030007414003460a0b011041e000581c1030511000c107029840342c0d1026140094401e40b0801410317624801220503000060003140103000301103031040ba20083e00000032808481045011840500303070a07001003203010135505d4004000668043c044141d00190449036861500d281400c054000120b0b080b2040c400c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 326443848 1250 326442598 326442607
    0x20c0111070e180d1827110c030f090310060315050a200918010608041101050d02030a0507090509060a030b0901020f270d0c05060a021c0906091a030c 66
    0x100245003205010000100329203c92580501c080c0c85045e1805107161710000310b500c049080c00c103800100714140521480b420700900c0248803540142502c00d21407058440030010850540387c200040d152403151081119503519640c4100b5140a40c10422551045c4c00e00d102000480e0303009101920000003404081881c1e560341040b64010011008800425010300020780004e601d900e015081d550015211996403151084c0a19005103091003032030b0000b0490300c00a80081c1622080c1d550740e1106040c0903041441c2001004143d8000f1100446031540c1d820030480050307440b41d2405c0040000761095900c0b41041800304280b50352501001d80031880e14408542590025412580201503007101951100040b42088520503202d1400002d03a400c00c040c01c0003e850007050f064000c40c0e102270380d01e1031103181409000150b00003102d004154000c0070701100f40c0c0c442c0025221a151880d51300d0075003440c20003101404071501e40d004548150081d0a8808140c91900304407a08450030750719941d1038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 326445098 1250 326443848 326443861
    0x112110409052109031e060402060d02071e02130608060a0b120a0602041d0106050702011101020d050a060f0608090303130f0516090606050a0207060815150a020c0111070e 75
    0x4103903400000d0300241d000b8070400000f07400e051018020803030f403c80540d0344180c1c12024280b0b500b03242c00e04c07200003034010001040041c50080010b003e0303802c15490140c1080441c0e1a01c00000d0407812500a04c140b092540b6021071070407050f00425540c1d0607104200d001d042a01c01d0b641d80700000c10790000f00745e81c1c020307040c410741e22050740920f4020190111495060185440006034019100d5509103220303c804410381c503260100e0040c1610060350b100b0382000d04076001120320350078504070a0500c0d54200901c0e1102c80042c000d0612882c4c51007008601c030f0386806070a05c5a0700d482d50100080011007414403001c0c82000c0b04a076001a0900c2c0000c1481400c0d04180e654212505401003a521a00070340e0081e440b81180000c0850b5640c003410014103503a440c0a40343d61041c0205a00103810070340c03082c002c550250400540085080c1d0240e918900d101c4080740c5481a051071180d1200b400bc03440c0c0e8140f036810000f0350070700c0d4000e28205080c01c00b964003082d41c03000d25000e0095402d168400142d01b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 326446348 1250 326445098 326445103
    0xe1f0806040b0909030903010606080115031a030a03020a0b090a0b0a11090907120b060304020d170c030408061b0405030712020102150406050402150f0d09170f030708011211040905 79
    0x90342d0b00c2c010305283c240d0030706110841c2d0700d40c49021403500035400d00f1030000e01a030050007080e0403144000070080d82c0020403c0700b1001426054690240102c4028152405071001c0202c40591842030300213001c2d00c0c5840c2489407030444010b00800560340040c0392480001c1d012078459800402085010480e10404a8286a14050741202c21703004104001044071349035020031800e841e0030b41c01808114203c0c0f203070140300c01803208960183d00301050884500004038211040c4614641105140e42040300c00c01d0b07203600f5a1710582c02401c045d400003003841355404000c1062101d03022075141e071614003483c1038003003070702c4050700c2c4564040e1401c100844015640240010f820352410703282100703028601490084005c1c241a60260700072009041d03030446424044003240c614440e5030003403900b0b294044044401420300640103c9240441c80036180900c3d8500c00a001c000d107951540640700e00c3d203e030740100002c0d4140d100c07405120040e004500031035107848105502c040241d4010030768010905007540b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 326447598 1250 326446348 326446361
    0x11e031407030605070507120507080931020a02072c090a02090f010311030f03090d1a10061805061804090c17010c082e090e030304030e1f080604 64
    0x800c000c0c1040100210194000700a01f1481d2080f41405078409115034102c544d4002e42c00000c1856070100180460340c60400c10f080c07140240e24501000290b109859a0b541e021550b44a1040c0340d00440d403000401d80610850004c4c0814001103c202c00d4a12022010b01a001d840480d60080030404034252a5085c0003c010030380e00941802075030b050241d0a140d084500744025102c0308002403102c0ba0600c0c01186540c150004440294240300420040102e0f142500d1400c891011801120301110028220624411207580c010740d0170b210300c0e00e44081e08000d01f91090032240c0f49036100901903070703413031348203507111546525106110100712002003002003d609901501044c2c6111002034402c20b03601c2c84400030040c1d000244181903c00d20f0582e41e5240c1035909400c85c28441551543c00051030031410300c4c05003003145c12112160745103000d8084a004031041c003041c0d08000308010505030040d0000400900555144404400803030b84440319403012224101082884004640c841d526500a00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 326448848 1250 326447598 326447603
    0xa0503011b1107090c0c06060602150f1503010e030c011407050d0b210d0311090303030c0a0302070b0411031e10050606130909060f02090a090509030d050115020105011e03140703 78
    0x4011000140070050840b006d0b0142c203e0f00641072180200707205102080c03a4518001070207681c41542c58030078440444000c020300042260464a00ca0030036660b09004005003d14a4400b45a840d0201c070740c45803c1d01c03403c080e03c0c11640500750603c806642e0000443d664084c16400024600140c1000500c1180c180c01541030702c080c00f81c240038440d407008107540000c4501514208450003412101d1030a03070007a000c15a03810340047c8000740741c8036800d100929401d00c40e490300500d00910340d0703552034282c10255802ea030710079140306814619080401103410750403140c01301142d401c108284607a64480a0008406c080758480000c40c045407188400d03903000e822110403e00c021900d850300c880090040141c1500d40310b092440d400c2c5072300141d100700d80c041080641004496410805400e002c0c207805020030101c0d00c010410300750031009034401c090281040e5840014110301e9030f1402800d49034183c004040c02015903c0c0d2511030743c108980c00d01120340c803031010940c08020250103410103a81382d102 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 326450098 1250 326448848 326448851
    0x10b0403150e011d100b010e03030906090a0504060f1403030f03070e0a05120d1d030721060507090608061f0f091a0306031209010801030206070609060e06060a0503011b110709 77
    0x28800c186074041401403011104007420006e40420900440c0c00c140c504000d0750709070704208401c090a00f07050380280312600001d800380007906d07a1100444c049503021762141c805210b48002c00d220075048100c00344c0b40711008600941c01d101400000c01c03201e2002602c401e060050450041503d03469a541030001020000d000e0903d0651052045807102d0040e4801400540c1038000812659130b02d85042401d55400742c001c141850038214520104020313a8450311301480c44188120028070325010b12417240e00305603591907205203820b4004e04681c1002d00b50610030b58080c10428000e0351803410300c0800101c070b8503204800f184040300544242c005500f042006081640e88100200001c0d030080d80a00010b804035010b0f450700501841d094014040100e000030012001040945030038009030501034001e0500041c074600981d10750048540c900001560744d00600d0030448940b40c4204403a009001c01d82c000c1c441c2d0031040718008a50500394145400344607180c01400400603003000842c010b407044100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 326451348 1250 326450098 326450141
    0x10b16020405090309011b08040323010609270b04200a080c15040f050d0c0b0310050f0307030503070b04050a14100f020a020d1101020915070b010b0403150e01 70
    0x102c8136203e42c404051603000ca24070001c1041c880e401c0700403480c20f0329081010304e070070981143d070f07201e410381d04d003042c003030700802c0c0307078281c19541e04000e100741c00040071400400106155615115501d031050006082407441d51403a1010105da440080d40303038080d40c0f20b1412003060042d0312604144140d20a00c450700300c1c0b010030000c80c00c6100010018001102100c0150f21041303c40314103c0a803041d0701842d0400c90702d080d02008035041c548040c1c0755151048142070686034070341410002941003152030b402401e820500c20041400e1820100a0300c010546c0641242800d6440f0030303559201d10388008000c2410000050281310081c4074910f600e0394080205007801010244076580c4280c49091440350a1410710001070241c500d20803540c2c0480213801400304e20b8441c03007007030b200da40140001d45030b155000c202c401001c2e0b8030601014299020b510b84551540382c0c50421030b00c0580160800c0b841060104002d102040000018070652442840041143e910a20f541d6024000080842c01c60050f483d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 326452598 1250 326451348 326451361
    0x531150f020904050609061c03050409090b0a110a020a021c02090103030c06140106080708060a031b0305010b0312030606030a0207060f290105090d1103240c070308010b16020405 78
    0x400038040c2e42c40c12a0180308a8403240200000e01074103a400d90b41c1301e905c2d44500307400245030810705400c4900904003682001e0ba00c8407403000740c0b045139000301c461fa2805d0b01000b880340c0c0244100559440b480100a081c185204401b9640305d0941d50080d12840c1100003030207044140070480380100d940546a11801c0d41c2d00d1401800c943d0070404204d654074148481050810b002911582c120b400656444a0ba5201c1c050250f90380b8401400c429001105824040045100c420301d50309802507403e0b0038540e140c51800c0c49421103800c40354807407081d000301c0041c1c40f9150074802641c0e0402c4003142c000b984c075141c40c5c101d030b4001d01c144000102000e0911200d40b002e070f03803a5448050900c50305a14401d500368ac030300540d00008404c010b00c41c0400c000380190b104e50305013030020500141c8140350140001c81c01200007454161078042d449000c42c2041e4841107142218040c0c5c0390408255031049003000700c141c0d07010b03103054014000c0c607c0407400401c00c2c641c5002007900ca081c01d950042c000b0025402e040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 326453848 1250 326452598 326452601
    0xf0b090a0b0a0c0b18070306050c070b04032601180b0117130605061c060e030c2b020f12130302130e0105060d150b04140112060531150f 60
    0x3020a44d49400320000107802c000f40d4244e003c100c540c2c680045c1800600b15076455000f040068401e2803125010b0007088005500d8900c1c16015900a0b251440443c00491040d00340600d20280c00c6005200d130700040126401d410a4480c52012000c404240701c100440100d400d5404060910324030160744050000702e2101c0c448041c0d505000310411300c103558958050140740000071010003405201d4914190200e40340354005c044514210007680c0c5041d680503001d070302c0c000052103406441d50035125800c041c171401c1010022945c0050015080c41070171046e010391070340c110355065071044c480050001804901c40091102031940103050181c480c9003a10303c10028226429944011b42c68a00450854a4056010b080f525070014914400000c441ca00c80080d09030b2000c03107034116890b50704181442c3d4608040740e02a155804814601c0525070524000b5240c000e080300c01c5945488401e111080307011001007210131202d0208100048092800070541c81d103c0340742d190010b18040025510700d415 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 326455098 1250 326453848 326453867
    0x10507050304061d01050403080a27060306080d110d110a080d0f0605090112150902060a0503091c170405070801051e09010b010c021c0204021305090708010f0b090a0b0a 74
    0x1c90041c0c2c0c00e284e00140042d00e851140340406480400c1c24000d01144602c105403034440a80c68416009100d40480c0e000c0500d8540c1c2d41108002c65201e00301440b0391030040280000548151a2119070600045005610360064038100030801081c44404c1103034010070410044050b41c801e00040d03503010542e151500401d580c181d40c1101320304180000809103080002641650000001c1c481c1c05801c070b559089810b080e403440d2034103258603082d101006d80e40c2c41000c4d01d0501e05030723154a0760700d14050710315500f840240700e8030b4914520b000590101d83e5602c880700509210561824130140c1c6c6031820610315051080e880440f0541c00c00042141c02c0e070600d915010f00010f0f414100b0769075243d810005003a6800418480c1c001440e600a04000d8940a01d1315032003440401068500c403082070700810103a0b070000c0340540c0d420242c5601000a42404410f980c0e00c85180e181c44580b41d4144036520300010514800c81c032401202152010f03081d6180104d180051802c4141c0c03642d95000500e000d081ca010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 326456348 1250 326455098 326455127
    0x30314090a0f05010e01080721150824070e04020304060b031e070911030c1b12030f090309090f150d060615020d090603050a06211202010908070f0201050705030406 72
    0x3416038089a0380c0d4021800c7c140101c4641d1658911031031983e1103001181ea240340301c100c41b581c98103d407500c0c50301a1820480500404405030002941c0c002420505581556520308401541810801140e6002c2c1801c83c0342501201e0240c0d898a581c1000d0000e00a0300c06415410300a1590b0103000324261a607221000245009843c031040d40e40c031010b01150098031002e0300c240002c000241100d004040184004030110343c0400181c880381c42040e1405004610308012100000240404480d40084582d40103030840b00031464802004003003019940041c1c51004100c060402092150a0841e5000b8001501401c0d0350440c5074142041c9000e444030780b00e403001c0ca010314002402c174544041340c0c200342e06403c0e40321042c116240c06411001054010080e1001560311a000b1400342c1200741310750700d405011645040080a2424000c40820700c15801e1000c0d60700d0301c40c0000024200c84240d0f00095001200f030641e01c0c0944c001660180314030900244140400140800d100c4d810803031079051602c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 326457598 1250 326456348 326456357
    0x1c020108180312071121092b03020714060703121b050d0c170c0f13080d020c03010c120902040905031c060b13170708010f2f04030314090a0f0501 64
    0x281e4000c0e194a80c40540301c1c4207860b10700303045035100307006c1140300805404201510000d50314443c81c64455414403500c01c02020f40c0c00050800044c168108841405403240010660001ca1200e00182080c400c030071000f4113001a4202c50038039825103078440904a08107550b1103101c014400c800514640c0102c02c0c1d0101c951804407240401486a01c0810f802c6161581040752900c4908456601780c011780300c1c01c056141c04104030310381c02003071002500c02424200010500030b01d0205010b030400d045402103070300a070316100702c1e02000c55104158441e001a504800035a141850000c14040c19001d280034010b031200080310702101229000d4280510020380c0c1c100400c40d05c540904881388a85a2030b06000c860030042400035002c90303200e01c3c0c0040101d01c200c48100d035407250480d0944880701c1d0401d010f15a5150441f4401d181e042810740c514069200b00e8115403c000307a000158003550001030100164480070401100301d48045600d4410024004540a50303034052403240f2140c03038002d003400035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 326458848 1250 326457598 326457617
    0x40c060f050409200f21041101050c010605040c0c0b07030c080610020712030e1503090c010503070c152009030a0809130e060402011409010206180c0904050f0106051c02010818031207 80
    0x510046e03261301903030703203d81c405000d00081801199150002650120255a501000142a95184a1042c410441d610f030b4510407041d909010700c0c803140c010450010326052607480c462040d48130051550202d01120034008548090300205c0c5007402c550441c00380092a04841d1007456004001010f1902003121030390400924141890080d00040d200300a5661000e01d0007941907000c0d20286503c10000d144c5072f071441c1c64645840361410803a24821000071307039030324041d415000030911010148010800e103510700202c00010035030f034400340038014103440808201da82d1203076150f4084490314801480c083c0544645810380d90b442e00d0054604901050020304251044a440740030380b0115581600541030355903a02d10358480c0c01ea400880508039000f90444a08940c1d44c1441460255020304001c1000100d1500d0705800c5503550340206104440c140b00480c01ca811084051102d141d080c43c4c0701c0d10035100d152145008528089a900e403500005c600b40c1400300c1500f11440c0b245000d507441d00c094 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 326460098 1250 326458848 326458897
    0x150403081c1514090a140a0507020d0f02060a050a0b0306070509030c0a290d0c03020c190c23150a14040f09050c1b06040c060f050409200f 61
    0x1007070b20f48a0741c80c03c0c0d6080d00d102e810901d030003600640d01c65109440403170100c482c2102e9904e80c081c111785114105036a8000d01c031207030340e042000c5a00d00509040032000d080940038013a59816008103004400d90f2581d0000c1c003142c015403c001d101d170b0070160440e4410b0818120190681d00b00d0180302d8040e00c5225034805030362401c0c0206a044554041071001c130381c0256184005848558200310010034400c000302030b01d60089105080900c030075680d005840c4c0762040415410003141c0c246094150303d07025129404226100c8012044070300403d14010304c1400e409089909040420840da1300c1201c1c441680705c0128480c00030220318900796601500f07903c03000440500341c0160301500c82c0841c080c440900414206900454000285407196800d01d21645068105d00f45080404c90306030300950706110800c4080d910340d02c060166401c21504d8004c828900a002d402284203c20f1030b240c036074001c441086c180883d00320113100c103010b140e5924420422a25200d602c80750742c040044d181c61455484 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 326461348 1250 326460098 326460131
    0x20601150306050f100c05160e10030221010915050a050601081012031b0c0f080a0b04120c060c18050402121506040803070c031109040c0302150403081c 67
    0x19501d0040201081c1807413030040c480c01c0c826802c0d110052154035499640031036010412542601188a908481c15013441d10340240114040e00c1052000291001030006030340d51100c2c040910304048040b4030441ea040c03501405424003010260030301249401007400000c070707504030f0752140214917024415521410011910b1507402c559800c2c0c4517800d4070301440701c2200007454010440c041d15040c0c2480300d40d1881080c903120554812140c00444080030448114000c01000c001c00800d00035040607425900c0d500c210080090000308000190745401c81a1409803204440c0c45400c004108440c9030342e46e078060721002420813a00d98110007600b00007220710b010300032190350301545080341040d602c44180c8021603d410b22034440d40100c051002180c021001c101428085004c1c0c0700d441c0c203091031400c02c40041920100aa8020700444003004041254641c0600c101c03581503800320140d402180b1009103034003440e04000c010002c00203c06085039641303030541c4c014004200c01000103c028032065903 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 326462598 1250 326461348 326461361
    0x806060f03010816150f050c101109010f0f230f0d060f0b07030c12050417061e0c191b0302150108060106080c0307090b07080a0e0402040f0b1809070206011503 70
    0x4006544000781040d034a03c644c01a080e46940b0800712a270500199034070300f0a86554294031120000e0125036a501d03136078040c20202ca51921824a190030600507071005003100200850040c601318080030320020344104508880c038103043e480c4460341b00e01200040300c010380031f1407060302c019007610500450201044400c6440702581030312007030740450140c2c0d200002401c4001c058070a001d000e0100007041c1d80e03441c05c101c056101e000c0c00307000300e0319001441070001c1111004001e1000b031030400b0403080310000001c03200207041042c1038180f4215001c404640141424074248080491940200101034000034000c3c80201c07003500c8501185e03240e0741b2540d5260424410000011044004240c00040e403000454000d5024a490311200d511415262100d6105403800c56441000003006400c00307902020115030340404480a40c0790500d0304404030310b110f166000d040443c910005401c103071700410040c4540c3c0b42c0e138054000d410501d403580c000782d103414007442101d8a0110030b40554004034400d12804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 326463848 1250 326462598 326462639
    0xa050f0f25020a051005180307080d0c051b011b020f0a0f06090e070207030f08090603100611010603081e0c0a0606150801060207380c0f07050607030806060f03010816 73
    0x647c2068514070030764001803070203081182c0500400c07402051041062001c400d181f00b01d030b00d400001032010300e049864200f0ba140c10410b5002c3c5507466540c3c13607a1009030542c5103512803628088141d0305000007049076451424842d07201821480000b040c828030544030341162510b8540c0c0780c6495481042c00c0114904441090050700101000d000003011030202c1c041c403d000b442000e04080800b0041040350340251808072040b01800e00230012244c0c0318060411a8503040000e1104900d507070350f0300159004101514401b184c509036483e140119070b00a491861003413004464803c0340b80d0400c4170091006019010b1172281c030303036040031440c1e01a400035412a001d81d801480340d41e02d0300c40b109400c25039009491410412035602c24506118000103190000e513803156030365450300c031011803a00e0107071000d84082070b0f908109020011503a0f1441030b1406c035901400c08032041e80d25000083c0c1140319400804802030004000820782e46070002d07501e514110701003c43c01107691a000103105452034a0500c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 326465098 1250 326463848 326463857
    0x5010e0105040207080d0e060f060f22090206040f1a04030b0a0b0f040e0d0206010504060308041403030c0a03030603030e04020328062d0603020a050f0f25020a0510 72
    0x10080707810709900501581e80151807040c108041c20050b081aa42ca168152043e94005018803441c507a80386c03401364000c0c0c0200c0703103204804200c0b0b01280c41c550f000c14003500c92082c0004214134803c65504076040c551f6000741481c1e030350340d19140480c03c0c95200780940c0000c4400c0e40c0d0104000c00c0307007004403402d80380c10042e01710090340c40800c20809031050381c02c1c07650801c80f6a811b0050948440c011407103a0395045000e0f0a00280d1044024909981603200a2041e420f211003000444d100000711015581340c80c0001c5019810900401d21318810007160510a119002400707041c990700d0b03030101090341e219030741c1c420303014810000300000d0340070655007146c00003140030001480b141581c1204241201032040400c0c8207070780d00b0204a030b00c0368000800e10710303000446100d0b12981c0b0a1020b0406890780c1c0c01d0460824581e40c0000700680600720031a10700b0701c0d0004100030b44250480c1500c01440030303003144030f6800c120503509030703003490380e40c0d40403802441ea010001c0b920b458641d00c1b22004440580e40c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 326466348 1250 326465098 326465101
    0x90c1207030f0c050d060b030f0c1e210616030b06030a0c090801020d1a061e1e030711010c030501050907050904060506180a06080702030f030c0c060106020c030d0305010e 75
    0x950b241040340c100c5049507011400c40c00000c86460760b540d849015401a0300020b01c0c2c1c1081e030141170500c000c503c0c07178040540101c0139012490380d585000f01c2c4600c41c01c40182c08000c50240204554810784980c1800b516150483c0011407000082c030f40e03204155030240d0071006002500150291400c80c245d85034401400d0000a0f1564034070b0340800e0611050f1301c3e00062180c2e03210003c1d030032607029003800001f15480c2c08920011155144540b1240e480948100c2d243c00c0c03260142c0b0041c046406003c2000e110005012207103140c40900c0c1c1099500c01c1201c6546e00d041c0780d003002d005110135140740c00041d402d0130320110300203000348942070480e44040c0c00550b8503514244120750302d61140e1041c4e80e000d03641e0003001c10292148402703880e01c040d0000783c441001c000a010014041403039071090080004104c100312030b280d40401620414403035496001c0d180d854901d1029282d004c0c81d9200c5465201d40000064410350001e50303001440020303410340c2d008000c003620440c01c0e628240200c140d00d514400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 326467598 1250 326466348 326466353
    0x216050109090c0309020d0605150603040f08030910150513150e070311040320030a05070608040f021909150b07021c0507060302032502100c090510030203090c120703 73
    0x400c080c0c503c140a250008501c14540d00140000341440800e0340d01c1c603030380c4042003440b044003000c1c004d0601c800c542503815480c00e84d84840307035a4986c000c005d02c0f140c00800401c000031000c000802442c00c0e05070b0300780040d02c222844c05000782d50510890384241301000703c1c096559118802c000c0302c085600040440c1500f021780d40301c0611400362034041010b07074031070303125200503945009440036500c55503003901400c600082c01c0100340c80b59807105109401860a100009800107404070842d002030a001405559505151040b9240441c0194200c85001000260200d000d510842a03403110082001403040440506145104030b0042500300202000040050b1810300c944c02608018403010103101201c9070741c0c948c1041e0307060b802200800d80203c184010103450742051b601c50200300c0f0700c403240e908104c540207503245036030718010f48e071596541000c0400354851203c00015020151064844034a09040180254400c40b402c00081c01004400c94440c549641d58084803101d40000389400d9003541c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 326468848 1250 326467598 326467601
    0x23f0c1b0609031605030f0304080709091a07020309040515100c021216090e0115030303020d0b030708150a060509010612020c120a03050619090e03040e0a0c021605010909 75
    0x3440501c1d80140144480740003036400b003045040702950520940462880c0806042c600701c80511039180541049c0010b22411000040d141d00315035805801245022207428161104100f81d040300c0c00b1030440c1e8042048042c1c0000040c042040251410401e5999202c1c164003000d4000090a901044001a8000c0309201d00800480c0c030740000d0020b0744840a1086640c503059880780d400c101a200d0180802605549200b502000782007200207100c1c4010400c0a404d00c0d00c400d010007828198080b403d4001c8a10700da201c5140050003074101d80b00d454403034641c0ca5995000b15071030054170210000003040e00c2600e010f648200d8101500180199003410020303912a45140450038559500b0701070113a49000402c0a400c405401c1058150f54040070b00d00101901c00042881d13009240c5145416030706426045070030308890700c000002030f03201d00021640b400c0d84107a0380100e81907540001807000501e680c4d40604020503040d021a402905611035a40050565110303d50201d004080304200c000b03102d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 326470098 1250 326468848 326468893
    0xc040e0d03020912060103050d0807020109120305130605070917150103020f010c06240602010b0a031211060f1e040503030f070908030705060f0c070c050d0201023f0c 73
    0x10180c82100e648136441900c0c2000c26401170314940e001c4e042014016400c02001a00300149100030700072001540c0740c0c98400c5840e01c401c10201585c83d4000303141a0400582c640010307a00c95410703c8030b42092000205404058010b12503c080d071192190106500025881107000007240105456072941c2c080200030441c903960f07141803001c50711042e40080c105201c2e03210003151103204131070910b440d00f08850400701281c00000640e03140001d01d0350701c1e565007005001100d600c404210a18521100211140e08019208003254402d02040c44414404c00d810700340710315070b1742c0c0a001820b0072414580000e100107481c06842504104007050140c0070581c5134507440b205c1c030b0416000c0380707507541e420030710359842648155440d170800e0081c081107500c0e104410b40c100c2074450925003043c000e61078a50f4803030003601c80e180c0718001c8661381104690083c450f6070b94805045101110880c8003880d1100440050040070f00c0d10741008580681101c100400c0c1c030b80900c500c0008000c44901d90040f41200c20381c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 326471348 1250 326470098 326470117
    0x1d07080a0602070c030b0103060606021501350f0a060b0f012a120c0210111e120f040303030b1c0f0f021201091110050f0a1206030c03050c040e0d0302 66
    0x104d2000800818030060403035000b503101e10390015001e8a440d500905005818044801075201c40c001041401008500d62403848204144800381c9240c00d5181c481070002c41c1c00300c5007c0d00806999800046020880010160040700140083c01105042105034012500c000d400f00e5140362403408210400a505078450010b020f0b001000000c0303450b00555014410b841e100040c5c007004014003103081020003640040600d007070107c000443d4a90a544400441c4061001c190024100004a200801c1112811010909503d58822440040303114551180c00241e010a0030b140000c141814941080420408410500083c040241d0364401c07090790080026640b031516102c080303015030f0351240301134200e0f8940c03000020303401c41610745215041003180d541317842400c06901003003820390040c04071403400d0401d20100380d5614500302c0a50703004c205905041c80da203182200c00300030030680010800640c1d025208440c2d50b01c060904000640703603c4546100250003050303c85088500a40150070f0b00301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 326472598 1250 326471348 326471363
    0x61d04030e030102270429010e0a060903200135070806040c020705090402010503060a32030307030e1c0b09010f0c02120306100c0b07031d07080a060207 67
    0x441e2000080d003a030700140000305619000e05074011124034405a1600a10310580d010710412046e400480c00311514085204140d640c2610140704c00d0b845111100c2404030003c00850503113444000042c460400743c0000c0301e031078090904411802007980c0b05452050416500c40843c541103400c24810003400603044070b0202c0d40c0a080c00b1114400090807481000d003071fa00c4c54000d03c0d0004c00c110540345101108000e5400c055005c0c03140e500c60340045a4050303020300700a544c940300c5c031020403424a65079204d610070154400301b01e480f54002096030100c104030b1100540042c11014201a141c2c03080c00001404142e00803035503412400c3c03108540c2e4141c0e000e80030f81c69400c00d0700e4039141401001110040c038241d555030401680e0116034452441102c040744014180d8180c04c400e880e01610010f82401d00c2108849000c0c84850300c56101641441d0740030000310f0b4103080c6180c0140c060007110000e688910101103040c02c611a0008034030b0112103c2c500100b01c0c00709583c031a00002c0d40845400d07207000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 326473848 1250 326472598 326472617
    0x11202060c0f0d0f051815041a03070f08070509131b02010f05010f0b04180f231b04030611070609080310050f09010504020c0c0a090e10061d0403 64
    0x2410702c402070707a18030410094055212610401403c200004000300144007041c41900102600c2e0b0f11014044101514801000b59080042c0404c9000b145d00c40c10f000345841404e100d070490300c480654014a1f0603187d40001041243e003c0e80c125400701c0e03154000420a0010039007c2c40e241100c00030025802e00005900300c008141c0c010204076207014030000d42e45400001103803904510449004124020f47c00d10031a080c649403d034184168455140202c0548100070380c0c0d0318196105450401c00b81c5810800400c400b02d1046001e5520203040d8680b0490000242c050342c0e03c007202c0748100030115421840c150941d501c0e50014200c4404004419809004d4400003407120320031025840e002d1000c440d240d180c81d144503910502e980d0003042c050503100343d0007921a200c2c01c2019040d28030407180561070b01654003183d4508401000010360041c41201c002528405a0340305010182e035590550b804080f86c1b22402e01941c1c1c06218004141074015003128040c003c0c90318480c1c21078801d10b0306c00d415 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 326475098 1250 326473848 326473867
    0x1e080f150301150e010e0c03160306080303180d032d15060c0b16050906090d0611090102070602280305040e0108060f130510020a1403090c010201111201120206 70
    0x71501d80d401c40c1d20703143e11001828006040b40e03402081c010305000421140394600001020158003026201e40000c000c44100302c03100718040c5e08400c01400300c080c212512854642010b44840360031140e406550b0240c0118050482d02ca4003d0203464000890050204102e80b500c6615482c00c940b10207603069541d010142d03240709e8a0740700c40001d00c1c0d50740d20105985c005080c505050280a402d0001c0030048203420701c44103801000b074940f10007084503665180c000510114400740c4150300024101460030525520f82d5581ca0080e02020500b0707801c442c10b16888210580e80e44600402c180007928003003550140d0310100c5c00050285512920300706040a079601c0c154060302d0000e801010032500032900304051903c1c03072000140d00a506902441008449403603041d01c8207541031040792035035000a0700302d9191b405454010480b0441007081039403032a01c03030341254480740f504a8440c01542070504825140d04070000740e803241c548a022142c0305d0391801e243e00f0181c0c1b45c5c0710380c100d82080007031002201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 326476348 1250 326475098 326475101
    0x513140a170f06090606040c02150609070912030309050d02030f0304021005090603090a03020d05091f03060f1e0f1508150a030f03080901200c011b09061e080f150301 73
    0x1250008010400c80c01c1800400050320f07030020501d009c55011490514001a1100f40d4070b070080c0040c0d4110755541c13540707242107070020b240b5080744284945080ca0030341019030540c0403501240c011000e440b100c3e20b60840407601e9100d01000360344c4034803051020070051311300b08861a0003042c241c1003092401a0704008030b2030a40048039054020340003130381c0c2841403680500501c0b21a590604d4661316244c0315500003803c030201c4071190714200b540030400410f400d001e40d1059001e0141c000015081c0e640d210058031203000151a086424062103000040501c402d40c45101640e46100e200c200c0403540d02c07800c481050000f49840b1101418030740860240d00e4026428001d5801042c1c00c1c603074040ca50401400d12180a424140c26070b15044c01801100c8100042d0744041e04060401a0b17100c003005201409010341c1c040429104645040c4129940c3c0c02120750300c201d404179103804201c001c4d020b4840187e1144100343c600030483c843e0000c0c4a0407000a80560700441881e68110692480c8000ca070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 326477598 1250 326476348 326476351
    0x105010c02270f1005040204151b050330010b0405061c090b150d050709111b0f06010609030c030213020d09030504080c0a050307060f02070806070513140a170f06 71
    0x41010341c48009001d1304d0100407000b18041c0c08191401e510300740c946500c506101d81d40c0446082004448000004082c1070b0154291865403c034084a4803000c02100c05101392001c6100000a9140d02c803100c0381803500402c07528129130750b0480060801d4581340a020403a800b042ca800703030703400251000c00355006040c03068205103401208442c05038a84403100c281c40c401c0380104e003407041850412490014200062050a680380d5080c0421048029500c42c2202e01450002200341c1019650b401e51000c400a94143c00260904c103d0300710707990ba890305039042202c80c000a0030002c0c4140c400d00244c01c0042201007040e0700364000500e01400c84604108070303007640004500065000404101c140c0c1c0400403c0b400000454800d140546810002790b942c40e801d104500070301c0411080c00c4d481a0007032129600a10705801500c0151070480f60051482d84000b01c05445425001008222503400c1000d01c150601d010b410041c1290920401c80344002e0140303d4256248214020501c0e802801e00105 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 326478848 1250 326477598 326477611
    0x80d03020a08061c121101020c06060a05120a060b1c11132904020c0601081606110c0103050a15120b0903130303030504020102150408030403170105010c0227 69
    0x50715212200e40003051080c2c080c10051003501500d41c0029800b0f101c095000e801c0350b11504e1900d0300d0b201050700352001e0010b41c1d051140c6510100c0c4001c0342c802c022038202d109100495150110584400800480b101c1c211a400e030b15912030031f03003100048c3d021b901202c20342c0002061003000d8190130341d44400381c010480781161007440c041d400c00c0701406c05202010b9400c005100512405146d80b403209060301582c194042103000d446202d042a0300d46a04540120078a0420743d42e4079130f1902c09040d681c0c2c1190444010a00410300e0004149209528059168442001038002c103004da070011400780c0005001c0302c0145560301c40502c018608001454024070903440b40074001c1d01d5070308081c0e0012000400c071807003c1d0000c000d01001d1500c003041101c1500c0c1c0c5801c0c009441e807038600040f440c000071045410000302c0b6503000c0c00709002c0018051131180384607646000340c11605513601616902d080c0b060b140030a0750084010018036048260b4006103050308515041c84403030064000510800352000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 326480098 1250 326478848 326478851
    0x1090b0a02070f1707150506150708070803180601140612041103010c110106050d020a030b10050d060624210207060203070c140109020f0409060e070e0a0e060103050703030f0504080d03 81
    0x14241000304520a0b80700c2d1040c01b00040129150981c040341401e2004005156404000a0b128040201e4482611662504008515141c0c03402c01101036040c0d500d522060080c0c4035547c00026044400d00c0940c90600018280d64200304401d0600d1050074000f8004403401420440c004809880900c0b804510300840d0b80c81c00380c00c00d46450303070780d0841d2201e400c260700454071503c08401603290404010206c0750b03c2215402141c0c0c55814804044995070889903114108010003000e03c220f60300074005650344000c030ba00c401406060080d150316106403480340801c5e06960b030000b42c20754010040d01d000350b054a000d4588021581c510381240d0040b5050b40c00314049560b1281032001c2e40002411288245000300a01c4810b500090005480d04003050310403503c458440d810000503400c101c05c60003076201161143c0761200c0110110b00811a00184002d03d480c0c100c1c92002c200042480c12260801c01418a00b030464600b124820302c100c649009105003040002100082005004e0080420f0b640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 326481348 1250 326480098 326480107
    0x21905060601090e310f0507051c0209040803130609051b090103030210050c0c060f071206060c060902190305030702031b01020606040e0f010c030e0c0301090b0a02070f17 75
    0x504001d03d00d8104031000c40e10709080000e21011009016180e682e1018030400d404480c840c90a200885d254004084440c1c1084900c100400000d41c01d05845085070a003018000c8014489098680701001960101a000109001ca45001c2c002d6402c1700002107e00c000d00c0342d94956000340c500b0540107c84d1603011455403c00d280e003400404032065411a44200e455141d1346009503100c100300503003c1296030b10f0b4040341c40305c800344049070840f01141056038124a800014901105400c0300c9803c085140342c40701001d0380e40207201c0d40040d41ca0343d888a202e51409501c44500500c4044400c030303085400405018500745100a01ca401035100d400195604c13281803050500b031070023074108cc0c0303d80410801d40e204140e801140c0143d00180039900004d010b075400388020b1405203140303c0c8040d2075180c2204610a075505400220f000d003845400c0b540a8081c00c0241400c99200e020003402411098022491142e029002800100c0c0103600c480c04084107030300e401e104034200c003030341001450b40081d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 326482598 1250 326481348 326481361
    0x902040b04030b16020d030b0a0306140a05090f0d180302040e0a050c0105090a27020c010b1e0603010e0a0b1c06180506060d0c081606110d1b020102190506 68
    0x20f9800b40d205640c1c110201e2035499005004c0c1d56045407030a05014151582c41c048859104d001101004540050042c4020052690752003682e10b001e0b40c500d08084d0402000130a619400942c802494800c0c00c001d208540e0b403c00c0440c1c0008143c0d00748103004400300340000240c4d58a0086260b0300960301d003c1d201c0d4001c189042c138034000b1803054441c1800800d104058481d41c419503190200d4101d070900f01d02c4e0b82c9601c00b50441c0444150488104280b01240600c13140178158080c000c04601a594000800d21a4000c18076503c1c0b41ea50017a8804800c000502c20704602c1c00100b500b15101c004007003042112000000e4449084500aa0b808848a40c004051000e58020b940c1c040c2030307191050404c007419407282c43e00c80400a01c65406080c2d036410183c10025801c40d400020101041078070071502d56181c00211041c0180b24450024981b055982d50002011036428440026038a681010140c0d207000302d2008500400184c0c10350040c02c1d039203001c00300c405500c603008522400c041c01a918241 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 326483848 1250 326482598 326482613
    0xd050702060711060106030207050f0604050c0f0a0b031b070b040b0712090201020c011b050f0307031e021f0902090735190e030406080403030612050c04050603070902040b0403 77
    0x800b410300b002411220301c0100500441c00d1381c192803080c500580d4880170790510500c0c0440d00410941c03144030f1541040144100440c1e110144c0204903001410118070808001072003c182c002c3c18091582000807580f0f0000c103004070743c0c813900001401401d00c00e41e43c03038010001004607821744611080c0030070050103e0348030101c408140e9941c503080100304510340000303544103000300c8050705200400d40194901c0180d24400012a0b074004119802c1945c1c3d000600c1d100c0d00710400c1100460301002d046651654081d569080c0d104007680200308880c001107040c1c1e104005894032400e0f0980d144072070000b68980350b103100d00c01d82d825110304590181030341c07000030480c3e09100c91010500302d501140600e1a101e44030783d50010700580029804150030404d900050460500e00e041e03c0c40001000100950001c54840c4264025201000304070350340d41c004107503a031088900910380e402c1041c210655203010b1303004642040024003142c40084c0c955000000301d9109400c14100b40700082010403c02022 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 326485098 1250 326483848 326483851
    0x21090a060c0503070209100b070302011d030a0f05090402190e030f010510060c080c01020a0807030506040c05030610170a0e0f030a080103150908070b010303020d0908100e0709020d05070206 83
    0x203600d4841c15800c4141c544940381d01400800074400d05039280880c401308100c007001d4010340001d650740359594485150207030082c2041216100f0a40c484060900c10707080200650f20700c0245a120f9403400030322850105c2d1507901500a0302e0f80140d007449075090a10360700301200720014a9403204002d01c5100303000c051a0400c181115180342e03041a0410200e956017510b59011600d2a04014100350031528001e203070760045a00c506138039072000c20412070080d80701110034081c460703d8504002caa00e504050200780d0340b40910510200da8100086221401c01c4241d0585240e07480c6850956060105442d01c2210000c1e0f41651000e501c8500d040c460043c00e015010042c048800110316080d1900005040d1140500c000b4200f1910490301c1c2c050184113130000314505030300900c00e0f42e880e44d891602080d800e50030f0009400604c5501c20400055000f080c901041e1081d00740288208095000e01501501c074485001e80540203a80e000944003150f8000703040c02e142e0222001c9420f150203203009161060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 326486348 1250 326485098 326485109
    0x7021c090608100305030a141e070c0b04030c0b090d05060f09010f0204140d080705010c1e020c03060c16230c0a1203080a110d090506010b090603060d0521090a 70
    0x3c0c0404000250001044400d001a02c2c20200300105002101c58598014080f0059501c00444000d0403a510a54000c100452241d481c2e5084151203400000e120301541c040101001c0000500740800c3e140b4002800a0050080002e1035054640e030f038181c10403c06031404032040b0005414000e00710000c0c0120700d91948442000c42c14140b0b01294104140840c505050183c540001d01006100c8400100c445460b0040020312540d954400c00400941d28801651511000d400590590900c04100ba5040701002401000d81d078546100055842d44000d95170781e0038440030b0100c0000030b2002c55000e030108500412101692404200301814910110308242c81224030440c203020480a50000c001042d40514180d109076803111265401080c10034a208150040404c190798054002c1e040745007132031b10420944166980e162036540d250300605151581c011001d1000943d58108030f40300b00c608900550440d04007418032020b4158885003001d04100504001034107911310304000004400900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 326487598 1250 326486348 326486371
    0x7120f0e010e06070e18060316061e081504050907080f0a0b011202010206040303050901021606020d0606091d091e0d0306060507020a03110d05011b1205010e070807021c090608 77
    0x407065800280090121008014a003801b5000b04585072001c0000c3c480d491540070030102100d88414004d0000101800ca120b058498007000c0ca211502c11540741d4040d00701c070014103c0c04190601007101610008100407a2846000340004c1c0c10325042004000484245000c0e0003203040c50700708102500f00503008005440380102075800140d03800959258010b8242c640010b07192600c07a130036406485110509919000f220541074140311460f80103060680390740c0380410865542c1d4200740c5071500c45210b4418204041c02140d920806813806031540141d08100303032340514591000c5695400804030f4901c169a001c080049031f040e425100e150007402c1242407050800398981d00080d007091090100400b00e0441c5400042c440d2501107260040b00e5005001344800e84c2080300d41101c82d00c1380c04100d40091900241c002140703203184192416240c3c06907045d04580e0ba181d1741940c048001070f015070304501c500c01440108480740e00b445401d02c0140d5460f07040d014500b00d001003625030082d11401000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 326488848 1250 326487598 326487617
    0x316091803020705120703020a170f1c050f160c1e080d0e031903080a11180d03050708130e0109051519050d060617031207120f0e010e0607 61
    0xd0300040c2d400f044031800c50b1100c50380c0f401d00305032608148050744000e40110b44030801058200035080021050301c00d900407199080281c6086540c1c03038002d40d500c21912007000c11844030300c03489034005040c1044402100780c5481030b0f07048000b5100c01940e1058924128014007880081001500c041ca005000441c01e00b01d1803c00d01840c0d110300402c02184184519075040c40c440703487c2072142e0b42421807074260700340341d40d10241400303804120200c135200d810520f00345038844090002c0050b103030311008142040c006908080c042c000294240e007025014014240107500001e0350900080400704101c01c1d000400310f00d0002d40405072003040e00011009414601041450251010030903c0c5140031200d4440c1d80002e1884d006c82e018880e004160400d8100300010140a045d070004d00c03c0360716071182c20041c0100400e59503140e00030910001c41c06089640481c03c124855024030002c02c6030349500203240350805002c0012607a001801d001c0503510380d04808809102400110b078484524103005601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 326490098 1250 326488848 326488853
    0x110415090b041d0304061d09090a0308340912080406030501060503070507021905060c24070203181f020105060102120906040303030e0f03031e0601030212010b030a090203160918 78
    0x50f40505d0244c54104000e15160f1f035441e40031840c0c020204c5074050958a0542406800f10743c807103100b0a4182c010410180201301e2260b0700426006c0d00070882c0403648940030107052541200403201d0303107a20400110210104020403030f107000c0700d0042d00c00c00c88142d80f24503140010702a120141e100c0028410180b00300030034181c1040884441a50442e04070425207080c8121340264015600843d81060340403602095003180000c8045140d06950300701500c0341203c200000c0c03820340464100c4010b03041131011301c0030007601d40f0070069094001044442c0e042540205001001000315152006039140e6041c00950358050000b0b000304441385001c14a40348008010449074807591100070200359440440b07041c040028461007600441a0080d01e54074200044010a03213580c02c5400d240481c0400d000c50760541c000c0c03033162868030b028205142c03541e20300118090f40d500024600d1284545510408005035820701030104140e444407140c5200604210310b00f0100d442c0c000c01c142401e606028103001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 326491348 1250 326490098 326490103
    0x90c0207150801050d06020d09060c09030c09020c0d200303070503150d050319090b0f120c1204030806180c0a021e03092202070302010506040b061303110415090b041d 73
    0xa00f90451005079070f9234403600c5100d0080940810180c1a24902000d510700e1960080d01d081c00c4900412050100544551030107040744600038240781c450b0300811403803170201e004080318a0715412030384c120030030504100c0150703045500c1103401c800040c038000304100340110b030401100803600d0180e40140c441c00680d900c59949100b946c000705050100e402c0c0b032079004e911070001c0070041c14940010607250303641485124500c2d00600e0011142400341e000084460084034195000036a200303d2000720f80d01c594406407640c03030300038104541151260362418020200e540070103004405000c0525034030541368500070309062040000c00e006040a207420001d108000041e21105041180d050440040c90300c540d2508003944e0b07100c0e111150000c01c01c00203043c0c040d8080c2d8410a019901031000d040030104003c180e2140c2c03001250712010f80441440802d08000c20321440c42c0e0040d10000325941c040301e2511780702883d40d00808000c0e807200401c513402c1c10940101003070520f01031341000340500c4020307003180c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 326492598 1250 326491348 326491369
    0x90a14030604081b10090512120c090a08061501030506030a020618040605030d030b03060708060d031d03011503140706050a08060a05100c0201170705070803040c090c020715080105 79
    0x20b003100d0300424031544c1100300840b001c44921440d001c0361502c901c6100408050400005c00752841d0040c848690034500e4004112454161a06020015650740464215140e040000801d400070108580400c07507160800c881802004103080c030402d0400500d000400355080100882d00075003000038124016150316054482d2210140c40c004020b40108021038010906030707109581c98460700514640454041e8400c0e0381d40e01e001c3e0140c400d142d481880c00e880e0a0404d55145421800f0b205100c00464401d00d841d1145058420400443d14400000070342507034410b0701000c5815445080401c1080148490700f004503000c80e0280070810324000c0c018003540280d80040041c80030800001c0d550740d5a200800010740380041284d04049010400109001d8250a0480c041007000d0f00301c40c0d050761351081d0720f44218819a1581d242100d01da403507200c1d41c2c00107030088984801d04d40010030414454090024000041c0d8020010342d4a0a200708100624600c498000d104407100144600d480b440b400c032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 326493848 1250 326492598 326492603
    0x7030b0f090a200415020703030f030f1d2407020d0c050a02040504120305100305100908040e01080a0510050405060f06062802011d07061b0f08090a14030604 69
    0x5850303a81c0b507101c035038090580e030201044000101101c480314903825a016000755003050f60b072441d0340f04c00c985080e80c0d6588a030101401013402e4a4225240501c60f8001904100c0c08442c04250a0910390001006140401400c1c1c0749030001700b005195070440070802c00000074040c405100310b040030400691030f415041d8500f41007200140e04c03802070000c01c02004640301e40c0500304003e60300d020b08190000006000107080005c3c10140440d54800130780796140c054030340150182c1300203082880110001c0c001e03101c045808800602c80020f1805100000f14005c18110b0050300c607000903454441e0500134115208010f45103402d060001007140001c1c007680c80032046442c55050b1b01c032000054035034054200c0c042c0780e40c5513402c0c504809000c0d04100c0710540b41c00d50024000009100c01800c00c03010028004402c50703000c280100324407441100d00e0081d03503080500b001001441500c07079140e040352942082d01c0192000416020f00e0a0010191000303010b4180c031740f181520b4610002c0d80302e07a00070340003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 326495098 1250 326493848 326493859
    0x4140402032202061b2d06070302030a1e0e0d17010306020904091e02090106030608030d0903030b09010815060a0b03070f0203040503011505100302090604030813050406030b090607030b0f 82
    0x29a0031134035a00c00315951203030901c400b410321400d0480ca0650300d11184055004440c1e0b0074844400200c2201002c00c0b030742c111480680150ba0f20321034110000e400041440140a031211804255500200d01c680c0c14550310100108003010010711032450000c003021800f080009042e000c4400488881c00305054035401140580d41c0d032026400a4050850300d4806421201d0240071004984003c0041c209042d1090300c0b2019180c0c0c5c1e4103400da013181d205200d1840f09070001c02801341d15401980c0031741822031003824000703078060034000886e941d001c0903040442d0310340c8070044d0051f21011150100c4d6101c9001c6844000850030110f820006000c0a031120091004401014681a00a0003078a0107030102030000c0043e480610b0b0708600b00c400c2c2e446118001e030305400469280d94031a0080310741d464800b904d001d107424955603411250f913100e00c4003078010744056a00800d03103540350b01419000f0b602801c4c2d00c1215003070200203070b4101840a4000308c10705141200005007a00c0b249000018400201c51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 326496348 1250 326495098 326495161
    0x7140102010b120c090a1b081b030117010e0c0a03110109081b040f0b011b0501020d140411010206040201080c07020d0c1d010801150513020903010903050414040203 72
    0x141c0c090554042c40590000d0800010740700e8002c00940760480510031a45464141c40e14000703907007115582c060000b2000c05000ca5200300500031810b240d0400082c1000d808150194000c048942d002a001a4203510544611804080090242c440b1b240305100181420800100004014400c81d00c402020101e1060481b031507070380200c0030b40c00188040020344400d0f081040929003141100d6a07030610841c90b02e1813031012982d45101c1d070400c00d079041c1c5803003c0c1110400d0b0508402c0c01c288004442d150b400300600e900c0c50006000311a0141051200c2041605051030840c1107c1005c0c0c0d6010304551000c005c00025070391110602d80c11245c83d40020703540352018000308100d40212070780034004944618000486844a04d85817020003503681e60000c0f142d884030682400d803581034202100c0086160b00a0200d41f42c8400e0396501e4040c480320040c0303880b90100c08a82510080d09040d000318a01190130003410320801c804c2c0b000c401044400314510710b401c0d9074884070340c40c0007440060308224504 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 326497598 1250 326496348 326496389
    0x60102010f140a14010b040e2707060e060c0c061b0303040807170a020c04021c090b10290705030f040905100905040302060a0b1f05031e010807 63
    0x601c014510080c003103050020b4442080407040a01d015103908800c0c91a095403404020416041c0e14140d901d411946031400b4a8052002d440c03440180c124419081d03a018222291501082805050540c110160001d140f03070400241c00342480a4005004810401241218100100c6e50084034207080b80d140e13803503600800e0080c442c0d06000b40d00c50300d1444004280020f00c1005405404000d10603040060456510711459003d805078680c1c43c400b40e4401102c9580030b15203a000307006501014181c8001074841a60148142c0380d001c0002d5404035402c400380007040d003080c1e07526005001d07050f904186d103800b010070720500190812001d200b00c25011030401c04000c0305004482030a00d2229035207849684403802c0b400201803d544102140752014000a4015028000ca0340306a4064014000550b2101d00b940007404030300012540c031107441840d071100d0910009070801d03e0280303a508d45131030b490545250082d500b20300480c8540240800010085a003000515205a992012000070040c8504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 326498848 1250 326497598 326497601
    0x1504110c0304061d04060806070c0f1505040203010e0f0a080921031c060608010e06030703060c030209120703111504050303181815150c0102030f01060206090304080a0b06010201 78
    0x840004880c0000507000402139800320545214031442094640300c0b080034001c01c41183e002e40304511064108000050b0792500441004d500301d401130354200a5aa01d5035200010f240300c11b40240061660303071043c402541024402e00402c0ea1480c8002c0140c031100c0b0444d0780e520b0a545400601803040066081115164194105213001c15041010784e58000d15000e240c494105c45000c0103603150281001d8450720140c002d840c2100c0c526114141180d0030009551000c0d0320042440ba010f100b600000400a480342c42181c1421109607001a21409603504100c0310000314480703011107600c0382400344080707560745448943c0c00b282151800740c0790722101c84100c03042c020b603405a54907000111b1281d035440002d5686481c10101200d10150407a90340d40700313905075039095a5008195030312010803481401c3c2007014405110070b4543d260700f001840040d082c26a801120358003240c51104004011403a010000c9035081041c007400b450030315042914007a40d42c50a401c002e0401040c034008103066134001e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 326500098 1250 326498848 326498857
    0x11040e060f131d0604050d020d030203041203050601021e03090406090e06011403070f0e07030e210a0e0406030602040819050c01030906110d1a0132210106090b03150411 74
    0x580d002c4d100c0b1441d10381009030325140f05550300380240c003441c0150078809200344210303031082d9400385502c0c0f41080641c108600408006100310b0540c8902d94280c1c80c0b81c0e0900010303a480b4181c550085544084141c28801078444030340c0070000e25420803c001c6040302c408117400c6c0c15581c2504401c4105501000024600300240d44000002019050081000903180c48114030540480d00c00340500b01ea0080e149590708041408c1d0078004c1c0341a03403414154080c0a0003071008180a117440318100c0c60322800181200d00aa20860350164002010000c0c80010702c0514601000c0c0710038180313011100d84506460f5881d030800d40c5c2c10941da5900e40c1e0104040b9a1110038250050b0010541b2000340303507100d10042030402c04031000420303450588071542d03118140b00c13110784518001c804180c4940c40c443d101e0400282200d000c6a20042c41118280088141c1508a550016403240362070f501d030201c040c000c00f1044e0070880c1b8004007001000310881c0c07441000001203409032030019652080700191310a9015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 326501348 1250 326500098 326500151
    0x5090d020f0a0308130602011b270807080a020f06090307090504020a0306060602010c020708060610050319110a031404032a14010b0a0503070608010303120b0411040e060f13 76
    0x42103c0000c5c820706401001910101d0b002004858032003030212844c14020a0b1810005221442810a1801c03071220700c01c016104040001c045178560611900781045c9070084500c940c42000030105514001010100e2510151083c528040c905008a40c0301d205a0080b100045d4030b800100f8110b4803030f6050032004542011080100c651a00c000901038591580b01500611500d0000708180c0701c0401e869001d007400500303a1a80c504010070945440c0c00050000f4183c10b46a444080075010902405036100341d1110141d43e030b000700c68000744c22540407242101c1070401c10010000082d40200039010540b160b90010440000c0000007449030f0116003100800d4407a02206840b04035905400902e02d9a80458240b014151244285a980e034118804c1000140819004201107400798140c180b840b10352500104008a5650101e800d5501c54a004150200009001c22401c0c0890146540042c000c860301c014421003400015203c803070346c00380c020f059640c0e603000c003030b016020040d000380e00d11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 326502598 1250 326501348 326501363
    0xb180f03030703020912060c090d03020c0d030503040201140307050a11030d060902030108010b030c18060a0b0408060411030c21070f090507090e10060e010e0315090d05090d020f0a03 80
    0x1e002c01c0010f010390001c0e0300e0103018001c2114072082c4000085100d81c8035030131040860f824a950342c0100011901e00c00c0c0260107602038139030310704082d4a0f03c4800c2c01445003e9102e0741ea403030a00d8400102485030542460842172401e00c20700c1802070b0302800f00c440300121442d18908068000a00d5415842085446906a890840c0c000f400c20155000345048411100081040e0307400d01042c152261804110181d20407003004105618a00034111aa040080541912000c640b2803120200c0340d03000c1c5c0c005078020f52200e010003041011a010740f42160704103074080e00f002600100450200c0d01010072181d581c0d078103043c40c501c500310200000310080c00c5441c41003c80680c1d0700798920003003c3c1a15144001055000c0214420300400301c40b502035501001200c6615240440840750104002e68046c10400b8005940c800c07079604008552115402e50185070317036400d10780c1ca10742c03a1030034450308142445024002d5880341c2d17544100c1a062143c0580b40700a29402c440006607200449800052802 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 326503848 1250 326502598 326502601
    0x7020a020d0303020f0d051506070803220f06021206040b1c03030f020a030e0607020303190905010605060d0b0a170a060e0f0d090315050c04060f020c09010603090209060d0b180f0303 80
    0x70680e410040c09000a100c10046444230381e010300c481403041440c09031880b907040020811040d100c00c404407010160105001d07101c0e42c07950b11440551600c0d83c0540f20f0320340105014103d40810f04401c0c1e046401114204500284080400c119580c0821031075180c000c101d021030241400b941044002141c8400115580c001e640000b8000f41444012012103103d000000303440b060000080ba80210304020480c5103410908a6203070140115220866040d5211100001c00b512404003500200c00150700100c0d07640014802c0c8200484154406c21016031401e460304441100816281c3c1d0403a00400003207440c8154160140c03525807005a1205548200340c0e0a031106684074220300e0950340728410724595803040780030b00415604140d0350000991000c020401030300d405840d0b5000304000303500658507444104c400003402d850003603001401090300c88c0e03606021890b0400090390f02c1202110509d6651440703032103001d51044005e00d03800701d8031401e403810700119804010b02490310f82c8250071607549 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 326505098 1250 326503848 326503867
    0x30207020d0b0903130f121203200c1c08060d020a0f1509150516030e040504050d0e040e0d1808030309070f06030b09040615051504170607020a020d0303020f 69
    0x5940c008a045401c1758502c1c00089404004080901c044030250303840442c0c003070001c0d200d21800c1d6010b40c1000e014103a89207405047c050300c141e030480404232001c40031504c0b9408003964504040200301e21a2104203012101d449044e000001c035900494155800c8204031007510110703c1c1c0409940105a5802c5034030070000d031004004009400341604c07130b95044056695410714105603008200b03c0e101007002071141035070700780c240f08070304921078020305d048824000d419000c2000c55070706450582e000e030401d4012440f102d4000c2015229207800703413020002c0621490380d40e91500c02c40c0c0d00c04d07020072419011425096001000c8580501100300a5a80d2402c001e0301081d0780305000c0c030540e10074030240d480000700c1c140648686941e40401501e842903658856881400a128100c5110401c00c0001d00c04220703034a815032205080440390112035511810300e07003010000041822101c00591140c010040307140d41c0841d8614035143e06aa0860141e000e40c40c00390040e0085070400c2a610318003080ca25034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 326506348 1250 326505098 326505103
    0x9020705010c020c01020a0b0606030c1b15010b070c090507020705060a08090c0a081e07080d03020d0b24030405010902041803140408120306030106210c2301030207020d0b09 76
    0xb103920a034003203940180b201001aa114140020003806040700d000018509041040085902490006c202850400e014111750b5035480d9943c0301009540c80b8080140b401450380205078054040290f010307003050215a03460260704201d0140ca442181c450020504441c020003950700684001461142c0b1103c44003001000d6290844141d1603070b20441040c2e0b0054140580c0e406c2c165074201c0e02525801402030740040c514122804420131502c505540080c0b40340081c442c210790101181c0d4090703039551442400800751848105090711403c80120503001d10407000240e03034030030001d4603001c5403642c2d21406e0440c01403075036000c0a90420708060b40e41034040ca40b08880c203511072107a10b4441c40058014507120441c0164010341650307038011526116002242c1000d564443c03001000400c00c5074540c02b818000442c2c06411a0341d138440c0304040d00070080d40000940140006a4220440d81803409851001140d4640340c01c0c103066000400c0c1c0107548903005403c6003190081515248ea0615403d081c0d07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 326507598 1250 326506348 326506361
    0x905240702030a1a06040507080a0902030f030307031401080303130311030f18090f040b1b0904020409021207020111072a0f140102030306030a0308070207030b0703020a120506010f03150902070501 86
    0x2001134807004006901803810744140e0f40580c40707640c0c07000ca003079689481c108000c110b1240240e03070510460040c80e103040c400700b0003540320b800700750f80c045a00e003160f1040e081407542c181c1000c070700c0d90824420042c1402c021131075030402a81504c8c2034041c8280c210303111815032042900b099645e42c00020b191000c0e0352903c085c08030600c810b4401d89000d503510f0885480c1c2401c182c0e001011002c2d075101144802441800c50441d1080141800b8a0040803030005000c0b640258800c6d0802a00820041014071b4101d0f6078a501c82150700007408015035910141a6078031442100401c100100c0145d0303d0101140342141c003180c2c40e944c403110103041e02d520030581014482d05c9180c031688802e01240e101075102109803801580041c0c014070190a41d0354094524010081c502400c600c10602c1c00000310b0200540c0500803a40c0c5d40f00181c3c0d03843d41e00c00080003500b100c3d50030080e06081505018203a43d01c4220380011524514000408103440b0503c1302c0c2104841d0702c80803100307001140c0c001c103100c419230001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 326508848 1250 326507598 326507633
    0x3080a0906020105070e090907260601050604080706082211032116210305060102060a05090316081908240a060305130c0305060609070905240702030a 66
    0x6140480d0340d441c04900740c800448080000400d035030820201c40c10f0101142c0c0d0400f000b8400e0b18504da1700c0d00220b0012a800e110b0a0091002c4c1825503090b07001e09002e42c502400e0151000da1405003000e00d4240c2c0d80c4070501c100300c00c00c001c100000b600140304944040107400100d031103543c05045420080c01d046500c1c1d007941e2090141010756025802074160300190307841022515070a24814000302c000780340f20b1800035240300440fa594007140510b070f42d503803521510403910f0001e844e082003800280b5103140200102e0b8024a00f90501400c107070000141c9040c03846500c010700515061345083e0700305004e00601c101d40800d6442061426a8204440c10301c15603445540e880001c0f4603180d4219588100348120b500314010f42c030203200c0389200390021540010340401742140034805642d0054424240da0042d9003d40003a403d02403686461404640c21140390b260009000b4100000120b0f031508109643c3e03229804d00c592070212692400035942c07041c0c0c00800307031902050b090504c01041e0600c101103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 326510098 1250 326508848 326508857
    0x40b0402032e06140a1e0506120103120c020d121403070201060e130c0b0f070f0f02030d09060e012d05071b150302030a18080d0b030a05030d020f1303080a 68
    0x4c51030303620207400c0c800c00c488002d006018103444c0c6007100f048071201005959543c00e015030089a070381ca50000529151858031000d125035132460a0901d103564604e140103007005a003191030030160381c030b0f803105070303400c82e00075061003010410a034098641c08070042c043c0403034000110800110719019440b080841d0300744605000e496640080f0b228501c8003100004200d419107480038804c008402c0c02918140b20240700e25890709900b51101004009085400c4551070040c44c12a8110f080502402903400c0c014103189405904201000e007164820540c41d40c101f0034078821981d9820601018500c62001885a0303941c44011200c005082d035120700e5042d11940311002c103201a000c1c110310424111101c072140e20007014180e460031006944040c0120400ca0b4a0f0802600c0110b01c100c0900c00561180520594a0891104800c03d80307030902010351003500031001403800700e100030084506100e01420010f0b6154000200601a0b006003440241d40f0344007100d000c000c010b50540200003020440e1038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 326511348 1250 326510098 326510111
    0xd050901170a0e160f290f1c23090d030b030a140a030905030f0309090403030b090f060901231309140706091a07060f0221150301050708040b0402032e 66
    0x4201b4000304c008003070000ca0100708108603021900c3d5501822a198400c010b241c940b060b02d01c800110390316516003038091182c0c0e41c40c004203070b9600349085104000030302406091f58a40b244044d0b454100801c55602459143c042d6540c05540501181000f681c1c80b00c2c220030b0900395280803647c0c807108007000301c1c089481d15001207940d1500146603031070080d01070015440e0605540a10540100241080f401d260f12084144404da41d020101e5100320388280c0c2c0310880d860200c0070062443c0c0c044c1c3c020614680302c40b000c5002c0e40b103a41280d052011083d40c40c0008a800109424000d281c202005450794144135107010700090003044034000c455a80ea41d902ca85a15030041c0000e941c1000145142544200108000075041d600509207400007010014106000c8240c200c0c074607601c0300d08040c903d40102d010001d1504001c0b10320340c00040158001c002c036142030071000e4a85800500080e01e1409207a001404558041040c82030407001d03000245a403030a113015131120482c112401c401d62600b41103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 326512598 1250 326511348 326511359
    0x2130908190212180102070308070b102306180301140108012406080403030e0d0908070b0a090b0304050a0206040b090906030a05030306300d020d050901170a0e160f 72
    0x381d2410a0359660f40e006203012040f016106810341030142480c198003881d00c00101152003a40a4001b00d40a00d15020030f80c900310017a510f03130000c00c2d001640421a8800190345100c4030746803845007040c081d142160f4417081c4659002c4070b548401d00080e807540c289102101c000c10318458044c101e60705e80e4000d001d00300341020880c0c094816140401c4610504000c100005031103402c1c1160403a000b4240080c5100d10500000e0030000f0003124603000ca540c0704400c00c405d1004001a0000380a20504d141c140b0b0145c420007010101c1078410001c001c10080041014014207010a44002c1d0303008101d03680e1a559581002c0040d0041500c6a124100ca04001251400d010030241e010a80c81400755141d03560b44e00030491032001070542521451202c281110850144850641c840000c98004000143c0c50500003031804070f0840984041250078008501240d810a8117070100403506a04102c1e141e851740b80d10802040407100d10880752140d0309940c1c005040f00309201c01036402c00c81c03226880c5500ca4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 326513848 1250 326512598 326512603
    0x312020c06070e040216030f3b0310050108070501090b030f0c250b0105041514040f23010e010501050a020604020f01021c0906030513050c0409021309081902 69
    0x201035210190856000505194414051034a89a078000c0006052412603014180c68a06d02002107000c96040c41d0302c1b860b155002035408002c500703100342e504084808803500c001003151407070304142c1800a01c18013a81903502406840c0c7c01c5001c22004112960791600307003690340c90f02846543d0100e0010300e030100d03420b01e80400700d038800e11042003444101e41b00e0055480d00303540041040842d240c00303203203101c0800104090440216004100c14070b440c0d41000e0400c0102c42c112079075420703000d2100908200c43d260b44950309103072580480f400a648284a000300e0302401e40084a04404080c0754907800300d01d2580301810b41613580c95010310b10261303205d02c010364a40c41000720250260744110001001850a004150300320030041c030584440c1c1d0502c004001c4040c00035100d010110705000f1003888115850f1107070320b51028400f0844558804251601511040000210b0740965141e2655206540301d10a5807141003081c142d080110301114141200c450f0003600c8040c91310b214541481d261103200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 326515098 1250 326513848 326513857
    0xd11040b120417040b030105090c160f050307240b06040b04052106010602030a03050f070c020405090c120102131d01050d05010b061c050906271216031202 68
    0x103410500d811005209021401030003841202d07080720410b03501c111140345802410040860032410303070f101d5040100f0452540c00003030070003e07581c606004a110302104080740003243c81d0080c1c0c0100000440b030515504607c0703403010203844888204200f61100c03000e84000720440350303041130402040012004021440c4140d101e000d85070b1406000502a91030918441c40805442400800450110141503420110241e005202580004c01c440703c459400d805000e900140140c034100355440c2004000c2d20b0301d152854003030f00456507980002c0e1014000c100b0600c3c200c4009000e0b203280c41754510194003035072003080c1c4254840c00000c40000c000004a01103040000e1104103020240e00300790902149200740325040e1170f150f40321008041703241c90b402e0080c00a120048181d0311454180c422110035101c000e0108a0154440e80402c1444480a170404d860300b0700140041166052080e44185020807201c05010700e010002101e0141800035000507500a11a458070a00c21140030340c41c008901a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 326516348 1250 326515098 326515109
    0xe010e0a03051e0309040c20030f03010303120f05040b07020d030605090114061204060203040204180b1f241715060706090b04050a021201020a0c1e0b04080d1104 71
    0x2c507107011008039112494080c501805902100c0c10301c000000011b041e10403130003e400100b115034100390000d003080e2601301d1b02811000d004514120780110820200c2c031051001a003002200000214940b581303401c011a8000c646a040c411402d0a0a2584210b0400e6030407034054400c1c20b034540034207402401900c0440e200100f5070055030f86400206000c12105054159020b02c00b0041090a5400e55202034002c0e0700a410060701c2e85082d1041c1300031510400500104000640b03100c00005021406d9035030300000d114880c0d4255041c820510541c56031036001100c04152080280304000b0600d02c42070084e1009543c1c0440d4440411000318510f00c00b9204494581c0000515081e1410f00e540100425442407000003211a400e1312034003e01b54017aa001c4844c0d811050300d0000394500003184d005502c2110000b14a045e41010010348402800d031001000401c40b1035014600210f0b0200000c00240c0201501394a840d05207000c201a030b0100c1e20044125250039000b160003054881650260f82 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 326517598 1250 326516348 326516353
    0x702010c021608150912030106030605030c040509030a030e120a1e08010b070303200301030f0605060303040f0302040f0b040e030307091409040605060409051006030b0f0c070f150c0e010e0a0305 85
    0x240c444e22480541315005240c91814801c0350403c5030000e213840002e500911310765030700154080c1044205030610348421801d0f8411800c080600c8500c0c000882200d840601c45d04000500c401d50b48111424207410001d000d0b61640041413880a1a4003c00c026074024101182c0300d0400140110968800c4801e0084500c2880c0c2404454000390203a442090640390b00385480220311003000040030554426001140e281c4070442d008400c1216134041c054003c0800c602035414542010b00d4910203040c030f448040d100e01d4035010304c2d4000701d6075580002000c0802400520003c04680c10140c0c1d00d500503244103000031980e15000461042c854001d00c20320704001c040045580340d585803403000c2e0401801c11540180d840440070000b0300308011038602c1c40620700c8045a06491420080048400242400100c400c4002000000882030b001c030380400f40c0c03104180041c07440d9810701e041e00202d0201c410b40100d1800405164054010890742111042680c2d403c001700b2070304062011b12600c0c0c4c8002070955 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 326518848 1250 326517598 326517613
    0xa200304030819051315030c11100f0e1608070e01060804030806041428051b1c02030a0204090606030213270f0f2901051c050702010c021608 62
    0xb03543c881050300241405281c06424150142003c4000c00030942c400c171a100020340090070242d40500070b42006480605040e484d460307580d400e0030f45a885a200d03041c1082d5941e4101601e000003a409440d141c00e840b001c8a56035803444200044841c014010a6524030801d0b000155851a500c18141a56101d56524016031211342e000d4649800140816030f000740c6808280c0ca01030550018240301d900341201c85074019170b02e11031032070212821546030b00e13484e401d03d02002480e0030550300300b4007080c00007003103a6a5a00d615007031b03503180c4a40803608000b460000042c095103607000d40140c0261101914100102da1350745206500300e10502c2e90104616040320810030641c80402e40101544a0300c0303120b100c0f12180007440204403840035404890031640e40e11059504070b014401c207000303032200281c1981200c00c0b450720704400c800f040d02c2e9a410050001101c1c64002081036004840b008002c02c10700060800702400b0340a01650000800144202c50340391501c03800c0c40c0114001c0310082c0005d0001da = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 326520098 1250 326518848 326518867
    0x180d030e1509030607021c020705030309090a060e0103060e010f02070b06150c0a0803090c010c030c0b07140c06060f040605060a0c020303160321050c030f19020a2003040308 76
    0xd0710700881c8440700e04407040c0580640c07034405206943c820301e080d5001d00440c0081c0300300210150304c0d8010600465104040510250b1000811200c1450003241d0b40e01c203959403481c40401911003604405100c1858000000c04c0184c1d9400c51059010700360002c1c4240c40712004414202d000d0351201904084400001c1006800c0250300850070301e50003030381c09162400358040980341000582e0221080b86c00007041002655040c4020707150803809291605800c091518014025041200050310703050300308000c02c2d200c6c0c1c042c0b80030030318145c29011810341300c403001400c00b03403201c0c1d0032142180504e410300780032400c501c0c0c94800c02c0140e80e801000942046100e80040f00c522000000c00c9130140700400102070f940c021020980f008a105e030740e54a420151001000e0f802d2444140041a25401c2100b84421103200741c041d2a408180024413030802c1d80d41c81400c00103094551343c084207a40c400a250810700d0b0b840881c8120980c00c1402001010303a0f42c10700656248a40e00c0082c208100a1002c28403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 326521348 1250 326520098 326520109
    0x21603020f030a061d15010b250b0f01091a0a15090b0d0b010215070c0f02062116090305120f0c370b06010f02030f0c03180d030e 57
    0x352070015040303800d02e01c1c9a41c0c5a008444110000780030402102100d400704210400050048201054502c00154946084087d442c0a0144d0201d214074000b0714610103012080d04803800b6541011000742181003540003410f00117028000d200d1b0080c18402c68443c6d00300c2e590040c2c08c05480152448081c140b80c0328281c4d0802c001144040100441e203040043c500540b03c0192a9103100713081d00085c1c0105410004e4580100000454080b901c83c0c8100700c2c0d500d801c980f2070101c1941201008030000d2091001070940c0c85040704400d42c05004001202d0300000c000381e0b6902c500d0b035002600d07240320214101034403940040c1c070000b405a400222049407204c2c9582c007502501c00d178442d000e030601c07099000040c00e03c00d00060701210f210040302076078111180c00402d0710607414080c502804003805a19a6045100300500310782c140903101c8801400c0500c01c000b254004021010120b40303442002c03c01e203889130b01401107a5011300104180000c6850002c0e0083c0640b039260703d5032420710482d5800e001c4e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 326522598 1250 326521348 326521369
    0xb010314100608030901030b1813060605090708040507060c0503041a0405030712110105030c090f010e061204020907021203011e03080406020a0c0e0601020a020112020c0d02160602160302 82
    0x58441c061803001d11545080340c028840549084000307140c0755100c10000404a80c00c010805100d28031500903a000780e198620400e800c0820003490f0311000410703050880151242c0e6000ca6004031303502c010060810740c030020540c0914840c1c2c02b61190030780c0e00c0000315607000490001401d039130404c00c000c0040d15040c810b0b41522840d0030081d03c1c1450b90750740c00039003041095400003d21111080c105410450028044100f41509003815805d504001c1c22481140c002c1040c1c150051400c400315155581c0101040600800c00030012695254160415a2070300c00c2079404170300841e01c003000320ba0702c01c1c000b00c1d0070301036a007058942c1d0742540c0ca400346c40d00f0182c05207079102481e50f50750384010003c55010401000a04100c0e001032035009101d00d40300d40b42148071340c00441d20300c6100301406602da1f404182550b105409280c40c001d80e1108030074000083c89045400311051003020f214000450f000b00f90003001000940005006603a150010f0343c40c1d0400710340404440004c000d080c80146070000d01d04c2d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 326523848 1250 326522598 326522633
    0x70612050a06050d0503030a0501051009060c030210050a0b04051303080f0c0f040605041401020111030a021c09030201091406040308070c0f121d010507050601050103020f120f0f130b0103 82
    0x842d9040c3d954000c50703440c5900744416101500000300b00900b040070781c00341c42d00402040c0d8288020030031514009004205d103014080421400305683c00506100304100c904681d0041c00400540c02c00c881980001c0416100c80b5002d9070420000840c8403401c40003e91000340c054480241659804000090b071301c070014403000071000c00340b140719500c031400009000903104540311140d0751803c04851621049a5503142c0e03045a050840e03201042900b030b420b6a0b0000640040940c0303881001d15000501c480e40400c3c0c0c44500e14000840d410305905400c0324014038050854880c1c2c0914413103804c0c0e103c04d001c4501a0109003000041240240b08420383d6101a0080a01c805450b420740d651588448810f0a0040003a80441c90b004501402009030290180242401460715149581c1ca0b07440d640148201410f060340440c0719500b43d2425421169148400c0300702e550f45240c0841c0c99031002c6019990700d0350402940000030f403085810401c8010154100040e24500e03880c55944030b01008060303021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 326525098 1250 326523848 326523851
    0x60603061c0f050a0b131505060301020702030a1a060109150813080d0501030201081e0c090105040b03010f0e13020d0f0c0f0b070210020c100309080f0714010e070612050a 75
    0x41d040030030b080d84a1070880c0c521880190880f1030f01da0a100c85404009840090f808069002c01c400207a01c0014403c1505012000402e09640d43c400180c02409150006505801a074001600300100020900344400c546891241a03031901e80044a294805004400c1300c401c80c8055000158045e46006034081c812050712404100c0940d50b003001c0d80c111031070302d007032a42d1180010300466030071240641c1e10050b11388903040c1601c00429504034121f80500440da080700c0c00030b902c04183c3d1040046401601c15094000d03030b01d595940085001140e10711608411604175000b0a500e04820501186000d40080052090071580e44070810055901c030811507a104061b1000595442454910401040c400300000d4865000d401480040c26841807050115080010802099914503049005820803480d00182d1040c05182a9219104254041c9407428011600c1d80811130844040b0521080b10300003400404841e90301141c4e10f844c80d01500e0045407a0601141800c1c490b0ba00156006007004070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 326526348 1250 326525098 326525149
    0x602040f09050714030705040e060a0314100b0a03150c0e040c030c1407030206160909050c0d0e0d0f0302130f0305160608090a060c0e040f021e0306060306 68
    0x303584540039500a1101944030810404050780046401d02000b420007900c03883c42c58524001061031141d40205040c005683d0007140c8107031280304030031b0017039a030100c0c060000204010816940c0e03980c1c00c2422000c141000003c0c0303e2814a403a00300c080729030210101b4462003000313403d04060715480300e501c01000041010003210f43e40340d00a0354204111500c00103980310040c04001c098150f03545030000e00c55410413041001035400034000d40d03c03000314000500c000903012001c58008100e0361106020600701800d02420b000100020070103415851802c12000c5803190f8101d840d4641c907044031010036a8080400b41040c003d4005016003e00300141008450300e03962000080540e0303400541c1e03a580304011508450341c1d08200b94028000c00d0402426618200c0c21155890621003001000746880e82902c6003480c0c05858040d100c244011700511903c41a031882e0402900280c4000c60141d110015a0041c0c0407039504507800f690001c6c1a0380d142d60f454402b071020741c48000b005545440c0841e01e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 326527598 1250 326526348 326526359
    0x91719030e0c030d18050f060a03020307110f0105190e070b13120602040501030b0d0f020f210a0213020408030f0a05160f0b10080a0201030902040618150e011203030207060204 77
    0x40044c0340071496840c0c868008115241500c600d04040d0400c80c0204c00340903d0b88803a0340c0f0b09007500d00345030a0f860013594a03541c0c0b20007140d510401580c3c8211074410303168294050344040d00280c1c460304400e550140a90040c5540c2d005844061204010790703001214244807441e074246c01000b282c0c242000e0651030590392007420711640046030043c2c400e50341c0802c06202644c0d040c06000c0d0100c000b01c0d001c3c0404401d544072404400e05507103000744140305082c2044541d80310300480d0013803183e0300310310100788500c0c00c10015151200003e04a10420390440c0d8600c1013500e91080e2400c2e507084800540c00d00f40021003800c65640b102d03040307409014050001070201400d078041d44800c140f103424040c0300c44160703103410300d114400501450924060150305102907080040c09404550b024600450f6244150022070014402900288240c040004807515081c400340c100c0822030b290300200c1c60b200c556503d11141e40301001c0c014018401c1e4420441d4010030f1090700030780092401101d0062405640300b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 326528848 1250 326527598 326527603
    0x80c0f0711150a0503090c0301022106040b04021b0f010e070b03040c1502031c0209013203070c23030306012303100501030f2c01020d0f091719030e0c03 67
    0x3d1002c180001c200100b0428204014000003210800079002541000415403010581c042c082c010400910303004000105070342d407076810484500710702400865698100280c1c1c0e1800b9061803900340c9542c0300e00414101040360502c01c55080d4101c54010700280c600388048500b2581c0f0190094900a0030094003090080c418200d40420b14207503001140c0d40c1d00c3c40c42d00b404800350700f96845410244184000199a41c0058501e0350003503450f810f03a43c10f80c01161000366030209852014400c0f80300401002280d94010400d458020b006036401c61840600b178100100842c5070050710b076032a800501c0855000d5010307000201d150009080c2d035402c0882e11280d158402d030412a00344201450744c180400955070544285030301e02c42e001105203d03c0c0d101e01c0c0000e4050000f401800d540d070000c05062607a480003981682e030708070080001806000b002a61101c050183d8400c150790311402011003812400070903044426504143c1068616482030a40960003080125100d074604c0c083c1507556001075030203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 326530098 1250 326528848 326528857
    0x10f1716023409050106050f030702011e0b0123160312051f0b0309070b160b0a020d06051f2616021c0e060702030102070c030c06080c0f071115 63
    0x80c0580c0000c480c810b2501541031a2156000c00b207420300d8403005100c3c1540c000d00b210701041c0304445450303885c0c48408041f801030544a07268820080080070103140e52603641c000402082e0266100750b11603080860404600000b000d0004030b0450400140b6041c0614802009400c1c0c001e00780f03050008807840710402600c00884400400d9904041b02010001c01500f44801070300e00501058214070741015800d039240e0780e5000350041400301080d2112005600e4078030104255100a424005080c81111140a5005044d0b868041e5090040c04a103600b425010500c8101107007400c10124511514140caa0080c1e20b070b0f00c1c0c4585a040c00130064500c4a00c80706a0086029084c082d46040c4e260800900f40f0300190900003400c4250080541490b41c4290050491001140c1c0c5a55454440c07000a009106080004080c8034400d58000240090400d80000b00c910035210a0300c9580c82986002c010710400541c00044901813008601043c140101e80018100182c1400d00325801d00d00078054a400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 326531348 1250 326530098 326530153
    0x204051803161b1d1b041202040b030d0807031a0411030403110712141606090e0916180603200102010e120307080a022502010f171602 59
    0x749402e155003046003800001030044079600360100e401c0d080040050202824444000e602da03548004229a40981181c1e020812403102c3d10a030b0300e43e6100b01182c001c50380e210302a88200d00d0026046020308000c280f10941904d03d03610b0880d50f0792012020f030020040c011401c088d020004588110f41e44030340c400e88c03500b404200c1c4490b869251519001b46420305914040d84c5580008908002c1141981031190101e98010b28079846900140c4489e0728001403584030800f4800f0521000a001d07412203407503c1079491011168525980310881280d4030aa40c030b44801c041c004882d0100181d003092034200c61401a00710012030b859582e52141804051821600b486030061150400310039a0244503035a10020040c002c0d16202c0c0744140414201e000041410f818031001d000040c20318131076035045480562009200f000800e2400e0601d07048a814588120301240d0b11081c1032a0060048410250390a10204401002d58540e48038101c00c110240004042d0b00c15090342c84055030b10b06819141650 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 326532598 1250 326531348 326531377
    0x30e0909030f07060515030106061d012601032102030a0e030316060506040e011a0f0d0c1d0a0e120f040b040e0405011d150c040e07120506010302160204051803 70
    0xa0440c0b1346806c544003403024600c03e03890300341e0400c00140c00060300c100c40310007144c40c841c3c0c0c01e43d080c00503240c0007000400d580e001450007030f13038248041c0301340c40307041c181d030f000f6000b40340e089603980c01a0407240e0700c400030800035034024000c0c2189544126240740c191140601602d05040396040b445226411340a01103ca65884100700701c07013030401d071186502e41000000207214401c2d0764000d07100b6041c0a9001140036500d10700412100c1c2c1c4419a4070042598024803241ca5150303500515901c13008516840c1c40340c01d1100c0c01250982055008842d090302c040401f8040c40a80d81e003410115904c660102400f056040c040004c1c1d024030640500014501141609414a020b18105007103a40d40845055800404035518891100006655501650080d000340305a110712105103918010365010007000344010080001040d17000842c100b0112400e40c080c44191500001074059014094821002c0c4140c4184d800141c90950080750f00103c5505840d0800a5614030250071503000c0707860002040d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 326533848 1250 326532598 326532601
    0xa0f0b1021151a0402090a080a030309061a0105030f04050f0a0c0510050a09030b04020a0b071101180b3412020714060904020c0c0316050108060904030e0909030f070605 74
    0x140311841a5078010808104100c241c0b541e80a81031408618080c2501542c0d0101b1a000075846240320200546550012204031140515000700500301d08402198124100325030b0000040c0b0162242035440c4c8140c40e91400c40d1b880d0324274541c28410041055a0fa403047c0c44000d00d5941c0d0502854803164042c040600d41b0b0ba0910381481074010b90100c8010412108104500d003180d88210a01c003502c0d0700052803e66900c50f4000222260303881c1e0062017411000054020401520304100e000101003030b01e400c001001c422810401e02030031441040800c410400c580c01e03030001c0350f000d205941491012400b482c40c0c00d003c4c0c4d1038061440c0c140100d68805140007441609501009140d0003403202803180300e0104034ac07001091031b50066181c000d005a0700400e00e80d0006505006640c00d03904060101c8206030b41070841c098980e41c04d44980ca022a404002080e110300b0401d094900c160b815032101880030010302c0c240890003600402e0b082030343c00140400d50840b0303001c400812002c1c0c0588404a0076 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 326535098 1250 326533848 326533853
    0x1150302090a0b0a0609060206010806061f050918010302090907080d0f030905030d020c16030f03030c0e19090e0a08031501021501150807050a02150a1401030b04050c030a0f0b1021 79
    0x4050043c1c20181550b8012420002641d68103845444184c0080c0340c40c40c0d80390030ec903030203030b03410301410611039400004085000c5e01c45510310900b40c102c9001729481c0c0c0c440c2d10380303046036138541c1c06d28058000950461a055080c0500404001c85005024600050308600342c0d00c2e0607007950000700c048035405400040c5401031100030058120110801144c0703554540c81c40d40c03003070050a070303040004041c182c5031080c5040c520300811400c2c000f80307400352100b91804c0f4004400601c2c03110b24020740c0042e6160408410171403100040e071015080e4842c4c01240b4540314101d04030800300201d58468114442d03115a0848824000f180b11b008016108140300c490031000005008030340d00806590420405200188086500080b20700348400e6220400e5600d480c0c54000801810100e2140305001158400000802410341c01251151f40242c003030b212041103540406440304850300d009050b540c402451072011074502884207801c030000c0b1014008843d950303c030141000728110760084042e0100305100b0705 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 326536348 1250 326535098 326535103
    0x1a0405010e091501080c040903200115080a02060d150503030c0706031d0d0f030b041109030105070c080f0c010b040c0c17030705040b071b0305070f050301150302090a0b0a06090602 79
    0x1c01d1078a4030340038156604084459a82c1c1c1c0300b40714113034447d6858402090a150203040009003150021086640f03804072004141d019084403807100280203011000007030940d0b00440c0d083d0032242c0c003c2c034403840c0c0450030422002600707251000e9603040300300d04c4000800b0f5504000604802803104050004545851409012504a90310003580242520480000c058020034070140180302e0741403035801d018550004800804220306025003091601d409404403628000282c51080340440082c080c50759031640888013078200701401041c100c01071100300c0d208014203016181501c05000002449011240000c1c10b61b074007021418046815860540c0c140801c05030b950340e007079026500780c61443c1040391000306030f441180704103120585e003c2510000c001081e101c559041c030380c40d07900414189c0ca81c10015100c00389842003d0001a10b204c0001e010309041c01aa0301c03080070904c04411183c595000d0040450004000c0e48032030360307101e00e01030141d50b402207401d0190940da039441c90784a0600c1c0c030192 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 326537598 1250 326536348 326536363
    0x103060606050f0316021501090204031b05060f18090a060801050610050d0e070905010f05120a051b0d0204060b0306121902061c0f0506011b0309091a0405010e09 71
    0x1002c2000c100856461000000212a0411145d017502c600b0041440300803810300f020340030040d1400e8060302c000111112543c0160060300d0254126803088007569400000025080c880c01c0d1300010207005103d21041164080c0c02c4490b0701e803908201c51028a0002b80c1c60031401c0f01c58042855903000b0601c9483c809100342c5500400549940b00002d4a441c0b014003540200150b41c191540c9030710301c5c2600c01178140490401841d80d110306004c1540c55400b1401501c01c0d501840b4010300d00c102800321094000110303c0740f0b19801c5009410000300710088400c410385886402908182e032165018010b84491007010300505009c843c2c0b07a20703410b00d80204101031303e260122041c5a80464190230540b01c004440340040c0341e04a40e1295286c0060121100320008503400e104840d14114020192a02c81e40025220724400d80e50025000e01c3c91140f000c800d6007440020300040c000e49000e20403c00f130395002c140035102c40444d401c58060120300240039190240c020318051600d017018412841c80800826 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 326538848 1250 326537598 326537609
    0x1090303180309050415030203060c031807030c06080606040510080a0612020f0603060d120c0507050603071d041518050c0c0a06020f0d060e070f02030a0c0f05010b04060e01030606 79
    0x16000070158034020110410b90003402c0c4910b5441c0c403800340300040c3d00701e140c0080d0750240c166400c40c0f4216903440c0017a0030480c0c0c0380201518100030200086004100303070301646c3d0300250380d00070070341055801c49500718000d040c1601701c40c2c2000041444d540b0501c0d41c0010a0140c4e450802c81c1c07601171012402c0c1c0f0701d2980003202c1c511210380b568005a90b4084600980740f02550442d441e6a216400074021405144018003030a40d01640b000c070041e401050014014001c6c4120741c00d280e5148280310551100300d8a01c40081c2010381c0c9041c0309014046403080c4424018000b060510401c504400241c4203a40020402c00c020300400c142043c59010700e03036000302c09503059801d0081c03024840c0e8803000900e6005103d60b07400109014204060003d4491501003140c0c2040f10503100c81551a81680075144400822912610901010302c00004c070754801d0714603034074600200c4040d87e6414810b0b81001088403155290307800610541c5462141c0c0d03000340034080030100b403549507040c0b103030488401e80c000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 326540098 1250 326538848 326538881
    0xd0b0603040f060b1219230607020105010b03040f02010e0a050307140f0d051c180e1e151005071a041203050108060c25150f1401060f021204030501090303 68
    0x29405403030070100c0c140b04c1400e100351082e1119159454040300f0100e0100d1f803c3d021050507030212111a40c000b41071031240c407080d0000c11650341c0310b09114001e400201c0300140710310031000e0050019445031902900c1214082c1140342841e4035a0006814021a5081040208801540d10000340b400021000354150290745155100003981c5440e500d5101c0e00d0420300c0180d40c014202c0360310030311030070b107092a031a01e52003804c1c1010b07110307e05082d1205050b120f10390552003424191403070801401c120b50040070700781c3d06800710300c1000d001d04c00010500088003060050910151001c20b0032030581c010443c00846030408945058603049241005c1e001c40202090700d0300d0010710040000184a9400404880717800d80c5910b40007a000542c07070b4500744c60782c0103050460416800c000c104810111500513018080c0004040003114000b101d60501662041c4411400104803550141c0c25943c40b0502c01d01c1914400001c40540072055400340e80102d840e07030b54406110703041c151715104003484090410349 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 326541348 1250 326540098 326540119
    0x12020d0503060a0905190f02071205190e0d050102040815010807060203121003061a0a090903200c030a080904061a030411010e0414040b0f010305120d0b0603040f060b 73
    0x1180003011140503000c0810f0381d034804900103441c0c106c20440f4a0001050a004100003001c903d00690006d0300c0c11030b000c50080c00b42104950007101603e00e8400441c5005001c904094421107419201076a00c54011820b203c404020900030300051015140e814010700c0d4500f070900480060220592100269421400c03090000307641c04011142503440c0004e40070702a842d19401000e0325102c40c0c2c001407600d8030780ba89150068980320000c07550381200329074403206260b40d6800b800c00c1d660302d108000c00151114004c2080390503613044078050301c60644211115141028042840c5c1f50900d04291413200d030104148105142c41d016034000740242076241c01402c00b80510400c0a0301001d0b0009110980070340c103030001648500318180844200801c00c0c040e01c0741021038100d21540546090355206014400503484820401e261412258000004c1c0703602080959000190b4101e025007050b2140c170b50f580b01940d0354400d40554096406217a001c8500306c4e040c54000121030804015a000703481ea0031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 326542598 1250 326541348 326541361
    0x7150201181b0b1902060a0b0d020105030406061a0309010c05071106030414030414041415120f030a080a0e06040803160e0a060315081b060702010e03010912020d0503 73
    0x42407040c403a44006660781c14280c82c0855000208540c0120700559400b10325042d400b5840080c034044d12800e030b0243e0717410362143d02c8942c00365882c00c003030340350046a400e00301c03c010352003800150350003802800d0000e102a120070650705119140e04900304240320100501030139203800e04c500c190791840360603c10b10f416000c1d034500001600c03481d43c1a10600010002a0500404603c08242410000e003501d0b078031a01c070b910f1380b0158400001814016407a1003480616070f040380d03200380e00483d0360380d820155641007031007004201d15408503040c005015078548103e0343c940410140020344119200d0032038500c1c04c0040e00c1c0c220389034112200d00c40d030320480c1800041821101142d0704502207211040d80541d12a1060b01d52002003c200c0781c109444100004d020780d4194007508104815203804004513560700503c59646c0590b60569006a074880100003091502034014164184181048240a04140002421200021406d5569113400700290744800c0d818448540c114445060030341c00c5083c40ca = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 326543848 1250 326542598 326542631
    0x1803050705070e131113050f10050a0b0d090309030605090a03030f09030c0303020f07050f03120c040819060e0d09081006030302100902041803090f050a14090a06051207150201 77
    0x2540a881c8609402c17071031500d501c1700340c80d041e01c0140c400c86c103121500b0049943c010b00e07141254400300d40503c201e07002ca140d1400602c0d00d070480c0e118258885c20700316542403400c0200b043c610210b0901019480000000c0e0007805010300c2484c5036005000c280c1502d081c098140c0f6000c605003031945282000c0200001e0708102d0b040051500b501e80141c41d07210020b19003600d481400c1c009030840c402d012050301d241500100400c0607040030300c0099602d032a0071501c0c40080c0110301a0380d2040d00a4900c200944002e4010005098001c00001c6000c058401c060ad040005420325800043d10b60321042c07100d00d90410542d4040700c0401800c008851464400a48816910a02d20000c0c0e4030b8030580401d40d036a41d0000401001142c00c85419151140b8024180c0c014612409910641e114400505450020280401c80d030100306805010a06842088030f0740d5401048685a1980c840c8081103035100c125aa6507840e502e0b4000342035a50a00e41303060760085a02d5002c00031a030600e504071640720f014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 326545098 1250 326543848 326543881
    0x1050612070822050714010801080a0807210816180905091c0503070908010519200d09050606060307300203070504051c05030316031803050705070e 65
    0x600d829075407900c0303400d04101100c3c00324111400000404282109020001c1507007011a070241d031009105000030742c015508040244980c41503600f0101e92400032812002c01040c8007172044190381d503081c42c0101e41344080c11085040b100010300031030030081c240c6589106500301d0300c842e050070000c0c0703409000c20360680b11281c0560249c503034031580840c502d1841084000321a40c0b1814940c0d40c00c020050b00101b054204940520000e481404000358003201071242c035026400e46080041201050040c000107008a2900e05802c0424010000d80c40070b515409000c0c07804049502080c255010b040451074048080c048500c200d1081040c003034120740090002000d409084003500c5420092202c03020903140030344c915581c030b038000002c010b6100e03404070042050f10401c6800307162011016140c0120302422440050181e48101301284142d11441c0200c400000a441d0125641d944459243d10000c1403000480202c0c0002c030311101042803c0c8039602c05084854211364551400b41d41003205902d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 326546348 1250 326545098 326545111
    0x2105011a0f0409060603090b0f09060c0c0c0a030c081509071505070c091b0201020c0d030506040e1617160603110f03041407050303090f040e1e010204050901050612 72
    0x10750801203552103410b407030091110b40e0042101a50314035000d0090400303400201c0b203003084200069120795220103a2401044564010a0151345901800c00b182e800030f002d04190307105501c1d50101642d0f9481c00c4002031403050710542ca0031440c100075107140125585840000529071020407200841c00a048401c031018104403a0034010f903604162442c1c400d0400140c20310109400114404a40760001d802040c10320321810464910003038100c5c01c078080c030f000c41da02682004140b0039806219070480c0d030308814000d10029881100364440c520b81107015400e02d00c0503c0d142000c01c20f250800c5280c403000a41e000181c2107080036a1030b030700c00d9212640966402c0c1a980c104013400f401506d002d6801c00d106681c035182d6681880d00707020080303040c6000141018410084041064140407060b01c90110002d401107103e001203004020141c40c403002668143d11a041000c9510a8010b04c07010951300d040c000143d499080c10b081c4842c24205030092805180100b00b004800104042d040b944041c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 326547598 1250 326546348 326546399
    0x13020702090609061207080a1b0605030402040b040e010e061008010b0102070e041106030403110c03010b011d04020c01090b011e030201050304260c01151a0a080a0e010507210501 78
    0x2695540042e03c1725a00c1c240101152084a0010410502c00a85031200c9030042c0b981c03408494403400c69003200c42c80c0340105000510300f80081001810310740c1103e010018020004a41e800101a6141c210b44103014201d00c594044802e0065400c0a00a42406003125100034400040f08000207075885506100301c0002c0681d040000d024421358000b5400606e100a1000d0307901c0c01c00d4100240184803601c180315060082c03600f001e80f980740c1440360380b0135130106131180c0b5840408440000c00d00c540440b0100e4009401308010702c1102c07400e10444044502c508440c1c161035040030107100341071a22984c0c02265096006081c00940e8110741900d0344141c0c00128410484845019410403a1003c0300a11090078003140ea84200300e81900501c606c8030000542403000c030794486203130700004d001c00810345080e03401b040766101141c4140041944102c042ca0003240b81141c4078880c1e801c681041700d140001032407084401c1b840c41d090320000c0f054140b150b401400203504010003000e610900c0b059454246 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 326548848 1250 326547598 326547601
    0x1d060714010b1f1205091b0f09010303050c0d0503090615190306050901150302060a050901140c070e01060206150108060a0801110408190b0103030804020a0e1513020702090609 77
    0x182401d40046107019000b0b412200802d04080303103900030002c0400780401180130f442c44030010140500c0b0360752080c03c4c0ca80080c030380c1d011084c12445080b401005843c1d045003090000c02e2054903540a010f00071031003a5917003079407140641401d5003008185030340001003040400c103001c00c1c14000918280c0014100e59141081c8502c840021004031041c0d0002c00380e14004a000018440b55a000910500d41d400c002d04c40300c0c40034105a0306040a07404003d60100091101103410385c421009084200810305004c105a450081d032248690001e50441d252680804804d1144d0100d5071050307401040a800144041e0400f40b400310000200e005010b41001031120008699640d07452a050003000148002c02c001e40c0001c5d4184003e82c401e0140f41d6491243e0010310030b020f58412808142c2c035400040c0c10351680d0030365500b1101d910028000703907070002c030030400032604c84d0001707048600036110340c0000404660000c1c14080042140d50902c0c0505105100900140e2251340709546d0108080310014690f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 326550098 1250 326548848 326548883
    0x506010302130609090f12090513020f0c0f0c0f0103020a0c0f03021e0106030c0503030c030a050a1e05030403090b04050607020d0519030c331d010e0d1d0607 69
    0xa01040c0d001683e01403c2034800001d202101024428445c02a0200d41c8038007d0744c00f00780c524181e140b0900d070304003103444000c6481c560594050000c002821107120f140820b0510040d15065408882c041b03503410072040c08681c0d14000c500c0291001080c00e09504003001c2d181d000d000c286482c1da014112460291b140410144244100054000c169086850308005894250f00034245030000301c50070320105402041c02d16000089c1e903008425000154503006000108a5140c0c000c6101c240900c060224800c3e00903641c00400310050440d036803100c0e22403505003001011441c4507880340007240d0003000280100c0d02c5080c216000a50180c40041c490030491400603d0410490341900b2099601c0c0005010542c2c04000c00c4003a502a542c1901041e050b100c041c0c107140c407044242030076080710b0141d07007501050680282c03021008002d588800d259018001c1802c2d40c2c044045410141c101c0c00d0074450854202640360790415200c1159400c000021010444034440e40c40d001d17240c41c1550180009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 326551348 1250 326550098 326550101
    0x60c183c031502040509010f050303030601051b060109020d0b09060105041520010b0111120d090821071211160c090e0304091a011e0c08040f03140604050601030213 72
    0x25a805100e0342c01e062100762104000b900503000e40c0c0d1283c0360100001504840d6070120703e06407200200514a16101c503c0190360540c426a090242005440415216118140140341c02403103c0503016a650b40d000a10b07000b01c8020080c000d1052103124144105668850180c60a44540000c29400c4920000050307032045048804080315258420f0120354509040d001500924170a80307641c804035140417021074440c04c4002c00020407100030300c10f00c00701c00070b00e03003203059460300840d0303403918048406400e4000088955406e2403c100142c0602c2901a44014840180d500b450010060080711040d94581449810854500c00c4035640d110003c1c07080c0c11a08500600d07030040c040100143d000d542070348070340162140f4209a458003400c0340a040654002c8004a00c1c169501503490101d51403d07001e8500d00c500c40b400b04982114140b00042d880d200400203042750b1a5041041440d605e010200004540228401c0e6005002800000350000941906603981143c500700c0b102e0302c0024840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 326552598 1250 326551348 326551469
    0x607110c03011d160b070803280b01021905030f1327110c10051b0a2001091505090307080403060c110c0a170a060c18 52
    0x107a255181c030400000d82d48003002015008501e841c240c60104100401d002e401d400c0c948568140d1200030401c0030000b40d440401076074800304080071a440300100c105c1c01222101c2c05400c01c40c131680d0701c001401d015030301080b41a014070b00080d48440085029a1000c0d100c0c016650040c90705800400d04502c2d0002c645800c41c0541008401c1c0300c0412040000d2400c000300d143c02c401c50303151603c800111a0400300302200e40850703603030006002c0380399204c1c1080018403004040c4004a583c0d0400c04909100000c01400340b24106d6842c0a02c40c260220107059000900c0b1900119a160403c1b0400042da240c0000003414980b40d070010f402e0340c441850700d04501c501035008144c140e00007804000c0188940c0480c808403e01c0e41d03500b0b02c0301d0010200d01e94946600000c150f100510400801c40d01100c200300480c1d181440c02562500390f0982c1c0c0342007c0d5910071010703c020903407030450441242800c054420041c125007010b40302d8000d203a0800708461310020f49035080c04561b1030100305c11031410036111 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 326553848 1250 326552598 326552623
    0x7051b010e0d0801030b0702030a0c03081911041703072d05010603061d210d111303033b0103020c1c02070803030103172503032c060711 60
    0x465410380e00102c001c19004007400304641c00341540012604041c4000700396408101207803070b102d032840350390348050360340100007018a81c042290018030308450206014441128400d01182ca88a44c202210300c0f1164a42c101040850750003401554041401c07071419440c02644a076500004404032203116805960070440603019600b024030000070045254000c522021140300001c510702d6049001c181c540800e503ca446400740380c1a4261804900c0c00020442000c040c00006144402220000035a4001c040e08d0f414500303031a2010070616400405d100c000018001c80c04840d030880003030342c0703d10210407891040c5a00c4850280b0407070764001c1e4101d40c0107460990841c0c0c4810182c03070704d01c100a03605241c04401405082000030340d401001003524141c960040b2003d07401c10740c02402042d03a420050b19240ca6030010304450595a40309440c0d400110300a40d8003060285014180c02940104040d0495401410301020002c8403008203000360803083d01c0c5001c1d03d20002c04035a10307203040940c8496 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 326555098 1250 326553848 326553853
    0xe07080f0d2c120a0302070e010b091f0302090411030a05071e050d0b090a1b020111040b03040606150302090a050d0b1602010f0c02030318030a020604080d11030f0a05090607051b010e 80
    0xd240174140c0002d9a1012107030301c3e0500070755036030305c82c2c04000c182d0141004040d000000004900840e044031042e08070191114900181490900d1300007600f40c4d010082c000e03040010010503c031031002c0c20301031103a010b17074a42000f010582c0ca11440c41c244400c1c5a0f005000c010001c1244840c2d40b003660896815044000c1c0106190308008a1590003040b03284110b41c070074120514110070803401030044400d00d6100390790450a00d0710302482e45802c0d41c0000c00460301c1941d25180401c1c01204592600c0c030041d915a1b00607181e00441040c0710400b50306402c00362244442001b140700081c00e690b55168404900b00c0030503c0304000300801d0307000d003290606c0b10000500300090004500c1e4004003070362044102004d0000d480012480007602c074800c101c10319005821480000b4082105800104a85040d0340c0c0005000b0380413800ea0000754009a400340001d400ca003040c84804949030003996000040d14000d84441c1c20040c01c0034025101e4155044103144000c0c24203026001c0a40c891001148104117 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 326556348 1250 326555098 326555113
    0x5090f040f020c0601080c03070603110c0a0302161d0402011209290a0606090b07050709060b0406020c010207180b040207021503090f070e0406050a0e07080f0d2c12 72
    0x1c0032019412a10b101c04551007800d0000482400029010b0403000c80500540203280c10024110040c1080e0032940007207420400c0810f000c01c1c810480c00b210240682d000e862252481440072080c45e041d940107020360b94020808003180d59280702c00f5608154242442d80c0c40c2c0c4080400c500c01340c1440500a4402d4101150f4045840c400c42d10400040c1980c040e500d000d0741d0b0381103001085905500034800080c00c0000188002400e050040103654065401c80d546140c0e1124900159442c0e9003000c00ca903000818100540c54042001c0860700e54240050b061890a10100554281d500e01c0c0e00b19890ba16011844095241c1d941111029500941881401e402451038407690794400e40e00003d02d44910603a1000030300001c250301c41aa10040040c41d4151a140c55000203008003520644140c0d0b600c800e6440d00c03080c108201401081070002030210030550030042c6013403032101c40c0c02d0b90600c03e240015207400c081c114088402c850a07011003076448130301000481c8480070f00041c0b00542d481851b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 326557598 1250 326556348 326556371
    0x601110115140105120408091201020c160e090622020402120417070f060c030e01090f0201030608010b0105030112030507200a140d03030914070f080c0904020102030a05090f04 77
    0x50384541540c5032042d0b6180da180303160b00111207611038020004210f84038071001c0340003d05000d00500d15200000d0a0340400201c03440c184d82241d01c14210304010794006044900c0078828000c0c041c0c000d00f05100c01c14020301d0100705242e01c441c002084c044a00c090301401080741c01c402d0500032806074000d08210340728246900020f0800c4802c0c0d809a4a0b00400d010440b49801004100c0b01c1959100e501c4122030100303503560310058030a075800c2800717160725441d0312118018240305008803180691651080c0c04123900024007195202d40041e00c0c0e0303034107000b00894243d81200450b411205040303800312146074582422140c030700034030a0082c82d510b20710400503a140d0558595035140c4204844000b449640c035244885000751011710b2617000400b038140c4202083c000e0b40018942805014a0603483ea00c00c5036084c20302c0416001a600c2c0141031006018a2400300b09042400d607041d21010540d08003500040d40d82c0c0613166510040000021b015041601d411141f00e001103409001800151030f4807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 326558848 1250 326557598 326557631
    0x1a0922050124120605070e0907030b09071805010503130b070f0210090210120f020a03020703080603120301050d080904180510090c150c020607030e150702100806011101 74
    0x40d6200c0200114464072420ba000300b07003060310448075070702d0740d40c01103507030654038034014160007014003041c801842d0889540f40c442c10880c0d88144c0b5150740002e952950241040390808004c2c261508125411424007003044000c100b039403e87e175090801c151213aa07041c0d101420507420210051000c80104c0a0002c450f82000c50002400016000d803410926401082000c8802c0c540f00650700406501003922031030302130100400707000d4032100d0102d02c0314180b000c42c1042e64032039100240003960014452040c90791002d90550071407000c5028080315290b00344411030900060003010300c03404903040e200041000f004111070700b08001800911880794602d15001144036000c8050b292401600c8410140180e00d125800744181d00c000202079843c2400d00101c100c10304c13107030964240610450101d000d80e4034440600001803080c0d03200402c1c80e100d5400d01070a40c0441103c1c17882407005010780b138016920071141da102032440745012142503030f900004913920400c55260407619440c11703030300d012400c218 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 326560098 1250 326558848 326558861
    0x3010903080f01290306130606050406090e0f0406020f0d05010f0504052818050a110301060501090b09040902011e0c110a0303090306090c030c1410031a09220501 71
    0x100c4244035613907500d49030145501a2003400c0240b00481401c0750b9285120b030080c580055014001c409054688040324040302c4c0369821501c04100e01003010032081c0d034002c0424002d416020a200b5003400e00d111030320348194001d4001045190003061569540310b5090607501600c01c0140d042c4182e5941e82414102d0b0900ca004907402507081c0400900016154681d0007018083c42440d0b1846401c07a4103004000d00c2541c800381022110ba03003004000c107004002d592501c502a00b503109004039050105402c499041c0d00c6903049c011000360401c0f00010f12810b44094080c2928003280041062004075101542000d640a80c00203c034042d40b042caa00103001c1c003065102e041800e0841c0001c40130070020400078400100000c0c01d44105200191054010310f01d40c42c446cae118140050b44968541c00001201d800c13100d0b03a2038451011200d02d14001c1c01c0c0c0300407114142010800e091b414040241074013030700103101d80518003920100b00c0210018400201c034242003544076031500c0c00340c504240039007070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 326561348 1250 326560098 326560111
    0xb3405041406040e0f0a0617070f1409040f080d0203011203020d08090c0d14010915050105010c0c0b0a0c0204020a0c0201081509040b070e06070c050306130503041a090301090308 78
    0x11014070360310141040c00c111000d03500b14400d80c0304540e484100d01e2503824030050160040603100d000c00501d04400086480001c80b035840506600782c02d101442c1c000c2001c90b8413805002d0703000c003400c402d07a40300c10350300795000ba81105c0301400b14041c6041401140c45031080c0e030f601481c80000001000c0c00e860340e504904074866400d0b220030200141c0101c0d1044400c4ea54464150010075000000b440c00c0c58030f88039414850f05079030090708880361116003121030114060782d1724012045480e0038091144121f41c00f47c0002d0070580d0213903a66031503114516900c2d01801343e080600180c0303030504500955030b40c81030a9004109564031a50118000c1040401032022808120014040344464280c0c85440507030b04000f0700002c03800d07500c1d40c946142a44c0d01030f0000040c03001c02c00d21a506074032400024040c0d0340c080c1205070962440c0505051401c407005100c244451034003403026002460100841d4211a084061848070701002c0b05c1c01a40d51041d0100260700d507203407001d00c800305030300a00f81c14416039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 326562598 1250 326561348 326561369
    0x506030f0a0b0d020907050a0228050d0201140604020a0c1718040501031e02010c0b07080f0a02031303050315060304050109051c050d201308010c05070b340504 70
    0x50301c0c00b06000340c043c18418000c0d03001200000280f0a14405c10151034011410702c100e80d903140c1c102120100b00e034006039107d60401c801003115000e02a04100420005156100801040000d40c103200b444030340150080e0f200f035800103413130074495100350744000100f508035070010160344c050905003080303038000b0030646a0201e250404a0781d5140600c5824100c82c1c109944801d0300040289060105580c11401ca06010524002001080d40416414403c40103034444035100c2c10610041000510002c011482e114010030420091090710401041c04652508266840f6110054041d03d00f85018400c107420001c04010002407000540007240024010b006507200c0845964400780e04400028a50300440c40410105400a0720341e8000009400c1c02d0b5048a1240380010810700264031160f104812128807107000c0c0715012003032140002103a000e041c10b514041c0700c7d0380c0da41c081c5c5000074801103c0802c50040120000400628030302e48440740c0c3c01c1143c0e81d1407120800342140c2c20a004986800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 326563848 1250 326562598 326562611
    0xc100903030e0a02130203090a080415080109060b0d0903030e0d0c020405100501080c0304030c0f06020702031b1e040204030c0602030403060c0311090d030c02030712140102130501050706060506030f0a 88
    0x1200110b48141484d801404854058070b07881611030180d80050300c0c1601c1445030141150100e9076110103400600113a0800805000b03103d0300042c41c2d1001a007000401501e018002c010349038406007190f0041c010444041020380282c00c0a40081130003a400f940580a480038610741d040d400607080d801c03d482100e0070041078640910740c5804030f03030714080c460100e64420301107803d0100c0745014551281c40791801905643d09030b41c0c3c2d01003d0032103e1040794065000b08180701140380a20500d0304551079a02e4403601c070300b99100000c2c011145405182d440601030300103201c003a1103a804490280d500455000380706555403070001e560b68014801136030b01038036194146010905c039002c0d83c1d0b00e6079a42c4550b00c5c05c09041c0410401e595008500031028490180b0482d001610305104d42d50041c800c010820840343c0f43c50500d20710f050744200f40405980d104121035820b034190850b4680644a003807a00320745034409403401a0061546401442c0d00c51742c08010028600c030900d0b032103441484c42c0181030185 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 326565098 1250 326563848 326563871
    0xb0120030d0f020414010c0606081209040c020a020913060902030f0610060302070c14010c02041419050402060a0c0503040b030f0a2f130918050f160b0f0c10090303 72
    0x4a0184d401116803083c294034180f2201e611521a40f40300c1409642c0006003595151801464406802c14801c0c1000001c40d00c03400a252520030580046074070b0010b041c554003140c0c0024141000100340380a014498551b400511605500560f12180d010701119013a44d01190501d60f242011603003400703e100c1074100802d03103500c28020358002c5540800000015801d18451620314201c0301c07841810003050082841c09655a8000c801e151415030f00e1188031424450a1b0516003c102444c1a6425051405110050729404122504482a40f81c400900a82440c0c25411845154400b04038100701009115445154440d10360003805140e0040004200600c0d451007041c80c0d08081c850050865095220040c03284e80041003a001220064407241c0d4403503d40c1c038102e840c154141c458410a081000341000350070440e00c444096910020481c03a01c3c42289850101110b0080e0b50507040e0204150000003610800c5d40c07c01c1c0d030303c48103481c00e494060712024010040707040c4c1a80004c0c186006240c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 326566348 1250 326565098 326565101
    0x10806061c05152518050301020a1403070512250e0d0303050a0f020a020c0301050c0306030601090e0309040606020d02160807060c170c061e010e0a0b0120030d0f 71
    0x1d031181e000014200000b000b500e903100b40c42c0d0007480c14182c90001d080c42685112504080303900c07102a134880e0410401c002140d4200042030f600560b0080c0e00c1004105441a000303017011100c2c82c7e018000d142c1d29a10303078004a40701d0140c000d000540b4980b002c10322503052210004249051288003000c094145400d6045851808040c51981c0011001030410080392181d00a1907119901610210340038604100c15001c0b41c0c0040300c1403005811000c030100403840d00380102504031042c1032006080d42014400240c90f2241032265440d142e50300c4500d0300c03080e5424010348081410040c42002075a40d1440042d440b60b010492440040c0540a0540e0715860390810240c291032040380104115070621b02c6c29581649021030940d0340440c854000d1040d058078a000b0500210814058446420204104132902010285180202d0720000052100c030320340000856028040b01c0010a0030608500140c809600230140d122102c08400304140c00e0520000040517414651441004141c442680701d10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 326567598 1250 326566348 326566399
    0xa02060324031f09050715021513020f0108040f0f081801080c0a0c08120c0c060c09030c01030902011107030b15030714060a1809050103020a0e10050910030b01080606 73
    0x7140002043c0702250092180d100075011441001211002c07a1691042048210103840d441b0061703000c0c1c004581210401c65030a9000502014110180d54150303002900c0d00001a403194100071508000a05200c0b400018845980c0c20941c4c00521601600b415071259002c98005103420fa0a03c15010281d44a000b10cd8445e40c1c0c00c003180780c00e000c4000c40403225840d0114082e11400024810700c442c050745482c405001300e0500c601c0320b03910b8518506480c00c00100824200701000305200c4500b05803404a42d030b1118480c00d180000302080d031031005941c1d41c0380d0014030305443c3c4107044012003002581080c1502603400151441c2150b0542c1d41015a0f8600302c0c0200c00c03605602c02c51451950400c2e1014145580329400d0000d2024095681190004030766441110401c0d240c200400c10760400d514060054034141554960138901030840c0710024825200e014040c1c004200080c0d10040000a000701071a4041484041560b48000c056500c1301d0948916128804101e0712000c03101035180e40c0c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 326568848 1250 326567598 326567623
    0xf080705090f090a09050f031908010608010911160f021309050a1101050c030d0b152a1c02030301030b010504020a020607080a020706090510112a0a0206032403 70
    0x100b120440c1d40b06010180502038154010140c5030b0030741c0000200c06200000f05180d10310700554440184d00f03258042d10315403082002c180a0703a00014881540d025100b181907c0d6200f101040d440e11515014100344900440d803c551612010800c0030491100034507070640d8001c8074a8588400381d00d140100302c0703a0b10031000b41590f1000e035070340c0005186800310394103100050411500340480040ca46096034030185054910302e946000400c0c0c1440e0508503803445020740c0103803906129191080802c0740d50300200800400c0c000000350714032150100f1090702651442d00021f41d1081c1e44030350182d5203400038001110300000d960000309060a0a1007544c402c0c00d4203a0040141e030311200c0080c1c50a040c003512201c001c0744c00300181d402050084c001e04514034071400c0105503140105618000712000c03070041550031002004000705454002c135025103060300c05900500721417a1207181d03515020100b100290802d0021041200c3d00c4024000f903502000026405006402030804050f100c50824468 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 326570098 1250 326568848 326568859
    0x105010f061b020d0c0b07120206061008060a090c0e01030516021f09060212270c06210f06150313030818060901021c0608070501080405070b0a0f08070509 68
    0x40360807282010740c850b840d0b00141004045444c079494500b1301d4a0035411160300081c0010f1a141007150059070340b00520b606102078002400c0c24400204683c1c4407101d68010801d29001103000e40e50342d028410014101060208030503800144040c180135180c402c414042894603000582440d5150f02d1003000d200950301600740a82d40d40c01c000b00404140c100c011665964104480000d24144001d088420b03400101144ca49400e01000c03c5440c1460070302d07d10708013800588041050700080044110200f1109961a00c1d12045020550f4030361500c95000081140c080c40700c20104040018011a03090351203a1b03ca041d000c000307418610003601c0360300360291440a5100440d2142101c01e80007220100017112044443c00d032030385004004e03181900540d50000703100101c10302d048a41a01c140c081d5609004452600307502a1b101c42862080318103000e440e10000b400c00005000b00f4025000a03440140c0780d40b03106070300030300c92203c82c0e801501007844000421022030240003a1144800d00034035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 326571348 1250 326570098 326570117
    0x8030405101404030c091517060109020f070813081e030901120b06030f07031a010203040b220e010303030c080f070f0e030d05030a0f1e09050a02120f0105010f06 71
    0x70444598000c0d04012288500c180404000900c0c5c00c0400402803034000070104403185180b0002503c8080e96010160500f01a20070405200c2c001c290302e411a00e14040040c0c8444124092000a20800030002c02c0528005129604032580780c0700da80540700200101e0b0700007035000006058045210516104990040c400c0e405190b1048240c2070a59800e1400804c1c2c2001c2d120224079190025181d1b001e5100c243c004205c0725607454424615081105040c1420b220113510010352a889140503010002100040c20840950f1180090429505c1c407544c8224055440848601e031107402e02046000900308210b1280d001d00c130700c41150007600501107400700c54a030a807081d203070300070b11220030b1061100b002199500c6607001e10100602d040e50781c45075613403880c1001a03201261491149050128079002c964107104016500032207941c4081d21000034000c0090070590b14000302000000c0d40301c0c001c52005010000c0110700e2000815465009100703590b00c0d5000c44030b80c2030300b6004482c00200c0e0b811 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 326572598 1250 326571348 326571379
    0xf0501080a0308130f0602180f101202220303081b12060d05010e1c1b12120b03010203010b19090b0a051809012702090a1a09030a0b06030708030405 65
    0x4e000c6010148241004808010641d8920302030360000c0100e48440090b09001c030040e8208a0440500da0404645400c2016080c0d04040c00d00c812181a03241c03079030b034041030301c2d00442e43c2c50b4240042c014425441e698080d03600e16000b41040411100014800e1b101e1490b2440418082c060b145110044500945c1c656600303c01e200004c8bd2141080e5210b40d03d41405006041041c030012200c1c042c0d052002c0b400664122003d0184180c409143c0188904110482c010426403884c661110085242030360b61030282001100c0901006000164154400000058800302000050101d03c0d416540b208114140504c1518408464030a21400f100204814009144030304002c0c800c25400752003030042d40d0905000304100d407101740c1100c0c004540380101d000d8441f501c0385a040c44041801d00035441c00ca001c60124500c80002d00ca5007040d00031000322040b01d16241001d440201c9401b400329058400f4505100e445000241c0c0d040e4045d00441d803002c24001c0d4080100c3e0240da1000d40800303400b01c61031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 326573848 1250 326572598 326572621
    0xd030302030702011e271703040212070f1418010614070b090c01110714101101021206130b0102060f100b07030809010f060302130506010201020405060c010f0501080a0308 75
    0x50a6100b113543c4d46280c803c1081c40d225440c00740d01d260040026a01150801110340d0300c8030008102d02180011041c0306c0001c800c0a101c11000d00c114400c00d4990321284040340101c85a2001c41199018484022400c0f00039403a80100f21040c0e000c500100e08100d005004d180c400c00d070406061401e043c00140600d42c00f0314041d203035041d0403802803481d00c5401d8a030301c907440e041540ca080342a00714a5518515607071241401c40780384052000741507035a10f418244107000400500700740c040c1b1103010030001c8003070240c0750b001400301c00b0720002e40d550001c80c002c024940301e0844000b8410b2500504903051855148a0400c1e4100184c000b00004d880360003c02c00c1d07800e030040c990800d0b5501c422005c40e043c480503024042d0a842a120f10100d401d10130704060031340d00008444030880349080c9040015944107881980345000200000606880e0310b00100e02a00c0b854215030303000000002d182d460442d055100c42503c0812000800184c0d03200e2980d81c0c1c45000300300300070340050071301030200e003020041c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 326575098 1250 326573848 326573851
    0x615060304061a060f0d150509011205102c0601080d03020c0102280e1504030f05070503121215010e090702010f051006080612060114150c0102030912090d03030203 72
    0x84450302c800c42074082001850035408201c0c17211203640c0c08104698440c080e0301403402c041c1030740c01040c426642040d0200e1074a080511468441e50132820124060140074818940364600c1d0503414019502c07000584030140d90203c100444c015080950064440008140e0758140c4040c580030b49a481b258078000c40180d00400f01c1591155030801844d5070803200401d03100d90140c0b800c0244001032072074480c00f50101c803980700054048d00540b5820a038071444081102c064a0b0303c032202403444070050610350314003492900a13580521800c0032000d40c3c21403d2001e001d8000340c1d00c50070f02c400c1c0d0305c0303c40e400c0400500f1078000303000c00e00e8080c0884030742ca800f91285900c0b480c10b1000050b07001122a0700800c4c2d48085e40d10712000e55504000380001d5078002c42c400e601503c00d07124401203078000c00307442d9907a40c014402d4545020186d11410002c0e40c40001140c50104951030640d2241d8030500564000c5d4404e0f288211988208a404030ac2c0b2400002502c60300d42004061008007001628140d019510 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 326576348 1250 326575098 326575121
    0x80403120b0604120b0f10050307030f050f0a030203091314062103030a06320603101e0602010b0a060509040b0a0504050a0c0f0318020f0102070506040b0a02061506030406 75
    0x1804049a44044c0c0081c3c0c075059405009614104d0910061002c90240701506042401d03c92420503c811b440014207201180da00c504500b50710001d0341451400c00e440b10b10b03190a40d00a000c488414141d00101800c100b0744c044401460304188106410100c900000401d04042c1701400010501d10300b126a030301d410f0611000200240400e0507080303007558801c032001441c544d81e80000f8071240d07806040e04200460a082803210b80304000403542200240291020302c582e4001002840c1a0505402140101319000e810340030342091703401c00e2041106a0003400d0066181c4144218146050316100c4102d8000d82c4400d440d101e914801c1c0400741c19060495038000481740d900003019100d40c49050322522030403c000a0020022800810901e050803c0302d08260401d1240c0c41414444031040707104a5041b03e8084000e0300381342c0140d0030801d50b903000541c0320801280001d40142058000d100b003008a600740d03000d607510300a02c800d00c44200c1d031005e03400042c2400000c000601d1035104070f0f03d046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 326577598 1250 326576348 326576359
    0x51c0302070b0a110d030e15040b0a051503011a03010c0206070504091512080d29040b0319050d2703080901021c0203040618210807050d0c020907080403120b 69
    0x1504d4528840c60861024a2540026910a0000100d007805c0c044500d0409001c9540c00050506803030f13801c050300014204440e00759484010414031a51202d0b24040004050000e01c040200c4241088bc0800c003c0550750107942040082c842c5a880444c0341d500c18074654550505081c00c00906a00424482100c0800c8594806000c100c0c09440b043e494189442112107540da01a4418800255000b16003440640da00b0780d000b0000c01168040415031150058500041101040b00024502884c030b00d062030b80401540c43c02c0c02400008501c4684101d020385940d03841e01c0c1013036924001242c050a4a540000f1524000d0002512040081001d800705204985280380c103211144948042000c1c12405a4800201001195080403204a402d1783c52170610307a4440c42d0050b2651001c1000301141000200490004c040043d031505035043c16070044210303404020081d20141c60708000c003100380d1040c90158002400c6500c140c4440303204540c140e83e485100307a5460b410902401c00c2d48003199110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 326578848 1250 326577598 326577617
    0x1051515071e2603010303030f1407030c030605060d050105090702061e040525090e120f0313082b0203070c03140c010f020409050702160e0612010504030207051c0302070b0a 76
    0x3d54031003108048400c960030641e0b580d525615000c0c080b00e0280664509079420007120b1043c0185d000324003035001c00a81408143c20400715001c800400c003980040c0e034040c101003030051544141c1c4d400681614400e071548600313611801e100340da4402007211000054455032200800250060007682c0d0841e01c91012225200700a4100351009070850100402004011a041044003001e01906480400807000b030400c0c24113800d94000144202130810041c0a0000f001c10440f0b00d8803003068056541241e002d5488c2e0711011907030500c002c003150070310115409410840003004018421a03002d04100c0c0c80c2d121200c03059070703001d880070407103a0400101c20505004040b03048600380100c00011a51070b0b40180d450382000506802c41d000034045004540c030020400c0b10420480101d2000d5801e4820704165650b18038002642c2d280040e9070f208100e5091000788010141c0000d402819a8007c40b41c9000c4100800110281004656000b0300107034401d042c1040380d07002c0c200c001c0c0000040e518203141300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 326580098 1250 326578848 326578883
    0xb04050f060f0a020a0c170a021e0a0603020a0f090506091002120705010207120e090a05060a03020a060503090d03050c0f0705030d05090a0b01080303010b0a030e010b0301051515071e 80
    0x42da0840b400010150700700c0c1549504003c0c1103a04070300580a90301420111807040c0840726903400041000034000c0b044094004810342000181c10070031040146403140c1640c45410041c00307500700c0340d400c030046001c4114020201c0d004510700d0084e66406400706007404010340802140300d5400e880c030010740c014010f181c0341020b05d804c02445914025000566a001c940ca0003540d0790503002d80b1401000014880e440341c40d07580c031401a0308500c04030404107141d00d41c0380014101c00c0c0107900080d401040c003c0001803268100c40914450036884045e603440d4803244d24180d041c2d03041212996100d030820807001008058100c098003019015408a80c207001f1400b1389407041715000d4a41c580d4551141d60380104116021a0076800b43ca080130246081d94034040d5003125902651650405154a5003002c503a041000d500c00354860000030000d1100b1f0070300e00200b01d00c078a260740300140a5040400c1d1541041e56550846050300c4d48071003403100c0c200b4000d011300003e14884204070740080482120b40300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 326581348 1250 326580098 326580127
    0x9040e030a0e0f030607020c06030414060a090b06100509060705070b1303120f05030109240906050f030a02030a0f0816060501050103051302100f14030c0304020a050a0b04050f06 78
    0x1540641901e0b002c10b00c0c16408100b090604084201074480d42c4460708114285901064143d0480002d481850f00e940b198a40f400000c1500d018029652248a080242d81c8100fa0001d401c09809191002000d482e580244000c2070311403090300e40821004c006131416810248010001103000794190740e4055100c00a0321020391101d0700700c10740b01c4044907051007885001c521845500095040c02c006a015049019240d40014483e00b520550384201001070040c801c058070b04442c00019040704041c0c1c503a1030120042c4240e010780b90180040004040160900254180910b90014002c211300304807a91010b80824100604a4013220148078030402c0100121048103018480e8801045543c1000b000404880004010072400a0b0494000015031a501c9041c0c18080b0580fa14044002e10068181c2d809040b200b000f583d0300900200308001048250040c40c0180e100b01e44404030590b4580c02c1054552481c0949031050300d042100f0485460011280c480383e0340d003d014a814558130294005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 326582598 1250 326581348 326581357
    0xd02063103120203070b04020607030507081909060e03060f150d060506042a230a211509020901090b18090a0c020709091a0c04080609060705070809040e03 68
    0x90108000c05024070400c00264015074100c00030703100a60030312000d40c492030050343c406000a4068240041c1440c1498814400c907030703c2a802c1060181e42e1440e54030b0303403004452a603403200300050b6104400f00c1d60342c0c8100c0f242d00c805200180105043d44501013250b15425004d801c6042004401e02c0c0d442003a2903000c05906154050180020185044000d20013982c00586000a650000d95080000303a04441070102c10720710300340343c2000c2c00c1c402c030724103242101803440e400c078000000420b840625507030110b81e141e1841407502c140744c0c01c49071190060040e220300b00030705036100b08124400d00801d15070b54094180ca0b041454211901903a5081c0500d641c2e0040300f110008a1154403810f0b024205401c02d9600f01040e94000c215580500400a40314444e60080d0402c00303843c3d102e444140080d002074005c03000d041a484c55440e0038207840a0180b80d03c03522230020035004820000310031410104016100721825282c0c185018460380d03a103c800e501450540354480d58483c0706100482e0104040d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 326583848 1250 326582598 326582677
    0xf12020f030f090d0c032d0206042715081e1e0a020a09020a1e0806010e0109030b0c031b0c060f0a0f0c02010c02010608061038031509060d0206 63
    0x40301010f07c02c040400403a80c580a8070480720307001115110050b101d180c100c40c00c94241d203403202480b0100c0741d91403524003144030040d40c0103410204d0320828018600c4081040f038060500b141d0980b84901c0c90001c00401101823510203801c201444c01d205686810100600d007051000d44400403550f170b00189014040c1d800804000c0c2c2d0200d0300b80b10954001c1c0d40c6021192075012502c0400d15040002032825500510b4036041042c0900381e6248d5034014042000911751258182a00d40b1b48980302111642085822003021116400c001d400440c5240449025030005005008103550b0301c0501006854054094482135690703c4003514060040c0c803c800c1521030315400132074680c0c84080001e0a492a03600b05861603004035003404040106007500d5400c40c2c859440982e07a28011007024600b440d40420301410035074402144d11400c80030b14000354400c00d00821039800c450105c0c1e0510a40203012281140c0141e80c54030b2900261038580701510103141c43caa8110f181c0d03504120803084244440c0e011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 326585098 1250 326583848 326583863
    0x2071a030f0601050c0a2301020414030c061204111f2016090f02090d03081009021204060b1f11010f0b0105030703110f070f12020f030f090d0c03 64
    0x6000c5110200c007103464201d8000d1070f2903814080951407141d1503403e0081c005001c070007003449240142c2070040c2528082120540215190b903600c4000061825644154600ca030148070b400101614154045d03948240a6411598080e0b8555440301005420052482d911210ba0101600100c10104842071258280d035100720108036000740082c2030141410b81c03c2204d40003000b034a8510400440c0701d07000c84100040100341800000c00d00d00c000e202c2c45000c25008071440d03a070b07901455000b40d00c2034045c00c046201d651009a492405034100e014044880c0003070426440803d0200d412b6410204c8981c00041c000d108103032890a4814158141142c107401213500d1140030702d0980700c2803180e003d03100e00c4140c050184101100000b4020312006160400303041e030380c01001c481e0404150503030340d4503105446510303901c03281030500820780c0d036208504031800c521000c0d4600700140f002c103e500c1e81c034980100846c2440d5904401d040c4541086440f250422210300400000c2814a0990300046005881 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 326586348 1250 326585098 326585101
    0xd030f0207060e16061412060d0602040b03070e030d0503011511030a1115040f0210030207060f1b0201110301060e0d080417150609040b04062405010314100504020304020102071a03 79
    0x1203043d50b211079601900c280b04c01c004043c45640703400f004540d007903120f051100320181d49000008240c0271685c0c1015007981c0c808240800c06c103440c98005c1d4040e80c101d440c0e00f122040014100340c0d480115000c0c040c0050703410300040012442882d2006c03552400d905010544410117005545144c202e50001000107010b0031940d5a103c5051000540f40841100c02e00450b20741620748002a4240f001c000b806080c42105200155110741c1c1565020b550029051100f10000b4080b240a081000301c0601c240350752110405080b070052143c02c0c0300c854110011b509513031070030405641b8507c50520f0f4940040c1c40080ca0750000e004000184054000c03e030b890003d088440100038a0b01c810074000041c04403100b42407044035619280c1840c0d01c2603000800f02129500c52070b200000c0e1111810001c002c4070346002006080150b4415501a1503080c4d070700300004005000c000340c00d06025039680e0407103600c4540500060a0035001190f00c1401030048a0b0342c20360300c940c0341d401c3e06440205003289040110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 326587598 1250 326586348 326586373
    0x110306130b0f01050c0312090c090702160519031403040e0609070c06020f073e011e0311040311130506060d0c090807031b08010204080d030f0207060e 66
    0x106144902040303994200280c40000020448160121100c141800004601c1d100c20250400c01c03911410040d11400da80c80c2007450710b00360383d200d500040900c00c0c0c0150002808262000442d8249040c4108a403002d030351400080c881086c00031b440040000420000200220b1440740c0340c0c062400d4040d0041d9542c0749451304154100e400a03000f284103801000c207000e0015404561444241e030003007c01650f0301c16400a00e0058801c0400041002c1900a496041d0450b403150f1503002d00e001c0c2050302c0f8041c8002c41d0000984614130034040c0801e003011007401e511070654448214900e03140c00c000480b80742d4030a5505c010b80055100311407284040c20081c415007428100202051707a485400d1021f42400c03000501d85004283d107064015584806641c55640300d0407100004014004c159211241ca0b030800c1035460041080c511b142601c0081c0000d1410380520072201120301c10b030090000900c46800443c0a44012603c080c0c0c00c940a204480c0484e0f19440780341c0c01e6000040c01000040d21342c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 326588848 1250 326587598 326587609
    0xc1b0f06090e01170a06050705130627050d0305030903040b0412030207080307022b0b0a02090108011a0702060a02030f0d0c0e0904080d15180905150106051b01020904110306 76
    0x1600000420184d0803d800e006a000284a42c80d05510600200301603441c0c8000720703118000c4070020010a0402000081c90035000000075803030242e03c19140750704001d01141c0380f008201501c105900045816000f1011a10420185400c001100c00792440c0030f07910554450a600280c0008401c502065a25810185c0410415004250398070155040081b1a00012000d201458100d90b01004804120300080290a910b54480740c0c0005400c2e050305125014500a4002c0d880103404078040c02d0010820034071080d900d031519503220184901d4141c40303500744512500141412011340c4018422a65155002c0c03002c0c0031034824054001401d810884d1005000300704000600c0d004a0b0000c2c14813001c41e000320f00311102d2145000010801c07206020307070b103a90b03019036501110851100482040b91b200c2690040380d4058050390803a400c40c080c00e1b0a81d06c91150030b00c01c9001103641000b030b03060714181c4031a000d04010038000006091800b400085001e59890385401031281c800001080300c80e00c0c20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 326590098 1250 326588848 326588851
    0x6050109060c08040b0304051c05030a0b03010e0c0f01120501181b08150307082b080114040c170703050106110115050409020d02120703061a010c1b0f06090e 69
    0x580c90b01d40720800c91519540c245100b20f001c0d800c0d2115000000405000003002030780910301d04000d0a109200d4050b4009050b600140c0c0c9200210741403540c17402d0300707103414050302d83d00031711840141800105000401400019000e007940c14031442544038030706401207100e21070080280041039407102441c00300110454400300078270307251149002841da090a62010300f86034004140030348481c40e81c0c0c1c1040000d10345000d43d4010344241c40380a108101001c2d030300c04888260340002040e90030320403070184140c4516009020300d020101c2281c940a03c140341ca0303000a0710840690500300e2104c842e5080018603501e0172104c3e100400e403200f004100c404da1084040d203901101c0d000810141030080c40300c41401c8210f01c2120302c03660300c0f00301d002c056558682d012160203500525601c10b005616245c42c0c0c58940920003501e00710700e016402c4640507144400c400500750165500c003241880c5a4403046d03400394100c0b61841c2d88111603170200c1c104000001c00d5000d0706103500c480340c4d020300e4282842c050050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 326591348 1250 326590098 326590109
    0x120a051002070b180102040b040f0503070609080a080d0f09030e030c0406060c030c050f01050133050f1318060e090a050a03080a0f021207080f0f06130b120106050109 73
    0x4108584800f240c8035050158101da0b071103c052a000e10032103a0140680a10707004503403800750001c1c2c0044d1030110800948100c58055041c0c42c1202e5a8201c1682c480100d4821144240c1002030084000781000e0020b0840c442d98400000b4401c0328503528500b25900c214040700859100f00c0310b501140307002c1025003d4624121400d00109003400e00041c0003d29200d4001c1c01e024000034240104981481801042e200d00c000802071076a440510f001d00008910b680e03070143d14032011550300001c00182c011000c000640780d00e0300e4440a040700c02c4095001c007000310440701c11000c0124404043c1c2910540418001c040840c01600301a0540c074101e90203400c00c68250301241d121000102c02044c02400540c150401e08440d82e100390a01010b8820322035042e240610004d207441850f25020617460180c0c3d1782d40c0d1030a0b00d56640105088401d00290359080b2210122400100700346440b2509842d20391040401040111182000c60041c60cc4200025a184d4543ca0b05200e9542d20050090082c00d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 326592598 1250 326591348 326591351
    0xc05150c07032907120b0301060824010b0909150d02040f1d030705100c1709010501032003100507030b0a03060504030305160504030210090302120607021c0905100e120a0510 76
    0x80c5020041d18044240b00c0c04840d0740c0e00c6d020112041e81d002e41c88940240310036000d9400728800302c0d1100407862581c009d0601303030408510002c941ca007000310998aa03400050107800b02a103c00c3c81034408003032074840b4036900c618a00361000040e240c6015044404150040104050b40954000108800800d154880720390081c460b8001007200040c84504101c0c102e1000154002c50003811a9454451410b4088109451080c0940154158001d84c1203e02400c0880a01191603010301131005e890031131f142d071560258100c0b628002c240d41c005030300a40355044c00260381c0c3e0b80b100890300c0c0403815401607681944e200108424103401d4000e0175031000000c200c00c0700c0c2e1036038428082d0041c022800041d01030503144401d49882400791190750301868004003580114a9060b1016955540840322140140540ba80b00031300c45091441000442180c1d803180100142041c0a000320340c44407031100000c00038183d42c003003c10703100c0300c42c00414008a030002e41300e9152141416858108008840054035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 326593848 1250 326592598 326592601
    0x8010b0d1b1e030c090b09040603140c0301140705120a020c0d02030706060609030b040803090102071a060a0b13031b0312080108010b060405100c02130515031203040c05150c070329 79
    0x16034460382003004d95690001540d180c40c81c42d8081002044660401461170040c2c55400e0b00d0604e0019800c10000303401c6009101172441d01c1cfe00c07000360500c251041c10102e01d0030311008150550070041e41f036021615001c0103050030540d00405143c8400c1c0d000f1440503800c0021820305000701800f40c4405005c07036050403050613246a44036101c5074001400500240e501001264481c1029011200c1450708082e0b074640c3c0e2007070815014403c080c2681d54511a8440301000108c0c91150016500c0903400040b409564504e10b80368070b00c014028690040d060b4480c1c800100008003940078040c407030141c40d911030300d440d818000e1417400c40d0384254155100d250140001c0049503115225510511500c0c5024400c0c1c41071440814151500240d440c0465420941042942c00d00004c400301c090a00b02d04485007015108a11102440181c8014181000c50b03282071040e81001040b0030480400c2201d02c5103001103081c180c600f000400d810448401d034840d07545114062194500b50942c45511104e480c46 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 326595098 1250 326593848 326593871
    0x212040e0402011116090204081605090a09050109020a0b19020304030510020c03160b070f260603160806010f06030c020a030e06091305060411070308010b0d1b1e03 72
    0x4032000104020304012200f91010b42408081c46003480301c180c2048130310644d50300d075842040030790003901030f25196118010440828002411560080b207001418102c0cae591205010007018100d000301c04e46041d0340300c00190005840380e1580c080103100000049031504460300c1c00548041c24600e0900465100344401c0c0082100442d0144041e43c04e144016a90b20300a03501500350302402802181a0418420704002d102c00900524800d5450341d990049204105009a0300c0780051030030a20742198103c07011706030090f880b0310540c000d40010304031038884003111078581071030543e03400406982d00400c004005800b0b0741411140075110382c0c107084c0030345214044020350310040014060100314a0f500b0440382511041c0880d504500041c10340881c1417250346401c4080c142c261804e0f4000c2d45440398418840311944140d4980a0b810340e60106c05901c2c01c0311481c40c540101c0400751400d581c4100300c3e14200b0951800500c2030f5000d0300d5126181c1034010309110000c1094242c58281801e05004101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 326596348 1250 326595098 326595119
    0x90705031e0c220c17070216081504110109050d060f0c050306010f081b0406030207150509100915020d051807080c01121407081f0b19020a02030106060f021204 70
    0x5078a2035540f0010380c0032002c0400311000c0b660f4142c900000b06000062250309540404c031803042032001851024800c1da10042280e5807a030455081e0912b5081e900450009503001c0405021143e051400381d13a40c6496100003042c81c0210071003110425990303540003664088a024503642e100541c2003690035480c1c0840040d282314511300e2a0400c12981400203404400050051160342c00317005441610b130307601c81b8400f030000e41c44031000361010285d005403951129804e00440d44914802405005040800d840d0070000e020304000484410045400110b180011480070b04644c224210010a05080401a12810b80640404410140c000c5034061160b000c0000d070304e101304a020f03e0f00003806401d8091010040ca0704007800b01c004580501408403031a801603486002d420f941024001040c4d1b44c1e00c07402d21039080f40c8580401840300380403090648074140d0140b00c0341003140c01620361010203507000a0865443d80c2015010481410718260440c0d41004400e406203102c402c0d0502d8036007030454010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 326597598 1250 326596348 326596399
    0xc06090e0a0203130b0403030e0303010b1b030405030a020607030504090228080708060d0512073f081f0e010611151302010c0c06081b0a0c0b090705031e0c 68
    0x5d01120038840030408061007507000c082e224019800340c9031030f541c4039004451300b0390100c000c02005405c60540c103000031b00084112012110000e006091480c265404c0c050103070030030b070b1069051041c180720000300701806000404c4699544043d2054a004240613a03040c10350105440301080b200e54200002c00b034001d42016089401240c103450f0311101c500d0070921744800f401d8494003d0750007066100410541d40304500684c01344482405150b1900700d16022101800301d02c0c2d00c28a003082e50010842801089a0303a0004480c80c18460701a111500403c01e001869106c0e800a2500200401c0400d0344200380802d0490017002234100010200f00404040e900988040c1c8490301c80441c400c210380c0507107200e4540079446010348009980e925809042d511007100c54030300c01180010094030078100c0c0c1c800ca0321049001d0f03c0710000180580c4505e802c00c2001040d000992251180c04113281d0340403c03803801d0507000380343d00f4203003a0884450a828541c1880c0498051707118a2240c5140204010424 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 326598848 1250 326597598 326597603
    0x6110a0b0612101119020f0d1416030905010201050604090206031519090c020610030803150301060b070c050f03060405030712020304091e0638070c06090e0a020313 72
    0x11542107450711403a0341451900d8601090691601102400001d441005404205d125886580403610344c074005a88507207011078004869000000c1010500d40941c1d0710040b01c911410b00c0c20b003003207001c00e1040c181081a500c01d5001c41c060640810a80d030742401030680c03206041c1c4d82400309403020350104045000c080c01441005d8405244181c454480030f0810fa9400c0c10503119100b421303138820100005103a0720b55041b0042c02540d00050222088d502e107041245c0e0321405203441e6a07555515200460001b80900d580f42d5210b1b04002a4110072102501e10203003c1c0703000041c120b160104001c00c40c0814000140aa0094001c001c0480c1c004001e444000d90490b901002213046400100d0442c407603074100d9000185400e081c0c0c1042c402e100041084511487c0080140070382f035048182c1040702d1080b01000040800c0758518105401c0d050241c00c4d83d0008840c28100b100c5a42c400a5081c445d4000703070001b44001000f008080e519000c040d030054200c0c0320031403960030202c02c4000c2079400300c13101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 326600098 1250 326598848 326598859
    0x603290d02040e010f050f0906010603110a030b0a03120509040e0708030406051305190302030c040b030601120501090b13030f03020304080406030902060d0e0309010906020715210c0201020406110a0b06 88
    0x1c1440f515400e4100040200310810204924600245880c3c1c0443c8103842d4005c60303124410020480a0081c4100070110506070041400c1c484202e008030040e000341e200503078002040e103400000150104000300d030305441e95103510b91140505414003044031004075250b0700350380c030102c02040002000300c01c0f41d003501c02c50f14040d66142941c40c04990120100d0744013540010010740840400311b01c61b40301201b6a4030032015121142078070000c11040d00c43d03401070654160065001003000305201000d0b0229680b0078000460074103000e440c3c0c00c0040d1022515a50040350780e071801c00c10940d002907c244180401e0400b14150b06003910340e0005030055000d027405240d0341c1c074403507429036464a06075108800d010304280445e0000080d40794898009000940c00324015202c04601c180c004200340e0142e40000010411003807048404550304005003190045c14040601031100f20905405861003003880d980015035141d180c228000c025070910140300a43d41c1250f0820300000b80045d00c44d5800030b404541 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 326601348 1250 326600098 326600111
    0x1b081501050403080d18050708010501090c051e0c10090b07020c1806090a02270f030109030e041d0d0f18060e0d050708010f0b0f041814160603290d0204 67
    0x82c6e03c01d000390000c0f0040c00718410181c00250807041500001d0584a20010034070188036880d500391200d004a002c03441d01100d0290203228015009406030075005002c1c02200c00d001100d900c4a022512810310503600b5150400c02c0115654042161411543d4107407040c43e10000e40070305101c3d1074000944414802c0c1014404a01c0c1080c142d0191481000c94041c01159203054815050f603800c0115140d600450036000250501d103018443c0e080440d8060301c07540c08401500042000600c00105034612003003984104005580e0200302079075400940340c41e1040c034001c82c420003030010054401c200d80c1300c604c0c444c0140061540100103002504040c1c03001d07814140d081c0b800e54100030342a048802c0d50742c82c290403a00c420300e4a410203038040e5001d540c1c4400c000102400c0c0b1058410132510641413503111041d80e00050300e0624070006400ba0181510080364101011240f100059400840044e458252035100d20314480d41d13280740c9800420045141910100100e003090341a102c1c0a882580c2d00d00f07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 326602598 1250 326601348 326601371
    0x50105030f070807021f0539030414010c0203070b220821090a0201030e0102030f1902210604050a0b10030f060f1d0f04080f030a1b081501050403080d 66
    0x312013000c1d40d80200c1c8a581a211806c400703c02010220349500c2d244070740d2103000c440e5a210984008500d50188942607503802c0c2c035008003446604c041c2049410798080c2d450500e50150030b02c500e401c0711000b540556620009400e19911900c1b016051100c158180380c020311000d8074031006004110384c04076400d40c507820082512151b0352100d51500482400c001e04000312030740042840e07000c03c0e06c01d803402c11114030400000c40c01c0380402c0740c209018150010100c2c440101d2010700341c56100311001c0252510894550f010039680560510000020b016410302c403031450306009003903010244981c200100514000010303250043c100e07a0b007060541e540116004d02080c5d811100203055890300c0e0303519860340c1341106100714078420500c2541110041c01314901c51118400d0500442d02301c0341c40740c00c200282e00c00f8101c80d031014108a0034282c0e5545c403940100486810303000c1e01100d030340700c501d420700d420071000054220f4030201c0c0e410060100014000240d0b000169503206030f000f500003504200c0722 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 326603848 1250 326602598 326602603
    0x1409010e0607022e020a0b061203160602070c121502030907050405010312020105010f0609090b01030e1504020a09090b0a1a06070f0c05060a020c010f0e120105060a050105030f07080702 81
    0x1031000b0b0341000d900c120760610f04107000e07451034102020b00c00c40d80380066451002c0340ca42c8041030005001e400d00781c1c0450b21519106274290008042e2038140c0b440d1203039607160085c02410a0f441203840c2c5801040417024484c03807100100003810002c607030941100441d6503606a011505946410156000c0040344034908100020806842e01500402c540c1d40c4905010f0320050090060500640c24000041200b00c0e000d101001180c82c9516a01c580074104a0100301804100d00c00741c2c101541e07030b140140440d0080142074603400a0300c3c0d0100c1e290400c0d0040c0141408260014118142880c28120014032001e000f5a840055050001040e00d07214440e4510340e00d003802600d030700074004519081031269554120b0701d6103108251814095980fa020310406020f40707100d110158100c0d6500203050b500968004e41c00740b0325840c18800246040c0700160070711a070261a81c009a40d282e0070415242000904000a804242804c0e811858034035a1440c045c10b00818200800030b01001080040d03008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 326605098 1250 326603848 326603857
    0x10609140f1012020c06041e020102070611011506080a11040f031b030501020f0a0201050a060501080406050a0b0a0b07050f0705061b0309060a080403020c100f0f0908010212040c061409010e06 84
    0xc100f415540c0d0300300196007a035a030720241c03001d55401c802011000d410880b40400c18442950603000342c500c16107485401e85012003540c41440281d500c0d10150440789010f000030741c0280480d0b80740c611081c01e040d105502100e040c103841c031215100400080c481460420307003180c1140e5000304a1070150411140c0b185841582d80d10080071580041820004110000060245035038181d00810140c0d030f6000c80d080a0301e10707511903540030070380c004082030100d00300f50480c592241c0ca14074045407004003032000c2803401d06240d21001c0d00c080041441410440c0a10221340e018840800401d4043d09182c00a042403058030210310303021028082c4440d030002c041c0155000300308020480d40d11220f406401038108070003210b040b030050040d811f1007000e62030304800500300068540d0350201304121200d81903481111000c07a020038041d01ca80700149511090000f0060b03c1071550303001040e8202841c050080d00b43c20f8020311709001094148800d00c0d0044030940307c1201e824a800c2403080d0744d80010401c644074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 326606348 1250 326605098 326605127
    0xb070201120501090617070518130b010605090a1e060c03020703080a0504031101030c0c1101020a150903030e0604050c1c08030906010f060c02030312091501030506010609140f10 78
    0x2490b00020780080540d009104803058800418040c102c560700540d119842d5000c0c01d603000c0743c00b00c1082c0c9071042d51310316198042c0351b2001e030051580399500c4150074028268440000100f000801904a00384401148002c001030740c240560b0701284100720319240210f01886041002031701140080c0341c403c000307540003150045101a40d980d40d12000400b268001d00064514000200341d86034954400d11866506102c140e42d00b140780c0d4134030755a030700090a800417080d04500c100090a804102000c40c101c00307080506400140b40e020900c0c02400b03035001e01802c5075544c2c11240410011076001700b03003081d5070101220f90840b001c69804154a11461418014001d180f000c020060308180001e1081e068030700600124194540d40d9200300c400c04000b05000313401d500103000e440000e03003061010300d03008810300054031010f44112000441e010b109900640d15940454010885150800c2c118409005800c07a031040f02d031032000c042041032480318a0301f401050700300501801a440755003040e00201 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 326607598 1250 326606348 326606351
    0x102040305060c0c031c020403120c020f0103090602191101050a05070c1401021902160902031e0408041707060815011713052e02131a07081b0f160b07020112 69
    0x70118a450310003500240000c69260254000426058bc00f0780a0060041d9000300b0000141407600c0c01140644021242200d03591303002c1c0943c0001442d500401078002c14a6600e202500360310800703290039140301038030701c00035246450184111140d006070350780d880c95041103480160300150000e0303030b00903c148190500f41a030b083e01c0328030880343c1c0424520003c0301080d4118060315102c070072540c1240301c01c0d103421000818120300e000b14000c01000032540039001c2c0e6007003810145da41e031440643d08040200d43e8085d801180041c84804d40080d0102c4c1c125180c180010704c8886018000b8140d000e6031080c010000200a000448410440780c15800b07480c2d000702550441015040c01d048543d502c11512076900d10081200443d40c1d1a80c800d4a1700c460b0b9060034000c0349441e00342c0d2104107521860303084003140800c01c00c8601084000317000744403101070211320203205a00e05407942e0424820350a501e180e50003400f4101144500202e940041e1240900ba070341c0e0701c02c240d04c0140d0b15499807110400c22039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 326608848 1250 326607598 326607637
    0x6230909031306171807330e0a060906020c010309020f030a140d0e15031e19050c1204020f010e040603060213050d12050a3e0102040305060c0c03 64
    0x2c6901031070f2000c02948180b2035644a0b217418080f00702e900c1840704090f400d54441e003801c000c5e80d01d02d810401c110181c03480c614141d42180302e02074910035101480c140e02281842005c0101c905005860344020203c034a0f01420b05410007100030344610b409600941015201e903840c41c1550303260201164820001402c4802411503032030500602400a00380061600880e010105500d0003050201c94410004000003c949400030682030316400240004245040e221250445420006040c0b4000d4149071010100d0412542408095400051151120703a00c1446081c844903045103920303801c50b0741110105261219100101e0b90301511921880d80701d810407200005205095008200c00e011200602c144c86888100348180911032500052071b8500301201180c00034802d0700640065642da1070b00c1403142080807030190042081c82c460700c4a00b00001511458104600d44008110200740020350405246485550310b900d002441071040001c0020a6200c01c1c0080c421030b554148940c0020882 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 326610098 1250 326608848 326608859
    0x210605060d0c0305060103060f122406030b280c020c21010e0a020105030109020a030f020c15010515040302010c080702042c210c01060506030712062309090313 70
    0x50b1266070104004203203058081015035102e40a108151100600702800c160b1034000302d0068598464416685a8840c41d03201040d04460350390510358107205040401d659086d400d081c03104400180030b43c1e034140252400301700c081802e41030120b100c803988400051095a4104141d0030a0340c122840703503000052020b0031490704443d41d20801d0450040008202c0d003000722010035518160104040d020810500c010001042d6540051100000301e14010580041c0e50811900baa041240d80192a03004403030f19082122226000e41d0041c0300c02c8403104910651120007030010f02c11408003070304001c0718109041c10b21807680c00701d84030b01380d000d00208010b04407800c0820b04080155540c07404003e5092070f095803c080080c00001244110a0b4580100c9002041038a02d0b41700507000e02a5540765440020165142e41c040c5108d0b461645030400e00d07038080220721040300d0303098012042c040b01080704607003041c1803401002651a004d039482001502d80c800c0701d038030f0340c095080390076070141006802145 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 326611348 1250 326610098 326610101
    0x603050d20060f13170403120809010c120e0a081902060702010b0a060e0d020d050d0311130303030903050c030d020d0e0319080c0c16080705010f210605060d 69
    0x403204040044020041c804015207910b036a82551a24241603d40c0041145000c0c20003c403060745100b400300705090502e86025600d02d030855401919140f20f0b0740d1144d9042d0f50010b000552040c00c002c000c02c140700e908080078085281020b10326040a03510b50404017171450030011401d02e240c10145541c2c484c10342e000c00e000044081e0003a00018010000882c16807401406004050140140070180090403c03070704482c4483c1100e905503000820762a03c9016071151300b92070305d015000310080e245120f088200030742035070f948582c42d05c0d20310001c000c1d0703c03480006483c101d010740e64146800b00702c04100b03040844150148071292400c9000005402c3d048080c0c641c010414068030f00014003209079001000758490203407056100c80e489008422104040c0300c1d154103070b4403103a80c030002e90825030b0001909143c1981e550000030080c15030681480340c40e004000f1500109000d10f820480d0820b03404006154241c0b90800000d40d01c810315000d90142007540000f0050200901000e8503800700244640 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 326612598 1250 326611348 326611367
    0xf0207080d27060510031a010806150109031112030a0905031203060609130f06030308091203240409021206040b220803040f0209010e01031b05010f03020d0603050d 72
    0x1000514021401072441e070144010300e014028903101203440b500c203480c2d21002d4800100301c03031a10303003a8030780c04400106902001f030f10905006010754801c2d1306205a041ca0706034090903840141c58039a003601c440e0382c1c1c0408903005495001e450340c6008101440450303a6040c00f41014102d900000c541000f046600105180444004034200d031240002100c0ea141c0c80e120580c0c4940e0012000c00c048140317414448800c11400c042c085e0002015000401a80c0480b803094204a001558000a0082009003040f00030929242110490318500705003070000031903c0040d071503000c100d800c4a40550a6a25071f0b11111075250060100720a4222050885480d010100d400320740452250002c204071890480c2c1c01020041d030420703207642965058568004a400040088691000c0d03140d000b80140c650401860003400c03500880d00e076a5055151040c404a081450b809195200b4202040075a07400181020844502d0a00503170f644403180c821400780003203800141ca42e1051707900c0c0c8501941e0207440300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 326613848 1250 326612598 326612617
    0xe0301060b0705061504180b060f1c060b040507050910050f070b07180806061e0d2405100b0307110111030106020d0318141009030e090601020a05120d0f020708 70
    0x4540240300318040108a800c801e04154400900387c1c50a000503040c8071880350816801001300c0d03440201400040c00c05008141c410140200c1c031034101c003c200f8280100c1d00945e4003240d092126240040c3d00420078010b03228a09d1141074030f01d405120443c0514100c68016640400b503035913072100c5050140c11a50f05580c0b110005d44108800441d90042d2141402038958007806010f403521a0020080c801d0800d550710180c0d5100c02c903550002d50b4502c003643e00014841c3c0f44180c1030001c0242441140e02001e08925040ca00f030608112100800354600388c259680f219100d5285d4642c0041140c04c5418801b012440390329000d540740d2204111000b650484120303034219441110244001c4042d140040076080c010741c2d0303064481001030343c3e21404410208101044403041c4212600c0c003008d039040310000f0750203d00d1514042d40242420041c25a10100a0009168810080d968142d5580405100c40084100451380e00081c48a076000380501e014405025034440040707081413519603101e038200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 326615098 1250 326613848 326613871
    0x91c0b040b0709080309102712170c0a120c0506150f06041809050c09070c0b0a0203040f02040c020f010c0503010806010e13030c031202160507050604080d0e0301060b070506 76
    0x9000380c000046601d450406060400d2041c00010181c803d90b44004003409810003126041d1088408c1c01040c0004102030300e640b6110b0388083c10003e142081c00c0c000c10740858404c01c0624092140081c0450010394000511820300b49415000c807801880c100c03004000307006981c14401d07180c4070380b0350128200104854025065645000700407082c0709500c180a441005903014a40e403030342c5540075900c854000c5050f18480c045410001f140304004681110100e000e6881c2d200500c0703408018145d0201517084218510f0526031907074a00341e5600d00f8000c0c415a2218000609036200340110051341c04060001c0c0000c03181800d002d4100d4100340a0b0844a2103000c0c000144c11902c070004502860008084035000da205403400c0300c0403040305074198240035001980e0f07141d444007840141034040d00b6402e40a2005414a805800c284581d40710b644a2813013400203005948010940c5100080d10307051003002d00f1030300004a4050203455200c0741c90700d440440c00030140500842c0091265400400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 326616348 1250 326615098 326615117
    0x210708060f0d140307060c11010608070b0306040c090902030a0c2d05030c040e011413060302030d050c3c010c08010501080403021911030f06010506091c0b040b07 71
    0x1405541c1c8111100c8a0748010790300400c40128010742800342c4010a61000c0e00c1c034001c01e40c1c6a4000380d40b106580c110020304400340c0320055240038401c0c90041d215403005008024681034403400030303000103030520707200300d03658a5000c280d94015481c83c03004144407803095480c0e01c0e02c4460140104402c40c407040214030701211240a180044c014000c004040103150300c184203090104880b9504002c10364045400b0800000c02c00f403d250142500030048042d40c10100a085410300c10504420700c42100307100c2c1840b4040c80160750104c0c0e44001300c00d00340340082c0c0b295507168030705291032000c1c110031000b80184510001c83c1c0d40c0340b00c4522000c2e401d02e0062410307002644041e500f200d0618440c0d10024142000601196100d000800c0d000b50180c0304a4072041904462940e9040600e00f0444100360014226100c0307080c2031003c00310030207090300a00000c1d850030300825283d10460030030300d02c070302c502c00c0542c00083c01055803600280d80046640c1b5083c0740c07901e06203124440950300700000c14203094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 326617598 1250 326616348 326616361
    0xf05071d06090403080c0f040e0709050108162303150a050603090c010c06060510111218152502091023040e0a0503120a0204030f080906210708 63
    0x8030207000d8040601014140d82e1191400c42d079583c4007810035910031000308000c03000340c001d800c082e1001e02190111a01c09e4103000d2400703040742e03100398803050500c0400710070045202145845440120704600b010740445560300e0b2000000c0342180750b40c100c101004418400b88078004031789090485400c0c1c1c0c00c40c19083d2108100400ca000072540d10984d84d00815403070b0103d511855401a071144210700101d80243c50303c00003804464410001000902e0040c0720007031a910070415403544050341c1a1035442d01403400c00200c032651540170341034001c0d119094612410303042c40c1c0455600100c0b001060848003441c0a090b130980b9017080003a4840c01900000c29041a0b0844902c012034103015600510140070781040641c4c0005804100e40c041d540c1c105460001c50705214111843e8401c0d0042c562352542103800c914580e00241040e041c00348144014000604104440c0400580210001d6102c8148100146803846040f0400780101d54081c41a50104201400c0c1c90203a07469848201e11a910350 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 326618705 1107 326617598 326617649
    0x408030703030b010e10200613150b0607110d05010627200f1c061403010903270302060c03190212070b130f0507 50
    0x18000c0304041e0b052255a55103507007400e0040320140300c980400c05010841d40d42c0700902040c880d180c9a043c6458040a00c80603400044075051301e400e45208403001c1c0c68400403104924070000e008106d0209000e07007042c40d40081d100c030342400d5503603c400a40064621041c0c0d0400300b040d00c2c00020460078055100945280030b080c0c0803000440c60116101ca0b456000050800d290500c030340b80802e202c81074a02c0120242c1400c40e00c032150307110316290b140f25800100f5445e82c6410003500c000145504504216400c41e40084042c085a00c1032500703a50806000500094182e002e03040402d0b003003601c031181c0e580022001c0d400240c507a0702041156006484030b015030391012901050400e5215500d05403004a0310146c10003009001866406000d880c000402102d45000024090065080350450480c0c008405c038207414100e0504d03c1d116003860041817a480d01a81113660512301d035 = true := by decide +kernel

theorem cover : BRFrame.Cov 326438848 326618705 := by
  have h0 := BRFrame.cov_init 326438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 326438848 ≤ n) (h2 : n < 326618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
