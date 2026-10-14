-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3308
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:16:43.883985+00:00
-- url     : https://prove2.me/submissions/23acb99b-ce68-43db-9469-42d2dbb3604f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 594784172 ≤ n < 594964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 594785422 1250 594784172 594784181
    0x10506041412072301021f020d09020904050c041b020703060c0e100f021e0c040e01150308030a0c26090f0a03030f1a150a05041d07141c 60
    0x30020304544403440105020b0707480c04040f640500000024080d10004014a941440305518400d00c010441e0001204014401404d07d8100d603090b964002524002800310340c101d0700380030b50010124000c5250900b042600d03081c04000a6124614004060200000303100d45504107200300d074000d00c070b600c2c2035985001c000d041c810722140c14058244600c2d40142d0350540400b0b0030002d40e64401080c0350f00500041d10b4610001c25401c061803240420340780980002403040325111084a0220f401c0905403206401015000c210f152210110413020051250160095016000c481ca082002c22000c25084a600c15035075007420300200d01e604034216400c1041015a0421200c41c203032592208554682460400080e60403404070b41c441000740102c52081c401c102e00c201103c40031075840c00d0200002060b207030306c40328450316007000401d03034000441c8540c0594002d4030700d2084205c00c61408600344003091314201c0b00f9100098802030340d4600b502210040d030740041d0320200c0140c880308a0002190150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 594786672 1250 594785422 594785459
    0x120112020d062a0503061c172a010203060603070c0c05031f1404050a020603040303110403080d0507020111030121050d03060305060906060307060e1c030e0f0901050604 74
    0x9207820158401080d40c611035558807000c0c150314140c501060703007900500111070350320000900c041801004499180d590200258150f030050454001c881d03072600e502d4180001021070900304001c5008030500c00c12030580a1010400c41c01d5690040280ea041403e0b0303c011203050b40c0005091004c140790328003503000041c0813403040104c003101c01c0d2584007091400c0e802954105a000c0314175807481c2e0703000341403081113040e000342d20b140d241c580752a881c1d00c2c0d81e4000b0f83c00002d015410001c0050207151003a4803110060041100440d81da80d942d00301040700d5040a050410083e28110106540500500c0344603804000485031500316881d0428688214605000c1a03000120702240340000680520030081e2f080d03902d0304c000035400d0550901e00d1900308002c3c81840070303a201d031042c000680d400007201400c407500c2d450300031040d500d1400420300524035130507105ca070766601c12081410150840d44640c00420107603418040645030f0010400813400030712920390489010082070210000c450000b0080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 594787922 1250 594786672 594786679
    0x13021e0c011e060501140f0712170903070204050a0c02071806031703040506060d0b0a1d060a05190b0d1203020f0d2a0219050709110d060b12011202 65
    0x1000704502045000d480220410500283c0e6032506100541e007101c2e0000000180d98402c0f400c1c141051501c4885106522018060b01e00c8860014101c3e40318204014480d007929401e21018100040c016a890f084203a0891140342000001650804240b0034400741e417580e0b0b0700500d9150305e0049200c44e01c080c10158551078603140ca50100120b030046080345003c0411015040d44ca01e8241046420010080c100f94401c5420300441004181440c061f2508449841c000041b600c0420401855a00c550141c6034098050b017420400c05010130f41c40749115a01c0354840b040356685001c079010495800d03140c4c83c0e502c0440d031911080420700c1c003c8811401105803d00514103000b040e0b01900d55000700400012181c2c0b90b4049800300707404602c0d0031103a000072442860103003495040c060f442d0036a0b201d41d81001078042146a040c0b10f4104401c070020302804e1420407030f111a03000491460741c402d100340303c40f2900300b00b0001000c0c0c40384800c0350f0001e6440403541c6800e0342494501419a0081d1030107990 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 594789172 1250 594787922 594787931
    0xf0906040b040c23030c0603010e0c0903070504050a020c0105150102071a12250512040602030403020a061e0b06070309230a0608040308060109031205070503070c03060b13021e0c01 79
    0x1035003445601c60404e084e06a1301c030a4020081002054030700120f00b8200703801480d0501c0100322800000f8101034100350501031303003a12000c441001c24a48041680070f50f5205003003500703028800307500d81d00800da49410100240202c0c3c0c4c51124980c0e51501c9140d016005a0000004100640401d1603098490102400d49403520818200c1c4100d10003041d15820b0b0703109002400d03000c50080b02140c0300d48041741c5091076410f00100d80401060298001c001038141a000030000d03007018400c0c04100f43c0c00794810410860f0034407400c038410201d001980841803e034604808404640360220a0f00d200c00da041d0346518150f41402d07807104540624402901d0b42641c442c030541d81340d07510954118084c1c012680c40104514160a008021308405801c1905000d02110203201082d000e000b0b91020400b2814403a555a03c0c5207456032451085000240c07003102d000c80040200324103a084158078810459200368903404803d50b0000f01d106002d01000200e08120b090f0020f00a8031020308030001a5000009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 594790422 1250 594789172 594789179
    0x4090f1b030f150f080607021b010e010329030706030b09060d0f0c030305180607120f02030f041712280504030f05010606030515090604020d0603020a0f0801050f0906040b040c 77
    0x741c4210344c0c20050341d04a00a6042c42024070800c110741d840f1105200500251460349a900c0c0c0e26083c00c07160728100403203100b1404682c1d0298118040060390072000e0700103400b8044e400d6102d00b8813949594460b006040c00040c1e458440d00036409103d500805d00c2c5140c0e1141d408214403101d4141040390b405a10203504030101d0391040c1c04800850083c2c0300e00d9960403080880e407010039044412030f403082d034040c003420001c40c01c140940908108581010070f041c40d9034003070980c554010460303850320340000010041809281c122070390402205c1c0c0c104071401344400880c8080540505007624080c0c0e240346e2040ca040d00b00c1e0980600d107c01d1181880792526840303840d4100c02752015501074036103a456003005c0040319498440d040d84080785001401058944000040200c1406003000e0312668000c10000032b048060350000c8025030780100721459070740d0f80d0390480000b07541340d12800c0c1c0d036540780000055001801246191048039083d028000503915a500c0310f0700c001002d00700341d5007942d02c0070020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 594791672 1250 594790422 594790451
    0x510021605030409050910062403020f1317120313080729070203030c040306050a020d0c0207060912020d1e08044e140a0804090f1b030f 60
    0x83c00a040103600104940c504420041e140c2070300307000000704051818408100d544005a80c19240581c1545407541d00740d050b007021030180c010300c910144030b0003002480c603151344920107440c000c80d488090401e0710300320445041a11000e007054640500700c0c04100207861030044a1060341580d10803139030142000e901c1e842d1425140b2440ca583d00c1d4680045000111481c14080c03007030303888941d41c4001c500d1441c20003c1c04032940941d2000401c0c0503100c1000c20800040b0360146c43d40c169455104211004401703c0c001e50315a510321908011490003030f80860440088900714003d0350300a800074030000c4c5a80d4030300c040000fa9626803d240004a10038600041d09000108014002c250307460400b00b1070120308041c440d014217080b410b40b40701c107241c0780b2212080c8100040e00000082c03076080d02040a0800d4161124a0041e812080c01006074140070041490003400075180000e01c01c000d80216900c208044030707404503020b0142c1c1010001004401c0c03298004e0b0804032080400400c0c00c80c00751012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 594792922 1250 594791672 594791677
    0x1c0602030a0203041b081023161d15030c090406030c0906050405101e03080a18050103020703090911070c14041b0f0c171303030219051002160503 64
    0x74180010b40000900c010710004003d881c0e05400d030b07940c1040ca42854116400e036190505c100c001038442e15003000d024070322051581ca100c82c0504040390301207032800807216066815200300020109047c081000c1d4800048400151101405024503c12281d400c0c42d62100e40c0004150000f804002c0184681c1038540d405100000c6114607501c007025401c000705102a2040380d04040d015034074003400c1040c0d04c91140840c0d0300b1108600d0302e10f6001580405102ca440c81660406000050300007140c1c4072281d071210203281e008605400305014141c8840046069104402c00a000101001c03000e01051080d80c0c40b950302c080d050b1101c5032500105690705141d000b0550304c1849854012200d0524a0502e030181c91490350340e208021f40c0b0241d0041c1e0260501c80c0c61079801c0d04101c01c00b2500c101f00301d107501d12450184402e10110f41c469440d00d0b41000703079030500d0004074014018000e210a58000000000c3e13280e40d0f00001410342003c0c00110130000350880f82d400c1e010945101240404604103000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 594794172 1250 594792922 594792931
    0x90c02010603020f1c020d031e050a171e0a0e0a0501090507060908030d0209220504031e02030409050c091203030a0b06030708070809010e120901090f080604021c060203 74
    0x1c110745266004001280203501d8282d8003c4070307103851814042401008240701a42d04031410111540203007030071a44050713200c2011842084503a49105a40e42010103000405080d5844541c01030160071b03d2a40b2142c1038510f02c580c51003400c4102101c04050f0303d2035a001c2d007032170000039450980f880c0c00c44c41c0240c2024243c3d56a599a50120148801805420701034115801d040b15601d00e01842d030741e900c0c40360b0715002a00d585d0100f017107002981d940480f4208010f41035a02e442417074a10950304014403094408a002c200c000844030008107403140f07640007121032900994103241c54201346801800b4010700c0150050030810039240e803582c130b24820030400811000115164605811070303204881d04030720110b100b603200344100506c40b80d0142da1107500510038035250100c0d40f40c42072000d02400303a11402a06600640c50003195101003440a000503a02c26a075a11511303503907140c0003480c1071240c0184e000f41e4000900040150901e451031005074050500d0201441c0203d0711442c2c22030700140c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 594795422 1250 594794172 594794177
    0x903050a120e10021305030705180a0f2c0a03050d15090e03130b1e071e060f0c080411010e150414040c0e0f04150803160210080903040e040c090c 64
    0x1658645c3e00391905080d0000c1c0c0016001130940b2400c0000042a44940075441058201d4100004042c0c002e15040308c00d04518081c0d081c410501204c01121030110282c1e41003464103a848940c0300c140000149049600380c158036030320718000c0b009607010082c000300d048112003191004400680425144103480b4010b00b42e201540d20344901d032800707907116070b45548020404a024481015003d02c01c1c0da5103c1e40e4003540012903901c0d00e80346010303205d98045100750040d10502e0303248042801203a0308541145151850100000d000402c3c05844d0060140c5015049900c0304001400341c0d40030b042c0f90584142d00a080b00031800c41c6030b4204486a00c15002195054841213200000f03040901030084041e416081c002409180d18012903495184101c5140c442c5444031961110304542d0301482019080e02d2040d2640c48911906040c040590f20004178047d4107180c0008944601c01c9020b01d01904200001d1841c01d80707010002d443c00344c0d0140050f03c54604000000071140301c02d11500b010032030140c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 594796672 1250 594795422 594795427
    0xa56090604030305060306010e150109151701120507090e010e030a0e03060c0c150c1635030a09020402091c0606080309131e0c0503010312030903050a120e1002 70
    0x61034020251a40940074a00907800740c0014011007009c4180103921170090130f0308901c44420180101c8612035103901029400910306040304015500661000480702011b400c0c00507a6030b41d80e408140001c6801000c2d0040e000010306204030b0810f07401c91034500c90f0b180f00210307500d41d907443c0301b5003150720500c421008242e00d08009155810184180c55000444480d2142070498010030b01b91104c440198105401071720300005400f02d079007041614100455001d2110402c00c1c645020080305401e01d01d1004803075040021043c2290016071000142030018041c14115210140c03020042d100b1201d007241d019400384400083c613103480f034400c030352110b401c0254a200445402c2c00c0080740d1040d0030041181e0010040b100d4203485280c104402c5800b079900000700781081c00f0303491a51041c4c2c8482c00d0989401c012058251a0344440030b54140d0340101c040701502c2c80d403c8400d4003110300841000300402d0341844501d03240c85c0543e4101c000807000c14030100e044501c00c8003050400d481ca000495003035501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 594797922 1250 594796672 594796681
    0x71202040f1d1c0212180102071e09150b12070c0524090f0d0e1203192007090b060c150a060f050303030a022a0a560906 53
    0x2a100800010307202400a0b11105d550854401a039200714030854072111906440d000459208103c41402410080c00f40c2400315400160114600c243d032048609036401d002d012000044101209021520b0000010b80b914400d519035080503c03004000d80301344084007070504046401032200005007041d0103000c0a01c230350803403180c2404000c0134028101d00d40c44010642c000f03e000180e250030700505400e181c0071980b1440005100904800c0b181d003498000403558100b4240b1101c11700c1c40e890115164159180c80c0d04152140035044010114060f40c00148100140240c692020b4080c3c1e0025068600c0d0000c100b01981c90010021b0601c071190f40036800b04840040544200b60250041c83c03035a901c1c00b4a030800003560f90001070000210705500280000c4002c00410300b01c88020f40045032a480382e14200c8074180c507180c0341c06080d04d403200d801c0601c114450010f03807091821500b0b032108000d02480c01200007001d024444ea1000e40c509103141e522a40c030b9404c207080c0e00c107001800040401c0c2c5030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 594799172 1250 594797922 594797953
    0x20a0c0308120a18030e1201021306110a12080406143108030103020f0402070f030e1503090a030c111309110604121401090b0a0203070201060602071202040f1d 70
    0x40040c580542a8580343d81c0c070800510640c5622003850f0149031a0346d0300d0b4902c00001d40003840c1180058400e610010f500e00c0104412141c04088400a40f9001d84000c1d0340401c20751903050b42e0300e00420381c076010390003c2486d034010020707241c02c40d010704400905020000c18160940340151032990170b90301d02d50310b02c030f00030a07200c416043c10300c5800d441c610340c00758182c0d01c0741c1c1c0600060100a1044982000740102c80c0c955605895956400c44410341d0407080c2400c0140641c40600c40c0103004c3d209c0784110200b40104a02201d0043e04428010f018044280d2411240724032060021110600800218805c030781d00c8115201a400007200001100350740c0b07103403c5d40240b40313044080b4040c01c0180000c200d00c844d8031b040d4451042d08012101d0303a03540342d81071943c01069061030083c41e04074140d050004040495024500c074501c1c58008000341500c40c1826030350b920091007042c24459107007001c040142002c0c0c018600ca01800e980228600b490300d81c0443c45e400e8419860a8036500c02071546007080f4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 594800422 1250 594799172 594799207
    0x12060307150c0b04021804210305040f12020a2f0a0501020c120309131a04050417071505040807051002130e0402061c0605010905061306030c020a0c0308 67
    0x6141944030725101e100502600903665400043c020286010025040d92036400b04003544d001c98054200c800e00c3c00b8904004902284019030240b5040501040c0304079000344074403405103401c00d0702480010300650307a011108102c0c05c440c00450161070200c0340092000103607080c40d05080b286901117403010468003c42d61101e09151442020421820001c0303980108540703040e0642941c02c10120101d5501161443c82020794864204000749101000d84005511044080c00b4208440030492000c10802040c1e910544e00a00140c440d0401e506112181800810480e8858401440d071501d44017100e200b01c0700d040740e00342e800400018166080000c00d21024800c00389503c011401c002c803005580409041b03d00071040c8070301041000ca425951a0070680302e5420070a1000804d0251401541c40503242501c200c0d400702e030000c0740100d01e61070310400350780c42c50400303c1074402080e181140480250008541040c2540202e001d030f10003041c60048036001550194110581d19490051804080e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 594801672 1250 594800422 594800429
    0xc0d1a030f070317030702120307031a0d0308010501030b0a08010518210a0f090803070c080d02030a1403040c080a06020319060605070b0726012d0e15040212060307 72
    0x2d4001d600300340000340d00f400c41d0745400c26144011070344a40e103002e8143e1410016200d120341444003c0700b0414965171640080b1000c510041c8010502c0c03003030a0034825020480c48005020440f045e0051045500c03960141201c14801058282c02c0d5580307422082c00c40780f05898003641c4a80b030680c50381c1c00321000c20000c4000c110310303000441103503141c21040c00c0b54001d0006003410442d80f8049140c10394402d603a040081d046c00c40c2070381d60341d40c80da02c0c000c0c1c0110b90074400c0f40c03558055410105070307140c0044240c4201c00d0480e158a1500000328605200ca0b41c03000f08111031405840e580810720300c00c100134026816214001c0141e40b801d2603030415007a6603002883c08222400d0400500aa60f072207419582110b44c400c07164032940e1103444094651803a0003400d2407104130b49c0c008140d5410745141d9298125592081440c580d0301daa1309481c14460391010601c44241c0c0020380c10404411030704500c07a84407842c00350340c0010701d0410000800340c0c3c3c40401c446484a02481c1407081a107000d00010000703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 594802922 1250 594801672 594801703
    0x314070b04020f1c2a090c120506060904110c01020307020d112e111c1a0a030f03050c1e0c0d0323070c030501020307170f0f0c0d1a03 59
    0x20100d4180301c4e003480340c110311300100030f402d021486440c000002d14420124401143c0e080090700e4407455554000c00e400c070307016030002c0d0000c0400703806084244911030180401500da1442d08008405020142200b04140100240f080090030032501003880a1806407200e5405072130080c2c2000001842c0d5410318280d0b0049070089003c90b1004000d0420703055203118800503081248000440410042c507890000940c0c5010002d55800c88030345021380d81c5081210442c2c10002e06280c2c41c0c244400140307a200c2a50007002550060020071000c20900c503130184645009490040307070b80d440c18100540c0c00700344204a91505140c0303100510910202517140415102151075030300d19140101007059900302240d402c00f030305117003841d01d151080c21900e070250441010b4a8069482c0b030702c24000d600c00c0340c4803130014145c0b0008d407015400c036440450291a00344503544050b100c005000c0c00c0c120014280307088003103040004141d40c002d00d000381e2135440e0044034180344a040b40350515041c158541480d400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 594804172 1250 594802922 594802939
    0x16090b09010f0305130f030207050102010f0605130b0303160606090509030328060806090f070e090a29090604020108091609111b010b0a06030605010c0f0314070b04020f 74
    0x7039a01800d01801d80800340b9001c140ea40ba83d02185c1c0c02c861410001500f8008190b11b140141078000038a0b8003111420f134002c10118142d051403104072070090140c613900c0b05016003c00d031105041d40010074044c00040035a840c00c3c00300d062518100541072005c4410603111401080300400d51320607664058402c4000d5850b5291020348000c2c071802c106103090041a90300401c3c4076440c040d90040c0050180301040b1407050400b180d07002c2c0e0311700340b862092229104080000ca80c0780b14401c2c400b4000c440480c02490007841513914103c050176441c046c3c51303a8400d038004624000d20411310041c00340340e0003000b601c2942403070b000040005a0003026104140e100138186105401c000c0104001c40341110400941c10503465641c0c1341d64400e500842100030701d44456601d0069043d40034600b942002c03150f00085594a140980c1940c02510806000c90400e80e018000b084d80060b20802651017440c1513160b82d1040c0094881c41d0704a041c007951140c2030f5408000460800111800c0b02100c00c80d204e10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 594805422 1250 594804172 594804187
    0x61902061e0c0a140d061e1502030a032f070507050102120409090606050301150927140109080406120f2a0201151508130b061507020916090b 62
    0x64003481688410000c00c0f2038600c0108400d04e10205407040d080380c0940c148846540e0700701c1707141d045441440e81c04485000600028061801c1c580b20301c41c04034a6005103040c0800514103a00900d8001c415248440040c1c01c2da50201d400ad00c000000038000b002d07035a44454003404c04038a80300d102d4000758195408041c1d0381740000b400d502500e0484d42088000b142c480c1240c903206000d0542640f20175059824500c0500c000310038072141c1001c1c1c550340c200401c103920f01c1c8032074140219a00c01007942484440d10480300803405040007450760140716000840c42d052103a41e8001c041c0e01503440003002072002c84035440802410700807095404000203003032001204042c0410b4004452101c1e1041c0308a080d4060b01080f4001e4018848805107040c1000c0080c1d9282c03040c1201c0ea0040356268002203210001680d0005c24104a81c5015000415103050307030780c1c04003800107404080c1035000e82618140039501c0141e40c1d01c4d25481c03188034480200c0303201d600c811001400c00140c6400200c00e10b8001c1c072200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 594806672 1250 594805422 594805441
    0x222a03030206090f1b0301110a09240507021e03060c0d06050102061509040213020d050105040606171501020a0b0108030c070f12080306040b04090c14011b11061902061e 74
    0x1058005d080d200440c98400c00349000034018200100300700004c41e40801e0385020315402c0800481120111400c07602d0400003654094504480c42d1100310100c0c0052110f00054106004101413000c2242d94000d4140d500c5800685044400c5641640d001c00005040c800350455008400040c60280020b140a00b084405c10f0517003030895013214001c03518003001500395640d02c504112060465107046544070345003000d41d00074190901420340118113000d030011b2858402c64180346d540e00201c424800d00e48982e000381d240d040c0302c4103040d4114407030340c503d40d80812500c4a8490007803051344011541c40c440101801d06041d41940a042001009001001507010190301064a5a401b100140c0c1d240c2c1c501000400801c0090036694105141035000c0341007188403403025081d2481c0d00302511425845000440f820300f00521044101c0681d90003030300004940551050207440c000b8021410020150614801e18030440060001a0b0052040c01300140700090030000c40395562400440c00d10f80340804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 594807922 1250 594806672 594806683
    0x140a0b0a0b092407050109110d260d02120901060f050d0b070203070f0503070b060427020d0b0916120803070f090509090307020a0509222a03030206090f 67
    0x101d401003141100d14054180d1114078421000f12070103480c1d80720507090a069008005110003207076811010200502c41d0724100314000c2e802e991042e94600c0b880145100d542d40300510040c803076107141060000404403405400074001130345032015026451300c0c29038103032800c2d5010341e404811100d0740318406124548070300b0103d400807034200c0503810340750f250640202d00d98860288082c001c901900d03440410090040300900245000c2c40040350b6907100d610801045424100140030310310412056035800701802040d41d2400340c0000c1c000d00ca02c0c00786803181c0d00560300c00c032041580351b00280d840d81910841100d441e4043c00c50800540c80954081d5251882423002605400c00d0200c54411002028800d0844201511015082c688030b414041480ca9072a009104224802c440f2588040b0f098103010b21000c2c41842c20b02c0304140c0759900e07090f16001c000000442965480c030301e00f90030b10703120810354000c0c4100101703500480e0082c0e00d1824000e05240380600f41605580101c80200c0c69190300080307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 594809172 1250 594807922 594807937
    0x2c04030509062506050403030b03010e07050d0606051302040501020d1107050108060d0f0804051c0206030604090212010903120c030b03070e10030c0b090102070609030b0106051804140a0b0a0b 84
    0x180c8a03528503d010041c01050f8003241c0180d02d078482c00c044482000300a8004034080c52003034030280301340d10f02d0904145c203a40d441240b0b29202d40c4030240030005491701807036031280e040c090b4900094854484010034180444040034030f4449800040412403542e04009100c01c4055a24141c01440c00b0752070120f0b00c070b01042c1309403810040780d000418003c3c2d40700603800c6052a0700c603903203500380311161400c114260828454640b01d0110701c124503089481984510800340d40c018003403851640c0359070821004002c079460998100c0555141512101c0c0240704046055000740c58141080046000501c152000200c500d02014207000403c02e442d00d0014460040d510301212100f07076a90340600350959040365500142c0302455078000091280c428100600740380000ba402d85048580301c50b801d80c0c18600034880104565002130040041d00d00c00c2c0c0182c0044503055035100720901440740020191400a251203603182101d80a0012895051040200c0031105407036070300e2268541081c00c04075028002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 594810422 1250 594809172 594809179
    0x10c090b1c050a0e1e0c0307080a140a150f0507031413080d0603060501050f04060305070e07091701050a0b0f010c020f060c1507020111250204090501062c04030509 72
    0xc040780c503040f4190010006800001d044030034000c0c01d1318420462400d07189902000d40940000c014250901107182c1050b504000002e003025501a42c42c9071b101245401000d0301170040d001213a00040c0c1312035030006041d180601c0800d400f0000040b900c1200c030050308140c140751804084018016800345da065006412160100c484641814508500d128104500c62250320b04400801008520b5201034160350003075648218030002801400101c403254040500207a0021804109a80d180f07a12076034050035a14124418907a00c0c8020305954001810440c260b9464004001d034220ba03c1c0b041e0040400105c604485481000d4006000c040030740c24080d0050f600f05107000041e80300d4004403039110012001f2620074000702e01a00701d00c8042607502c4001075007400d0301d941c079005400d03068454459002c21640c0b00c14480c0c1804415008062000b241c02a885501490120320288103c000411501c82103100c80303490504070309281c1d1710b0091100141c552744070510022a40c04401e0fa80201c00a6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 594811672 1250 594810422 594810431
    0xf0709020a14030a090b090d033210030b1005030f010605010905060f21090f0105270a1401200304080906130e0703090303060806090c130f0905010c090b1c 68
    0x403004c25015206144014103501030400038072400003c0020829080c2c41560341c104070329048243e01e0142e0201000343c1c0482c1141c03c05c1007c40741034000c01025008003120b11084840c0d5681d80c5c5006e5030b040101ca484245882c01c1d2000c2015080a00082100344801c2c0000c11445052200103010f89015000f0f050085001051081c42000c2a408440c040d05010442c3c40c14500c4603c008010070071704070f801c10003600912084c820700450500849020724400c0c001c0826034601c0f00090f4800e2a503202d01c40c0300740d1145103071140104030132045012983d402e00b4004176030320030712219200141c7c81401400100890400c10000400c01d07900c01c0e80e9003010119011541d40d2601c0000202c0354101c0d030407805c1451203120611415581503480005c00500c640c0b020700109a42d44100c0743c598501b1290119a0b030482400120030745400442160f542c01402d4000600070311510081003110100f02084030b09a55a000420809030400040001041101600d174503185076501580209101e4198914545864 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 594812922 1250 594811672 594811681
    0x3060103060b07050c010e15030103020108061807110c010c08090616080406080a0b0d030e090604020c01230108010506100521130c0f060e0d061d0f0709020a1403 71
    0x39030821070060060982107901c1c1d950703600380079442e090781010a60111304100392899550504008005884c9090038205055a18540040d1038600009003210b82c4128040491903001410042d001d004d403580d950741d508040782c013221480ca009840310700507041c00440300303810001500410883d05100380507035802c2e8948451350901c0d00200e0200f02c005140e50790100f00412401d9000b44110322990700040140068407000b414821128040714000e40040c5d18001c400885040c5100c00d2600007001078801443c1c04040303100d40e400c640b007141086001e44003560407000350f9100e11075410301500d038000c000c0245007082c9000841001c0b001c2222000d02102007050086194030761040004042d424900c00010f06d014003c43d600020003c1d02101d60000d08200425042030760f8024400fa2401503e6400f4140c1c0541d0802c8901d100c0c50302c0403100503071181420300902c243c21505039082008074000703184a084800c025800c1c00441e0304a270034664414003500901991001000d1031510f07030018200e03942c1d03c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 594814172 1250 594812922 594812927
    0xe0c090f0a080f1c171f03060606020106030204051006210908040909060e062406070c030f03020d0c0312090317010b0408010c08010f0510050c010f05040201140306010f0302030601 79
    0x350380c0024620b014103030f543c060750007012407031041c0d680500300d18000740860b000007604c00c04000001c20408101e071100180c00e07007085c1c4d82d100da503800100600c440c03496a030742e40c5c10701500d01c02c0c0c01070b00041c0d4446004000310f007464052560010b00b81c424498000c0c0c141900189100b90161744001001860410030031145074591041002c1c5801140f10b235aa1500c40500380064003015000b216400d2401d4808e5007000d40100d41c1c14010411007092805a0114001030000220304e02020740e4805800c000c200c0c0010740b0341689100641c41104800034920150034080e0514030781181c80800c0c0a4078614160009510a080260044e605d08000444203024203080f9440b81c00b21107110010408003001113110700400c0098400c44200d03030028072442004450880301c40000380700310ba01c114040a400c0c4228074010000b05685003041c9444d500703101c00d0b00b01e8642500c61090f00020403a90f108180000d40d6170002e0b03e03007031920180c92810f01e0340c20080c00080c01c0c1c00008900400b01a40071000c03851507031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 594815422 1250 594814172 594814189
    0x150c0f06020f0f030f010501080106182d030f020111070b04052106040506041202010204050a0b0f07021c020310020901020604110118091a0306070c0f0305091807090e0c090f 76
    0x103003840c0e0b60507228a4102c00e945c001c08800c0c000c80e0301240f044400002e903184a1442500c4100f4900400c16020340341035030011010a1003401c2005000c0c140310040841c1369021558002503001d0f82d08491201d070a40005031000d005519840c000360041603040c0028103501003190115842611a40f84595100b6180d034805090111507110b41d00030041030109004d4000f0303610f4010340c0100b0202844980d4800213030308130710030381c410141c2201101c0020414201c0032000b4003100194100964505011607000130a140981c00014154101c0d01a400d825420104103280c000112900e0840c0760140c0a40040d60f90240100001c1c05803441144608507a403003a88850007950740d0461982e045901c0d103d02d0300203001414107054940300d00034602102c03490f0002c2c842e4000c18254071140c40c03400c003640702c4901113841c6410550900c4000c00051100d515030001070704881d003a90f000d000860900c7d02008000d20003550010050880342e87c10301248545100031602c01503000c8401500384d80c2c00710045140d0b50b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 594816672 1250 594815422 594815437
    0x904080708070c03151401140919020c030310121a090f06010b0c16121412030c09030f010b1302090102100213050918060705030a02070516150c0f06020f 67
    0x1042c0f030300e000020880300000d0700f1940c0d42800001d108880c88500a1515070009200790641100c1003109240d0320305200c2c0500d50400d0850713a608044a00c0342d00b82c802640d10001d014400c0354000000c000d92070140d030404001074188418110a82c4509840e44e160a200940c2c514059011640101d918564200701042101c01c03690140e9110303607500e441800c0c01e6044218844080d0090007814505000000400380c2907404500110035202c125496844171501d620103400e4140c810324544400234840d681c080c5104540480e81c55903501d00c11307000d05041c0204041241d001d41e0501801d00440c0e61081d80d0600380c0d0300309640c01a1261035540040b403a181c2c03006911404244002002640072500450320b0003070b5101500e41c41c109454104c0c0e418403801100d00c492240b034120700d02162110344580010f40e04040144c01c0907081020070b80742c403400c0203d000d94149481d04261420001241d114842c144031010504003a07140c080382c0d4680c6424004c003410024902075002802d800480e15040c29038844 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 594817922 1250 594816672 594816683
    0xc020114010e07090e16140705010e070302120105060a060f02070302040203041103010518100515060a0c03031107020d0b060301060e0a060f0b0f0a0c15020a02070e0c09090408070807 80
    0x50703503910b20307071142602c2c0c003a03608a00040f40e007540417401140d40c00ca5140a01d50441060414207a05032080700c0956038040403800c174400030080b00d408a402409118001c80380000139100803851762042000c65280e842e181000d41e410242000720940c2d444058400301c074802c1c140305001d2400404100e0130200035800c000d40c000e02c08410300c42485591050010304640a8000f045952908110004100786026031400c1d294800b2991941941a40e0006034000b0f03075204140c40700d00751030b00002d030103a0808071114000401000c040010725505010b01e05041007000312041c0f40810503000f007046164525005844090710340d0210303155490940c04800204014241c1c840d5900703101c00004007030003217442800b0f50304044c4070011038560140f02c2100c44955288280d68584a1000426120002c07505815146c0d80c0c19903607103105031442c5000401c1248042e50151021758100006c0440290010308035851002c4c0c05d12a045041d2150855240c000d0b40001583d52650410f09d0508180e224a0394010309 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 594819172 1250 594817922 594817961
    0x6090c0415020102030603010b010309020a0b0c07050d0506101517040c170307060b010f0815040906020307030b0a1a220b040b07060c14091c060626010e0d030c0201 72
    0x2078607030341076020b9401440128000d100901e418001142034032018140650f121a038490200b100c5c4402000400142c220700307058900490760703500001c00d00d002c840000d4075960480f00070000300e0301640003490090210744642104145c41000d0003080b1304c0400c20041811343d2141c001c03500344811003040f0001481500358038100380c0da01c240e03050303201d1300200720480b0380c0e82c1490360101e100c2d030062402c580910030b0b0313a0307038002c3e1aa0b6000c000018114030030302c1580c01c2541c41202c2c03000701e0701134001107110b200c450302c02242c0031901000b4041e9206560b800018214400a5034203200d0b4181c1b01200d82c02c400074801c0705900002d504404446c0601c0354171514075100009800503c442d10b52005d0f05601c0d0042d0403c1004c405801000c0d103005041701c03e280c0c1c1c04801041000a41d242c01840321082d00c50400105900c84005d81d65002152500d400c4440d20710f4942c20b174141e0340c2c10a81d03540c0003103601a000a02c40300301c4070060299640c030034800c54000e00d9150a8484207145c401d40c064117a842d071042179000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 594820422 1250 594819172 594819209
    0x20a09080f0706090e01180903030b0a030b1f0506031f1d040b010504021e0a021603050120070308061c080a03060816060503151801270e0606090c04 65
    0x9640c2d6074140b048401080701220000b07511135411084904035503c002040010780a6903014500401081d28200e0616968181d0030050740c070b544644801461192a18600034200351704a4030901000b0b0346607034000f054042e018407003611000305481c1c01006c0c20100700e11246200c15407913141c0405400c445034490700380e4078503070700780700b00c4200940a98054003640d402c50762074801340302c240c6c49013583c000c40c034917460001c4940c040115402820728080b81d10544070b10031120703441010010019402980d0700c1c2c2d1500c5048050081d01d4034420f03511007540940c1850b060b41940c000c1e06200307000300300d04c1c803c080e41c0d003a25004d40d0b0750351810403085520010712640c40503060806401000e00b4041d20146105030a15501c0251206500d00250754080d00c403203085942e1036007841482c0d80c3c2e0100f46904008240440003543d5040c040c42800b0b0700b03001d5038a0505180c0140c0042150340c00104402d503650621025035401c00010807040d400240075205461540c0d11100801600c0c8296802060040302a46601 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 594821672 1250 594820422 594820453
    0x4030506040f020906012f1c120c020606011d040b180a0507020c0a1701090c03080c12040509070503090f160303080f070e010f0908030a050931020a0908 67
    0xc05002d101300c0300500c0d591164801181c844121030342580c24070200b4107064045d030042c0d001c006111011101140c10400319180031001245a51030b400c0041040b044189075891f40d01d001e46848402a8130003040340f89444000240310905c5040d244000e5541c00000201c42c0d2240e07000140600030150021419a0055120b034000c20407c680c0c5100503840c0c40082500c062004ca074155951030014800340d0403a05181450185500001a4035001c0d9a01c08a000004140300103010045004034807203a281d4144080c450700b82035007894246141c080c1044240312541d104084907030001d19900d40340e80c803641c0d500301c0603250102500588559101e450050503910f11301c18044825203100e540c43e142940c641b03402a100545c4140c0e0f04174081010324004a6495108003a907084441d802c4c5019044113640e02a07541c06c6034050031501703000070400640c0380001e040408464200403900424944a880322428400c2480207950482c0c548c03030380010341544000e00c030750b50200290000c1015500603070ba2282e2030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 594822922 1250 594821672 594821693
    0x30c0a12020f0316020109050c2b051c0e100f030b09041101030f09020f240423190515040305060f0a0b0a030b19090803070c0201020115210203030403050604 69
    0xc091404c80d140341604641c910601481402d02d91060042600809103410840390804500c2501441d0940040c51650b034802e19464242c018080c0d809001c1002c0e01010000f03c1d180070869007424085105101d0f020f54a40e071490443c501242d1508035132001c10701e0f2044000d01600950aa0301c94a12800d110910407000c0100d10f51807030980b810407003c0e18070301080050740e100c918045e60000f034259140400741444d8607821501c1d2850410b002822064004610854010390032a0055508540c040012061000402d508050088810b200c6d01c0c250031046270101003080c018107014201060200d05090b25020a81e80515440b2013580d40b01c0c90030240c410610030040310185143d50030800e28908900b011074010068070703000410131000780d13034038140ea1102d145042c60324074040c0d5841043c000891401c02c060f50080d64265503601040140340002425500008640004907050341c0d4200a05050002208038040c00140c0300302104c80746000080c110300a03903002030a80d0090400f04020003103407030b96 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 594824172 1250 594822922 594822931
    0x9130f05060a050d060b0307050915210a1101030b030a03080f0a05040c0b090f0a0e16080106020309041e0908030714040302131a1f1211030c0a12020f03 67
    0x60400441d6111401c2040c58266441075580084aa40b10381c0040341a41c0c0010502c00c0d0050100c2c1c40559484000c95844007045545600c580c000425070131140c507020001030b07124441950825186690f19401c3d03070329440b407a00000d000c4500f034800b8806a034082d0b049410300c560020b003a51403400281c00c020b482d002c0d0841b20200044100300014120000c0303489071038080c907081813525104030f04020101125900c2881c0560b0300c07070781c0040900e072990340b16040f040140650030092084d50610003101e100001081c1000803d215070030300140312540e40003041d2024a0401c035000702c1c0420441594078410300005001501460402c0d02c80d00520802000644c01111107a031040c0000c000c1500000342800f4600000354040410740450705c82c1e02154201d5030700c110402031590780100e004000a1a1034100441018058100034244001e4540200400c1014208064203200402000a00c03a695103c01080058101004180c05070401d03c691700d17030f81e01200412021941c034001d410100405030001c45 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 594825422 1250 594824172 594824201
    0x30a060b030907240c020105030a06050910030b1e06010c0f08040609060207080c03060604051806090609160302150a0519020705040c03020c060a0b271608100510050913 74
    0xa040e00c03041c05004654802c807110545e6843c541d034000368011500c5030b0024120b429140d44034080842c590307803520a03050013004480c0c20b01e82054554508145d2004c0010b0106442c640c3d4099200d0040e0101505160b22103024a004600c0011174901030300084064080030f0f2204a0100d80401c0300c0360000c10701815039101d602110000c0c0d07134442c0c2003580c80a01c1d2481d41e4064003c08049462802e00d608001c0d0018220350521342214420004e40d0f14040b000c03202c40040380d000c0d005200c40c101060000c9000071408104413258282142c022507105800042507200c603420010320010315920801c295200000c100d80800c074149443d444c020b40d220254000d51303100da880d0034100d40800c0e01030300c200e420b08100c5602820255a403920070384002c0001030718007a000054003245920079201071000d42815a60b0300c0c520106420700c201e00761120000c0c51751400910800005010312804060208400c6400490b50351000c500b031060700702e0f294016403204541011401d091081070075410780140140180c0b09 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 594826672 1250 594825422 594825449
    0x13110f04050901120c0612090f20040b0d0b04050a141c032c01021b24071407060b100203070302060a021303022403010303080108071415030a060b030907 67
    0x141d02180136821602030042c90304030f580e102044440d024901142c0c3d0700c00b030f0150008640a0316200d40e280010030803c121078020304005042c60729046d00b0081c040b01c0206581c02c0204000c0314003c40c00c50700301d40c00c001d00007041e224001020000d0401205081c2c5500507003448003441300c80b480f03507a2010713581c0101c480f6109001081710340705e20906c01c9079960031011841a0350091010030b05000040c5884008506540801c50800da9040004515030302c0b0928400916030340110201112150001c018825804444202406003841e031000415000c0c552a0404d0356032686946419401071811030010383e0030241101d01074103d43d40101c054a01c60707000c2e8098820030354542c0c04a07c200d2184c24065001085004414409410f1251440782815000c11101c2e480205c51a90b120f001e030000d03401140090020b01c014005d0f642e0501210000700510485013010100d40d41c006240500c80f82801c9060450100009100350602c0d080703400104040040180e0383e042010590b52124403074000c40014000c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 594827922 1250 594826672 594826679
    0x80c061005043c05010f050f04090f0b151f080f040314070f0b09060402011d010906050d0209180709050a03080a20070605040509060303030f040213110f04050901 71
    0x14002c015041c00c03115140d001c5040c03071440c40540d0143e84081081032600d4800da07001030301040d104180c0600300ca03c0c075520344035103490200501c40b403000040900407400d212001e000a04e003a601614201d5200001100c16a68071230b044001040240186500c6803003040f010340141741500c586050071505a50700c1c2c510f5659480b81c1c60b00010301303a40040020740c94185001600c003036100038101007407094a40309201002600c0e101840c41040c0c0e841440c540224050104660304940d000c420f5501c8034607640046803000d070000c0e11385001da205440030700c0000115080c10000b41d40c1242e50f05d0200500901041003440d40b03c80d030110040721581d0101d844e10344086104d00d4002d0501080703a900c00441882d141c01590110368109003241c007039240d040840701a2680c54018030951019040d507569042e151440d1100300304490740007401d5117009030410814002d5a002902c2401d600540542d01060031030742c0010200300420442c85541199070300801d0802154810a00030000c40e2811141c4d400166213 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 594829172 1250 594827922 594827929
    0xa140613062c09010509130605090d020c01140a0807090503100606081b030105150723101413031e0504050301060503030412060b012a03180b0d1107080c061005 70
    0x5482c4074142c1c4480650010030440c9008290301d540a0203544d00c5507041819661502c0550780117440d0010700ea0005480d0511941e41000707088400d001c01d18081801540c415507106941c80303255170740c200300018640001d8210f40500c10013401410041d08645030580351000302802481607004030ba0014030f11b0000310301c0c1e00c400101c2c244040158201000c0c59a40f0780302c108040c0600b50030703130314840c0322007441908081a540c890400941003001140d0507880c0e1009512810191307403540a95045143c03a1488004001446c807035988841110300355103516000b8241603504e1210000c09a1119843e001d101400c20743c014050800c4030010790007400503d485008050f140d010780d0154a5207a6144c40b070030350100b60036070410a12070006040c00f40716203c0300004000410500b04a010040036036207642010158031807050401d00c90303807002090f40c0301d0500c120b072542841841d04205126846242c0315044482c6801110341040d48071070140d5980b810048030a854603000c40d0f001e00c141d00380c02d000103030f00e04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 594830422 1250 594829172 594829247
    0x60f070203040f090917160b06010306150e0109090509011505041404021c0204021209060f07020303070c0809040204170d050703140c0c090420010504050a14061306 72
    0x410f00c1d1052025542000e50600041c8030401c01a03440c80710302c04010000c8144500140501030409001c000102c4103400c0424040f480a0040da041610302401000050b003250080c408205681c5045003070200b000c401261809216000398017154a810240480a40158030501d910760000205801c0f50b41d4440c104000c80f152901c0621044920200213401407400b43c804502d0350003480703115050034240e40c02190807a00b01111042c0c0e01000d45041c042a00c10800686034000e01c15440c10407585400d140094070fa0102510007c14080002100020807542109860041c100500119121680c514003c2040845091030702003c1c018402119201031061080351402501a1079050340300c02583e2005551743e00001107200b0901407801031050f41d42e0b0314089e290059006013010f048202c040c20b00c00f21815191200c5d00d060000c1008204103035215880248212030100904002d10b500701e070080351003489100740003085022024000b04c0c415400c11100b018000c80c80f00080e40c90400a0080700050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 594831672 1250 594830422 594830429
    0x190209191a13090203070c050f0c12030703020714011101240f23062a01050105100c060b011806030606090e060f0f03012d050609040f030e031e060f07020304 69
    0x440d0424018000c0f007030315400841d04440d01c2d150540c1030884545403e424800d03c041c04030342c40d40104044603000e05d44144000641ca80c0300000d03525000141c0c0e80070b962080140314a074842d00101c1c0000d01c80d40e006941c410141c5150b040280854500402b0348051468041175078500070909400103d1910b01d07100400c030036680c084c000794081e0803c4140f417105000c0f0003d04182d201700c08010030700300c0b076151480304158451843e0f0740c0204c0d80340c900003071425554160071480c011440501401100c0d503010180c0d03100d40da046040003070310b6040040105e038601180078624140c012899400075455515910041c1158100e40d1510450303a2031310b0100c000c2100540e8250362100410f6036407285482c014207039028880005000042201d06a09000c5200d02c800e100a0108010b0020b1010345e110a4040c0d40d520103003c8840401928050343d4450f1a44100c09002d03081103a800440c0d2803a40b010008051031001c0d100c08a0f5007000300d0407105544a80032070f100b004c9814000045400240008166010b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 594832922 1250 594831672 594831697
    0x16050a080c0d09140102030703060504020c071205070b0703020d0f090308030402121e070e0c0a0c080f04091b0e0901240e130506011b0b190209191a 65
    0xe07444000e2809103030341105030309a501a5492107044002904c64075140b4059002000140e242e00c0c1c110310180840d8655030200717006600411106144950101e409000c0d15111088400950755504080e49000c403550451118030200244081c180764000030140c246410a41d9007800352402c0c40b42c115a09000d82c44002c00c1c00c00140045801880c00d10f204103100e15081080b42d880d4103c2c0011201c00c429000f47c13a00554001c10700c00d0000b903102040c4142d001c40c540545ea403078044011002881d41080403800741101c2d202042c3c00c1c842e800040100d400070721340203030240710008041802e0140d6141e080598000b090740641c2002c403c2c10101d4009040300e04050744401420600c10a404154215501540402a8007100d0b44510f6503100305018a00903096000036079450554000b4040d921080c8101c500d298600091200040400080c03070303402030a13062880c0c034004100c40200b0103030060050b03941d440800680c03240c00c0c1490708802e420444200b421920030340302c42c0c402c0c1d0501ca88202500301c980c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 594834172 1250 594832922 594832937
    0x21050303040609140111040512011803030e15010f090c02010e1c0212030906010807050d080702040c03060e09060a1a030a060e0f06010623041401210207050616050a 72
    0x851201e40c4200c0b0075500900d44c04c480303d094080c1a9007110302e1035070404140710f00850140041c1c10141900030304030404078000c110440349081ca0400c601d0400600800b0152500304c05001070f002400f822600c211041080c01195850b8461800244024081d000715185000c84110100d0b1050007020000032041004e010003040710717a500b814005840c0500d03402e62142105c1d25400d801c0d084029445840400003034103465041103005818052141e015520640341c0c0c00d1604040b50340002120605681110002030010f90520150082c110550009510041d03010402c940c80700c0c0414190b00c40c0181c140100441403c18a0003c210006075115030741550100d082d00c000a906640032440d80415030088981d4081201c030000d181c43d5090300520001b5245140900040c4540c140300c51150b26151042130030a81016040710b5090306a50030f107170400050380d00c002c900d42264a103003000c0a48400d4255900d41d40d5040c542c0d40c1d004182d60361406000ea141da070040c0240b1400c1601c50f001c507655100030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 594835422 1250 594834172 594834181
    0x120b0d030e04020412050f0105010f0617090106051c0303050a20130905040305040e010e0103030f030b0f041b0206060a031a04170703080618040308010b07030507050d0921050303 78
    0x107a0003401409200d400c95402c00c0701046802c4c190030041045c501c20402007240100c1e08000a00b59a0180d01c82c0310076080b03901c02032189a4010500340b8444900c0321404078582d58172819540036290550000b03820580301b180701b501a9800c0c15000b0303441070103a1030901c80e0b5100c01d25003204a03080380c69908404d8000c0052103e051001c40014036207180d4030b1007600d849035102d0f41c0c00b80454500340c0d000c070041400042c4c01c000c2c443d0460301d01c90040844803040c442941c91340c2c50140c401b00d00d8890060401d0741d110042d07040340e41d0722524080c0c0201e025004000b0441c0c21103d19a00000344600301c4094445d40f00041d84c2441c0040711103040d0380d80400d503140351410508030050a001e0191085034110302c2d0944d0110003042c5400906101802543c8403003040c180349080c01a10f0391140d116081e1115114100030120360040e40c128112460441175075a607669602302100c280c000c00380001d00318010740707164174011a403121798a01603d45885a02040740c800d0050380b034021041c0700008103150420720024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 594836672 1250 594835422 594835427
    0xc1d0702030f0714010507110d050703050d0209190303030e1002090307090221161b210c050105010b0a0801080d02070303030f0e0607080a1d061621020703120b0d03 72
    0x43c141c03030b0b02c03405962000304206100e003401e50313034221841c0c00069000d00c90201c80501c10030824006d5401070a000b85499810340340207155100e4000401d1307070250006010702e0030307445035092202d03424400c801c00342c0c0f0310381c903840d0003000350004410801c054440c9120580c101c10340c034801c403043c508005004284081c5040d1104c0041d4004181c14050303200810086902c090445032141c1c8076a40c144002c1c010001644405404010244d0300038845020442044c2c0004000171000001c2d040705039510482c02c80c100c2c00480e0b180440300c01c01850340d4241400080c072405e8217000b41c0020344880d03e0318030140e0380701c0344041d6a80420501c2800180e00013407003007000c030b406640045c80c88041d209010074018480100c0d070f480c0400503219500029400d40c10061608038901c240e41e81014840314805d16640c001c09039994030340d0040c148502548042d0f540d80076183c001c20108003142d001103003070320f24a140c0800070002900074080940216051032403444646005205d0b000c2d4003a4020210070403803800b078608 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 594837922 1250 594836672 594836677
    0x30e011107124b1b1103010e060109200406031e0c0e10140a110f07080604050607020d14030612060a0204030611030714071e0c1d0702030f 61
    0xe0006100d4440c8115201142c901c4860041d1001d6400500e2001c0300c102c05580400611499000388910f19a0b002c94660742c04040f18800e800601c48078100c812190a1220402200c5940c1641c11b6207041381a8000510101d080c40c1200c0008034100980392006024091a0b0210511052200300030002405014002d0b40460001040000012116000421084101c032050300010011908810030300aa0789414100b140c0c4100c0e00340340907003070211400c0d04250b0364000c01c4211824000c080445154a180c2008100c1106810300102d803c125502d607a0640c0300d40382a034083c0c5180c00b0b0380000412141c00041d2070400e2004561350840220101c0130220203540014200642c030010004541022101c03c00c20140240010500103a81314514034008041b41d41020302c01007808001c7c820482c1240c0c01513940a00e03001072810080d621500b0341b03400e8542d05580d69014486081021566003417107601640700b0260344840d034001040c1079900241c110076810440341c03500145c1c020425849410000000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 594839172 1250 594837922 594837953
    0x2190309080a031e0c0c0b1e0301030c0302090703020a091202030f2e180308070c0c060309110103020304020a0b0a090b04090912051e0f09100807030e011107 69
    0x10229101900d80c07550742d05005088005800080c502d9038161101d880303c0010001ca200103050104031040c00d42d40c0c03e081d400040c880d0032061070303000c00e04070118503048038000c84940f5400209540c80d0307140d14040c0c015009a00041e0f000307045038070000740c0c414080d10850f10340100d107403500c44445180c1007a80b010807191000c22600344c0078681c10081c040c00204418010b07103a540d440c554090701002d2182102d140e01054503144103081c450203403030404072200651032454046c40c1c0f07511944c2d80e90605641800c10b00c04010007180e2001000150750b641688543c9103180b24a400d20078880c80000110168002614003035440a620101000312000369001083c0d02083c2c1c0c01c000740d80300c1d41c0ea41c040a0380c0e001a8804000b00341c440c00c4440c03c0002c0d100391420f800b83c0605029082c80d0750060548000200c0e950015030030000090201d80a2034050140c074114200104050300c00351181c94018809030040d01d00d0404642803007141d83c0d01560601a10070810205480d02e800c29415884003c2803902484 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 594840422 1250 594839172 594839177
    0x804050409150c0e0907020703030914030106030f06053c1b07111306061b061503110109050906012316050313140d020d050705031f050901020a021903 66
    0x100c0031000b005a8003c0344203200a640742d80100c8a01e0000384034200d00014080402c54210090510000c0d0304100c4010a82e0040b01c0d2011490500501181c0104407603003024146402c5540a84d0401c007803504064400d10600145224400c601c0383e68850303005100003a40d001001120203201d010001c0000c10b5404034211a2083d811103940e844001594480c05042d111340c1402d10030403480c0c1c00c0c0a64a9aa0310346100810004140781c000002d105a0040c80490614050036030028103210140e00116000c0c4000950740706682c2e42c074070349040c448818004060100f100301800040d02e1803c0c0e03050b14822030042e15107a902601d00d000b0748544e05c0d40c5c040e4580702528140034040110501080c8400058440c800450f55010070401c21001e1805030b0784020300104060000e0802c60722560b4080400a6050b08d00700c07030341000c40ca01107090402d26000140c2510994040b10794400c9a4165002d040707004503001c0000b030b21784040f810300b41d1092840e1000980e201421300303035082c682c0501d0105114003e2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 594841672 1250 594840422 594840443
    0x70813240c0f08160c0506090a0509190c03050109050601110303061c06090620070507030b0901020706050906060a080309030303010e060a0902030a1e0e1e010e031c14040804050409 79
    0x5903155030b0980c004c442e400d40080d000507108010403040c141940d01500c0110789903410500400001400c0d00f66600445005403031250115400c0c60201406141b04076400b8000e110700040f12000a0060900f44a070401090070000070400650140701c07048010740060016510710f94800d014000c0260744030920b1040302003403c4010012500620541194034850000402c80080000d07030102e2040c2d100a1841c0b034808104800e900007540050001c0440e940700281d100b0f10351b1841c0c0c0841c0240134000c4042e02d010b04103405c116901d8004906684a510f040700d1550419807100001c540d603005050b403040d0580e00c200018031012402c8240035038030203002880c054040d070715100c049003603030001c0d60780d9030103030780c44500d00000f2046815010810b241640e8042002c600d21540042c0d581c4078403080e52002c9082c1250030080c0310401c0d0071401c0751200c5c1800720396036000140c00d072140004803105030000c00e903e031103400c004c1016080050f50103560003185850505082c281000000d010904007106c030718068 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 594842922 1250 594841672 594841703
    0xd02011e050409020f0304121b0f0206070b0720070305071a0c1209040f0b0306040311240115020613080a0513091505040b060a08060301060b070813240c 67
    0x38001030100100c0000b1040c2c980c10b07c0e2818180c0c02c4648400c10051180c00100140000504032001c66056048100401500450300108446118114001d80000340356130401201541091071003c00ea507500d0701c09201d031401c43d401e02d900c96206001c0242a034000210800c60300100076858104003101b51035492500012129107860440310310300007040ca2401040000c11072030140728203107040c80c401c101030140e191315400207a111100104001d0902ca00b030b021000b0000b0b010451008400161000a064141d030b49003035800c0328009105a090f01030500d5244c440007440407400b2030041002c41c94010031600c465540002a03088400800104413040c4500b070319405c040d96850300140702150001501c22007010f23030300c843d40d039003031300b045020310300b401d40d06c11060311558101c41600841c0e28240046880da0f1300000d02503c040d45c003c44079043e0102d550f400f0300010400802d003207002c050800100540d51b01e034605081400040c11407100c4020001840c2d250700801c580e00e01c0318031410320000f1441d030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 594844172 1250 594842922 594842939
    0x319200405040b1005060a0516110405090c090a09020a170f01060b07061407080c0904020405041a011b0c0902070602090a030818010e0f120709091b050d02011e0504 72
    0x44a060b5800c841c2081030050340c0001c4440e04c03000d4002520b005144c00c030441d00c0904244610052010503c440e080f040c0c0a0000119402907140c400400900c49402d080c0881aa9041900000c0b4420290a40800e43c061101d20403e0801903001c1c1132040b41920300039210f003504074080880c00071030240c00c2010384038040038450040a00303150312105403100c0700e078200403048644090a2162811401d002d00c041150820041a845001c1c415880d944400e00d0010801a0140da44101c0d045030030301202840720b5203044d0400610341c0303081c0e81c0e00c1c2003545196000d0484243c1a100982002240304040c0001c11071a002000540d00a0034050f02d08030700311002c200c406007141d1040e42c500402203050301100c1d8000ba07011140903024a02491080502c1e40090314400b61055000d00c03076400703a14207220400091000f03500070250000208940912800c0c0b01c80400910902c82502140445000c5254a08003480300102a0180e6603c0c403e01d0001c2004000d40001c805208103011040c03100003075201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 594845422 1250 594844172 594844181
    0x8070e180a0515130b06220609020a2a020d0206190c05120a27081e120a1d033307030c0c080d06090e0c090603192004 52
    0x24861001410601a5040805039141015080c00199130303c401d40340300070071754070341c00142c000000b200e406503290070460a0107403842401944200940c2894800a03091030b1700c1d40a032620422545480200500c00c900403182000c1c1602c00501540e005100100581040309040300c1c80f070320103080185480d10040380340f01c0d0480700b42080b00003c0d40c80090740c000c0003400d00085206844501740e580c03c020541002602650980111001a1f4988010f031140c4030791110340c48005041c0d05094441e40b0904401c0d92807115845019844c0701d110700c00460a89101407000c59006078441d0f40c0e410300d0601e50f2051826402c402e600400d5041c4500519086041b42c005215410f10030b0312010845640410910b403a1040310041054040c0361515107000c80d4242c000b684105016807011a00f503035404c40b01001c80040c1175a4100c200d11514003451340c0c1c6060f0b000201074a540008031610940c075640d020805655242000171048406000b1080d400010025040101e4080e595928211080318100101c0c0864 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 594846672 1250 594845422 594845443
    0x302030a09060501030f03120209010f0c081e071202030f070204050a1b02010207030809060c0a0f140301090e0f0106061b0302010b060c2d0604151e060f0603020408070e18 75
    0x1ba91215100701500500c1720315034014031800641c1801c18010001e4002c22440c5040418030031090408820065140112088400001c05400022008001010050b001000d044845d4800c0000c078010850001041c0c074001d4082c0800a4a4519240d0900020b0039014203007042d855103601d60b884080000c0b400740c3d402d500d01076000503115205410000c000c810098000340b141c2d0414018441007407020412983c00c000325003001202011424000c5840410039214040e51782408400801c0104058001100c0c10034214119905500d15000e95422952a880307a9004110412503490707003280710540d401d40c0b0074040d000024016903010007040482e4040100001281c001017400762042072003110340c8044810316609501804070f40110740c2d5503480c015001601d4002e03220b076036411002180d04140c144114501a1742a070020703800419000d4041406010f01c280000840490031520074800d8800303e81120004010540c81d000e0f4122080001038800d00700407010040e0300303920050410031007980 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 594847922 1250 594846672 594846683
    0xb01051201060305070e1903020d0c080a0c0306060b13090b0103060e15100206040b040305131d090706050f12040303140112020307091b0807050c0f0606090105010e0607030302030a0906050103 84
    0xd0300c5c2032500108140300c0700170310300c1c03141f0a110f80d090480b042800506050349c1d810f80d0a48100001e0b410705904200311035101701d045102d249030200070045010350352000c0b80d21a14003440f0540c1c0391000c80449009403450f83c1c5404481040802450400d41c00015000b101070400003060f540f6034600020024080b127080c48020411040003086e800c1101c6041e0341070f0b0107031000e01800d0400d95203254030328402500181c01c01a0104410703504956490520008040441c040c18440c0c0c0ca00c2e0402d44909021950a1401c3c0954480061900d000710208c448600c1380e003020918103080c0b84101104000b0107041941010350346c46004641849c05000d807800b81c108001e01040340029407040602c1c002e0a41c120420490030f100091507149080e15606807403690a0070852040d42c0c541d4802c4515000d041054101d80c0b1801ca50081d00000116403503000305010b03900e00d02140c0c0c0751001510603256040070250050020400100401c0c800d40c040d54200342009000b0a20b000c4c540c6404060360703001e0f00306a51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 594849172 1250 594847922 594847931
    0x807091e080d0c02150c0705060304110307061e110c030613050601050406060804390501020c18040b10050d24090b010513110a03140108070305100b010512010603 71
    0x100e0010032030700c0b4101e102403030440301c9450503a000c07840469070a14090440c00c0e0100b100c081508042c41300101429014050395203a19190600b01800050076070428064025494041840c5200b102c0741c0060101c1c3c440000c590700d04182041b41c0d000f01d2842c0b105031302d00074115001042d5a050140d0b03401109050032a40d1220b01c1d44c101141840c4060340000d124515101d810080540c010540d1540281c00001d0729000d03403c2404450310b091990316200c018031002d0401e2940c081006c4404ea0240c4000f80e00f200c888031a10000e00141c0b40407207052688100111002a0001e20307441410f0341d21404141d040c0c240c40355507501044c0b80c4004481d045440141000f450800281015a04481c5102040007488235030380c0c90f12022a10401030041c6401030509003814002d1440035005040041c1b5062000e582d80d40c10000d004000703140400c400709000d014003000180300711000900400f60390f00080644040e6840714a0840144140600181480024019000b221099a0080b4020f1400347c80114 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 594850422 1250 594849172 594849179
    0x30807110f071d0a0501060f0c080c070902040f12050a060c090b03010602070e2805060303210a050915070e0111060a06050a06320405030a050d030b040207120807091e 73
    0x2c9459200138105a000c1e850107004110082c7e0003034036110700b0003071130504907000d8a10781401d0029100703c00a035003062040981c0018240d0180d80104101d50100741c1c15030429403104a1448007d4201502810350b51055000da00458181d03400911071061a08160f0059542c1d0301088109130026440440541c0224200300010104007001c181d102100003041c01c2d0356100d007441c0700c200c800c82c0c0380303014a0155124000340054904200b00c800081034410321400d121111000f10310000011244500014101004280b06890000b41e4404140d2180448606951460011580d0b0b0082c00000b034100074050042144000c41400318a009042421010880c0741c00c0006000c4905041e91141c000c000b2070031415401c0858030780216100c00d107101c2c110003d0303d4008200c0501d50007250407990385805501c00400030044e000460940500c0180c40c1440b50a01d24001c03c0100d01582030003a0078113010101d81d5510611030400183e01c41400e0038044c1040d901c2d0401801c480500d500940c7c2802030745031092 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 594851672 1250 594850422 594850469
    0x1e0b03070e0702032512080c0d0908071203050c12090106030f0809041d1e030c01060e0a0c03060e130317090f070b030921090306070c110d030807110f07 67
    0x2080c0020403211500b030f03280b15907603901a0075049006c2d003c041000d02800314078541001030441d0005a800007080c4490380707c40c1420311090f44100c0c021192656802c01c030141650080c00398512980c10311f010241840c0002c020103441000081940c05e040d540c9440200019074211706420400d4000c114883c0c5803480c440600c01128904501082d0703a24400e0003413000cec444006140741c40710b0814400d80d1a001c5c00301c0081da07d140146042c400940d402c01501140074078200c5100c03881b40301042c81c103021380060301805408a661a02640c1c80c04000100010540300307030a1602d90b6072621925209114100000c450740710410166000ca41c031780c102a02d030f00403000c001c10107d40501a0300310510302c0c6083c05561241d442504c0841201c242891110541101c00940f040d141d6401c00542a40c500d0715003640002e1038510441400c980300011210792811030301348101132410781d981c1501c1d09102e584032064295404400782c0058003c9104658411101c1101400440002c05000000b40c28000044004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 594852922 1250 594851672 594851707
    0x5040b0313202d030a08030f1807030201050309031303080c07140a051018180e150606090f1c0b060102061b090a150e03010b03011e0b03070e070203 65
    0x400c0316071540c100541c40b107a40b141c6a4194a0040c2d031119038281810a55503203450000410066040c000d8200d44401e104141005500c219440280508550b90364286110600e61002002c0f0403580702000c00e000550042d402141c11071a010100c0b801d00801520f15603021809800403122100c022a02c1303e41d0744000c00c50140a000364040d03960443d81c6180200d841040e00740b0071641b058090b061a201c4250090b000100c02c071b869207008143c010b0f00c0f422002c41c80c902c3c02d14010882854144001201c14002c1120f4101c2c080700913405500791101000c101c00b58101011007640541100130641080d41d03002c40b903648820b11380c00316a817000300508184458410060110b030640d080442000341032802608c00d10380140044c2d6155444502034004580300f03680c1074210380840010740b04150517040e001480c405555030201c0003400395412070014142030b16100c01c1c004082004011180c8040b2002d0703049038482c20400790444001c245da4840c071a18a01050b80c013200075800004849444e07050b029031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 594854172 1250 594852922 594852953
    0x50a02040b04065a0e09100507050f1201090b040608070b071a010617072c030a1a070810050f0907030902040c050a09170a030f05040b0313 61
    0x90400c1441d24002c40984030180e404214000180c00c11040c00d0b80f0204540a010125180a603644e94103401810780c0b04189600313a40301900040f42e01d0000750000070400318511440c100c00240c0400e1603984000c0019001c050444410f0050500c00c5e5024448100c0107801050701212007502030354500580c0e0390407112161041c81c0200c0c10050f0622020500113000400c49034404c00c540d42d43c4081d4244260313680014061203102070100f04c00001c0255100419400c8400d40506448403520707841001d42c1c800c070190040844049800240408144208113030800a4a0141c140d80c1c1c199113983e078502d9000405c0c0c90340c400e664600c3c3c09002c01d0350b80c0808030503480444022600c0c1418107003030001d400c910300360190b9403144091000080c40948260000050558003502c140141c4c00c04a2010300389402060346880082d0807001d0004c1d604000300c1807030b00c2c03040c4a00d020b054950300d203440031a0100d00400040e024018200300c00100e0342074800095116682c5145643d02c002c0f413a142000c5142e10010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 594855422 1250 594854172 594854179
    0x3080901060515070507030f080301060e0d030f030b030a140102031623160501060f05030d09290c0d02010c11010b210a05100504030f0f020c150c0604050a02040b 71
    0x940c280856120002030310107441010f0280d50b207842442c604035140c5481904014003600d03080620f001042002006507040e61525210800a880e48806000328030842c40000340000304032108101020b03019502c19020080003400380c692144c056111a440138000e080d03418200e079400002c011210a010f00d5041180405207001c114600c59685c000060b65014142c1b80942440003a02c11040e1401d807030b0b01c0d400c0c6a8000000d02c0041d540320148c0d4800c0c2c80910800b800381c0226040c20f000144202c120030f042c0c50402e81040c405a21606141c00c2c00504c5001900c2100c504000c884001c0000300091002240980c0c0080741c40d01101100401700b005480c4c0c20b0711141e0401070400c4c019911030001c6100c21041000d00d03482100508019403804611f0100503002c0e001d150a20959080241c111501c21806900d99080200102d201160001c4d0340050620040e005403003000b0780d40c40d103100000341c01ea0004038060b09040e09228043d04040041c2d401b150154800441078045003018003a025990341c00300d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 594856672 1250 594855422 594855431
    0x71134060206040305090604080d0905030709140408090d08190e010c05100e030d06141f08010603050c07140f0f1902040b12010606080f010b0f0901030216150903080901 74
    0x114080d6846a003d072000701031080100d40c6101603144c00c0b0641d001485041d00b1524185d03803000c005405c41d60103002d050b000c3d0040c210b0100d440ca0041c000c201040c403003004801c901d6a1103849010702d1b50800380f5140d60080c2d444040c4030109040801600c04c002100804116911240801800322500401c415051048030588040032070300c0424a410143c0420a0104540e01c050710003600f1841072103007440b005803622402080300030361007810380040101607813241c7c86032a951482110008003400d401d00002e61500052004510a8018a403c20780c0001001d060403050340d19503182007040d48050b160351f80401c00210241e80d04100c5466040e0481c0041d01109048551a03115100d070000c0181c000d503112040f44041e0388402410038014426200200074058807000300420301c40c000e5400041c80081c81001103082c00340d00d0100c5812a07001004140b424032814015000303500842650381801c4000b20140c1c0110b080e040d95114401361000c40043c83c00d60320325024000120142801076140e140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 594857922 1250 594856672 594856679
    0x4021903060e07080402090411090c132925140c0d1214040b131502011503030c1103070e070f020c28150c030306060e0f040203071134 59
    0x841d04e42c0d001501903500c84c1d515034803402c1640c02050030090140d00550740b0300c104014034010340040d001510290103840703c4d4a55a070002166401ea92044002d0782c0e041c8104000014820801000d003021072a410400841e10107001c1c54103502c2c2c500341612100e0415912400e14030051203100801359040b91603c04038403081d1500541c07d0002c07822501484541c18455804400b203009441c001c00303282c0d1610750b0756243c40300c004400c05900d00c108a024241c0840a000040c01805241e044500043c8414080791642c0c0f8210f919581080094590382d0001c0d030085d500d40c5090081c00054048040c100c0307164188190028120b0200100b0070f0b0440d005140340c14041d50750420404040641c184800e00c1007900034195625805456000c01d40e1226840765100c142a0030600da040900d00070b80301041040d594a0f002e6131485004800c1d80c4e071281890b100d10fa0343c2e00d4258003844d001241c52034101991110182107a1501811300742800106201d6012540410026401003e03105813204007821051715 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 594859172 1250 594857922 594857927
    0xa060315031401021c14070f0e09040f0b1e0a0b04060b070b0417040302010504052b0f0c060801050603161b0b010302040f0e0a03050d091a0901050a05010b09010806030c04021903060e07 81
    0x1b003d01400b040252110007096032501c1100d6800011a0003492141e0f141410b00d04072699290f070701f008659150f40d49000864908000c0045240800c0c886400b03051b96640c251100001c0101102c1181d029544901c042102e80c1381c600940312480c41134000715043d06081c10700d8521243c210400004e1074030b01300002e00060b6807003401d89088410589454000403000010f03803210650392000c2a20401e124121003091001c0a14250112400f82502c1054107480782001c03100140c0901030303260407070030400210707410180340c403840802001c1070305d8082e4540013401035080a00c070038000c06441500881e030043c0213514041c440e0241110542d40c080080d40b00b00715045403105400e60010703003071003c00b14091004408940040003100c0d880b90050042040c1d01300761030803014040e1080b024540c41c000010318460554400c00381030301e580c15403031410001c5e46030044410302d100411840d05401603034002d442342e48890001d08055000d0668120903155100c60080407610207078021504a0500b0007885080368 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 594860422 1250 594859172 594859211
    0x10803040503100f0f1b110304050904030c03030608060106031d03130b2503030e0c0328060b0616021002060402090f07030902120106091401050a060315031401021c 72
    0x607600031004c00d807101300003525401400d50200032401c0343c2c03c05144e07204081c00c0c03d0070850003c505032640d8140800a0580303a560780103030b0080781d4000054a0118000c00e02030700000004030711924000c242c60b80c41d0640c050900d4801e9100350f020a0b150904a00005856a41e10f840300a4400045d0f007041c490408814028841e4840e000c0d051000245002c041110200c01400d118004d4000541e0643e2074900180105001c10361002c1034000c14202c0006403034003150340c170048454001c1f180181d207031504160b50302c004000d100f00c855940d0b4801c5200641c0f600c0000c1c10504110780c132001220500b40c0144010230b00c950b11342e1070454002400708801030f9204031201e034124141c406000c0d81c9503240f45064005014402010703500c2503600384800c0040c81c05410020a862407114140301d800520110229050380030300035154081074520003400300030b1082e808200c54242001c2800308441d5a901c80000c2843c01011012441c1d400082409100d40990054900e07040400d608110383d096290402c442c85 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 594861672 1250 594860422 594860443
    0xf03070c061803060603200d020a140d0204050906041208010b031315150306060501090b0304080a14040e071701051c02010e042306090702060a1806140906010803040503 74
    0xe0351203003541101003140002e024503404035042007100e4036400e11140c641c4500d51800f80346003038240310059a04080e50b501d6052503000e049039120038103245a2003400396507801e40c140c01011700e00808026035641d004090040007030101505090825041810349444008500410300c40d03940e0040160b007444070200ca6020350307007018101c0b00400ca0b251514800c0c2c000d01c07154911506114230100003c80003140c0c5011244100d01c1044450381d100019034644c4100c0c4188640740005100140214407140014411660ae038034007486640044a0705040b0b03038205410503c0d0086541081015803500201107421a4039101c0c0034501c0c2e5850840000c5120301440019244070095412803011a40105203505440c50002c00034043d0f10340042d03560310001c001011603151405075201045803400c1450100d8094102517000d05810359445142e8406044128512841032440180f840c012500901c07580d00f9101c504500c02044d0705120300c1c514903142043c1c0180303015400400042203540d90015030304d1381c84c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 594862922 1250 594861672 594861677
    0x330a0c0f03140408031c05090c06030c0c06270109020904021e131a0a030f1b0305030a0503011d010f0618050a0801020309070617040314160507080f03070c06 69
    0x214103528084504045903803085600001c00300c0c0205038a00003101901030005101c0410450119210903401a52015a018507054008822085240c240100210b038848a1040c984c0d01d0140740c0c1025514000040340d00c0303600741c940c0c074810402510307200001680c48000350009020700411500080e00241000c1c2c002841603400300300c022140c3c81e42074848107200100030185a804420301034901d01410400d880000c2140f0242e58448040c5002d030741000070b0b250020f844450304401d039564403900740001402c54210120500002001074801c00080c81011303015030310a91a549881425200011800408500144042c0c010f1001114159a10048403110b1070000d400f603001040090118400c1e0b00803a401c040d4042000c24a07c0c4150001d500071082181150b031655a1940c044a91151581282d880d007010140800c1c0880e12982d82c52419460f0180111728003518804130075565a0000d8089a582e040080304015100003442944c1807440f503000918549102507a5000ca80c00300c60192a09 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 594864172 1250 594862922 594862943
    0xa0308132303100f200319050907090905070f0f17060f0703020d0608060f010305120a0f0e0f09040c0e07020d0504091a030f03090916021b010e330a0c 66
    0x556180d03680016000e19040d00c0321540f65010040406141e90048070240065840f1845203400c20307c0b80d10440f8811356010340549032560500000354098903131402c0a5450348034203c0081100014100400001c1c00c0912502001d1858040c0c10034104080e1050703d405034200000304000c000c00d0180351548030509180040e07030303001580030140091810750410703504c81c070483e020030902c00b070400c0c4aa81a0b07806042101c01c00001300b40201071910900206000141c548506001841c1c010301c0412442e05009001650a0fa94403001c1040104201c806484c0300c8045641007152000d2600301b540c1080480c8040e20342ea2021b40d00c094424031840c03080d80022039a808031640c80c05129480c0318202c2400801303860b81c003401c1041242e601d800440c03c0610888807030313011408c2042d5180d4002242d01303250f00507011a0903001040324042500052403818000f0000f4400200e654501c01924020400c0140802c05a1004090070004280350412261031340300700140080b454016815013081c2d0b40c4a05000d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 594865422 1250 594864172 594864191
    0x61409011d0a15180e0601050607121e020a0308090c0a140a1d040501110406171918051e060f07020a050114060909011109040b0a030813230310 63
    0x5000342082041c030f9018900060000c20b481c6404042d80d0a206521881170101c030380a030312640c0c1c54000a00c246a0720010800c440c90010f00740d081c80682075940d50400c1e2504000b000d030080e0075402039a1240c4016040850b42c0d20402da0002d03101c42d000281d04004010b5030309020b0104500e0420f80c008c084800381c2c240c0701070342e507551008200e4000d440d650300f403214009440510b0b00310303043c0140c50440c0c8075400c0101c0501d0000290041d00c08490301c590399001b280b1030440d2030701400500507141080340820000ea94405800c0c0780558401e08066070081d005004007800c00c24101000c9078602154107075a65607034040d242d40010b00070b80000c4603003030b5404281c0320381034180d141c100c1c0c21200400d82c0d400c0400c81c2c1d070700703c8011803110701c15502a0b030150800d9880e600800d00700c4181101c01c0003074010511600c1c0d058106503004032503404000e004c40811944a8898014940210800d840040701451081c8074100e03400040e1251890004104040690141c0029440341d41c210107003003150340d4400c0c1e4603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 594866672 1250 594865422 594865441
    0x20c010c0e1e0a171903050421020105070f140f071d01030c2c01030818041418070504110405010e01021c0e0105070812041e030806101809061409011d 66
    0x40c410300140e01d00386140c1a406c1c40d0203010360300684500242580304040704408829241c0c1c3c14890039505075909450a400356070391000060348000141c405d2007105004440b02601001510220744070000202409442c20140325a002d40500e03204c10b0140e0803000410000fa00701c40e007041038842000c81c201d1000c144032241011000304002e8030340c1040703a0b140001300380000080240442c0708072405000c4042044424442500c080b610356091040300d1400140f00071106039226614142c445056403010350359400002c1c10b03548095003642d0b0001001500b0000d0b980c0100900d40c100a0070f0000d407014484040324561078070b24003200b010600c101c80c0c8194400e80c2c0f050048902c0b0316448641c10351181c0c000480c00405140032a41124000303810104129550000440d005045a255030f90041d1030381d0310802e201e0010f0031510800107116902d41204a216060440300000d082002400170390306140c81d040e0440c2000e0100c207140103810b004014000980b1200260b01d0729076118903107207410380354030284 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 594867922 1250 594866672 594866683
    0xb070503250507050a030809040902032508012315130606050702030105011403120c01090b09150714030106080405152403010b060a12020c010c0e1e0a17 67
    0xe295401030090720076203003a6040003407420102d00074821502c0c1c550b00e980a000f00541c0c42d0101501c12442488501400c0c503198001011076413015003a5a84081120b40c041d10408110f011400c2da5a00898244010300b02403040b80000244001a00d00710107880b48110700138400034054040a8810385400d00d650f4507401c000a0010030030550810040b075460100402980280804134440d5081800018203000a80c038800c155040c000e024125094008058210651240c00380200c0ba54842002d413020401d0007001901c00d00162001d4000f180007980314000400f002440c000134003101c5041c00007503a00400c10f4a06440b21814039500ca61102d00303003140340c90024012180d0385d007101b40030002403003074a40e40c270305d5001141400e00301668894410503091f0361040300055048003092000b241c1c02885440b8078003280700004001484d01d00c40102090a40d1408440300e00401e013206070f980d4140c240103400700411002786402d100000d980500007a1003c03d5403007030503517004500c0340080c08680180003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 594869172 1250 594867922 594867937
    0x50904150905101e030b0c030a24091a01021902150d06061205070207050f030f0d05180a05030c060304080409020309030316020a02010e242206090e060603180109060b09130506010b070503 82
    0x84440d02b00e40304040d03402c4851424018078001d00d00300080c4888000441071592a00501600503100404000542e4100b1062202d010b81e40000600c01d0805840d0910340103080e066060b80b80070460740d060100251654485101500c842c9161904000085901040305070a80f0000c0750810f0108030328000083c074080480300880359501514004004454105000304600c2c0c20281c1012120381c011001c003c5d40720154408c0b680c142d042081007041516192000390752052160700c002c3d0409403a00e82e00c0f4202c1c0c10072510304003203910000030b1141c4911455541c40303030388a0b688000c160303071825940000e0101c8162130751580912004151441c41302581d0311103051001480540076101d20758246414208200307000c00c0c21401d143d4000200300184503924180540f007401450b20810345503942408942e500050440d0b80d10f11414002c6030b0070390300a00400c040346014120205502c409241085690a0060070701d400040065203e6000034402059282c11110444212525000d0a00700350f4118401d004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 594870422 1250 594869172 594869201
    0x1527111c090201051b0a0611040821070507080a03120516111e01140906070f0804020d170703080604020a0e012105010303022a01050904150905101e030b0c030a 70
    0xc9240750103050006d0400703d5603025010521148a04440b50407140c4a240a03101068000503600e002420400000100d5200071034000c0385081e8190f26164103059180e0444a040e8120301e030300805041d84035060910890b00f46504020a0804181c0215000307800c0310b4020502c22901c5040c03a55400a100e650440302000f040744008210a480e920b000b8103080c4840820406240d000c144035100026200384903d109403110b84014aa0303c80070f840088008104aa01400340d02c0d280d40000d01040c0c2103544000c50014850b19003880b403801501d5484001c0007203004901c14400c0e00041c592001c8900c0100742c082c00d1001c1c0502c0120700c1d8001044c1d80207010300c04603081000010030164001650ba07811410829034070118403281010030008031541911500240d02400305207074a14042d4001488200301d5660240110b80d00c8c41c1640984808950643c0c6100c503e1034100085d807a490f4007094440341c407540c0d1146040c11540c902c10010406072000740c9001d004400a4045041e0368041000250f024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 594871672 1250 594870422 594870457
    0xc071103010f11040306060e2a040812040e07031514040b0607050a1b080d05210108010e070801020f03041115041203090e0601080a1527111c09020105 66
    0x80c150f4420a44c4140b008585071032900c500020001002c0e085035003d004101c1c03210350046440144091030800d41444599028410003000034900c074104503008012156400071519503181c11a0030b007072010020014024542020b0344842901d4402090300300b903c0103002100200205140410002d0040044064124000040c028140308002440c005018810104100b001c042c1c0060160790900c64850743c1c07029030241500d01c040b5400b500141c9101d060181100740300110400c1d102400201c02e03800200f6595640110051128042c010308020345000c0303000303602e806092248220284001003016080002e240c281d201d081e92200e4902c0e0712507a140040725129074407800c1c0d12080c0410b100045000c6485140d000401241e0345401a00c0b030101619201481c1e5200c01c000c102070001d940034003211100010010541c8410800c103040000d00c4032415400324106400c802d01100c0c0983d450b074808007024410303001c40c4c42c01101482400c144000004c5134100080c80141d809000e10002820402d070030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 594872922 1250 594871672 594871691
    0xf060105070309170a080d1b090e0a020d0905010906050910020f030c0f070c060504050a14010518031911030105090102090a0b0a03020904020a0e100302030c0a180302090709080c03060c071103010f 86
    0x180d42009801c0c08007114600032110a01100351072484441c86801c0e0030480c0d2600045030116207601613700078082c00008607442680d43e64050840c1e90582d400c489040c1c0c0c0d1340a0101d1080d04114502d000d08903090218605800000071201500000b014498003440019182004070146010359507000c4c0d0206041c000562603401c0a001c9410500905010f2070844a00140c14004500c0c100f0a0801c1038407203600e4102c0f0b191804000d100000c1e00c242c0c141c458a0140b994404c1c18002c01440c60f4012080000c80d120098101030940344090044440340e801400503d64070340d02c2d5040c034000c407a01814a1035444506480c140c0290140222065005102003003400025030000700c402071401040395a036901d10103003202a8105e00041c0e070380c000711400a212700c02c6564002c44841c0b14080f0038868210011f84c2d65400103085001c00c96101c800111515020400408200700702280c0000407400b510040c1f801066100d214043c005020b80441c07100752092005032020f5110302e0700e545401c98140b003104c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 594874172 1250 594872922 594872947
    0x11121005180a0f0603080702041a030706050406020c27040510060603020c1504030917070504091407060207080a020120010e070512190605040206210f060105070309170a08 75
    0x40302c0c1d0200890508801c43c00640c654480c00c1c080d60344c00200d050034004590244401860001a54a00e2000d400c80140f090b59041001400801031999025915420004000d081440c400270131030280101945141038000c207205a0400490050710700350144d92641003c514010b80041401c00c15442e1120104805616800900c081d1001400f2103d040d40141c4c201c0f64000f10845000c0d00107052443d0520610706081c003404009140c15040751501d40e01c44001030101c4009039811100081c003031003481c00d40002071000f83c0080000380058840945813010058a940c0c4c9010004d0410002c280b180013000b51518403481e644010500800000240c0c1195941d0380f016801031a21869054803420082500040c9008918681e140002030441495682c0d00191101400c201d90050080c01000d042d40402417a1041d0340c0c107019000b00c40c906000985507a8550082c1c6010304008007004106c4c0840d81106024084807107011052031031507400c032001810125516001004110001241115144c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 594875422 1250 594874172 594874219
    0x60f1e21090f021f0f05030601141306230a0c08043503040b0715090f06021e070b0708090f030a0c05011b091208090a080105100911121005 61
    0x2403080d03400c0031090803100300050400355904501310019502ea50354001482c030907000b42d0703007205c2c040c100841c1000c014070440400b500900010703a000051400d0804c40e007a44904142c43c603a01c0c80c103000d82c03d1400368443c81c24034441c440318002030104100c0d44908000b12a01120000c1219071030380140d04800308062949035203461440040400e07001054260100040105c078200c90fa1900707007078589103a07550f550b0f43c5000341c0240101c2103661400c061000c20415403182d200d061242100603950003170f0000d68034400c212068070080620041c8800350020700080307a5550440b50b2420002c03295501c10600c1e502d8005901082d9406020202e11903074a15084100c0500d42440349000740320190307504c14241010000041c40e48001100311b90104038115000c1d42c0e0021580c016040c01340ba02c800c800200e07840341e1140d48800090f0b0f42d95420400021600020107014010304202800781c2c1410700039a4801c3d0080e03c0c00301036180d001d00c000c01c4a8803ca40c001000511028000300200144845400a0304 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 594876672 1250 594875422 594875453
    0x2514060702010c05040f03030e040905031204050d09060c020609041517011802031507030e030a120515061b07030f111503190209040209130501060f1e2109 68
    0x643c00c103080d658100c2c0c015015a02500da25a05942c0010f26585049880448039540e403030700195180450804160207000070080311388025840c5d402070130907140c21803504000c15400700c20000200e0007803000d903034845020540c0a40449505840300b4160380060014030480040715420080301000058400820038000181540c0d40700801c02d1680dc021701650858414a0003076054000c4150450000304950300560414902d10b0001103041003c1249459540000d001102041c2c600003442014511401155804501900190081b480050100d19980580c09402c0300c0d00800740300030365421400f0440700c0001c5822a075207031100300d014140b00c2c1b491445520403d025504a13501c0300040f03a120411280030700000041c0d44503a0700701d1400203000750000543c3c603a100c6d4080242009650b142c5140c014134655015000640f94940000036103101485000300c818048100400d541443d1100c43e0b80d6101069414000c2070f8102d0808981061114003040f60b0080b85048481810b000d89080900b904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 594877922 1250 594876672 594876677
    0x507020f0f0615030f0a140304030c0303080105090c1822060b090901050a03031d01030902030a1401240306020c030f1306080105090408071202030c0a03031a010306050625140607 78
    0x14039072004103141c0c550300817420a0085a02042d020340c001000004001d511520302e0003a42e00300f41e103940d40d40c07000d01501c1c0d109400180e641710040c000e626166825642108107031202131310f04600b8440e421150322008514a00c5041900e041c591400e140582c103030703020341115100300308250b1251050103454014500c01802901c1d500004509410a110380106690b05600d80c060100c202852121616074102d0b8410304241c0c0700d19140005850420056800e00e1050200d0214100d00c19215800c6034501652515484140810191410390000303110302600d411600250f540e88ae00c01d022441e500c50050341c002c0d10310001074010440780c180c0f0b0b4088190f488654405040c2c0c1d1303894041288445050380c0c080c0019204009070400101c0026a0040107072250041d02c0c10401c0c01d1030800d0502000613403e03400310391681503144420040c009110505902402c2c20085541004e01103a61800354485040c2001000c00e1031051285e600f807000c140f80b135400080074860b032100d00c0710030b0385800c410b80c0d00102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 594879172 1250 594877922 594877951
    0x504060606090315020f0d0501060f02151306090615120b0c121513020a090e16051903090f0606060e0a050f13020906030702011d0105010b0406030507020f0f06 70
    0x81c0d0314403504080040300c0e0440c44051208031000307040780003540f0412079211143c00421545903445480d0041d640200841c0d2a000d03458488428040c0c280703201420001c0c2000e803007034104606c03166070b251200c00c503941180300020806401e03d0136000400712220110103008002200141f03107041400d544c1103580c46019804082c4e01d0b05641c041c180d0250102a05c0185200c0e07002400c0a1448034024000c2c2c2d40c010030400e01c450810200204a078407410581e0300191202200b031050f42210380c3c88980003500b241c7c11091019240300d009056000300c4140141d0800e001901814070780c800d4100c080754a4219a0744088000d480c0f51180040c0309034803419000c03901c20900c4d0105464490000c9007100c0c000342c40340042d030541404002c4082c502c2101e01980550074014034619403070b0174000e14880ca100341c00015105540d800e44008005110002041603070509005010042d0b0b1071003640c088945a0801240d2511411001e0b82083d0300e051400b490b51003000c005190303825000231514095032130a2041c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 594880422 1250 594879172 594879179
    0x9231911150a08041e150b04060605040e04080a1103040b12060d02010c11060d0e0109051c020d030b010e0409030807080903120f070e1c1a040b040215040b0d05040606 73
    0x112203000340c180d0b4801040500000401060050180410b000800042d1400e0b0300407590703540d81c8241c64018094140c540e105060030440c1441e104140141c456410828205450604040e40180001708020020301010030800583d5018140400403441e280040e0303a190758660f00305040700c1d00b2003009150141c20ba84042800cae0701746420711040403501a035486500403072035241d005c84e4084101500750420402c004110428145105a410034415040045042101800c0551603d80060000711001c484001c1d008400340e00042d81c1481d059079801c4c0854000c1c00300005807110605140e03425081428002c0540070558410401845960181c44035241078856141c0c80c0c2e80ca004826910b21501080e4000c105507000c0302503d20b40c0015a4503001004481c50b070041105400360465600b41c40582681c1042040f004050048444095800040280c50700381c840194542700680041e009078402c280b030025041c2c2c0001180e018000c080c00f001e658240c0c8070780260003404100c8050712458984900030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 594881672 1250 594880422 594880459
    0x2010c0f0311030420060d09020a06030519180210080603011b021b0f060c060f0105010507020a060e0f1c020a090c05030601050a02010b1504061209231911 68
    0x11400c0b10703900914a400c540d03455540848004415640140c2e130800b03052030280c950394440082007081984900032518206903c107000e43c4082e2604640141803d000030814130161969441c0f150300040600402c6400d2041c403030114004c100c1c080a50031184440c42ea5207540d800c50a16801028140c008000039910440981c040b4502c6501c0b01005802c00740808410f8501148015101000180b48804c9003c003040040c02075031060381024001e801c4002003114001200980c24010042828040e14001480c1c2c009030800541c0c0c05070006010015203600714980340d255070240c0c001809401005402c02541141070b52000c034003800c0b88140b10344800418280558043c800d1075860a45445042d620340c48010348030364006140e2801150368814001c001565840d02203007803101c0b080040343d6100e0030054010100d001a04112a95904141d01d4100040828642d6900c03a000c0001451070414403200c241c6c1480d1203903141500220b080001c81e024003020410207404d0000031a92100c0303002a00b02131 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 594882922 1250 594881672 594881681
    0x50c09070e1003140901091401051603110d1e0f09020310180b010b0306040c030b0306190905060f0f060d0b060108040807050d0201050108010c1103031503070b03010602010c0f03 78
    0xc200080c024216201d018100502c09000d110554200800d02d003280b072560b14505030003220041801d0391100031071004d000781495591050492100244001e10303000d0004140d4602c0d003140702080541e900507940c2008000001e480010f005604148410360b003c0008420240703400350740308109868404a0003102c0c500b071041050b4264058060510900038002c048028400e41108180b2200403103800d2000131000d5000502800580ca4007545a00b44203007031108541d0391033350140505140042e008110f070f800103000c9611641c2d402c0c0071289605070200900c042d180030280200785101e15818026003c8070900d840344110060a00300c505d40c0d80b501308201481c803942034064031107041034011076101c1d44141c50859015028a06052800300aa03484610700022302146000617503442c40107200700c52082c05600321500d0146405c1404c00f07803c041041d00d9210140148000c40824043d51820b5141801154002c0000710705580e00d941c3d65442c00307806070090180074400514010038070102c480c0613205 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 594884172 1250 594882922 594882931
    0x20703020c030c0a1202090c0c0d12140702031b0712240216260c01090203070504110a120f0504050619020703090306090204060e1608160206071d0a0b07050c09 70
    0x2120f45d10b01d1450380034007068441c00381c441d0030180420003d54036048410801840180b02c141e0f50606e403481a24490f4007120390074510328405051020510920712f5000040d24203000c8041802e8500010315400700f450a005907000300b40c00700c3c51008100c10710070428400c00301c00f94401000400c00551550290403882144410011080c00840c1400402c0590080d444160b411365410083e10f03d8018012107190070000c9070f40c40980d15040910210b040030b100800082c02d040e030701070000300068041c040f454042c03045410204003190140d5004c1603015040780c80e840400c0c1504000504042c1400ca40702d01d4200c1c2c0c5c040d002c206413814040303110200d1007202d4a2640603580c60340c20030706590360304002e4815050241d91184d211180810b40d02d070714402081c00791a40c41d600d084040c82d40310029112080080100501e8200106403004998000c81c0e801d60140a924021200b0300c85280000e16001305002d0540d007285a1007000f1907491500c80080400c940207404885140c205101007100b60a0300b1034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 594885422 1250 594884172 594884189
    0x608030f0a051c180302150c0d09020d02060301150815150d090210081b041a1b0102030c0a271701020c01020f0d060e01031a0a0f020703020c030c0a 65
    0x72218402d21860160a007081003c60070901104070300440c0098510031400010041d0111244204241c3c04100c9a901c11220031003c40d254a000b00c0081000c1c02a00d820900d1503860b010702c0d008558031400031407085580140a142c49585030003240303031201c00700072035407010805041c007141e03458802116020318040001d000b0200305100d071071508295001110070a5136141c4500e14100160350312540351b190004150b41e04042c5280804280020403840c0c501810342920400c006d02a41c0340d0b010040c0c9112004a960781d5890b07002e42c1e44d800703000704040c0303503001194404024009030300100b00080c2401c3c2170320307a90610201c603103400032540080807030301200d6a0544590304200001c1c0e070408882000c4160030005061080d000b80603801d9900036040c807400807400060b01c0200c07034164403031440079100700d200ca84007a44c11540d81c540c110b6200040c0940c101c40d084001554820a80c0118402200d0792800f5915002c0614019560f910010700c0300d031190140e03c0b40c001147c10485054001c580740c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 594886672 1250 594885422 594885427
    0x21c0b0a1a0724020a18060e06030604050403210b01090e01151202040503030406080a18021e0a0906120c06020f100b0d0602160c21021908160305010608030f 69
    0x242c3d00c0034218101c070315000c2d41d041c40801e000200c0c1c4865101801e542c17000c07500d5030f42c401c1c2d00c80080c1d1545142942c21050502c0000320760180244c0f15103050b258421009d540c0041c103074496040c25140c112816000710004005407140300b80d2211242c0166511000a88585031165241d86418010304000d00404903050071804c49444100c2c442d020a60340186052001882c00c4c1e1610301007401c5902941201c030101e140c0c1c00c09d2060a8205125048961802402d500f00c489120340c001061561a1408010100d0b00c580f2440b0180d903d680344500107148a10b82080b006650303081699403000044004e81d031812460400140c410b00215032801e80200703220250030006170040644d0f0050010354411500848040d411038006034003440200035850400c004481000211302d8032000b203c54540101c1d00c08618042d10f24400307006c0c03501049007191304071211801c00e056131080b02c038440c142c0d5004242e1442641d030182e1040350301001320be0599000d20000e104440e21805259070340d2042c2040b40c1880b5204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 594887922 1250 594886672 594886687
    0x405040803070c1112030c0c030d020c010f120c0305010501020613020f060d0222030210030603020f01120906060e190908041a04080d030f14151201021c0b0a1a 70
    0x100c01c2e50151500c510b0021398100070810101d241400314284240141d80006040d46440c002084a1074030204100c005200d40c0b5440a0025110000303155001e05003c1c07401030110708030b4080d4a0b071980c1201d400000304110038081800401800080c410a03002d8040d19021510300390710030781d100002d990007802480d10a9003105c24004254003c80700e070074003181d00f0300420103e540c41400200d0310029902001203003600394010890070700034030710301071060518012013000107071070f0707260071100860303003424401c200719031745600800a052600d00041030b0030b151060204118085004890042110781c003c01d501d20070300c003003d5080b110316042c09005800c3c1803008029250700b4059400c0324140c070651040c103290381c4201041c42d1641e090542030209445128045183d1514805c500d6031164404158800d8100801081080b40d10140305d03501400000c00a090a01402d40407222004540c56031040142e070244800b100030304003464194481c0700c040c500092000c24190124a0781921428840e20b0070f00f4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 594889172 1250 594887922 594887927
    0x712211a150903031201150503101a0d05040c090f020a0c0605101203020706030f05071e050c0d05040305210d0c021603050105070e120a0602030903090904080406030506040504080307 80
    0x301441c14404200700850100c81e101031010b01924116080d124041c0c0d410250707080181e116498101003085000d204000c81411960308040844003200b0303049020800307400d050501c51042025210440d41490280030806c01008480e008840346124104038000d0760003014420b80c0b1030704468100040c40b03210500d01241c0c6640c8840d400180e2500801e501c1da0340c0e40c4441c2c00038030300c110064015801110b005c1101e65054001c28004040b4203204010601e4400000760010311165603c820041081044102d2a8068030886210401940c212000034030401001440da81c06800300300c0f203a00032982000c622011500d408201c010801054a04102c1402031040c001c0400113180e4046118001ea912a0101d4078244007003c1c501501c008901d615006c40050114544401228022003150000c1000031401040002d000e5602440250340c0b40c407220b10741c0780b4601034440300507031100096040c4010410340000410446905480c00d2202c2c0c0c0e030f50717002c00c0201e403400c940290500b9801c20000e80e003072f403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 594890422 1250 594889172 594889189
    0x32503030e060c0d021c0309030c080c070b0c0a110603092e0609020c1608060c07060615020703020a0605070b06090601021f1d030702100e03030712211a 67
    0x10b0111070500503846000c51408004d01ca0300405078203c0c0f552140b481e07805588150030384000d42014424001243e0340240808000500a0f0412401141281d070b0504140202e0b0000d142c045030b2a6216005558503984445d05800c003100c1800110018454500782401943d1084c0b1451b0007138200d1901c5000010942801d0480881e80c4442d5100715900000d40d600c1210041c107280c4000503258100091070518105020342911018003451000304902e800000d034480c2e00400a4403000d81f1a1020b00d00340c400360281b90403031b119810b021584002001e40c00a03100081b64004c59840c04030603038070b40c01900e06205aa6002d070920301b80400140b6181044040103401c48010302c125410461014510040c110407010b091000c241c84115001010324808800703024406082d000e5031a282c82503001491160034688854180710059070b02501c143c1e0f060054800c0320717400008a1031804800d500080c070b1102445240175050040002c0484c000c103481c866a5601e9191941d565102d0060070704204624 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 594891672 1250 594890422 594890447
    0x1606030209060f0706061a071101051323031606120b010507051e0606040b010512041112030c33060a09090b0f0615040e060f0603090c03250303 63
    0x2000030004002c810102c0e40003005001d014010000e039090074113143c40000501034865170303a9a00c0038419235010070825204071920301002d08219559060410002840310016481295684442401c1180301e0032480b030fa0000183c01202601c9800c0365501c0a0602c041680c000d4000043c424906000c00180c190300c464600101410030314201042c03555950300c0c14080800c9030007000301d604c2040942c03d50801080ea0000c1c81103e0600c65200d000c03000a065014030b950748107500d00030001007018404c142d00040c1c40a20098485000d1401c440901540c0ba4010860521305120748410b40c0c400426101c04140220103107490421107684940900c1401034014100c80c0e0b001015003c00078010102d481460b00c0580b24100205282c0352048103030900d040c00510b010b00802d090001c039900c2d0741e096401c03039003540c0d80704012a50f41c1c3c6500380824078031350f420205c0743d40009000050040c10b00d000912007401210440441d42d084c0040000c002c1c20140d25404100c0910f12030006100203401941000f071031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 594892922 1250 594891672 594891679
    0x1060804150207060501080d140f0a030906060510020609070f1203180b030108070906080610230612090c031c050901020f0a120807050309070603240608181606030209 73
    0x9003c00c5840f00c80450b1000c0e4040035003a0b02902000d6482a04101039017034036080d25490700d0501d1251b030b11544041c4a890100020956180800020010290f210a0140c0000381505a041c0d02c40c81d0042d40c1c0b0b0034160364200f6103100e40c50300091400c107058058420f68084480640c00c44586980549505030195070300c1c0380500c0a90b0000c035440c2100380140d03000300010001000224980a04041115101e800c180b0047d003243c001c0005042086c2401c6046499015000304009001b80038605a6146560000e0740300301c001500144818201071540c0c000d8920780181c9211690725020566508180c3c24212841c807480400e02814601650240002c5503060060303c4c07011080070310075814821b030140100c501401e003001c400705890348401e02c03d07072005550800928500749032184982d2210244940403c041e10b61980d038030081e40c50201090f810440c15407801c18a1303203c59002d0a03181040b1100d80c007085400b55440c000d00740c0018611003022039000c02814003802d01c1d0003140690302030a4410307007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 594894172 1250 594892922 594892927
    0x904060e061f060329060705030307030203011d07141303210809160b030604020918010503011a0604090510080d0809190203060f2206021b06010608041502 68
    0x1488000c0c04501c0c86210901018592240b800d03051400c10b589035001002050319020740c5604640c0b140e40d02e8810380f441c0d0704060302c0d049141d0000410520a560b4000c00500001c001d1002050305034018505940894041010079954210001610141120540c00003202100c03c81c04601c80c4400600c0d1601101d550440040d890b5110008000c0c4d401c041c4666803040d44c9152905103922102e42a00090b210000c2c200000580650704a44a078078011505985c2c00040400c8035680c0307a0f411150802c00140c075a0b01e049034a00d840c0d0360180000d1092601035400c000c040c3c00004040c01062090704001000d86082508195a00008002c01030001c030390b8100824010910f0502000300fa5486c0d04c0c0c681d5034881030b16006480324208024501115100750250511000580e404512030358041b185001e07602c2c181d520032200e000c0c0315500c03196800070407120203101401c0c407503150010305d80b08045909803900c5044d081e4400b50341d03c0007441014000391504000c0740015020203081052244034680250 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 594895422 1250 594894172 594894191
    0xc0d0309080d1a03070b03180607021005071b0609140d050f0c0708012903070f03030e010e100504080c0f060412061410080c01030606080a0b0301090c0b0a18060905090406 75
    0xb45003c050750800c6c00428004020010840341903c280f0300c00c2c08600d0041c0ca024140301c4000303513507081041740a10308a51514001343c1117178800c61991400102c0c9194140007024503052060050860721800ea0b01c495200700007250074440000d2400d00e40ca82942c40d03a01d04410350102c1341c556000300c61804110f0040396000034000ca000d00072080b00d00a1881100d007070346815544150540640f040305400380d000903000300701602c80300d0107520441ea098100b2581c181000d00048980c10b117569045507200c0003000000104990003c081d00503030b0f5909084410300030401c4104010b240150056640c895410082403100e09403441015815a00c2518082000441e05890240f501030840e44c2c0c100220002e8420407080c6e90070001110b501a00b03090401a0504000005201103401401c46184940714010607030031ba1402d6002c00d00c0742c0c0e004a0181c8055403a200041c41c0e6502510360a000a07100d09107501405400b0120b5600f1030324a5102d1483e85450b017018801108401801550182c1c2c0c2c40a000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 594896672 1250 594895422 594895429
    0x100309110301020d02040e220f03020a051e0f07210f06091203060501031503030e01020a060504080909010503030c070e040314070605090613170c070b0d020c0d0309080d1a 75
    0x130076003005540409a02d880c1810b0a503180707d07200401242d00b2200440c018048080010414122180c120380c0860b484000340c2026460301d843e0b080000c00f130b8070034448014004802082045104003038032082e03071000c0d84045001c6030740b403110740620015800c00c0d20f01c100c521948500c043c46918400e41d224480b0022540790304044a66408081d5100d40318a800d10300e00651611038407025000034201000001d41139a011113540c0c225020080038803414114040030307a07000300241803c40345e1002d4140501e1400d03240ca003035181c020b608614000d414400010541e89000300030b0b149903000680c001c042140c03a0011484240303001401c26024041c050300905140058540202051400761502003001d00307061038498170784035000380700c1c400c04004514090002614100701050300c801103074038184c0742c992400d0718600f812036542c002095140700181034064100160041c242c004070500a8840c42030095809409458084000500025040260b200c50407126848010b250f102a1201c081e4192001e012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 594897922 1250 594896672 594896677
    0x50706030e100e0f2505010c03120e010b04020a030b0301150602030328060902032a092b20101418041e060f030503160305070210090303021b10030911030102 69
    0x712070500c2c1c0305d80f901108041804d18914014082840e0404500d40c950301e00601a070b01240a410049842c2c541c00c00303024500750401001d0f404004c02c11541e81e03040080150041c40700b10039050187d402c0101b25444500d079040705404641c0f06030007551450760707100e5502051007442c05910100d10202c04002c0741341e07609481002d0241c1118400160360381080da542d688511401c0701018008103211380c1d0012005901c80940b10340c42c034103881c0142070003041d0140e85004800312401350070244c180c9080d0810301007891000450b004220090f800003850ba0002e00c02c4005c2e00c05d1100c0c010910f5030140c0e00050041500a00141c1c0f248546090b0a816034000a4142e50486800d001001c5c3c5030f80260b0203810240c40764600901c500800220308503d903640c2d045c1c6030b000e4004880c44501042d0010814580200202c0b000e4503801080d10010520111000e484d01d0140e00050700184201141e080103a500000144e9800750014a00d5200007a50241140940040e0404507003d0b1041c4440c0425500d09001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 594899172 1250 594897922 594897943
    0x105072a080d02360607111305100e0402010c0209070e100201060f1d0a05061201111b030307021b031e0309121204062a03020604050706030e100e0f 65
    0xc0541d542c03010b01d015402c882c1e41318001408070b00088842c1c2200c1d41007a07400989000c401e90780c29458803034600b003d0b1500009200300542150b00f540701c04140e60802d91207a40300d081550700828441e078039101040510341d41200c0003400304074404248000b40c1340c041505507100141d880c0184001e078400d004148290f202400103030260703440c0c41050100e28a0704e040030018002800301e008540700040407002c54644050243d032803881ea070b800824016181c00280900d1841004024010b403020700c2003200c2d85620800c800d140301006104102d00c2c3c80000301c1260300400c90740d8010464152410f80001c9140040390b1056410b107d06030180c6841f4014070300030700c2205a42006107888200d05001c0c84180401e070f2024516a40103003541d981c0071445201540c0603210076180c8440340350070758000350703601c4903091070b18619000c1c0011f1480105640003c200d803150b40300d00c00b5a15140ea40d4102035050b200510341c0c900d480c7d00440700007044215030f40d1004034807012690484030010507000020303080540461 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 594900422 1250 594899172 594899197
    0x1502072d0308090a0b0c0313080403080d05010f14010e0102010e300f0301060f0e0409110f0306090a0f0206041505070b010b09060403030e19120506090105072a08 71
    0x1210300d400d1507040003400d5071040340d0901514201031305a482088020f0700408041840e5008008a1036060300007480340341071070384000095580d9480e801e0601c01c030f8004c0c0e00313801052800c140000c01d003001e410540108440100c00c41e4001800a00015603000409102490456594000021079848204241103072040481012902d01d00c2e1501300c0c4030003aa4611641c8440c980c03c0003010a00754a000440313045500c1031030490060300411404884259a240b110b07a4460700348083c0c442030040c0010b0107211900105ca8410750481542d09141d141c03401195000328681014880e000810102c8034a034090034401418140380545540312955051822186180020808109401000000d03080c1e0f60141141085507820200e1040001f00944514000142004104030040140f44c448080c8030080e1b21203c40c1e0654142e49402d20002c64481c1080d00b51158801c506c0400d44104041c412a802480c0396601d0f1004024000305c2c498a1098910b46c0070182107000c03524201245507400074040c0940c0c1c40303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 594901672 1250 594900422 594900503
    0xa0809010c1b090b0321030402240a030204051011030a03020f0c030a031b110601170f010608060709060509090f090708071211032e0f0f0b030d0c150207 67
    0x11081c54902882d1904a0f45ca92090b01c3d50006d40300410740550398420360488100f0f031301e5440e40c141041c14480c85c40c4040030502c00401d804242e6070b05900640269601030701da028110b00320104c22602c0c01d006110b45601c2d60010014515030030301ca9001409a0328500504e030740340c036410341006840c55001000840c0060b0f6035540e419074403040d0030740e00807d04002d49040003020308800322143d15a141032050074060f003841d0f1000300d012441809a0780120320210001c00890790390794182a100c1000b1102240000d15441e00407070214002c50031740700000f0340074140603a41e65a4541d82001014080c12485243c0314116001070784c4c04003044050301410f4071f080891001c00462601403004040000040d21941001d04041480030f06406c1c4008403031505480c0360303c03520301600c4540c0101040304841c4030207810304801c107444440503002468803501c154201c40b000c1082c000c044a081c1800e4200400319070090303100000c0307542c0d9030300079021450103245101301d8030440800001303001200d00c1c02000310311600d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 594902922 1250 594901672 594901691
    0x6190905040b0c0f0a030504020d02041409060606040b040512011d01020d1109030c0f01030f0608150c04050607080f040f060e04050711100509150702100e0a0809010c1b09 75
    0x503402c0040e0400f035510070150503e400b458400c00035001380d0310210101030751200060155680c8074141d10741070307070040d100700404c003000c20170462048000c90f500d846500c10480818880d0034000c0869085911841d6000e080c24103090400401600c22a0045441d40d2034030106143d4000d90103400d5151240b02c1c0c0010396608402803002c007070303d800360103c07940c0c5c600501003501c01d502d000c5035296883c5421076070b40707000051800041e0020301d0b080f017841504a09d460004038054400003240c1585d00b0f200300840200d540c3d80325140c002880740d070107016003002003403005100055410300589850306c80700300130320b0030a91103e4550f02c1d00692a403020001441c1d00c1c4a205003030400d0303c1074030f403c004207250140c400c098940100b5a1800110060080160b8400001c2c20900040c00071020a804180c806c0c8440d041840f00207644070611a20300c45000c1c5880d5001802003800164140c0b400d030b00c031340003e052021007401540c040107403400c00c0d900310490401005600700465200c1c0080d00c0c201c01d000401c0c000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 594904172 1250 594902922 594902933
    0x4120c05190906140f090a0f021804050f070c03051b01053103020d200105090d020f06090a0201080711010c09090f140f07020f2a0f13050619090504 65
    0x40c60b80104440000310301c0490854130b1700c50114880b080180d40c0a0000d840e07180d100b50042c0a034401007400d0300e101055421009207040c41210040c032046800307114980314124209045a4280c0b80c1c0f001045111005400284c051000303044252100c50b0055070495a85264509443e01140c1307034010a18821400b00384014940001c9074800d02801d20002d955001e543d000c1d694452001c00381c000e00c55001700300100c0e0900c0c020400d11000c000303c000d0082d400e0544949540d009030b050624054003890200030228100020840d20600a01c001801100781d04d4005440d8104094114000c201400c2000c1200e81000d00031010025496a1084505440c0c039040c0411240c50741014080142014082c6120740d2a8002843d0000d104c9110302c1800c0e03d410f00244d10304900c1c80d09000d078034091901103142401001884c04030300d000010030031410f0032041c410080d1224000a040d0342c886a10000800350130710590102d980004003030b00101c02000480007840400c081903000c4001c1079294801c0104120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 594905422 1250 594904172 594904181
    0x10e010c0b073b01270f1a070503030703020a0c060905060403020715080411030a05060f040c051c060c140d05091203090d05030901060b0c0d02060105030c010504120c051909 76
    0x6000f250a0700c054001040d450000c580118446810042d8404030554050031030140744006544100345208520765669610422451510aa408002c04c011940e5003078a059021102540e40c010061440d41d03072004c8042c3c00a4101080c04030800061443e6200041d29a01c41c0dc01071502880c014107035480c09290080c9000101e40000f800d0140601040918a400100003600107501c0030442d031a500388400800e01e82400c0c040081c01502c00e28013031158580c00c4c5000c5070b015600510f1000d43c0561140140181d83c1400c08134160540c01208490f808500d4a03842416400f0703542c80d160145c0714010b0820840b5410600220780c08a03650703801d01401078020086440525502c009081c203600c0c4c0701c81950340364541110205c0a00c100003000507000c50003903002034042d21500c0000c680f580c0203000c03460b80c5c41c1c0c00a07031008058407400002103450315001581c86000141659103524081c10001415103c4c00400c004850340d4070030300d1300428140c2e900602c1003c45800c990325a41c40514000716001600e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 594906672 1250 594905422 594905477
    0x40303091407051c060e03040f210b060d1506060e01120b03031204030e100c03020c09061e01020a02040c0302070b10120822060503010501090603060b030105010e010c0b07 75
    0x59020990810550322203844d00c820030410300704518a001c000d400c105000d0581100545868040080e001c284001b5008846007034691070040300c594840010700701f8901c0c100134030020b445410b070880000c0685c6000360340421058403425500701200802000c000a0764900c1d00303c40017103006444091441c0d40d0103100511880301458050008540090200c0d840c0d12844100b218131592540003d0141401450303040c10100d40034024042c0021002d000410442254504a0050103100b450002a19040b100b0502405009040990280444518102c200c0f1003200040c154010b100c800005641e442c480d1843c6200d140c1c07409030f038652061801c0300000c4801448174059910030346042c00850014200c1801603684071030ba032607448020913507c03d01d600c0c220118110300040d03000041380d401e42c8000594101c3d602030300c500040a40300e0702c0c01d805844040c0165981660103200403c40c540c440e0100a411030818107004007540000d4503080c00b00ea004480000200c3c890605090380300e4641c41c68a0444c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 594907922 1250 594906672 594906713
    0x10c081b0f070605040201110d0e1e10030e010605030601120501050c0a0e060702010c050303190e0703030e060d110f0309070b27060c0d120506041b0c030306030b04030309 75
    0x40c8580401880c1090080c0341016089a9803500005e045900031f141c040000b80c2104100e4488040c1032000404465100d803689029070541c1000c44007548568458684103440184899880d09117a01d00300d00601459198075903564881d40002610b84041c0003c1d0f010b070030f080f599950750368000e04285082d208090b0070300c40058420040300c940c895100614800350002107800c1c640d200c20382d0004071803151042e02c0251a40c040001031102c3c10a5485d030802081c10074910034002880601e00e46502e0714150302c000f8001c100c0f0384070a5002850003400820107942040c0c0002101103a000c1440c0300b54110009040d60b9440000a11110340d4042140320001c0814081c85450301d24203210740c1000c10040c500400d80c500c5041c00d898070550b15201075a03260050741c001c9400700c0014090041807101d2960843e5501c915010100d0214105030240d0300c0702c000c40ca40b00140300024140e003111190240ba41c25800c1581c0c2c0d240100019800001460259029030b0b13000c2600d071042e0409000c0d20040c80c014444c0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 594909172 1250 594907922 594907927
    0x525021813110612010e0411030606010c0305031e04121805010507020405090f06070c0c150504180e0a0c0e0709030c0b0a020102071b0e010603020309191103010c081b 73
    0x3190750441400001c002d034890390075040501c1c500e011400038012003003000103250ba00400490310244851201e48254042c103401401c0d043e8881c203260f2107010681c1c8032400192000580008070b4050f000641e0481e8148040941d000b0820304040801c04c4156030450351403082c03070b52407102154401c51907618050890741c10102d0b6443c040020b00184918003000b8010343d05c4d8000602400d80031300c1203d4280c0b2003c41038031503501d0a03260082c6000ba414070211400c0624010106810b072007082c034080010380b607446242c07511b420160348072004c02c030420807003d2041d101e641c180e52490302845108100c0f403207013204250260424030207085001c0010440341c10094051001c0000c00e2901c15860202c13079460f03000c1c540d03d41030000e089001e4451060b002e880203081c038010940c507141c0c1d001440304032080c4d0054180b80381d882c0c82c0200c0607844155041d042d182d0005140f1845501d125608a002e140314005075a48941050701090075108040d04400100d0000b204100c02100c1041848425080401c1046d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 594910422 1250 594909172 594909181
    0x2070305210922111e120f10030f030206040624090203090c04150311102304090c0207090b0a06140a140304060905010f0c0e0f0105250218 61
    0x80c80c0900030199204900142182842c00740301c40803c0440c0744842414040d110410359654107590010070031003800714a242d501c107580c00a000c02d440c070030b0342854480075a6488181e0800c0483d00d020300500c1c04a241034400000040c94a2585903490748039401520142c0b403d401c12000700c0702c480405400200040055542101e0740f00040e03415035550303100058980d00e481041d5850078101c3d02c04035070412b00d442c4094a01c040c2d0120080100c91041c0742408013013200004bc008003408103902c5a0114111003da9292041104080c0304403444544046040c03135501c580c0c2c6403d65074440c08800160b00706020a01c12070f080750242800140c2c06480381035070a031500900030034022440083d0541404c0100342e4102c10b0b4400c0c3e01e85c10581780081c040d19180c0c00d0504000d0000c0480d640d0072107256280200100490300030340195140c2c0c0d0281e440341002c1c0c13003244052107000511450403d0410500f00112a400a642400040012800c20006801e1000d52040c0708400009590006c0080112030811 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 594911672 1250 594910422 594910483
    0xc151514011407390e090a1b08030f180102031e030a090206030403051e0a02120315040e06070905012118050f0c0f030102040e07050d02040302090a140f0613090203030405030d02070305 81
    0x115030052340040001480d159421052184801507080701c02c0d036000005190482101d803a01600d50b180d03c0348513190714500018010f84c0c1d41d2040d1382c000080d546418401281001840d4040c6901c0400204003003028030003a0300244859208a40071030200d2000700e16148004801c01c40307a54040050110781c1d01e000e0060300c0196445040f1503148000b03010010000d5548030601d0b4a6a04045026006110b0086084c40450b03c5181c01c480c100c00041101c240021690f10407610910504041044d200c1d0842c0000800000341004908148804080c1d001c010005002001102c18419400000d071241d4445441007088800300d9800b0248030340e00600007440700c030922001d1250071030000e007043c41d0303100c02074030b103003c080d0045501c06540074004100b0440083c6a030740058102c00a8200b108080f566094002e4558003020b40c0c11030f400c182c4508a204090440358020360a2a00060441e0709055a4500091520b6511205000180c012500401c01c0000030001000008400004406103951510300c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 594912922 1250 594911672 594911683
    0x60901060516061506050a180b0403110f120d0f05070c2c0f0105040501090e1f06090207201c02100c151514011407390e09 54
    0x1c406003240350303200c02c80401002d54855103c0c554803880614040341c3c0c410016109412103414400840e10388c40200c1c1074030041c400300d00280c40482881ea41002c0c25601c808440810020300300f6041340c0c030000350414942d122141c3d01d915840c6500203007820040c0440041031040d0028010b020b000301071142d0700c0051004081c0d0000c2e0707449080e00c44881070312034000755501c0621040d4010403840c000b0130310412031841c48030241a01e0003a9010f02c521390f0794200e400b007100c00c13011003000d094009c50141c1e02c451241030310107900401d178548081812501c68610354101c0e4081803084030414609081c072072400136146044000010f044514541004040080140401c50000001d1203180d2890030281c481d40600000c1145030b1700807160046001340000c60303000038001d2400700142c11380c544000041d126140c0d6460340702290185d40f921103c600c2460b00740c0068000355821111607900142d82d242030006000402d4105a03c500c08000c80040882c404038038032559000f40b82040c02a104010748170000180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 594914172 1250 594912922 594912937
    0x90d1d1315030812070906050c060a0f020405030321060f03060c0a02160620030a0e01050304020607051204090501090209150a201024290409020d050609010605 70
    0x201280381020007038500d00455940e040107000060210358514101300d03203030090744102d090303440f81c4041c00d440d20029101c0d8042d041c2e0440c401d60010000500d120100e0700503a801d0030a00d1005420192180c0c006801d6401c00744001c002d8403807591026000060503944182c0140054400c2c28412546001080e01e40600901c0c481a0102c00100b211502e07100700b2110b03c2003d4071007444104c0b81e445907402800000c1800c0c91200d020301d0000b1074104000040704a825070380c9284c032600703071609404006640d242c2008100742c0e40414203000700e1000c50030038081e000819800c0303a040c5a559040c414070004441c0b040c1c1201c01e041e4410300402c405910b8081e4036001028025000c0c0703858807400c02c0119098034102d5801a0318070301da80c500984600c00082c4046a40076062000d10209101e00d007038940d4222a004014540c1885800030842d01c82d8220403004480000300382da0101014210030180a9402a403101c8502540000c51102506092044680280d81210b100c0c06551502d94001c0c01c1c0d018100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 594915422 1250 594914172 594914209
    0xd050309010815090c0c1c0203190c020619020f030a0504090902061b03032d01150c051b010905031c03050c1303150c080f011203031103090d1d 63
    0x10110301d03620f40c00d0325400c804041c01840c0c07200d50318050684441d1508400031010180c41440740d001d0020324a200032a071140c2d01caa0045080840260324400008034034000b060a02080c4000000036031a100001c050110b20340e004009803981e17080009241003058a124034041d0028070513012402c0d03000f01140c0407510041c201080c0c01166000141d498441d01400d01404514403c2c0d4041215011002d90320a82a42860103a0340207080c00c0d000e00f903822902c45500100c101e50042c01401005860074847c182c003441d03c450049480d035642e600c0c0c0700c0504400e10740f1003050545242c0325a8054000d03005000203901800821070420802c08042c0203059a03441410345540c0056110701c00c80d0706889000700300ca48440c401315a0f9003010034580c1148512400714900f003e410a60542c080c0011034040c00051211014983c13038405a1050b810003034201b2010192190011802480120040c50003103600750081c0051501ea41c0000c0e00c40c0e0180000044482c1c0450100003840d0740707400c14a402c514844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 594916672 1250 594915422 594915437
    0x1e06052503020703031202071e08070807030e13020a1b151e1103090a1b091e05011707060e0a030c0605030f06040908091e060a03090506060d05030901 66
    0x440c1690200680062035038411548100004241507001810804890003504d844800d12041003200059110b030301000760000c10302c41e01c1941d4030140b4080c0c04040e1800b8551007428941241d803000c0c071b00d9100e4041500080d1403103c4003030480c03030540c80d504007200c04901c2c11860440e4802c0050040c0d4503c80d140e039400240040030200380400c8074019000c500c013104040200c1c9030700c200900d0034070020300340b1131603403902c0c09030058403480300141100d00445411000b44807050342a40c0300072030784065001120740c1001c201400164003406010301598101031aa417081c1c2d400414034424120b48050340645012150804c010280100208581c03081d110369143c03e80c40d641e40c0c24003281d1a900c59600040c40c00192003400110517170701501450080c40603202c050102d440b800104070541d104010050000c0d0b4007000a1540340c5040c1d0728030a5000341132200b01d0f000c52007107000940550845091400400d031580da580081103424465568059002c68aa2942e8106515075598901854041e1410701800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 594917922 1250 594916672 594916687
    0x2090f010e031015060206011d0f1003170301080f16140d0c080703230d0509041409011a01080906040b100902030a0204170a0f1502090306040507030201091e0605 71
    0x1c0c0030a000030f1600400600030261000100c00c0000100c2c41118014018440045031004e00708042e00e070035000c0c501c4c000c0d8082d00c2d01c010040180401504010440c1c0b8030400000020f100c012612841d2003420f25819100e40c9840121400d02191080c00502034201c50100c06409400042c0081070740e00d8a01e540d13000d0501c01000c554030b1010048081c04d244020800040c6031080020002c00741c0344100038a0310080703000d0f142d0388500918000f01d0807880d0001d00301c41d0385640c41400509184500200045601803200600c04100c0d43c040e5440b4940f651a200259000d4803424660031100c1420f1801461502d4020600e6480e0400644010040c18544010408404012003c84040d1030215421540c0303003007280c0c072500254403d05c165141c0c241d9001c0c0324000b8071004111038214941128074807a9120b42d507642c1a4143ca41c20100905059080c001c14003282c4080004610540c8618010301c0b2050541c000500240526880356005404100201f02c1c81806d42c9102002c45481d81017040d12901e9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 594919172 1250 594917922 594917929
    0x350324130c2c030d09080c0907031b021e121204060b0a0b1c02270a12060902030c151c0b12030703090503030322081308030711030102090f010e 63
    0x2040c0032004000c4428225440030b2900d10300303007803809070303049044070740000c030300682914189000e05c00c0d18902c0e040700031a01414140380d240c40750700400300d19001a240d0344010740c04415a165844a0f80103a000c4030741d03455500c54005105840041d80002404102554591490244240c89040310715440d00c00c0440d041205d550840b07480610b005142c0382c0344940306c1c0c1c0d070b02013160024602480076106a8400c2e0024503020300c00c40b0b03006282001c1034611700c10b8001000d0100d80802d9001c2e90400508040040c840d0000701602e64400d1007084086481070090041610304844c550318a48243c0c0ea02d105224224005c1040320001c00313400000d20581d001c039003130b0040104080510290801e001d4514807140c000084024610b0602c203440390880f00d03490b2814503559000031a0700f402940c03446100101d460f690140318251040c0b040c00c480d031802e401c2c076009018880f280c0d405140c440d8008178440d82040011030840030f000c0000c0c0c00071401d000104000511460341c0b42d20483c140302c00c5228002e6241c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 594920422 1250 594919172 594919187
    0x2010b0f031b2115060603130f030c170405120106050d0f0501110a20011e0905031c0204170a0b0105060c100c080901110702030604350324130c 63
    0x124034040c5612010b0421440c2d40c5910240407240c4a04800ca40000c007176141400c280d9004080700c0400030700c494100e40d209030240c040c4090a805004180351010002a004204a421010440c111544842c40d1030140600c80d03206030040c000590402400b4130003a2100030008807044e0308a100010800c0346401c04038014000c000384410202c3e80026559203a0741c120b0300f042510480c000c840c6541d184442c10311807c8a115040c40d80000c0c04081241e00409091341004c0030303aa015009680c07030141e41040d441d011f500d01c80c60340403281d5004502003200e1004058441724001012000c0d020f001400c0e40c80b09110380c014000c151269801142c1140c0500741040072020000c0c03103103000c00444a1880020740110b00850b00c1641e55800c00c0c0c1c024850b400b2941c1074926995005c0c0c0141400e80313960703940440b17480d11503001a85c454014014248c03d811078a2059100101a801c555900d050210314810201c20528001c030440000070300aa035a42c8940c1c54240c62034800c03440000c0e090114420884448 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 594921672 1250 594920422 594920449
    0x603050c1914041508010801020c0a14010f0e07030614100302011202040506071a06221802060a030c0f080702030a11070b1305040c0f0207090e0c0405150102010b0f031b 74
    0x10001c80e010502503889484180502144c0d114842143e070b845016500340c0c2b045a030840340d030b0703040304080e18000f582d000c03040c6c3c9500381c0100c004201c503101c1d400d00c1022504c04589205059101007020424082c0a106000307511110f16914240ca240404041c8050703410391000034100038044588154a50456040d9800b03040300a00923541d6075600c0c200040000e41d8243c4500000841c0c1e00410000c0c90304161148061a89031220300c0b00ea0000b01c0761100409141902201a40044080c43c00596441c00100412081e0391800124010001c0000300900d0f20501c40400b40401c1409105049400100b43c501f0700c8280c1ca07040070107c2a06800c6030405000e41d2006030030500106004120401055003507094a2065908012058902d0001c5400d40382501800d00907070020f01c82809880301c41d170800490381d15010700300c4283c111082d000c1012100221f8500c3d08581c10214102410740c2d081c0a1820080d000301c0700c81b0304921480001a03198281d40e03030542101d0580c41003a41d0030b0b40311030760142c00c03d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 594922922 1250 594921672 594921707
    0x90915010507170c0f0606010903140f03030705120f1003060915020a0302041a0301121e02150702100216090f0e0706020319050403050d21061403070603050c19 70
    0x340f4003038a52a50160092031240c841805556440c0c0f0090400181080c0301d10b005a42d1603003d5803a44c0ca540c00f20100203841180c0a00038540f5100d0340b400100006c50044086994903595102d03011030740146103001814040c0300072150000e00c0003d00e083d044007010f40740c1002c80022000d00e90301d425207880e41c52201a401c0280041191800f041d01f59000c1d2040703e034645a400040c000b0240101558882401504224181b416884003c00c55100c1401503403110718001616094882d000241c18114041201c615210002200b808500b00b00a4a18054a4500044c1004100c80c4c0f03000b00300749101c2c0206130303040e43c0d1160f40c02d202d14026000350127076580c0d140640303680c0ca8039510002d44070380c402014001c1e0026007400080782e082c0300f1012102203c0d0084003400c2d817410407100c1151030481c04c0b2040e1350044c6100e400d00c40c00001c40d100f803034003d100100d41d40c464540444e00345070500225a0060f014585400100030030010041c040349d25030266200500180741440b0340643c3c1842c18124403182 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 594924172 1250 594922922 594922943
    0x4060e0307170307020f0105060a0306090219121a04031d01230c06060604150e042304050f01021c1508071701050c2526091302090915010507 62
    0xb00700304850300460081003d80c0c292039010410500c0b840c2601c030290307007003508510985020000310312991306c02c16030302e48003c110900001102124002c119042d070840b8041c02c142c006880100917500d0002422030400c85610317505c82c6469103002e80302200c907000300445c4101008030250700da84103a0211060003880c908016818070300301001c0712290803103a40c0c2c607028800c28000c0384551a111055408640000002143c8040e4030031044401111644d41950450b40310615a42c501c0c1c40c002c1c40c1070700304956168055641c40c203810000d00d00b00e003200000c1c0c9207074810440e003e85e1005020f215003054030000e0000c02c42c0141080b1000102c0101da102e070500f8000d8000100780042c0414407140c0740c80c100f40c000c2c4515190b1120b206000d00c41d02171941d1060902c1c20144c01d81d148800040003144e03020701c500b0044c600050341c01d498011075a01145101d4140020f4480052074095503501d0800e00000c021401c010b144804510110700140090640f003d80e029a0041341e0700c58421500c00c40e610900101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 594925422 1250 594924172 594924203
    0xa060e300609010b12030a140f03090a020103050709181d011103072601030605060102011e020a140306032e090f02100f021b0303040308070c0501110604030804060e0307 74
    0x1074940380c056441100340c1d401e014400350301e4640b015420040401030405989400386089080c1d0301503006032004ca501c604240059461101d118014510031205000034112408007031000400700d41c1c004080c80305000103507009000701c890011910724440801d140008042100c4540a80000d0540c09a41080c3d800d10980b0211700a0180c0958012100b644a58102d80040110000c0c0203c40d02525000010f040c001007001c1041ca0300b1050301700e4010b000001d40c030b4040700c07410600420225400f0b0800c03500019458000b0750300602d4480701d00c03d013500050550410000181c0c0b19210104249403030070024949040d246103c2031003c0114985420410820f4510301e03140d0240040c1c6041603206003200d1100d203101a000d244144424080c55014101e00620034445400f41c8400c000c44940501c800d1002100143d18030004201d9203002e18000c14141d840c00000501500c81d24510900d250805014040004c0e0081d0010750465800351005c204045101306852842c010320601404c641c001e03045c4034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 594926672 1250 594925422 594925519
    0x105120c0613150203071106031f060f0e040506030d0c150207150c0804050a121803060e070b0c0606010503130605070e030105070e01021c05040f06110c0a060e 70
    0xe07085aa084000f08251400140180d8490190b1000900130003052000c001c0580b07001001542d21000f016441c04c07001c1c04c03211081140c011550070084c040760260742038021661300405c480c250b105045030140503501e001c0001c80e403a0003260380031009002146107500c0400c410445010344941880e18115141c0d201810f141c400004214001500b0f2841e0180d510040c0e8800c44010748a55041801030a40c030115036906904410360100c0c1408100051208180b0030340d8900c11807008601030203000c5204040b0031185410003100b03600c10400c0080410449440100c081503040d8001c0090906646950307480c0024501d880c00300c14010700035854201082503d41e002241c07a40100400c1d00204410f0ba60343d64162112a8415405400740e0b00c0381114411444101007202d440c41000d181040c00c05035101d0300b582c50f218541d0040d402240105520754003940c03040180503010607040f6a500003c9240c864050701d88a4400d102c5030041400c000f031250758003c2c0361001811440031608011100c0b0000111 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 594927922 1250 594926672 594926707
    0x4080d030f0506060304201203220f18020a051605030a020c0f0d111507230105010303050a051621030e03040e180f0604111002150105120c06 62
    0x6007070075460880401c190f03052074000e603031080d5030001c2c18030382c0391503a155405848120071012079800306080d80700c5404e840040c4081c1602c03000e01d840203a00c1e21403203e140e2403900c805410200101442c001c04200307440407407140e842c5188041d03000680e120b141810498042c8248004402c190b0698500c581c20410000700510006040340d0948405901e10410080040d060b4848168000700c001c40d04404103041a00044208070700a2504503451b80010100009801c034160030340e154100302c0072664902d41144d230628640f07690714000b0051981182c2d0094181c0c000c5098150805c08041903182882200c0b0700040302540e0040d1140b140c004500d40151300300214014001c00107400c0600c0b104c00084000103aa054881401001ea542c0d6911105140700e4141c04c0040300d058858515500b07101c03601800042d0080d40140862400b5140c0070050245041040001d4003c6522100380e9129240c0c0c0340c9040d5041d0784007201d0801d0700c5500c012860b0301d4103600c030313016940c41840010302e4207201e410200d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 594929172 1250 594927922 594927941
    0x90f0103051507090512010204090504081b060601080f0727090b0102070509040f020d1b030b0f0403090e06010c1e050d1b0206031312020f1612120504080d03 69
    0x8540003030100007075402c98450103403040c1011401c044020301c42407178a0004001400310b4840010305041e039900d400e03003d85000351001e65080100050307140280d80d80b904441d44e0307114000021700844c107203180000c01c3e0802c0104000c080718941408101003e00c50701a500a08843c045009a110b1050301e0309124101c0038458040700c5403910311042c0035175001041c0d040480714010503004c51680d540d224102242d43d1400d040382c0c411401a808000075400d5410340160340f00e24000080342601314502004040809000100366451301c1d020040041e501c01c0c40314043d81c030384901d4960340d512014010b072a000d00c55100113140c1001e00e6034200c1159920b40310000e4040c018411140d012808450580359002d500640c1c404000348030901d017000d4100a001150040607004d1103004106030b98542000d0344254000d00d00040e0854901000314680400803c9640c1003560b40c0e07009001d1500384e070080c011680c1500144480703a400743c032010240c020300a4600030040041641c00d40b1030f44100043c0100310550 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 594930422 1250 594929172 594929183
    0x5060411030d020a05031b0a14010903030501050f100f11070311190b1b07150206040b160c11040b150a0f0206070f050d060302040f0e102d0605090f0103 67
    0x50b4100c825a10019454018640040285287c10401e034400710885105e440c1d81c60070f41c814604044002020362006c03600c805515000080c00710034030b00c1d0080c1078401c10781c0304034030841e0700001e00d5103103035130304048030f560710859080000c5816000042580c240d644030651082c94041c0080010500c000c1c24243c0201460450f03020b6040055110740c40c2da070003024040d01401c03d00c2072000f10035144800c18240441c80110b811034070441c1d0341d19001410000300900c20001a00034801b48000c0041d00d40d500740d04510405960340500700480d2004040c20074510003d80380510214948007141c89541c8030321031112000c3c2c03a2869070705681c5007001880d40041398100c00501d0009003500750f02e1011030502e0091034103a4507a41d011088030f104030380c1078010354040751105e55100350000c0143d40f40e01c51185202644071012800c2e00010404908115003400304030321041c00e0000342d41d150210300c0c11401c46101c03000c0d2804812201c1c402d84000a000640046410184140134400c1c0e54840c42d21340e038100d03031051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 594931672 1250 594930422 594930433
    0x10060201050c0322030219111201290d020d0b071101061d04020103021215040b0f03120c0a0f0318081c0311090607120f02060c040b160506041103 64
    0x2c0d80300c4030043c4000c41d620600343c5400e081c09001d0320000c28030144054003d2048541c21075410104891100b8010000c076040a401c100c0c19009041030000c04400710a14402005030024402040041e41240c200c81008402c14010701c8140e0b0380c503d42c250302e40540241469031162010324080800f100e066460b0008507020260314032802405000d07440580740041044840c07485104400ea51401c40600304905241e000e0050702e0301d1807844034046125041c440409600514480180022034044801c0c190051800d50f1024541d524001540001c003420030100c036030398084100c035072400d00c00e004d18000e26210707203055480f00f032540c01351900301d0002c0750f4004140c1d40fa5550309003035643c400300380001000720101c4200400840c025400010640a0f80c54041d1a06020350009030042d40107075002c98030000c00801007010719038002c0038250140b60700e0005002c7d43c02d0a010070003050003507100e40001d000300060311501c5d80c1c1c100c000c03211320180d02001b25005810113240c03010700b00712000c80c260f000b4810f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 594932922 1250 594931672 594931681
    0x50d061701022122020f030a0501050115050f0405130b090f0105041103040b07080702010f06030828091404090827060a0f0806030a0b07180801060f06110c06031006020105 75
    0x1100705590007143c64105201d942130142070180c5060012841c143d07807191000000f050540c03801e10968080034444c83c0001010b6060654080f031600341c1c0c3e4107107403c0090034000807001c000c070a0111020f6500480d8009401c4403040a00c1c40904880400d0a400420b488103008a9083d041031860507280c01320340c180440002d2030601710b168001250017800041d102008903003028058272074150004ca10348004141c00c0391218001d41030760b106500072221103d00140f44600c0320300300d4408a0480790700c00803a002c0410038841c01400f50030b20b40076246280080700078084d801d90701c0d58010710215070320031469516580c0058154143d10b100b814040d41c1e16511000c0c0c0d90320782c038100f0704484180d82030380c45200c03001c0080802216403030001492907405102e0340c3c0c0c0e240e001c60782200d5120f204144954031a0941411540c10348489030b01c070340c42a02540e0400e44181b01c40302600f914042580d80b1840c14240f00041402001c0c40c00c2c0a0070380064020b100001841304646110120b0070a0b90584d400178002c540301c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 594934172 1250 594932922 594932977
    0x16030515070c1203150f1401020f070e0f250f110a080a050c0a06060e16030509030307120209210c09100e060d05030c07052e050d06170102 61
    0x112004001c1c02c1e103c05040c808035290182d40301c400d0400e0b01c000c0036074080b500c5940e80004031400d0782001d1035000506403035a000d503034100020509402d0040c00f03400c440d07282c01000400300a001c4c2000d084941aa000990b5a07510002a410040360654140c40d002c007440d480504140320310f017007040021f9560808040c1079070300015084c040b0f96012426038500b2030702c94021250f9070851a60000c1a015840310f01011810b54050000601213072401c10100e81482080e044507000710104001c145420841084030007070001c01a264400402d0901c54400040d01c1030000080c45079104581d4080120b4800ba2098901a4101c10546200c00100c50304041c044040182000046030303126450310a40c0300a02c0444501e0304030b0354210748050301000c1c0152140e6a5981150410385103210281e100304000c00142c0307400140e5108000d00c90403004041d56141a90b0000c0c5841e1407a000103005002600e039a0344420780d4060002865178108860306144041ca4240c080e6201c0c60503d84004c1078001d88105446 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 594935422 1250 594934172 594934187
    0x6070e0a05120d030f02040e04050309190e0703050402040e0604140d030b062a2b030504080928030c030c0e07020a0b090a06050435070b06031603051507 67
    0xc007440240b15150482400710044c100d10b4600005c80c41d000c0c00001900845807181a02542c40b07180074513141c90111080c01401a504115440c020007010001c00000b0a40600799420665600d0081150b0359180040b03170141c000f13030220005074800c40c402c1005005c01c0c0354000d440321104030180c1c0c45006070081e0450544944d0b51502d0f921450400015030704613242900038000301803070b00404508060308100142041e0782001116079058030342501c0807207056080d0782940000d1103800e003000340c1c0c1019118140c0c40e000700480b444c01219031250341c0c94803681350a100880c0741030203402d0b46040b6840e4901a101d00340184422996a4401e40001c2611144406600d01c81d0039030790700070281220342e62101030708150007604998660007424018008102e09000342c40c8204d0185907042d080100c0090b1041f900003042c0640e2844c0b4504503180e000034030b8500100e030703620398014001d4903242d200e1400003410080707a014600003a00750284000108500410790644440c000c00c103ca182c1c0c1d45a0303100741c4404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 594936672 1250 594935422 594935449
    0xb0c090111010b10051c020c0a0507050402070b010b070c0819020102011a090c0a030204080109080903100605010e060c1f090c0b03070203030a1d0d030e011116170c06070e0a05 77
    0x1c2070130a82200120710610103020b4042001c4516030321200c40c0c0080108030b1b03020740008440781d001500c0210600000f0016400280001c1e2000c600d091869101d400700f040040c09281140d0000180d54000d2050122200016210540507135241e426445041e600b084140c01c400c034055401c180040c0c02100e40060019000b002c0a00071401d2030740c400fa00c28555a200c01104800e050782408007081c0150240b0410202d00e00c0356032015550016082018500056486c124021500300003081c0f0160743d10080000e034142c003c0d0740458440c504104401d04124038410304180c03400d4802d407407240c5030489070808030845010380c540303000711612002900b80350320080311403101503802000418a04403140d800080c2070340301d41d00d5070325414050303100107414114020b0502c0002900d0b41a2603c06010a10501e4441020400c940d40b43c0141c1c0d5100d005903801000e006807403014904003000050359481c01705d8400d28072030019a2528030304260090404a40680307480c0c01006084804a2141020b05500aa0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 594937922 1250 594936672 594936679
    0x170106031203090804030c060e011106240d0b0a050103110102060906060625060e06060f0a050f0d0b04120e0d051c0e03030d060e06010f05030c160b0c090111010b 71
    0x5181018160090400980102c5104d10200400004500c0340182c7c0006400c081e62404151221640014030752140d40c18010882d401004c240b1214020383c4580700208603403110070318154030421001035042140000082c0c5403084135402c00030768145e01d61002e41a680b0a440c2d030039088001c1c8004990b500d41c201e0349110158000404a080b80c03407d000601103c02030380b011504401c0c41c2484283c101500c010b012106280c403070914889503001809540e034402000d8a000300028030900019025822501c9000d0040c3c42400e0842c4e00394850143c6507018903044207400d29503052518012001140b201a0394001420544408105180910b0503c500c160058003c2041e52201c101c00e001012030b2134128001c0c41005c003940301150301c0501c041c16040032a003c1c0040d495240c4180301c01c146030b000345250704000e5944094011580c00000380e03600201000071454840100065440c1c4210700e0b85006880f4a20020400600c02e007000b000f404600800e90301c410681100307500c484e09980d03214517010f61 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 594939172 1250 594937922 594937943
    0x1d060405071703041d04062d090606080706020d0807050306061c06030b07020a050606030a02030d05030a060b0d0c0f090b0a030b060d020304050a21090603230c0417010603 75
    0x140c11100346462410b600d184041ea4075165482500703283c000300114901810724442801c10003803100314440c041c948038014122140c9141105500784241001d01e0280c89072070380c0c030100c0509000403580312101400005048030340282d01c0d900c010307643d103440e081c0860009141000042999111340240ca00603040501030505225200b80c1940141200d44620052241d03201400400b245440321000d01502079a0054403114485d0300340380d400c1100050409000c0c0d4054004040142c50006000141e50241e01e01a034072130f2202070504018120a42c030081c0b1111010825000c104a260b02c10038401c102070301e07420000309500380d00341c5501c00d0a01c160034000784180000098a400303508807010400b0020242840c0008081564040ba0030645054030164000e401d80000c0182c0c040034101462040e0700310800022462600400540060040104154030f030a030400e08541c40c040700300e01e0610b282c0b000c01c000c1c0c5018002c5044c960040e00c0741141031b9880c407201102d01c03001842000184c075005a043e54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 594940422 1250 594939172 594939179
    0x160c171c091a0706180c0f060302031b0703260f07030e070329041401060b03090d03090c050d0b06030601090c05161a13060b060a0f0c02041e1d06040507 67
    0x141d140c00c02c800648005403605c1e124280041d1400101440340c5c03040c01c40e0104641004503403010303262103410001c1854410800e10040ca0344070b41c10406040c01011900b40d5507000d51804a03240c08981d021050302d2030f0341c08280480003d403101c401c0d00c02c00d03100580b140c05507294a030803029205002c000003c036410040341403010500d45454580305080c20403080307030981c110444009204104580a441014030751981210901081c061032009100e060702c66030442c00c3c0120030340d403610300ba20326140901d590390302c103201007200900ca41d50050200906411120940703050404903410100e030f17100e10a000d0f04001143c03260300d610610007030400d01e80e141814074a1541c03036100441685e81c005c0e600c80441c1903264102d0340c00c0410340c40c885d50000146c0140410245442400d5601c0b400d01d85100300e005112000f46554844003a40500c6040d190200001a40c0c2c00460300a2118003594840c0c15880c007051040000d458000804280c2d0720303011010780e80e003000e448680300d80c000d460041c0950011003040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 594941672 1250 594940422 594940469
    0x60f031e0705030f0618062b0305091302071e050a060207030201050405070b03130b060f031903021002030609041128030308060d0b060907020708070609060e04050c160c171c09 77
    0x4121f89240480090001c16100a405080008c02c1d0450000b00c001030300311502e04041c80c82401c82c808072801503003007040c0ca07650984036080403011809000f02d0ba14049003480020081c03296560b40042003156600c955080090180c1000c0b00c055031107100b10000040e81d141c0e618102c901c10140280d80c00303105c0400b0b0356039004404005c1d18803070340109840150009135405100611490007e80400c02c1a80034900d0082c2c24440d104942002c0310b8410310030002c840d250034800070391060f40500c040459040860004903601c0d40c28605503171091400d82c00300b07883c07103c4d42e10740c505490090704c0e40e00b1240d031694108840c0980407100200101c40c0c0e000403d069041481c591074009086005890780640ca46140b24900f00c0c40d541314000188494204216194004196002007801030b01c3c14020303490000f402c00024400c007400c1042840c1030301c04031414042c1c802c00c284042e000d207030010303091001c1840c0843c2d5141c444004c10f042100f16009001019401240c10f0011960300050344802007100c0c1802 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 594942922 1250 594941672 594941689
    0x30e01030f090b07050a08010b0f0901110a060e030406120b030a020d050f030f1201060f0c26031504050f1605070309031a15030c060f031e0705030f061806 68
    0xc0240480d00c0300300800c009100058581e00c82c003120745e02c0c103803114640400144000d8040c0c1c41007400c5882001244c00d801024412222207003c00e0812000071041010154030380070a005014101e540b40c401c5a0a888001000a00c1201c88554503410425881d0441008940e01c2c2d00071568107510030400c610040c141000715040c514010420b4a0315103403003200f85411070f404003d01d500500c1c40050703400e6036a5200c45025000d44024900220144072008006c4e140b440c4c0d111b800b174013140b90b0300030345000b440c0387e56110bd8040a218407000d03140e040003d14402195000400a0322490070301000640040301c0000760351145402100a064405e441038003524260b0004500b58104078620101101242e00004480c0d80c3e030110041c1d400d0246400f400c405a07410048102038441d80207101104603c0d238540d003c0d03e00e14041021040c0d62600d411482000080809408a98200c8000100005142c111014520410036401030b8148c036510b001c01c1007080400d07070402d0039000320311001181e42801c21105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 594944172 1250 594942922 594942941
    0x40b07050c0d1824080903160803010f1233020a0f1103032806080106080619090c090c030e01050c2710050a2c10020703030e0103 57
    0x1000d501d40000040c0300ea050404841c400c0c03010400300e1034502450800d01504100800182c416040a44544030301500120601e80c0000700700030030440407a048000900484151108075090b050050138070b0f1030300b81c1c010341091180d81d1b00c200c125000003602e208115000000340d035101c155814400c151344190b007008500700308400003294070401b2004c05440144002c00306400710b80c44421500c01528401440c0300601c4401d82d0b800c0d0818001e11420508412604012038450200c40c0c680e05684a2000028811580122001d44c20440009020b403c0400c0c5a4001d024112107101c0b00a000b500907400e60744003803402420300e446200304100300c000340e42c003405200460389408240700701b030181c203142541d1003900e400d500d81d1f0000801c3d0402c2c803030800c07145814401030b009480c00c5042d441c001420070107941e014402071040c00030302d00c7c0080344120300c4081c02d40d85403c0c04040e07004004e2015a1410b50054926004001c3c16940070009800003d990040b25495510b809041e08200d0044020700398460 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 594945422 1250 594944172 594944177
    0x1413261b03040f18180c06031a09040605180a030507030507020f19090b030f120a17090a060c020313170a02090906060103200a0807092607060314040b07 67
    0x12000c1903001c559001c80d001400440c039400d5812a40413000030466019005081211595510000006e040a25400c080303540303030b060001d4044561030a50241802c1d00420941c044005001c110801c07000e50310450142d00e6038107002010780c1a10712003507926002d500707019010038402d00292001a1150008241c00751010308200360200d51036000c25400040c0c0304103100304044c88101404108041d00c01d81810340c804030f00030800c00440f503001a44a0002da0f4a09903074003000166107240a01590b000110f201c2590801e422510749109031030307211207551004881c6181011520b0304214400425605101d5406403003c043d103140519041800b0012003401985020703410704000903a4070940b00301c4c446c18060340600075600c0e00034001800c40c0c0390192116010703030002d1040e02c580c1040030141c940c0b4207580d081c840710302d4451003800e071950a0b07140e0040b4101d8004200c01c1c440f01d1820b5800f602580803010450b02041d0300d6032400d4003641e221040349408041c00354006004108441001034000c03a990 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 594946672 1250 594945422 594945427
    0x30f07090513052e090b030a050303011217041d15130f0e150c0f120103050a06050708162607080103050c01140901030b041413261b03 59
    0x41d0041240c10081c07211510469070748078104101c1684800700e0708805880c11850f034010008034040840303040464028904556035075440201d40c0c1c0c504100c00f04105400c0012680c4030340c1d40d0f10140740b244000c3d41d01295040700f4a0203003c0d21000c15800d940075500d00d0a0805035104041c00300c071920040042c409080c03000d40060400054440c0e0511103d00302c8000000320b80c2000b032002840c1610040c2d2302c0c1c00040c0d4080f4071000803008054000719009030070210010f541b1890100219242e00852a03144120035602000000f00080010203038a41303442180e09001540d64440141d031460310803a81502c50004419494452603c1184011180c0c1d103a00d140b85c5443d880b1503031030912103504490000210b0132250051043c41000c2080b403950100c03d10f8140c401e0241443d02c100140513401440b41415103440c481e1b0007039a21500003503041d030400490b445a074905881d0402c24017415000039141340d00d002c1750146000f01d0070180b22940000c0041001e03d41300035196041c089907004500f240090106 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 594947922 1250 594946672 594946679
    0x2090f040b130f0b01021c050316090306110c0115081b011206060207050a080309010905060706290414010f050607030908030d0605010f18180905011409010606090605030f0709 77
    0x640c8038550942101c450b00107004c0d5600d1001901c0c001c030003078544445030307009100a030303406520000f1a540b01d84c6030490380d080c000b09048140d074402d2254000421183c10b0469100260404902500800100300001e02c0080001c05e0f000a054910303000d50007040e0030007489102a0590600d1b45008100c041c94440300c086912100e20341140c0311a0042030040e0442e500c00c011310300c0c250724400c02800400d0091440c2c03800345000a44540268810b8500a10740841c640301880340c0c030750040c048440d81d2311035940c0c007004000342d20150070642c400ca50712031858641840309490382c02841506948065000c0010203040804000542c1c000d660100d01300081000c8c00302e07450000b07001800300c003032004034041000ca00341800075062400340003e9508220314030040003589401003484200729807143d1402507800840030f0f03001c8042c003414403010f0565800d00926041d003551200805115201c40402000840e07102c0c4804c840d00725891044400217201400860f10071191074040c180c01c51960704003150f91594 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 594949172 1250 594947922 594947959
    0x200d0213061d100909060f0509071a0a02071802190203030105011e0807030b12010c08150405040f06230c0c010c080702150c040302060c030c0d0302090f040b 69
    0x680c0030a005015840340000c0040c0d0071141460704000300102d00c848001c0c60041c000382508072a40c800c1006094070380701c840050100550051543c00f4207074809204501e000e404181e0745407580c0c8615111141000c020111605540050301c241510b154082c0807894a803154402d1180d984c500c40b545019420410361500d481101c1005e04031030201e40156899615050015090040700e040c81941c0342e001e180716002299000c1070065000701c1c21306002448030020008a0700b500418275143d81258680080c0f00030300d9421581080c07081c05007003a003a4a503d2a04140310a131002502c3c018095809030030702d0000604030343c0102d410819940441110350b059108412081181504d407140d0703440001440c94004035003800755101000c441c0c00c00c0703803445c1031966000359540c00e050102560440110003040004c02040d04403801160010f19170b944945101c08a0741d26544544402c035883d12a000c500900030b802030080c0c0700403a02c01858090007240b80c03c103000280c00a002120b40c0110709411510a00d80c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 594950422 1250 594949172 594949189
    0x60706060b0309100509030703211d01091b03050c1c0506010e180a150c0212030c0c24040210210b1503160e060f04030302060a0f0504200d02 62
    0x10811401484131185254501048960181030602e02d03400c10001e0201003030b0800038260460322121401400a500c0e030030003500a10f41e1002c03040d06000510810b44e00810150028512203000328906071500f2888020541480100d210080c000c1e04030f0541c0c000f1601d052520180300440e2503036a09200302403617840d41d090480076040461402c0d10b0505203c103040340f0340407983c03c02100c04010148404103855400541d00341400000f003a64840344100c846510038403032200d03000e0b8444c0300c82d0f840e07050080080b0040d421103002d0b10490310990604c11144034208200454130b400034002e055050f1519024429400c5a000024007400500c040340d40c9940c3c20041820000d10141c10300141071084203003000110f180b8821203955140051062040d109801c4000d00100000da007803100d52087c4caa00802d216000d07121490200081c007081c004203060f00840c5c2c1600c200319074142000505044a2f03048121071050310080c0403080010396145810703c000c00f05c10500d1100529000316100c040e0300241200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 594951672 1250 594950422 594950431
    0x5130c030f060506030109150e0f06090d022107030c03090b070f0c060302070314031f080d0201050703110a080603071a0924030a1509050703051005120705060706060b03 74
    0x60070610046028040707648180754105004a00a001c0075850341c540000c8880d6001c0d917070845559540020514410800012074214241d0041c0d83c200c1c5040800c40c0d444108100030700c2c015019881c005000905914008001c000c8014202402d000715038908031540c88000c10110288441a980403400c4043c04020b03000d9140302d0200084850705516107001444141c3c0e11040515005110030000281c0048243c09922412290682c40380d69501c103800510805200720242c10202d408040342002021820100f4200240c0003404182c840c0c203411002c44110300c00e1440c00f8181800f081001601c1540c045401080050440d8402901c4403401507a1100401500075142800110003400c0c2c10020b81454503040d070360b14010041d11081901c002c0340d02c0001c05454003280c3c1c80d00d8400d415200c108070320001c1c01c00c00c03808128520702450060300030101902d0f914154243c40400244520f02204542c14120458025052403440d160600c01c1c0f60b0880002200c0850703c848020a00009101c0a184034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 594952922 1250 594951672 594951683
    0x50703141209010c050c0705010c060b04050403050c0f0c0a0501050a0207091806050f01060e150c01020f030117160b09010c050a0809100c050a0206030606090901090605013005130c03 80
    0x1942041154242118844000c2206208051041c001d50500100700041180c00070b00344554032b0b812600e8680300038091085960307130042c907002c10b00c0149a40000640044081c1ca4112416040003c40c0a55940e6100303c0700c0368499804001031009500c00c402034024801c4500480e14041c7d204c82c1c034001520b0000c802600445800700b0364809010090241d10380003d80900300c602c05506180d00117141c0710840d55403500942c1c42510f8149c00002c0d01044420010940008645504440031030452a1b0f0083c468400b82d400c01c054500f00e1410082420070000c047c100f050001c4510380b04204442d904030b81103180c1881a40c000b02000b081d070034044030f10902d01ca00150b542d1644004108049051400546010415040219400100c00123030b2450b00031b40441d10342e0b4807a136407500041c0c400c2c42401d101507000300201c8000144c10200d504801c0c240c88091b02c494005003019008100140c603a0300d2840e49200181b6008490544960f2043c0e41181456008820040081d00c403080d010f48250b01c100c41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 594954172 1250 594952922 594952957
    0xb040e060c22080705040221011206050c19080901090203060a0501030c060f0c1104110c0706081f05100c05060c090301060f03020609100504050a09090b0906060108010605070314 78
    0x1401850280244a030100001c015040703418510140c4d80c80300c0d1030251a004507070015401038800c0300f410000758800905480d009181da1960019150300e064110101c82007410600440c641000007020b841d4410b1039406001043c40d02c42400b02d031080b0024000302d080395601d400d003a01503103082c06810302c0b8080356400450694510728262011801d507921580400500f8401c00141076840b070944151a5040f42100b99060a000300050040481004c0c50740080780010b000c0e80b100c3c4c0041500001c494141d22480140d035035607042000b2100c0010200c48111041d10740070300007858180100c040014551900040191981d84d40900d0f0010507a07000181402c08640c0f01e1a40c0360901441000d031054048003100f845c03450340465403e029006440d8440c071281210080400d02c5802a9001050004d140c14035050fa102030240c006c3c060550306a8540c95000001355400c000021000c0c061300044c2c0d80c442c03490b880c0c564121075641140800303c00b08641c0003164003103004050094942001580c204c00b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 594955422 1250 594954172 594954187
    0xe100b0f1003021209010908040905101517010b090a0315020d090507080606031c03020307110118020405011d19020f03010e06120f19060e1c081008060a0b040e060c 72
    0x4216841c000c001610aa04018404001406800584085031402440422f158440041c2d42c100d4410507080342c0d08a143c080d0f46060169031210840b80c00182e4035080d03400d10303601d030f614100300c610500030b5081c3c00516501e0b082002036400c2d002c00104070111000142892050700d0084141c4000100076039035607101c04030a1103010b10070701a4641064044000300f4110844002012448111030040000e056012000070030550164404420070f4040c0c0008025003030f04071039007030000c042c4464140d0055261070300200e000c43c900010b00f405501240202940341d039480c000c000f00420200328641000742c0a0100045014590010b140a42110042d4608a1401900744000d0030001e450620b042c3e40542094100102e010910042020400707107001d004101509002e00074024514000c2001c0c42801850320b46401c060b6480000f19050b03a540c4482a00d846c051303425081514020f080c4181c020750302085241c5002d0b4084003142901400c0403560031080311003582002c07070440303516030310810009040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 594956672 1250 594955422 594955447
    0x4050a090210020c030a06020a020c090a05092503110d08030c120c091305060a080313060e0105071a190207060b03060c16080304020a0f060903150e100b0f100302 71
    0x2c0141c1c058500c0181664044000060398500380e50f04098801640041c0401400f4400c2c499140c018002400301741c2503040c18800c8400800c2c0861306040c4902801001362070b0349080c0543d1041c5902400c1d00c504109043d510764840100080b40c00a81c032003005051040000c0c1860702840c810000542e202ea29981242c0d20b0070301141c0010011041c1e05020026040507030349051040740380c4284c00000040355600c1c1c00110701001003030341000d0614400480d0711001d00c0c9512903403070140c818640c0d4820005101d0001541e9074010010024022440e481c0510103c1c43e40c004d080b640710b5006107050b0540c058408940c03040b64002681a01c04c1902c03043c00310f00ca41410049150020700101e0b420385048440341400f460348094802c001c20052000002c00e09541c0c42c0030483e4040d0002c201c203d1a00d50fa1142c01400d03007403251104131503030036189103030548803c8a44208014208000094851502e40c0c100045c010a8503101069100f07040d44050740490700d545241c2c2100c1403482d24010395545020204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 594957922 1250 594956672 594956689
    0x90c07050105130816060b1e0301060e1b0f0f07080a0206060901140d11040513140703150e1e0d1205090a02010809031e04061d06040501050a0e04050a0902 68
    0x1e9049410310000000003680300720450303c5ca04602011405000414a01000581032020a00394401554500d00c0070003100c814440d401c0d85c004400070456039503500820000400d04445c480501c80d110b80a01003080010401022910216204c81e46854400c01114007242c100c08000e90308201c010640c10707000c0360104203294200000302c514407015890618032600c05100d5066045c06071854010103000c024000b104240c500000400902c0f6610301600d003004d1420342d08905441c907003031981c9086203450010a0800907039410082440301d030058940e20001410b0481c81070052440744518010b000d0f1044408a0442c80d500005000303a910085002010145104080c1454078500f00030f101c400700c0006407424a059083c280603c01e90b03201103101e4110b009180b0b8215001400c84c3d08003014400b40d40040c000d90b070301c40c0c96030b00032240d80c448514039401009026a812000412043c011580908041d0200c0c401c43d1600d845045c3ca0203000c01c00365801611103c0d5038030703104d038009811850320a41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 594959172 1250 594957922 594957931
    0x3080405010f09050c0103090302210306010f030219110c120102030702070f050f0f060705071d160206040209090a05100603061b230c010203160320030402100e090c07050105 76
    0x2803c1c00031034540d4a6490721840d86034040c80c149035581e11040105402449000c044e017254107040d01c0da200c0854103107146a88220380d0355001076a148003403e9218007a10a8600880e00010700c80401504000b0a866142e04c040403c2c0c40c034480c00c42c0c3c6294a95804d00d400c0c0c0c4c20750b00480091703224146100c0c041d1800f8004d40140c65000309081c4140b040fa16a000d010100e160103d45980c1e4424000000c0740051203014070140490241000109004440e182c0724890084441404007641d42d0300c00003200c4801480101e58016003141002c02c0c0549082001550044514002d0b00c1c50f003046940d90614000000d48107101540d241c8804000340001449111b22032400503126140c10880c841c0c0080c4a280085007481410400a00410749190380806891566a24000031503907820310b5070115140c5100324481c003000030300f06038140789081d603010001d55960a040c616203066803280d03800c108401c0c04900d2402c0c00c200c19040304440c559103000340d82d070040c60109010340da42d680d6130900ca82540c50090 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 594960422 1250 594959172 594959201
    0x9060f0905031203071107150806040b06030a0c021606110609030a1715040c05130504020a02190809181b03100303050d110d0204170d0e28030308040501 67
    0x290400ca1502c012030540d180c1000b000c0d001d40d682d650f00c5000e5a081141e80000d0801e40300303110002c95805230381c07403602c4204561520350b030a85039184030800041d180651241a042101800070543c440c129400080e030070122401a03441200303041d0401e1a0700c402c65446000098045507070b440c490001400f1058000880f10040c503d00401c4943c09041039805244941020f03110a0005a403c07200f8204240c07141c1c0f0060060020703500410005103a03070440e01d0b801c81a540c0d24080020907140a1003183d0a8031700fa070700a0300b2400a0b83d4a620300d01604c141050325442c10800c00440305540314440c100b164400c0d140c41400ca42458240c00070329103132007000032144240800c1800900b2071a102c5100c101ca82c1407a1040d915034140c201c0802900c0984d8400c82000e8020890b81d12500240d00540290384084226000b205000340e0660b5446c00b14244c454013040c0d94140e20381c001e0500c1064625440d10b00110602c103002901c43c9010a0149640250000384e03425080c801009001c1c0a0010781040f01d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 594961672 1250 594960422 594960437
    0x50a0b01020c0d051623180c0a050f0703020a17030423030d1406010e0109180902030a0b1f0e040c09020d060e16030621060b01090302030a0309060f 65
    0x400081d640b0103060103202d20484000710520100003040140c0040c01d10411074080400e96078002d603241c50040606044403440c8620009000390410701c00d881001074a6103401211521401450817203580310030000020000104101398504021000424046200303a00a0030380054604124400c248801400410900100180004200d41c6a03103007070b00400050444448078000da000343c5c60b5206180303148c0c640c181005602a4034109801c02a480380c0e100380c0707038a004400400c004403200e1409004104140c84100296807402003650300c0f90006602c041c0444207144ca40e9101c260180d042195000d00780141150312080102c1328181072002030806600c0480c0c070b400c05983d031582c0c0008500450324142e5010030142c0440c41c16812040081c10820458a51420f1406100380200340c18041d6401081c2403070400100483c0d00030b1900000c545043c817446201c1d60642c1d03041d01070130303291603035038100040d024011000d6541800f540006600c07945419440c40e10b805800303080c001c81c4804450500000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 594962922 1250 594961672 594961691
    0x1e060b120106200f0a0203061f0902090a0f0905070e040c17060a120804080d0906022e0f1a0901061b1704080708010b191e030204050a0c03050a 63
    0x2080100c03419100e280c01d09803003102c9800f1031000c0316040c200000d203451282c80000445201c000c24111304d041d000398241c480b655108058402070007000c07203120a0080395000100b101941d1071303000c0c0081035401019044c583d40d0f078a044c1d0304050002c2d00f040d45c14990f0340061222040d00540130001c00b4405440c14840580407950240903000403100c0210b42003003850003c0d080341d90395032010014103800030fa401281d040034100118950045e000f240204c1c0310b5a82c12442983c0140203140884000f68020444034440940d0000150ba07000310481c4a4014000845900800b601036424628040c0c0400500740d4000412300781480082c1241d6400b07920304000501505a02c982d8403800440e0308000045525007500d82a00011900c09030a840000041000300c1c2c402004680c11040b0303084070000780990325400c010002080320404100d103012603103034402c018042c0790480c414110b840320341c94111425501d0700454162030080300ea00c0041940ca41d0001c40140d098403a840c1c11188120042125500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 594964028 1106 594962922 594962947
    0x1a0d1e02040c2105011413020403060c11010b0a05011b14030c011d1501030609060b040f0f061208070b060604090f0606081320131e060b 60
    0x143c0030000c148a8420b8021a41070740e080095140a00c540038040041e250b902e02c10300400c1c66000d00c4000081407081c45401c6031082c03030384c9450f00d492428210707250031602c0e03203a603491040c0d44030001844113136401980080600010b41e1944400d8003142001c080344150401d0710020313440005880e20011006402c407081510414400031500d20580a106840b03800286040800c41030800c0104045540c68000e805558081e400c0020584081404103064801d40300c0d4111400d46c0307520061082442511405c002491040c20140c851115951001014403508201400542c50302000c90502c0d40c1747c1d4100c5000313004100040202c81c0e04001408040c00d018440d14000c6100a0b001600c0312440410031116503500810704010b82030940503180244040d55a6581c1200d168100c002d03902d00d05208200d2a048810111030342c05004100ca641554080c1d0441110031105010b103245915 = true := by decide +kernel

theorem cover : BRFrame.Cov 594784172 594964028 := by
  have h0 := BRFrame.cov_init 594784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 594784172 ≤ n) (h2 : n < 594964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
