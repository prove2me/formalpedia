-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3772
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:37:55.61398+00:00
-- url     : https://prove2.me/submissions/e22a4f4d-fa67-4b45-958c-eb93cf9a5642

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 678237410 ≤ n < 678417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 678238660 1250 678237410 678237431
    0x192a0803033607240e0105031506030f040b0c070302060a0f060305160509100b030c13031e0501060e010e07030e010e030c0f0d0305040c0b0702060d051e0105060f04030b041406040b0a 80
    0x60000c055140c4c0010a00c40c01540c40d071580514081c651040c00d09050b2483c014904000890580c4101ea46003094050003062100344a41c034406660310150920015180159548010b5600c02e001080d07600150b464060090b140542e40d0056001107074808100c035100164920070704108611402601d0041d000180000c0024501740360300c0f000c60b000b80810ba480c54903000d2402005901444000321211100400000000ca000030b003901748010300c143d0288112498640b00d82510504d034054000e50308403c00611080e14494800364200c1c19500700081c06c0e42000101e5409131503c0803d104103030001240da082c2d02000440c480c0c4c13800c210041510720031040300b81c054084800944010f40b080c0c403040000d12144000304010480719000400c3d9604000c603500c03805040d188115010313803a1800c14611001102c1c0c20a84290141400322506400c1103c03102e400c04080c0580c5c031001e07202400320780c042402d104064002e824084241030568030103141500349040642e8041e1200c0d00315516054050700b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 678239910 1250 678238660 678238709
    0x7060b030105130803091c111204031104020d06230315071403070e0a0b040503010b0409111005040315020a0f02030f0a11192a0803033607 61
    0x2d03c280f03078014010641541c25100c201c41e80c1c000905a181d80d00c240d03c090025441c1c4c50503200706080b02640e035616001307441031000f42005506088441803010a00040c400242d0303001b404c040f0b00c0015103005845041400d0658044d0109901120000006006015080180d4084c0121980041d421100f040507017503408003003000111041c400103003902c5004542903030440c3c01560028960b151040c2c40881c8040000c445103041e45c003e0700d980b9000142000030381001e011f580c5100500300c07020005a8030030340f900311000c01e00c00c1e8000d204d00f0801e0304500c0e0721805003050700d015682040400c42a40d58000061000354007000c07050303022907650303000307190001d100100700c680c10b48190840c141000071444003515076800c400044c1d54036004018142c800c4c0c070b1092110f4a902400f131381c001c043c3c180c10608a442401510b5090007081606660706201c5460000700300d9401080c101440d14030a040c1c0c03030002401903c108000d855103a924900c0314801c00f00000e0f040265900032a804440d030207050200d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 678241160 1250 678239910 678239921
    0x30a0306051804120c050d0c061406030a0303020a05040f0b180901030f020105090a050d0501050a05010f0303200c1905030c060304020d030e150f03220b01030f030509040e0307060b0301 81
    0x60b000704100008002502103034068003140c0b003d041140c05442282e4425041c4a00b118030780300005c07400d006c134100307111a602070440c9092440ca02c640f401e04120b0003007510742c91822005002c0c95000600300010510034411a0000d15150303842c4850203840d520004001c2d4004090b01c40501541c403000e407198a480040c0754103d0707034002400340b540340440d8010740d100e07041801d0f159800701c00054001100e0315000c0c24820b1480c407480000446280140c0b06d10111041038000703c02040203401300b8400203030440c3c078444619017501d0f2414100140003455030719011661000c50380003412855a5001280e82103c002d0aa99044007650800340003041800341c64001200c021794400ba2059203100800c4c05840078000380f00e805401d2550585250014041d0f0782d100c1501000c2880b000001c0081044001e10088841d00040031072300300d000c803151507003a801035060001401881110750501d040600810403210401001380c000d020081c8525891034aa07006901c0549403103003010307800401c1d40b5061184 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 678242410 1250 678241160 678241189
    0x90f07050109032012030a0906030b010e0405090304050a030521090d351209030430021302190e102a0f020109060c0b07050705031b030a030605 63
    0x214000c0a20f903450f40400d8981c01e106030b10b00320f2003240c45010300351103940812803a565000000e50341d071440d1000c020400d80150703000c003042525040150403241e0780310400c02c41600c0c00700c4d000b084c16100c0660b140d0a41c412a4040d550007944007a0000800c400454080d80d00302280740e01407491040c0b610b8800c014480e00d07130043d52140300100380000190070760711076001414440c00c01021401c40d00180350f039000071126440c0c858410109020082440e1710b0184c42e8440c030004003640c10203150102400184202d496003c01d10000400103040c100c41880850303035410740040c0011911000c03c04100000e40c807900440d114006040d00c602252805110b15202000000e840a500c00c54011400c4803090b0408601080c003583e0194505104d1400502c1b513881036002d81c0c0440030900c0c891001410720b920f2940711809111280200d40c02082c29007a0342d0350300c440a400c19607610702c034a1500034110712074005c071030b100a854032101d4010300c0c00c00406031100a00341d0324104200d40d2194101320019001150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 678243660 1250 678242410 678242417
    0x3070b0f0a0c1b06110c030c1503041704060f08090c0a031410051e01120c09051302031f150e0c0706140a0c02120306010c1b09060b03090f070501 64
    0x1168400e580b14408031040710380188607000002c0603e4089444401d4564130280c0001c8490680c01c014101c18014104070000840042a01c1c0126101003501d002d0b40b4040090010404000101072004020b4420103071084800c8103640c440d1078a40150a0210800180c80003403025800507800c0d140c0062100c070b01c80402803218600a24669565032048032440c041c4016004100d800d0442604a00405015803510070011110301c50381c0d00740145c4601f05920038280c410108002c4004950700d1010708003030790007102000c00d00e41d403800c0811000c0301c0021002500361003000307008200f05460508102c041c0301410f8007030003495191001181c00c410240540c48002d0880c0000c2031101c1207800080410720310504001c108407090381e403071060095040f0341c03160515407100d180c0510564140800c800c144000c01e1210b00754100f00d00002e00070301e41040c00802d007511f540c98841e401c40c1c1d031030754580081508140901501c0c0c1c840060719880d80003501d00c00310714459003442151291000c1440c906584c810394 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 678244910 1250 678243660 678243667
    0x1c08090a0f051e010209040f11030c21091501050603190e0c0307060f2c090402030f030307020a0c050a03050c061608040306091104060b04060c03030f0c080603070b0f 73
    0x320342040d210562142120203100d4410f00d080701508014580c100390b002e030f000068481c0095001c0c4005ea54101c05402c1d101d42c9007041d00d40c159081801a030742c0000801c211a0313100c420b0305d20a030b0409407a1030b015140c2c001401d820007c0c1c00f6000100014010000064244c96991b6a0103001c090300090b6207050519039990342e9070201018a6204e0071104200400312041c40041c503011a00309503254015800242d001000c008a80b6003200e0840250444032041e01d44030202c000306a1320703442184c0400d41c07040c8049404103082d598104901e00001d0340c1e910640b42d0741e00308614003a45d1049040021559031508800015681c9090780b035031012640c1003401340c8138040028040103407962000c44503980c60002e032580c20011549000103080654032403c0d0005001c0c1c4c10b410021850b46e410402d5510407414803c052105941d840c06480c1207070387c01e040640240781246001c0e0041d00c21101da4401aa00e0b2685080d1180c1d80414000e000d000198284c03400b880d100c551241d098890315240004504041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 678246160 1250 678244910 678244913
    0xe09101a191508090f0705010905060708130f05130905060a090c0b030907051e031b0f030105101406030907031b0e1003060e010216060902060f0c1c08090a 68
    0x3141d0355500340c600c035004809499182c002400300800035022040c0029810010000c15040400c40b4120010038139006010072440c1c0130000700a03640314001d160090b040442e1200400c440981940e51078400046d503a154980c660085403110f031081e20450348640c41c14510003008000a1085d42a4550008040e0890b66184001d40e000b070406044100e50300811142c0c0042c01400351405140100f203410301504003146808100201c803031700710452f103500c000561107142080e68006504480140e00803c80d8061440e6800092120f504821a680e055400c10040118010031401c8a600365481c05100d507400c040200240502800122001491039210135420300100d0100c034041031100046031811000c45403a407080c0400e200b420b0f5400c42e8038110b03019050003000060300480000701d903880000c5040c4020011a00d200041000c4040d140c3ca0780d604c2d602056460303a00880c1c00b240e00f0b16403596a17502c1d00110303555950850b06203040c00248a520170414041c410201a801031003800010001035849 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 678247410 1250 678246160 678246169
    0x619050607020f0d0b0a0b09090d0e01120f0f0f0209060708030606190201141602030d0e030f030906070e090408091c02090106020708070f05091b040308040e09101a 72
    0x1d403080e80c3c41000c1e00705000b20365035960301442a46100d1884507090f0700741041e007241520030217040ca034452043d078003c1040d000c030b00141c0950741034000c3c80c0280420241100599940340c881510f606c0341820b0410380700c5480c046800202d11210448000c20030103406980349003c80c012031202c141d002404215240100303500034059600980f0042900b0724000e041d1024002c440720550700400580d465104141210710700410711507103c000c4c0751143d201d150b01900025124460358a11134149940e80c41c00c09807903482002030354001102d4941041d41d80c10b21040003962001c0403921a40003034140e04042415051a074501402540e01030340241c2003480c0c0350100001541d038445500c203070801920f0a400580d42c1c1029880c024a00c540180c00c83d103041a031418205802074001d0b030b1500f9800081002a0345420707040a43c00301c00c02c01c080800b2000183c240c0c1c002d1280303030b00260078080301050116003030469051440c040c1d040c400442d040203000d442c0350b100752041682d041100c182c0c00140e01d82c080c1003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 678248660 1250 678247410 678247417
    0x1401061a1305091021060506040b0a0603150302060315030d020d09060c11130f0b030a02030604080f0d050a0606030b031f1d0f01020d06120b010501030f020c030a0f020606190506 78
    0x504c101209100d41c40b8240204040446003c0c1c01038040d9144a0328140700d800d10880c1d1b04410251000d00001900c0c101080b500016403080404041e0b440612003112102904504055540104802d680741065040ca6648030b4081104910030300807c2c04a0f80340306e0000907102d000e4a5585c8803202098074119003a503c441e01000e05503540c0d0284141c80140d0350b1000101104903003103030b1000405415044403201100c51310f0482030700942c40a00b440025903400100181c0c4030380d020403419582c4540801c020140e026015140d440a0704060030b02c0344200071074100c0c9060750103543c2d08201209800781015581c0a08503940c0a8036420b803028141e00000d141c1000c10440e0b00c489404410061080c4140d00d0441a01358001c211795010078182e990b00200d004140041400a04a2403143d2654550b6894464103208003818540c0d03404100980303901d80d40549811581c52001c3c1d030f40f00e0451100103001e850010030360100500900700010300314605400a035101075001c001c031140a5090406001c81c603071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 678249910 1250 678248660 678248671
    0x90237150f0c081908070e0306240d060902030607080c16060e1504142e0b180403020d052515181a070503130606031401061a130509 58
    0xc080300400b0214800c0c3e80200b0340307041412a48110400003190003480e01101074400c004000413800c0c030314070f00d5030006080c68001441c505000103d10801c440a035001c5080c01b4030342d4100d07000c0e22003002404229400b00d901d00d40241c0540d205a80c1e0700d00106d0300110103c51044030082c01f4030044010803080c002c003454040c0300310300016005172144007003442e113628005401328010b0504100401c1244030a6510195541080180a00101c0340c030f803403e4600b408802c0210692503804890504002900282150540940b81e002c204001710001014107200300e174294058070030000b010314481e105404540c800062601c1440c0c251445404c00304d4002c441c41c0d01591600304040003481c10507920f00c180f81040b08c0070716070030001c1402c61074100c0c800303840081825a02914001009006a0040d086079880100400e0001e600002e920b80704000b4002c54101070f0080710010780080c1c9104d4154410310a8a000d01c80d100001d034451400c0c84031511800e0b142a030111181d0781c0c10090f6042400c011608031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 678251160 1250 678249910 678249917
    0x4030806010e19051905011e0903020a120302011d0601050d150c080414191104140405250308040506030c0c011b1b02180901090237150f 60
    0x160005000120a9034a40c01041c100f20303520f6070204224508050003040c0d40360310b5400e00749054500400a01403004001c0a6081041c50351800b43e5414401c40c0740801075940107111500c040d07101d8103e501c030140d40307203802c82c0998a0040c8410200032400158940002560014681c40e07080400b03025141c4120002100c5e03015100300314100e540803034000c044c2c611140740e0350a24645424103108020203c007004050b190b811440c46201d02001005001c1c1041d904074025075107040c0c09a020900074803001511b4605c4208180600041080105080140b141b442c04280c08258400700082111015440300078030000d410007007044641451006158031116000007a41040710742010f00e800d4031105400f40082c0d900384200307402c04035001160065411031742e40d400301c0580603507030100780b540b00c20028002841440c1000a86206404d4018084a540c003509480c00b018440f10b8000f65212201d07101080040244543e070030000724400c4140448020300b2219299a030a000c0075101d84011560004c1003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 678252410 1250 678251160 678251177
    0xf041e0e03090639101a06030a06140609090f070905120307052413020319030806090f071205040501110703080f0a0e03040306050c09150301090c0e01080403080601 72
    0x3942e54550142c00c451811a040b800c0529130110100c14050180718030001307440700511070b00c410131000140b65100e040801d0300040d00ba841c2e0454400d81c40d02e0500030305c2d40f01c10004100800c1a0351a0805011501600200da01e103c1200003001068083c480445070001ea00e07100040329900e840c1702c9a90000164284000c0310741c3c445010508003010000640c240f588002101c40c10420100301c40c0d1800002540d06010081c511410340500038406044001c0304030201c003100742907542c1400080c0003085c20f072115824200c0c0d2031601819428046410a100b001100001802c070350000350307058814912551030510346a5800700040c028000500103a440d50b6a5180c3e102c081c60400004042103406500d442655240000c0c0101c2282c100034402e010b81801e02c110a440f5100010954060b07962050012a040c2d50350a1005868002c480c1442d910040d07170040078001c10f04810045040c0e500c080b90900c405420300006541c00034410350540e0004548a0014001c0303441000515040310051514808 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 678253660 1250 678252410 678252427
    0x30218060403030512160c0209090f0607090501090b070201020d05030a1b03020d05090109081e0f190f08011a0307020c091005010207050102060108030322060f0203060f041e0e03 78
    0x845401c160030440110748001100c00d0a08083c070210350340550f03040c0e410015010702040041140d440040e000f400f178074030000030400a420920240d0100c584001c102e0f42c02e0300e400c85d03004000414900c5003501098081c0c5010501c0001c02080301d5850344c06800401c2000030300b80084548d54002804140601d80d5547c1d880c1036101000f0051222500b43d5501503190288200074504460000e006040c0580c586040800003030598401c0c1d0300b05402180030345009103100d0b01c60891a1055800f803041c401c13000030702070789103240210901440b01000d54544003440000202034401080a00580340f031038081058084006039103c0045038090a20300c10307110f11030500302c041500c0d0031069a51031211031022005000559042020700010002480102115454803003115240d200c0a0940b00301221803466002c800b1480d103034040c034110307800202000100da200101c41c0c020340056584c0c0303214404440900009207840e005010110142d080c06240049020706214004d0480d155141c543d800180809072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 678254910 1250 678253660 678253669
    0x1a0403170108010207171602040c0210060815161b0c120609050118030e1002070e0f0103110406140904110406091a01052d0d0603081b0c0f01030218 65
    0x1d0003040e40380e0026850344c07203525055079588024070340b1a082540c24014007074820725101040040c2034042c1d800003011000368030101d0511b007511684024450801c04009080280040e510403a4448040c84403001e848411154019203132126004002035270303144030042130001c000602041c0c0c0344509409070741c0903a00c1e11408502208100f00b604c80035130351780804050080030b004882c600a03161003521403508076503501500341e040703e03015940505140307180140190b0080161a02604902038202d816203007030020300684640900044408810048012000f820103010710405d46403100002e03d4100d41d29000e001c035001d001001500d12075028499907000c0d880f14820803016101c3d0501c042150340d410815803d100e04502020360420034200001c403020201c000c0c248120158807900d20300f605207542e50584560103a81030640c51207103080f00c00800c00803080028031072840702180c0c0c0104902e824000701c1d141c6c1d621520507500003204c00b03a00122036109078001c1107400c6000d1541c240600f4040040fa = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 678256160 1250 678254910 678254957
    0x503130b0c071524230f0604082512150f0c020a110a0311100201020c19121106150415171e0d05030411030604200d1a0403 54
    0x8400141c0e4600040c0e510300c030013100b403404100e4015280c04006181c10031000c9600188800c01462034600c908080c00ba41e1400e080411043d401411903131039a03140c11249444503000b0540c681c0c60f002d40810b151099560031074840c11150480c039402c40940342d503100e451081d0340d5503882d881d500d5902d0b40c98524241051040d0204019503038002c0202c545549000041308840c41d0f861880b85021410810005044813282e8034110320684084e200c2c2c240002d03041c1d0183c0105042001903010b90f400d282c81116411150540040c052090054013100c1c01c00c1c00d40381d0003103a1385400c0d110380140e400520900c0e42111104031500011f0400280c5031128401c4080c1864a6000100030841c24ac0c0340d8000510104100484580e0451108020103001980c031340d956900d0f0840301d0300380500800040c0610440720b444c1407584e00050107442c2640342624100e1111001c0d0038100d80d03000c5400d50a1817250a100050780303501503000c00c20703020040e460140d000e1140c6006004400b04908540d08111410b11540c08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 678257410 1250 678256160 678256193
    0xb010c050d211104030f0f050a0303020d05061c0303230a0e0f0706050a1d09090a0c12031b080c1605040b100e01200a0c150503130b0c07 60
    0xd108110b80900000208040e968240d02140d90504016042d80003000d0304960482c0c1d804560781040000303031701d49030214009881024047d0300a0461030001c5c0b40c0c154000303104810b10303a98200041d035640c20422610081000e20103200c4100d1758900000240203074040c81e40400701003410b4560300e00380f41010a00781030441d800da442986130303070068403104420082c002582e200071001c0c211075428a41c0062503800f03160700410800011289260390840343c1c0500d1143e00d42d000c0c10301d07441440d089030300e80c0e510000d8180454107001c4210000400c0040e580b070b07120b60984d05a80b030385800c5a4680503132000c9154000190740b0b1131010400c2080701641005a00c01000c1543d00c550401440c1c6402c01c4100ca0021801c9409560070340c030b02d07241c0c1c0d5a10071b60050b401c3c0c10908111200b80d0300c0050036060b18940045010031071003011080010322440c110040101c400d200c20407603d418106804031554003040d08c1034481d120234602c1ca0000907115119a80d8400c030361404031824224a510f440c480303500003036903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 678258660 1250 678257410 678257417
    0x40c0f0c0c0f230103180308100e04050c090106050306010e060705010b03060405070614040302091f05150904050a060b03130f0f030305040201020c090106020303070509040603200a09090f02040b010c050d 89
    0x3080003a0006505015550f40c80c01d081c1000308004500301703103080c3d01c501c0ea802010401c0c0d0303c00140c2404442d03204807014081c1000800079920301460b2181c0e4030b00c104230001d4452154840002015031050f0708684c800c50043e5103407418401e071340b8248145500415021120f2795240c2c841064580c0301003000600c12030080c2c00600f82c05103064030261815180481d12249000304010520260b1240000c15820001c202c00c20002200c0c00d16803920b02c10180e4200a500068109964001c1203480001d450944803c42c0c04202c2501c85075241801c5031540d1140382029241400000c8640364100a0880c809000342001103101c4c140d41c2d00e09102c01c6011404030302180c9d0712001c0c481596410044040e18400c1520388000c2941015000396032400300821080400c08000380f40d40c11074980350411001117034030180104030f54038124031040a005800415a0040d0080c2000040d9402d03036000d419082c42c2c206030810702c1081302c0d40a22024060f0312512a050012654002c80007a604001d0303004450440c0c0c0c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 678259910 1250 678258660 678258689
    0x30e06101205010e030f19020616110114091b0409110103090201020307170301030b0619031112010207060c0e031515060408030310051002010b0108220b01060903060605040c0f0c0c0f 80
    0xe0707c02005240000401c0466100390200301400e2010803590340c0c45581e81c102102c12042c130311540342c00b42082c1c1e030030010745000358414061103030030000ea03c440b0940c0c4079242c45420380e100414030080310503602002d010385c2e40c40b01c03156548d94002d6100002560040c81900d2814070b064840b00c11041300218484001311000004005100780a00c03a290004022140551298804528182008e03490300015000c0c04502542660030b5403200d401d40030107085007000b552501c00d542000b600420024028001294510001c07444611b00030a18041059101442c8181c586a0343c1034a6034120041c41802d4100404020200b01520300700050f61241e01da50f03040f4051203051030f0501501c0183c80402406580c101505048030780c0c0c020100c10351003905a0600c4170b0400307050a00ea203082c003149002600307101c1c0210003c210340b0f40c0042d0710b50540b80a218144070300c03690348085c032044501501d0100000745203640f041100501c40c0004c0d00d80c881c02561140010b03a1101141001c000c419481b08904681c640c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 678261160 1250 678259910 678259927
    0x27052104080111070b0a050601030f0c0e0f030616050a03060302060c010519050108071206020f07140d090620010b03100b010e060c07121a040f03030e06101205010e030f 74
    0xf4003071030004145502040d41008039940c3c8242100703001806446826481e480003071011b034400d43c845040c1049110083c005000a007074003802c404204c2c0160742c00b80d0509078501c2c000d8100040c100c1e0103040100c80e80781e8401c0b450341c000c50b15600044030900c01c0540300d80000001d60780b000f01800482111000004040c280300068140c15a20600350425107400c1c03000406c580c20000c101c0600311200980941004c40991502078000d00c5100c01d08200c0c82000f103008000c0c0b08404107445800d21016080740d20b9030303c20070019103d148440c030a100004003c2031410b11440d0b0b036007103911103458210740041400d04903800040d080c106c00c4091a169103030790b419008200d691202c100501c01105444251404070902c5080d91520600e0180b44842600042c5220030001104c17060307040072188100070607203810589030030902040310300b40540019040c2419600d00e6007001c900b0303500640c02007229000312807521004d030050103da4501030b9415581d0702c0e014502c56409000a0001001d54181c1560f43c0110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 678262410 1250 678261160 678261163
    0x120c0703030912210c050901030b0105070602030f01181a0f03030d090602030718033906091d06010806090a062103110a030c03030908071a04030809012705210408 71
    0x113000e0004007800d21140c624881d4001085a550305005e1a002c03443c24260070041e60248100711005140ca0301c00001c000031103a101102da4141d038400d40010700607840c091420400d81c5e8111001c400e03080801c00b19003800d4604519a210720200c0541528145140013041f50b04407501410107980d9150008104042d09910415185049079110038114820b8111b460f102040f00c00e80100b404485400d0801c4100100c04002105004412070f0300017804544078a03000307048011520541034003200f41d138030310100d40d40c9002c012480b03010183d481c2c04a55a9400c104150741801610055620350b85400c0890014441810f0f1500e90b845201028103044a61070700829150540b04032608a400150311803001075030208400c5881c075010704c1c010850310a54100452507214860b0018024102e03003412040c1c1ca581048028070960190b1076a1020b43d0b43d200c800750076610480f90928610b2980940c0e80040300000b210341020a01400480340f030700c407a00b0300c500000c26a1103d4500e0203400802c081216840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 678263660 1250 678262410 678262457
    0x309060c0e0a06051c0e01110a0903050c0a080615011b0c0f050103060f15020115090c031113120807050109080706050108030909010b09011206060302090307080102120c0703030912 79
    0x205242540c82c0c03410b9610700d528420001c16040c5171460b140c0c815001120070940010000c040c01145040d41c60b80d59600151905c8210f10049940c0d024030750042d405850092400000c40d07134240050021503072040c209010035107680b001c1905105040c0305605c1042c01d40801090311900c41d021050701142444a44080000942d1200d41018208502401080d08840c201c1088070750b442d840b07035401e0f010f1031416330240c030300f0b2001004070355148400082d40d8411500700c01e0403229942c80c108455404114050f11780c0c4901021300601c00d60703040e01009401710304143c0520f05400741c8189420318001d66205030070741d821810b0544044002084007000c0c0b00040c4038483c0140700c07030340c001c51400000a01280030410144955102503401040046259000d10303d03070a403000f510034040100d55101c1078042d000707400c00d01805001e88141900451050700c14422200f05050840c1039001c2c03a5500502140550f11000c1c08400301511481c4078000540250022801c500054507200d40c000301005007900d103040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 678264910 1250 678263660 678263669
    0x309260901030e010513020d05070506070c0e0907060f140d060e06030d1b021203120108010e010c0507080711030a0c08031222020105220306200a0503060603070309060c0e0a 76
    0x245070000f44101181d2148900c0103242d0305980f85c7c6610001421b102b0f00b09500750b40b110703400c64000a00d071400c000707025903410180d49030380071164900e8440040310381e0b582d0b0550003000080b400c10380c85280c405000c0d0050301191400d0044030b80c9094244e20380c1200343d42060340000e1480c110740d800e003c2d41345018802c0721036500c02881c0c2408110420070324003043c20081170020307004443c0c09030005100c00d0f0074011207500707000c5108001030f196940c501203402451520511503055107407c1030001020b10034030850f0440d0750409111424003242d510fa010000a90103201c0e41e145c4280711000c000948950b40d0007004001050181d52121451403d05003104002484800d001904188110841101100e082c0b40d00c1d03020b04c0c0040d20f43c8c58080f002020360303240c242d2034500740d02d217102c0010802c0169000030b450b0b00e841240d541e507091108600f01c4660700420b60b445000c03a400384001109400d103203001e168010614038000c074585486442d014103e032654072091000804018110000b800d08807034802c01403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 678266160 1250 678264910 678264913
    0x11e0f11120a050408091806100f0e04020904020c16031b031e0212010e0c03011b090303140910030f1a06090402131707030506060a03080a0309260901030e 68
    0x30300d008101c00c0c092005000020341c2d43d5880105003440205000d1b0b07418000c02501850099540c42446651035104a0700ca030301c2015244240d00400307108080c100c0654403076880740b1110300d48142c1088043d411540e805a0051b90a11126209442c100201041c03404860351081e00c050443c00d0449582e0070a0360020b80c60100340c141040020b44105280d1194000404800c0914049c1d02c00103a040d410010f10035042e60814000d1802e031603012800a11041045000304640150b202503031284827019a918008604003210400219002d5891541103c0f103c0e003066140c8441c0c8000074444a40706121400041d940b000701c031080e450f0b503104000500500b16101c40034481100c0c001051842800707444e42c0100d401040d01100040301105c0d4601518600840c0880c03e02d40001c0b0665461a43c4019a9548203800100320f442c24086038000590f600b04d00d01303a19041c13800700709502604901c60201c6512201a080488045420401054400b0b0380d12131240d030b03982100c0c001000c0d60a080d0304807009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 678267410 1250 678266160 678266167
    0xd020f12032205010c0b0f130c090e0c0a0e010e04050f0d05091e03191a01030b040201171003120203090307061809050f04110d0b09034503011e0f11 65
    0x1288200d00304130f9111018001001542da03511231070340003191625100a0502d1001e10300821004802e1b00060b242e1003074101103840c40014101009030041d10b900c00e210758024054014018024580407a0358480d000c1e00884040c000e40005c1c2e1498041b280607a10000340001c01c80d030b4082d00d0440700500742100c01d606498402b007401c2c800a92915040d802e84010116052600d00030401044180714104140c0d2035021a02d603564203180e005900c04075400c0380080c681244008400307041c0014a40185094090310160505550302d1124011051944d00203500c401c0c8085041958200602c40141400e5607454140f9403016190344610542c2e0341040603070908000400001c118141c8110303a006401c0120403900c1c0714186c1c0490810241840050045140d0f5030800a10380790000040c21030080d0304200e04181b00c0180d45e007203090402d8004400781a000403102186040400e1200c481c3c604004000080b1240b01c2a02d44c01030a15464074482000e845040e01440e800c000e200e940550101032118514 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 678268660 1250 678267410 678267413
    0xa020d0f030c0806011107030f0b0a27031404030f140609010605010203190504030f1407061e1107080304090e0115050a0b0315090405010b030d0302090d020f12032205010c 75
    0x90343c00f00403c030904108280000c00ca0a10007040a04021504038a091422400c1d50420079454282210208041420201c11010206842140071394468080310099151092035031704680d0714102504800741c0c00001c1c040070021428005a200f10b0a201d40c0c6181e6100d2448001c00e814102c0080402480b80d00d4404100704c030741d130048215004403c0141e000043c4803009641680c5034041d5030005400b40f00710061201c10480c81c09402d902c003182400c12100c100355180c20880741c1c07080c10f030b804207c0514150b481e00346241c01641100c6030801e20200380c580082d22030040303d00d550000d5014482c11070300e07058507420303481c02841000d01001c10b10300e10307100c014100300c045016001c26208807229540c000000510030b413a070b040c4400c14490014280356950415013011400f81c4071b06c030360b440d02ca402030340206424907003e071080b6a02000040d04208030b40000d1b0f0204a080e03460100959044201c00e01e250119690070320040170706004401980d111000003021149070201aa00002d0502250420010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 678269910 1250 678268660 678268667
    0x140c12070f1208042d210b0907032f0d051c21020d0e0a150f0b03100204030308070503040b0a02091909050114040b090c1e0a020d0f030c 60
    0x41e0b4200328002c240c4150103240164061041d0380c4204000c030781c1318455520b0300d9110f5042054020b11800c41131000c0b91102c0300c5180398100d01d009040ca0900c28011500011039207200f05c1c0e4060f1002d000c1e0761203d60780340ca40066085a40c44070a1450f4001080c890312403c0c40b01d0240b114050a40d60300201c6890b580d1600e139285078040300c0b40c0b04043c240c1a00c0c0b1803188070f00005444c1601014000c80350901202e4a84080c0d0042c1c81d246669a00b82140c20001d45400a00c0841c103e42000d101c00308104811500c000030070030740540d040e80c16102c2c0486e0380151010008040009101d0720b0059a5919500b030081070a507024000104100c0208280b0010600385244c980e041800e6200059658020700d0014001040b94040b003010080c0c40300001600f140550300c210304883c203560013520308500100400c81100e09900b8284c0d403184844011503074031020341c00504403100e40c40c00d1303983da80200342000070a5078124000e6040144d010031515400b45500094080c076201140c181440390400020f0040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 678271160 1250 678269910 678269939
    0x20106170c030a0b060a0906060e01030c0503090604110f031203060a0518071d031507020105010603200a0302090607081309050405030307030905030915040f140108190603140c1207 79
    0x40c0001320000c0100c0ca090391600b54200c020718000100304203003603641c036001d4600b200d140c0c00d660101e490590b00d0559a40903004a038031951805000d0240c40d500ca90380c62040e4030070131103025002116a2034103203060300c040052040d1521104221a1030385016020010042c0f45904180d024003d000384010781c0c049d5002c0d0f0a50403d01d00d092844500340071403001e2030f0584149200f5985807080c2007041800d1114030418031700400c0c056000348007503030301e440c4e0076070684030f12242c1083e86900d16001c0780c4003d411580941410301c1a89400b51402c01c0f154001842d03600310706800e451140c170018104641200300955400204003054040c040d500d8603481d015200d0000803c00e034103140e154000d5100f041810310840b202c1a100030b200d81860000310000710140c4d0414081d0030f45510180f8400f080b14002d0144240c841d8030140e4407203889541b49034034494841c0e07011518100d256201e0b080071001480076003600040c44105002803400103c07000401c8400041e4510341003503608299024840c100d0f034110742 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 678272410 1250 678271160 678271163
    0x80c040b030a3302040905060f0a15081f0b0d0e06100b0706110307090302030c030f0d0513150f021e030405010c02011202030108060f0a050f0a0e010e010903020106170c030a 76
    0xd0040060603401d8051000f854081580c02c1c00d01c0000e000c03030300403565804540950300580f104000c1100c204c06100414100d8044d00f088513104002501d402403280d5805a07203c443c40a0700388070746603100d07848420122640c0011084000101d4481c00300d00c082d200d20300f0f03038900c254002d108600741840e0b400c81240303140c020109618030024058080c00084d8203c4c88002c080c001240e540d0303282072071001b080d2444030702049119000d40703541c1c2c0509190000c0d00b82c20051400b8013601c1c13040310b2030606903819403200780c184903007130004000080d0349440c0e41e146400d80d03c40c949950040d540080d8009084c000e039541e00111040006440824814000007603801b40d40d401c1c01d200301c0700061400140c1d89022080d84004200b8000400441c0c0500c000ca81c6ca8000c0f121601e800c07643c1c1c4c0703641d0005020340701c00301c035440754000d0803100043d2040d42a401c14a00c900110340000303900701c40b069905003074403030101007034000d130b912802c08002c035040c108010704924400201814042403490300113900c41d00a07850 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 678273660 1250 678272410 678272453
    0x4050901050f0409170c010e06091005090a0c06030204090507030c090e131e0203010b0612040605150303030a05010e06040c171b1204020f010f0c1713080c040b030a 72
    0x2103001600e441c0c0c06070300c22070380203141c038040030300300c5d000300c50260780903800c1038003c2e500705a40441e0b480c1c40020a01d001b600114080c2281e041c000310280010800241007003200d100d40003e00d03011071040845ca00241105980240e5603034107101ea060103503030011701008105858134001c562243c2c3c0c4130b84c0000a607624031810041c2030b191000b1050b040900d1510140940f14130148a00c4180700d003090b0001503620a8000340041904101040b000e07010b040b06001400019400040014040360b0105511407500242800e0b20840390300464616001100c241e505aa668070040c4240102c084400e50702060481d0305002c035604245006042401c040034440200b0221004a004030034000070603007907207007007011164544121071207084000d2000d440690207a03003810340c1520705500c00d24459411908603101e080ca90040c83d0b6542c400d507030b85030980741c1030180207001041e8040102640301d40100944001012180d411000f0003003240d03100c1098078401d911514221000400103840c2f070001d89031411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 678274910 1250 678273660 678273679
    0x130e150705032e060201021c0501050603012c0406050a0b120703061d0d0c030f0e0f0603090a0804080f072301051b060a020a0e030706051903060510020d0f03020405090105 75
    0x4203403052220707284400c40100808082d0104003645d0540c060645c020000c02c545054028413903070641251000c2c0903041c0c01c0801000184030071a0408a452038850012850454000482991143d108019101254699240d6003400314200310f80c0150144160100c400451078242281155030300c071030314400145023949a100005928050703807042681c24100106030340c588211808001e2160003019021030102e403a03d04010300c81c510920b05002c1040000d40703141540c0c1c0350441001000d0b04001c0c01248580308800e13000d40090280d0b000b400092548100034480d80c001a44482e050030f945412030740e2101c00040b426640d502ca29400c0300511582030a04964421b61070404480711a02d82c0c13594a200c2c4100010302c8082103c650040c0000545591054048100380c010103850792a10320507680000c40a11000c503054210034440700c500390b50303030800040e6181d0f02c8000c10007274540c1004500160b00304000101401d0b411440c5505000840e01c0c0851801d410000041c00d80207060141c24069100c2c032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 678276160 1250 678274910 678274951
    0x601020601260a05030a0302031b0f0a0c150e010b0f060c1e0a241803090902160b0c09010810030f1b031406090c0103091a0c040302130e15070503 64
    0x500c0f15100e103d8008060720741d105103a01c8080c01a42c000ea411806884100382100102a165002e50359103950f12a01103146c400174000840d00c4142141c0c5c103488141c8407948000203220548030710541412040008a40032042c00e08101c461400b0410b2240514010000504010000b0800c400368102684480c0115100c0004143ca402e00d4018003c0141128003010030140014010a04074a0402c000074031035121040003a841d14000c0400090124110070014440642c01c2c0d0094503042071050204084001d05840702d035201c41e4292181c2a0700c07400010a000503591264449a010403108a030310882d40ca5607541c02c0840d02c9400026099050440303000d01c5842c00076440a00864216581c202c1451120320101c0e11160251161110381c81120744040b00d41d4028003451086982210f513556003088100d11140364940c00818180000c03070200008001030380c60650719040e0603e0401d00140002c40e0400542c030f0070700400c0b0325640c0109008100446540e2200c1100e070f000380d0840c200456524030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 678277410 1250 678276160 678276163
    0x70c030b371d07030b0133050c030d0905061b0a0305130b160f140a0305090a1a1803030f06060a11011109090a0c1e2c09060102060126 59
    0x2440c1e5840200420490b4000c200301c001003002c252405031090841d56665200c0082424a5601c0034000401c2660500500c442810b0f8441c90340802c01d041c100e1078030690441c5c0303600350b500440020801958400050052143c200503c90703214504003415480b0074015110380c1424004c10001d5010981c0300c0c2d00040c3d44e00c0e10501c6014815901660021141c1000703805040158502c2c41e0103400a1552420356251074800d03c44d980c1c031504107440440c64025441c400f00c010b00b5004001408601c2060407a40004950304502589001c034205082414241030260342c0e00300b1810a20685036a10600c1402880c240d0400c132035130001d0040314aa6035401520a040d607001648030703180f16003540380c0780c0d107408041c0b0b52800601c0c946804a40903007140d611112030100f2104140461000603401d00707800080d81a83c80c1000050212905000c0d050b03e22040e0101000610091181e203480c1101c0c1580c20542000000990440401d0001e00b030158107040282e071106000038404e00b4000311030143e4a190000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 678278660 1250 678277410 678277421
    0x30c100504050d080405041b050405010311090307030605011a0903030f030a0b040504050c0f01021605100909052a0a0f121811031608030a0c17070c030b37 68
    0x10007804100394910141841030841c0c0092044c80e01a0303043c51511100c2320100c2d264a40246459100c103410103003040c00440040c11888541d604204040000710340c640c4e41000a60000e500c2a140858a58180754030f030f04d21101c0048400411040c24821220382e50342c00701c252100346080800440e181d0361002c04002c041c0444182160b0002e140400f40310501401180840c050181619600c0002c52140c00480ea00e140403c0210306209074000c0074402843c000810710701810407444c000c0749030354490422604a60040d1040210244002102004504c00c0c0706080e80e100d60f00043c80c0c0c02c024141001801c110b0584c81e0081c2003044076146444101c5260380000302001d80359002e5409000c4628002843e000f1600390b1510030b1190082c4550800054060002510352035805103003081345441050358003141c082421180c041840100311160124074015140070f5001d6022016241d14500780410000000340480c18122088580b803183d000820000118000710001c0e1041e44044552030a0010907 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 678279910 1250 678278660 678278669
    0xd0512190c0c0c0b1e03090a0206160c090c360b180a031a0408072004050f06011d03120a050c0115240c1704170705030c100504 56
    0x5150219035600550312000410320144030b035010440b4030b61a0b400c40c00c0280100302c0e46804000d003172598048124050b4025503040b280110485040403101e174000340c5203810400c9034079107014032005808240316041c050300000b094400701c20815442c500c00c00801803225202034020010780d500300c00d00981c0c0d1041c200700a600300260007590007902e90341c1020040d0b106259408440d403800300c08130100c1c60040300c54401c980d030002c0440e810400301c1003c140e506400910070b440e00c0c0814040784000c02c101882410049c018050a44824540720301000203c54019007500900103454041000d0750741c22000181c10341402100204944a004000a103099200c20454041440205c1e02842d07554211000c3c0090090b0f92000303000320b04881200b000086860702c50300700780307403010380e0064140c05085105161008036850090184066619161517145542500c0d00b12040c001800300044041620700d600384448100150801d07a00d480002995a00c1d0741031940e10407541030120801f0180240c08540090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 678281160 1250 678279910 678279961
    0x30c0311060109020a0e03070807060f03020702130516080105031902031e010605033f270a05120d050334030b01020606090a020c030408030d0204080c030d0512 70
    0x1e40e1980c100101942104800300003041b4801c020811901d0301103090020754400b10003c01e541850100304868042d04d00c60800141682000382002507243c2100d0702c14009400340000c101e40c2170805e00c1c00400580017030040100110040140300d03a075004190b586001c0307114240c0344000001ca000085c2040381c0c025901080c16030007001050b80e4a01904200102d400441c1542e4508400303580d194124148010000300b0061120300b00000c0c10001c12110441d42d80540b440c0303051030b102101c00341000c00403031003110030f80100809405852406c0041c50019003c10b481a0741d0340c4403042c4040e6620341e0880041c50902034080009000c0c441001e103001214059004102e00c60202254103c0380301c2078140010300084c0c100307a01200c1d6940001a024040c00000e018603000703949030060340c0006c1d00300b02c032000601c0c00300b0040090305170405c002a103202000c8100040e070303680c076003201e192030101102d19180c000c2e0414072400202c950000c0c1521903032900d5420700c6125641d62070344034000740000110096071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 678282410 1250 678281160 678281173
    0x121b120e010911190305030913140405012009150d02090904030503060a1505190210060603150501030c1b0204150b0c0d020c0616062d0501061b030c0311 67
    0x74461022443c003825007041d50344100c0c00500b200c010960310154040076100c3c1e401005480c240d0706013034444054181c9000c03000134242c8200403d5032a9005c00385e50580306a03443d00e583d4010240d86504e0503802c071841820161600103007402159910300d0715070405094440c04164000c2d103202d10b40484c2c0c64140c4c0100b4814080ca050301d0050150342054540c28022480c401021038405884800006d152241da22001d052607900c071407074141110300005400850040b440e00e80b00e8020701e8045c4030007070005620089400c01099100d0044055260b21050405050042d004440d64000040c08070741905101000441015030000c038000c1c0c04485003010900801315070010300007001401520715403100200380d425401d84182c0407aa81c00241c80720a40c402800c000c15085000707400c0d540300219104800c007240f109244a5401204074401000c8030440d00301003c20b5110114a2107406c1c00f40a46003402e4030320440099120070006840c0100500740a0304451220526014468101e88140c030300342111003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 678283660 1250 678282410 678282413
    0x2040216050c040c2f07060c05010b2403090a020a0b09130605010813140a210801031a040f020904050c040e03030105060d0b1302041203121b120e0109 66
    0x180c4180a410595041c041c822500c8030728034080c0203d5000302ca0300e0b921007460707200042150b015124102e112052050319005080031000080c400040100165200d40001c2205401c143d42540c084140491186d24042030444000700e40201c002c106003001102c164495444101681c544440480003030b41c025950040042ca07a801d140c014881400f058842107000a40d02110506585a03401000c2c00300e0700c4c60b8000741c52140740b00c5000d081c66004407803000050a64690031410040c61040a82d40001c0280c51000c0900c2c0480e42051000c42c245080764456245480308404500355490401030400088045070520000f96001d11140743c00414102040c00c051410310f940d403144502a0b0f009508004080942d44800310960b07040f03d401404d003c1c6881581c104040040c81005103e035444510601d00103c3d00c58284060809024100e0a001e50a842428041c122200100140e1030f42800c011440c12480c4012a49820109103410179050200030000ca03d030150080b040c2c0e101c1e881d03113000d03207800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 678284910 1250 678283660 678283687
    0xf030903070501111b01090308060f03150108030a0f02070e040f020f060d050a15050f0f0307170109150203060d0303090303270c0506030f010311150318010b0103270f020402 76
    0x50100b114110745c041c3d041034407401404d89100c05400350100e00000001030b040d0401c5440c00d609090002c042d1820402c8861402055540c00e8100d0070a50340042405d00d01d054000703511214941060004046d00741c40e150088158a00003400103003059a2130080c40115100c07144044060b142c01841f10343c5580030a26441c004240440e00310036000d040a6413412545003602001c406d8542c058110058041c40c04184000c035485840c02e82c0d014801d0380000104c51290142c41050024902e002103680720aa041c5540c00591000840088901c10010300c0001d0743c4035032190ba01d481d854200030441002909064000f07080300081c506001506201200445180c051005d417000d100b00b185020f1240c4503814810540411600804880c81e04c40c010700c003040c5d081d03000b5a01000018904d007581914840070940903001035031110000c02c0e01c0e06021089075000e000305e540441081c40e04000e802c0d10125269050404841204060600600f103802881072201d462507045070043e0041d9910191008501c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 678286160 1250 678284910 678284917
    0x240f0315030705040b060d020c0312011d011d070818030310030b01090507140309030702040207032c1e150c0d1218021c0b04061b140f03090307050111 66
    0x8910a000c0c10b50040381c0361030203200740480040080c2c0300038107044008690318004e40c049001041310b4032052088a014654113105140a45000c8840b24410f0885070541c070180001a0020030050940c8140300040290314403c06070301c203503545404041a120590340381c504a91a644000641c040082000011360000108070700300e0b40300301450440b0b41e0345e4002107011030f441a102070700001d103003500a48031040b646003d140c0101240081d40d280c8882076000904982c0403680071008203496240c0c1015a807120000381307007400c40b018155100500b103000000e254050402031907000380200080c110711703915191000441104001d50843d0398600004005070745e00800a01040000c0300001654840b86039030003018042500300b100c030402081140d0030440c50114044080690043c031644440101c0e40030b883d01da01444c0502d0002900c001d1081c00a80c0307140d480c1d908041400020f485101282d015081250b542c09144145079449888500c5481c0c154031506e240038050350b0078050087c80c042d83c6813006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 678287410 1250 678286160 678286201
    0x3130f120e10051303020607022d0a090905120a02010b18160f0210020306060d1b0306080a02060712020c0a031202010612120807051306050306030f0309240f03 70
    0x814030720350070b001e0b04072003901c668101280c002440032070802c01400c03e5805030101620007803160342d1909200e00002d080c2c0a103250044d25009001382c8a031410b08010394280e024051050060001000e2071b162650358000307900c1001c0030000009009480385200b075001c500728180080104408141c6925a1a4100800d0350f880130b0780c6910104260f0303202d008901400c85542150090308550446111050094200030700c1c4541000c0c042100c08400003480c4a050b2045860281c00300d40400c6500c8018101e03070b04c81e0400241940080a0603002d40d0740e01040d500840c0d4800c920881004080500701e042000c282000c0d80c0000041101100304202c6686500c101031880d802049425a10380099015000c03496025241012101d01d10300c800e481740d40c00340e40c0038000303091a5103819809440f070b000000269021100042c408400c3c040546024403440c40003100c010011800c0100e50800074000140d4000210414503003000d621442c143c0e41000c1d00e43c02c0c03219404454492900c00300003406070848488 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 678288660 1250 678287410 678287419
    0x2040506070602030402120a171804022206020c0d061802062701050316050a09050307090e2413030c0b0a05060f0a240210020c0d1e0503130f120e 64
    0x71743c46411040048c45c000c50b590400100d40c9021070080c3c00305032a030302042d01c81f44480c0c02030140501c0e03030700c4500040004c88450f0300d8141c500c0c600b00c5450300d000d075503540005003150000d2140000d2552105225104240c10000028040002d004280c030101c031182d00c020340021000c42c104415504a03040100404440928001c0805484004442d14842100c032020810a141d06035151948650050704c1c1d80c0249040039400700c0d8403003000a240c810305510280c0380640722403105c01030307203001c0c012102c1e9141c90004142000c0c1070601c5040d62402c004003d0641014225026403d01d4807511000641e01d8004000c032005007000d02e000e0016080c103c81c008d002d940380c0c042c6050f103824410344404c12114980c1401c20741d10b0010f104528656903064801045100e40704a070003100000744010000706650000800124030240c0780a4500403d20030440002ca4550302c081c40780a40010842c0e0b440300034a03d00e104100d590380b400ca100c50b044180301400ca52070203501080c644d608080e11107451501103d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 678289910 1250 678288660 678288679
    0x301051320061204060b0909071412030406080c071401090c0e040201020d0e010e121b010f02071e1206050f2d0a2306100314061302040506070602030402 67
    0x989080560340a072207100d800000c00c10048841207500c018150b0405d10805001c01d405210f4000a4449201511910455001080c0400c0300c10244d1807000c0c030aa105a82c1c502e0310100b0320002c01c3d141d008500c5038a06100480d00040c100b11588011152900c1c0e00111000e070000f0110724490007854035080032101904241c0c0b001c90b01090324469030307110f90740c160700038603070303800d000004481d001882e200a5051140700d00c1c8018031a0b0b50408a058500ca02e43d00034110291021801341510998903003242c10701c00100354240c180b5a01117010000d9540c0b030b1120800e42e008a10361100303010700c980e001000c06054a101201000349542006024038085604440240c440420084018403102c5007640d007000180c26246141407152451607006150250005a10307030100e149101d1100c42c490309200701c00c400c800300100ca203409204d252802d030f028501045043e41c84642203401c40000380a0301e125000761024142006560380480d0003611014000300e481e15007524103040030750000d9401b01c0c03190f460b42 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 678291160 1250 678289910 678289943
    0x1109121608030a14030112060f060b0d0b0a05010c030801171906020702150c0a061a09130308090610050603150a08070603050a0203040b01060507050f150103060e2a0307030203010513 80
    0x1c03059030706a407c0001c1a130b600d0840f81e91803400034080c2100307013107801e41c540f0350000b41c10007140c0107040081513106010602441d00c00400c0000109070704214140861450020f0100c0d901100b0107043d00d200030151116041c1c500071541c507000300820340312101600002101d0410413960007411a02d0300c20b40d551055880c070038800612038000e07212000784030b07880038201303401081c1d05801c10092000d58192050800514074042003c098040f1555118000d00c0d41801c0200b6038040c8a2550041c1c074000603114504240f641c00075030200b14414584109804004a0b5942904600c011038014005016094061b070b0b8919075610b81225100c0da1003c28946000501100010300032a4802d0380d2001d0b11300c0381030b0308004047c1c400381c01400701625640300300c140c1004144001c1100c04280c50340002e040c5070b00e61652801340103039141d4402e400c2d0a5045440f8035a00071680515901d0303043c0c1003142840002c9180e0f0042481c3c00341c40e0f40041d606608003c1840701c10104506907509a070b004404072046841d58 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 678292410 1250 678291160 678291197
    0x80a14011b030f0c020703081e07020909010b100302090a0521010912030e1504060207030c05070e0402040c033b120d060617011806030f050610091109121608030a 71
    0x6d6103c040d0413908100712016203460303034202c0c07007194240000d40c1070308110454004c5a0382040840f05041145c0d0746110505462400c000040102011842d0a42c0382c0360300344000c501143c0662041500a400d000c0062104602808105010450500c000c000c48130141c10120028042c40c04540c01086c07411004591903c40401d110f0f90b1103605580b558800e446640e16040298000101502002002400c0d040007884c203203c62402400c490b4180041070500313004001c1142e41d0b00301c0c620149840e110034085504020307011844070103036900701c00c0c50076950480724540ba41c052507443e81d03850003012052035000100c80b010f4290a102d00d042000300b9510380c5801c2da900a40040d00030381c20045440100030001c8100101d02c6250070302030021444035a02e964403c604a4211001c0b60b07190890303010404804800e0020b0401480d00d08020300100450348182c8416120342c04903580980741440d8541180482000103082e0005091301c0912080d0f900d201031074483e007284c6003020000d403070481c0d0000d24158 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 678293660 1250 678292410 678292423
    0x7050904090609020910123f080c251e0f0b010b1e160c06030209092409090307050d050730050c010b2101050a06080a14011b030f0c02 59
    0x4012000c0d000a45450b040480602c84060303102c07401100508d221850002d00301d02015420700303140032103054170340f0207442c03003600a00002c4c40c0c0300c5c14042024484d0000da109500c40e40030f841030708203904582c20725110365640101c4d014076100c0381c0000c0d1010801660503000c0114004c010b6080c09980710707884140d5611a03090b07901c99458242201001d420003d000620f140f104017544080d003030050f5503454960905c1a8080301c082503001c103542c0d4aa08101311000c0e8403485a10344402d8100507010200b10064194040038000d00c900400505004010030845041e07a4121003294800c05020764000c1913640418030031561801d26044200000d4803204416195040c0089582250340502c5000c89032034021303c5041520b9901c6600b40e17281030b00c5a030200c000040103282480440c08031450304c0f9094510140252040c81d00d030002c10064a880403a0450040b5482444409140d0710021880d001d0003107080e40d00d5601b20445003081015030154070483c1d150390303405014004c5840000d4140c0c0c8030309 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 678294910 1250 678293660 678293669
    0x4180b0f040f031107050301050403030f0e0c060327100605010f02010209030a0803190c0503100602071203030905030d0501080105180d0915210b01020c1c080307050904090609020910 80
    0x101c14030b4040010b4003c2d040725048544404c215581c1d2691800003a0a4800030340b02074010030781c0c4090941c3c05003961b015500318044c118000381041d21010340461a01c1c800107115100f50151030300c00003c0d0000a4461018400c4620203c0c1e205c622008550303c0204024032607140484c4d640862807943c0c0e4010700a491251a005014110034105903e4180050b8001400c0461000c610901c1c0c0d10102c0c4144900a410f410980c1c80c1a200d01c0d03c2c080e070000017900c50b0400f40070766004010400100c41c0d03070141800c03095490b02c3c5c0440c0135546880c2a41c81c50180c100c0f1055500c0c24440007040e4500d0560201388104140d03400408100b400048040d190381c0441da2100015440103000d000c854080c184500911440380303422a80800b1103c0b801903402180040202e0580c0c660030f10b400300703690401c10380400384800c8450007120145c3c81c0724100c14006c0c0003001488001c011001410f09070041c0290741002002070b1040c00749040c0c5180c580002c04a484007207101d0714109003c581b101c1c86900c40c681c01da6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 678296160 1250 678294910 678294923
    0x61b010c1b0c030b0a180b0411010c0c12020d0c1811120f15030d0c0501050a020405010f11150f16111f0e1e15150d1104180b0f04 57
    0xb030304540320300703216a00c0148844013050325450b00d03005c880c05003003d510006019000e4401107041038901014103140e00d00d101410000c49050030004205100d070004226800103401400f4003d561010500440403ca409403810300203441c000b44a58508040c02100804100b0030010700014020140080c0521000031942c1c000c101c0001d002070f49400c8083e034201c1108815030310303503201c0180040c1ca044c500c42c40c01000241c000c0401e804000d024066690000c02c4020190704103811303c00002d00800c02d5040400400c02da0000042c405281400400110507040000310b100e8600349007131091210041c0d811000708481c41d04440c00c000c0c03040c51500a5680c03414041c00c2c2e2400c0b80d044aa01c2120308914a01185a48110054260104000c610f22800b058280021004c80c06030b011420680c2d100f6243e03071504800700c2000f0020506d1021403141d1001110504100716803414400001401d1042494110b80f500c40c2e20310038160804050709010b48251070240250380d812214410310901518000d088 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 678297410 1250 678296160 678296183
    0x3070b07030c060b040f020a030b09070f141312050c01090812090a051e1009030b040201050f0d0507020c0a08070b0906090d050a0303021207050c100b061b010c1b 71
    0xa02c10b0901c0e02d00c8a004032800314280c101d440008007162071480c80c01c0000f030b50004000a0a40e098007820744c52100c202d40c0a415890802d4000d0802100c030080c0303c4c00c006090311094071802c099006c0c2d51082103103801044101e51100000840c65241540594041c4294500140e41d50310035100c020580d40c0388805842c40c241c0790074102d4826040070809a91200001001091948034003441c6400c0d0341ca2041e040c21040d00480601802030782040703001d01040070035001400820540300c0e01c00d400035428a810341e51114010300c1502e19004e10015102410f003004107111842d6070000304407000e403008580c000c2c00241e90b0190999919a14443d0001c90a801d002070000b903d000409008c14000140861034002940d50318107051454a04048000c65808112582d0404080700380e182d01c14400d090161030b1000d6541816594071400101c3c0481da921108501c0705603c4403001d03a403210400310503c110b4920f010342002d0180c001c4141041c0013410715024150409190541403c5c1e0300e8110306007400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 678298660 1250 678297410 678297413
    0x1d01091505151224031507080705070b0403091e081c0903020a030b150f0303190315090e01050c0708040608040201020c0d120e060901171b031f0503070b07 68
    0xb0725181191040d0890b814800b43d5406000d80110b2445002002c0c03116941010085062070041e0001c0c2103940203a0014161401e50510f554200307403c8440c81c18a503109070364411049034103204195006040b4001c81e02840f04042c1c014044009407003080c01c2d41c81d5814402c892440c2011a284a000c1b550b5000c0001c450461b40301c0d85c504c1561011f90b25098601c1074403a004929042c544e5031088440300390716800c204550b851800028901c0f50103c1e5040041e40ba40b02c00260b40c2e001da400e030309031200c1d48100c202d81c1c428005c0e0300043c01c1d425680704c1110380300e54442159005003180007251070f41c1d500700b0001842c0100301c04226020103610009807824107003880c00840720f0f00401042241507102d510511840f0390344181d849080c00e0311413801020792001243c2c0003002c03006065041e074007805041c441102160303001401100b8000100381d00c0c20740381c1e40c1d450003008a4a46818404040e40c0d0000c14001001481001407075031110040d10080d201c1c0e50340c024076648010a200d03204528805000480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 678299910 1250 678298660 678298669
    0x110f2a0c010c0620040611010b09010620060a1a0901030c03080d290f040903081b090402120906130b0403110309220605090405070306020c1002041d01091505 69
    0x1000c140a035000041181003201c4c4881003881581101d00c840d04003190030000e2aa01c500241c4030b84202034001d02c0611b0b480030114174054418051001030141d003400d241c0808540c1d110030301c411500113085511a0529512242c0140760200155a985060310000f00f01070070306000841c1200d602680c6103180d00d1960b180c59509410451500207010b4990000001d04641c840486000c1d01002030943d48035400b42c401c1002d00000c420000340542e041c141d902e4003103a009010603a1100d03100804801a40c240c40035030b05207114031000315a001d4404a0b48090740411f64051500c264600c0e4100c901a44a03141c0794000c294500200420800c3c1390000540001d00c100c1c140d208208160302240e04005010700041e00c154a025045880341d02b120103074140d07405040c0658001000291a615510308054440c40d031200c005c0c1c00050705080d0002003c0205c1c10003000940300f6500c01190840d266510b4282e082883d511391075094280c52910400411951031382d00c500e40132030207240b046c502124948828407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 678301160 1250 678299910 678299927
    0x60e061306052508031e0f0a0b04061e140102070806360109031206061d0d0c0801061a09010e040e0f010f1b0903050607080406110f2a0c01 61
    0x507802a034580f030801401c00003055100c0300b1511401c48180c40345008031a10f1325005040b08806500301c510402c6c8020a10b103004000c0d0070580041c008111b00f065440410007030010703944006c05404804c4070044403095211511800d035a0f03a500c0411980300d0030001281e8540582c02140b243c0e4004d540411403100d104140707803a60900d122603100e4240560041c03403d418007516480318240e5140c3c5101d40030180d101c0020709150390140410054281440d10003002d1490801e4a0310030040c04840c545500d40c1d41d076200801c6282d100010040054540740302d076002e0310045c0700c0c0d03420080c0c1c0060354000402a00d03080c0c524030081a5144000d1a03903d408104c090044181800d0361402402840d0540030070030700a028000448801c045034034186041607a1659541c044e0079400c000184000b840043c8000c40c501d504800d251502c00060349039810420010100ba4010800c0a100045c12907a042c600a000d8840520340c048107140c400205400c00c00d0303100b070101e01802182c120104032038140d030241000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 678302410 1250 678301160 678301177
    0xe12040f05060310090213030614100602190b0406060509100305010501230402031503060a09031409090c03070516030305010806180618030d02221e06081f0e01060e06130605 76
    0x224101c1f00c0d6240c603001d007211030100302c590f90040054100701c000d45004150b0380c0140b90714401030102c46020f003145801d407041000c008210a40040108003030201c0c0b500688064200204400b0709401d180c118000d010382c0c05d220444695003030070b00004040044500c002103c001c00c02c4090402100c0c0c1c2304100007580000e0140c002048400e0712491aa00e0030041d0303c0c801c030b2601030009a02c3c185800c01910001c8820604100a0b00c200041455510b441d120182c0008551501c2c1c2d481e034403201d00aa4441c06000e6100c000442c040d803c0e40281545500498100c859100075070f0259180c001c00101030000b103d1166041c0e511140c0070810b08061003110b0300c0341913a0b02c2c0560342411421203030a0142d038401c4c7c544001402c02c921041c100c4d48010741c480d0b001890103140c14070001240c244d0200754650b0718400c0805001c000e00000b8110982484508282850510b05d14403480c0c590101850703499081c01071400140c08044810010f003801012100d400d80b14080000c1c10b03901e0b0801c203d91917840300c0c6c0c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 678303660 1250 678302410 678302437
    0xd02090102100f020309070b0c1e0708030708030f22020f030c0604090c020601081911151c0b060901051e0c030304050a03030f06150c0302010e12040f050603100902 72
    0x1100b00b00d80a03104021148800410260307032410040c2c0c04d20f02e00344903034000001c001e1040007440030801001503c6c0f03000c1055849500032001601c5500f40c1080340315030264141d0301000881c80c08200582d40103621032080c4224846068490000c01c4403004c0c1d09807030b00c6441c00601c0c12000c0240ca0070302100d1001d600700034211840000160081200e035080f0340d000103021901c07014400d42030394040c40060701410841303005107a9000101c070a40740921490070094090548805e2590407030301c80c0720482c0c155207a60040a0783e01d45164141c001d98421038003541052900d841c0114001d0b16103041142c0e4000030581d00c55082c1814510661035010040b90072200301c200801c14140100414405148100c0c000c4001d03010241c2c02d810081c00f5540c42c0c4c82c49032101840e182c0b040c010b00959607010700c203400c601d10301810421000d1a05900410b0300d0302c1858500d01c01c00081c034514045c3d240040c41074920f84000045c900d030382e4600f8010035000503188441c0a0441081c04d014051859010b80002d801045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 678304910 1250 678303660 678303673
    0xb04021c020d02090a0e07060c120c0308042907020a02010206010b030112080c072c0a23070e04051303180305030405010c050c1f1d010e060c2103041203110d02090102 73
    0x6e40186007900b00e5215a02040d619032050782400601540044003152508211610044030340c2d0040c10700800500041c510300ca618280b1406030850b020b04420303854034182d1440c503824000d1001c2d5940b800040304900511403200086204402e800c25030341254450121000c1054080c1c2c3c440c4111f410500d00080d203071246080004a0350300c4002d02410900c05404902c03c1c003c1042070111814000501d0003400b18103140a49020b00c5103410320311610381046d04240c0c0c2c1c0340c40707040d02102d80c1c405048405501c0b03030400d814046014100810816218425102c0c035031040602c403801d080d03190701c912018060307401c1800100b2241d4014010b4003c40c5e80f00c0d00540d002c046450000400a9020110005507080803a50034100140c10840e0880d00c81e80d00800741c202c4416442c0001c02103041d150000b4042c000100e414201e4074402c11031a080b4034000f0444088103c61518103215542080b68180c601382e04000e11100607602920408043c0c1000210051a001600c0c10300400703580040c004d28114407444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 678306160 1250 678304910 678304931
    0x7080c040c170c040618060f0e01051c020a091d060108070203120f100504090b010902090f03010204080a02030616020703170705060a0f06061d0d05190b04021c020d02090a 75
    0x8603544184038080195807110300b0960010002c1b01c1d50140b200380d00b150800d090004542080c0718411411091502075682030454004039400d0150021120340c409a805001002895540162188022654a1610007941c84461000d50265000140e1110284030302040c480e522840034194080c40780e004491500c160703900b40000100044032850128140d8609216882c0743d2107070841c0040c60100d038203005210543e15039502c4c0c180d042c8900c0d1401e075400200d090903034540c032020404483d002030086407502c1d61561000d44034166032408920070701611000840d00001408212900300c03483d802410640d085680384050b040d010041d400c455030307007031048030300050041141c9449030200c100040703440090789207808143c4403290090003e007c5c08511181801010034411121404103e1b1860851102414818244032200d2a0050f41c3d21000c0c1614040c4882013480c203014610039582d14a012164610462503d14030b80340081d407054540c0c2074407015203021810a0303000f221084000030120ba00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 678307410 1250 678306160 678306197
    0x20d0e0406030807021215100816180515040e0309090c070b01061101110301150212041a071712070e0604030b010b0d0b041a120f0303010513140708040506070207080c040c 75
    0x1294030080d0043e0310001405001001e001d814803d00d00d42b1481e0b94003d007000c0400864200d00080002c00d2651000050b01e40c801e1090302541020004c2d0040007840c0801c2c224584a42c01136040a02840c03c4c0004960380070110000c40701c46903002451074103030f40d00f400c400701e500000c502031100d003564840c1c5040050041c844011802408455644000c100f082c420190030305400755014500b510091004206030380d000010604548442c00071103960b140c0d28580700c0358032070340d40d4030ae12801e05012078640c3e1090300d0031180c0303400b5802e181c41d82e0043d1052002004000e01ca580801042201c0590042200703050350000340c03107640401c0030041403865010010600710f4209a03510031401140c021241070310f0514001001e00c00d0452409040f902c00b210b490702e5034911043c40340d94010206d210400740741107402d610200c048139600c02c0315201c03414400001805401d0a0324140c90380d000d00d4002c0fa0601c1d000180d1841200c40641c040d114041a0008200040c00d002e42020240305000681d08264410f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 678308660 1250 678307410 678307453
    0x3030207081b0c040905070611120a03052502151503150106270b07050307051c0f180e10030204060909050f1920060703020d0e04060308070212 63
    0x503070a4a00c0b8034144000384546405036259049000e60b140c8070010300070540100ba00c1003583c0883c00c0c42d01d0000d0311100180d24101401d4074aa0346480081002c0f2040c607890b8004500400307003000e0400701c00300601c00c110b40b44009082e900e40543d20066190949492840d20580e015201d442c0a4a4071080c4602113030800720112542011310310790070b0040c000c04c0d0b080700c00d9080615800e04144140205030009506240c00c50181002c074101c04568078080090400440c1d507481d41c031200307480409000354404511109022541804120381d0008400807500c5003000d280c240c3ca40c60244d10f0002e14083c801f110840c8003410582c043ca90026001c030258959008010040080034000032b8841080e0402d14100075100c80740c4010340c5c000303401c40759044108060070b01d04c23360807550b0441040c0010700003449050358912800c0e00040d0100c0c940f0227054001c140501c82103c2138035400341c09008081000700703e034070b80c7c000105040001d116150240c00d000040400d5414203100f214110300b620a030b11800640c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 678309910 1250 678308660 678308677
    0x109082a0d03110615060313060216050d08010e0f060f06040f12060509010203100303080c070f030e01030c09180207060e030f0d1a0d0f0c15020709060503060c090d0303020708 77
    0xa8038102115508102007003841c1e440040e1781d00e0080c3c41c0800c1c4001403420722015203c0c00d00d4070005601c41c402c0c0071195044402881600003501c00115051800320745400b4564040000703d40140c00006010680d01102e0b440b80c0030031080305241381e0b2460100300700c0d00031301c541c50b0360407907810310000c1540f0516001c0c1c00c020305540103003003010840d00e01e40380c400d6074001483c20075240d00600503c51030a9a084112058030b5050a02900a5540c0c12441010740502140501a9202641505d09060b080088103800d00c00a0b82c0074401c0b00e6200005460394000d9102d5507160029158502288040c2d550180244620501004c140340d20b0042d1080c1c036540000d00400d42c22100014161001503240c820720038555407039150184221300b03440010b408000c400c0c0b8003074108507008055008210107039420b400a0001075564610041d03c0d0b00000390742d10b6040c0141c030340841c13626001040c20710300000c0340f40c0300380c504a8029142140705d800344201503440710021000c0c16028410342000a808602424000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 678311160 1250 678309910 678309917
    0x10050c0714070314210a02070e0c0f03010e010e09010504020306130c030c06090f09060b0306041a0a06021f0e030f070311010f090b010b07020108040b06060421020102010b0109082a0d03 81
    0x151170881d0b04583d503200022980c40340810401c80c00e02011307008600c400844280100080943d0f4034100100703000d1141402103044020000004280400c0400d80103040c0c40002c649600c07242c0c2c03014021401c94005940180d4580d00040c00115490101500b05143c18410f0001c1e202c2e1607070301e58a1500d9040c1a0300200d010415a140500c503d140307075500440100889801806001e242c190b44414520020348007502482c0c40f07517074a81a40000710b018180c250f902808415140ba990f510081d00d40944c00000d0142440c0201c40d14080203141c02a510b0715982480590714000d055021581c060b07000d0242202400a601092407018400384034205800210b0800441d00d58544d01d4103007085e4005030000340c80c0e95414401000940d9001d45025880356102500450320f440b114002004da000d10360000600b03c0d010310345c2c0105001407000b100543d502c00c2c0c0080c4a148600e000550310221580170b1464964003010502c4a03840000569030350000410310500c15151b4074502058045c81688400d5000c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 678312410 1250 678311160 678311173
    0x3010902030601030b2e061d180601180503070506090f09091c050c1b01050c16091b0512060d12050705071505040b09031e0d0210050c0714070314 64
    0x1e1000130300e6a4014681d010740c122103909070740507689803150741c6401034100308030342209515802e4440064003079684a0003401113400c0d465554084c13000060852b0894000f540031801e01002c40c13000760050303058950050241990f2030034481804806d030405140180e0054013401052160b440d00345180c1e00840c0e840d80540421162130041e07c11b40e070040001e41040080c02c004140c024280030404142d035081044401c00c035220800300489071405401803c1b042800340c4a502c0c03d02d00140392681c0c0c203c812400c1c00340010890412100c1c405459840d4a5010072020003040118504502041d903009400410740ca40d01d40e500d446905d02451106901800b048000400b14180f01007000450300411032008104140d42500500803c10302031407181c1d000c0070f600400e0300012554103220700610040c000d00d20b46a4442d440d01b906641c0c140300040c15000d800346404080b4a5561406914030880000c2e640742d103801c3c0f086d81d0342c0038608565011403059005041002c0006144071500f41d4050480400a101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 678313660 1250 678312410 678312421
    0x2040906061a0301061704121107170703030e03010204050108181911090a0c1e0509060a0c0b0c072f1503150901081002031312050a03240e0603010902030601030b 71
    0x40d4080d48510002103000c0104000026003107070001388d40366015107070003c040d08040030b440d407a0445a4001002c09009110070012200000601d54200d0740240c3c0e4072182d101880050508034416070241c240000c2e00034000410320200c4c14580d041580c8401c2c211913510103c582102c00c10484180100c814080e013400c21101c03454030814090300401c2c862001c0000c64400c04003c0e201c608003010221540800512600d21a8092002d0390001c110240499a6a40b507040005000050f260801c1304c0308211840851078200e05901603c902681c04072042211805900d0400c101d02002c1808510f444540e004102080d01c4a07008041c01488031380455031a41440c010b61048807074884061b03030041c600300700100400003000401c00c04654541c2c00051b52501c5a04030710540600c07011010b030004110341d038449400b130340c00402080c0700c002c1070350100b000807000e680b10900c1641030039501429022031681400351a08141f807041c1c001000a00000d5048001c2d03010a040c010300f40c0c0207a8651031810701304030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 678314910 1250 678313660 678313667
    0xb0a05060301020306031e030409110306240913020d1a120a0312020304020f190e010b040305031902010609111209010213151704060e010b010201020a050702040906061a030106 77
    0x58019404074025411071420700c0110790745600024201d80e440b242005a10040e540600c00c5030003402c441c0506004c070581e4152210302507441034440c1c0b80502602a08664105c00c003450150451400c00a100e20b40640607080152803c0007140000c68142d081048004901d090720861101d003990b903991040c0a00b20700104800d0b80c080c0520005103800180d28140020751140d80c44070504d1041d0401601c0352503138004241161081c0309401c1d00900751080c1c030080e0074100542101280c040e07551344a070f40d07070300c40207503420358000c9120083c410b91040c1320400c900a4100080305a440307076807000007505a69a50000d00361a00c07641d00d0307103601200140e810500c4948090b04c55022801c2ca0003940350030507040500100c0d100c00d12450b5010100b04540c0e19100e880740c094452000400018002c03d803c2504105005040008071031400758a007103080e00c5654018000d86032050000d86910381040d6070764081c80040c000710403089411a5980704040341c103c06a80060300c503030107468581c1707031250304020340034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 678316160 1250 678314910 678314921
    0x1141503010501091a090a1827061e0218040b03030313020d05010e0607050c010b0f220f0e03120a05061e0118060f090527040812040b0a 60
    0x8605288100018001039070082c080c00110b031549010b1a00114070507a8084a03030068000a0381e2101c00f00070002000d005100900031a03242501040003039100400c0c0680010340c070743d440e405400801017030000214050760f121350f01c0c4440c5c1d058a011a81c159501e4801240c4c04000c41840020001c0054011400e00f4400c50f210100142c00031440c5091501c6c1c1900340185804000380709901c1d0035910341c10032000703401c02c41c50002888100c0d0001c0c2400c1c00040c28940000e040c1c00403039031070048040101d02d4500c00038a00301e40007518241c5080f44244030750118143d03651000341c41540b0740300c1c04500c180b69849040001e400940c041e41c0c8410810350115500c0d200503180c021404d041c0710900000d80d440d0812911f010381010110b5405100b180016076860a1821540f183c0040c10000060445e030800307000d040b100d225546d40c01c0b005480340d041010444510744100b240e42d20301d41ca815040c1680c85111a045802021020704040600001d5a044041110704494401b001d0381800310107001c0340100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 678317410 1250 678316160 678316189
    0x30d021608070e01030f02060d050a3c0c0e060309070f080f030f0a0c06050a0c03050105042705070e10080d0f022104080a0b040b060a0f1502150114 65
    0xd0420305180020000036443c0c18040580000180601c440c21903039080216888080702c0701c4107001910704074005d03000401c1004a100b801140000c041f86a60a01b010315400444910b03168090046100b1201e10007020381c40c0362030090101050b441d1000d0f580f010b004d54816480400244034550070041625a41a40382d446840b440d8402a0021420300c0040705513007103800208101750700d400d0b03070000c101d40c240c2100c40b000e03181600c0c14050104041003034100402450303458605120513680d95061004481c008003880075182e5081003800c4000300742030007200b90f1030b00503070441e0300c00d40c1c69825105003d9801c0e04d0314594000c0800c42000841d80034800740038040c0c0d0b2810140108503115002a40b00c00c040070007404003181804840002018180548005d001a01c040303803803c805916041140703070801e54040c1c911018900015001d85007070005d007003d0b9081c03014400ca00c00e260440850320b2040c0b103105a81580200b480c6c901e030750752030b4401440c001d004603c0d0003100710240405000241075074004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 678318660 1250 678317410 678317413
    0x51309052406031e070b0c0c09070c0b07140409020711060c030a08100e010303030506121209130e030412150c031a0d03141305090109050106080c0c07060507060b030d021608 76
    0x40e40c4c010864003140c441c1c200c444070618180c1c0c03502d8503001c0904003e900c044090340185120207100202c0e030f0007260105401d00ca500500000e0f11060b81c142da129500080715560720004210900c2091340c540c01500031309100d4214400342040400000b030b4540c201c03924a0860740d00201f100ca00d804d520524964010042ca480c0c0311a40e41000c05540680805000280600d034640300030484945a156503007041190113400c3c0d45281c81001078004103507004200a40c80307100300c58a1240500003600c51031441d01c90074030055150074504001540240400b4100740c43c4880c500d062036011009901403010030bc0c546590000e03c245008000e43e9003141d10303111950286031400c1d60000040d8010b040c0c0410031441104c040c1e146e043d40c0d4064184405240c122680211000c000040c40c0c0c980d0b9004103068401985544c20540d0325442080e030b0a0060422040e0710307500c002010003000340640000c000481c051074010904060180c0407902c3c00c44100189001030b4010905018000094507144020300481d10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 678319910 1250 678318660 678318703
    0x1804060e1e1e060f011803060204060f0306080307030c2405040b0a02090108180a06060f060f1407020402070c260f0d08011401030905070e041b05130905240603 70
    0x8082000100e004014600a9540c94201d03041680510b10050b032480605606d515071548070702e44400650011f200e00004110b0f052a00703a046406801414159401d040095081154a0701e0407155402c00000540300c0c89504550800500e14001410350311000b9150003203074a0905240124103038070006d10310440359106001204003680d1141401e90024aa07100092410640349800b509251258a0013060545041000a00440c100b4441000c07104a07440e80116980004000d403940c11861001d0b40f00d00c1b100300144c1c00146001e601800071036019078003018a86403030b00c0e0a1044400202c69130501800c0354005009030070f90802010340c0c6a40420041c1103c83d802e00d0010b41541c10600403030304400703048003190310164865031020b0000b0342c200007240c40325990385c004100e03428005c0e5007d503112074507144150202c88070b40000208489000e0701c880780700550000840d0051180030000c49040c00703403007502004030f01204038402e624a200e900e075156078100b88003058a003a0b9002000d030408001d10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 678321160 1250 678319910 678319951
    0xf0301080d14032e080318040e12121b0d05040501063005010f1503030e01030207031e090509151306080a170c070e09010e0c061804060e1e 61
    0x1241400188500307041c414420344207041c83c1206445890300034901511020a0300b921f000d40450071400320f42819a0104140700181c0000c50302d4016690142d0203c1100308807840c580b5103003040503688100c0140031005c0300c410811003c0c216510010040800035128000e210500c8000c0c41040010000e2031503200d841508550426507c60703101c244403c0c910740b10f41400301403010a421030b04050b126032100b081400c5401003042d441000f140800c2e4009000c066541a2a502030b2007290040c0740c01d6150070601c66055110704000c1c1c3c1c400311200c003c004104000180c203442d070340107450050241121520f081c15140d024052035404000143d0403a40c10440c0c100042d04002c6402031006402c0345d51030302c03007509880c01000b8038410f615442d10540b28151000608030821800907014900440082c0018041c81c50a640e60b0445e0182c11540441c0c00c0100c980300e811409200c0755000070107080441c500ba5540d050441c00b03142111401104072144100c98210381c0760407403d9038041a2803407208515480c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 678322410 1250 678321160 678321181
    0x903030e0a020f061305040905011b03020a0504171f020423090604050426180402120f130605090a02100c08040501030513060e01091b03080d110f0301080d1403 70
    0x7911805000b81000175802d040a00c40c0303ea104050400a40240b1070f1303800d18900b0900070051006440f403014480c2c081e1038203131840b034022607070303400305503a102414941042c42042103154420f410042074451501000311401d44c7c68944409060082e60068449191218041d00f52404003002c900080c450030071010300d61707246040e254011406540010f1070307a40c4e500e40072000a42500d075481005405280a170506c01c0407500410b0f1090fa211182860390340d4180c140000c6e40075074541c0c044881c4000740000d8504030074110ba16413004d190321031644241019210b200480301c2c00c3e2010703240c9800c03513881754040d801d0864070038041c6080f5180100111005c0d8940e14281e001d5409250b04045c0ca950100b003000680e003250510300c50304510300300411507504e0360090080c0004503040714650030722000c06140000d9640b00724110394018092914201c3c4003035a2074020080c003404003040e22014000c142c001c0200c000a180a0035001e07008020320301a814010303020444522201e0102c04042007000810b42c40b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 678323660 1250 678322410 678322429
    0x120a02060a0506030f030712020c04060e04060915021314010807021c141207080c03071b0218070c0308010e0606041502070504020319060e13080a11060103060903030e0a02 75
    0x9440c01c0000c0c040d120fa200080c00c040606008440501c40880d40340c041c0240396103a4051602c40c1e03002c50301106108014001501e026100d0700284080c00c02c001b40c00310b152a08080f0b1114400e410300505244205402012178003c014880c0d2644444171050018603004480141e000302d00f400c000d005446c18140096481100c00e8a13131140381000071050a080d0b00558940b001000e181400c29141d2091080c00d05906108690b203100149501e80851340264425040703034002c103003680c0c41d82c64258101207400302010500c2c5040b0381100c114042030124044560200303001c1c154030398480d84040c2c1d07607040051190380180c005607400c4c01c038030042c0034072030703a4a00898040701c284146220818a40a50603410700d400ca40c005504039000000704000d00341c0c0c0758141e500d003880c2040c04008054480005081098046860110704a4002402c03030200d40c20402501c04d0400ca03180400d0a00c044202d0141040000c0c0d10403100503440e14050410180c140c0a1080810b90380b400520b050901d9800142d18200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 678324910 1250 678323660 678323671
    0xb041a070f032007063b010e1801091e140f0c190e10020a050c01210207050a0b0723032a040f0509010308070210050d051008120a0206 59
    0x2411080040c0c403c2d0b404400034450105060b20051a510302014200d09030241c2c1d0001000c0d0f503e252403040b1300d007070300c00c401b01c6d820481036190380310b40d2800041d2550030703800d130803664082000f9031440850701102c47c2840c041c0003135450102e501210715421680920841c0c0011161500b4205030808102111140c2a8020440d5407211441d0301ea0056494a42c8103400c0080f502030b15071045000804e401100340707600c665058925402201407140e080b030300c8050498000b44583c02102c0e2100ea19071240d9464026060044e81064034403441c4107441007281e104220032100b603000400c64400b4040411156a44040c540c20100b6036500201103400e4000c510882250b05180c002c4040307000300b46640410900c0c6a841005207407914200508000690032502c41d4072601044d5000100c0c080c00c10115460480394414000e5003004020307030802524141084c600d104000040c0401181b012480c054140503540030707d80b2081e00c43c1020051801c105400800d2803885d44108455550258005186940038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 678326160 1250 678324910 678324917
    0x4050303040b070308100e22051e060610050904020306010e12060a050a0203130201080726011a0f0a110102090a120506070906050702090603212503090303110111040b041a070f03 78
    0x203150480b40c03007000d00e104002032700d50320484141400e0240c4a150a074411956041281c100391313681420803102042e10320314400000d20074000c07844282400c0c0c028680000050411520440004010584c200e18504840016900000c1070100d200d80921805800c1400d00b2000c0d407442c0fa1291598240c9030b1311080080c108001d04e0005080c03644200f440d610100380b10a0b22010358800a84440030540080c024640d40b4200031100d0103180700304408980e441414004420b0174103103110400d582034804c55480900c555000c00c11244203589200d440e4010b445c0b00940d07048031500c02e003031552030207038024800828841c4082c41031111a40141c141c0f01e60030f604680b0740c45c0760394600000c07a003005200400e412129075070400c1845200d00900281c40c40c85c0b00079900c00503140c40f01d131007040544003408018001ca040c0c01014404284280182d11144441c1e100100c1d9003244104610745a07070280e03211041807240440c0a01c4000c0703c4c508400b101003264100a42002c8168a582c16030441503c4020b060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 678327410 1250 678326160 678326191
    0x33016031a0f013903030b04021219020706020d1a03070305070902090d0f030323103606050a0801020909150a1a0a09122604050303040b070308100e 65
    0x1c1c540c034124411521030b888128400004613000402404d109031804078042401c00410300c0c3c66003400c1c42503400c00c10b010341c2000000e44032605a42824a1103141c42070055400304404008a0aa40000e214081fa56500000c0303080390520802c070905d2083c00110700ca81c110f030a0801c049500015040d0540c0c100c0080140d03541c03000700c0042d000107050b000040c50b40c80030ba5001e07800d2540642c4402c901440c4008094070b01c081c1c081030308106503c00c03102684568a001418840740040d40e101e86124502400c151102d58510b012000c02d0360091400f14500644502040c0400e040400704d01005001c508020350400040d080000d1192400810720341441e24118110358440c1e0b10407805100074038aa004003070000940c200d0182180d4804c051140100d0f100000006419090181c0585415041201c5080420710300e6400c2c8500618400c40800000092001051a68080c0001c01c001c12000196559580c0340d4500078164030001061494240d0f10f04d8410004140b092540c20f501041c0c498000300b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 678328660 1250 678327410 678327437
    0x1106011412010c140f1605060406150602070e060d02090f01090f0b01020307140a0f0f060b0d050a060504140709060801060b0306060d1806090f03030e060603033016031a0f01 76
    0x481c0619507165446d0301e0f00c0552402071102c041003c82c080d1380541424002030700310701c4031820703c51683d01c184401039000f030104104401200300c0042c0c001d54010700070700c01d100003900014840003098860180c0007044400402481b1030520540c0c1c1a06400c51003030280c041c003400044d44a001c2c0e40000303417602d00c0d41d50320340e94040014046400c0e4543e0000529074040210300300758505804081d800c5580074a05122824146803450b4403480a82c1e0110090400001710342e1844060316014004580c3da148400390b5a03c120420702941e005092500d43c0020808d182441d00c0e425603403030360f2010600b10410010f112040c2c40d403070200e4a0207141d220380401c548841415000f44007218a00181c00d0902e05030101c4200300651003503c1c88140070fa03506200209840c2e591548408040d100641e16030300070171186200d11708042041910000c03c626003c245050746400b202c5401080350b03803150811440224620f20340d0107200710b09050114500c6495464031000224100b10510428207041c0040b403007001d071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 678329910 1250 678328660 678328687
    0x6040e0c030d0507260c0c0904020904080d14070f17010605220b0a0e03010c030c09050d080d0e1e0706021f1506020f01391106011412010c14 62
    0x89075a400000d030034414000310310080c0d8207400c05a04120745000d02c0342d40d085c023450254a282e00403900100a505075444076071b0b6103022039200703980e010101902e881079582101030a101c071620608860306c0d2080c03c4200002e0041c0034484240a580000a0020061081381c1d071100c240d440201d0301c0c00c5520003042001a8072a07035080c0c5540b01102980d07000400e0b06040d548648603c00355070040c1c0003407018852421040c0c0603201c4140b03448000503845d070001c005610b85100042c00031800303504070520b404540e005d40401e07150401c44221481d4007024401d4040c0c01300018051110500350041d02449081120017500c070801045958031035242110091503040c4158400c2d00d4054035080c14034141643d0750406903d0f00082c4506000d03651800505030074655a80c60008000c0d0a010004046041c400000c0d4220001c0048503804203d0841c0c014502d41904010540c040c020700601c1d220b1942c140810000c1220402d040c8a06076418540c907903a5941e0811800c00000000410040c0c64030004031048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 678331160 1250 678329910 678329933
    0x8070206040f030510061d04060209040b19080f06070203030f06011103030a0609060f0f0315060e0a06030c0b0a021009020f0613150219150f050a020306040e0c030d0507 74
    0x403102c0805000108100000410701184a0500400c1c4041940d54085480200c00000215052050303070700018001a040c1d0300510b075034200240000390554080d8085403400c90084103098214884a0b41400038820401000e024450300303000916503850503040080d2680005420b0024115000001c209a6070154141e1400400c104084a89914007452414003a058070301c01c0301c4109103000b4010070b024100e4900c071816503003030800d14900c17185507a556030000d8149100b136001041c0d131b03090045000d00c46500d403a40240b0418101081071815410800c52400d1a940030307125a820420003481481e8010403129002c0d98030b0440003840b0031207400401c92000702c0328440c9500140004043c10203151408001c420355070000c1e80c1c41503030b1200e10800d0f661665183d914140c03080c80c0b0040c1e50000340f007040f45490b54108000c80822514601701c0350400782c2c0c0041e18403007002e58000c41080f08508040c030403141d8501c0d142b001001000c08590202e0303100c54041c8405000c000c00051103005000441815 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 678332410 1250 678331160 678331169
    0x1211010207062903061b030a0e030a1101051006120506040e1606020f0a030c0b0a091707050d08061302070204090b0a1e02040b0a1214090c0a0506070f0807020604 71
    0x81c040086400a40f00421042d00381d442800b1840000020441c2000510b0364801c00200c08402c4100d003414401c0744c100d030070042c20303903044503110030419042c1c8000784049d0024100035140c06140e402e2015516094501c0100800d4410080744020007801c2d03404540c0542848c0341d00b40001d01c507116280031801070410340307094152a225216994218444454508049130f140b035080c4d600240410203c16241d00c50404041c002400508556003c10320105640360800f079541c10000d140b6825544107c1c4070821008041200000410b1a50500c035081c480600c1028261502e0109031806000003030200c50f50801c0d1602450b03001c100e031000c640765a4080e2704c0035900015010fa0720314058850714003a046a522840051641d43e80c400c0e0080034a000307840c1503c005041c642e0a00d403980c842160319940010b41e8403960781d1549484011540400c9880d401480090050038100071080c050005a407055405203002c3d800c108046404100310000c005c0c249603203c45160b0340e581d01c6000040250103103811 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 678333660 1250 678332410 678332423
    0x2040e070b04080d0806030c04020306180c1b0f0703060e1609020a0306080d081b07020d11030c01020a050a0602071109071718060727060c0606050a031211010207 71
    0x34045400e04501d07002e041103d51001c21180070710784030002142c0c007510a449042e0942d1000c040b0f446285807540240d03900840203440b4000e50a80071405110141c81615a60100e10340001e0030a024403c40f0300103044910403a0080081d024242401590350425200103080305940c0d5440215080003440358040c0e90041000044569840c3d4240f54000e500105420000c0f915240c40054030f00300c0480c1c281c000075a507448046d011303950b00900b5083c80e0010300d1b407a200400c04004e8000160b4601b119020041e000d038580309a0a000c40c001d161402c3c4402d464641036501105800001400c001480d55082e60b01000150b05c642c20344c90040d141c0c13506000955880903040d0b0800c00181d83c8003080340270070241a800391800d80c580a4900b01240c1460f904205640c001c02d001510403401880d024241550000b201d0076480600c071102d41e68503000c1d4000c40001102000b80400340200c43c01140050302d000c450034801da5295030303620b0b180d40415404c40303824010b010240d101000d500790b0546038032541001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 678334910 1250 678333660 678333673
    0xf0c090a030c0e060a060518030c04020304050307140c1e060d02040611010f090c030605070c1e0201271205070803030c04061805060d020f040f08060402031b0607080702040e 76
    0x260201c0c22001602a204490b90080f002509600d000703612281141e1580d151a450f040011b0f01c50030140709441481d5401d486400c50300b896076140d07440154881d60144002d540c46031b600b0b250041010003148250001799000c04c50321041540c417640d600c80e002910b0540015400d6107800811564083d003048140240d1012400042031600156141d80555103a402000300040c4901400101c906981015201c41c0518030280001021640800e0304191141420b4031070360090f54440395a41c0804035054200d4240e50081011540c100641d011403e0500880b648210394850100b03101c081107214035015020907004610900105004400103421403005480e60b904c0c1c01c0341c0090311076007c1d00c25071f00083d24820a000c0802c0050502c8402e4841c02450b6604d050445001ea60180d0005200401e481c1c0e0104800a880210841071200400980c80544802d00c4c1c203004050800e1414210001003c2d920304903e440c41d52403c04469000c0e5022480e540c5a04d0036001040c01040b034240c02c3c2040b803140c1c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 678336160 1250 678334910 678334913
    0x2180904030207030b0c0f090405060d060504052d061f08010f021306030b030c010f0e06070c060201141b39070801020c0601290a050c07120b0f0c090a03 67
    0x1140c0d01061300d00030642500382d625968504c003128422500440c00c2c00c0070a000043e01460190001600910001d0565000d003560740c07a14411038109490844403a4030030055210940c07200000c0c110021049054614200d074126086074440c2e6004000803d0f9140410303d1204035105041900c000e02080e41c000c120803c0b001000d40020362040408442215522400054033842030042001500e0064061b002d108a108010b450b010300c10241e203800d01886000783c544d25103502d00038001e044d000e500100100317440c0510103403c4070804115003d0400000c8100043e00c1c40096900c7c5510003582c42203643d480700445940c240b4445900110f001c5004030136011148010b05100d40c01948688042d03609695440c58003900b00d101e43d400501c25034002000410a403280303841c0c415003082d1035041c2c1032404205155005000d40c0007040400101d400841c01022f07030311040148d03201800450b05103002c1c6d2240d0b0740342e241c0c0b40340d03006109071101d1111200103440c50110030243d650b01040a4041201c2ca40c0320b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 678337410 1250 678336160 678336163
    0x120f0203120c0c0a1223010f0207060524030a20060c1501050919050402150c06040b0115050708030603012c0f030406050405010f0c050607170604060b0904021809040302 74
    0x40000c03481054a10300118402c84901410341d13803158041c0b86c07807260550360703032080441d852140c20303582d00c0e0b569690760403600c554940004d03d1440d1041100040c20314054148408001c1b49141c03015481403070901550040e04c0c00a00e0307500d940e420045020032035210394581a040000082c60540000700440d43c0c442007500007480103003c5941d07662a8a0aa8890003030003000d041c1155000c4505d28000c2250046078202d9000c2600b050000d400300740500300e041d0080b02194000c01e43c40e5481da11820800040c4032500300380030301400c0c420420017100030000400030081e00030380303002501d4940000042034031680d00354030481030049401c0e1044c8a44048540e101ca0050040d0203031a050b00a540d008200a04040121802c0d9992900c94a042608000044815110100c45441880359100d20300380811130400c9414810400e607603035140c401c44c0741040c2078003402e0040c0c001802142045005e0100e40407040030307030344480001e54005031218242400507182802134070303c607904143d19405200515a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 678338660 1250 678337410 678337423
    0xc0d06030804090b090609130305040f1511030c060c160204110a030c0507170c070306020408060403030606020c03061801090609050a020102160b04030305031e091f06120f0203120c 79
    0x7240f410802e14010700c09104a814085400e254090072040004002c007844111841c0780364080d1802e142026110181d0041c1260581c1021850010700180d0040701607201c10580008001c00c0c0103182071101002000b5a00e041c00b4015075004035001c5100004905410075000c030300743d0001c00c107004103d401e500c08032440e03000c10f158a0000e0700f81407002c1640e44c0114215103445501444800342640003514014803a0030214921109014500001021171001d001030030107080c03032602070041400d05140c0038003114201c0d804a015508141044030301070340d0200c3d00740da01910003041151617842c3c03405a50700501c00044028190b0381386c0b82280c4140f0000150f90442e0b98401e07022601c4080003425070a10b00c0304140704100c0003c1040000380002881000a903402400c543c51442c0c1045442401e2011080c044912414a030300a02c5082941840c906004111b0324904804100050822040704205009540081c0034521180144c0c41192010001d0720b0a28403071012070750b21514421802910f580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 678339910 1250 678338660 678338669
    0x1009120516330e0c0a0503100203040f0f050d09060f0203090118080f030301030209010e04020d240903110105010f05010e06070c0807170111190e01020a081c0e070317030c0d06030804 80
    0x12460010f428182170807a540c3c0c00b6150010020710205140d500d002d0065407000780212040e0503000c3c1500006076100205040c0c003885000031f4184440007090040440450340d200f5410000341c0c0d0743e040c00c0c09802108071458070740c01b864042a00c1007020024184418503900c101e6a500c02c2d9001203091b10b0012000d1410303a4400c607000c0002e6641c600d5405c50035002a1000381d0701c1401440c0020014000105000c0182400101070030b001491003007070400c441c0c0c103c8095002c5444034050b03003000c003004e1141d64090035200218040d136600b0304000820144200d4a45401070600142441c28001607460000090540030222105c450321006680c01126100700180300640c2029004a800031644c0180c1d000c00140c29010224000c00d2541100c1a062000c2d00d581507000321180100030640c0e08000703201e08005c61452003040000b80c00200119148031078207906a411110061000840300e550030700b10300103000d8030a620b035104c02260034050721a40f42e400040925250002040041c0398000d802200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 678341160 1250 678339910 678339913
    0x3070302040e250c03270302012601050f0307080d0f1b03170a18060b1804110603070203130f05090c03060d1209081009120516330e 58
    0x3d8454024070445040301c515050605030b80b00c40707503000052080300c1102c01c0c40d000345003c07001140d4842ca07801c403044081c01c1030720098514480510940d43c014400030070302c00c0c5401015804000b00000180b0300c84040c080c3e01d203d0a05440700b2941c072f0340c003045080d003c0d14811050712032721007820202400c091200c1d1005400b24003489610101e0700d42403e8190380c1d25030140c898000d00c0540042006003e58010b01e2a80d038266240380b101a00c07001031001e0409248155000121320106800300103000360703c00410010341111500300000200c00400d0003940c0f500030303580c8940b25103400000780c0c15402004504413050074000c1c000141804010501d6040350019502d03c18607843c1c120000d0002e1108644140e0000010120040003e204104003072216007035280c08070302681c6504910b4101011014685010781c2c0320800c0c401400b54198105d07100c101c0c1030a000c0d107403c802040b05510440d1140000d0412000f46400403451003488408040c05d820504200c080c541e9004201401003060790078082c900d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 678342410 1250 678341160 678341189
    0x5210a15050d0305040b130e04030903060e0d1e0e12100614101404050301111e0a140901031b03020318070f03240203100306050c03040f1e080307030204 67
    0x60b0801640d64240c441d0156100740c0340c1818402c9681403a8480c0c2640c0c031240504000006041070341d000914000c40c0b0a940c3c150300f0a2540c00c0070f1003a101075840c1c0d10380d15040000050283d0360000380340c10050146161b0788000740c2d01210149c8030020820100c58005a8001c032420070704c000412600802d0140d800c0420600c0e854010b00028495480d0982c0d811003c10a6100d200c14001c0d81c00c1d43c00c0405400c0c031149031584079004a0b095418080801c1c1110b100441c5070003050115030046500d40c00d802c4405400d1001c1c0d20720041444407841e119070103486c000103041c0e02a900ca500324440c0c102401c2e074100021103100400030001d600440e0080d260642c03501510041400100d030300d20442d0880e0002501c2d260460b21440c02e0001030001030b880c14150750005115401890020714420041c03d0207040340c50b413031420002d0176560005d0000b40b0b44942041003100081401c2c0006181a802044040d915800302208005000075004c0180190b10003004005285905400034801d4440c2e0b840602c44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 678343660 1250 678342410 678342419
    0x40b0a11060112081b010f0b13050f01030209330f01020a02090c0c0f010606020c010206070e130e1926040f0603050624030a060b0c0d05210a15 63
    0x2210207082c010944019243c040071004144018081e101c00e002148180643c0c3c140705001c907084803121100d2880036515010b091707075940b0b402480880c000c6400c150601461901014080690b48140070080c0b159180401058001e0a030030100f454010032a0004101024442155003904d110140300d1485244060304122103544042841080c1035405000440c440e205c00303803c40707681d81104c0e110440c03500c64251820912803003401a1001043d154029045011400e00028100817006090341d00b0321880002c040b60382c0d29002c00c40b4079520041c94001030211403100701141070142d60202c4103803404250342c900c07040c04000b001d02d00a004c0724510a0010038991064040207003d07503c2200101c4001c50820003510340a9041554400e03c000c051803c20f01c1e80200d407826900810000b10580702010003003040340c034600d210300f901030488001603c0c20864805a6140e48042d1030307202c10104080801d1100310025441c07040101c010707a003c140002da10700030b0b24410040c83c1118001d150a0102140080c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 678344910 1250 678343660 678343663
    0x311030c030a03030b190b0c0616020a0305090402040506031905090d0c14010605090703050406140c07060b0102070902040e0f15090103062703021b06191b08040b0a11 73
    0xc00034050007400041c4825101580100502c0d0020394102c3c0c4100300754950000e041c01c1400203017050b60802e0381c503101d10000140c5010300040101d03400c4420f03000c440050540000303003d0b030724591514010385e8030030001c8040741c003074000d130361040381c0010002c002d002000710354007601c080d2200110420402070303407210381256460380100b280801080b41440110045400425600b60340d056040021549075561400b290660b641200c5100c0013139524800d1208101103801445003942555000c10405d0401c106082d05030f10812000900b40d5503941600b100590091201e42c3c000c07c40e00900b1500c9594840280d842d10400701c0d041c00d88220580c00140c8400d005006804403132201400c5c100c02030782143c0c1d038031001b091806100c440c0744481d0540040703141c200245070803019110b03a02810351414034507002c68185211580d8140f040703106120000b051021846000841c1e02140740905440381c010700112050f0509550240240c80000350101d603005000c0020709840c0b41d259640c140c0c087c000740746107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 678346160 1250 678344910 678344923
    0x415030e0d050f030a0e06091506010207060e040f06090516180f170705090c1215060d0f0603080d02130f0b0d1a0306272b0504120c031103 61
    0x1c0011420a0100402c0709000c4030203568415140c3c00c2c00602078040e00c90315454540100c505080541c0005485005d00d83c0201100d60440820700007041814181000540500d002c1c2800c140201da81c2c2c01c61040554984c0c101c10b00418480c0010031040c10495812101540100744450108001ca55215600c114410b070041c1107600c200c000c542002d06200755240440e000500409030391084150214803503403081c4403070340220b1000500d96941c2e100c0e0710207298030010050680746040d1007451409a692280800c40307100b15005040000c00c950300d240704100816064101400041c00030a400301c000b003180d402400001c842007030103400316940e408507907005c034614083c11911040920010a030b00100350007074004003803542003e0740c1100190020910b000000c60303120b0b10316010128420004000000d00c0752425143c040035091030603152403d20b20042c0c84160541003202d0305904102001d2143c000d580c00b802d118100010550b180c1e050050b0284003501058500e0525071000c8851840c0c0051345 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 678347410 1250 678346160 678346183
    0x1110f030103140304031e0611160b10031406010e0c0a0e130b0d110112140f070507080403060b010806040608061b0d0908040e0601050307080412050f0415030e 70
    0x41900e103a0860303440844803250041c401c1010b10003440084001034030440b0040035521707120603010142c01607003050401d5880100d0240d030980070810040c0318107503054511036946608072000100685640408245a0003c0e52024003c000a911203c5802c1008680039040340d4a24080074155240c03451003141901c9458003081c007268030407015102d541000b218108a04140b03000024040027410041940c1d81880182283d0500c0c503200f1000313081d80c000355014035464212204105031016890000840310010f0b09283c5030ba004600011003c1d8428800c4070150755200014544550f600d2034020050400c0c85103807400b20f20078000050140c00c003071092008403074001d0001c0c03610b03407a05280d035007080740c842a9071921010304002e220200d0046009440c090f520070359516075507524040304c00041300d401074501410403100f001800000e80d4401e1001d90001d801643c0c0710311300e0402c200e0580e290701ca1500030712580a80401c0000f600440b40d00c1d1016480b1207034405104104c5000c071229142c0d10702d02d44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 678348660 1250 678347410 678347437
    0x50105060d0f1805340b1b011d06220b060a080714031203060604210501091208070c120309060b04090501020a09151b05100e0c030111 59
    0x90021034007550403205204841c0240007848201031025031005001d100019a03040d4400f42206940c40c03694205800540442c0c825000c00e69842040c103410b011852040642030840829039180c1d44d8108070842103010305e01802000840a800d06c000450364203a003c0d81c0c602c0c010b81c400541200c03441d110340c03d6940c0307002c0c60040280301c1a81c0d80c000c140101a15040e0480d800703400100d204002008808003403c080c40d007840750320211404040c13a1810300c1400111242d01401440810b03190700040d5029601880001d0078a0303042d001c10388000d80140c2401400039802c040c4d002c82440303010031000718040c00d150ba85d000c1e5507841c61020345100c1014a002445803d02c1400241d286d403007640724400e01c520900b400f0a411801c040080d01717942c40c40506641c035941c0060701441460b0800b2030a0300a00c01c00101c003034691207102010305000300302014408000d00120201c0208203050003100603d0f500c2031340811a10361181c402960f03524030319101c0c1d07010b98605035400c10b60103581c0c019200103071342001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 678349910 1250 678348660 678348667
    0xc040506030f0702150f0907060302070c050904021302071b090b010206041e050f0c121c0309140105040c0306110c06220503040801020702040609020f09151c021c05010506 75
    0xb540740081c850000d0a100441c0910b0300103075180c8084c0e410990003010003001c451100d0400004090070328065600840915204000100009940c1041d200c1103550445410745140d4560000c81e811907001100d585401c3c2c800103000040051340c4c644076a02001401e0444c1c41c2549560041e0102c0d0540021240035900c01c0d000500001c1c0d042020511414620a50003c00305031566040c0c82c0c10400340b480503403034102000c4404075007800c0c0010448010500300405500031011290f808000300300d40084100360700c821484003400b1107201a0907082c0300820007046646003604100c01003280ca8002114068240400300500080e81001d5542c41c10703010010304400d4a0b142000c0c400c0842e0740c3e9401e082e150119031141c01052050002c0c0c00100002c070005640c60f40c0a104110855011b40c00000c0708601c103124040d64900098140c5559070000c1e1428086014030050554007406032402486400f460f120300102426801d0b0007800e10704841c0100440c010003030910500542c0e000b40107451704100c051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 678351160 1250 678349910 678349921
    0x513030e0f040e030f0c06090a030818070f0303120c14040605070f0f0b09060a090804050402090f04020313020a170c09070302040f0b03010509070e130b01120501031a0c04050603 78
    0xc40c11000340710700041c00000e0038090406a03a0854004c60005217040c0c43c0803038028072445082c81600ea000481401400440d1030640e0090100c590280c1080395025030000d51810061080000b01c010740080d692800c0030070b60701c0c40c0040400340ca0040c26a0340505003c040c01140b030117840404401085615124182420310710112082c1e0040c03042664141a06901c000100e402c5075110b01000340241c0c00340c010303441c0c2070342814035021001d0320905139280b901c035070301000c128480155815594111030250b80c0d115640001100480035414507540b00f807000040c02641c0b58070a02c6040001e00c01d45414580781d580d01d111080d5090000000c00550f00b042c0341e028020b19043c95035035403012043c01c006040c00d480b203c00f18103240b0607401000300c421000004ac44a0300e4000f070801e0340030760640740611b0540000004a00a00e40c00c0001c00407954492a070035000b83e0060348903102d011003c410410080d0780d41d007841c0683e46400701e4504910641320b804038100c011088203c9042d0b0704060451481e6403540b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 678352410 1250 678351160 678351169
    0x80a180f120c0b0c030309061b0a030b010e130c120615030b0114030712050f10031401091506060f0203191b0203010f0b3109031812060513030e 63
    0x74003022100400760b4080410b0b02d000d0580640300f45010a402152030303103090010945803240143c541421594203c08032900c811804084440c400494600851001d4540b00107032083c817811100d01d54004400c14100d42d50940550052260042d642d5504042024211000c070490300b46006808501202c040d021100d5806a040b1350031219062410810310107050248040681040e1a1640013951246445202601d18083c0d42c0d044014100b101c002414a00107900307800f4041d01c00140a0510081414134401007903002e00341e100c0c0c02840c500c030b1201c000039107a030003030a26000d05800700d51910242d03803100d44000141c0352850801288400e404000100a0392140d50300016007e02e070408400c5240107880030301564460341800040410604100c004011000f2040000340c1e520a03180341248080c4045402d8040f02c0c0e50340050f000440722802e04003150031624810140194041c0200000341003207401c020010b101740140e1041240d51a4880c2c802c0c0d400400900290000b100305130301d042107142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 678353660 1250 678352410 678352439
    0x210090b030426070c0f06030513140c040609060e070504080303130f0f05030307030e0c03150c04030c0e0709092a020726060f130308090a020d080a180f 67
    0x43c44509010002c0c418841c015560214000701ea103200c0642040207020500002400504000d00b001d018520b8140b94100039480601c1c00a009d080c0300f86030010154000703002d0005210400340040c4029078940d01c408014224611400c07070700f00310302c0700010b0ba02c03403268003541d0a46000c10040c5241d034880035101121085084019200d2400328948007002820340b00d032032006e040c400c0c0091502c84c41c142201508840b00100c11107605c0e04407e101e84104d030340102c0c2810b000020720036450020381b24030f0f0907044140241e42004004042c4500d01003007403030f03036022110700c50807055075085041d40d25102c0010582d0709056450381c030707000410381c51a0000d0208400444008062040300c007580d030b4500c000e252000340c030003142c5d07000c0010491407058010140440d070352020381c082032002d803811b00070301040540500d260007130100001803004c6004010240704e00341c0c029400270a012502025401c00860302e0780b2400724400407403424000c01140c454020048401c03034681c0380e0f01444903840d01c2454840c00c030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 678354910 1250 678353660 678353693
    0xd1208041b060905010201180c0603111b0a0510020a090b0706020d060e0601172202120109030509041b0f03020f0f07060b040605010203180f0a210210090b0304 70
    0x2407000350041c604081c0655030340020007203a5100b8505516010000e402c5074210400360a2141c4c0720151940416440384003c412240a440c000454001d00c0c00c861503540242c000b20704075500c090030b1007840200000790090000c1e0194041d601d14002103d8150120320683c2c0d080b10100e42c005a0410a07840c03480080d11155004041c09480c04419003680f004030360b80368002e600140100e00070b1081550b44401203080c01c3c003030300c0c0c0f0454803030a0900e21650030028001e0780540c007000d0251030000710340782d01c1c0041c00e10f0b8543c00024020f403101da150140c030903000540c0c0302d80234a03d400d03004001030301c1081601011250f55140d030340300144206000c402a6000c440007001041003000705402c0c0e101d180005120441c05101e001030038214180c10002a41d06a03400541154024803880d91202d100c9000407103600b0081344d80d503080340104400f2940b28411a400500b0b80701140001075400d0000005240c1c0da14404ca07118050b0065084040c1c42c1c09400b40203200700123100f8000034001030607807002c41c1942c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 678356160 1250 678354910 678354923
    0x50a060506012607080601021f090c030510020d1512020111010615050403061409120c07031502090301060905090d0e030a0519140a0807081620030c0d120804 69
    0xf040e841c0302c841a41414001d500542c0000410801c034143c0c040c40300c54001e1800d2001c1c5c5522204403150744421504540010050f0769601c0d41e4008002181091310029a80318080e50a600c4201010b000290014480300d00f403e0708092070741c2012612051a102960f8400c003402e42400c070f054004490ba0445034080c00c10540d650040800c2d0722400280504807202207a458941e2181145007980641d02207070440440c10903400c1c1401045400403a080c40166007450115450b1158031026074980310081d40090840d04000d011407140012903001044441d1094000303000c240d0fa40c920030030441d502101d890070396030401914030320241d12501d01c024038400c0080c112030101c41c4039181c990901e4605040d030482c046503c14840100641e000307400c00701d6021800500514002c03500c076480c42d071151010041240c2c0c1c0016090700102400c0d003451400c15009107030ba002000e442c610307148481038410400d501c0303841000c20345c200a1030003400a00c0000d80c050748804802ca250030b42501c10480c0170308203c803070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 678357410 1250 678356160 678356177
    0x30a1202160c120515062b08040e061f090902070f02031203060a0e041728020f010e060114060f120a0b15030f0f070e04091406070507050a06050601 65
    0x10564403010140503201c5001900c0282c2d02d03d1510900d4000d0b1300601001e017030480004c00c0f405548207c0d16400917041088514a107032007031402c11842520380d8200038074004002c6804a0303241d02113a04140300b4581a04e050194462a0800107a9542041c01c0f02d000a500804280701c0450a80c01501c0c040c0c1c410b00c030408654840e9400242042000c0020031a83c50303000c01086081d143c00341c8003800510b025070440e42181005c0d15410100c000359640b004041200084101030400d02d07092a10081014600c0300020300b500c1078000703444d09e500091408940d070170840c00002c1c2000200c0d18a040714042044500107206050500c9010740080686009840081c007a90200203041c0305468420098034500040d005080700c20003c00200003020304021101c01d0042200c44200d0a006a40100550544d034800ba610700c8400c46070300450000e180c0d04141041c00d130b0000c100a1540ca000c443c04174506075a45035803840802c5460b800b4008010706950300c10b809520101d452a07011a402c41030603d030a980303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 678358660 1250 678357410 678357413
    0xd050a050c0304090b0a0519091104080a050a05061e13110a120b0c0301140d06150e01030b01120c060c020102210d0c140a0813020909030a0f02030a120216 68
    0x4681096104c108865194881c0044a00c0c1c11003c690240ca012103075000f42c60505400c166441039507002d2001c075941d5075106042a00f0741802990000c11405007142d40401c03491404580f80c0f0001c0754112428801d28010a190042c0301e51130310f542c085000700418080e583c014411000c00c01492090b01c0701c00b0490148103068035152000400b8000c004180c130303042ca2644c94402c1d81c0d1040140a540e8408042c0014041c200001000481e0b030038080302c079004405c00300d0616100804e0101c00540c01002c0c041400039110307982030300d568100e034066050380800b81e0b079507141441a03803c0c07264001d24402c083c510034081103000d600d882d080c407401072045410b40803003200442060fa01d0b048070f510240c1800701c1c400c44004110f00440c6c56036515031404501501044001d00a94000c0001413001e00441000081c28003004400301440305400601850080c2401c092036902da6000707006013400507110b01c0d80c0c141c0300c170b000000325150800b40340c1e905203074001c2c40c1c1c1d2030000a402440c1d8040da00d9002070340340310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 678359910 1250 678358660 678358663
    0x9100b030f07020706050301050f04150f080a02120c01050f070c1e0e070903150e030c0a11031501050d060e01150602010209041d0601120302030708131401020f0d050a050c 75
    0x501c5a01607032061903581c240302030064030b0401c4d160720400821000304010301c555103682c9010300304043e054070003180c5c6c203d0042c001c2444210f560001040e03040c4650300010608800101c03d204d2600039243c0650114488040c00d480e0801009020302182c0e042094124001800d0001d1051500441c0d070860a40e494083e0500184561403003003400018020051000e1400050206d030000524180481004e28585d00c011281c1c1c04c940403a2003455440307961010b001024000c64107485013103825100f9804c0b5501e003070100264110700c1280070744141c0c002c9403400080480c003a4140e4070001e0448090046595940300502000070220a0070f540720307040c0411000743d01320260043c007026000961504007200501c401c07a1030701d030001c0352070000d24224032840050100302c59041d2081d00d00c4006441681c2c0c1410f03851340c410303090010040c203400107440c1074103043d041615050701e2500c55000042c4142100490381c880d01541603400c140c1000400c1000c4034011002014034102a00786181800c10080049 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 678361160 1250 678359910 678359917
    0x10315050a0627080c090c0a0207030312061e0f0f0e0a09030c05061e07090b0d0506010c02130606081602030a08060a050307031a01090603030207090b06070b0420060a020c09100b 78
    0x7980700d0b5121460a130380c170b03242c0500303041c0d031040d006000c10341441c40c03038103009540700420302c0302a05106110360384903c030818603004880506080c2140b0382d407071400071804a211881610909000e07442c0410007040390440c11200340200e1300250fa22a4094850002d00740c01044200c10807400d11040400000000700248551840f400803410aa200032030030718020358242c10000c041c503041008200041c08201d001c0410b58890351040c01c000249580c900700160759024415001039400300620600544c14a140c0d0030040a50321a9550b0f400da5460b0110710565020419244901623081840b00680c900d215825040d808030000f0150b0407865507680200f4200700b9103170425a0180c225840c042d0724401010381d42401001c1e9200c080112070b2a58800946401e114001c422520342c83c3d00105140f5035030b40060354007941d007000d8025800c0c101840c14403621203883c08440368000300309100003018034000003a100750345056000307000c02c2c0813510f08200c1d00b500000c007115520800c000b4040703100c143d00c1c3c014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 678362410 1250 678361160 678361169
    0xc0907030507171006031a190816030c030602090325052817010e12120a0501230301090f030c02030601080a1104180f0809010315050a0627 61
    0x2545040c4150020012403211032a4094002003205002503c0107070605203046171203c0c600054581c10b0b402c2802c014100106049500c0700815007020301c03500d210200741048a0001045408e40c42180c0d002c034a00307015078807025108080006041011900c1c60f00104141071000741915001504003c410411031401c10301b220001c12501414040b074100f0283e00c036556400d008007282c620801d80c0d005a6407500c0d0740a403c52182d0360380c44400d82ca040940081300c890880909841d1800605454000c0c1a0800310380c2c103000d03801640104103030500358403800c3d058504420003600401e6500d10318441072033580d10702e11f41565981170044003140106180445c00c6110b59552100121a030041524142d4181c03c881c0541d0044050800080e910010b150401e44068801041c2d10420200c0c01002e940b40c0f0707202074004006280030300c0400c6010401040d20180c2601c0c20442416030600043d0a48031a0013a1a0803014191083c00041c0c0603098080c08000e48070300e0100d0101c00000c0e0000e010a0340d601 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 678363660 1250 678362410 678362417
    0x1201080c090126100b040c0819181e030f0815060a09030f1a0106020313140607140708010f0902241e1903020c0604110109081f0e071a0c0c0907 63
    0x85c1a280c42c6407602440501840d14500500c060801c030502c54002c2c045814000302c1180d944542c1454040c00340750030820303030742c110361502e80c8013414514010b40301c1e01440e4118000340c1c0603800c2800060040c4507541c0514140320342084001c004000380a5a5030001c0382c0c0703100340b01d000f400004c001038101045c080c01c0d41c81020300303056900f03001c42c440b00014010781082c070a640042c414441d408402c805024225800c5484800012100d00085643c511400034064034060b10000443c01c449000100342c0c04441101008101100c185210081120a0600300070350007115030309103c3c2181c4144072041000070481c03d5051a0010202c0c10103450001c0b14070300d008070310020502d101d10084803203003001c084140b802d080d49044081202c8640300d83d40140002c081d21009401703120f40d644940164006030544d041155034801c00198060b00050415a0114030141031090040d040000840c02c50111a44003800c0101c2c000405502d4010b500281e103041620700c5808502806941c071030401d54011007294030f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 678364910 1250 678363660 678363671
    0x512041e03200118060908090411031512030724060f18150b0304141b030c060a17070c060c0e090f09060115020109020d081201080c09012610 62
    0xc070708000c2c9054070761001010703916000d8000703a08610303c0e4000c0e050b29407001c0009800340907460704030b805004800c8669009841c0c1005d0b41d2805510341c0c000e500407140f1f00080301010403100100b0104800d1a4903141041d0400d102480c0012504418090f1042e001c640030603288618401e00412107001c4d9100c46044940e1a00c1000001d030091030505003007141d818140071445d520400001c010803180b0400802050000000e800d001c214608242078100c1442900d5500c034094181c459005c0480140910a000d800c0401140b803810380115162500c9a0b2039405d8000000c00078104072000c02044803080c4035420740c441d00040e07860702c19010728010310b40303030b01410b80315210071700810000040c0801035201c0c048003800280680000c015044410000314610381000d40c0e4000c078050811040300035000303a04410300d00c2c10031019401601c05400c80c0e03050220103070307a2042e8030707a07440c2e800e070401640041006005120513429000b01103d00081c0c44040c0c0c1c0c064001845c4103291407030300340c030b1401c40d1076032030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 678366160 1250 678364910 678364937
    0x31911190612050601051905120a0e0c031c0c080c060f0703060506070c15030b06030f1e0f06090c0705060907060912030504050418050304270c0512041e03 68
    0x50040e410b03820429040107140351010010740b8074401c0c07581c4403080804640511000c140b241e0308941c00700000e42c044455604107100c02e2006048003420040f203901908460b10a241800a00e0601001c50b220003a11040e40b071100a403403a103804102545c034084204980d501d0501d08004c11405400707070354010010341c9007071600142260b06035045980300318010007403030340819003200400040d5600c4110700d11045000000503802800441c040035040301c00402084582c00c032840555105074000010403941c88107040703008066280c100d800c0703c840d0051002180907818030040c030b90340c0803264035240e516011a81d100d8900c0c05004840e110041c2d0f00c9000c09000f910f40c41b02c10780e0000c10307071040c000f41110900e54002d0000d0061f8080d980c010396651032292040c031001541090840d0700302c0300340c82e0345070703129071160340706038541927401210380301480034030525001030300c2484602d1141c2c0e501c0c282040000c036036460410501810958400034030001e0614101d41c00344088201d14803076141c1d8000c801b2071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 678367410 1250 678366160 678366167
    0x50c060f01060c12030e010606020a120903081204050c040204080c0112020a1d0310090c090501080303010308070602090d050d0f090906050609010f1209030e03010b0f0319111906 78
    0xa108031040405000100079490300f2001c80080b40d0342c040100c2c4125048000d044000b480102041d01166081880001d417064000c92201744e0a40a0401491402960001078a200e245807100a02d00d070b4080180410100c1d080108641042c800e40513a90142060f000003000d0ba08103401114a94211081150f6150703040280e200c542001c00c042076042000c042000340180100d542111003500c0b1801e61020140d50a02419000c5034250004200c035400c9400c0c000b51840140c040c0c501080c0c40d000c0045860400001601c1c105d81d440103242e46426a0b50351440d010f50081c0d0131454010340a070383c800002940030301c254644900f40f075407500303907071180c0c2e4000420600d8940c3c8401126880c00c84240120f440700c80407142540c000b0308150040404040e021103004d11034544003001d507454640100105036001508284640c0c00720002c1c403403031403c00e0411854600c1c03034007402d5042d4809162501c0030741d0090001d107003090103061034560300e030855008610120070301001d910032003070492810300000c2d81 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 678368660 1250 678367410 678367423
    0x501270b1b060906060d021915080a090804030f0f060c05190302090a0302010531031a090705040b130203042a030506060603042f042004150e10050c 65
    0xa8a0004280906003c1202c0e9103072a000741200d030085018942c510199160a040e0080e8030a00644540d01c0c0c076a0b89240b5041800c914130b54200081c02400070944806103801582d0b0010b8005101d10300c1d0529540c2c07902142d50114204540403080151100c2c00b04a680c400c8040e0000c1c50340b603a6950703107240700070400012940d02550041c5441400518081d071110ba29010a0703907420300305940d03940e049181d82180c0c1000c446148400d419016407402c540102d0003032101c2220712480280301d05101d0080c1c0700030340d0741045580858603401f22604000528241e000365071030300c0340545020341d41000c2c1c3d068441a0390045034192018481c201c0280c0604007101c800800080780348072401c00c000d04594410b0b450b600090a4984a050080040340038000d4030032212507034100c4049846d0300d20126003c501604020034020354070403807a094030308640c006c1e00c054241d440c02d20428110301e081c1c02c1101c2d001601c0700c0104804100001c80c01c42541e59290740420008041e942e031903107600d0b40341c40c494103464140f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 678369910 1250 678368660 678368707
    0xc110f1f020408100b04020c072c010b0a0e0f03030423030a020d1b050405070c02090a0203072c09130c060e010804020103020703030912032003100501270b 68
    0x41c41000304105030580440d82c1855890a40c502040228007440020003074001c5030b401d034015001d5840e001440400054030500c0c0d4400e4098282007181a203461200d140d8403d21658508040400149440c24410314907002d01e00303802007407185081d848101180c9581c1064210100c001c2c002c0b1403109030120000106000c841e400c80041081c80c4144d03020540003140200020122207d234800301400e89815000003003c0c1102500c02c02241c500307418014210341c1c613001b040c1e00400504010036040c88450007128803036a2a5111028000400d900c003000109a01020400c0042d0301c0205c5c028969880d0039580c000c900e11f00c0601c8500f5901d0030103c120f5000366211005010f42c0450b4180780e641c00402c0345511036024280142c54482506081d000f0b40740306940285800900c41084055682650044950004029410346400080440300400e403106441c400d02985003d04100300c01d61203548035050655103101c629001585054540c140e024250f00081601c20003c03624021680d8030b8081c0d2050340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 678371160 1250 678369910 678369973
    0x8061e0907030f080315100305061903020f0d0f06021b070e0f0c0f0c0d05030702070f0e0a200403060c03240320060c0601060f0f120c110f 61
    0x49103150f031035442c0720605078401828180c1c0400000c0014461001c03003030701c00f180074004800c2002c0e4144010300900c01200c00a2107200045c10031610480e6048482c4203403a03024008002e10440042006101c2c1181403049851140c503000d21030008280d80050310300d440c9108040b40d0041c042d00681400c2c00c1c4150400c0540b140b03000100103d2001982c101360f00714003050300c010764031030b0740c031804090611940309403504901c164100d0301c0701c0e40d5111006504c1861070340c0c01c2c1d650890301e840504407008504d128042c000c0515001142016010340d21003503003031808804449601c680e400500c1815049030340142d400e5076484039100d603495054050103808a0241c1c5040c403603142042d00e584441c00702400b000d010003122801c4940c080801c5088000e41c20001440c0c07072380300c6400600071070392001c0034058100000c4165103100040e074003811114404104d2529030f001c50f9800c0b03584560090000c2038414040000b0751416a10000b0140104540c0c0c0e81ea14002d4410140200820b509045175800000902d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 678372410 1250 678371160 678371173
    0x510120305041206021615050109060807031e0f11040c0e010f030b0301022b1b0507030e03011401030b070e010809100906060e0c041505090f0d030908061e09 69
    0x2540001102d0a5944070680500c1240050801000a0040c40050000c01241405000902680c001d40c81c1420318030b110240083d80c0ca88911406603002c902c01c01c0442e90240c13509100181e5480103032180c20290441001791790503680c07191141c03200b0101c429212000f202e00301c0307165401c19008040c0d59500310b0074850380c00400039000a2111200c6110381e410140e86020f1813030565000e404032109040e01d100c0c1c034602e0301b0a1015101c600303410b010310400c0c400c1c0f07054040160850071101e08440250075446003424810540c50545e20b15548a09440e41175684031103880c42c107600b0401890207140502600d0f0818644100090b00c6128072140c42418002100c080242c040070002c2e100307200c0110300001082c00011031071b050f0085c029a80096441041c004100400092900c0c0544220360b5010440d0020722401c0a09480034441c0c070351400c0d0890b24202c0d9007811070a01c02c81d0b81d00001e110b460150400c540d10b4013a942441d00507941e04181021036906d01191240030040c0300d0300500c45001a018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 678373660 1250 678372410 678372413
    0xf06130b07120207050a050d0203010e0609070f0503060906190603060c11012d0e030f0a020a0201080703050f010909080735090307061809060e0720120f07080d051012 73
    0x78421b0b4184541442211914001411503c0070b422941c2c80c0c4107480121401401c001070b00c42d403280300f58050843c070031a41c2c0d200041d280c81c0010381c8500600080c401b426135901c40408801c9820a02c98088100d030f501c815002000071014421031019410031381c0c0301c0301c0100c0b5900c00c8509444010760840c01e40700708040f071113145902024038000da41d01011000611900810707207460840c003a03441b11400882e00403891503a22600410342055140c03003603880ca069640c600d441503007103617030550704154400107100040c4002c1007568070034000940a0140e690a1007100d42e101c1040a910307107100040d05c0c1c9884a0304d46a06201414549a91b1012100301e040551101c0407a50307580403481a081041030403031500344426040d02060300a0818035034107108680d00da0b1018040a0400d0b40c1745e81c00140106244046d022040c013100300201c1003400a001c1945a02c00070911310740010402001e8418100314040c0003a10341c2004105810000b44c01041e41d00e03000a180d0010200c0303510203840c80c010b003c00d840 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 678374910 1250 678373660 678373669
    0x303100504021920120307020d080903030c132303060c070803150a05030a05010903090e0402010f030c03060902120f09010504032304091113150e0f06130b0712020705 73
    0x8443c5424600104840606504800c2c283d0007844400c0643c0205d07003102d107007100740800452054919400315419103030182c400700c80500381142c0c0c1e4812074000b4400700b802e1041440c01000f086a46a603a070003456110fa0000e1841d4a4107a0840300790080b6003150003450a00740600c2e5804483c1d2801242003000716141c466581c8801024082e02120022a4004907030320042c88001410015007116010907143c07070514000c24108105901040d2100030000c0c090030410031740d6100c1ea6069480c2e50041500300760588c00340c01601014007d040d10388a0100c2d948802d407004d0031f00480c92a4140c14141001450812041705c081c0038900300d43d05110400012940111080003004402c0e19541c074200d100c1c10345111340c0e011b81d07004440c0c0141041c0b40d881500300200090040c48001c80d140908003652211110b00b1070301c1c0183d80f4000708000c42444d10307462030300807500110544050001d41c0b9006c0380071039948482c01142c100807103d80c4042804428800c00003d144802e82e010700041c14103a09080c0041c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 678376160 1250 678374910 678374947
    0x90f0203241e061b1005090a03121e0e0102071103120f031005040507090501110c010206072a050601030b010603021305090c0c0d080712050c0414120a05030310050402 73
    0x44050390071015850106840e42c900300c61264034160351003901c8040c0004031603220b4000417507148049082002140c91441c011568081803581902c4840e1100301404003d009840c01406008000b49044880070342464a809000001c5100b0310005030707103603428900b401c0035080581c4c4c201e000b03500201d2010450101402191076092008003410740b00e0303480d0a40d840b030701c0d51281c00c5680c005080000f40415280c00c044180f003995026214030b86e00311801401c00c0d981c1d05881030460f00607404007002c10403850207001300c0760100c801804c401c0480f00e455819802c50182141e001c40392948107400403c24000c50907016400741800c1c0ca0254030f850742803d24412515007d008442c030904c2c2da8400705400c49029011507540d0505041511800c1141501c0a0100c5c282210b0102c0801d038020000300f10940329200722445440409600c80c240307030501030b5140c80c03122031440d01a044030351200d800710041c40400c1029984c030b01c180c00641d40da181107890145040451b03401a4065401840204040125200031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 678377410 1250 678376160 678376189
    0x703060e030705030a050d111c0e0f06100e0105030304030503071b0e2503180605100b1c0b01170a09021518030114090a0b040c090f020324 61
    0x1040c589044090182144600030b4024010f21001515041458219002d00041f94103100100080c1c4078541c0074010303512661b02204450360140021140802e0b060b40a050700c207403031404488600c80e01a48051903e201600e0f48500742214031000c11450800340d40b040e001d02410750142d03040c1407a542e40d00780c2c1c90040440041400c2c42d0000000e448520b00d1b08c2c408001c100c1107511030b8840c10418007021124002c0c4400d10703035800403c0e080240882c02402035181c0485010014440d14001c2e44a010080c00d010344000120500b900001400c1c800c40310240450312518410701e462901c00c0c40c8040300f101c02d070034900d6040c0900700c030544034588050341e035155014203d0740000c6886032003440054090340808004c1820308002151314203010010703100300c080c088416002042414038130b1507010074580c4211000792aa601c03001c00140001c013489207843e041071240e00561122519800c040040e0389000042880e45a4044200701c07012001c032034081105426200c9010300d124142d000b09085100d0780c0701 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 678378660 1250 678377410 678377423
    0xb060d02060316170711070519031401020f07050d031b08070e0111030a020d14040503070b1803070e190e070b13031e020117060f0103050a020903010908030115030e0703 74
    0xc0c44041280105054161078000b4900b49020b031416905c007401001d11b00010300260f2180c0c240201d50303410400441005030f241c0d042071004252031980c03020010005983d24110a5400340b0036204030000c180d002d406050f1043d009042100c00c90342004007286c0c1e401450010100696200380461a00802690f40001c041c1c5484500501c4280050744c02c1154500c2101031444000340f588030039503001c03030305e840c80c2003007580c3c2c0c8001000c020b0b0398226030380031318003130f80780d260300000c01c200500e90800005001303642c049207801d0000f038071907000203051803a41c3d0b01c002c04003442030301040890800c140c94480c62240c10101004610040307803040340d031030055001e000080703080002c440a58272404005c0c44001c56000d00120035402d01c1c2a40d21584c0c0c09844422804100c8181e030000d0401c007000c040e5842000c000d4822000514004011009084050400111260300300288503aa072428000e14250601420600780d072540740000030801c91010b4007140c400c00d450400ae41e0780352200450301800b240c0e000007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 678379910 1250 678378660 678378691
    0x5060706240305030301080d0c0213050712090b0601030b092509080102130f0b0a0c1e051606020c04060e06090402060f0409290102060403120618090b060d020603 71
    0x68101100c03a80c80c1d5070a1004940c4850002c01c12100000450590384c0902c00e884591805040994012915001c000d40c030a24a206400c1c080350154081c41e4400c40c14a0201d0f1150700598901c011180b003031100b6203c013038000c3c00f04200c0b0b503018050303920740d10b4040d180380c180380c035001503210444c101e82241c25103259540b10312090200d104d442240f01a0414000855440590f5140000c40c00c030140b00754040b0b904c404100052800011302034401000c080d0315600d4080200c1c0da03a4005980c52036507800d0f0030303441610310714001c01c904121070041d0440215488245a0500038083d1600f0002c0c407209120341d00303218050185941740115207030000e9069a450302d1030344039440040d0700d0380160050340141c0b0101203800140282c960b0000c4400c00311a018110382c4c45a40c07004400800fa010303201c603025134040b0b8080b8000a205403072501e0050a02030001401c12340721400d1007400d40441d1038a000550b26001064140060701c000b06030400412078452024071116401301c0c405000007420f4585030003008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 678381160 1250 678379910 678379931
    0xb09011d0105012f0c1207031101080910110f0408060a0b040e031608070515181c1d041a0108060307060813030903020d230c01021c021006030c05090a020405060706 72
    0x40005e0b070441c0310010a16940007070788003ca55941c811a100980b0343c02a04a1510f00550003040c003240111803a1001c3d107582c1518a030220098800c02c062844880c0741004242038403041900a0005000910094005401c120b5403450580701c46c0e0408500c10380ca4034480d0701c56688000f003100d140c61040d070048085005203051080079030044c141d024205000700d00e0840d028416200c0510310460b2500045900e0002e80d0003c69a1082008000d0800c0d01d42c07807000f8241c95000e5003404801c5000142020910a40000070909a07883d25203007544040411002860540e00071511580c003240a80041c02d020b03160040040851601600a0100420f40502c120a15100c4e582800c055900644810f040c4405d602e450f075028820b0290303101c1c3d441d074811702c0e10310040380110b04128100c1059004200c8568040e18820300d404100c0c0040c0d056200710040400030302c8050054000450007200c07000303042c83c5032006204204100030f0030798400920400003413140f980c405042c3c46407140c1000c0001000c01c0e40c3c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 678382410 1250 678381160 678381163
    0x10060b0d0c1404150f0c03050304060522050c0a060c15150e0906071b0302070509190e0303070e090c0403110f04022b0902031f0b09011d0105012f 64
    0x402c01c181d45502c0003901203a0381c2004e1031003085041c00390b40da0b078211000340301044840307018512000340000e5081011401060140d0462504515106d4001c480b244412041c1800d080e91320320100c5c1d494021944100310b500c0d0144209006100d10b00b44802040c8095072030045481c130284144602035910004080703031021704034500c000342102c1000b00c03000b802e000c0945a92800300302d0b61500000e1408007104011005000618100c2e83e0580003043c00310300303007010483c50304c2c1c0080c0400095046c00c40040010f041c00c1c0100400c10403070401842d40c904141400030b007045000040301d0b001c1c40c1c00c6006e1219100318001110216a08400c00c581c8040707200e80040c4141001005045d401070003c62920750403d02c12561017074507444200c0c40c02000c030400420a082d00d0001c00041d505820106013202103a00c011040c80401508640019041000000180110f1000e0304054403040c110039000c417800b030003404502c1c054402420200601c00c40551240d001c10080e41d0344407076410106540c2e0720328900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 678383660 1250 678382410 678382427
    0x20d08031503150604150503031204060b0d2a0f061b060501230a060909021c1e062702091207091a10140c1501120510060b0d0c 56
    0x20042c2903424140000c1041890840151603180c8610301d0040200b852040e01c142c010308551004d409181099150307029495076100080065400c1521004a1500b650320040800e80d9103101e0403400d90380112031039161035212000525681c03402d000c90b000740302d0721040309500c0c3d085841d0303460805a034480c0e01c2c007420181c15030720b8001003d840c2000000308440c0f03501c412045a4418811782034181088200c1000801c5070319105001c04541c02600900070070041f40c00900786489101c1e80810f9000300d09901c241244c11110306c1c003141c60101c440c0c2003101c54040c0250b000074000c0d8400c400d204c0050380d548114000c60700d40c005c5d10403640004c1800454441090300d000402d99001510070340ca42d148500d0005c2e280c0b0000c02000c4440070b0443c800781d46041d02e1b800d40c41075004e903030f0300c114038080806406003a400002d00a6035445800c0e1004801e41e600200c80d030103040a41000404541c10b494000e240203401c000d051140307400c1020a2100d04050402d840c8400c100100102d00d004000c40c0641c0c0104 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 678384910 1250 678383660 678383701
    0x15030e010207031b03170c0c06060a03080a0e01030e03040b1213021c03030912090920030f13170d14090a080a03020d05090a0201080c0307090b07060b0603040506041e020d0803 77
    0x172003030300c20047d025480d41c000d04a81481001500c0382c640c1d0b40b8081000444c02804010410607003032120380b0006100f199400811403048c180096600301d0112400c2c50744c0c0180e44500c9a0b28400140100300d128800b10854001c1200d07845003000c00e11681c0003421080c20b01c08810003c20100d0021410b0502c42d0f007207440019005190482d28240c1d400c1300a014007400d015041c0e006043c456604000d06a101103528202429140b490454403882084212124003521910929002c010750b0004910039580880080d82840085680c51029000c6541030f83c8190000c544c6904580c4104207807860003168800b015684a060316540e0890710505400a0144002c400c44a5250004026002c603000402c1c000301c6000f40c90720b189560390b40c02c489038940702c100c810780006031031400c0c10011280c2c3c8a0141003210310903480850803900410105005400864064649901c01c9042c003040c4006079a9011005c180603c608805e00c4e110b40100e54403640f0f41d40001c00e0762000000040c00c2c82c001074200c5660a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 678386160 1250 678384910 678384947
    0x90402091206010627050906010302040305340b0313050106090618110301180b01090909030e090c04210c1a07050105010905060a03060b0d0b0115030e010207031b03 72
    0x818081c04450342e03240240202d40105030b403440210b0100d030307500c01d20040a032100c0280210303450400062200c0480098541411b041e024400440020b00504c10030b80c84503030040d82c0d20a4155526981c000b5500310074010080710700003400a00015180c03600f03c0c0e511040c00e8410303030003c1d40c051030312500602c0e00358022041113291220115004040042007001c10328603680a01c0a410780600c01d070080d200a220340b111186040c4408104000e554214041d038500c141810502e242e0fa4114040581c1c492280031000100d00200c034005620b0302a10440d005003e0605050816040416807809040d409054007686200b0100440c100607a95042101410115640707040c160f402c46c9007017400b40c000301c1c81241c095090400100d414000d41c46894070944004000364035285c0356446450041140d00c0344903402440079802c0c100820100d44645000340403518640c8169841c0010040071501005402501c82c1d0041080f500404c3e40980e40c0074500e620101c6c1d401039200d0714030341501e10b5610300b040c0300c42a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 678387410 1250 678386160 678386179
    0x1031e051b03060c09030606010c0317011710091104020d0b031b01110a050c0d03030b0d0309081009150c110d051b0a0c0b090102030405030a0b01030221070b09040209 73
    0x707036080d40801120400580c100c3d4410307100c40c0b20002c0c16005030404d094146e40405d0010340c81e9803140b019122118003a0a0101941c0b800c2200494140c000360481d41c005007842d101c4d20f000030010044040c04140b44102000060041da48180d19030607102e14041c03160707402144d8507501e00880e0340918280c810040488001d039a0b0070340da003603030711070110b2141d400300b200401c0a24000760082110100c0b2a4000c010b486950304400401614001c0c200080e4205950713500d100d5039a46500c2d10340042a4041e40314401d09500e400100e07882d0244000030f16202070704001822002070880031b21000c100c0304201c004aa000411003003240c0048095603140014400c0300040d41c84907411000925180800700c04410040341c46000c56070b9143c82103200106040440c88041241104034000341801c0c0c041407060303d25183d941c200003071400d00701160580722540114010811490f1190360110810315807c600074502d161040c40e25150ba080d4810080b0040c00010040d480e40c0e90b0f641122642d0710020643d004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 678388660 1250 678387410 678387433
    0x30f0708090303090606221407110d050f340b0a060e0c0a0509060d05041b03081803071d01090b0d02031c0207091107061d1905030c01092001051201031e05 68
    0x12900990381140410400c042b01040440b002c118290710180035100c2d00c2c90101c0c4407110810982c03104100c1100c0324142c100c0c0b40080258001c03a00781b450a21420002042c7c09800d02d02c03603c05010f4900ca40891610404001f007040307103a622981320700ea104029481e5564181c1c00d403854822025620381c4560300180400198450f60b005070f0049004101d000342d18043c02840340002e11040c000600400c030305000e10180542510b4a01c070008202905a4040341d035103295210106d80302100102d1a048400014000d203542c44c41040900b0710300710340e2420000b18a40100e41c4405400034011a40305101c10340e040c40301e0080090f5001005580c0c000c00585a0031404102203800c068011600541054803603030704c1401d81c0e44040a54030b005009010010b0300c06035040720b0495480344c00c031260301061100d90b05414080c4280395020307014001c8181420040707980c6141151803124800c0c1485818051458034a00365011241560385c040c40b11090342c001c02d01811003004034280020a1f83c401c481c414003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 678389910 1250 678388660 678388691
    0xc07030809190f031b03020f061303060e011409011b0809030c03030a0903020c01030b130b04090807060b03061f03060b0d0213061d060904081e030f070809030309060622 74
    0x822240511110460464a6441c201c10207403d803001030f5000702d0401e007c80039072078240b0050144401c00ac0803001c000741d4941d1020161840e02668910596540300315140002072960401e41c0300103200020000090300504841844007000c150104000e13004000a94014082080750707540451070003226100d00c2c040c01014003070310032018102c0050003100d6926aa6501034011152000710082103903081d28820b18001008007501c00116510985600505020400c4180103240703041c050140403440c0961074080c94a400d074041c0c602c0b04102c421131405800075036a0b606050079207a0008e80401c401c00500002000d40740b0320305020394800000300d103070b0700d140340e90340e0003442212052045107a1400041074000c10f28241200d200c2d4102d500c04c000100011216002041076200042d003030404c40f0340c0502c101c100364004440521400c2010300601400941103554a0740c041380c0f10f8011840e600d4008907064030380001400c070b40d006111070722034040d07006440c4042015084941200704014078100102c80e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 678391160 1250 678389910 678389939
    0x30c010e07030212060f0a020c0c2229040b010e090a0e060108070303050708031f141f02101d01020a080a0b03010209060f092b0501050a020c0703080919 67
    0x204c0c428007003000464000c20022130000d218442c0c0c403841e94032964070303d018207010398080c5001d00311a018581180342c0990b1000205441e20041d988001c55002e903220400c0e04039010030000e007803120880720b100c114000400e0702392000b0743c1c0306960218200c1c2440b00180d9140b10355140d001d522100390f60403c05541826484400e50078094003c40d009079030317141400e41d120320090001500283c001c201c20000701d84654001d541100080062882040500d05420800c0d445500a800c114880c035110410381d00e0101c0120140382e10607000d5040b5071104c0100039541d06d003801841d48c485521054a8007044010900306443c0a081000030f565454100c0401410b248040ba29904031504e0940001c5581c10f05200340c490300400a044c0e28601000c400010b05103400108406d0351084078014401c22040d28401185000c02d041c80080f0b2919505203880303400d40302c0040c46107007414414450803980ca036000406008580d04042100d6503a10200003242c4800401040004080e06150700041c0350750040490 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 678392410 1250 678391160 678391163
    0xa0c03060c030510120803041103010612060e0607050d20130e13050307080d1107081809040b0c07020607080c060115050c060a0b0111010e011a0402070f03030c02030c010e0703 77
    0x2000503903980f00c81214280c40f240100880c804810340c4145c0011002c02c000d40d04240140d2103132980c0440800000e0a680241c0c21140709030080c502c1e0b003030400c50607000360741200d0b40250183c000c41c9490310005240e0b01881d051030000702c0c0c031541c40c08801030550f601d4070300c200180580c190341e03804011411440800307107208100b207100e51300001804a8414400c00510b680c1e01001451070a125610751910700d8000681030305881e41d540307030900d80501c0010018001c40d0321910085403130720034110221350030140710300c9110b00400050701000300241e0301234a441c0d4003585001e4074588455050011581600030311000030000c55001480032114000044d1542c101ca154045800c00040101e1040701d840c056408040801d42c00600418408a1180c0181012034410f00d0440c41c001002d41d115400c1d980840c42039070713080c0d42da00c000d120194490340a800b107403801070398254544400341d52055401070544d00d0107030406581300d0030711248510910440ea07008079000f009000d040d06c40d10440344c840119110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 678393660 1250 678392410 678392417
    0x118060302090a06212a210c2109060609020d060b0a0e2106070906090f050f1903020a0305030c0607090518060307090e0c0a0603050f180a0c03060c 65
    0x352144501c2c21032407224041d05081c0d6009a01d068001c001c2c001c0c600c0d154400f0040440d0703906011521520644d1b2407013803540c0d08643c914145071b139003941c000882802e0281e0380c2800810420075401c14448210340c0200c15130041d10b401c9500182c802003075080002003495082400001d20f11449030083c02103040381c0b078001c01005070350701c201c5d55252084070f904070041103011003200c00c64501440c201c0760405000c02c00c40d03200480203a0103410490111015008185090310502c01254401e824001428603140315012580c2000b00082802c0548101503200d941450802382c1541403030b12a00c0000c5a001d008003600039104c0c500300d5105c1d0418104494070344100740000b840b080c032803003016044070000303001d500c00922842a40804864010101601031250b01c00000c2c1200c0184036010401d95000003520030070800c2c0d1304122140700a075001004041c10201072000300c00040c045541c2280c210703076003034441002c418401030602d0701180d005003006031420400402c4c010950042000f4800503603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 678394910 1250 678393660 678393679
    0x80d09140301200d110f0c0606060f0f090a03050f100b0d0804140315010609030b13050c061c020304030c14060f01060e040212100303091d0a0b011806030209 69
    0xc00345800c85080841c440ca030400d00700324903800c14040500811084411850100354000c0e08070640034035501004511240078000100700e00d200005100494002a044891900c1c0440c202304c2142580103000144883c03c600040c110352540e20000d042000b1603201c01602c41c014100100d15803101d40c0f261581c101642020701c01d040f14a0300c3c0c0c5186c1480d6074003500041c00c19084c1b5280d02121940c110a40384c052045400f81c5d031100402d007235040e00828860303441034509801d510f4050380c0c0707a8004c0c002410300042c0d807c103040054001b040d07181c688442541e10a407901001d05485290401e1150010b50325840017041c0020b0503400616030005900400303a0106251102c40c281d66140c40c11105124a804010014000307544240f401306580e038401440903040c031b0f8030101f20071480d01d030544a4212020411204101301500050001e000345541c0c0760050ba541c1c46800103034070352100148050780c666520783c600d0580368022005c96640c2489024110301e07031a1500800303002980f1030101c1510495404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 678396160 1250 678394910 678394949
    0x30f25030507030b19050123030105040b04020d080724061413020307090f15140c120319050a151a090609030f03031f0e010b19020304080d09 62
    0x4002a0040381e50000041c0021851a100d03481a110080d103c2d8580c01244105d804800e19240030300341c060302e1440d44000c0000601030b8032038120078103007650b1801390f4140f600f0880030070b241006c00d55200750142c2e00314604002500d0b0104243c803980200030130300348044035040744003a0f000c445000354020f200000c000c100c0c1c81b41e5150612044e10a1100d034001c2c40244510000d960503000b6641103125410301000070b07038695001c09600506900709100080c080200010120342c803030804940e00d840340a040c2e26161109842d40e4540c02a80300030280b0750400808110751011044000101400342c60781000300e802c00080131000303401c4e040100003083d00d6641c40070941e64480a041d8000300302d404465403074840300c00280b1242c4d401941501c0d5042c0250f9100d002c8142c428401140f1465240c180d500c507049000d04a5074892044c0d4002142c40043b000050112200003021526000810b0313149012a00203200124550300c556000190035000701620001015006488034040c4c420b01203a4200d071001c030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 678397410 1250 678396160 678396223
    0x20907030207171614030c010609021e120f0403050d05010303020c121b130b10051c0b280f0f080f0d050a0c0510020a0c05010c1e0e0d02030f 62
    0x116122141164810131203d0005003240c4080c1d01000d10840650742041082c0300003508484880d40042d45403230300003c2503141b15940c058104d841803240d9103d181040142e07030400343c41e100014210b803242190348001c102414010740995041e03587e101800e20842da100d2800a449650261010b409000440504400e0f41408120140071b00c00700390304503c4038800b040c1003120042c01d2030000e00b04c0e556180f00940454940385101e041c00c0c811600c4045d9148019032407a0150211803100c181400e180c01c4100f1038503540c02454074030040c42c282000031500101c2012080b41c0007594000a11900c68020000301e000b0012800e004480200c0151a22030680c041e4083e202c0390510908030014000f04a240e406c05d00918240703040c540942c0444806200d07000c0c03c901207910482e5481c0c0850055030109080080901858060501c1ea01d054110582200e480b481210202180c1b001440080900c5d5030705511031020140076641c000b03089070f0210125107880c58a400e54901d02a4180031290061a980b040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 678398660 1250 678397410 678397417
    0x90e0702071a090402270102060f073203100801090503030a020f1b010b0f0132040f090b1201090302060604181a270309190e070e0f010c030801090e030702090703020717 74
    0x2107400d083d40303050342c55410072105c0c0b40cc490728103000076400c5411480d801d80908150488503218190540d43e17403d0108030900083e03043c1e800429660304000e0000000b8070048207480c1c0010b5000409030b2103075000c0d0505c490b9070203221500f1010500311b0701981c4101005400594082406a80036081024440c004480e8003101084040714007424281d50b050644810b50042c1c2820100b480b0181042c1c0c6611000d9544803e561101c046c042c0ca0304030400d86480c180e2210411003a05a000b0001c1040c0c83d81c0c003a440d0180140078502c02c3c0d42d00d100703046100d2400e50014080e95407200181080c50654102c0b48010b4800751460503102445c400c1a00300400e5020910496024000041d4100440441001a108041e5410301d102d080c3e806c07000036812191100960085191b0703103403001c09100c14010701400b6140c203140d50b41007040c030610310404a90441c00450545222044c080352450302003ca16240d481031510094000c0081000c1018956042d40506252032140c280ca480100c03a900d40d011700784c003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 678399910 1250 678398660 678398671
    0x20711210a02130b0d1b060c03020c1e04020f180f03060a0c0903020d050a050114010521071a03040b0105030d0e060903070b0408010c090e0702071a09040227010206 72
    0x6001c800c141c070240c80c1880c40c0d035542c801079a0000c20f42102c4800403a400000c040d02c125010316a40c4141030303101d81000c030300f20054095444d01094982c001d490003550340b10040c0310507010303203c01030180c030180c2812280c1d02d02c40c15000c0c20039562000f40c03080108003036104961086064030000c5039070086181c00701408c2501540140184110348800003400700900403210a20140081041d00000585035041c0807108540220040e00310700359035040c603500b92040441c0c6e40003603000c03000042c4030a82d581001c00e040801c040c103c1c00c0c3c947c0c8881201d41d00c0d000441d0483c1040e80b040c2e41d2891104651f540040d84128441c0500a405903070754020b00d07a44920079a481c4010440d06101048a402c0c080080c1402d074200904484815a88816034011a486a086000b281c2d4494500cc036203581c01400400051420141d12500391400000003034a4441c1400f80050303000007400803044840d440350a441d1440002801195074000e2190400c0340417504906e410036400f0001c1c5074110ac0e42c00032a1891144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 678401160 1250 678399910 678399913
    0x40c050c010b10083705190c09060c0c17010c0f0801030f030503091e0f0d0e030a0201030905070b0313110103140432060108160b0415030603050102071121 68
    0x5071105c1c072591301c3d084c00c20003100c00e22046603640d21100d1896041c407a40c901c0c403000c40005031070418044484400220f11040c100240c100900303000c420740c4c400681c501301e0340e0714035010b02880311500e04504d0110301035100050f0b2101c0103c0c0c40400071019400f0fa003001036103449490f00d00035803c4041d60802c0e001d200241040491107181c0c40030a010388001c5a00825200c290380c1000350702c516040d0060701030840b0381e505502034400b80c4441c11080011480b00c1d00b0604103141e00d40e407480c0000f80c3d210b0302c01794003c0c10140c0390854801007040400c0a070002d42646c949031134880c580050032103829040c2d6042603c131013100705c6406a065019104900e0b450b00c02c041158001c3e503d9842da1800d490f0a00c2580b5030300c084a6054070517407103150a9418083c103071071001c1d107810751515541c4c516247d2500780300354a01c4072480003000426407100403142116880107880b412217803038980c160002c1005501c00780c150b500008020081080300049418078680c202d68500003a0310000341a80304400038403551046 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 678402410 1250 678401160 678401177
    0xc0905030708120f0f0309100e150411040902090c030a060b0405100f180902040e0106020102040e0f040507030f050f06160c060e0c041103010f0605070305180f040c050c010b10 77
    0x509840b800105aa900122642e5141c56482c4240220304d50040b00c3c1a000c640010401c84039923030142c0201c0c41c9240748080100710034075118400128110000c9c200400d01100152030500c0b0f901d441e046030100f41e800034200e41646c500050103502c10b9004581c85000b00e0318024011a1600f030001c203032800d82e0005080c00e09120314469094492807000060300b001c0c804082001841d0203001c40310f50000d41032075400942c42c0d0303103042c800085801c0103030000c0c425a4010321091105629205c00d59600040c804420b0809803543e051207800e00900350806800080301c451f00400b030000010310507120b03610070000c80c0d042d030303451f107218840340e48000007810001414066200c01055640d008040c40c22100303c280c40111154200080840e1155440143c3c01040803004100fa0070443c5d03207407001000303d42441454051142e030010310622494010400011140b215020a9110703c50b0081503054040c0c01041080c030035000190a43d000000310508075800d00300038000a040c80000100403480c1510303032801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 678403660 1250 678402410 678402433
    0xf1801090f120203070e070905130c020604030503221a0708010501021f06170a0215040506041203050d1a040e0a020a09021c0603120905011b03030c11100c0905030708 73
    0xb054a511002d81e89407244100202c3e41c400d00c0b0000718011441d0751a0754102c6441e00c0c040c001d01c2141c14a5040d4880e141c1028110219004207015503c0359240c0b0f001a43c9607a0a07040d00c00c000101913000307403160f40e42d06280c020003401c280c200125009031406001c0382c3d03841706801c49225100b400b483d030058100c004185801c510140141c08108440f0002080c1c036600c81c0501541042c101814142d80d84c0000f1500095041c03010800614014a800c20780c0b4190034640842ca061040e4416001c81084240801d010315106005031100344d10848420702521490301c0c000c100041c0c0104015100301c1c507040d40782d03c20040025408002c9a03001d07090800c410700d0401814000e400503120020307600000c40c5a000c0c021490f01c41e66000d1841114801406880c5980c0141100c00d82d41201e414000105202440210004c001c104000c1d81890b01041c180c0c5500c00864004a00d00031022051007548608081d448403904520342112003030392403140d402d960b6010166108843e210710103451300079988080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 678404910 1250 678403660 678403679
    0x7020a0306050c2107090b16080f0f0d090b09010902010c14070b0403030507030201050703060b090f031e03040302100203030c041403120c060708070e06090402090a03080f1801090f 79
    0x183c0c00016241d42d03070b0401e0001c110100e444d43d42c1c1002d41340c810040b00c04124406030080810700240c240c6501340c81c14180d60704403080c040f0651031005454102c003c030701080b44250010850348032001508070141c4400d482c0144001130b107040c00003191794041410002c5d00040d0144528014190140e50310682c600964035058190020004880b59034001c40d0000304454540d40c0050000714401d81c2e6595903038a4500b402800c44070007402200405007007000c100003c0b0160001e079003040c0d0b001c84d0011021500740001a00c0d03d08051446030348007078100303c114500c00001c0050002c5134003d035120704041d605e0a80482e2603100844141c4200c0034140000d02240035528003d45600e103010b42151051540070030442c01300d80250b42e9901040d0b105c2e00c10000300580c858401e5030880c0944c242000c9081c540341c0042c5c400e0041141050140e5404501141e0555426807400c000356080890950f860340e42d981411030951020140e07803100c4401844031030565102d65100c000301c030000040d00025074104581c1c5c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 678406160 1250 678404910 678404921
    0x61b0904020f04030f0b161e090801150602010608010b1c0507091107021e0a0b0903010b04150312090e070509120f01061401020a0b160212030708010f050607020a0306 73
    0x58000781d0910040848407405030091010354042c0d460190850380c10316100c00c0295008061030034005900b408409015080004a004d4002000c28241a1039907200b04848400180c0d007c000150300701841000c201e40045440400e6421301da0082c40f40585031030542d0309941c0b40e6003450740c100203a00102c8943d400001c4c6000c001600c1a4240c500f0366a070391a0480680e40f100101702c0e82d004000822000b10316214580103880e6402401920354035107000300080303044003148652944954001144407266030203601c26821890014010401190741990b10844070300b00740800c54400d0002040398a000c0c1c064040300341200e03840c2c403803142c181e51200c00c110b0340b07900314030368880c2c00024920340d003c3c1d00101802010000f90685c2e00020b400c51518605181c010614030301c0340e040d9009460000c0100c0c035000c1c1c0e016400f030505840a40c081d440b001080785032240900031030410718400f1080c440f00551106509040344c5140504103002901d601c01c1200601c503030726000303500080220f410800146143c015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 678407410 1250 678406160 678406177
    0x31e1005030124031e05010f1505100c061808160605061e0609040b040e01050a11070201020a02090405070305030a050c0c01090509040b1803070f140d09122306040201020d02061b 78
    0x1400c40c0d00d12195a081d00707492049041c0c0ca00a80c481c040242041c2701400a04010002203540c002481c06040020b007000004450103043e554540c080e10903c8041c8080c1c840c646540511185e5844040f402e01008100014400301c50042c1000c000c50124540b0181c83c03074960701242001d480f0030540c90304119690b4820342101d81c100c0c0d00c4018050036a41c031840f9245150201074008603071480c0040d208400c90b162a03c00d0081c11400707200d80703c0540d0380040d0078a00780d54151114200f50300e170390501c00c0ca01455580000c0c00e40c4400540745a901b54804c01500200c01a00110b60b003080945005492400c4507000305908501450005404101d1111026410400d2145c00c14006003020700d2582c21640000c0081d11044000c8020034100041d40d40c0d02e41500c44148050310345000003000c014151100ca00c00d82039440340200d07a55052010481140480c81c3d81d0100782d0800e007610044d901c4c0c0390130301110705901500079144941c50700c6002055052080c21001e26090001d40c4005000000f504035082 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 678408660 1250 678407410 678407453
    0x100608040c180b0102010b030706050f0f090d0f11030601030b07050307030906021b060606070f020112020f1801110f1908040807080a170c06060402031e100503012403 73
    0x300180301150104401d00c1c0c90380c442c5000c60310380e010400281c00c0d1426054101d010760300c502c5040005691240079605821024140d80f507a40c025052007108500411401c0396200c809800d129040110703905460182500c107000c546054032070a41015120102440064881105800010710b0103103d10015035001c482c5080024044203142c5500b000c90300011003a5034a04000c0342400d00c3c800e81007100a40c08502201c1d0300c0c1c88c20090380d40384100110b01c0c1030000e05226031202c0405000e80c80390180c8854000c240005504d60402070b03440074070002d4290703415000c11080e510001500c1f1001c5031004948680a0050040300300d041c00c0204000d41481d0151100c110a00021807040e9050201c44001c1c055440282000011420100703180d00e40d100042075980001c20503403044a40c013007a0b5942c030000444005840790750780e108464100703014000c1040d01c0102c0c802005405140c01d0b103030405440c0e080c4c00030070028590034100300703040c4400000c002030044d1a0500700001407414000c10281d006011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 678409910 1250 678408660 678408683
    0x903020f100c170c0f0102040b1633060902090a1419080102041e0f050d0206091f080a0b090f0c0f0a030902011403010b03242d01030510060804 63
    0x840300c4800540092203583c940c5000940030503201001c000724800d4108181c005c42c0741134a0034203001e071148211403640d02d12843c107803400c0007840f121480450000b401425030030003103130000200c4003000d18451542e01907207150010108184502d84299140340348080c10b4005954107080321801440d01e0890b44c983c0c00b00fa16140002500d41106101c00208000000940c070b59043c0740b1318041802450302e0010501518810801c41802c0d403843c800f080f1841600e42208400c40d07800407800b94441c1c6018140c201040c040c845910521130306a10141207e04c3c0d880d2000740e120b0a000405503294160300350341c440c1c21200804d02101c0c1f101c2c080b40e00084500c0c08030785400d0202e90000300642025042c1c5c400300b6950b165039819941c0000403041c12103024030040e86998100b88200e4814040582403942e003407260f000e41c0c0ca030701000700040c03040000c0c0208001c0011091800e22201c0c80003c1e0000301011490b0400701c1515400382c041e00e07014a44014a81c022031381040c804490444000b041a554004000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 678411160 1250 678409910 678409913
    0x1701020424081801180b0603010501150909180c030305090f1c030503090109060501120c0b0421030e090a0f18080403030f092123120d150609080d0903020f100c 70
    0x30f61701c0c104010b1085054084a107000001c060171160142c2c00180212001c0705040d0045900c0070b00c81c41070f00c00013540060486561614810550180309008003101c4203910b002c001d05801c0341c060007490000310b50091078010000144030380241c80e6400300d1185411a220040001e014902440d40504100300000d0311150f00e03245c14041d61000ea00a0380645d00b100034070001c0c000e65800c2140601200410185810310b030000782c08000c1a032010725610701d212141c42c0c0b010188901c020259928000b400300000d410040c00c500001c0c240f08402e000b26034582152442e0b0840000004400160031a030141d0420b03142d601c0540f20b03034910050303480400102c00401701d44440b0744030160030705c23042c04013100c0ba0064542c5441e041505d41800050300e0380d8038951804005020002f0307144a410a0a0302c025110394008040e00080d140c100c0030030b00700e44a008000305405d0fa000209004859490007141c40324803540e00155440d2800b408042d41016400d41c62520601300300c1c02000a100350b518201110141d03a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 678412410 1250 678411160 678411191
    0x605060f1e0d0507120e2d010f1a030a0c1e092313170c01110c030a0e09010e13110402190207090c08011e1701020424081801 55
    0x3010700c14052650f41ca084c455001c0d4002075070408410b0001d41004a0078042c0116651001e150401283ca400114811011148010801d60154580b403009010034180c20340707400701900300720340d2201143d00f0f03c04104500345000030b038103001141c100b1124a045820240c240c00122408030254030b0310403607100f00040d03070519480f4003806605a4481c1510b0a0000180081c4505000c0c00e06450408001000400300701c034030441d0640c03034020105544d540d84000e42c00c1405406044204c01100ca00442c61240d4840c000c03000704480100c584e01c1c0c200300d92030201040702c032800c05e00400b142d00021000040001d144551640840e42c0211124007080400c00c0c005403d9a008a140301c68004003040b00007003a030b804002d900d0140001460a2014621080703000345806014858002400c004021106010300302107442c0c0050b00744401c8029250400b03800b8903002c2d50140c4a0700d000a203500300b48031424001504c92017002d09480d070b102e20168492001031881151014000c8260303559548640404030203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 678413660 1250 678412410 678412417
    0x5040f03110109141f2a0c0801090510020d090b010801090212060c0901120b04050106080f0702031305040c11190b06040513080304050111041212030605060f1e 70
    0x410500500a940c510340010059440c2c0d902031400311118420340342150f81d50381c2540010206000b605d003446a90540201c0d41280a120701ca035030206030452a11400c108020402c00b018003c201e5031a5041d0703a90b90441c00c131010b0b417002400c550850842a4002611a0010840100100404108560f981d101e0080981d001c0c0c0c40507846a540352082c400f1820314800b429070003943c05000c0c01007403070088450007aa00c65207641da03041040031090310b024490b195212602011014200700326542c1c50b0b03c0c01900a0a0549411082c0c015400001e000b6a02c00022100501c16130b101c40100701d071030b0400740409400c40340501c1e020700401c07070362610211500b004220b04100500000c0440804241045440860003420713960003a81440100802c3c4012184070f114840c0d441510603940b42d8079801d01d14010700c0b00131081048007000140009070686c051a41100490003400398841c14544840c064040b0741c09803060a400c6403041c0400790f0209451000342000d50350a044008180200034498a2103a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 678414910 1250 678413660 678413663
    0x26191a040f06060905160215070c0c150801080f0d0c030e010c0615140405060f010e031603060504020a060305090703060f02130b04060206130c0b1303020d0b0a050c070201170705040f03 81
    0x99070703041045000300306d41803d44290355444c00030344203050b102441113050780c40003071200e030600c02c080030030508004d40284042c0040035940f80e42040f811403418014040c100a108950052145405c50380580b040451103040c0520703181c44010072411070341ea041d00e042d0080041d15062203052000c1070f0102e0903501400022901d01180842d0882c24032160740c020107548117289020300d140504006841c4c6968100d9040041c090030031182d0f140d0302c2400a80340c088800280301c500d060074100001000459000140518030883e01c40384590b031180ea0890032030b0022203010060ba40801d10402c08640356901c4080990910f0318054502104481e01c05455034080d4001060080300003810445a641480305542000a0903203000d40380c012034031858583c517800e015100310058000381c0c01141094030301d41b00005540c0079200081042c01d46c10300f100c0248045545079603d030708101c0003650302201e81c021500c0442e8161648008440800714208100d4001003860060060400012810211468202d0001d6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 678416160 1250 678414910 678414929
    0x3070c030e13090203060c0a050d020c0307050a03030f27020409030e15071214040b22090e010e06010510031d1501090b100c02130626191a040f0606 65
    0x1440c0c4107161626000138180c1511040502c2303135400e05a445000c403211680c0011015071a641c10025003420b6200c2d101004100f48a10301d000d50801d90190004c116015600d03408000c254007038040c00688200c030003016040111002c00100041c50594440e20030a402440c01412256583d0013080308890110120a030510002c1200340821841e03049034903d8506a213400c14408422032f03100c08150003140a10281920302041c150f102c0d1145100405212100012200c1030703c1d690010300d0010200c2103240d010550070410300421482000032114100c68016242ea40c0c007110f000c00c100c0081007140c000749800c0c012440c0c5140311100801ca800e403044c4040540c103040d0b5141c542e81400b100c14400b42c042c01142500c41c5010000d410641d42c084613034045e80c900040c4070210344001c0080049170440540301e1800b0300010411001084076503540c41d00d500407101300640704100650003203c070250007080310720440403240640622480c1660001e1003440d80c101d08500e42d580d084d0a40e616a002245a07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 678417266 1106 678416160 678416171
    0x3090f0a1a160b0a0603031d01210b0a0e191803050309010b09160f0503010b0409020703091502010c0806010f1d060405040e0a030e060f03070c030e13 66
    0x201070b444040c0c00d03204e180603d1801c0050815000580009440c0c0e40b5480e400109501c1c01c440c00c150584607003001403003200001c2804051601c03000900c90b20b591501e03605844845c4054045c12822008003d1441c1048820401c40e9040104081040c20404c0001080003c00c10300880e80d50107291450ba296a000e420307034050803004008a0b00600002c1c20000703004001c003e032111840301a5100981d085c2c269400f150140401c2c010002c1018041108101044440c1d0042c60600c1c40780c1804003100b0b40d03800e00300c180451800445800b43c0d44480c2200e41e00340c0c1c89060319074040c1090031f00c041c100100c0103000b005224075806510580b191300b000d54500da030700c00d0141c800a200007041400240320422006454200c2044100c0100f00015041160380c5002804d9a906032a60618242582d40c0d05c1e00442d0001c107611026014044080601e0b41c0d07540700c050001000840540c00400e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 678237410 678417266 := by
  have h0 := BRFrame.cov_init 678237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 678237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 678237410 ≤ n) (h2 : n < 678417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
