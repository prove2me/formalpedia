-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3172
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:45.443244+00:00
-- url     : https://prove2.me/submissions/580c4840-d87d-4876-8614-826da2694b3c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 570323741 ≤ n < 570503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 570324991 1250 570323741 570323783
    0x1201180e011e11070b04080a14070b15010c0b0f0c09040e06040c060801140907090302031c090b04030803060d020409050d0c0b100b070609030210090c09060b07120804 73
    0x40070096514840c0c6240301e03215004100f641e0300c2c00c5007078a81c09020050200001c000b02003159101c0d030000030858440d010071904039180800800a140c642c07501184a10078003d80d20090ba0054200c0d140500840b0341c00c000644240300c0c07109015100d10300580020380940f82034074060740d21020140704280781030b07003800c005030450b181c2000910710380d441681040100412010190050b260504083c222036240501410300c0c0700c1182c14841c015404034000c140803c1c01850040051a070003015180420340241520b100121010000f40001e8010b400c0065211101310444043d02d81000501d40b13151782d080e00b8000782031200c0800b2a002590340c0c100d1808a4030901a103000302c252a5079180001d0703501c0c280401c00c09400350100c81880f4044104000c00114242101e80c140e51046012407400802c0c14140c0c144086c2500d40da0304d2070304050000c41000b44050801042d03402d1018100031068403080803108e14045c0e03c00040100c907440050343c0100d40074081c0c05900070300c1154112140150100c400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 570326241 1250 570324991 570325001
    0x3090203210403110411030114130603050303070e0103020a020a0602070f020613092306010e150a030207050f060609040803150307090b21060613022a070b1201180e01 73
    0x606907031100420b0a000f00f0015040490101c841105c1c140b0045d070041403a07034007612041c403c880700503c2d1001c1314102d903100e002e010310301c0059402007045074680e2400c0c03e540741c0e401100c24200050800c0380000c440d45c020700c26250309541c03d9000b48031010042c0d0b1040001c2d88103d60039244c08a00f20070b0000141e80b070348024040a0382c1e0040c089415403911400300180c40760040c181086202e02034407581003e06801200d540902c0900e000d55440c2201c2022402150360305c1210f048443c00007031510061030b05600181030461140d000c41e45d0b00b4280c00303042a15051f0584420368000c030280e0224002c03964100c040c1d504101d142505514682e0140d0011340340c4503407580010102501c914a6580615148900c07940c4031048060702100303881e050340303c19204d0328000c201900c0b0b40090516950000c0081d819074462400f2119003413030411900f42029100c0302064020300b600e11a0003070104811381c6001c1503401408103986054080c0c1d0030601112074912202814480b52641d44801d02d400603002d0141c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 570327491 1250 570326241 570326293
    0x9050c091023041104180608062e08070501120608120c15041109010e040201020c010f09030501061d070f1b02040b0603040c032114070f0b04140c04180303090203 71
    0x1440e640d56150031141c0f450851b945442c83c01961501f00204100840810b0380c40e400610145124881d00d90813007184641034002c0b142810002c03074060042282140022800240d940076240c480149005001c184103407031950051034030941101a09000d044c541d00040d018843d07044040c2c0706c00d5100b61140b05500f00044800380e407800e03c3c180e80f400440c100f001065015019004450060780b806400103583c420040300407034100580c50100b040d01b0f47c8035460a01c0a10b0b0701500a008a80c0c0e1130b80340c051800e4220700c080c9007100003180450030440c00b400c003030000024a40c5940b00401d101108003c0301c0c01d500e000c242c0c0c204e9111010311549584120046100c0c40c460f03d400c500c15811401c181c28640d942410801d0003082030403900700281e42200c0c10030b4200306c0400703e00f03a89158500d42600e080d81c407100c00030410103011b820b100400540d18001c100e045103610846089074602e00800c004d68800044483c8516440d00402000c2440fa8202d1200240040c0407a40040c680f64140041400a441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 570328741 1250 570327491 570327521
    0x603040507060306060f023d09150603020d0807020409080a20010203090c060c0f0a0f11010806010c060c1413090509060f0115030905030d09050c09102304 68
    0x802444030702e4042c13043c600a401645480210f503000014065520400355140410450407100552a80c9182c0f100026200c2085a04084000d12022114010300a07000c0112002060807151768580312039032041e0000c9075002062441c04111548503449240d0010310140d070081e49404820010603c110014101210701380c1c0c990714011054814000d191840c00718107140c60b4010800d010401d90700140c0310b142050b048501a0b42c0e130414814080c50110000d101d4030007405140304c668103120322040301c0035a00d40203c1000701e50003406001101c0b03c250480d48640401c1c0340803500400304905620031100003200d42003041c03210350000d40c3c55041d60001281c10040d44080201400388005a00032075410030f050340028401410311806072004500c05001d08110804882c0c50320501500c00d80140c00c1194103c025a0756a140e00d001702c402a085226064030184103a14040448d402c3c080c400d03e2088410041d150005421300642012003002c510174840f0b0358042c801034180710340e0b652003542031070078540d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 570329991 1250 570328741 570328753
    0x180e011403070b03060411091503060109080609070306050705130b0903010f11030106030213090203101a1801030b150c010e0705030d020705062b061a0708041e0506030405 75
    0x3140d400e61648140c56030082c0c02c0500104001d05403c0d095a0b00311381c0c2101d02040c2401d2070703080c1c14510700030960910391101030009006110a0b076000258041e090a80c0c4079082c072503c1c0d25286039940b00507a000f150035482110204040791a0768401d03a000855441c1444c40c044200c00c2c60100000030f600080e03c2c901c40094810603070705d82442408001d0460000501210345130340301403040c5000501c00d4a09054000500d5400c200c1d06c5102c0c070028000c00d2000719224100305401c465003560500071240d526120b036591040d411050401c0c2e4580c140c40c18400e1051a1150004402900352a0001c41d0001000040c50301c078150904041c00304070301140d000294401d14052002e241a41c0d50384698082d07000440024a070540c08140f03001940c81c181d070041c2d500c00104205d020314010040d0402c0094819a00e10f4000c81b54503080001241e2085100d0700c0c510080d203c06015034800c1100c001d03e0990100001c0108858210380107070344001104c405c18440340d455000c1380d01c40d030080340c0c02c8a00760011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 570331241 1250 570329991 570329999
    0x40213090e0703030801050f040e0d0804110109050d110f0301020a030902040506010807020a140313061e0f17040203030d1803090b0406090b1b010c09081b0f0907180e01 74
    0x203101e003411414008004008052940d1005065035030103005080c003c2514003100030581d202c2d608500e135451040d00842c4c07925002c240009000c1c0105a404035503807044284026055031140050300141c071401405203034412650740d11500c1e092610404203400c6611003071000f52680c2e0a1014007840602030324045000141441004102c40c0014115414400e0080600408950004a40001c143d014101003114400e4582d43c600c2c0d802244812128404101c07000305d0881e80c8180f0300301c0c4040a100c403440141103000001e541c0c0c58052011180090b4580d8850b00d10301041803819134000740042d081d00d15040b9040051000c1d520100c80043c4140b20720008082019405200407004103c000755450400e4241a0001c00b081950301c6150001540410a5040c01784c0312246107400e28400802007080c0a90300760f001c1c1c40c0103c14822500d0901840c0c4084004151000c400b460f0064014075019000c46075008000c03547c000a0710950030000003052140d00316031100a680090b142c84104d03041c1e03e40c94 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 570332491 1250 570331241 570331259
    0x7030605281404021207080a0c184203030314090106120f022707030b040204030c0501110a080c1e0307021e1207090204060921030c02060405040213 65
    0xa1070701420301900c1e1182e40007040c10112603070307500168111805002c0030040039443c2e10340038982e0001f044a0042204010411140c200b01e2000c4030302c00102c890040500901000450300d0005441e9842c240480503082d1079100c0080c0d00300c008a544d980c02c068160300940002d50b54042c0e80086002c40d641e0b0701140c1c60460b80b8072400e0345c000e01441c020300420b4141004906242d041800041104906503840802c40d038540c21070714941804482c1c008605d45140c1c120300882482034518001080c5441d4a04a060400303000304c8058030303000102603104c04e240100448076041e01c0e0407081424040c9103000000170340d9081c01480c031101174000429298500e0b038100603030804005502070443e0310801441700142c44030300341f4088040180c1a40f40c0380e1f015800101d40070800210b180e0050b80101040402c00b089180d000e070050300d900d0742d20212901d031118041907072109882c0c440b164041e91191800c0c0000d2240c1d00c0031107081d00c094400c504003507642d030100d020790300302148003424108040410721202d5a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 570333741 1250 570332491 570332551
    0xa0b1807290c0a020603180a060906060510141e040612110301031e0809150304170309060a2007030806100302090a0524071a0709031502030907030605 66
    0x4081c40c0894505407400e501c4a54440201c14024000c01000c400120b00c0d960000060501003c50810b50f801402e1514041d4001c20030803104440180c40c3c19008101c90401104045482d040c039103a11b031400303000b1001c00b07a05412108040c0b90403141319134590025002c0304081d00082c0180d4880b05013800c106c11012090f5103010700000091241070004002180003d000d44034100721503030241c00e690301c16080010083c4108015107400ca001d031903400700229030310402544110702680c41043e40c0745444074240740d244001d84070281585c1c40280418800320a035400a0301816103681100c030081e9103802d2010031741c0c20211007500401d40d204200005420201c0d2882850300c0c9926045282c03410100014980ca0032500445009d0441c8080354640c2c050442200b82c04ae40f100d07000b080d01d40409160a0a1030b16100d400481c20036071410200c0d4070180944a007000f030320792200540f8015000311415000941000b081401948a2441c000020419512030f450003502d0300c0701e41d403240c0da004601001d9005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 570334991 1250 570333741 570333809
    0x110913020919030b07050f0703050a020109060203010f0311030a02060a0f0306030203101d1f02180405090109050f01230601022a0f0607050a0605040f06020415080a020c0a0b1807 78
    0x21001f000081b40390314948080b500c41d035515040c15610340300d44040890042c401c890004150358070000001c2402480400c0203400ca0384500709010200c000c64081c1a00e0380741c140300080d0003603400d012003191b03280906101501d40e019894000f50300b0307603641c000030721702410790100c0158150707207242000c0d440140810212072543c001e001401d04150070122840a40340301c600c8407a0380c507804121680781e81d182408001250b50010024081414100351950003402c003000111440d1058914a0140ba0011f004954403410a841ca140da82c1c16404540216484010b2410341180205c218481805c03600004c2004800d440341c2511300484a60014040e50320251145a81f0480c070a100d00360000310300240100d880340d031104000c1800d45841c070f03050104801c07002000b04020b0000c140030a02d40410408545075000d1075840c0c003c0d42e03c8004a11089101e03071804007407150021400d136400700d04c1c022074183d000b0895000c0140c105800c046e05030b00b807002d01c0e007081403030b005003251031710143d190010004280 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 570336241 1250 570334991 570334997
    0x605010b310308030a0209041514150d0903030f0207030201150807080a1b0518060f0409020306060f0f1201150e0702030a03090503120f04060609110913020919030b07 73
    0x15500441c032010074142988030042019000200183d1a914250151160408080c000303002d1006001e4080c40381d1040390140307484001c2d0400050743c0b207250190101251340ca42c901d41c0c0b0300d840481003200c80070348000031083d004d16481d1143c1d13a0042c0d0a0b48001e081503402540000b50707042851401151004269000030503d0780030304424080c5141c0401e00025031079006000702c4104407840741000c8581c2c00341c0e00440e800f68407403892410041d0045044d500c07031030b0111080c0e08040348142c1004103c4c0c4c0404c1010750035a1002000030000e0600400000492000820b03c0050700c5800002405c01802103800e0440f40c2d4442c4181601d600120903000082c0c800b4085452661a00c520300035580e0240c406d50350101038481c05c611040c04020b008079180c44403420822086803912804d12240450241c50848101d81780c03d400243c90318152098103010001c98040318a490361003010840702507991211061800c1c0e003007100c50140e564007440d401071151003d140c60011403440c00c010b0b601d0342d8001c0080080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 570337491 1250 570336241 570336307
    0x2010302210f010b030c0a231605010e2806200a02010501080118030815040204030b010825052701030507080d0201060e0c03091e010f0b0409230a0605010b 68
    0x8084000c4c42901c401f40d10320f14010341101d00546c010721107680041076103492020001844420001c0100007054000d004400038031040b910040c600d561030600003444440c5c400448800d10410a000e04203210090040030f004c510300b10420341c1280308440c0ca00102c080d0541c0010103925241d02805440e00426034100208030060745158103c80318488108002c04110800c0c000561748071405001088101000d04219282c50700d07403900200c9004280940c0843d403266403c10300c1400d0200421881000240d014648140e28100902c2840c1c105940000107500300000076510a00c1c1c1001c1c114000c0d40508000c100451818810700c0c20200c80805c04021039050072002e200d240d5020038a29001503034500032541e07aa45030b100355030500300c03c02c4c951202d48420704281010004150050b200401c0c000800300400c446080400c400c50f204144010188200380c180d01d210090703e2001441c0060482041d580c100096030b0742d0300d0403141e00b604411002800801e0960103041e4143c4030458060000c501402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 570338741 1250 570337491 570337501
    0xb0306161218060507050c06130605010e04020a03080c10020d0603170c030a081e09011505220c02160810050a0b090a0c02070f032319060902010302210f010b03 70
    0x21160101d0035000e0020f07600d8401040b03d040c481c0c004c0700d040f0203800c0252901420400a80c000142d100d200030760b40c0e40d043c88004160703030b200e055015006d507900504000b5811314603610300040380c001e5020034a181c018500030808001c80c1c0e0004003e2200701d000c00090807400c520341032059005440c2000c2403103a05200522020310700008441d0b1000490801c20b603555118a6400b40003400100703510540c4d0000000e000c07070b0f0401500400301d6035141c002d01c6506903440343c062050800b15240d00c21085500c10744201040d4215900c800d17200b0402c0d10640328491595540d4001c0d9038a00d80c080140ba90064880c100150300d28890706400084201c0107210f80d010f5035001541103039020300800c0e03481d540c41c40c0e036403240c03402000b8400042400c1c1c121140259a0b074200003080c0c0211800e6800240881101042c40640c0880c901c0c4034603484880620021010b62150402010b4038041281410381c02c222003890701c1c9103440400c0300b090310220030040a24080b52400303443e20040e448543c5100091003440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 570339991 1250 570338741 570338771
    0x714030901091406070f06050402090714090405090f0d02061501031a040b0109030b09010b12070303210906020d0c0f0305070e0d0812010620120f0c010b03061612 71
    0x4400c071210f00a034044401207a000140c054400d141c0001c1c125071130744070048100401c0d50801e034411402203031101718555420030140c85101a0146903504c0300340801c8928050b01c2e19500a80d005400041141d400c8254a2174483c500300c0d00c51b8152001d60300410402000114003c4900f48604003841d00f480040038480c00100f006c045000075071300c40e07a00e4402d815a180d100d24150001503030841c5000140d41840c01c49680280342c00c4c0d00c40b42c0a03100b400c3c0840640b500c0003950310200e030703415980c140700d040700441d41380e4045ea01101260202c540740c0c4c15010100b0f0f0640040d0241c204c841c80300150102600b03501410002c02d030301440c0309240c1004c2c1000f06c400c1e0031100c0101403640c20345210000d10990300d0b00c5802442040000885007220000101e10a9807184d000c4002d224090200c80888105000e40c6a071460b00c00c041c0c110030102000f0140344040114040c0ca83d05101800104201c03001d840041d04110701121752030405000e01c0c002000d029442a4908001d810a000420403e05000004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 570341241 1250 570339991 570340007
    0x3030106050906160311010c080613110c010f05100e040b062107090510080a17070311010c0806010305070513051905090708011404110702131d030714030901 69
    0x49000e2100c007090441c040d8642d8000c0340c000e803140d01040c1c0c07084e0b806840c016028422802840456628000c0011a035030300401c02d01c0d01a10b4010442c080e44030780c0b041d0502c00b030400e813800d14800b0402440f01030b810031030900070504135428800d0041142d1030306419440c180c40060380300251942003070703040c0404601302307071400f6810260a0324544003592180c1c6000c21400c4188003080201e02c961280090100d9069010354019110300c91005291a6140704d1550342d4105220080d00c0c5169a6014241d504044001444038031710030308002011000740003038142111001d10040d0003140100b810844990303898800d6641c01a058280b4a0601040340107a0300312519a0291034001e03180380703000341e400c590082d04900007403a00802a0505150502d8028500359080c469644413031500100b03601140b030207000d101a4540010412810003034190200070181c10305456039020307036a40e034443c95440c010780d40c860043c160f0400f006607030720030b600c1c60b00c448001c04004072007129070002c1c0143c45260303074880c081d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 570342491 1250 570341241 570341249
    0x90c030b060708030a0903140403081b0304150302181203031b040609050f0d06020a23070f230d0509030c04060f06140909070e1008010b03161707080402031b0102030301 74
    0x10010f0700e84c031b20f46001d0344d2184004848015031000400d00004004e8810018242c08030440e5190b4020300103803a220340c1e03e005600500c0007060349000a040300900c00d902414184c00c10071344c2c8001c81854103002c981c450316100c01c1d41a0b150800010400042080c640c05070601c10f0a0703000901d00341c0751450080c44d4200c540a503074810303070703004121900540d500000d800c05039801200c00c55641044010151000303c041990b601903030252084520301d600b800040d2020150803007112100000345940b0007450b81900c0c084070f8060750301721070002070340344080221110740d64540c1c84280d0740d040400f081515096a8000d941d1042d41449014499545510503070000c444441c28a0b02941a2250403203607035010701c101717040e0410081000c11210f20703804040051004c1050b11080301c03040c4c10b100d0448041c18240074005103c801000802d0b5105400c6074002c1b10207a4500c2c6c60f1211041d0050745003000c1c1c00a450b2840007800c075000344000d41c40d0170310805c100c0101640c10002c0803244c10001035224001441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 570343741 1250 570342491 570342511
    0x21c0803191103181029041b051c0915020705071505131d0115030b060708030105030706020607140a0918050f0a02040b1e1201090c030b06070803 64
    0x440002414426003000120b00240d1407402d03100e203401031a02c005041c0c0d0b00e0350000c0740e00c55669000a840401c4c0b040c82c14600c3c0515a1244008000034a4600c404100980c0364020740d907890440030710340d4444008103028010350b40b0507589030821026075080c40a25820006c80904d0040d10000180d03407901c40d960040c80032800580c403018181482810b245080d03015144a0f042240082a086d502800034100f4000d00300004c0e04d2030380c560204003004502045000e280310080b2005101000c101c100c0130341042000c5c0b901162031108140458401e4200c08411103001e840400180020303d030600c40301c0d028090900c0146040e10341070310020a4000603103194121180c00050600d0340f58456500c8801074041c5840c3e0a880e500403c103500001c120440385440c0202110b00401ea101074140222822103c102e00c6050800000c00e07a4280703217030722011755810400b6040103e40440c4000d030007503034000c02011750002150340c2c0341c0402500342e540c5048c1c05d504c81c4170204050000642540c06881d0080a900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 570344991 1250 570343741 570343771
    0x91b19090f090206030901050403020d0318030c0503040902040f180b01050d150f03120305010807270b0a0617010b0301300203010f060503010605030d0206010611030d0f0207021c0803 80
    0x44030180105800b4030b01a401035800070800c01c610350150017443c050f0784a41d0132141c580307801c0c442c21821216070050b038411080c850022030011a119815102a003402001604d1505a80785444002ca900a0f07020324200e41008504110343c08004090301c80707041ea201d4060241f20450000200107105480c00c01c400035640c0c01c0f900000103007614407200944281e40c0c01c008441d40340c0c14248040c089201150300044d05040000c1204c0c035003c100d80c011645017504000c0c403070412844981111295040e101441c0b555104002c40c107075030b881c0300302c0c1c028445030701d0366042c0040441054460010582102030300100c200010410742c401c805030a40079500c0c09030302c85019200320791010740c40c20800001a60641c01e0061030700c4582c806601080499000300c00801034140d60340185915030702040380030400342c0c10107001002450b01136207001c0048a081d1007500d107004480140002180c000303100c140c540d10750108a9a0440c10200c40c01040c0c00380000111111040c10f941d0090284001424140003113544 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 570346241 1250 570344991 570345011
    0x1b0b040e0a060806040308010320030705040207050307050d0f021203090a0809010203071709121b040903020f0303070305070e011e030e0c041404110d0506150f09091b1909 75
    0x2030303440b41d8007400140d802d4502c4c3d41094100148681000e00040d00d0001035140400d80614141c03a41c9049c40a01502401c181850101008020340003000190f500c0d00080040c000040c0c003e01050300068a640c075101d40170310384940001d20f8290307129000341100c042001408011747e80020b400301c5c1194000100b070760707900d980030040f800c5029018000380210101d4070035024843c09003000d030074001c8040d00d04022010000c02c003903941c1c0305203c0c06444000001240f4007410308194000c400505c0c085d00442d14061100444580345500c103c550b600001d40e503a003400380440d1300a806003190f40007441c00d505540710008813540703100358214185050560750440a00c5100c1b0a101c64100d2440090040294011515a4000c1e07031500b01c2c0c04884000701048091945d1a011280c100d0712600071707001746015130b55042d1103a1191440403140ea4481482c20070b00c9160350790851a40d20810342400034201c4441a51048282c1c1581c13410014410490901e1400c030984c090010b20040f01c900820100b030700034034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 570347491 1250 570346241 570346261
    0x80706061703030411063a0b010906170a0204260c012d09080d0e0a080d0c1101020a0605130506060f0315060609060c15010f050f091810091b0b040e 65
    0x306410401d12101030712903c0540e106a60200b4403a5025603400344107544020004580700b0aca42d0081d0300129031880c002c0d45180000e180d4080d4007001900c0d00510701174031000c00b801440780308076049401c8001c468141f01c0301001440044070112081c20a030031880c40019a102e50b008000f02e440c18803081c0036031076510f200e106540c030100401049040d508411180440185140c882d00720450040580d00000550244002511038010400307036166020300c0d99564038003544c0d1800350b0308181107114030381078400814414484e241c001c0c2421016414071210901d4818204880102454070a0164800c0d9400301e40b0003003a203a404603a9480310400a5030f501d00000c42c140503000c10650400d034003140c90441c030900010120042441160031a0050f1b90b501c0482a80d1015800323029001100a202e6a02d02d0401c2c880046e04001d00d03c001c0e27602c030b05464190314079044221001d09241b90321840983c0500c0080004100300321801101c00014908210310b4000c284914421407000c01440e00c00155103a20b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 570348741 1250 570347491 570347527
    0x91106070501060e15010816021207080c061302030d0f080604020d060e0a050106090b07170702180c0a260f06060d0f0b090105030109020d0303020a0c08070606170303041106 76
    0x7040d40c86082e400d08010750201c1d100308174403100c5804251980c02103181d0b60421010f0012a41290f03005000d8422a50503201c0241c0180d54115030000050011a2700c2c401c09004041c400c50b01e894468210706114010503103003c1d0440000002c0c0892a40c24140940c0e0056900d0741c026815140035a0303e07142184a24010107241e800b1042114101c01441003118440e01301604a5940b80d55098509403548401d10b4175105a680041c041c0e800c4d140800c41d140070800c007500d01c5e075000038100c182c0700780c0145021103811300031104201e5008000910002058121764032005200030f00c420100c840590482c502c1c54000043c2c03007001e48940e50030016038076a88210884141c04c513010814004644c0202d0000041d03c031542c2054170520300200042000c1c10148a02590190001c0801016180e1030f00d042d0001d520201004c0c04002e0100501000f050380c0d400200400e620a4000080c40c0d840c5c11040d9039003e1810881d104150000c1040c480424854811081c400d0070448160356500000014040a82 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 570349991 1250 570348741 570348749
    0x7030b09190503180a12020d170c07170706082406070c06140903060411010e12060423071401120e0f0c03060c04090f02040b22080109110607050106 65
    0x100041d2101020818040050007038181c20b030322410701400d030030410171454045a001c4c5800880203a0030500151400707038214401180103c40385c003007485001d2810f5020740c1c0200c003078812035440781004001e0016203110f1307080c011850402500405043c000020880300001d0072040141500d01c1a810204042524182c00d024008100b184d44990341e1410200b681e0491241001086c00c0d10418440940100c4c102e074031061000340500120750b1940c0c1c6082d00d2950440a0504000c4180c01e003842030b4841160102c1289040e00c014081490035203006c1c030516046e80700c0d5031400321440f002b1503011b040028010003912003e081c0c200b42940c480004030350000040744500e4a4904181c000114990302142c032050000c840c4040c5c6941c05008810f155561b9003e4410368a40c0b0340c204010040f14406030b00a4a24614103000035152994036403044035960000000d80448140145801025000780481d500050a0900082c41184c0709515004040b6480c815064003840c0c0004a500400800f944020043c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 570351241 1250 570349991 570350023
    0x1b11120403030804060b100e010c03090503071214010209030d050f0d0213140d0221030c010603080a1d0105070b13020301050405100b01030b0306071b060c0806040f02070507030b09 79
    0x1981d52810001d0070050151001c0e10741a02d416080b06403800c0c519101e2460110580b9219039a410f000011182100042c1c0b0680400051003008501d554003402804000c140d681701e400591a1941003510030b02c4001d9800c4c90a07071b1300c10007402150340c8021030044c07210009420b000e52187d4408003000c1d100d1003420b4404041910001d60685101c00c11a40202691a000765072041c00340750034140080380c0c003e501d0180d40411941500d420941c9503910f000e581c420301000b030741d09083d45045401c2c02d445054000f00c48412001c07541c950b07900e901c520b148084140344103540c085a090f81001074868881d406000d008003541800155240403080c4040712080e601070001c10140c5401d0070010344a40704c00c0802c0c40c54a040030300074003156109008420031160000c0150186485640d4180c55841200101e1520f62502c940e480e008210039108131400c4a520f03482e810803a261400c200000c03602519010b0714030303510600c0040085003001584006903503120406104030349401210510780070540022901c0307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 570352491 1250 570351241 570351247
    0x6030b1303092103090b0702150d0204170307050c0a06140d02090607030201060602010b01030e1009050111120609060409030509040e0f03040f14030708100209060702121f1b1112 78
    0x483e0350050f0240100b0700a0380c0d404020f585070f6102101a204881c03020303510124500c001280c66150000514225000d00d4005180607a0f4661400d848009041050b54503000865424184030050048070046c10341150450740040c20050083c2220041d1840c4040d00040450345001c11122507048801d10701006004135220700582c900240038200c07a000b02c03030040d42000040c1c3c0f41c0754082c0c0190000130a006000d41040000c0320940e000802162406692540d03c03566030741c00500d007074802844d12882a1958401d00c0ca072240034091045030180416008914040f96607000c03030390103019a10030081c1104d0201d028864415024508600c18980817014000010700242e83c151642c1c1da4000c070b5255890500b41c2c450107408241d11140548120542600403d0028a110342103138010820800010032843c1081700307a401142e5540d2a030710150003141e20403d2506c0c0306040d100e2106c00140752981040c400316000603440c002128401d03003800103002050100284c0100c06004141e58058480c0300152 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 570353741 1250 570352491 570352529
    0x5130f050618010507020d0c0f0b040b1005190e1b040f080c0f1c08130b0301030203010e060403020c01050f0c19030f1d120a02090c1b0106030b130309 66
    0x20310340c10282d4411005000e61003541c41c030310a060096074411016900a0601015030000c10f0b618041212401c958001e01c1c45414400500b414510034040c074002c20083d4024036081d000038650704c03000c0d000309228004010100344110520718424003540d402e0800000c5a80342c0034003003d403041c0c2d407002660023620040790108920308a0391060f81101c080c1d030200c403903000d80c490620030301001c0011455000081c2090501d14010b8a40807000c0ca07078450070015280000c51504402e00034280c0d04184400a00080108150300e03090040c12003058022000c2d107403c1c100b03030750060f65a5030f80086a9040c80b6010415030001d040140c191010301858100340c1d42c9120140a4400401d144144210081107040001c184114400d50320007011120010b001000550200200038001102140b81c44807807190949103030060b1074018035207005922120707409460302088001c071521f00340145c01030750003613260110030004103002d100c08130f420024140d00d191a11000d070031308580f070542a42100c0d07110700080c07000761 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 570354991 1250 570353741 570353743
    0x130207050a081815070b190c020705040b190905090f1009170c071e030f12140c0a111c110102150906070f0201020c01090c0f0b0703050d05130f05 64
    0x4a03c070045120341549100c1501080112a01c880c0d0b4108800030a1064200045003020025040030018a420858a612203104405d03543d0f154403490043c2c04c15802000981014003c0d800c1c07100044074a001d0480942090004a8a20b40315802d0404d84500100d200306000780050600100e0820988200680d03015a04001c1c04000a040300d144103181e004842d000e060105032119240e40390042e0036503519050700744e1264025070000703000110785008004001191410072241c098460400706241816460340030300399940b001815010402c08100d020340303c078008601007048a92020701c5181c0c2c1c0e1090000b2590040c0d881040c0170200041c840d8850034030004109116811400740c0c01c42c1c1c0c92000c40c80c5038a000b00c1042d15070800d180d11942c049240a40030312404010885a44001070030800da5040340c60035100e041409440c01d0b4401d850034440c00002040794400b82039010003980c03a005250350010b10a02c5000650701c10030b82d4440120716910000d4401c103c00c0c03500715016080080303240c244a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 570356241 1250 570354991 570354997
    0x11d040213140f010c0b061531050d0201080a0906092307242c010e030105150904110406090b0907030b0f061c05011d07020a0f02130207050a08 63
    0xa0001036009400314142e81c5890f12102d12618010f0703441c06119102c541e01c03c104564040e10f26544103114070303030656454103561b01a06820b0000507261144200114507250038611080c0b0810095861610602c026100d0f0035000c01c07090390a1074191141c0d070b54a0f480800030007142a008009a051107510300500c000b10f0403400405001422801d60b01441500d0542d81d06c0c410b1250a40558000f070880d0301e00c00b240010f5a075520800e0500c0032464100c0c40304407403500d41170406019040b007050506181540d01008181038100c0c20350082000b07052400c0c802c8030010b001c0c416544921001000202041401c2c1c01c0784405083c00b40040c85500c0d118488800034048500303000d4000c0364500d00141c60b00e446070103824090040941030070002012501440126032089620351300600102245201a130664411140202494079440f42e21900c110203951824001410b84001c56100301c001c040450956600c03004126070465150000e182640960343c0640950100a41580140264441800510303401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 570357491 1250 570356241 570356249
    0x708360304090c2309100804020303090a03060c1106091e070e010b030403110c010e04020f040305071517071b1a0f040b09010c080f130506010b0a080c03010b09011d040213 75
    0x110350003490485410013030302400041d02d51011070307007202c2c00b40386008203641504503001034156841c050051000c01e05101c415402165000d40d84d1900c40380c03950780007420524451021000d0412400c01208080d501d00e01154031440d101c81200700c41c3c00607001002141c0081c2000003464200f507a40d1076595840c1c0d001190250042a516811801c4882000c901d410341d85070161941441c3c0a81081070000942260900c507010a03000c000100c04200100701c5c0100070300c022044400101c40f1100000c1040c030510f2510b4244180d02c0061160098000d0221003207030400421900c1c0b40186414030301c4840b04504074080000d10054144515050300c8040180729034050034071184242c8403004903c2c200c6506502d800001a4070501248000d40c213082210740110641c54684a0800343e0707220035040c00070071303841604d03a0b240024140d01219041046503500059485030b55040d585002800e0506200303600781c150400038900d0350140008644010241e00c5c01707019200f1902c40340e50920810b40c049260003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 570358741 1250 570357491 570357527
    0x9120507050f010527010509060d0221010f15090906080f0c010503100905040f05060f070e01080709062f030c010513021807020f03120708360304090c 66
    0x40314049950107002140c2c0c45100c2c50003d200b061410384094000d02c00752116071810880c0804c9400c8052751028050011900a5280140d45800d8010101030302d01240700421440075840004000428002031410122801404004400c1034402400c4420f031510f5040003803054600340e0041801c1c0000100301541700264012546252a10001510680800c80300d00c003840080ca4000d0003044031030340010f0b80092040d441e18003441480c0e680e45007403500032540131041c220b15002300001075501c00c001400092007802c014485003420480100182a180a41400d11821201880000031800b0340c0c038100034006980e030042d0011f907220303642e1240e11500840c0e00b150309080200d0309082003031a0600009500070400d20101c0b4007941013480b100c0c80180030744150b020380c10b035103020b002007400109290412003c2d10381440c6841c85000d08140009042d000c2c02685204603025143c0d010003448960b0800c1d031071030305560f00c0074003241481e52095400182d40c43d41045c6002004039000321801d00e030740017960703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 570359991 1250 570358741 570358759
    0x200129010c0c1809050d270501020715020a23070603020c0c010e03031e070c0914180106051201270c030b060a09090b060301060501051c0c0912050705 66
    0x2100440d0507a10450001e0a9030007a14010400200940d500303541c440c0c04150b01140118154888500b01107403428090f02007920300702290602ca0070600d07015254510050801800c60074403000075a2030f00030380911492011001d03009981c80d40200840010175a0102e40007015100c000140c8515489440f442d0b01c50f4821081c01140150090080d40c2e0040c0454004110400014004440c10680400c542303130140010091103184907c13182e22401804602452103a54100e01c0c504186500060341c04034003e1482c10b452010750302840e034056900002860040488000304628441c0144400c1d0300140e8030114200c03181c2d92005c010740042d6000400040c641140c03070340260303a13000710030084480203242c084600303418000107a013a00d2158018801504041045866000c0a421950480d0007a5400d031148401c10099140900501c80a00002e190090511245002d80740d1002c02d4541701d41b40307450300c0704030700c036100381c4180c06100040004c006c650b03480d00d025007071550300c2d481d481c047c55002c2c0c0148 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 570361241 1250 570359991 570360071
    0x8060907081e0c28080c0a120305090f0a0b1803010507021203010e040302160b180f06040b09040b30060c040e130512040806060406152001 61
    0x4000d158040381d000241428020710740800ca66a0030f010101069554004403802c5444540c1d00c440018140c48401450308103c28410001c1d6211f140d80010081202c65a0400000c1d034400c05803840c84000b035640c82c0c10400984001041c3d0501500b103900045004a185e00030030131400000380c1601c070290020841511215406c0381c40d200c9038060702c200e81c0e2040004110303284c10440742e190701c5406481a60320203040c0740c842144032150f0350b008001d151400302d40a03540c02400e44d410180004112048400340d10030340041001c0303009038421540c11801c0820080880d032070f660050007007190010300000f41d4041c50502699501c2c2035501c1003410039948241d5070039031400012042d014002014219050a15100d03184540d144001c0c5080c0020b2150300b400300002c0c6040040c110072400c2054000d440c5d03410804031515001005050700d20550400504102680501550800203011840d1540c141c02e550a15801c80003130070000c83c4100e40c80c050100d00054900e540140310047d88550004482c021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 570362491 1250 570361241 570361273
    0x3130f0b0903150406060f0b04090e0c0f010e040f050c03040b0a02070b04060b011b291905071824020d02370b0604061508011e0806090708 61
    0x1c5000068060f400700c0900c1007803926407540e0703992152040a003c202c4a85a60850341401480e03032000088502c04070703041c05020080e0241d050720500395001003042011090014201101d0603020b1414070100c2c43ea40c2815883d6600004d10301c070400307401440b123070900d407880380070a500440d82a82e07410410301c0403031004044c600843c0c01098200b984484251680e4035000020802400300d40e050000000351612104d400240f0340c2d07c21030042d000c504030316034100304c2d01c51108500ba1300030103000380f80703000c00ca5075181c604002041c0d041b00f5040000e0380c2e0b13101102038031541d0510010901072544200e00084185180c12109125000301c107546001c5020440e069070784a43c40030300f01d00560841c00c0d11a0f440c000f44000171140342500301c004040110040c0308030910b010b06040039105911407904000c014209400351381d009010a0301d20a11f202e1100c0402081c40f0010302030b5401000c20010074041c0007101c491000041c0035924151406d9003854694039a445140c1c0c41002c0c4103018646000c044140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 570363741 1250 570362491 570362497
    0x10f0b04080303041518060912030608072c1311010f0c021e12010b0f03071203050d2903061b0d0e192405070518030c0303130f0b 57
    0x6441c0006504580396540c1e0380c031241554420101c403095490001d9a940306100d400c0803201406071400049a540900f44500c0000c1039803c08000d0606150017004241d03000660f0764120b4035010307048201c0314102508004015240074180303c00e00c40020902044d15140024070132a14031449040b81411180c1d40195003a03050000a0f2002c10405000d1b5009400d085801140c0703251480c1600d01034090390800105060110b5085540a0b955545421107030704001c9418080c801045008102c020b2509400d448001500900282003100220b203c14101445410401201c0200d400000290311202c0d100c06c3c0440c64480500d1086c892000481c041d04001d28928281c0c0c903002911903d005100680341019041104500410303225260082c6c4d942c0010400c105c0005100385421000c03281000203c10345d6803068800e03600440c0c036120601861540006c200e42d4280c1d90740c401c5065a080040019040044c0403400c03640500000402ca00710b4201582181d00f6950105014100d0540b030310403860040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 570364991 1250 570363741 570363749
    0x51002060a0501090b0f060d06030c0b09210a0f030c08070b09011506021207020105041d1614030114030f0a081e070503250501020706230402090105120a051203010f0b04 74
    0x82444444140c00b82819001010070032300e460307004100c4139170707981c1d440c0c00c2120150b001ca20001808101e04017a031078010510903e903030700001314844803d0200100354584107843c0004201da41f060f00d42d0f50406000d40e00c0541280d8102c0c1034180c54101500748800001d0040742c140100303518040c8080c1404803489200350541e100c1d54010808589111aa19959400f1078400da0611106220000c3c000350041900714040c00b07551003d0a03603041c8100d00c2d08400d007004002200f03002035201e1701400e00b6000c8040e2030450302400e00d4134000002601c042420900441c1c10b05409026600419003441190300c01880032081550941c980340c0440008440c8074080e8250007001c0c0d8004024290219910a8060854180d0710a80810710502d0755600e900f2603120020071602d15446217800001d035a0315094248a541421192a01d540307003a034009489080e050145070b06c40c1500851418940d94104021444554410111401c40d195180d100c040b41e04240300e180300d6803200b400b0124880a02d0b4040c4d904403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 570366241 1250 570364991 570364999
    0x9080f070612140a0f0b151e0d0c020708120901090b0a2d0305060604141201020d06090b1002010e06010b030408070f061a04050112020d0804051002060a0501090b 71
    0x6181480c8045601c80085080503201c5901c9100f107500a20510a105000e80c440d00d0001851a43d9000d889054030b59208000340702e1040741c4248440c01c2e40c5001190042d40d166030300080c917910f00300c40710243c6000d540e000c80b40042c0703020080c50341148c0009816050782e202004903501218640c11a540602c1041807040c0003401c002001c012401070310001e03140403015800c195a84c5d075034402d00032811881a44100c0d08021904111443d00b03901b520429400100a65110b840d1070b04018900c00f2a021201c1070724020804a0034401d00348400394181c85204580d00ca060140641d1280caa101810803086020b204800164040b01e495005108580d9030100c04c1015000c2a03290002106082c0c0000700f0641b030f02c510811005002500004041d0340043c4601c900090469407d4040890100340d4003c05008524010061016031011540300d0000365048030254090a4036240180340d6004a80c00720350810a10514801442c0e00070621a1140c590f880c400c002c541c0c2da8140200903500c0542c145a00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 570367491 1250 570366241 570366253
    0x7031b0308121506031b07171c0b0d0206090904020d08130f0b03072a0203070b031f03020307260d020a1203020306090106053a06063e060405010c09080f 67
    0x410100382000c0d1110034003560123084101003405062041358000843c103400e410307191401500c03070b407103e20901034000000d40f4040200011540492118400c42207242d10503078001001908650b5521a0940d0007580141c0c09901c1e01d051a50210740c1c10814010920480100b07540400d50500680c25031384610002c0da5200b041029405600c40810300300249008030044070380d02c5a0241e1001c115942c002e203601c1d281680e89180a00c207560108039001e101d00d1210031450b50410240e41d002480d481900c0c0b030b00b40c0c0310101005854000000c40c0b800c940a001900401e0034a40c511038022690240c068007a4488400c00c007031582c421012488201d44469201c041500180240ca2240c070151040680310840b00c000380742c0980d041454101d40215070320280f240f8900c4445000414002c400c01060b06040448042600c0060b2504400b1a041d4500400c04031200b0100024126030810075840141419280103040509100f400f810683c0038010125840040000e000a03001549e0b0501c41c01d02e00180031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 570368741 1250 570367491 570367531
    0xa0f050f040509061c15060b0a0f030b13110702032506260a05040c0b07031d0301110d0b01090b070317040201031b0c0209160207031b030812150603 65
    0xc12420050040c6821556151002c046410007044d107042d400d01510703000035100800e4503440c0541f8140d421030036101006001841d140e607006145c10b00100f40d50704001c02c8101c07401d8040744840d182182000001820151803030000750181c1c004000c07003402542900c643c2441401d0040d11602036407046000c0703880514007040344078071500020b590344641600600c50200c01141185100d6000d880350b2042c90341c1c800034801007185540c000402405448074541c00c0c5070707540e00c5c0030740080458400c900b030740f4523010f040d65a00e1790300b1740c4124000c086010020381c840c000304103e400144203120f040c1e808945a80408108010350340203070f4a0031641552130305080c42e9036030b0302c0201e4510040c00c22418075032107a003001d480288144805920035450b5443c0d10031101c05004002a2280260070000c11071589608604503c0c0c0c080341d070805994001c00702560408000c1104560042c050340302512039407021170310703079400014180030b140600c1341d01140d8000c4030440002c01072184404d81d80f80740e400d0400704d0005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 570369991 1250 570368741 570368749
    0x10c03061a09041104080c04050a110d05040c03060c17060303250201030f1802150703080103030c0f0501020310030201030b09010e0117010209040603030f1209050307060203041b0305030a0f050f0405 87
    0x114010ba0098004600088007081d888400d0304140c012003c1a0050001041d0710708283c07007601ea0041d11319400303000c4140e03100c0040300d09204000c0780545040d1a40002014004840380c10340046600003070800c54000f0b4001e0041c2040f400c4000c0e0f811919502d008503001d450b0010507503400d0340244050b04142c5000201181030300c00d2181049050503102c07002d82004481c00d12032020400f4240c400d0f014082c485204015001d0381480040c460300b2030900051000c00e9004040c031b810340e40d043c202401c41c10420b0600e08994071180d01d0041582d030000040240036459580e122084a2003030f01e0070310000c1c401c4402c001c06c0310424003c54000350852801001040505000b04640c0350303044000618041c0104040f40540d074440d0415004514424440b201c02a0710074110742007100805c40030424201c1d29501c282c0c40b4407400f8000360510350041b002c1801c1c02a640180661000e0405418001e1788c3d80e854410b441c1e0b040440381c1004204609a00c1c405c1500420803a40c4000001c81c2840c9400c1c2840100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 570371241 1250 570369991 570369997
    0xd14030c091c05010507120603050705010507050312011e061d04020306011218020108060d031d040212090d090621090807051e0c060921012c010c03061a 67
    0x1c0d403220201102d855001c080901d502d2106000b0f0001180b02e2800b0705006c0c10070114104605207440c80c01070100007144020500c0c2c801ea034004d2800c1c964500c11818081d00d54020520035001c141d03090000041c048480000244c403d080d15200c41c543c459540ca4140c6000031007051a4500c041d039600d1480082c946a070085a01820505000e43c6111540b0500000c44000c3c2c0a2007008100c0c0340038032001e560704031042d83d0303005c10200c5403103c095145a0b0000c01c50700d0800c800c20b400402002c0480b000e607449406858800800703254100561504090306541c4070a80c5841c0c0700410403610012508030b00c500c0c084e421b2140c000c2150350109041c501c0c040010101c449050300e14407800d000340b400207001445409111450803c0341c2113001ca0b240350440c200101c81c5403040c425641004111140d440d4400360041d42a02c0c0381c1810081d1841140071030140006440003d0400c01c031514494201c03010340030800b09006104000c00a00c850648103500f22007450003081030b640c2418884510551100c001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 570372491 1250 570371241 570371257
    0x6071e030c110d080906090c011d0a03080304061a04020a0e060c010608030a09060905010807080a0f150626070504030f050c060406030b10080421090503060a0e0d14030c 74
    0x40900b10240c00070b0580e06040c11011008002110311092000b902c20400c05540c215412070090310443c03020034000303490040d00a44003241a0152448ca12155a0f0348000d0f00055420024a0396070f45410b2926074000c01628507044042c141d00c1110b043c2508041c0b01752403001c2510384551041e80310102c1000180d40001d00c10321442d640310600030a041c4c2003031000d007507101019141c240c400350030600d01230f048055a822076410001100b04101905920000c8150815032a050014201100f900c04001403c01c04070310303003a20074500368000340566000000c208891030000b00700c6000710100d402c540c80c119081d04d44034001403041c08140f0110b12404c0d540380310f440c4114101c40a10200c000860707269003055200b14003003660b400b03504030f60341072070451221000140c6c540554186480d03a181541000c80c3e440410440c0c0712803405054450060007948003800c4003d00b200d490b031030000202030203400503914021450183c103213680c030b0803070045c0c41d1500084502079015080d81d0b1800d8001a0507006160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 570373741 1250 570372491 570372497
    0xc01090f060b03070b0c071202010c0b2d060a0311010912080403020a1502070621050114040b01020a030206040201080402010c0f03030603031e0516020316080102070506071e030c 78
    0x400054140880c040340c05100d104041a100c146004050a00704d0036803092011280800c01d071854401c002ca40b04061383d849403070001c111016800101c039000707a050001040140740f4418030103200c0d0900c200803402c0c0c3c1490261003000d1140c0909114200c2c00b910107a0f041032120000b400022081541c0c5c6403082810300d4032034050b980d212200c04841040e00c805880d18200050180158200300c54074001809108051840019000000940c0d500c1203103c0ca004214035841c10540803d03810417990702c03175100c154041c002961a42d101c003218000b00f1100c0d03072007a032406400b50540c0d400030131000d2000d50181c000e0407441d0340b1038006480888000340220f04029500c2c00200009014030084c0c00618026540000d4650541ca40070b011007140307100301d01e900d00c009220401e2255001c81203402032510048114468115403000c0ba00d04281203032003c412143c80c20010642c8001513001d00061070180c001c9030b800707881d0b00700305a403008000104141e484442407000d250207070098000021081d01e9103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 570374991 1250 570373741 570373751
    0x30207030206030a140c120a0e0c130e070801050610020a0b0c0d110f0a0806032e062d05040c0c020d0c0305011104061d0306011a2206021519020c01 65
    0x411a0020385a080721b510014010100c0e2000b00a038007201800e5000200c04800c0000740c2d403c0340440e540d4040d1154091003800198290840e0442c5604644140c11900e0308a440316900c0e0b00c007141c0601822a0118042d440e1005250421440000c280080b15000003401000d81c484080500b010762003242c0840c02282c0f03400c0c6d8062040104402071a2490f111001c4a441d9803d50200500c840000fa11540c072a50061014131607c10000105806900f4060f1000005002c00d00c0035001500c140e50011602c00c885845502c050003008940e0703117501410a003100c1c10310303465a080000316655188094005803e80140320010300f0f1030b81c0e20302c5c4a18003480103041300b10758030740d01d8a00751600000500e0400700c1c045810004a0b0b080f05114042c03012070500c2d8040c144881022036511001403040c900d919450844510381031010100b01c501e9040240116491080b85840803c2200d12038404e00c401031040101c0d5004000e075140200d409101c0800b8102412040c03e08118080e4100400302c00b115540c1d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 570376241 1250 570374991 570375011
    0x3010f1a0d0305041e0b0a03090b0f0c0a110a020907020312090111040314101a040e120901051308150141031002030901060e160221040302060a08060a12030207030206030a 75
    0x2c007d0485040c080c1d601242e907103294a800908844042e202c460807000c000c0621500001000c11768041c00311a24042c1100b0000d04001071400f40c9481c030294000380e110050205e0300d07034040014400002c69049401c415141c000c0c01600700c0b42d0560b11040c0440c424031084c00041c6040380c0b1940e808800c074044a1072201d106014404540808507105141c56040314014080c0c141802454005c80680e005400d605040c0d038541821343c03003004080c0d81000b100040c00d0780c802903c0018440501840d2048070340110010100d042c52220038094142440d1400203a000404002402da400e01c6041c0046c00d001c8041400e510482d030b0300c2911545606000304401149400c000e48040d5100340d40070800820b01c03516090b640d801401024110f4141c0f40700740264400300031b4000468988801c00c21a041c031400081e13151a091724003803a04000e51281000074030404c502e0340020400d0051408441520311503503a66210034521690a6000300583c10a00081001d86040340141d0b50240860f5008548a80d40d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 570377491 1250 570376241 570376259
    0x140706141801180e19061a03010b0304020a0f0305030c160501050d111c090b060301110301030b07090e04031e09050102120306030120070b06190b070303090203010f1a0d0305041e 78
    0x1121114001c44140541146007003060040000500c1c6401010040002e161f500c468540b20500400c01d82c40400000705046444180e050002404655080741f0455100e1070103a40b681c1c00030410911030300c519803640400d80207040c81d02040b90300503181d01c3d1070420100d2143c4090491040706c004c5000c01400b420501e80404510b09910041c0b0000000b006c02c01464520f007190005083e8a02903031501c0760150160614004890541c0c2e0050248000b50380c910070300301e40210481c0c0240c03140b400c003c4c050204068200484014140581c4c8000c903041e68200307011558401c09100d82401a840118602c550f101e00381c0045801403401341c004031303015500c9103966614a140400d0420442000120802405190b1307036010b402007421180c0c4523070049040401890101140981e603816000003c140007094000c1e880302035210740c05402401000b21002e461001401c9964540306000c005100c15421072900340c065802c000e5040d121b0605150400e0032034010342e07041d002c0510100e083c2c4a0302042a2003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 570378741 1250 570377491 570377519
    0x6091823070f050103050907050607081b010f0e06060904021302070609080a080910020c100e010f11090414090a0f0507030b090616050a021b010c14070614180118 71
    0x10b500320601c440b107140000060071501d00826588407504560024003c9079901c50882d010b03582c000c005580c88030300140200130b9841c4c20203407802c019031902250006848903030b080004903017084416203100350740715018030540120403140250302c0f403103490b007003030b0510140d43c050700d9600e00400001410301540c4c0c1d240c0d0140da11101e40c081c041032401c020407030041000c003c0b180041410703007010360078865400d90040c1d44104603503640b1156520313903035500c2d10120250b0010440c040030b004240001e0448094000080e440015114020750a0186e690030b0000b601c020301d8010581d060040c450b040c2d00d84c481e00d140316004030b42280c1c070740644400040842d0709503104900444a45014020506058090309541498501301006204091000160f0b003074010034000521b2100703c410743e02c0b80d50790390012500303a12035100c001c0c075036080d5074000b900d95400007444105030b825a456510580341050711b80c0116015074100300c210380b03184d8000010254420354002181705088020300944030b0f150544600110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 570379991 1250 570378741 570378749
    0x9090c03150d0f11180f040305220f0801020403080d0c11120901031a092a040602060402030601060c1211031209151f0509060f100207090609182307 65
    0x244046031030000740156072901d00c0078040103d81804215000503405c00c040e01000307200500c81c0d034010002078103040c002d0048420020203661a940141d403481c0035404103803054082e040140200301404103c8420508c216000d50350001e0b1035a0418503c00d07080c501801c00b0b490000200701144244100c1c003481044400c503251b440001541c0c44600100004040300c4400b10020000c4900400240f0b1503261043c25980000c0144032200e00c103405091803000b541452400562800c500003030005105901040c0607003c1c80c421010343d030250f680c5140803120002100381c0074200c05034461410120300d0054480411103000c2d0016242010f0703c0c0d201003548600700b140c40e00d0b0b080e0080c4038120540c40c410b04000d540406101140c0150500306994405280c03014000c5500440210000c140d0390358600d090030303000030390080c803480c441e03075070a5802034482825100d5904a58100500440c46901da401461403154184241a95205840d201c4c1940c06218180b00100320f981c1e0702c0441c4001d4802d11200020b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 570381241 1250 570379991 570380003
    0x31b06020105090727110d23060f031509010e0601090b22060e0a0e0d02010e030a0c0804080708010b01021b01020312070e03100507110106030c0e190f0c090b09090c03150d 75
    0x5202c0c900200090341c00d001d42c030b0305407039904800302920343d000e407100d076a0415010744030407110030002c00101c0e152902c00403003038001034002330421000c0d410541109000003220026903d499984d00d081e0b00944a0b0101031641c000221110300e0080c01200e100d510705030703e212101082017651604c182c01e007442c0030350360703024080e880f00d00e84e0306400380400c580006603020744002c1280e00005800c0d507403a800b07006641d004000c5c1440c1c0c00001e0210640c01d41d00a071421070142d4948950301c1d1040e074000d0011f4818030340540204000713451190014403120450740d5040c0c015600d00100f1103814808140c0c01490324040c000ca22030115000d403030800601c111401d01481c001218140500301070501c8240300100303d11a07060201c01d00000ea501d503918822100203040c5070b07000303455104540075045400070000d96a0740c6031240014600342e00d41c1244010999607150780300142c1e2038811103515172140c0780120345c00001d541c0100d0500b030068030045070700c0314060741c143c100090b018000074000c190007101501c50b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 570382491 1250 570381241 570381247
    0x313080f0a0909180309030b090c031006062714120d0804230330070810051e10030609020f1309090b070324031b0602010509072711 58
    0x7200c00203220700420031001c0003404024613030541e001010240a4040103040312002d40c0854440c020801c04d0450480e07000b0f0550300d800c0245c13402c860051082d0300c1070b4000254115041c06082a0500070250f4a01008821000b42c44c14842d41011a014444485c1e41090600040314080c1e01c0a0008040a1090b651a003006080ca07003450013818554111100d9040e4aa90700030024400000885000561103043c0d42403042880c105c011401d1840122941d0f80602c0c0c030200014564800f410781c2c828121294445242900ca80603c20450000c0720440704c08410b4000c450042c5c0303420b62000d00141e103203150110740c0584071400b81c42644c00075600c00f02d0111012a1004844092400f240d0103440810820490403085440314401c10101030218021305580360070191028103003800b4404868407030b004421400342e492414184500700c6146038101c4060056021076014410700502e4040d0302984000c040b0b20f030605404000390701d001020b030f12300c0ca051551a100c00e800b00f0300440d441c2418648030951 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 570383741 1250 570382491 570382499
    0x40308180f12160605040513091b0b0a0201052809051606030b0108130512070c0504050106050c061003112205010e061f020304142e0e0111030313080f0a09 68
    0x1403c50280d8100d5800d02405100501803620b442c2207041420403082400b069132071041c100b102e103a03100031490901040c075038034002c180b00072004024081c080499008021550b00d2401d803804ca0206800014005003100d2500700d503611036600910142070140c03003640e0260b0341425002e1101075080c0e0040c808a621041c3c505140c0d0f0b0420301c01d5a1049013106800c48801007176031a15211400743c030321528841400704210052080c0c164a180107804007900421041d40c5403203000e40180c0081c0c0b8102c2c507501c00d500010b2051a602401036003100d5110402820080800b81000300415440c519484c0601c1c04810a8801c250280a002e00a103c00c00c00710300c15041200a124200401588006014940411170399050307900004850448103003504142c0700c121008001481d00080300103440d2100504001141200e61b0522a0149e0700844d0303d50a0f144a01d920055560b00d070b04d40d1060a0b10380042c80082c0940c01140e20811016104030501071514501610300c04c1d00f40c00c0360601074005803150100b40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 570384991 1250 570383741 570383773
    0x102040b09040c050d050a2f032214100f0b090109050a02070b04140f030408060a0203040609060504060f0515010503011509081903021002120403111606030f11040308180f12 76
    0x2034801c8c80d480410109081040c10f000d0301840040c00e132030008040024107401c5204007151421215070301c48482651990382400880c0d0b6103901c0c200c803d50f8285052640070840303101d8810403905202c0a4004c82d070070b84c80c141c08840101001410070b0200e41d004c100010000b001d90000c0ca120301d2080380e2090142c04601002460011400424801580100428006080001601940244654400760b900da6491074464060709201c100203214a0400d001d210802c0b82c40d820107011961304000411070341d41c4070031840c8403504c0c01d450540c1c0440d070204010709c24110038148044050300b0b903041c80b035034040d6a00c44891400460704540c40f040340740f91010404040d8184a100e004c004110015810f0012198000d01d0189000e0001400d2103051000c040d01684244224450440a2110055032a944040c0900a444501d2074040301604d4450301c140c402d55281c050301e065981180c502400d18500005110100313006510440e8050501080b0068503a40d04480c101d0384072042c0301402d440d04940c0840c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 570386241 1250 570384991 570385031
    0x60e010305070915090c26061e060a1209080408071509030c0e04021504060e010233180d050726160c230a080102040b09040c050d050a 59
    0x21100c818103000d40300b41040c2c86220b80c2030585e80340c00c3e4001390b514410704082d10610491135420095241e41d95101c11110b400703828091140d6002d59540425201d20b10700102044040900507500c0a018440190190321424510b110710303010500018254005456981e841d0700039601030f0703006920000c01400007686018002c6840c81c22030405074101800e41c0e803100721141e0580205549158030380300007003c1d035071036040c0e51000c0041c0100307031507070ba9444804c018500351060524601511800b915000c0c150040c065044c0a01081e092046080c0e10482e0001e070001c0d00941205140141000400d0408005000c4222103d1064442c6035903002c141c40c0425081c04e039400c094040f0030324884502101d0081c0d004465440f26040c0c07a41c00b000710070f40303071805c160507607504404060701070000c0c945008009003548000f0141d0488100807003550340c2410310300703030320030350144144ca4142071080c030780c56042a4000e802c00300380a04020741044455071244040300c20072501c8040003030703c403400030706000c0b1001e100b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 570387491 1250 570386241 570386249
    0x2802030a0b0714031308030916080c190e0604201903110304030c0b070327020301050f09120f0c1f0c05071e0c0e01030305070b0709150e04020d060e01030507 69
    0x70709524024000b04913170f1042d20005000308000100041400303c051000fa0103000003080a0401d03162520b000b80d45d240e283c10012402401308000c20700c5034900801401044400c101c01c07041c9250740e01d5003804050a044502c044030b10101030f03140003050301d00c60007030700100e40c5070007500746101c000317850090070307540105580850700004000340000f00b030b0f0007007603051895013000c501d515030384406400310010700100700c040041e100c2004c0d12400c07200720304140d8409540210000c2c04241c6540c1503800b9200c80070341d1400036a0340f10f150101c40c0980c0c00d8001e840c03602c4c4000703482d40c1802c821031041c43c180040b06840301c2807000980c3ea01c081d0140304c3e02c12190035800e03a14049041041940d20404100000c08204502c13500b04103000041000044001c0040c0865540004095031b483c0340c01341a42c2c01c01001200c8860404001540180c400c542c07400449507c111240380603d41c40b041510078031109501980c00540800c030314040c440040c081c81c0018008095007500942c5542003d5040082c1504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 570388741 1250 570387491 570387527
    0x8060102061503060708040206040f08010902040c09082119050d150f12080f0c150108060411060304060b040e07050f0306010518090a0b04120e0906032802030a0b07 72
    0x51401c20303901d000605640c0176034941000350721a100c3d0300001d25103016907030100c3c1000c500c281010079620b2064100c00f201d14400d40c1c00348001c040162054a40940c1c41c010404640d0252503203001c5150080d901491041c5940b00442c90044c1186c0310b0050300ca110035052020a80004411510110340d100700c80744070003110700c0c40302082e08000150304d10040314405c01c021030450f0b00144060000d0350088907007881400d2905907031013880b0462951944580c0d08406542405103000050041c001b2270702c684220b81c404c0e0100b0b0719031080010808103400150042c0e8846940b04184001900c651080d1088071220100408041c2c1c40c28082294120354800007500135001040100002e455141101064010400007074415554496000c1c0c681840b80f040640518208424401070001106071741e502d86406a8840020714019028010207200503504250903900c58610107284c0c0c90007803060480100c0c1d03041c4076003018481d0340000389096080714080e0303650b40524081c080100d402176140407032a05510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 570389991 1250 570388741 570388771
    0x605011509080c01050a0201021201060c140a080702060c0f01140a0f020405030709020a11010f050a1b140c0a0b0115030501050901081002070309050405040b15040209241303030806010206 82
    0x11240c141c83e81c4070121803a042c4000410442e079040d000f13406441813400029100d814669441c05e0003408008540000e0369140e1031008803242c08400820710044140d0040380c01440d06181c0e40c02d21200f0b5014850003041f6002ea80035802d5081028001c1c224820729a000e420342074101000d40a00b15041102c01703052445c410401003101d6100890000704598142d0720050b2203034200e0f40309580076040b801101d0440c2d4600b650142100c0c070264403050050401c950704010100b0141c02072482c0c4820000680c0c0426200b01507100101d07000030081c80c0d6001c180054681c001407075540c440c000c01080c0c128002c5180403000c0581c0c1e440d858864140113017001c4400750f810794540500a921422801c0104010540000f0b081003803600440d1120018200035104200030710302410800f070982410368000090590031841c03100d07180360600a6034003003071000385044581c50798404000343d5080014501c00310f000c424403000080f00742c0e5101220041d07000762511038091401c00002401d10000900c6841149020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 570391241 1250 570389991 570389999
    0xb0a09060f0309020306060d0302030f0a11010b0a06050912070518090114070c150b09090d0806030d12090606050301020c071a0406050406032c030a031103011a030a0b06070605011509 80
    0x145d4160007c205441e070090039181824120b0441c0310304401440640c0f00010549451644615851a02c01032503000b00890107501c800c000c41d495007071040000081c001c0c0300a000610345140010106070400c0c1c05c4600b0302e6903c03000309116540e208032042c10220f55070200503000000780103009680a00c02031164403445d0021000c2c2040f01e03d6080031309111007034200c9008216007a0300040060724010185649890b245400e0f958a01c0e51051741400641c500c00403400381c0c1400103c901c5000042c1e01c4420005664078240b800404000308159609a19030341c00144544080c8001c01d0b21800c0140075020315418812103148580c019800a044018200020010150b2103000c0d1029584c103442c0c041559030300429114180c422080c6540042c0ca80241140c0701140000024070100200b40c400b07005030085021041ca1a020910412404051407040d4806484000d80190350100c1c4c005800192013001c000801d44507040140c00712107441d502e4005001c2001403101c0c1c24034400044c903104000b6401c3c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 570392491 1250 570391241 570391243
    0x60412020106063e0a0215090901180f141e150d06021e03041412070201110a050709020a12020918190f0603020f0306061f0c02060309070e0105010921030302040b0a09060f03090203 79
    0x5104580303c01a444140d035038bc41c4400d40149030540080c1030203001e5007000300e440480480c0d054072003031440e058502003034003040751161b8a103101d855109010b200c45000907040c07143d201203401c011a40564204031074150024606103880d80b003a00608425240c1c034092900c150444050100e04803158030921020950000c80d404840f20b081d820f182018100d040ca2040524000c2100c030014503038092000081549003c0f40d015240b6240a0340d100200f4503954004082284a50511113070400c501410003150550703c2c51606070403501e249000c0030000c0c1c44180346800c9803518090802c03010307258a820000c4d441d11101c0780302c01c0401240540500d00b05000000c0000b40001442c205000940f4803a415450180802411144d0081c2c03059580386044010551103007118000c50030381101500012910754400c040d20014ac9003406c1030042401c900b84d1450491012100f030840c1056000c210100d9810b038014003070000c1c80029100c560100d1705120018181d04013010124040510300301c103050141e94 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 570393741 1250 570392491 570392509
    0x20c01020a0f1707120206060108070c0c05091806100e010509061c4b05060a150f060302090301060603020c0a020120010203010305060412020106063e0a021509 70
    0xd800200425584814400f04450740035010010b010161090394040c0300701e401041c6203120f12030907a030303031562a070b9000c0080d121880b01c40c40240c0210640c1c030040c01107007040340c28a90006a5000511400035441c54000e1030300300c003201c10400461002c1001c004030641503030014050242100d2800031403411101280c01580c2c828514051202000100d8040c488140e00c1d13841d003007008034038407184008925588001c5201401019200d10300072210030710a900c0002d80e40e002e8a9200c3e001d00b0b440c1d00c0310800300001d011004442410301c052003100003010403400000034014015a02c3c096165040f0354201030845403d98441d4081c10700410003803510050200340d2490003942403c0c24010200140c1c04190b41141e0310311103081ea90302c0040044107208001400f40c0c0304074411080b2144850750000120300380c07201c0b48110408038406685481c4158108a480910a008138010282004140c0b07070718811301021030395940454001c540d000080d41440100c11202c0760140342c1940c40c2c5483d02d404290800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 570394991 1250 570393741 570393743
    0x30501060c1101171003020306160e0111010b03100914010b0307060f02010209040e01050405071202130b18010905011406160f02120d020607120c02070611101b020c01020a0f 76
    0x84a84072215020307a008002d01351640b0b0301d0041510181c5000422181c0540303460205074400e21442c2c000441a1041741c83d40e9845110ba039407003d907407000040040d0f500f08080c0286c01d129541700c680140301514200908051909107100105e004452410305807814038030480c2c440d825904050200ca00341d03c0c00108041200e2941c40c002e104002000801c0b070090040358800c0303900a090007003c58030b00d103054101c50b02441c003800545100790f59400c6809540e03841c402000f500482c01084800c001101c65005070100c0b01e01070060b1b1010145407185c00c00e0301009070003009019035504014445088210029600c55009031840e602e81390526a000c108103040d41001407035010100d01c00d408540f1000c2d8140c9040e1451002c603040b0b0303c0c040c04013940350300e02102c0c0d03207001031079110042c040c024181c001d010a095041d00604145030500404454104170110200341078800c0b90884002110301e0720071b01450741da6003003504c0a19a01000000d05060480003c2d80c11580f0210008010511189022080c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 570396241 1250 570394991 570395003
    0x150c18090f0412030b041d07080d0e09040f064b0e03091909050c190c1110020a051002070c210611090f030f0a080f0409051006020d030501060c 63
    0x8495880800c6000c1c041c045c6001c1e03041030401407507091640d00d00e84c1d10300301800502c003503c1096858107503440d86e59031241c042e040001d40d10024040e0900f0000305454001d80224804020700000e0f031200000d941051040ca02c6038140c00103200107070089113001046080301d90075541c0e45491800102200b8000216840c00502da86510500c8520000c0040b1050388201414010072500c40d0300c1ca40040024912480d01c000707090000240e001741b044411203d41d070304c1c60900304000c485103032000c84194004c1c900c00c845601410a0710711480e5501d280d80c4441e130003564020100151146003181c14a004081800b03150790041c0000c00014440f04412400c1c1e40003501c0c0651301c10180f01603540c5c40280070070003409403072411000d012060b44b6000207280c0c00c00103540f2032403010700e0350713050550310891250400035075000300007134000041141000b00f4001c080b006650b8140f507102c061900440700103803150100c034114444c041000326010b106003400304000d0f0504000035803400c0000f52141d509186c0081c08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 570397491 1250 570396241 570396263
    0x70302031b0c07030b1003050c010203070210360f050d023d05040501020c100503010605071b0f05150304020109170102130801020a1202040305031209150c18090f04 72
    0x10b40b0b4000c114403001590000103008050508406903400d1100d1400159014040d1240741041540008100c5019030742c080c003907a0f0042540002265941c100c41c90100c1481d5900b00849825038003e00c2c0c10040c0705003000e403d0801840d004c488000441c007039010501415850741500c0c050381d034070520070450390b201c1c40100d80342207040014440209000201e0308000007580c0707102d0307440d90351003409801920001e07002c07030323010029040030440d051002403540000035000704010b21a42d40701d0300150210317a20a2507100d00020110844807070500d20740d08540350a0004080030025490100144c6500e0010300000c1440e47c149900000c04070842070080003400d4100c03188603051208254119403a400700103481e601d1a64580550702d000c0d40c08120054001040503145113800881c1d0f10849007203950203001585480b050f00614030715007400820300c203c980100b424005401449260a520810318040010351b600300c1d0707103020480714418026440c00745103440b04010b402200305034480d4206401114000d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 570398741 1250 570397491 570397507
    0x1020105152202160b150901360e071e03060207080c010203150109080106060207050f120d033206130f06030b0a0e0619020c1606080609070302031b 65
    0x2441c8502c4080820310000e440240b10303000081e28481c59124004c40c0c10750b40c4903501d68044000a5020051380495460010001000d04150311a5130f002c40e09184100004c41c0a03034041d40001d4007540700c00c0940c03110442508043c003800018040d02d90114665001c0c5040b9841403091050760000401c09680080e4000a1000c03840c145c030602c400302402990340c4c0c60b241c000c1d800c0b18400340b2505c0e400f241c0320303c00200700f401040c0280010366140d41c1c02000002d1800d0108848030407000c3c156a00240c0c140d10040c1280c0b414000c0e589401442c0e00c0c00305020203c035010311104c140b000d80d40e0324030034400410050310405c146c2c209600311300112808444038440c0c10007000104100d600e42c10381030349042c000004001a00e140188100ea01550800500000c1d002041e21403504540a0b041c000000000b443c0c104680e5028210080a107000c48001f034600743c0b1049444032075500041c0225000c1030401c0040e181c90300413180e21880e02d144c25421400d00100361550f0620703687c50f03010030010201d0031b81 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 570399991 1250 570398741 570398779
    0x70f030309180b040207061401082811030105071d010e22060e071205060f101b0b0c0304060f0902030c061809130b010e01031e0311060a0e0c0102010515 67
    0x3e220300c00c014821580c500c0035140c4103004002e0030442085801c00748000003041c510224420804445004d0800504020303000140100045450b04946840d846044100c02d074800340700f200d2050103251200c0305807009a01c41d003194890304192060420030301040e045400c1d1629845030b40b044c071050581b5100d0f83d240c7c5a41401802d45034100c80328100c004410051202c0d0301c0390300158010503000041001e51612820302c1103203500e4400c210b8102d070b40030302201e0a943c4180024074994034a059203038421502603451031a2020285e6226803203103004410300c4280a228819203402c03c3c0740307590401401200d40d001c280c4440406840c580b0910740400c5075003c841d040154112003403030080c40b5421a180068650880d40c0381140e0075507010100030008148601d1503084030b410303241c0100040d01d000494182201c00d00c2240d4808030104a1034401d0703a0000d80c000c2040794007400c0c1010010a091142090003441c00440b452568110382c189824040721154204010107141003d032140040030201c54146 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 570401241 1250 570399991 570400001
    0xf051e060d0f020a1403010e0c210405060f0703021806030a0b040e2b020307020f120a0507031202010b130f0204080a0f0b0f04111e03070f08070f03030918 68
    0x503201d98141210152980e20650081800c1c10b59074a40c2a05400603000ba0a81800b0901501101c0000d0390301050300041c2c180050b2030b0017000220801600c80b0f40d03603001070b00c0741030540f01104c060344000c09002c0404140500164402c00d03d00c2c0c11401d10f000440300d558480e06030b24119020742c00010200d814000140c100c41800000074200f031101b0702d46005101d9580000404000108c41400340824604182800706e101c1010503074000c505240c4580c08014031580b8000c041648082d04152400141506004941903035016001401c0c0e801d05e03506082c40103031060580d000031640f40440030a00d6549480402c45800d9a180001810200b200180c50082c070664210000502c01e480040c1c003040710150110811038829a004019506c41c0f101c06045040f081d40c00800300d07207280503840000d0074041d070000246201070048090308881c52010a003803003203503001090407610105c1e00b4040003008104000003009941014410340340b65440041c4030811070b010340f90340783c07221b8483c031045c090841e041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 570402491 1250 570401241 570401257
    0xa050c0906070803240604060503060604091a011103042315030f040507060e0604090e100501141906140c0c0a06050903010b030c0915030322030308010f051e06 70
    0xa12580d0388483e080201c07143d0030884030344245502000e129906003000c2904e5401c00c00c0c0c01740c001403c050500b80160740300d4000612082c4c00400500000915042e02d020b8100c0030714402124901c0c000340b1a000401300c080300051421140e00410041003618903d40d015501c0c0c064400c150481340021600040420171111000581040c1c00320900190402601900b401640308074110342d4040d03502c01064072160f268040c00d03036001c003003404108141c103080d801152251242c8020b44400c510080b0341d810440300207070400c0c000303040000c250b14040d040c0540c40c4000c070741c0c114014404162600078010000c0420a04801503440302040b00c240c0d4100810000030883c0000b4020056551211401012604940629480b80d070a0a401c0f103a64103022540c0e81c40c8200203000e00c2e60315038507000328151102070b8404140c0c25110400186407480003100d50924900c0303d414041d4001451400c0c010191501a0003c3e02c048401c5802000706540f000002c03010304912204601d8000325600c0001c0c164080c04103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 570403741 1250 570402491 570402499
    0x201020f0a06060f150215090c0a06020c01230f070f050f03070312051501031a180f060105030c03070806040e0a0b040c120507090b0d022e0f05030a050c09 68
    0x403031080020b0350300240103031210f0000b52150f081ea02c403400f68110b00012011030160308024584540c00500c000103075400290941260072030710f150400304840301c10700c1c3c0c0f0000c0142c000c3c034001241507900015601d65203101d01490300718074060600d005143d20501030f440146e8000042d02100300000445078100b80e940180036204a150b403110701039100e500140049001031a80070182444120900c00d40f40504481c40c010795244c1290300054008000b500c85820020400c020880000d50302d00d882c101c101c20610402c2941c41c04d00f4038981d040d602011780141d045c80303814420840954070180070769502c42c50504c2c107451261200804500104809004e11300349000300309c601010b0110b039420140c01184640d030306009813582c0304880c00040407422030082181c1c1165104000900c4035030445c6d02030042c0203100c0d41e9250216800969135140341c800c1540c4200f61914051380380f2b00c65850303cac41f8100b10384c104241000b0008200410310f1000900525400d03a5660202d00e4070903130a029542814400781c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 570404991 1250 570403741 570403753
    0xe060103080903061e0f18030c03070c0801091502030402130608060601021b06090402220303020d08070302040e04240c0207080f0a0b07121113141909090201020f 71
    0x3003010003280d0b00c00103003980030b40700d5200811402c51204080c03404c0080445c842610a032203240c0a4401c07010090140c211a0070f04d01000100b05906000608003080d90400a5a4680341898401100c4045500270300b01c2d0791402c54002d000c5074400c02c41d8076500e12843c00042e40d17640c8a1000170380100801406030006ca00d0124042070300100083d916004450036001c44480740d0401c95100682c07050602c100790090018050a10350b81041c0d009000f20b020b04200d2034100e04034164001c1c540000690003540140d0228148203895038002040c03641020051405500c0c103801c101c0a2845200082c00c0100600070b840100c1540460401c410041701c0030805080c09450440c0400a517038031000e000e80c001ca402460750040080c0000120000c1099100c02c02a600341c1d035400c000d0b02c40a660300b80144480c0e480e50008880894018000c1103660004000000b0f0740e0f0a060801c00500e400c503001a02072080002c40120a9100c602c0c0e1200311403150074042410116440101e05200c89000c480d103440c803511f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 570406241 1250 570404991 570404993
    0x3020d14070503270316062a0c05011215060c080c06100f06020304081213080304080601061b1104050603030708030103121106071d0609060a080108060c040509190e060103 75
    0x30100050301e10041384d01d81881805040308160b21001e20b0005100728400c0800b0400c1454010504c0800c0341940030146500140c200000f490240050700044500003103400f41400b0300d41c0c004860302e070a126070840030000030b007000840404801041c011401400500039400b400c0028040071101c080000b43c040d20450300300055105100d010034018202260400840860464400026101115090002005030551400300300c0ca05c0d40c05003070b103170000140d016000703c0c10b081c0400080009011000003000c0719031410030001c00c071a40041003011000030841415001c81c151640035041400300300e90024640d110900007a01d184202e42c0000d04200010000206100e00d07401404440505620741d0740d0204200c5030b02c40c0d195202207070100003240007a201d2030200d481c00d851200c00218050003042c03400d0444000030715650403100c14007000909010062108113024842e00d81c001c8004a2000d08181c1014005444104c00500364038040360313440491620884542c00c14084024054207031200c550312 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 570407491 1250 570406241 570406267
    0x190305130b0d05060a050402071e050c1e01030f090206092209060905010f050112080d110c0c1002341706150d020904120c0b091b0a0303020d14070503 66
    0x1c075001d0b84180c0d4000c5d40066142014005c6840349648840701c101c000c078800144000103d00400141c2c0c803889a21010b030096151a800e000304055107080b00c129180903040010305447e0812407160f030050a0400880061316028250368a40b6011524001c1da0100d20f842010313100e0080f904a0101d42c20708007850180580b60b03021003480f5000b10000e0243d89200390320001910b50071720070320700300c1a0f440c81c261000c2036800d401741c1300020300c152010420b0b0000d0007111640f0381080c5071085d01c5421028240540d40f60610310010f801c9001d00140c90f0f0381510f070155868864203824091510700108054034100a01440e030034014000007402a01080511080203a941c8021200d8400c440c1d5802040107241c039141c491a120113034014014441a511551120030070042000d881d8140845001002e0002c0d5070788116601c5407048400414420f0340100700310030b01c0003110700703014040e00301c101c000d201103607010401700404011800d18000e105680b1440d0102c61180e000080c0031800003040d51046120 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 570408741 1250 570407491 570407501
    0x3090e04060b10050c070b190c060b06030411120a0308060103022803150905040804030210020a0b15030c010305040809091306050a0f0605030d0905010f0c0501020309010b0909190305130b0d 83
    0x178900103c600d05500c41a4101c1c50384241081801241c604481c03800071941b141070000340c00307445600003080858030100880c0c4c4035042903030111200070b0340d500b0401003414403007213061000103541c0046c24090100d032400b070078031000500300b01d04140d00003612039103508880a841c041d014071644140c2c200c00e031a010080c01042400c03000c0c0910b110460000681a000b0701409008580040c0c110f45450700c0c55003040b92004100301c00030254052904800c0c08a620300da400341c4a0410f803030f00a8501c2c04040704140c1040ca48121807414940b4040901c40862580c80581c2d0259606036150111074441c0315000211000c6068001e0480342464100840c40c21250880500b4a04c00d08003400940c1d102c50405d52100500b142e070600251009008024a40c42403800921001c43d070304010048110030380303585e03007640d2088464103039981d11034a402c00d04d821301d50b404541c0001c0c5000905a041000c103404411003104040181c100403011450169030303a0b109070140018480301826554a601c540080d9000d06 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 570409991 1250 570408741 570408757
    0x708030405120d0804081806070501090c17070b1b2401050406030317040809062101050604081011090a0b090a060512240d05150612031c061d0a0b0d03090e04060b1005 73
    0xdc0d44482000680f030303040c1005051643c186c032010300307002c90500031410500d42045075041d0141082c2d03004001119004e2001504940002c1d900c0d403219803d010f014070300e040045e40810f001c0e5141800810110b41d005410302003019105411914a8a541c1040105070003030880703481e400744002a0b003564401e00750f401c407101c0c610315003541030300c0e680d17184100104d43c012031246189a4000704030001d8003074081c0d4010002c182c130000134641424220004074010035015000120312460002c0e01c0c004518202440f2801000245810740c03030702c4854a0302200201000e03041400100d201d003001c0d00c42410042001300202c45c0540720701380c40c0089007051aa01c10200382d41030307428510070010480ea0f08201d42010000304031080150310301846030024541400c00030140d0550b84d035441c4401b049040b07510035101211502c140744c882050a048d008403040b1040407004600c500d603d0800107000940140c00300044a4040c9004041c41c0e503a81085005010220b110552004401c00d03202c1d04c50781c1040141c02a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 570411241 1250 570409991 570410003
    0x109120810060906080601030c030923010605040515010f09050409060629180d08030108061f050310020f1216031401030512070f050708030405120d080408180607050109 74
    0x59840d0000d070f070810540c3c0500000a00b24800040d000c2d40290030461030204d20745400189004c1c142c890b1000d195108090b54802440011102040b4500740558409071004a604000e10b06104000c031950307411010503203040c00000c502282c0194090300501c070041c08094000d02000c0e1240c0362110041c0100e01550408816541765a54010001405402000d011052807032038015501609078042141403903007607008050900180010b201c5c00d000d58000c001104c01003015041030100c01c82200c80041f00c040d00c0c1107150740c041044c0d5500140c41d24840314100001a51400380c114011618443c016240002c9802241800445205181c2a4210503601e0350704024a51442001a062031003e20014181d0350000c81506440d01462000704030051149038018015041640c1d000c2c2440131030341c44052607400104003044242841d0050b0800c3c886d2490103040400e0320790380044d00c0c0c2c00c0d0261000d0100b01c0081031804c0c001c00d00c1031001d025014010101c035195005491b2150280503401412500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 570412491 1250 570411241 570411271
    0x40b03102115021b0f03030a0e0303103302060106121a041802120a0201020d03020301060f030519063b0a05090313030b0403020105011a180301091208 66
    0x10010710881800301640400c81d240e20500c0c000544020307410022900b410b80f586145140500c03c02001180c0c00300100c1d101642c0c6074904020000e045800f21964a150740d0402c00400010b58040c2e4030702e00c2a502100c81c0c0c1c0d2603009203502c509204d4001e402184c0c0c0c01d4242c0000003078603142c000603824103c0304180e85500c0c000c640e8203a0001600c10010300e000b98001ea0010300c1c02c03107251517003200d140b12a4880503c40400c05540020307250b504010380c0c684448c0c00031460351080d540d05000502d44141d56040075491545044401800300b6028070400c420980c1d2a00443d810410f04007841100d1b1a40c05801e204150b1101112260072440b503424001e040800e442c0161900d1404580c1421741800e914244030a5440084841c0980f00c010a1721215000030496800d481640e990540c02035401032004625900d401c3c50003a0844e43c040e08084115500b03108154801a090411030704a22070000c94801c200060f4008203016102004004100a01c49006240142d5200b000d00744030b160302c4407603504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 570413741 1250 570412491 570412529
    0xb07021e010204081e030d0912030506040b0d030c0c05060409060807050a0e130f0f0303050106260c0913050901021c0225080c1f060608130b0c040b0310 67
    0x402c0f0300c2a0321404490381c0180d21004d4410f075a440107100d9241e02542900d1a02c1e150111300b00c01c03503c540d9000c8542c0d09140c608980525818428143c2c000300c1070303030100459061100010000d8110780301c020f00b040300c44403d000801100c98926001480d0140880e91140d0b00c075208000a05880c2c000d4203928424424002024501104801d049540d0f40111850980302c8a1400d0740034080a807003610001525841c07440019520041074254034001d9400003035039410641c000f41011911300042d8401102c200841110f0440d0f00c202c01d4100d42e03040780c0c4503035489803200400e030070b8119030210301e60303071442c080c00c1003648003064000706000e401c0da1807000e4208000c0104003080f800b070340b042e0605880c010300e555100e41c803455520074100c6004803421810020800512803a02c1030005c0b5405144044052081200415001301405000f990402e00c86a00c0c203da0590b000c0007001c01c000d801c100500010541c43d0356007000b12030141140c50b160302e58a190220140c0c048042a229102d22a081210850 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 570414991 1250 570413741 570413743
    0x2a090619050d2403080a020a05070603150603150506090d06020304060501030203190305090108040204020702060d0c18060507020d110901060e03070b0306090a0c0918090c050d0305030c0c01090b07021e 88
    0x41200050383c1850361007242542c403030700d0584c1c2040034480d003544140c01340d40c0c02103402040030f40000c100c5680c01040c080c3d000e2000b8181035445d035101405040c00c125400012411080c000010b564085d03d040b5243c2490000288440c070390b05401411551001040c402801202c1c1c102d14140c3c0e0003030f0200c4090301d03203900340103130600c0141030701a0024809124114041d0f11038030907150064002080542440000c1d0001031040c1d00050903000556592402d1003425900600d09070310184400c2c12180388540b03400c5014020b441902d0f00244101d50300501c0e40c04008100b505c203040c00b0b4018000b8485580c40300d901a04402d4460b140300d220b07105030307100018001d00c1442100d21502014254000036150020107401504040100505100500c10b0200e5140c2003001444018001e010700850fa481c268203001c918561039030007a5001d02101481e540120750490102c940006118080640e03039049016900c1c014109048018006076092082c0240c132940050540d2011081c03000880e2000d102e90142 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 570416241 1250 570414991 570415031
    0xc02010503130507030c06110706020309030c04021309020703050c0606030607170402120f01020403060f18080c0a0203071206050907080601150504090c0302122a090619050d 76
    0x24009601080040c41d410032529252021510440c100d46001ea00d03551440e1030300c02c007a0029400120061051035005504104500051600d130000d18030b41807043c40401d4980a146940d00e00a903000200c4505a5070707030401d141c00034808004119100c00ca249401040b940c4240b402c00580d2251001140e201d10b8081001806450b150f242c06000802c5c000c2c1000b0b005400510030b81e840040350001a802403000c1c0300d201c580403200b100061b5190300318a0900100c07012801000c018034170b01484940182ca0705540101c030f0580103118242c5034802045d44520381511450029010b002c0c101e000106d68130020301c4c1e525064420302c000d00c841da4407618403503501c0a1911440645500500040202c803503038900c5180003008a02d46185019142c03140c11040c0c60002e860b800000350300007020407640035440925a08204c0c1405600b0034114a003c1083c00e40d081c070011209030781d000040a4050f5a40d1104845503451240c5400c803c407102c0f01d170041d02d01d0f0013900c0c480008500340704882404120032041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 570417491 1250 570416241 570416243
    0xe10180f0518090c102703080f03090a060212010501030501090b01080a0f270c1a0316051c0b0306010906180203070207170706090504020f0a080c13080610060c 70
    0x2542c20040c2000d40200300782d032070207852040c05020300d4180424544034000384004144041e2903000e0b50300c0f02c00d04507100b210701c3d01c02e00801301150510140001900300e0111803035240c0d0504096260b4550002607400c00b42031f010001c01d0588001010346449004a0b4054100c400136241040b40342e03650011903040d203030f2890020340040d0140c80011641c031800e6100600c8002a050001080e000c4102c2c524403c025006120b145815405c402d84104941506180c0141c24001800e0901072001c011070591400054644d1000c002403526900c0384074070810655603030254108918404589404044001b4400d42c5003840c0280510000800c94150a0040074111159542500d01807900b880c00c040017900041c00c04421402a00310020b1001c070044486040c0620301005008014509940540052100d6009601070382c0140450b1003d0b0f5010015039012071441d08150341142da030721410001a1107418030203089540e001002058001c00091554441c2c00d1040c00110300136140c060503150b44040d80c030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 570418741 1250 570417491 570417499
    0x180f0f0d031a041512051c02032109030f030f2a0d0504020402090301060e1e060109050111070b0307030605090a060332030a0f030b0a0308190e10180f05 67
    0xc2d141c1d800f42060350140107240c500a20043c0e04035114000003d0f204507502098401d03900030300025110052100315504052032500045140040040414100215820350807031900b00200c0020703084d803814012180d2000c04194007603a00c3c42c00a640782342c40360080e204009070011074174031a4580d40380c004020401d884200780f03240c206000d00e00381c40c016040080089800940034404406962000d01640025052410701011186071126a00b8a55203141100e01d103524041806e1281c1a40c00c4004581515020f1804902088111141a14000995201281d020030020420008640c19803010050b40ca0032280d001181d103560f040d210566110b400083c0444500c1c000c40080c0507180340d1800c0082958100d04600340d4a1000c44d5400c6402010308600818500c40d80070043c01c2d454407a0100e880011940c0620171130131034407260345a002d440814485520015203521165024840541c2d035400001d20290400001050091107151415804510320446203000f188080c40502e088085d140068 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 570419991 1250 570418741 570418781
    0x60b1017180316020303090d0f0212010c08010306091a0f0714091c0302070b04030609110d11040b0315010f060809061e1003020429010513030b180f0f0d03 68
    0xe00d04403c10b00d69641241e061104100e4115281c550041042c0101d004118941094000d401848003400707012403165a0780e4580a4689981a000102c40c1d0540e50080000a11a83c141c50401b9040040d0b00f02841d80c000a0000c1203c108180f0502c1403080080b0f980b010035a54080c0314a48440c02803c14440e88904010420003140d0040304000c4041406841103800c2d0503900c8158546540c016041504e4443d00d0341c5d4803009001440b904200080400e499260350540d0740c0c1c03105402c030400380400d0361207103481c0da402e810303180e404210940a1000741a1f40c0126940c0d6440300c183e181606100700c0002c11580000200120070109030710b441000c4100141c0003014401703481000b050001000f00c2a0b440035010048056100c034810a928001c8458000d420b03032400000c52019070308502c981c0d038100302040200c2c9420309000b407030b5034080301c0d40320340d2541c4540c4600106805680c41d903561040e00e44aa01500002c80030002500161180c041c0e0544104042418040381a07c1d03a40d04c081100014803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 570421241 1250 570419991 570420007
    0x130c08011401090b0a050702040b0909030a030e0705030d050306030c030c011407080d05090a0201172e0e0f010e0c070b1909200a140a050d060b10171803 67
    0x1a030503008060205140c060f43d2151298042101c0e07030003c0d18130100051001c00c0040450420340f0a4100d4000e080b509001d41d403501008241da41d2090312901001c1588036921242880c60400c5076102130314005003501d404018800c402403003600200c403010f209100e0a81c10150504000c200180d02e000d069481c0154142c418124003940d41c003664003101d0810003005a20a100702c5407141c5400f42819101500d0000715a000040009201c0744280710f103858014248001c0c000c40c1000420714010442c032000c0a001c82200c60507411220b5480400706044940c10032405903564200c45042c0c4601b000c604540d501c401c0c1c4103119a02403003100403c602e0f40d040103d60b00000102035103401000e91140820585119550150b0008214102201e4518240e51440541c90400d8a0724090306000031101801c42d602e000082c1c2c15400c0380300e094001c20104d00c8202c18031100742c00594515801a00e1920f6566900c4801000598005480016280b001000c02c002d4258500e0166111282d02d005604092032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 570422491 1250 570421241 570421259
    0x3030507050319090303020f060603061503010b130501030507060e010f08060439110a020103020c07030606082b1218020a090c0f05070308040803071b11130c0801 71
    0x18034000e40746848148052000707908050200c0c24041c0450750745480c0c603440d514005e40740020b0400703000400e80005041090540740003801d154401e0800c208003411210010110f0700502c80d6a41c1580c101e441940900c1c11886590412030480340f0800403030b845296104405c480e2000b45000c0240041c0d02c0580c035000326485401580d402c100000c1c000105140c1d006a0000413841e420700000b8050701c80c52450050b0124500e017050600300d10700f00850110b00b501031b0310f611350000140003418140e0208120844040c10070008000c1c5500041c02c1000c540c807803841c10364ac0d802046000110101001d103551000c11500b2807060400007507152001c9840a1100b2a0064100d96030401c0d11000720110390000b580c3e404621038000d044078000000c0400402070024036019240c0c00800503c6030800c800c10009500004181d03009401a0800707450f602d80c400200d4050081d2100254001c0858a8001c28082040000c1141580c00c0f5a0100004c8104400c1010f440c0e000c0421001310380e20b080100071340d1308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 570423741 1250 570422491 570422497
    0x103060917030702010c030b0109080604060e010e0615030c270a0b060f040e10030510050a06090f0b09061e0607060f06030c031e121101381801030305 66
    0x111650301410350280c01c0c0325086058000301c41410061b07442d600740860b40c503018410140c201c482880c0250142d4140b00041340c3d01c41c8058801016542d8851190411300029405031855040f042c007038a150742841c04102c00e000c900600007078031078042c4540c9051a45001402041213094003440c84100c0c8540d01030340b05e040c2c000100f00d00d100980340c204c00384c1d6550750b4034001c0ca644943e0a103880c2d00e65040c00d800807080a001800b01100003550307002171001c1500010f91103407811b07084070042026605c403030141c0301600380350b44a40038140c20040e6041044505070041100b644007542c0d146581d60340ca0041240c0c426245110301041c0e81c5046466001c0c2c100007004040e05c600030100030031005041c291503000c44079154403d07162009500001c0c8100300c840440c40a510800746104640794905890700c0072012705003020303a002c0c01100c0110912411080d000360071000500000903e00e05160b4200c86001401da611001c58280b00000f442d61a2034480781d80c10300d560654903c00610b0b82141d606071982c0d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 570424991 1250 570423741 570423743
    0x15010f090906090207050705090c0712030e060c07140703020a09150b19021903121d06040b07030605031b01050703121b0e010c020f090c3c030103050601030609 70
    0x2004058001c114403809005401c014a01c511005903a0b440906105050440b5500400d05c6002c02c4c0741070200c0454241d064a280750b8002d031404c003220814400c20380041c804003e1a940d40d00441c000c00c41c0142610014166281c020918044c541000e8a20980ca40c0041d0000a40c4461400400d0290310400c0c0c2c001080c84a068480341d0340140c540c3c21070351060f0002081c4030024413005030280c400d40d6043c44510002d0b441509003c590950941d0058038009025901144050b900c81c4070000202d407100640b4000703810b00d829107000341000d0419902c2500c0c00c9403024007103810903100080354240040d800e8080101d58001e800d44083d1000115190343c80720f81e0580c104801d15010078a034900500c10b01d4031109201603d0741c0304000c03020010740314030000344509040c00101c80511000d030701c0d00d422112500e001200c14402c5079841c003626003118042e03400c826070003110701000301d10300008214441d04c103c0c01000304401e01d03042c8501c41d00c2d40340c4400d0200500d02d800c4100100002201508aa5801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 570426241 1250 570424991 570424997
    0x6040b07050c190c14060a05090907120504030c0201020d181403071a180d050618030c030a0306080601091e020705070b270a0f2606010b0309010f0515010f 68
    0x51603126500d0000740d80c03043c01e0b030785800d624401700080511002d0100c1040010740d045410042c824001800e5070080640c41d0f4081d001200009665501c01d1115480c00030214100301f00078200307401c0c0280302c412030b110201d000d441020202071449024404c00307001c015030381c1c0945c40c5103030420140380740000354000c103c1d07054461840c000c505002901080100c400010040c0c03501d40030a1030003108040150b0303013094065000c90603210702181021441951180391400206074107d0401a054918425825240078900010544040d0030381d0580080d0100d07940c1c3c104803547c5980f540804011108c01284c040e5403a0008008611100042c2e0090301c0600d01420607940e070b0326643c05e010450756000300b0a03a0f002410300c180c482c02000d42d1078044500c140f016034010070003a003400d03080000c03803402d40983c19850f5110103100d80fa200b000181a418071101c2c030180c81c000e5a58420180854000341c03040079041d428512004e90043d43e40c411280b1030b4001e101141038031401080199202c0079800c0e011420 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 570427491 1250 570426241 570426253
    0x81009050c100203031b13050607020a0b04150806100203160f02060409050702061308040501050706061809150b150c030c06070f030c021528090303090c0806040b07050c 74
    0x1c0341e40d50003825441520b440e0051a80e03840c0c040c0c00d003145030307507041d01c4900c400105000214900e0b00820f441425140c2c162030190380d0b46880e00024505054a5000d20b107202c400107000b04081540d550b070001e02c0311044d145c0541075280c180402c6a14609580c100b001a1310500c44511a104000c9800003103d004041c4000240d6043c5c01088541d40075800c80f4010301e44820502140660401c000d507409642120000000c0000d5540e10b0158800c5104e10341c10400003140d040305001345540000d00a1107014000820054620018409004403120583c1c01c07112041c425190307048180140340b00e217000101000044020001d1a0020f0b4200070000071161100340700c003001c0c80b0002c205583c000d1801d03440700c001c108507004009094a045880d0324086420400744e03109040c1084503460f41101d01042d200385d04c14039040d40c1c241590310800b10103075030500740111181810341551014000c035010302c8078a002c2689070002c8030f68542040c0c80c000c1a0030310160001e11040d2160020704103150b00c01090310301c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 570428741 1250 570427491 570427513
    0x60c08160816030305060907020312040b06030f1504020a2306070f14160b07211107030f38270c0a0f060f030c0311040603021b01050108100905 63
    0x300e40d516403c90109a9070401d006492803c100c03455888140c0384001e502d030107034200014206600160004041d00000000b04405540500c20302d44280343c1d040847d40342c120400c00d000c0f0000410741e07050b8000c80709404086081c5c0d030003c03418100842c0030080c90841c0070104052040c0c42e4400c54042d0b0301414480a000001060184482129078003030300200242d0410038100b10024489610038200d0703140400081d00000d1810000c0b8122004d0b107908141507105140c8159210103d03100901814001e504000c8100024030403c4103206009505248006a40448054482d113481c107403907008a034039030b00421400c10070303c000c43e0303000c2055207200181940030210405030505000344da0303102d500b04440000e2241000c0104030300400c1003c2180091030710700f4201800200307800b1899410541c841f044030009500a810104005038444071881d40c560f51804014005d400128400c1a50314004218003a41601405039606903007110000d04150030414107000001c3c0a00c0002710307000d01604829070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 570429991 1250 570428741 570428767
    0x2040504050a05060606191103070c0303050a030c0504060c0b18120409050603030702012109080412150e03030a150f0308030702150f0a0218041104050406060c081608 73
    0x240a24803070300040c0a000001c1c038080f0f0411400030103440c01854180700f1a501c00c00d26044180c804051810400c4100120300190342c118030803110060030120070810000304042d440001403040080650f002c018110341e41000b211688650300c00c10000aa4454884000c92071000d80d00b50000f180b0310300703007403042c0c0f40441040c00d080780b0f84582c0542406c0403800b000400845d0085d11352258044018500d40f0303c09500180c00384031000d0f4800400d4050144100c0c1d03140640e48000545900510b40790740b6203030b440907070001040515004451030000f086d00c40c01e8909a0340a0b00260310444030103581566076a1080c00010042e84120000e05108094005840c0440b18410700240d030207200c00a90f40d02e800000030f850003103400398003a1200d0404080194507101c540d4401d400002c0c0d8400943c3d260340d81107010818400690310f00741c1c060b2501518071010101a0003e0040f00d1054500340107490f91800281d961885103c40901490390821085145240848411941501c11061503007060100444030b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 570431241 1250 570429991 570430001
    0x20f09041407020c0909033a050105100c05120915070c0e0603032b09051b10111e010207050703030309051c05070312110a0315140109061b0204 63
    0x800065511101484402c2e50b043c0441d4003800e00c1580c00800f581407040006550384946c02950030305921003040b4032502246100c0040c0710400c08108100080c00644064006040c280f00b014401ca42d81d48001280c64001c05115004a410201816001a4000007030300070f0b034044d0041350390042c1502c0e148001000e41d08013a00c3d4050086112412060600144007103203200078014074402e61040c001d48007401403400d02508036441d1000e00102c80603088032a07002a02059500502d103002c2c2180c07140b40c0071819240c4480388241160510400d501000040e144a00c1460440c20260410a40f420810030548085010041c0202c00180b5080701a202d86040680c690001c0f0300007502d43e034041062000403c040c00c1c084061100d103004101a90300050014450460020107205400784100800262603201511803e006000b4964a401841008005021206508507a40100343e404a107a151100c4016441c0e58103031109d40310386051210a0319001d01c0f44034421024801d4680f079030016100c50241c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 570432491 1250 570431241 570431261
    0x60e0603040b2a04050301050a0b03061b1b03190815120f010c050c0c0102030a051822020c011401030203071a0d0c09050906010f0e04200304081b0705030d03020f0904 73
    0xf0072a12030b41000101402d60f41c02070202c001c49030802c191304441ea40e02040d8541c010044041d1040e2002d68000b01c0c11550040004a1041044158201c010b01c14080000c02480d80c10980b0a2141d03a4aa86d00f51600d00090b0340503503070300d850241c00322190b050080c42d02c1d08112002048544aa5110804609480b02d084003c00064808108070904040c10800b2103910710090025509000c41c01b5070082550141400f0340c1d80b8101628032500720758490201c07940000076224803000e9a00108040031010354401c0001d44155841c1c984295101c00a2004e0075040c1c0307500401030809240380908000e040c4149161134884007008000c0e5800c101e042d0b1092900fa5242d03600c03503030b00c00d5181c801080098500181170303a05002000019200c03840d400124111020011200082c01403404641820b8202100e65100c4040c0400002e10060195850141c196113500c00306032000b5801d480742460302c90803180b141c00d40581c008000f90500502135000b400541e40e443e03548038108580e11000900307032012001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 570433741 1250 570432491 570432571
    0x3030d090c06080c030f060f210d090e130b2d010e0901020a0801061139100c0f020414070c0303061e18021b16060e0603040b 55
    0xd0704100080e08000750541c04400b034000305003149406000f2010380d4400a0500780709400c103c00c8040c0594801c090714401c403108503103503201c402200340c00c540c2e240d5080c52440003181c1e10709000a520000284000d10451091f845200c2d2041960340740c50704048042e248076842036024815203005800e4200d04140808814454100c5514041c018801014050144180f41c2d0040200c140c2c1c81d60892641811180c09140156151161441080c01c04540e00e20040d030225074500c1c0100f52149210320140b82461a22290064901d940304202000d4800c0101e00041540940302001045041d00d58003003150004d0004521004000b041c14140201221004046010401000c0c14980d240c030502e00580410b090030100c2026440368400400901e00c60901c40e0400380b8400f03070300b4142d86d40560700e000001d4540aa920510312140646480000e14590701041c0c48520004445116100c4071184000140c1640e19581359515044449140204062150040d054240149103600044201c108107244 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 570434991 1250 570433741 570433763
    0x20a03090807080a1b0f14031306030204090b030102091e040f021b0c09100e041406091b030c090a0203060a2304140c120a060302030115080d03200903030d09 69
    0x80d4005d00800a44800c124150441200550005407410215240d0a403c1a143e084680004904501e1842035201c050301c2e0910344200010201e800d40c010317200303030381102e02c0521a412141051500302c0c0a15000b455110310704001c1001e1280c41d40e82040c4c26030700081c101040700515032000b41c06980c0015800c1e201c500b5444001d00c10920280007151803101c0c204d624203180d040030000b003000040c060184210203103080b00410100b000003e000c003400100c4c0700c2500c0711840d0280c0c180791522a412a08440240b02ca05140c1103498082240b0801c4500280700044036203c00800c440290401807141d50005900e103130100c0e0f0087c800d000c281500c40403008414143c1c00500038401a510740c051080c90f00c024403424009400f149c4001e94410785a0314600a002c0c0c1d84604156000d0145588080d405510b0000a0140b00c01c49401c01008e40e40180c00716610983c03003001c101c088400039420b90a00c040280640c0c01c103000b00f04014804042c00400301c0342030040f040c40040c21905145403c50f1104845 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 570436241 1250 570434991 570435007
    0x80706091e0510170f04033b0a0302120601030c170307240908040f140f011b080f03070306140d02060a031e05060a0e0412031107060c080118090f0204020a0309080708 73
    0x80c1c059009020301444000c0e510144888d03503005189442d80c240410841510305a40640702e41e080c800044d81c00a1a1a0360192400e444a0300c40e0300a000542d03204840c0d00020030a16a4500100c0200e00e4100080d4a400303400d03180c182d000b41c00d6503d20703400702400005060300f4410a00420b042c1c0b60107403070210764891421130240880049648440d02401c0c10ba920064641c0d00c0114202040301e003801c0c042c820503141065091030241c0070100511408011a1550840c2140c1c00510300c180c0442d2030812041c3e44840d07091802c14540d52419078051030a020100040c00c1040103890101224200407415420901e0400c0103d404150b04061283e034802c104555464881c041500408500d2141e100c14280742d2121052aa09203144909040d110440780c1c82e025000d101f101d01035600494200202c0c0c3c0511030040c21000284111001c801c00c0d155209036a035510b2046020055120710400148000b070390a000181d0480c0180405050355821400c01040000000785070b550f200c1e41290340c2d20f15903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 570437491 1250 570436241 570436247
    0x27030a18170a020d05031204030f1b05100e0c031e060f0403051914072001050316030510080a051513021324080706091e0510170f0403 59
    0x4691150402030141c0c4030314207140001085410b24103805407030402d400445410100c2c658403420000c0d0043c41020b000b00414140d11804841d501480c60751201141d000440d448040d558040a002c0c1c4141c100361100a81c50380240d106d0002211107005442518112400007424080f10710300305010840c0000c02032040d9030090050580c07000006014082c18246a24000c2090040a1f03080360749850403004140005e000f180030030b0b800303800c400e0019542c40081c5059140d2501c1d070f4115404500d0107004405066003e03806a07482030081d440e02d41c183d188000022400303400d001d40b4200d002c00c07095101103202c01e401e10420061601910081c60754200d41c1a00200000c402007180d05490040b06c00d580040c0e4986000c0d03c00c562515a0201d0351040021a140300c1c00480900c14440303481c6000c001031641c0e004590201100e0301a107900b440c26580d2032285030144642103955071032110f000400d001c0d40ca060031019641c02114a805410071480300f0546085040999544030791405480401081541c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 570438741 1250 570437491 570437537
    0x200a02120c031e1e0a060501031505070309080d020703090e0c0408070f080309010c02010e090f15041e0518030706021314131d03181008090627030a 65
    0x11040302c4100084100001840e00d0b495184c080103d9000000030380c440b81202089001c1000b034101e0820042565a131600c8012042c042100c2c03a078403401c05000808890203841045181600a40410b00d041014407160b402503111400407014040c0b444004510780201d40c14180c072504040304216525810001c10300d151034243e5016600400003d0001e010241000c0181c1b01e803540b0070300b4180c4042500c2d10068a00008a410103130b04202a281003041c0c130002c80074000d018004071220341880c140c000c002e0209480040c9100401a117245004000c07c00c150740c03180d50710022422030011002d03a081040b17801c55022000544000e1b401040c0301d88401084592500203105400466000c0d01e610301c040b91181682c41c0d01c0d1901d8680c1e0701210303410034a81e40c01b5640101c41e41001d036603482005204514492201003000780c0107143d134000f400000ca0107212094081e14044008000b0b9a88200e250401c000703403040203003443d02e010040f03031041600c2000030303003540d86003915a1040341c2850035005040d11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 570439991 1250 570438741 570438763
    0xa1d06101502030901051e0325140304110103140405031e0408250f0608090114010e040b040213020d1e0c050f070204060302090f0414060106200a02120c03 68
    0x9854031041c10035a00002180e810a20a013841d940b14006121903040206600361205010b83d000800c02c42e0440401000200e02c4960405151408070381c5e001c1200e11100081c40c140d0745100400210303010880b002a0000c0301c4505240218000d4542d482c5010014016101106d659101203024034200c80310500f8440180030f41d0000302d040a140650950f42d030300800c1b1080c60904c1e010007105450408080400020f040400107082480b07581c5d08004295160854811555500e0160084841d9118a01480c1254200d01c600041621145c072088640403010340101c1c1e1102c084070134006510030f1400a0030442407500000601003100c52483c0c800350841d40b444e2104249803454801d0348540140c180ea8130200c403a001c0903150209032004c24000d08498001a6000c0903210402240034512507103a481180f0500c884a80941031548880d45c070301081c051840800d800702a850001c0100e81d01d0020b48410100440e20305070b055401081c1001c0e10340c18841120f8105c90382014040c1001c20903040c0107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 570441241 1250 570439991 570440009
    0x50301140f06010c05061f14060f0a0e041107021e0a061b0203070806010f0f050d030c0f02120609010b060c0607050a050d0507020606040b0405041101080a1d0610 71
    0x3420440c091500c00200148840d0580004001191407a44210402e06180b603002c8125145401d200c00390401300c110131880d401c140203d10101040c844000c2c2001c4003482e04c0034006604042c00200142c0c01d54100340316000801003154a0600d03656118024100d241030580c000341d54503040d900600006200507040e0b2440079800740707072801141e120681c0c2042114445d144c13000322504162074423070f01c500d50500b001e54144030300c030400b00d44090302040302c904031500c01e0b5031800d1071aa0303008031900101e9148a1150300624103800807021a00070316001d00202c0c4544851400480c00750b0002d4801205030098000036070018041081c0081b00344100620101c1c1156114240844503240b259512402000603003000303004118400303440c0c06101a07070901425400240714034580124000d580340301c2114614450344c00c0c08003184c0340f414184541ba0180c0c2d0040c0d09003001c401400e006540314100a002c24910503507c0090407404010601d000c40303c040140054090350914a0084040c14050303000400d003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 570442491 1250 570441241 570441251
    0x7052218020703091703160c140907020d05090a050d0b011401091a072d1703270712290906040b06010c0f0302030a1101050106020703060e030705071e050301 69
    0x800e0f0000c21303002c22144a864004c07445011224140d017103009010801ca01060130313031041001c00c1001341c49001500d5410411703a01c40a002c808212103d14161540c10240e0810a8186d604074802c400500c400b00c80500340ca40003c4e0f031140442e007601070610302910504002c200500580c5662201ca404100d42441c1c0a4a2a814130454800000a003149040c0381900000d58408104144030a103030b1aa0640485440c0d1900c0054100c04404900d04200c400f9403030030b0744c0503018a080c0d10a583c080e000804424000c0646000c0303c5000c801080f0030f030406442001c030001040f207002c400049415200f00f107650034a9416114803052f02440a0030030004000c0e2004200302c0d0750b4002142607100c2c1d00150305422503180c090069603100811000680b8000e424400d54003895000002007016051951318820301c1190405442d080390000e00514005130031541080000ca1036540000b8041a0f100040d00d203800d11541c4c0c0c7c0703480c212056101c40b14140c41070a110640e42664510000104403d40007800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 570443741 1250 570442491 570442493
    0x901030f0312060b04120f2a06020321091c02030a181a07060b04050c040503060a141303050f030a0c141602060313020d0b060415081005070522180207 66
    0x40d1328007941c040d0307074101003040c207026082c07001650b99111440c1d003044d09981d25180303002980800c80c9500b040d01503038102c0540000384c2c5074400002c4408940c5c07900d403891035160f0010605d02911202526001e0184117141c40703031150041e026940030f1202a650011030750f4a44884018282d90303824584800311102c2d0350b9040002c480040c8000040048050019aa419241ca00340c0e000f001c0042006410518041c00c100200c08504010b00aa41084045408641d43c6108000a69400201c141c0000b40c0311000710305409040358114583cce41c0704c3d0919500f01f5204a0b041c1956400417158104c0c01e42d2900742c1c6503240d13a00b06040900307022806440503e095021000da031541003400c0002800f6000000c00541100021220350b140d19900031b10848000ea4242000c100d840002c2d40d0140c0705514201c0c82c03507002d22282c104081244d0030480940460180c032104000200001007500060040070413501c4842c6a2107000e20b602c058550250901050400059010b040010b41407200c025204102c07040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 570444991 1250 570443741 570443759
    0x90a0c030b150d0e122106040513020f010e06070b0708100f0e220b010311060405011b05030c0706020604050601150503150f061209100501120807020f0901030f031206 73
    0x83c40410400d10081405405040c43c80d00d01080d0049400340c18001140341030b4100111800c050003000350540040700303911098200720407128162503040e04629881203040060401041801c01e01c2c40504002c00481750701c3c800302d100395021643c02ca8030940010308002c080da411084440d04000c0c1c00710390781012403c00b0f024140c440b41a015600780301080c0c400280e2400c0016004201e41000761030221885240c031319014080010a002c2100c040c80ba40c6014825801c141c419038044410580d1012140d1003401c101d8401c0c18030360300081e01c841c002000090041202040400000c0c106a401802285090f0409504041c810b030007042c1007079244007041c0b00c101d034003100f0f50b5000343e00f42e89100d440c00355250003d81b1004000003010f030850f20120f852090803041590403881141e41c074081d5240007001e00c5c1100202c8d0000d006a48030210060340c0000410318080250258034800342040e00c81e510a1400542091401d034000c13035502c0c0d1360b02c1720801055030200c0a5008102422401d005490500c1c1c3c42c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 570446241 1250 570444991 570444997
    0x5030301140a05060d0b0102010c0518090a0e01050702030705010c0503160e0a08060c090406172805010212190b010f0f02010b06030a060e07050f070b04050309090a0c030b15 76
    0x81c1c941c8030300845401505545201400005207030083c1803a65824039408510083c1c00c000981c039015529140c0704d00002802030b000c849650741e88022022a40e512601005480000070304404c40080d5500c9599060706000d12400f406140e090300290b84401a0345465401c1d07401003880201000f00034010b028600b07140c030348203045c05141c509103501c00b030a005010601c221794542c01100d0030b1081109116015030418003c048418042d070701403128a407920125001c4943c2c0c00180c80341e41d8401d040402e00c0ca400c0c200d03401060720300f03404860703620b1400b9120309003aa003200001c0d90900c4000814030146250510340600c00306e555042c24404c5043c4100064500203a10220f0001c0c00192008048114400c1d4450300328880000c0c00281c5034100b03c143c200040c241c0d07014211602010742c0114a241c3d00502c156548081c80c40301c4a031500f1100e5079894000c442c050000c481e944802c0c42481869034410a42610504000f4000510040308400040075100c1e558aa1400b4200c070340154116500c1030412 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 570447491 1250 570446241 570446249
    0x11818060e0a0c061403010515070c061119080901050c07090203090606040e1b01080718080606010239010e1c021e0315060315040605091c204605030301 67
    0x1181c1c600c023001c0c803c00c89c0611800800800244880a01064103500506150b1017492200e080392500c0c1403441d004484c44c100e144002c1c044080901a01805c1d6119000818048a01000361984246e40b0b0500500f030341c005031007100e542c1e08003c0070130100d0704062040f80d034943c3e1240300911038094034085c5400e10351400702c1c0b00c40c104140701e0300295060313000751341082d00e12200c81d50710124a683d865140ea04c80b042510b455006000c0c1c1c44503da18501c480b500c4807804c00e01c1420340d00341000165292062403906105460500c20070600c054440e41d62901b201840e41480414180d51801502c1003160800c52202108036400307000030b00310313a00d840006009483d02c080c0140d4030796035103c000c0001d02c0d0120b680381180344105035400304400c1104640080b406080da400840b884240540d5019115081d80c015410000c0c610924140c12583c5404846440c14a80c405440c07400c1401c1068803001070100c515607102c0e440340d003050f0000550b4070301908144001190040c50b0160310341c1d0303243d07120304c41849 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 570448741 1250 570447491 570447499
    0x403031e0b06031308040f0b0415020102090a12030201140a050603010b010513060305060d0203120c0c01030504020d0f03090b03090115080703020f090a020910110114011818060e0a0c0614030105 85
    0x321360800591904440241c54880c41400d40c40769566012200c66202340600314214032140d40a101040c014001d850071003200401c03001075079003440038250400f521044203804646d2204c480c101a03a17072181d42a07000d6030420b000842c40b464100d0034542074402c0c68452504224040050100301d80e180e1401c036003910ba417840c02103101d0300c0d07000000d9004206140007035070500404540c01c0784c1c254a00000c196283d4800203484a03500b03030310019800c59008440194011820b10107040009450100a0b03c5844c428188400002c0e158181c4008903081280ea404441e03651b02d000843d50b1611038411001040ba08006090701411580419071410041404501403c910310220b8000c48250f01540c01105001c3c0c80113841d010350040c01002c980c58203007120081e500c6d015504409101c1e1105042c1a90100120b03440d1034070088040303600806000c0c2050b080c034004031802d43c00003000390003100c1a000c2104002c0280041d1030800d58981c40f42c80e0b00500a000c0229424248030b44607034262411188229 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 570449991 1250 570448741 570448771
    0x111030703230f010b0a020721021e06090603070512010308210108210403051b040b060306030a0b070201060b07060504030813050a0303020a091d1005030d050405150f030403031e0b0603 81
    0x109038035008d045d80140004c3e00b0f0240c0040900b1f000a05852030281c02110200c904034036410100e0f03c481000f261a80d0408000c01c0303440b00e01c3c14100c0056800810702e1401904e0b0180d18000b02001580c05e0300f04a81e81e0800107a242c080c5c0d01c95001212003450300c40c000c520750b0352419242c0340d9a10150f1004c4020f01b80d560440700f401103144810b60b4021600a420745a40011400241c031080040c212814402e40c41d04d14828900d0400c42c0c02d0364401d2001500410404035a03440e80d20061500500700d40071903403a40c0c1c01042028420001d80200d40c40b0f100041140c0c1860f07d0f01801d001d50041040c0e050340e461404040111b40c000694000e0305405042c0166107006056044500840ca90404800214080b141d2144401c038454031600c52040115042c0c421034440b0209610350386d18400c8100020b205002c14441854030700d01c052150041041844e1400031820964240c1d500125400c1c1d0100fa0f5422012941c407030300d0b2400e04102e507007401d000c204411036170000032104c3c0000307040303c8030802000d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 570451241 1250 570449991 570450007
    0x30b060a08030a090602011401030f020f0f04060e18010e15090c060f0904052409090f010e070e1f031509063602090f04050111030703230f010b 63
    0x1100320101600c408002e4903600c0b1041c160140c0284400e00c03d502c010b61030300c0c1030354559501d0300c540c0078180e07a84001c04242101e900c0c0c00f046841c03103210010a5100c03580510324840c5560314420400100751a1018039501e103030403c00202c042c041c00c405680140d0411101c50000040421100b6800407114080311083c2c0f5200d074510301e00714032071828603081140003800c1a809445a03002d49517100003114148045d642d00080211810411180e10182d0104000c0c010103515280798040d030310803200002c86d07202c0e0207520480360075905140c10004064101202c01d0200b1401aa040b590044035503900d07490740150003013124010040c521018001181c480520040322a581c0c020780c014a4001c601823283c100300301058810300714048400d020041161148001d0035440314862208540c0080c0880f0f030640c0c81035000742901d40002e2044440c4c0d5a00d5030450004140c00018501400c91954009601d6184102c3c50b140301e50081c03507040d80b0300f201000700040d44069136030160548a8202a0315103c43c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 570452491 1250 570451241 570451249
    0x810030c0e0705090301090f050d02011506050903011509140106052a010b0a0303090807170705060f0706090c0603060503032d09030f03031f0810270c08061f030b06 72
    0xca044c0e01d5819420640220140041c0562502116000308241c0d89002501c00040c2d0880380c0920149410301a401c1c001c106190050b0058504018040e0000c14890805000f1240f40e000782d8204064040c1d4509141c0604c6007820110345c00341c8002d0030000d141c82d1820704100381c2aa42d13000c0c100d052034481580d5200c101c20070740282c003260b00003a1090754150b4032445c010700701b52614024003005201d1400000351038403540b421041c0f03840414001d05816030420781444081c1d480540310840291040181d4000981c45101d0034110b40d000b8004a9481c900704940141034511079488a0301c01c0e80280034562034050391004240f141224140303840d00c8a40305114415850083e105030b183e060141055154403141c0200045205600034208414130328004480d11003450318500641d5113981c803c296851007030b111903012400c1450703195180301010401d06581444c84040700800c4403400017280c02000489000c0100c103401c50802c0b5501d095210710030070807a01d100e41d14030000c0c00034200c05000c50306d591a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 570453741 1250 570452491 570452497
    0x22080303150a03140f1b0d0f060605270a0c1205070e0301112a03030718090c0f12050105030a081804140f06040c1209021305090d0810030c0e0705 64
    0x141c451841c2c1c04000081d00c10307646801640318003501c41d003e13103a41c1c0c0090340c070b200c41b4600c050b900082990340d84401d2601d07640515202480229507007652500003040e26559095030040b00024000244107110581040c159450b030042c20407280385083c1003c4950168111a40f03581303009054200080944c0c8040040340c00c40078446880b42c25518040980c50350002d903000508018401116410842c04c07020b110544000210000d62150f4005202085045101d104c0711011940d60b160f029401e0794482c050315044542400301074000c103051500003094160414810035005a00b00810030081d03244c600443d49036600e0a800070304042d400900d02001c03510004815040c52000b9104010050f004080022215000c1d644010b09040000010341d59140c603005903482d8800e00e070344002c0d00d20402030761b000240c0314491301282d2014240041510ba02414800d05228101c0000102007050200d60083c001007009080b1041c0d5103907402052000c1980e2501d40821141c075008400c505503130b0540c040392140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 570454991 1250 570453741 570453743
    0x1605090409170d0b150f0721110d08100512161401020609010b01020703030804081e0a03110c0a030509060d0f06141e0f12011122080303150a03 63
    0x90096001d4042501c08201a00070440301683c10001d0a03006030030455614112480c0201c591000c01801c0300060709500980b00300da1044107240840c001e5000d02c034110700781c0081c19000182186803007070a100b90400001a1640140c1451001400e040d0103080640905000c0c0c140210060009207200309800c01c0707401001c4e01d046d115054695100c0d0000000d00c0b900b030900e00c1c0103120b10300118200038410b1291181201050b002404840c2c9150750070340d80c89800903c107580c6000280b0002600407880d007007406070503d013110341598912411034090220b58107074070081c4540609000c8040c10043c006001000c494060800d23580f66246070780010b010344240d820780b985007410021504401c0c06240c218074203481c0c80c40f40188030700d0210030500203503028600c03090070034051000a00e01c10b424890844030406c0c03c0600134503485811070b0b001500395542c041d0b0416403080d0000e080d0711851201c0407044054501982c03101d20862502c45950790304d01010381090088501030000041d181c1d100e0344690300039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 570456241 1250 570454991 570455003
    0x20a110708030c070501091202150c0610050910083f040812030f04060f020c0f0703120c0c17010b0901140108090f0d0e04020c2b02061605090409 64
    0x6900e5080340c81e2a43c211072801d420798401d8041c040380746d40c01100c60f00d042e07914199500c501a4803c1e020082d0840101d8608a0050f10030808516071080a00c0421f129034560490aa0744600d0300302400541207008141c0c00d0300800144060101c4030001c070b0350b00354104920348400c003c8520034240c01840140c566203c980e2042e1030849403c50f500325030181c0200c070b16480a03103418910b800210981071004444809141c1174900001d00000c2141e4030080501c8003040c401401c2440c04444140740050b0101001000e0f4000003080042002d440c06c21001500545490454807900c2d954402800384c080c000d0700d101e00c034814010a40c0c032100b5880324600c094000c02c101a5565107074450703103600300c004e040c2a00240e032100000f4581c410014002d134003a600c40c00240680d144d0b0f08400c494010f000000503074410f4082284884102c800c000c905c007140c02d62403440c0c0440324040d1565000b0304070540c0000554200108200c011170211000d5500c44109003003190380d0b0020f10000030002c12090000501e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 570457491 1250 570456241 570456253
    0xb2d070317060603060d020103020d0f02342f090a0f05090d090b0a0e09010906170a050706080711070e070306060302041809020607060204030b060906100e0103020a11 73
    0x34594040c0c006460819070010001040e110b0300240300c528407040b614640c011218030805001944a50b000300065050241d001800c1141d4908181c183d0380140341c034410115218441003404000040010701c000506600d02840c6041d599801700c901c0c05400c1404102d400325100149044032204050760301d10310060a4561516103208014000c28030002022071007890500010303501100000c5070514a5240c1d10740c3c0004034948030022017542e0180380100100584810701d055641c0316000b845001e4a81c0000119a0505003400c0d50041e0071a030151030a150300441c542c4000c118040b40c010300744c810b58607005c001c5035101e220580f101d00c10700c8090341003886240d50010f03070710b00c010f0103041c0a90340c60380e806d01005a45010803400c1e0302840c007a01c42400710b803003a0103001c003000e5400300750b019101400e140c0c10181c0a80301c40003241c11541c820303510318008400300520f901c0c029078025484081161040505002040e009210f00f241c083d209050503400140c1e8030f01c15015801c1035144003d21030071644 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 570458741 1250 570457491 570457493
    0x30b0a050301091e150c0305040b06120a0803090313080f12161101051b0a0c0503031213051c02030711090906181c09180c0c080904020f070809030708070b2d07 70
    0x1444109d0b0203480d40d43d40c810110754285050740317600d410f844181000b814800b0741030b04e41180a40c0041c00318a86844208040e2000c034080e502030301c00a20102c0e018000d034104a01e42c0500300310032106c0098000d1000c00041450300ca280880404481d000810240b01071042d00c0141e030f03c0c0c0709008918045441c000c80030003800c00009043c2c88001c1c494291254040c1d61001031640d01e000701c07054000d51545c06400511104245a8040012401403040310301c02c8001c0f15030751064150700181c80c7d0040c1c00020b1100240110380320360000e60b15054600c500d0300d10744404459141c440c00f0f04048001e01180f803c5a040640c100000710190741041c2c0054501c071265030300038000c1407080c0315441000c02c0b221070b0140c3c2e03c1020301c00c0344141c50a68507160f400403080e6465600750752203001c049600503400e0084407603502c0104040c00c10244540c8649a80e409000c0c00c05140c96142c3d07004c0c03142d03644096000c0c481c00c4502001d440210616850101090006003403d640d481c980000c0680b000c0c40c045403240c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 570459991 1250 570458741 570458747
    0x30f030d06150f050f27130b0f0409260a1b02010c02012f031803010902090613140c0405041a060f130e07030506090106080708060909160303030b0a050301091e150c 72
    0x20b18046403040447c10f14404400b003a11501c072180d03540320800860490150502e504004d00c0b440c070848085d50180d075030240004c0344006600448456080208010030283d8001d4008104110700d02c05240048200350b00003450421f003080c000b07041207240030102011140b82d801d00c501d4048400d0706a0082280e4030031081d600d400ca18462004060f0300c3c80c4c1003190b41018800d0008454006c0c200414560f42c050a100600c1d0150100c20f0440d903483d11298956080c18403c180a81e5604805581d81c40c6484208015030302e0348102c88020340c80409003001c0350b035a804100c484903c8002e00c0c003510782c0d200d0181213003250142d502c6080758403030410400030307078070344c59405107229440444034000280d896180488144204440420200710440040f800340d240c607244803070b801107103601198996585040da240b585040c0d94001c07030110b601c07035240704260710b4102c00707a001410003030b8000c00000c54140c8a150000c4007065045c0700107034000f2142c0702400001480110b0316401c2ca5403e003d034200182d401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 570461241 1250 570459991 570460057
    0x903020d11010c0f0845030a120201140a0e1f0e0114010e0f0f040318030f0506070324032603150a0515190905030f030d06150f050f 58
    0x8510041079400342c8000040c610740d5000d4580801d00031103021b03181c44c0e40d81e448103a20f1420440e50601c150b140040000d00343c62400300c4200e509900200e40140440000c04074000017910340d03035070366003400142c9415002c00140c005044ca4452410700c0180a000e4009000f41034250941483e5400c0c100952040301195054a04803074100c140345000381d49811041d58810000d6a8000e1518142d6000c81d012030311070090503c840881c0d40403640160f50b070365206490380340302080484494024500700440e0940600c5506c04091444c241200031042c2e004a645011078540030040698201d0810540720300440342c100c5008009038405c0341c2c0d8038200310010440c0a03048404c82403190484000200385030030403801c04040f92101480440c2003151080c021000c00301c141040e0b6007041000300d0005002d94041106504429200c80510f68500c521030172042581c0c0c440c0c0169068101154984844540c00071005088440b50320b051a15080751100140451290007071503600c0a811580304846180303030200c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 570462491 1250 570461241 570461257
    0x20609221419020c0a0308060105090d0609140d0c0321020a1d030c010903020904210e0103050a0507050a0f02102d0902061605010b150301150903020d11010c0f08 71
    0x205620b801c03038054100240d03c80c071001d040c850f400520500d00080e024060ba29048841410000e0500a00724041914400c5036101900d150343c40348543c4091000d46034407079091004400251060380da15420181c0b0f0207503050401400c20800070a030000545c2c002d10000c007a1444440f066584038007804005000305000090072415404440c440d5100741760010b80d4102c243c1c07040c3c4540150300e00d1502004808103008105442a200000104e800c0286122070a200358026484492180c910ba0000408840c0010880c0e1011807a02c001d04c1a000e1b0020b0549140c4c0d020ba1910b1403121444030400c80c2800000304041c04c0403800c24a19000c01c2001305038080515440c04100c003607003140d8400c0c01d0309031000310f00d0203500328004008404e040c101251403210458064070000c500c480300b9002003a050200c401c403601c840b501c0800103204501403000f0384810712480c0c1c80d0003c50a415500010f12540295030010a54850203170140503030790290007100203082d007040b02814125418184102141e00100d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 570463741 1250 570462491 570462511
    0x90d0c0f060612140a03081501031805010606090915090e1e03030103120201140402190803120105030114010803190905061b0f07080a0f0503120411040f090206092214 73
    0x4a10703130305201c0004904110a80684d40c4000949a8080107888052480f80307550400d81c4400d980c44036644a209104441da03c1000002030051400f040102140a20b80200314403a041150254915100c1003112065402c0b5070400500c3c507441001c03880c50304040c88052a0750020b00403070b84100c004044041e40c100d900a00d82807907400c0030140d040f400c850341d6a00706014102528041005424101f0a1206400b413041d040003a076910383d0000380c516004150314000030030158005005c03905082c019503a1035052403841e026254103141d055500d80c01020464980000c1c80910b8a0507144558032607401070034080d02c82c1d030f91489159a0031031803100380d500005a6215a106440840d10000381d040120b82c2400050320525906989584c001e05034000155624031060081c1e11244442c4d0101500032486180c1d00520364080700244019550302e02c1e680d00996140542c01005619040c0448262010894041c81e05d000c44c803170541208003502d9600505145040d0106000640d014889401160748070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 570464991 1250 570463741 570463763
    0x1f120b09010b0406051e0a181d060601050a0302030c04090606180f060e090c0c011d0105010b120c090d200307120305121504090605060117090d0c0f060612 68
    0x24062105540452003840e40081c01c10302c0000066000d00d4808489486c002e1003495501d954003180301900c1e00c448054290303035981e4183d018031032541c5004001e400414030060843d5141900000c0d00501803280f210051640000000c0c800c0c1e0054030032613000d800c072510b01700f1146495240c0101440f205041303c0c90f00715203e40011580304040e00368102200e0b985d83d151440d45801e24144006140040d165454001c01484505100c0c1400c1c02040103444210440340840403a600389982540c50680c03081304510810407000e041d07003c070b0703010b866400080306101c56a1aa400c0c00801c181070f2243d840a40740c00e440780b81c4119a01042c0c41603804188040b01118076480c1c64101901d800b42002c90001c01258042120544400c0d440c0f100e90307400b004600d000440708240d02c010405079901800200d41d00790350b42040181568101e41541440303035100c844d0080702e181541c1c8440c1d54821095120007031200c03405120040008a9020102041d03002c00140071403075130307201d00300071081904000300e0b0382c00401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 570466241 1250 570464991 570465011
    0x70c1d0906040b070f020106030204060608060307141e0f1e03010b0603060d0326040f0309090506130e030405040e06220b1f1212030b12061f120b0901 66
    0x1081c0740507030f8006407100390395211004290f07030280f4024070550540d5254440000075076aa4420400246469107621140e46801402c060a011080d044441e109200c0701640c0380075140d501b1001c20040d0303840c031143c4040080030001a4016148501c81d98840ca131400c0e4105052080c042030456020107500901c078542070f02c4108919030004940440d08030340490061030129116041d2101c00c640c1d90f09884e20748103415003281ca060401142c0907640110390900c1c0c1ca0801d81d00507070310002410041c0080002e17042c034500044021100001143e921a12120094900032090007194020718005104100c000c0c0304132401c40d10b680301162800f01075501c08031045081402c0307012000810f03030b00403450300f03142c2c1c0c5a0480c400440b01b1080c0140081d507003030102003008180d0390a0080098000c0c0420310307480030000c04c01400e039840d00b004d1034080c12980b44021007030709000880d40c0c0c10243c0c000c0340000032140d000c83c1900c3c0c0f42035540642d10500310641028240f006803003250b8082c125944c020711103103002c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 570467491 1250 570466241 570466243
    0x402040e031615201e0307050909060136080118330c0507061e06170304060e030a0204021c06050609100503070e06030108071409010e0f0c070c1d09 65
    0x40e0700c51440c0d480c2201001040d9a0b600100a204401c1c170210201100500c90500700042e40003225480046540002c1042440c940f20f50000e80c050000d287c154001c1c0d40c0c42c4444403440155008074801c1080c64240e603184401e0080300724001c0d105450080043c80d51002c5034034800205180e0642e0540e4503c3c0d03400d05200b06601082000d21011401200d10182540310880104004084901000402d006100000300e49000700b001c4000480341e0389100202c0310303030a00120750300e43d800700d1380d2803403000d0b1010b505040100c10b0320304581e042d040c00724440b100d29000ca4201403440b5002584144009840143c5900007183c200080060701000c00007151a90300f40705480c0700c1c40c200745034000140040700900c01d00c00d1009541c0b1909602c0c00c0901080c8101c04201d59800070780100b58650480c0c0d10a110000701461540300700d000850700710310194541b80c1f000c64069400380c542c101200d158800581007032002c100b1108460782c0140a46100389c1c0d039019420440c800000300d02ca5603044e03000030441000c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 570468741 1250 570467491 570467501
    0x103050c09090105011202070602030c03040b07170613090503130e090109030e090630010f021206120708030d15080c10051b0f0f0c09040302150402040e031615 70
    0x10242c030280c803603420b150040d00c8890310184096030480c6c081001400080b81d03800a5801811040c034059101c0c00c0918210b0100c0c1002001c01040222000c218812012004281600044281e80d84e4015035084412003020707001601000e4218440050381080002c0810142d030700715044400e06e069151a4030145500360303801858081d00048002480106070303d0b080c0c0c0340780c0e00207200500d01c04185a440307507980c500151001c07120800300c52030900c41803030030000e004031030400954031030441ca4015003a502440000000d0080d07802366011b103081c0c2418000c204841c04c06040468201d941b510003500c040c4028050311000075011502803c80024210781c0000c880703251420060108090a025200c2280e15400101951810200703420912048680500c412038417510240c0c01b6060310391582441628210119050340d0051852404000109074041a0310b08043c210042680340ca44850002030041c1583c031071040210b010003d0112200c00340c0704101d00c101407190300c0700080040d4110f0044120b87d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 570469991 1250 570468741 570468757
    0x12320a021509151023010806060901090b030a0e06040b15010804022d040e07151707030c020109020a060f020f0102040b040b2d040603050108010213091505120703020103050c 76
    0x15002801000c001005140f540e42d0001d500a6440c900030f0b035504500a21492101c101d00038208100303016800c55a00c8a2090b034030007001e40b0001e00d0300c030036000001c06a01e0a0321070002e044001102251543c14650004907009030070302e080b0f4009040909010f44030407815a06a80d2071106514000f0f499405140ba4512071900248244003070f0410440390382c1800340f040000307441217041c50588102540c891180000401c0017000401507503050205506201c07003107108050500c180150040000ea89040e100c03584000c5529010800f605014421b03409030407203000c003d501c61000c410200b103060f80584601290b00d5140d00301d6a8910300c4020050803407141d4058145859402c00c01807050400c42001010b2491150100d810148800b107c01c40109039400360380c003010f0b04001410007429030f00d80030703850251800c3c0000b10718110f0038882200030300c400d5202d00c000041e00c4549000424029402d64001008060b01d0b081c1170480c030f095819256501c41c0412400302c1c0c680400b1440f0080620280c070340c44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 570471241 1250 570469991 570469993
    0x601180e2406040e10020406020f060c0a0f120617060f2e0801021206120d120b06070203060109050a110702031b22020406090e0412320a021509 63
    0x1003008a0201604071100818003500251110020a0103031410450035081700300e607500c01a1142d05090009082c1101c1010b900784503031185051041aa241100b15030348040b1a061035001460074803415241b13240c54807480043c00c1c2c5030650000300c8103406116000d000780f040f42580d48541c0ca045c00304046100507210b0340c00089888254080b0a181c60240d40c3d00158121880c1c1100c40d036030081c05003a03034862003800b4420f00445080c03001a0803d20704110a00380050b01601d56078000280091000b85400e6045055a841c2c0d03031854000c0d10340394110342c003a40e009016071314290307103074600000503010a5941900c09440c0c50b4420a4410201c01a50301040d40100a45a008401c90003801905000c00c407a903403000100510b020209000b1a01d0082030098002c00750301d85141010180210038964000100c0b18001003c11000554144207042d50103018181030003605443d65480170300d401c107640010000d00c860741c18845500084000f410002203140c1c2215a019085120086200700075203180d001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 570472491 1250 570471241 570471283
    0x20c1c18090c1709010204210528022d0a14090601140703030b0906040903120f0e010e010207110a21020105070c030b0a05090c01090303120b030601180e 67
    0x30078091504405080241850b2210701c4400801201da00a0300588003140c840c0c3d8000b408201c00d0101542900c010f601c00c202c00c403015200b0341c80322030320b81070741611494040001c800c00c00414880000902059034000e0480d807060028070f403048000343e210100b403d15404000c6803464003464408184015540c0820b8420381103881c3d0028040310f040017030030240c1408a082c003a008040000c40282c0a41402070342c012500c40c2c41c143c203105403488050a15402503003814040d1004c2608600e1008011441c8800060401801040e200003003240012402c01942030101602c2d84c030350150042c140d4140202c1d5182e02e403130070010030000d8160f0580300f6809452542c0f20035401e08598103e420100f2401810220310f08141d0b0303545c205060b8002e400c100c0b1070304940820701806c003800380b28465000b04408014140d20341b9410000e04481c5062100408000e03004110b495002150703006180c4009024003124100d50f1284a40c01f480c1246889840e8001d180440340380c0f51260000702920014084068042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 570473741 1250 570472491 570472499
    0x190203011206050402130203040f11100815010905130c081f031b0b0304140118170901020f100501030201110c01121a09071110090c09090c09020c1c18 66
    0xc003902c0004c0040c0d0b846180b1a07420b550080b01340c0015072045100b440540b140c024030385003000c60710440d0820381c0d005881a142da2510281c2200c092600501c42d42c080c0608406038500480300c0c102c407508541d0b0040c0d61000d00860000403a08814250030300e5450768170285e55840c10414142000450a041c103a100b14800c0000c10402c0040d0101155025182c001154541c440186998030684080760581c1106001018101082c4140441c544184117085500a8292200740700d9800300c2d5200c1c1480600018540d01507030003004010781003140d0343c081d80d00202d10802c90f00c000b0a002d200c00d0f800700740600071000f101d600104541f580064161158542e070303a90204440024041d2144040c40c3d8201e440700b20a66a60b02e40780c00d8410b20295403890510301c000c1315541c0c2406000703c001e016050610b0940e00c0090603065010060f100030300f00000700b40b1100c0c10490149175071603110268052002818120f070b01d2002c512000c12000807000d40b69402d11100c01103c05240616619002080e030740e100340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 570474991 1250 570473741 570473753
    0x50901110c0d030f12090503030610110c13020d0f05040c0f08030a080a061e061803080708090105090901030803040c0605090616170d0e100501080303040b1b0a03051902030112 77
    0x641680501c0c068900f08205c0c40c1400854450b0325095600368004800c200340c9d490000c1c03001001410701c1c5010710415010580d400d40e83c0712011401e91280305824040c2c041088540c1c15100ca21440000510100c0b035965000c40040206031402e40b48420008000306005144021880c1100c1e18103000710b14042e00b1210440b0509000b41109601585a00c000181041c80c09410190010b1041410800a241c0b4002034600c03030b074894a00c0c0314443c4c12682000801c80074000d0300c2a01c0d030413800e0300c0e56440024004079203a00c01e03c260190300c0408440003100b030001860165110700d104e4400d0801c03103074403540c091707900b809411031550b030005d020400201400d540c04d05100b000d500c68491007491101da840590381c0c030740081626441441d5100d1104c54008001c1040b08440d44000b082040594141004c591322480f006102030212241d0001080000100101c3e01c10415520035440340c403103150010060203400700b5030760350720000d41092203c00410700c90710881c2c1c12100454200610a000e0317640d86 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 570476241 1250 570474991 570475007
    0xd0227040c05250c140901050a0f05010309080c070602060403080a061a0c0703060e1f0905060402090c0d020d0519060501050901030906060f03030c0209070c11060c0a060c050901110c0d03 82
    0x900d6950f82c8141c5003000945200d4046000d0405950321115a1004505011582405070b202a1007251009020040040100d0190040e61070a280c0424030104a0030721700c000b4070403800c100110780301d812400510f9503408600180114425a00c4500d25115281100250f400754001c100c80c4d44040040800b44040000051116005480c10b417032015689403a0541100c01242001d141a0080c100f0200000280030664070b0f1454279480070020603a145d1106c59442c8801017000303000d054000d0208401d601442c041d031702d0f071008080003951b81c0c2d00c240701000c000d482e0035144589412803040803012600418080c40c0c003070350410b944a0b030411100c000110041c11460b0403e4030103542d60300d00451400c10300c0c10340b48040e600079114004000c9080c8107100014000a02c10030411102040c0000000c60803040100c0c522821940d054840700040c0905080c14400c6170020505468139100c200c005400030054820482c00362036030710844445580454a441420900c95440441b19a261000034001c00750 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 570477491 1250 570476241 570476287
    0xe0f1501030f1a0a060201021207030504020105070501020703050a030509060910150e011706090f0a0204020d0f0c0c02030c120309040518070902031b16170d0227040c05 74
    0x2000c6091000c0d0b404981c112031030010702d4030f8400d81e55000e440a03800e0814440000340064402145011507102e2400e181540181c42d80b030805448034040340c150380c07007103080d505000d801c04021503880740c1c41c0c940039105a22040011021070704000000b04120804076582d4440c1030780c3c4001e0021402c0040c8100020100d92041580e035901e03a490115039a400181c2490207480d55003e540e250220000d18289064401400101d042d808068075070000e090200b00410400d606490150702c40c42c100c4001800f4203400c0010384e1105113404600184507610004410142e0700070303010765507138135460307800c1c0114a01000400c0b0199401000ba03a1003904240c1c0c00264080000c8800484000c2012401c07414a003540d405031113046d80200034400c3c00100904020741401c28071018502e0042c034070000c42c80d41800304001401a05e07002c2c0f8034403a00f80d00c0b4000c41d0000401c6003011540c0700454110f10b5091918103d00081204142710b07489142d0030144a00710003c002c80d01d0b42d500f8458150356031543e050704040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 570478741 1250 570477491 570477497
    0x9011d19170f040e101208130e09210301080a02060d06050a06180501080f2706070f090503070b03060d06090209040602040e0708040b01060e06130e0702070e0f1501 72
    0x141d00c090040c0800c44041c821031565107280c036182803286440600010740c800f8001c0403c1145546441d042e02005611400c4541c980300c0504640c460152151302660000841d1400c11100701030210342c07050b2044901044040000c1000d0800016000034000c0340c02c2984808041009894502c01810020720514008103003203441e03001042d1809d1440d071002006c03440c82000c034110041100f0007100604020b01c3c1918840c80c1411519010607400b80c0403c500c105400c01502c00e1b0106400da8849040e00300040b9100ca091100c4c00404040c0c0070b0003c0070014078a040041610300e408101c01c070803201804091130858840c40f04011010000f000c1c2240c90070355030100400180c0f41c0a0000e882903000b140016200c601c7d012020700380d40c00041980040180f88010000051006a1049d0640384180390038500802040082201445100c038804030051860780b00183d03045941e80550b11032455542a15001681e4a03200d0302882001d0743d40101c4420098009a04060301c0440740c0850380e4145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 570479991 1250 570478741 570478763
    0x150b1f022a030d0914061b0f03030402011106041203020c10060f150206010e04060b030a05060103060515040b01020a14070b0f03090f1621150b011d0303031501020703020a090509011d19 81
    0x1d021f0501d050f004a0000285401c0842004195a00700401e080d00564000c041c18081c80d2582d1000c89840240481c80c0605a011840b0b14042c0f80c100040d00c50184140c80401180340c075101a0303688250b451003500e20f101c1c3e1080d88491540d2001c0749450403104ea0782d000c00111f407100d640f070501070469510321340d416100b030041c88008500d042143d10300031030081c5000503440c1000c000008200303980c0007040c4c2c0100c0c00c0c018030030010303603002901c40e0b0707510b03007100b1071013042c050422080e4104070643c0e00c4580c1e25103000c209020300c0d002e41170055018880300d404542081c0380280c8660f483d004584103551042c80b943e02c04108281021403940c8080c800c170b06194801048541d10035008201c415980682240e8540c00002d075560003491082c005c0590a50b0511b01c11468800030369680b200030715007044030309041d0b8a21175590080024401030342e40241101241c0e91184002c3c4003c00d01154918525030030f1804109038145d00e280001c41240006024200e40703e40c01a01400d000383c26242100c0090b052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 570481241 1250 570479991 570480037
    0x609010302210403020706080f0a091509033603030c1e0609060501270908190f03140c0d0e07080304090207150b1f022a030d091406 58
    0x450005041c0d4000c0b4030144450781001d041c024a010500d42107070701800011401c1c001c04004039110030303902045100d00899150224a401444000004405c2181c02d042a2602d0304060700640d5400e06220101100074003205880039044041c00340d4440d00c01c5203000c0318401e0004c60300c40c428110515010742010628030304442549250b1148000b010b89a040da41c03900081000210301500e4010040c8000d10064191070004000c2001d00340070340094160358904a1900700038812065074038030907550340d41000000814002a041d00880b90790000080d20f80011a012010b103040124016091501c1300c1c0e091850100d080001401aa00c0110b811320072000000b6903900100014400340c06410000740c0c807070000c1d01d009001d040c154000440802d0410300001360365200e0380084e158420b02040040c5103d88458000d0b402c00e00c6c024012a202050300f80e0141100354011130709101e41038190215822000528011100f01c50203000c1c01844045244000c625880c182c405841d81440302c650f40350621940c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 570482491 1250 570481241 570481267
    0x6050a14250210080105030c01030b0d050d0314010803040b191701080f2e0203060d08340309050108071b0b150303121612150504050a090c050609010302 67
    0x540065945a41c115041501141041d440380e421072905070134000020350615000a8592441032034050405a9400e283c1c115551400c585c080e915070010140d035a24641900003c02510341001c0a422203460390000282c3d206001040742c08441c04072803218185401a0036541030300128151030010010300c1040c0030391800b007043c0264000c2c62024000c0c800b4020f0718541d81c0c10251850342c882c03d15164420203505d400d008000728104100f80b40c0005a9942d1084001a4601a03001000d004004c02151561045504003040813600b203e182055000c10000025266400c03c20040240010b922400400c49540103504058108510b0b0074180c0d122140081441d5050347d80b0501925506100401d00c043e0909e4920720903086041640074601c1d01e5240003001c06034540250848910b45103008161900a00c1092035070200301480c001404251190203550703804000c503010702032089103420f001c00c00010052061740611a40300300e0084a25142008004480c1c20000499060503001c1242030700c3c07410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 570483741 1250 570482491 570482527
    0x319140909130501050907083304122a120e030a03020a0b0f0108072d17011512020915191e030c0b1c151e06050a14 51
    0x40029001c2c1018116030601d40e082d2080904003030b050380c120000c20720a1440200c4d040c20303804008005250f14450210440e55060b20016668104410900038803081110700a4051401c4540365181206002c040d15036180ea03040a040a08422400600c2d0700c001030b0840c08403203080c8409040c4a200c503001a804641884030200b8101c0050700041d00140c10080c20300215034001d110f041070902e03558140900c0c82d58802041c000c2e4520783e2104692400301107241000e82e03240c0c0c0d4903c040803005603540c6d450700000740a01c6040301c2095007404800b201702d0695500340340888608844299400b08240c00703109c03d10002510f07048400b0388181207044c680d1601100089000080038050074054541442000c2d01088030740b101c038803202c40745010070103d216402a442542c010700c0fa000e966180290034034140006020001900c20308008580c0d01e501c401c41d506200300c0d401085110415480c010789030040042c94020480400c10a000300e41d5010720490070807e0442c0424000c0f40707810409800803c2e01c803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 570484991 1250 570483741 570483751
    0xf0c050f010204260f0a0201050c0c06190e0d030203041404090b100e010b03060f010806010507020406150207090b1005130305070e04060c080609190f050a0e0d020319140909 76
    0x41402d44e10141900c201000e42c2d503081501d4000303040600450f85105440c0c0a8250300a410031001050305060b034841071041c0c504040b002010950340c2d071070040c184040141411100c00206941c0000d646007410304030001c40000741e02d68043e51800d0b00f080111301d40ca000d1a501d40d50002d95441e014000070b404c84844a008030b085001e2050041d2411041094840d0140c00c4900e551005100303211068480c5242c405038407209080080142d6030350401245d140c0264800a98000d0030031800090705010801403040401143e0700740c0d6901c684540101050756010500590000c4c040516481c3c010b202d8409800b00d51400c07010b010f0025138a443d824680242ca4102c04032652120f000d110402409110301e500e40007107410002e98916010b03000a240480060600308000840c001903815660154082a0440d1074120f0030030942c01c18080c2e20005000c01d0b1300003004d900c03504207410071923400001521180c0d1036040000403201020402200e25404001d1410354080c0e003440001c101d6501d039000307a8821 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 570486241 1250 570484991 570485009
    0x10b030a060b0d09110a0e06100e04050a06050f101409120a06150f0506180301180b1006030203010810150504090302030a140301080705120c03010513030f030b010f0c050f010204 78
    0x1814581030000c041d9102d10040c1b440740c4141002001106a021180d075400001112801c80d0300034820380943e20303900c2c0849043d60261800c0300b008400c02485d400304040c0e950940c4c1040e03407288240c0502c00160100e14000001c80c2601180001502d10200100b074805400b03005210807020704c8429914103c519031089802649070500c81d0800440c41c00744c1c100420780d04c0c0075603a03000c0c03418012174040c1c4a0340d800c10030003201111780340f10b642d00c00b5002400c44e44415140100317052001c7c01c010200301426518005490110003000030713014883d00989040c0d52180014204809010215000400b0030002e8000e00c0d105203403001030740e540d4038403441c0c030814041e40243d81d42d040c0800004040592403171115420b18000c0c0b0060003041c0d40090428151013007910031221824281600f14586441c030070066034107608000800410b9401811500f400b6172098840c0e18060704820f03415019500c074101800c0c0007800a218080c0f5042c85030501e0944140208146e0311003a4900540c282a6403050f0440307184 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 570487491 1250 570486241 570486251
    0xf11030706081b1303030c030e130f050c07230a060f0b0909071a0703050904020d020a020d0507050604030f180807080c01080112020103150b190305070f08010b030a060b0d 75
    0x52074003c0701100d074220150341e10452428000c01ca606620440a01001e8108130480c58100101400340040069405000f000702c061103086002e210041c0803a926080141414480824014850303081640d98441c2d00460102c58010801030389000f1254411440c1e030385124686004003c51081d214994151504c01c40c04560594181c05005440c0e0001d000100b05500184040040b00200c03544410038011816080f40d036000c007824222000d002e09030141d58490700c0000c0e05034040820b64002c7c114030351300c1d4007500c10340100d000c0e0039165402207100207800b5130800000180043d201d24503245031003000c2d042440407c500d401c7c084e08440700f40d801c604031a0740000b005201c0c08208000550381c06600340b074401d41d55030414040e200012150040241410b8403404400054020b4020b42d502038203c1000140c1c0710488002c1160001d5000076015002c0b900e00b031702107000d40d131040b041000c081a280d19181502c3c1d29000702d030b03c6c0070b03840141506800e641d201c0b0081041640c00000b8800480340d4203001c12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 570488741 1250 570487491 570487501
    0x1f021c0c0207270e0303090607051803030408010b01090b0403120309080c061611070f0e04080c060403020109021e1008070302131403060906061302090d020616060b0402090d0f1103070608 82
    0xc40c4c4000c1590042c42e4002d0040105004001030320f1603205403d07240ca81c3d218102c903040391080b0912510100c1c3d060002050105010205511400c0014400d80c0c491100b160303101903040880c8114040a410020000c85001c0c4450180d04040740091265074040d15182800d00c0380d90415501752101801744480b261070205041e407020003041d6002c952400342c009607141500302c1b00220224400e9802d001407050000d400d106000c415917205030242400d40b9004c3c81c003450300a0003003030309903800c91140807468540000c9107505510f80304071031405800004c2d8410303c08000e80304050000c0c02d0500b0190200203041c48580c0c0030340c0100042451a1003c1d8103055400101420010b00819400c50340d4400070812605550f03002504280b450700007001662440c0c241c000c110f020b1049407000e500b0603030000b8040c03010f20369182c0703a04200b400360004101c04815141008140d10a212f2034692003204441254085000006551032091081490780903004180000c2801d064650f402400402c800008102d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 570489991 1250 570488741 570488819
    0x1809060b031b0a0e22020c070e01060c1208060a17101a0d1e050d08241012061d06031b03030d05271f021c0c0207 50
    0x700b82c0203101c080440c200740c4200c10040c40350b40200e090760f1190b400040200300382281002644401ca00d6510195980c0b02450406981c170b040512541402040c4200000358251043c1c030b103c07810b01d80c03100e100c1c02106550303030007100d2180002e40010780c012a850320005440402c840401c1401034084007418441904035800e00403244c07010700007002c113950031b04a0001541c40140d0640140e0380f0078145070700303400f60002e90703480c1c0c4548400c000d005104030680045202e81102c7e00e1441194412003003084200350b02c0c040c4402c1d1090144072904020384d203c0003c1c0c21400351050007000c0301a8038002414580c0d0305201c2e00900341d211411080b2111420a0103070340c0c1004d00208828503400000c0c0307014403c040700409c0e928440c1c1968603220540c3c0b20040b03040154840003180380d900001d82103074005094210105d480c0c4030041c190103503111005155080e81e0415000b55084800441600206100fa0742803810151001107a10300c1140a0a0b030045010303850441c501820001048011102200c4941c0031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 570491241 1250 570489991 570490021
    0x20d0e150108120c30030a090210031b030203060f090c040e010b1801080c0702040c0207080708010b010509040b04091b03050d1b030f1107080f060612030a1809060b03 73
    0x40306032140800510302c2d841d20000d480010b010746031042804076000000031145d00c242d81200c00c50080000000e0185450807900703d071000c540210703942e02c4400c0344c0340400e030100c0f004640c102c007428501d071850742001d6009602a60f0f0080b00500f18000d50303d0802c0004001c59000c40d12400c031a400031a0500103642035a130220301618980a00529002d00101003905419511011070b0420054400160104803147d080d1100582d01400038070002035079150180d1951030b180103402261003810000035524005009000d010314060711070300c0c9020b2a03001400003800c0c0c0001001d4210f9161205280000e851103032154080c480310f420b41c00d6580c1540741c01e80c1800d858440c0310741000054508502e03400084e000400100e945400c226101116585084c0c8180c100c481085046003e801c1000444041c08a86032003030f145d003001a140640d0b83c0c402000f05120301c0b00308100e03441d0320601150305d00e54050060000000f404000441c0310315900d80d40d002c00c0d14210b40107615030315004418003c00040140034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 570492491 1250 570491241 570491263
    0x50f07060204240212071b080a02090c04060f050903031201080a12020c0f0d020f1003140f01030c030f05010e031305040c090b031306110d02043303020d0e150108 71
    0x6424000d100c02c0f0000d50714100c11307801c00c0c0707400c44c0012440c003041492012100c0d030b00b60000c0201c0c400d5940c2c41025480721036019059000301810f500003046515184101c400b9030351181c680d04600c10043c0c41c11106600f1001c54280c061200b002080042d80200b90f005000b020040020080d08800c0c0c41c0482d6510480440a070965112406440c2d00d07660300340c1c184c050302c1c80545004107048128000900e201603c12100d503080310b0020303070f49407440d031b41900b0912940b810090050360944940b4107a1290800900c80500b10580c0c0f64400d20015220141682101d400740300040f494480384514903003107600900b00800c0301445404104030f02d06041c0980452103031903050149070700d890100390072291320005040240c122540750b50201041500c1d4010f00310000d050001c0c1d522000350b4102c01000b90300c20f0060100b214846c1c242140d6260b240702581c0d0040d050f60081e03041e1841400825800380d001088415009515071400c00006041045014820340c0c82a0041e400b6502d0240c0c898100440390403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 570493741 1250 570492491 570492539
    0x5060f1e090606060c030d0c0f09050a0f050f0604092c0c24070512090414010b07030806010c150510081209060702010201112b0e060a05040201050f07060204 69
    0x10811100d40c070082200b0740e2181c0191026a80d54031003084950440c450121040440c9181c4280c045056a12146480540f056500c400010136158010001e41c0c0c02a48504c2000600c0407a0512103800d1568104841c2e204c00b03072005050644817900c40f0309880100da802006100c000c581c2200740c2d401ca058140390002c0c244c0c0035001c2041b52002003000b40001f00441881601290030301414601003004076080c0d04c0d00001512190700080c1b407003811a610141e809441103080185000789000c0324100241200d60b40c0651a01d00304180d9000d0350400c02c0180f0305814070000c005002c0201d054290713282070540c4075060004c4c2c0c074500280c5c400e80040c0300da042210107600010000c00c0054146003150f0807107004a8500e41c0b5130aa80c80100c1c003401512104903001c0d40d0110b0410007011901d00b5011122460798601801041a405003008480500c48e07000820307400607000c076400e42403035031140f0f40050061604624040e50410000402e902c4541e084501c01d9000808201c89200c10b03000200b0340360990 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 570494991 1250 570493741 570493801
    0xc0209130b06120a0b060a1e050315100e130606031b09150612020c1c1b150203040f0501050907060e0f060a08071107060806190b03180a05060f 63
    0x40d10440e510b02000308020890395509000c1403441c4d03501241100203001c0d245520300351000d10311080300234460a1041902a01c51441842020948184620310658100003542181031074152841e816980142204149901c55182a00030a86030700030b06e0003460181542d01020b02d0403e544400e10921907101200840c82e001c0e9603c1d00742c56481000e0103c6109240070340521031041111002441303a1540e8520f01d2154046030950a080b0365401124484192541000401c402080c07075021028150010a000c40800038880030b0401507000c2d60f00280110710300c1c85c2c4810b0325031700c071030031954141c5e0303050466440748e0810040c0c0c40d446000b01c0039a0806560781440c800380100443d800340518143c40301480740100026a41a1003041600160241030b402c4828640e80ca40c800b8101c028152441801070300c070802d4074101c0d4003ca6864070202c582c1e42c0b401c2440c0d641c900030100b04055240554440034005c0d0b000d100042034080201600400c00015802c00a09025400c075482c403029100842c00200c1007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 570496241 1250 570494991 570495019
    0x90b090610050d0b0a0503010c080709060e0a120602070615051005070210030534030513050d1b17121602060a18050f010c09050d0b060d030c0209130b06 67
    0x41000c0e0b42c140d114201e00444c4c80044135000030b910490982199405629001690000950001006001e41829112848584d440798421030b903401c2c00320002c3c0d0304445120010450f59088002800d00745015940c01030074507905540b800c0949201381070301c900540301d00320288528500207100c9001c60502c0d0030041c0c6004820350100744c1451070080d542003415178500c00118281c42500114111100201d1603a08031440c03000d024148032030100d0500006860f00c8000f56000070001a6480324541100c02005600e6407100202d5070740440c090503460000b4000134400010f58160070726945142d04892050312072080189100317504000428610803a800011401c0d005a0003040050304050440004104007050581c0b0300d10100300c00c04003c010703125800c181c0300003560650044038182c9469507140320140d071310420001c107a040d481c0c002e070000c1c1481c4040b80b40c2e403500540c8045540d11030300704482071031034036000540e68010440305028011908400441000402c1c480307664040700444210b0071840b40c0e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 570497491 1250 570496241 570496247
    0xa020a050409030215040f021302121302090613020f040b091203040f0b03130f0812060a050109060e15040609030b0604020313060507030b091f08030a0203190c020307090b090610 78
    0x11a04000d10b00005c54020905000c0600612641c00390042d2441c140386c08240341d4007000f944040024100d00034000c003c681600c1c3c4801c0ca40306c02e590010b1110440d903e0b00700800c010341400898002d4819400c00c250f801414461010380010f04c900303968552100d01d4042848500320000c4071006158104000a0003c0e01c6101074000079a07000031149910307a075894003990003140041d5005062032682d9400d0400704020000140100c061401c0c1215050b11207405006c03065005014090124080034000d2050318411442000c10103c01000b5210544c00d000c20b03072019610640140700003c110074400d009101d500103009811010a0b18114514030381040942820003041d1070003080280c42e0300c042448680301c2d401400c2c4104004024090500303001450140c07581c42c4407860500f01203030700800a1400404810f4410781c0103160082c604e40280b140c1b4101103008141c800c41701340301014150340050b1320100b1403200500301842d000100b13210600304200c2c811000400440c402c00c480001c2098160b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 570498741 1250 570497491 570497503
    0x8010e06010b070309030c0b0918010b0f0c01110307200c030a0f03121508010e0f03190915050d06080f07060e12101a09041101050906040305030a020a020a0504090302 73
    0x41102d180c0c9407180041d203030464000b205580068414440301c4c1d80400c100455070000e1145000c101c40c1c44a80c0b0b8840021035a50a1091061030f84103507080c000c088040d00b084004000c00c944980000440e0b800003440d00d83c2542003603a101000659040c2041142d004c4542c1c140c0c1411440c0c00100300600004001a64568404400509071801803201e58100740c0030300c13148140005500c40500c41700643e02c02d0102c400201d442101095800c019800600300804141402e503090030401541c5081502411848813016003508a0b04105040310700291600100440d0491951079a4508d552040c40458580a50368150098102900300041400303100c040083c0c1c9408076885c034103046001074410400200d0030019143c400d089401a8100300381c6403840c681c0301c1c00b90b0700304501440c00c18054540c00d00c005080100c0c0c0c02070050003110500c1c410380d07010300c0c05400d000320018070191402d9102da0783e6074216000711440c070002d60b1103030100400b10700d480000e07040500800d460420407203450fa107000796584 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 570499991 1250 570498741 570498749
    0x6010f030b0c0703030605030f2a06070f020604050d0609050706050a170705130605090405070e090c07110a150e0102060c0d020c010204080607020a140c09070f0306090c09050102010608010e0601 85
    0x740c400643c42081501941202000341401000e80380528804d409258075180c040f0ba120082e0f1075014202681c0d110500070182c030741080035003802d0801100c1c2d59281543c400b101d90a0b0390008080c0000121651062840c240d140c3c403610001c500c00c7c940b8546a0b14045041d0040380034030405000e55580c0980c00400340ca0008040d40305064180c451840607101032103400303c2c103a80420324203008181c0baa040001801001c10a803801c005581e5a26012664013103c1e44c90b81d83d20a00d1100031a104c100d201c800b0741004d5008042801c455402c0b000000c210032841d0f0b2100303000074849007806d0105900501c42d04c000b81400e002400d1103107000c0e21144c06500c43c0340c2042000f075a001c22412401d00f4258140e070b0162042c20100c0380d050030b0129003e50f942e58100c1088865a4884911403607004c40800c10306290000500200c60981310714109640406001c2c0712582003540d10000060602e086000c2e180001982c0d40341d69403684e003800002403e41d00c07140c01c03800f1542e0424180603d09840000c0c4c0728115 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 570501241 1250 570499991 570500011
    0x115030902040917070b01050a06020316050309041b020f0d0e010309050313031b06020a050606011b06051503150108060f1f180b0f0a060809010209040509010e06010f030b 75
    0x280c6001d10000d4014040c00c6000380c100d40c05080a030752040300010042403030381d00482c00c9407038681c0d99008004007100f040c092080140c006101d40c0596038170850001c4609032045090324144107605000c641202c0c410a02510287d86082c5c52549017501400314810300c0d90010090410201000d070050420300d45030380761504242da9840c4a10900c0024401d440070354140826031039035191f5908004c405c0051041540245000c0c000000600500008110350041d0340030000c0c085995070342d801900c0554071005071480c1d0300d104000d5031000030300a203d0706114600740e40c0a00c94a02c43e01c814180f4080c044020b81070403006c0500140102c440000d4100d920104101c00c0c410555070710080950781400032100e2903042540880089030401401c820060500382d01d14081240029010422524405180300c09402c01c3c101402485014450081142c1c025400000940b41c00d00c4180403a08035402212000c10740d035500c1501e80420b03c402d01c0b62900401150320003c003501d0540c1c90702c00780706202500c80120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 570502491 1250 570501241 570501251
    0x90221090705040e010c0e01180e070504091d060105060405060403080c0309030a11010215070e0420070b0f0c070203100c032007050105012102060c0111071a0609011503 74
    0x1660000c0100c0c2001e4071002d00180000c54042104d28040d09060400c0408280c480100c0c0384154800ca580350011601e8800c4c50b04a00c0c07500740252050100075080300d08103c1c08000c0861034405a010314040855010001407951034242401410610180c000b1403080c0c3d41040100705c9595600148c800f80c0b031304041c40b55034521104541c24591b01c1512034280e054099103201809001c05080c800f0141d180030703000e81e00850703071501514818140407107181b000318049103400310b840e003071a504c00c40204645248010002c056803000e0300e03482c3c008107030896500d00c1c5042004180100f4400590b0007800d20604c0e02d091075440c0d800a6110243e990128984558880117504c80501c40c1d00450021585022880c110004990f103081d855800900c023a2819800c003400084c2c5500d4241000700c1400c0c1111418005100c0e5501300013165005486002856485241945601070319100030500e081c4540003161907100329890300f456039039005155512801060b00104956415403418030b1164403103184c0003070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 570503597 1106 570502491 570502501
    0x1e0f0601090903090e041406091f090b01031b0e01060c200a06140706140405070608060d020d0501020d05010306020a110a050a080a02120c0313090221 66
    0x40000c0644c0410010070449080191b00140b05070706244074401c2c1941d00c0b81c6085c42c00d0f0b8078001e42d500500710045001c589100c01064050b9919824441c441d40c42d1180601184148809807002c841c01c0c18003041e996807002004060040340e40c80b80d0710303541c484600418440110004480c20340343ca25500c030079001c074154806481031004092010040c04d10b001241c822201c0c84500709080307400c2c4400c200041d40381c0101d03452000c028400d11058505820154989005ca5102e4000e000c1d680303041c8400e030340381c05880600d09501510b540d6200c11017884c05034028401c1a02c1081d805180a00103c100440c1360020001c084455598480e1141d20000c0340e600d92002c00c400404607841218814000354a5102a140c40061801503642a0505d003104815036403020f00e0141c00c5400c0050141c506180e43e0b559000640812102141042d808408182d072748011050151141c54640001030 = true := by decide +kernel

theorem cover : BRFrame.Cov 570323741 570503597 := by
  have h0 := BRFrame.cov_init 570323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 570323741 ≤ n) (h2 : n < 570503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
