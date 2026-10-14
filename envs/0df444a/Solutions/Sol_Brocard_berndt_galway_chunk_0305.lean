-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0305
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:05:49.44141+00:00
-- url     : https://prove2.me/submissions/08fb3373-fb6f-42d7-994c-47f9c3030120

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 54676262 ≤ n < 54856118 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 54677512 1250 54676262 54676273
    0x604030f09090b0a050d08040b040b0a080c0a120518060906010e0108030715020a030f1b020706031107020904110303030a1e05010308090d06020d0c030b0901050307050d0303050c0909040302 83
    0x2140041c050125034102c0e009050410105200795640e8020300702c103403642168980c164030000d144c4a00307144921741c800014600302250000e10381e03488e80040c141c00c0c0c0300340e1500c0b8060360310108002000d204260304031003c10300306407103541d01c01030a40c00158000d08101d02d100c0d800f211400502c4c60001c041fa0300140541c0450010b020303200c00054010300400c900c000a41c00c2034440d0f03840b09504070446e558036141035404200c03410402c0c401c0e0001c2980c45c070b815208000426030000001903c01085920740054828283d00040ea98401c0c841c07040500103009800c1d09104882d800c2103031100bc0500240c07001e0350300002c0510035681c1400210f01031210050001980c2040003d0703d8110000c20441d098014035042c010804544190121034403803101700c41408007a0301a1030310b02d00030300420110a81e51460002a403600c4c41d01584900542201211003071166a43c54041640c1c82c02140602c42d046010320058500080c0642c00c030381c1e089004800b0b402d080280da0300101da03c0942c21070301a001039028 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 54678762 1250 54677512 54677537
    0xb0c19260c100509030307080402150c03030a06060f020703030e0a1a030708070206040305070210021c02071e060c020105030a020405060a050405040510050102071202010c0c09020c070902030112080702060c060403 93
    0x4000d825507403440c1800c10f100c0d43c0380c58118640c69000080c001414412240c0000e400c66560396841d40c1502e0400c04080d403142001220590340b9001216806503c03443c005005c15400e0144041040104480c0d00400e032131400c641c0e00302c80a02907000c0d0b05802940f407081c0450303410840700c8148005c030640808540c40b85050b80c002800380030003902040540d0002824000030a07400011123003541d40583c0c40c84109080000101e1401c403904502d1602425440036403c84140d0225101c4111140040070000654540001c1d0040303010500c541d0300480d914644100c0154010341c040c50384041201d0740107003840e42d00d00c080340e038941c403840b191000510002000d10161400344502600282c0111240c4040b5041c240041e5959186001d01390494411940141c00c580c840d0b80014684da0b800340ca007248442d81c980307080c0301075003042c2002404d5016070080400c81517036034400d0303038101c8050070b0042060711046c3d240c841c0b450340140402e81c2c000c801004201402074082018a010340c2c420f0f9580262141c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 54680012 1250 54678762 54678787
    0x20102070608010b040306020a0e090f090106062105060604090f150e090c1203090607050f120307021c11030a081b090a05040c03020403021c0c0b0c1926 67
    0x40c1a044041840802001030058020100948007034981c0a00b0050ba503100b000070540c0c900595505055012903144c003081000314018283d240115040d00c028040140c0740e01040c0ca00b9100d0a014403a0b0843c46100344154480343e4120940121000e0442407809440302149400d45416000b0490590b80300c1c003014841c6810106441c0c01007080003201000390404581070754a622108903994800c64440b6070070000014280300319040c1020061086517a03840602e8005e85a00810b65580f4107170040040f128070413041c14048900c104131607070103402c0500c411300740c584071200321445210420030848950005003030204010252642903880d82030492828800307a119188150300d030b0841c40758060010000300c0c1c0f50802030380186c4004450200d8043c1244904034000e01132070380042c2d0312100290303040161890303d800040605d0300904038114207a0321104000e5252140c0f48912039254044003040b40c04074450444091854482e481000b04587c500c0d5003420340c000500040c500d40079000402c1140d010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 54681262 1250 54680012 54680023
    0x30a0603050a030f081005060d050606040b070b04050f0c0a060c030903020a080312070e061614031207080c1218070f0f06170402010804030c05010906020a05030402120106050a09020d0b0307060c020102 88
    0x5000c40d81c2d0000071b42c00c1c0008a9010b0003400740c250143c503110fa0111300240d0352a0152006030000d41d0241c1d840340000d0030004038094042d00d003070300d0720b000c1c54842e505000320125100a1110300134101002c901d04e841d0080311400300c1e41d0b10a904000c40c20401000680d94180b2420003408260300440e101c07802c08140c4801d10340d010300b01031300340401d8040319200d680f82c003010f841441c048181d5015802050342004180c08842c021088524040001c645114004011202e40115070990790302d4803960710080283c17407a21440d02043c1481d03070760000181400765120884500c80c6400030a45900d2a95124034403401150b07600140002c0c00c0628042c03248603801485410008500503111980d403e07e07800103444002d015002600704104902c04109101c825009424007076400441190703249410300e0000e000d6042590200e02c01d118079003201c5000001401404181c80d0018612607025203000c070150020b5000307481d00c81c007442c0c91f036403422040d076007d025078001000d054841c0703804c001c003c1c4002400c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 54682512 1250 54681262 54681271
    0x1b12032a170c070305150405160b0301050402030603011803021e03040f0b0a0203040e04030503180a0221070e100504050f070801030609031b060b030d030e0c06030a0603050a030f08 79
    0x104569a510400315009801c01601c0300d04440450390344500c0e05507064106040e5410240c050322440d044404c11500d081e0009200340d02803416101c00c90010383e000c0183c0c80c0984a44508048140300510072490107078021500104001c00008840d403c10035140018909081c00b0307400358200e41240501d0301d0083c080d220b075901900e40903514003414045a400340315414010000b0000c004280440381c40e000700200c03805020501e80024849c58a8a001003140e17004440c510b081a14140d0803d0000f00c000500c0e010596000b48646941c4030640004494002c90301c42c240c12510694500045070480743c010702e4001d020546081003c142041c0621040e1070000d404a8991030450003040b03003060384007024605696001101151502150070f04442c60806802a4140c0b440041e096004004065002c40d140c2002501a10b4a00c1c003402002e80445030307101c80522103500110041c1d00c1900c0d01e070300211740c000c04509000541c2e070340f44e45035140340510b20b401c100c020840316042c2d0342ca00d0b03401c262000d521 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 54683762 1250 54682512 54682577
    0x3020f0301141803120c18010504060f0c0206090a0303090e090303060d1e0b010603050915162d1d220509010f050907031502090a031b1203 61
    0x102020541191001c4800410352100d811020f22600c0100700d06008039100381e040c60022050324148203001010a40c060401e00d140a1100c01e46030206500410540741107985945072030444042128056902e08400c010032640103900300000201607131140b1140000d14000c0d60f802e06a681052600c07660b845000e4900d201c554414810451159202c0c070799203154960103254002283d0002440e07141c88424910010600c610080c0045461541030b031008d48a100c8100450300700c44084280c9500301d001c1910000c07502d5400c000c0e81c641490155520340d045022030800301002107500c1e0035228800744090703082c00010314003082c028000603494407481d900200480704003607004003284030f1441220580b802c80c00902d8484002036060301f000c0d4800008007200840030b11075440c01c180501e03154092404204c40102d1001f01154502c20948261080501c0240062010324207684881184034140484007004a0510030301059417a58080d040201034820345800c5542c400280f402c00d0340c0d4001840c19400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 54685012 1250 54683762 54683771
    0x31f08010606081302030c120114070806190b09040c0e0301060303020102090109080304080309090406090501050405101a09060d08070c0905010e0a090b06040e0a021906020105180304030201080601050d1503020f0301 94
    0x15a074049490840b0b044120390395080743d081641542c0c0508070b051a403441d00c1e02420100b03c400c070340002c602c912837182160700c0c4015081c40221780c401500c00340100c4480b0501405070304d026041507800040c4035200347c2001030b17014203c0e01c0003c0c250741c1140c00440050350040f80c54803980d600440c04001410682d4044c1d82410b0600001c15502e016944a2034410310181022a05105040d44141c90294011000b03000c1880e1078100f903079881c480407841d440054138044031900b21080f2002041c8071600024100700540d211705040108098080c20140d80c0c224040003040d00046034200104000d10300040046802c0d0301d4115140740030303000105003440603403c21401e03000144041c018503600c6441140e000408006410106280c6900c42c0d4001350483d294095401c42c2c0b00c8500d03400d004541c1c86038000d1000d66101154204200c01c0511850b8041c0d00c140000d100644c094511194000c0061510710b0800d040c00006400752164012007007003607611104240191300f00f40e52441400398090f0020302 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 54686262 1250 54685012 54685051
    0x120310080c0607030c0602070201050405030f0f06160206010b22060305010603150501020a06110f1803060907050d080a1404030f260d05060d0b040506010f0f1505031f0801060608 78
    0x18000c5c4514800180340703580c0058403204680c0107109640280a01030300f10ba000070a1149240c0c2e507006110001c0d01a441a000001c080500e400174655658600740d001d0034240c4d01c0e0101c0400d95400402e0301e080d4400b6007200c0f4040220916083c48020042698003107510751400d840078084031901007015401030103070003042c4000c1c0d80004408020580c46100050625160905c2c035101e4020341d030358080840000583c00f180d0001180c1c1c040c4144404070300b65101c0d6111101c002c1c1d924805403141c40c0e04400c01400d00b001003900580586003541141c03d1003100004c4281c0303d840580c0c050f410840d030704d02c003820b0700d138052054441404522420a03c8480070307481000f01c1c41c0b4018019100342400d41038070364000030203030384545240c91402640302c4900b0241d400e1a1904c030b91500e000740125001d0305130441c40044c0110b104000e03075084840001c2c140340c9603104003a080f11664030080c4503503140c284000d01e44604c065a40500d0300180000400010041c0c2087c41c028400e003400b6200e45040e2040d402d041d17 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 54687512 1250 54686262 54686267
    0x102011406010c170a021f020310150c0b190c0207050114180d0b041703060d020d1b030605070306050604140402030712020f04060306050d050604060e120310080c060703 74
    0x19608070609090070ba4a9100710314129998a4440340401c1203ea07020886105058001035100d01c56816011843d00d00030410741030b00224003003200c410001308007139141082a060524601108130030b81e4500850074280030f48a100c54400296010008a1a404c071100e000d44480d21400000102c00c1c8003901c409460310300020304c2d051180d844d61706007800c00034252080d1099908984824600070784103900840f403a09207a10700f00811501034840300240110003001c4581202100c3c82108014a5050321030340035000d111202030701c07000c1280e800c41c0c020801c0e0a03e801c40c0040f0002188651408245890102c0e401400e540050b4080d40c000c80003400140310b0311020f072802c541e2601b010760700181c5940d1031410455172203ca19207900c020610010380406107260f11401070050751b000b601c0900c02265100213014903025080005400b58014a0110300000c2490b007029000044080803944140a40a0740141c0f50380103545011a105d01c0c5d142c10040c81c0e4040c02941701c440402c9a19905081254501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 54688762 1250 54687512 54687551
    0xa0903020609040603060f021b030c2505060304140705030d02072309040f0606052205090309030d021006060e13150308040e040c09180237060e010201 66
    0x780304030740100c0d002202d40c550f03034000c0c0021034204906028600c130b10082e010003136121f800c00000034030a40300b10600e0b0700000401c540420000340014940d080c3d100e0a41a458205002c021040d80c6100c2c000090965480c07000d140658003400005034000c1031100c0301484c1541581c050360007070708100c81208400d40c011400e0400c0b5620f90710750f0a202031b1001c280a04600c82c6040c035590020301d0b54107001c00c1c461034984201130280321f00804c05c50140ca8078100512f0381d8882e40402c000d03a41d4034a0151a40015402440d00194244100c80c1055040030010341084000c1e0303240c80042e0301102e0315284801c00c5004182c01401181002200101100b001c903480240441c0030001c055210a80303803140d40141c07481c040003985c200c80143d444546601e03c0032803001047d030f800c0d1081c50b00001c0c0861400344c40e1003032151b40341d03500d04c0e00c4403030b18450382c00c4c0540c03055464a5070400203c40d8901400340880c0307141800ba40ca4a02c1d844840c10381c00d096015206111001506046a140000e00240c05552512 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 54690012 1250 54688762 54688769
    0x62d0f060e06220303090806100b030a0e0a1514060a141e0d080307110606030706030f060e0115020d02031809090f0f011b02010b1003090305041205060406110a09 71
    0x1040e0750b0701c103d406035080c01001c110202900c843d0184500000340741e44400c501043e200800c0c2500c007d501c88034000050b00d00c840c011440e402d40200042800454150310400e83c0640220942c0d02c400a82d03241c903141c07040300c03402521005032035860404811740308092966010004407180711129003070013000520035071450350650041041d03481c80320040070100021030316580010114091151070b480c0018680e0001c1e5804c1c1e000c1243c2407c142c1c1c0d00400410090311506014008000d80c6140c007031304a015202d12441f880c1c01d030703070b48100c04140794401502d11030192078000780f14844d5840e1710070000d2514207030f07802c0100cc64106014100c4d00804450070040020b00864900c619510366608046c241840c00001e142c09105030060580411419000001c450329201c4814042144500003039090b50b80c1405456840069000c01c401c2d450301a5001c040200d0091a260741040e4581701d00c80140310b501e081c00c0d40c082c5c0c0a10100f2003003081c18080c1185008a041400d0300b00f008104001e856101c4601 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 54691262 1250 54690012 54690019
    0x30f0a030e030c010204080109060f090510050c04080115060f0507080301140a24030e03040b19110d020c040b0d0803060103050604021908060307050907051b01062d0f060e 75
    0x24241040340010001d9409148241d00210340e659600d080b00c48c020401c0c0001250210300700f007800c2c131290500c1e100b10001399400101a200504004012000601c1d0050444007036003824000448c1855007441118440c084120006803075904084024000118070303055030307080041c20090351002644070400da03030440319526549282c0d000d6100009007003120581080352140019841280c41c440b5001030034807a400e01d92020800080c3c01c81600303417240308501a02050090810561050445007012169180c0c0c244c81c0c02120240d6202e241070600c61012800c500583c4101c0c02300380d00c0e1801c0d2040e4407910600f26003410748200541d0319240140002085141856030300c100142113a00c841c1c040340c11010041705004a007520008000e8802407042d10741c1c81c043c0c480d146000c201814904c1e81140070310020340301c00e0304010640c6121a10035035440b02440c1e01d5501c51000003171450880220a000c6010b801c5038440040d00c00100041c0d00d00c55030b000700301c0f030340e011201040b0864221100c0300803158180c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 54692512 1250 54691262 54691271
    0xf080607140c010209040f0b0a0b031512010e07030b0a0c180509090a02090108010e0601050301050405031207090308030a060501020c010903030e0105130f08060105010f080103110f030f12041403030f0a03 89
    0x4800b4038024010b24408681260400340da00b02940a983c1c0400019501280c4048103583c841c071909160b8007080b502c0d112180454025100307549841441c500c0d09001010010440c3c041e9149101d007480761aa0040752216082d00c01d10804072800d01070060b0880300c524061a903c0f03400000c84505004600c43c16000d51000030104607140814008124444c0d000703085102c145d41c0d240060350090041e003e07410480c1c0600707400401d0615040c0582f601031600f10009500303110482406440000000d00b480c010320a025000000203500f8a0166204802801c0e00207003a0b0715041c0068202111115000d0411201c010140b0000790400780c041a005000e10709151101701040000610b032960f90800b940d034140b042c40024205d0000984541664420390fa0702c01040501501070740d0b41c0a080c08010912111301040340201d09100e420f0360300c1d100c401000c03540b000810444c3d035030402002942a100c0e84900160074444240d2080c0719014048054006625141c1c40c80d041c5003c1d401003002c10b00030913854 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 54693762 1250 54692512 54692527
    0x60604030605041b0f0626010510110a050303010e0c0901140f07020a0321090e040204090f0b0f060906033009090112110f011e02160e010f08060714 65
    0x4d4905007420030030019440c41001d51150854860702c03841d84036403c00602034201d1101c40d034000d010062510040c0f244949a0b9901740b8042103d6a00b86018a500701f214103500c00001410800c9000220350003031000d03560329410403d0300c001d2040014080c4030302d98400c00c1104002d9a10241c1d04617160196404280c40301902c04581c02e2030b114856001c0d50004480d8404401e0090090150b294190340304820304e0303614161030341506e81074018868041c003000c1c99000070340541841d230000e5110a1041d000018040c10070b541c2c0400703410080d5a04884151060104074450420a05003034121400b18001c00c2071241082280e03400c800c0011410394100010201d41d803881150034262000030384010900d80e8075685079955050902071021054540e54500c5408030050b0030940241e8050040683d01c41000304000e41c00082854900002c100c2107204140401c02c0400c4400007101c054840c025440ca40341d49402440c0b1081d8905802a00440e0054002e022645400510010b528040101c4080e00d8141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 54695012 1250 54693762 54693773
    0x30118020f09040201030b28060207060507080f09060f0717030603073503030906010b130905041407080c0306060301020405030613061b0f170f01090216080a080906070806060403060504 81
    0x90100005811000100b900d410314248401100c8c600000c0c0000c0300c1a1903a550ba0403a03607010303e4400c42d004140100068000310752000010002066480c10852400c90f1083c0802c4c0240d0002040d405c0e01e03100400c56804009503503d40300410396820031881e0440c1400400039031550064400c02c0303034070083e5001d4203810280780c41c00e1040783c407244400411f0804150341802e40300d5104903424a210f000300000411440a000140c612882440c64401001c40c00e1805000c0145009002520b046e100b111081c00c11400c01c001c4803014000f41005042c41c1607580003814501500540401d209034018001400740307440001303005a02046401507800b58800e281441401082c502a2104491003015403107541c040c2c0041c0f035000c0d410b1b400d90700c1c6480040f401c080580314030019500d02c04003110f500010429114113801520162640c50b080700400025960b03030322244e602949184000c9115041040f0325480c0900050358000d00300d080c0038240349003180c001589881580001803c0719a1540800c09011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 54696262 1250 54695012 54695021
    0xf1403010f05070305070f18031502090d140106050405090604030e130501080c0a09140c1e0705010b01080603150f040c090504030e040c2f010e1b030118020f0904020103 74
    0x1a074a0004200600340640c0040140c801200c0319400b00c1c107862400c0004502c20085890418140740e0307000704e02c03400c5680e441d1803102e90102000c12036030240060365059552001c3c1802243c410388451051542c0030058901b51511540044d1049140900b000711810000c58600d45c4283e252a200c5a4000100700040d901070000c0b4916510614080011403101000940c024203001c046038048030541c1e6402150080c1c8ec04051000840c0c00c48074085548443d00324090701000c01da035040041e000d15100801c040e01d0704484801d9416039199a012141940c200d86030702d0b040101a00500350b11082a5064048100c0241c042d46107041410b00280a2207826203124001d041842c0b0140054109800d0043c411386105c2110b500c00c602c3c0515200e00741740284140c2080051740358004001d010f80c205114900382385c0240c20a00b035500c4110fa1111030710180580400c4010b40c00c031482c0086080c1c028175003100c1d44940c090555850180c00e84016075580b80c110640e01100f11500a401d944a1004a0242 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 54697512 1250 54696262 54696281
    0x50409020a0e0a05100b03070e150c0a0501050a050907060c0b040201030209060d090302010509010b01140c030705071203030b0405040c0b0304020d0c061713030e09151507050c0a0f140301 82
    0x20681e5091081c003440036006503014145c8000d9280a0300d4517800c103c1c0480c8019a450b00105665002041c2181800820451180b580e11400340c184650070582c5030400c802000c2c100c0751a50748004014000b00c55125203600400f021008250b0281130400150034104030b0072001c0c1c28a1324080c001021688640c040701c40d031101c080c5c011a203911540c41481c0c00707002124022000340d42444002803038204c0c144a004446101603442c040c0071102c9903c0d204165000f0350045465020030800000421010040c030002480036450b1000c41240c00c0c2030080464086962240c4181d080c0b00074803002c941c4442e20700050704e0b010840c050396030702c3d144009a00d28128000003440c104c80303200005102c1d500720744241101400200558a5a1b0b05c0800032003001d103208200401040b4041c81e0b925880c145032008503404540e01105040b10060b100000b4109040c44210b11103d60000908400308039080c0103641c6900000d542a9030303103a040c5959100104c0030f030f01a030f000c03000c2d14407002c604079942500201c40a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 54698762 1250 54697512 54697529
    0x9010b0604060509010e121e1002120402270c0f120708070e040e06011e081c0906031803030209010207050405100509090d1202130b0307080411060f04050409020a 71
    0x4599a075100940f20350007011405011400c1c0840035080780c1820620010341020410140140e5001c54541150349203902c41e51070454420003d0105031414944024080c40d00502d0446689250910400030b800001d00c6560503004134450071a01d81103910018a038004117451542c40d00c0c2ca10140c0c0c00790090042e80c40c01092a4441c8061045554009540301d01a01ea0b035070328039481c100c10009000070b03034024007519441da40c48480100284040485259111009040b4002e034079980c4003c51840c00c00c2c401c038460700fa590940b0f84020700c250480c0f500c074010f0a841c00e0600401116030380c003040742c0c105040090f0a064002603c5440c40e84240040800b901008004010a08240e244000040e0550061600131410040802c2e210a000514066a104103503941465004c4007010000a50440c2d19003048802c1000c90110780c4041c02c00203584941440d41d180d031201d01e05414840064812422198020071301000305d01c1e10201404221019101c068a02180d4001c003031002c503503500b4036980b01c000d9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 54700012 1250 54698762 54698767
    0x507080d2a030b01020105010609031109070c0507080309011701060c1202010204180902030d140f0906070f050c100f0c080c120a1205070305061e040b03060a0603052103070809010b06 80
    0x191560143d00000034100280c4c0204280c1c2e880f000e0645842626000c00b03403510000c0741584d40e5619210034015441551481e2003010002e59030b988038601200782d0001404c6070404104403c617035a025801c0490700486003000500e83d45804070117001c412142002600b09883c0010b44d6850341d000350102c6000300903403440b8580f416450300280c0000c04015404038403c0c06a9a40840100d204050650010342c2c0c000003503150074810b0342403002c0c0303a10114445801c403505101e8080821048c002c403e030780758083c0c4060040038242e0800c00200000405044090000001c52000240e41c402c41c1e40030750980c01140280e4a0305004242490590790b160386002c00c0d00300103888000c032940510b92010007501c04009104948500e08150180d0f00c00300c50190300805054080051404041c03e080031480c40500002004088400428145001140c8802c000c40d00e0b17240c200100a4204013010314031071100d812844d440030030014000705100c0a413014042020700000f00d030b01c600081d4040300020500401d15903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 54701262 1250 54700012 54700091
    0x30516080c0d091a030105091509010f090e0109120f0504121407081507031d0a0303060807080105011a0c0f030a02010f050703020c0c0103051905040606050f010507080d 74
    0x1d81e22540716080d900065400403000405040030902c400d0004c0345404540d041d41e0a081c188006080c0040c02c4100404901250310340a4075118000b80c060512668001c43c000e050074002020345034184400c5030540e1602e60500c011031402c1c01000200c1c2c545150006654070025422202c0e402030750000907213200e44100e00c00801942f0024810014aa0307015210841d41e030b402c2258440c420b04004060360403051000500142c422303400342e0000e400326560480d00c1c2041c41c002c2e40ca40f5400d034200b180400d41c0c0307060911031420b0420120f0000c1c45140024000c960520307119484201200c500c5041c003d0000c00c000d182900c06205100d0792000941c00c81c0d448070303800d50000b4060301e0310030090305241e490440400ca09501c24000c03581c0040c1c0b02801402410f00d510011401090000c002e20340300040b050380c0340e61100490040794000c50003031102282e1242003008201c284032705044d510307042c000204000400600c211050f00c020407440030340000d0111880400c00d001c6040c0044100010f000a640f12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 54702512 1250 54701262 54701287
    0x130510020d0b01050406022121040213021c09060207080c0c0a06090303020a03120b220b030a0201090e1003060c1d0303030105030703080c0102130314060c031303051608 74
    0x1d04032400c40c8002404452111001501e45210714050680180c11403c02c1a44181030f041a003400840c0f01003016181c54081c10045204460081e41c18032540d40b81c800344002d5241c01500c0310b00210340c1c5007045243c0110000d070445100d845d064441a44c40d20740010b80b050214603419101040d40048a440c0d451889100c0300d80c43d28841070395140725800104011908034402d1401c01c2c2500e605400520041003961000d40322041c175551518040e40d1964060205512003b014504070004182010b65100c59000e0032025290a0303154180070360322a41c51600541c2c0e010b00aa0708440d8409032030896030300d40e20b000c1001001c4e1a04098089410540312136130096220813100e80612280180c200b000b1101c004054a07480b007071040c50b91580c0b01a10038000714948200401c100b440b038100046c80c0c06400b00f6200584c00c803031b500075290080c2e22014030345452420b00c400c95001c642c0108080c61480c1c829440341400000c4034000d0f007046004aa80304001c2c0130280c0840843c1e030028502da45508030501d44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 54703762 1250 54702512 54702517
    0x8090c151210030f0204050907090e07060801090c0c170f13080f010c120e07120c03050d080103020334030c0609080a0809010804020102070b0403030e040b01050a0210020313051002 79
    0x44010001c1400c0001d42a2200300a01006030b0b0f80c46440248080b1098003000040c150103461030f6403d004659001886040b544a200c480300d929501900c82c907458214003802c2501e0523402051002c2c00c0c0303214a404a41d03c00c030b4021324507500070100040b603c40d50400c49043e015081d010521703102c0000b00c0b070b02c4444521007454210350f07810040701c9908444042003400d81c2d0b0a0591080441c00f0300842404201036030304002242c2e5248402c82d181907941f00c242000c5a0004078058440c0c15000005000303020040c000d0380d010844505003260903514650208e0b40e070380c1000c10400800060b60040088502c1c0d140c50b5805011100d8651030807464803400d061103c401544101004140700280010f45c14401045000005030480c140c14106011130b0010b50704114014404c07411401100d0000c10411520406000910f0180d0f49a03258044090140803c84411507021818800140300f003560703543c0e0000305402c0394440d00b040540c887d2a840500da114500c81040144280030301c80c0d4040035981c05a01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 54705012 1250 54703762 54703777
    0x308030901021818010b030606280206070206040807030c031e0e01090602010b0a03170405030d0203041406030402030a20030709020d110316050c030f0d0b151908090c15 74
    0x184840c40102102c2004004c03c214103c0d8800505071100400007064002e000e1680000080d121610380300c06c41000380140d40b40012601c038485205090f281005604000c5a03034818800d0004150f83c0c00c10743c66000e42d50241e04801020021180820401c161049941070411411699051071400751004003401e0002c0c0800c940703002407803155000803502d10500074000140800b42c2442807090544d22960f41c60b00b0b141440307519120080200052a80b010042c1c003d0391442c40e40656100d5040444820381903010b8001c0e14031a1006000b48409a6404a800c04140d9802603140602d904030652601c00c442100031070503418040c10a00203290500e503001010000e80d46602085444000d50101c3c000780403e40341c0051440d034001c051a0f21a00980c0200309481e011803c43e42800b03d20306c80c81351194410084c20261a40b079440c403002e9420402020214800125103250074040c0403110b115245603004041010040045c006c00c0d1010701c1484110340c07031840030740314a00c0c20342d078100d201c0e46035409030b81c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 54706262 1250 54705012 54705037
    0x70509040c0305060105071e02060a050c0d080f0a02031008120705010608010203010b07080309031c0204050f030d020c010c0201051306030c0f1b03030b0402090d050619060f0302010c0507030803090102 88
    0x40300884107034440e1040620500050716480e040c50100c0c1c40e405080982800c90407040c4402500500c0036a903080e000e0100000195152a0380c2c41600b0803490070001350740e0b05481800b12450502c09440240c80005070310114407040141c8a82d100800d102410a040e40408002d02568000e0700e1100300d50802480c0351340c0030700c00178468141c5e01e120352400c0348024400d46c440000b091000d078002980c101c00840d00701c0e8000048138100915600e4018205a00180d4144e185a000a04100c075040503000c2c041c0ca21401c0300500700c200e20f028000380d1a4605069400e0402c54410501001c5a002d0350a64804040c840454054140c882038080c00801d4003041590200d0822100a03081ca4400c0c0060741d2516500c400881c01c52011766810390241c0502010a940b09400b4491030315075403550700d803090009001c6c00042c4203e0600c11405041001904022808a8281442402402841c01d00481100c3d0f0a1034107150720304960921a04004045d00003c0201400005025a00405402038480b0403c000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 54707512 1250 54706262 54706271
    0x105090f1603081b060901021b010c090e0c040b070b040302190c06050306060d02070b101703070b0a02070f03030608070e011508100911030f0a0c05071b0e07050904 72
    0x42040d5544a49041c81c141c240080350109000062501d80980501000140000131500700065018244403007250000b05580d4003289171202d02c0700052181d028032109000800c05c4240007a001000050325005e000020f00c138500101d40c6d008848000c0ba8010644041c2d07403522440d00e0b240540d813040b42a1010f40040c0704480138408006001750f0124811540129800300c03a84c6014402e171442e4000915460344442e00380f06503041050310b070005041442c0328440d031031040d142105881c014a504ea81221021640c45007070090200070001c1162001c0b40c00c002c040d50643c0d9030307400c00030103441143e40c01402100f01040c0c244c101600f40d08000c0940d03514100752850507032228171442a18109101e84040d00c0c0c1c50302000e008040c0503010303540d0071945510a01d825aa210b442030800d1302c2840003000311649001003000300b0f1044000c41c00d50001030340c190a000c400440d900080103402003e201400c11052165440490401102501c0050040d900003c4283c174007a200903099801c651115400760703082 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 54708762 1250 54707512 54707533
    0x5060d0b0f031207050d0206010b03160c0b0103032102030108070306050a09020a12051b0f010e010c0507180b040b010f080a0e0a03050301091508120a030e030f0c300d0b12010509 78
    0x2c00d03422706a50540c220b190443e600e0b0340c1058201411003c910041c00804020032020609a01034a0b010318000c0c1c40d1040d200940e480741c45100790400071202c0030584140014041080017040c0d08007241c1d04060041800d0310350840400007003540d4403000398003510064000609d03590001c01110b21a029506881690f40010452403200c04080d02c5680e1195043c030b24075041e5130150a410b1004441803600e8141e85a003540c5940c03a16186800112140701d6407000d02c09904418000d80c0717400d020546050050010444c0080e000c09140071500703091003c5600003078000034590b0320034014100510206d91101d40681000b805541c030a001d804100c606142c60515017142d0b4144400494014034002d007112260111160003540004c001c003000c0540780da214400301001040034001400c45070800030b03901d002410030b0600e000745031009598251421170403900c440c00d9004001b000c410711012410f540c1e051100c0050300809031006a81d0384501d05a107403494070300055201074400c903007400840f0000a203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 54710012 1250 54708762 54708767
    0x4061d0f040b0c0a0c02040c030f06050105040806012702040605090f0402120109020f0d05041406070212030f040204020d020c0d110102160f1b0e0f0a0605060d0b0f031207050d 77
    0x1c50380030306120032010104100c0c640d010000d007403998451502c8940c54100354000b9059030341400341c070740000340c80d0f0504040303000302885040018802424610b1502d40b8001d0196143c0205208282803400300f1801184c01070320380d0307032492740010b4495001c41d51240c480e103000d040e9400c54040640103c40c4005c0c44001d07170074540300700c0745c1081514807100280c3c2e180243c064060742c0401d10046818605100c004c44100c4c550107000d0059200312480800c03840d0700d044141c50000d000b4080341c03c66101441070b07003000d1015070850b900f121480f2140710350f5544138004103000e40b081215080000d480000c5120b040040400c0c1e40508641964030703d9031440c03078480071500381d01400b003400c1d1200c0049980302c0000390071070390500740c6c0f1752061500c2c1c0c0c900a007181d03c0e90014981e81e0305c91401300c005513041041d07104c90b0005403980980c084c0010028141044003080c03550050045600c041a580c06c00680c9a54500c410a000394200400f10354141001e204000b280c0d4010740700840c1d45100358105843c1c00c50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 54711262 1250 54710012 54710041
    0x50f0c0703120b0f180117010207120e01020309180a0b060a14071502070803011e060905060d0608030c0d090e01080c1903050102030f04050606090f0a020c070504061d 73
    0x15015a00d031000910300c00c90300b100038154400200d60080705452101309646684451000f42040c216550902c0c0d071401411511030940d9054a800c0380e44108650800104007444000079910585003c3d58030014010061303142d0b01c076104500754403040c00e210320040303100c15000407840f0301c0b0041000e000005005051000d10f0242680d90070200d840d0030194194a05150058440c581c01514035a03400c3d40e40148001c00c0340d21003101034410010000051000a0b9043c0e0804806882d4000c0c1c234083c04d14080d4000c1182c9a9030180310301c01d500004000d4498901a040302d0701600340c46040c1c1e81d6502180102554032401100c4020100e00c0305400011101d11b001d0b5424120340840b8050705800340001c0c00c108041e0901c0c024809514681d00010020030400d00c00b071841044c25800241050400b1b0410918210b401041240b040420204010b81a1405141c80341c2240f4101700241e100d175007400c170940c2048034641005811030f2a200c400030306040c104088a004100342c6600c0c3d10507444040d1200c0110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 54712512 1250 54711262 54711277
    0x71a150f03060a1109040905070e0708040c050d020612010f0f17070e07020328120b180705070501140103021009080a0201050a050d020a0315050a0e04080307030b060706050f0c 77
    0x640110340007814a0303443d03070086102c0d25401442e482c034110043c0c00150803610384c0c000c203980380c0e845800b040c080c01e100d00505d940c00c820b2500302804035180c1b558130f250407500580181406180f19100c440210344440381510301c486001c406803141036844122003032503d2840d110f43c00d10984c070f14000250f02410308803261880c15811002c1c04149050203502d454040c03001d01144d0851000304061298881c0d8005640f44514401c0055600d02040039402400388601c004c00c680c44914041e1201070b0f55846045007280070001500c1c0250540d200c2030140d90314094090003034a1942850b468404001e440d12009040c0c1e842140c204a41a810050450b100c00301400f82c004150302511990b4090740c040c00160100d10040c1c83c210340751041080102042e40c120842d0701003c692503184800f00740100341000005807c050391213121007443d100040c00c104030090310141c0780500020128810034443c2d00402072a0202802c01695030809140080040008440f071415025615000c58800b855040407508507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 54713762 1250 54712512 54712519
    0x60902090d120c0b04060203070201060f0501020c0f0a090207050604120e0319150212040201020d0806060a05070f0c030506090601050d021809070509011404050f040b01031403071a150f 81
    0x4910031940c640a10151110640c001d1041d0314000000188031421414445e62003905c01584a081c03c2901034251025602b0240007022041404e00285c1d90000320721030720941c2101c0c01c1540c03101d0340300400c51031907d94200341001ea000140c1e03130041c400e00041c1c0300e000e41e10448040130360110481d81141e01084900300f69034940c10010b403500d000100040c40c0c000f024084c904140401c945050140200d9200880d0203000441344d00c100819581c040c00840c10856983c180010b280c5455400550240304000710001400000326041d018850b07285000d1001692190032110956201e0400756901c4104a914400701e00c6001c00219403400d04130403060815a000e00502e02e80b90980008000d100d0000301420300d140314000c0f0004181d84c54002403030080007841c84c0c01ca4071210003403e100944500500c210191685074050000081c03ca00301e40b03044a03001030010481092490655046118032100a4520207460031100005041444443d01502c0101c843d100a203407060140311121800c10500f590 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 54715012 1250 54713762 54713779
    0x180609040b091c17060306040c150302090a08030714030a0504030305030405150f010501270b0f0706020310050f040903020a0b100f0e01140a08100903030f0504140106090209 76
    0x6040900703803640140100040d5020880030301d909143c04402c504010300011401c040c081c800703c154100c0c4039040b10f410740140805240ca40c03910701036451540300706c2e190803110120241440e4443d60545411680c02000e00c40b40d035980399050b07681c0e07422168042c3c034807005024446000c0c030400421101c4000302034072074034241441c6450a51f4903410050040d1a5401142c01c0c0206024200344400d1003510348081d55403155060000040c0b03041410320303660a03410444070181200da000c5440980858104895541d556100c650340c0c0c1000c0e02488100070300260010043c4010403528100a0341558000e0740d00c1b044480c440c10800c0140ca00801c006000358024641040c0460072860909034490081c0c111076000550b07030308000d03001c07410302e500001c17130500c40000520508001d59107014440800302c0da5000d04a040200d05d5032076003030007034050101a0352200c04108141c000d400400c417400b07200508004500d01400c2120184c07000111044055103403010201e0569214400d403400440003809425 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 54716262 1250 54715012 54715021
    0x61c260a0903060f0905030d05160c1a040303110a0509040f02030402060a080604020903030f090a0e0105011b05150103060b0307060311040302061e0a09090606020a08070602030601200c180609 84
    0x18001d00f2a040005070442d225017040b0301142040000780760f4607109540004d15458000c3d4141c110f828400018403c000503150ba010119541c403e50014a80000d0f03040305060b2202e1600380c005140307107120751141e09404641042002e8011000e8000c0002c2900c06000c80c0302c807450301104a01c42190300a51000c4244070309081c092182002e15801000580014500000600002d1840d006040c031088000000940c201c0703503050100340c0400410411014800c1541000b002a0403400c03081140c00c15a1141c2c1140801c1c0002044203000703600c01060901520b584a0800b04058410b00509034024401d00ca00003400c032b4400c0c03180c0b046080c85202840e04150070341e42081400d500010740f410b920b0000d226000e10042008c401405070500644421140a16141914007503401c1a44036400703541000a000000c20035140c100c80406910080c0141e5130356903400180d500ca001104107541400402103d82c900c01800280d080058108807030059503503201000020031400304030b8030325400103189804203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 54717512 1250 54716262 54716273
    0xa030f05070309050909100b09060105070b04080d051602060709060203040b1e2115011b031107081f150b0c100504050718020705060708061c260a0903 66
    0x50000d60320038a4504007244d6a0400240c0d0108151803803001034121400388000c0306000d102d54400b144066a03a10b1083c40c01000180c45806402c601400390f81d0504001010403091030210384c42c1d046400810407040c02d10142081c00c1a0398850722002511840000c981b4590154000d50101c402c0c6500451070981001240103040d0825038191400116101c0312003251032400700a000880f0328a015020400200000c50b2015600580451050a694540a06140d82c04805076191040c1e0034030501400c0228681280c003000c21215500e840e00924801060496010078150341110412003020a83d03460032082000310341c0e2903603808058880c1450200880da0101018040e060744001c190380c40c40143e8a0b10070140e840854044030503802c03401091101014450704041707240c050000450529016507159540c07160007912503000d000d200d10018045550300000644d400400391191005007405152100b0f026038001e499003200043c941b07140703085404420966800c400c09540345c4914a1468454 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 54718762 1250 54717512 54717517
    0xc0c03030f1205010803070c06210504020f040e0606010306140108040204150f0b040501090e07080f0c0c1605030f0c01200106030c030803071815052a060f0105030a030f05 75
    0x1c0c041c028801280480105144a01da00070303c07041029580c1d6013180d203400c000340e43c80c42c0c01c15000d0001c1701820121150810306102c2c0880041d21000034680c41c3e900000741c0c07403141301d19925403060410850901035440800e04070302400c0280c03018030080e512001520001ca0101082500148152002401625144c0c0080034002546400380b82266103641001c042800303507030030240440e07900240800c019607004090b0002012451403451190500080040c003480c805446280c1800c140c1000c40d031903084075400c44107044121403c8411108441c0303200a00210b035072050b90301c41d014402500c0e2400c01c0100f032020301010140e40d42e0220a85c0e0b5540d00428013580d00c0b240c4240e40d078402020000030b0110407140080d6019401090320ae180180e002842c528903404001002442e1f064100030f421510404c00c8106202030034a25103810071000c00c42c48084650b03d01200e0102409102d420a0701c001c030314103000719030489001c1c0d03072a078858040c1542d0310070ba14802400546900305c080c01d0317903101e10007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 54720012 1250 54718762 54718787
    0x270906020c070b03040c0b1303030c1a01060315080604030203190306030b0705042603090d2f03070e060105040e1302091005040c1701031e05010908040e070c0c0303 72
    0x1006092090040e8590b191a0741900038210001c0008180814491001c545100410b40c40c440c0929101813071040c0b50034200c46220040c28031810b0340c2c1940c01c1020322107200d040040d40c0c1301b0046156035a60001400340100d01070500000c2101a00455209800300f1514440d40e09034000f58a010b012044106048808104110402d5a02d06010000540c400c201c0b44c020041540c032251900e0030030586030034601e158884003501000148110354044008000d5488400d0101c4a10a0000302400c210300420340c80c848100403000401e024004813071080101790901c1070240d084441180d182d2070075142900307082c1c3d05030b40800d40904c02004800d2840300041d43c05050503038015039500055003c550003240580c0c1564420742c10120900103410a03100d4071801042a01d00041028950782c21006651b4060002a1820440c00c08180c03110b03031251074510304258450000c0040d043e0600300140c854002d030181c86203103003508004c161050300c00c280c40001c00740c00800c800c0d00da030315542c1d0603243c0f09015007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 54721262 1250 54720012 54720023
    0x30c0d0308060d050f0a0b0f07020c04050711010510090501060c0c05040914100b191212030b03030a02031e0301050f040506040f0207060b03070909030807033c062709 73
    0x8840f00001e60501c0420480c0303500d41d00400f020481c6d40307000101068010b042e005100d06440800c50b449500013100c078130046041e00c0003c0c41c3e40742e1351012154001c0300c10007115a5802c1906004401354099030741070817070310700c40350400c140d9803103003070445d500424100c000c1c0900c441000b09010703503c1e02c1c1d40500303440f910035845d03820b10034510705c0c1140c140070b0280b1f129415569111740440007814180343c0d480c1c01c2c2c003d108030b10301094140307001d20040221f03034040500341d1085616082c0106029600c80714156100400702d94403168a403100a6803a4090801c40d010703290607a85100003001c800d0280c1e4180d52009100c1c0308004034580c2404020840107242e01d41c081e4850f2004114040144003c04480e805042e0100e001d041c1c0000b032628040080d8050001e062130310100c074002c0391380164071982064161501045030614407005c034824144003480341805602c0b5080c03074081110403045a4488102c81c1d4424881c0c03958030140c2c1c41000c00c3c101c0e00c02c00c07038403171404a6407410611513226985440c420b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 54722512 1250 54721262 54721279
    0x1030305090d060c1d040204051e0a0803030108030705010608060105150315060d06060905091510020a0804060305090d02150a090f06061214010c020d260702010506010e030c0d030806 80
    0x640b80c40f030036924a420140b0200d9181e02506a150b600004000b2a21500b51000d501c1c1c02e142a0202c1c0b100d0b02d200f921040d0410044020088581c0c4006a01004080c860116500c81d40c4401032140c499001e001d08071265840c0c00400103103501e001c1006070486100502d80820300151007110b08080d0301c018210b52140702d800c100000190ba5840c068410311115000000e151814200e0240ca2400d407500058442c1c0c001c60100122506c0b410801494031105540d404c81340960107105900d00403c20310000c013007040104000c035186030b2592100307100d0114101154070101d20301c1c0060703031119420030300f2500e4034100400098000c034140e0015030a6a1086406541200f4242c480c402140c16540003140f02d502540a080140f265054802400c6a0042c001b040002c40070070f400395542004013142c5061003007003004240b07881d2190ba284003154803a0051b007001e078905044024000c0c60102d401d14007040c40c0e01920619810001206440302d0700203042c0028962180e1130641e0144d4005121031340c0f03c09003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 54723762 1250 54722512 54722539
    0x311060f09040501080309010e0307030b04020d05032106041b02060117030906040807030c0b030108030d0b0112020a02010e0f010e0303011701090507060302070320061b13080708010f0b090103030509 87
    0xb50301c00d081c0200041c901450702d4008590005100b811030140c41c1f8071030f500541c001d03c04585030600d00d0b44c00540c111030b60328104034640342c41d604501440ca89001e00030a015441402c620b1880360080c4940070841d820011000211901810920219080b50040e8004001880480c0d0305202cac0700031000701901101e06000c582c84c00a4a1a8415000001650403401c41002000170f20f50701c840242814440090441d81080d045580d00c0c00f030385007100072040d03e0310101082170340142d107110319001058200b5996202c403400f020f4080c102d950b00d851002d10548070f600164070018030602240d50b000e400a18a164a48565500d28000c00f0b01501c0d44d82d581c642140000810400040000302419200940c1f19849428003901c40700a401c0340054510300090250701301c1138045141c5500000040c00b02e002410307281c0050607180101100c0b200840001400440c004100203130120855005000070b0180d8030745071402d8010b64030b01000898106540c2001800080d0151000c4c04984002030600b40c0d62115 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 54725012 1250 54723762 54723769
    0xc050a0305030403050706110d0807120603050607020d0e0604061110020703111204060e040525051c02070f0f15021602010e01030c08011206060e0702030a0210060311060f09 76
    0x515920880341e903030000400300104442448880c008100030f003800b0b0075040f41e6458043e281c0701c08004110420854000295400e8000d0310107285003083e4080800149481e8644143d8a00301500c1d04000b600c1588800781e0418412181074404180260049003000e107000710580340c1071401012040d05006203d401045856244040c0c16521300a544401d010322144200d0340c24441d02c03800122007040b00b00000e00c01d10b90420500f0480150a1300c0000b17082e070b181083d81594401c0a2050040c2914014248130002d074400081c00501e04449003d95900708080301c406d040f481216001040c04070001c181c0c01c08111188060003401d402240c1d01200441e000c2d207000120380c883d000c008504c888020922055503802424004403804c01c2c2020441006441809003400005100e0105c018990f280b12030100704883cbc00c02c00017801c1c41c0c001c404860811400103500c0b41c001a203104014410740180e000c0e00c2c11036018802c11660401021110f100700a414404158088219031034481400c204902542d00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 54726262 1250 54725012 54725029
    0x121030203120f0403090806060306011a07050d03020414060403050a030507080d09060516020a0302060a0e0a05060c090f030703080409090c210203060901020a08161b03170703091104090c05 83
    0x600c0b0543d07802c00c038a0a0f10b4080d00c00754807904410941d6010104003d5aa140010100e0540d80c489860f440040f02c0442015800c3c484c2440041c030900581441070030030b54240e000f61090b84c24440c089801d40900c0350900500780030b00d110281840d44091104400309000703a00a092940c0183c40081c039010242d040d143c00e454004004035541503036102000035250303105408410603510751002e050f05004a071002940d60502030800810350f0340d1604540b40040e801c0003e02001d0f0391250036181c4030314007140050050740101c115103001d4001c0d503120360018900828200b0a0340d5201d1400d90a080c20702064034002c140d641c0c1c080355440e034030f031002242061130412500c41022841d21851110f2020b0f01c181810444040c2959030268014445880499045040315900400703044480007424501c0004942c00c40c8500c3d035a48422100c540f014082c142d0003000b801d000240501048001d40703641000b10200d0302e549502801d8034100f91036541c070724a404c0e0010781c403ca004c0c10031508076036241c00002d0b4945 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 54727512 1250 54726262 54726271
    0x4030503040f0510051209030d0618060504020c030f13030807151109100e0a17070801200703080a0b03010f020c0c0909070611100903091d012103020312 67
    0xda1000c80c007003019030503900081d8050b02050381e001c00c01440075500501130740281540300c840c101a540016404d2182042a2501c41058142c10b004080e40c43c0c807100744041d11041c1a0f0101410401c011540d401c1500032a5145041e003402585460a01c4001d024540c201000c000001060000300001040c1800090003070640034011803108581030b10380b03500440300e030f000c0511034440e024004124950740e0386c0d890802d03415081c1404880040d00345e000504208468104000c80c88201c0d200a001400009904058030032010003001403843c0e403001ea0740a40f032103000742d0004a904002c0a00064814a00d04d0b4102c4090200407980030b08100020f420f54508401038500c8a034041801041c6820030004d00d00300d0f00d02500c80644504140c404181ca5810600941c0180300b144803c82d259100200040080c01007164410010b60700c480c83c0040c14040148140052258400945907100300350024a83c121421209141092440820452400c0c0082e100a8040d40414094190301fa43c440034001d108 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 54728762 1250 54727512 54727523
    0x10080109030807080a0902150f120a090c0605070b07030e0109060c020d090f1202040509250f06030b010e120f032d0f07021903051c08131104020304060b060403 70
    0x9440c00450044c850500281a00c11203401c1002c6c80000da190051010000e100c0345900c0c5580352444505400729104c2c02c440c046010704c2b80010002c00300160f40c040d00106111310141451140d13030f404110745900512070003901d1903a403030001c076940728041d03806007070214100c10010a40401c55101c26040311401100200560404080307410400d5010f040c44001c0d0100e054500b6426040480700240b40d199440022300455807100881d1441c0710030030411031094558120300112a0030200310030307014103003032150070180340c201040450346034000d00900401e003a040c2c0d00e0402100c194001c02c88070840f50300354404603010340f09000c102c1100c140014105201c40c219801116500004180c4040c1d40002c0002503940040c0002c1301c46c414214211001180c0440b640305100d8510b0700241030070b9082d030340000c20901c40c1c481030402c14070f00700010403000446500c42c10419640c07951400986c3c40310340001002004000c4105800346044e034050f540003802103d000400e1182d90000c950240d1094109840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 54730012 1250 54728762 54728777
    0xc0d0f20010305100f03080f16030903060515011e112a0d02030a060e030904051501030e0c01020c040f021201290703050301051c05030f07141606081008010903 70
    0x84a58050082c15003040642030984e01c0c4034036188050303480359014000141244000200065200c650f40159060541601c01c820000740041ca0701030032055103444115602800e02000038a281e40c1aa03c15004890603140d040e00741004a061905142e4030505040c28010f003120b0458402400b000900340303c00240303503500c002c402c1e02d8074011211800c000c4040d06c81d4400505400044e1004921600c91540c04200459113060128445045014024826820070310303010800417113141c4007202101403c0700781c80400806551034a5140c40d00b0040c0500350240e4402c8440f40b48170f007400c1c0e0000112a40c001c0c001814080200150044040e00382c0c483c070311000d940030388070003640c22015a8298000d810742c40d0601d043d400b650b024060b4041441441e110b8400310034070500316079100520500c84e640c42030550342e441d07250300300f10700d90703a00079010556400e5140490718410b05800a2484203d0158411300c00e500b9140800440e843d690040007203552040741000010092001d000c0d000885200703894040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 54731262 1250 54730012 54730073
    0x7020a0803072609030f0a0302040302100305010302040f0903050301061209020405130b090f0a030e03010b0301060906091d030f16051204031502090f0f041d1005060108090c0d0f 78
    0xc000410750000301c22010f40303034083c803c80003400012603d0441c41401e0380394039185500e800b60b000740903070f070f00c0690041070040385a00000e074180d0005050380d03c00c8900300817140d9004c928104454007000b000b070220b00304000500c400b500401c0d40071454044070a02054400d0280d0204058410071398442d8251041c80709140c080102c0307040c00c99488504200184181c0b000c100146644808490f40031b001c1c40541d230241816500c083d08031b408440d4002d8005d000c210b031743d01e400900810491084c0462607180407000b82c1c40911003848223254480200c011401c203080300031600da80350301000f40020040c40c000c8055001403810b120440d0310038160040c803910341d85503061072400343c1c505061503503006104100c51500350b919038001e08a180d0f0103403482c1c101c42c200c0c034001c50010b02d201c41e980d001141c55090011205000000c020b0101d0000183c00c0c00251915801510002ca0603105103550340c005c0b04419955003088002d81940314001c1420140c0f8104941b0ac0101400904880c0105050111f0341613 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 54732512 1250 54731262 54731297
    0x1f03081b06090c15040305010e0d0e0301020a12050c070c06020307060513050604151e060f060201050606030a02030408040504020c010b03010b010905010c0803061f0906030609090b070807020a080307 87
    0x80c51140501401841c600440ca881d1a6000c40710b1540c403c81d010380c800100c210403202641c0285074000000c0000301c60303240c10325a40d0305030340d04800c00180114881d640c89040600039601000c455403a50a500780801d604a4050100180300720384400003030000b400070909404040c00200995000345507207010034241a81501c40c0102500d400c29100100d80001801c00941c259105800c10011414243c407240c104010b440c0691918070740d0700304da0855440310081503105078201d520140d104040e45075605030584c00e031401194000d50100003400060203881c0b441c0c00171341d4400e101c0c11601d40303030075156000641241c02c2111410520303903685051040740d0400744108030300d200e0f0900780714000d685080c0008141c3c4a030000300514542c8003102082c4c85840b044455101004a0b0440345a00c060213013004019542511508001904141c000550307a02e840c41041e1155030000d5110041e07544000c02030300c0e403400c007808800440c8200d00140c4c010400a001660042500c0c4c0e49000ea075410f20201c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 54733762 1250 54732512 54732547
    0x3030305090703080706050601020c03060c040e09010c02060408070303020f16050123070507030905060a050a08010605030402010927090602190203120f06061e09010801080a0c0302010302031f0308 86
    0x18038042d403003a541400814a0002130301d042c29840100410390340e03a05c1004074140151032110761341501c6103100b4410301a4658000c4c00680c2e000802d06252681d07404030b02c50903152401c64100c0540c1008001c04d021412030002001c415009040c0075107010300f0f9401c1420300394040402050186510103071a02000000c0c0100036901001e0101e43c2d508034030355000e80801a03800b800b03c80502600185990070580030b03100c81802000c00404c11601c4000c40701016066501451841000400210010510310700032415a8080d03901039580304104d0741045500e000c8801004015a03c1143c0c24034041c0481c4824020710960328843c02c009070b11150380325800903440e440b14040400355003041c001814000201a441e6500580c50002c0708605d448980c00303e05944980d1501c60070b050320b84840c0703001100b0080c00404840703d0a076142d00740360380da5455003900c541c21010020400001c05400700095846900619040812055000494044010010140c4080364002c580d003100c041410090014984c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 54735012 1250 54733762 54733771
    0x70207150203090901060503060d0606120b010e0403050d02030a0204050904051609060501051c06030203150105030625030509010f0204181107150c050906040e1602010204060e120c091003030305 85
    0x19403d0820f1000018441c0d00305000d00420008040001501a500c03410850400394115001704071891726401c1007010780b9001070007a9100c46c1c14000004000ac0d20140c100e2145426546803400c040d143d08004000e0340c4080c0507461003039000d01c0007040c169241c01a40e0b002e507200700000c005548502c030f2040280d2403250b215400003490303c0d200b0030869802000f06d0302c1d41c4201840d044d0b10914030002d004000c1010b5000070b5014440d9000c0550208902c84601c0c0c1a90b00c02c500b190302c10f50f81c0207000c100e080a200420441c00d0092055100d00501075004513820000100c00412400040b80c01c010807600560700c00c824a40301c4070788891000c600e500c07449103004042c201c842d2070102541c07500d1039600010703c00d102001365164a408020741c4100156014000001c0c01296102e83d518105d027a00c600940d6a4043d0389458101701c130140d03005100310b80458002c3d4455222840024040014003508181c804915004d48101269540c0c0c65280c0284100d882085148030182141001401c41d0001407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 54736262 1250 54735012 54735017
    0x6040b040f0624080c06070201030f090804030c03060506030a03120207030c0b0705040617150105030c1c0f0c0314072604030504080d0f02190609060905030301080111182707020715 79
    0x2605d18140d07142c21045840700368080c01c011504403134144000c1c0c01403100440140502601040100400c0002915102201d00490040c003460b1135030010540c0780c40b42c003c00100400c0c116450015102c0d41500940390045c000e003003011200c1c00b40d0b11050050101120712900048000400f404202e4000c100000342c4140300b004c5418918000390000b5110418241c401e05004003c000900e40400040c03c841c880c1c042d80707410300d10035851000c40398003070801048190025801e2240d4204035a03c0703803007410501c030300c203082c201c1e015280c02c0803e5800c00e00c00a0001d40c2c0c0134500d1890703042c0401202c00c4901651080c2d0364195901e10300602c550030700000d07404000c00c000c0e442c48203034034080d0b0014103410340110500c1a54880405803401c40020b120190005004a061100310350a102010020354100d43d8468000e101c04550503181003c1d5221b00401400004001c0c00880d0450420300190a00300050180003410407a6030305e00c055200d40100c0d20400180c2c420001400751150200c440c103001400360 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 54737512 1250 54736262 54736273
    0x50a15080f030714070b0a0207050f040203060f040203130501110406020f030c03030415020c100c08010b070c14012a050705010504061b080f07030810050901060206040b040f062408 79
    0x1d400c0a5200d01c1900c1016008100d544003c040440c01404000c00a0130154800799840300c0c01000a511040680701e030b20f103e0922114004000c0c2442d0088900c200310003007101070804030860400c0000d40010b055050540821134850001580900ca408140a000b01c18161607d01d4500001d15100c07c000340c045180e00180a60502e2078000230036290040e911800c101401212201450b00078084c03080c81038032a00c00c2d18040964031034650300c40c1c40020303c0c030741d2000749036038850620038003600c03507074400070140480c17040d0400044c4401030303d604502c0f07014948980c2c800640003001517807034000a003240012011000000410504001c2200200003e00742141028036021028100014855040c1e05261601c0f00903800c018490044514483c40d141c01c440d18ec03400381c100103202d010112451035400001c100040780c1d5107850b4140364102d51139a4000d1816035250758030340d4021140a04112030001070880300d400060414002c129610440c224840b154107003100c14040000c129501c0b4800d036802a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 54738762 1250 54737512 54737533
    0x504030201021203040302150a020d060f1d0a0f0509060a0c0e0a151e0f0306080106050a12031103070803060f0d0210050a05040e0c030106140307051b03070204050a1508 74
    0x802d007003c26104000ba40c948a5403681401d0381030047d038007601c0b445144a402044030711a550b41c09001036600d2103408000083d00d80440e0f419000c0140100300d034000d4041000b909003140d40306550f601c10903030640401c012860109880c103880050341c4809aa400000400c030100d00c0304e1080349c16201061901030340d8400c40e00701148107240e0602800811020032a401d9104030702852408011a203e05040007803c00b40410081041143c8003408000a080200003e42d04038140101416280c0091100c2c9010b45881096900040090760440c140b0040100a4604490600c05000c0060086030015a08c0c07500004000c0c141c080740c00c01620030703100e5420100168440c0307010310070328108500305143e440c88960f500b591a40500c1c0e100c44030302e00f0f800b81080300d04101c0401660407242c1c1600c3d0301d22908004201080c55000c221454030010307600b4042100c03060b0f8544854a003501006050301e16014040c3c01060030b6800460b00c05100684400f840f100006a5070f14940c000c24034032010f010071085 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 54740012 1250 54738762 54738767
    0x15030105131a130203010816031505060109080d0903121707050a020a0f230601031a04020a0308030406050402090108070501050f13170f1005010b091005091003020d0501060504030201 80
    0x501a05482080d600c40911030801148007502c10303401c500801c40040b00d80c2e0b20700100040e50003401140e60034090050803a085804480b000d00075243d200345005094204440c035400106401045da504005074400001048107083c8041041c0b900541d888440841c114180308000b0812240d1010400140d00c4280141580c0e11610300e41003030780c500e4000e5451140042c100d1800400b109c0140124000c0c1c580f9a007000800c0c50001440b100c000002c8002c0c6005440d1951510070034031024081050429048140459040710140d01520041c00c5601441e00c940f200c40c4140c000710f03022900f03036948034280001e601e0150030090041c10310600816425080c000000e14a001e1020031a45081c0d02061000b0080701c2455a0805011824010442e4080d82d00c40b041c0d58202c40342121308280181b40c000c2c0402c070300c64040c07181644d082002c01407620141405010001912806240c01c000090000d1003055551400a0b41c2c041d4083d80c01507103c04180704d04004444041c1d100c1ca003071000c100030800040c1d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 54741262 1250 54740012 54740029
    0xc0806030a062d02030f1e0f0c0723010b060915030a0e0a1203050a14011502070e0106020c0a08010c081311060f070308150f0d03050c0a0507030215030105 68
    0x41e80001c020411884040c0e840780c0301c039680c94101000d0074220b051269100c00030741c0a5131264841a0b2140c9546e240e507c440842c4a41001c461143c0d03040020004071030854080f0307266000440010b0480c501308194541108203500e858105907520030f04005018a80001d00031216400011954140b41c0307040640015814020000c1c0c120301005c004c80003c1c406615031307200e041141c4c10f141c183c07040c1d001149410f44003003400460001c040307445c0c440070545c41e00592080c00d40b00303c4200c140c0300d084c0e400c00d46c044c1d0b001c810046580c005c62264a4021500c4611010100c2c000d0545800230a05040540c0421501d42840d40200c0d070545c0c03400081120613a4018051364100c202031070301d4501d0308150b09140b140e01b244101110f0f008040090742d20a40007107103005001040c041e650308484c030b03110340320f51044066107902a43d40c403000f140440e428924000600e1159180f0a00780f051071320400643e154109540d100d016503480e00180030400560402070825480b0008180045203550b040600041041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 54742512 1250 54741262 54741283
    0xf060f0c030d0b100e0105180a03080c0a02030717060a020313050703050601150305090304290705030a0305160c02101701031b08030c120f090d1103010b0d02060919050d05060a0c080603 81
    0x255a980c60300081c89c2c0702c501040740a5900140216503d41003030031410340c1c80320b80c0d0b01e00306d010b4400c5140002d640352029140444e04d2101e0800781140d512080407440280d00301800500c08080140c0383d0070009079080018600840c414405441c036507140040e11101980e64118850505080404004440001208403415581c088164034000c140b8200446c003464000182551105030000d51003051140000180c806001542d074103004940d50110300c0c410111328034800304045024450038000602d403200002e04100c0c1c1910f80b0304c844000c6401142103120302039205480c20030300031095900c504031005000c4043c0031544011898902c034400426074841422a40c81d07a11342010a00c042000300482c115a16800c00401c9542102a941440010140796000c42c52181d86005203d00032030601c19258085580c004000d030b41440e07490004d01402c201c400c0d48012150030100c0b03010a0941d00e0700307041c80c0f615006500a042515040004004484200b110700e8140130081041242c0d0303130350005100280 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 54743762 1250 54742512 54742537
    0x5030712020607060c020c060315030c101b060f180501050a0204030b040b0406060f06030510150203090108060f04050106080702010c1e0513050a0602010c030513020f060f0c030d0b100e0105 83
    0x85c00601e0400700e0030310510f0ba0841e680310701700000f4080550400722052150040880036998199103540402000080c959400c0004c03c044044106040c01d54481083d041d038081c80d4041140300120010710226007080d215481c5030781c00c40180c81c05100c004d1040560101c00180c085240c00d007191039006000800400c010400c0501da400101000303001d40113500141103142ca0b2080301e64503224003074040e06c01100c00070880080c0c51000540f203d80c8508020182601e0740203503261060140c011109400014211504514250804480783e1035906c585802030140c1da840303210302d00b002a802400c1d03a201c0c682403001c00c1340c0c0b068141945c150441c900040c00800c1d00b081561200d18021003080110a0340c0210742c40b1000c420005072040e019044240041e0155500304101d51303804806900a50603a00041c2d00050070707620071040c03414184000c101100c0802c1c045420100804040e9255038030082c1e5203084e40361101c400e80b409041a01040020302e9141c200261060010400208180500709140d420f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 54745012 1250 54743762 54743771
    0xf040b090f0303010e160c08030a0c0c0b01120c12020f0d0218040c170303150d08070c0612110c0d0e1c061d12040b030703060518010503071202060706 66
    0x351100401c41015180024030950b40c80f580d40d801200c41800d400c0707801654042d10501d01203000c2c0d02c0395405400f0940c1c07042e8800c3c10341d29001402d10080408880030020300000f1110800414001d2200c0c070f00825082d0450b0704a6491880c6c01c00452103243d02c25a040c0001c0011400103070341d803555034441d0003c01c0d21080928401c0b400007482146468100980d62020301c0f00b4841400704190942c01038400a0b022816240300c07003a0700e540c0d684030441e1111100003000c0c407080100c0c984195105041c82c022070401c0e08000751a01c403099441c200d9408140032a4400030003540207591030040303854100d034034061076013046500d0440ca6116980c4040b2401005a0311050011540c0c0b202200c2c06035048628022440c40c00503c1d215000b0b1940c1d01c40c907a152040020505231030748000803468020849245101d08041c5000106c40641d0005011541415100c5002150f03e8442d916111b004881410186100e94546000e0501304170701c0350822042c0b002850304000241c5c59410465005a82c070040005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 54746262 1250 54745012 54745021
    0x10020309040b06040308070c06020606010207050f0609061c0509010f0501180f11040b030603190201090e04150e0c040501050301020f04030f0c05060a1d0102030a0801090f1b05041d0f040b 82
    0x92444c4601c2d00300529a00e00810b4800074828051302080039611280c0844129403500001607990f2000c6102c2c103540034070100805122400c1400143c0344021002e80403a052401543c84141c0a000d1b544012002940d64402c019400800b4011443c0020050008202c1541010501456445840860500c91383c5070003008000312100d038010710740320610383c0c0315a0311b854403031000d035400b5441528600d100e4400c03800c0020740c01503902c40039180c181c0c0c141c564404c024070700352650040c82401070054407a507107010040480d02e0403501070054101c2003c400741c0030a50503241000115101a040680203070301c14030410f2008440041200c05030303038218104031102c03207080c50403a4840e01c0c640c104a4001034045080328889401114203100c1c034490840d080c420200102c01240c1d0382c0220141c00c00025400801088000e0711075104900000f801803022807a0380903e07c0b12a5001031031200a0005040010104100c1c0080b000f0145c100f00d6003584104a82040d08105080707160240000d015a800700f40440d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 54747512 1250 54746262 54746269
    0x409050a0209100e010509070905010c0809030a0f050d08070e01140d0603350322050a0b0106090602060c040509060105040e01090b01030e010e0d030b0315091b10020309040b 76
    0xc030a01c1d8000e20303103641c61030b280c002c0500e4080f452081c52503083c4000008074951501c00344291241c0c146585a030b119629001c0112000d00c986081955104010400e20303100d030700d083c000403018034000e1801c1208000710f40340452a05440e000362400300300f007580622008a0b40b01c103026400d2102482c200305407000c03540c02c0e00b1051050380102d0b00c0040c070307041d400010002e4a0310903403900340447c0380010000203800000b1410441840f90745504c40400c100295585540c07004184481d19503501586001c10290341b07070391401a001e9010f550681c0074030010002c680d4018029005040c12f803002e00500c2c200101076107030314041e13406418481ca8800c0001800c50344101c0555004104500380c02130203583d2008036100030201d1b0300600d4002403d10450103c03141d014002c000c5000c8442c4010002c0f00c1220004800a1269200b40f951600513010184060007401102d503004502110141094050408200030600b80c280900360050b4951910000b039640c021082d90080b000c2560089503030603208000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 54748762 1250 54747512 54747523
    0x120105060a090e0f040c0503030f09040510030b091506100905041a03030a090810020403150e102a0206040b0a05070507080d090605010b0c030711121903080105041406040905 76
    0x3105000b6124081040921000c42c044d8007650207825180310b619103036400c0c1512445022401c04014034108007000c401e090035030003a9804801b6040c0040b240d42c90381d031a181c4000703059407400f56651100100c08002c580c0442d0860b000101151601740c41000c6d1310b00500009c41ca403051074401c0f566014015840e5100d680710860464000701501c2c3d64408102d80541505540c1c001c1c8540c6104407401e150105400707100310707000d0701e80140101d1a19503540d40071102405a5070004000c900030005100f00242142c06140c0d6007442c031080c200d0000070542d03d010900f83d0000604c0c411540711005000c0440c40194810341c000602110100721035841c03803002d80d4a841401801001e4400000b6907417103040c140d5004001641c820201801b043c5d80e60400b000d003d00918084104540040205500148001030502d608803005003600700e074011050840741c00e100d001240320004c0380410910804041d0301c5441c02d4003505040f2410048120404501d51003044020802405507a481d0100414808100007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 54750012 1250 54748762 54748769
    0x2090d060914070b0a0e04020d110301091e050f180705060f0304050c09250311040906080f0a0503040302010c1a0405010f060603020f1603050c0303010b030402011202120105060a09 79
    0x810320a1080901d090030084031442c4500c0400e000b1840046a42c2000e24211510381100d503036030380010b030001c40c1004021f40c400e456a4400c0b03655010580e41c0c400819000d14028910000d000840420b101e4406410700d100003d4060424070304020800040c000001c003540002d85981c3d005440c501401c20949040c000d90000c41d801600450240004a0004002c5109900c10b509549001c1076030800d200070340009450124140745140c103074415000c030711010100760000d58074000c220078030140740495440e4001d400440c0e8031500c42005102c4048100001e504203800e1000500e04412943ca0b074941341d00450000904000170900c1c0d18052145d08080c0425051104000c1c00a905007898240e009021024088c0052400c212000031418007a10a8802c821042d100c590310b004084011040149201003085062040912170740810f6402040038501800c0f450800680d079083c180005841e0402d5082054002d03030040214009a02d07054914a044a00664480e911038cc1e010308192980c1c0358682 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 54751262 1250 54750012 54750023
    0x4080706180b07050a0f110f0d0f02090c040905010f0303020c06040614091201020307030c03050624030601022104030314030c070f020103180b1b030108030a05070219060509011404050f0402090d 85
    0x1b0f80101c140410700524803655002181c0c2c1c007512950301d6040c40140b240c2c7e101c0143c844000d000043c405400c08002d41d0340d00c0381c1100c0b8000c0c50700b91a2000d10040702c10a03040103005a448074410f20415404000c00607035000b04840320313414545086c030024044072100131400348481010902d030b241621202d14001052609000940d241c1c6000d0200074000c2041c030700b00c500042d003000c01003103560400f00803800301000104600c01e101e01e1140d8900a981d4409008141184114240c8102040c1d03504408000e1b07000701c4000e19503a84c614100103200d02410314100008410820a000c10340444404403482c01e40d120344560500031080c00160003e142d105d541d00050440d21004104004225a10303d218055102c90000c41241d00301d101803040c0400d0080d403003143d008000c5221040e009001a1600510040500102c0c0d00d0003130840d040c002181e404000414000f042400403981c001607204000d000c00440141030901c0d040001e090b840c459450507004e1580082c141405440340c0840710203954011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 54752512 1250 54751262 54751283
    0xa020a1b08031f051305090f070f150906120504050109060e01060e0c0a020705011d130f0f29120111030f10030b1501121104080706180b07050a 63
    0x6040c9100706500c1107411a03ca55844140702e080100524a200140c92025140300007041020605030b00921010308130100300c0c0b02c0c0281030001202c041203013074080c10f80140c0c0750540c1d502e4481038800303001c6561108020300c040b20b00c0901c09940d0241e044513110b903110902041c141c1744ea090035030040502c03417806031120742001c15249000d60150082d804880c603d2401c545d90b0b5035014900119802101c41c2c03040143c12042d0108180e611510400314840ba2614910202d0101640003440d806c18040d11100000e881300075080c4400424400c40003000e00124051145406844410f0342001c0618440001001200320012664031102070400b00c1036841e01c020089880e0b0000c0311003080d001216a03550007941480050b01d8026081e080d02c007200c0d88681c2c0c0d0305103030f02c074036511701c1200182d01c0403181040000800000f0405c1c00d4040c1e580302c1a401100981d885050901d07041c100309068001d0f03003e1004114034001c0c0c02104801070421240349021694540c60b4500d003440c03c06070001006000701501c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 54753762 1250 54752512 54752567
    0xb120d0c081803011d10020304020a0905060310050a0b0108060607030c121b050106030b070c051b0f091e160905040509010204050307091e0605010206060f030709060b0903070806010e0a020a 83
    0x320f144041700826120460b0300520324850354a0682c4402c440094001011840030441d1034556000981c002c0d000030280c41c1c201300f60350002070881d0021146120555100d218110031543c00038016504000c3c2500c0543c501400c98402804d1104034100050030b031144070f500e2010f00c910407080c8d40c02c001c1e20308c8810142c2403503d0414074041c00007800141c1d4140d913a003000c5070101d4010f041000c0c0017503001029000b002c64440401c462004481102c3d0340068143c000c410030b696600c0703001c5118005801200b20700700c08003580d9100c0c6d000000c2602c201c8103114010700110710740103c012011203104450102c1d8a9545039100e41c068062944010f8051042c042d000c11940030076004081e0744032009000070070803c1c0d100c0a0500361841440303400e0160300312002107012400e01980300180080050110750501c2c3c1c1d03070b2400b0800c80f601c9901c0640204030205811035145400d004d62401803615800070481075042000220340282c002d0016400c3e46e03030000d02246418010403000d8584408040c1e00c954100c4d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 54755012 1250 54753762 54753791
    0x6081c030e0f10050c04060903060c02190b04030f050903030d180501060b0408010b0a06050403060f0b09070c051605030c060d0e01110702011e050315030c030d030b120d0c08180301 79
    0x3c1050b006049a0034903000554610b40c0400b81d5044038030b80d54403144044c0c41e5844a400a0080c03210300c80450003010200d64010301e82070340e00400c8610514032455245464180107080002100d03410040000c20490781c006540d000041e502c0040c0e20706030014008040c3e40b0801014446900010015420031301c00152540080024008850b0900c0092040030464000c008400600d805400c0101d14188018804103805600032110481c0e1481700060350341e4044c0010381e20803012a400400100c011a83c24100501802031007a25a0007512231444d1504280c0003036250404e20001602900c00459030052040040d00f14207610b500c0400204040d182c3c2d000408541d502c409800d0f03002c20700801a03c282c3c0034422024012400c03d070340e1680d0658994241001d00301404180c919414424604501401e41d401e0003020315840380341d10b001032400900b10030b0048103c03041c40100030729000004801201ca800415805105900010044c0e8414802d0104440600c1d03420a980c5c00d580b901c02030f2500002d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 54756262 1250 54755012 54755023
    0x3011403100e01021306080c030f1302030a0803070e010507050606011407080703020a110105070b07140f0c0c0a0e04080906070303020403060e07090516020a0f050102071a15010306081c030e0f 84
    0x31481030741000b0b0f9039106ca1060340d80400660340c006030b0300010000103600242d0003031590b13080440721002041c8841d1980011345014100c18058601640000c14002c107140c000e480407820020a0a1031414504980c031495220b55004210a050041d000c80702a103242080044400856002c64465100c81c2a410021740d940c0c050001215040243c00130500ca540c091030176030301c0303407588540601d08603a140902207030041c980704401c0d0740c01c4c141400f000601c0940a000340a1541000004000c1c0c150f024080000310303001d6074080d0040c2c2c0240018080421502000c03200381e08020b51f00c90340c0e141214076080340284110760006d016145013645072101d081e0b01003211001c84142500500003a140e084064080c0e4903041980341c0540e0040740800001b483c0507486000300b60240f000141414100e03116541085114480505243d1408003000031030140b211f0030310400380302840c04101c0a1700b09915103540b05a206480c40c11000c2603c62241c4c2a80b180e0050804841e02030f069650303000d40c1c0c1d0411030b03844 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 54757512 1250 54756262 54756277
    0x151a0304050106050913020d21020309040b01030c080406110f040e18012c030d1107150614011101091401020711100801120c0b1803060906040803011403100e0102 71
    0x39420b103d00041c040c40c01240d020300444400740501d5410f00c01d98204150400c00d500c08507104800c48090361b00c034002407004800303601c500350040c50360b51002108010841e00e03101d100b1070600d480d040444c3c00e190b0b48003840030350055000c200003030a03c2c06d0504080c0c043c022190361180195000501091034180111150f0103880b03041c507140c6040100c42c0a441c281c60420f19805091084520200622410082c071521030b050382c403064900d4900c58440400680d9601e4041103043c04001a40d4020000c603160031100200e02c0c07074800c200360350400182103142c24184100904000d60300290181c07001c029400380303c4559002a0300310810114000c031038042d41140b101510704d40302c01120482a410106404200080c250f40c0700803c030380c00c2400700b1010105d655001c0d1120300406c03401052085980e40140b4603515038060080020310080708140c6020f00080c2410f200360441000c3c803000500400642e41540c291041e14080c4d06505000310385000c42d070881540c065410020310506145043d4001c1041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 54758762 1250 54757512 54757523
    0x406020c010e090a111309060501020f0303071209050f0d08101d04080f0c0111130b2802011104030b01050907020304030b070806120d080106090504110706151a0304 72
    0x46510303210040d1040041c02c96590b4118903102c000920400d010340c820088a50040611814465180c40c0301ea40b515aa801c54404150b881c2014481ca42c1c04101a4070a0405500203602d903140c0707100002d0007602d85041030310001c0d8072445001c0c02c20800340329950114410204076281d030034500c1c02c020140e01040d00d502100c18032911001c02c0e1400c0c0100307038105800d00c41983c450305485a65070a54954411071000000301e0051000c0b42100d42c0c00e00903020300c41c50988015859524882c40502d458885a0242d00408001c000c00c1303041030303406414151343e45c4040400c15104000501d046e405000742a104039201d0300c00040200404c01d8070881581a104280c2d0801056512003500307030380d01e1007030f4000030303050780752440003c1c4405124250315544a00060503110440000c030f081a45404000e03411140030418000050050300d82c482043c1c4001c1c1002c5070148040400240094030500c034610000c5c100a4032031940d5200c440224000c0c9008004d136030284240c0c2c0d10510b090503060781068804646 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 54760012 1250 54758762 54758773
    0xa020705040507020a05070506030a060f09090201020d0302030906060d03090f080303010f05010201050721020f0301030506060108091b01051809040c0e0610120b010306030516031b08150901020904020f040602 91
    0x2207852002500c1c1e00211b034031a0080080504000800405410007480c114860351601c00c0030941d600303950081c034020002c0c101d012614540910029083c4010544030380304140c414420000106000030741550400001d54012800c2030150800301c13006c00c200c0e004200c100c16a480009000c0c50300000540c102c50080e640100c0c3c0703a403035100481c20707a0019208000003c2c6a5a134424200340c1740e0980030307582000003100525100001994210b03981090b40255940d41148080048a58105202c983d0282c400300140186e26505240e03114000100401d00f410000d010450f41103000b644e120010010600a01e62007440c0380078a40b20004140c00e010b0380800200740c034041103840c100200744421070050703902d50f00c64a0765a5681c010051040c1c3c0030f820304040d22807000201041c002d1007494044050341507000d600a085041480041608104000ca28401d0840801103001e02080e1000480410400800030383c5800c5042806800340302c280980c0144000f9201d41c103040668002d00455000c0d409840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 54761262 1250 54760012 54760021
    0x7020d02100c05041a090d0b0106030f060b0a050c07030c0b0403050d0908192f0a080c0d1b03050d08040b060102060411041107151a150414060f0a0207050405 69
    0x16540c00c4180b803404280107101c1880981c1d0300300203079910060900c13a42c80c101103182000603030510322079506840c840101d000500c0610b600d80203802c9183c00d581e10601080e46003d805110511035028070104100000c14859003000c01030042000840d048000c0700001d944580e01c803182c0e81c3c890701c401c60b414440c45140c65a108e004480b03030401c90b18640302030b0802c04880c20b0390703003a021111181122504001c0c001004491182c019514100000e43c1c15a00d05841d844140b16500d10180c018110316408102071440e1992a03505410f0240d41c802c00f009400e003903040c441080b0f8411900001e105004806081e0f02003548040c4c02440349008055080d900d88604005a840c2e1406803809041c4110410841d0038500f89034000b2215007008410f640e20f0101c0988030f50030030b0034100400d90107403a11182e01020201180d02000701c90b000441d001e130b02c1d1036180545403000d84102d105209a2001c04540300d20259078000c10303a117488008510f502c3e42c035088454001d48407440d038040c951040c0c0ca40400b06 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 54762512 1250 54761262 54761293
    0x101505010215071214091b100f180305061008010612050304050d0c0317280c06050711030705010b0301050906061f21020d060b0306031011090307030f030e0607020901170c040507020d02 81
    0x21230b00303400f036803205507540100d9182100d0a034000c0c801240704400e02c51303001001030410000b035403240710001d103120030720360800d0304c0c503420748010368800c481c440c40c0c1c0c03086e00020a80100c04c4404403202118030350070708030b25490203241c130040e103034030141101e6111151444150030310001011001442101a03003c8184192100c98170007510b1810000a25526002e000044103640304a42061040c1810300c0c6d15840100c02c4c900e10f50160004403250794444140b000c89090034046c00d50032440f203d001c1c00d100c0c500f250120f035501c4680b4030340c0c2c08140841d01d2501d074454043d0100905001310010351605444020104d84080d500545001e04800c0c50002c00169062154098901448009015182c80852803820901411848602c00c041030402c220000741a0b50410003a07004500c00d0201d02600401400c1c05801d100000c07c04c5409a90704204c1c12005a96061046055541c1c0524820b6031007042c41210386841800301103140c00600d0f100521098035000940440e582c8a07030340c00c45600819400e0407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 54763762 1250 54762512 54762529
    0x3010f0e010f03030509030a211e0503070c0611070803090c09040512070303110409060f0f050105090103020c01090209100503010b040e06040b0402030f101505010215071214091b 78
    0x1024007810403042c1c2403000904c503c0041415400041c00c4031602100390f00c2c1d41d42000c10885084015081b070380108604160030a0400b00e000100310700408076181e00c1800900240300041030030f400c02421703c0001007040704a40c0508840a50001031940303500103440c3c0040254002d40d00e1a181c0c0c0b0942c00b5152403454405035542c031441d448006460000307280c0080c10240e07000b10200314103060310340d403149059041031005030000f00807036840070032100e103807849401d40f202c0250000c01c1d0441ea000c0d014041c40e6000421144a03c0e0286801a0364007415015180108182c2200951052040d070502003034043d243c83e054250744c2c0850007000020110b000300411181400010f080a070428400100880c8080311451343c010f0024056642150719000e0080c100000740e44013a846550318000038044d803042d207840c2d501402080c0002c01210f041c0b44801c0c142803078001c02c98000c02203906010041d8404030741141559005252411040303061004c10251218003125000d003440b608586a44800e00c1c1c450003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 54765012 1250 54763762 54763769
    0x4061707020d141b010207020406081b10050910020d1e0c11010e09040b041721100504020408030405040f110301090e120a020d091a0901120b100503010f0e01 69
    0x41c54022842c02040d640c028450856000c20b400510090810b5034429a480b150303c0d440078001030f80c601c101e10400080b00d00320303000b00c070050340318001040d1440407032010910f8685085890341c005650306081221148201070b0030a0300440d6a0396000342413500060b03525403844c03683c5c607811122032480d139000303115248851310100041d25681c10480400c034140d905401c1d405062400812403141140410181581500c0445030700080a0400041c808904800c1c2d03002520301d011280703825950107500440c189815200b0040c1011b50003c101320301c9600d00c103c00284000f820a64030b469031a40e500e42c4035040307841018007e50031704404d10b0060065124040540200f60709590459007454006001086032280b402001d1040308850700060700d548024100c40022035005041012b40d44500034161049035000c10140101c1c0c0128140c030321120000c4e074110035801e18240318200c0410000c00d003d41191074003150000766500440b49285e5000c40154182c0b000d2464040403142d5400c031040d102c1b0000d00c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 54766262 1250 54765012 54765017
    0x1a0304151a060c010e030301061805010203030103030c0b060a171b0a0302030d0807140f0414040e06130c05060301080d140c06040f081e03060301110705071401090f060504061707 78
    0x61054500349040400f802625201e0302c00000c40680e0300e11550f107568000e0b0000404200b07100303181a031142024003440c0141000307101550540d45075580213004610041d20040241184400080090302d0360740d01d8038000c283c4060783c9081e03030700307407603480c03915002408031003290802031900309030302810b02007855021290b0140050501c07025200c0202c5801c080034203094104100080c02d0110413442002609810860b01e000780c0e550781c6011114000710128100c102e0041d070403e2402c00e2000e001060850b8002510390411056061a2130f0514403010b40303401c101e600040210001c164150009903c0340c00d03441a842d9000701c5d00320200c074080c05000d0a00f4030b80841d8440e0b80024005000b0821810074503204940c411304080700028040300c080b45080c3c03800302ca00350200c2000458078090258450107003010040c0ba1501085484680e200c00140c002d814003108c03184041c440f02d900c5682840000c0130300342004100192076140051981d4000c0c82280c00103980601a0760681d4140501140919820f8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 54767512 1250 54766262 54766301
    0x402060a030c020709060803091c0b010506130305120301150503040503070305090f03030a08090d11030409020912030a0903030f080c0901210903120f020a0c0b040c1a030415 76
    0x403501207001e00786803603450086000e883e0001604030301c40d00640010380450805151101507102c213010541d445404207009542000420b00c0200f10108140d50541e01c0a4840c0c42d50b07144002188c0703511503281e6200078850711030049117000081c1d5030b0000c1c505a0742c51040001d600780844904032500c0c041030b14054010703041000303400c1c00240207000400e2600005401480303602e84840002c1c2c19030300302c1c200c0300c0b010030718100410095500c14800994200010b007403c0c0741e10b8001c0082c15660f4040da00460488503800586580c007a51160402000040c240c0708499580d900c01c3c0d00104610b6941c4011001302d0640c2120a00f41801050200d01c28180f42c100d10342825500750046840c03100c4003c0814100c21001c01a40da02d0085000307945440e8000d03190900010701100c0303420100d8181c0c1c0c00152040348144038036608954400b40384d040d0030b034006098002c161078034204940085070300d03800081c2000c00c8542d801071003150340c00550310450151103452842c034510f1241005441c40e948404582c200c01e07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 54768762 1250 54767512 54767527
    0x106060c050d0f090e0103060e060906190f090803010f1703030613051b0a210207080a08180105070c120201050609180307080c0705130b1003020c0f010f020918040206 73
    0x594840ca0b03d004a460900e40155450361040203c913070a810a580a540f941003558100d6410850705070001e258000810483c0780c900c0c04091030060f0801c07600c0c04507868031b5801c41001c25680200b0f80d481e800c05101c03580d95035a010a81403281e203501c40d1107081d4281c035018007507410004c4280c900c02c05001d44415155107c021861000340401800381c2a81d804000e03005141082c07201c050a02075106481d5018200f0640307842107040040c5120b038048003801002100005a180c00039181800d6160510b841c2030340303a100c62099080d00c4088400c7c410340c47c01c0c0c10084590340c842841051240100e030080c5a04502c2001242078420840d241074214816002180c165509290420520800342040d242005215070742c84e40c0ca5030080140000a134030580040c00f9900d020261030317020b1020110200007800200e408611030350015100e582c103040d800300c1c185102c6501072180708250b5140702c008001d00c04042ca9000000e400042c403079401942442c15a145100072110028091074000700301a0034041c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 54770012 1250 54768762 54768767
    0x203010302060906031909050c010908070302030d050a12020f04030308073207021206010302030f030705060109020715020c01060e0105061c0203040f0203060403020a0302010c03050c0a121503060603050106060c050d 94
    0x2808006050341c00c4da803681c800303904031f104100d59148503e000d0282c400080000414045041d0440405500406420401642e0002c0c4c21180040d8505149031101c001d070350240da074941c510401d44411030000502c03243d00e001d00c50007071040c1c81c802d0302d9207151601c030f03040110751031447d58100e14040c00c0c00c0390880040d107040c8400002029a000c0030540340c03002d680c2c0844c9680c0742d03245c1c038021190711150051046180038405000f1201d281d030015420400c00d610f8450741e03810b040c4101d1210f01c2d4005404001e1022925921002424030308041d5501c4144102c202d009044511030165078a0012002292628100c4100d580300074481d0180034212941c402040000c0d4405042218000a0800c1010050b01c00340580c1d44201e00070740181c040c1405504010f402c0d1015019000c1c1014a4801003051420b1071038151500d100e654a0484480f02008134840d0017030065909850400a201c180002008019002003042d80c0c42880203001036076441c20309860080500100616540043da801c1d0303510707413 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 54771262 1250 54770012 54770017
    0x110f0a14040b0909100b0f040e0901090c09050702070302040203010815060103020f070206031302040501170d0816080403090801061203020c03010b010e060310030812070314010503030a0f02070924090203010302060906 95
    0x40705d01d202c6919603a5a843c00c080790780c2c004540610194000300d402c11003034003503c0d52164070220280080c045800703d5035901245e940c0c2c80c0204024240d50320003180b40d20b0b00c200b01c1d18014690260007195256126030210740d49507034410481c80511000d000149255100703000341c5400c0d5100508803424204681e00700b112a810061005010f441620400005030340c490189070300900b03042208400c0440240c12050030000c4440d245018420450140410701020100003007990801e80b428034140c7e01c8503d4203e0b01c4009981c440e000942c01d10f000410390120080c03084007014030980844a8101140041c103080e6a00c2e802d406000c10f101c06410b030603c3c24201c00569100c4128070f28402c0c80c58136956605a07941002001e001d005408400b00004680c052140a500840f402d5018266614120010b5a24401e80c7c1558040140700030525803c0ca00800c01840503040859051048803100c41502c061031101e1920340b500c03031184410000b065600e0b8800c49060b80e401400003403508019a05003c40ea5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 54772512 1250 54771262 54771271
    0x10906050c0c030d0305060102160b04050d05031201080c0117150909030c061006090504140105100309051b01030c080f0604020f040305101a120a0213110f0a14040b0909 74
    0x41c000d50b0030a1440f59400d2103c0541e00001d83c90001d01ca0800e036000926050071100e00480464400328140103051031441500d0031550125032000071005c151804a040d40218942c1080c4a10242d00208000c3c1c000302e00010030300000ea81d0380218a10120464850001c252071032120120624141c80e114180040003551224100b82200d00d0b25002900c41d0740f500d4012036610140200790342090141c1a40300440130000d01c01180c05000410101c81c0001504806101d801c0c03199010300c81100c101ca0103504906c00480c0c109080d100419420351856103040018201e0742d0020f450324200c0c04006014000c1240100d00e4449104c1003640c07410f05020095002d44000104100705000010008a0801800d01d103da81c101c1e010032100c040180030780d105080c0c3c1809920458a0341a14440c00c0340000d6005290f41e01100c0e12200c6041401280c2c008001800709909884000185c0c5148407150400034419010a40e54001d0141071071010443c00e4000c0e801406105981001304201900c0e060202c240c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 54773762 1250 54772512 54772537
    0x7060506010f0309020a051e0a031203180305031303120e0627070303110102040b04080a110301020f07030c0c0812030f01060e1302070501060906080a0b0105060405060301120501021207030b0306070e01090605 91
    0x1064035280c00107270b00040c2075200700c600d05091078803c4401c990501500c6445191181885201612541d014126010040400c42d4083c5000c0d0f101c41803600c540d64806045a40321000c00581c1d22044560f40c036020200c0d55100740150b0b04405864514681c0402e4100f11a4640035001013810341d9402c9401c1d440080343c0552940d020b00c40491403605803002070008005a4008100030f814910b8086032030088852100d12a92051095030800105001103d0310700b581340c5880341d1002e0f8585006600310340e56410071895403080200c052440415400103500400740c104a281c0c0351b81c1d803032408541ca290603060349a0000480407810b1214031154000c3c1080c10f11407800450002d4a4039003401c202e4150747d02a50f0780b0b03031100340100184084410303054054081514044d18103810003010500500c0306108402d0940350750b003114000c0c00400e5058580000d00303a240c02c3c08030700f0608001805090410300b0796100c0e0041d04003040e5424040c1030780d000410f8040e1074080301c052400c0001d54031600143c1070f4810 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 54775012 1250 54773762 54773809
    0x18070611010f06090903020c030f060105040216050601030c03230703060c030209040903020c041409030301060e031c03050a0c051602010e04091a0a0b0a03030914010302040b07060506010f0309020a05 87
    0x2110700b01401080050100080c0c0016410391a003070003480c046080101070300903080700d091441407580110720b65054420540b400f40c0d0307564000e01a42e105514004000c1c0c0940600c0002004000da108694000c076409032040c1809a8000c0082c5081050107010a290503803200f0070400008890b03400050348440c181c2401400d0110540c0481c06450003075004800517007241808808a2502d0f02c5440d84d100c100c51210790b6a80340000c012656484180a45018060981c07002000e60364100603000c81940c150040d600c042c1007251700039001d0402520b030300c40d84509140040c891507100d901661003000900c4140044020f4580040d18401d0742e1320b09447d006a200c90381c607000714441d242d68601500c002802000c15242003000312085640d07466819200d160401010408254400e1070310056400da055030512110740500140d00038466a480225041408195202813001991102d481081d0a0329046d504a040c0031007141140c100c103078002d42c400f00d000028132641c180118902801e020404844c007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 54776262 1250 54775012 54775031
    0x9030d021204030b1e0709031e0c140607050d05031006050304080a0305041b0303020606090601090e0a1a0a06020c090f071b05120f1801080106080121020a08030408061807061101 78
    0x445c20504940c82008911450720400400c0f400c456a8602d500c20300c041b00809412542e216030f10300d0003920030304141ca441e04202065560f0307031a00311495940e01c2411a40c10000140d80a411500704031150a103081e00804004cc8243c060004c41c0d1003694400d1b5940e1600c690600160020f1802030310170b0300d902c0c0900482140e00210340c3c6d1030b000039600a80040410b0b10307183c0304000c85200c005107401e04000c5039200c2002950074800c41c403504200b940401144c88640071100350003541e043e00a4643c0502d0605000907850340200d0311703004e1441c0c00c0e02c12110560310340e40700403800740003a10003d0010700e049401b0708143d040202d00604442c884c1c41952000d061038200d142c2c0703d0b00f02500400184400244520598003503280d044111070080c207050740250714145028002c4a014415504404440f800040030b0010f0080c56a1280f60300030103c1d440e241e1905040d5650342c209000c1c1c020341d40b00311000329041d00720500354041d015800308002d000c1d030781c28400e040b0b510b485040000440c075900d07510f021 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 54777512 1250 54776262 54776311
    0x1e1305030f07050a050d0201050405060a021501030f060f050f0c1602090a0b1306030305030a09030201090203071707050301110405101b0b0f06041b030506031501080309030d021204030b 81
    0x6000300308560000b41940ca080500304841229140d121170711550002c03003400700603604201510226101210415200c0034080800c0e820107814400e03110104683c0c5d0004030400c0540c8402e020064060041000303070421020441d011a041510380c2040d1111030b00018240700c96690081c03031007260307000d800c004144141c2c0c04180c003103030207580710000d03d5125003c2c03440e01c1c205164054036150211106226151560f100500140300140501d4130050b1642106000c5c14001d4200746080c036405070494224a98460f00107999411303d035454800b60181c070200190343e180500803100380c014808802031070180303410108201c0f1001ca41c1d450051203020600d560701d0480c115400305078180590403071802440c15070440810043d00800b09840b40b0302d000a084800020304c41080c529a86500300040d0316182c1d08002403820301e000c007a1403180043e20001044044011000d032200d840c6c02d6044805410800c00140c0e1980400c0080c514109014001080401c20828480d038000c0742c0900c1c16080700d0210b034100e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 54778762 1250 54777512 54777523
    0x906031005010801050109110304030e09040618060905010608070b03011701060b030a02040626040f0c08010c020703020901050f0102120901030207020a03060c02101a0607060b0303041212051e130503 87
    0xd0003d9954aa004100140711030003144d0b154001130304040d282d403405079030183c84080074042190042038082c001400300607a5620400d0700440e40b031000d01e003024451804401814000780c1c1207400d5401c00c0d0002808075000a824401c0d90003c0d224981107a083c9088018451107011064003a0f40d2600c10001d007001070300000b5401a44c0110300583c3d02c90030004042d060035811080c484181d00c5030318500c0340c068902c0344031682051780310b1081840260315040c403400061003504010199480c2c4001d490416400245030b0045074820f030b0f6000d8040c7e903580c080051598000c80f03a02d01603045901a60703552000c2c4001000c00200504006081620540204103119600d800c00c03500c9070381d00c07a0350360b41c025010440e488082101e0401800040040b40413903040c0c000c0784120300d00030200420308100f000003a800c005802031001e0116511543c1d07a500c20920003104032000d0b9598a0401048000c4510480440f081d4001203607105042c0348003003200002c103602400c00c10f108400041400710b11036600703000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 54780012 1250 54778762 54778769
    0x3021e0a1206050906010e01030f0f021e040b030109020f060a03110307030e06091b010c0303230402011b031e0507020d032021031012060501060e03010e0a02090603100501 75
    0x808900c401d00c40d240c28001c69001401079940760b4000e000400115030364044d41815640d200c1841691303c40a4549440017420141000758484102e082c0c0c40345111040e200b0205450085500340706400104003491700322503503178002940180c0d2401604000b41031001c02401640e02c02d203030015441c11a40255180c0d60425900c1d100040c1e00e4140d4007002103810800725400004210140a0340944030704041402004010283e040c000d98410710000e0600990050003100c260070044448104070b56400001c280007140c080b8041068030448840c0e8408225880c0011039041c0c03140d50b14480d07605c000002003040180d40d007040000070080c010043e1034180301e402c0468825110005200e40c100c1e103400c41c3c40c044195a48480d84002c540d0508821100060440912982181039807504c2e00e80da4189408115001500c2280c040202002006030075401181265072541e104816054403808042c01c0c2e0b1a401496112940581c88440c05460199041500880c004040310044d00c1418505003c0c1c400c26070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 54781262 1250 54780012 54780029
    0xf011109040c0e180a0e060c0a02190305090d2904020906030c01021203070201020c070b031b041401111e01060f0602010204030804090b0a210311031303021e0a 70
    0x80003612400c00e40640d1007038050609041c4807030086840810b445002d03d280500760040060080307600020103038006a804100e440694007140340401160109600241d2000014864003081140080d82c826810300190f030700d991258a014404400c01c510442c1c00b46081d00d44585581c1d152048401c0c81313403460b40807074000320303043d056241900400441200040c040c5000b070700591550034140ea4041001001c080100d10701030303241d4a88103004c034028010603035468054429040041180310840f40910300c142d5003c66048260502011044107074025480303400c40c10140f200d074040296006050f00c14218522000301c2e08650f141a009140000d82c4c4901000c450359243c00074400307103680e1706000c0054110741c0025480c007451507544076203038441c1e882808401035442115288554035206004000d0102d0245903003582d41d8008000a0b5400741f00085000c55540d00c0340e00030012010081d40c80c5030030b4175014407100910b90b409008040d40000b0300d020b40e2031540e54030000f09541704c914000113000f440f03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 54782512 1250 54781262 54781267
    0x3030c020a0506070605250f032f040e1003080a0c050a1b0305060105040908040509090703170a020c01091a0702010504030213020918130807020612010603050703060906030c170f0111 80
    0x100085405410080c41041c81c8507c0c00c83c00c590380000107016240b109190006454902c4501c440749250a402156008103018074012404011100039105a94841405851540311514000d1500d4000d1000501004060010745e61450081042002da1800750045d1050056aa620a001070098041c6602c4204041006106009042010074007522065504004030703001902d07501f903c1e024510a2034468a100f000242c030b841014031030315009643c04200c240405520300998070b92034100d01110f10052182e1020140035601c5800028100d5400000000001529050300c900f690301201007a03043c00b41c02c01c400801a20344c031840c90703003220400800580302c070001020000c40d600d844204845005542c414084180340061340200b4141d80400300c10303900c02503803000c1462401900e04442c1d11030440d0000141580d016000b840c86400240c1d010010261a44035000c1200e60314040503055924607002400304150004961b1100d011030411106985120b000c41425226201d80031081900003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 54783762 1250 54782512 54782521
    0x111605070603151d0601050c06070f0f1b06020901050702120106080d080f0f070c080a080421050909070203040f030f03080606090904020103050a0b030a0804031a010506030103030c020a0506070605 86
    0x54810f04810800903c0003070085894100000c0044400d218101182150380c00840c00c3c0d6030048084400b43c002c96000c1d80c0319403401050240600b0100040c0d1404600360351404150f2038400c1801c1407c0042d02401c040d80c040d40d50300c1d004000d402c000030090512404000b4100969505800c10451080510004c01c400341000c86090520200c1300910003407000c18824000a86500182240d0005060151110340d07521600221940f004130700000c1c001420000d2028652984141c51910541c01240340480701c0100c44070706801c0d601d000b140200020004d1290613036500d00b15103146c0d0071002c10720480c3c1c00d06884144d6100f6484d42580200e9002c0e850b0700d00ba108054100d44583d030700031011520982404207810204200440c010002410140e840001400704401940a08261074020301101c4072003c5510f4110b030036511034007041d941c90360303041c4041501095030310780b4030306861002e030500e811079103940d409403411030074000c04a034450011000030034a910f07014054814107008401c00301d081d090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 54785012 1250 54783762 54783767
    0x30f03010f060e0d080702031603080705010516050405150c010c0807030b040b13021e0a050a1107060c1704030b0c0405040c0314011703070602040603020a0906020a151116050706 78
    0x15950000042c0300341164043d41c2079a9078480818155004014556901e030b50b480000d04001080d128a280003951040110900000b44080d000180c440c200810480e240c2c0c010382d1115164052070a0700283c0c040000384110b007081d14054031481400c06100342031040fa40c0042b07094540950351781000803041410800103903414001d00222032400d40b4100450101e000c00b00301d01038100c2c0400e044c180e40010350039501840045900414681c44171441d91642c61001009080313a110714000000140b150b2803a0400c0c04010030300a04540164642031742c604480c0e62086501c5402600d40300c0030410610000000c200e40c0e00ca4140f040c4c0e41d2039189655107051204000848807001e007444205440e200c184001010890340260544182040300041c0608658001d441d5110310b00004140d180003280020781140c00d50041e03c41010551142503403d6112081281c0da401c08000c05408003649084501c0030b910a540804403480070004180c1c9440200e0300c1c80390301e06560510403038699108280800601e0b5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 54786262 1250 54785012 54785039
    0xc020109051b06030f060607060c02030a021002040b030a1e230a1a010305060d080d320115050d1d160b030105100203090a0b090406050103050402091512030f0301 71
    0xb01c0d2074149070150b02180c00320740b183c080103003002c0b401c54141c801300350966900c1040c0c0b408258030043c01d0209500b40d000083d125000f48200c0c90251281e4130750320024260600075034050b00d0282c04402d0660b503c80d94108090710404400101060140c0c4d60058411054000d1500c0c1c0001048040905220261010f604040c01090166043c1c9443c0c18a40e0303541c150200c1c820341020074a400300740e5440c1c00c40000c2c1202c901081c003c0c12180000359445103410b8a80240300c100c1e400014129039030311140020003844c1e04181c00c0c016411814001441801c507000c1141c01881d070b5a1401c241002d00300c2c0b0810007140c1402c03088a00c00304e010403000090130020007000015407401080c41e1a03440ca40a110711045c001801118420700c000130300112222310070020359004000081100e002207036a084280c0c0c082d03000d04011343c0103070306125010680b94041d015007809260f000d03258002c00c2ea02c1a20116800b03154a80d429400360030f0b0180a1a80c0004001502070f55004403030700350b0b8030752510890743c1c0c0341da = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 54787512 1250 54786262 54786283
    0x40f1404090f03110c0d03030f0518120a120501030f021002031e220e010611011103010902090f06041d0609090d050a0908010207030e010f08060f0d03120c02010905 72
    0x16400c0c1081c510009400c0040082c4440e894140708103d03800b5920940c0c00c00b010400c08030782000c058013013030301451341c190070138030b4110140b5000f0040340d25812044c00426000109400042d80040040705040d11608020030302e5216500c0c1c08080d0080c001045010f42c1c2d4281d006440d420f6200001d84154680106d0842c0e810309240000c40c80d00c2003c11160700980038442410044000204601a07502401d40d010000008152044a1103545400411a0040c0c1c00c1c0507450000744110f40c0480d540105205070013034091402e800c181160710384400b010295000c00c010703503004400c00004400c5512108043e10107000f0170b030a03500c0d100e55202e65030b624000b0000d06251055542005000400d1000715060440c800b040c9803850f5501c0d802441550145e40030b81c008005903100103501024903600100c0382001c03034400d980300b204a03100341000316440b484c26a18244c1c40712031000c1d501658170f0000c0884811368444d04010759248100280c40f81120003011001d80583d444503410170070004240700f4031072035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 54788762 1250 54787512 54787519
    0x702190f050103020c0a050f0607020d080417030403020f070e1801090f0204051003050a21020303060a05121203040b0105040b0a030f03030c03061e0306060501030e03091306030206040f14 82
    0x15141111401403010540324042c1495800150b20f1001c00042c0210154a6007200072540b80b65001c0c0103041d59000200c1e044070050041c200d00e24680d0340300c3c1000900a03500304252030242e0041c001401d44940c0058000c40943c03040c00d5140034240d8041c4003480c0205104031044006181003401e45019180d040e100c0f03c4140d00d0b1000740c1c000035108180701c5401d150123490008980d940e46546170003040054001601901c15494840200140d050900803034055261a00003902c40d01e0505907075a01054544a0b803021100354180f166051030150b2030782a1100d071084404d0040b41060b5100c0590064a0a40d60b001108006103e2400d00f80149684824240c3d0200c1c001c1d4950348480c100800c00d11f10081c00c02d6180d0b04104000742c401d070040c00140c0980701446101501640c0014440f00c01480222050b5060040010307242d8003038071440044050050142d8034001b8200104141409070a00522a10b955454044050b88490002d0700107002c18124084145041c082051403844440c1c007580e11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 54790012 1250 54788762 54788809
    0x12040c060e1816210507030b0a050907080406150b0c12031e0408090909010e0606030609070b0c01140c040305010513080906090406081b01090f0806190b040603080702 73
    0x2c40c0c452440c099921114103070340d40c80c0b502c0c0c40c1142122410708001c0007a1194100c1403211080128a520a60054065403400c000c0f8407880c0013405a1030714580304499000c0100750001c1d0246020b820031582c0b20b80309060003d04100320340f026051441c040e811015500c4004115950008130405c902c0c184103c5490030035003140b61a480c440c3d00c12161010a41164040c0c101007010040300105842c0159001060040c83d40f901d031003418020001c541a500e854400c10011658500700800c103035014228000140120324104481c150036075122070307520b000941d640d181d40d1803140c48603500c05014030440d20110303580c0c510b181845402d66802905119101c0302d160b10310750010300d000c0201e03850b204058440c151120b0036640090300800745503001c0c20391270041e50b01540400d001c22502e4006058262103000c0e8041c1c0f15007084c08004254040c44400380d01072408541040e441003203481c910601c40b100810040001d00225003510043c1d40120382c01207000c2001e10031440d03d0200f1003803850300b040c0e5819 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 54791262 1250 54790012 54790039
    0x20d0b091008030301120501060305010c03051f062715020d08100803070f0201110106170706020c030604030c0512160c0501020d0c0201110c060313030f1412070512040c060e 76
    0x5843c0d100600c030700d414244c000c031911403c105003901300d10001c541180c02084113650914001e000351000700c40106c00382040000b403151496900c54544251035450746d5034010b00c5505c4640280080700e10300e41e0422440341810000e62400c034040441c443e144250b01030002000402405094240301600c940d10981a0410500240000109541c4417941200c000d5285801900040e41d00f0f43d47c0d121840c0b0a9400c00101040310040b0024111128058004581d5070564592003262140c9800010035403580220b404580441d200c2c003a80c04100d401101990842a0402020b0419a0000381c16402c4208002a45401d1240025000000344001e002030154072480c054001c108400140009040c4030303034400707008140350303041000c440c2400300038128503079a0900c0c0d481d481d94003800c400c0480c00208600d24000c070035803140c0306d01c521034102c070400b0798140030000000c40c617a824000c25050400005028151640440f4044540503900415942050504240d001016482c0e04801c0303d019400961050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 54792512 1250 54791262 54791279
    0xa08060616060f0c1e17071103030f01031101050a09050f061b0d0305010609082d0d0302071202010902010c0611070803130201030b013219020303010e0a0b0f040b13020d0b0910 77
    0x2170300781c0c1c5000081031656a40d8000c1921100b07a01058075506209c00700070042c0702801c0c1c000160503203005500c007815080c01d40c001110584518000e6000042c0308074010006405d00b9481d036038040c0c0c0020007090820010324054282a102c5400200f07880d441480300c8490b60780c05205460140c0120315114002c6410000103c0d550080001207203844001101c900d01b01030f004112092000c18880d040d00c0311040c107410300034060342211805442d44110003071011401401440703010500c6a044c0c5840005510307580b580070041003e00400100310904100c0074000421420040d03200c1c0e620b40840c0210003c00d80001000c45902003600c60500c034000b020042c008440b500d0f0b0200b45140f040500180c4203a241c61962035006414034412100c2c0c070703502403030003268011001d141621007046e2048490303692200381e441074640c80c040083e002001c8100225160034581c0095102d403002805110f44400ea507420b03041264071007106e02022a548240074a018a40888200d410030131858451440da810700010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 54793762 1250 54792512 54792527
    0x4140603071403090c041104170319200a0804091b050306040903020f0703030207060f03020f1602062205040e0f060a0b0a0b040e0703050702030a08060616060f0c1e 72
    0x1582c03415040440054800e030340400640c4444140a00103126040718a0300d04801e503000381c000d5103610010703804403080d80fa0000058665101409131030220840547e0000d0b201202e010701e030a02d44001007016590a070104206817406244a42c0704103903158035022041c0210368140c031070402e424500300c0804805a81c0402517a80103c01118001441a4649020307490405802c0786050346000e030440002c141600800e6000403146a912a05c00044180384114102c1c49001040314000d030040c01310016411901c003041602c20b1003d4030062810041075004140b451000c1c4103105005140c58007030105082901030b1b000000307060700007042d84000323070703d5010303115500202410340d0b03181d0b11590540b195503210180e90051501101d600c2c0e640c1e403255a16405100100c0b10b88001c80e042c0004141440d00c00011102401a65981c070106500c4040400403035500600000c00302d07955044880011404500c03d0103490480c0000002d030202d02008054041180700591401c00154a0f11190300c05070400b0b078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 54795012 1250 54793762 54793787
    0x90504050d0e040204030b041a06030d0519050d0f06031709060318011d0d0215010b07030305070201110a020703020f0108010b1815160b0c030903090409080903010c050414060307 78
    0x4010380d4103602d0101080090180b9400509000304410501081c002da10080105543c803003202048207540c0ca5040c10b85c5d841801115200080040060301d0074007580406154000015240052505c1c50300400102030f01e120a481d146403e95070f9000300100501402c6039100d00e021504100d04000d002d60008169002c01403503196000410b030b8001819000a51140c000a00841d54110070034150b000119541c100d00e600602c00f512401d40c0e0301d000402105040e50403201076a2a4918100a90344c045000d058043c204005641d21501c400c540141c201010741100031083c0d0040c9045491070040186030b9205d44000ca06001c1e08200521510000d401281c05c050030076200e040c0700c030701c03040c003c10181c5402c40508049610003255110a10311500d140a918034011742e00a68184c9408a0b0015a48000e80d4604c500ea40100703e58941d50400350040403c1e140a2039425042c03a0b200404242900d801c1c04c1c2031800210005400c0c030003407034203200d402c0719500241d44130360840c46d0000b0060410360b0b2800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 54796262 1250 54795012 54795017
    0x307150906030e1c090f14060306120c120a0b060409030906080702070e04150f0b0306060d02030a020301020c010c020d020109020306061e0a090b011103030f2a0301060503010f090504050d 82
    0x600781052100300084d11451070310403811001000d091100415440240c0100d4001e01d9000e00700198041e0214070358031321040010001c0b80b950301e654007007080003000301d048800a801500346400c065030752290210700701d1b50104061720002d4600c2c6084080d80300e0040845104529141540300407a502001c0c0005035040c0b820100d040b900c540d10141c2c03420312654801c0d1507070942c54041104000743c0080c907081c0710303050340307414400c140e0f0201c10b40c02503c1c441c074025609035200c0301c0000c2c103901c3c1402d0b182038114009801d82e040315000c4e03000300382642c1c0050306105a907911101c07002d00762030341001409030550080c270080214104590000b52500c401030240740c4a98200c1c8000102450383c601c410100100c02018902800d998660050250007240c9080b408a9100c402501e01100084116407084601405420196450b040f44190846401950329044460076884036496004500114013030000794840d5520381d8542946c500400a541e000040300742d040005000000714001040040e26502e030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 54797512 1250 54796262 54796271
    0x20c01020f120307050c0a1209080c130209060f030903030f1e010605030a020c030c0601031e0c03060203040503070c030501050f060a0b030f04080910030f0b0a03080d0e0307060c020606030715090603 87
    0x80c030304545d1402a00d940d154540150b200880800c2900310a0000712071960705c6006d956503071010080d403529841d56401390800f00d910514501c6c45202ea00138202004024100d5050038090780285180350411210a03005078800420f100d0050b020500b020f07884503107200c003c6d8200c0c0c0c01d0601125001c20602c00c66040c40004004501c240354607405590408401ca000c80b0303101c41001070202c2d0384001c00e11040d01e0402c40d4108450b000000301c200080c5c040d030030642400e4000d207141e68900c001c3d84001e005a40d0740c04207005490000d40c90740d201d98025401140007241c1d9060850a04111b540c000d05201d00c1514440400c010100010050320303030008001040c41c020356598100304900d80b182c01d00040e800482c0d0843d00d0072041d01035002d01381442d2000d8042101c00303000800d206401c0d10f0350002820702e007401c0c080d000c04241c0700e400101d1450550f0042d00d08150f1a60344035010b48080030040d80260300319008120315030404000903001407118a003490504c0048c101c02412990b02d502600c0c0426489 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 54798762 1250 54797512 54797521
    0xa02030d0f060e07020d0e0a08120c030702040912030c0e0108060f0d0209091005010f050f10110a080301060e0d0b01140105070819090f05090a0506120a0b07020c01020f1203 76
    0x180c2e0106008101c01c0040c2519840c01c5000207403030312078451542011400020240c0c00500340601e00313000b61950340c00101103055105642004a41000c04d808540e40700c204480c41c01a00ca41c0103024026110703120080c011900f260303005c2c05440408000c034042140c00c00280038660ba101089940201050740c4650001c149034002c203038a42c02094000c1c0d00064442d0500c9441600002c441c003000c01040004c1205988800c0c040c8444a240c0c803a0030341c0103a50f4548034040c0e04d040e50a5034002100350a0040c0001c484030304582c200701904005917840d5070080010824503401c0007640100010480e05c00c580409595520240d0103018040c08500d503184422400312a4050011030f2103003904a080c0356150f546081044052900c41a00200050803079440000c00c81d02c0081c024040d540b0090151501d5a202d8a0840041100609040e0b02c030810f4001283c4241c0180035292590703004201c1e01501d46040706c00686003050140000f81150b01c07a400081d110440454182841401d00242d280c0e01e031507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 54800012 1250 54798762 54798791
    0x90d090324050405030301050a0b040308030f0711190b06040b030601030b0601030902030106090b0f01110d1209060905280c030b060f10050309120c1f020d02121b0a02030d 75
    0x10000052501d20389880c1c2404140f201c00000307141225412944402d41d1602c0d803030152014043c40c40b000f0080041400400c401d14103200a040d8405528a0b00c4140300940d050542e1405a8001d9102c00e0919135102440a21107240d01c955031201c42039505203d0b14601102003980c40c4030502c0050b014403050004540036038802c0d0094204150018028804241c80d09032040041000840700380c403410206220502035400740c45d82a02a0080c0005084411107003141a02da175034050300341c469200e64031601140090614030544c00b003180030308002c01c00c0c00103400c60038111021701510950030301c0e0914980c00000700b00144140c152980045040196126034000c6280090550340d440c0d840440c2c55030310030300345038044050361003901184120703170581200e031605100601c152102030043e50000d018141c50011040a840c1c0c088210300c00041c540300114814200701d82042c000004034003060f200b4000c28038610406214044401c000c21460042c40e11400f82d601c0c410258480d05054032013010751070002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 54801262 1250 54800012 54800063
    0x30a0c02030106050a0807050406080c18060105040306050a0b01080c040b0a0309061d0307051b090106050a120606050c0c15030f13020a032306040c0506180409030207030b090d0903 79
    0x4001741640d10a00e844d81c0b40f40380c6030345080c01410700442c035150300010800700009098401940c05041d8051940e00c01290180300301009200c541071190030440000018018411b1070310442c4c6401c2d0018035100c02200044c081c50002c1d20000440d442400148030344042041200c110310801d040004505240d444d05002810501030001254031814030080d01201011005244ea54410401d44074451644480c18045200d00301d0541d40180c3d114006005690280c4028540041642080261072a01c5103800e001e44015810420000c0c2c1c010442104540c2d04200d4400c42c81402c990008841030b4050340142c09000c02040c200b200001440415580198040702c00645a0068a1094895245c0c101055180c0504401c44003606542290890f03404012800e030340110352049044900c603142004004e42500001c45140b45049145604030180e96a48124502d26100c1d401030606545035042008406a00805e91101a000709010b0500c6961184480058035441303440002042c0b040d4400c1007211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 54802512 1250 54801262 54801269
    0x40b1f0b0d05040302120f090103020309010902030115050a090207050303130215070f03090803090a0b090105040503010e0d08010b0a02060402130608030706050906010f30020a0f0306050a0e030a0c02030106 90
    0x5030000120342240319a550000d0b403207103001c1e400300c51038185500d072070500a11889090704400a414041074030303150b210303800440e08114601c00201304170f49260002800c507121814a0101c9000c103c800f04070b44e04058100200030300f4138080450500d0810b40701c003501e0780300c0107060703445002164200c0421540d403501d04041410101030b0850311503400703144c55846102d9040e01900800c00b500e40c0001d490100008030703015010050016840d051401854800c150400d902c054184482400085203a072070074850740c0a040c1e04ac4c402004e046440c0c810160010806820210b8092010070401c00605c1e00051065005a81035500e030b02e5880340900c0400090009800006060100288100c1408015003055020b403011000307588190360780e140385c0070555a107486218585000c1a050041c94101c1c0d40c403621400302c00d09804900c0d020282c1c000b0f500028541c000c8003102890745020310030710070b40340f040340c1c2d01c040c001004201240840d51103a0341c070301a4400706010820004138030b0341103403420740022004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 54803762 1250 54802512 54802529
    0xf03170106050301060e0f030a170904022a010b0d17041802030402010210061202060309010f09030c050c040603080712030f051503010e0d0507080304030215070521040b1f 75
    0x200e5854000042490788284924000999004d070041001d2802e601d8604210038010300824014000707580340c0741c0c01500740c0b00030443c900080c025040a511a4001416100c00c101100ea180404501122907120050140445640e00d13002c190060f5440b1859840707020303900000346203c848810740e052880b03440b4030740040c00e9604100c807000f064910720340c0145009501c00d0f0240d43c000e149000300c0300c0445d1424851107924500382c10804001d03007400c200031500f0110780380c00454400d9072500340c01700f50f41c0d440800724009541121300c5400e10409015480a5420844040c440146103071542c0d034890081c114080e0000400e01d9148845500039485240c038162889400e00041c83c010204000f030b007105c03d40ca00e01075401d200300240800030204070029803007003a03100c2a09109068803800e000c5d4100900450551060642403003d2501d0010800e00c1107000340d44842e9500003004801042054503280c00700001030040600c00018104241503030300054035170342020380041d442c0c1000c050f215182c0c05100c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 54805012 1250 54803762 54803807
    0x110403030908100c020712030207122d030918020705010606080a0c02280206040e0a090c0e0906061e150d0510060c060c0302091810050409030504030f03 67
    0x40503008925101140e0311002940e190740c3e45001000103580b031481d03d42c00140c000704011b0050005003184507100601900c1141ea182c3c0c0c54000f010b8003494070701c506031902d20005100d00f00f000e19180107600544a00b01c2e00034000800396901920810701c90040040302c0034104440301d41c801059041d250a590098003c4c0030300d6a55110140c0201c03410f8600069150820000c025001c0c000540d086144890403004000c803668050b8074052075030180f000701d9102c5000c1200290210124412500a40700d03048005000f0540e1714001c6182e140070340c0154980003421040012a040108846502031000d40d9203061040700458648240208010895030000000841e0b14019200f00003a240b52040c5140410507601c802802c1051511241708200015414615078800100c0c181c0005207440c0c0c0d5400d000d8103080101340010000c000c3c0078446004204240100711034041c41c070107500700404040d01c040080704010b407070060461160b40000350044405c0c0844008041c854040810724586a008480c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 54806262 1250 54805012 54805019
    0x30906090308070f0905010206010e060a030b01060e031c1211090406060e040b010806030a0f06020d0501140a2117040306110409060503151504060b0c0a051203040b0f0a1104 76
    0xb01501000d50b20140090301c4140500c4c035243c0a402d81206072803058009000c1d0361b1030848035001d40f5030020302c000e810411980000001907905204a4064505520b89884502c00b14007418541040c0015841494642d201c12200c641c1e00701000f82c64404080e403020408503032031a080202132040c42e0020360000c2c42c19a00040d541da1218495020140031a400d00044080000442d0b00300402d5a2a60b407603000800e2800c0061180968a80b41600c2001e0244c1820844988481190802d80c001d4902d04ad004d000807415140060311540031b00550482418005091b01e1642440c18080c04020084488104a0b45422201409036402560701181c284a452003148660a50b50028400d0540003424614082800e14003c1401030f070080c4035020041c001e544071031340075918600403181540c02c01c0d03a840e03010814016000003040c8001c80c800c003d224207180d61400e0351409a183d0b54280d0200800d105000001d00d116903039942105036024083c10f940c95800c0034100a201d018a208204480000c001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 54807512 1250 54806262 54806267
    0x11040906030b060a0605092e0804060f0e060105010e0402040e04110319020105120a150e1e0c070605040203100e010f0518060106081003060906050a0e030a021207030309060903 77
    0x10141d912400000b903950f11084140b04001e03005000d81c0002c200c051000c0d002c9801c0c071071489200c0c0b40141d40242c180920603181c1000d00310f052041e407000240407008000c240000340c000e0702ca62020310710b010031160441e100c40580307a41060007014104252915041119644c0e50140d402800c031003000b211040c146850303c074201e4000c00200700e009025440c14032011480d0f000328600455010f8550394501140e26100f002c0c0490014504069565103240c01c501c04085201444058801d101c11070005003080c031040440726854102200f50004035408000b407200818080e9aa0642e1265001c1096111440003d0a0400300706100741183e24201c2100c9588105420090040220040821041c3c039909010f0b442d000c0ba240104040e580300e00c00411001e4801c00303400d0703440031b200c0d603100150b9a203d503540e0041d90880041660130036101c01c20721a198210344030750500b2640841c02945010311201c00a5200c107003801c015100d034400070880405040c0290821404a41c1c094400c210358141c52802 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 54808762 1250 54807512 54807521
    0x2108040b07020708031204031815030207021c0609020a09060501120c020309030a03020d080c070f0f020a080a0606050301050606040f030314130e04030906090513020c010b030706020f0606030303040c140301110409 93
    0x15400270340c50440030000d04008425600c243d0303842075461292850302c0c000544c0a940411412608490b0115022080c0ca40c41c04150400600c581c0001c40e05c00440d00420407041c0d05a00010400c1d07281c11030402140c2c0c0c10151100b61070090046c0413400c031503203903000c1e415405001241034140c022810302e00101030340421f107000c0c8482c00391280d990603199002011901e001d0684010700d240c280001c0b20001c14100703c00e01000360710003441240c4050701d4090040c00c006c0e094004031017654684078140b029140a0240c59880802900c040e4145841c01c080003084040c1844040c0c240403510f4200810141c00808880c03044400d1400b500e070040c1d881102c0079902101f2981600041c081c6000401c40c01d2062452000312407004108142145c020400036000750300078590b00342150f580f13240448940d1028051034004000a0300034081803140d07080d5050a20741c0043c20f0ba40301e0b400c10420480041d038503000d92410b907070380101d02c2102d000b44200420700402014606043e10540450001100b8800341c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 54810012 1250 54808762 54808771
    0x30302100e03040f050f0d06020a051305030c0108040b040f1e03120b03210d050f0106020709020c03070f02011b081c09021c0c03060510032108040b070207080312 71
    0x40811524405061076030316405113009010f8075005084041010b803800035001c06141000802840081b4140e6561604a0b8030400425001c90400b282803080d1a07a20f4080f080201410b40c00340031074504a100003400713075100820081004500c030011170304ec003140c2c2c48800061039100c03003408112030078030209042201c1624000c40005421b200804070851040c003842480400c06001001c401d0540050078180b400c0c801703507040e0380d00414040383c05120a24020180201c41d000e000c0041c0354108000241450515000140014010400311001ca04004100c484c020f810041c14041c2028178401200e148411b000d0303c0f41d407400c5c1c0d004001c042c0040b41000b0885181101c3c4000102e003400c000e00070a030fa0b9042030103076001c8058940150ba0200c844419016540302d003081c0d41409031650380b49001c668041c0c0382501d541801200030700c20403042ca181030f9059164441e40c2a5407a58003800103040c1c04000300700070b00402c0d0b00000b1030080760007088040e022f00703600f90a0300c0e10341d55001c02800c80c0d0317402102c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 54811262 1250 54810012 54810043
    0x7050d050a090c180b060403060213050306010315020f04050d032a03090306050901090c0e0a0c050903030307120f06030b040c05120d0809070504050705030f0f01060203070327030302 80
    0x45800703118244641c0c180c150344404290402450544015440c15500c280c81c02d03029120100c00480e070341d44000400c06107218910050f00d94190201c800303c0c0380c9817038204034040c0d80010014008620048024811407030280300159440c0140001882d8034052544643c0d00045608480b20800da005551071910183c00c00c000d1040c84072140d10806a551940c80c0500420b6075003c1c148045661a04895030100d9404000304503042c5a17900c01c00144130f144d1090115a0441c8203004a030034480c011800b101c0124907209051001e06000603403248000380200082c0240c8114450484580343c22440c003c1c6580081003240a0b40c9040640202904407811600c1d030300141c0c004603c40ca4107001d10002d034100a0000e040c0e1740d02190098a81a4020301820024424400d00003060755850103454812103c030340d2843d03100d00300149090300b050b4000e05203002040d940740050041682c0041076655441e0540f419a813002c1800701071a800998401d0300c283c01181c07891011051640000e0400c2e0700030f8801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 54812512 1250 54811262 54811271
    0x60d18051006060f0e0d050f0319180605090414190b03030f03071b200f01031a13110409020703110105090a0201050a180e09011d0c010c0807080307050d 67
    0x260070a0048a800b40659000702d0804014401c40502c1004802c40180020307101004403070fa00d4807990700d801d18402c40010264000141c6a20302c42800c0b102c074041e0900303420300301d0081044001096a052050191000304440441c50211541d02e9402075410005403945502c0caa0510b0000030040d01c000c420000601800c0c00d07001c80060030300004944424042000359815519504c004548010440b0b036031801075002c00b403604000c07408a400d0701002c0c1c603078140380440d0740300b403201849080b550701c601e07141c10306151102a080c040c4820354556050501259400080a095074408008140000030004c805c0300204021407400c2840e030041c00340038000c0c0ca0b80f04080740702440032426150212510803003a0414000c43c4019405480601084036203400c1070356044080320389241d5030f044140d216403800b10101c020b0002c6c1250070b03c03410030b020418020148001d00c5201c411551400340d10700b03190400c112040c0c0c1d0414040000203031801d4552000d8052b6881c1000c200083c9a500400f07050041240351 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 54813762 1250 54812512 54812533
    0x20c031b03041409010302090c0f041e0510020303060102060f070c1401090203070e01080712020103020c01090c03030f0201020f0f030a0b030a0507030312050402010e0405060105211015050f09060d1805 88
    0x504a5241247e6000344000702507503500c0d4000040e5006150001480c81040c840484c07c6100300301d0803600315040d12540e0007414070f043c2c2003203010642c01c03005c242550010000d214007642d0228136194025840388891409440390074080302c1e03034a0070a030040c01524114110000200041d00107440c1240201c0c00c9980a03501d411040c440c0040a100c0d0224a9012040c1000202400e1030b00440d020f005047c01820003100b01c0649003503601d0385c81c040714041c050103414010142c02468440300503070b681c802141402004441415244600c040c6540030801c080005100d0541d181c0144000320009000e442d51510249010783c0c0c1d4101d42d02044022440d034100700482c440143c4a45480385405945002c0b12844107801e00008050281000c0c0c10420100b11040006241c481400344216900016030028544000a81c0c08600350340c000505d4403021072105404241e1142c2540c050904054038a95540343e0b04000600911901040e0120b442c14030400c030700398074111040b06490500400980c0c00c480b48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 54815012 1250 54813762 54813769
    0x40306060f05010207032904050a031403070c030806120109080d0c180b090d020a06020304030204141611010f1803030b0409020108010b0903011508030c15130204020c031b030414 78
    0x1d2401000e0040e400030004002281e88030891114039540700ca4135801604031806541c5039031030111016a0664407502114003010362140010700c15803030010300e00b411800c2813100244040401390015040000d8900450240d070f940310300390300040640c0d10080000b0071030340c41c12001c00e4103d104a50700541ca84131540d41c03c1ca004000544010741c0070904021410b0030440d460303209810203292160004102a24000144c849081c0704c0d01400c150380045444030b18600c104415603e10210726480c21a05d141442040e0300d06401c06030200350306d420400f019042c0850401d00501189100e040120300b0240b02c1503103ca0003011042d0158002e075030510802100741e050205441b4000d4000740010300c16070040104140c00b0001e08010f0398010008070304040c00c0c0c0d040c41e40c0d29041d900132a40c240c2002070031546100040024004803044207240c0c038000c0c507041c110000e2041c0d807021b01901035600003c00682502d0140100d58000e44905000004100c80b0201e5a58a030890702030700c0c03060172803240e10210078074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 54816262 1250 54815012 54815039
    0xc1903020a060518030d11100b060901030506010507050102030406060513020310090c210605010806090c0403080d0219020d0207082b02071802120a0501032a15030204030606 76
    0x98000e04160745842c6030000803206070748036541078240c42a1502d524001030380c06005d9120298211303520880c2c118600c0c1511410480c0e40101184100d190016080040c1c5854042c4c035491030b82400d0000e02650b55100689903480b40210090507075100000700300c104650750348004103844050701c0200d04621525141400ca10064031003084801e10003008000c00300301c81d0054032030901c2c145800383c280b014000320310b20392002c0c08a224a125403615002d02440d6840824103a001c001140e0054ac80d08048000740d03564482c600016216a50000d102e01462400da0100c41c10b036111069031b06c125403642000251201010042000180150b010002d0800c0e4009801d4034040f281d414520710340c284c00ba400d40644410b001003841580a050400145040c1c0d982a4405a4113001c1c0c4c0966280c0400c2104403a4500c000d200c291210300d464014404100c040b207458581000001c2001c1c400160211541d1003441107034400503107400b206040c0c001241d07041e00030b401182e1046806000c120b0f1648034030070890 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 54817512 1250 54816262 54816269
    0x7152306090a05060a0504060303081b090105070f0809090403051c0b030c09060a08010507020303071103030f060d060b0307080a050c0a05030316060b0d080714060126070504020c0c19 80
    0x125041c4045000e182c42036002980148004201960b016612008507003510110f03441079000c107142c0340c20004295510b1061100200300000242c1c0380c10360050000e80303103005819001d4110842c0041c0c2c68200b1009208944007010010b007074003814902403070001d2481d400640e52140380449031040c0e009900e010b018860301440018054101031481d50f080c044a031200410a03680301c44002c2e8005084142803142d03038081c0109502840d92417900180242941741d010f00c010500e81d00c1002002140600c520340550000400c69010084d00301604104010b422030040caa545409040340003c3c20400010304c0903015403145050381d03002c0044604100500c41e0510030703035030540c000704444e10b819140c071070058520900c070321000520306d00314801140709200701800c1203540b5100012044184140961041c0c00000904010a0720390f0500d1800c4812001c4004844200402c030151281d001c2b4041c402c000181c200036008645541c03210070200e50710040d0b1120b0300d000e80d800705000d0b03034404040d4080c14142d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 54818762 1250 54817512 54817519
    0x18030f0903050304120615061e08010305060105010518030111030601030608150103020d030c0f030e1516060b0a1a0910050a0c020904170705070801110405011202090607152306 77
    0x2800d14048840320174084502c1d04a40d56590f5101064203901d1910202d40a0520341e990019500100488440c4191a22020a0501c20080c00400003c1c00001e1550706442080c603003544c0f654210319908403045500901e20340d05501b09081603501480440c00765209070320981c1d06000341e5a4402001c0d0f00c45003850300c10410712a1500045c8050700f4002c0140c00c041d480303468010410302094a600c005910481d20450000c0c1e00200c0051031464040c0388045c0c241410100c2a2a013507150b8003201019640050041c1059110800c030482559002e030668001c043c83e074a45540c520140f448a0040e500c4101e14a100b064450600c1d41d00900c150182c0350825010b840e0144000c80503000c2014a8100610450f4140c1c0544180003082d80b015014101e160710440c0141103480c104100682900c00b1424035a490311404d100030449681e11040e404481c104c21080140c4d2006003002189281c421004058190c0307820b0004d10ba0f56040c5540010500c95003006425154501003041e0310040c0707015103090743e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 54820012 1250 54818762 54818767
    0x9020c062202030316120306062012131703091305060310020d02030402130b0303090d06060b041203110303010b040e062101060504050f07020d050f0d18030f09030503 73
    0x400ca20121540d007036040012140c1d0781c180c61a600081c655400654084650340d01c00d15500c080141c0c106081a8250081c04e05000319410003100a240c0303022002d4610f12013440c070900d12480c02c0c00340404c5441261000d419603407500b001c1c103000c461031041d103d80010081b03000c412250b8444d01001380c0d8401c150081040307006001d00300140c1c015001c05000c079649070090440c2e402d07094a251000308590402c1c44005a2249410b00400180031254011032420302d09151205000755004812541c090404885044041d00d0a050100c002d00094008242045c00040c003c80c1c008081d44140803218032a03030b2110315030032042a40c180c03030340000c0c0f0803000180c1082c001803200030380800d5416030124005d002c520300603a500749c0b8503c000b0483c40c0d040c0c02c030380d42d1001c0070300c028145409102d91109810a0003a050b041800d0001c1d5104401409c02003001008140c3ca001c00d101401219044404020240070010140c07420103001001c000c4118041078403402d07481c0310203000c1c0e200b5000f02c0e80c00801860 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 54821262 1250 54820012 54820021
    0x6030a050304061101021201090c171006050d060e0403080115030b0105090f12060411032413020d0510022502010c080a09030f1b0e04121404030221010609020c06 71
    0x44203483c0c101480004ca540901031174100c00c1c240b268580c000e2002d180c0219696001a0019090041d00380221814650440070412003210030304121045400514141350740f000c00c820300400909451704241809901c01003807005141c0d1004105060307800ea444e03501e1000d00c0c2d8800c2601150911070800740401c03003c0c00080154034119000806111014054825080c0c0008415041450483e01101c25800468108205003010002c0b80d00a80b904008011104440303440c0030700d1444000c0210165003034460740c1074119140d414441c0416a88042121040c8c902690030f900a500042584406100211402c1c00103101c0400003010054040c2c40708408036850f0307150b14591358800515002402002c2e000000054804001c1e4140c96005010182c0e00380c07054408000b8500c0203500100c6103402135820f00001c152a82c2c10181c4006c0310342002e50b03040c0300b00f0410f20114003466101a41c016614490b440304e8601c000010010400003000800c901921a220780301280a40c0301c040342c543e0310070400503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 54822512 1250 54821262 54821267
    0x60a0b060c060402010c060609020d0c11031602061b0a05010906051501080402010309050102160c030203070e0106050f070507090c080f070207060207090e07091506021501120f021504170606030a05030406 89
    0x70603024202c00b00e039442e00c900e07278441a81e000e80e04a80c80c246d551b40380da01e94240d001c1c0b99180398188140c05107180014800855aa03c1d00d1100e01920035540001ea4000c1d407404c59044420701500b0b5015561980e40504015000300b120303040540d8134034203020014408071000c0140e1124103a05231940702d516106d940046000b080030510407600e80d9420001d200180f02c9a40703154152a1003043c214210500318818141807a10f1035015203022141800107205203901f10082c0c62240c01c2140c0ba01da10303030f0303400c1c20114a403100302e078440b01e420b516201c1d01606c0e840d48510f40521641440e0708000c6191074005089139600da00d1700c14400140c0100c582441002000e0700405404070004c411180350903103400740d2034110303080044400000c4560240410030990103002c1540034602d84004400903615044ca041d041c0700020100501941c2d207810440219620100c0a0480f0005406000c0e01c950702c50069034021408440030b980141700c6e52000440c0d51500080c4000e2440d80803002e50305080ca041c206 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 54823762 1250 54822512 54822527
    0xf03040c08060903040302030111040e070c081c05040218190207020a0510090609090e030a080702011409010204050315130303110415021506120a0312060e0108060a0b060c06040201 79
    0x89400e1006028002414141001041c1c0502140c1010310f540740d1441c4101400c5810301e1002102110040c4004c0101000c503103203040e400600350820065440441c42c0810300d501c141c030350b09082142c1ca10000d6030f1004003544845d200c2c510030784194103c0c420060b4600f103600c8045461641c150036640c41c0000135659500a0054503101500c07080049444500090381c410480e00c004002411804003080102e038400d110000414212100300060042c1030000b54403445250012414011345e803000c100300501c00d5102070f0504080084102c0c8500f41039050602030b49c090311825100313206014032491900c09a01070180920031042c00254001000e95094014045025501c1ea112005000004141d4120030700e21803900ac240e4040c01149480d00b404100046018001d40d0140400407225001c08900299880103242c041c10b0140342c481102c4002000350025410040e001c80002000194004001595501030001c0d01fa003440780006d00820321007d409480580116507004001041c059401130a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 54825012 1250 54823762 54823771
    0x11060109110f04090207051903020d1812051b010201061d040501141f06050f0304150e10140a05090303150d020a1d0603012315041113050901030201050f03 68
    0x68904002c076059031060142c2155100c0009107400050300810000c013444580e55044101140d440e039100d05450003541c44200000b0101480050b020903061488840c0c1e40360024400c1f4612819010400d00d80310b519072046170594070881d00c487c01c80500960040c0210419036094424001d10140300d0f1380050014507000d44152095544c0703050300b01c1e07402104d201040c46035000003143c0c40100345280d0026444100d075480502001800c4c08003810200700704040f6500150070410341f000c100e0103004520001e15107800d0301006403151517884134440c151a000b6040e04514142d920b003079543c0e21442c4100b80c81c01114100140d81040000078003403120009400c030900d60150002022480f05d80c0410346c2c20f00c0030703003110281420306280780d4983c0c007050100d240c3c0080c2c2600203205480c1d80c0031060903101d40e030b0400c0d104c90141d8200020b4458000701c0da0410010b100030000d02802c0e260382240c3d500e9901840f4680d0701d14001500100d41030405100f114100c0398103a503914034250711104104c0e4a03800180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 54826262 1250 54825012 54825041
    0x6020705010c0807020d0f0c08060105060f070204020903340801020405150a02010f112502100f11010f14090102041805060d0c0b031801061406130806010e1611060109 73
    0x403042c1c00407921031f0998120151040500300c0081c0d0038003501c03501c0c2100585c001841400204500c00c000080202502c00b5103034161005a181c21014001a007441012010700c031044032b80540c01260b2510a4800b05180303201d960300100050344642c0307407500b83d20542c001c00d074000b40000400c0c481e20380340400a15180c0400e02c00041e03210304243c0c102c000e42e100414403545a08000c1902d004002c9480c111030590700107018060020101c41d0b0101c0e0079000005042300030302040080304402c2e24003e0031490240e0100d03034000c1014010001e620001042400007982c161180d0a0000b074240b00d0510880c3e0941c0c805003c04580c00d034003980800040c0c68000c00729a04211043e00d08000207103041b4014014010b4050141d84a2410300308448115044a65001e0140c2c1070100030001c2c680c0502952610301c800b640c1c083c1d5503504401c0035643c1c890081c3d1081c00140b0440c400003a0840399601020702a1041c00300e08020f1500003102100c400d9a42c180d2580c075500400010080d1144a50104c5002690207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 54827512 1250 54826262 54826279
    0x605090c090d0c0e0106020304170105060f040e0120040806090a050307080306040605060c0c09060a030c03020609031c03050108060a0c0f031a0303130f05060c100e010914030d0606020705010c080702 87
    0x2070004e400307198400c0e03200c0000760703002113000d200300960f0381e0038100c91044100c006c02c036a00e400c50004071036802950b0750600803a500c204c00c08050100f034001500d4861020040c1382034202c042d44036511383e4054030030303003046000d0300000c102c4c42ca10201d0740400d401d800a004605151081c1c40c0c0700304981c80946040d1344182da40a000034203448800c0502035441803080a020282080400c1c484560802402e1510030280b001080c030001d14400c0d81c0100380c6c1d8040c2d030700c1c0e9210748024000ca8070f441e01d1440000940c412440a40e031415070305402075411303620030505840403a15003d40c42d03800c0d0f4003001c8000002c03071034600d00740700ca0510a502202d020010380543c072030320a00d030b00d01081c20f43e4003e001d86460b545003100248000c004440c4120010041604c10300d181262180a460311003800038500751400e61101403005100c40300b500514000ba4000018615611800365465521380c40910201c01d07050800000013825400400c080c0d04480068550801402c025504c1d28981d81c055070003240c0c050b550 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 54828762 1250 54827512 54827519
    0xc16092f031003020a08010c1101021c050408160803041103030f090f15030c0c0f0a03050a0c06090b100801050601080708070c032c130603030509121905010c030605090c090d0c 77
    0x3d140c03517074000344a008000625010310010042c00c50300758203d0f82100d61b00402128800a851403003140314409601c100050740c0e21030307103088503991151040a007490014070700041c0c1880b82c140011801075100300f4440001c148038005160f100d0161030780c0b01d6403001017480406105d040060f08091800750040581c40440580d005501c1c0c250025070350110317041c901140400f040e880400907100202202d0004100e045071998005000f0700c80d1021401c00c10604200c0b84041011503000641d9080c1d0010021080d8a001c4a00c051540c100c2e114003807141d82005d02040e0380354055100580246840c1c2d4400e8455503c01c2420b554807082e00400710304203c26401c1d14694020598241ca10b070220080056495400010400803003c0c0c400005905044c0b030403d0400c0001c2c0c00400712010440d0175101c11403e0643c070074001c6d0802d10559914070f032006100060200b00070040d0300c0313514864182d4400300f180c1d0340c8030300c140070006404070b81e040aa00d000700311219007842d24804098a0b03910680101511548 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 54830012 1250 54828762 54828769
    0x6030c0c0105091c0512011e030507090507080121060c050c100501050306090706090e0705090301020309010c0305010828080c120306010306150c0201030c050c16092f03100302 77
    0x20450340c00702103070000082403045401406400021400c0b03485c0980c1040c0c0111880c0041c44c034184100945465a00d550040b81c0c03203520540401180c10000362044d06998443c5000546030441d910030000d40400c0012929448580c2e8040081070301d1400442c0d500126680c42004124080000e01404014030074510f060300100a038580b15072400c2004506540b514081c149081c6009c0c125100319080510305104180d40503950308101c0d1225034003100701d5200c901041d00d052003480b90168242d400007040100c1060150410070400301107580400450381da0340c5a242d01c0d81c0121480c5020100c0a5505801d11100408658a41c07402107050518003038100f00e02c130340307442000d903030181d2803040200c10040c10b503806115400041c01c019101e080c1160701184000c00d843c3c0300400081c1403640d15401c18400768881e000342c0b1501c1030500b046070281210030b01403a45207030040c821500c0300d40c100101c001c0300842282c0f020841d0b007078070000200f40c014008081d0440e50030040030703181c002e4400c0c4000405070f42c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 54831262 1250 54830012 54830021
    0x4050c0a03080d0c020609190c05040c020309030c0102120d1a030f06070201050a0203040b0f0901140a0f0e190f05010902040216050c0a0602060a0911040f240506040506030c0c01 78
    0x10b101c0c0c21100d41e10440d901c00f5105642c0018025000c1d5004079041011307801020134000c00d680c0c1c040e1071102d00348009203440c0d980707a6407075042144c00c50703d0b00c00000d4245c2c1e0000300a0020b100220704942800c00c0e80001241d45942e2070403100c2100b40e043c0305800000302c0c150400e01c1c1d1250889120486c01e0b8018011034a40302c082d14180040d544001d051020840c1c0a128030b0f50400c8110209620f540361545400002c004081c0c1507140702549400068803801003940003100504500e28924010f0a00000c1c12000c0c3c00c2d07a480c1c07181103a00d00504040d10315400200c806810a03000a081011a5580c55030300e85011a0354050f203855407110103400c0140d03140d100422080f000130010140885c04e90502c07a10385010400c00c14054001c03110309000e11a0001401580051030950104161845241006100840d110600e802504148106030004020707005060f0381d020101c00281c01a01c02e40f4142540f205500c0792a8002100b044180b00c5400d0802c010b6902c00000c1c41c4d41490119500320090844 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 54832512 1250 54831262 54831269
    0x10c02030304032a0b090307121d12060105150403060207060903030f02070f11040e0a080901082404180b0403030f050c040b09040e070302060f040602061b0702010804050c0a 76
    0x68000000300000c01da005022001d07210b861080f40600307009403010710f8251542681010b0b2085c050302c000030310a200100103d52460342d0040c5201c001600b1700c04040d00d9185107000028400d0300d408020301ca10f0034a01e200460055025008040c164604022300041000d07034401d100c0f840740104070100101e82d0b20300040c184130b4440c0c2c400042590240c02d0040403108415080120603004003c0075010a5140c00741e0303000c40740c02c086807407c2c64080b20300150080503420720b9084180900013281040c010180b01038140700900307807581503c0b5070381d400c4107282410426141d440068040047c880007410681d0050003208801a03c00b0f40c0713203100b501c5000030b0141c212800c074002603c50070701100b441030a0003000c0d0070507429140c21f402c01d424a200701c5c4550007131030203140c00f5a90b503d00035030217900c0c1041039500458001c0e1065a94080d590020300940e40140103074000341c0f03d608003144040490502c0240e01e078480c0c10a0b141071000aa004444842d030140050314a4410140154029521641c545004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 54833762 1250 54832512 54832517
    0x50a050c030c01111b01030b0a030c03050c01020601060207060e15221505090114090a030b040b0f10050d0c0509070903020102011415060a1106180606030c0109090b01020a05010c 78
    0x100c1a4a0081600c1e0608020503903040020b40301005034040000900c0452030418070416101c04603001d00101c00402032440015841108030030000244180e11641c0b009980c0100180c1d0003040b001e1006903640c0c01c0078880c3d440181c0c45001c00b0002284500c18003100f2400c024401c6014001c41c200303e80e01d03500403110030070142903900c6500c04030218903184030004100111100403144107a0030041c025004810205060011440458060854030700844802010041c0002021a00c80c2052004058215800c83e200140c0f0307000302d0341c02119900d140b480b030031000d640c000640e07041c00b09124810a890208640c1e1528450012400b1351728217085902c2003540f41e075000c3c0c039075186000081c2914040300a0343d0342920f18505000d8074200e0398846600e09842500c40541c1c90540c280c0c100c0f40361104c645103440c41d0061400340300301e443c12051103070300c80300000e000c4481d19110941016119601c560050f0301044003004100083c14464001a6098005006451015007031342c440609550744017054400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 54835012 1250 54833762 54833773
    0x1020904020711090f011a090102010605090103060504032303040f030c0b040506090d140a0c08040801020315040b060a0225050904050d080f0106020c013c020f0307020d06090807050a05 81
    0x844e04207220382c185c0c80ba8541e0390070295545400342540c0780103060013603001c40380400070700c2007290f9000f5008140180300240280ca160340e540d04101001700010703582100041c0c040d61040c225084d003401014072200d842e0701698039540f078070f5a039a18003a921860850a00c1000306844010502c10408144114002c00142070285007030800301d8140340c8150a8002444000d400c81018003001e07900340d03089107901d41001c4840c000c01d4103041400c1e02440d440007020f50b00000410014024044018143c90015601404044c0501d4100080d0707009565040d00160700c45e100c840c1c6410240c60b080c449001e0011030020b031154030350380451204041160240c58030340c05071001d1134805500c143c1c5503500c00400d1000000d25414150300075112003070000020304011a81c400103c01d00c41d0310391446a5607090313801000c1007642c1c0484058034404c00010180c09030040c1140480c8104000c07089075072290b07008100950010083d541c00000385100e18013650b41e60814005500042e000f00407206105000d14002c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 54836262 1250 54835012 54835043
    0x140c01080604021e070501110a030209030c0a03080a0806120d02011b0e0307121e14010f020f0f030903070b1008160b070b07120c030f06050a0e040305030702010209040207 75
    0x500c4048040d014a019600c1000003400010940e920702600104c103d000603900c3d081c0303040080c050310132500c140810740390009025644680590041151041c164161480d212040003044060f02e070600c4040d110000401c8405410b500c1030b0350250340803a000f010300a0b1900c43c840384a04d08199101c0890140c0e6442018070300b801400c1588650038000c130325021524511040110303460300450300c501d516020090503603004100840318059800d0100c1603030401d5070502414442c44541012840c00819440c010701503607025803034006c8401c03580288030b40c0d0b440c00101d0050142623600041500b0801e000a2080380c00161480e01c000d4018000ac00d000c031201d03401c0aa006003490003100d44907042409983c820080b065966083c2c4012a0300040c2c1084a41d403445015200300c12000b001c003c965150482c1d0140094040d8041c1011007046842000360341e84070f806001402003103019801408000c01d000a00181c441c03802540e00040c0391001608215909010400341e03000404201c4014a03105e46c0034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 54837512 1250 54836262 54836267
    0x30109021e04030201090e090309090f071211030105060901030e03070c03050d05030f07030b0d0c170d02030304052e0f0603120c110108090c0306010902030f0606070b060103090f140c01 81
    0x200302000000410b481c280c6594000307411440d075032045400b90240b00c00042c030300d100180140d960344040035141c1c40040c0303040c4076100f2030304c081140c480000c12040028021004524811040d0365041003c03103a1545e4209000c0054980001598038109512000c004551180500281040912410340c882d40c0504500c6d00505094040340180f00b048010b100300260000c40891464001155003000134001880c070001c115841001c13174003e00304160030580040d5810103003000500015044040c1c4d1545084003908030707128441540c1c003a005600c00701418a064813490104115907000b00c2250060450320865401a64404841040d038075a9940c010001e001c1040075080c4410701b035141c1003407001140c2d59014900d40240400a04010400c030005070071300c000f04141215254000c04481c0c0643c0e4540300700000c1d510403200902070107151808641c080c00c14505403540d403640312002c0c1e05960f6607000110010541d5034000c0e0b0303500c28606500030204440c0ca101c1000702e0380040282071080c0340d40700003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 54838762 1250 54837512 54837547
    0xc0708010603120c0f060b0d0203150709120b0103140c030d0e031c0507121b0803010f0b070210030c0306030602040e0f0c031b0f0705160e0603162105010203010902 72
    0x1c92040c0828013060708006030420605602040d84102d00042000c11400419600c4190b50002505403246003c0391541c076442c107180324400d41a964440500a40b5035100d041c03c220802c100410924031a801403000540703c0302c590700004419400c48110014400009151400d01481d46021502c25031203003211341001d0044400c2c001c1d041a03040b8a60566000040c5144182100a020301212603038081d401440360044050052049240c10748440342e500700303140c003580b00b8840c1000c060104000001e1104200081c2d50500360024403102858404200c1174000c1e1458411580800d03580b11000310014207c0d10107000946150314130007000e482c2000c10b1a1600030003030401d141041c0107100300314814180d40c00001c0e0521a030301b41e064031180a20a03ca21070b00a40350001d00c83d004142141c5504211950844100c0c9d964680d40d40c1e1986945042c5500c0320800b914450a407a180041408103040036920240c408410492903040311115403101803c980003a004001c000d900012a0707020340092104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 54840012 1250 54838762 54838793
    0xc04080115050d12110102040f0e090c0114130f0609030501050708041110020a021c12030506030a02010309081201030803070306091103061516060518010c021b03030c0708010603 78
    0x80d4000860500d070008507004103c010041621680c081ca0200041c0b044045c8141070000708025500c45407100010081c0030114090010600481130003d0000240000d00003025801a100c8130800344000d21006150b0340088800e0001c50751041c0006185010560441d000309800d540ea003204606524080d82500c00c080d1a078000c001880c014440402c2d60354511410a10085840070007501c4c142100b0303400c0002c5824040e500900290100703600342c1d114003100c0a01441425004a062003c81051302100c3c010307220250954082500000154001d610a42c0c0b0340e4007401d000741c1004000f00549003005026013044032822004410310014917018010b02c2c2c007401900038188011422048000d2250000070300780e91060080c4101041d108000702d08030f481e924070070f0090b111180ca0078140803014003c02c0d10113085050158000c4020024103110349075544d00107601801007070703403886494038404a4920205a05000410082e0020203040000c80000c03d04000081510f9165007401300758090b9070300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 54841262 1250 54840012 54840041
    0x706020a1704020a05061308030c010c02010608240402040204090c0c0201020f030705121e040324110313030302090a03060902030708030f030f190207110a05060a020a14150c040801 79
    0x1e0074040103a43d06203242e8140c03401583d62548400c5441100003004055900c0310400f4000020342c8819010b06401500da0118503400900c05203175901e6081b0350722900c5028904103540070600c400400c5002018180d00700c1c0c0014400b40c2000d48032400366044413140150303c400f046074000c3d441c0841d60103101000652000001071410700c0180d440b0f1039220343e00801d0141540e0070003c0e94010094589001940005e00c814109444a4480c036084241200b50000301c82d41800300c0120a03900c1c074081c00307a0a00800410325a03820b648074a0340003012502c05c0704080b003d041d005d10606499460700381d6003a00a60182e0004079425059006242c1094080e0300305411a8104100390002c1c0f9448100303c0c0c0e0005500c5a85070b45a0780e078180c00071102028070f040b181d03d07540001344003000e010010080b45494503085860000301603507042004050b200c3e0b031002001607001009028003040b803428440258003034840031f454200c030001c06200d514103421070b0204e4544c0c8000c0380602042e80244942c2c40f0910030074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 54842512 1250 54841262 54841307
    0xf0d05040b0f0c07060b03071703031021020103020a14030a060f1505071209030501091101080a0c0206060f040e010606020102031801140c0705010f0c0f0e0d12080402030a080706020a 80
    0x70744040103602c50301c100940903580b01c1d82ea031105511f0400696000701440d0b8200206800c0d510502d50f01c0740d0082d01d01c1c90080e03086090100e20401e109030b016180c042c6c1d001c3c09952074034940d40150087d4110701d0b02001802803071914988511880c03801184503481c865000903c540c10011100510846a0044040000e096914084d10364202c01152901c98100800615079919407000b02d44103411900003c11650174080a02c080140c42c8000142c4103c09890310701c8607a558030b101d002214161010000107038010f00c042000e0341400f00b0011030148025002203100c9034144103660079074031154060030050b0350000070464010803001500001c91a060028000100c5021020820070001340c4813645c1074100040210030888254008014060f280000340103548454101600950b21003903005c0124040d20100c00c12840c2030080c203681c41d40d100ca0541c0801c4401e000445200c1c0300200220703098464a0019400309441c00f018108641c800d420250340d4801040b002000c2020050300042d101030038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 54843762 1250 54842512 54842521
    0x901090605041505060426030d0204140d0213020c0f07140a21030e0f1f0909020408070b0f1b0604150504050d031a12150c04060c06020a02030f0d05040b0f 68
    0x4245c125012a0050011210402800d00d0044031030301407400c500350a40720001d190b03910702e14140c0140c82111340401100d44400c0a81040c022070002c4801c0082d403140521040c100c04d90040d0740502240781c5075404640c000c0a05620179454150141c0002101c02440c914008281c0342a000503400751400d8200000c04000705101c00916260384d00005003440070311400703403109446d080048014103a008010705030001102141d81d0030060403c1e01d54002818500d0081008074880c002c039402c0711b501d48010702c4c2041c42c041e88800e07603802942e04c0c911001420040c003807a0b02c590300c05000d000e40403e000380c261030230586000b084115200c1c8134560b03c01c0c208410000412070104005c502c50340607003000700700b4050301c0021045880c03510481c2c1e64030036030441304414500c800003600d50480048071243e28080d03e92038403076000350046209600004980c039100d04001031440e0050706440074280112424a07000e0346184600e1b800c1b1505031001565201c04110921020080003034000790098800401d0b03080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 54845012 1250 54843762 54843769
    0x3010b03030f0d090611030604110306100309020604240306050409020f010c06090b09030703140403020a030f081207270f06140403080301120210031b14090901090605041505 76
    0xe0420300040c0b00d5020610b03803001c4480e43c110405607580180d04212000c9214210007140c4c0050300e52a01440c030701000280010502822203018100090038248416a03484089000d072460403012a007080090000180c8400c40408902c110744425180c1102107010042c01011641181d104a01c82c2c1d0800e443d40001d602e0344001c0315840042841c1c6030304812103174181400505800200102290400f40800801c51004005031445a02c82c0d982c07012040802c070842d41460050f400040e6010111140802c002000300d00e0980704144505041c2e410520013444150f00700c0780c100e801201280b40c01d850790003404d1103107140190242180d12541442c82c1040b001200d0801c10313008880501c0ad0320f01002500101c09010358000f5580070300c0182c0d40b985c56250107203100c0720303405089010346501141003089074068001c8503140d40a0061041c90224071020407503c0c0c40c511004020311010820109907140c47e118102c5018040d4500b003c98600d03d01024801100c1c4400c80700260105032110038030003940c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 54846262 1250 54845012 54845017
    0x22180c0314150a0b2d0f040501030209010909050a06060609030b07051e0306060c0a05030a0810060e1903050607080603060702010c0503043009091b02030307030e07080708060f0603010b0303 83
    0x40800c000007410816103404210884405ca409004900750070400780304490112440094840064506050310b124000a01c001d60340207000c000d5000c045e003401409044095445040058001c40803a103510071203403200f000b101d0705a0000030000312180010300c02e00100c1415560401428a055481c0c0a4608122440901d0b421140103a40030b002001c502c5035030303418003652101d207600c42c180c54085400346091541c03903100190100c0402da9401c0000d203168051081401211980e4a40036003a10b0f084041044402c8075103140d000440070300c0d001001040c02003003281d02c5110285c48414490402e2400c241c0780c030100a0403101103a04012200807800d81c02420380350007561207848041180111b02404400c100b0b00030395002459401c1c80c0c030801942e4800e0640c0201d900c0d400081001501211480c100c0e1a107e85032040580e2080000c6501036109901c000e82c1e010180d8159a00192185000d07810054030790301401300782e4001d2084c4554440074016803a0402802c0780200001610503000c680c5a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 54847512 1250 54846262 54846271
    0xe011a07060903020f030f03160908030a05030a020409090506070305060a06020d0806031c0c0c0f050a03230d020a0201030b030105040f080703050d0f0c030506030c22180c031415 78
    0x68682c0c0c412402c040c000c214540601c400201a0b1303880f1810804002e0f502d410888040601ca145100e01199503405030160009443c4a00e000e58500f0107207405c181e40d56480549201000c0341c1c00c0000040d1900ea62045a00c0e50784900e010b02050b060006004041d2a0080c041c03510034081c020341007180e2350300010999604041410100c2c0e03203640d8400041c1c140307040c865001c035015140d048483c03885a44502a81c0b105840380d24113551007034945000d034012a2250089903040000d1000500c0400d02801b10180000041419007000e80da080c0328003400d1420a00705000940e004d0900e04d000c540e090b02803d200c04405800030440c0e4a00358542d0302054442c180c01400d450800200f020525104000301e40c00450043c0c0188410015031070904010035015001d500000d2800d00800d600f864089103003440f2001c0145104c0081e6010440c101158441400380300c03509684204901e1816860345040040c207004a0b0080d0780345186040c250311081211445924a0b00412004282100d0090945030007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 54848762 1250 54847512 54847523
    0xa032301180201031d0601061b0516030c0603020415030203280b0a05061612050712180b090306040311070e0408090906060408030a030b010311070f150e1903030204030b100e011a07 79
    0x1114a50702100c5001591010090014000d0360120f0098201b0442f0540859100ba584114a00c6d0307104000c8089002c1e601030181d0465014203005c91151094012712317048952800391555003c4a20032401e005045007100c08403180e1902c20b0307440b861078003015520040000f5600da0389408240c8411001841455000a24109468074401030039072051041d202c189034402e96202000c90840d01c04cc01443c54241d400800030040b0501145140c03a45041c1c40050714080c000f042d581c1c4880e40c0940f10f4540c1c2202140d17880c0325004000500b001002c0c0f4032401789000c0c001e80c40d5100c0b8290140600050014220340c020001000104541d40002040b25807030091494002800c503150001200600900962408118404a00d0100703201c0840e405212691060400360358025031130030054141c0704444a1085590824049080720b408242c8140c2d04d401c0c407a25005145c2074030b99440030b0034203c007034840c10b424060000c803d2100d40c0040006034007500d0005a10003682940c1c0c44882c1e40c52050b808000c00307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 54850012 1250 54848762 54848777
    0x6030803130812011d0c0a020a172218060e010b0702150d1401150c030c050f1c08010b0f0304121e03090302011404020a032301180201031d060106 64
    0x180402c0c01c068420b0401040b00c0342055594a1029940915103601c0408841c2d42e4072000c10702c504140c101300c8162030b01d981c0191a011030180c55455007001c2c0d00a4506e02d01c20100990b000e17480070924a03034810000b00610a802509206a6030071001640c8512101103140a900f80845074400e130410781110ba500c0b40099803074000384082001343c200d94020049009010800b805c050606400550a000c601c030b00004d0940c0c0c2e80c10100c42800785031a044004240c2000041020910038030f107500240713010303004544a0105070b40c88140743c80c2c1020881e1100103a48081011050392244041c0e0050403255107070ba06041c400d1034a0f103023503c0042c000038281d00c440305604400c103014022101800c450110f0648000e0281d4402070b0250509020481c0154030b0292001c0013489003205490040f60003400c503510310b5086640360307507c54440c020005c030f00200f28030324040c420343c0902501c4040d0b8044542000c450f182e51002400f9141c1004944085011040300700c511000c000030440d04440103490401c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 54851262 1250 54850012 54850051
    0x102011d01140f012d030819030e0d09120c0317070506010e1b0904140a0509010e0a0b040807140607050d050c1c0c0c1505040c0602060c0a0e1314010801050a06030803 73
    0xc03003c1701641700400b200c10226040000d1519520241c01307450041c0c4003840101c0b100c0a485848a10b0011700a000c144500018098401d1480391a01c1813481041c004c50440c5e00c030b40342c2048030303010b4190341d0091074030000e009000c014042c4206401840409103641e00d504040d803800100e4803a5052021080d071001c80c1100095689804c003003481c0c602070302c0c0c40b401400d050003440c000d424111075a040d19820301043c15501d80c4009410211640c200f131107124681c0b16075840090741d42c802107059500c0560b02c0542051130100384841409440e642d21002e03542c2041c80d6400d810b899005010007030a400601160703071400581040410001c0551400060028480c8416500ca40302c00c0740c003a1035818a00180341503204140d01c000d0103203000302c0307250302a9a41c80340200e9440ca801c94141c42c840d00144000340889000d1001d0309004840201407102c40c904890412080b81e0340443c103030f000744c0d440800402c48414288140fa0304428481030a025003429619a000f2511011b450220522251000307803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 54852512 1250 54851262 54851339
    0x30c010c11210d0c030b0f010e010509120f0304120c0e0c0304021201020d021606060b09061603021c0507060b0a0f0e0c090d05070303020105060108130807020102011d01140f01 77
    0x1100c1200c07054004006684010a0090042540c481c109005051f1950784140d158010a040364050105035119031904503800148901c411089008001c988100d0401e821800401c0c000340020701403044d20005101024142440c0b03025882d4441c04144040d5010f21518541c410101c0b6400754050b125030101d419102c104500a02c0752000303000344c080c4081000303c00c9442282000e04201c0c00b480303061142c55101d80000000303100341d024903070b4008801c100955403200c0080f01204400d002c4e006980604280490b14000060034050400000d41c0010b40c04042050303038440c0402d001c030166503040545042c103411317454281c09402410150040d031000259039440d40c4088908803100a0a4490001860301c0c08560726811800101d0155080c18002003055108109080c480c0c4080340c1040200c030003944441101d42d12800d01a030455494140010384d05020307035030714001c0111f6400001182a00c2080010322104007078500d0726001164030041048000030b4121200e8544005810201c03649001d249 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 54853762 1250 54852512 54852517
    0x6080f0a0c0b0307050313230c03010f0b03190f02040207060203041401060501050307051303080403230604020109030201050901170c09040f020708030604150f0303020705042406050a030b04050108030c010c1121 92
    0x10048180c00c6074023140f030003030342c081000203070700506900074030903401d2001e000c000340c2d500c407014560598842c220200b034035146505181c0340e0031b01481880ca40e03000c480c0c02140c142c0c0d12058041d0350240d000020b010800c008c6100840c140308442000700860f40c1000c0000304903202c060903400800101082201d500c40392440c2200003076034081c0805a98598a280100704a0b00801c003070940d0241c10314650918240100d59240b04980c160358a440300c0303040d075005458541200600604100412300100700d07441e0b103600c12501a030484030003140c603801c3d17000401043d07e00c40d84850700b01c64014460000051003010030388c2d4000b1030465000c00d152000130041c00f001c044030750014007085481003000040c50303004a070b000b06032581550248090000501503842c81314419400200200d84c04504104407880b4401900a5007158600440e4101602d800141542c41c00e80081d11190000164004000c4091003030003202103860030841c01c50141868156100c01c841080400c92151244600d00104075a404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 54855012 1250 54853762 54853793
    0x906060f0a0e01090b0307080607050d15180e060a021309020304260a0206060105040501020d0e040e030a02030405180907090c0c0b090d0216210606080f0a0c0b0307050313 75
    0x10b003241541e915111440604003150302540a17020b80e0402248080000c80c14900c20115515064034202808004000414119076031124480345c07802c02264000008961079450010740e20042607600c0302e011030504149001d002c4c0050a44104014000d00745098184000c0391400c00c40180c4940d22410200c142511607003d0a4904125400d52594040201d000d0000d404c0039900301c68050781d4260040d1036030720850240a0150b800400c03094041c500c911106078086074041d02c0460780c50071035162540b640d00314030819405a00081018021420040faa10300036441c0b100755001c0078246444081d490b100b903402400030700d0383c4404a0004035070117038184071841607000d20400a0382c41c002080989440410b03001c1c200501900801c0424400c0d2006103001307030307440c0e1940c00d082560301c9860700c1c810614003d41101d01c16103800000403280414840080b4040d101005071110078075903d03202c200e141c00707500841c1d01c44c1c03014020300010700e52100950352f00c01898841819903000505080404184800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 54856118 1106 54855012 54855029
    0x605030601050706021308030a030207150504030e1512010b041502010b060a03091e060501050111011107170c0607020708100e06060904030507170403020f0301050906060f0a 76
    0x14001c2160710500c0c246c1c9080035a655210a0441e04024034910200b0f0703020407147d05009866a03036004919481d8410011460541d40240c4036000c4403103010f000d0a1540b02d041c0003405041c0403104000c4c940035802c040d540e914004950160b03c40d0046226a4110440545100e401406901c1c44d9060041c103090800b00340d503c089005007001001034414100280040c60f0802040002c0c584050080302c000c2042c2d81414000b41914000560043c4180c0c5030620041021680c2d1003940c28141c1d2011413020f0021140074290101d000e0340b02e0980c0c4070702880003403161850300002c002045600c4c0c6000d503046008858070002c103c59a800c15100181c0000f00080c01d6490b0607800c40364083c0c46420502d05290b460784880588107403406000c81c009000207014019490a14038400010b1401c030000e01042ca85401c03580d4440310082c0c4042c2c01212030105260541d0b40d9004484017520515 = true := by decide +kernel

theorem cover : BRFrame.Cov 54676262 54856118 := by
  have h0 := BRFrame.cov_init 54676262
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54676262 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 54676262 ≤ n) (h2 : n < 54856118) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
