-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0466
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:57:33.544886+00:00
-- url     : https://prove2.me/submissions/7b1ba1fb-2142-42fa-b96a-8d05a11417c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 83633094 ≤ n < 83812950 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 83634344 1250 83633094 83633119
    0x15040602090d14012007080f0910020304090c020601050a031401061512060923040f0807030c15060305071a040b04060e1801030b04020402030a090b04081c15030618050d051206 77
    0x4505c0d20500c400280115004a06100c4010060b07003560301450340140201d40c8107602d24402943c0350018030490000b54102030b4100b00b650b0000c9655410307104041c01601c1224110380b0b0320481d000c090803079509550740c1c5d240c0001c4c000842164000450200e5039072614810000401c1d01d007507501e16004500c0980c90408481e00341d00c45461041c00e60225a0301c400c40e240c1e941c2c1016005496403940250001600085c0e03802015801041d615015101d420546a00c0358040010030440760103000041c115841094140900c265900c04640903010321035802d0b14241e00c0d9441008aa000369104000ac101c10038031040f0380b403524400707005000303480022908496265841e814000301010300f011f03000b0340d400000710321144081c1e041030305c1042e007001441d2503a0030f09103090013495009d40c0543c1c554501d0b0210100c03610750540101099087d19600a501850441c2c8858000b0480002d411005118110917003002541c144001d0840d6500c688415480d100540000c0c102654000c01403445820080d5a1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 83635594 1250 83634344 83634401
    0x7030c1a0c1b06150904050a0c03080a14030f06091f0e220f12090504140a050903040303091a0415080118020712140c0f010506130501060215040602090d1401 69
    0x407041c0c0402120745100b240c49070b00b007050601003200d80260409c400c140020042c803110030b00811281c05e0360b80d40c10b082c51003c510b00c0000c0f40015a0100000341ea2080400d41c24a00918500d41115011965404250814120b0a1040c030203601c00c3c54081440000c01450a5000300d80c01044009440c50494850b42e0b503a0f5600070754407940005107400304103103c40050500c00d5842c1c60203400301400402c0708a01114514420010485904072200d003098005072040c400402a641100d50507260b000c0703840e081412085521254000320000c0305814400000d90f65454000e40031031405603100c258441d4108441591704501c448418100d05004001c0e100001d243d0446021400c0014030f48132b2400c0706411056112072007152003c110f6480342c4c4400660b4900103500c0300d409000e0403a240301060b98070403000b00c181d4800744502c80c00768001d140c07aa112070548200c0030f03521604c108001403070210104009a42d21306c0000003652820400358000c600e840092250031222000300c2854552f1010030980d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 83636844 1250 83635594 83635621
    0xc0c0201050f0d06050a0b070c0f080d0c0212150709050105040b0d050604090506010923010b030106081509010e061201050c030109020c07090c030b1005030103050307030c1a0c1b06 79
    0x410302219800052210f481c001141e0043c0c020300380081c9400794035591240e01140d260007030f840668007004200030001c2c1202c07410700c114086403103490182100801c248030030740d00c17040c601805a030020802030046407400000d200140031002c50b01d1100d000c90401c0d0340c0080c03440400c2e42005050000130042408011001c4050f00c460300071846001c2819920ba10204001d41018036000f4041d1003100e0002ca44a400d40d048040c0360095505244e1004480c46c802102c0071100384a03290005500b000144031642c42450b940e540610b100c205114a285908049078202c4400d901040103907114a0611480f80b4020994503002043c21f4000d214a081490b421070b4a40300600c648070000307900003160901800f0a00805004001050f03040180c0030000e400980a00140c400302032003111440451400c050003201581d069981140c01103080c0340c080d680c1501c00302c01c0410141d4450344a2544412501c240104844c40f0700e001000003501c1e130800702c10003081680903c00d107040e590441820803506014014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 83638094 1250 83636844 83636857
    0x33c0507120b01021c020309040c0509100e01140408060a0c030903020c060c0f0106080c15040602060a0221160906031e050c1303110f0607020607141e010b040c0c020105 74
    0xd4000075091003200c0140c0c0340030245c40c06103a20103000318000d280103030040040c1c030802e0000d41d001d00003061141d1080b12248a0310004590019043c14100740091040751200407141041c1084603681c0c10001e82401c05030440c5d8041c404682c05681000b403002000e0003209020105401c09002000840e07a0280d240c003c03011340d8900852010414200e0f81c0010011265407100c410000c21189448030001e40d10b50360460381250280d0b44a41e03a0b00212034081d001c89003201c2643e0301621490315007041a00c042d5000d4000c0749501c21510181c00500504075107614014410807102a0320544d0100000d40a000300760301c071030281881e014190300786c180c69101d40381d6a519042000100d60307843c820100b00f203000320320408161210111011080040c9a0507000402204480e40323030700c00d42080200a40d40c413400e030000b50400028800030001880d07a1a600d1031281e1424140e0340303403d000050f0b041015459001a009513915002d100000b42018070a9000248240c075101241a20f43e8001a00c54402c09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 83639344 1250 83638094 83638127
    0x10e09150f2205041a0915150a080a021f050403081605070f24090303030e1f1d060103020102060c07061401030803091b0f10033c0507 59
    0x110440000d99541e01140d0401182ca85541d80c401500720481100030301c000c41d421901c40c00c4a510070042a00310a109a2059080400800081d5004061400040710140809201c10b0120070421580d0340c40d060448094140d0000600d0001c6487c01005405480c00d8088028030410020003008207074800c0454090fa41c1140310566104d115440d60031170101040d001030310501900700c0100380d5180c0314211000720749a40d9081c020500161480c4150f4103100c5c002d50000c1480c0318804c100080c0683c005e100741c01d4043c1c0542d904003404842003620a6010443c1d0014141e2ba02d1030701602203000b03002110341c5403d0720b00910f103d6041da400030750f50b4040501040400b03040072955200b0404240c10054600a450621040559482c502030220b030700b00f540c8850180c007590a00321482d10010381c5a0f40900c03401004641e0001c0d17a50180f00071220000251801c154841d0000120040da0b20403122030342d00302c0c0950150b4510100c05a03074502e0106840f40f41054203140502001c00e602c50317007c0c0038211a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 83640594 1250 83639344 83639359
    0x9020603070c030c0209090309010f050c06012706090e070603020711010305090703141c211a0a17010501080304060c06050c250201080903090303120c0705071202010e0915 75
    0x1a0700f0150b400c10901c3c0e50084d4001c1380c1d6800c0201442c0040043c01d1b0381e420a0326070a0040c0e02080003a14103004104a00ba00e640c800b200400416410b509210a801582021286140d4084800d0001d84006800400003140c41d000713071040540c000c10058000b41101c0c54110b0034007c142c0c0d01c80903050101c41042c0d04154590020800c101c1c0c0c00d00c919030055610910851184240741c0c241a100c550152081240e07144039401111054002d000d0304402044811154802c1012445440b00500d0300024606081d00d0f002482c2c021921031b02c00e440c010701510402e1a82d48841c0b41545402e60b0816000490300350000d0000f0030066401261640c60240e0000700450b00703543d90001c1e50b40c54001c40d1542c40324941c4614106032448819098040050300031703695998981e8484120580e24410b140b12700390158010008a07180d00000079105170442c40780710f0160f20300034080d11101c2c98014180c001d4804503501d5041d02d4210b6070803c0b10002d07003a40950f8955074030301d4800040200c0307181101c2a14080c182 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 83641844 1250 83640594 83640617
    0x10e1206060f010314011d100303021f06050301110301050405150a03031b0803040b18030a140c0f03120f0105040603110402310326042105010912120902060307 70
    0x40e8010944203682c15110f904a0341c3c3d21180310047c5a105503008149a0000d008141304a020154010940b03415800034048142088000c0c10b691204102d80c1c910079039100d401240a07a420701400041e90543c0011903102d50400c0104000c44101800c2010b010b41070a800c0c0c08161100ca0b030a0040700d405080030200d040d01d8883c00d0012003402c0782c004100c207400100b0031040002ca004243d00070110506d400000320007825191b6603c2c401da41c038181c0070621140e81c0c00b41981d0900c0041041a000c1c00640340800c031301110305031441e088842c09104a40885081000d00491980340500501c422207050060314959110110822a40b903609801903400003142d20f185050030741031030242d0700d101c0242c9800c50b13400005000503030618042182c00d0300c40c0c08601815140d50b446401c1d00f035803443c01d98030303c1d05103009a0342c000048918801c13a4022003007490840401c500303110706490b1034003405c0c440b08440c4140b20300901d13a441c4550106480f070303e000e01200246e1640000e59500801320f0500300d01d0181c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 83643094 1250 83641844 83641847
    0x70c050102130b0403050f010509031b01020d0c05030405060f060a0501030c110d02071d0402090105220e07030c0501051918030212250e07031a100201050402010e1206060f01 76
    0x82245907080b402e01507000c000902d00c403c0e400070310480e40568103031110100500740386c0c0c2c00d90b441510311381016402401104515601902200b00120315240014600100c0d6010f00041c1c440c80c0a105011170000b00401c4203001c42030144a07405034402440000602d0858002148994140541c1e4101552020030201c4140103100d4400203032b0340d403821201007040700c0b28025560803a80c0640c1d44410000000a006d01d420121072600550b4000c1c011405030b82071006120182014280401e2204025103110b06039200a225844070010301a0103451464190b080c091000e1032607602540c104a420002010b00704290f0420025003101032a14118180d00c4244000c0d255170b041d003010350b01080403034200c008044000343c1c041e000d80c2d0201004805020044e1140c0c2c0120640c4a1803500030480000601e2407403182d405641c3c5100d408030640d20080c0c01401185400e4400100e40000d42e549800b03000540d80c00c81d081c04081801190203920781085c04010503140d03100581001e004900c943d90030381e001da = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 83644344 1250 83643094 83643097
    0x8180d1214090d0b0405010e19150b0d0b10060905010e0d1106040f031101030501030f0311030d140403031d0309150c1c03062c070e030f0f060a090b070c050102 70
    0x2c01482c12600c1541801c0043c01a101614116031075807800d540240c0d0818082200840380c2100c00103070410315100c3d180e810850020062040c60380b5500d21f80200b40ea80d86000000c1140e01441c0c070003c030b501e0403d00c0a0b400501c036800c090240502d8060030081607034841a11080c061003955441003040e031a2408007804803040c40c0150f80f00300b01207004109190000002401c40f4001d2040b078800c100e21800542c1211802c4c04007030a11004e0074110008070f0700900d0f050140f240ca280443e03107411204605241180c03620840500c15503110400d103c1816414003070195201c81410342055035410948440e07a07a8420030003024040e8002c07080d07050004e07501c1402c0d03c0c5100b848000760341e5010022909180e803403010001c1200802c3c80c21001142c4d01502c04028813900140880340401920340090407180c1e034000030300c0c42c81000072005e6102c200341c50038021503c42550741c80080c205a889140c245051403c01441c0f808014607002a0b4804107032440d80c0c00390007903003d0518099000341420a903019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 83645594 1250 83644344 83644357
    0x140f1c020c010c0305060f241903060302030606010e01120b0a150206011d040b0103062d060f09050919230c09070206040308150604080a08180d1214 65
    0x42520110710400c400384107410040340d4080c3c5607000c001c16034503a0200035064544032403d58100c07600c44c0508000d548220500c8000c4402204042c0c1041c01d060003010000001d0742c502c00000c1c0d100c0707408104505040040703981100b0242014042d1603451000205030410010008003030079110802007001c1c0e12902c0c141d03c05400c401c07052604064038000003954401081c82a59010352010701c1201c00c001100000c10f0003503502000609583e46161103000160030303050441031031205a60010004250100401c03a000b4959101c045084c80c40c250700399088800382e51040707101c5805c040c100005420b021640040c403000140408498991b513050083c00e80402020315004202c10b500c604050410020b072545407035030229806012581d40b110100c1c3c0760481039030001c020030042d0010842810006285124119002d0001400c00d42d0700e02e0258940140c0c2030303060742e0310b500018110140c007000d40300c2c0261003002070351204a121540d50b5201d0309240e4101502081019425030320f03030f00300014000c4405c0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 83646844 1250 83645594 83645647
    0x90406030506010306050411030307080708130b0d0f0506010c050c150f070c0801060b0901020c0f0102160b0d0b0402190c021c030201020309010c09150503090f0d050d0c140f 76
    0xb0075038680c0350103402442c0680d820341d40c00e841c3c101c1825143c80c000003101d1010750b000380914200001999050041e82154410704041c100203000803445005280241000c04043c2e000880d0304100301203420708840000c0c0c0740c281084403a16080001c0740000070074416603030094a01200704034010703010360f071140a01214980d40100002d118000c1c420720140800c01c0d00c1c1c1041c000c2058a40c2c03824040e0b09071181211031805600240860041803400903814141c091060059a114100100544650007100d81040c09a5000070680e81402c103454442d50020141c244c8045240c201c0c48131035266035002c0b0307110b040c0820102a9100d400c42d16082c00c2025590301b440d40c43d01c00b01c0c0a61030701a011790801c036102c4040d58a00f081c3c5c44c07c0e4511481000007194604c03034981c4005a1340380400c40d500d500003401e404003171061407134081c5220410004041c82c0c100c0c030381d5440c0d2a1260308814805482c1d448039202c0420602c08865075071800e001048074511b40340d80041030ba5982103940b000e2540c0c440c2410452 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 83648094 1250 83646844 83646853
    0xc040e15091303110115090e01200d06050904022101021e03072d050d0b09010f0e0c03010f0e041a07020105010501030b030a0807020f0604090e0a020406090c02120904060305 76
    0xd0820b1081c00302c0522a1080e15100800718410b10700508941400c103085020001c0c80130f003081041c3c45503000030340960002001203190359040410b01010301e828034074049d8913500064003840030b90303075440307580c3c00382204072405201424940c0002e5482003442210041302c03941c40711940d1000000b54126a0b008020822403210f034003032003400502030f0304115017441c04070b02d0700310703d0401c40d0001071a14602d14a482c4900240300380c4190f002c55161f005202e41401c120303910300c4801075a80d240d1041d41e009000f1039162200007424006040c803c2c07600a001c1040502040c0014403c4080800008013901d082c51300000b190703a11824140c00d40c40c4000c0100060300d03484000d002e0400d03419004541600e200380c80500804860805240d902c042c066406006c40105202150052501402c1c10440560040c000d506140d01d40f02c506085940c41040c0700400e501c20966041103040034010f200c01401d035010f08010b101409407019480d09038030355031640b2090001826000f241d0b0703103510450103035402c4022603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 83649344 1250 83648094 83648101
    0xf010507170414063417041d1920030f09010e120910140304030e1e01020c09070917030304050d09060c021909110309010e070501050a11010902041a180c040e1509 71
    0x1106d03c0c0c1c0c42409202d0442080d10b1406242c488020500d901400c0455200301c02011800e407498001d1104041800001d41d074107518014a0082e50091070291083d1801c18a0300c0c101081b00500311803883c82c040c10785030003c0910002000d0b01d0302c21303154161010f94074800f14559101007201c2c1880200260105180e0100610041c15801220214142410b40c1c860900310030f514040004a01c00c0307070480f80141d01124081000d400c0026002e5000041800c00b0070710182c5600c90941e004000e6888a01207a002004100c24880c1c01c000d05400401281840e0110030305103c1c0041c07402d17944000c041d0140080340351003135042c6075025802004007400d1404100d000e41105484030b082c2e0090710107070303000c0d03090014280110304040703544411186c6c161201460b044174818140d6401c40e00e4a9407040d65503841c59010096103490184c080c4c440000c4403410074004030341d005c000a124100616500b024000c0701007005900c1d03203a0807681a0342281c1c043c1c2030309942d8404071882d4000c101409940020040b03051 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 83650594 1250 83649344 83649383
    0xc060c0c030305060111030406110307020d0b0702070b070c0e1503030a0f0216060504060807030e01150e0f01030507090b030102190e03060c03060105090f0105071704140634 76
    0x19021a4482c1e5414021500c80741c004480440d00c44c0300000c056007007080100300040c003c44215416115480a0700e0074071000381c00183c1c5010b09001c0513121f80b102502000700e07144d414031902d00589004100b0700c0c2040030316111007031540071a001c2d10305108100300110b0f245c006029840700181500400312544c1d0501000020309022080c1003580c05445490041c40c800b017440c0d903000c4140e47d001e41d6164103251400740c08a41004019041000780f580e85c510400200380d0070f0145610365003250103d00b98840ca0030515012a00e4001d08000802004a0043c00080c2c0f0109869040b14801e41010444078014400030b0300a01c612540c0c400b041c4500698010100d820852080c079218044058850769a11448040514401110041e0008804100c1c0c0c151078506089112511007043c98142d0030b000346960341b403101e41210560100000d20208080200044000300c3c0d401d40801503c00314100b1000c6030004003024180760002810b502c01c1302d2107020407019100d41511031500040c0c164501e0040000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 83651844 1250 83650594 83650607
    0x306030c050d1b0312020c010e03060609060d050703030509010f020c0307090f06050a0f060806060304050a02061c0e0601031e02061605010b100c0605010e070e0d05010e0f0304050a05042306010c060c 87
    0x321708003d40a00400c06802c2e40c0211440c80400344060050021952118104443c0e9500242600d42c41607a900c05c07400894030801446016520a4480540d580001e00001d0642c0e141c0d65410000c5602820381344410751008035501c4111842140042101504241c20780d01400e0360750006600300301d6241c800603140d9a56230050046070300c41d441300e1101741c54000a0043d24481210f002e4100e500c00c482c002c0041c2012401000d9046a042d82482a00c11458a41c400d8400d44845481035038800001807090003954210710303403103400d11402c6e02004030031580810120f00912400c107982c03085440c2c2c20010b00c2000c2d02b140700400401030403d1500a82200060943c010360503054619a00c2c210000c26505a4070b0316860040c42152104500b0b2940f0108010252284ca07204440c2035481c0e622041d0042c10410440d00c002d012400034544541c20502801860003641d0301851140382403807100340b07070b45280007000100c0f50401507014802d5a503180040c6c0e0b0b0150102402071540f8030b090a00602c1590007031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 83653094 1250 83651844 83651873
    0x31e03060f0625031b0506060111030a0e09100f030b01030308091f020a0228031805010519020c0d1a0a09030503060d11030610060f0306030c050d1b03 66
    0x31540c07081c00c0a42014410315000701c01846640c0c4203030701c40380140001d040740300014443c407901d0544510302c069000e090210940020407903940c0c1c0300c0014000c0c1c56030841020701841d03101c2c1006500b003a020010080100c000d1703004080c02407241e070001c500c4012003121948081c2000815144141d5520703d0700c40e07a41e5000340f205400080d0320902040c484a0045004441c0c00c640c2422090906800010f440082d4000b071038a90a61040c3c00115107140c40300c91001869484044160101c04440d04001e46011644d4040540003140b24030b003405107070b80000a5803000c0503d8546003030503c8064a0507458104042c00f0554031503002e004800800c22082c164403010501c0700c41500e42515980c0702001a9615040c0c0140880c03003c0c00090301c98100030031061000c41c000c1c0c00c0e108489184001290a0020a449984a80315602d0b4140800303500007401d9082c1d0b406601d0200082c500c1c1d034903281c0022019014280c45812901d94403030034401205144d42c5510580c0f440a0605640c1345030000101c001e00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 83654344 1250 83653094 83653099
    0x11e171c05070804090c180b0901021203010e07050c0f03130302040605060c060c032208030412090f0e0a02040b0c0114090a03080109020702040e030712090b0f07030f02031e0306 78
    0x205400c03814600c2003054038241980f02ca91203051600745810480581441c0040008004142c0d100368540407100030018001d00c440d1803907598454807a4002404e0030741e09450498181400c00042003481080200d01b5400103461a1894a4000904003c0c0c2010880d44c003600841c80041040941c0000040c0c0000880740308035400c1100d540c1d61030a1190394069110020465045000000c1e800d6075210300a540c0540f20219003410400c041402080081a1000507502d5220100410040090026082d15020b015050200d40c0c42c2c6005460510040d042c0510702c1c1562000b4040340d0b085100c0d80588025012541e4190785403021440c40321300a240001c003000b200c5440902103210f000c0c4c08110804030f103406654400d1142c0c2402d000030f01960094000300d130016600c65918a0354401400608001441030440541d0031a1013000105100300d0760f003180500305c5080000390500040c0408640ca02c5034103040281e820720000d0b0042c2c3c1180100c1c554004800c0c442c0800f1035004000e4401144034071000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 83655594 1250 83654344 83654383
    0x305011b0311030711010b13150503030f0706020906040302040501080c03070e0106020309040e07050a0608090115120f03020a1b180c02030f0c07051909051b03011e17 73
    0x45480c2102a664018001c2a21642c00c00201e00f0700c2d40300d080100001c942500010588040c004003040f812190013005d010015a02d4003e03020718199540c52000030941100298104140800c00c040d4030310500600504080d8001000f00141e102c180540e40150340007401004550303940c80c9140c2e100c1c0300f1204124407a002c1c00e40041090a646002c041c10713244e19a00035400d002c001814000100080315601d00caa2240b148002101d640c0d401441c1d0151070304d903035406500d061410f055820340d180014200500c0442110a0100340142d104a407286500100740b16283d040505099040c001d4448020380641c003180d041204141a0381d4400e0101c0e0000d004c40d210764040413402c81c2c21906401034000c01a0000c001540030b98004c280604681340419042d2915542e450000810184210504954910f1a0a000c00a441047c41203c0e80000c440701101150030800c2c075094060300c03050141c508541300e001c6110049500780c50b1403070098800101510801200d01d13208540c0c82c580d000e03005101502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 83656844 1250 83655594 83655641
    0x10603020304050c19060c0611040603060f06020303090628050c0306100201060312030213210605150d08030703090501050a0203010e07090803030408030c07060903090311010302070f0f020613030501 87
    0x1c2c9015207812172103c880d5041d003010b050040403910700d0400c03401510042c0d118918540b041c0d040e500104010982900c1c0080c1a5241404014000049512000942d041401007001c0c40d0700c04580c05902601809408000ca1301c401d026001c16820b010b1038079a480d250208000380b5010756001140980750880b001120a0801d0808a081c1d62690100400981540080401e180d0094001d82601d800395039000e0b4410b52542207100071542c400c003008003009202d84422007448070b40e2080365004070346904101400101c00c0c010030381d440c02020004185080000010b900d4900c03e900802c000d5070310200074007483c200b0307002100180d0401c5c0159401c074014040414401c5009504102c00c81d00081c01842c103640d074546a82110340c1000308920324068003044001e0004400e4802c0352030983c0b003134980146450444c2000511426007a1006050502c10440c0b013000c07402290f40c141c0b00c40d5200e0a886061031161000c0b50307150103107d207440042c448904010080000c10340080e90840c0030003079103004203017 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 83658094 1250 83656844 83656849
    0x15030102130e090a02270709140d05010e070b0405040c02010b090c03060f06040e090d0305070c0f060207061401030b150109030308040c0b0316031a01021f14010603020304050c 77
    0x70614950110503640c0007030070018909060007003540140480c0580710f9001468022516181124903141c04c6c50510454050058100700d4080380c02040c1071401c0a10f02d0b00301a1050b0030f04155a2201e841074026a64100070020309400905182c82030100742c900850395003e80007050b0704203000781e07413055090140c00d26103588144101c42484100518401d11921031810030951580043e100b40c0d0896407610290303c0d69190440148000e10200200401030315240032658203101542840f80700b01802c0c1021b00c60661350007615000180c1d0084030001144000b403030408001e104103e00105458100894403140c48251070059040300e0044c148900103075204424005000fa41818481c04180e00a41c1880820310a05219a0062040c0c584200007510b800b844c50040c0c0045521041f00c41407080d04070f103c0e541c1802042210b0190790001d26080e6a0f00380040d440300d00c0c2500112068000c850b88075030265a80d007004510505206104086503141e1100070040d500c01c0b11306540c030380300702c404442301ca0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 83659344 1250 83658094 83658097
    0x13050d020307060c050a021e1804020f010f02010f06090b01020f01060b04140f090a0b040e060910020a0207120c030b070c0f030827060f060307060e010c020a180515030102 75
    0x603802800741c203840c0d003050b600f03940640191200f525503100700c1402a00507140d804059035400f03041c4400803c00098101000f0901c2200a41c0403800c860040500006807151007038084501800d09120398030301e0542c1022070060844601c409441400d141c0c0002c0c07881c503a6402074003409405c1c1d0a1300d051411a5180070f0036034850344582060303840200010010400d4519003501903920042886d04000651800142541001d94013002c10950351440d080c054a4a0310411080d5150000640f0140c80e01e00f42098a074140f80e00d910b172429400040744150707540b0a20030680a0303c840e80501e00b0380d011a05002824105500049170074000040c0481e00741170185258051031a44490010308a0840399011104179102600e9619262214940c8441004408007a000580356010040100e40790980345407100e150060300c4c1718020b8010a4091128a6200b034285041c0c8000b030030012000301e60b81c40490803410859010791401c0e8000c85c01d040c00e0b40741682144e405003074480316038180070b5000f078200741c200e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 83660594 1250 83659344 83659369
    0x109210908070302040b040902030102030a0b0a151b0507031509052116051f0923060411130f0e0f030901050406080a090b0403170906011215060b0408031305 69
    0x15440b52100300300501e4a038000d070005032005030010640b07124503070200342660170035516504941d80712114004a800c294180c0001810701c1400c9030000345ca15180074060b0840d46646031207013100390620609104c010041600215032180c0101c482d04d8004c00c84400030400c0140441e003d01440c0f60041d1103180d0b4500d40c0a00000803900b0358540107485d0f01840701c2d01e00810044490340160115640624121304410340e8106014001050700d03896403038005100400c50070020740300401c003c1415048440024081e5105601120b803444245082001543c0c08600c0000341c0e545a0a01d200d100b4407095603084942c14080000482e010300b0300d40c111154490203210f4a60b800120280810404203200d032036025080407a06d00c001404001c0d58482c0c01c2e070824121020b0300418040e09240791514014551036500c10030120103400c00d5414000c540509118291001c2c1440400005201600aa5500c18801860003035030703143d07489960f011000d031244c00c900e2442c4440024480000350b2414414501d910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 83661844 1250 83660594 83660609
    0x50d0905040b010e010f030617033414010b100306062d140d020f040305060a051306090302190516050303070503160c1a070c08030901090303030f0e01092109 69
    0x4c01d4241da00044406420303034030265081544540e00001c1216000744d00100015030b18018542d502c1005402c5007901490140202640c80c440f9400d090692544142c0300c01140e015651655103140200c1990240480100701d961140245440c841a1900340d07000e80b045840b2a00d40c0700400f11080d10740403000e0300c2c900080050108113408031900c0e9102d03050840c00828480f905504210f88031032244200d0704400c194600300d0100107820700c02c1c01401c200341c0340d0143c5096000d11980c030b40840d844841c00544d0000900d50354540c041c100070140203104640c0c1e103005400003003070340303190b10b051641d6a100d80360103c480d00d140d00072000c50941404400c840e41d00350044010762a02d08491100954400b141e00c080e544118114000b0038040088845001c000c4403095400d034442e01c26052004101d00b030760744004a0b650082006900a03601320b20b070601102c1c1c15013800605404180c141c0380142c0102c03401040c065113028020130401000e001180b030380b0504040c0f803903a40d0040203400e40b0401114011901c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 83663094 1250 83661844 83661857
    0x1002120f040201351e01120804051903020402030405060a06080d200f0f060601030b06070201120b06040b040b03090c1008010b0304052b0f0206070c1b03050a050d0905040b01 76
    0x1031605001d01094800c105000e107080401c01c000320180c0d14428056a0071744045a80601c424a041400001d550141280140c0641140065680c2c1d9040748907602c946802035100c010348410380086603420b00c00540c0c01a20542d607914051800c952604021181000e005140190101304002c00082103a02c0c94020780310302c080c489404003640380700c1c0d00401c400e8860784200500c90611440070702c0000032480040004203580e00704400090180d038014040e540c0540801e000001c0940e901c5280c5408041041c04000740c1c2c0c2c2c0303506001c105144190b41003002d41d10000100040d011800000842c460010202964107a000d1a401c0100d042c600400790300000348440c00611911004000858100f0303c16005c58032021900d98007000020f080002e0740308045502410b00d510140c12403e841001d1104d807010b403040e0301d00310b0320140240042c000082c00c50a12442d05a0106140e540d490010350341180032034003100c40c94036000341da4081501000340026040040041d0b10308281c0280d01d03111fa0143c440c0c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 83664344 1250 83663094 83663117
    0x9040e07060905090406061a0703030501080309010c03030507021c0f021002030103020f091801060306060509070906050a0c0812010b03040201110102030702071208070c080d111506060a02030c1002120f040201 91
    0xd900380011740b007175911a80d64000005d84540804400311100c48460b00039803101100d040c091708581051b40f0020064004010320451b50380c0c043d03a101039040e414100040d02e80c80d1090200c0c9040003030400e080700d07108404030001c0c2e01134110b025603d08a805d5402c03101810811411002a80001e10000f5005288403203400494548689078070351045c455002100091605000f9501750748080e40300b03480290707643c6010b0000c0d0905111132540100507003401c84d0303080e2800000800b54031401860004201c0070003c02010481480c0884400c904941c091804e2541c46110410701c0e540151403c07404a00101240107a806041c02541e11074617090300a0301d060341c40d056070035000d8500c2c8041288c00c590200b005100007401e000140c4040c120704001008229a2510068a850740d0f6030f251280301d911188100203a1540c18920035407052043c4cae4a01c3e140c403a40781c400c1cbc0c030314003074070400d00c2e100d01032803101412702031440e40a0702822400c139956801685403a104401504802d0351302a00013411490344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 83665594 1250 83664344 83664349
    0x80a0602031b041e05030d0903030e0109091d0d0c080d050601120f0b040f020c070302060906040b0316030f020f030a090c15030518060c030112110a0b09040e07060905 73
    0x185500c007a42d40301248280c0c0c0c80821009150b40140c00a84040d04203d640100d403220011001e006442c0940c0140341c010003808000e0000301175031100504000200600340e0899225404209c000c0080300703010300000941c010305d03141e0700224413074130700d0030388611800180c400c1d21400d00e001c0255003080e0344510340110382022030041c000003020320703050101040100340f5440032803288864070001407800290400f400c3c410401039815544201c6120307070041c880d03481c015070040342480440b41d04079003184c0c2d102c1c00000411058040e661001c10030050100400402e0701c008010494815055a410000311040740519022809036003211801e84006000054583c00c0c69404140b2850240c0030300d03036113a540c13040c20110103030101c0c0d1b60360006510b61040c00055990368280300141181200a440c3c0c03894440c20041c6107000c144110078001c184981c0d00014800402d001c0c1d4180c40025010707020f0180c035036101104a9100302000380c052407600d401c0c05010706000c9003500070f99007907036a403d0300d25181008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 83666844 1250 83665594 83665597
    0x60b04051e041e0c090b030d0905180a0b0604060921080306010e010c080406030c031a0d02090a0e0601062007050102030306040b011205040b1b0306011b031107030302061005030304080a0602 83
    0x181c401190200d25a080302003030300d904486000381001007000c06e06000803c14181004203c072031041c1071107502e0800b0302c019a102d220050f071020724000b00b05010390741c04070810301918080b8016a0400000140800c41685c0050702106403041e0f0380190040302d201d4008514010000320700540701610605c00300c0c41c40d40c8038030414030f11650140341c400000b81c0c40ba00c0d031201543c450b07840300021035a6480e882c52141e40502500103005030b04200490444085004124001224480244034000c2c0340d000414408096000c0c0003500690b0040710310070740e110980030700201d07071452108014202c0d4401c80d400500d8005015001d0700c4060340a5030968507803105000140c40b40d10700f094140041e820f8405540e002604c03a4a11450141010a007241001c0344507001d0503107402c40880c02e0090410812841d6600000c222075404050600d031070a501050a04440c0d2100a800100003801041000406d15a001580078064903440141c040c07001ea0b03032400c150f0359214900c40c1111682250b51130a0100e00940d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 83668094 1250 83666844 83666873
    0x5010507090e0f06040e03122a0708090105090a0b190e09060a030b0703091401051b0f0703140f1209010e070e0a090c0503120408010b040603030e09040203010f0207060b04051e04 78
    0x40481e41400000b9115408812045902c27100819900000455040c01509294415090210040d242650744d0f21690240c0c401c20704841e061040004103059151070f41440321008112076056039884a0181c2d9020f144510000644800100b500408880a24000b442503010300c00080001c41924a10303903404032102c074010302007018507585070b602001040040701c3c0c0c01c410680b10000025649403072008296841c01c0240c003030201d003905000c3c2c41c0c4060082c0c400c46038829010300300fa00d5840d01d20b80b0001c0240c441e0803c07200c00f490000c0748640b45004514085400707010710034001e001840c444500d15988e1416480344d450746220360004503d404e4200c0d80281c4001c1d005240810002e61640c01192400240442c5504903490005040014030400c1c854002c5500d002c98090012501e0b544000b41800842c18905103d16032034000f0604540d001d500480035a10810015511000700d820044c000303200941149000e5400c0c14000f41040a92100005280000c0055101c8984454903050307127824992 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 83669344 1250 83668094 83668121
    0x503060f150303121b030c12040507031401022a10020715050108030307080108030310030615090f020720090403050c0106030b010b0c011d030a180e0405010507090e0f0604 75
    0xa4070101140e281031008005a0f000d01070000a0341c00c0082100c80201010451070503680320500500100540c42c10844082e01604681c00c4031a8455040a6003000d000f50b000a00300103103004000e01c150410b4010b41803a50407005000b240401e61409003d2200c049403000d8944c0c0c006081505013017000c0c1d4091721389a4050035020700d1140c40b411420f42142d000380c0082e03610341c1c004010040080e034054031a038090440040507604505107503840e09200d45003804002c03c03503502d03651805c441450f4110000c000f0b0841020071300c0010800007505000f50b00500701600d000c0d01c0c84201c01e112003406070b60b00c04150f41c060310100f096034503602e0448581d00442c4031803410f5501d8103000800f058a2010f1123001c2d02002c596540e07264034082d400350840d0000c05003800301004090141402e104084241c4919040c0ca08060f4031210a180c01e140400010350801c2054101141c1800240700d0158040c5215000a854075400c1644130a134506240d00c003110480030052081000400f14180342d081005c1480c80c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 83670594 1250 83669344 83669371
    0xc0609060f070804080f12070b0c0903030705060106030501080d0c0206070201080c0412030503060a050f0102120309010e0105040606060f080f01030f021804110108060a0302010210020a051b0709060905010503060f 93
    0x2d540d503401403a40590f0140c40c450340f08004007443d01c07201b8000a00c0c003181140380580740c00f210b95100805110000d0074072100c2c0c2030101c1d407207483c1e07181403044070300c4684c0c0401624459a113619000d4001d03c800e000750007203442100011503000340500701306052942c00a008a0505115900448118078020510900740505010005410f150442d4410115201e501c69507101e1610400f8080c0401c060342c44a07100740034084609a46036000f140701205128020400b5a60b13540300c4c1c0c585800742950747c1d405403040d860107081005010281c2d11000507100c0d5692500c00345c004c050340444080c24103882710200b4007030540041001070300c0c0300c40b4500d2842c40a024442d0502c0da001220300000c000300c800743e8520400c81100100d035a030205c3c0403940010111684103809055800003503a550303901101c00740041e40000c94204c01d60144043d5556010f481d01120302c0902c800c210035454016920038420ba6508000c4041403400c51405068141e4001070010300144e41c5c0e507961101002000342010b00038520 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 83671844 1250 83670594 83670607
    0x810020904060510020a06230a0e160f090606110d110705090a09020f0123280909200f07060603022805030a05030702150909040b16020c0609060f 64
    0x21000a441100b0134290060704800210b4200b400a4074a102c5001c002d207650740140c501410700040c100d0b60025032301c082c0043c800e00307000112454904036511086100081ca800012081c4100d9482030580e070516009000302d503a10501500c2100102c40b4081594003d0480c0d040518415040300011100e001e0844c1c0c0e81da03507500c2c04284180d000f9240d08801940303d00d114810350a1407400c14078240000e10308800368100ea8204501d40d0b442a00c045668481c00141c554040080c1081868100c0340303100047c0207900c2c10b0903014144803d0707849031612060a147c011030141c03140f80d04908038500400500c4d0300e40550801d4454085d480f0445c204c0e451a6034050100141e144c203d4038114000c080da12954003221040e1000e10134114aa201c0f503c80e030b119095880000f00301000b80c80c540740d416521303010880280c0e90301c11864003900d02c43c42d0700180c0c140204828040c41c082e1943c025607a084d080881200c070410100d80f500c0d11420000e41000742080b0040d003e007056802480070a251038055800e01a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 83673094 1250 83671844 83671849
    0x40f03050418020405041407080a0f0b041404020108090f0303040b040317090304090f050c190c0501180309050d0308071409030f010e010b0a12060f02162a08100209040605 75
    0x908964001c00b48a5010500b84607604161140b503c002000c0100c000351440c10070801440c1100c010240f20405e0740303e0920407280b0b0b03183e4200f0b40d0600c00007401886038800600c41d960302031004860503400104844040f40382c00501041c4844e5901c0c0c000c0c0510b2a42c1d855403180e080112000c3c2c802c40030400d51032100c581084055500030300510031400556030b11440c000ca6242581d074880891541e880c5840103014401000408840317068024901e51420800303045c01c02e80c2c3d920b1190001900c030354207018101618032084020003250a119468140c40070340c50700240000200202e0b0002c000c5499075001c02e01483c060180c444000c40e100310194503009001020a007003008454583d8000c2c2e45480e00c04543d0b51080c0550200700c10180c0d0403040c6c0d035241c250b080340c03020706004c0003422060307450400d2508500b954040b110b4190000c994560120030514020450000f205140400118016030042000b07042d116040c080303800001c000c00380c8141c065212030083d0320811b2706075030140d5204400101c40c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 83674344 1250 83673094 83673119
    0x3020a06050709031b0303080c2703071a030103051b060306240a09210309120302030d0203090f0c04020313061e060305031207050a0c030f1211090f0a030506040f030504 74
    0x1c58100040034a40c95447d0142803903c001e00034440c94201444282540c00401c12000381e260108d102c01c0b080c1c038401d0b60109041c03071110340003064003104446120301c615a4400003541240c0c410800c8030800790140140016004450101c03503440030007000420150329000c110700c41d504190604010800e0918110114a80d000044000116001000401281d512a502c4141c8044017080006000040303503001054802c4c2401040035001c050072810003418420010ba620346044100110340e04d080c41c0c1e0100b955103850007512140ba03c10051401050705060007034a0041d00584a1045d1244142d40d900f0007500401149a00045880050710241e020a0056200440c000d0740a190794440c6030105c15902d500040c605007e0000810004a005d94440c0c901d1800781d8051603d0801d0380d030345100495072003007150a007104050801ca940c6116400304001030800780b2046511549c01031000043c0321030f880092001403c0740c0c100400003000f190b02d0103041604244240b41c01ca18203601e844150030035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 83675594 1250 83674344 83674373
    0xf07060f080604050601020303010e04050c06041d090a0b060411070204020d090308010e0c0a05090415060806010207061b08070813270516030b01090807080c180403020a0605070903 79
    0x595042200c00645800c9000503400070401c1d64103001070f10301800044e40d284010b104259002c2d16520004003070003814010a81d143c40b00510380e0f1340d199502d03000c40c56100c2c482180280f2041508020501c1040c0c00a101400071340e01c0201c004c03c0c1e03600c40c0200f00081081a01d0720051610400100f001651035100170701c1644c4007100700060706509410000e201c118143c0124082c00f41c1d07042400280c00001c0e041c2c920221640c83e01036034401003400440d024251060052101c107c80d8440460321036000300002d840b880c02a821950780c1c41da40c0008403403181c031400d0000710b604a40c0f181803012820800041c10264001c0042030314002a003414030000c031b0701c9a03000ca2080080340300d0840308680c8003e103d4a071954001010f21a80c100324185819401030414582d060640e40c0101c02103d901441400c402448040282e46215aa0703500d02c1e5110002e0000c100d2040041d5142500e14540103107610340956015401450014503650340e00e401010003511000c01e02c04070780c00000004107a08080f044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 83676844 1250 83675594 83675597
    0x1b01051321050c10080402040903030902030604060f0e030406140304051212010303030501120209060904021306090203060907020304060c32010207140601120308040c0e090a031205040807030804050f0706 89
    0x580320070904169041402c01c0c920240b0800d580c0d004020a981e000c240160000d4040b5400507082c00700d460b00f0713401400d0b02c46000303401d03000c1c0c1300c2040140712903688a00685241c5403018444500072240a80e101c2c4501d009010100b00e01c5800e0b014104040c40145078002d1240e803c907103018190086000c11900000200b40340c20804000500805a240c0101c81c01080d07010f444420b03038503440d4009000c0e00001022a40030b40401d80004042d035980740049211a40009001c10410b40c1301e08800780658002c6808902400c1ca010209150030300c000100c070700700c2c2c0d10369949800c90b00300303030b40c8014400501e5803030003080d001d003c00381303c1d28680346100840001519000040c4e0307481d200c0c50414401105041000016044840101300300900f944003200700c10b0385071174240220f41d194506028401100d80048854607018000c203d001000094400c6103d406503d4490710840c0c406600703010707903030100c60003020080c06000c180c1c0002e0160442c180c06c0307440f850070f88280c1d40c5018661440e08805620000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 83678094 1250 83676844 83676899
    0x18040816120e0603010e040204020a091701240b0f03100b0a12050a1505151903050105030f0d0f030f02160b01090b040b1c03180806181b010513 63
    0xc00310354126240060451090b03d5050556141060205060314003c0000c0c1c002d680000d0180240343c0f18040b458080e0010160422842c8201c0421034020f0840202005803902c80c8050400090000c52440c3d04a80304a034800b4544403000055000c1ca410190803804000ba0030400071070401c0420b80030f40745c04d41d00d41c0e42c2d5252020b0a485500165200549546150b514050a4061100140ca0742c003081d1a4159000d44030412101119921403040014840c05841c201114000d145e6054200d00e040b500202d0480d1112000001d069490722018181040414060352841c0f110714065004008440c036003100c01414076078034402801d0110308600f41103551017aa50700500604403103100c2c030151044280d4003080714080b100003003900d10340140440c415102000c810242090310803d4044482c6c00c10300321038003096a85046041c3e075040c090b900c1d03000000309401c0f00d070303241030000440d008490400c034006891004520b006461941c07241c200002149070b40da9012503d54048440315140b100380d0001d21 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 83679344 1250 83678094 83678123
    0xc0306040c020f0a06090309170c01080601180f05091605030a0c0c0803090705010807050c0703020f0a0803040f090f0c0e010f050d0e101d120306130606050705060108070518040816 79
    0x200300415980142a410b209c030500c44070b0460300003400101c441c41c203090120311a280c0a0050300d40300881a40c00010b040c500d00081144ca4200c00c0f00400c40c1c0c425185100a038483d03800074024800c09842c3c070740001c0c0341800042e50441d075613006203d840781135090200d42c3d6207040d1928980c69204035030211482d40646c10070016540d004210030760103d51858001d04080b1440012034440640c2c1c031020707100350030300c0b030f07064200e655405404402007800904030703030342c56642d8040c001c1b14040e984101e40b522490314682000c4500140202c40600d01640c0d41c3e01001c4841d6401501c68194204020b400c01c8010706c4180f850810310702c40c581501203540001d1841503a40381c18074040e90201002c511001120910a0030104030020f001d05504e5000c40107141ca07691040045055403107007074034098440d4102080020350540243c001c000c001c1c05001601c0190782c0b80c407d02d6540c1c0042d84542070b000a120f81008501703042000b130468000d845840150710f084090461180d0b000389004064491000e0520170 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 83680594 1250 83679344 83679347
    0x2040218030d0503091b03120712030b0105090609060d0b03010e010b0f040c050319090501020a051804060305030919080a050c0108090111090d0203030702280b030c0306040c020f0a060903 82
    0x42e030710b00300b01031420628529002c4012500c0d039251402401c10301071a8100c00d012550240401d4004904110207540c9031056414500440daa42517015000700e0318218104000d5407043d81120081d43c405014185061042c00a02055a01c9502c8070141b05680f50140c403015070b001c0c042c030483c1403061400440c01600120810a1001c089000584210316010304060042c2e007042c140c99003c0d5401c02810089846140042c010f0030050344020b189500c0082c02c0c500840d082005044040400000c1d42e180000710800c1c003088a29500003d49654400d0000320f01a1901400402c600c9a40d10300641213540d5542500d880c04040038011101c0360040c1c8240041960f112a03410350080720a00203012100c4d18820a003228030aa450041c020031600c00f820080d92000c0041f05c54080d4080c00c2d1035014003014002d80601c002003100d1842d02035920340002900780e9540162406110050815882c6403030b4035040000a01401c11180e00f0350007004e007000c2484d2020b2000a00316809000c0210310b80006250 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 83681844 1250 83680594 83680603
    0x2030114040510031403040305010603030207090608150a020a0e12030d0c0801030f0f21030606020c010e0105040b03090708060c070515090d0309060b0409060b09070309020d0605060109030204021803 87
    0x2103a50081d49400100000301102d910032508807604004e03030602010783d0210707490135881a601301030319641c2068400030415a00141c2c150480c0d0401c5800c01295031100021038846000d080d642c04181c2100d000700f8580c2c52180d00508a40003d030402c0d46100c03009401007a08540b0007400711380550408506413030042c1c4580100400001c203440d11002070360566171128280703204d015019000d000740c0f076014400c025200c1240032007162504a0051103081038140180608158080d4070014001c00040f242c65502401d500c407160b40d4143c44503400c090a140028415406c01403000c115882080e00c0050040e106000460003607801d0100107568400ca41880e9103803220303250a000040351803030108040d044011a9000caa200b10b807802051480d0581000e80c0a0041610b00550003440c01e1581d41c1088080c1c0e02c0481c4011003526885220340c0c420b8016011a240664080d422550524004000074440d41c0310baa481841418505151034494012508a80204001481c41c4c00f07c41c07914803a5240422 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 83683094 1250 83681844 83681879
    0x50708010302061c0f1d120c190602040527011a070311010912020a21021905070902040303050d0b1002030f091503100f2408070c06090501020301 64
    0x10005000d51469000c00d00038840d030701040c201000d0008150b4110502600703d64400074064406103c0300d5000300754401d0644140400301d220b480380c2c40303454140011820644030194000f4010b0003411907840e1800e03a8810802e002124040e07800c00001c00d2558a0041c12614601d2201141700d0048490749110384146044c2c0041880745104481d003406810301c0030807100d880d5031500e0044518010058000e01400110400910081c0410880e11078241d0002c1e000044074056030b6803035030341d00020f50341e1051074202c605054010380100445241e18441040d40342d40042c4584121040385641c0d9012004036001500110700080c000540c19118501a014207018910f00300c411098441c0310b294013941e240300c2c070300c0c241d510b0030800b03c5c2d07010456450180c1207050a0488003000d50300c3c9400c82c1d5070003260b04a80075020000c040e070f58010034001030700303403070704202d5020240c1d188959082204c0550f8000401081c0c0c42c108400a140e0000150050040c0540c080c81400003603102c1d41442c0c20815a01c0311031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 83684344 1250 83683094 83683097
    0x1505040305060109240b0919030f020f010909050708060112020a171503060103062a050324060a0903140a02130203070917060f0114061801030b1005030103060507 71
    0x14001400401d40100340d03181140c90701c00000842c441024107896102d01c01080c1003105140703001c2c0010744c80181000400d041c42080b02c40301c40c0c2c43c00b4003035001d40b0114a400082d100e40d003184600c800608210290250300f40c01410220807246d0349001d43c40a0b10320484801c00054a403e05100c21540c0180c00c07508079544c1903000b0f50501004d450b00a0080070300c410419031181c5002d000c2508a103101e21181500b00c405000e8901960f120b0601c00c1c01360030306049032140820308541d54502011003103100041a081551543c1c078688034942d806c2d2028541c416520f42d08240c210100d50566a490010541047d69448201200e071450410f60b01d1506c0c20501011950001d54503880141da40d100710300300a1061181c010b880b0b4861620450745a0b40703c3d0440c4914a2000005103074105001440a03c00c84c44000310001c0d0ba80c0b44c422016001c01603010303a5070811410711911050b0f040350401c1a20041040c900003900040319000a2190082c0d1800600401c40020041c002d10540b409080e6120794507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 83685594 1250 83684344 83684347
    0xf0c0a0b0a081302060f0a0513050405010609060c0303020d090b040303060603060602070303050c0c09040305040905100308030601051e040f17030c070e2a1c0506100c030e0603101505 80
    0x40002411a0b40002c0c0b840c016208203261881c219559a000c0c0d5a80066000f8580c1d100c011640300544150701c030000a1144042941000034245400d0080034180c1c1c01307603902d40c0c2074030389412001e865100101c1d104405254013400106900d4205200b0300614600405810403141400c0c10050308444d00c9811603410542007071030070300100383c00041034411070b603140c5045591101d80180103800c06c140344090781c0c0e02c00504005c2c4424141c0c4840500181c0300110020072050311900f888044085051000419424090001500030340c0500040c00e20481c0304490500c6151080c08181c80c507902a80284461004030142840880019400120010315205c000c520f062403030050030751307a0000c42c810320850b011303c42d00050030130ba00c0304803000c1e03500c02403a2100022028800c070001203800c014140410f243e0040e004640140ca6409030901800f0064122404060700710011180f03011242d4043d005c0c404000080d15658980e080118814000120004062030400c0d070004544020030902c03008000c2c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 83686844 1250 83685594 83685607
    0x70f06050c0304020906041b0c15050108210309070608060d02120d030c1106040803090f060702010f050702210901020a050303041104060605030c19090503190b0703020f0403020d140f0c0a0b 83
    0x10104480010050380327007040c4070000014030f001e103140100c03201c00f10f214505210001405800015070036030404401c0e070f000c01c2e50385050f850600071400221040e40c050752003081c04000d42400b4600345e076004480038080d04021301090f0041810518840c5070041d6581c0328a82c00e11800b5410700c07603000010701600c3c02008004002c100d035980c030440030b800a0300207203000010070900301041107000c5002e003503842a03841034a824a8003900078044060008006410301c40081c5001b4404180d46030340040c120a41080d40c89d00100054541c0c104100c003d05501c2207a02c44000700c0d07400c0000e1340c4280d1041c0900350030402d000707080c0026143c1e680d0290040c05030500a021030f1040d83c005484000c8441c8405180c46907402c07000f110107409652045425008808007140200c2007a2000b920081c05446520041c1e00c551004400700d210700088081d031000c05000900040c640790011005050003403210242c0d0b00000c50209080030145201e000083e03220607125109400e0038403111009202c0710448504090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 83688094 1250 83686844 83686871
    0x1107060c0206030c07050a0b16030209010c030c020a0b1308010c1e08041a0a0203040b150604050405040602071407170606090703151a0a020601050d080708070f06050c030402090604 79
    0x30440c1000070301c00c410110000d1001d941200c140ca40c0181c1003011194142800e051030701e00d0341010380b09180100d10458114049500038001c480720305d0010b964010514070152021a0300b5101080201da102001d444005000680c540c060f001001034050800b888910f0164030301c0c01c68464281d82014884c2d8041d204e0f0101c00741e001000d96003151400e000080703640b94503108042547c1a100c182540100c4418400c0400c019030166100c2d6128045501d0307141c840c1d6085071f07140d45115900c0c0e648200204400d1105082c60b400c00c0340c000d449954054203100d03156132001240c501d2145804095031010b078007088240042c4a0880380c00c2083c0d0041c0141c1d040050210780507202c01400070041c0b6448030222000c2c001040c44202c01400c40398002c099101c41268103802a40c8080b10602c018402e802c00490a4a85103901e005440d0f4400f1a1929000b0b940e03552507103035001b00340d058842e03a1200300040f001c14410700440b0310845414940c02d640e40752910400540781e40182245006500d401800c1403c0b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 83689344 1250 83688094 83688107
    0x30601030c17120a050c06060a030c06211802131a12100c030b01111504120c06060602010209040f090b1b070219060801050303180405102103110706 65
    0x1039070b640c070300080c42651410140d450501030004860310804005288405154010b003d4440041880281c0712191101000c200d54403219000181400b0f40e021b000b000158050110161207a00100429003172010b410440d10446540c020141c052015140c0d0540452421a040703403010350240c1070420640d2000110020072002c0158000d008403040001084080e00802200d42080c0c49040107200040300e030b2400501403d0f0a0784a240403480010922124240c0403600c5011074545602090f52a03072141c0701e551002d0041030701403042c0560b0392400d2010520030f000302c901504054002694a0803480140004c980c3c542d50400002443c00c0039000014228a0034160003001090f01c11414020510001c41c0c1441100700003540a8a40804c2c00b00c4104070304800c03800c0f0f50702500c40484aa9884040c1a160f208001428185840c035266001c4c044c45c00e40d0205420481824141075515210040300110441d01a00070343e14840030b110190405071b200380f100326102d40c51400b4010300c600e8002c014104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 83690594 1250 83689344 83689349
    0x8070f09050c0c100c0c02190e0709050112020711030f011a0f030a020d0303020405060d0509010e034611010518030726030403120c0c0317181e0705030601030c 70
    0x2c549480340c5c02e8215116030394180c501074000300728042000c7c0045400034030500d24402d80800b003000c000022200c078000c0c041e0b14121401a15050002d2407103040d001d0095100b070004441140104c0d8a0250640b410080650042c1c108000060075013507648075128170141084d00180729801b5480d0501c802e480104030508200c1d4166180e11141d038891a00b500640915003106400000c08a4070280c890000d80002d0b0185c01355400810030018074418882d2030f849500c0900402c0300d01e0500c030500d03003070742c0400d095000059102c01d140082895010a012811074509801c0000c0e0710003001020300b4000e2045030f0b040003074064a803010760100c03040c95440f40103c801c064121081011500401c2c45110b40042c0316514840721556a8502480e004e420038410a054140581c9070a41c0e100415008207040707100a50507842d4440c10301c0b00035011a2451200a100040c0c070301003e150860f1079041045038421110520061411030325901511505d003078020351200d807003a03100c1030042002c070b000898a1000e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 83691844 1250 83690594 83690623
    0x40b1003030c060f0f0e03090901081204170c0306040f12080601090b0a0201020403020607050102120c07110603040201200c2d090402010513030b0117010e06180708070f09050c0c 78
    0x80010225040c40002c16642d030029881724105220b20002c0e120110040c195800300301d480110f0799032075498030703a59625984c41ca1000301004001c00e01855900c1d114500721025504100c50389206110086803c0c43d4059800b00c5540c000c4070030420800802008812030042180b50101603071034481c1c0000d10000c4c603442002c500500025605441034802c1d0110b501854014001c1c99036100a842c209000354071000744000308554290210360703010550b80856442541200b20341b04045060420400180c0c001b9008034103102c0080b91602c0d254003401c24400c10b120b03c52014121110b0b6035028009000340a90362404003c0720603000e00078409203842d00d01c040c0703003060350300310883c1e69588010b845c5442004200100c604052600004000c028400203059690f81c40c4d05426458150703417500d00343c507407801030328820740c01c400c4c0000c81010340002a8801c0b01510001c42c7c000d0395580ba1400e050201541203614040303141d032030034800c180c844c0c02250b030449041042c5900e0150440782d45610340850450402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 83693094 1250 83691844 83691851
    0x10507081f0305070b0301060305010b030106020a0201050d1404110102070b0703080a1109030a06020408071202060304061a040e0303010302090603151513050c0706150501090302090408040e040308040b1003030c06 93
    0x2011001c412084001959101c0b044031509521443c859145401c00d2040c60b00090401c400841c0400044e41580c0c12030328103400501c90325150b5801950140c00150050050a0b5980d511020241011750100d000754003801c00e0510310800b42d40028140040b03034220b03202c078010420824001a0380110800e5010b82010000198400308000441c030b04c4c8150a0000e03410311078040c14200780103482d1300902c1254450412a880b00769194000c01c03a0f80040180654019418000a80403c4080d0801c0c11421000c801c00a040074552000504841e030b5642a201280d00100040c021402c2c5040c200d0340014007100100b0414400c00c1011200b511300030700346181600c840d28000840c1c4c89000340100442c0c0240800c0c4000d10301045280451340100c102a11642c0c14404015440c0102c000503c06460040e582c0c0c040d003905580034082c002c076002d001160503504c1003000181c0c0c600701c02c2d01c090089100b030351031b030401c0c2c141400e10201c040c0e0003400714040d035050740900b040000d030051000620796070b01c0480803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 83694344 1250 83693094 83693131
    0x30e1b22060905040c090b180c090f060c070303030f0203010f0501260a1a0909060112021c030c15110d0b04020c01092105091011030c2d01050708 64
    0x2400341015a01800b01e45080005000803c03801e20700200030381e151040704121054000f0104015008060144804000501c0100701103160480c010048000003400900c00301c61850082812503100f56130318203071500700c2103081c000c0641c0350080500e8440606000e609550400c810003482410903c1594103001c9a040381302e200d44e40d44ca0621204d00001c110390ba58503e441c09011003d85015513101520344280c031b86d544010300d413401503d07018a548800801d0305a017040c0d131991055420b040c1c01da0380003d4410340d0040c500d00c03c061179001c65120342d80ea40141101441d051a2109402040202d960b090214002c4040326140503610841103000012071149107940104000344a0300c0260910395081110100500410b804014444401518104903550407460107c03401d00420102a034001c038010510740000e84039060a103014a54402642d181c501c04d074119611344140710301c660808214003418020080c44114030710301d122100703800034442c40c900040010400c502c0100000103450004124 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 83695594 1250 83694344 83694409
    0x140f0d05130b01140a050301090b0f0702120301090c09060914040906090506090a1203090203120f0f03010e101d04030804050705040c0309061b020703080a050904050403030e1b 77
    0x400981c1da002000c120007542c4400741c0c0d100002da0001c1d0140101c080420000d681e050501c20800d00130f03000116800c00380c0312064003107150100500708000310f21510b0b0362600d5116401d80114001c104e500c00018100c4910b000150840e10720f907010505100070704004000e83ca20086110f42e014000700c4000a480c51306150050040002500c041c2851244404000d59001c000900901c010301034aa0078142c0003110804400b951040c000080d055040760709419500f411040103003210144070308109041c80340c0c40807514040d4000f41d01c4046e0a801000c1800b500100d50741010001d0961342d440e04000103030018184247c40800350004080220700000502848400d0140c0030117403a00400604c030070354000703034001c002d4026120309443d040c0c5004c003592545000000e440030000c210350050a640d0703140d41c460004d16089a000c000c140901004601e02941c0c031445402d00c02e900c6a100018010b40741480c241c80c10f0805501c807403240e071007600509000d96510004400340c000c0d50f2000001ca159951a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 83696844 1250 83695594 83695621
    0xa050703030f110c0a020108060f1005030c0c06071701060305160e03012406080c12060904060228030e010b0a090c02010b0402040608190204150503060d050d030c140f0d05 75
    0x680000c11a408103030444d00c9800410280c0307845000340c2e1420450f8903420300b0400c03542000768816a100f14065108043e06003d080550ba2045401c3c01031402d081d900503030a41041c408071981d50028140055808414083e4802107014281c103240c10002460000e414108080030101200e007880400344800586581c03d400440c12519484068100080300a4184600090070b001d1940070a100100180300203c00e40280c8260808440d20011a038541a0600550081c080d005841040e000c020a600c0300c001202541c03901d46020252004011055600404036404242854001d9044c1500c0b0f110590782ca140c0101542d07004c2000042449003104168018408104c00303030b41050010400003126500042d010384100041c2070a440042c60294071001244168024946007840343ca884448040c4034002441c5e02c404003070440300c5200a107866280c0303032090b10800600026180c2500409107035010440c901c0644181c00158108481c42841d120940600c20740440c54541d030301c0c0002c0c0e0075501c0302e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 83698094 1250 83696844 83696861
    0x60518010e03130506090609061c14040210050a020a0206090301140c071202060403080a0b0d0501021207030b040b090a2f040302010e0105030118051009020f1e0a050703030f 76
    0x10003000342100014201c2d84030342083c0424507242404540c0083c090410394200e6102d0103004200520b0680c06004000b0950008602410020140c40d000030b5814440e21a10b18070340748100802c4036030710f0306204021101450500507003c12400348480200c5540000e03c1c004802d42c1280c8181d1501a01e5020900402821205550403000c81c030910410005140040c01c2a6008141da0702c030300d4414540603686c0700410ba9000740040c040d040058240405584040c014000040038590252040d031141c43c2a44c0003421584844d8071083c06000079140c040c46074202498081e24244002844d1070700007151958020700300c5031001d440345202c1120400c40d242d4030381a0303801008401e41c1c4031080c960150440d04980812404a16110080c000a600820540c0d04880c0d20704000070351071000d071003040003030303e00684901048030104001140390542c1d40045d03c400f019600941e916440d450242856140d60401a001200800c00581c03a100b50305c2000c03501d00c1c98240c1070125071031090003000001060b028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 83699344 1250 83698094 83698141
    0x80403050c10061802030903030c0705030403120e0111011b0831030206222406171002040812030709030203070e0106081026150901141b070605 63
    0x2c046800342c42045501c804240c81e52107a102d0014030b16024604224441600c42e000682e0040c80010a0800e07101c2c000c1caa428400d20969082ca503903581c566400710784165405002c0394401c00e200d011540d014000075440102c030740003404038240a40003620040002081c000420840400107059071080903081c801d801103000c4212404021a0080084c41900c480128014018440801d480500120040e1101c44002044407510106640c41c0640e41481d0403491070054011259041442c955101e0100202072103501d140000240c8a42181030440c43c0f41c0c0c0d11025841400140504840010400350301c03250325490943d0703504c0e44041510304003060b41c0029810300c580307480402d0240e2078504641c101c03250703900d4506141d00d0702c0c0c0e00035090103c0ca000e003458074400c04141d0070a2454100c5250714003001c0e5000e540240f10301c280380180c0c42c00d0071070b034224250f9101c1030360550b520502100d480d40590184519001280058400660740c4569100900744940701c03400310f48424907541506d01a10310341c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 83700594 1250 83699344 83699353
    0x20604080d05120a050106080c030402190906050f12030d051008010c1d030a02010e061305091302010801060c03090b071109130201030b0a06051209010e0f0106260c01080403050c 78
    0x21540010441d0f44407070103ca9240400c030020900480550240ba4142d82168950b0703010755035201300c00c0c1c1803904002d2040c1d030700100054480c0c0d4102400e0084502418074604040b4006091506100002c403110103494010074540380c240c110700701d010064039042445620040340030707260340c50209500c90550304010015417904a484206a030080d15209000318120140b01e5046030540c100742c0c440303070420000b9021546c4840400e500349894401400100e0030002100800d688440201d2041d4008540d000f000342000c4103107034250760300315220500512440c036100d03e007410b0070398004051551510404890610104001d000c110002901405411000e020301c619490310b00706041031411030810a82c0400e15080d1000400c0c00d2040d006010342d191600c03014a00341620700b03003200e6120300918032041c0c0d5507139100b05802100b0034440388d00d4003806240046142403c00c0c03446100103002104040c0100748410000c1d9540c039011580c0b20a07040f003400c0051311035446007410f440510592041c6900d6019 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 83701844 1250 83700594 83700613
    0x705100903021003021c020c0309040504031107080604200102031c090611030604050a0b1005070c0803070b0a06290702032805010605030a051e071805010603050604140109020702060408 81
    0x81c503070302518030750142c03c1002084507111b1328844101d2003403c214036035580007084420f50605083e0041c2e5000380c4a80b4007031110368112144a03007092140d400c191455000901800103028600c0c0d120810000848030310f2003a6400800042e50383e00c110602c04a1b40303000102242160790072a400605815008001404003401943c8105c44982c400c843c114401d0b442c01000c940320790030b1441030748054040504100b02c2005038143c180d0ba140c02407041183c0700b54040c50041540d00b41031028000c81c7d48140103a010318200194070409036107003908500000c000d020b94050300741c075640c10030384c0d843c0104440c1c0701d83e51000c90000c40c0c00e191004218441e80c03d00360440e050a000b1400c00b002415000e00000c0052a88a03001c15844104518020b0240d500500d00e40500c00c10310030300810321413001c0302101e980550390341c0f0041c025000710040d41320712950341c401044019014000c290780b188007243c04100118425011441c00c18040c081c0c1d40009501040380002c6440b8001290040d00840741141c42c00803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 83703094 1250 83701844 83701847
    0x602041a04050414040b0a15030c080a0201120c02120c0c0406030809120c0a0e070504030605040b01061704050d030b0409061d01230408090402160507060906020f07051009030210 78
    0x14400d10626000e40d180020302041c04204d600700e20300956000240c0c592644800103184090f000e401c04820340d0b401c0c1010000002104094848000c05a02010744101a1940000740c015040707400f0221403541440c072036000c1d107980407405003079521521750484d854045187e040f41c0342480c030040903a0000c0c50040301205104410300580703d07641084442107025986150350a48425041c1c031107a030040c252003800e2094907540c50b4055030004803440d006081503580c0d1101000c0e80c5043d0f0703050b5a02448100140011707540b140c0314010b102d82c886241d021790f00b0300b5a11145c2c1c0741400d0301c3c01801c241e6244403450080c1d1311a0040f041c0d65170402014000c05510489185a003041c1d61602c42481d071816070007032039440c452808444103031148441e030320b803564594a920010381d00c1002000e60095082000340c481c0c441c40a0500d0f0351501a0700144815820120f0203800811a6049101954841c510052600d040010840c00b65081030318102140780c07041701d041c1d400d0f6083d5000291301c2180c0020b13110815 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 83704344 1250 83703094 83703097
    0x5041e030c0b091e01030e0601061701090b090f0603070503030c01050906010e04020a03030309081314040c050c03070321021c05070918090f020a0b091203130302010c0602041a 77
    0x59024210031241d640c0e45980000c21840354080503a0800202d0803959000c04181400e00d070b040314181408554181c6400010381883e100340c0155010a550303140c034000c0f502484807190701409100300b0030407614101800003095800003c0c02e88481000e400c0c00110261828441a0f006000103000c803501d4003601200345000c0c0c14111a190300d180700b00c1c0000520740d0003400ca043e000f26005006030070740c541140c13011800742085080548040350100004181c2c0003031450214020403402c440c40c210b891300381d0104408d45000d5032082080201c180101051010040200e504080c1e05080c071030703610360845d0300b03019815104440c1d1844a5102282418600f51060704950301c040c1d18120420150380d4499040d5000445401485460122901001640c0216134007410b40b40d405551060096142c80e0300248000c140c6070844001a14049003071035142c24085040003103800300d24061030401d080d11055080c026040d11020741000950170302841403268030b0b4100d0700980340071000311101480040403542035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 83705594 1250 83704344 83704349
    0x12050a1508030c151005190f09020901030509060402010e0402091c0807051507080106031a10050c070902070f02010c03050f0c01060e0601020616210e07291905041e 72
    0x500130305804500301105807200034412401155403422450905041c132002c0900c031446419840100c01011400c0800c0541c2d20005000c00c0c0b60150762806a0701c001416510f0103030100409501c681c1c01d02c40142e8010003900f815110540e00140c81e82e00540010301009110000e001c20300030300140070402e219514000b842500e0041c800c80b240603000c0348040e41c200e01c0c1141c030078002941410051000724401d8005d13403607500c8040c28082c1d0703000c01240001c0c1b008220588400105900003102c4034201c00c2800380c80020400c11404508042d2540c41e002403a41d0030200090412420320f4207130781014051411b4541c040107400b910390312007481c10318060003001c03940a640b0003c541c10340002e8482d880003601078820701400b41c0c0486c0740b041c03140c8155a80024141c0300c42101c4160036800020b41c1007885414800d020b80c600414070f1078a8402202c00c89000c60a803c0c0d0041e120001e080f00350301c1940c0c04c6509800882c48035004a00b040c000458150185810000f81c04400c0c2c28440741e0311112074a40c400303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 83706844 1250 83705594 83705617
    0x6040c0c0b101a0304171305180a0506060a0e040e0a0f1101020c09070f0305191e0b01020f030a1b0602030108030306011706030c010516051f0c03060612050a150803 72
    0x3d80c012145040820703400100c500508890300d41c029401c44109200280110b1901400203c00c2c80e51108000340e615860900100c00d42c01307050342082600d4190b8001e080c1c0000040d641545405c1c003100b0000c000c012201c1d00d0b58013440d00c0d80824540114104800d0054a0f0010002a007400c0d4902d030989020a40301c9107035005104000f01c0c1e10041c60400f1003180101080c1c0c855440b034600201c419409400d00070540c1c070045c290003009459000680c02100307100044400031401001c600980e840403500510405411548002d0100c081c00400104440c421000c0342803600d100b806000001d682c400146800608440c0084000901c8401c000701039805000c00f40c80300001400c007a50050b45002e000c41c0c100e6450341c0720351100401c2c1d502683c028140d0300502954104016629158107103020706503240b4080d4074482010705d001d805000c0c0720300855a1410b15003844607514016006221b00d000703150076000b05503101e0200785000a680e200b40f094400b1520200055591049210307140d410401da070b0742 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 83708094 1250 83706844 83706869
    0x200723010806060d1d120702120a0206071b051e03101401150c08040806010314010528090203150105040b0402031902030408040f14120d0806040c0c0b10 67
    0x552941c01249078034401c1030081c0c01c450400205030740d00c00c060848044007610b21041082c400d8420401030201c14280e084007001295120200d00c140300c01000c6200c40000f058000c5014035005949030811540031a0300306440c02042144101100c00200303140c0e20995103d204211501c045c014042c00c0005c290b0000c40035915075405006071304050b42d66004908020848020042c03095078031484400d001c2d43c0b51703491704202110559444a5840d0310a8101c030040d548030200400402890130950083c1e01c040307200911a504013000c40c00400b98840c02140110509000803076110841503100c0400c13550002c044540d008004845402c15a4081c0541802141850810080c0d03080500840c0c1c080c1c080c52046000c0aa070220800c03000703402c00b400c101d510396010840060001c05541808001e0100e400003103580d07045da04104070101c0c5101c41c106007950010030082e880395400240d42c0760300c4181134071f001c9040c0703549402c210740e025888800203003059646000d0044842d090074603036050310100b0399040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 83709344 1250 83708094 83708159
    0xc06070201021c090906050d12050a210b040c05250311060a050a05090705030a0807080906030a0605030114070813080d0608030c070f030b070c1a010801090b16050a2007 74
    0x3030003441101002c1c10103060303009c9a6030740c03c0c400c00003414000c2107480c201008403548000301ea240142c00d0144d41b05541c41e001030b813015117018413a03100c9998443c2051072800500721342600e044000307801c8a07c104808840d2807020715018265034281018140b095900718580740c10020000e000555100c0500c0d464800002ca203810001181c009407507005004113100c2c1c4050359640140d034080d18040f114140140022175054940304c000c2d5000c0e241884010034402d040405050841c0c048040c90030f02d044854040c0240e00750000e000035081000e4224a9803802c082e410189414414002400511440c0000c00580a8004005003204008203019908003da40f0031224180c035000d070001030991203a00011032001800f0340b0550400c603100345140d451600080710f040400303031404d034810701d42a51106130800402841c88105a4050781c44a00400380c00c08841c0000d00c5130040c2034141050040c0703400820082c1c144841d40108241150003100c21072515210704004801142000960701d03414940701 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 83710594 1250 83709344 83709349
    0x30c2b0c0504050310050a0f0c0c03020114060609040c02010b0a06170606030403080609040c03050a060204051201060e0c0c0106120f0302160b25050a030e031006080c06070201021c09090605 83
    0x7260110f60b8014000c100c2d181d188900300000706009484981580da407442c005025400340c2c05030440c0543c2588810034008003d00340a4252002c4041c014854003541c001c200701e90765048140c845911050b1000140258804420b0703005100304c0408035031050500000141c40d035845800100700c492804100c000326200c61040c0901c1d400b00b07886c010701241040c0f00148582c207085899079403080c01858010f00c45980ca448a40c00d201542c1d03811f580d40d81c0c00240c01c3c0442c1c1804000442c010400030005c216041c0b4101c0040c400d010094400d071384040b00080c1d45140c26100b500240068103880702c48145410b07103890300d401da1203000a41200540900391003d4103000d410310360202280d4a01101d50302d014408111842c03071420f100c021901d0680c84400007000700b0790402510380d07618131903211781040421303482c10546855000302c2c10788101400d00c101446210404182c141f0814000e88825031621050310040c1d041400ca8202d0f4071840402207020b0b81500e0b404104102201c02c00d03901004116190000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 83711844 1250 83710594 83710597
    0x204050a0909080702010c020303070b090304090b0612070e010c050f060f060105030f160302070b1602100b0312091203160c090509150901111303050607020d14030c2b0c05 75
    0x2c0c06407440b44180018030255026203c250b016603c0241660310381485075890a0342103205a0301158241d00100f41030091484911070300324404401c4403000c3c28094074080700035031181c0060440c410030820700e04032411b99010b400c900610301e0b03011003905c40c0d01e03041e262007030350b6807030215161f00505200d42c000c03450340d5014000720b900581402c2d20202461303841d400c064031406244200b85e800c25a0070406880401c0384540d4850040100d070425034110281c1d60f00003442d0407400002c0f48003840c03512a4120740703590700040120900004a00d0070341c03100060400200c0b42004c2041515040c000001d9250300225003041c514031342e5219400f0121950340310f125500880c2c1c01150748598036840100e0700000480f8100000780d101c0800c000204502c001500d41007840c1c0c00c0449201860140c5ca0401e0081100c113210b9940d100010348020711007010023840c0100141c03c0004516595000080490403e075440002c60b0000c404407022074025040d040f4070715400c00c04642d20340881da03183c070b0080c4110340d10400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 83713094 1250 83711844 83711861
    0xa210e070b090609060a0305040b0a0608070504150801060b04090e060c04030f14011803021209060418020c0102031014010903020609040c09030c03030f0207090b0d0b070201140103060204050a09 85
    0x20040103458148031210590b0ba1050070019408103040c8044482070f035031030000701662601582c01040c10704262a141c00c0b40b1201400d0f028403d410712400b40000840040c0c1d40703049510841c0c000c01c00c10400c07030a90000d01101d8000780038135400c3c03030381c08a500750170180240101e4940c600d04004404441803061f4940300c0a4480131040f0004210400124128008444030356005021909500301c0d61500d450840d01061070080040074000144003c2c035805228580020400300d50b050b16101800002901500c1280100c800c03c4185803900c080c0140c0c180c0c181d07003011800400842d40c0341003a80b6020251100b600c10300c010b40017883c5a2141e030354440c1c1100e5003104e031701171b1010341032401001c2000054403460100104000055030000082400e14900000440c06030b11607221101c00c1100083c10070920b900a18211410020301221645400c50008049600071800c04c89a480350034049015100d00e540c0c1c2c400d82c0203000c0003c0b05104155000b00125841115405032443e1388416170400d40b22080d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 83714344 1250 83713094 83713121
    0x3080619060f030b0609030a03020d17060f010c0f05011a0f060901080c09030c06070f05010615091208040e04050d030e19080304050a150c0e010c020d1202010e01020a21 74
    0x40c0c8000c041e140260481c020700d03900180906d04000b103401c0030030b02c1e0080045040c0c0c01640f00b44902c0d1030258001502e00c1d5210201d0f80d1000d002d03d04039022501e030720b801501444c108100d11102e01e040c4407050352002240c1d6403102c002c0c010550700c10401e00404502542c1a403254543d400802c180b8a81602160740c90346040c0c413481d4183e03540c00320710292a0062181c4c6a05401740149040c00d41e51100003d040892168040c03102e02400307810f005007100c4050300102d1a0b440d41d40c082d11071054001056a0846840c8043c0b02d1202280c2d00d400c01187c00381d903004014040b4044144010000d0114000741d2044665500300002019590200e41c3e0300c082e041a80186000f4071840400301350300000565126025030212503000c1420741d1001d0790507800c0f46404516550341c0103184201d0783d01014011164dc400d103001c2c105031540e41c00080c203465a10800502010300d00c9070128030340e0700079009038002c06a050300842d1650f11503d000340210080000c1c882d01c0e0329a5214860115800d441000c10b102304d007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 83715594 1250 83714344 83714357
    0x6060a0f030e0c040204031b08030309071703070c06081f0b0403030e27010806010603061d04030c15020a090b0408150a09150605030105060409050d031a04090308061906 74
    0x2500400d500070441102e070880203000301120403ca035200ca00041c0003d41c0b0840201000c603d24040d0358065100f00d4100728a140c108100307000c05803a000482c4026982c050541d40264202681103c0c594400d00c2001041e440f28000000749842d008501588554641e0b541d60a084882d4005c500c1002c10b40c0c0111401080280018070100384102d156111480c0e0280003100500000e104610306201c5003004044241c01d00c8006000340700080c84001e004008506042c0921400c01c0c002c500f0300d203c00c141c40d40004817000e001406040c4159614503455400c10389003a0b400c004224801702030360080c003030b43e030114115030b100003003000d0141704840031648280301030702c06100e0b4444003402d05040545181405a110445a0b01150404a040642c1c0449480014002d0701d058149420350720020281132144c0c1c600064000840c41c08201e12060540c18030300022031241c5642000d031541001c82c54160010f15043c4d4510070503421400e003601801c01241c3e0800c4c0c3c88885141c0c1e004490003070255900041b02c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 83716844 1250 83715594 83715617
    0x60d03090b09010207170319031404060506040b090f061c0b0105010c03050d05090d08070e211905030309160609030615050d0b01030c05010c02030303131e031706060a 73
    0x80d07100504000b8905106403100b0b00d41c0d496481c502e01e4403200007018650400114103c000c54071a090311004072540c10244111903034030501d019401402017000e0032550312000029100d40d220340c030840050354000d1071500e880c18000c401c241c6d015021600c6600440041b42c8198041c1003200d0f114920700e500884031442c036800c2c41d0044411443c8400100c09005090090070040f16460145920070010400144400b02405c5c01c018011440501244144400e9002580aa0f00e0301c400c80c09015034501c0400c082c80d81c0c032143d030320319007196034100b04040c4a40403001d03002c000c008002540201092001c541d2082e2285103002d01042d41445220085824402d0400c0022810b4024803041000020703241c00640d956400b15031444222081207800340f2070305005108000d681000c3d18050102032a1440550941b40d002c00ea42c1d10028104c2051415150490f00411080340c051202084015044410912281c40d0113006560000403c080214400d0000703003c83c1024001c2c0c0307425990950b1115803501 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 83718094 1250 83716844 83716859
    0xa050f0928060204030b0f040204061a1803070504090323030603190203150106020a0501050c1303080c0106030602040312030608010510090504050703020a0605090103050c0906040317091305040308060d0309 90
    0x401d403030440354a902480008040f401c1c21500c5032099039080c05074001443d25104002c100c810940290586c0b0f000c02c0f8421451214240c1600c100ca500528001104880040004d150041c20341c00683d00c035090034020401c140e0f00c20310401c01e07613010781c2c10814040e0b0b1405c0c445145000071626186c16511440310910900c1c0c90012480c511030014080d222428410340b400b01030307018243c1001d00964030690300c070002c1140c244116540b0204000c1030f54104119640c4807004072a09110141803c3c50124a00100d88800e41c03051006640c006003c5507603903500d149c00040c1121820311000800d14010380050703442010300032039205031a80350007241d801c0d0406400200a15014102b9100e40c400c068010005841e40040000900480e80703d560311188040b00040c240c60b8020106000075000f0f0108040589a607010b84090704e81c840052880c616020000300864025491075581c02601040364040035412944024002c9001744d82d507503c3d580d43e500c00e2204c0e9450072400240021240d040030030902 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 83719344 1250 83718094 83718163
    0x90603040c05091e060307151805040e010b01080f010b071202100f0501081e0303160c050a08040e01050108060f12010222080c0306010803040603110708030a050f09 72
    0x180c03003640c1e0019680e445501062105070100c0e40401050f0184c0c90451040c540180d405600520450041c5162810040d60721111030102000d88280b101070b0600340c20604041c01c130760001c4d00c40074204008154a03074040c5ca0103040180440c901160b02000407c0517140e44504041c10303210350003000c034170b030642d01c0d52a86101001c494a01c0c007103004e508403182158009025142c6010341c4400082215414081e00a040c00301c3d41e8030351001c02d0380040c085440d8107008400d80340d0040700410000c07000454010155046001c560006025025604004c000c002c440800341064410700d0040116a80e250401541c40710016134a03d540700968421090306454401540d142840484001500308200703408011418802e4000007003511521540a0015000820145c900c0c818102c1c014130380355140102650b01da01c80c40c0504810903445415201d0102010021200399641c4044074540d207141940c500070050505464003000c0f4208140071440d03030640021310745100c052041d0f641810079901412040c06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 83720594 1250 83719344 83719351
    0x11060103020f0a05060a030603060e010612060c02120c06100f05061801052703011a1c0f12080f070e0312030406140408120a0203040c0312110f010b01031404020105090603 75
    0x303c152840046181c0e190320002d8255050300780c80100e030321400e5103466401e4800c0000c1d034142c280c1c5024000c01c190b04c2c0310f80c6c155640541001001500d11030840d4102c0c2080405204803000748000190341d40040b4000510714441c811084401c1c1e00107403a07000f155040038035841100c1d0f00c0380003440141151010303c0c8101691503014180989411321426800c02060080142d900101080308441c2d40d07107090a0081900507504038001c018a40c2d01540010300600440509040c4140b6030343ea49400c004040f07114110303554102d10a072124a50315080102455001c884140800b4080400309909a0145280b4100024001e000d0710a441d1421000059900700800a0703510039240d0041580746140f220000e80124060014644d4400e828407034410ba003040908440942d80c410003c000c04501c4840664064990001c880741c60581c000101300d41e60140c4051a44280c0a20036411144441c158010f0064480a88050042c4a1079140000b0214412140a030200d41b081180b80e66515242004562 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 83721844 1250 83720594 83720599
    0x3051801141911100603020301110f03040803040501060e0c030103030e0a081b030102040f031a010b040e04021507020301060e0106021915050402030a080708040302091f0915050d08120711060103020f 87
    0x500500a0f440b078940041c0d61020b94a81c0c0e965881401581020b00401c15441e00e0014803a02d03115101401d13140314800240080d00e41080440800c00b044003e42003580100020005010142800b91070128150300030b21049001c80d04034001d80071207052542041d412240003801078101c2e084001c801c1c048801064250690655003003001241c1c603130320352008502650044038a4001d007030714484204104281a00700120420050000700310308a19000e090358003980c1515145140c0207100d610032214007896400a6040d42000801b0030744408080701a4101d48081d800c4030b001c04864188184841001c83c40689955500200910300d060580c00c0940c01c640b01038122003001d2190744803801c05401a038000c48445100140070401d52400440640d00b141000b48401c481c81d0f201e084410314200c9901c540341e10075490728501e40303101140f1404200202406480c1304800c0803103160070b501c590b0045020f2600f80d0129008140c095100383c111552030506170008002d00d908540070001c0c81e03c1820081503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 83723094 1250 83721844 83721857
    0x40f11030108010204080f060c09100c02060711040507030c08041b030f0b190b010c02040b01051902010e1009020901060e030a140a030908060c0901081b07030518011419 74
    0x4040115850045008000b6540010f0f02c0318101190181400709664221106512507010710070010710041c11600480001c441511426140a1040c0d518a02c0b0704000b80d030180011131074074140041d0502c48843c030b4104071800c0100e50344021007a07003100d50034508031000820140000d00011807503032089641d50000e070000c1c09600e54a50b00c0040039403802c4130480d44006900103200c0c0041c0f400703e1520303480180b40000e0003c0c01000000034010005500042e100b075441d01000c1090b079000b071040b80c0008a40320303891880b1486804029001e0032641414a410b485100035202c5841650300c10b80611513402040c1d04656460000112082010a1445035044c051070071290b000544140203401c036005198050603801890b0306000c1c1c5011001d5000d00820b401c00d60400c05540d060904580010400742442905034540f00301001c0c15003440019541c40d407000003250028590404068906800b5a22008401c10062401150200c07120761290800c0001800001c0380108071000d01c00d42c8032441c0c60100b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 83724344 1250 83723094 83723111
    0x1f09020a03020d080c1615082502010b0a0902091005031801020a0f020f070605030c0c0307050604031812030c030c0203010b030d080a060b090901030201350a050604140402040f 77
    0xc40c15544042c1c111440300d000280205c8205080c0281c0700002c0310f0707540340c01800b8a4501c10042c6503060b0343d410002c0015081c0003454101e10502c8a0b1207098110000900c6085400d001900130510070181910401d2440300001b200810b0380200e4031244e00281aa0b803d400003260180d07020741000c0c04070b40e55076103a603009a03422f4200b44007822089400d60340e040b00d0f11090400180c1414020405500281c1222406001a13a001002c8075000b50342c1040003a0740d010000761107425402101c2d001041809403200b84814180d116588114044514201c2d0803021b0380c03481d8050458514240060100b04182140b40200c0e010b64100d114260000c0d0000c1211000301e000a81081da03a4600d08010074900000d03c0b026484a00c00c2401800e101d0110302d28080c1a000021100030051000904010381402c131719000d4041801c2c008074404060049099841201c51000340c000d904890400c4900c0c940000291685014020105030064694621081d42c40765000d010141c0a00b60080f031541d0f4035114403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 83725594 1250 83724344 83724349
    0x120304080708070c05010306050111150705040b0c011d030c0c01080a060305010f06030b0601020a0320030f030c220303081504180308041104050f010e04031202040303020c03010c021f09020a0302 85
    0x40c6616031098814130b0440d42020009000c80c0c070f4a40103d810019859000e201c405400644081e0804043c00c4660444d541e03004100c40c08d10640d003000320007040c04141032590072415001000d00c0101120b031190202903618000c0e43d00e02410450340700c95031140c3d80da084154007445a140d042a003035500441c4203500c1762902c0782581c1c1c00084083c0100d954090070000c0c0710056200039009082480940b00441081d00d0003082c5d214001d11180c48082504100450b00c0d004004440018420034a1035440c1e18026400840c5500070301c8960340f0490709070203031070b0074144036164180c250b9516403141d1825851700c01038086c0d02d0114001103600a0394581c603114101d004441c0b41017207244250349120b194a041d180045494034422031081c0210701b400d040c0540c030f0b0801201181510101c246041d9540d9039828111414408281142809480003a002c4141540810342003100d40f4140d000388890b45901e1412a0740768004d0301ca69803034983c404032010000078180c01080806000500596013261070385c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 83726844 1250 83725594 83725597
    0x807051804060303020a0209070305100b0315100206040507080703120f02072312010216080a03091b06030e0f06060d0302030405030613120807020a020108041a0406020a0e090405120304080708 84
    0xf095025074010610401103140c0b103050b640c0c1c800342900e07049c03100f03003081c44444001e107800b0302544080f500007000081d01101c01445903001020000c18280328810b2102c03001e0f44400b41501e042d50350340102007000c9000e140020300d0100700c6e50300840c1000c10240d001d0381100e1400c0780410980460056074030018114002a0310421601c4030031040700c840001d0402041030208041040058903401400f00e51b043e0200c0b80302690506404c50102c070380c0c0e20070a0701c1c100d0052809c80001002d807101e104182002c440070400e044241c41294404005402d00072500366a5211f54065050711980803500150f6030b818903500c010700c031700c0c801d00440e0f0400381c0b1140000d00b880001c480841034403006000386020f00603207546c0c4009c2540340303003232514040c2020000292111000400071307050184030000b10b0108508111401901c501e565200c4c102c0d42043d10702180a50f0246800b400005c561070b802244a1501001d0039010310b80c030070020280092075044000300e54200a00940e02990144031190100d55280d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 83728094 1250 83726844 83726849
    0x10f050903010e06101a03010b0702210102120c0306030d0e0d06051305011508030a0819020304030305330405040305040e0108010f050a0b0d140f12190807080705180406 74
    0x4024200900c1c0c07000800101001710f9100130036042c0800d01500179001c101c03041302c0c1500c200c810340700e50b2800c0300c0c0081039032509441c0c000b03802c901c0108400e0314942d030190701610042c181381c4074080042c0c8601c810f001e9140030030380300c00750706030088074010400a01810210115110182176146a4071054850400f242c40859044550941c803800007400c00100781710b82a0710884183c0480c082c0340c20041e4255890089180410038050700318042612a000c1d000c1c0418003100099041d0340e05c4c9030034500100548015105a0780c0310600120b6003050101c82c401064480001c08071a0107445031802c10480504400b40051702400000c01020036140c104080e941c2c01782080b0f2001040c00c42d00d4840c484110307080140081e080900d040d5443c0201d503034500c038844034240c1028480c0306500318918410304058004403030513120f10030845500c0741d61425202812074111000d00c00c50790034008602c2541c40d00c808481c108001440880001c10307007405200a0320440581941c4c61480b030740070001040c01c90b030a83c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 83729344 1250 83728094 83728121
    0x60a0f0f0e0609070b0301030512030705090619030b0a080a06020f0c0d0804030908010b060f0702010e0303041701060e04030f0f0e03030a03020c06091c140708030c0901110d0905010f05090301 84
    0x10b80030007000660800544006020040c80c4a1440d890754680380d848012001411400080000204000603c10070540b0558000105015074604c5920a5203402400d040721690210341070800340401490015010021a10040d000e010b65a0955452000945c001a02c0d03c4644005000016010100f0000000b45007103540316000142490305001d0806005c580c825100d031f81c10f00d45040f0702e0340c40e16410340e5000d03807425402a8480015100680e2840040400e194061002081c00605610703600c490044c0c00710388a00801485482d000d04080c110004c031006404903d10940b03840010b4407540c00e001c0c08003458588120b07140590070020b03055520013842d440000380c020030502d044d01c00c148217180d0410b400400900300c0c44250910420381d007040c040b0740814044e2990602103a48000c9049440e0650b20205c0d05569280c03c2c9070594a0b50060014540000c07490f8000d101d50020004000b07011000a0325810441450301c401150a410300c0407030340c4200301040c00382d41c3d01910240181c50052a00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 83730594 1250 83729344 83729353
    0x602030906090a0201170601030e1506010f1404050910030c0909030f08040314030c090406030f06110a050904180609050a1e0b04080f04030507080d120509060a0f0f0e 73
    0x403030300080c601100501400c00da60844000030f00142e0300080c41204a800c506a03052041d40c442c0c0051b00241524080d9503098020071100607203400e14041d403184910000d0322380050b0148103d001b00d03034507046110348616880c410403040c046450010b03205a44103c482800c00c0006440e6074a420384d440196010310311103a02c800f00f43c4200f64000a031101643d143c0c0c07902c0340e031320701e000d44002780b503243d038101c20605464002012402d5080740e14101e90300301c00090424865103039030340346c5400c109540e00002e0391402d1415140e80980844241101d544c0300c15540c0c1ca0341481c0b00c040c100700c004c0400b080e03e0400001ca4400711000505540181c0d4502401a00680480d00032418041845802c0040102800c865000068005038001042c0b94126404c016200d446114200e1040021b1140e900040c12901c04c00b80d0010700071400045d006c0001507503540311801c107103d000007a4103444043d41c2c02c2e40c0c650813140c0040c5120000754031a00102c00521004a403041c4880c0e25042211218816101c060b00b0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 83731844 1250 83730594 83730601
    0x603020a05090f0604050405101802040e010203070504171c0c060b040204050d03080a1418010c0201020403021509151b061302011e02100f0506030d0906050901050a03090b0103060203 80
    0x40148403040101401d9503404914030701030243c8440e0303070401421648551340d40d2000c941030000402c0645942840381104005105444120b0381264019280c100c1c859070400070a1555044103000340c0340514625121541402c3c18542070758511030f81045410510f00c0780040885c01d103100200380b2030382c500301a11070320141c2c1c11508041080c0c900300140580507900400c03080016807134030036899040381d40520b00076180361180c00410015040118443d20070100340303414410070001020b0046400e0703242c1d000802c00700100e501d09a090303008500c4003a50200182441540340c0b60300b90024071b0300f50390007060940c80303000b42c40d00b141d07150300214000509110300e42201d040c00401045219004842501d0720030351400e4030340c0024610442d0449412858034111100c0a85a000304402000d072084107c0901c0030170080f449600040204584d120320920814414047da00d008100880580d25590744a61802280c80c00668041e48420340220815548280c110082100007407031320b001e548103d0300541c4d80d09 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 83733094 1250 83731844 83731849
    0x7080d0606110c040c120902030a02090a021201090b03120a17041b140d08070206040312020c01090e06090a0203090c0d08030103060c050408030d09021f030e060c0414090402150409060302 82
    0x840841c0704038002d178a0201d6903d14550801d41c4610041c0c03000d0303c00700342d80d0905d03c0407074141010f01200941001503802400b05a540c0d40c3c018044103107c40c641105140c0ea219051025200281c5103c2c0d0103800000441c00c006500d440204021485070502030604a8110526103000c03200300c0701560a52100e405180441e880750a12000400c501c010036a1844d54440c002100b04034440c0d0300904006001030200119101d5409030b50040d074020300c0410b40701a030900f001e900c031004495a0b80c0018081800460400e050b001680e00039607024180340800c0da1003511400081d840038040d60010f10850080807034030355a000c1d6075049a8400c002640d2294510300e40321044d600400c001c1c100b80030040c031082c401c0c504004243c07510a0030403203021840310203d00108031800c40000c03d441d402c5c0b102c2c00c0380301c0c1d045070160411212074141c6412103e1a9640c6072110149019601600703107a00080c00700040e4034036041d03005680090000701810581c0c41e0141c48260158407941c4011b1006444101c1081540b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 83734344 1250 83733094 83733103
    0x40b060301051509010902130b040f081501061b0302010b0d1b0807060c0b1b07060c0f110d0305090f0105010f0f080d050d05041401060b1803031201060507080d060611 73
    0x280c0107102a03d0f410040c00040d810703400500075540500c0d404200102100c5000089034001e060310b0401c5584d507915213407400d030349c00c4e868040c503070f1103110b1020300840146400c001c482c101c4a01d540d41569089044090351030390040c40385d054045641304c4c203c40c09140d46014540f0220344c0301d840c64810000c1010521020010942e10449190308607000802c5825017051410111962011000342140c0e112001c1046000012200900d500c1001c216407003082820b500926020025449169600190920840e00b0002c8484412501e0300f02000c002c1c0c6940c020b411058102d03040c0c80c2034648254a1042c0d06007195000d81c01100e400c1c00705002007140c020000c6800010b00b841202401d10b180301803030007810500c109214130380c0c8542d0340c00000303040c0800409010303440780320078000b0300c4800e1f55515655034036004056404400212000d22280d140f800200f103900400500e51030513a1a03103824400d80b0541c0020390b055900f0002084481124440d9102e03502c041c2c02a0f032142c820070340e40720b60401c1c5031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 83735594 1250 83734344 83734351
    0x3020d060e0907030201080403021c0903060f061802130503030d020717040b180d0512030108010c08041502030903070c030f0b01050d0c0e070c0b010306090b28020f070209040b06030105 81
    0x600c0806801d1264a810103d00c26040c1d0340c080c00c204503d40c0742d5180481c50030600c0340d6180c22464032082080c7c0c100e64081241c4d0300b101c0c020a400e10407604c480c0100f1007200c642d4030804006c04a412200d001d84101c03600605096416a48151a46a66440443e08590002c1074070311070143d00041c2c081c200260302c0b090681c4181d40c00400c038241828605140d146200b00078100186000d020312207622991014035500440b88d1001c15a40080c10700581c50509030001e0080310441c0d401c1c9424104114458440f041c42150032003214804c485816455000962014003d12050f010400281d40416200646580114855041e592400c1428180b2099001041c1c221622070bc070018464000700d81c54006000c10703144483c107640c1031340c2c840d4103055491113068070000342003c4003040000f090110680c482411030340501a040700d00d41c5c1c2c882141310302951081d070005401c5d11f8030504540c8401c4a43c0640140301400c1c1c40705240403100d4000424000084400b241d08200140821845e801e00780150341d003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 83736844 1250 83735594 83735609
    0x30a0e03030f0408090f03030c07060e01181401031d06240607060b210c13061a03061804050607020d0305060f010507050a08040b030403020708060403120b030c0303030703020d06 78
    0x11410074031020450402d020700b000e0300e00f42012420802968406200a64040004080301c2e503401c442003240b619800288103075800b0440701d40c40c0704915401001208410b00358141801c680e00d0034052882a5407140401090405584800c0c0c00d0f031f00d40b202d51848080e220042d00404440c0f400802c150000d00ca241d8034004046505484450aa1140c000380d0f58082c0e808000440c00e010400302080502040400b1801d1400310b1038841a003240011442008104007902c0c185049141d160100c0282c841503c66441c051010404210301012a000555040000203020a0300341818030790003d50b083d02035138240d4090b00f02d0002d0100d10398040020b050002d0081c1010310079484c001c0001052181d12140300c40c14000300182c5c0c0404c10030184006040c056105407a00c2e25191111040c2403035420031181180548145407000c124400e0008460784140d91555913a01c1046410b24490007802640320915018440e144140840e039806101543c031502d0070340d60058440c1c0300007201d01c0070380e005c0364480ca5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 83738094 1250 83736844 83736847
    0x806011406090607030e060a0309022707051605030708030609100302030615010c0507060206090d02030f0306040b061b010b130501080705010507080d1b03050903030f0a0c050c01050408030a0e03 85
    0x2050751070702019200010421140d10b5103c81c1a41402d5805040054600382d110500041849035507415601600751540243c440f00081c3c0c4212001023084201451142d0358005040c0020b111244210018040d0303460405c01600c03080f8280d5184c42c0343d5041400c089850440200030802d643c2455000243c2c40103880c01d00006d01031071a00801d44912000c0c0200c031610f084000c640e00140d00455a80b4072160f4840200c038600c980d202c50003074a501e02501d031403000380604411011007038400401d031469108000c0f0000d14540b10003007000020946901c580390448014441035200d00030780a80301003006001030000c00c0d50210401042a05010718224180700303480c04006008c10f40c000241c080583d0801c0c20196503076484c80c108a41f4074000d42e40c000143c1c60a120501200f025180007403062130382d80d0b403024809501c0b41e990854507400100c0e015404107140400141c01000325070808003491101e42001e41c0350845400d40d003402d48004035400d5800c3d1400200748240190144201110401b5040185 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 83739344 1250 83738094 83738129
    0x60c03081f05060307210204030201030c0c0c12030c02220501051507020f01090b130503190b040b040c090c080108101503030503060f130509011b0c031808030c07080601 74
    0x81664000d00d00a070b40c00b8003070100c0000c5610380200803080610411868101801030700da041c000c060760203404200e002071308041e81d5510050191050f5090745034040145411a03040148454120301e00b43e400f0390030852014010000342e200c240d410304400d424400c0c80460710341d0000c1d0039015030700103a11650040d546810002d100410383c1e010b6501103070b41150003083da02e103c44012107540c00305400c4019545000141009140d00c24403014049030800e40681c0d00300328007546a01c50302070b08090042c1441d05090300107030010f0b143c04945a80075100310600c0d10400e481d204258101c501d03064003803021800650050009074010044480340d22200b20083c040c001090711410490700c003500c00141803003c04000f29996070380b0b004404000794406040c0c00714045556001102410094035001e80951810400c1c1d0350b0742c50301004840c6a500692105032009030207641c102d031240d0309035080c4691141d42800110715401c05100410710040e01800038000e450408050074100001079015911000b43c03c12003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 83740594 1250 83739344 83739391
    0xc040e0a0c0503390a080604030305010603090b010b071502040f0303020c100f080a0b0319151a0d050c0a14010206091c0309021804150f0e0c040b0118060c0308 70
    0x54204161054800ca15141c2034440ca084c0c8081c5040200341d00441d42c40700800ca00c4400149144964020355050085036a01c82c0103404070f0300407280107440314080701c00501c00d481c0c0c004014000c840c41501c03d0440700720400f80c0e0300103d8100c0d4015254210070003804000303045d410068000d00e11012a01107c1c3c2d04d5902300d000d000c0885a40b1090140a4a2400103003003d030703164030001d100c41c0040c01303481c8129903054000128031640c1c00200d030400c40202c5583d420503030b14800d10079980290180d09014240d070304100000042004021540c80c4289015228191555442180249030f400c44800341c0300070400003e03061103402403801d03107141e0150022428011081180d0780511440b42400544045107001049101c485c101044410070307410703005d000c10400c00c4610070310021b030b807013000308400d00149451206481d100094243e60764041001c48490f8506070303000c0030517008141007406810312a0100d0034401070441e4081d1002c980c0007004402856000401d00380d2050001310542c00800440381c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 83741844 1250 83740594 83740633
    0xe03060402100c0506070509010f0f270f08070311010804050c150705030a0f030c0c020d0212010603050d0c051b06032806080f0f01020f0d0903020c040e0a0c0503 71
    0x806407156518580600d9010f003d407021000698000c01502c0c0303c1c1c13800040280941e8000044940010b01b00e0180d4075034a8814612528000016990700c031103034280c501d040d60600407444481403803031034140c0000340540c2c8488851009003814405454010300e941050404149240640c506105681d000c11000960110304043da200c4211100340b0304400d0700215410304d005104004109201c0014091409034207d28008001940e559060085103540e43d811030f065166008000e4000c103805d8410001407070680d50640300e906090000141907540c0c0d4607050310b0700205170706080c0420345c02191001031007400c5c060650301c0c01c0303400800d0100ca429040414040c2c8001031446014188611455103106d628600f030992a900c90741d0148003042d12041c0f081c0d00d40100034850201c0703100c3c00700310780070f80c1f0b03c1030099030311031001600102d042c0104d401085015145000d0100c0860044519404c1e1540d281e106000b5076048031001800341c81000e2401c1ca492207d80d0700050304c2680300d9101e010010420700c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 83743094 1250 83741844 83741851
    0x1207051c0b0901140901030f03020111040905060a0501020127060b220e060403091502010f060b2106010509011d1e0f04050c030601030b19062304030c090b0d0b0a0605030705010e0306 80
    0x1888c3c041c5a001c0703414120b0041c00c0200050b41d01100000d030004801c00c458000701d003d40c00c21515450404da03144010b81c2210104903150390121903501a00082080100440007107501403800890700400410000c0d0708041d02c40c592010704410030340d0f004211092841f450b03070401c5080c0000c00490905032006030035a00c4a116480c40e00038054200c501c240d100b90084030440101d21004d00600740c5030088400e540d04001d6200c000d80340d800b00022410380c3c80c10103071401082c0603120741f807800c0c00900044414a17610480780c0c01032501c0105500041d01c40d0958225211508511751409a141c002005400b0141070131452046050205003c45042c24030226030300b058090078001817048940740410200462400791000c661650f41d00001c1054020b0b4258004a04c503141a5202c82c580141000c85402a0300001c0c11211551605115000c11380d07116180c4031400506001da10b9a06076280354000303e0894802d5505522104100040c4c10200a0403000c0c1900f420880118003900c408241e680c403004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 83744344 1250 83743094 83743103
    0x6040e0403050d060f1509051503070c0b24010305060a09320709080d0207030201032c010b030106081207060f020906070602121b1207051c0b090114090103 68
    0x9002090415010304102d071403941000d541880807540d101c0700d6454500e050701c58400c081a0707916100440903c40d040d94801d03140e00a007020140f00c03a00703210180b0341e00000d007558107020700b40340e00002007440c41d12040c1c440e414802c492900021107100c0c00448103400200a070500d824102880100e90b03c260060042d03580003c8009100c10005203400281c9845a0a08546441d40c1902620200030880c009110700500d0f01e9001613a659a02455555081d0585a000503003284030180300640c1300b5000100040c203990a00260b02034a2100481c0b00040c4504100d0142c0d0340321911b00f014242070007074078000c01054015241c40040890600ba0324800d4003c000e0220707070f949150011481003941a5880480301400440c0c8030030b010300d0120000d6002d11541c890403800b5000240c460341103c41c0e40901c1c00300e072043d464207041600e09501a0580301412610900c041840340b00c00058500200408042c11a003003c264038280100380f00c502c0702c040c1c00c01c10410260b4200081181c9980e0345850440707034071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 83745594 1250 83744344 83744369
    0x10903080a03090c090e0307060b0d02010203120603011d0313090c0e04020d02040f06111501060f0e0a030503030a0f0f0504030c080a0909050a021209010b0f0d0206040b03040501020c0d030b0604 85
    0x2941342c0440ba054944d0080c186030b80c50003100d80f000314000009403090078440c503020054442c203503003000700c10310744440000e00590040090076290500c2c80803540d0050740240010030041442090034100600100c2480c05a50012903103201160310010304c0780040500030020409850311500040021940c0d99005002d20f0b0002402d000064255040b1001804c880c1c3c1e4010040d034940320002c2888245a0007001248640c0f40114030490801740b0260486a09448108004034100341c1a0341e1100e1032100d107903204c05c43c0380001001ca0007e00c001c46c41000c0c0305100190a11000c22a1801c844940e1a165501d5141008200009411026810a15400c6142a62140d014031000c40b15000b840e04110070140c106014000c42407915000303004c0d00c50040b00c6c480380030b540d2000c1c1036088032084e0400b0799004801d280200500d040c00f03844c0d49080ca0000d01020728160b2152403840803644182d6044030b990b036000810500c0b582050002c1000100e1a1034240801d00000c0e002031418003c134001d02000202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 83746844 1250 83745594 83745611
    0xe090105011b030c0803100f150801060e0402070203010617010e010506030d0305090f030705010c0e2409010e031203090f0625031b0305010302010e120316021804050106080c010903080a03 82
    0x290303185401320b40d0180e6065601d24044c500c85d100154688503050103205281f4022a602903004140d000c03404150780c90710416880c116048442c000c0e50300401d030300f00d43e00300401809030b102801044003410b101c505580488507034000c07144c04c440301002140c209901d46010f10034140c0d4003003800740c44c10480d40340c04540c64450980c20743c106401c61030070012034070000680d901081010b4102402c0c803240f42c2c48001440d0b0025040c45100d0350314210b41528601e143c5400e054203000075000d8035010300306242c04200a80e28070041303490500071075100f4428000120402490280400103859012000c002034051420076400312120800e43e10426180d00101000140145119901030519550702900c110582c081c081c00203401400d080c00164001522403141000380c1c24190644041707503035500e00641c601829407071982d203c00040c8608076030046031340405c0030314100742902d0203005078028000001c0302d4ac41d200c445c607d0030004102c442e040c0b00d441d02081010940c5081500e00f5422541408a260b01d0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 83748094 1250 83746844 83746847
    0x6070303021204050a030201110306060307110c0a0b0712020304030b0a0e010b0d0f12050a0c030e04090605011806060c02210f0303090d0201060503070305031603050c06010909030e090105011b03 85
    0xc04000b00c10240c840e030208418400c001407070700c0d9841c0c02a00200700403078054001407414801219034640041c000c00210304424851303401b100504043c1803d8502c0104a0700001e000140213511802481c3e17030102ea11014490a40100c4e03e07000203e0000711301d003c0c81d603564940c050000402180304550388100e44500e0410030b400071074440320002c00c01d8803407103014a400f80e005203003000e055030707036400342099500700c4c0d40550101d5600030200d840e140e501070b403181c0c0c0c00c4856001a074851500b15403544501c0c000107540e401054043c040d291203c1c3c1f0301c240c460201400300d540c0c0303500c10010800c56500c0c01340540c0b80c000c3d181d0241900811148040c4582018003443c0c13400706140000e0301e2000000300400b4420101d40301c1440300b410350090003e1683c803000c00d5179440355404042d2554000308001016100d03800481403116205c0d0600d20300b841c07000c184680c02d04809034002c0e20743c151104004802c065201c02d0b2401031034804c81c2c600806504200008008002c0c11141d1400c0240c0c1062040a06 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 83749344 1250 83748094 83748097
    0x4062307020a03080307030c090503061306020f030c0a1d0a0b0307020a140705030f070302060409020a090803120109060608100501080606072111070308090108040609020310050708010b04030507050607030302 91
    0x450700039090300d50460f030307a20b40922264021580003001138900541640302620a2140c002101d10043c0100016161201942580b5800b0903003120400e03800c201882c1039185010140d03101d00d01054655880d0f40c41440058420816051481110000d110361100182e0302c04d0542002d0b66403c0100c1034680da9000416841c02070a000007070710310400c94440c0f02c25240000f038044240d500580c10b840c46c03450f00c4a8060f607510018000250301c0641400113004220705030b80584044029440c05a508070342e69004bc500356802800e0100c0003091041c010b22044c00113000e031a00030405032404190b1460f0419850740d02c4500d50150038100803018011616030f990f02c00945600c1d940010400300314038040c0e014202c03411801000b420105403402000707020034201142c0d0800322500410843d1909040360700441740c011009108450701940e4004d10005138804005a0818400a100003d400d00701560041c20784441640181c00740d547c2001f091000400c00702d4040308440c400e4455503112030180c6400d4019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 83750594 1250 83749344 83749357
    0x705030f011e051e0a0b0c0307150612030207060e010c030203090906190b121b1b10020409020c0f03090307090b0d12080a0f090c0308030601030912020703060e0102040623 75
    0x1199100b104c0fa80030012040490030114421103c44e101075980c1c07541560940502004031045400a000220118464440360b40b80c42100400c00030b000790f21001a05010140f8000c2500140d02007a010300106800c5000001e000307809003404a0000281c1c0d030021b42e28822036455500035500d00780499a2600d468403080d00c12500f040e8080039994485090329060780006411007000c80c40c01e0041000a81e602c0c810880c100c0c1c0d14036506150202012a6510381007241700a06028480d034040700a45094910140004d040d080e48050794400304502e0721841d01d031803100012029007042003181082d56001401c0c1c0b04846040e41e000c6042e024010004016180301503000d07002081e6800c40c0240300b0750025150344500c0c0000d100304a200e209071240411510090402045940038003400d00101d180720000d540c0c484814900402d00e1180b62381c490392012000f10700307080964442070041c02002003501980754604c0d9460003c504041c9805401000720f195403d035071001d0401c805038090b08500990441d100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 83751844 1250 83750594 83750599
    0x70804020f060c0c030d0507050709050408250803130201020d0906081b070501150f06030203041253040c090b0d060e0d09090506030a060b0409060e030306090705030f011e05 76
    0x16411b6041da0060155030160300f040b03845014000c804660152184641030281c0e400014103828415401c07000d284110020380075004004800c405a00044c1aa000461088415880d8102045001e1002a1800000195039001e0003030369541441241c3e8404101d81d80a00101c0314201c5c58009820241c801d407044803000783c16942440c0c4107614410140107910120f81d40b440c001a0315035580c94086040f8002510000c0000500c141d0700e90140e84941482e500c80c0c0d00040050075061401d103000b010042180031505181e05190784686403207081088070200c0f14541c1200d0750030302e1170990307204c540c202010301030306c0641aa540c100041f0f54580d502c14002059218008021148042660030394840a680c9074100140005c580480c294105000e1180501c0b005401402007661654900000d040c2050700036801a60b00c000481c080f900c103000d00e00300c6146a202035550790608905201502100602100510204200b4001c103a09100002411a00c01d500d161503940310820654042c1d6010380d020704c2d13 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 83753094 1250 83751844 83751853
    0xf07050310031b0609050603040302030a210f0506030f0d09030f080f120604060b16120302131409070221030709030c14030c0a08031c0b04050702030a0305070804020f060c0c03 77
    0x50300781c00c200b40141d069130040c0c1c99000c2550740c0c45040000d24802100d00500682040c050603c1c2140509110031582158a004c11464061600918101c0d001c1860b403d811688400c14007840d0f040a1085a04040741d0f2005003817410f5003128007901103107007840700034802c01d4000081c2003070101940035281142e180b03612440da01e1014969809213240c3c01d0740c4492090f454140d0010740e00c5400310854094140c030260202400c0e031035440e998055420a1254018180c01f0003800c80018084412000a0700e82e0300a031ba0285603100091110a040040a1806542c04245030406014a10548140c0008900505e030780d80e42d902c40c4120781c406880c0c0d2004007002076404000c198001000c1441c05407402c00d5088442d42d540d1070040003444040ca1041802c182c00c20070084110290202c4071a90076419141c0202d00d0052000104089890460b2148010380002c039a184100f0b030305018040e0484036a180100351410580c0010755480304015419105140c000ba0b1146402e07414049440784800050544 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 83754344 1250 83753094 83753123
    0x1c02061209060f01030218070c020316090506090609012c0708070e04050f0c0d0605091005011404030c060c060f05010308042d03060e1c0e09010e0f0705031003 70
    0x10201000980c0c1480c141c0c001e00001038202c4040100c3c940c1241c3d0001d01c50300d05162400e00c14410144080c142c0d8003003210304070341c03800940ca0030404d9071341801c0c260718040c101900e01040300c1c2c101c401c082d005900c0341204006100d480c0d03450000180c10345200300262050760205260f48a00114a40a284c0a8442c8041007155454000c105244503400940317509903604501c00c200700465030201d900c178494007510701c041130812945030003401381162050740010b04582c80788006401018125203410403000c840c44107101950340301807900000606020340310304160550703903031070520702e00c5020360f80801007242078500911440360040382480e08180b0701046156141d040c200c1e22540507009600700807400d0105401c0303039000389106146001e0b202035245070b03090540c4d0710b040151107616841c0c4258481e90032162440105600103013065107490b00c0e403000150381441032010b0070b07205a008800c800c100c1001c00c501c1603808296140e20074414940b140da0b17a600c81c042c1c0c1848030300302e07000505104d0298a40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 83755594 1250 83754344 83754367
    0x50c0103020f07210908010b0a0e190204030803060114070506010308070c0b0714010b01020714060a03020f0a05040302030c010e060703350402090a05040c17120a0c06060504020310051c0206 83
    0x8440108545d40d554000c1600e400b1a0f60985026803021364200d0350500e81004480040003250303402c03030300611815030400c0c03524002c1000d80c1c1141d002907400d52030001c24040551b800040f4600d840300400c008a0074044240c84090b00c60505200251042500044120411600d041480d010700320015480b074440c0c0e4681010494981c154904000c0d039071030003e648480351f000050190032203046110414080e00d8031000e02900c1e8002400030418941c080c4600c000f120108130141105165564515480310300d10b004044c41c20740040d080034103000c180e00f01c00c80544c4500d400c466032250103041c40d140610140716543c002e07a8030f0804440b020a28161030403991000e00195034040d5000321201e01c6940c4a141d100303811500155801002d4a11a040800098440364034249100852005682069401406070a40c9038420910700d8000764111440f8002c20049100307031f40240205035011401d40c609410348c04032144d40d901a1900c50507400201d40e500400d480d40c190061f50b4040c02160b01e68610203030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 83756844 1250 83755594 83755643
    0x20306011403060a120203030903030a021c0314010b090f040507200c0a051207090501030b010e09010b03030f0f0d0c171303140304060b03150919050c0103020f07 71
    0x11500e0001d0811003115006034440c03800d81e030080c0801030005440d2071510140e68291003081c54101e03054002032014901d00c0d039081c8050442c07420b898004e022600c040d4299421070410095052042c545006440034400006806c5e050544004100541e99459114001070402c020301c0000c82d40a820300c41080462a8410882807208901041c1d0481e000310b40f4444540303da2444401035000048800c0c200107601d0401d032040d5607880541e05440e085602d942c0600d003910341c00d800039a0044d66110041004201031500242e000c450700008000610b210000a40c4901c103400901c54183d00109501014584400c201c035542d20340c0c980c4c20811401094406000ca8988490f00050404408000780628009041d8811200c0c0d05a640e948401c0c076a201405481c0c01c0908281c40d59951403d0400294400f00700c003d030010564480c007000c601d440d01440b1710713000070007082c2083e1780c04000a110006c0c4000545c0c0807403540900740942c03540321641e0440d09a000e04140903100840c40c1005403052040300f003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 83758094 1250 83756844 83756851
    0x204090f051e07120b0402010804020a12030201021b031801050a090905090708070b0309030d0207170703170105030a080f031807090b0906010c0201170c09041e0b0901030b070806010c0807060203 85
    0x70b5070000f40d914503d00000d045038800150000f03c0640010700190300c030300085640148028003d400c50703070312601d01e103016103020322040740541e6000408900a406103050340142c80e01620086107042c804881c2d440600b00959049818010702140020100d4011030560000e800804410003c0385040007540341c2d00d441600c01c000b0103001e491000304100041e80126880341080300c00542c980201c0100203c000d43c09000140ca42c00c490100007545842c03c3c0d0000c1180134002e50301c2d5001d080021282481291046e48600c2c4030340d102642c5800001c1e0204155151154a000410703140c4c2d5070280302d0700c7c1c582c8004000750210b01410202003103680003a441030121b40c40580c0d1901640d600c0c1c0c00192095203c0700d00284c0819480c100c41e990120b9407100c080d074048000d4131a6030900c83c103800843d0079514206030110300d1042c4104d22110798841032190319100582160300319640e515546400c0c1801c04017a10315402c1080c880005420740e40590120381105501125066a490f16410321000940054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 83759344 1250 83758094 83758153
    0x6010302090a020c0d11191a01090501050a030209040f0b0c070c060206010b07122a060e2e06080307030914030a030f030e07090f060e09010903020303040204090f05 72
    0x150089400b15219109548201485400400d0303031082c2440e0590382c25102500d01402880790b45006207400041c0f451400f09a48103c0e0848540f550301c243d004030b0700e1016048441c1140c6401e00410040c0d6448610104807070b0161251092034407507081207912455600c03400b41034036201070103202d0582c03a00c6000704100c0303000b8005c0524840d1100000c90304c0751400e00c600c0711400400e01c21140480c02442440194004504080740b00106450221103240a400300103c040f494042e0680d05101042c0115081c14250308040c1203050141c03000504102c2105050895800300d070039001c0d45031201c070b501000c06440300d901243e85800d041c0c42e0003800140a400385078110711843e00c003000181000074450400719815140c087d031403141400200c00034286010449000d2242c040300040c00700c86840783c4610807401c0400402d142d828040e4400001801070600c90060385844494030120358080292a081070b0704a5000c03031400c0303507401d049036020103981d005451030040300080a0415000107024644103080d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 83760594 1250 83759344 83759359
    0xc060711031912020d020718021201080607020709150b0306060f0c031801020a05060703020a090906080a12090303080622020310030507060903031d06130f031505060d03080604020d0e06010302 84
    0x29054101d0f01d1700a2003c044015074000c610602000d50350009090510301e02c45001410031070640514400042c0a0340201c1440c2c101105005a0a9040c4542d501501351210244859204010031850f40308040c424903981d0807010001c2000c56540c00c007100c3d500c030000e45406d4bc407002054441a01c039030207041c07001035040110002030b01d00d50002c1000c1d401140c010b400391140303640d005d1040c0c0280d0f00400c804010030507045004030345401144184805440060003c0588460398503144090800b01964041400f6149404100003540045415804101513921741c81d1502003400c2c1ea24103058460642c41101c0c004000c02a200001c090b00c40c0c1100c5c010000c4034072450303403150169a00011404007400007640d0090448960540c02d9508600810182116140c007000a12000d424103894004030034440780c00ca41081480345540c14410342d2401844208010b08040d030018842940380300e0010107102582c800150150ba81e0350503580c000c1c2911310f040c04891140c440003030711100309000c100c0c0715165 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 83761844 1250 83760594 83760623
    0x1020319060e0a0c201c03020306100c0507030b070806150f091c12110d0f090603090201020c0a0f091a06070b040f020d0c090506030a03020c0607110319 67
    0x414040c180450b40c00030030001280c0c8a4582e0000905400c0a0ba80c092008010300510f80c04038910546138001c618030050140c150240c50a69440b0140b006140201401801400000c1d03071100700c94040440301d030418219028140c03802a09020a03941b0240c01c00b044d401c200441941c22171507403403061604444a0052400030040002c4c4c500030b405c1d00c2140300d002408501900c0c18400d1803500c0b401603a90300152848034595902202801c203540038400102d03003000ba1215103004000c1c400080e0210305101c0104043d1034001000c0e10801e01c182010907860b02c650301d003503900910046081280141c0f0014000f07844000d00d100304d015602c10030364214030703080600071140c0b49607413000000d0f40c00509a5141c0035241d02d5a10710f0000c0a80141c840c074001c3c1025030b00683c2c5190190551610540d40b80034079500e41455402100d0004008600940084090000007603020400010140c0115421615401b1505069060748070280c40fa542610416542c40007034008904540030281c81008840c10189 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 83763094 1250 83761844 83761891
    0x317161e030e18180a0b09010212010906030302060c180909010606180b03060f010212070302011406030a0c0b0307050f180411180d0305070203010213060e0a0e0c030c090a08010203 79
    0x1203624003841d0000720800d0114040f0550b0200f066148103c5100300c0381c180105451b41c400d20503040d541c1e6404c6031343c000f8014040c0c1c08000359490050500240c2003044510710b880c0039484a100800148085600099069180100207088003103035002600340d0105241454219008109600842000c074980000c10160030361a0016101030700c1010b65414199118079091015044892003510306500811402c000c022038994040d1008501035400861991076036000359141040107403100f406a004211013401048600341890115409030309030035506d03964004103e860703000342c05100078440c90004442040d00c1c3c12841c0c0e822441c0045404124403d2041c0100000707109850102c0303651840031910129915002e4100a00c1d0f601a042c8a8940b2ba05940082d08982c040030b0f00c043d1000d4094800e010840d403140c3c1001140c4d400b940c0b14a0300e24106004a010f0b400010620320360030000000013900c0c44201d40503a10b04003800380110303080c503484140d2203001c1c2d00222200c1c4941c04607242c0705507900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 83764344 1250 83763094 83763109
    0x4031b091109031b010908060408070c06050a080609040302010b0307030303140105091006030b0103020706020f0310090510270e030d150308030a0902190b180a0317161e030e 76
    0xb800400500040444284d19614503100c200305905000404100058140d801d11982c1c1c815840303000072076510403032494410051501900039108218090146a40c0d09403c687c4050308000304980710b40c166562460120b016005042c0c8158160140110010400d03416400c0b0384458000000358001071303a00d134428050b01401c21607410141c3c25110504101c1c850003507021006211042c9805443c080b00d80d11000145e80c0161003226011000004101c18450b206050340040e1100c1841840141054200c03044081d07454081c2060003100c80750040020f808910003210003c0d0031803424001411500b2016450b0703044062801592400d1039489290642e1402090040c2e0303901c0840f960842d168085003e00401d01c200e0101e130490000346014024464071030078600102151801c5541d80c00128450b90740c0707203842c0c00d0528043e2501d10300c00c1c0001818005100011805600703260b03221f01401d42d842161404030341c4041c1c0110f100380840754102910780d0b04809030320301989481d40540a05801d001c0c88 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 83765594 1250 83764344 83764357
    0x60117060402060f1201141201060e0a0b12150f0702030403020a06030b01020c04092006030408070f0317130209090610090e01150e04030e0607052104031b0911 70
    0x1542000c4005801854010081c2c8a0422020740d0765003040c50700c103c000b5041200703070020528480341c020304440602c1c00c1c1003008460b4040800a01080c2c1c500404100030304800381000074120384030003000e81140c5904108401e5912040202e5250132030700d641400484100b551101c0b16000c1c40e03400030344281d0000084408896014144a00d554076045003140240410441581180200e4007841c440341da031401104415030107000a50110302c0241c2201a24906c0503440600841042c1f080002040d07900e020703507080303e81003002043c0d11011841e0844003c1d0f2841540228815000140700034030310210800c1035180e10a032500780b15070300c03150105581c60100315100342c01815442c0013030204e0300c0140c000b45020b414440001c145484141f40032000b03908260003925005054000300018994040d00d5030300d8400050701d00d5880d00e4850b4032955103400c207098000c1d608040c0181030030842c0c0b2000049800541e0440002051050705104040e2003490610680701e1007800d10042070300c050004011076a2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 83766844 1250 83765594 83765639
    0x2040e0d0c020f180906010e070c03051206060915030402040605010302190e010e03030406082401050301060f17010905150303180d081306020a030311120705030a0f020a020f0601 78
    0x4186003240d08100f01e0080b544402030b00b00142e02512960004405541070040007000040d01c101d604100c003c2c80203000042400c5e0801c09480b030480c6c003003074004080310f0360746214101180c85960740f940400c001c1d2140c240002d400020581414442e040c03000c000d9402544200d5003484480d90300c0700118103900489020360910800400c101d50118040e07110702c041c1d6107041c100030150103131200c002801c1d174116a1001012581040400180c4d80100004000c602d1035882c9030302801140d6030000b0590b000500820083c025175030450041c0c140101a40c4800000706500d035001503071611601d1002c2c4c0000d03102c2c1440f0940302081d2108511307020041d0b403072200d41e403281c1d141044800010401500030084040c0c4400208205041d450040c61448101600c00c03500104121505e82c600207003212199658500d40040c1400304600e00740d013810106401c00380d580317043d41d02c03504d0f400380680051820355580c05c040742c4005000e0210903008039046501c0c001030400d550a680e60b40541081c240440d0a0707020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 83768094 1250 83766844 83766857
    0x12021b090c070c0302130b190605120a02040b07060b1801081b0f090709060210060e1504181101030605030714060307110d0203070b1f03030302090609041802040e0d 72
    0x410784495500a002d04601a0340c00000d03140e601e0700030400308003c000310007094039110900c5c010b441c14560740351051070044148038200a45080c0b0300030710b58000c440822441801c00808101d03200402e0301a0707400382c001e10035141d035117140e2803a0200040c01c00e200d41c1401440c0103440e140c7c0c0c07840f62900c418100c84908025019027542502c24090340c040c070080b00e03944150004640c07074031a00d59409461040101ea2100c011a6040440180c0b51400344a1541920ba0401a06124601d40c0d03004550f04002d04500c0d0380c120101c1e420001c3c015007420585540d030720b00c180c0403803028802e00101d000c00200e420f88040011503101c80178561a90709600072003194840c24180000b4a0400d03000540c0e04c083d2501c0c0620703142c1d40c00d9888608203c4c0b1040d003200140d002180d081c062012003094990000700032100c044224603003041c1c4200304100d0707100c05000e01da0b01280e5003010b92034a0b412901030b24401842040215170320301c5d0103004051f8038a4140c1c01149050001e50140500203044a4110761544410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 83769344 1250 83768094 83768101
    0xa02030709050c1303050303100b07050a0605040309030204090606060f0908030f07030903021002010903031506020a0201110f030c010e0106080604082b0207060f0f05010b0a050304060e03040312021b09 88
    0x400207080c019080c1d20f0344440801400103281480303902d00d0b000d1031046028581d02e0034021950902c0b030389075811070348803c2d07800c002d80e0000a00014841401d154861300205e078a079524201a02d144d80e06074006500a414030b0360b02c90800070180c0c05079042e42c0868454401a28080d0421030342c5000500810a0642c02008030303030201007100c409003200d68440d1401201e82c2b40c9a40c080784c0040340380741c1140003607034440390380700b04064140c0141c0146003203140200b00760f03601c2c041e0029507882d201301020341444004022101a01000d2002094841c00002100e9444104461042c000c140c3c10300405d4184d4608000450583c00c04500b80740119007110a003420860450031030030508084102903000e00c03900011080803428140040c0c500240554400610424910302401c1550644240307140075900e4080140081f904105c19a51042c120786481500c0e6600d5141c0b00c00180000c18052900c3e210200d0000204002100c41c1e50840c01e00e42e081e6019034102c00446102002d6008803541d002c070102000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 83770594 1250 83769344 83769359
    0x1110a0f140405040606120507030b0a05040e01110a02071d0103050705091005221407200309091501020f010b06070201050d090605070e030106050d0206251a180a020307 74
    0x340001c42100a400701d16107a52200043e00f1149203034840c83c081100080c080f0201007562044036030100355420203010390300c000c5000850403842401031070f2003203503203d10100100d40c00b50702c10a02c090300c3c3c0d0801a600c028442c4007039594901841002161500700f1150118006800d00480c1200c0d4480006c01e0321a051004010721040000c101c02981000c00200080c5a510004268015100780300c1c40c1c1c59025051010340140c1d0201440000c00d0301184080c402500c0e80300c024143c000c80c0b50051051a4401490614118420000c40399448004034090100c40c440d0368400820301c0009808690308607086440b014241c412100c034030b56000700c051141c0d4015501071401414075444081b40040d038030107950745450444000750b03003c0700040c1c03241d00300701d0300c40c04d0034031840b000340c03104480242e10322603d540010708910501900c03064105a21215000750417101000d00c6d809a40200c01e10891600400c00542e401821034175054288000f05040341440000300e90585c272540c0103400307058041c1c2000744 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 83771844 1250 83770594 83770607
    0xa0507020d1b05040b090114030f100516020f06071d04050a0218030f0d0e0111031c11160609050a02060a05090913020f090417210a050106120b0109050d030f0201110a0f 74
    0x1142d0036001c0c1caca0000032100004d001c01c005100e01503600090608000207080390000004c1c0c403110942d840814070030103540002880310351045951030180d21260402030030b91811380e40d00c14201d0b0451304090500107200540c0c0c018140f01090000040c00403240c40041554504c3d1205a008542d0040c80d03051262500c149601f09030a42d040c10180c261120842c6041d28640c8581200ca0301221030719a0203900340d515020301c2d0076014001c03a2a90401220a80302c4610320503010f0000c00f8242d481d1001030410500303000309000c0b11340040010f61221181c180c042e1055010020346889484a0303400030f40140d041c4060071106235006404c00c01d26502080c248100c2120242081e19000317140382402145920000081c84011400848008095007074000840d203040064640d08105041600501030142e020b1002d03404d19680340c1010039602941c00050718031705402d0b008590880c0d08481c02d40103164200c1400c00d5500c011303034020011800240201da0311070060385104000214000c0303036210100d10508 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 83773094 1250 83771844 83771879
    0x130612111503040609050d0206011503090c03050f0304030b01050a06050a1115090c0a0e0601020607050a0302040506030c0c0f0105090d03090606170a03120b13020a0507020d1b05040b0901 82
    0x8065512503035851100740040d400407a0101c0e01d644e143c0d4407181c01c003d820312100c850700c0083e0004001e10750420400c3d80340d80394525044420140c0d1255a09c0521404410b203034003c40d084404d0700c0b8003a520b00b4446440307a115020a6502e8200380c4000160f90804040f04030403203030503948a40c01c04071603c204803418005030043c50164464000d0807a11041c8a00703115010f0203481d00140780b01e01f440d2041c0b0100b00941d900c020740c41e071007130010411540d80104589074844460316000742d0311800900c05600070b0155422007600150b000c0108800b403d1400000e180260602044400e0081e805d0901401d0710f10440382240f00350084074000c0c01c1e2500a1700050034062160310049081502c600c81c040c1c40309405441038050b42d0051119406060b08026003003150501403209004c6095500046040040e160580200103640004d03940403251055041c1d51480d0f50080001c0003c001c2400d12500002c542e1801005451000780005018640fa100e080d544000141417141030b60720703000300c1c1c051100551 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 83774344 1250 83773094 83773099
    0x8070302011b0b07020705100207230a17010207061113090506060705100b1002070b0703180504091104050a0b010c0f08041203050c011a030a12020705040c0e13061211 73
    0x80300040001d8141e8007191080c1d0045d03000b098101d10341010046003c0c61441643c0940d04603c209004031050444d1020030791501c0070b030301c048101c90000480d5000800394003460100c00501e80c1508039035010f400a08042d4003c000903c14046c82d40100407452082c1e00c550301d8411900d074005c00112941d038000c1548034000801d51824503031540c42d4642000140220001c41f10340c1c5840c0c580e00380c5482060700c81062800c7c40140351844c10700d480107059104805002d001c2c01084103144005150b5541d2090141002a1050000206c0c41c6006043e2502c16005184501e04140000b5820040c501c82e030310100805940ea8690b540c01a1940841101301403030550b5202c00401010540491022108003100d20a030707203180c1e0792212807036160300312994003e402c111560282030231602a80d000815004041c2c1004400d22080095a016440c0400d00d0b0b001b1600076007031611395050140c104150307407241207040d103802c0c036141d8541c0306070000c5414030b004101e03003090080200e6011803080d04820702c1d00d0001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 83775594 1250 83774344 83774387
    0x10c020a050301060f030212010e06040609110d03020604021302030c0403080706090b0c120901060b0d050702011416030e0a050a0803280902030f060f070c0203100c05130803040807030201 82
    0x6038404030f4250f4101c0d410880f40030325044020021401e0180c10003402c5543c1c1070082000b01414a01c940e201c050180000d003589844a142c041844031206140c144c0c450001c060b1503442c2c02500d030181d141c000443d81a4410105000d20720303582110f034000c0704e1240100c40304052a143c00d60341e40d41816045a5400d8031626078900c15000000e00c124001030099030580301603912001256012103090400402a1a080e4180f02c4208000c201620503603100c0711655070042600e54407d141280140640f0001d0540c220380b1005000801030101c83e4100750001a41d42841b03080e00c0728514076030751101c00c04024810342c00180362001140180c0041c64018071b40c406404142c5001d4404505030710368200102c500c250395501c1160440c41c08002d02c40556031140082e05c0589003103031070b44201c036500070541010b0044402e076100455030180250140210040e2041068200c4000000d00c650800e64291000b49090400801d40b80c0e8000140c0e001c0f034400700000c000c2c41b4190390044030340070135665481028104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 83776844 1250 83775594 83775599
    0x1505070c09022a01021606020f09030714031009150c1101061d070804032a02030109060504060608070e07050a050d0e0d020d05040b09040b03030c06040f0308010608090c010c020a 78
    0x901d0009010a0f2848800025840d00120b520402958450502c885036841041107080f02611421140785142c0c22a400585401c102000c4003e02d200d403001c02545801407400104a041c0040400c0c1408101038040b40d40c49144034020800311890000003501030080c4000b40c1c45c1400300c0383c202c08081c41540c50640701c100e040d44c2006003900c00c507030410110040706241c46003021000403074030782d446206440e1001c0141080d8070003800c68940e9095900100a45d0000e074408403000510301000c0d10741c0074000f00107004c803070300b402d0004210980301103d00a04000c400107010342d0010b01d030415100016407034001521003e0040d200ca80c000c268800034070000f4000780c2510101403050360411801d00002d010601d00e01c0300021708082912041105112050005100360a040800da0708012415900020003401c0b001c002461b40c080c4000640c001e204010401c01000b4401510802a5200c0d0706c4004159072584800d0301c0480b0103d0755144140e1150f20008010f6124a0040540c0b90000d42102129038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 83778094 1250 83776844 83776859
    0x8040210030605101101110a050a030902010504050d0c14010503072a02131e020f07020603090703080f0c0601050301050c03060907090b040807081c0e1018090b0112061505070c 77
    0x40d550720584049070148500785c01620313083c0160341070228602000740c505465104003900700e000e60a2440105130340d03030b0300300011a401001210081c0c10b000f8460b80241c009407508601d6404607000b1a2202d10003200b61500301d5015006581c000c0603561a011b007210b012801e804c40440005009240d10f43d8400540c1d0090707100c0072001c0140d2074007113030082020800014030440360980c602008001c1841002420070060420081d9502140d04440180d941d8035040800b40c602240ca40001d0141c10740000c096079810180001400c42c44601d5080e154140ea942080508031442200c0b44201e00700c013040080c545143c040c0000d40e004940d800c1c40d5280a4031078143d0401500030340c0048030250300150041c0180301d400c03c06011f4180d10440b032882d402d09240001000905403075159806010300c0b89003030204e18002d000700d410400012501c0b0007002d55620b186d00c003410300b09012902081c41010a01603802c2c26004000c10f40c0c0e890012010004000c0b0421034103a40000c0d030550b40f04004160125210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 83779344 1250 83778094 83778109
    0xa200a020d08030604140105060f0a0e0316030219120609030c1a0109063519060515041b08090316050714030303190b01120203090703200108040210030605 68
    0x180600c00310b58aa2501c0000e000c103da511940c8404003405c1e6100420040d590102203603182081e000e0120b40701c1c1c40d00309013680c640c00d00c90f800c164180160880500590fa20166200c212402215404403107440c4a0850642c0030313440c0540d400b000e02c00241000032840380c0d00a0207040d0312034a000206800b00d602c80e80311448250966034039003405140100441100c41c0118000751002106012081c4c9503540a2010a02540c1200003030705070300c110f03a9030910000e0000c40e0050030050500200b03811185810401003c1c21504d40303a01143d10400c0c5062030030320f4444e1300c213051540c400d00d840c0b504840380c0a40301d020000345800311a20003000310a242c01840a520204984104002c0000703d0a210109002c001d060124501a901c14401c2000740f81c0d012013a100040c461803400200e000f641c00c0105c518110419221284a00002c103022a01c0000a10b03d0102d03801a0104a08880d00043d1345114013001000c450000714446c000c2005440c3c1000007001c05440b9007000927002e030795280414990b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 83780594 1250 83779344 83779369
    0x11215140906370603020603010b0c0601060503060627130b0f0301090312090c03020d0809040623090c041e030b060307030c0308160803011502010b03030a200a02 71
    0x3051a00007401408441088142d80081e15904a1003601d4001c1010381890b401e241d80e410b0758a840c00e07070030340c2c1c000b40c07035500a00295401030012540d035031312546d41401907440180000401c1c4a0900001003051151041d24010030b4010320003464021307180d60303401e1111407448850111000000002d4419510f000e48240040d01c0d0a801144010728081042001c8003000074607400390341000c07078184c002039200c10f85440f500103a81000480d0600c80c18161400e07600341e00000c1d000560500f403402840381110280c0740140c003c81c0d0034000d05855a0342c41c4034441c00a14010000348620100030640d1926401e1603a1041352034035203506056840d142e030341910340103604c0c8003083c091320380e018414008041000e83c1e21800541c0100b5000e031031680d072000302105511001c1e21911000c958490115460454142100d4000000545a58440040140300c1c0c455041400c059840e01c3c00f26161030402006540c03200b400c0792a030842e01c0481c0212195007070a0242c001186004184e1444010b81d11000c1c036121 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 83781844 1250 83780594 83780621
    0xf0b03030d0606230909071e030b0316080d0f11070b03040312020c030d0f09021e01090f14090601020703050111091e0901060e13051e010f060503011215 67
    0x2030491030500003420fa0313068052503007a0243c41c031400740140c0e074240040360b0800c64240d034035103010754030940210303186032454101000780101038450820a581c15040009210000c406641e00ba036034440b40d5400900441c4141c0340240c001d000c5402c0c10300d014003243d1214501301d0038038482445c00d0322501e500b08000360f0055440a0008000d00081c503511004208a1101c1000210324010b040c4005542e03900616822510407a100c6400007c0c8403c640c2011300e02d19400f0b45400e0003440360348600740703482072044c11142c002620420300244428202c03241308112014403155240c0200c0800501421240080c0118154420140008000381c402d1044505605000b1074442c4c071a04100100880c8408000c2190a803c4592186078401d580340604a4111105410b081440d200c0074070203c0e944010104005211130728010403c24212032034010000c1c54485000340d0740c9640e03200c41135a01074450f540103160000d6070070f000600000b000d000c0c1c8800c0031030040c964091200c0c0518804015249845500e80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 83783094 1250 83781844 83781851
    0x2409020303040e091501080307060908040918020301050702010908180d0c0306020c0d140a0e0f0604090b040c05130b030603010908030106030b150a1d040f0c08090d020c0d060f0b03030d 81
    0x14a640c1c041c001c05c6000c0c14214070034941540b429111640d00d0080c1e02015007803a40d16400d4030100144034045070002d10408109001003101e804050040483c2d000040c0d00a5092000080d400c0344107104208405a01a582c1400d052030742c0380310300311650300c3c100180c0c00022050703e900100c0c80f44403140d00254800d240c09a910021004000c2c02c041c0d0301c5a002c42070041004140b511402440700b5111440030b1458060b0700e11800c113000624100001643c2d9400100004010030102e505400244100c10141d40500021002500c1110306110303804085c103d144148106004140b0444011500304d40e0040000c02e0059454030b400a0981c002ea0028010070350391901080641013000d8100d0240c100c10b00442d013804400c0402070100025030080d01203490030908a00642d540303c0c1e02c01d048070903490703a0400c03031081218000380c00b0341000c1d1000308841c0f0400e40c600711064400103c1c040c01e03940213080c112102c58560358403400740000d08482480941c655a8141243c0c4040021f0b0017810340301c0e480403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 83784344 1250 83783094 83783101
    0xd021608070c0f0609030b09120f0903060c04031a04050c030d08040506160806060a0c08030a0b13050411060309010b120715020c09060f0118030605040c05010206042409020303040e 79
    0x2900150480e88810308030b4003900703000c100301900172428400b1682c200b80c0541482c0d5031403000f24100000502c807111032740c10100d4603411018602014080100d800d8040301c2d610713261640902c0c214000c0d40b2005000d860f0303020012880d00c10140e126904a840b950032a0b6800e41b04a00003400c1c072540003a201c0004903c0c5d010801032003030801520f0f40228080c0750040200741803a500802c0301000a0680e8090714001540c1440184500b90803122a0381100b0b8854607810001c40584c003401c40b100030341d071050140c05251180d16500388500c0e801103603c0140c42098100b810107000300c030307080203044501e030b5580c079148038a958469227045034020000d140500602400d04045081c00303e1480401401c65010840c6513086489890040c1c1d00090304480e010380700c1c84010012180b50b0a00521821280c0c1990030000c200245a0011400b8034860a294040c05407140700482e6646003c4901400501e400d02050300d2102c503a00d40310035083e940b84808a0b0002c81600442d1465000c1d9200161405408040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 83785594 1250 83784344 83784353
    0x70e040f030921060e150103080301080622060504060605180601110d1b0507031209060e120a030c020a1a0c07080a170a120905030711030c06040b0d02160807 69
    0x414040c19002900214201c0f11000800030b50050070001400305580781e400020380801042012403114480f8400740c200c3d0b03168030700405190428803034a40d10b03208940201e5001000b80d030181a480c40860442800000e0a88030040034000251094a2042d59440041202d44a05104215140c40d006440c4218200003000500390045e1500d254141d4003c55401c62015030b0040d000415a40400440710031240941000f508080e610fa0004208002d403004075000d040e00002170704211082920360410304c1c84481d0902054210510f03040c01c4e01d40003001c040b07001900514a2502032400540a0304000e0b03110103581d1030204080741800803055010880c4550b481d001c100080241400744007400241000307070b440c1d00480001d121000c08518002c22010070a0f13201e40d817050410001da9009000f100598200346850f68006601601d407071802a2018100341000115544400c1010700b0301490240b414680341c00541003881c56100a5400700030070000c0480314522000824042c0c4c1040f170365455585003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 83786844 1250 83785594 83785607
    0x108060a0b0f0705010209040510030506010504060e01051207090509010f0605030714010813021e030f0705100509010504050a030b01240c0303051e0115020106090605030309060c070e040f03 83
    0x4103031080303210003424001c600d108400e4803003551503580307100d898810601e0042d019000c0d02c1205500589000100001c8010501004d01100d0182040d02c4040e600c1d03000344810741c0e0f054003c005610118500400c91403d018800c0c19220441100ba10000e40e103620500080d24015100e410660707441e0600c1059078074842c40303251700505003100204442881c059002c10301c120340c6983c041c18401d6250004070b6038441298a2412558010b122003841281d9411103200c03540703515401402071082c3d00e85c0c19441017000503c1400e41d0401002c030503a800c4000401c45055010035540c0e4100318090000040f00e480d0032401c1d0700598441c1148040c19810001010050031035020340d01031840c110b107860b15459400503100c0f0205501031802190694a10b00d00022180c010101032912441d154000102d106100614510f580c2e0b9039402441899a1182e03c58251000c0d40216589504100031210652410000900c4280c100c6810f07580c0c815030714880c140840c0c008071001e6420480c1c9800c0a000c0690014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 83788094 1250 83786844 83786851
    0xf06060e0109030507150512010923070c0803070507140d1103070f020d0f0821090d021906110a030f06050d08090d03050c0a051006080c03060f130614060108 69
    0xb812140e86840e689640303a59404512940b8210343d01007544160240c450400c81e2010072615190140e50750b915000b141c01010750350b030701c1c81d10038124003500e102681d0100c1c0d80a014605580d00c160785058940c54005190380094248014810100b10a00004180e010108c1c4845000c4002d02500030001c803019010907407105801c40c95030810041c182c0041d0407502104102034041e20118042000352803c0c0700d08640029010b030a00401103012075400039003038002c5040d8031450103041c91136121f1014240e07940d41100541c20251700000400c644043d140103e04045602074100400d0300c19180c54202d501c1e522100300000001e80300c1d11900e25411840c0a518024141910840c601c25241c0d110030301a8060380951911607494070101078285841a001c0c1d568000124060300c042c00128500305540300e980f86a028049402e0010000d1804008078403000140e10290180c0405d9480410034100c0741001400b01d5040c00c031550000000c070f4518840e000418881026500640c01d02c80000b415081004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 83789344 1250 83788094 83788097
    0x5030606010206041502090411040b030604150807230907080906010819120c120302070209010503030712050a020708330408040b090d0f050106030b180703031407060f06060e01 77
    0xe0092000040da1440ba1890221144170010307264802000040c002d0b14950311429004103000c0f6001c00d004950364002d600401048608008182e11035011020f100141c0c4030750f5150b900507034820001900003440c0c5808180b54401c1c0c1001c1c0c4e41c299030015500040540c1d02d41c0006030524100401220704200741400741800c8002460031407001d80701c1d2440c0c12101c0b4401021404580b8071040b802e8056042d49440c00c0c1e0141d8103150361450810020b00a40218805038450581c00000044030b003070110480304826000038148040e644d9417403056409034883d5060070110300c540a0001080b400600440d005251034032a108400380c031000c854190140203030303581e400c40c084a809202c001941003048038112a03d9488254660811000003000e00310710503006448030680310010000c00006506c000180d0303116903084801c680398480b8a04080040320720401c1c2607440620281b01281c000c0341000085980700d0011803131302c0440d43c5e0b88410380382000d8620840c6500d5942c01d2000503081030340588444020b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 83790594 1250 83789344 83789353
    0x903070b0a1a0f01030f0f150f0302150912010204060c061406181806090a0311120403110a080d02010605240706020a030605030d020f01050a05040f0201030507180f050306060102 78
    0x11181c18441d80305141001c2c0b80f14140c8684800d2859000350409a81c000d00c0203004c22000c411020400c028064202e2440d60000785030031f01140108118080b00103403a0042d1000c103103e4103115100400f0380c000382c2c1c61540550707094099003042c0c1d0240010005814070381c0c0e8103028280149010001d5030015401c40d001c8104c0881040080d44031090f030b012582d101e4166220158590039200f41c0d9803c1c1c006e45a40c8940500740c03c008803090001a05124203209030b803150845500201d07519100c2a44100d1030a0600701000200003041c25060b012007403c00007050307800d007a0747c1d03100054a008c244a03001c0001d41d44a610401680c5056542d081482c4052031f450071020604554100080c451160000e143d20342c00718124581c9442640410040c100141c110381c40000000b0010390307160480c003c4442d00750700b803100058800c20f40303002d083d0007186d0140c1610320b0074080303a0064010b400300170001307410050f62201c0301d11014107640c200401401000303036940100f0304010a1604155000b0f184a066620 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 83791844 1250 83790594 83790611
    0x70507150b06030a2705060f0f070801140604050d140607080135030307051c09080901230d020901090902030408090d0c09050c04050102010e010e0d1206030602030903070b0a 76
    0x1200b00480b940041400c0000031102c000010302580344e081406140200c00d840340104040220025005002d0b4110901b00d0038160f90792155480700690032583d41c070004a850004000307000380143d5a011600c40180018240f40d1210003180c0c41c95014042074407042e5110f0f60040761000d0074041e07107402c001680750400c0c8540c1000b0203c1040b50410017245164165103525060641c9801c000403001200d200550f6902c0c180900c00070084d801c010700403010100d20b03100d8040020301c0b62003602003003070340300182908210802006490791071081400c6050220720545101102002000405505070a450010b8440e46031800050101005401c16426244100103001c0400c114005072010404119201481241c152600700c4000c2c0755588075029090074003041c010181c0c0c10401a00645000380d00030003400070950f030401d003a1021000b440e1110382000504c0000c1c03911411201032044014031000c50156541e980316000c036403080300e03105442e0300f000c1410810403013500151030304891040b40a01c007000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 83793094 1250 83791844 83791849
    0x1140108060a170a060515120d0906211506090506030f0a110d050c041703030708010308180d08030610140a1d192405032d070507150b 59
    0x10700d0080310f915419a162048808104103c00411140d000e4418092810041d0301c480f40e50180607041449146510341c60201500c0005419001415aa0701c003040c00340f92030001c0c1c0b10341e04054240701c10841d40106c0803001c0c501d2800744c05122106601240c4040d882c204004207000d0280d0020b074841e440170418840301001001c6803a800021800000a83c58190f00076462280b2603107a0075400381d03080500304507404048a020744101c0d800140c1c05000305000070402601d030b200c1158490702081d40c410051001c07441302c0c400b400301c1c1004803403448480940c0000042d80c4103103818045800e46000810404907040013144855150360600300741c03014800b4a18144c5860154001071800c005542c0b8405403110b01c175103c1129105070140c000200d09801e180c682c0e449403079502454501200854030300181d005141d482d104026102d55038030b801d54030340c90000d0002421120714043c03582681880345400021081c035250150f4469207800b81e44440c0d6140540d0004090241100001c1c5440980d20a58 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 83794344 1250 83793094 83793109
    0x6060207050423180d050307170403020f0f010f1104030c06030f020d060801090c080c0a09180206030c0a080a09020607030804020103060902181906021c260114010806 73
    0x503801190042507102e00d15089403c0c2e00c3d00d450f030290f030401c008002d0143d842c4c4030401c4d034201001024140c407014005e08400703940c41d12042d1040701c000303420305084100c003031b44890310280c02a200c1d00c1a40c002c40b480e2038003030346004030017100e60055941d20701d0241c440388400d10400601114940180b03042901d1500d13860030b603912610400007450f40b0b5010910148070703107074102c0d1680d40844108201d01c40d10703003217a98004c103510039088de00c03c6505d10001c00c5007640082d00c07010030103009101c0c0b041d01d4204480100a1304c04245011517800c2c85545c0d110040c2d460201662007034085a40321a00c4442507070000305421800b41134800218580740209002d40c45100450780b0302501800c121070b40351100d1004900a000c0d0b5400f83c1c500e070303102241447c00040b8980296440d544100c4801e5540400c60154840e64034151140b00096401055400c50300c0d404001c2c1c1c23410352030301401d00c2c030807501e251803000d0542500d59104184c0b00031900c005010462608000040f101c0d000e1900080e10310305a40440c18070f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 83795594 1250 83794344 83794349
    0x15040b010e0c0909070e030f010626010f020d0212070c0201050403060507110a0b011508060a0e04050a05010e060612060906071d060403060c03061a120c04081506100306060207 77
    0x28400103000042070b2000c24030403526040070182091010b890408001006016181300c8a4403e01586801c146924014041d2609994070341c04096801c0092400d892401c1c1808134194040f5502d0721b20030003a0850714400740028142040300540d982c140c40b84441c9045800034044020310800410600142c3d90041c142c40c1500d03030100d40001c5076242c0200c1500d03008200100c8a51520450720040200407106801c03504a8101c031450342c0401c038000c00300350f0310b44108a0f038058220300409000c01a400254540700c1d04140900280d440380a1692105420b41d4180113902d00d866100105100440c184001040c0c0c0d00304a1002510450500c00e50a586030302c40038250f2410404054640800f5503208400e10340580c0c0000d2141ea56581c0d646000f03406491201c48001c0031a1400f8400503900b0703051000c407102001441c40340c1d858018040100c9400020190200741310041c28880442d2124040080e442300c0da004140403042403500e80100305030340c840080305600f09801d00b2810000150001421406d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 83796844 1250 83795594 83795609
    0x40501060906121a060d141501050d090602160b1005040c0c0f020105210604060605040e01060302070303090f050f12040521160b030a060501080103150e1005070f0215040b01 76
    0x2141c5060702006846258428000c1c4c5d40a200000c0141c50a051a80300300d00b0003000f12102119075a070760459021800702e6410a5010504c20409140341522943c01040c0b07040c4a104014102500600103500c11344d503148045a2425821040c4030b1000f02210900008110864080c031525601c6034004140c0180048004e2a000c40030a200c0216801281030390061040c0c00030040010845e03050340100400143d6589009519000002c1411fa00c42c100303c50030b85440d289880304036442c190080303000f907010b4003003a0304150f42c58118800180960401400c0540903100038025026050960b44c1400340b4030f48010310422080004102588511512150000c665000d1001e40b001005280e810f10465481e061038404d0031070307004204a41403030040c5004080c480420044d0030748420043d40c11080a00014004081c0c6c0c1690001c51704030742d001001d1a41b040300940342c07414800c0c41024181d407000d80d02c0102040304217121811032a0704220199061607a04000719444c10030f619280803036003060140e0803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 83798094 1250 83796844 83796851
    0x30c020904020d02040f0c090e0402090c0d1104060c0201181809030309050102070c0608102303031b100b0306190509240a0623060c07081b04050106090612 68
    0x107003556101c103107803040d0b0354020348240054081044441c00a00031208880c01103442400003080170403441c521188581d501404a880548486a000c1c41d103400440814400948980b0f22032109801c64000d40000c01d45901d494211000790300c009001030f240e0000c8495101c0310001e0411a100d000c81c0d003a04041d003285400500b841c45418202e01811a241d0094600c2d030001864900700483c40e001482140c085a60b00d1406480702d00c00d00d100000700c2d12800306441714003441e900ca9a00d102c2c00407140641c00404423890542020f0350301c1c00c9110004081d4a080e0041050490a260903008492400d041103007d044940761075006407903941304000c2910704007540c400c0004d6007400100410740c495071000f0482c01ca160a906804940c1c400c0494100310664100400000c0c881101911450352120900e0061609031034881404207a030415038810180384500080094400300034000850f69680c01d44d0480402c20042c070521056030010b038011000c004042030100103180d0300940c102c604148030381020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 83799344 1250 83798094 83798101
    0x1012050903071e03110609030d05100312030501140103022d040e10151704170f040e0a14010b0f0309010204030b0712051b040323060112110a03030c0209 67
    0x16441c6000d80b90005220f041c1e61685551080030031220201410300c25030b00c001c0e02c042000c0b02641c80b89000d80340162544c0c4203018202003140141c010704c0d80602d81441c1000034503583e40b12402d02c07600440460380032950f584014030000d240700c14410344001c02800e0039442c1160380340e600d11034109401a50050f103000000f5150100c0007100c1224020609c1144042c12810700101c501c0c031768002486400100d411a85811000e94003d5980380d100d00014040d000c10365540e5141d010000701c9801200e0401d2030200040c0c0f4800c2070410150014000d4540c40c14160328016142c2c0c0c04651a4045480468031100010001d490490040362614002c012425481e81c131507104480c007a001d143c000400d920101410055000d03480414450036906004084c0305c5629540c001c11344490050342e209028030000c02092010030f02e14885c181c241c203c107400459106400070100c904000c02038020303402c2d00441e80084070600c010404074020071007007201c030304035241c0c1307107542c058000d140300d5000031f00482541000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 83800594 1250 83799344 83799361
    0xa0306020c01060803070507080106061403010e0a0905030412020a0b0705060c07080d0204090c0e0d050d0c05071a0a090b09011b020607020a0306020c070e04020d0305031b0408011406101205 83
    0xf440081c903076042265201d0010303241176501d40f03500e80900e81066203800000912184144080b0b82d0300c0303080000300b51840c0d00301311001020740c3e0010040340c000d54417410f84900103081000140014540c003440405121080c2c41080f070819002d501c5141003403014405203020410201c0c203030f40c01a40610902e0b40e02e001d1840c1415060003401c41074964a4030120740052040d0a90300680d401907802d5944007501c0504004002074113905030000380040c0d010035404100140203542c9403038460300513412900078580d61110303020341098041c1c900e03d010001141e6048450342000094001c0c01a56054900381440307040001e1000000340c8460350f050742c1c802e040c0300954032040110b0305e00310b4010f0100401e050b02c0e820844080d5100b00c0c001075080c480c0c00d4000600140d01d850541c0190350041400d40500c88540f42241c5542001e0801c0e84205203040192101000d200d0050000381203071400032403000c104096100b404c0074000c011a000341c41c43d503003c4150a5104203600003c10118000060780d442c0e0808 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 83801844 1250 83800594 83800601
    0x303060f120106090b0a06030c020a0209220c030201022b050a091e06020f030a0c020411090303120f280f02090301060902070605070903032c0916030e0c0a0306020c01 73
    0x1003a811951800d01c0c0844d4460458000321900c220a94405060603503400b8101d080714807403103581c1e0040c1c10101c154001850589484d40d00600c0150b2989040c0d20310307142444002c0501d0b1800c803810f00c08003c0401c21541c041c880741c10441c4880020000302000c1c40420410718440030f0f8040100b00c40002c500003c0c82c0104481c070064201c01041700e40c041c145803450741d1084c01c41d02035107016100b110801d00d00044008210f400ba894180d68003071002d92180d080c00b0240c00c0e00c44d035060f40044148070303010b0700d03850801c05012207003848642020107042c005410901604080c200240562840100c11081081d01c904440c060794030520000305e051640385001c0003406410120b543c1942054400268040d00c2e401a288a078000c0d042040701b0384903c10f0681314010b00d8440100401c40522481c0c000c40b0301102d403066103031104d101d081c1034201400000358058204552030398052004485070340b00290315104000040f031200c40280150005a000a0440d0220b44030040503d17030001850a8408400c1d003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 83803094 1250 83801844 83801869
    0x717032203180503061509040507080d02060a0b030c01080c07020f0405090c0a0b0a090312030e0a0f110a03051c03090203030403060501030b0c04060c020103050a0207140601090e0f0303060f 83
    0x10049040300240303002040d40c03500c2101030303903003164403040440c46240105100f0f0150b0001000170a4200c100010300008001c01041a1100c0c010640e0009003040c0501401c2c4404000d54040d1056250609510341101e00c0703400141d00a901c030303030700d2206a640c00c8000c15400c40004400142ca030449880011510b004040605410038241030501248200c0080e917003a401c0012120b0440e103d4407200c1000c1e05018040050b00042d0482500b0070110b41e5101075102c031404249808a180c0840030842c80c43d2145403903003142d400c0c42884100060003840d01030807100080c11507036214501c2c95902c940741c0d00e0032110381d0300ea50700e4201c000b40000c26000340d010050184e8050241c0307071656981d080c00801003409100503540030803920002240000500c2c03c54042e200b107910f4081c1c00c0d451640046004000042001040750360800080c008940b21b00414182d02508a0042200d581003040c4503050341c2c0d00010001c0c899200356101c01001c140801904d40c0708405580ca19142e0000c8070000752240e40c502c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 83804344 1250 83803094 83803141
    0x108040f150605120102030f040201050a050408031305040e010212010b03090f070e0618071b060204050301020313050d0504060516080405060d0c0f11060403030c02030f0a03020d05060402071703 85
    0x502800707010039101d40000b0704849003201c10240140280c4441401c3c0d2100315014078034801140f00180044d0b000c3c0700904044512880c200c4d00b820789902d6000d01e0f43d4008403070b8121f900e8544c1008c01c01464140920f003c080e141200940c10b101d010030844140c068180695a0208000b0002a41c000c000300404c1050350108821286070568584421005020954080d8080c400c805410b80001003040c64140c040d2070543e0f90000480307008039900040d00c0c0000c03412104942c08100001c2c090390240040c6004800c0580148018461494200d15000c4070001c40018000103000812855400c0410742d0303090500300d5442070400d07465240c11409440780390440303980305030f010401200d0b5130402d41c020154100c040c0c072542c441c03200d02c003003d5640301e801104547c041d501080000d00081d100380c0001042c0d4040740112400c10800d0150840c41ea0010303000c0c03400090b030202d02c013498284039014494002e10181c60031441c1c0005503c40c14210400d89200c100b0f1404d0000102d0b111088502441035420f444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 83805594 1250 83804344 83804363
    0x20a05030f070e04090b2406040e060a1214010606020d02120d24090e010902090612071a0a02070e0603031204080d020708070201030b1f030b060904020a03150803070507050108040f 79
    0x8924085a080c83c4c21f98082c50030000500205640307800c50703020170300050001495030b42098900900c08891131802041650800c1c415003000502025114610070803500c0b900822a2080440401c14212003080e801b17a4219030068100717045998002c84c3d00d03500c4040382c402442c1d0740c10102d0521000381009c0e51000d80200e540e800003180c0c0100440200d010354600c01e409000c840484081542a41c0d150b000c081e5001121101240591a2503d2001c050f041d4020568001d90303582c02c0d2040b40b0465030400304104180000e06040c1d201c0d410b000c024090040c0c2480b518a80c100b16010a03500d00034114a403030481001c4001c9824030003507a06a8450300d1190100755520b034030074500308800e0f03003141d4401c82c0400d0901404007100d203403c0612910068100300003040d0309040b1081240074050a00c00342d600584200714000c4181c0305c0340020442c4d2002d90300c020030800030700c90056030a6402644000c40301e4209001c0200042c0010509c1d1003121424030700720525450700d00303040b07050210100001304541c90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 83806844 1250 83805594 83805611
    0x12030c03060118031e051903030f060504050108030403120908010c0c0b240f06090904060c0e030a0309180e0d0201050403020705010903020310020714030c0718020a05030f070e04 78
    0x1540001036109600a81c0c0f04407882002503250403800180340001050800c10036040700c1c2c3d00d1000d0321141ca006000d84201d524030382c00c00740e034081414460758040c0e00103a20760201c04030303108075402518000c1c00d084d0360801180d0700d440000c1c0c0d181c2c0030f680001041c1071500311a0404452142e00c80c00003074041c1d80001c102d0301c12001c80140c414910007608507200424003000614603a4184005100f02c1c47c00301031a8401141001004054039005001030b070b00c40d000780031100550300c810a10714800c621072440025004403411024141c0b0684002c0c56201e50701011068001035031020007501200d801c400a41c40a110462098010f840b4404240360588100c7c002c1da495075505401c038a0007180680c007921205515000111752040050102a4142d4400c20161140003001d600810801e4011075205012001c075500c03050071684212400801a407003c0000c0c00212140384a40004c03805c4a82c0851500031810700280807404010800c2040aa0b010001403101d03000b200440036a042c000c4c0b04104408 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 83808094 1250 83806844 83806861
    0x40503060115020607032702030106090c0c1502040510030b01021e15060907090308030a090b01030c0312020105060901060c051203010603060e0603070501090308130b040e0f060d0b010b0a021203 85
    0x10440010b480180300c1c00012403803e60007403040642064a000c00c034040000800b014492034120140700302c0c3c06640e00c40c800268030b1060312030b0341d0341000f850366407842c603840702d04103518101d00f0f59000c004075510410042199a035591000b0120310030030308010030501034600c0180d0a060110041030800c1400c21804031040c00c0218128583c055401280040e6403101c0091200b6858200c07440e9022800014040c4041100721000e50760011310603001190703074841d0b03541d440324074242030b80304555461103103c0900810944010b4801007541301c0c8003c000506e8554005041c620301840707a8810310880580d00e0041c0710b01804020318a546210f131907581c950b55100c00a00400d043e00c070740074051042c3c030049020b074600800d95404682050791f9800c292815500d8541c2d4903803124604200902c0920000a542d65105020704010907c1d842898260310744002e481c480d00300f005001d240318010b003052007030000f40343d1040c06056410364414503840311880f80c1c06034a400380031220014444800302c100560301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 83809344 1250 83808094 83808119
    0x60403080412110709020d060f03030207060206151c020f1e0102010b01050702370b0a03110705060106050a05161b06080903030604050411040e060f011406040512030405030601 77
    0x7036115207500200908100c00032204000140720200003600b125800304408070301d81e0058500308030302c244c0000d0000d65554250125488661080b80540c1110303100300700d0300b42c0600c4007a03484680b02240015803c1004001002d2070120507602c00504004550402551248150a030003200050508510304400c00320000001080300741c0ca600540c20704120103040c0d440340003618491680a00350a12070050200c86503e802c1440e40c142071110860b00c0100c803c200c5444014000702101c3c2c0c0b0080d40c40320000c8004051701e2118242401c10300c003c02130322002480002d01181110302c01d1601c5510f4010712002200c0030300c03d88208003100e0401900d00c42c10b0210744480008000c06460000c080c20307075109000c2d5001402202d940040707030814000a84181840d8224641c8148a00c0c03014200b40490000203040f83d40c4c80100028961011040181c1864085000380c09800b040e4050010350f5100300010749217101d140140c07030003200800c040826004040042d9005043c008050f5881984c541a56a401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 83810594 1250 83809344 83809351
    0x50a0e0402070f05060c0a02060f0601030b0d08040305010b0901060c02010e06090a090f180302061b0d060305030c010b01020f07050d020607060603080c0c04291206070201020702030c040c0801170f06040308 90
    0x4034043d9002003052000380c0c6c1c040303400d40c3d00290060607450f034446050714101c0c2070003000d050505444141c140001d90741c0d1407600c034141e13200f407015607211825400d0081c21161100c0700140101300d0000140074164001a4204c042d55091818031440011540419643e001e80ca6102d90040f8071100c0102d00301c942504150818000a0020030000480701203024015210840240160b080040032032a002c601c01c50325207003810311b00080f600d802103c015210032182c0c5540191501c0d0070100b030704041c0da0401c0c01400c80d4240c1c02d200600b48070440c4100035480740191322985100348200702d0718508645641c41a1001700e038025808011440c2c2e2420030700503a03400210b082c091805110031812507441c283c03042001000e0003103620031020100010101c80f2018220416a10407038902c0d402041c100104201881582d00d07a0000da120704d154810306161800803013500e4401c80c14002c03c0c25019900034101e07411a0301050718042c002207100c0c2210b00300140d10b6080c4541d802001c0801082c1a0001d0b1445e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 83811844 1250 83810594 83810603
    0xc01141c181b0506041a070b180c010f0203030a2007060608070b0f070308070e030a06150b0c030307050a051b0c09060f03060403030e07051908010c0f05070201050a0e0402070f 77
    0x9442c16103070000a2000518010190700040030b000074407040e02c10441e80c203174480450402c50325110b0a500c5500d0b00c00c0c81201c00f42c0c00d110b03a03220a40c4601c41d0070701000a4600d400c0c20300e0099071a074554060b48a0200030941c440300e84c0d9409000c8140040071300c14469040450502a94800c80c40c148403000d03000c0f43c0203078445880b0342c01000550181e0a021120703400303096403c1034184051598102c0b0f03814809050481000f1782c4001840582e0f03014012030f101d40d0302c40c50001800002200101d40d10500e40e034001078214605000c00850040c000c03044030751007021072030180d5840c01200816121800390300c010308900c41d00d4410080b2480380008505201d0708044454003115a10350007042040c280410920381c0542040c00030900107030090f00b0541c141d021202c1681c400585850201d4054629001a65084108a90100b000c03010038441d60640003214984120120030700e080160591140e480e00030304000340081c9803804030340300d50f9200b007004030028819580d900507070502656040050b04280c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 83812950 1106 83811844 83811863
    0x901180b0d06050f0105030d050702030601030b04020303120f09060a0207200f060a0e09060d030206040809130c030207030f090501090603020f0909270c01141c18 71
    0x40c07280c001309110702c1c03c541c0761500f003514000c082e000440a10400300580c3c00540c03408075038903042d41d401619900c41074403544040b03881d41c4036101604c0b003401c1600d01030040c4245940c0616000c2c454260850745107480e0103244000302d2241220040020f0742c0d00061110001c0c8000410461b141c0c0104203002c0d40680303171b010890540c0152054400203444800304801490950141c2c2d4200209903a00c45015803195406951b407580548050010100400e0b12401c41e41d408a00803040c0ca03072590700b40702913000343d14054040d4010703140440c081400030050710f00440c42900c4030002c0b120141d540c260443d1030040300744e001358040300e512140c2c41000c0100e04110344443d0795943c0511400d42002d0b0400d044005a80745540c411030b1444003c0d000501c03048016a84095807d00700c00038101003560307800c1c01648400008280e800c0c01e1951324141701100f43c55101c2112000304490080ca05503 = true := by decide +kernel

theorem cover : BRFrame.Cov 83633094 83812950 := by
  have h0 := BRFrame.cov_init 83633094
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83633094 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 83633094 ≤ n) (h2 : n < 83812950) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
