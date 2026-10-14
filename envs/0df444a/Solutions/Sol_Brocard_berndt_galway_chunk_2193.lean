-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2193
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:14.23027+00:00
-- url     : https://prove2.me/submissions/1010dd01-bc14-42f2-90f1-cd031cd6a228

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 394244604 ≤ n < 394424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 394245854 1250 394244604 394244629
    0x60111010e100f051302060913060b03070521040206180d0b04030c0b0c09061207030e01060305010f0c030e1c0516030c02012d080601120e15090712020d02040b 70
    0xc0b000680f20f10076122203822244050700480455609080e1200540e480c0303010794a5081080712490308a003844081d1a0050409610254a20310080200094550018050241e049080209000c1e03940c60390054820404100c0e13000750302c0300781408040760b40244224906440c11000e0902c1c40d101e0300c0c940300c00c222288100d03000c800054542244a080000212500c1e8000208481081c1070088210009034240030754051035003409561000104968440e4200004072843c1e44020000e8036120308001c0e01810010000c1c400d070600340229030030154071a2094090703065451028003070041080c191705c0e202025107412001000024404036040084a010041c80b00744251240c1050000e02c0c070015000260f4440c00c03602c2d04880c80c014a06060080010030381c856201e282c80760540d0b48200051754582d10281640502519018100bc1500350003d14400e1b041d01d2103148075250351701c44680c280d03030f44a54010300c12400c1b01c8803841d030011305080040400c550700c010008603609146001254540c8680c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 394247104 1250 394245854 394245883
    0xa1e08070e10080601140906280f0b09152223060a0804020f03190506010e090c01120906020922111303020603091203010f14010c020108060111010e 65
    0x340078000c90b408440754140083c00c0b1400075004a6161501100000c40189050b9004504140024415a84108038044e200400c1c00c01a451031f00c13480100c1c44a00d2190083d50b0715140307400c0e8081417270384014040d00d10056006000c810690441c02041c005908035807186c1c044491760f403103c8286c00b9160f103020300c098000801e501d81d03442040d0000000c09803181075243d000344420055a00301d40e0340104025071080c1c050321018140703160340c00407034075001c031264541c20700c0a0042c04070000c1004c003081140c1282e03c90107075a021911585030b200d80740c204090070940401e190a41e802121801c9070440b12031075018500060a1401240c085603003007151545c40d80c1000c6502d1442e00071034540e4407402800440c81c40d05182044101210303502c00b690280006032040101100042140f04108051848031042d8150142c03a0b5030f5604802c1c2c41c4218a000d041101c1d00e00c0c1c0011002d03548941e456030741e1250142e403007d1030b0781c89010040d100000401c007000441d5403241c445100921b4108418121240c51 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 394248354 1250 394247104 394247129
    0x806010206330a270b1509030a0b16030b030d091a0c0a030c030305070c020604090b1201021603020706030e0d0c06090203161a030c0702040b010207080a0b040209150a1e0807 76
    0x10000d0341c3e22071581c1e10b0920201c5494003444200c0c80d1a041d00c61b0b00041c404a922541e500008000a480c0c0000003d00420f20484102000032104002c2c2e9207001d603500e15201445103c10031401c26480300d00d0002c108000070301501040051314100e0b1401d0050b00d00b080c000c01d10b406c4100c1e40b49410f003c41c10b02d040d004281221201c00405d90b06100b4158843d0f80c44c604001c010000da030000e40184200d00c1103143c05600d40080082541d0f030001000b55034207403034008640e00c0c02070319800036001c21200800d41c0940160800014014001d00442200140c41b5001d02410140030200b0394043c0e0910b101070780c2aa5135001e00c140180c8041090062500c0c01c0d149040e8010707c1c00208041d10702c072804603040101014410310000000210544214942c1168041006002440103e1038072981758441100c81c414030a00c07405200540b9500c034003035030003500c03038481a55800f010b410320b40054194098020000000401c070013440101d00103154803601e1f0704400e00980c2c0d2074400d464020b150b049407040492 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 394249604 1250 394248354 394248389
    0x901170702010c08090109030c140309191a0705060f071403090601290909070c080a03051b0301080a15061d09010b030604081c0906050411010806010206330a 69
    0x30020b4003154003050405c0203103d0490700e940c009100c1c000002006021680c5040b0b090484030050041d50820310024012924428070030b81c0306940055a4429440e0b16011001d50808001d803500c01c0714000e940020040200352250400100a0381c401003251080004048e540000b80380c00000440c0903500d8900200300315410083d140b1000ca0500c0304400c027183c030125800610300c10150907103584550445045007640e448180645102c0c900d924001c00c17203d40011009a80345d0141d200a01a8050525140d9161070409110041748403c0c05503408a6000448a0340041c84d06841600c0e45400754001081440d0303120072510001c02900158a0106c0f610020000c05513000d115540401c1000c42c010091410151200c118600c0b4010000707015802d42004003070b9410058221004450784000100400c2c5403d00302007480b400d01d44807480c0021202ccc004241a50320000b4200d0150328043c0c1901c40c1000c081c40340340340300500c040e16080724280100030b1850a0390341805c640c004120b01254048143c1307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 394250854 1250 394249604 394249607
    0xb0903121902010606080112061a0a080303041a190c02120406170f0c0a050a050403021003020901030509060f01121a0411010f03060b0f0c0a0b0a0b030106050402041a0901170702010c 80
    0x1602c03a0041c104200d0248010051000111980004182c11440002b071480c1e100385e11001445a1640c0c05421683d81b8800103449600000103511030340c01002e10072800000c030440c10243c0b2006032030300f00d01d20101c4003668542d000c282c0e0082101040c20300454529102c101e000c00681d4220742d2000010071004908002e01111355014542e10103040110f000d42440d204807940c1c5a03025a00480e010800c010400d81070301c6001e0001c0f5009940c004020403100c234115103000300a5840400e1440c0000c0c1000040b8a60740340004c5e03601d02030b03c00c0304024005a0300f80f809641c1c034061000c2040e10315600054444100740100201d00d4081ca010f00f00401818440000240542d10f80034001c004052420b0005c1000380440700030342c2d0f48d0094080340540d807502c001c0b40841c0b40c007000321005418940b0a9050007071000303140c2c0c0846114501500240a81940c0b0f500300000c0740140c3c8548c1180c1c644d45e541c041d08940d081c100414814505040900d4090045490f00302c401c4030840e8a580941c1d5100401c01c0d182c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 394252104 1250 394250854 394250861
    0x70c1a07020a081b0913031404090603050304090e0307030c02010e0a0e0a0504060b4c09140609090109180506041a010f08031b0111130e060405100b090312190201 71
    0x44c032040e20482010300b00150450080c244d080c07005010014507003803040c82002e20800b140c00030320100c41c040c401d054980c01c00d16203d52092040c0130701c091400c80041c1d56501c000c02038569082c0c050f01e075405c0c04246038005554403100c5600066002c4c42d42c0ca001b28007006c4206150740190510540042c1c2e40c43d291600c1d01c110303000c8298062041d80c00303102088080c1254805880d05010004050a8000207010001c00124054640310103d544808600702d0890388442c050084440408419102c007009000380309151051030701080d0045100c100510a00f402600800240001c2c1c1c1054401034440c0c1c0ca6030380c20440c081d502106c600c0000a80800031742003000303405002d40035545881010500d020405a540d2180350070b00b050094030003010b980001020b42c460f00c000e420000603a40c2d140481001c0000c060403500584010171803481c04113406041a00c03807188101e00100842e1001410f008107484260130110403550315100300c0207620300c0c2d92495000341800020386180b038190280e4040001e401e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 394253354 1250 394252104 394252153
    0x112060510181a120604060e011e05040b0601030606140708040803070f2f0120010608070501080f0912070f0614062112090a0e101a070c1a07020a08 65
    0xd101060070301315221304042505034200f035010700c1c0054540b0302a0226130140070040051454078601e81d043d041d0403a5103811103032056104030400340c06959140c005404462150040303000045020352611109405440140851130041e12000d082c16502c90019146030b114180072241045d6003c680c20401106030700c44500c0b8926040c011b4840a40f81616400e00c80000da403a030704020444501280302020b03c3d1004583e4821840207104050300c80c08884d0b80d40005100381400a0104e2000030a504818042580214041409005590b51080d1401541d41141d0301c20385803890004480d42c005082807160f00080280d10311440440e1074104108820039880c1000f000880c0040b140c03020100e200816240c0f00300b5080c1014a84400c141c3c00441d511131180d410a010389007800081c010101e54004824045451000c800310001c071541c1500c14480c0111200181880d803000d500340100846005000032085004041c54285400c5030001485006e299000d40e000c0c1d00110396580e001a107000c2c58025 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 394254604 1250 394253354 394253359
    0x7080c03030304170c0114240a0515190201050a2307050c030d1e1529160614060102160b070c08060c0a170112060510181a 54
    0x1265009000420385a1000900c01888042407020802440c4503002c2500c60b5502c00f00300820002c400010300310710f02c1c04151803a1103908184d404000d00003580e80d0011018210260070790103041c1c81c003001c0c080742011580d10b00744289400e100340c0916205100024100040365400861a4105000c60030216038500e2500000c0380c0c4248144000115030b4103031290004010326151750395052002c841421409107103c0390304820b0a0100c5100140c04070310f15440d944440410400540409075103001c00b4a00620039403101608505420311200c4c9042c0d4015071610048060074078041242890070166400d10104680c001d640d0300240316040600d21501d07078407480c20700003004000c41c6040c0040d60100c441c480c0c0c41c0f12000c00100d03c01040840101d003c01000d00303c01700d488a080400c010300182e0450b01d50200000c010080201c09a845002524103c0704e80b603150798040009900c45201400c00184540405405103d002603082c0c0c20501c44148be0b120b480000035819592501c40780c01c100841146407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 394255854 1250 394254604 394254613
    0x16060b0f190f0b04030525091104030c09020a0f0509040f0e0d080c1c0b030f0303070c1205030f040b040201030e1c03060b03060a12030905040614131119090302210708 73
    0x18400119110981f9154907041c2640a84016000c0c0c0c5407035942284103000c0c200303a411031b070054121015105480c45107281c00942500d528003401240a888a944009245a0840d0b59000c0c0914018172480d0070280c80826503400041c208420385000c21440d03601540144506502070f5071081e000c03600301307804184c002d10f0030007402c007069103844500411420583d954509003040395020001c1b00c1341c1d80c2c0b829040c0c03030f140d107042003000c2c001281c480c1065644038155601120f105201e80210781c07046104160003051911180c03038803c151440200101d0506680d4806003c6180040000945000c0c040c80078550401c8000c90090039034610b581b08800694092040c08019900d0000785030917992601842c00408510342011118030120f03500164121f440d0101c00f00301c014145040f00701407042071b0b0308d1215050030030340103104980a800f210720354008d02340b00002d15412442c641084c504064a00110f2140c0c4a400107490595281c1250420110032003050509a1080c00584001e20055000c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 394257104 1250 394255854 394255859
    0x70605073002071a090d0c02030703081b1c1719020c10050108070e0105010c11130f0203100806011707260a05010b130216060b0f190f0b04 61
    0x50210703400c081d0441c45a00800141421045581522012030300041110300c0c100700800340280d00c0c5015602800240958910001c0c001c1c010928115403543c043c1c01000018950344a5050715001030001da04009000084201405020070542c0503c3c02030343c2408640003c149800303000c510051072000120201c40c02040f0424220a0207000741e008003e0025a41d00c07501c3c00101e00385042c1c88440c0394a01c5c83d000001c07400220015040c41130719003030b1014480c82c1e62210b0040d202d110344000c0c0100a4a4021200c084e0741c18059805252407104410110b848a61040d50380181e0308111100c0e0481102c1402c100725211080141d2801002d5464040300c8079203110010a45403011030040d0b80070110000d07441c1d0028204884428540701520040d24910035480c80c145010340009601d191060610800502c41c201007031080310500d03080751148440c00800369584001501913120255403140710304400c06101e44a40d000e042500d1415a02c0c0441c29040c0103403140e1402090308042c410b1003091006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 394258354 1250 394257104 394257137
    0x7050901092702041401030c08010507080603060403140f0f030f01240f0e0a0603050f06010509010e010804050c120d080a050f0414070f0b0406030608030a02030405151e07060507 78
    0x703090301d6840074800001c0740b4038004500540b07200c2c5131803a420f06440000000f0306c4101c5424805a51418000b44030315121410225403c4100f80c840b90b5040d0400c001182c0085c1c0104590008680d034240e60a0614201003c0b02c1d40b150498100c0e0090010000100100076607804e04850150010125018049805150701811049042018000c0c841c6564000b1010ba014440a60001d00c5c024041c0340003e4540d0720090242c0303000c1d078a8412005441c0e000c1921580507005032080310703006075201c44491a140b4011241d000010f001607071540508100c0e030040340c841b03d08030490700b55280e00415000d25a00300042107000000c0551400703c1c40c01003888040d81c11084025002904441030004200c9519001810a01c2c0e0350300c0402407042e8100f0006000d88600b01610407034000c1d0b00c1c2002415521302840381c481c8a69803507000103030801c01c014010b034900040742014000c4032040c098104a2071480002641000d540400f031400c0001c40c6042c10800c2c280101e07076200c2c01a15164071024050000d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 394259604 1250 394258354 394258391
    0xf0e03070f0f02150901230a030c1e0207030b010b03070806060702040e0a0506010f0501090e0106050a0c12050301090b060c070303030e0a02030313060206092e0204170705090109 78
    0xd0003004500444145400c0c40340d00031200e45030a4000f00041c44c000b240c0164400241e2140042034080740c000024480c451800541014106a4560701903140664000084005242c1c250b81c030b0081c001e121000c3e000e2000a400c43e4600c0d08200d400400425085050400049c03605902000b50702e0010810800e405501c03a40e02ca410650540744552108103610004024106510740030081c2d10500785540288200000c0c0345041303440c40d03404a2200d80d00c40c001121350041501503984001404401004418031810040c9808003091800546c501801c2d40c90031441404811040c000a80110043c0400b2a0502ca04d80702d29104a072000d00c1c10350139241140e165842c520018040c1a9609602c120850050012850090f40141507a03690340004081c0c044488845c00b4080c0144101c0c00040d940707410004001048429010101c0c49090300c0d102c18002e101c0e2082c0d40556003c0d007e200010306947e490b000c1e005254000000b0b0001642024284044040141e00040303800d828050071080c41d03014010b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 394260854 1250 394259604 394259617
    0xf06010b0406051c0c0903150603050303131e030f020d0f0c11030111070501020301150e010504030605060f040203040312050a020f0403110d0c0609081b010e0108070909020c030d0f0e03 81
    0x1002900c45810844c90180901e4403011215103030b092480c1d0b1960319a0080092090720300c00c03003c0000080380c0091030001c5950601000b06107034020000b00791500d141d00c0e040c03007800c3d100b00912840c3d90b00d13168055240307641e00c50701100454a20503040c683c10b81c041c400008528070516010032401b44c08240144000c5403444081c0401e100c5039000d4800d0f417400e4002411440349510050366488443c60042d000754801d04c66440224504000c003400140724180940b65003405a562034103003815525001d00900000c2c04003540480400d00780d21136900c450000c0d503c280d0091f190303450f900303007111080c000f5280020500840b2610412441c02010f02050030398007070320b40194003041404515404910940384146010344032909207100040c0c859404103620040c0d850300e90603900b501e09480c80d0b4050451241180c1d42c082038145400d40c405500c14000b03a80c0c01007452411145143e03542e0010030480c0e004091300d20280d000012460b104158034003e10001d4810403900f00214404a40031603120300401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 394262104 1250 394260854 394260857
    0x80610090f060503070803131d01151110050601082a0f090a09050702150402060a121404140d08150f1314010f080a020a03080a020a170703020f06010b0406 68
    0x1400040503a0055600c000054403018081700c55658489564035074a07007010311455600c60360000003064500300317007003242c09000c0305101c0f07201035900340103110610400110009080042592049105001c1003000104d0080100b0b070026907420060300050205070018015210010b00c46030585440c030707003400d01d40d100c0d0510614454840d1480702040501d403181380b180580c880402440030983c58996441700e4001c0402e1303002c0300c0003e0043c460f1101c860201320340203907001505200d078120040c0200e000351003460702030000141130101c03901c0405c0000e000340c80030b4943c104420722083c05035004000b41458442203090001d06031510401c011850300d0a1018a4003a0020340604100c03034403180d81c11081e05000313507028003944100c0042150204424410042e00540048002545403c081000c221154024101905450850315080a1540210340c10310451040c40074440201c3e9000c40007070460b0032422003040c0d49050b582802498407034410a0a001c1b50403103c010001e0030290f4041320304031030300b5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 394263354 1250 394262104 394262111
    0xc0703021f1508240c09041107061401050a06020a11100c08041706070903020105030411011404030f02040e01020a08040f03050d18060c03180609062c0708061009 71
    0xc07003504090040c840301d1001e000c07100d0801242c4600007003000800400d240c6800c8000c0c1c29101034840801030191108450b0300400c1025048504264002400c444c1c2451001c1d45451425614103040319003507040c11695020410044c002ca10340092203400601441c4018080040c03075444003c0c2008404d144c10744141c02a560204480c4c1c0108850061f15400001d0b02ea1500e0365040e09061000005081c40898051000091456401081e0b49070030f50380c06075115400d5981c5c3e5074640300009142c95140c1e0521448543d9000e269440704020000b5501c5401890480304540c4140130507160181c040c5140c41e40180b020400b01c5600085181c0d0040e040868040d2900e030381c2c1400c0c0c0e2148920048026502e04011044142c03a5002d040c449516114150030070200801420860803500b0702d8181c06c0c010038025180b800400c0d4581c0100701c103035014080c000f9100c1d00300240740d00441c1400c40b585001000ca4046019a503c0501500000740440405030a40346803121042d580c0710040d001301b8503580e54 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 394264604 1250 394263354 394263403
    0xa050306150d17070305030f010f0605030103110a080f07081e0c130f05070906080604062d090501260d052502040e061b090a06350604050c070302 64
    0x122201a80300c40443c414942c0c1c0e841c28181030042144d8001c40300242c1046c0200c00005120300181c0c82c800c11a012641d580d415a4210394803c000e1503001041a540460f01c04008155207000340401103050440100a00362185821001d5040c240810742210842c0d2000c01c01c0ca40324200802c030401d00c04000c54000f00041200c60540000b80074883c0d040703200f00d01d00310410643d2500600d8010940301e023038843c01c515a441004010940e41e19000f2202c260540d041f0100c2150b8500c1c0c0289401c100301000d401c9a1504c83e954403007201c0d4264410343c0051120030341d058200c461141d018000b80d10902c05081d4080395000051700b184101100707142e400300d0a800582c03041074000d45003039949a0080c814058912030380c0740d1741d9450700250703080c40403408402095200305080d0003c030b402d031302d00c098403a0840a1400c0c0b001c0e01d0004242485100030000305d483c402c00c9031411071805c0280d0315001800001420a141800308031040101000c01e1280c0c104000d002080e0005901071084044861904034020b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 394265854 1250 394264604 394264613
    0x1b040e031b030711061611030c0301020c0d0917060c090a0e040609060f0c0903020f04090503031312050903150c040b160605070c0b0a091a090c0a050306150d 69
    0x2003007080728184284145003104520402000500000f03004020007101102071108019051103a0744807904a41142c003425800103036241c081400d109001803d49806102c1c8a0102e0b00b03990000f0b00b1802d01d9080304410076640c5030008140c4c1e0103031003510f00c490810410040300d2642c0d80b00280010407000808a4200c0740c45d42d42500000c0505800d4241120608207460080080d00c00c0040c112005401c0881d46d45010b440d40c410b01c0c1305170b011561425081032454007844810080c0a103110780154035000c403040400c108000941c0108001044050003001a0800f20740b00c903c00380c41c83d010041c0c10010001169400100c40c1102c0901c0c85c4c3d00a61a103881141c0340041c0b00340d41c41140ca020700440e038800c61404c00b028240750540141e10a00150781c130194211621200070400620318543c0c8008101da41c0041e0340710920185c443e1000c081000342c24540e1510b524000c5400112a0303021049540140c00c2c86654540101020b900801e001c0c1491807401401c80d40b1001a00d004a1000c1d00b00000e01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 394267104 1250 394265854 394265857
    0xe010f0b03090106230102070905060f0607050f0102070f05060a060b27030607050d0f0606021e0c0a03080301081b030c010509010e0d0f021005040501080637090c021b040e03 76
    0x501166034800940405c00c1c500203090050b44241c940036006911001230110703035a0086a1040800410309941d0400c000100040764004500c15034644c1310355104d503e00c42c402440100075490040d0541d10885060340342c0685020740052074500a40c0c10b2210401100b00480c099415680c0a01401a8420741d400504003d00744218075080d4584241414841480c0d0464002c00045509000a12050002d180054141c80c00f610880c401640a1000305100c070100120140b542810031081d2000800800c0016070b9074003450b08142c43d9900c00100402c0040d804101042110071802d45030700c40300c940840025110021801814144907001407156056886100305450125000308031080b010381500740b0407a000300c12a003c900a04800c0c000c41201c0f40500261000c84205940c0c0c500d8581d01d003010711400010403443c51040e00001c09034051003406944010703080c035042414503a0241c1c0780600c94429940025100e0302550404040f003004840980e1008800080c203076004100001c0c21016685513 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 394268354 1250 394267104 394267109
    0x2100e0102072a120f061a031615080c22050418030f0e062b14090a0303020f09090901050604060f050a0b03070207150906020c101209050f030a09030203070e010f0b03090106 76
    0x10300e21f4420004180ba00484241141c2c84090741261010003480030703449a0310000d80203c411800402c0518080103100d0025141c0c00302d482d01d00c0a00381a1400e0308005112007202600d05a161064010301040c2850711480c003102e103403822108007040d0a9140507060180802c4080204010302c1702401c0e003a2520300c00c42c0c07400c2004031089070003800354048092000d1500f0200c0c00e03240341800b45118000268001241c01506920f01601840441d6a001e8001354841c44103205070140c1804009142d0740d40c103d40521031034001001103032914080e42000b0440e580d82e000b05070210400d48082c00305881e84503d031410307101c100340460743c0c0391103515040c0e26002c066804a5480503808802503041544101c9640441d0700a8084500170300e5041c0401901c082d10741096000138492180c0c0060341c510741e0300700d61055400f41c0c0540d8000c5ca1002c032101c0c00d590249034100003003212001d040085050402419000f003c00c000700700140c0d41011890b0032100014880c0b11113007507010020803003108003035010000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 394269604 1250 394268354 394268363
    0x612030903100e0d021c110106050607060207140115060311070c080d0801081524060310030506011d070c030e090708090c10050a05070302100e0102072a120f 69
    0x107a6507040710b207070080c19a000c16110280280000c2e00d0307040d4000500f0348000003892244e901e085100c0003089801c580c8400803488550740300e0b80005050745810340141070f040c0c05000f002d030340c0309698240656055820780c29000644c0c58016445200411040003509580c024035003c03804056000d5800154050f4140240c500a0035840004004800148001c0b0002c1c1d40c0e2211781d082c1e0f903603540d881c3e00d8001d03000100048840d9500055000c400c2a44100195070465000c80e4881e8040c4c008241241c000301c50785103000041c800c0074001d020041209600600d07a031022800c0075500040e06010240001e0680c409100e418200002018042c03c940d100302200030f0070250841c549240c0050a000c0151640704d075a0060240f030040c24149a0803070100403203541c50702442c05100c1d600440303150340101000e808501482c0043d0000305184d00a02c46103445810000d61181c4203410641c0c1e401e0305092a604108512440300b03480503521082d840101d5600b20400034a00000e0700341200109803c980c001c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 394270854 1250 394269604 394269613
    0x2040801020a0c15020c0d0e011106010e0105030111070807032d02010914060702150a0b0603010b0d0c0503150405071103071b051017060303091305190501030b0612030903 75
    0x8403180c1c0c4a61440d402501452000c4030344ea640b030541008911940c00030701c00e20b13007151441010890003000f0180d5071001c10314020249181038076000341001710a80003111012070380801000185030034003441c4080d1030810030040c07400e800396480105c14814108020284801c00c0e422046103149001e00b02c09200d2041d005407031b0030104480003402408081421141201d9081c2c0503140d8040010b41903201d11030503002407805c01074014691040844c01411401880d07211100b00c5202d880d24070245009084c1803440360740f160158541102a9040c5486003401c0020610822503640104981880081800c0d1800520703a210244212541c1c4c048241e12495840009a440204500c0b070342c0001240880a400041c242d0319041044000fa0070f258130440000d41c518298990084810b4900d41c102c600102100c0c07410386001e011030b49007681031480304c065998170720030820f20401d0a5070310407000c441d0945c06c200c5503045580b0310300d41d090040c05030350041d1314450b42100b002c04100304603040f07100010102c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 394272104 1250 394270854 394270867
    0x601060207080c042003070201060504231b1e070b0c160303090201121a03010b031b0618090f01061202070f080705070906140f041103011a0f04030308070825030f0204080102 76
    0x289c044c080e41e108050040b0300d000201d14480010302c5560f040c070072004a04009035210240c00802d110311100300103540c910200942100070303080c0d051850b80850a005441d813240c5c01414804d030042c0009007000740400701000300f000001c0300910542d6010303901d03043c000340300000b60004865094413105803000e000e10f0319980c01c03410034070310004c2440100110000e101d000c407800b0603d6260100404141c16083c415120f1100500d80030005d4803001407070000319518500c50000090144074280c881d903445440794001445610740c0890a2000444041010b42c58842c2d41e0f0b41d000101d0082c0712014002540c04a42d0000304182800f000b0010102003005000254a9000380b4560b00c0600c0d644500c41c045100380703034140341028040d03400c100d0a401042070850303281c09030742238132850800240c0601c08010040000c0304200c910282c07000c1c500942d11000c2c14900304401a00c000d0015140c44c90402d40a01c0f6070250111000c09101146003a280c042540740070f01000d8001f130302464200848550011503103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 394273354 1250 394272104 394272107
    0x30c0501090b270706021f02120f0403080108060606030708041a0405010b01090501030b0607080c070803270f09070f020304121b0501050c0705090402010e060a110601060207080c04200307 82
    0x1c0e0740c1808402d07007043c0210500412455a280420302c00c640250304a00490f8910708040302e000046110030020152030726802458101d5400c4040310030341c4000440300b00f84814590f1006a190251508030b000301064141900090303098000105070070200001c1c0d0740060304010089140300c040740700b04040350585040a10305a4041c08402d46820b0003d880c04400154542c444c0c001c0d03625200c000741606203040c1d041c0d100c01c404d5600c090241400d0303100307048000a115204000500040350b620480c8400d50050017211202180c100d0141f0744103040100c0081c42c0f581d1003244d4940c01c050507040030f54440e24290b0085c1e0650107194001803210180f100c0351030030712607441544c804281c840c070403180344e0b42c1d10707480103540c0e42c0521a401d070050b601480b402e10040c201506019002401418030130b044215980c0020003a9000080c4000001c2900c818030300d900b6001c00c04036003d000a4005890b80609044000342da40c5072002800d442a0380b03840701c1c203600c5215607074800f8007203540381446603483c03519400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 394274604 1250 394273354 394273381
    0x1505070b09150a060b090402070813060309050706050304020603060904240e0708070812031905180606150d09020d140318010903020105030a09140f0706200a030c0501090b 75
    0x410a106400900020b541d501513110f180e05403607104003024200b00b003400601c03000b50021103040350f16080420500c00820150b00a16004090f9654085900380340c0307250040c10000170b5441172080c84001d10034800140e65400c01d580d4030210036110441c1c16651070601c004e507404507052240010844c11000d0800c11060b0300000001500c0340d044030741c0980c4c0c0340445039544006100d8101660024100940c030300c0b08580085030400d00758010010400202915181281c800781c40d559001c1ca5403000d0000354903414000e55510010817a4404016042030425014510030b161442c41555900c1403c4d004543d12410100a0380740c03c05030f011210000c40040ca07640b640003170811060000591340580e031540c802c030313072a01c1900c0d4180d459504584482106501a0100b04070491300c45e40d5050b1808200c010800803da040740585004040b01c42c0b401e40d014040300a00080355090040c1d490b0030f10019580041c80059883c0d0502c1d1420710249142842c900400c0c201500078419503100c1c041c4a5130484110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 394275854 1250 394274604 394274623
    0x1506090c020601050f010f12060803040f03140601060e040b1c0804031716111f020304060f08040515040f0f031706061317150c03041110091505070b09 66
    0xc080b60880e07600c5904101d41c1801140d401e81c0015120000421300340d01c590b4200340101d0201102051075507ca4031124207580203900300054a005a900c02c206010303c203840c0200b0543e4090141c10783e54149a4014a1030030044002401030b034840e0304c000e0f039507141d01008000a80b00c6074903d503001c0314545490b903881c0d48584401c0d520500404820711101c0d079000e044444010090480c1103140d8259550900100000c20001381d100c50300308460341e09000181e0b1a0020b1100b00c0d07016695803401e000028001c0b002c0c3d04070210411801504100001d9000130300d52800c8072552000d406113907500c0c90600b00c1e0050303c440c01071075081d90790451000c041d000a80c1c150359490740407500f5038550b900e8080c0f003958094040d0759604645290340c10080094a0200030a21611520540d9001201701e101c0e0483ca541c152602d02811400204020900072107141001c00705034100d41c0342e104000c8403c402800408103025940d489880b10b40b92100d501d02800449a511394007034080d0310f003862718960300c2e51105c9810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 394277104 1250 394275854 394275857
    0x90706031e020f1216120c09080307060609050702190609020f150d05010e090604020118120308090607170c0f07020d061406010503011226030f0115030203040c09091506090c 76
    0xe0100340c111035907040c4005d001e003450b61801c518402a00340c0b403014140150703000090002081c00403500310313000d00003480414081c2c1001308025152205280854000525000840d008150300480141001034051002900020003295a0800d400000d0a40d08038600080d4059064101e610740d502d18203010301403140341307000b04110aa903150b01390007540320700f01c92400d12608030fa40007500544c003420a506d0649022020940c81c07030f8071144400703180e59900c01e0503404901c0c49030400042d4402081015441003aa01d801c05c1c1003d0242c8100a080130090b001c3c1c460041c02107280040d00c9512010717120540c0c3c0003441000c0b4960702f820b00000a02009000803181410640019003c2d40580222412119034042c00c060ac0380194071030b43e21609024048511280600c1551800c903005c1c0300145001c0d00c460501100740d03500d081281c0c851440901e80584c2031500600400c000308581e070a0342c0080390389820000c11380181034a0003940810000c20030500042c80d10300e0105002007140d21050740070903207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 394278354 1250 394277104 394277137
    0x5011203020106120b0a0c030908033405040312030905010204030c0e07090305030f071505010617010f0b090d03180b0901110304030206031314120702010f0503090706031e020f 77
    0x10390045800200004c2406441c15000202003881c4005030b50081410044624001840900c2c0b562003961540c001c5d02c850900c4501d9030810310680454100081140d840c07180030202050041001030220f015521002d003c0340420084180c01c18003d4009da040e03580d004000315681ca4a80c130340482600054020844804c000e1800500802d008004d9001501d82100042d414900e54103501c5440d0341c001d600480750309105030340c1d1401844103400b580707018100742c0d00c1d03040d042e451246c103110388180c059110741480c6510f000c00b0407000b0341e801c048400d1810700761483c503618070322828140c60900000f0040704091034004070002d16154810041d041c0d0340c20984e1005c0010134a40682540e81c000d0b4000030350300440400c00b1402c1920b5505085a00511800d10340360f2400340026254180b081041c0c1980100c800095084210740c1e03c801041a2089282030041c00c50400c00115a0b48500c2c6005640501d41d0713994401004040c0d851007003002d00041041595144480803169510b600306404002d00e01c143c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 394279604 1250 394278354 394278359
    0x9030a082208010b010e090601120f0902030c10050a0804021c110108060d0507050d0f0f030203030108060a05010608040f060623030f151f090c030506010e040b01021905070905011203020106 83
    0x7040c004d4900e001c005964126504089904202d24250040c010300d041c040b08002040e040c407030078041c000ca89041e4030702c001007044080c014141054000c2c16014402c40c203032408510165007050540e420903015242860190b0744502c01b254036402e074420011012041650440b04001c650545601e249000fa03880a001c0d4989105000c4082c0c0c2c1000000c00c580c00c030840501860404190541225024100d81d0701c406450307440395030b000f02d06140180c1c0160400001408000e0007000001d4014001800400140d850034900400c0c409000d0001803014071400c0758501400b00c1900140c02a01010120300500613001042c82041102c0b03156007802405441070480420401107103c942c0984403a000d18016618240d00710b5400c0a00d040d09030502e076048901148510107481014403821a82d00c00080504190001406480d14003803e00d20540c01c1020b20b912903680415504a8401d450b568000c00980b10700d091070030300b85590090054146003000000305020030030702030440c950090b0001c211b081e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 394280854 1250 394279604 394279619
    0x12230a02040b22020c0c040e0706030b0f1005090409060f06031509031e0203130e04060b030a020f1011300f0f390d091a09030a0822 58
    0xc25210500314a6504881111607041c0344d0000c1540c004050240c03030300400580c0029003107079041081d007540ca50040c00113001080d094030800c095107004480c4196100c0918000072600b00030801002c0c10410b000c0703805410303625a508500d9034264041c0c4240310302c0e0505500b00c0000c100c03911050f80c1c0c0c1085202c124004040510130b109a00f90507540d81c07884c22581d81890031010004001231001c61000b007020781c40c082c5201200b08041e00d1104084005400c2505004042c1d91082010340c3c400d41150900348016500c4500e13000c200c610580e5503004c082481c0388151448080e00043c02007501402c2003184d22842a5079903486a1100c4d11010b40145a00d200c10751050f009142200c8004402001600c910200d85400340046214140000e0004565059507101201d8603100c040e071041c41e22110410010b2091110350325000403443d00f03c0c0a2031070040d010a5822401e50001031500c000540440192070500141e0300c016008600c5598924190088521501114202d44504141041c000c101c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 394282104 1250 394280854 394280869
    0x13050603151006030b03070902030406021b010c1d010912050c1815130f1514060705060609040501020c1e06010e06030606010809101113050a0e0112230a02040b 70
    0x102c201c060441c40c0315082050030b4004114854030581c1c5031103031081c00545450307607000451065105a41c00360301c500060000b003000030020b00c10722006034144000100520f9000010203000b94a400000100981280c0144c82c0d035200c580000816401015550041c080001011a00124140c0d103054020341c6490600504801c1540d803440810212501c280382441e041c0b201003e00f1400003800030b0b21104011003c4216520404d80d490b5a951608080009048032954030400c54001d0b68841c0c40e0100303554030280c403410010300c80c6114410040114013805400d5040d1161071220000320381c01e0001c4140c002a4100011816400b940b241000114201c0b000d600b10501940015006127100d8440d44010340d031144000304a44d0140c4640c02c2ca1f01a050824001c600d010510402016525000c51901d64a62061904842d0148400038820442e41014540b040c0c11281e4004ea1390080400ca0700c2c1070030710043e441aa5803000b455030310100702e041c400816010b01c07142c800c940030840e903485082800140b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 394283354 1250 394282104 394282111
    0xa11030709200706020f04030308040201090902030907091e0c080a0b040207020d230d051e0c0a080711060703200d0e13150306150b18010c030e1305060315 68
    0x10008203550082c1008a0000a410030611400016050203510360412140c0e810aa1055000078092030a0000355600321088401611800c2415460351910b80321180c1e039000140b00310001e84e0b540b081e0101050002060001031804a00b0051020004101000302131000c160b8080031864071342000d4035802d00c0e0070301c02c44131200d5010b8680e0300c041c09540c540d00c3d070300c0c00207010742c80240b4a0315008110403101846500c10802d01a120280c03190a241c1c0070108507420741100b58503104042046400300f090016100203003030341c02060640e9038001d91034002042d0030039034100c0b81c002c1d1012500b8401c02da00710b815070f080400041131001001e030300d40381404c3e51005109860804940c0783e0b10192490b09100c904502481c648040104001814980304070418100780e00c16500c607903075040442404440c40c2c003d1002458403124031810301d0449105040364841c241c8800b810b0024130056801098090342c510888010014903150003071914400d91000f0b050308441c80791190154031403003401c2e14101d5002900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 394284604 1250 394283354 394283381
    0xf0c1b0b040b0402010e090a06061214060d0503070605070c060c02030937030b0601030c08090705010f140a02010f1506051902010e0d020703030e0f060a03050a0e0a11030709 76
    0x180d40d00c0e191074040e640400a0001e85c10041c04a0034026152940104940282044000042e0b002d2410301c0090645141540031403075035050204001074119400b11480d00000120b4003115140c0f9285411881e501c140340c3c005000f1400c00003000b0080c0d400070b04130381103540585028803031081901000c90300d82c402c8140c1c141d8464014401c244d440d0021580f0345802c4403a048107032040c140e9848038090302508590044550010f41020400556414045e401000c0e0b170500744802c241c1010404981c882c10309000d071604000716541d02450389032240d50103075241e001c14034035a036594042c0da034024083c0140c40c0c4030341d0350b450404c484038620510440c40c83d41113403090341d902800c1078030748081a00c4a0081500140440d074844107032800b010414480107281032040d400402c456841c6185c05002c03224081015846810031000d03540311501d61100319001039007646070000b035641d00ea50500c0003c00c4041d404007528071030114010b040240700d052525003402d007142200e51441d0345410240c26101e11029082 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 394285854 1250 394284604 394284623
    0x15020d090c0e070e060c1902030c04090b04020f09070525140a020901150e060f1e071509080d0e12040801200304020a0308030403020a020d11010807021203060d0f05010f0c1b 76
    0x41c7da65a41d20000c1126100500340e82206203840b0000b811b07034202c0326040c2d8281c0c03000b10a100441c500042d08a010351420f550101c0c00d03251001c4080e0007401204401c00c40642c10b1109165a01040e800b000c0c450f03039100281c0f05a0b0711944540301c1e650503c0c084224042c681140c000300b80201e10840b9145107990683c0d0f2510046000d90501c03119421120f01c50720818800c1c0b1038012404c503030380090b80e00c094650520f692600075600300500c07400094a4506810380c036140c1e009012840b031404a40060310078480c00f191090046c4505407412031360881c61074464401150214120300103410680180c2010030f507440c804001851501100c1c4402d55000354421010041000000c042502843c0c0c003c1c00780c0140c5407401883d8000c50403400300702000726035a03030040c10b00c0d03c0550380044090f500400507100900041f1491940c0710700794880509003030700c192090318502c81040301524001c0447d50384007000b480505c140c00b072004094001e610301040450400b1460400d1884020144d5406c182c1142e20034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 394287104 1250 394285854 394285873
    0x405120622020102010f0c03021e16060203280b01030c02011b0f02030c030a0302090117070c15200d05070203030f04171909030303051315020d090c0e070e060c 70
    0x70201600c1c41203003241913540301c0c085600c401455204440e2020350380c0d18050380e240c90704030000007200780050103e106200188443c14400d40200d040400c080d601c0140103030f03251149080c4400c03524825880b44200003060b00030124402141d00001c00045083e02c1c1800b8089054000307034245e4495030803485603c12034550203003403584964007107a000c0f400740c01603a01d0700380034898041c1190302110100000c690006010686035a00001e8428031032406584182d140c1040400100b6001c03007980d000d04050321054661001214a6020b44002c104003d00a1307201c0d55050070244254124601c0e10302158500400107032154008400c40b4422443e6212054681e6140d5480d1301404000c0d10b18081480c0c000d205114214207000b40902c007013000c98071b0702d2801c6803035031400900762a801000d1480c0707501103105903030029400d1019414139080310342025803908a0000310100800106a0151807041066000241401c201c001203004070003e80d5020701640f103000601031144a11000c0505590282009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 394288354 1250 394287104 394287151
    0xe060f06010c0212060f1b1801091809050d0305040206030c070c0f180e1906052d1503012a0c060c05181206010501081306020f04051206 60
    0x120380c400414102040c0102c155000f0440c0a900b40c0c013910f00720b03404841809a503400c1c5003810ba60210010720000700071100d0306c3c08a011802800c41060803607142e542c04088584c003a404200203400c0c021207800c1c4502a01c041007028000c501001e5443c1d003d641040382c00c0070707c40c0c0030306440b843c1c01a00840c03030740d01c03510082c409580c049842981c407511454404122034918008190003013056241c02c902400388070b4106412a51002c19031116580a1609000c46032680d42150031010f0304010001450b0b52041c1d80d203805070f024000180c1c4050f048a81c0a04e0350b1440c0c0c0c04850140e030300381e601c0b0807240d808642410300300c1310041c223039003400354030030f1108050311050094000c410180d034a0805400b035043d9859105617951480480041a008620740e1907819140e40d0458041d0b04c2210018007264803021540d46440d41030041d94100300d6103a002500503034600103d81c0700503500c90300440da1503a0040c883300454216005007482451081c020500326040001c2180c0aa80b0b40c403c0c464002c004920f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 394289604 1250 394288354 394288381
    0xa0b0f03060c0412080c0106060e030c03060709231306030506070203070c12050c120102041e031203050907030c030807020a0608041101051602090109240e1902070822090e06 76
    0x142200e5018017000041b40c00482800b4480092000e92203c14400340c0000030141080100c12020307000760f07c15070810034171a5014181008072035691141d90314009079500c1d0b51003a6240707403101a8114600f0b08210a0081090344080c0c12240910103a42c032a0700c411074121b03180d12461202070b1110310071510601c1840c031015600d04c18144141c08680800300f0106c0031030541c10148101e000030342d5010404120704140050000c00c1d140030907025010082c04c580e1303003641510384528540d04041e41c4c0c0c000a0080c81c010402840a140c10112032650281d0302e141801280e841401c04074010441e0b004006441c0b800b40d404140180e42c800401d82c07001c071160b401102d050300003155607110715448104242c05601d031519103502030b180050300464002c0c80b8107044055404569000007889041700d40c104000342c02045c0150708601c429003161261041031100d00003900540d403025006800002d121210300085082940d4280154054203010781c0c0d4a21524080750340400159809804c141e0004015041100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 394290854 1250 394289604 394289639
    0xc0a1508010f1431050f01080109020310020a230a020c0f1309052e05010b28051e03071101180201051b1501030b2a030405010905060a0b0f03060c04 65
    0x50f40240c0711341400b11401d4000c507402c46920409070781c3c4e011b000e096903600c04914050300303841009114003038540d40070a070b070b4406c4504105600c40c1e01082280b020fa1040500d50940807a070606503509064000010a107036001d0302c0348178090301c2201c0e08803180d8100814691100b9030000c0c415500d21080002c11009410b500c4001c84090061020b146040b4425022203408208171031218282c55100c00c8520f030440764180c00114800d8803e00c82c0c4501c8000301e001c442541c4541b1a0799016a5a1500c019200e42c0a0010001e181000c100900e4500c65280c9019601c22515540d03404018034016850380d080365001c0c0c86c2c0d50550b030f40010f968009940184020700c44141111800020000e100c0703802c50800540c4501c0c54807408103d401001840026480c150700000c01d41100c11500341145025843c02c1c3d045010b20002640110004040c08000c0d4080382000350800c0c195452b603d07101d49440c00420f9411050b500c101c80c5050900c816013030028070680700310148803c80d8a8142000c600816550252 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 394292104 1250 394290854 394290889
    0xe10150e03100e0f0c0a051e030a030507120c050303150a030204020403030905180105030312131208011a180607050f011a150313060e0c0a1508010f14 66
    0x80801620300e07102003100e004050b400900005000080418290620721a50240c900c181d011102d0303070201307984110313050048800440f11454001c24840d54012074079025890b05d41c1c50300448a80000b410b070490000e01e400c40c42030802c00c40342c044554040d0348103203204201a001d82c2c000c7c80080d110b8580181000c0e04800001c05440503903030360b42d0014041e6070098004400144900c01c0c10445030604890640444941450a0b001c560410001c65502e00560000000c3e490b51b03000441c444821040706240110f81215010308100031a80303016020340000e02c40c8200c41190143da4200401802c01036405440542d0510802c1e900807108000d5690090036082d5094050000e442508140c01d10a250122510040e0800301071445010032204035008070f000e048000c002c1081245a5944481c8842495400318002a04002c1641e01b6498464020116034200e5035030b10022803510842c40148580c030f250380d42c03a070180d030384c9038880c08030061250b125900b02405403a180d49000d01d003a500160241190 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 394293354 1250 394292104 394292117
    0x1210b0c16050709021206031c0e0d0f0506060f04020f0904051f080c01081b0904240b0d050a1404080f130b2a03070308060a05060a12060e1015 63
    0xd62100da090088607131280c03000643c0018203402942003102c0c0113600c103c00b10090001c10044420420362440314940701000c205400e6224501c40e60340050650344a40c21400002d4030200c00c0c54a15900c20307098468612501c02158000c0c820301e003500848403251040c0f80510304040308901400301070840904020003011520b0302d007080c100400c000100040c41000003d00041080e540054910038002d02518011318004003140701815400b0201c1c0c0b0074060a6030002440506940303405c0d90030101e014140031034100d410000412501460142c1840c0a04140800281d225101c02a007103071485840718055500318000180404e0621020701220f860140b103103858440d49040780082d080c1580c0003101c407120f0108007100e080050000d01c1c8840b103103140200002e824801242a80ca000340b110081c1001582c17000542161118410f1a00034103001d030009440d00a1190045d204a660800c4038001d2441c025002800d001d080719030900881c030003084448818202503092066111102219061255 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 394294604 1250 394293354 394293397
    0x14130801052403060f070e0f130605030c09091c050c1c02060a140a0b030703050a050c1203090f0103020a0314070e040606180b091c080301210b0c 64
    0x20700490344242c070b4000560502910400c40700802412401099000e58869001c00c5200704000b11401d801c4a1541003a1815000034000175201d081c100d000e09422100720805803010034202d400480c2a07450440695450350003000c14400c02c824111000d03001c0e41e1000c020400b00110390b0043c81d41b150014944a850044041e901528004403000010200010308004004155050100340d8028110030000d000d01014814050200e4102800740c120031580c8030010f00041d50108010b600855111064800400c82400c0007512810402042400342000c41d81c0314041820210803110f00c442e0091450460400d00d900440003508900210401e040d0b841010150540300088003920a4a05950702121010108144802d4400d61b52202c0140406151040c0c0b003401040b00030f40070360f078070b01c4566611a0318940000310710f050040c05280c000c121982d480710612031104025030584500680c01c0c2120300d10800425110042c040014013560043e00100b11254064401882d03503000d0781e00c16450915 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 394295854 1250 394294604 394294619
    0x91002071e0b0a0c110a14150405010506030f1c050a0314090a0203010b01030c091823010f0e0106080f04080903031b0105060109030f0303020c01020d090609030306080106061413 78
    0x301c8160203460040c154000c205a4903030030701483c5002c850307502c3c05d1003900655021030741e0b035100a0f07400107210200c0318103c294400300421050013640401d203001c4d4400e00309424454000c200a40782d40d4007a01070081902c2605400281101c008049881c1f0113201681400084030b881e00a0615a010152104a0598260411075689005400580261000304001d1042500b12800c1c0c1e608d441c180350802c50b00110280e0091228422110401d44001c50307203036622280070040000184031598411245070b01c80515402c2c1490034141d81c1c940000143d141c0d101e4000380d050b080240302d00400650907400061401742030b1071045030054840c1c403c880c14072028900003400c41e004501040c3c8540c10680007445e80300001d00696400100a0810300041c5041da01e804441b00b1000c45c014040c1a0005400ca4105034254100c484040810004025945851030601c0143c1a8244240e0002c1d050080215880d0810302c100d40403100262100c102400d51081ea01c400ca80001d9012510500542c50006510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 394297104 1250 394295854 394295903
    0xf040603200109151b050703030906080c071502070215040b0a03140c030c0c03040f0e01030204360609020603040b01170f12030a15030309060e010809100207 69
    0x11485550440000c80040d59518141a05503440c0342c104220384000700880003c480300440300010a01c3c160200010f0781c0300340c08010185c510010907a104015000050551010340d40c8141d0310303581d5072504581c56540260949008404014002c121314413840b03a2164543c1e8003d14403c0e102030607a229842c2e0405003140142c109130301075040404c0029000c8c1d00e0390791500c2010402c000300b4001700da02d410321842070300083c00f008002c80301c4002c00041c11405842d0802c107860050442d8056403c403191551980114207070300780f01c200d004a0a160421441140c1030350996000080c51502e800c0c0c00344e074000d40d4459881c0000c002e446950742e4440f07083c096100d0f40010b521a50046080842952405a14a00c0204130808524035070b04140000209060f010030652049161150450b890b42c0703075611684024142c0d800718035512240ca110000806412038213003030454400d034032403d003440700306401502c0e0410b0844003a10300ba040300c14001280b849550240881a0180b1000c003d0f40c280100c84070100c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 394298354 1250 394297104 394297109
    0x50102060c0304021c330f140106050912010507090e0c0c1b0406171c0c050c04050a0b0904051b04110423060a030e0d050708070f06020f0d060e06030d0903110f0406 72
    0x1080d13000303503101e2450403600038003505007c0e41000304a481c1841d600002d03090818040c00c020054000380c580119a101501c0c1c9404a41183c0200101d003040300000c0c2803103c01d440b4405940894000050f8048031724015214a602c00001400c80c1c00340d000140600d1591000c2c059034881e80e2003401181035024001d52a5034410030318010404405951104440040e6030301501007000101c40a02001910200d035407401d07400c00390303400b00d07103605c0700c1040c140513004601209420410f40d02c204003d0007030000d0b5180540d080c1d100200c60703002664040c4002d8031603d40346923085070001c000070450160a000c0c00c10719940c50050000103840d20f28002140303030b1311400d000307000291035034540340103030006100301c15082c17041307040041c0b50441a59540f443d034007440b8405080c141083c4504014442150112a0320701b02c03a0480941c0c41d040181410000d21f1940500c510340204840010264140000c0c8001a500943c40d119800751941d41d44010912503010710980068038100c0c011080d482c2c50241402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 394299604 1250 394298354 394298423
    0x7060306031b0b0f070c030602030c281704080403170d050a1a060c010605060406031a04090317070309020306040c03050c0906011b0c0e040507050102060c0304021c 72
    0x1403092650900e1000040c0301007180c450044145000c201c0030341c0003421a41c4a9040218894803001742d0b00f00320741c20840f280c0c00030303106c80c0c000401c00c0107040824000f812075008020160280f2002c00709020b42c0c003005162355101283c0a42c0003465244249410143c0c0940b203082640e02d4941c50b036035580340701a14150100034190002c20909001c801a001c0c50f94021004802002107061041018003c0c990aa1a80c2d016540000e10201488406e400c100064080a0b00740d56541c1da07240c1300100180b580742210740000008100807100c0d464a030182d0300c1e0103a0165180443d1152928031001303424000b42c1008141a554041c140050310107010342440b070390041841c80c0c092869400c2c4a424003180b2180184a00748107400c000c0076a0304100301c6001d01c0b0f084002c042c1c0c032031054680081a5003094100c403594014007410001001070002e01174017500d00a03420380e01c0315115400083d8080c0816075000303600003101241c1c4580c510940f07082490480c00b4034802413082000011281411025191222 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 394300854 1250 394299604 394299611
    0x60303080c03090705060901111209041a21031215040b0d240f1a03070602030403080d0b06070b310c030b060a0b040e04031d03030315060c070603 64
    0x185600401169030160214508625510f800450340f91560880e02550348940000314038480703164420925070130507100310710403150b61908104a5200c141c00520f091442203007040120481c444800039001418440074008400c03411804800d240c400b106071032500c0d071a1100340100c48080134444a140d01610100100c41010070f500c0003800145c40000c00b80d0350042000c1b6107030400090000c031511782c1c43e2040400d902c4101000d08428070240100d0490000800e09011000401400d055661526030000710304440b1000d0b80d40c07405a0b264019440040c0111034140701c000050341e21600f211410400040882d841c1010a5880b40c1c01c880342a20070180c5c40c12070000101595035050070800b004000d81e042d4204001d00c644d2707010440e8500d0300009050702412030100f80c1035280c9082440240044000c1d4a48036a00c0d507214820880084505a001503000c0030120911856401041c4d041030000e0702644c51550b03a810340b2000d03c00560301c802d4100c801004005940d40f414040003015000e1954040b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 394302104 1250 394300854 394300859
    0x11032a030a12050a11030703111b030301090507090503030a030f0605091305070b04150c020a0806041a130c0909020a0306050117120909070c031106160305070e0307050d0606150306 79
    0xc02c01c4403401000031540d05c0c40c1c0000704140003200000e895001d12036240120b02403800940584260140c08010410b0010400180812800210285040e10b500031010403c40c0da40110884140c0c815104140e09504104121024140f10390003660f00003d00c0e00000c04d905540704041581440100c0d42504940400e07003030001081021b018036001460b0b40d1902c00d05050601e1800c621070a6030410034801d10030b00b00012011515803104a40041401c081507620303914044c20f0055000a4028408600b1240c5000051001e4000b0303018044960700500c000c1003950810920000034044600180c2c1c0c0400c06020002c0001d409015540c040c21024664213000c22407900b0031072916201d10460141c805040c84610303403548a205141d0392103200c0d0b2508004001c1c1a060540f01360220701070211860007207108115681103011002400e142d040d980c1000300b65608401140d0900316104001d603d6044600108054a0b04004410041d0301035000040c2c140d07902d888a0f1800030f04151003802081e283d8404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 394303354 1250 394302104 394302137
    0xe01210816051c0e041d0105040311071a030a0e10060603020c010609022515090c060f020c09010b0318010614041d10020706020f0c010603021011032a030a 68
    0x32800c802000303020040e0180358804040d04c004951040e05006036642c0c4050b074206d21684400e44003910b030303600080042c5c0c1420706004205265280342c0d040c3e18031070b00074000355335140010081105181c0004541c2140c039020343c0103001e440004101100d500c40c40c4044620002117100d4030004160a44006070741d41004004603003540c0f074540c4070520061041c084488074507100c00350b034910000750078246c2100c40c00510b0704410090900300084030841c6007603010030800c24580c10100603500c1c0e50b11641d44001307542c00200d03030b07072550038580300d0f0051502c50040103110040d002540c2c000c48244032020280d0102d0040078216100e50b440000080307032031903031650b032820584550081003032035203404c4680a40500d183c2c0c0d81c4180301d08842c0c280d43d40c0001d040044c46100d42c1524000e0490200c91541c0d82207114405000e00348900090f80f003042140c41e41500a07004200388007200d000000510300f0314903102010313400b0301100c42d10313200d00c038000b2107101454510600c003c0070039038201d45648c1c45ca00500c140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 394304604 1250 394303354 394303363
    0x90919030c020f5b0c0804090203011404020a0c1202071701142203140904180201020f0105100603181a01090501050315041b050907020a060e070e0121081605 69
    0x4040029080014240c9120084511581c0c42002030340141c8869110400302203c21007407a245c09040342c1e8000c00c02180340c2540b60000e504952a403502030b86c40c541d2020401080b4031417182d240740410300a040c2c0c5000038441400783c0707280380324a0040d10503181c4d9031401c40000100a4902440076503440c0b80074040f00e0080445d10f07401041800d218011040c20212110f000004014060309000b40001e910942d40c80700c004403101250040c10030300100031081c0c990300030b00c6000342d07089025024001c85a01c940d9814820540300341941c4800c211070714a0500c040e002000c182c0044240f000c0006034000200e0302407440ca40c40b0712034440c0c000f101503140103d80021078106800151294000408103801d0107240301406402c250000142c103944400e0440004800190b81e1002d90020300004c1000345164004c2405a00c260080409110000a024040d62908d030180503074a029a5510014400c10010840768455000b04416a1035400382c81c0d250820f6540040300080c0c3c020309003c00841c1040820310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 394305854 1250 394304604 394304689
    0x30c1308010e06070c06061a071104090b0c0d060b120103030801080303040b040624060203130506040e01140d140106050f03210a0302120411090919030c020f 69
    0x10000c00a0015001140d0f40302d00002c1c1c288810030805e0f0f407034801032000d25400310000703041440b84a41c0085440348c14041c00d41100c41c0580d11010360001115140c1003901620724001e070700290440003a9582e165908054000c06001d800c080d6130f800010030342e4441c031001800f00c0e892524520840e585545001000200e0580150040750020b20602000812405c070079500987d2004001c98a606502e00019190b84040580c150461a854000507455004401482d00c66240305491408a8a490a2120500c0f41e03202e0070b0301c0303400c4000040145580480d01c1808070113008041e00d003100b1840d1120800c400440d201580c1596568800704040e00d404591090701c8070060f4003030701401e0100d1545e25264000c50f00c1d4401d01850000700042d0441c442d81c100e0342400044d0032041c080707041c1802c03c00c403145002802c0c1801a00c1321004120300b0b410000310703082d2114910910046a00240e9012110015114012a040040841140400e5594903007000071059070a00300c1c0030281188038240c4804040c803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 394307104 1250 394305854 394305869
    0x8030103050d110a08160f030807030606031a040f091b0e0105090705070f0c0902040902030a0b0402120112030e1338010c2607060e03041424030c13 65
    0x4644003c0440340100d80700f000650403103840ca40380c10603844070005c00004450002c1045000c540031000f015042004075020f6000c0c0c0d90104451034588406074119404441a44075500a05034000c00314a4542c000c424603410000d00030a40103c0d40c0d490304124081940c3c0c01882d80c035400402d02045e0381e801300460040504982c41e441c0307402c0c400c1010307007244103d02c4050034003121408648188001c0301c444070001e2140100455079140c1d00c042300d0009410503944052410300384540e41040c0e10b494001d8440103a907003810059640d00c0d0041d840036500b01c0d0b141c22802d0110050f1060b0460b580e084800c00824214080030030144092514417455400a0042100c20008502c2c1d5107200c1002d07640c800c03c444000c0c24130342403004039030800c09641c0301d074482d28080411801d510340f8684003d042c042d02010f4851401800400c4012640a849000d14007424007540a80841107001d40713001c01d00b0025886110780f40c0d404003904079240004076401251101200100041c94038401703002104801c0050010307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 394308354 1250 394307104 394307117
    0x405040501080f010e12040e04240f1802100503070912121b120309020609040e0d1107060e01081305010912140f0405040b01090801140406060e0708010303051b01050408030103050d 79
    0x4080001058091f40c028251100d01b918001001c02103420018070146103544104000c05501029003000740100211030545035051041841d001d070702c10b034600ea010b03660080190444460101c0e0445041d00010310b0310041002207400095107942c0358204035007503400780c02885030711446858040c0840d03200310541c201025001d02018085214426803244021142c580810359040798000503a00b4010b504240d60300c189814501c0b440c007800003440d0003540c001901d900311819410f003803443e143c4100c2c0c419500420300044220b19690700c1107080f81e60100083c40b108020a099444840c01c590381c20714111003034640c1141d07241c01c442e0442d00d035140412403035148516249601c0d0b6603111601503481998007a40d100d8801e0a440da00411216024080500003040a03402c1e00d04043c0c01180292410b9800a2401101050000e40b2030300b01841440c1c2500c0300000d692840c0c2d03084455501c000320440003002c601250345840b01081c081e850065000303c1380e00d41c0b41c0d415810180d0400c50485084020b00c0710 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 394309604 1250 394308354 394308373
    0x6020102031618030b0a020702060c0304030314030403020705090408070803042625030e090424020705061b1c1e020702030604060504051c021006080708030f0c01020405040501080f010e 81
    0x30000030302507079806002c0034110744440781b444000c0d000341200294803903804641540c0b07000c0000040e10031640250754864807880c0c0f203261141c0e07621042c1c80140058114603000c0c041402d04800041d003052090788210b142220079110700896800541e01241c0340e8486080c80d480059a4801443d50f00441c0c424070340c075001140103000a554000110100321011a004000c281030158103620b4000e90003600801c3ea40c90a4030300001e00340700c0081c84043c208041c0004441f403000500c00d4440550f4400001c0103641c951101100b10340c019188140b0001d441000a000a43d008490b62400701544600c04a03101e9200e08d61480d80c03025504090300d11500c103002030005030b40e002500582090708039400140c4c49c0c40350309100307040030304000e1103144440c0c402100c1d60078075034005060742150199074020403c0b035483e0f060003a1250032600c21344c8825030040c0500045040404000c202007203454000500d840d40daa0085030648409030301840050b0030000e10b100d01d940007030050090026540b0050101141d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 394310854 1250 394309604 394309637
    0xf06060f090e0603070f1818020604060c020d0212071a0f030711010e0102070c1410021209011112030108070e09101a03070905010f06031b0c0f0b01060201020316 71
    0x181c00340700d00d410380003209010400380d440500c200401b8080150a920542c1c0e00c5a403202c1c1511541c4a403100380c0d500d0982154422000c4450160340c4030743c0200031918103440e04c04116080204028103076406086e42d00040010394a48a24400a04900001e000b800c0d107071081c082800c1d001e2140510301c1000070002402c207a0444401c49920281c5420084071100502100c0c038010402d8a1403000300d50320000e141c20500c0707103e15141c8110780c0c40c084001a80407810060110b40c4480c0c815110141e0f00600748540c0d00c0c01440c024100c42c001c1890b1030a031400c2c44280c8141b418030000e00340d4103444000030060082c41e005010304000b52039803282041c0a4148285101c0d03450101910341c000c1c0e16505c801e2159248110300102100520040442c0c005544400d9402d0003000f0070b100715948403410800000d2018041e026698030702ea12000f4090360043ca03403038160f44c8620804800c80301c401c7c8003504400050301c01c81b116406010103500050305c1e031521129600b0519401146207040c031002c0c450410805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 394312104 1250 394310854 394310867
    0x40c08070e0c190203040f063f0b0126011403031312020103060e0f010512070605090d05010b10051306080f27010e15130201080c070807080c010f06060f 67
    0x449a2842c10242d0f1a1490700301e040d8000d9400c4501c0d05600b140c00028040d6000c2c5200f046980407401184062800d20000301c42c0c4030f02e025940d46d52000b922400500c43c4034035844105040010305001700b83d0102e1003032100303142c021503545801243d84038005000e00000f40c5043c031404c16055005514040c001301c500703050111684600726101300c00c07034910b80c00c59110341c003c14001d10340c44400c0207480c1060340c0340c00c903240006d010b414012403401c043d100301d07030900003009411074020381c40d0249086940801c0c0a01a00441da09a46540d2528003000c40c03074640d09410f801c1b00c2c2041e510941c603222000072054002134242d1200d001c04c4035070424000c7e4503100c1c0e4003280e0002d0702c855010b4102c644041d4407080010b5a085240e40b035500c4c042203000c1107040407444108288422404103400d1352400d0544644e104800303000b17400680b000001440122123039000700b031981c0c01181d81d641401d2455950054950111828a40d265115285103500d0100d90080713401800d40ca04100b8201d43c9000d0f00180f40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 394313354 1250 394312104 394312117
    0xc060c09150c0a0b160f26130f0b100504060b0f0c1513020108011a0a0f02070e1003150902030c1e060a02030703110105070903020904031205040c08070e0c 68
    0x18000009010542150030443e2407005544400d03881304503e450032030444446070071000070012512800d55102c1081c03045002c0c03075001103034114000f03000c00e940d10062400c0c44003d0070002110300c00d0300030001150402002008051240000640c0d80c50b1045074803045005c298001030042c2d0520380e00b801a0b1500b00140c40e0019800a006521100c2c0c1070f491516040641646200c1710b0405002c0c00403111b0103811411515001f03807507007a00c5036038500141070264007143c54a110568140441581540b00e600005446c20b00c920444036080e8407582040d07001c02003a6518100307000405e02c100300304000c0c80014400c10030441c030100101031841d00460703190110001101c2c801c8000540c520020340c1072010840c1440000350031070303480c0e4880c107030044c7d9070742e200c004141c1c007148100c11302c00301301a01401070138481c41076a0b4603100c6052440e030070700c1800c9101410403000e0003210103034198068043e00c9543c1c452070241211807000c1c0d142c40e1040c2e00b0704059400045c4c000d902036080007440b138100e10841343c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 394314604 1250 394313354 394313389
    0x141606020708090a03030e0f24090102150c030415051501081e1303031503050c04050a020f0d09020a12020f09090312090102070204060b1204170417030c060c09 70
    0x1c1e035064a10304200319201d920359aa9122140000c088149584000d002048031000d99003d00a81c0950042004da070204130240f0b802c9020410000035402c3d204405030004c802d060040b50041001311404004000040b00c1c5c0d4200460040108803c1c40181540c50801c0e0500701002c105c0d909084c0d44a00d00e8050141200341030101010104070001039448056640321141d9034110240d003000e00a604100710a407100364006810004051007070481ca0002e201140d90103c0180700303000700d080078071019020081c11004040e030b0174400c1141042c4010000d01c00c503000007100045010b214170401013103081641141107410144800305006072500c004103c840c20044480000c01d9554441143c070b07512503480306400c035001d4441401154541500900f82c0c1920861782030203c5500c410021000b0f01070b618280c1030910b2004003140105611480300d02e0200e900034145446c2a4a80c9201c0b41c0402003049018103a901c00074a0807090b00080c4640c603040000c00c0c0c002443c205049002a8800455028184 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 394315854 1250 394314604 394314607
    0x60a111902071710060e010e01060315050d03121d0a0f02030a050307030809010b10080a0e071505041406040503030405150d1e0c11060a0b0315010902030714160602 72
    0x440940200071000050030322008030280c2c498180700a40d120201001c1c2c800d1310600300360002c1041112454100e058520403001d554040e8a0100c0480c090310070407108040d007440811011a2549910100000440c000e0315001216122051040b048400348290440c4036156a10007280f4800f012030005001c507048040f84801d034540740002403e04040a20003005844001448001c02d034100c0b14961007050340c940200310b014600e80c1071010542c0d1002c000c100081c80700c03001624a41d80b035030008113142e8041003100d920030340321a08a0740078643c011418012840201d4208038070340e090300351131900d03e9090b103000b4200761500012903541e01a40c080c3c00e101d1a054100c52039400e81200a4580d11528000c0038441c030704103500c0d05002a500c80c0342e4826160b0034007040091550060b2035800e01d209841c00117200d20b03500e0361100310050200c6000356174140a01c184030500da514034403505010748079003000140e607401c00702e1b4054107100710304204840c113500074098480000c81071001045d031361b9003010015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 394317104 1250 394315854 394315897
    0x30c0903011503050c100813020411280504030201020303010501051b0a0506060418150207420b09180102041d0601080709061707050705100906060f03051b03010e060f0405060a11 78
    0xd2b0280c400d0605403280e03d1404540122508012000504101808080c07091000c4080368101c5103881280800303805a44200b00402165104400130020980c400d9000980002c0360140541402040d15054507503900a406000341407601d07210b00600300c400303801d1545a44201303980e180e0303c03074075110720755082540e010030704905200304080740040d01e4215806104405a1004c900700a101a0205070180c50b01709c0385640e0f0502c1c0140c070910400c854002d0860392165078070401003d80d1084400d2042c8255000c1c0400943c41c104080c04084408402d90407002030318065000500c07105c4001c01290811000c81c200704403c41c0c0008401c54129140040d1100903907039a4000d0341d0520640d0030003080c1e0301c1501404c4803d83d14540c4003008052080405210b5031b6603640504241610900010f0043d82000d0003256440329000d48032140c4070809070000c04c451421003400c60a2507001c96418002c00d401404000030060240001903111039421010800110595048000350150500300604c110308610b24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 394318354 1250 394317104 394317109
    0x8010b070317010810050c161101050c150115030908270a030b0702011506090e06180405030705120711010e030a0501020c01142a030c0903011503050c10081302 70
    0x52030980c11908501c240c2e0b580d2000c05560341d100c4028135204852400011409811280003114441d50000c1d03044440072031035448942d800307aa000c9180b41031010030003200d81c0000d8184002d000007007102803201110341c9028650200221100c20500800d803900388007030000b076035482c02d858200154140512114808d1003552095180042c8a40d52020040f01c1c00000c10607098032492080102c0e0b402072045e6090342054080141d00303030244101091048000344017418601101e150320010042c0804042d41e00f010f01da00320154142c4013a0742ca9000001d0714428010200040d010991007046001e15104c100e0b1201c18801407681881030404c95441c610085569080081200964020000b1995980c082e4407241c000e060821481900014450010b18800c521802961080d21a81180703203880041d400841400c0d40018518684d4690038030890b54039881c2403041d4071260003076800803024030341075007055840d14500041c0b9034070440340141c408248a89c8020016004109103a10311948a06d130f100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 394319604 1250 394318354 394318367
    0x260117030705060c0c010c08070807031515091523030406091704060f0206010b030a1d030a0320340213061e0605040e070504120b07110d08010b0703 65
    0x1d002c1c2c0107100704024000c902c24000300a0000b90b072071100801142807070180035103c03288201d40b9030002c24071000000c1c80c6240650440398840a440d03c4400724503466900b117003a40c880c281c03c660f001034107041c001e0090201d10140c151040a55040c40f000c1289100d0300d040c1c0e01c0000c611441040b40300840031604000280c3c003c205483d9011050981c2c2509903d1040741c1c0790000c1c890306000481d491001000d4a0001c030741c0d24140d40d820b10800c2d18550b603a550100207440f0900ca1030200c0c0c000344415240300c0001303002600390700e202da54000c10f510001c01c01026104c59a45c6450117117207005c10406902c0d074840b0780d00c1d1700340080c800d804a01404000c48005541191040080d40080548240184503003131944507000744c2d0200da0b8500203400c1c0003540b410403401240100340205104100501030703030402c0444180e1007241c91400501d8141c03030320700300422001581412115440300e482401005a0041505503200d81da000051581000384900201610418410200c0c640d0001031401c0601d8420f40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 394320854 1250 394319604 394319617
    0x30306030f1a0109020c1002031803040f060810051e040f1a030d4503050606042004050105130f06080702150f06091f09090326011703 59
    0x81c141c03416000e8504040d94007811203814010482450000443c100406100703030f0789050500710041c840b00408411041c000c4d440500728910900c840d08030103c100404200400240042000b8039000514054000e00000005002080306c3d441d660024401c0392a243e2078242a8000c0b004021224494100850020300e04c1c003980d0300c0b040b17050aa400c0c1c41305001c064800080e280682c100c0d184114207120489400d803540c003030710f00d50404a4003580d5502c0c91200ba03a5480307000001c1661080c02508255980c00520741c0d004443c0390700400304011003403620340309000c00f0b2054940926010305082c0000503040c85075004290612001080c211024003042c0d00c10805042d448041c111820b0b191038014124140440c1c182d8014885c10403807042e00484078181c1c60290b484080100882c1e20307001c00f040303540f0900510008113182541204504a00c03101842e070300800c0d10103400102070015040081c48030803078106540c0036400c000a19442c13420000c1610f4112102100702040e0f245203441070605610440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 394322104 1250 394320854 394320863
    0x103091106040611060c070209040b09120d0506030c031203010b0a0c050a03110706050412060c02431518180218040b0a03030809160b03180712020d03030603 69
    0xc2408100a60080d4030a507020345140105e40e250303074421100c0e00147c81091002500304a4450209000a000c0028150094680801d0f03849070100f40d8500c1070190040b681018080341ca030406c0c0240340c2000c0c422070b0101401580604080318500f881240035110601c100f66104e40006803581d0711354411080103901c603500030b05541038000d960900402c0c00e485003500050a000c0e0410000d9100c1c041c900711000c455242d01e118091903102d40780c60340100181c00500c02903009510f8400b015003458076032601c01c0b114441000d945055021006183c024003005100d12001407400705001c42107003048441e04102e114034011400c1041c000041680c0f24070f9074003118010500c003540415540d5550060322105040c125840310f9003140c00308004c252014012aa60080461403080c40031a12400c08558400c00c88000c4641c1c0d24204010f10052491550001404100110901081c00c04070070703030400141d42c02402090040d042c10290600d18400000c000c0c4105d11030b2039a1402c1600a0300200029500f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 394323354 1250 394322104 394322107
    0x509090c100c080c15010e01060e1302220602010b0d05060a0b030c1305061c120e06090303040f080c06040e18070e07020c01120e030403170f07080703110105150103091106 75
    0x51481c09950b805e110788070706900341000800465a4115011002c1c102c0f501660b0b81c1008030041c10030b0140c041d21501000c0c40341502006140342603001c6228210850200d94807041855283c5032000b03084070b09a01500e445802d881207910b002c92800034845420626501000454601d4100001c0c1707404030304002c107a000355504019240344119036002a1290205507440101d0b001e8520036120020745404008104001207208401d0180c8142100d0300d08480107424a85080384060009140d0741055101c9508040030001c00d00054006200c1c4c09082002540d15a05040c10100d164907a000000c08180d400c010b03850030302d01030700010041c3c2002010a107010b02d510382000c11000b0744500d111242e1501054902c000e4510300d40c1a8810014148201000740d4180303801c1d0785c0c40c1c26400007002c80c410050302007401800b400141c541e00800b0954410004141c0d07d00030ac0c034010340303414460306072150140d00d403404100e080d01800350715000030f4500f46000030700c0f4002441d0034900602c070100c056410440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 394324604 1250 394323354 394323367
    0x13031e061103040b0f0105060703030e070f1404060b030c0f030408160c1d070921050d03140f010e04020f1305010b0a032904020705030403200a0509090c100c08 70
    0x64400030b50143c0c2c01a540100710741d82d0b440c940c1103a4031003882203540002042281002007031207544454008140c00080d600304640c6d4000340e5101d05130541042d038488010310340243c02481d02e172103104000c2286070300c03050552419031042c1c0d02c40c1c042c1c001541c0c2c9821000000908200b840c00449514030900c088480b41402d1604040c903078624540203d1081415000c2c0561b9100501d00c1941d10404840e40d88014003070500003220300c8986c070f401600d03000d42c00c1100ba5600042041c070020400140c60380d000900c074089100d00c1103503890090044814502d20711b00501c008401d00c001d01c1d80c030a80617584126443c40f11f0000c1410fa903800c15050310b20394501800070403107094640041c911566960760500c03552071428500e450045101c0400c1140141910980025042a4018105042c0030320150390a203550380d20b40100741e07035014541e00201d003c9240a50124a04059000042c5c42e083d0780203500c0b46000344420f40c1d00c03541c414610380b00795801201500703241d202d41110001d843c0e10447e100d8036800e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 394325854 1250 394324604 394324631
    0x6180c04090c0309050705011404050409050d030b0a030f0b130506090a031202090a18020408031303051504030503070305060f04090503030f0f04021507060b0604060c0c050613031e06 80
    0x80040c01030349807082c180b8010100342072180c007a4556042d005400341180705d1515005681554442442526101d41800000707207647c1c0300d20850b50001d000300f01130070902d01707082002011a000307816001c6c440c05840c0800d1001c80c0c070147c2500d511992024007044c13252a4030301144000c0e9595807000b00359100b25004c02c83c55420100e0148200c41c4252240242d403090f04083c00164062a0940f903081807041e001080b01001c102c2e12143d003103030240c200516050701c0700c00301340c20742d40301c444011f0b50300030044400c00801108001c0007454104944d8035902604244c0c1c0d000f8507a20014000008150301d130004958a0b550300c040003140900c008200b04040401c92601a0b102d4004980c2c7c155144040790010302000d85092250303204650080000c61032144c00c0e400c10100741c100c6881990391655400260039980c98110003007000e400551103c4503504858500100500515040180901014080250201d400a0442d010780354010741c8424102e003501015201e0800881010f001e05d810080d0054845 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 394327104 1250 394325854 394325857
    0xb0a1d191b08010501030e031819030b0714040e010b0a0905130f051003020607030809030717072901180e19020909010b010c0320070303020607030f05160806180c 71
    0x2e8440041c00e0380d80c1c10040d412220600d6018095070002c100000141040ca40301d0311107020020302107841d8007143d00c2d454006100542085480fa00c85106010041e42c000311484505011400c11520301424040f030210381c40010301c00c0c0c204420000c00d5680e0300c1401205c000000e803001901065510080803d1000642090380100107414900400300303404201e0703442950140c03900074150714034210440d90115239114000740140c1260005008800026000d8000c6003003940c845802c0c1600c5005c41e040641d404002a0b507c0c04000351001e8941a40500180c10f5034110b52401d001c01083e5000381b6505806003448100054290142149541c4049403514002c000140207803088a903d64848402600301e07250102c03860f001c0b852400c43c1900191051071202c0b0203c120300b1800091102407960302d46041500e410403000341e003000042100d4079070b0501c21440a80780240003407100e81840442c3d58204d42d1701d0b03038820b010010214009001d41d1200c1142c800345508204041216250054100415 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 394328354 1250 394327104 394327151
    0xe0d0807021201060611031207050a0c080c060105130b010f080a110c011a180a02300703051005012f0706020a030e01090509061915050408010b0a1d19 66
    0x101e00c002c550840c1b8600d000007900c814400c281150115a142c0715000e8aaa42249060600300200d0742d681c000003407030041c0079120341c512580081c40c1a5041a040106041d07070410b4004e0b2040c81d141c42004240c0c0c1c012007100d04903509080450940c1c54909400000d00b50120000d040c201000139034444811055100b07041d96159a001c1490104410080120300c1000442d107090b010210f101081124005a0041034928442041d0100079406006d01c4114202c025030324241d0201944200301c0019014007038190300001c94581c90303e4050508002a007400b50034850203031052074420407620f0303902810040c103181402090446000c1961075500a6840c40c41e001c0403000074010040090341075000e11400c04c199031005014000c250384400900c003542c06404100820000c40b9140000d0560300100050f80c586100d44c8c42d542d40d9810400c40754255000030f26400d000e8440c0794010400b58a0642420000700b1100c0050a9940c41e10114030080f2003808810390032072868080404204040e08050680 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 394329604 1250 394328354 394328357
    0x209031e0c092809020a0b03071709070612020c0a0c0f0b161202280b0f06010c12091509090e010905100b030a060608060f0a0b010e0d08070212010606 66
    0xd007901d19805014800030240d450048051200c002c2601c00c0200420a041c201e0840b01c1c00103214a42e07800160310000c00b544440c08849001060040091340000ea02c0082400605904038504018140c2503468000344646401c100f482d010015000283c0d4046407513603081c410407203141d40c1c8607050951300c1e10598440d800003e004407000044121a00040e2112070380b0380c01c4840400f00030303900d038039040030903c0d003036442107000e200c12081003403008144544503900711203c15074645e10645082c1e1003d42000c1e00c03001045600c1d00410010303030b03442000c901480754400d90340c804010714042c003035944603601e420020006c4030702c003900030100303602c0b0001c0c0c0200c50041d80140601c0300c95408250813201203841c085d00d0780d0440d000c02c1098440c55003025080003030150844603010340644a40e0304031b40c440d41012104d900b111080c01044032401c4200c4d0740080352000200b144001080020b407003006410743c180e02912048510200740070504003030703814203500074162206e1050740c032025034001c0c004c6019400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 394330854 1250 394329604 394329613
    0xe030c0d11010903021e030d110910050301030f1103070803070503130905060d03051308031b1c21020409140906090a0503030109020c0a05030d02070c06051c0c030209031e 75
    0x16038903407050150045664064014041d54015030510400000c90703003156250510007000b14004000c440d100342040d00104811480c1c40722108401c0040c3c41c200307042070b44100003083c001880820840c524822685a0103500c0707410490340000880e05104643d031141c20140400704030720742031101c0440240444d20071822800c116070b480c0c0b6160011103105442a0b5040096201490000b071b00450044c4107000f5107501c48201c0d80d84c1c03407480c0d41c0746130b0000c02e40c058080316841e5290031502c010042048412a00030006c030a41d003024100030300b1007200e207246640d41d00c02d10030382e00000c0506070304a03406410814020b003c0c460440802d2581e110043d150f07003100d0311401d00008c10a035000304507a006150f01c403004c0c6255900e80301840029422110103d07045004c1c21011100107581000140300b00c0140c96030141e01e556041c204140201d03955808002848000c00c108400d0381004001380898040b0818001003aa5808034100c000380244042107406200d0380060302c10710403941c140d10801c3c462040807034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 394332104 1250 394330854 394330877
    0x121a0405030301031b180f0b0406060207170f03030406020f040b040b130807081b0316061805011d0402211806150306010302012d0807020d020106140d060e030c0d 71
    0xc4149800744c4201b030300c0180744000080300da101580041d90b0340900c541020811100d600001003c541007a4491302c05684400d50411806022900d01d800c1d040c14080981400705401d0140c0c0c2e168403009200408882d400145450340503a0882914040c020085100d42c42e9500e4103129105c95002d0b08691b242c0812458001845c1ca800240c4d000954011002a003410740004101d13014102081b9000359040c040c0201001c102080d408600d00100390340d603511045034104203e8023481f452907410550401000d408910a01249240460100f51080d18016902c804450442e40b123084040f0b4221420f5008600b07200c5040719110340924032065413001e580140d2541d0f80c030000d603a6070707003030055405410090040001d58010f6a40c190070621340e02444400002602c50561080c03a02c0c110fa40104080d44280a055175041203003400d0782c601e9000821142c4e00301211160220701006074184100c02482104042000c90341081d002d014100048988170889042c59031307100d0307001c0d41316440001d8000211 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 394333354 1250 394332104 394332143
    0xe0303071d0f101119030c150b1c081201060e0a0501031a091b190e0d0f1e020604120204181718122b02030301121a040503030103 57
    0x50500c000001c1c50880711840c681800c1c0d58200e040d6000713500c1d901038000c100714900400e03c0201d0301c0500c6540c030501c62100c0741c0b515000805440c10180d100500e40309010015490324501c1c0002581c030620301c49112085440d15100b02e115000302920202d00780000045c01c42d810a034448008281220001c024a454000440c11294859180740700016100304d40742d06400c04a01c0c41e50401c61800140c1c0301226504c02480c9640d201110780000020100c1d80313140300325407000c0d0322004110102c9511038040310b9921000c0522001d030318050310001d10f038840c041c040c003043d01c0041d01459000d003a09454641c0d8801c24a40440351100031790040341003468100c07007803003600b140000072760740b040343d100851140c03800f1122281c01c4a01e27049101c201104003901546e0765208807511400d40c6100400d040c42c03180c8100d0703a030501c1c5003944c80450400080f40408031500801964103450406c102c1c098a003515007800e001158001144a090380100d00912091180100c0258140c90007420380136082d640001d47c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 394334604 1250 394333354 394333369
    0xe010b0306010b070f0218040606152025080f010e120307090f0306050403091403070303031802060c030a031a0906040c031427010207170705010e0303071d 68
    0x10203685900100c00500c500c0f18508060f001c0680191031104102030658080b5a90303102002d03a04544030681d808001c10444075009890151220304110103902c1001900600f2001c04540c0c1d9110303071a4801030748440da840800c90902600242e40800ca407900380801c940c4d2194038580900e8510b40180714810070350b100d05008051003000000c0040070701100040d882d1500c2c0e000580a01e040011081c0c001680004842d90030015600032400040e00b800c0c280f40240c00d091169000241140078440342c0d5210340d80c0804d05008807a01802d012624050300ea410907800c4401c83c80082d404038010507400c000c818008040c208541068508000c0b94084041d10500b00d0701f0001c59660020540001440e44e06154004450701e0a850601090316001550040240c4600b154021319000c001e00300f401d9034802040e40c13041d0a6404000840c03a1040584480c41900b0403001c0d02401c1c000002207100c10090700758041544000d0702020340741c07a428a8000201a4279007281d1205041081103a4102c20345012034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 394335854 1250 394334604 394334621
    0x120a020406091d070f030206030705090d08040e06100905040209060403060e010213080f030415030f290a080d0509030a060603051c050c100b01140d06090509030a020a0305130909030f030e01 83
    0xc07401c01c0c0c0c03d8515820423446910003020201041030500180b84644c0326000c0300c40016205080d029285e43c1040d1041d040704000500040c0b10305140b09c0b1181029030081810703002e48105a0b00940d40340c80d80e10119499100300d5000a00c01442c1000c0000c0700c500c10350241280c608140302d0014402e98413012259150081d0004c003016130400c200c1001241c3c0758287c000e5018540c4e040108001c400256040101c6a04215540c4c54500c0d44030044442081c240b180300c00b4540880b03459031aa410300c2ca402340e40c1c1000c2e0004405018000442e0401658104050307501154840001d0103842d8072482e14984402c03031298401080d88008490404041c05042510380c00d8122030002c2144503e078248100190003200e90b60b0b4140184d1150030410b45191b40c0c000d00008003990004204c280c0b0b01194082103480c01010400d444e0010701030809641c0d40400c0c5100c2c0d4030780515040d03440300d644480300148401c1d194864560b49140c0080b00c410190001036208107000136850420011a4503030140e8261001034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 394337104 1250 394335854 394335869
    0x1c0807060e0c010504230f13060e010504060803070609030306030f050a0203240601300203010503071401050f03041b06020105090c0102070f030f1401180c0801020a050405120a020406091d07 83
    0x280e01c407051491880c003550306c45450051841092401c014003068800c031440b510b1380411912144113201d00c1c1e103c1c10a95004010a54040029612b0003210685a0103942c00081050b900e035581c0c141031502c80e0300410080d5400c08158001e41e4020b1034455966401c0c80001c074000d000f044020400f00c04480d20107003c0441d4101003020503a5003500440303422039220803100d8501e4424035190004d900c50055003000041100340143d51354100307410549070440030307440043d50300e050103e1003185990000c181c030404500302074144d40b2030311203240c8604241140b640526280d44042e4001520f10b5054000501806501c2c007900c0340071002d403004988401807800303034040d00c4e4148501040003036405024005680d000c0d1500300152901c150b410390a68400c011042495071075100c2d00303021700203110060002004190000c5107000311a110184c07003802184070b542d1084c4140005082500014802405030303030340c010700421180313866149200c0140307840d40c0890280d01c00340c1046224004009013500584400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 394338354 1250 394337104 394337129
    0x50d050a0b0105031306110a0c05070510021c27210507062609070f06020a0320010b120d260408071514160201020a08061c0807060e0c010504 62
    0xc4520105c1e40000e44002100c0681d0746134041c00320514000f01070300b00c503c801d90b0b420030805c0140c10030928010320b9800040c40b5580e41564540c6483d000101d03c081c20f00c400d500400208540c0c1c02c01d59502000b84050703101006da40300c0c180009841014641d0548045605d40b90500101d800681104101c0c00001809680300c0d000c10b02010307000320031044180b000b00400301504400d0a401d0701010009850500d0750354020f641c10b0001c0700b4800482d00241545100504c06504c5989005080c00312000641c140f5001611901c40841801c0d004403181c1c0c40e026140c1403840080400aa076110030b405800c070001188164100d41c0411403840600075520038a000c2e04241d00c03151103c801c0356100072000c4640700800402c66000307031601d0259100c400d00d511402c0c80c142c070f8004402d00a07104242000c80c1103900c1001640c286982008819401110588100d100c541e14420052408454480050010500411903404004541e00103240c0c600100d0f00b0388014400c0c0a0054407180203e00031608503004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 394339604 1250 394338354 394338361
    0x303050a1b200d0807050a02030705010f0207030b04111e011b0803010306020306061b0c0306060f09040b0711150114010206060319151802042a03050c09030706050d050a0b010503 78
    0x182c1c0145000610703030007040e101007400d440e5a1034015600050046800e9007025111105503d003e10120006040a081007054006c0c1c1e540000d484400c90300000304402d040d24049024800300e981c0380c400c0d019020b03082400f0365202c28289403014034581e80c102d0015625611700104035441d280400304c1144d2100b442c43c25a421070781c030300000e9000100826000302c014450b0b4540c4c1c3c501c0d0701d42c001d166083d040103480740003080800d2501f4410001c00c0c450041c840c11003514030580b62502c001e6030054004542001d551512501269905288030f2980e136207210301c0354440c00e0030030320100380760407910301e07011402941c9006030040ea01d5480856210350b0680126012441c504014410002550321451031b100034482c1d50003003003048414165200441104075129003045040a10039200c01e844010288449050720003010a1031040d4828031030300300b58403540422821100c20042d1050042c005007036400c0340d91540740c010480d4020f04050b500241c10100421070f881424400d00d50b0f0300e401a5610f501c2c51386c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 394340854 1250 394339604 394339643
    0x11505030d0c14120a050c0706050717030603010f0c110f0d020d120908040303030906050a0e0d05090a0905010605031e01050a0303030c020f0601090b040b010e090604050915010303050a1b 82
    0x20781ea80003c20080c0180c0c1007030707071510b250a0b000b00140c01203600e0720350f01c8103060a5404d107410007907000300f03040c40400c1049002150004210366018020010020395035030303a20700407d000d0161f02c81940c0e401d504004107903042c0d54005d484c0400040903541240c503000c01d854a810340c2c5081340c0d080e1401503000890720244440c40348680b28010003188a000c1851245940c8840703181c3c0c4690700950010f9991003a0f10704111040c040c640e00034507000003c0c0140072180000c9900c85100803583c07024001c0000d10000141c84000c4050010b02c01c3c07410820940d0303525480641640d0089a900c00c40041500c4020100180c82040c4c030f06840300a045040a5400c5a07010380c01006a000030005600c40d000280c0c41c080d800300040d030301810079100c0c0450000000424801583d1038101034505004141110320079548401910b29804942154041195101c0e400f1840c20460041200881e0711340c02400881410340080080c28094216a42c0b2030038026030166240f101640014028000c0d40c05003600c41501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 394342104 1250 394340854 394340873
    0x1103060d0b06010c0503070303320f070908150411060a02070506090a08010e0a0201030f0908030f0c13031103060a06050607170d090c050907080106050d090f02040e011505030d0c 78
    0x40410f0500130300d600710390340300c803482c3d07400031407003100004d880700902e5001c01030390900f9103083c4009600d42c0e000061403000c8480c504400501d140c564840b560b000a0803030f40b1640c1c20f10f0050411000745e450215000344003810400b0202d0b01075981d400140c001c0c1c2c0035402c103442101c00194141e4064114a8145010013003503601c0030f640290302039220003011603031040038482c444034508070700c004209150862001400359244130000a00f0503240840341804030740030381d04a9901503070b1407200c42d5140d0b4610b44000348500824141d4103401240d0381000c0100103220700c0c04401d86004508a40740d0b80d80e00c03031040066070018003490340c00c04000c1c480000062021980c0d107220300c0011039264117260b20316040b00101c17202c0c02015902d00e0040c01e01004241070904009810500c1c514085150398103014014104c1c1c4105520080110358035a00a0103200203ca03801e80c80507401441401804007010b40e040c082c06040c02800104d5114020014542c80c000420642c42d640945907524000215211321a26 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 394343354 1250 394342104 394342111
    0x90d060c0c060c03152403020d02071e060b0411070f0201020a0501111e0306010c021c02090103080405090907061d0102150708010f09050403020a02060c031b010f1103060d0b 76
    0x24058564203690024000f40500b40305210b203982d0000e40e811202c0b0a41085000316400400b00c80101c089203c5050f10041000d40501001d040160b503a21400070010000e00c146000500560f100d040d039910042600c56540c409240546414003698186100b0842181c6e2900d02403501d40c04200424800541c5201c00303030710042c1c01401581e003000c00719180c4c5070a4804115400904620004a46510310750030420fa04114800107171503411450304000282900d40301d2705000c1d00c03411403001c0e4420f040e41081c00440e4580d0340500800002e503580c2c600b6070401c0d089802268410340e03a000000e100a0340005124080300c42035031b6100c407034101c0c4082d015010f22106072418114050030302402164a07902d12502c1c01040941d58010443d072414064130001620382d000040d100d41042d0910001c43c1e400144c9003080d580450b0459038070021600d1051031072103210344065090484a502c4054001c0640c00000300519032034080c0300100d81140c2d640c0091004448c415849048904040b01094081103c180d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 394344604 1250 394343354 394343357
    0x20406180e060f180a1b031a09280603030e0102030c0705061c050405030d060509251b061e020a270509040b07020d050304021809010209040606030917090d060c 70
    0x84a8520200e03020a05002c0f5828003175070303449810044082c3e010034043c0f00381c110b0ba841d042014803c00507a01825958000001d842895840c0103e0000c41c100300d180d21b108000707500c8131541d41203488100b4001d40203d201c20b6000c03958095210078a07500110440e23a51420f004090100d050401c01000039a40044940444500300030003601c0100e5181e203d400d001ea8000c000958a0320b211322065410b0342c03a07541005000f01034131010b00039800402c00e20135011824040c031110715514640b808850f00c0704605005900854004800c1061005580c041c0c400100801c480d04c00c5d00c4d441280c01b4090741314100078180011510402c04015001000480ea001c5000b02e9020302410b544400180c1c58004c1581c007900d228010f0342c1841511038041040a00c015000d00f803150852516800042d12943c400b84c10000322200c04d0f001800e912000c1d81216010107000f0000c01142da103d040c000d00071700c0d02540c1164083d50032071a40c0164401d03641a200e694100505c5558064601e5031007401402e01203010300c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 394345854 1250 394344604 394344619
    0x216032103060807080313170304090b0f10050307090609060f11191a010807060e131b0c030207050a150f0c0209010e0411010806130e0f0f01020406180e060f 69
    0x360b03c0d20522a9100418109000f551514954030415a00303e185070301075201240701e07480b98545a00040705035401c43d0450b5100084250808010444036644600f807998429941d0007420340b8242c000001e14040c21150755951400760301c998043e44c4c40c8045008040200f001c41403100c40e6644a0544801c1500c81e80c0e0a9803440c4050207042d882c10350300c0140496100403e010741404010020041e20700602d1321030024042d29103001d40240482441c04d1540b4014544008150380603040e0342c012800703804141098410000300c0701002813130321291110440050080f04000120740c58044101000d0710042d5000c0d60104481c0b0f4003c1d00c100d484a040c050501803d140d191002d40d42d840080f60003000202c41c061002c1c503051405800c1c0880d480e00081c1030207145418070125445240c120311841032801c46c0002ea0820340d1000c2450689044503090141c45401c0d441c202180041d0080d0048405503140c015134425102c405003000003050003400301c24884880002c9461400ca94400c0f034251000e007126 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 394347104 1250 394345854 394345859
    0x12d0908071511031303080c0a0c06050a1b0c0608090f120a031116081303020d0c09110a021b04180b0f07030207020609090703140a0507021603210306 66
    0x14148540e6921105190411410210300d05030020103104000f5449809180342c085d081c00d40c07100340d89240c0406000303090041910306200600f003021a450710340005013948855503501c0c0003003150b40034910480c00659041c503a41440501c8020b0b0428699124443e401d805085c508100d500640041c900c00062060800c0c013103264006101d01480014501406960b42d00c503000081c083d08d9555001c80c06000f0104810440200c1100303d240a4951000300d075980d403030070000342c1410600140c0000c0c1d030100c030416515040041400011044440300c3da000c0c49140582000070155000740c000c1c120142c1c0045201a8200d80343c000b4601010100a02c00110454580b240b41c6030500940300454294044005101110509101650b0700c800c003450154a0150740d98041900c0d4010000e6042c0590051804100c601d4020381003122403a00c0c00003031103000e2800e03100040c06888240d41c50320240c0120b528000121a15000040550b42c0040d000000d41030b800c2c0d04100d64030302e164201410103617a07a901 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 394348354 1250 394347104 394347119
    0x203190306050a08060601140c19171b010b0307030203030a230705012309070e060d081c0c0807081617010f080f010c0807080717040c03030e012d09 65
    0x40004c2d2500400821a51515070300140809030a101000c0d0810701c00d00881b1000c201c0000c14060580a103a510b023200c0086140805420b14415541ea81d016400300c3c4d281010054038414403c5118400f009101d054402d03020f01d80c41e40842d000183d007540040040322091400b502009102c00f2801c00d44a15000103030b00d002240740c00c009821a4540d450703032000070340500d0500c0200401813040c0307890b09440c200750000c565035125922620008c42556400034040c0e945420201401e00d4001003450340da1203030428424080300d0700408641d150b44c80c1171911000300e4421500e0071b10604440d10307240e000d80ca0741c03981d40d8612402001044100701c42e590a50300300480030403842d4002d004140080c0c02d40b50600a41904100d03480409034002d0303141200c0c8440b2550b001700340750f070410f60314100021251118141241c0d00303480d440040c01442c03412000d0108102e000343c5d20208480c082c3c1c0c0c6007402009033302c004480c21801203d02408030203070351400440e000c080e01c10a08008900d41040311040c2c2c0d0300c101c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 394349604 1250 394348354 394348369
    0x5070603050415060f1502160602030903061b0706050606072010020c0607030f0c20090a150b03071701090b18010e4002040f0b01020319030605 63
    0x100181c0c907581480304000f0304030314560580392a680c043c040c06003841c8010302c0481d010b20820103100030122100d070850f4024400d40741c80017079425010414607103625019680b80e0019440c1c5d8001d120304800070f145030b10407400040c0c0d40030401c0d00d401c0c03804403291280c10140c0030181056501860812a46000035041d81111b0307081c20310403401c1030142a0b22400c000000250100e460255042944842c0c140e9407024206c412440c1d041c10085490a1102d00407500450748040042007044040c0488045002c1502c0d01d0001340011110050940c0e02c80d519241a180445001c00c80c0300c0f803041c01400700c00305640203543c0c044228034094915012040300c03c40481401e9107c51002a920000209541003c0101001003212030144501c02d524140c487c484041006041c4100c080d105020b020640035101f40e15059041e02071684490064860704480d620035440c0e07802ca10072442d004600c1d80c1008107014620301558160059410002e5403c00400004401a80075080541c0c4100101d00d039590500c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 394350854 1250 394349604 394349609
    0x20c041a0303120105100306050d02040905070e071205181506060d020f1b151f0b0a020c0a06140f070c03020306070804050d02010b0d0201051c05090a02040f0e060f0c070507 76
    0x20803d11540351005100c40352030801e13801c1c0201401c0c80d8090010342c50345084202200d60580f0009001c812904086046c001180c110078581e010000c103101540740c0c001c000100c090040b0b1002c0080d40c465804000d1140d500044c84017594204070949882600002ca1031640418080c0c132a91808076004041004ca07031010700102c82c02000401ca484d00421224410920b030824080105080909040111844840200b4a58403000c0c074503007201034007010a03c7c8200900000011350340361001130384080d440d8400d4902c114041c1c141d00400054007841030000c020180500c0d030a0924092a2070442043e07940480c2042d03c40e03e801140005c01a02c0400c2042c1c80703941c150f502c00340f841c1001c3c50050704142100410004581c10115113810541e02c150003000d556a0908210f41c2c3e42c6d59224001d01240014100d0340c1003141780208110b84e451001c0b0720031104601c01c94040180568101c1c0d42e01c03c480321480d0100700342e40321600290707004c40750144454204030602c0e2a14208149030707840302d151101c1c54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 394352104 1250 394350854 394350877
    0x120518040e07031a13081e0315040b030c131508030a2c0907112418030c03030117100c0f090902091014040e10030b16020c041a0303 58
    0x110304006000c2180030112140400710310242417424015025034a156904134050400c40300000c0181d03031441e501175102d44041002100c6512071801c42000c14190302280c403450b02440c10700b0784140d5a403a02042482c82d01350300030120074421040c01c00020061000e040d1140c4444010340c4046000c010400261201e000c00d41e07500c01d24008905807200d00c5000c5900072400f49041d040140c00a6a074484029a22070180e00d00950740d1140d02c05024940b24442140d014101d0440e019048481d08101da118401e00d040d070701461594204604140d0f49104005045046c0d400500041c44004c0078a05201c030891100c0c0d0464100d00000545001150b40d518200004650002c88881340c440d00200303090010f01c6801400c50030710f0f11000225041c1101400031004100303500c40e113004961907610071346014000144002a0301d01c4d101c030041800805501050b01c4a501d5100095591009a01c0540c48020b030391b80a008907408840034400a0041e04118019031071b0110310f00c4503a42c50800c00307441c1c0340d66070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 394353354 1250 394352104 394352113
    0x90213020a0906020f030a030209060721020601080a02031009030512010902030a0c0f050702150c0d02010203180304031a06031005070206070f030b011b08040b030c07140109120518040e 81
    0x4240c0076101d010594060030030b45d00182e4036601900b1010099a0304d1451608001d07950750b02003c0000c2443c030400000922103c1c40a60310040c0c00744000e501e80d1284426000ca41440e41c0350449560f44041e02e0100071f43c1035102030141d00c000c802c2500034004c0b070307440790415070704112101c01b03140729040302604902602a400700800c008001c0c5e42c000e5042052682c00c04940c82c000f2707200002d10600c5141000b81c003a14213a2441070841030450200c1d030b590414001500c8140d2180d100090103507009903212426204040d908000202e0040f08840803258801540407205000700307124298a00020720703030356041c02981e011301d152034481e00441c3e108403210b43c050700840c43d001001509083c41030710444201842c000041480da6003052802140328a40c005035080040b41c2e03d0301000c544110f07008500340c5900841804403251103080544071452250348014104202500500c0c02c9400e103c00140c40244d003000070703443c564080c80041c034001c08424524081c101c4500e02107015900423600c4202150300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 394354604 1250 394353354 394353367
    0x10b0a1202030c2107060c0c06030e0a02270f060a03032a0c05030f0604031209060b030f1e010c08010509040302031e03010501020d2c030f0627011b030f09021302 71
    0x4080c05040003804407030805906940588e101d01410010718010982030640c0e60318200c442038000c0140c0f0f401d1503802840039a840c0c605400e10b141c0703c401c00d9103820700c03207040002107071001400b601139501c102c1000e440c2000003440c545089810754140b0000030f144001400d020195011803600d0040c5c82401040746240991a11080c90714141c5503200c0954590448018000040e03400f4400d111070780e41c2488007007000c05190400c50010000008110740c18440c108414049020108014074803481d0101c56000441030005040d00baa0f250f52082d0000070f402034014001880d10b00e403c41e41140c044e2040742d003040481c500700303440300d000d594010200c079401000420a41da810006201100403d00d821944001a041c00300d0001c0c03940b013107088a510400342000181e031420451700803801d1441c021510ba070304000c00124044c6070703869941c03045082e40074207030f07012450140200d4413440351300c91044c040b0b090342ca40d0440007048040d1104e1000c42c2c44950860140ea28900b1250814805410050351b41c0c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 394355854 1250 394354604 394354669
    0x105070c14150901170c0d060815010609080604060f060e0405010504110a080c060c1c050403030306090c050d0509010e030c0312130c030605040302010f0614040e010b0a1202030c 78
    0x34031480d4140010404200f003545690344015801118100804040c1081d202c95082000c1401b5291040448601c1c022001440f00c100107401c50400119802042850340c07194402c03501405180965a5164000d40c040b40008000d41c0c002042c144039214000b485e40d85840703294072048816642903405070346520038481408900c0b0201094590b0850782c1c000800c1c6402c40c0300d0380780d649005d0312038850702c0040380000945805110f600801a2032680e190394030058000081c2541d001400190300003442d240b00412209a148100d070441d110782c1e00c6550030411040c05103009044001c124941d60354843d400c0c4c0c00796090800c00761100701e02d4607001d15180c00715507080c2ea01104000304443e40380c0f4401000407010076010010101501c0c1c00070804503195840d42800c0c2d014065039600c0400701440c00500168444000d00c2e900343c07441c411070703040c0074041442030000d09841050000e5540030105901c2049a2241092444d80e820300c050141c0c0e1020680038001000311000c0e00b40c5201f0030181c07003411040039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 394357104 1250 394355854 394355869
    0x8030a051309230703060510030504061d07030c05040903050f0c1e03070b0a090b070503040602300f01150c150c05040509010b2b09121e03050402031b0105070c14 71
    0x1035105d240420000c2e10b0500084c1400201c4d050480c03e140e41c6001180a101b1550895400011010900c028042ca1404061b540311050303c0180d4020084400c0400c540c9030030302482c4d0326283c040d90ba035030030140101c159070100d90101201440030f104120241e1f034810085103031006c0c41c042c8030b0040c50310b6200034104441401e2004000c1c0074160f18012803e00004c0040500035081192450480e40340d41e650311f0180d00038881c03901d000740703803d904240d0194040c540c0842540e141c102102000c4007a1908181c0240700b000a018404410314410400748501c4d105c0c2490802c0c0314001e15445030140e103966009070807207071052400000a00c00140501450800f0384100c0e006042c0c1c0301d8a186842071135050804100840c00030040c0181005208100e00d1005c1c3d005100141d41050078030860b200b582e04081c200c09100d45000780d0340c0085213408a4014001e1003800e00c17071a0040c0c00707020201ca0781d03c0740c81410414405180d05125007800890049a81c1801c1382020740408c01d800138514000500300700e0316 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 394358354 1250 394357104 394357111
    0x3260405030c0c1203030c130b030a060510020102090f13060b1812070f050f041119030e070e0604020c031204060c02072112021906200408030a05130923 67
    0xd04c102c0074001c8554500104030307039018001410350360b146d045e241d100700c41030501d980c048820808080148800200310703034440000c90704c0840e0260b0b94049105003d900340c0c0100100c507a40002220000405418400854464005400b1001072241d07214900c1c14410381100243c00c1d00c0c0c00076083c140600341400c201516a880a000082c00c590389000c0c00450750340c10501450380156001c0400024a440e1600b01c80c42042101c0046503c9010451800005003202b0359800700003400c101c0034030007038600800e07030b13800742c80e420240e1506030b0b5034800c03d10020303602c1681700302e203e8841003182c030910100c41c40249010324816500820780300440d81c0d00030328090864000e40c020300000318419030308950301203441801e5076120001c002c112091040c20390808981c10320b2a05041c1c1c00c50a04130030026994844404080103401030446071200600d101814000c5000c0c0c010070354030420901140c1ca00900c05091480400000c3c1614903440c0d4554805681401e010380380c050704501950700380e2140640942e40d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 394359604 1250 394358354 394358359
    0x5011a010c051b0616290712021818010612060e070e040f06140405090a02030316170a05031e04200303040914040c060311030403260405030c0c 63
    0x1198070710303440e825200c0740440100c0c00481e0f100c40140149851313020607100502241548a101d006003410810f042260300ea80108110030706c682e0f0000c1c0c4940010446025400d83c0e910755542d0080b00304284020360043c2c20080303d070142c41802c14030b107aa076000c00d0801e21403160b08840b00c9514069024000e103a400301089c2100381001014803016031b500c5892a4030491a25042921401d120041002400e10050b0780c1041c0d803c0c12000304000302c0300d800f40d8210304420b8804000c507694081141d034481c082003400039810303082040610a060000d18500001d507004603400070242809030345210301a4440003074400130410200402c2042c44020098200c101c0680c001d441c454980780d520759020004851001806000361000143d4944081040e50094000c07d601000184000c80b0702c2083c03da01160f0803601d005003c0000b05010b40702c1d0141900303052403201c00300c0c115103d0b60360582d800c2c07201c44001d804296400d0400d01d46d2901c04100c0ba8003c6000307101a503524500c0401707c5003000b002448160 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 394360854 1250 394359604 394359617
    0x708120a090b040f03051e0316090803040302040e120d050406050106030b0906010f170a020403020f030a20040e06040f0204050105060c03040306020d1d0d030c1e0c0201030b0d05011a01 81
    0x1804680d9103500283e01a91050f1420090384040c50150740c2401110510340041d290369a8010200180c80300440c05115140c100681d02c0b220000211110800c5010310381e540d8009100c1040142825045403420501c610705498149480d03400740f42c00c40c0c0268111001d110703218000d010610040e4811039000d4041850280440d808910120b00368500141815040103001c28082c00b6442c41586420b50034840e429aa040a0602c9042030000c1e4105002c203902c105503008444141d4640000c50403019035110000e007011880381080209980081201103802640f1202a0140c500d0203010b441d2140d8481d00ba29210010640140011610160062406a48100716580c0703000c40020a8034100ca0703019002694a409801002d030282c400c52120306044580060000d807014404102103001c141190340030403544141c002d00301c070350380080302d070481c0c007090b42880124849210300f603e655001d006042c00b082e2132a104004c5030b20090311101c2554165940c9005084586032040d041c00035040900c0c0c80c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 394362104 1250 394360854 394360871
    0xb03060907030317090606090601110a14061005030d0c0201030209130f0509030901050f0903160617070302160609050c06030c07140a020f2103040311010e04060315091401020708120a 80
    0x1664844000c2e28030352103060107c001880c50717031107544040d590303041c0402036334242905480c1c9402003800440340e00f4250b000d107000207000c80c05205103843c1210b03c010000d2500441400c015a4140708880046c0d04041d020008070020b85c6841c42076940d0290141000a1000c441c1c6440c4421224068441c1f07074150000c200312400e0340e07448019240040d43c2d8109107a84c0350480400686130902044030081e0202d000040001c1d1160000508500690300c0c03549080955910b0200320224400e24500d40b94074515030018078046081c50b41b00c0042c0c41d2207903045070394060040b4001007141d00216003054003d440010141e0400441c00d03080c1d03520a1040004110b440342d60b60001d00103a6060718a00c4c00b0340c0c50500e0700c9905c1000452641d6000c41030f0000d82e965281c8030305064040940c42c18086000c58142c0110315002e0502d0b11070303502180c0d04003004400da200e40507407150281584c02404c0c0e9610a4003003090300e424800303200030151140b00320611a500d0ba00d6a600c440c4014000380481006071030040310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 394363354 1250 394362104 394362121
    0x3010c0305070503070e0a030605040503070b070804030512070320180a05090f040c1a0d060b090310020c07030503040b0304060606051312140f070e0105150d0902040b03060907030317 80
    0x5581d0420300364101b1025018031003012801d0703414107900280ca614189400e1005201d404001840d882d030242029240560710820103607056041540c0c0200003910070002200710013105640079400c076450b03180100e440d12a51001400500c1008032414200c00009403510101c4004428001d003000e003510300010884c500f2000881c920401050304062422020010382002103034014500900040740265080d41b1040c015015030f50001c10070385008515190700403030600d00d1041074400c40341c1e00400424054071907284500281d040000c5c103581a105140f00400011000d10141004e0144014003c0c4c0341e15041c140788040c0d50040d03101000b07104c0c040000a802030741d062150816116565505541c85142e49000303c0c02d0203c40d40e1061050041844400000341c011a40c0000c41d1183c100c0000350340d0b01c8104201e00000d400f00700c0200074504020415449090b0b03003115600d9400180700080000505003c241855011290042c01d600a0138081c010180c1105001081515060f040300392803820f44071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 394364604 1250 394363354 394363357
    0xd050f012009060d060521010f050f0a272004090503071416091b0201020901090303031503060204032103060605030402010c0c081e010b0d170f0f03010608010503010c03050705 77
    0x14124001e040000c2c201e84c40c06001e03004400200781c0035201c1645440b50b181801c119a07003010303080c00d0341c2d4203140001d80c40350031a00503a170080790f050809880b16160f010b45513004228044089440107500c20410101180d822950300060b1300030700640003217140b08190901c0d0200c1007200030303200314038104000010070400001d0751030050780701c25010031000250101500d00300402c10345000c079610200c400710b01042190800c1c00c200c08282d50030b00d01e40301201426400e03405803c400e20300040c0c84d4082040403d1083c1c1141d60940c020010308600562030341c40d060160f074403607041030b00c404503550003007144108824203000c1c10030600e00d02044410308003030005216200280029040241591b01034083c031401025078030040c00d0034002c0f6083c0030410288094480e80842c001d8899518201d45080c1c2c234148440e101c6e609540c0406074410881c40710f10600d07990b400c4070340140900d84041c006446840716900085021705410784038850707298500000c040c00d5595514a0700308040c140014002510340080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 394365854 1250 394364604 394364617
    0x20a0f17071b050118061d070e06040f0b1e1203040605030412050c070e190b060403060509030c032b0c170702030903030f0a09050907080105010c060b0d050f0120 71
    0x820184940b032050038603074003415014400c007800035808449082004084d40c44040c0070343e00048044070340c48617440e40b151200800d2065004448210000070b5862625501110074044007510000d104030044021039007810362228040e4000c1070075030525400e441e01c41000d4400c03213500d0008500c0c0a01301300004019000182000300407107403e03814890001e007d0070940d51a594003000b242c00c11544e41011900c5200b007030702e45040440201460381d15500300c42c081c254007810301900a0386014a1507a68100618000301419840d002c10f0100d005642000c0c0002c003284694030801e1302c00e1800a02808403941d466070344800310a460084006100764201403101d61742d40c4044d00028003070f81c41f52400d9084d0705c52644584d81c0740c0000a420300e5400c02d0b800c003500090516545100810b6241c0060025903003040d140800032405420041203198800c9902c070054911850010540f4030000010843d80419050201d4036034000016080e1890400d20403006040c4207180b48102c01117010b001c08110348540d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 394367104 1250 394365854 394365887
    0x10f05092e051321030f02090a05060702040b12010c0e06120a050403090f0605031b070b0f13060c0206090606100e060729100815130c0504020a0f1707 66
    0x610010308660703245501c020820342c104c80348911490300d603410101c0ca03025507135030700022038940f040e003409015003032003034400003900504091070381c0703042804015043d0400c0000b00e0780540c549000c01d05a89a0100800749004184001301d040200c2c0d00000c0e040844240129000c1e074404d200c03441210354030122940e0003a0100c7d0303000885456900b01182c42e0000d6401c42e0180d4000740c40000750075a40301004610450099020350746030300d00c0c1080048280f04511010f8455608000401c41c0202e10143d01500400070b810408000f00e10360392040150359112900001682052082110344c02080c0281e941c442002c0351150f642580e01e0001800590340c0182d2640190008203001c410881c44421a01010344031441d01c940d6410205445a000e41003240c209a00e40c041d0503000070703080c000155860002003a80c4d80d6062565403d900030601e00307400c00d0150b41c40d0400c86400035003078690b0710081162802d01d41e50030700100200300006d0140e144034518490400c40d04000c01203880d5001c02c051400c0e0700340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 394368354 1250 394367104 394367111
    0xc020409020d0b10030203010501080a170c0a050d050c1005092a0d0c0303170f1b09220b0d050606040c020f011104052b150e010f05092e 60
    0x503400440e5600c5020000103008005100c140a8130601d24000c4004981c8210002d1000d0b0781c032001b03160388441290340d0013170220380e99017030404989581c04090001d90a41c7c1d011518005c10705e0301c17070510300644104c2d030f10085100040c01400ca540c042c01104505071402c0801d1001d8113159183e6070b9582100000d60800c040c00b4071990102c2d0000300c2e564540210b009061481d001d840d410b000c21400c000b440220082400c0b0840b43c43c26607001d174030503071040c81809090b04a80d601c40d06610460710702420a00400c18003044012a650b845040e180104840410400031203140e00a5090450b283c0008192003406504484d500203400066016844641583c0c04901050610416031900c0d2281000040c04d50034104251a0340e0745200181c411600d0481d0114421080c500e45c0c00407a14081061501000c0404512000304100d4203414808840f14100020040344030301031903003180c0004244012031a11881803090035071080190fa98485500c500101c940c000c1e030310700120240503540100260343d0b00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 394369604 1250 394368354 394368371
    0x702010e1003090b0f07020706020610060c030905030d09050907181214070303020a020102010c031832010614030d2106030215030601030c020105011d0c09060a050403060509060402010c0204 83
    0x1094000f40b03521a4800c018460a0811480500003a002186c0c0c1d500144a1400001000c4c1c0c07001503c9030045400007000708030a410100201c0e0b64a610f20400d50501041203800111601e0401c103d601051060350340d8540e090a040c01c1041e00540540124200200c810300c0d40354070503010014408030707000c0b420413580398031051034904081d040b5032455070b84900407014000145500480c010003078a200f68000c1101d41d128400079812901e521070316148403181c40144800082c010350003996580c0f200f58080b2040d5404d001041c201c000949c0038000760ba5180d040420044103041008a5507600c00c501604800001c514014000740c03003001010306441c0050025411000079510840c003668020b07000d07051071182411400300ca940300b60380700360002c1d203480f800181d000c1c410310036181603414090510309403041000c41403921850103005180c0a1000708071503526569207030010300701ca40c020748410ba206c51a5050840407240010070804072604281e04005c01030b030303000e5012655030354101d8001a1101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 394370854 1250 394369604 394369607
    0x2070f050a12021f05180a260301030b01031509020402040f05030f0f0d08041704060c2f04110d180302100e03041214010c110d03180323071b0b0702010e10 68
    0x3805011b0041d00d80c01083d08503414000e02c59440744c01c0c1100d1021150b1603148141c085540c9100908c0060100c1084100500000341c010794844142200d811001c950b0f14001c0d00060f0413607010748c0c444406074003603400c2000141814403030084003140030000780c5807401c02403001d1502c0d048038131303686000c0202000008040004030b0140c0c0402c00e40a618054480fa103074400688018045841900c0c102e441c1d044a4419564070701583e072024442a0507a14a0441641404003420744a09902c00d4884140a40b003902d01c0c1601c2084480306000b0707481e206401d00b6007001303400d0903105110f400301304d030401c444141103403800400c85080303901c02103200000e09858284051042c0700b2101c09542c07542014a124901d80d031041d03106a903a502c0906446800c01c4145040d02180c0314920741c5a02d052003035492502203801780d4048614004901420850b42c0f01e51900d09081d0b5001d4007040361854148103026100313401d80c41c810006400d80194462810f00b40d030700003a1540d05402e00032481078055800044005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 394372104 1250 394370854 394370881
    0x8090304030b1b0307020309090c130e270d0e06040e07140d0c120b010203070b01050d0c030f03020105090c10050706090c180b1009030807060e0102070f050a12021f05 73
    0x1a0b080f068036a2603050064000b0b449134481940c0320302c98142c03180172800b051840c20842d160107080c0c0021083d0705140c0848039800c0400249150400038001c0d8166070300c0300c01d0400c99100c9141850107801e00c1c00e0000d00107020150703c3c8401c140500d905001c1801025050800a44c00c4800e9080c6004500c4169000008a200d900c0100501d41e0a04d607210507800e400c041c003481c110f04404000c0c001021004012031356400703001c00161035076070150010041e6051541c1d00f091460301410030142042c2d03d03600e9800000340f4503078040f40180c1d51101080340722103003031199500b8a0002c680c0b0200703a82e1101d1009100d03000e55000078103103070741d0366004204000239000160024000114406034401d060003503900200800c140f00c600892041c4661511144100745110989520a600608101032901c07072034001d281c4040041040e40d07080103c18081303001c00c4034a03940300784036400400f1102c8135450705074600580202500250b40c80702104c0401c41c606116911842100c000d4005131a0399000824881c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 394373354 1250 394372104 394372141
    0x2061204110d0f0201080123010e0f0307120b010f05220b040c05130e0903040b070c03080f0c0d02011e0b2704120c11090a0b0901180c08090304030b 65
    0x1c0111a0204420480c80b0f411100525001362034403400e6030784c1e03114002808040c28041207203040250425415a40c001c2255000c07c01003d00700fa42103214903408a0300d010b00301d82000f204410f9031008241000341203020302d4090105081c4407190941381c403012800c42a001310340d240320b2251480340072201c0075548e03010400d4000700800a1180011106010304240d002045100c240001d141c00420800881041d4038042c4180100645c903051420b40e2000c4580c000a1040715044502c0d80c0000101710b150001d0803d203618607103215580c001d10840c0d146401d014041da10156410200126440c0a4001c2d0076000003c029002107070910500000582010020704c0b000d00c018120740c1c103990f01f122898426441144640128021120810400e0703600381802c0c0b42c0102104106550b1361382c907061070b44c009504130700580008100000b03414005202800240c105400460455401c0034030000c503030040c401c403240182801c0c401410803501c415102d201d01d0002801c0c040180b00800ca40741100c00f88002c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 394374604 1250 394373354 394373359
    0xa0209042306130b0901031101180e100e040b040212070b07350a050d0624030c090506070b0601090e1f1410030e1612060f02070206120411 61
    0x4040c00e59a0301d056450105407046070052440d42c01405108400b846080c4008200510714445c4e070f0302e19660a21155610744003241000040d1800d0785518102c8540103000d07044041c6a20780c5450020b40642c02070415521855002c043c1d8828080842c031140c030170381d030402d0b010368032030001101015075645410100d500828400000080c01b9042c030030303040c4041210340824800c01981100c1c151003107044110310320495150040800070800385a014070010b080b40c0c8503011010900703030755a00503280d500070001581c00e1108140895103170303c41d500d031049104216090820725159800c200100784d0034000c0380c100601198080300402e04070781c042c0d0a0b1500404100509603420300e40f1810074486e40c0b01c41e01504d40100110a03000c02e02e0b41c004420410201400303014401000e0f00d140341100a001e880e41014101e015088005112410085440d4060005455010400043c40c40e01a088403d1310400039841441403105400594405d000c40f080440344a0340350204d0b8403942018003000c0c0140d03083c2075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 394375854 1250 394374604 394374641
    0x3030a0306030b0916090e1e03130e070c0807061103010605041e050114030a0b060a0518040603050c0111070e01030f120c02060d09050c0a03050609100606080a020904 73
    0x16055040d0410400e5912441503003105807100031406640352410804002c208a0031513042c494041c20340d000c105000301001c120341c4c412034186520141d20a000300d8000e80c68200003503110f411080540303000700804040341484140d2825200061403541c0b0b20780d001f4210b42c000030b2010184403494000c44454005903d1161707803541d6078500035165920501c1060004028181c00c4040071528807812011210180c4507009181c2c9100d40e0b098031644000c01102000d960b03030f18003c07003940316540035002c8010540c0302c507a83c0d1210003c01c08401e401d48158544203d040400c10310001da00031039840c1070480b0a0030141102a40d180310242000507c0c1c1011641054000c000014085403004541c0032600a804a83e21010201400c0b21468040e0f4030103900940c0c10441c0760f20307211299000d903183da030041c019903001030758171000503008142581c42035803154402c10520542c0042070200c8000d4444d64001080340501e0924080d0003440300030200c0c9103040c1e010035841c01686480c0c0045510210f10050b05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 394377104 1250 394375854 394375867
    0x9190207080a020a0218060904030e2205070e0a1a07051c090f08031305132a020606030f0d03050c0405130f110c0a0b07020109050607020c030d14090906030304050303 73
    0x25510f60711000107034420086c00883c44030740e0588a03143c2d030003507602400f52074032907030f4540f4141d805420030019030750862804654000b5800e0485203008141d10a1030300071406090040000348001c0c084d110345480380c90f812000300b00d8203181d4940035240400124505440c1d60007410300c05e05004142190044800c030100a140442d0380c0012004127840c081500c9082e0180c55000e220384da0b006000310b00f4070390321498800344454640144400502c2288540111701c1c503c0d5104114081c0f00c0380071000c0b210400211290030310580500815a0001c401c4d001801c030007a600b000c203551200c00c3d508103002d0666030008217405942d00000c0750007400016000d19180180c5e42c0951009040f000c2c0200c1c003003850305103c0d02d00703038845030225030710701560000a00e84003c86448401030b81d800900320b0303412740d980d5140c6180010400d0040d1842003220360003030b000000d09202410300f41802c4066500c00c000042c14100703581072114040e5442c03060181c6155109680d0100400d20314419604002c0d03051002003046c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 394378354 1250 394377104 394377107
    0x40e07080906010f080303190608011a0306010501021507030b0f0603070c060f06080c060c030d050907080709020f0313020a2d05060406140a03020904020706020901170609190207080a 80
    0xd05000d1a1440100c4070281c0ea11920715107850098000e1600580082012172010025000302c00d000c02e441000c0015401e594402c1c40342103540707440e49952900f0805464620a00d028010540108000c0c0050010140c0c42005035030f010340010020014560b031103541c2509511411003100701010080c12070303981c074200b41101030414111848100c91681c00c1c030107130700110031880c02404100c0d5517507030042c05810400c034200b040a80045001900a100603c00d40c03070030360174070300480e070050000c80040c0801e20f062121140c00e0848903040784480303c3c0104114401c4510f0071003265409040e40900b001c26103007503c00207041701842c1c1d11000041495104064024001e0400003a599855000080942d6034460a01c000c0e030140f0b00c103420108504400400341e00680100801c041100d41c500103180550140000703007240c100c3d00d42601d0b0183c0c0803c0d9181d165030455103c000c0b02104140e1006240790502c0080e0070041d00030808640c2000301c4900900405464042d00c0c4110351220415803200841e800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 394379604 1250 394378354 394378367
    0x4030804060c06180305032a040b0a14040b12060f180907141003020306010203130605040306060e040c14120109050616050309060f040309030f151a01020303011a040e07 74
    0x201500c00f40d2801158609002040c54802d403065070580314203065982d40e0f0b40c00002e140b40035503904500043d901c1d4040a41c407405004001034101102d4807034440341d030791100a00c454080c1070707080c2c1c0303850f401c00051026010603010f4600c001c1188400d440e140ea10b8101050340c0301c0d03481c14000d800140030b40503480c03c102c2c2540150b1052408008940180340d64a074003503040f012015105420816003640c44040c0d034460313001907501c018180122403030000c8060f9507400b080d46a501910000d400403d05000b00906801403000900e08c80c3d8021001d0b003010340b80c465014020f8420301c0c09003461807104e0280c2d512111032034031402b10484020001d0640504150b80c55a0382200d08040070000382118036401806241501d00822411004202d030381c0d01c828070016450000b901c19414082840c0000000800441c001c00700640b046c0070101410b0804840c402c1910002da10000d81098440001081030b40c0c004140c81c119520903100c0808003414010078182c61140c0d80041881e030b10702a0800080680051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 394380854 1250 394379604 394379627
    0x1509030e041506080f07030b0603180d03020910030911130b1f080a0902011817070b0a020a03120603050f0303011406070c0b0306012a061b0f140403080406 68
    0x110305000055181c440c11958006a000c0d90f400f10f4141004134480785d603105021648858207007000950780f109600081d009410031076144003440341d52513030f4071083d540071710026249007010304003907040421120000c0c0d0702010002c01c1c03904156540307100d141070100d450580d5180c3c1c50051300d5000319010a601101c00382c150200a603004003c0d422a40500715282d80c0441c2074840541e85050803a2250b540c0413002c3c00364a04142e040100d8101c1146541c4d1402012030000c15903610306024a00d1011205420540705500c86c0d08882e806208203003805030045814848544d1614110b07100d1700c001030320800100050780024009206400a000e0780000010040d41642c103410740103600d03041c0180410200b841f03071050052147c1551041080b44a071000c5c095a049101410000f42606041d0b0301c04038095002e00c03100900d60060400b00f002d00c105845401c82100c40483d400b845100d84000c05442200000100c00401c00441c6290a03a070b8203035010758002d941c0c0582d0042c0c0c2c8130740e9420010000901c65 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 394382104 1250 394380854 394380859
    0x221070609030215150f0312030c070804091a031c080a15080f060103150e0304090e030702030a051b0103061409130f0b01180b18180609030a030501301509030e 70
    0x41b881e0314140d00d00081c042140449601c50175141d0740e100380304081c03d90000c4604030f40d031090900003c124119a401084a825800480c02c41400e00031020945040f40840700e0031602e01d003252440040551150242c0e0b8452600100402c0d8001c0c0c0b0401e040c074104065111031740c43d00844956605c10180401c0241c1201d01860a0041182c0d040740041e0480b4a5003201980c55441048204000880b5030800101d441c2c2d0901600e0038003485401182c1403400d051021a280c0d000346503c01001b203092092041b91040a28040025600b041c2441c94010342c1004c005200e816050300040b034401c00e0007035444d131680d80700c110180764400b146400303126040203009007111030301128200014105507208101c1e005000070007100f20301c0e10001d140755078240050070f14004000f030440044114102004000c1c0a035070713124015a56142501d40040031507406801403554600c0020030494540682072500480108401c2d4280c0d03030360040d29058030142c101c861840c4245003094800c078117144d04a607603c100c10405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 394383354 1250 394382104 394382119
    0x7110f03031015050f04152606010306090209060306040e070803070311070504020a051c0b04060b031b03060a03140a061b021006050604030303020310170a03022107060903021515 78
    0x803c00380e449009072403540011a0050004004034100007002d031081c0740a900b0a0b500c40d900a0321171903e00f4038090882e44024010700c0512400d03503454030520005214850f070440c1000e40a40025417503100140800340b003aa01d07034280702e00b0214240f210000500703c99044a07035628080c034025200d43c2d0400c080800900807540c0c005024200fa000321340725003100340e6600e85044014501e81118903042c03400c920503643e4498000f0b120391140c3c1309620243c140407405680b40c0c5080d03403804045d0301c1c090440800406091045c892a1707111003842a0550f5881307040320009070300400c1145e240c20100340000e0034842c1819080715105100850443d580b41b5160b081e10704580e40b00c842182541d81c03910440760890010030080010034071a90265421501e07000356056080e65076220748406a00009c0020040d07040400e1b484201601000341c81d00c518401c1d540c09040c1e46070030180b860076002c0c001d00038110f5600d4966040425109114055840d0041082803040d4200388891210001000b042240a10360 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 394384604 1250 394383354 394383389
    0x2060906012106021b0304140319081605160e071b110d060e01060906170d0203040302360108120c0c010c0201140a05070c0e090607110f030310 63
    0x2d0400700c844091580340020440b10b04965210002548000c0c000ca12000360890135500d040818001080182502224034102240410805091141c7c0d10507400a2008a540f00c0c00021a50002d461225008801c00c81644c070301420074605204410b10341e4460262000c04c0031950401c2000300c0780c0541c8041d0b644818111001b05a441403006001024010b10b4084010350344600c1c0c601c03052072409c0d10960011a413540b107a001c0d1402d603040d58229601c41070700e90105003c10014940800e16458002c1c00070041500070311806900c038401ca000c060300808803074a40d4a0010110849208203005100d1a60900d200005920382c1c2c8180a0044c00d800c0e00035194016009200b007010740e28801000c0000c0c2102403c03c0005481d13040d08400101d0500094000c42e004070040c01c000b80008483d162215039844055203449003418413a90403006592480340d00380903030190001035080e404041e60a260349904c4800c03c42030b1408584402002d640e12000040210b8000c0300146842101d091008880300c168 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 394385854 1250 394384604 394384619
    0x709030c0914090f060f061206010807090506061314220504030806010207061e0314010b0307120516030914030c0f1504050a0b07140408031306052a120a0206090601 72
    0x1d04858020004d58004004112010b01c1c402c85103400060040485840e030109800560818800360300156041d003022104200004030384c0a029407083d411100d2070315243d12000303010304441d4280a441056401c030301c0044e010352203110140c890b8050080744002c034141010083c40180000b160220009850440498030310350000495400fa02c00544803c4051003906100d00d418420342100f03401015141c4844000d00c0d02c0003030255010b170610448090b60b9280c10100a0440b4008a0400e4030fa2031400081001d40e43d02510b600140104600e00070802c02e034281459150109000798000741404001401c11f000d40700002c01c0b25200c1800c20076500103a4030300401c014482c0b022034004c0e00383c0c0c01c00307090040000d60040a696100000d400e010482d01c0c4421050401500aa003181105a00c0010031000c0301818459520041083c1c0c0382051408201031412407203940c1710310b5104030015a015401722051403d10001210004d00c500d000c2c2c542c180c2e88002035844405440c0010301c0d0089100108400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 394387104 1250 394385854 394385863
    0x2060c1b04051003030c061b170f0c0409020a11030a030f0b030d0c020d0503071704051f020709090804051023041505090301140406020c010b0f1005030709030c091409 73
    0x2942080000401c05245071400c6e075081c020f100342250741503500c1d070010700d0142d107501200c14045c58603900c1d45e03c01507498210a94541c0701030020300340c03000b0b500c0401c4000402501150169034041502585a855404080d1101002c16a2080050202041c100c10740c1d0b42c0760780310314180c1904400610030041d0b041e0905458008420164000a40c00b21040c005410300c4403403010624441c4088074a07151081d16038064907041e0420107441a50002001c01c0b8a1030500080d809046007090203840c00c02c88410081c0d41d07210b81b84290300d0b0306038503000e01c18103100100d01038030010178028000c000041c40038000104120114039184207500b4a80000d0f03004048a03009407016030360348500001034000c4d0104240c85507045010f01c0b40d40356480f00401c242c4a02080c071017501841c0310720070160b101c40f00c010003682510382e4001501d01422840a0070445a655102d42c04481c45035400c1944d030b00e40b66103604a0708004c01d0b80000d440f081640400081c400c207203501006904249424880054a410588079141c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 394388354 1250 394387104 394387111
    0xa0512031611060f06010909020a050306040b0103020325050c06180f030403050c130207060903020a050606100804060c02120c07231f02070815151008070e01090302060c1b0405 77
    0x103d0b0b02c2032000540d40204503e94039004038050419888160762205110160f0b803040543d4030009001000740043c9007054001c414000c1000d007015030643c54910f0b95074124003151825914030705107900064071194041c00c200c40c40100a030068880c50f00c0e00300e41d0030009a0305203070981254412032036000c45a035000300a03503090b0ba6204019110700603400c0200050006124901d4016640c20452440000c15900c200c030003091003034001d40444126130502c07038240240205804c3c014005007170301034000341d4005c00c0198400d9008800041c68480c01100324602100090302000f40240007940300404040011702c60b0446203500307804403030342c80584000074440ea11101001d42104003000421280a4080001b04114140307204440d0382554604629140c80021845480000c1800f000c0c402c0c040102c0b5220720403918140c40700c50343c018410700014081c1200501c0001004031080ca414040c0c3e00c034020b00c6000b0743c1c0080000e51216004e80c00107884150740200c46d60301803000d01c650900c074209030280520 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 394389604 1250 394388354 394388387
    0x709020a0504060c0201030f0f0c0908011104050d0c173009120c040f1a030c06091318060615020a0206040b1806040306060503060a0504020d02040e0a05120316 70
    0x8143c606075055411407540d034003c90515840c4d152001640815105054916000d089c0c042083d440c203240242407040380341c004104590400500202801c210801c03a412644103039151500200e840c2800000c500c40340e04814080c1d1710403047e500302c1c050001a0a0608001041401c16140c41400300d03134410103a4461040c406002400003c0140c03608040d807000c0a20f114098802c44150364000400b00c903454500030540319038030000c0fa011410600c1c3c80e09282003051b00200308500080d00010481d002e160f4034a4070400007200020b29083c860340107511003d0160300012070a50b0585000806400203000e02c1e4981107940c7c040702c2255100085030340e0805d4000d03001d10700d010708041030b808207903000904007007964801c1c001806554691740c1c000c000460096000144460505003054141000a032102036403504200501016036207010320b140782164110f500195018110160b6402c1030050f40c03000e0400c0c080e8964100c42c5250740c00085114a0803c44458a010451a42540d03040381681d16500c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 394390854 1250 394389604 394389607
    0x3091e03031206210201021c050a02010b010203091302030408040b030403030914190b09030405120d110604030504050f040b0d031808030c1f0e100b040c05030103021f1b0b090709020a05 81
    0xb84858440c042000382c4e50042c41075415144420304070342c202410242407030740051130000b02507400030780c28800c03005030000904c0a18508040d80b80000c46035903007800e4990041d84e00202280800c40040c0448008101e0614120b03207038035103400d01070000c0521440c252032464030004181d0031118081b681607025401c485036505000c503592548254150010603000302c5101c10000410b01341e5410380c128002d540c13202d00605003210000c40082c000840321580d02c03130552180050000094002091740d05076003064540b020080790f280c00040180501c040881d401c01c81004029092640c4100720740c00020441c00312060055440024590341d100d000c0010400da000652500c00c1c90304044103044a8181ca2240400c20101c100b03922410700151480c42d15003641d90b07080400e85030820b80034860502c411420210700313662454000c5000c2c090800c04040c1c0d038650081901020f031b402118400010036204004000c030b640c0905d4045a1b02c201030710100d1081c0f24050300042e5002c880c1c02110800d503030390f642d0036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 394392104 1250 394390854 394390889
    0x10180b041b1e0801060b04060f0e0406050901060305090606090105060921060117070e010302180405011410050a0e06030d18050402030c1903060b04050d03091e03031206 74
    0xa48103400250031a421440c898000072845501a2460b101c40ca0691805826600d0062100d0031107410307074008240000d091000b04031050b00301206040d2000e4500307041c82c48080060000700200707456088664841d110700000304007a503150740f100d03114442d41c1f021036000f512110108005800309204460740004104410842410503540c0d45007803e41d2212050005007a02400c64102107090700722045003941490707001031a400800c1078100401003e40c080fa51175056070049180b01e03990150b6800e800240c1c0c80842c0c20040300f540203a1050a02d642000c0d000e0501c2d88452424413010f20800b40f1905943d480803494032103565000340030340c0b0010b0003031031000c448031802d513968407c81020102e2060304010003d072a032601d0000354480d0b08184a01592510455440f4079240d05c41c25055041515115043c0110000343c01181d041d584100e54510103460103240880f4192480e400c02c62500f0040c080c011901050003d0b944203581c842d44031114051340941900742110342c5881507100d01e4900e206e10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 394393354 1250 394392104 394392113
    0x906090a020f07080a050319060b04050103021b0106030606171203271506010816021f09020a09050702010501050d0b01050f040f1826030c0c0106120510180b04 70
    0x5003850b4400c0d442c51070611003e600c8100d820340140c060000813070400010840342c00c00b100d5030201d40405241c01017014a05007681440140144e00074541030641c0001d12814402c010b40403c111300345c0b084028050603480f031420a01810183c42903122005851488109040001c52940c1c80d104600c0180d40c110b655019400e4400e0450b0398000b40010020002c441c0300c0740c4c06000c1c0d09810350b854001c507185410300000040845c0741c01402c43c1c400c42d00c0240941203440c0c2c046803000a00300c00b010311824103080d80008400520702c042e0000c3d40303c900c00000103005001504039a208100a4000b000303240e070b0701c1040c00702011403070303000401600c95180144285c1c5000c1d928034050b81c6028100041d01c020b1188850211440c004100000b2200795062904000d4802c903d8100d0000100740c002e0340042c00002200d0502010f40305204200c4046503045080c50250701180040c0084907404802c108903007403840c2c881054400130360030141807840d610600403200c2032124070310ba4021140700b5a50b50350f445 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 394394604 1250 394393354 394393357
    0x30c0c2b0f23121e06040c0f080612030d090b060f24161103060702010b031908070c030c0e070f0f030506010c21030506240708130b180906090a02 64
    0x9a82035100901004450300c031100300c3d49110b080b410343d40d1320800c14451528101820300402c000e03c070764203140705082c00359401020740159280c1030506d000b00740c41303000000e500c4c2c81e00d1010401e540d01c4080340003040458550001090f0701e02a40e1142d110f80c4840d018801c061201c40000754000d42d40101c1c403030f80c1c1240240c90320301ca20010800c403801d12103860340c0030303801c51000f950a030b800014810301c50103c0c2c0b6003841401e400c003d5600082088955420100e038503a0303405840c42041500849078102403090210403261a25070180c85c21018a0301c81c41c2601c840c2d9454090342810190b28000a6582405160540010166511007030300c284250502100a003100500d051304228500c1921000920f62a04404240380e00a00d14404035558010017000c07180010501d03131240f8000311441d240b56480118040521090300100d903a02c61050030f05603413030311500c158580303002000600080c2126424000c1d215516014403400e0320020071000f004464a030135034920307134031102c90300100e60720040b580e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 394395854 1250 394394604 394394657
    0x31c030b1f05270415140a260106050409062a050f0d200904140f040b1b130f050904030807050a020a0b0c0304020901050a0e0408030c0c2b0f 62
    0x3d07245080a080000c14141c42c54854503a00700d010380388062103080c1035080e42006e80241a1441c0360114541402001380000384031030300144001c02200d440d001030007900548080c10000d0400c0c00080d5613450090300a007140c00200303ca0320840c403880b041084011051000514060392050b0a001d071065291030f1692240c10142d40302a541c0d01c082c80e481c89030903810052040226405901c0c1c4150350184000d8450500c400180004010204681c0c0d002a92806401c10382181d00c002d91556003030302c02606620700038805241848042080d058800c0d01031460401d4030800d205e002917048d03507001408003940058400070003107002800004d540d580708cc0042c01940c0041c0c0b046134040f01c2580c41c3e0f000e0500c41907801c1041d03410000104001c3d0300f0289111401441d0544a48a2003494440d60301070902c1e0241004009007400000304603d860307400c040c0c0f00444800d03010f6030b0900d0302065450303100b42258070303040c10800c00100070007003070500404032544291031a844840302c403403143c15155040881e01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 394397104 1250 394395854 394395907
    0xa080a0f02061312030c17040501020a1e02060309060a0b0f060904050709050d05010b12150103060b011e050d0b010206012304091b03030e030a0c14031c030b1f05 71
    0x400d200caa0604c0420580291241011802c0e10300b8080c2c40f410f0f02c1d060f408941c80040000f044030380d90020342d03542401d07004504204400b8000000c140d13203a40c80d41000c2d41c0408080144049020042101c60060040080c2040f0f404000d00501c41e1440032400025807250f014000808141070075049994800600c0c50140304281d1104006903100b2408002580d00f80e64580556031182014030145040503621802015251400d50b40c01000260502006000b1034845020302d001d64051000042198407000d0800098420240300a050790070159009203d00d0501e502150729500101381d190580c0c2c0b02a0703008120104040003181110490652140c019944800040210b0741401c1039022181401d08548202031442c10300608600284e02e416201c0c0c0c1280380c030b45000628688040003191446602036003407030080c0c000281410389440405111902d903080c0e070b44203564954007283ca0640110341d80e40b03240b85101c0e10270050303080c1c4006800114004001c04c00172003031600300540205004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 394398354 1250 394397104 394397137
    0x13200a0302030609150906010e16050f0d050708070e030d1b05010212062103191709300307080408130e040c0e1b09060c0303040b04020a080a0f0206 65
    0x220707804246401c03800c60b42000c4507008844140020311076825a5600086e001004001c0c1e941030040c40341c10444040c0101c2c00003003d1039107500d10640a602614241100c400703441e41c031b980c480300b180009004101d40202c00510b0b07100000300d005000365188007241902070700a03d501c81c4441800e860131f01d45128080210b9540c540d07400001a0240001e0809007051419101a030420304c090014568408000e41d0305204041945140f10000001b0303115044221141040380c0070f01210156120300f64058900d00f0b1408030000c00c08443c4000800503025100030500241080030300314180c0c003240d06030b032200c62000c00410100704074500c601d00c1903070000d00a154030342c83c052a103c00e080c00c0003001c3e0302c420780036100c07001000144005024498014102190908010b24106011542600c42c8a840e000d68032004214030003d030301e0b58000c2d00c940304034000c101e079640d04041c140505111005c0300d00320300c6400b010402088581d0082500b103115544480845039140c09542041425000f101407803c09402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 394399604 1250 394398354 394398359
    0xf030f11030103060c0e090c0a140702030d0e0f01050a020601090902120307051c0306030201020c120717030d06061103030a021e0a050a0201060915050d050f01020703090e13200a 78
    0x50045000798444e420005002d40c0d000c2019103401c8505d50b01c2441450900100640920300204580060606240c0f041416045d101c60050078058520042c1d0188528410740c1d050340d4000b11040c150780401c450000000c07003a403004407018450900142c0050300880d0040100100507000f01d0061840100000213862200c0100c0e031941c0c10a003415110741d07014460106400c1e500c00a41060b0304140c0c54180704860860700046c0d80d448a1a010500031440d9151584858030180700c2e070805032110307460f0018203000e45140d00b40e5070341155094114081c9030800016a91f4090505c4040d50300d2480c0203181945c0c0c83d131a494000750801501124440144510450165066030090682e44143d0321950f45603144204000c3c01c40782035810009007d071071709118100c2c1c00348502031081194011610007040354618034046090402d054100d078010360011940300200b60700100141700380e42480e030803c041680d494140e000c140c414260050900e0040c5411046450200d090000741440c01908003503a050303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 394400854 1250 394399604 394399631
    0xa0c05062d150d030801090605060403081b0f070909020a121a04050c060d0c030513020105090d021323090d0926070902040521152205010c030b060a0f030f 68
    0x1503004104d00040721980188100364181c8907010143c00144d4486040c1801c42c0da400c1654171400d40305003400c0c0c80c04205490301d040c040001c65010f402410581c0d070344550b00ca4416019080c091401c80c8200d01043c004a0f004e541044103170b001d42e07007000182c1c009402c0714800081da41b40152080d147d40c00343c0c06024205403a0032004007840f02c01a5030004600c492040020102c0c0c40c0a080e00f121409410088400740c0c0e4042c06580c0c041c82c0c101c91500c0c0d050014800523a507820284041958142803d007502003143c0340c01254070882202030382050b01c681c2c1e071184241e03ca202c02d00d0b424000c242980c8080c01281002c000d0a0540b0b400850040c0c0c8590b000d40d039803842d05072254418201590002014480340c20f00700c034100a00e4051084414003c0300e04030302641c6605d00d100c00c1e0b4200b41c0c1e1050010b0184440180840c0d42d0483e409406801030140b410054003a012404020300400e00b003d4080c11942040411941c1601076503440c81c8040030040c10403030113032050346c01d0403580c1a200c5409800e00e1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 394402104 1250 394400854 394400869
    0x6010f020f010908030a0e0a0201210905070b09040e030c0a0f02010507080d2c030909060d2a24031e02040f0302030601050f0a140a0b0a0c05062d15 65
    0x140500280d6459180900040050f501c00031420241f541080111400503604460160440c0c001ea207529400e4103010f00034000280b5101d040a8101d210361140056548003020041c0141078080c0d40078445036086098060350b81c0300c1c81e85c40040992000d81c202001c02c00c0004500750061052400510344040c43d11540c0040e0858000707085144c2d41e4040000706940308041490040c1c84001510071100c0c0c00b516003e40740d01483c610715008143c00350018806070303221401481d8140d400310180b0400105e9008600d494074042100c030410120440e00803a0183c410311150400300c1015440b5100c422101034100c02030b0920340a41c200403a44180d83d003c20340001d0024001500f0104140c242e124614010903250400690003680030f10f041034010580c0e81c40340340e11301041e1a81070300d09510540481c00403034181c101c1940a0b910b00c103404192040065404000200071078000c00c202e40407600c80e540303c0400030030800b01000003488a14001094010382140326035000744100d940032000c0351003201165a8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 394403354 1250 394402104 394402121
    0x12d0506061204030305071107150e040603080a0207030308100e04020f0a09051e220f08040305030f2a0606011d03030406030203100b1303080f09120102130504021206010f020f01 78
    0x1190300d606c2000b1a0941c4500010002626580180314041c540b100400c00f088800031110304104115107007106544450304031070000c40d800041705558100e150002501d42159000440004030507001081c0c0807010312016a046da6010104020300d81c83d643e080001e029049001d80c1e400c843c81640004031280c2510529114117504012001e5440d0703490281c0c445000000c0c8503a144010b005131034851040641003481e0709940c410040404807199042c504160f00642d07000400610000070500341101161014281018503052001d19036429000d0749072901d0009983c4c003040354021070005903198802d143e41400c0039060301081c83d4001020300428103550103a00300401094001040c845d50800300740e07607a00184020343e4014107114400c1c013240f40c10300b107030710014020f0040402c0010341ca0a0000071130300c44400060580303030030300501e0b4a45e81c00b0f50412220312081d0007040500044074205802290b51a106039582d17552183d4441c8010341d4500b521688810031841402c084a41e400c81c24400e1312130 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 394404604 1250 394403354 394403357
    0x8070510030e1c1b030f1413050918010203100906060e030d08062103211509150603070309050606030106030c0e180d030603023d02031e03010305012d050606120403 72
    0x4910b0501d0740c0030307022401996003001c1d450707420002822030308da03803060440613140d0840c0c0134019501c4105200150802191074007050754400000e00c095002d0032540e80040b01c1e0440e03014450142e07283d0742170300c60602030b100c00394064204140f07541c2c03d03a22034130b40c503030340104002e01351070001c481e02030b04e510403640d0750300d80840c6a0300002c0c07240e1004000303100440a1030a50424504180341103d1907181280c2c43c400a58024180710000c07800942e040e640d180715001c00542040d48900d0802c200030068800454296414002c02c40411820b043c107004940c26a90840388411400f40f81600003075401800034600e00c04a03a80d08510803106d4014040d619400c00507503802f10b85a82540104640c061521180340070716005502c1464544c80852510324140c90b90304400680f484e04120706070b0440c400c02014800c030030588900d002d070400031000558160317030080c0700030420382069002ca004410714086450010252131108072001c080765400c03242e400a0041c02090400908084550296006550460 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 394405854 1250 394404604 394404617
    0x280b1906051b070302100807260708090d05090f0d0c0b030a0605030604110d02180a0c0e0301061d091f020d2910020a020a08070510030e1c1b03 63
    0x254418030410b030301101c000307108040c0420503c1c5a00141070310b18461400418006034400144005020342e1240c10003540328005004034826100c440800080d04546c0a0045454100428404400003a09140401140d29864035100c0d40030b0402c2000050045c03a90b82c080120941c03500010089881324008206040311951241400c0d010391040d41d01942180d400b0790700050800000c00e070342118210305050155034039201d860f00382c00440e90341020035401210f074800b10b0080c000030300d8040d4000c189220f031554505c02c030644428101801c1e01d41a1007201c550358100980080c0b23403496000c8060308184a87c0490f03401c4440104522801b000a607007280400b03501103110320701d665060164004851440b4801c035507110b80400004414050841264081c078450a074808403a4020803400cc42240c00500ca482c005540c1e180c1c079956051240215801131001d106600c03e40d03802405645080071001019054404046803800d08581c455410380741002011045e1010b182c5903084517000c900c1c060f82e03800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 394407104 1250 394405854 394405867
    0x71823010f050702060306130212091f0e0a080a020f0a230d0c1502070602070f0210080705030c1c090c06090b04030c0510020f1c08280b190605 63
    0x9011103000d05862814070508100308801170340c4403070031aa80540c08841d0124407010760f0807420001c0c050202e070718106143d5001407040661002441c1b20041da030036a1188424403001501e00260fa46000118000341d1140c0070700c100203850724016116034401803040300c6078259034422a40ca45094030f05c040d1031a480c0009101c0725081d0342810003400080030401800f00303141c4850b0080856291450180001602c1da800030744407142074045408107901300c1e00035910b0300f059080183e10131029040c2240f103078030042c8800310ac0b140544940c80c481d1055403109803c5541ea08040c0d0a1a4032508440003c401810a0301415045511a414a4a00950007902e2980c1030100c041c0568016401844400c4000d0000308001740000c0c812500b56482504d10488014046009030f2400e180911f80311200c0c040c80d00419001ca4009104125844081d40c60410940350034241d2420700d17409001484244c112030200380f02103042ca41000074200000b030003a105034810310b20702c0114030242c0d030071080c005140018070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 394408354 1250 394407104 394407107
    0x30c0306160224070c050115030b060f120a15090b0c0c060c041a09060904050108060a230a050414060702032701092303100606030c021507182301 64
    0x82500f040ca1907841151034043d0061209403030500401c0032080120f0b440c0060308005081d04101c840350040010010b65036100d00d0103680e800d008485031805000307601004400b91070900181040826542c018000c009070039140c084858280c4024000102d4441645070000b89031038900c14415100900b407a5141c82a8841c01c5041132405084100000c0c0c052005100c2004540010703451036148203510790b5503070581c4000c075003c0d000380c0c0411a0310610303000c0005107524003c240c03648554a0ba6000b0085211011001c4070124503401d003a0703480c4464900041c0300d840c41c0d40d100caa00107008030805010270f400705150502c1c000040702e40340e005800200341918901040e0f034a0f40100c0d202c400c1c81001101c1c840000824003030880c42441e40008001c0503000c5441d0800140100400002e0103031000d8002c017860784400382c02c0ca0320881000078a000709401d00e26102045101d80c803103078100034089540b181c00c403c50b101c1074020460755042941c7c2e600026009081c0c00d105a40e80c0000780703542c100c501030f81c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 394409604 1250 394408354 394408363
    0x405010512041b0b0909090a1104020a030605041b1407030816020c0d120e010c02100e0a0f090c0e0603150112140906011514041a0c030c0105010306060504090206090d02030c03061602 80
    0x32100035508c08680c1000085618a841450460540303005845400828048029060300d900054200345061001c0c0c40b0072404c02c022060001c070540301c001e41010b5600c051446031041100180000d20000d0101e08005600e00e2496103c244920448030103025041c001a05030031009011140c03840c5404101c92884d0300440607641000d400d00b06101c810380c254000c034910b05400c031910420030070103030a810000d0f41c46408450250404101e040191034403500c9500c01012491540d401242c0c260300060b985203440c00c00c40c3e104411103c803007109480c4120064811130044801c1241d400d403101201d041ea004416441d610440d507071720003800365514080c400484c000c0511807010070051040d44020009813000211030441d0b801101080c2d00800c00049030390503001b42880310203d40000181e07801905815013119050764020b1100b040207a84d02d008000031901c0e030f81c800a40014051100c0c00386454910729214070140081c090b56510301040f00048e040034022115490082800000e10010550400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 394410854 1250 394409604 394409611
    0x90e010f1d0402010c050f03030a050f010302011b0c120c15020c01050304110105040f03060507021b0112020f0d020301030f050607051204110406030605090c01140405010512041b0b0909 81
    0x3051403401506141d00607a544912501d6241449812000b207030459202e5a41665070703540000641d0f421401c003501468580d841656036103040d909001c0405d01a611040629040f02d505031a41900900d81e06030041c003210000c0d4068a400c44219400a44c10242d4502c01c542c50f071103007218203070540c24040070b00c1149800c00114411540070085440440e43c02c041140d070010340040c840e42d880100400100d6461190b0b030800d81031001e0a9500108018560b0010f500481c400d03000c0c0c0b000002020708000c0d071086c03480e41260005150b074000300384d200456801807500115003054203150021002e10038050342d00070b910440308040c260100c041072000900140da003002991600505e4604000c40c00032014070003410103006154044000221940c0f20b42c000350007580c1c807a50a03c800e1604c0c00a00362500300c081203440c0441e00b0300d4880c504582c641d07030840d07040e82c2c0161a4032303080c20030080112040b00703002041250b03101050b440345040c10000c2c84550b00180300346811256900c2044050103907079075028 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 394412104 1250 394410854 394410869
    0xf0e150a0213030b0a02090d0c03061a0a0b0d060807030b0106201005070e030604060c090b040b0a050f0d0905010507032405040221090c04060b161e12090e01 69
    0x1440180b410300d254203180d8080f030b500000c0610264a6181c0c0440080c82011103550f0702c02c41c143d00200c200521540030804980c0266000c0041c3d01189841c1240000d042d01c500303512004000d0203200d00b000400140c0b02d000502440003444c9522050042d03e00030b9a42c10986800a40307500410040d54042e000c50120352030740e030074000d45d4503001c005140d9545058000c00c0c80ea40d11040003400c03041c031a04005e80008001400c6414500305418001d00a00a10a18600056058002086a41000084501300c42c803d451540c03030050000000c5425030041d0f00410b8250600b001010082849402a0080d5034003036000003540f0f0800c030201800703d4054104a021807200402e03500000c1c1c4d0410003480031124252005640c1c1c1c0440540b001c0000094104901390513400010703c48490030015600b000ba42d01500c0411031a130b241c000c3c0a150b4010811041c480301e00200d09100041c41c0440c0e411700103800c0e06950341c1441001c0d5189440c60700300c545400c0000d2401402000031a09158003d030050114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 394413354 1250 394412104 394412107
    0x60315020c0606310f1808090d11090a050402030c011404090504080c0304090f0b0a0810091511030604050705121603330501050306130b0612010e090d0e0f0d060f0e150a02 75
    0x11039447d10024011200d0483c8214012803880c014003092005840b8032000007031258610b45401c484003170080000352801ea000e44036924401c2d400394010030400307403143c0300f849074941014907001441e23004d0301005208a0303060380c1c00d010790105440c0c108060400f81c5001300e80480c0c40c0300000c01c92411070b15903c800c44d1281010b80d104114003800410308102d07004200e0030215103c20b440c02c0512201c1041e01c1041e0ba071a20302100318502515075070155002c1c80040302c0c2800b140c1c41f0070008885501425001c0c45000180601040250200369074400c2c80000768200400c1410b00d4040502941d140303840c081102400c84034400b42c456440c6981040500801d007026800c5040007400310303c20f10382c4401103691003560340741d41d9100f950381e0030203442e06000c9601c0c0c0c4845c035603141d02c003000c40601d040c0e40b83c03030f15031250b550341c1407180e0300608518503400f1014100140455552013008042031559106850040d699104400340005d240036503490035501d003005080034207030301503003801400f0000c0540d05024030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 394414604 1250 394413354 394413401
    0x406020f0c0904031220070606120c0b071b06080618010609061d09070315090b010c060b130e0303090d020f07031122060315020c0606310f 61
    0x100c24800300e410139090b150004000da40f02c0c0000c40140f644000c0009040680300502d400c00b01400c1c01802064800d04052204550b101680601e0041c00c01d00140440482c0c070b0207202032410340c0081d24820740542c080d42c0e00c00394a51000380807a6001e0f002240050010b01c100001c504004981c48420144003044241c158076110008106050358091107040104105a0304c4040325882c0702d480c0c60001c002e01c6100d0740e0510b40d0f005001440b84100c801300003183c01c840001c40800c0c5218950103040180c4807101503072032039901c90000b03013250354919912103141e551510403005c0e28400c00c00482030035801150349080624080d80b80001041c064401c6600c07220f04034581000120f211022640e1003c0780e03080740051180048d0748492003d40004055040041c07008241e16260000b0301242c0c0114800c00e04000208c62401c240e100340f400886081e4005004908181099101c5407a200c4040309100d400300361380c1c4030030281494001c0f2101080340c0c56240350042d03011648260302141540401103050b411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 394415854 1250 394414604 394414609
    0x7260d0237030b0d0b0a050a1503050601050409140105040311061008070b09030319092301020a0f11030a08070b0f130f0615081006081605060702040e120406020f0c 72
    0x146407074894042548030032180209840d1030981d48800d99001c020110780b89080c0d4500c000a201c22100150401e060401c010038412802c49420280e03900000034113542e80c204000d1001400030300008690420210020079503200080c4145070080d031082e543d50103070103a00310116251940242c001a5071807800e00040008180025140e07049620044044d80c0f034003000000a425401460784168070f08000b03910001ca01c80c0d010f00071002352240782c840804603400070149000700160700110f01e40983d110026400105411280c0c401d003652107200101c110400402c003090070000e01c1c4100300c40c3d580010820904002c1d06074052a4800382c200e04403c034500d420030880500c1003951201030700c1c2c4c00d800c01081d02400700c0c9400c078101c00043c01c2100a00f0340e5807066500d82d503040c00b80c4444c400515212001c605a04045211441d9071400c0344c03180d03003140c107113820415aa401100c1c2261b01c03541d10818046404010b1010311000b180078141c0700d48852402d076000e070800e100c04851100ea0f03041031289101c244d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 394417104 1250 394415854 394415947
    0xd02070215190e061227061509090a05250b0c031c1506050714010e030910090906120507090e0d05070222020a0f110307260d02 56
    0x10010345040000c840d503d9010442c07510904070b08181140085c81042200851200ca50320411500307190a0300c68200808003030388401081c5c0e14a07035041641c1100a07114038040c8900c079001040308003501d141030543d0b5200b40c90b108d06243d04440c0b06601010001071044403504510040803140c43d03940c43c2004000040703499200d10001090012035100700c0154072520b0307500442d072454881d040c00740e095840304070140281d00400c03801c44060103402c55a190303200041c0601084e1503a8400214105001c000402c008401940d1072101007020202001035003e000303002c2e010042c400798144886000300c0b810700d40c0c00c024241d001445200d06203206052a1784000500500845051600c0c64681c4103e20006d0962901400840d00d000710861061103258110b9006040005803078440e00d104030960701e0705079884043d445900301d55800c10700c11140071418150720400110300c1d07800d4202c400c01c45080030801c0d07a00003505050300e040e0b021801d036288000c6881c440d901c500080d440291003000001d10386059 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 394418354 1250 394417104 394417147
    0x605011107051c170c030403151404021003021e03070e090c0f070f0204050421030606050403080304051608010c030f060513112a06010509010312050309120d02070215 73
    0xa400d441800b00d0240410240000c85000c0c4140405503a280d051a9060b40c6e43c105000c15078480440031201018040306114000513840d0240201c456903440e80c08216a0f411031546034014541c00700611152102c8100241c01c180c076258007107a8590500d000c004040080c0d00480e45d020b990705806124191a199060311120021889001e658100514107018508041031000790014280018081003146001d541d06180c09024607600c0d845401c800100c0945410780b24240105204010901c0400d02580c01564007a0141e403c445080341210007540d0b60024542c02048180d554400320b0708030a03458000c6421110b0344040912000c0d05000004542c08207600038445520b40d80d0650a00c0781b00204d003941c20404407280b03040451864a0941019001c0302d0811646500400001107101d01d003003420941600d4100c0300d2010901aa01010b0307c070341d8009880c41040b407150104092200080600a0441c100851000741e01c5640340d00c144142000103481001000303800b03112214182100c10500e091 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 394419604 1250 394418354 394418389
    0x15070e0d0624032301020f0a0c03030e0304060509010806030a12120c140306010309031202180901050a1a0703090e0112030e0d020112110d111e071109070e0310060501110705 76
    0x103400c1c0030180b04c900a02c0703420480d585d51400800c1c503001403034228003210541406a02c09110300d1038071030340c802d4032445540144004520103200340802c5502c90101c003540040d02a00300e81e00006281c40d0115048101160200003d4030048003c1080c0c45038015008100642d05040c400c92804800d1911180002080c181c1016076039001c0c0c0082c50310403a4061b4540c40084000c5589041c2800c800620058408007940105c00035400001d45081502d094400c5402082240241c441b8100b070141d2140c3c4000c2e01542001403486006c41d0f201c0548415078000c03c070301082c176544a40f41e441c1c00781070800c038a4401e604c01c400d081c00d50800750341c0210402c0f0f020718880340e0014040b0034640a451007401350040000e1441e03d031070b0007049602002d4005004420102d2940050004558803286940c420000020040c6100c07001400c0c2c02e0a02100750340d003000e0181003d500301045480464034090381c0c1d0103a02800340d120507040000d942c0240f10020601c0d403d00280c03e9a50901e404203010319083c541000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 394420854 1250 394419604 394419653
    0x1b0a110f01180e1014060d05090307050304150807020a05070b1b100b0a050901060c02090c04090e010b0109081212070507080a090513090515070e0d062403 68
    0x5480d03880750180108003101180007984050701c1d01041003007140c00f110401610000013901240c0c1c2403900c200141402c90051026140c00080030b050f001416014040c0199840240a190005075092002e80090400c44003c2010307a801200001c0c4140d00103440d00c4155005215604007244022a055040d00c01010340141e450301c0d10400007680749014070040890b802443c801290105843e0001c0261040c122903408006844404011662038284128004180c0451104005041c00000e080e80101c100d042e450815548444d0501a00c0c0c01c47c0c1c41100c0d03070755a0a0302c8041e968200c162040a00201d1b002044605d41c04007010f0328920850075010744024807400041c415900c0b80088803c15a440060b16440d0070074130401501210650107460301c60319840d0200d07281100548901d03462560040000c08580c02034140354001803401a10301c008000d8218406511038941e03441c61200d103403154500007449608481e142514620814840c42c0c1003203015020404034112480501c510182c0100344c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 394422104 1250 394420854 394420879
    0x51c0c080a0e0a03140d0908070c081f0b04141807090605010e0d11060f041a0f0d0c0909110703080f0c1210050d0303020306031b0a06030f0e121b0a11 66
    0x7172054081c1d960103040d070b9405c03c0d140b541041841c10142c401d84c3d105071a88149551280c0038a03448003030404d0065200f0b080f80c5003d021030341c070030b4200e207090b49030150000500e0300f12191103080840d01201c07c02504586845200a484010001c80005007a07000c81040b009040000003004282203105051184400503880f03824031000c4c110549a407070000305007039900c50041c40300350303003e8001c1c3c4a205e0601d10142c00b154549228241150340c4040c008501c51b141c81c3c000841c0350014801d0354a030380c0400851201c041840d0011b8402c40002c1628400303070a86561203480d00800c45207000b0100c45034207540300e05001040c4a0002034840d030030b402524600c1c2c0c507a10310a01d040c590a040d40003c5d0b0081f5002c00007c18560554004e6000b0710050f0309031904145420f00141c00e4000c01c0601c0c940200d024841080300503c00d03400b8085c100c0c4800400715841100807480d510782800094090000c0d0b0300010301c01107050141c610303483c0c3c9903400406001101000d844039215048030070040c030701411905070070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 394423354 1250 394422104 394422137
    0xf0e3102040503010905060402011e05070204231911090a03060902030f060403260f040b0606090a09020c071d01030b0a0b090a05040b06030f1c051c0c080a0e0a03 71
    0x1541c02924003d4001c000a41c0303541002a60f41c14282d8081e800b00740501d0b52080d280c01c4842c2140121046070303c45500d000d0155003480004c003905241c001021180360f11416a0480c601c0c8068001d482041015044030708420080701280c03584201d501481c10100501001501c51240d080c0440350480710000703100629001182c01c0400d0801580520b0003550100420507030801c128180b140d5001c3c2031103110035041030302c4c048149820b0351828003207452540050700003090001e6840c2d20020190255040030070302d5001c80c03c0c0380c0c0950071070b805007030300465806c1d00c690040261034000d0a2003502020342a229401120f6110811b000c00741c1405250303000142c080d1481d80019a01c90070251114049107440301da400d006190035501283d03600c110602080e017a1400255400801e0325070b2018140303006480d041d51040000481027041846024000d030102c041c140504140b420304084008603040194000081c108800240205000d500d0042440c048801c006003000c10f031903060508a4101801c0070b00c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 394424460 1106 394423354 394423357
    0x2071a01081b270a05060a051807020c0d08030601020d030c0e0d0f050706050316020d05040b030a0615020c0f060a1b14010c0f0e3102 59
    0x1400c858929a602c0700d10700d000d0000305200c3c40440e20f0054400c0604490340b60b103c54000c040e003080202c0035180641c40e4002001c84001c001642400001401040c40d1103080b5142c4241c2800516254001c10000541d84d0f8020610541d2108600e001d00050340101c40711030050003800f141e490080d020f4020455072032065122a4100c0c00000184804510003072015a00881c003103220b03402103201030102030054021035949540c0c030700d440d528403281d04e00000c04280c11540410b602d4030340f40340d0001c166410340d0700c0e10280c0c40c0d803601c8420282018001d207410264824840c1b409400440d0303000078002111500a59081900c010104104621130040c4200c04c404904448210260100d5500080c446980310306000c2a0361038107000f12070b085070300d00540322010625140070410300c3c580044003001d602804071400300f44100760325021700109254640580d000002202c80c030500500980 = true := by decide +kernel

theorem cover : BRFrame.Cov 394244604 394424460 := by
  have h0 := BRFrame.cov_init 394244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 394244604 ≤ n) (h2 : n < 394424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
