-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3626
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:12:24.540246+00:00
-- url     : https://prove2.me/submissions/ad76c21c-228a-4aee-bdb5-35754303865b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 651978417 ≤ n < 652158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 651979667 1250 651978417 651978449
    0x5010c1104090b0717070801050919050702030a020118020f0d1115030f09070f060f0e030d0f140f0406030906090204290301060e07140706060801021c050721020d0501 73
    0x203001050b04694994110403601e040010f002d1f4884c9001d4110b580039036010f88903032610001503076410b29607445610f0301820101480309555000000300f03400c0525900802580461040099190241140295106518402c1d0004500d0180c281c0140c881c4a00d40201e02ca015042c08520540111a5003640b4408007004000007651200f28a0340c2c852860005400e00c1410089501800d407030700d010b15000c201540c002e10507080e00554200b0341c05000282210290902000028400201482071400040004c800c0c80c402140442c01c0d504030804c01041c1d6400c05007400b46c21001490036507026104191141c44003400342c2c1311380c801c01080a1141300c1501c414800940c0003483d031801241d06a00aa160a5003000700403d00041c0c00d40140151034540101c0ba440002c02c41b15000d48040030b010249000c0000420f18815402000c146024031201c019000e4822103940858104403800ca000c034016482d80719105111011082c40b80610100c01818110802410400c44000f600842d1002807113901c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 651980917 1250 651979667 651979681
    0x80a03183201080402010f1d0315040c080304081f02160606030c050105070209040f020a0312020706090b0f07030f090b04272003040302031905070c0801050c0405010c1104090b 77
    0x1485101d14042800c01034003a040c10340c0000e1100740d000300164100301120115480c80c900078a043d000d2a000241160100101c40303620740303401c0c0c00c1942c04692041c3e03003800010b6040e0000c410b0310300300c440384009010364003c076a400340b803100351101800c45c0370350f820801001072201c1c445c40100c81500070720340001c44504510341030004003819006181802800c1c003d040059680b0006ca5030702541c0254141040030961010981607142070b00000c145104440600000d40d60006a0b0b07802c44095030348190000e030b581d00c410000d80c0314604030040e280c3d9042002d200424058010240303c4103461808410a03913551016240f103400c079400010b00102048420202045070301040c08200010040030440704805d0350003801a000d02040100d40c40101000140a0500030700540300c0350398450341080e495030501100281a64415003003182c20312220003010411070720510540f8403c4006851031480c4c903050400558010300514801c45038030031401c5841c12a61101c2c0074a0003d00e204028420345414145 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 651982167 1250 651980917 651980999
    0xd02071a1012021203070506090a0b0606120106210c0e03100509060f0a0b04021207081303090b13030c03050d1b030e0405090c1504061206080a0318 65
    0x7a1141001902060052041c945089a4a426190304a80044c400e2000c542603034214003030240c014000c1e002d0030382000400c20010451140c2e4510440e54556203644078010041c4034020410b80702048800c00006110b401e02480c13110f150a01002010740d0580d1500582009031004000e9510000320a0561502c032030808220514200c0e80e500c234148400d2070030140883c1d54000081016504100b2113000c513000d20f17000c0d440a00305203000352055640300080c02070030888917416141e200c0050101740010714070b403200b044000d84140e41603880070000c0385820004e492a40281c124180070030900c0c4000000202c03c424104000d5106030081d10080303c02040c082c2c040701301203005600c2003c2d04042c3c200020303405481020700300c0b411900003405445240e845840d110720b980900341c0184100300c0b000700000315407001d0070869032142d8175296030034079841050083c1d0302c0c588608001030b80190f448100080c01803040c0ba00c0740f081000c034900440e030780301000304030801d082c1208801c46440c5880d20307040780384903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 651983417 1250 651982167 651982171
    0x3050915160201062103080c0d1406010e030a0f02120c030f0d0201060506120703020a09090228090812030402030a1a0405010f11180616050303090d0908031903020d02071a 75
    0x1030554212514041114a8900005d4a0014100b088510000340c22200000a071040c0a0007a0020041c03c09400130201d80514140c035124003188451150700c42c1407a0005124008941c4002c5901048803180d0030b202c4950030294a05419000f44034680300706403400c2109842e152411402001c10100301d0f03a0107803c4610b0fa42100c0c2c0100c10070010469184102d50a054000032989001a520a03480d00704031500d00803a08600c42003030000415141c00c6543c030041507e0003419421254145c01d400d001a900080c1900c5024100d402440d296401000e800025691103030006d410f9400d0801c160343e0300250320184100b001e03250481c1c00240418440244100501110704003802c0007070040c4500d1100040c054105074507580c00301c0b140b012003661107072000c1d0340c10b03a0300081458100c20040d1034200d45035081100d040a0a205c0c0410410207103104480030011560184051407524113108194040165030344842c1091540821151422046610003000d40500401d2002c41c81c02c1c1e2401a030083d2480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 651984667 1250 651983417 651983429
    0x120605030c01080c090a05060412030e0603060d1719020f070801020a09410f0a03020a150504030f1112070b041401090506031305060f13030305091516020106 69
    0x9000c070000320703036084242143c00010a9900a0f1103881010014014111603002141c00140200700001d108440844250001344a0340740c0303510b840c401200384a4079000403500503030720510103140240842c1c2118400c0404140405641d4035007184507003540c1d810b41c61764006600591041103e070130400e90511082c006089610300039442e003000711b4401071034810503014420188000c100580417a0b5281f0346052a0b012111200d00302003403030380c007054414440340300341c0394000c03802480309520b40c5c600b071030207c015a82d005121030102030500301486825210134042d1421301c8410030000c00841e07005124154228480c05c00d26944150080034014101c01c59402d00c44581e100aa0038440c104030b0704140d6007501c0c8100d152109403581c542c0121030b1040180c1c4403e820220002c144004601000301880c00d10303008070101d4440d074442e61030882030700c1c404442e100c42d5108289141c4000034402d412141d0001c2c6444115901d492100c5102c41c0c10440c250742001317412403a0b0582000464080c0108401820 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 651985917 1250 651984667 651984673
    0x605090f01060f020f0a240603050105090d030605130c3b011b0b06010311030c03060301181a280b040606030c0206040b0403031e020c070509042303090d0312060503 72
    0x84051300d1550740d0307010250003090204151007e404013040f040f0101402c441c0d10f4001e0058031755905059000b0803080d1180e81c200d0090b5914001c1d0180a40a50022900068852041007030238450400003803c004081400300510900a0304a05100c480020320340d40308042c0140142d841642c0b040044101c1003480d0303050041110b51480e4034401440d03054071181d0460b0a14256075030700c000403801880d40b000017120310400441070004401145007d03600c10203058008110301c0350252040b40300a15140e1006002c5080b91884110a501c0d00b0003941c0c12030103041c07041001c01105c07000b0304208800801e1403110b0307a03551500030360149803600500c2c00408072820100304581032260020340f904c0001f480901403503807100110b02054031036401140c042c10b01700301820900003082c940300040d501c0681c0e107110520402c080400c1c28a40008400d001e56803001c06281211220241c07400421154250348031396002c14400200c1e1a11209101340e090380c840c3d0f41d018603002a45907030f4401c49015800c1070f40254 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 651987167 1250 651985917 651985933
    0x3060909020603040b180a030305040b0601090312140d05090a02040510120602031510080414011104060e03070317040e0906042d0c0905070320090d060605090f01060f02 74
    0x10725041c2c216070300583c00c080445e105a80e00300d54a07403200030f480690203c40c8224400c0e07c090507032550006018520408480015440b0301c0700440303e503c06800080c100b0703210707007010303660301402880c030f44c0e03600c1c0c407100c40050070805039240ba0b00445908a5188071184c110452074000c5203050f20609511014800e9020300721820071040c01c0002e5425840206081c1d400008980d03084003551211042400092a40210140340b1000400a40c4190b608503490b4001c0c8600044041c4180203ca143e0103070011400c2c141490400101e0340411031400c055018000c240300800807034441d46120311400390601e2003e513541c0c40c042082c000107500520340c0700590042070078040010503101c00301c00d03035075800701c0d018284d15103c0c0c1c3c212050705254200104504244180050b84502c203801c0b00c2d208404a484c10060300b40c103440030864840c0b590403a102c22110800180040380740c480800700405000700b2002a20581b102c7c0403d040b29400d41b030880308410644010041070b03034460400d900b00042840641444 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 651988417 1250 651987167 651987169
    0x13080f0f0c01031a030304060215070c030c0f020d050609030406090f05060a05090a0f150905100e100e2119080304171603030c0207060e030604120c050703050601060306090902 77
    0x240941c1041c141007545520f0351980101c5255a100000d10004040d43da0b85c0e9540d1b01c002e595045890780700e82d0140380000020729514020070320343c0c213515050740b120b5511420680d600c00040d4040d0f002281d002c022a000200132810400c80284583c4042000f160741d030f4200300d4040d05221840d40a425202071000c1c007400961115029983c100301142030480d1140b40a000144442003141c1021081100380b4200088401c500420b0002c201c9003500d40c20f4100d501d400c1400410310388215a000804c0c080204108141414580e503001040700e843e10407059405400003401911200960400c00401c5840c4c12418410510200d40500c184c01307690000309070180c2e03031100319020003800503120017002007016402c08201021500785480b41d0442e44128540f5103405001898581311603030043c0700340c0b4408030b42d980c042e5480b203d6543d401002802d699896a4a00c13150b50904507103441008080120000015010408080694800e8014103541c0d81040c1d0020103c861540c4640895400c1a0103d405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 651989667 1250 651988417 651988423
    0xc011b0336080c040608070e0a09080c1f020702032d151602150109090501091502030a0c03020418090c080d0f1205060604030f0515090c040524210313080f0f 69
    0x44038072162300c902ea1660345540010003050300703000142c5400c200041000a2202c04a0f02940d6921851440040c42010548900c224042c0c250300070340603070100c40e200f00001e001107920f492082d0302c3c1340b00c0d1440c0c1030948081c0d03050210b869140d02d06405102c4c04c1c00050001c50940541c43c04080c4000c00c3e490354203500c400304403071040c840d80711500c0da192000ca00340002034102202107a00b120b510340701d14141481e480000d5204490001150f032800c007424021074801c0c0211411580001c2c82c03580c01c411182800d80c003d03c0071540460302c0340b8590b01d00064000c01441820b03090041da854400c41030041d518060140c4080c03e0b031a485840c80c04040000e1a9118800d17681682c1c0c010500c1040d4120030300c0c0191600c00a1080c29030055181410410048d0300040d0400c40b0704000c1d80d090140340c80d80c1d803000040130811102001580d81080304c0321001c3c1450160520324255101b92a480c14140038180e030706550107425110b003600505079090148020400c810102e54400794000d200f03040c01e184545032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 651990917 1250 651989667 651989669
    0x25170a1103120c03040501021306110d020109031d040b0a03030528050703121d0115050108060a09020307050d0c0305040201030b030303071d03071d090c011b0336080c04060807 77
    0x261243c00400031505100e800d6040d0744032210051800200d450301c1e841e0140c403107800102c10028034411007000b206140e00c10b004a10a080d8903031036900c40f00c1060350300d0b2081d100e103080c05d0341c1c0c1150340d815004810340d0702c00c00d450001310300903150346540700b102040c1d030880b00403d2621400f032009886001d80d007690740901103a03011034062420f20000300c4422142c03030240074420148101205c41d1004a500410103601c81d591480c0d04198182c5510b40c1c0c0c8005540c419412221540d000004070400c2020303210a8006680c803521500d0250314146408407650308503064920200000b070355401c10001103582500c54480004002c178011400d40c5003164000f0a070303100321040349502403e4050200b0040d01e0410010004d0100744481c40e4114810b450000b090400032107110090b40700d07200d07040c8055405074185503005c201070040d402282c00c49880586000d034140c4094078550803040c5103404414a50703000c0307030215240070540d848030b603260045291074400311441081c4a00d00e420000c008024000a00c40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 651992167 1250 651990917 651990931
    0xe040f0f0309051801060f020d050d0c020115030b190b0603062112120609010609270609090507090216140c102106050625170a110312 59
    0xc61000900d20303088a04120590003030380c200e4180c1070b10b0070003450407110013410380b422642c84050240658500302d81e41c800c20000c14000c10000c2080403e05c03181500701643d691154000441c00100034401c500c060030b03e0340c0c0150750300e032080814400c2030a690750078010704103105074050000c1070384200096003520025007403511507141841c4400900841000b945000c1880c1d0301511614900603603071443c2c0d540031110030034400d40c080000912503d4007541c2c45050f07680c142c0d0340c420b049091200c0c0301c1510f0781c0c04010f40741c591b9080959000e0a505401340801504d8111800f00d001c01c4d07985801840c104845d080400d055006120202c14040c2500b1007e80445d0020458042240002a410b0815561307000c000d41145100d249034082c2504106002070700100f105000c09154074014840040b910140500c5500100400105405040400c1c0e02c10914540b003100350300a61482d604c001b480da100c0020303000c0c0c180c0080741c4400031980011b8060341a8083c20302551808040e074400b0028800000c000f1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 651993417 1250 651992167 651992183
    0x10021c0504050a0b07021005061912080d23090c09060f0d050604030302070b0907150503071b1104060b190c140604060b13090b01210c1d010e040f 64
    0x307050290401440701515080034150480b41440000251035445181601078490b0902000c03901c81d00708100fa00c0491050814036440160400c21880142202c0020036182010144a501012041340c4a600700902c010904166500d075010205000c8000040440d03c1c2501314140c1c40707034991140350086034045070071101c0d18080c0020b02d0004000d94034646010703006211301010001007640603070013084054081e003060b400a0b074440c09403a5403a041c0e8055034044000a0940030180d60180018542000322402c2c0803081c80b082c5a4800c044102c04442500c0f40504001d401c4a582072600c50b00700a010052004d03440c100340518000504582002c414040101603200e10080c480f050340c0f1080c03800f10135425141e0030b04140c100840a00105480907205401000c00840e40500500c203491049500150f800c041d40c1ca0120302c01c0c5400400254000030807a03c580d504000bd003000c180ca00608208103091400000e8400c028000000580108450300818020320010410305000195003d62043c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 651994667 1250 651993417 651993421
    0x815040c03090f0804030611031308130b0703030501140d030203070834020913050c040905030c070608150d020109090c0e060415030b030102030601091206091403070510021c05 77
    0xc2140281a40e11000d00074001c0840031a0820500c1d000400481f40500c1c0c0901008080386590715640c417080e1001c9404843c00014100014200c401420229185901145a2a903110f5400d61694407443c002c800281c1d40c2c07001840a00440f12103c40d10030016609d01e10750a649a80280d84e91003070081c090b04c00c02004c01d20703031a08001200c200507151145aa82c0381c42491a20510880d2034000034124031541d518400038402e034a81c0402071a050350000700901c4040500e909100090990000554860208001d1141500020030811000300704550341d0075100d103400c041c6600c40c0040b8142c0c1034804c1c2c24034042c4c00e003d40c5e0320594103400d4807501d542c006050b0520880c2601e42c03014940599421820110340003601c900e075803845041c00301542e02d044c0003091828041500701c1c801204e0903170209044450038000780c80b640d010350043c140708440001d26140140c9540140410500e0455580d6000051440400c1000e100300c56040030f02c038605508204081380c60413481c1100e400c218540070b980d500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 651995917 1250 651994667 651994691
    0x904061b0e10050d0612150c0314040210030615051b0304030503042303010c0e03010c0e130e030f0301090603020a0602010603230a0b0f15060408060f06010521010302010807081504 79
    0x32107480108400314440d148000b035864000350000c5d4445807c40c58520f00b9100788103860007401344903500303500c0b000b68030000d0317541e83c3c01c108036825151581400c242d42c030140030070b030152000036180031084151034558032100b81d40c8900c0d8212040030110800c68200b07020400001c0c2000082e103040c0c80d0744020180100401282d90030310b50002610039a490b44c20f168048859a8000c100031400b01c406600034840d089202d801035458440c040c140c1034100d0341d44000302c02d01811503400a1010b0070300750181c0e440c02d840031101401a40003a00140f0f03016a807610b042085203402c0340341100404160000f841018656183c00001c60350403545a0310303d448002c83d182180505005903c240c0b903201e0300c3c0c101c0c00d081000707031000818011188640c12060500101c1060b01e0914103407011146000f004000703d9407440314820302040003a01c03150511034280300c445c8041101e1002d422289001107101c0c01c1a40c514000148400c5000d0b1000080c400c0000901280d01e10040c5054040d040a036800b150480100c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 651997167 1250 651995917 651995921
    0x1092a050301180b070c290601050313020118050d060b04050610050301140f100210050a1104260312090c040b030c010e12010f052d01090e0109020904061b0e10050d 72
    0xb0001d040242e410041f40c80803c2c1c130341140c81c60050300440981d036541c4800054401d40310503a880100350303020003100f01c0190711038480840c5001501e0035000030180d40e107001c2030003e09003c2044941d10f0700c030001302030b050a0a101c2d0035800b0b0710450b004402402c407044058420f1006004450410317034241055551901d0b054080203000c071010b4800d4008100040c0000c1d2103c55025041070842c0c02c00010800c0d5102500136507600441250000b8981032030509142034500503000164029183c040d80c10803000004e0001c0d1000e81c0080301409070718070b03002051034204801d44800f1807081e0310303110301d0850584001402828010702803c0c4840300010280000d0900758841340110310300c0d0308154031003d6240180d00321f00c0c000c90b10110f0214190b00641e07034002c0c0741081110340c0c0380f0104502c0010031111000c1c1d041030311005401c0f03000180381daa868010410700c0d0710484055900d10384820010500e03080195040381a001c140c5480c42c00e85400d80001031f01c2c03080b441e07001810402e0106946582a54036 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 651998417 1250 651997167 651997187
    0xc01091d090c060c0a0c060e06040e1f0611010f110a030902030c031c1e082202030106091a09060307180638040f120501092a050301180b07 61
    0x18140d540f180011044c840d507442d14040d0403556400c9400e00080c03e0381c0a80c0c00300186410041c6124105400c007202d420480100074080c00320b140040c034451030030480702c042d0304000c0e0206540e40300996280f000355034203403200014100310191800300c1010003040610300341c807039181452a01141d4810300740002454041c50404142d40b602a108100c03006044c0280c02c1c0402c0d151a851f07034103011001c54005204100007090301cac40424842030005000c0d034188062000708001d003d0503c85806081c0e00400d0031650b40750000045960740f0844d204000d0040c0d0104801420300b214519180c2c030700078002c0394940c1c030580701e06544c0400c9001c8c00500303042560042c9001c1c0c1185a4100c150808040005442c0c084412950700a0f422800076110400c2040d0120b90582d40081140b50038285400c03445100c82c3e10042c020381e81c0b035690b41c1101001903c100c600600e61180c0c1203c030840f000c20452400d83ca8101e59111501c86d17890203482d01d441031940702c51480c0454000410b210541e8440c001540c1303207008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 651999667 1250 651998417 651998419
    0x1050405040e030702090c031e061c020a0b030921070c0e070c02060f030103060b060711130912022508190809030f0303190c0e040c1e0306080c01091d090c 68
    0x2002040001120401f8050f51140010780a9051030540040c44009440800d460315500400c0760b908110009000503184242c113480a8400340300d1660780e1404081540081d101215583c0001200e855807501c401c21600c01c400722800304074901070943d5281442089644903c801c140c0005002460301c0340a0801d020800380c0140c1201d039548264401c49015510901048408074075005c03511100f414518140c9240c0c5510842101e650781c511410840f0581d442201c0c1c001c0300e5152000800012160f000c2a500b0f2601c81d0024840700045083c000082d2254007550124032600d41810003150500007520318000780400b100003620182420004194030803c8011134140c880d0b0303501100b0203031001001314420100c4c40c4950403096492000c1605440340499100300180310405182440e2030140d01950599a142c00d00803901c0032400c81c0f002c00d9044000b07414000c240e944000300001030003840000c40301d440034a465a122804c0c01c0d500c4c000d200b021a050484003104100142003801c0c00c005582060300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 652000917 1250 651999667 651999679
    0x601170a23040b0a061a0304020d060606020c120102180105090612090d030e1605191a070311030a0228080f040302030c0102070e060402070501090209090a05070b070201050405040e030702 82
    0x4800858100d20070015181101e0601202c0002000c0081e588070710381c1941d00e11482c1002030007414a03008034581000d482030303a1213901103a80f0f000003401441400014807076038000e0175090644404008171003101c1200c410f4540d004100d6910100c010203600c4203000001d003000c0361110007800c0800c07100c0c065010f280255010300c1c400d0080d1081d00140300090046907980031300c141503083c10f080d6100d280d880301c44641110b840d08107114030b19181d510583c100006000d581e12050351071202800941009841e03100c000b20005185051690112980c540031140e2001540390604501c00250b40760301042450000078904002840300c0c407003100070703074204581124030b0b6502c40c2101101c003042139010b44401c0b0710a104003084c7c000c45500102c0c8600483d0071200c80385200390744200c1400301070344c8400c2084030380e0756a031205400140d03141d141d001d00607444c0034000c044040d420700e00f0030714000312600f00f032900c4c0c5014420540140c0e4480204c9044e100151004100d110210081c41d01c1d44c0503000c1c009501203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 652002167 1250 652000917 652000961
    0x121508010204090e061803070b1e0c0c1b10080c070b07030f0c03291809060603250b0a0909020304030f081f090509030915091005030601170a 62
    0x1c80c960000e0003001201405d0382c8854446501ca440100000d440c8104182c00034091203010401000032181d101e24400e0800c82c1102400c108504600401c44905240070710204500700c0c2035204100381c0300d84035150b56180c02050360381d400007030b0041070000140c000c01c050800002c0c502c0801500f0b803240700e40c0c80245030480f41403003940903002c0c001110b1030001c80c41c0f414511a81c0b1910900070f0f241100400c82000811052541c50202c0b03081c00c020005801c0000b03d00e1403060030403101c1f0f58038824080320002d03002c14180401018113148501c1401d080014000d00c0314880c03880c800c02210110307045111600d07a10540d1441c184c401004a60001080510110030401459004404020f43c6101ca641d5808181da80058141180b102c41e000601c02d0384040e00d050040d40000e034000740d04003903460216410404110001845145401000036001d07402207900c2a5900705428025200d2160341402800c0d0718040c00000c1c401c0c0c554804402070102480c0119810052a0344241108201114240011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 652003417 1250 652002167 652002179
    0x20702100e03120f0d0504050c030f10051303021f0603170a02010501170a020f1503010611010e0d08070c0c0b0316020c03120f0d020f03040606050f0d03121508010204 73
    0xd21011900502034007940001d0702120f8030030f00484041d0055000b43d81d040016035140b0700002c00f03005004075824802c0341000c0809503010401c4440d00c403143d600a10803c06800c40c101c06a40010b01544480c0001118807000680c0100389540c1004d0081c1c9081000d86404480001a156548c0086e1001090314003400400c0103038401801100c0c1e040c0c009100c9a40e0b2001c000c1c0c48410440b982c0c1d801500203001c007070014546036417840301c075400091916500c0709000b01c0700001a170003a0700040115a0401d10301c0c0d001e800a0086440c401c04100207840d499510b040098406440102074500700450740b00c0810400c045001040c001d010380f020000d0b240d03d01021400214815108d0340e8000d482442004038a41c50002064564000b561812500300a0390f90a0f03011190010760404c21040c0c0c09004410b0050070030300140d40300360f001e2040031400340e2801080c0040c620007040440d00130704850158101080d00711080a1044100403800508203000050150200384290041c442c01c0d4000540000c0d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 652004667 1250 652003417 652003427
    0x40f0e04080d02041205060f070906050d0e0715021c0804020904060e0106180e0627190f02040b0315011404060e0906090606060703090b0a090b070c030c21110402070210 74
    0xc0903220700300711689922140100c0741c1008c0d04451040004401b400180051481000a8440c289403400082003c1814200107410044950007051110140e441c42d0300b0b5556042005550007407508000c4110224101d500030426000100040c0c011346400b800302e020403003258003405004406000030840c141e03d982402c4140c1942c8502b0503e030074100704140000d5030000c208a4041c6408020121031800903d0344d00080c5000c01103050502e000d0f240c542c28081c0c51896502d04118030403000021100094810001290344e009400c40c081e038020b03460915840780700e080c0581034884410b1317540414120540010042e0003145c20540d000e0201c2d400340300740c1c52000035845e409000d01c0016501999104002c1c4006030162140181c0014a031160410000541d84000c207011485460241079071615698616800d030301c079440450350410044020028403040404e004060b1440e00d042040740c01004000310090f041011010388100342000e0001c1c25988c5030390440c0c0d80241d0180c00743c0c51452003000040c0c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 652005917 1250 652004667 652004699
    0x7030c140d0210091a0301060215090606041509140103060f091e03030917070309080106050607110f2701080303071706010210021909050402040f0e04080d0204 70
    0x94200440880426000362250094103064005048162a03455070b07002c0000300c00b0004801018000490390100383c0c504050310b050708503000202c1081e070301d5152850003480c0c402660201d80041c6004014401c840c0c0c800b05e0015000901240c1c0890f440d1000b00f006088000d6a1740940c071010300d450003040d482d4004154140c1241d008000c200550260354603500140e45441800408000c0824100415405006080303034003103000b8a070002c3d1407292903666101c0c004000e500102a0304000c81c0c1c0c441003650000c41900034140440007807020601e0302021910130b02550304010700c2403045200240942c3c580844002103220001c00740314500361860080071049902021104000000d00004074625200104981c02044150390704000c115800480781008900a0071090440c09240110048bc0e15203001401440b020307110760170440261404003030450700c82c560000340281c1c0140010009134851042d0001294048050000c0c40d40e103074504510107115108a040e1034520109000c1401120b00308120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 652007167 1250 652005917 652005923
    0x20f0327040902010516080408030a03051504060503030307030e03130f0e10120b040203011e0e07061106010b031b0d060302041d0705061b03070f02010f08160509010912050703 77
    0x24401035029040c04180e400d84000a400b19004122130480a01240741d611200b42c029010a4200b40d200c01c000350941d40124142c800003078841081c0300c4008054500140b04020860301003010910340030210342c5a00004007034000340f50351440065060381d0700307008640b003240d00c0c1c070312080d00d0742d0711404031074aa05640d000300c100b407107103030400210b511501003851016a8011751510130040d24a5498080700300c0010812a01552103190034a50700c211015011040308103180003140030805950040c3c588489640031204000b8000301e000607000c8040349040c15036000000c03481d526130300c07081821000c0400b900c9883c1c3d1800001307401c002c10f403d40d40c45081601c0c8202c1e0144000d080f48031080c81e07e5400940c080d0203e41003e002000537281c40001045900e49800101c031441c00c0d01008181107410800b070580340b00a41c217076400119070303100e143c4130250241c0741040d043c10300300300248140c038100c50300000050090000c0c1400f803d80c059a601d20003822004801444844c81e46003064940c6242d01c821 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 652008417 1250 652007167 652007227
    0x904060518010f1707050f0103110703090806090d0c020622030f111509040c0e130b040e15011205030403020d2003070b0a0503060f06070f050f1b090601020f03 70
    0x7080d0b00108011507800780c02660010300520741000c0403c03051687e22600c007810701d50368848001070100c0d114068140b450003a01c403059030382e140c03414103401c025008085400a030030a401600085801ca10001c110507015100191110100c000c21005150090004000100341d0f520020070401c50002c82190305100748148580c03000c45006000b84c81300071101408415800b400364803030905080e132102c1c00030056450417214030742201c0f000c141e51240d00d80c036290328113458100c044018141801525a140001c1c40140b01000071140a03403a101c406014404510300900e64000c1030041c100240d03030245400401460007040140f07031900c1d034011030907143c803403c0d54103038510a01884c020402200b00e8070201c0700a890650240b108503102c1e80f005240651044d1100c9141081340c503444058103405100d036101015448242c01d1042ca8010904407a80d0740b90702c03000040444144a600e05842070100303031070302c458644415005034101000c0000305a500c1c4008900320507003001020f5041010210162b0f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 652009667 1250 652008417 652008419
    0xb0a060608070c0201030e0c1905091b0304240203100602010e0c01050d0b01030e0a2402090a060c14061f09050f1b1306030609060b0304020a0302060904060518010f 72
    0x10a865201c4200e60b01d602054603c50403030301550082d006501c1c141e601c0c01c10f40311035400f0b000026664910380030060080b000914010700060401c1848141c20410b2104000d0f0882c0700c081300d41846210052000b000926010108500402c80d1501c4192010031480150744038545000d007600b0b0b020080c8030340302c0150f003131218070000031501141011001106a48591422001c60070020182061504090401d07503034031011b441165003401070000b518440d10080e95032202030066400103410300d00060314440c0c410050915a81d80343c4540c0812220700b4209800019010701f40025800d03502030a05085006040c00c224192840842000c880c00c0c000c103034000419200ca03841812990110380e10300340d40825078040788060303a5003c004954843e454040c1450000425070140d44099103500840200761200c10510404002d4056180a8586048268214500350f000101c1244480c4806409014009071030300c19502c550704080003808018102228183d81c0c80510114101e0901c614801d441002e14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 652010917 1250 652009667 652009679
    0x3060a170c0906030708030c0102040f0503191b0e04050f0601120c2d03110907050a050a081f14100509030703081c0c03151a040b030a0b06070b0a06 65
    0x161541610811000615441265000b40001520301400b01c0b41c3c9071003041400110f201c1c08000030118900c1c5c8000150703c69140640d0942c0180c0070360400c600c2500403121118000d6090b00c03000c0525034008070032220400c00d60041441080755078100480014145007008140000054044480200300c012140c00b40e90301d5850f00407100350600c00030b000c140210300812000c40c11000300c40700c0d1041e400300d8001c09287e82c0b0310f400c101180c0e03500442d01c4161200091650f4500501c060ba4029801c0c145540342c005110170007451403040c1d451103010301076520b010034410003607203800c18400d40400f0000d20040341c031103a1001c09110b01c040c009100e548100c054985240c86281611036011000d00104220307815070741d03100416009414044441540001c254030301000301c0c0140b207800c3c102d41d02c002070001c001440c0d9160400e0175800030300005090300d03028101c0f85090012601112043d007125612911450800d1000d000d40c0541c4541c08480480d104090001c0070400f94010300101100b08040340da0380c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 652012167 1250 652010917 652010939
    0x31103070806061336060507020d090603150807090b030601050604121205070204141911031306020403060c020d1107030f03211505011214060415031703060a 69
    0x580707031500300d00061200d05480d40070360080c403d0308114882c07a03544009510030840c3d00d6007902c0d185060b40c890080d41172003480322512555800c03001d188003400401180302c001401d5501c081c400c0741c003015034070075208601d5403000803000082c2422505407124103984a400001506e41e0100c1c0c42d02c20701445000090519100045030200da420f4a031140c00d442c000d0f220b0309a9108040c8014040c82820080c280c01a036440c41800203240780c00e0390324016418504a80c640c05003402c5a030030f07034040c07800c1c0d05000c281010f41c080d00c0d84042d25141c0084010300d246403a07070107400750351b000074805800d0402c080c00c4c2d250003140190108150b550b49a00040c0e803c000c195681c211440050000f004540382c49022a100da00107884040294400c10504641503074203008541c00c00f011007540c011207240901c060340c0d22100c20328100c034580000f8041030150201040c000384000d002e944c81140d40e01005c070750b101c9601603064010354100b0880c03142495603614546d1664400c0b034849105203075041002c00c44049032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 652013417 1250 652012167 652012171
    0x906050603160f020a06090f03090914060909030f0c1510060807030b010908100c030507020d091217030903030105030c040911010309060b060d02180418060f15031103070806 76
    0x440a10008401c2481e41901c600807582d4000d4118040c4500000105806d4003e400c8036178810100510f5040c400d06004000d5221070700045400d90034040740d0380211400d8100581c1058003210310101d40e464200105107940b0500d0115150001c0c00319200004240c04a0314442000c0441d0304105241c0d00c030524210341042c0d40c000e00340420000e001107a00f4600c660300400602c0e4040c100907801c281c03501c6c2014a001d05814039814865190010b1a0046905003d1130390850018001001182c0724102c000c1c0035a6450b001d0351482c40090f03400300e4240020390352021059841c0100c0f8950300d091140e03034280c50f5403090155502038441c40c00820254146407040d4450190400700c03c80c40c10f0903c10046003d8400c2181c1542d05517143d055041c0280d640f44002c1c80d4800c403c3c0d01c0140d880d2074402c1c0350303c80d80c1e440a0b0170070720032850026000003900c80c042000c0c1c4102e44c400b00000c1c40011186a81000f0b0404882e0060170031a0700501104000e41c0c240b2000413104220b0446401685c5d5801c032640c0c0b1081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 652014667 1250 652013417 652013431
    0x10b030d090812031504021803010b01110a150908210f0103031d01030f060906030b060a05030705060a020f010c120e06010b040b0d060b0706021b030901211404030503010906050603 79
    0x481c002c01018035820700e0240d80c201c10321741c4060480c404c2d5500050f00b40e810040e986520414018042071061400344078103074800c00d0038240617245c01601440c2c0c4d03440c0d100e03d41d0080d1101030305200100051105a2180d800349070310102c01c6456070b548401e40c2c1d038a5184c410381000f000318000d0200341c40c17030720540c940c5048a5240c3d0303035600c078455401090120384000c504c1032418951a9041d2160101c028060007003d00007240d00040c01500c1c606001c0c0d48000080d000d1070040051040502054601150782d00648009480d184d65800150200701d02d0161540203000c2c80754070704410000d40a511104070244126070380004e001d010000441c40782c82e420b00b885245c101040400c0100700c0b080e0090302404600c107a9200c002211a070b1145010210350121000300c5140d80c0c00500400b4412001006025030040c0313070021400d040b40300002071310b0b001c02d0b14010b00c08402485994a100740164210562208200403c1c1c010743c2028500640590420f0144500640c240440460325042c40b205030382c0b090308 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 652015917 1250 652014667 652014673
    0xe0915010b2d0909040b0a060b0708030103030e0607080a0f080a230603030c030f220f03030e040e1504060b10120213051f091d0412090512010b030d0908 67
    0x1482c0c55250811480c090400c200d1550103110b41900c0daa1807000710391060340615902000f074500750404104641c1d107604249642070080c06005d000c51001740540b41541d90504003452000746a80019246008808004101410010324410f40503070128043e622044140c80e015402d440b20904601a56079502601e180c62584e040048404c01e01d444406d900b042010b02964942842c910762142541d000c1e1700703075044124000503201c845200e0042040e03115540c0080560041c2c0c00c1c240d0034411152188001340410540358246000307030b40c407a4004070b101c1d02000110343d031001840080c1a007040c1e0440301034428916003c640001802e02c0f0407445540d80041c2e48065090b5101c0140100a4102180f01961084018030124840c0c41b542c80310046a4074030310b60502a001d2090f4010107155490300401d540c441e41e41d0141c01e480850407511034000d580701400002408a1890403285205c59031701c030503070004456000c0c0e01424810b500262071002c0603010707508118002941920075041c64403070848254 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 652017167 1250 652015917 652015957
    0x405030307060906110c0c131b120b09012606061c14011e1505060306010c030228060b1804030c240507030c0819090501060e0915010b 59
    0x80069000c4524140b04204c0001e003120221044200360308081c0100b1007581c440700f400079480c50010780b8410b500304044000e0203030310792540710010340a440b2841407007030100015012840030784e0b070340100307800f10700203000d855017580d541e264421000640c0314048031604910801000a181c046a13651144d031020b0011030780701074443c1c4481500d40c4000402d0f00d001c19a00b0381039801c28420300518400c1c0713282920103414119104602030441304004090b8000c0010704508104544601098030390080e02402c10043c03040b51414164242420703070400700705586200d12011540c1c81c500c00410341c42c0b4040da404100e405486d00c2880501207201180b0040c111007140002d001920400c200c0d91524840c0183d010506c41c2c18a114594580221a084005488504120a03181d0510481900b2070192424200310708185003114a02e0000841c00203a89854030408000d0000c04d400500081010b8100e00c0540c0c0380203001031780c03114a2280c08400301044c200c000074058000d2010b582c8034a409a8000d00e030b81c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 652018417 1250 652017167 652017173
    0x2109270714070b070833010503130c0f06030c0c0b0103140307060c031b0206060a0b0c07080304141819091104090606060216060203190201110c0c03010f020405030307 73
    0x141044603200070502042500c0005080080c1e2a0080d800ca44071041141400050100b9000440034400003001c0c1041c02820079400203150006480740a003001d079629142c10810004a04940a0142c4182903058002501c0640e0808540480e64555010032841d0506c01080f0303481c42c0d00d00c1002d030200461130700600101c0e103040c515020141d07005044907d4203417184c0e074072402d0780c01d5051628042a81d8008105240275940d0b0220000e520b2480a840140f500800144444019000b01d0811010200c0d080e0041e031020480c200282032107504694a560341c1d1090b0030021201703c9452405414400ba0702c1221821080c2c142e40101032580c0d164400e56420140940109128042900c64112006c0310f24981e450318494030326081e00034040410094103000d000380c0761500402814654000e004800c21500f0340c044103031081400845403040c3c6040110700c080340544509000d8246170303100010807038070f240d10001e841d0180100580003404903007165440f2078101d016510406415400c100110000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 652019667 1250 652018417 652018427
    0xe06040b01020a0203060112020108100501170411030724022a01050d060902030a060608070e041a0901060906030b06071a04021311040602070e0606071421092707 71
    0x40c0e04041c4101c1c0c11464180d0002450310f10281e00ca1808106d0740c012000555034811030895200c6a0070f1501c822241ca0140000c081c0741c01c4002c00c012010007c070103c2c0820200314004441d401008048070392940d128285000d20b00b9101205026810b40c00f11250721190000c19805111b00300319541e15031504400c41c40c0c1a1a00e11f028043e4100242003046200342d40071449200050400750400603141c1c82d0180f694021200c3c1c1d07420034824400840104880c080c0e0040c5000e0340200190b60200f0500800000396144059510305950300162072000070540c2944001c81c4001c41e5071503541030003100c3c2000d090001500ca02c1d98040c11001441c02c0103103003094669021030b089880500a03188681e01c81c40c824044803180c22282a403402e000804000d15541002014040d290440700c4003038a0a000000a4440c400e0520040003001c8030b102c0c000e00d4400c01e225402c40046c012000307003001664810b40000f00d03408010400d1194109d03811460000c02c1c1c0080c524501c20010504c1451a140d4400580b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 652020917 1250 652019667 652019681
    0x309170901081321110318030f0105010305030f090a0306052e0e1b0d06080d090501021216290403030c05090a0303120204030501021207020705122109090f0403020d05040e0604 77
    0x2401005c29614100b030b0310400003031108000c01400407400c0c0710b154003014201f1049000584441e81814010300102c2c00100c201c5054100d240062a0fa5640e5103021840203510f0368005800e951410b000c00014088601d4040b01d41d480290507103860810310a024644801301c0c0c0964900c0b90420300c002000e540a0444040c40044e49a11060038100c0841c0c0c0c0506803005604120100d4114514034250550885a00c2c0c018007000d001400c0a00d11005a0307542c2c902403c01d084100c581c0c1c0180490901c04030b141d03559206144070700080c010505410070015010020780e4120002231404288840c1c043c071441c01e40f245000300a08000c100c92841d10300304c072400000406900c0480d03080200100180007440140862041301c0d0200c0158078100001074141206940901d0050140030403040c90004049000600584100ea86c100d50031001c3e600003c15014403141950041d400200307002c00e00b00304403901e074440c03071080c0d0803204440c11001c0c1c1100c0500440c490071624140c400041403039450607410401c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 652022167 1250 652020917 652020983
    0x12080403110a0819050f030f0f090f0a0609081608100e01110a030905070801020f191403040836041d01050c030108010c0c020d08090103091709010813 66
    0x105049846103a800e081c590781c28820108129600d01e44e00c01c00c201070068030189400c0b0381c041c50800350500781d0407245115444c80308145001c000b440b6030b6540d0300d840800010500141044840b40d0b210b120203060001e05020743c1b4420700c80c414684890002c444507040c142d0b20100b0243c040044c1c01201500a4461040085065521140940958000348000e007050507aa56400310301c50f149800c00354148045031f0003001880c1d0041004030440c419002c21100c81c00d0031f941842407918a000403c0300c521066903100c480f5254000240418403008801178440305120b800300c9000c14440c0b01030410040c220b00e805c00d20083d00c184000788145040e603c1107144440e0107440c03142000c04000c5082c02c584084a01d904a07003c0070005204c45c40d400d1288c12422410b5050044000d8241d4000802c2031568410040000c0000a075070351490b4800c1e00003510803035001d03010010398440c1c601c0c0c0c000b01d50402040c250000e82c1240000e20021503004050896581000c1d1240710000032442c0d10404001d044001c2d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 652023417 1250 652022167 652022179
    0x6010c021e12031b0705030c09220c0608163510060206090307172209020d0c0801031a1b0a080f060d0302070506090d0f060b04061208040311 62
    0xa0710a4035060084454260b420000c1e50343c0da09090310110030341c400e80340c0610141d80988001d1185440c000b0303983d10440d80803a110040c0f0343d54080e501c8031504450f04200c48102400850030100140b105d104801d6440d15210400103660300a0504a100c500c1c02200d00001c47c8020140010300250204480800c0308c446003e2854140051f592404c0b0320940381001100c803012002c100e5654140219031b0059030b4200903502d0300c455902d56a1a0b4210003500400c41e00c000145441e00c0d075941c61b0b44107001280c2105845c503040e660340411000350404400703c034940d401c010300b96860074854400103050300d034404624910401041e10b102600500185060780c000c2c078400321001c4440c4040040c01e0039841c280e8484000d4605243c062074035040181415015615a408140004c1c0e0080b41210542c0e2040d01d4050b00c0b8614030000940c1030b07501c010040c0011034030302c0c092814000981c000300d1401e00117440610070b00b13680701d480e8958182c0c0000003402a0707005120030f00000d50000c21204a0800c01014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 652024667 1250 652023417 652023469
    0xb01050403050303010b03222004060509090105040b01120201120510030b0109020406120506062b06141c02031902012a110604050d080f130f0609050906010c02 70
    0x89503d950700a03000560100300200c02c00854000c10304614610240010000145509a0351980540c0e800c180d81013000c00084100c43c10f144c1c903642d110708004c10740101145a0303070a04c1040340d40200070503030f800e49101807000004640c25607030b44021080a135042e5100015099200c40030001080042e228003500c4410a200002043c10400324502074103000100594552a010010b000011400c89060606041c0400c0048075628001920300c41c03045040b20203a2034116000c00d02601c00038820300b01d07200c0c0c645640031070300c01e0b0714120316100e403101503941d0641d803070b1072400f600520b80614074029456440a00003082c400002e0b8002c40071f251040c10403c1d85101c29078101c0266420122100c04030108846441c0c0c00e000004c075000071600b034161001440d160405000c14840ba040d4a03028140002c002800c02c8004500d6080341c000858028954100a8550b01c880450031054444c540002e02d80e51004101d80c074003006110300a4a050b111015081ea55900340500707011180303621000f4541030743d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 652025917 1250 652024667 652024673
    0x20907023c0109031101060f0501050d0504210f030b0303040b1902071a191718030f1605120a050301050f0102010905010e0105190504050a060b060412030e09011d01090b01050403 78
    0xb0380036845209848889805c10410b4109003111495070108041c0c5036082400c00c06644c01408641600754030403070202d80c0781c1e02c0d0b06048268000c1d9050103138450055510002400b42d0261515409400e603170b0701408504410004c040d41d074080c1c0e00407001c1d03500c0108505410b0b014812460541c622050069403e0195a565540890f0744002c1c00c0c0c2d060900c00142c240e9045090000e200900c05050031300a0740352001e00f01400508000915900c0c1842d52a003841404503010002d44140d8141001c14980d5040a000c010020301e9110400310303030354802c042c0781e907190003580015030f04c1081040d80c94a003142c3c40c003400c001840403085005810b5560f81c48091020800a000d081000b6144000104503030509000c060000c03400113042c0d0884500d000e0500002840109154400c507411560105031000382e20001140c0d07100d964010001143c0711301041040541140903a4080503007140e00050703a07030b80d4104903805080000c0481d1042d0140b400103101000c51a80310500c407081c10325140e818a07480795 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 652027167 1250 652025917 652025921
    0x110a1a092707020d110102070f140304030b04050d170903030a090201050405061305190b030f04060209211203040f020d150f0203150d020d03030e0c0607030c020907023c01 75
    0x74a1650044c3c00001212501039000617105046801c10002185070424986894441f0303200500002d010403007006000c400c4030400c00c2a030f8040d68000c40041000e00b464a40681e48012044521002c94450401d020803081010001b501c101d0344407001e5440c1d565602c070a1001040050f100300d05028003030001051a0300d5420181041158159580d44807906140c2003020940d000c40a000305030055881c00c0c0300c0c4100075820340350400230f1016246400c2c1c03610301c0c00c00c1c040d0095841c03603034200703860702507003c0c1d6070300044142d841d0b240c01c0d003094400b0511514110900351004039070203042001d007049220010f05211001d041581d01072003041888c65000003480083e9000c0700b2a0403d03054000c01403140c2203000600240700c420003114160b914000540c040b80803000380540143c1490396803d0180610305040c4409048140c00401d003c0c2e45003210310300a0500c0030702005c26801601d01c1b4002901c45400081d885103864007032100400303040124902081c05074072891040d03990003400c00070103a19107030034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 652028417 1250 652027167 652027171
    0xf030a0312020703090909050f0705100f1209050f031e0301050d030806400c08280c03020315030d12020703030209030106080a020306070e061b0c0d110a1a0927 70
    0x680080d11100f60440f01c0c0b42e1800d652b94202500c114040e5002c00c01d40d42c3c0018010503441024141140c032900301c44074040042110700f20140c114041d008108640040210003451403148880c0d005174203000c0c0780c00352402c0c0d0000f4081c5070340114150a50001190107407400c640d00032401807a142900e06002400585040e941000c1c3e400c41c1c4a89001055002c80700b298403080c1100c0303810030000c2c0e440c08200244518006803190034400b001803001000d81042c0c5140d1680c2c02041941030000300c000e003200a00941c1304842c2000208440c0c84a4607882c940407413030441d103001658495060b0740680038420003e41c0411021814503070f081141c2c1d50b6640b42800f400c0c004200c00005404c007080c49005240c02e18030000c041c80100014402a021940d940005541074052240d558039809481403501e24503107640f900010758403000e4100104204610303610a00103034402510b000d00b003955156036004001d2101224660380050a0101c44514100080308030400950b03101000000c01d800b081040d103152007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 652029667 1250 652028417 652028423
    0x510110a090501020f1b011707080f15010c02010806011b0c0312050c070332070501020d09060e280e04050d0c05100c020313140f030a0312020703090909 67
    0x4080381004009800c078001d000109000e0018181c2e0031076103283e00362143c90032905118801c04e4007804a00907480350019080c14000c2c5d0104844600b0008005810030030101d0b100690400a040050704e8100e00c411200c00298041c1c503524a1070045a00640b002c4000804075810440c0b0f900c0341c060755a41c0e0500714a43c0901030900510094290304240c00203c02c0c440811060020401111003105800900c00044a800011b1428070342c03900d10300c04205005610580214840000344d04490301404982c000846800741c089501c0141e102e2401da4036241d4030300c070781004030304120340c140707101d042482603026048a00344004018020064240288a8441c0c1008036403c1c0c01c9800c00042040c20880d55070088110308110409060f1030392010740c2c510342c608000d025141c40b001400c8016008009880c140f00c200c1c924490b0030741c3c4400e281c904202200805e1403007280b6000c000181c81c10f020070070714507140d051740d501003204d42d04840e000042d504c00d01046040108007840010000f095220300d101c1984 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 652030917 1250 652029667 652029701
    0x61f120216150f0b0604030f030509090f150405070e0d020d1b0f0905160507030c0519020a14061b030906030a050f0a0c0f0c05150408130f030f0308040510 68
    0x1d40b0010341421120b0302030f101501070b8540551010540d42c0e54082d07400310b0703511440c004400305007031070110f4090250160f03168002002d841441502000b40040b14443c02d400107288220460510820040c1c0342c0c20b03124500801c0c0c20400845003070030003041d4800403d0001d8080e004440d11541c0f05441c00140103100d51100400d43e00a00c20b00301009c0901d0010144641c052080f030030070301300050303902e040c036980300050160005003d02058000c51400300c2c102d41000c01c0e18007081c0d0640c0c0c60000942d0003c0c04a208000034000450891a40b1560b0388807260090880d505165250399a8440c050700034010124034482408003140c2540c0301401140300c0c0f064180f01003541d0601c421589102e1102800a03011207041640c0d41149981c0305212031103144103440d00050030002d40c1000c07410030000842d05c00421858004220a2144000040440788641010180d0b815a01d0040e03407004012800001c0c4000310b0744e104c1401080c81120b2a0341c00c1400342d001e550201c07006000c1d9100b2101e604820f0039142d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 652032167 1250 652030917 652030943
    0x3050c09010816060c14010504080316180b030c0c0607030213080606010c0308060d05070909031106130803100803070f0c050612061005072009061f120216 68
    0xc181803559a004104201c01040c41d0000100f041034149a0341c042c200400c640d200805060080e901d480000e0001e050000300030500b014201010a548100c90341e1030710580f45185012110720500c40c014001c0700c207107800c02650303041c02c40020a035400603003d142c01400500c4a2020740006200c1c86029190302d40300140c1d181060f003421401c00c16260b02c007000d41e4104000704400f60760090410f0122a80c54034101c081a5507520003d03108103540348000d0503070701c50a00003141c40310017030703000d038042c5402920b81c20020021800183e50300c0c4000c40d0081701c00010006210006030001b40619000600f1a000c074210b00e40340c0710f85074030b9504004421303035500580c800f080c030610688403180c10180a05403106840c0184100d200304007968080c0c0020702540100d4019035489103d00241c0b003509070300c61000321442116000c000b0301d1034102c3c51207501c1841030b01c010528619080000a100080c101c0702c2c0105c8943c00754041d030300c041c4404454064260200520050403448841028080e03205006a00c011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 652033417 1250 652032167 652032169
    0x10b091005010216152001020703170907050a090905340b031012051015031505011a03060d0b1603051501092d03060209120c0f15120103050c 62
    0x704440460803210502510001c5c0007004155280c0f04110406050085002c400c0817042185d040340c4040c646803a51012880300c0800da4044200814265010b94011054480704c0002d03499103501d105a03540030840751400c00003c401904100801d03070050060f40c444100744105219012611041d940200c850f901200d40a02d11008083c0083c24900e046c190552400034550b440307034504c0b802000740c0541051380c00010408100b000c00852060140d080c0b20011a0b00042d034151803031130000300c800e400780b88801503800e1098400c1504860301000f502c103200504425010386544090400e6030001c6240a814000c506c4144001d8080c0a8621410780c0c42480c24900404666029241c2c0c001e408a5102004080e0ba100241c003007581c100d403a030b22400407051000c0d41d000031600101c29400a940b000008280700d029805800c480006031956102904440740403515500202c80f075030380c0300d0b0f20505a140c0f11b080c04007900e202036032600d500300d180000c40200c1d40380c101026441100e49500c42c0d04070002d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 652034667 1250 652033417 652033423
    0x10030f05070504090e01050105010206150a030c080601030323090f12070602030c150c04050108071e120c03230603070302130f06060f05040b09220c0f050906160203010b0910050102 79
    0xd02c01748100070405541400f000030b4584c2c001501210040c040301c07015035056a60165528015a170016031814180d60341c404590300d13584e0900c0140c011802020243d104030000c0d503414000e000342035076018901141d07407003000314800380040b516030049103840d070840d00980b04001d540003501040c0c00841c0c4400b03030258058038180401018051881880c0207108040c2c1003403090380c1c180d503800d0908042554420104896900c1d501b032444d8074002c1441000700c8060703040318840400e120000c60034003150181e10419400d940100140c0d41184480c484444040b030010150103820800c010309469046540c1c0c0c0000b2541c440700482e48603800e6071001c80c40d036456000d00c034003001041e140c200303402030340081c107400707480b6010b40c1c814203111500004044086544038080942410b010b00e6400c0303140c0a8425213040100340820a00e0301040c45583e900040380d000c0c00036660444030081580b0305e020303608002110354000842d42281c16640b12011800c1c00e0762000c94451003482d0300c1d000c240c951490300c80024030b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 652035917 1250 652034667 652034681
    0xd05072f090a0605031209010219081c0501060815040204050301020a03020301080601240c020406030b0403050a02010609110912191a0a1103040b07140409060f2310030f0507050409 79
    0xd42e0310740442048aa2808140c10504480c191095034a5000d11001030342003d050001302c130b00204c540300000c002c102604000d0100f981c0c3e2031781404148004074501324201c4130207001d541c000c00c0083c8001240300c0c00321084540300c0780c0050405030503d030740d4502103420b9030068519440131036000300c018081c200e4100056070043c05029980000507058036604800b000204129208104100d081c0c2425074445401ca04001c5522103260380b25498203040080658010013003100c019404d100d00016040510f01a80c1c81c00d0319002240e5103492400420030036034a107984407550b6980124801d140407400e10540d40304029014120410400f00c0a400c1e038a01500001c0c4000b85951601e8000d4041811902c1502d42c4260f2206030803d15807070700c2100381c0e0004d42404240e6440e0000140200d4080b0054000104640082b01c0075885681c80b0005990700000c86c100807030401981d80000682d52904101280c0c08614601300000d52100c3d00603004142d91003118110040f4000117030420203842c0358401d1342 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 652037167 1250 652035917 652035931
    0x912071202180403090b0c030f0406030b1806150703091e0f0e0f130f02090a0209010e0a0e1b04090905240f010303051b0f010501081e0d05072f09 64
    0xb8005180ca0b68000d00240158020900c006001144411101000300120b400300425a0852600c030359680d1801030141c84803801203409030b8800d442050702c0f180001207650152070014201d94201e4451803c0c0040340e00a140700340c042100318034002440300802a50300007510000742444820300d040210b03040c241d8a00d42c2c090b44104804400304800d60003d180d83e00e41002c1030007003207071480400e0706203a4100a14460040c6d0b02c1400c18040c0f15616501e64010991402d082e07c4030100d08020f50100002007406205880b940b02c0741d50000740c201c40002e682d41000e0b42c005441141855110005103045420312001252740381d100814803003c8a280b00c00c501b01000e10301095104a01d0920010303690050180702c01070a10401180f0100d04040c0210828049c8500008a46a003003440d0b85a5021705428403a68219000e10703d2491081c405a05004100080ca000141503580b10f090040b184e0380c0c01210203903200d000e0009400c4281048611b850a1424803c0c120301045a80404220884070003500300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 652038417 1250 652037167 652037209
    0x905060a060608160c0305040801150f0b040b070212150a05040b0c04030201020a0f0221100501051206010e09030f030a020d0b0303160f0c090e030a12050f0103080912071202 76
    0x4101907440c102421340c0d406500c0d1101303104c4514601900c00b401a0b4006031242d509240032050f41c1014007070744004a52402c035100d46030b242c0e10032290410f8400ea0142a450000401070003003d400c000c402c0e070040b000341c0012964988408849680c1660007a510000720300d464005000c18803a48840054110100340c1002d03140c107143d039001035542c6061901c014810b240164001c0c0c15541c450503c40c3c40450700c40c4d10340500d8a24178406903280da865443c0e490304545800c3c00031a2904000c03c039a81c10302c220000400440e402d240c08290f00c05e1000b85680850700c401c1143d480741091701c401035801040403040241c0c64001a20a08080d035000549030b6000307030310600c2080210512808903070040c5030080e803501507000c0c0a0400011608598100b41400d074100003440704400e0b4004003c10b00b038400380d940e15140e00342d400b50b580240d130300a84d04814a0300b40310b0b00500118070804010b100c1028024900003038010050a0b042c1803481c1c80e070050b8109402c2022410560500c60740170b0700e1400241e500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 652039667 1250 652038417 652038421
    0x31801080f0604090c15170a0b01051c02040308161a0403210209100509090f06210316110a0909080a0f090306181112060f0a020702040905060a060608 66
    0x19015103000000c0200f88515143d0780d000d41070010b480c58040c064007206801e03d46030107040c00050001248004102400c408640000709000c4443c07043c21100d080c142d4515241040d07076082042007042c031110017107109a00300300001c0022a10001015445420002200448903a05041d00031b08405002d590364014202c00b08000690701405903540c50601d56010203080e088210500e000380100e800312a00070b034030000c0c8039030100e4002c0094142c4001c2211501101e99a2100d141204141501c04075003004040424090350528200340070b81c00245078048074181162111034486805c48107105a0300c810300703034003c2626418207064100c003500c81c182d0140024401950345520a1003036180c1801040a84980368640500c9444400011900b0080a106080b0810034000034002d40d100102c41020030000754181c5420601c00000da81c8001e035020300b080d541c480b0300c501c410340c50090020300000e40c03c10050005030b07a00e2041c0c00800e4080e0000300403d140c0300c081d04044400507009242072100e5402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 652040917 1250 652039667 652039681
    0x23040608060f07080703111c061707061d1e0312090a2c010311040501120218060130142202210105191a010c02130e03180108 55
    0x30090f5005030300c901d0028999500e0181c100d000f056489903100f526500003a01400c0006443e21110244c48005002c0291940d81c61141c03003040041101802e40740c0085008004890040441c00000e00410000c0c02d50f00300c010000031503c0d41c0c90405c1301d001000264490b007045c1420000324651580300e2800c00e14200205001a150003120b201e12006045001000548081c21440220050500c00b58880482d612807424448245d0280440f502403880d1600004240c400010980109500a080440c04143d10850200001d600805070340c18460121000101d01c2d020241c03448600a495040e024607803c2c004414094981000580506000c0503041c01080300162508850068016202c0c0d51070750341c54800700d0105000c9100ca8248014400036007140c00b141900030138443c0b1401402001c1d4108070031540000c8400800c4180c022014003078419683d0b5000e40001c400c0280001c00b00c81c0b0b86081a0420b0050301c5a02c0c85400880c1c10100e880c000301d940100c0f034100426001d0030420107500c2e00d82c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 652042167 1250 652040917 652040941
    0x60b06130509100b070f0303110a050406050a090305030415020c0a05060306060c011413150509060c07150c0504210206091c06090821012d2304060806 66
    0x10180510806030324000c50080d943e0401c0c3d0070002e01c007402c402c0351900d003903060086100090803819000f080c1410403103034a221000044915180c1240c80310360130715040c007104550b1074000001c0402407101c002c0c80440030400801c050b2006185401c00003410020301c0c1d10003030030080710000c50390044640a1080c07041b40d8484003501c0e400b90f016202e26450740c203171a200d603003d0b0030b030350046400220b0b840060001c18404c03035840156184c001e80b20300901070483c504c54012600c0465103000960000404945540800780040a000d0b0241144030074120b4802d000100703c038229120720012400c0024100103240c01c4413661103070142c911031002c1d91040702d9008141644564000c841c4107161400c01c80c0f4140103508881a402d54120208018058440c80c0c42092a0f00100c24039a0140807000507074400703400c41c52140d05a458940410850320504400b44000750710380300151490018560703010a11441078401c01d840c0b40c0e58001e02c4200b03940507500b48401c94035250821040741c2c00c41410004c3c0300e0040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 652043417 1250 652042167 652042169
    0x1814120f07020d020a180606031a01021b060d0f02030709080703080f030c0403151d07080a08090409080c06041506060e0d56041202010b0402070807060b0613 69
    0x1a2520f11031001a8030000b020404107400c80d50701c80c858000700c8801c101d00c540c0700c40182c07031403030720304000c2c0340c0440a5080c42085c5030400e55005078000c0d0500f69034052813403a81c01d440c044c050211030078400180108415600a4601128140d601004020311241c0c400020b4000f0200000640421402c41d11221103500ca03000000040040c0007001c20707414142c031400c94005603000102000c41d0065604024042c0200e0b000079854100302040b181604200481c060041707c16400081c64800c101c0d580d0702616401ca24240c81c2c2c032950703409610303021070041d0000300090040c900203402d80789003078613140034581d00030b40da0107045900d005028413a40e83c006041d250042c10172505009100c0161814810105444c4040c3e5002000d582170404462000d07800c2440e4501201100800d64040c603003050030a94060014000850b800070208020401c421024501a04588004900000380002150699000c00d100b2a218100045d000302408074174490703611400f1086070f589290032003000e10385140341d2407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 652044667 1250 652043417 652043419
    0x6070b04020405060a0828020409061a19260307050f0d14030105010813020a060c02130216030c03030b0a0e01060f02070f05100c050106090b0a0905010513020309011814120f0702 78
    0x40c54411100c4032007c04a00485079038010000d000861707962800401a000c1d1004203003100d45d110024101c14640b50507051a1403074000f1180103c5840e04100401d02c80781007410030040c40300741011500300d010034001404950700403801041070030300c0071034000d251408691483c4200880050100008400c2a044074111402442c2203c0703039850310703954240c0802161900035031101a0081c000354658201403988106030003200e2094000b035217141c05000342c0c2304456601038079407403002c0b071800000d0156000c0c008590003868002044121030b4003144940c4202d411070f0441d005144e004121f980c3c0d20104076294a600e81c4007415000e4504007584002d0070349806110300c0340090b50040381489200704940c00d40c8503002402404100e46d1018040002c0a1004801d40a80c013203070b902294080a03801101c1c101c480103801026030850303011007580290400f0b006925155207070308114500c25200a14085054042c0300501c01c03055600c100c96140c1118007000c0d0750001000e002106600e500401500d800e550 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 652045917 1250 652044667 652044703
    0xe010e070810120311010509010c030b01050708030c0708121003060c030c09051c06021207021207030c0b04020a030515061e0102061305030f0d1b03020711040b040b06070b04020405060a08 82
    0x90f461405640c030203800d8040502d50740c030b4003007000b02400054000d1101704007a51010008010420011165445400000f5110960070808110004410350040444078004d40003a800e084000710b120903c41c45c00e90392050741c462a80c0084c814001d03d441a842d039600c0c141000c0141e001048400f403c0c1e1003591041c40d200d040440c4400d040319404480300c901050740b1000031546c07801139101712070055505070f450394010300c00d035450f40300c03100c03d86000c4607000354141e1609031a00d00d490b034680010a100410481c0c01c05181a000000079a080280c0140e4440c280440d481c986010401d02a10a800440c802c01c0c0410194a0f0a102d0f40c0100e000c980040c0c000500f0349000d1070324103100d4070354403940d100803110820001d6002000160f84d0300610202041b0f581005030402e000b00c04a0603030040d00000f605000d581d50720500d0a283c982d0040401c490003800c0401ca00c0c16036400140c1c1c81c0c212100590364001030741c04010851600381f0410364400703802c40c1d200c0d14650800300d24540da28000d03070342d00e2507280c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 652047167 1250 652045917 652045949
    0x3030c070b040f0e04112b0501051f06080c0c07150512280b03011d03120702010b0609040c02070b030106090807150f0f09030206040f15080405030f0a0504030c0e010e070810 76
    0x20f241c0c0d40620440315075190387c0a1302c400403031038a01c0c001c1030110780000000d546425410100304400300e6071030460315903079a49600341d16900c9492000354015805c2003140d101d004000a0b203044e1101c0c80c40c3e001c0c0074507101c160f26a5040c01203035140d00340043c508a00001380b80012201c1c0340000380a80c0c1c10420a00001415502d2000440d0061000012001344483c815800044c5404000000c2050305641140da6000c0e885da2130090f401c0e0303480f00c8115944aa030510014000342029803021a0500c201e20458910035503d207038810b0140c2c001c0e0807440010750500014802e0580c100092001411500d1400101440c030701402040d4411102d04070703041055408000d000d05d4840c0c0385100245400030880d958a0f0b81d51003003104418098440c034094440e040b910003940c0f601406200d4456a0860702a40c075080c41000c4014007039101042c240e0070f001040c0004004500c408119102800310201d5050131941032803060304005100030403810411800c007040100070059070b1070303000884aa11103181840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 652048417 1250 652047167 652047199
    0xe2d01030608060c0c0f010513030503190501080705030706110a03030b061c1a0d02010207060f02032a0705031209040b04270b01060c030c1103030c070b040f0e0411 72
    0x5410150b005407210f11461003401800c541c080028091201403204442e58105502002400c1e10f80454144a490b40301501000129000368003e541c40707d13040c2640182a4035505002e0100c1384283c02424050f442980280950700702004148007400540c1802d0702c0c4030554119540d903070103c4900060400d622102220110744424003520340c0c3d0149030b44401c9000381c0c0d08a4000082110122124201025120985945c180390700d04045450701030f4082d1402904150f410b0312200c003250300030421840204400c0c8003200302c0720030321011b40c0428003002d141c4a004c15a01490030b00c81e908424401c0d001040d1505080b0f05000443d00c014200361404990b02c1504000a0010590400e030412040c0106240082d03040b40d200c80703094020b210303003e07402851b40c813400100c3e0108c4444030700030302140a43c0c82100c0480e00014003100b19190080c100c03481c04081c1c180050418003a903100c8080c004000c6424403041105840e4400a84025480e445261509803680e00c09075448111481c00350104403900d002d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 652049667 1250 652048417 652048421
    0x302010608070608071706010807181d0906070302030106020727111c06180f0e030c10050901023f0c04090b03011506110705040c0503070e2d0103 64
    0x41078204195181c00340e9031034000d4552102210f00e48001448000c800d00140c51450190b4003812069691013401e948600d02550300e0540303150300d0321981306400800074010354115043e2074200740c0e0100310815820104103491500d6005400c4105040c010300061040d00d0340010440103c0d2061501c803180c0c00030300060b14800c00a004010040b241c205400880c10141d814001c010403000e41c80060200e00140c665442100c20030301940701c0040e5000000c00c4100311070380107440c20081d028000129124071403001461940200c2c10612550000503911000e20501d1240079400181c04000b540703132103503c6202800a840a200555078038040c19001807282e120a000c1d103e000c050005141400e0a01c44504407940d082031084140b01420f10907200700340d00301030080c075144d401c216492320341c0c00d03080a909850000b0108030214041c46140b070001140d83d030750f0190450084094540560700d051400f4020302d0403414100e50742c0142c4080c40c50203140300c11505541030520001b030150049104502c01200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 652050917 1250 652049667 652049669
    0x70623070f03020c0316031814130204050406120c08060c0d110d05010b04080115030f11030a0f0f0209070c020d031b08070b01140913020f01140a321603020106 70
    0x2906120120b00c02520398450301c0c01d0b2506a003c0c0e2a4800d50600f242c08c00080102d003801044901c03100c82d8030207801e41c03d1041c02c2d10300c1c5030301694015050a8503000402c0c00c441c0e01d43d00c40d4050041030308408081c0036201c0d04200107002444003411aa20b0491114100da00c618a845006155241d00f407881041d100000e81e18504c054600510031942c0d50035416007180c00c18000e80d5030315441c100010031040c001c4071a5804695001d003c004900200d51900009a6200380285806014002d040e100084d0a2401010302c0f030b01c20b0840110100c164010301c50360180c0140400c01f1303c1143d91060300540d669040342102d40e07030b1518007400e00d0600c000e080c20f126819000c0041600101081e4481008000f07406107059401a12904500d48521000c00002400a0b101400d0034244104000050305040c1e14045019a060610030251180c600c0c0b443c5c2680d000e1000040020f00b0284254030348a51803a409240c610030541490b9000c201d8000c5410502c80c00f000070114884c1c541c0c0036410076000b900014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 652052167 1250 652050917 652050937
    0x504050607020109210c06180302040e010b0d0f0b01060507020612040320010e0f01060b0d11070807050607021e0d030504110a030305040e1003030c030305072003070623070f0302 78
    0x61210140c0c200384c00181d0000751080362000080640447c16030300c0303000750980500688031588070491550302800010040300f07044146954a40308000c0c1e0f642c84d590311022001d4070807444c5d94404e1081d0b08103000b014406030080c0080010400150740542c0d9102c003900c0100790820f00d03820315900d0b940380907143c0120007400150400c0701c078045402800030650082c0340c01445002995084418141c4090072641e06000b19a40d501c81400b001181e00542da1010070365000b1404410701c0c140e00382c3c5804070300ba04079003821034180d40702501300182c0e00e6050004444041d01041241081c0881e026a55203580c2101401c4c401c065540340000c0a002109090001030200505040e41035510707810010b00b2a4068000e01a4003040c14021030b00010b1038100038000c81e50540e4900d081201e460782d00b2006400c0142640d0104008500340031180e4080c64020300c440410704004503901e003001e142840a6601960f0200d00d1745003250000050203100d400c4042d40054180f4200424803500381060b0000d0081410300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 652053417 1250 652052167 652052189
    0x240906120b0a170a0203100902010512040606090614130507050f090f1002010b090106050412110f13020406031104050312070f05060906010f150e01030e0f06090303010e090604030504050607020109 86
    0x22000d003d0000c14542c400c0c0c1d0007607003603e0402e651074540109981c48508001d0009004110206005a000903000c1e0054480c440200b84280e48148050a03561503800c08100074800e00f1480b065403038100090701407d122180d0a20840c90500e4018009005001d1a03060340f0400044010307603599259038808804e030000b003490f6a0649001c4000380209040e4490300c4c09003048400102e0701a02803815507049950760740610b00b821050380d84003000345614800706a000140409140002c0c1e0f02d50a40500b000c0c130030080107864034036208008054aa03c0d0b9100f52450504000034015504e01280041c2ea150443c0d9100380d0350301d8280761104019403803c0c0090042d00848040c003640080100e07405040f02c00001203e140c6980780c49401014041802d10300c07000c282707003200031440c0e940240c00101500c001303441a91682001c9441060600c10111214252600000010300204503044282600610507100410395860559005401c500c2a405418401c0710042011011a845007503000040c00140100d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 652054667 1250 652053417 652053449
    0x110d140d060f080105010503060f19180311062212180b030a06090e03070605070509041d010c05040807181e020a021e0d11031201240906120b0a 63
    0x40c0500b0300c220b40039442941d4201000003500d4a00012014003d03031148080ba0959180c0c0c0ca00b003607280c0020310903611880e485c0d0749500c0103014540040e4448500984500c01c40340c0355004400d0412030f004102e030000d144081c1c0218000703495030b60101e411551200030483d248480010555000602c208580807107100c03851b000c030345540030074065401166200800c2c829143c40ba5003441c02c0e22a9231030500320b00e40c010b014141c04a0000d030480b0360807004900701985402d200f1008107003562001011003003440c40034a0342e4002d10f07809214900780c105a903d400340c200760400b42010348030100d62042402c1e0b41c2c0310300b0300e0041c5d070b40480c0d0125102d440085040304506840d0b0200d0000ba400c1040d5038805800346500000442c00d00c0c96001c0700e0722080340041d007200e0345502400d850000440034114058402070040c149050800400c45028040103800c03407590295071020082c03c028401020410000c1d040f10030080c4603003100803801028464078000c10b48175580d1020a20307090881d4080030f505550014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 652055917 1250 652054667 652054679
    0x16150518040203041a01050a06140d0e0d050c060603060c0403031443020a0504021c06030c080708011413020607020a03060c03061d01051c12050910110d140d06 70
    0x600f45c52100d85020711080706a1340c60042103400a50341c850000801c51100b600c04a025020b0014921f0b600c00240c00a1800310400b88a480c2035106100040490360004000c2c02c03200d02000055408401200100401e10b130080054840740914840101400004130103100e041c0301d0039040e00c0c0f6056041c0100c034180442e1880d40e21809140c84800030246800080341801d20049101550f00190050700b502c41441ca8070085c003001750300208807000c065858407248602c00e00e032802901d00450040e80c0045085041a81031401d0480ad80d100b482c550385443c03000701003007200044090b03005c4031014195440e42c0c8103002141140c031501030b000358008800301e4003104002c0c040d44500403031155076800b000100e4551104095080e220007650703005400c0200100150328000d41c8000c078007100800c001c0803103211641c0d410002461100890701044001c10b5407141800c15038806d02c0039180a2601019148200800740c0d12040c0d0040c90408001d01112514201747d40f2408540100c54003680400a0581e240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 652057167 1250 652055917 652055933
    0x80f0304030f0e03070b03101706061008040b2406030703060f090b030319110f0102030403020c06121302060c070902030610261e0106020f1615051804020304 69
    0x25011030102d80b200840454407441030703040c5101c6000c054014540a4100841644a50401409642c90300c080c01004504400c00458818042d6a00002001d20b41441307010442040d05852500042011560030040130641841c0f000c2c3c1c1224405d04e01c000c4080c500c1488184d04003105010b5900044000706000c031035030340750740038008031100608592583e50f00c460521096403400e0103006d038950301c00c0c40110080da8030324091060540103418003140c01e801244c41c1d1401c042050300054001d9502200b000285501400013594241d405c86160b441d0645030001c2014001000d0174601890300000c104808640305c0004907143d20240204030341049a0351405d05003e90b000716241401103825402d000784441c018000c500b041c82203441050f00d074120480b414212250700809041113030074840505240300c10001c440038060407c03030b40544a00030081c440c451030310700a031608a803c001086001c10003a900303070320000081f14984c513000d50b460994044010801c3c0b09031806661141c400001c5c0010000e0760 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 652058417 1250 652057167 652057171
    0x71e0203040510180f0f0303110102090411030a32060f0306010f060e040203040b1803040518221707110406062c010203030c1606090b1f120308060a03080f03 69
    0x100b10008605038440d41940450b03c1140318009805074186c9040c400680615480d580440910300018203007240b0388009030075036032118615a00c2600000c20700845594a0140d45055565100140410300400e1400c4401445898050100d041894089810b0780e40b0910000d4034490020101c40b0556142d0b850122004135a101e0003002c5820800503a03450b042c40c0c02500d1149400105059155507407440d181c00070398180d90003800754042040003096030f544586a600008000000c042d210b403a110119508161205e00a000a41c4004083c8400503914106030a540c98440b0807040e180d0851f8500b102040944d9a401c07940f02c0e041810100c4c1081d8000c82900007509428400070050042d5803101c10060710105515005030001c10005180c4c4a10303030000d010181d00d50344030400c2c205e01910b92000301c8255190031901c1070b0340748040c000d003070301180780e00d03005031505144002201e8549540c0218040341c510303008040c01500300004102e030361030004c030710015600300c0780b030a980b8248080445190707401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 652059667 1250 652058417 652058447
    0x1e04110103060501030b130e070f030521160201140403060204120302060c0310060c02220b010f020331170102092e031a06130306060e071e0203040510 66
    0x50a000042d81e98400e00460180071030140a40c240551f40301101405080c002c2d090306064400c00f000002d010306160400001035018201030301400c0601c224008080e42a1030707004403031081c148440300404181d180301400055090801d401c03601004921241e80c0c5c0030341c2c3e0002c0c02d42803001c034001034001c0d44041ca00e18000d101c2d41c2614130760340c1d0321a800c1d8880d0005035441030032003641036400c0c000d55000c2d800402e040e50000309012030031819022150401c0a8004100d54141c0d2112440c852558102140b007407884040e0004e14140001e0181301100d200c00c1c9182081102c415141c600a06154440c400d4054054000b0700c09a03920615100c50113035028009140c05040c40100100944420081c110300c0c0401580c4030504a05c40084210080d240900d0200700e025901d04201e0015543c00c002000380040056801e006103107141442c40031503c2d554011242281c0d03a40402400642c07180b20801c00390700381b034480101c1c030402030012899030049030000c136081541800c0000e034403034004001c900701e07107030b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 652060917 1250 652059667 652059671
    0x117041a06221e1d190c09020f0708030711060a05071215050a0e040b150f040903020f0d0906021b0d2409060914010b060d0b011809020a020f01020915031e04110103 72
    0x20985179510b096403400c41d002c1c02c0152810401c2c482480ca03074000b40070b8500391410305403c04440f80c4699410ba88140c4044012814071120a00c0c0180c09020841c0d1013044034001b006540360941024200500c240c602d006402e51318405561407000c90742c0120042d010191411155940f500b40305481404107032000e4071070010390000911048500c0d400c11000e000041c02d1a07040100d0801844050302d219642101075000b48125016000c03020002c214450500d962681086840d20b03d000e4100b81c0740f201e0002a246503400c1c0101d85031508d0b1541400d241c0d10480da130204e000b00d0741d244011007500c1c140d8040043c1c200080b130018400035400031000346014518076600414050100703800c031251203403000d80140e8140034a0100a0b031030351080e200000c060400f03c00b030f018000030007001c0c540c0030b80091009981c0452504041a81006400d0b84048030700b000314a4401610000f07200c4800f10385200c64810340c0040000c00020000700414000f500140400c4030300e061502d4600e8079581001d1417036000034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 652062167 1250 652060917 652060933
    0x2007030503031e13020a0504020918190c05091809070e0702030706231504020708030406090515070c0803040c05030d031a010311070605060117041a06221e1d 69
    0x444d0b81480e815499001304000c102d10b24140600c406500304811075540034845c0700b6401c00380300c0318000e50b42c4070304081c020191075a0410340c8003030201e40c0060780c4042080800d1001d03151980310003a0440e00c54680441c0420141d0350141c0d50b42c5081d490341c10010b0b000460f1018401865000009011801c1c811082031008000b040d8070003000804001c100406502200081a512407080241c04092800a0301c090f26010680d1541140c0e0741c01594200c440a81d28440f070400d00409000d8008070a8101244081ca803c101d50010078080c0e00104c0034045080001c0440c3c104180b4420301d0000300400f900366401803052400140061a003071420003803401301081c01c03d10701e40c4644280402405948407503824000c641d10381d4070080100411807410b001d0f08900c442c00c032581161500744150705c82c00c290200001900400d81c1c0304038010300014007408222405000d2801c1c2d100244c3c01680550b07030006250000ca0ba442480d600c0481309400b0964604080b240307810b41000c0c07042003100803090403a5601 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 652063417 1250 652062167 652062181
    0x2120c030c04021911030f070507180501030503070b06040f06080d0315050303070f06023606040b0306011211030a09030e0307080309010503070c020628030c2007030503031e 76
    0x10344105082e03444c95a64850144600f81d005002c8804a01c4003602184c1c2070050b86417015415074007401c000c0e9140ea000513003c00440114082090b0101006001030000c0e5141d503135025600e0146c0b6000504950b8043e000038006d4403650312101c0000800c100c00c0c4021561241d019032508548003030280002e0a01456640304001608440c04646024004502e00f154948601e000c000007c41300b1100b00390200104800009201e06a40001100d081c8003114480c46072203240358803001ca443e150080b80148410080343c480c40c2e00b5a07510000c05c0c2403120005007090b030040024003121044c9030541e5008024040b16400c15849100c10350b00c01e841d00d4414046a50070150394070b15600ca044c03650b0340108241c920a512400185d6045840c9040115610182d54006078041d00300e18580c1c0510100c2140c00030001101034403103030150045040410810345034550003080d05410403541000010b4001d058495024108880c00080d50443e040d00c1d142c0c02e100ca404404040205103800d4030140d40c01c049189 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 652064667 1250 652063417 652063421
    0x8010303080709381218010e030706020904021e03090714030304060f170106020a210e04050c072004060803040b040e070e10080405070b0405181302120c030c04 70
    0x50302e403044405112010f80b03d043c8028040003845038600f406a010300c40c04c8074a6400090101c3e50115440d1506610700545128500344140a2040340d680c140300740a001c01a010040302c104c1c941101d0b02580c0c60303001e4004a0042c0c400c41c1c030b0b2120326820741000d0031801c0ca039810155000d4508001500c0304c459940301c01c0a0000e4042419580c141c004010400099004114581a441c40340c01c4c0480040e1041e120320460f002c00341d0104002da00190703511410045e1040300c078902c07840c40e1019800c5610000000410781d94076141e0683c0601d03a12004502c060224000b52110543e1154000200304c4500f158014071519610810340141e091000114001d04048291002e45000f03e403120b0429151271003d030445607020f0826014000c001070600040d0300d80082401e00c0803101e440d000f139541001c0c901240f908035903038480d00c08500144414000d036070b1602c229850055600c050808035440380c1c41d403001c18000400009502c419041090042d4020118150300f0b4004202d00782c070242d690700c00900003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 652065917 1250 652064667 652064669
    0x30b0411030a0506030a050708100c0809061501050405030a140f0106120807030e091f0e010f090f02252001090302040c02071701060f050301271b0608010303080709 72
    0x361014000205040b51a81c0855401480281203400a62603503c0d510300b050700c00d800003102900035440c0401581031600a00129002c6c80c50207403041c0c0b819854658642070701400c1541d407800d081e000c4840c9a8401d1090390081c04005050740e510b084a458900c1109504083c0280203010f180d170402c1c0c860350107101e00c10485551101e00c052140042da12102c40754800e80040341407110802e06203000f40c4880800502c210100c00c150400140e244003824920507465120035805110b14005005840c0060b6118040315158000864200100d070390401c041e004916012801c51501201110040351405000740441c1c0a80d40d14191080e40740b290180362107180043c0340c04150f2081c010001802e1640c04240000d00340d106a624450702c1d000d103889001d00307070100000a6034482109002d24520b000d1a20001e28045008000e01d0020900c201100305207803200180c10190041c0c0c900500200d21029144103484041c00c3c0071254485001034400e100070300090740007841050000d4480c500640300c01c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 652067167 1250 652065917 652065941
    0x8100609050705120a0e06070c110f0109050111010612120824060702040b12010501050103060806010503060a020c030d060b121806180307021201060314061509060105090907030b01030b04 82
    0x3502d400842d40081300c40c1103002e0804c51201d65161125a01084140040b0b0701680107aa5203213038007403690800ca403c1c01803000010344125035080e44401c184c1c1e00075207150700f125000c1c00e258410810001010b80103103699840710420b0140a1203d82c06c012003030f460b03156180c000e0349509100351925130b03c070442501203100000c001200c04086011925082e4080d0035118401000401d103030302c1000100f042120030a000601d07580d1144010700056806001d41c3c00500300c600e0044c10303d0740c90f150010f036403001e0192116150681c00030b25292100000c0c421614941400c10061000c00d41c2d90340074a01a030302c0098512038610101d400718079a80c00d010460668071a88100410254807100038071114150481c0c40e0401901c010081032005842d8000c91030a807002c0d0600009115165041240e00742e1180c2c901020190000001c02c020480008000d60340c1d40c200380c9076a68180c2e14480140d409100f4145010307404034100080080d0681d050700311510080003a42d0600c00c0544020070301c4161a4000705034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 652068417 1250 652067167 652067177
    0xb0a020c04021305031006181a1e0a0314060c040602030711060409090c050a090b01050d0b134506020d02070f0308010608070c020d030e1801081006090507 68
    0x10300c0c4a0300d020b4002c0c02510b6049440c5410f21580e640000e850140c2d00c103007002d501d0b6102c02c001c0205007030715540c0b4040c3c404622024408030f0f819444e94184810b0700c048207446410f0448040c400c1c8040c510311148090f00142c10481420703100d040c030240c6040c4812408410f031141e08005028004044281c0d0122101380c2c00940c10a010340c1e40b01c083d9500500300e01d54110300213010000d60008540980080c239405440074a1209041c8400c0c0b005154054003c820006d04002d81d030919030b41d10200312240f114254000090800c10b550008100780c000d10070b042203050401852805040603801d0305890260100810760341d04080071222445441d011032184004450750001c800030402c1d58000340488201c405006240c014031340c2e0740740100b545240302603000503c00c1c00103120842c2c000300d110b50440e2103800c00d2031060340c050f8001403450b961003400030104000081c040000d6100c041c1600d41694641c00208000d684885459076a0720074070140215640c205480010800001c0c03094030300503040380d44c807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 652069667 1250 652068417 652068433
    0xa11031c080405120f09030106051008180a0b070905010f110303070f0c20090c0c030405151605010506190806060402030915040f020901051f030c020a14060403090b0a02 74
    0xd4640010080060b58203009200d11407290300c10700402050208600f107101070b1906c40c100245801c4078274542046010388e40301e80101c8410380d002824203511015403a80400c400c00c068070300d03900f040d00e80807000700118000b80074071042503000482c0206032407003a84d5859111041200031a25445140803503c41074108002180a062064281d084c40d111581010000400b442d680d00441d41e5200d1024144900c8205070750460345402c02c0d8080c0c210324100d10b03550074141c00d03114660b264401c52103618422135031840008041c107018410b42c0d03141e44041240d00164038072428000e0280c401141c281d0b03c50303440d08070048102e00e407580260302a1040f060050155070f44140601000b944050a9041680314110040c0400c48042d0a000c2c030440c440c09098640b4899131040c00350420060b00883d10900303001542c103024164800200c1da5031803541c0f502082c200c4500340c041e418034a2554015080d4038044001c02141c20b80010b4160245200396586040035988204480c7c01e4011001450700581000d50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 652070917 1250 652069667 652069723
    0x38040b1917040b13080409020a170903090603101e1715180307020a080d0306050d05062404022d030403020d120212070324120b130803090a1103 63
    0x44059800140040580302d0604c90fa240c0c81519041980103404242e00003c00040f82580700743c001c5603404a1800d4100c40e8102418015160f00405040c94007942c0040300096030080400c18800c014800200504a4004078920483c1c1030b5405010317800d5045074040034201134410000d501c80e00c4481c04c520000e07076915000c11041182c12880f01c2d0300ea89100038030201000d43e42d41e510a030000c100c600010410000e046002809940301e541c0810720034104038000401052020440340d5004840303c2481403a9078562800c20071480d40003924130b420500c0407813140c445080500d1240a240b12289a500c5900c6200100c00349a11040f00c00800507084018203041c500c1c010014081d070280903040c054201700c90200e858031103038400c89071000003a480300199170501f0346040b4080c182201603100c20000d5801c00da51a901c070070300d02400618a580e1030000403041c481c0c078034000b480e4503401130340540d8a04044071007603078449801c8001d9412041c25003013540645070004400d4010410940303140715a0f84801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 652072167 1250 652070917 652070933
    0xa14030a06080d021509190303020a09091104030204150b09130b1806010e03011505060a09080111070c120b04060506040b030618070902030138040b191704 68
    0x30380340300318031510748102151085060003011030a4a5603802081007419082028600f02d001804191164020150a4601c003e440e00003c400d207400d81070240c1c0e1520380358000c0392030f010f460703011155031460101a000c0c804258001442128021038081c010403090f01c000317180c81c01c003622400100d42000c01200160342000741920f103600d61810720000f5550703100000728a1450342c5c4403401601c0d800500402a01e0760b08030900c421f0345503081c2c008101c5142090324100c0d15118034042d00b031142d103004c240b00b008580f01c0d04909000e40070900003030080c4007445140300a95046207078100d032001e0070b0f0400030804a420741400c40d01e8641121581000ea207560701c40e540107280c00751445400c00d444245180b02d5480812900740100c0440d641c424142107144041810403201d0f1700101841801040100811251078100c1008100d141401c120800a05a050325510015000c2028030b0400803800190700c1840700043c02c10b81d030885c1055070012400510441d01088811005100703030103200c0100340030038152 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 652073417 1250 652072167 652072171
    0x3110708071d160e210106091107020d060b0d050111040501030e0d09140d0f0308010602100e06061c05100209010e060901020a1b050a03051b09010510050a03020d020d090302120a1403 80
    0x40c00301020080e5821101202010b00441c5c5802a91208020022507a140c8205c0b040c0c4601c990f800b40c100b140f1a4001400115001c2c6e000d0610380e21144540401d55612490001040d4060000c0143c442806007140071608039100d01404a842c105071f4007001300b0041403e8038141083d0343c40004076070800c6108000030b06960b40c515080110064030754005040f5a801140d6075004c1d480300d01c2550324202009203040c08002e4001e0a0034245805102100300004080d500008203d5901c4900e6502d54805500d421003940c1c050100d20520442c0c01d040c01c003039802000405400e83e01c1003982d40c004420b1191621849142500607406086131030081101c9000c0c0c4c001c600d40b4541030880c1c01d076a0f48009120600160004d40703582c2c1221103050098541c88011800c91041035400035070325031404000500c4042081d4006050010000360039028a02c6941121640e8400c0c82c1c2c01c41d00ca81415005200a00c21924110003511588203048103800000c000d0303841c04e140c0340e43c6a456154100340600b00079040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 652074667 1250 652073417 652073419
    0x140f0c0a11010f02040b0c1027020301180308041104051005060702310b040c020718060806040b09010c020c1c0c0e04062a020c010c03110708071d160e 66
    0x6074203c15628040da600081c03000f0300c002001e00f601c0e800c10303243c514182160441c0c02c1500380d20f0705481006a01c4c03003102c0030f51015030441111700300301428000b00e1301400300c08016a0b481c0d55542d80d00410541c001100034003560040d018444450740d40c030180400c443c030984001d8110300700c2c07607020002da00e02040140491840071302a1319410b110140d40c911039580182c988400000c8092901070051818414202c2c2410102da0503c80c0c0815004042c1d00c3e180341d40180b200c0700c811900303003c0404810350040c070010084107040340d440e40f0341400c0c01e000703010301034500e6091542411000303001c4910010b1141612000200010014500110030803078070405400b040341d42d007100c50230000b003110304018000c0c4102e00912010484210000720541c802c0c8500c40c109800c51848005940e01c542d0003e00012403c0c000e007041d2098001504054640300b601028200562040d1040030030651000b1600c1e03001c1380c51584c0c6900050080000c01c03945d40300d04444954004e91500018440944684440204400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 652075917 1250 652074667 652074671
    0x510110c0a06020d0e010b090a0c091203021005060603040b070509012c0f0a0305060402060d090b0a090210020d021c1407030e131e0e010605100201140f0c0a1101 71
    0xc0d9800d2410850911815036601e030340415907840b00f9030140900e030704170a14031000b0043c2001034400504007100c09804000c0c1140d50b0320f41082150b000f40c2042c4040c00801d01840218001403a00a580e10501d18403060100d04100204030300d030400e1030030740340100ea10460302c100c0e5980d201000c4900d50840016503040044905900b520342c480021a40700d00d21f103400c94064036059280034840c1d0014100600c0f8041e80c0045010000725a001c00c8098016a044501d01e55a800403c0743c080540003400c00507000d000c1c083e0610125105a0703200a40c0c5503c00d550460080d5400c1c017050b47c65484c00300c008005a0044101060402001d01c540ca800c40c40e80d0030140c4041c0001d0100040e141c0000c00c0c01c8000c92202c56410350b20b894954411521922100c10a0201c00908410982c0c2c0f45091813044051a0301c4000010b0b28010030741000019050141000107010803201d00240a0f102442d040b0602104900103c0d0501404558040c0f20b011400005454404403007003c480620700d170383c40c000c0155 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 652077167 1250 652075917 652075927
    0x9080d030f151e0608040812060f060d02090a05061305060f0c071205010e0115140307080610050a081504120e030303011205100504050715090915030519051011 70
    0x24001c848240203000b010000140032810381e0071a0b10f10500340d0700044144042481000b000403403810840e5801c2810748980c130380549a80010580100088181503445040441c805007034840a602500b00c0c4203048400d2015907642d641800003500ca40d500c1040d4064412000340614203212005082035049800400d10300a18104000d01300303130441e00415240c284144540b01841030034003411824401440c020003410003502c00b44080c070416441008802c4400008035030003943c0c1440380800a00034401610340d40e280403481c801380e03000c450190354820f0342140000300314401c0004c0c0b0044c101900314250001d2740c465842d00c0d030510b1a800f00113420802c0e10040c006550f02d0901c0514002c100c40c0c0442610b89245107002410b00c5404c1180ca031895203000d00b00000305500141d10310071101e00d007025061006010328221507108803038004c10001d0341041c01050001041c00203a408490188041e01c840d4901004440039031600c255000d00690301c401488010b041aa5102c02001382c0c41940f854584 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 652078417 1250 652077167 652077191
    0xa051c03050d151e0f0e090f070b09120304120206090a1d0f061c061d07240503280207021908160503060408030603010b0d0b1609080d030f 61
    0x103640c196400d02c6044103c3d0004110200304800a1400c8000041e2101c1000b4188400154a514a07115100c840e14a990111340c01c040700f8001038022a0007041600d4580d601c81e92050750a60110055a0041e90509007802c1c0284012098400740d40354020a450584d40c1602044841e0300440c4445910031440030000804150140040300000c54dd2420a1880d00e840d2510300003a203c0100709038054240c00c2c0414920b2081d022151008992128000500c816840319080c000100c2d40308030151441603080100d4404034129146000c4400317900c42c50565602a81e086895000a84102d010702000400140c02c6100d40405000d03a41240340780182012100d8000403184000f40c0040d04104030a88002d03c04050b0600c0144141415405004109441c200c0030a0b91020018000750403240040041002503a084d00240080c0100820300d0881d1034180c00c02010103003081d21683c412050749041144818004c800d514100d0f0490800351000901c6401d0070743c003410191081100035079480c600d2504c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 652079667 1250 652078417 652078421
    0x230a1701060305040219030f060e0c180f09030a120216170702090901020a050a0305060d050d020615030604020a03200a080318030109210c0b0c0c0c0a051c03050d 71
    0x800c0940d5003c00d082c107090040c840e1300a441d4204841400c000c8400b400800c078414002041070340d00c5003001034210700c0822103e0511a88004141c3c0c8581c0c00482c2002004540070725078003500b01c00c2852542074035190030145c0d803403040390081c10100d031704000c6018a02850f0750140550030081502100d0841050381d03555440260040044c03a1074001094200644c01c24001895000c07070224021480c0030745484021b44039000b10340c00d070407c0540320000944103840d00c03511410070f203031301400b104d48c0d250458001035100d920856000c0881080301800400c14030f800206e01c0d010310f4002e000c108102e402c0d601c1d900c100d50308050b100d260240220388902125110a0107140060050401854541501d0701203103801c0d11503121510320076030520700300e1404190182c0d410100000304d44d10b02d503c03030500d40788255805d204400000d00428444420014003e11b200c00410b0b10300c04500940300304490140801640300702d01e004450b0046005901100c0e80c007549041c440c0c000707010781840d80c1411051400c84c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 652080917 1250 652079667 652079669
    0x607030c0c0f06170405060c0c01020c010501060309050d02010c0504091a10050a030b03072301020f0a1a0105030d080a052205070302100503130303090f0206160210230a1701 76
    0x11165101002c1007243e5584019200e1280e0400070031421503042a4441c941c2c1d0785c1e005001907803202c0001a0311102c104096044070865030a420007841150384d120005001000c0910080d2414000e02a0802e00148188500d00c040c0400ba100d90f41058140140e06004010380c87c055500310305e0b40f94030500c079942d90040300e03c407031001556155a295241c2000909460341020890f010f42c0c40120140400c04d810741c2e60410550b42020351001d11114280100d01d4a9050411281140501c0d00c0c2507041c007003440d40f44901a00060401c03802e9985e901c09241c0d480b151a10240002021400820040103c94204036045030041840f0014550004008000381c0300c3d04408662541c01604d003082141068040060b582c00181031160442c03030410b200c00031503076209000600701643c0e451924104084034a0740d070707400c43e0003070002c86d144c603840280200140103030071041e88158070302070a1407001440362412180642c40e60140d100000b401d00c4001c1555008039a5400a000750350407424021448601c80d58 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 652082167 1250 652080917 652080929
    0xf08090111030c0a1502270a1703040b090103181103060f04030c141c03050f091615020114090606030f01020f0409093909060b03130f0606080f01290607030c0c 70
    0x503020800d4400b00a10a403072341d8041b140c86a2071843e5011900d1010050320119100b840d9030569801001004030018400d5618440010b0074039015131003841100300700200015410350895403151100081050890811030b40240040d004511040c0090700e41c410001d06005540c04880c810855410000c0c26070070b0003010350380000d9980080000050f030b5903003401d070820031107800341684003140481e25500c10b01c10300070300858a40242101c88000d100354043c1e406002c15941080040c03c00b01e400e40e482e00803d40c0c2e039901c648103042c0315010742501031080301c003480948040145064a0f04040c02d01510080701c09071481c4028104100740d04502280848001501c20000d007820102594a28004c40040e000b644115141507010700008080f1400c4075003203014003001c142d421141c1d02d03000300002200c0b1001030500e4186100045c0380341001600c8000d54610782d0003404025810001c1900c0543c03480c1c040e0344d0f401d0100c102038006003400802086482c1c002c0c50051040319090f00d403080030084592200c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 652083417 1250 652082167 652082227
    0x6040e101107031715120304050301020412050d0e0901090911120a0308090606090f13020d060f0b0d1518060e07060e010206040312050903070f08090111030c0a1502 72
    0x11020103511444c1d01c2e142c50381403968804c0030704050b0030100750305400654541c007480c0c40b05400070304a0000c00c11f96004010083c000d569403915004540c8405840d02001c4039113124003020f038481d0314002d04e41d0110b10f500160452166a01c3c3c0a0904050480c00d401541c0c00c90402d0390310825910313820030219004042e00001c003594041480c00503e24032005241c2900d5802020074099503607038488043c5c0c0c001800c05408512a1074109403881d50190500700250b010b04032606250422100780c0045952141451041006039811414080000040d51f0001c041040c416281320750394a459000c0f0f842d4090b0407503001e601542c41d41da82c100b1241107400303a1f40142c0c0101800c120003a40640c581000140a101521242c1000e903005003010301c02c440b400c21407644690008038602010000d40b5030303444c1c1000f981400ba0006003404000c0d9445180e6150004808000025590b91b0020032100a92100d8005201612854599254000107102d5540e5100d400b00520064054200141c41b000c0c8808455 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 652084667 1250 652083417 652083427
    0x1b0804080c0901031a07090b03090a030809030703020a0602130b0c1f090503030610051903020c010c05070c060c082808090d0f0509271b1206040e1011 66
    0x8040c545200c0c420102d01c200244070051001420814080322001e078407420030810f0703498040c01a180240190014141440007004001081c0780018404030f089000b40c66480d03554a80c00051030310703441901c00c0135025074400010500099241e9000f01220a140a044d5080503226142c0448650000003020b419502c201350a0b59032900600180d5039112880d0400c00403065255641030320b0340030040000b840340d08003a10400b03e40703000300101c0380081c2660115107640180c1c2c5802500a4001009689031903203050350750071402d40030724225513405801140303212000d85415000c5032003d180c2642100c4c006000e101e105503c0554003041d492400c80c80c9200c2d014245c009000800098000300010026032081555a46458114290300d642110f03614200d0b50381c10312a404a00032103500518880e00c04820020400703003c1c52100d02c0390060048441c4142c080c0150581450103015820710700302c3d9640000301080c080d250542c00081c813150f44409890700010006540300403a400341034410001d00300021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 652085917 1250 652084667 652084679
    0x40e1305191106090d0803070504061b0503040b0d180c090b01170106050c1903080108060c12010512010e0105070e240301051903140304170d0806060a1b0804 69
    0x401c0700c46903540000c4030007840d03400b6150a801c20b4261420303a4010500050404c65036103842c00c40e00c4801c0e40050302595241045103004040b42e01038842d8100140310107a240030010f1820344006c803219040802103042900308401043d2541c854035045039010b80c1c61100c0290390244c0d0804a24090003002c0c1c001c00c451030301c0c02c0101a1400500e0b014100281200100000c141e1044400d0540700203180064a602112003424908016210b101001440a064400406510100c400e050b9003010b41a9103240d1034201c0d42c1c00d098055183e01c081c035101080014042400c1c00d40080b005180c0d048008541100c1c501020382c01c4070f00541d40d0030001070400e10b50764210b04101c0900151113905100c207030300520000f481d001c541c0c0810702a15100c3c001c600c140c61008400501024055a0810100342c181511144180d0380c99000340f14042c0b180509221001c4101700c04550084101d6041d151802e2a81d1000100b055940c46550711509100080d00d11813140020050742c5000207200b40c0740b4550300d0382410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 652087167 1250 652085917 652085923
    0x8070303080702010e07090e010b0405040c0512030a020304030323030f0906010503160b030c2104150b093403020304051002031b0306211b0306070906080a02040e1305 73
    0x70205803c0da81004000c801407103000403c10300f141c40348000019080c913860490ba01402c50510050f078407600b804180300900144c0c102e03a02c01c55170304a0781d20881c01742d90301142ea2640100e00ea4840960014801000441c0c090300e41440c01500d00300c86040d203060070960200302604180c4800701c0030322007101000148601080904d0140c1320071402000307100d01c076142c3c025810b446801181e50b100000300104006804644c1614511708192150a00c451610b10100100540480c2c0550b0708880100030720410f509144a02c184405018180d0846039561075000a190491402c00310b840750b03a40712603640c00d504441d03400103103070360396a401698a00303140c01d1452034880018181020103104205100341b44200e0041e140003e401100b11688079900c21000966404c2d50400141c28407800d00b02c11240e0900101d084500c1400155115220100078030506603101001c5501002080303c40c80c003070cc0400d0280740d49541c0700040a9003d40f43c0f40d00c480b10568803440940e240095450044841c0b01045814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 652088417 1250 652087167 652087171
    0x40609021e060d020c16060c0b060105030c0a030903120e0a0311060127020903030d02030f102d0503010c050910030b060f09011106180d0509030330010807030308 71
    0x4424080c4100000c00000e030503485580c1008640c0b44e40003e4821a20a05102140c004580c40c000d0520a40d80c030740c009010040f81000c115071405d0030781e001074401d40c0540e0950b40207a4180a5080c20708440380c506a00420150000354144044c1d01c032842c0d125020b501441d0701400c0c841c4090100e000d09481d0103421480103409403c0250051001403000e4400c00c008100d80700650030401c280c0d283c0e03108104009110b0024400c1d054080000c5440141c1c040340c00643c01502c1e03840203581c4940c0d400111108680356070040c0c80c10440300d18110b030700c01c240140900d1150204003d0b946025070303940d00003a084400c2282c41d64003007040032521561504e0b2001d108461417003142414042c240c4000700203100380c0328001c00c000ba0010003046001859100f500740f0068070300f003201207440c2d5003800d0000208020800203142d059100c0e0301100003005209500b524410300010340154241004591b0600d02c0340d030001c2d00c0c2174041038180444000d40d00d200038214001d28850000d0b041c01703415401c00600340c0c400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 652089667 1250 652088417 652088449
    0xa090c030204111c0f27110a090207050105070906210519020c2508060105220c0c02150405060f0c0307020a061e0f0c2a06030e160f09050c07080304060902 68
    0x5e11b00085040f100a0280341149038402001c01c00d5030142d4002880b0300c403454209458481c40807a001080280540c0001e000b102162138101143c0d503212021690030780182011600e5907060041d1400803100340c0c109a4010280b04040210700c01154101d00403a002a150b0401c980d104107c54410001001000f8000c0d9021040c443c6202d410200c60326a188018402d690003040b4561500030790450301d045d0080c251240d100c080c441040580e6000740700c03103090b0005074468960704007510a040d00c0700c0c00f00e41c200c5001030f00b49400e1080c02da083c0c6003950089004c910160004119500060382e8072940e00c0d01030a05501ea000300c0c2c8901a2005200d14058030a080078040c4905000140075000007211101c5039100f5042c07184001c001740c410f070803182400030304c1a030320318400b0b0003041d0f80382c054102030a0b000121040b40d180d01d00c682c8048000104900c0340707401c1415507840074800c1c200075070049584407803030390a90781c580079185d601c49446500481e400d0361410303921300c1c40030114a40b0304c2c460509105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 652090917 1250 652089667 652089701
    0xa0609170c0706080702150106020a020109050910090e0a060c09090e07050607300f0809070608061e090a0b03011802130f0617150a090c030204111c0f 66
    0x100e651840c6982d0841d9014490500102c2c100084100d44200800c034140740d900040c1012a5a40c0c2101a5849004102c201d0100d4126480070525042c640c800070711894000300304460079440c044074000202200792000c40940211442800482d24a000f14120100c07242e030b8103031003503207480c183c101144c0c031201301c2d103200b5000300c00104141c2d43c513801034030700d880e80040c20025200241c0c0c4034060612801180850161a1800030404581d007003c1006100700c2030340c40c1c607003041d9520900c03a51960f845000b0300c00807600c404040b13007160901c042155032126480340f10f03040819a0030001000c4c2042203c0310307200c030b5440c1e1b403500c2c9180c01c003800f44a05084120008100d55143c8d0f50020b0038807241003100044a03030382c0e151015001002900504000c092010309100201c01d4000c1068580400012425400d00754602062491030117120720107106420040036a042c0d400d50382000090942910354118180c0241b220391020362402c1c0900c88008000c000006100d080059007c1c1603814040340d00c2c170140c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 652092167 1250 652090917 652090927
    0x44e020109090203010b270d080906090907021c020304030c170703170403060b030a0506182a040501050306040807020409080405130c08090c06040504091403030c04231e01110a060917 80
    0x30308ca80c800d44088aa00c500701548400c40351000c103450740100e8105590003512002800340d0b094011130160f0310800400071002450f11030203c240d80d45e202d136100040600d600c4440400c840c0c210b1810041c04c034002002a40c40c090380d01d0310303010390103160740a0113201e04200260070010050a441480c0c0e0313005050300a03000344041c03601c41c00d07101c00d0000c024045c160f4298007012407202050101c1010100d1015038840c0b0850717801c0903001c9039440320341207034040c2c1d2401c1d0000c152441c00051841c41560701c500c00780d140185507402c3c4000782c010050b04981540082c44085420350b0351201d80c490002c501500010402038003840100320185c00f0f440220300c0e130484980e2958507181c0c3d10890f01030301c0081e1000f2410340750b41c1c644039041c01a001c1c082101c902021061180080640c0003c108030340001003040b051034000102c6d030b0140c01e072a40004c0d60080d00940c0b0700c1d10641c0c90070107e41409605041c1034646189412815051079580c89003101c0d1159103107580d008108000a05081900c0800798090510b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 652093417 1250 652092167 652092169
    0xe0c01080730090503070b100302030d0c0f1a0f070f020318130c080f0a0b011b050109120c050601140d0b0c070206044e020109090203010b27 62
    0x944524001070104840d030701d82e04807140d400d041e648064810003090810444000b420081e460350000e0034120b1300ca403070040220388500080e89080003a260024043d08520340d5203903080d60300c000b056900702d40001e488103c100c007090b2004030201c0244d0074884a520701d89010000d221003c4402080b80042c0b10904060340c1929500000341c60640c2a645d0402403c0d10340440014001400d100c1c21115880c10485641c01d05035200311810700444055a811545850300a035120035214981101b41c001080c800030061182080c13038501e050030b0f015200004c0d100c105611a039001d480001170400c080307448050440e08100d010000c460042080070384081380189100001a000c41240002500040d000c40209408000070b204861056a004164680e20b0b036551071840500c0c1488013010400101c0c0c284a2101c9911842114271458003c03041040c0e10040502c0c1030504880020f000d904008001c000071a070515944011800f074007001103415120400e03142406208031f1211400e078080041c00800030700c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 652094667 1250 652093417 652093427
    0x4050103291309080a0e19150c0812010608060310050f010e04082205040b0433050904060501080c01020304120b060622060e06090603040b06030f0d030e0c010807 71
    0x103604001c5400e000c040503110038910183c0600c0c400138081360000034038404c100b40c0061070b07102c84107070964480c02800c10100508201c5a5184600040317000c100e00d40344810780c4940101d8281c1481340e008a81000c7d0800c60400700500b0981004001c100084284001841c2c204500240c14145880a000c00e1500e404007104512043c032803c00541c0039540410200480002680d404002c81500c0046030300e08400c103071500f402c55108443c01103150160602da2418a0300400c009991000744552811a4900c0480f182012070307107103074503800c0c034541d0040b58603581c07a42000d00540c0900000f140325410080001e09000c1c68180d04e9065500400c000c21a00150400071241a03402041d1902240e440d080490304921842030011a405e8541186010701ca01d06252b10080d20070b01da40f20b4100c414080117102e510700c9241f400340e5200c03505000103400900801c950941c400000f030103880418075200301052812410b49000b074042512221212501c2c038041000c010200d00074609035050341007071100601 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 652095917 1250 652094667 652094741
    0x10618150509070207050d0b060112110915130b0304020411040312080a0605060a021c08011a0c100509030a1b080a030b010c0b0109021b120910030b03030f04050103 72
    0x2014022400002c0c41e02d6000307004104c02130001078280b41c1c4c1f03981d1902c0d02030030b040411034034240401c05041d600d405240284c45061900081c50300b02c2450102000200005850000150001001d080200e241b002c1d03490100c5000408003075400d02d80328142481044141c810642c2100f0b0495414041000404d081540c00030203c0000c0c01c19a0040c1c03502e03201c05c03014050940003190002c500061280609a00045c2c030074440624600d0300c41c040e006400308903038038002881460408021a6115410042d01d240100400292141101c0600005042038400e0710400c40c1c006085030000b1514941c001d8101058070455010b060344040d03900901c1da510009400362040103c100743e541c2c03031024802d900407400700448541003048152a5a07682c02c0300c0b4003944c08465843e00452014488681075070001601c0710b401c072031911407a4109050f0009001c20b1414005a5000705030715a40101c03d107440a000070300080c0b600340d9004c2d5455040600150559800c0316007248644540301c1c9045190080c8540c0b15 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 652097167 1250 652095917 652095919
    0x34090504020306060412140a1505060102070806010b0f0c0a29040317151302030a0e031201030b19020409090b0f090a030e0301231e16080c0d0903020106181505 70
    0x40c01407041f0300300504061940c40e45036216201f414a540107200d0384999110038a501c02d04140540d0f07494100480c1c450b00907100d06010b560111006003c12100c5101900d20310746000380e09400c0c1103090311014500a642c072400e840c0b0f40d03221b1140f10001da100074455000c0701c88210601300345040a9074003c00c0002160080b0003d0705424010900c91229442c1290f0380d001c00a00010722280d02050480007580107407081c0014500d0030500741c000500100940d0404504051034282a03071940c4c8a0400c200c000030507801084480b0355800c140301c2c500744007030f06c003804242d14001a004001d113403641c28290b0281030407245d20805030800c20440000038048080d240e1518001c030407401c085021070301408200540803184007113290065050030000e0105480f802c50502020401d42c4200344c4408202400c4e500740100104450f1003015a0b40a0401c4640042645941d1407030808111080c038222030110100310010b1351039810800c00d2078440e480901100c03403022000c21410a000c13041c680b400c401c62140d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 652098417 1250 652097167 652097189
    0xa021f0807020f0a060c120207033209090604090f060204080618030a11120714100506061e1e0a0809070f030b0a02190801150e090f340905040203060604 67
    0x348070111310491203d1084211510150744a074410312b8058141403102079421042c040780c0510b20f1402e604141240d5004180d04100d41c9001240d00501962440c0280105d4100d41c4075451b000c006400200b800c3c00660240f07800507103c0b0300f020f031010b0030b18001500743c094400702c404140180100110403030703031080110704101c0d5034144280301d0702d400c2c01c004411100000101040e040b05124169003004100d400c3c03841500e4410002000e8002201c030706540d00d58000005101c3c074417030040ba403014a20220240d4500504241c203040f0090b4281030301824504030781001041c1c1d40011a040300c0c4054104903441d02034031007903044c41c49410008e0789602c0050192001c007808a803c503030896041710607208502c0d070441d0201c1403d4401904104003841010850000c202c03015044500c030f1851220310007802458410561170700b4924010002000c0c00d0107150708041e000d00c10124034003404a82d0420b82c40c903140425261020070180c042c2c0502d90046000364010420004c0d1503072a642114140c90801c068 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 652099667 1250 652098417 652098431
    0xa1508040c090606020c130c1704060f050c07050c09091011070c0305010204051513050103110d0507081b0c030904021e0301081e01140103140a021f0807020f0a06 71
    0x400c0c028203541d90b00030b41c0c801c2d00c0d00c03a01041140d800300b1420b08643e0191000c3c0100e0f00000402d80c210385405001000081725000103040391429180c40541080c0544400700740070f89112041c0040f0354061b50380320b101c1980080d01d003003000014440055140801c9403840424a00200307115103600c0515114040503580b003038480c1e62100d4403170a4900d0603400c227920780e00e402d46900d03020307000f50303c070380a002d102c0e02044860044002d022000c40d081029604c8a10b22550315201c010f4016003000d1390450b40c1c1044c2404110044e4070306200307861141e101a038031070b12a4145848520041581c10021441030381c800c000eaa000f14038000100c5080bc8070940d40169240e1021101310040c0c5089460100d6502c0000000a01c65000046040700b5054207081c55082c046c01c0490982200c40d80410701c0c417410703120030041012407900d5115103030940c0c5500944240302c1060313000600c203c2c104040c01035000409624071100951001076180e208c00350b40010204a0f0202e0101d90746ca11070410002c144036102d0328 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 652100917 1250 652099667 652099673
    0xf0204020a14040e0a05091f0203150d061512051e03070f0303060602010b0a030f02010c020a05040204030503040e060d050a1203060b0a0203031602011109060705030c0a05030c0c0a150804 82
    0xc5580518007910340030341c950fa00c4640c10b46132003005440c840342d62410a00402d60010010a05410490300c20a1013022000e0312028480030390401490a65105c07650000c1d030b8000c1d2140c10503004c080d44504000100c1c488070381006e4049034070039000110b821804030004400900c0020700b2110410203410789280c505000740c000b07803962141d000c1c010407420072854030500300354150304000191092030f0002c1c41820030b4842400070003030b85444083e0250300300301016409035000c0d040004c805070001c2c00c810180754070b42e00840c00ba43d000b544106d5007030b840001e0402103100b5103284290400e004440c0c0203417000b9641c8507107a03a0341d04138001400200c2c521003002d4619000b54888030003095201c86090f150354220802075201c0d0021a60440410b103010740d507141e130320300c1032140e8000e809c20607440605141c6050305100d2aa00300180840d501e1000f00072685034041c04011001d0802e1050000355030703554100c1c003901d0034605070340700940c081d0210300001e10500989000c1c184c031504a624002da16683c07141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 652102167 1250 652100917 652100927
    0xf02070f120f05030f1306020309010c0b060d05011802031203010f05091e0103141c050a05070c03080d090c0b0f030109020d0b0d080a03060e090a02010c020a0b13140603040f0204020a 80
    0x12400a143c1e200010b50700e00d000045030003a01048102105104182e50380e4407060740c0b01c0c46684210b60005407170f210081c0028401c1c0541c15000300c005450044410340070f95030305007103640c40c2d50b0000c1d4060300071a8540c2145410054400961070014841e4110351504030782420b11340c00c0f401100e10600c8540f000405a01a00941c0c40a01c11550050f403e1540d580c144890f95040c0f41040705410b008040750301003950f0000b005810480f01e00d03622549480c26220080314150400101211150405180000401c403410080d040c0b00d40074103000601e0310028a483d4441c031003039500034000c0a400b403200145030803a40055a046500c82500942d43d43d202040e01c0c0010301103003101d540c1c441d800c05010b10900442030098801000140c9007049581d0301c0d404160703e1071200b21003145407070380218070a20041d4440c0543e407034500e2026040044040d107070708081070541c00003900c6081c240300380c1104200c0100c080d00c121098203004c0c1c4a603441d6040603100e03800d00e80e02101c1c020740920380018112840078419 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 652103417 1250 652102167 652102193
    0xf0509040203120409051005010804030e220509010609150312120929150a120c0b030903030702010b061c1508010614040b0405191e050405010902010f02070f12 70
    0x81403d6a640791a5030740c070302c02000b080ea14101074182a5501243c2940035800c00c501035500342d1a13404101000c0420083c500c54016001c2c00d00241a2803400c0210000c1c1c01424004c580d000000b2445505000c0158103e0b0348040d0a21500c481d800c030108046045058a2420307200c0510703081c0c61440007583c800000d010720342002082c0281595850b030104094a030309641104551101045c55220910f07080340c0c444c0e070909241c1e8807000d180b07000c2007091600c80701ca0241e14490450404100c1d9a40241d00c4950801c40d2a0351190300300104001040d9820720607900e0303004089810606150140d0504000d80c2d400040c02c0070003954a020391340361500010500030040c503120f402400445e803501015902e07030340262840c1c1d014504002880420303140c280202440741c600002105490140744a00380040d104548082d23807448401803101e0703044079031070051911aa01030340010404140798070006004080c0d560960b0300319084180248a94a15140018200c0b10f0a4559000d10700301428080040440703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 652104667 1250 652103417 652103443
    0xb031b04030303020d14360601030c0f0e2401140c030a08160f050a170705030412020d050301051e06040e060901090b0603181e0319090f0509040203 65
    0x1000c5000400c06905400800844141c0f1070188060b400036a61050313025401d0b1440b003041c0e042c00c50001025000000c0c0da46280b110441c200248132060395049041481c00e81055440d4643c0310305c1882400f0740d0b980c520b4000c2c8510b13101d0402e40d292401c0300c809148075580d0780c0c00d20020011541e14a41c0c3c0b00325041020192100d00e030302c0d035480b0b1021810350361f0340c001c502c4007010680301c000061030102400040701000c3c40c107459010a0203160103085a05030f024462035824482e0448140300c00460a4060078813501140d120b681c0e0340e0502e410001c41144a03603010b08110750188506c108150b5100042d681120400e8603c0e000300d0b543c0c96025182e0f03688400303c454101da0b000c1000240e8600110020707004050507a203035000c907600d90b48000251240f05040c0750304a08204046040c1c44448c04050800080030000ea0340a4100d80c001098002c00307504a14081d80d001042034000d90383c1010b000c951500513400c04401035880e0907141008510300d441580e00ca680701ca00010700307544080c010710a02d010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 652105917 1250 652104667 652104721
    0x40507020c030f011a01020f03161b0f03061802030d080606040b13052b1b0e04050d0e0111150c16051c030b0d02120712030e09100f0b03 60
    0x70f1403c4a190082200721522050b45400315040304440d4000300320042c100f0401e030301441ca001181d00c40c4070004207401c101200d00c050501c0c40307242840300c5001140d010b80010000c00f1100e5146080c20810b5400720880c4e10082650b4411000042e640000d078500000542e08100308650784050010303059000743da01884030000000381c140721001103c25032405440e001c0b10409c555090100464079180200c515002210000300341140100e2420b420144a0380c41d440c5810f0101da031207103041850f00105031001c03616a0f1041c400712078520f03007000c20b00700d80c01d40038607042404061110340180e5400038220003500c0d8008180200e101f80800d5402c5600380c1d091000240d03a400d0030780c03600540e0741c9103e40c205005c0015045004405c01d100c0c1c05400700321200100003900c1d0141d2a002c00a0307105e213030641d0107818400c1650000d1950007003105210654000c1d00c80c08a01c420303920500491000080c004040a914118280719080308102d03610148c6100030340080d01c1780c0d40c51014980b10030150034190540341d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 652107167 1250 652105917 652105933
    0x102190306030203061602060f0406021e0306130209060a03050c12070207082503021207080601120506060904021804060908040e1f0f060f1704140706110c040507020c03 74
    0x1901a0441c00449100340c0c100d822a82c1c0c2e1175030f01004503043e21403003001a0085c3d0007180e00d400c000c100c101d40084c0208001032511284040c1d0818486a5602c503a414075030100402109140031070008034400c04d464420740c0fa2020501c00500c1c0c0e8491410648180340e5180c020441201d240400d80b9011100b02c0c0103100e990a000001030750300c800341c0c850b441c45032160490070703404100341e90801c0d621600407144a46a00781107030b0811101130308613041030a851080c5440011840390400c40903008280b101641d0b0640141420140d003003c40041c40117024902c0c1d0000d120058a0344c40c07207400344540c0d03408100314580359480e010014009902c00a8001c200c04207000c900c9810444e8041d004241d61591a070400b1030712a000c480d20030300e6108140d110070a1510070000a0b0140000144503545441c144441c1607021518000d2201e007a1800c2e2000d0f42d455490030b002c21310402c1540003520890400c4c61803156032210742da54880100500710700564984c8003050b0100d00070008034483c1c01c0d008045d9a150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 652108417 1250 652107167 652107217
    0x306050a0203180705030c0d1406100f050d020a05150f0c010b0112090b010308032205030901020c0303180d0816141606050304081e0a0203040f0506040e0a0b030102 72
    0x40c0d041910a0101c101c040c3e0b00c001501000014568110f40d00500138008516044040298100914400355000054404040d400ca0400e00035240306c0c00d4088004503c0a00301440c50905180a03080240110082501500560341c0e03005610115001260302c60429010046080340a000714081c1c4c0c1440030011442c1ca89150040d0444242c0b81002e983d60181c3c001c0440d40e0405881d07840740081c12800070040140003040c085801180e0192080d031141c881205014060040b1410240e13041c1c9160704041459000c1b582c4c180505140c41c8002c80c02107040540440c11101c4400e001e00450384613061005030300c402c10401c2802c0d101042c01c4c0c0c400c2c1c20501c03c41800e040484007a02540c40d1000e0007140c1800500c00e9250041000b6111555a51411a0f482d50b03641901079218042c0c101400b1240312000a141040600401e1440c10a41c061030f11546095580588001550022407051000384030600080034116002c1c0ea002e05403000c08150640c2c0040860300a2243c5514802980850520300f104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 652109667 1250 652108417 652108421
    0x10030b090303150607150b210616020609120d1407030912300624020607210507140409150806091c050c03070c15111908040306050a 58
    0x11542d890f0b00e6000c0c0d6250794a0800045101c1c180d0005c00b020400480e40c81d041009902c400c0ea00d40019100003030380d00002c070042c1202901c0f6520402507900600c1000120700144413911809480b9000070401030074444012611421a40310f80b41c04164080307200e04440942d80c04c84a110101d032a0b03e2450340c00e00400040182103885d0050301c141c5450f0b18180c0b44c2e144030340700142d000c21010203101c02c0c140a2105411000410800400d900f585440c4040341b614000c4880030000c8000070801c1100b0390001c08080c1c20164000c01c2d8105000c5011000500305000c4c031541c0201030000100000c081c1d0740c07032005490b50200303c40701403d448004200412007600b9507000d0780b08001022003003400c0542d100303600360307480d801100d82801d00d4200194100c0f00f449000c1504440c080b05081c0b03070b4201051002d1080c9150011001900d004c0d0709103008000c00c22555904d400b000049241c58842100e01d05440b940d0344406100ca10316102d524a17120052041500070f44008c0d640c049800d100030b003002e11040d40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 652110917 1250 652109667 652109671
    0x908040b09010e10081b0f04090507080109140412120f060801061a0711010203120c03070f110d08060d0204020403080c0105070903151d03030406050421140310030b090303 75
    0x701041801d43c1242c65032414616009032000f01e5030b03032545203507503075140038103107040001c0a00354625050018603201002d404c0540050401c03023000094a1034030b1180104031003810f030720004200b4030b0300804110010403801780d11b0744103420080c2a08000c600680449a031000070800280042c81c5c4100c00d40101455003140003183d01000090284036190b8500c0030071140300d59140b240109013040300350000f0b80f0310501c68000440c14016030341410200d15000c01c1024084401600f81c0000104200000381c200380100c001e60300d903140c4a0300103841040c9040d520410743e0241014860700c0000502540e0782c9406641080f58041c10075915196645021142e64015051a0210354281781c00190b102d0b204207144011a504031000d15035090524003600000d20440c1820a0f0300001c10300c40d4a48404100300640c06184a03e9000446140904095280140b144088011981070041c02555158000510304040bc0c2c0c40540580d2607d610708402d500398825400141080702020400c508503401001640c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 652112167 1250 652110917 652110919
    0x3090d050a0e0d0c05040c03020a2c0d0309050307060302030c070b1b040f03110d120e01030b09090d080c09060d180606080f06070c1509020d060e01020a111603150908040b09 76
    0x100c1101306d01203098069000d030f4003c0d28005141105041e41002110540c03001c0b0308519000380198bc1d0410010603410502d0b800c0030b80c041860800704004900701005031200400d0300745000c50031814812204010f5219110b000340c030002d00348003c1482c0250022126051184084078580e5039079070f0b607880200c070401070721041d5005110090000468101000e456031070951040300440c2c0000c10507000d0b189003040e034442504240d55500308400d0340e200c0003035082c059078201d0006e00b1a5001d01d07400518042c0002d0182e64481d0040c028a06503032520b0080d0b0b041c0780001e40000c21003000c8800710020082410b03d010300740c2400e0110008a00c540495144080d05028040d02c05941d5000401c0e610400c0b2960020045021f818460301c141906034000c044107840203007261050060741c0c0b2281e0a45548506000c05a5800120343e0072242d045030b4440051030000e00501244e04220074034a5017080c4c1880f0141c83e034858180ca04be00741080303612044800741d00803200c179103468482031500501d4010031516 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 652113417 1250 652112167 652112171
    0x70f020c0a0506040e070219030c02130c050306060f0f1201031e030903080a1e021b0405090c0d03110613020a090e072709050a0204060b03090d050a0e0d0c0504 70
    0x90300c01828142191400c1e039401a2010745814a0418070384440200113140c1c40845c05011010007052100c0c42480075014001d503140500c1a84a0041060489100004480c81031030080f075804115002410789502000407035513140ca0b984122510400d52103143c00340c0c01503c4e40001c1c0c41d8204209515070034143c0f8003030071404030031001300307072481b00c1c5407a40000180224032040410800245090001c18401d00d19203050f1902000035006400c41801015050000d0b8100100802001100c09070b0300d10f03c05001c840500213800c022080b2030701c030b0304540c001c01e015504c82c80410b0705141c0210440301d012490392048845c0c0d49026000031001d00b9903100101e10400020500160781901e0303018100c0300106113409050030914003075040003074401d0ba401d510000001400c07a042c0c261aa0306c00c0241082c042c90207030142c1c800502c100701c126101030b0042d081c1c420050042c030901c01800954090203695904110b0340d01d118611003a5250703000c0c209150f0380003803a0303040c0301c08001d26610030201b143ca0075101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 652114667 1250 652113417 652113433
    0xd080a0e0c19080129091e0f0103030f020118150603080403080301080c04111b120705010b03100204180221010303021509010203070c15061a0316081509060a0509070f02 74
    0x60000f040036070b04600d40302c0469824217820741d1410501040d0407074001d45104034840d0a002c01c071520004222482c0141d003035407000410506420041c4c40d20405030620080200b0b00c00070021000c442e14403440a003045400c640d1031201c0012560100000d10381250015031034664031b24200400b07034424080c50509d4000d41c041d541310f40c02e1600506100f40c1042c40f86605101c0035a4035103064504040c1c2c040094800d1104c2c0c000e012308201d00034550280101c00108255004005242c034007250a54100c0045104010030050301e00b80310b142101e410108400945d07210200300c0b501c540d02115481c2498108060317400002059000070341500105c000580e00706c3c090f07071205803a40c200c2c0400c46a11001c01c265451100004400a805d110000086030000902c00e8030346003001c01d4098141c0425030041c0001044c494454200b41d00f04084005030318182d00949801c04144180c0032220246901030031760040490842d80c1c50f001c0102c042c00c0c0142095025151800008150361135001c880005802601c40c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 652115917 1250 652114667 652114691
    0x3190c0906050a030f05011416090b0a051903090510090b060d200319050606091003050d03020d0902030f0705010e06041203080702190302031306020d080a0e0c190801 73
    0x41c450031141e00400280c0031501e140c5410a5643c00700340111a155a1841c0c1c445000e642c52a80901504903180408040003c0120151056140d034002d0740c10200c0c140146404030f82c0c0321088445641d0302c9000c0640402c0c4005003900540203905000341140540b50f00c41420790700701e50100c3c1c00c0c9070180291a0300d5440d40014400c0c1c40c1401c0798040c00a10007800181072600c0c0310200c41c40860000b074102e8101c190700c1c001150310020080300440d80c0381c1284e0140070461800144607504400c921000c001001d25654400360345402c152600020300d50042803480301800b099024040c0290040d0a4a0112a21448260300c0c0c8210380030740c9000c5415a81c0f2041c69050240584054810180901c440c01c80c29031002d542c5200002e0694046225035109580e200c511040420452072180e0000c5032210043c2c8003030804000b050b04000110b5016944100009500c1a0600c0e0010041200042c01c0f40034a06028108075400301741c2500040ca01090700c000350900c1c0e9010049455000003040030429981d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 652117167 1250 652115917 652115921
    0xf120e040c0210050c0d06140102070501050a020c22090c05090a0c0e060318161805130f0c2111030616030b0303041d0a0b03010506030706050f0903190c09 68
    0x5003550040e8401146a40510121350025400529030042d150138500c000960b44141c40b86508144c20345040b0171850303041560100b160390040e100908241e820b00e030040e80000c1d07030b50706940c40f01da200d8500240101c2d0900d812850200e0308084140040c40480002d0401b00504c00c41881540d0040c1c0c4808001154140d45110740d03026914142c2c1c60704800c680c000c04011181c0c0003c1c1c001e0562139141d050340000c02d0010805e481e070035010034003502c40321440e004201c42c4214520b2040d19415062408114880c41d00c080c908500540c40550161002c205041484140a03150041491740300d00342840c2c400103003c10380c02500306208000c00108000000302b0716031101000d45040340c0c1d03901480d0038284040e0107038014003040720014045030b00305a40e80c43c409001c00000c9540c03010714103080c000d120701821640141d145030101540244030b14180703100420b584550300e1060404010011034020a010704c0e0500303c0340c4085000341265481c0c03185420316014010312010480b401c0707d0b60b100004003150b940c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 652118417 1250 652117167 652117181
    0x61801181805060a0f0608070807050f03061e041a1c1a0c25031b0c05010e03100e0304260c1c060f06090e06160e0a030f120e04 56
    0x107204060903407041d19407501500700075240543c86600814045189030151780500001c1206940d002d4082c01c15a04c05411501e01070550703801c00008120705606001c00408072074000400340c0c0c00c1d445814024401c0b864007084009116446402c1400f1660000c81e0b50789111300280046900404240c41d95803000031700c0002e000020049925040c0c50581422803859069011420488991500e02c68071400e03805223065225036690581c0d0029000203240c0e00403260342c1d600401d001c414980400710b440d080580355203407103102d041000d0308032850340b15241480094911703441c0b4002803140b0a83c000801e0740f42d802c03600030070500800d1114084003480003c021441d103010079001821800f01c0d6001442082c1d03c581425044c501d1001c100f410006540c0e204010880358042000076150b03040012034000c5e12001d4072103603981d41c040710034040001950818000b2200e0503003064008021854003080038103c20303610107013090349a030100109100240e42141a1403c2a0b80c034901c0c000c50306c4c41048200c4200e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 652119667 1250 652118417 652118429
    0x21906020a1b02090f090f0d17091f05060d05070e0417160f02151c06050102010c091715040f0c05010914010f03150f0503060a051915030206180118 65
    0x4801c010510200c00003030380c5c6030482c0344038094645041d0180c01c500e02d07007500340482000150810350750b51103055200360410341200ca400d0142c82264504a4540103540c8040806450642d59102044195580345c3ca0007030b082d80e00000380c4e103006645002c0c035810300f01d0407a000d856009410300c000010b0711000086659000341340f1549442c40a50b034890341c401d4034044104030b82154840c060b111039948414040d11981d200c203050400100181c00903501603900517800035042d681001c3c0f00928160304036443c030041d00c01400d00001080b20340000c5074942044000c3c40841242c03603509200522107001818085603011344000c0411aa842c001101c04d00d803140b0409880c6c0c202040c1c644129072145549440d80d003820300d40130444428642c01481d07001030701d13409000030504120003082903080921903140d101c0000380c01001a450311a1028031403080e60100183e40341da40d010040c2d048070448680f5070185da0081d010544403074442803990b20314440d409201c1d0100780024008120140020344400580301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 652120917 1250 652119667 652119679
    0x609091b14031c021e160f06120b131e1407050a031a0418020310060b0702060f040f03150f110f0711090709060f0207061b03021906020a1b02 62
    0x1051000034070f9885103031144411401140e0032603081300300314035038512181c9101c8007804ca15050150480184101d983c0000d05405030440100607e0b60000d80400c02e00003010b002007882c0131301100042110b0000c030301e02100302d1b00c2c201e01c00e04205506c01546d00d280c42407503010070042800c0622010503e5040301e840d00060820010244031602c2034011a00c0713814004108061050b10340e0009041c1d903440c081e140705000c480c501940952038100b201d9208043c44c0c3d201008558201001da149500c5440c401a018205c009220004940e11748110307401040b030238880b00d201585070318000080802d280da02000003400c2064a0311145030b40d202d545140c00b09922054682520501003060a0300b04e800c0980340c03a00081a41007803070300c49a4070ac1d88122100e5a030340010b40d08054014040340000e100030030855110030401c0c0031890b04101e415060042c80c0f0002007540e20780b4035040b841c2c40400d103d4941400c8107000d0003070802030306802811400360300303458121202200d5400481d0407402443d029621407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 652122167 1250 652120917 652120933
    0xc020606120a080f090402070f200a030c05060f04090e100e0105090d0e0d020402040b0307091203050304080d0204170f1c120203040606050d0c031a06061803010609091b1403 76
    0x81c6a001803c1760507018002606001d0701780c481603100325070480103a941c103003011122100c0108038044a040d00808a41404999056454403002241c15024087c0600301c0051140c0d00c9200c4601550014139000c0740a01c5600d600900e01601c0e210800440d040143c1070090360b034018401805224401e04640004104010b10310104444150b1003a03882d03038100714940e0302c0d00c0240c1c80f14001040600075050000d07a50707082c80d09008000500c1ea901c185405a03107400c0c003e0000e5030110407241c1050b00604295160110304181d90020710031607003c043c000a020346050002000855682c003441420030554044805510740d20301d0203001450b003e80014500e0030038800c81815a8051500f117400b840b4001061601e98010881c01030000c1c10a0329120100c8808104110144e041242c64008803480c050440c21700d000403420b10300405c0d041c1c000c8846144da01070f038561800d500540c001c203d078000c140a161070508240b440e110b5501e0690021002040c80031980403500c410724100317108060000c0440d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 652123417 1250 652122167 652122187
    0x142409131226040c050d0620040308030708060f210d02010e0304030f17070c0905090d0e0d2a0602070b03060d03050c01060b030c030702010c0f0f031e0c020606120a08 73
    0x4040020302c00c49211054403c0880c461301c2e403030b89079066a48121f03000120201c1c04c1c0710030b4042e8030080d8505400c12000301300c18000500304000fa41e403c0951030416003d192180710005145143c1c4007140b1340c0000c202c1c641d0b0b0740c9078440c030501c1e0f030404112035041d0351800166020403400d0b20010111100b403603204120810001d606010b4803801540a03d20700030110b928a2a90b0300d0035801204165203401106005210281607845400c0e081120140148070950f94040090008000d035400244034148441c6e008050200152019101150002c1c1c411010109400c650003203c0050040c000188074405000c21410000c104480c0103c40091401202c00419078046880794040e6080c070420307548800e030000351034041c100518020103a80c58081e44914110038000e00711550140800200480e6812a001c1940c108043d01805441c0340780208400c4080d0100c2c4800340540341c01e4100c080e107080d114035001603010840e01d004a604540321070b3350b403419468180d0f0f0b03a0010700d005003180108000b504d1039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 652124667 1250 652123417 652123487
    0x4050906091501050906070803070f1202070203151f180b0d05060402042c01062c06060a03060509090609120301060f0f0e1206010609091424091312 65
    0x150781700034103051070100c0c1aa2141000c1d00296a034002040c60741048003103864120114624540785101c0c218240754064001075030b240342720030142c03600d00c5850b00401c9d105054000780b10980d0040c1d02450301420f40c0c900b22a200b40d0b81001d0488007480c5484456501482d0024410301c0303050708100201031544494007000020a0460701072010b410820052030443c00c0681c0000048007a004000110300740740801e5100d8852000c900340c4440c0381c1025040c6004e070b42c885869034024200351501c2d512070780d103a03106034005c01c49600465032003200c3d03004000d0300420015066109203850b6080d11003002205500f40c117140002e000d0303840411b01c0c20040114640c8181403400000055140c00c1d4400c0800001003030400c41d2506441c1c001303800400c01480081d030490340310030050002d01410840c00001441075460440094400002d1a045503a03003803c84c44001148000d810000f8504040d034146105a080385200301ca8040710f0302c07030480c1020b15005004800b20044518004600c03054400c512031442c003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 652125917 1250 652124667 652124677
    0x10050a0302120f0f0c04200a0c0309050d0b2a07060902010903140307301b080309070e011d04060b1201110418060501020304050907030902150405090609150105 70
    0xc1c86104219603d1002d20040000421600c484006403c0f00680c0b08140070644180384a03d01c000440d400e51514142e11001c1220b4022820b0f103040485404a450201c6500f00e00d58000e07540035030710b803013840140120000d0aa0084010b00024000c91194485a100000540149000d800c50130b00482e404910a50041c0082520500d0480c11850716a514030ba1807040d01c1d0301000703c9910101c0d01c80300b00700304070048261402010703002c4281c042c0d078506000354038840c1c001030000b008074005032880f184101d03008060a00f40d0001103541c99140c40d803803035641c905482c484d2882d5415001300015a0301c0302188540b11007004401e21351b01640c0d440d02d50130054080101625084581a101a04030034428400d1140508800840c140d1302c61810780300101c00c051200c9034100b45e900e031a504001e85d80e000021070702210b02c107a550090703039518240190018007040034041d4100c260b4400c0250801c0d4090f0040c429100704641281103616050107102410404540d4002001000814400c40303601681c0501 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 652127167 1250 652125917 652125949
    0x120807080f0706020d0f0c0c21050d05040807121407231b0102070b04050604030308060102030f04060c15090b070509030a230607050a170601050c030a090302040510050a0302 76
    0x51400030143d4030002260b1100085e08045d41e40d40022011184a6000303806040b1f40c00d1610300780c405482d031100929481003440381c01400135444115030840d4003c1d800e450311418a40c004101c14581820014080e6124843c101e40d100441480c1687c40b034018000402e034031140442c041d00b0022685c3e5104072504c0c1103c030301105400c1c00300110380380b803504000c40c444000b031440c010180f003501800003914000f100d400c54500e01d041880300740002c0e15080240c0d0200d80c0c00d85002a1a51036290042c3e040d4400e000a03d0707943d1000150101d80650000700c0a081148502c0c0d000d00c550f503040c1180c1c411100a501e00401e0b4248100c0801d95a51081001d0100094010190307401000300399541180a410320307011000c01d400701061113a000f8820300c4100e520001c203050080ca0700302c61042c000d095400c00c2a03107483d8841c100c40480c6159100e201070760744000c003800480765a04051500940500807031b1004911584c10710001950744454080c90904890014124401046c1198200202a18103120342 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 652128417 1250 652127167 652127197
    0x20f190807020d0b190b0f030a020f12060c0a0906030c020d08060a050a030b040b1806160e0d051f021309020f0918180303070e0f04060806010f0f12080708 68
    0x1a10121300090101d6028000078030720a4080850442d00074140e80042040600c624429030300103e5a803004110341010660441d80b000c00c0c01d40d11000151120251380c01d0005902c1000104000310780408010b100c103625039181c0200c419650b10045090b10300303c0400d80010703040b480510b031b0070720f009d070000a40180380109031114030b648030004251402d00991007030720514a401d06000c00c1c007180b554042d412074141480d0381c0d1300541c1e40007074507910903000d850b40045408110040c1d044920178000140c840d03100404007801001282400c0340c0d11405580c3e05448000d0400f040d02c8241d0003842240c242d16200741118088a281003d641300a41100d000140003010410919541d0760340c500a022088110481007045802d0403101d0020b00d00205030b202c0416802002408109500810300900710041203610400c5130800d5000706000e0801c680c440c1007603200342c100204181c1d030000441002c0da280c00c00e200d8030007507407210350160340720380d6440240171030300704000200114005000401e0b80010351244 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 652129667 1250 652128417 652128439
    0x3090803030a09061a0d08032a270901210501111e03040f0f150c08070e030604150e03041a040f090c020d080a150b03040201020f19080702 61
    0x24090459004a90310040c2641d11031280040043d5845009400084541105501040d540100c1e9015606880203440e0100100020f41e112800c18880300c14940d07240403080c001400100d00e01180d401500c00c1e8199008098246000041802e2030059032090003040c004081c3d1812a00e00c1c4614040c0007d110780145561075100400c40c00d01655414107203444040d581c0e850b840b0180200303d20303c400c0c1941d410310104107210204070414403c6850070707002220001c0ca50014548800d03182600c5030301c601006d0901101813002038101504902c141000d440d0445501c00749030415880d001c08072001003c202008100c03802c4064aa84000b44c90000e00c000c0700e1400d6181c008040b038114100400703100303e250004083c0030743d50341b90ba040c100a007542541801844404500691107203100b0140b030b01003142c10310000f2050021500140000500040030045550304c5d00301c440312607402224103a01500c10304441880d5030000080455003001c2d4007400400804c0075a07206145940404010b0340d0001d44822 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 652130917 1250 652129667 652129679
    0x60d0203070b0d0b0d030e041503240e240711100f200d0903140a030f0e0303010e07050a020a0b190e160b090a091d0f011e090309 57
    0x84101d024100e840300c0b003511541d0900a880543c1c3c602d542e50b50195240d845034400291f00556001e007101811603011a044000490748200c8551036031020305694050000f2160200301e824005c0120136841c1c20900c0050501144240e5070025440c031203000c10010701c010500e1001e010203036500400c0354500300d03051440c2c0105403031500206444150090b0381c2d0703014240030b03003003203115021200300e60300302c03100f0b40d412590b8091016000ba42d602d2980c0584402400c403c05201d81204050317401ca0840903504d40b1782c1d03170900030014484004031880581c600302503c0f0660703000000342e80c120b4048031400c8220740e61744207040b1202c0d000000c4050943c410800040005144001458402c01c01d00c82c00c0120301c09440c01c4a002e0304c54601600301c0503000111441090a48103101c01d041c1c82040105959510040000c58041c5031240d20000340d85290090300e00010b60f1101c0c0c94448190540120b03140f088044107550b003224884219030041e0103203070400a5401ea507075000000703034074040d05000c0c000507520f85d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 652132167 1250 652130917 652130923
    0xf04060b030c12130b01031104060b1606050a0501030507050d0302010e010504060c20030406050a020a050114040b01090234020307060f0906050c03030a090f08070c05150c060708060d0203 82
    0x1440e19610b0010110304024034400d241c4201d13900103802d0703400c00c0d1164000e03280c488251a06000203880080ca40060301030907140c40e00808028018036200b80e03650f44007a094140c0540b1204030864000b810701001c40c40c51103c0c1c0c000c0320b058a030020094041750341f0304420004400b007101c038112b0941d502d91707100180d084420310407103100b940528404104058210f00c0107286c0a55103064942d03450240b014809200000409d03142030715801d017441981e0f5102c415060f07180c03c1001d08014510341c2000f9084078402400081a8003c130300c02e001c0111942d80392010300041e0301076001190414028113954002000384005403002491f15580014607070038442c1c021a013400c605822000120b10320200a460300c1c0e41c0301d6400001003a062620500704144802c0413522880043d01003003449403145400000c0c401c0c0d4078290b08065034030540296440c00c1918158a02d0885482800d20558070b050560021990100894000381014000b41c01d031583c070000190340c4104050801900860940040c0005840170 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 652133417 1250 652132167 652132171
    0xa0e070909061e2c090c031014010b1813020c0607210c081b1902010e0d0c050d110708011a0306150a031403120c0c070801020a0c020f04060b03 63
    0x3c2d500342118819002c81d14101e0041d80c0d0b02048040a00c0c4080106002c042580101c608640300e020202e02e407504600c6500c0e0503802c14400390b25024014490b020800c0f2640001d825000400045410303a9a450303c08015000f41415201c0290902c44082441d14001d0400b92503003041150043c1010f0200480c0c0d0300d00b02e01240d2070408030381540c504410040c86650b02a01040491405004910705050010404038018140001001e0403503d07180030f0004140c10303034140c0b030314828410411180da0380d4020701034000307028040c40c903004154002c55094810b404120000f5040380040143c45003544003120144420404c0d041c06028100d400700300c518089c00356015030601a00345003004000d183c00c06041403009006c0c1068010b419801d1080b40d1903078211842103e810014103038084820001e8142144920080c00c040003000c0b90801c011040882c015110700701c404821141841d496203030309402c03031045c000b0240c0840d04150703c6c0001031400c415154040380002d03001242c0745076107400080c010303082 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 652134667 1250 652133417 652133429
    0xc0f0a0503040201031103010b09011128030f0305010b090d020406030b091b0307060c1b05100c1a010503100c14040f150201021c18050a0309150c020a0e07090906 71
    0x100000303020941d0317031501a1010350300c617510856141d1352509520790403500c42c00034010305100c20140b00c404440e40500185002001d0400440041c446801d48624011a0340600724086001c450380400300c144203100f028141c0f0042e600c000c0c0f502140c03104202c03110500c206c04070f0303009884400100014403030081203405100e8030401030080c11200d00310360302c41d103101c06515030007584a94001c1041030b03807150324521810740000000b507080707089900c050352030540f581080b600111030084840c1010350007079940355694004c2542002d402c01010702007035842e0081c46040d5050340100040c5001c071030603500480341c808039030038a0700c4400d1901d507240c0e440d0f422a61140d801100d03110300801129490080242c1c156600e0300c001c5107821615202030220010405206010540d918210360340e00750261801090319400000b201c07040480d614005040258901403801c61181c41000588268060b00514944c103900504040c05103044ca900f441f09110300400d002c003003020380c00300007810041070722580c030207082 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 652135917 1250 652134667 652134677
    0x20a0b0301060f0c0b04121211030402012006060108070c060608010209030c0105040308030a150302130e07060c0f0807051203010b120f01050d0b0c0c011103060a061e05030c0f0a 78
    0xb00d402d00240c840e1100480340e4081c0650390791103500003080304410b01c4c1d115522811a64120070101801c0b44e20b0030f808408028030615164040254084d088040c5100310b200b681c5001c0040c1e0011642c82520349005a200003e1f03229002180e16580a00f20322540011186042e0340c1d10081034940304190342c040e038403841c090b960024031940d8a00f4107100d007000d50b203420700301a03262919690b03448585100050100843d01ea86660400ca845440c400085c010f5800030804c58002840301d9442000f401101ea1269051040700400500c03240034040b800303403c1c1d8004019407400222034440b040d2690000341c0850340343c043c42d11a4180034561002039406090b0851015032298070001050300a0000078201c1030452060100401159480c0a606000f29078000301e82401901c414411501c07034020080c00c01500e50800005562105103000950702c1140c0880d581c0f4000c564442c400d0b0b038000282d198100110820260000034640280d009542112090b58440d20b4001322909504840c0c00221142e00064 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 652137167 1250 652135917 652135919
    0x301150b0711151b0d0804031205040501201b010c050702040906020415020303010614120103030e010e06040618050a350d0302041805070912050c040e0a200d1e020a0b0301 75
    0x11005c002d072110035035103401d01000b242402e1310007a0107402c241c580720480070346403000202081000c1d00903500401c041061030841c0810208007209a800201d4180c4c522081e04024910b20768050140c1001105151100c2d4a04030071a0244070140403400001da5180340c003080002180511164a4000030030207501664495043c400d00402c28903055510b0181c4900900c08000d10103650804c4504691707050410b010740f1541840142d48402e00c0d0452981c0c025004107002464076008081c4501011585140c00781203034442003080a0b0407024040c60b014100100e121804a01d074400c1221061444001e034132660140004803d0303e880e50141c2020300003034001c1810403012440a40032015150514800d0120b4581400c1c003c0c03202e4014131070143c072501c888a1030801e11070107010400c8003c10280c02030211460314039419a4403112441c0c12111801202c6118140400c483e1107140d15500041000d00c1104550b250440018900304444060704818150900180ea4203240d5400801d00442003648039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 652138417 1250 652137167 652137217
    0x803030f06010f020105011406031e0c03010807080307050604080c0a05120702130506030c240c1c090e01030f0c0b070b0414070e010b03070203040506180301150b071115 74
    0x10b25410343c4080e05581c149030041c4070094040381d0101541c0b90a94009440e50340d0050002550508802041e0800365040213001844d5400001541a82c074200c00300c403034176561451400d95903c01e03d0000340c07143d000700b070206c0c3c0003d06000080501c1440c00048070900c5645480707060900140e8456a5415140000c43e901182054452155070003900e9908105620304400403c1e105e6000e422a1403098000d1071100008000d004003030046102c822048548840c80030345581d0361181089158503103203100034031950115100e04216010ba450404101d54241d1841e0783c0c0c0c0d016030310940c00440301912511000b107070714440c14010301492070140152104a0815007010b071987c3c0003a00700074a80d6049100180080c40484080030304503000080025a25947d41d9412415805550805540030800280b004100c2400c0c00703007601484802c400812503050200b045a080041911500c0103405003070004c83c4c046000c4003810034a1030806000710380c502802e6018524035601030500f4060905c8060746614036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 652139667 1250 652138417 652138427
    0x209090703060f0c020d080c130803370f031e022a030f0c0f030403080414010519120f061d090109031b1707030809160e150a0803030f0601 61
    0xc4042d81d034010007402c140360138020f44131054a036981050140d120003040c603000102c0201d030220382e407846031840200e80300da0f21552660b000c003152103032608203c00c0340c07181144142c40101189075a8030540c0c01e4142c604105440e00402c018140707050680d5188a1150985081400424501d81c40c10060b03948000c501800190030003007141c50700002d80d402046400c00c1001003250441c2d078606448946800049080615011408081c01000e0001040000c108000032010300160b417076075000001e4a074400c100440341c0e030140800344000c000401401c5e400090058100c14205d500140012600710b910700402d00666980381d1112200c0c408041040310034602500d1801c2e08030b03050100034000c032120f0381c500501d0880690003413508290b03a0b04801c0b04002c621001c1c1c0d0f0301040558000c5445200904000e030802804403244585030041e0b81020551002c1821070710251000a214031401c0d44800c04030303001818407509040d4020781c4004011801e0103003003028611030900605608150300e002c10004007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 652140917 1250 652139667 652139681
    0x80424030605010801140d12030e060901090f0222150501120501030c090c1e081e07020607031a150405040605061305060928060f021f090c03020909070306 68
    0x30186008410712481c0e910400c0d090449401a1a0802c407a0382d0300001036100083c0c00000f442003050a013601900c43d050780001c24031b1145681038600d199580300d01e0f00e090300c0081000425030300c80a02c0c84801031404081202030b081c50b024500c860031440d81f00b00303000c54024194050760700c20880410840c940c0c0c09000803c000b11001014401545182e4645403448aa4040c010415071113410840085114410707100c8004880310f5100c11820b80c01201409141007640c5040324020380c519140e01d0160603c40045c0200519802080f203940c580400714000d0025202d204890141d8011311b0000d0703a180d10315403200700c0f00c6030001551a80b4000400040303234203035442140640d0081c80302c1021030440f001c41000701d95094035001d503140c000c8070028040d1000c2102c410b0303480c8000910020b4900b20552203005441050700d5030004d84030710309802d036a030700c003000c148110400c02da40248041e50415004041030904c501c4240300d000f0717100d900060304c100044030002c419901445082003401100d0141203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 652142167 1250 652140917 652140989
    0x70c141603020f040917070c0b040305300406021b0109080a0b0405010603021c030e1903110a050909030309070911030103020108041a1518060f10020106030804 70
    0x4a8210411981403141250380d2101920481c80e40d5282d20441d19280c1000d0002d80d440498520152026480040c440e00060026550002035800c0802c041c0c4000b8119025a6080b0b0f0040203200e400c1c01280c00503104c1d800800e440d407900c2014000e80d240921014201800441d00074286016000880544a403200404e0a04210392100c0400101001059000596410245194540da120b08105024242c20791000b03401c01e0400311148000f10748141c0390405144250b4400ea58003401342c0802c0b00c48545403403c01c0b82424104020000075046480500d644280a0b00c080c0f400380e0395200240c1d04502c12a004110b80c0c000004100c0c4c100024030188000d006820000c0010340b000d442407080a0105000082c144091600414103104030030301030840c9d02c1045e01c01505580b070800301c08440c24011098450040d07208a200000c0c040180325018860b05019183c0401c54a01804105108a5455004095558030100440402d00c2c080090000e89691541c0060200480607108010031030b5000302 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 652143417 1250 652142167 652142173
    0x32d0f07090b090907060e0d080c07030f1506050f060c0c040c180f030506070f0309060911180105060a031d06010608010f12050c0f49110108070314070c14 68
    0x1c0c482190011849250a0700a603423003100a011854400b00350702c0340f0038810800d445088000410000602075400190f44141c0c02c81a8050b0450002c9080e0380050003500d41c4185240a0341a560074168041c0080306424011982104080008102141e00b184032010010f01a070400e150707403001031091071004280104c02101000d14584800d5102c10307003c0c140f1010040070601d52440c1c1c6219402909101d500490100f25201c0035103040180146c403160014041e105606011100c401ca10404a040301c002401c0d55203406020ba03812401050300340c5040c06420040c00012030f51600808c850b50103090141c07225000d95045c00404a121034241d40001d09003540000c9201c00120080f640d030394841026101080208141c0b00042c001c81c840c80c540705a200440d58824440c7c4000b40035402400042c01683c0038981180c0000c107040714002c00003e81170f1802c4c051b16002951040e6201e41d0f110403945400904148003200c2003940c60350030768031880025011310340c00003800f1104407031200c149006402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 652144667 1250 652143417 652143419
    0x100e1908071d040204020d1416030c030209150c1905150a0504120c0201020f0109031701060309020a060c020f12010b0102011409070303080c070b0f0114032d0f07090b090907 76
    0x840b81c03003180c00410003402281c010404002c5551540c0005042460540c940d50085c60107a055501c03510480700349100080c1003294018a180c081d00c02c40c2c2c041a00944404c04400c070303c650744145544042029009849400030420a07000b80c0c107240c0040c544594017415401c513844051f15003404018110110382d601c1c00c0d0500000402c40284a801c14030fa03401c0840440000e400140d0030400680c0c000301e0a0350826800320101075001c60320340446041c0f0030b419111a62140c1c1c048044466911000f5040450280c0a00000d4092074960785118401031000401020b2080070a9280000100c080c042e13a4407044003001035030302070103104030340d240300000f08400c4d191804800d40d072113501d884007600340026180802c2400f0400d4085a02540d000154503242d41040c281507004000c00b44100c0da10010400d40c450080c0c03a0103e801440900f403181c200385510780e00c02044103154010603420185114031410304841300c81c148020030046c02c0b1400009001c40300ba03000d1040c0600d006040007041d40000c20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 652145917 1250 652144667 652144709
    0x4061e03020a091e03051b040e030a09300b091e030405010f0c0803040507030c080102030106052704140109060b031311030f1204090e010b0f100e190807 67
    0x40d10030110303031810381c16803142c1070708000b40700d0780c3c81303981d000a4800d0040294030804400003102c51108501d056800f0010207442c1d4900300c1c0c681c0100000d0750f0000e00da81c0d408200c07200d03a23122041245141018148001c1100d2600310707441d04000481110a034100340100041403006005000039200b031166042807220820029680b030388160300800381440b00701803d055603607100e0540820b1942d0b03c44001d0385c0d20304150500981c0d0320303850310080390007410120700400c2510060090742c0c101ca58a88421341400384030300000322503541c0c04001c0103c88001194440b17881e41c0314040d84029070900c0710b070710b0819414602103005540c0942c1100b5480c180400901034005204800049910b8001d010960045961000a41080150103600f50a84203003040f501011303403aa40104212601c0001c10009401d000b0000e43c240d03010304241580c080410040d40c8180c0c06c002c0040300440b50356161494401d52040002580c00e0141217114500403d860300a12004c8420002003010b0900211603840d0f81c01609 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 652147167 1250 652145917 652145927
    0x110d08190c09180f0e07170f0303040b04020d150b101b08160215090306070306080607140c0f0718050c0304080f040506070302010207110907020d050c030c0304061e03020a 75
    0x441143c8151405036240a0f0511055000180d0513100060030f2044090803602e80d5900c8206e070040384d03051144007482c10010700000a060f8070541c141d4000d182140d5032600d07072548545004005036040460034404c10001404e2400b102d030f06803c1c2d0a8005811800d0b441403040501c12603000100b44a030300103043c0740c140c0c3c5000e080c01a9a6025481036511a0100d803211151a8005030003500164032444181d44044100c02a00343d29205908a81c15991480400c4080c0c031454491440b20741c11000c04141c82da44a0302c0d03216005a0642400361408840320121803074080120304004c030f02e8000460038404400400c3c174024154545a105101c2420580d207002c02c02e2102400041881800040b4540140c403054207603001080001c00c2143c03a14030f00c2c24064081c1d8407500c42190b0005020040c4101442e24040103402007140c0c0c0d00130500d4179054242501c4c03c3c2d0140440b0b102511052003001c03080c50b0100000d0000c2c0c4155134425900707000d0320403950311031403100310904241401849000c510301d0307003c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 652148417 1250 652147167 652147169
    0x70207080304120b0628030501050c03040c1203140d0c0206060931020d030c02120a0b06010509010c060504140f0f0d030f0b090103140c0109050f010c03110d08190c09 73
    0x2003841381c2e0042d19a030b00061074681c2d4901003445032060321501c4251031030000e2140411603005100a01165640c400c50105511080742d00a0000b1920038040c01101a10700f00c0344d40981c481d04010640d914151140212034201c6500d102e51240c44000001c150740e410f01082d508008182e40e851030504154154036100700000441c2c80b60604c0e1114804e614103031001c00c80342c51a801620600c03901c1803c0c14000c0032010300c07030020b034002c0285840340e10920301c00007544ca810a03040104401e0342c0c0c440c1d0703004440c01e030b010240c860704000e40102200007280840c81480e0040744503420b260401000c00b04920b0038004607201131b03201a000801c0d24014060042082e42c107200052600003280d0b0141c120040082000346c070a5600b0030107880001c0b003001111404001c062822804a40b2000320140044510013114050142c00c080002c2c81607817507500480380c1170341c240c1c400c0c201091301c050440605840d0403405010280007900d01d9052287e13a0f03003074003840540714034440014840e1144d650400340c5980d000f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 652149667 1250 652148417 652148423
    0xf17010f2d090c12060f060801080c1e0f040218010e1002150406060305160320061222080d060509040203031606152d301a07020708030412 61
    0x150000c3ca40700c0d51081401981e4038141d03003010044c0c15100c4121044213007545c05110041412038002082c028000140900c1003080100204000070b01409110103c00c6031000d41508005a55060b9131190b4581c00079102082100c071010b003d00c04140001424243c0a0407003d009451600c1080f40580d40880c82040f05600c1c40801800c688803881c01100600e040d074400b42003401000c0344450206041d802d00000c03640a011010f101c404000342c0b4140d08580f115080c7c2d40410100703d0100d1800801c9851640f084d13000c104008005c0c41d0030700ba200400120401242c0d844000101a81e02ea07031113120b00c0c0060319054407280302c0c9181c00c0d4042a41e80c03050764001d250b0783c9610324600e001c1101e42e0704503808503100d6802c0d00c2c040c155903034080ea081d420b51900d09035480d410010316103030b00f000c0808508102c64107600c440e09219500741e0011801d1440c41195010104d666134120b0100d030303884440084040c4080302c04159881c0c8a44000d04142242c2c210094a03002000100502c039820841d640901350 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 652150917 1250 652149667 652149671
    0x806010e04030c0602030103030806090a110412050304030804030b0a180c0302370302090f070c0201110309060a0921080f160506010f0305060709050a03030f17010f2d09 74
    0x2241c0c14142d07841000d4060044c1140e000000202c209a4002d520901840041e0343c01c0031541c444170491800d65007a142036810010051004210230074060300180400b5020b40162407819031680c540081560041d0020344540c0301035010700814400c2ca104020100482e010750805250322595041c00121407071201034422143e10156541080d82400d07507010b08074440601e580300069181300025038016502c000da206c0c040320b00c0017400c420710021000c0d120700c0555865030401c4110341c3c015200b2440c0b20303800b40140e11050040002a48030301c0300400c00b0501320386841d01d003a072810b0135a91011001ea5045110b045511403507900080d101c0d03051b10220552000303d1600c40c03a2441c0f02c420381940c8054094070318819040001400d081d0040d6210607680200b060790041ea45a69080d1101c0740c0c86c0c4507180c0c000b1302850040012078491041030313646140f42c0c0307096a00241505500300324800c00b03070054098503843c240100110240d81c5440b9a12846801243c80301c000b4030041520400b0b21807044003007540d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 652152167 1250 652150917 652150921
    0x706050a0302190f020f19031404030506070206012c06040f09020303031303080106110304060305070504180c0306150509040203090a02090a0209090f160e03010b04110d11040806010e 80
    0x280a40c041d903a0fa0804a038581007010481600140010000b030700c140090f000b2645601180100801c0403900056212001400314005030390807508041c0c036800180d02407509100100000c1c00c00e002e40d50080c00070b94018980c950400c03a1040c20411410b8402d01c1c0481c00c000b0320110910050815544003000304d0380094441c01300c03545407001e0050940029414003001003081100a001500300c40b083d8000e80e610000303a038844005139012407040800705580d60080c0020040c2a00caa084254040030318034240b82010359a0311070300e080f41850400c5a080b0b9444503000c24140360b01d84290b0009080140d02941e90003c084400f5002d44a6056500e00a44d00040041d00c1600200b143c44526030b4060502d07001450030695681c000d41010911504c41c81134000420b4904810643da54000c0a40d0044058150700800040d02c0c4990645003850f0195251101c00007070381d45a10074928405c3c0454089a55810a0048034044410040103c90a2403051205000f2404001101c5041d00e11151140b00d4603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 652153417 1250 652152167 652152187
    0x10620101a04020f04140f0303030a0b041811040c0504050d230601030b39090a03141006121101180f2601090503180a03020a03050d081503070605 64
    0x718400d038105603086400003c911440c0000107004204641401580314004908082041045a9903055055050b4404d101040320703000b003a4003030320300002c00400c00a0407010310034035440c00110b050002d540ba100e6000071340b20682014080c104d070340c00e02031510910706030130000021a039802d0400041e051007401140c840c01400325080c20401c41c0b403510100c83c0c06680d00e01e0541803022003108c104104e55604020980d10119554000300900480c044400c9407240465641055421524100d40d10039061600000420b00380156002c0400703503640a007001083c0039a204040d64440d6006a680310140000c400c007080e260394242c01c01c001c09103444500403200c5201c0a284848941015845200350300c0001121103d5010010100200e04802c4100410070342010742241d80f00c034030140c140e80041000e148118541441c406000c0d40040010910035169000706000202580048665030312074485901016000a41160300084074106410143c10001c00700c0c0d10ba082ca031198005100300400e1513520 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 652154667 1250 652153417 652153451
    0x110606010917070816030309060513170c040c120b0f0918030d020c01020a030e031810110105090309090f090a03121b0806040f0e120a030908030103030801062010 71
    0xb0028242212000a085c110200000c1900d00c07040300801ea0078400014407a00031010355205040c0c101003102d41c6ca1808000e1801c1003608101c4000e14004e034003443c0295911480340c00c0010440d50380703c01701c01200241c413108071812025058468004200e0404c910390310107016580c80240181e0300414500b20a801d00e00d98010003032050070031400800e00c0e20640d08154044e045c10045582c090000011b4080440d84a12441000d5038404040a546401c0350400c050300c0300f6400c255240101130f19040c00c0d03005084810a4458204503040019102d4807840d0030101e071900550003d80316010340c00d1a0081c950360b0381c8003c1005081c003e015030404521002c550120750180d040341d03590030110310000ca0003050707500d040350440e10551504004072440f403051720a110780844a08000c016980c180aa010050b40203040c003042055100e6009000066441010b140250b1203030f1a4070b14a0b5041500142c9518600340044000c0c2e200d151110000031400580745c1c041c41d400120010301c03540a18002c10b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 652155917 1250 652154667 652154669
    0x100c02030a08030f16050a03090c080111070b281a100534140109061d0606030309010f0804210f2003030f0a0e060a060611060601091707 60
    0x94180142160601804402401140f198135a13104040c100c1c0d46640c030201d01c40c60055600b6002601c18030001c0d04c0c0500a52085840740c1c0078001c40b0100a076607030340890950b100c050009034500700c046681020040011900381e04480705e040d203000c00c0c014402400444444280450714030b0b0352a100d8010361b0414240b0f00d01e903204000340020740d20410140c006010350340140b1800f80c24400c88080c1b060034007503078004198820030044440d410055561140c0c5540d41e244503048a02c0d5507510072107000144944210a8110880d000815039165000300080c18004000e041074069081045a40580d83e40010103100305005420841e55588450810840c012040c0500c0b140d4903540000b54207a60b500840100c281d00d00c590384083d5a040e01c140d1401c9034600342200442545e109101045115550005480c3d1200001c0d10009602e1a181c15040ca03106003502e803105116900c0b1401d020342c80c1c1c0a40e05005003014800100170074284140001c1c21014144107403035000161101818040c001441804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 652157167 1250 652155917 652155919
    0x122a010c03050403022b030f020f04080f15012106020c0a06021b070503120307180e100504140f060607080d0b01091d0106030c030b0909060103140c0f100c02 69
    0x5640300149001e40200825542a00540301c0c0440305203003d480782041e0f040d598164802c00c43c2e264058441075000d0300070b148138040c4480d028800c1c102c444040c00c0280c002400e4400c004c050359104080d5071410102071030540742c410420103005100c040d01d80141e400801d1120341d032074000d83d0311a082c0380000380240c40882d6042c1c000c41c1c4452042c0012600940104a0041c5149500d406811400c59454000348113564068008544d030503000c0200a000e90fa000c0c1103814606480c0c48100c0c0c84000d0700a00381c1007075944000e03000900110000003072000c0c0203840c081d00c08000c1c030707a1203000030381c40c4040081460301031000d00e500240c12500e80100b50b42d00a50f0001480b80c80f400b1801842026282205e5128005109c1c0c180015949102e042034a5500712000c0309c103074290b4202002100600180d0014200341925900c01c5c00168030b5540f805d61040d058200a13180729415481c1010b038020300700030030301c0c096405413202d60081d56900020b00b0707424400325100301c2070078000c0c842500c00c001004000303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 652158273 1106 652157167 652157171
    0x501031421130f030b04060501050607030c2a0e0603100504030c03030b0d080705060901051b04060e0f030106060c1703100b0913020c011508122a01 65
    0x1000c00100010480c0c40c2c0a485076000c00191416a008031800c0755850100310901480344191409000c0c119001441d00071280c600810140c0154400350031010340540a91611500c0100c0811a02a144211010a6a5810800083c801110b6541c06401541e0941e0714441d41403094074801c55258480541c8036005440440060154112443d00b102180c0c1c440c0c008109000b0180071000e100317400500e001e107480800d0600f507540240c2100f1303100d0440c402190700c5490001c10742d801d442442c50000a015001000502071340341800c0d105416510702000480e50326484809041d82600401003e00e000c040e00203217415911007204c4600302f4170420b60f8103000c0f01b03000b003009200850005024030440303034a00303001d02c040342d00000085400340e43d1080f00c0d183c03d140d240f001c0001044a1806002030544074408400d0500c0f03401c2160b0780c0700c51007201303a80b0080302c910450081c459002c1c0007 = true := by decide +kernel

theorem cover : BRFrame.Cov 651978417 652158273 := by
  have h0 := BRFrame.cov_init 651978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 651978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 651978417 ≤ n) (h2 : n < 652158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
