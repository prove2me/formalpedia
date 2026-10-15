-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:06.474336+00:00
-- url     : https://prove2.me/submissions/19c8c888-8772-4cc8-8732-f64a36370e42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 738848920 ≤ n < 739028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 738850170 1250 738848920 738848939
    0x11030a06050402130627230f0f22020406122a0b0a0309051002041d060402030c0306010c210207080708032d0717070302011a13090219 59
    0x2c1d80e0903401101c000d0304041511415209800c16612000b03084000140f02c105440d21040002420b580410786450120350f41007401d0540d448203000a8010f64154030300642c40c100c0c7c80c00001c107021904000b9a09100d5080c50514681c2d4401c00341080c2d1045a40e4140003040c06000145d00004003d210020b184041c40101d111440c1c000080c80394400d801c4008101c000c016100c1c1d8040c046e0800700805c05040c1a42c080ea220304000c2d4810401c0e140403000040e00d440882e000b660042140b01c3c40d110059202c0680400e0013030380110100c1c0d045042d414030601c031444500004240e18140460f1845040034841c05440d503c0c6201520007100c0c800340c2034050000c0d2294610301c107180852142c2c0501040344d10b004000d542e101c0342c0c41240b0300442c0d0044a00707034000c1600390050044202c001c20416011809100f490408181800c80407503940809160003401c40301c2030b80055a140c1c4042091541d0b65482d10100d841480740c0142c0441c002403140001010582001041d0049030400440010107021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 738851420 1250 738850170 738850181
    0x603170a231207020a02030729030c0901020f0109080304080306060d1a010e031207020103091509051b1804060518010f0b010305070206070c0813030609061e0b060d0911030a06 77
    0x4502206500030340f2000c2c001d90b540d280e010740c0254190010f070b0090240003141070004000324200b0020200e034408101c8a41901d52003644c10000a035000101000596010032240001220344402000811203c0d1030307007030060201800040c149040040410407581d2610203032102102d2a1204000b0701c040b8034101c0a051715400403480c04141240006101441e0104442150720241c1c40c890b442d0800e00c1e4011030081c0000340080b0f440214003441d01080003814800c0e0780d0701ca03104000030b20201180c0302182304a02d180e042164491703844641d5003091090703400c01070350f00300d64041400b15440d2a60710200c0034450b02c1c403000c908658680003081d50000c17210340146000b004280ca0030459078440381c0d822610b0704000c807840301c003150340098200e00140c00140204014800c00c0d5020084589030380d1030405031180c0a405440094031388c4100446d502850041820300c0008110400c0000340c9880410f810b80241c92044000680e50a140300520600384800130901e680141038403208406e41c50701000600c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 738852670 1250 738851420 738851437
    0x50105030a0f0221181506180108070504110a02210d02160c050a0303140c1603030305090d0f0c03081b07050f0709110d0c0207080d0905130603170a23 66
    0x40340c0f5400f0172450000401040003003442900580304111515a0510702c0f5070029240d039400550b103110b00c2c0320f01710141e50f100340030780017440103072014500c0c2c4820031080e01d150a4100c0301000c01041840c102075000180d101c0c04805c02a045141151290b0380343d4540d0062040d80d04500f400010608911522807814156052241c0c1c000e20f000c60302d5030309000c90001d060000a000c03511a0301041c02c140c10f580060800c0c00c0c1c00030102c0305101c3c0805031400c00c00103280d00c1100440c0c2c442c414049801c4c0c0038032071584d03805000e2418520349899024014111b0303004240140c140100c2c040490f01e8075030310300d00c803411400c52429004e9440034185019a540c10000f00c003c4024015490003240c418414090740042c0410084c03030905064400f20725500a10002c1c00c0601588030b41031001036420000e2081d070400d0b003515103811700703000c0c40c200500c0201038403035800d080811b2400701d0600000b0700e2244040d8400e20f40e80c01342d81e00c8a010322000d4906080c0d003014900a0806000c2e04458900741c0002085003c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 738853920 1250 738852670 738852727
    0x22107200f07120201080105060d0f0c0c020f010c0302030910120e030a0f02060f1815250c080712052b0b0d0506040212030906030f090606010513050105030a0f02 71
    0x140c3c1c0d81000349004803040030002d0006171284010000780c5055030282014943c014800150f15003208448011202c000c00000d000c103420140c040d0661800c3c10322507038070041c20b0a01c4107481c20307a0780e4001d440f0711030f00781524441c0c03049114581c404c91040c05055014480309008000141480c0c50560b981d400c40d00030a00001c60354459030703154034808a003503401400c90038920a450349a40795481d0007a1107489031180d80303200d0803034404c0070100381c0201c1900600700e01c03603074190200d200c0030300840c1040d41c018010280030300307081c084c00020502403c4800300741e08001c1c802d54441c14200100c1f828070811140101080328141007406103401840098500c10440c2c408010302d402010500030181c2004201518980100d0001030140c24690504500700d00c985003a00d141561440000c0c0c40c43d0411b48001b4a40d802040800c07035422801c0000540240f02404c1a40c2013a42040c14100000002d001d418100480800440d01c081c0ca0360708036030f803140c04d0940c042d51a0030440420061b41ca90211260924 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 738855170 1250 738853920 738853933
    0x41a030d1707030b010e101106180604110f150406020d1e211802090702120724051906090b062205040501060819022107200f 55
    0xca402003501151100480d0100e0816580316202a0010000d0003070040c144000c04001c28442d03a5001221400044151540004400d03080351309864004020303c00803006100500c25007a00f500085c0c1103901c00d52000300340315403c090704003189442d403204899680260800031b040404400740c4005d08180d80c0f00360f00720303803200c81020307411607001c24092080c00e444140d03c002c140d4000e00c100418000b088010407500d010f890040310000450326100c041a0103c10840e00d14021403610090054128030b8910003030600504902c2401d82600c00d24000400b0300e40c109c054074031200c0e80c02808502c06404610200680d06d0803050b482211f41003445500560741c6003050106602e141c40c814049880c10280c079450034160110716410703000c076403102000c8110041c4200001d8590312405134601808059594080508000104581c11a502101c2e460401e00520800c501615201140c0d6190882c81c41c07260340d2515a0941641d41e660090000c80050034148010a44564009444601c89040e0000c8401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 738856420 1250 738855170 738855193
    0x41d060324070e240a090e0702010207050f16290a0c11031c030b030109022e0903020d021516121106010f0504050403180810050a0203071e0509041a03 66
    0x100304465040b000c540007a0f04009141e000d1380d0000e00980503ca00301000c0351922501c01203003590b000c666030300050790000b401504200d0203100c806d8249220030005c0050b60550400004002c1e5280241c4424110143e5000307201c040d42241c01c41448a241e0070590b40d0861054000d001c000164015154008401c0c20341e1401c0c00d000030001c5503000c0a040d5144100d148000840160090303900311a03040d03488600010259442c680c000c41805400c0d0664010071440e4242004406481201041403107000c00c810400350f11101030f0301c4142941110218080751040e40c4e041190b0054510740f00d040c002920b200b0040207000ca00514043e0f071103407160400752403042c10041e07490000340604180c82006110401081c20503411181d0003520a003020b0442140b20285e000d40c0d02150f0707008500903406461040c21000c1c40d031188903000a0504015455843c202d00701a0001a800c000a001044010199000c41d0700c02c4081e610490380040040c481001403039088000030800d035a40b68400c1c001c1d22174426 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 738857670 1250 738856420 738856429
    0x506060a5a0905070c0308060913080418050105030304080709050c2701021902281d070f2a08090a030b0f07020313290d02031803041d060324070e 64
    0x700035546c90f58445010742d8846040c00400b03407001c4d1420041d030818440100010340e002d4094400b03004c030080d42c203480c4001421500300781c40069110b18003c1e081007100b800009001704018065407110794011803540c9500380407420500c02c00e03a0f0b00d45118010025000000700400c0305080d4601c090b4203d80f094124234000f424401e803201c800079442000169484c00340c41540404000b15544c60303c1c188422a0b87c0c0c09a25021080d98003008440c90b0b0300c404000010703401c4034840402094a24101d403401000c0d207500b003c0d440c9804c12088200f0742014030312003002448030844006400103440386c5074056403031400b402c00782400c0c1c2d804d60303941c51035100060001c0e10000a842d00201e80703541c4115070354940010b00d44210000750300300801880300c81304010030b14203860082c0640b2074058070040e40da150450750580348642010108185400810003044050711115458268121020103c1100c2d11840e000a14001a0100642507002601d2050103803000c242d0040307109104946a0105000d0004c0810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 738858920 1250 738857670 738857687
    0xe060601090311031e0a060507050a05030a0b0a1a07170705030703050f0f0301030b01050310110301060e0103090501050a05071209020a1401030b030a0506060a5a090507 74
    0x50008a00c101c0400c041000d15501d1081040e0203400c0e50701c1907424411000072000742070410745150340800c85c03810400c061845001e074402c01c9071401c6c40c181410000000c0c02484007800022205844480302907080d80c0d10100040104610000301c194854040946800303a044007005403460f404e40c0402000c182c0b03600e400c6a003000d40c010091031821b5410f603010342d00d0760070814201518841c00e201c03032102110003030000c6000c2c42c0280710710100c2c1c1d0b01d01804c26103001203035249458030508024449500d0110301d070031303241584c49500b044d42c010312204004134002d019480001e0200e41c2000144804801d4682c481c900404080e9030304650001000c100d84140c1d0001c401c002d4014840744010800100e500342000b030000c60502d004a40c002c50080001e18040542a050b281a003040c01400308a290a055020003490484001d4030030001940c440041c0c18440000041c04404280b00c0c80c841561001030b9803400c4558440c14001c222010310303201c0601740240290160a8640340204070000e0042542 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 738860170 1250 738858920 738858931
    0x30403020604031e0b0c0306270115270e01170304180204150906030b1c08070212070b18010c11010c020f0a091a0a030c17030f04090905010e06 63
    0x1002c0c81d007441e582d55600810708050341d201110100002000004c1c400d00c0c1d1a6028240e0b000d000780c0c6a0800d50700f000040380744e00785000c04800003550b0828400c1000054241150080724000401209500303094070081c02c0e014048642c400921100103403440c4480e50b18054499104c0340980d203a03212501c1440200d50034124a081c0c6d03105110030004050f080341035540c0040700c0c17440542000d548520704010655403c2510002c0380e9404801d02940703901d03108040c1059001c4800d01c80c0e1443d540840c2401c1b210761080580181c2c2d0002d80c0310290f4071024071084220081d00c0c100c404081e1b69400461441c1c000d8080541481914054400079612515212a050b81c0000420048005140040d10741c808a40c4049030012103008620346240d444c03400340b8004202004011580c414888400c0080c00c1d815a407940c410300601c5030034404a8218540c103000d40b003140809414542000010310319600070000320811382240000c0214595586070007500005110340300a00003d00481c00036030f10382500304c92 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 738861420 1250 738860170 738860179
    0x1050a021c020123061018052e0c03020d080c090607030e060a201b011101090c06050705100e0c040c0504030b01030c05130507021c030b210d0203040302 67
    0x11511144038024050100603645000008105006008100320425022410010340d0038100802c05e5601b00140c40b07800c03411052411007024030352600d020010070a58001c0c18082c105074201a00c4c00c0c0c3c1c480a01ca9054000c01750100403c0c51840c200815800100c58201c00501504d80d0102d011801540d260f4043c11903100010b06040c400024400c203600170b48010344c01c024585090000c191150340050801c11220b40da0103280302c000f0810707901c2101c540d07240030003594450b1b03010260014a00b41c008003480c400b440d10759504c18a82c1c504034007400b804075018045400106000542580040007801c0c114400c9060314403081550303250404581c020142c091882d0040c00c033400c3c030f91a11354407003080a029400d100781413030f40381e407201c1c0d0300090309030012200f4441400080c00f00d49040b059190641c804458140f10034641f0300c070001e486462000b501d100031808602c60f484c1c00780c02074100c0c140c041c1c00904139220b00856004211000c6840681030303b21070050004104029201004070740640b90082e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 738862670 1250 738861420 738861433
    0x80a090b07110904030507060e0f07140603070503040201091e0612020717090d0c0902031e150d0f020d200a0b0417010212070e030606010c1e05100c050301030b0601050a02 75
    0x10b080c80b281c02801402102040420415503001440c1445800e840081c1c807801030520102e011034541c60b0808a070010744440c1d00704802480b6a0361943e0031a64014060b140c560b446e5111440180d803103d4103a00200003007100c0207200c072030211007000078804071601951200c1c240c240f20440d2804074490050098024910000b00001301a840402080e6184020b131604030041403a840e000c0c038105140d000400042e8002040c051440184505c14030300c80083ca841910303d040a00e111002064041662400fa00200384242c040c4805641d07502d0419401402210008015150029203040c0c00c120f15480300c1100c01d08520141010b03070301c000580782c45519003032503c1d0400200d64681e0070030412000f460340d009c0080803100014103010702e019860305e03101ca020543d002000c0601700b0200030140c90400104c03502d0721000c0f80c0c2001200d112a54001582020f4403a181811801d115003c1c1c0a40300179030501e07006282482c1c0c0b09000318100ca0103205503d000361101c0004446c0b13881107101c0382e00141d0003034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 738863920 1250 738862670 738862703
    0x90a0e0f07030b0f033c1e19030507060f020c0304120c1205070e010905060108071116140901120f0b130b0c1b0724120207080a090b07 59
    0x340c1c0f241c0e11044005201d030514040d18400079160030f200d04100c552001700102501e0102c1d05a150032041c1102c5600400803541014083c2c40d6240013110845110400740e20009180344000d01003559081c00360711114000300220f00b805001c0d5840020100c40480c1f038103200e0798a4002c8e5100383c1d82e09602800103541361a1511248504e0b540c28960184c0d00c09003503560020340300c0312409002010034805d401510000e8500303100c3e140c124005034054480d050810707040186982e400000c041d40036649041000142050448203840e02d4081c2030650102094a6800b048403c400454500b28010031a00d0441c04e80e22030304203c1c90b400e82d06800a142101490a08001441c402600d9500084050b1420345094690f15250049401943d0807101d840780000e010101103480d1b00d4025842c100480100701c4185843c2441000c104541801e4140f5855012501c5001788075110001026800c10000c0d03481c1c0c1d08600302044198800d8503d4000f0540208000522111217020b580d401a002104139110701241b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 738865170 1250 738863920 738863927
    0x2805061915050a1e11100917030a3902031303031b0c0b031e0709030210030b09010306062412021804141f08060a0b0102070317090a0e0f07 61
    0xc03c030b0f40402d011242144c002001c02c101c08081c0780c0f007480d0340ca04900301007020346903040c15422000055030504143c0c122020030307000d41421070000e444400c850755950b01d01d125040200804610403541484951203450a00c83c5900071400c0524000622040c2d040000c6060ba520311075690421400b0700303035140800c0402d000301000d20301c2c1030004095200d00300f410394a01e074000002d5000304820700000300c14001c1c00c08100d220310001504000d030205983c00c000754040c00e82c0802d488000c1c0b081c20600c0b034510200e882078111034203031480504000103558480c549400603003014004c2032400d108900380028880d0026444001401c0251030300c5500040c01c00c5854003940c4402102101c0e04a2201144000d40f143d05c0b54000340e40040d842d07020300303007840c400400d41a005001106c2c4a00024481400490300c017140c4d46402440d800390024000b500c00c1e0042c1e05280e200d50001d4140000300c80440c10350301e0703001d004061080c4100c40034505d2076103e03600030f540003400b0307580d201c00e0190704400992100d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 738866420 1250 738865170 738865177
    0xf02040f050714040807260f0312010506121305100e0f061b04120c15030509070f06020d0c0224070b0601030213060c02031018110f06030f280506191505 67
    0x2240803118011f009200c8100c0c0c540701800c00c501619610000e60495000800d10100c0d000d41000c0f90f009280c031f04038103021100c0520241941c00e0700070f01c1040000030010f08000d0210900302d51001848800e40140e0f42035114484500c180c141030245100003415075148420041c154907400b1250b070b04045c140452400f801d1680c9404440d402100000801d942c604191040b403050020354000c039581c50100050303030038000310381e01200550101441c14821a43c000c5001c0c1c0c0d00b006545040a404195400000c28650103034101481d15503200000480c0400c4d1040280405400358501040075101d0000460403442004200390380c42c2103090091003614403c00048212500007801c07581a00701070100e80c005c660301840c0b12140e07503400840f00020040030b840744062a2800721000a0490010340c0821910302c0001c10b8103840740ca143c1d001440e003031003104902e190426041706044142c1c0c0500c144c0320040c41c040d20311703500c114590855000d6070920b800001c001d695103460030302c50b0780d009140f05489942 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 738867670 1250 738866420 738866459
    0x70f080907030b010f290313080405040c020313060f0c0b0915152b0b060102031b071703190e1c0b010509011d0708040f02040f050714040807 62
    0x514000040403e114a000030b000c1c15030001080711061400c0a141c44d0f42c6001d01c1c1382900a05040307002400c0094040942e0760100114040c00d482101900d0101d44920650b0000c65002c0c0c42c0c44e1500f000154000050410f507040d03c018060b81c9a19000181c135422624402c5000140e40620a900000c41da109076030b030400510f400301e900c6411f20000b0380c60710f018105c40342c0e0317108151006030b41c055140c4181e02003140e0004d4500584075540e051075540340c1d50f49201b0050800307298100451400d920030412184030158480840444100099031140c541d03e0b54440c0e418803108003200d41d10034000210464501030003100030b400580b41000401e0b1241207207000016070140c01c0002d2006d6045100903400c00c0d03184182c071010199070400c010403000d00303010b810900407038104940729032842c03000c01101c58220400e418200480d9031580743c04e021680300c002000f0b412a080c0001d84192303440c00c4d00218000c6640392141005042c149118210501851040c002c8a601c660010000388203a602c4a01044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 738868920 1250 738867670 738867673
    0x9060c0106090e0a150b06190c26030c07030c0b0103110a0506040b070b0a060503070303031d0109030c0803040606051203070b060f01050405090c0906040e1501030615180e10081203070f0809 83
    0x11074003500e414010f080203a88d500401c03040c110100c100500710407081c0c85d16141c01c5908498480c5c690080003640001072051001d148005207480515001d40b04d00010140d2010f41d0200c10f42e140d20300760700d80c0c0b140c0801c024000c4039034002c0072640d490702c00c007940c00351a03038283c240380ac000f12501c0c0c40c4031504000d40441103c035030324003001c161500c0c240035440245020741c6010030202c1c1c044d00400c18013406a0520304659242c0080c880c0081e6102c441607056176049940c03992a03489034100341c0001d1410b58400c13a072100c402c50071103490340c4011010344a0f050241d800024140d90700f00520801014960045000442c20030040c042482d05105494114600455050414040d803020580c2688a5006890950141c00400c03200802c02415449444020b20b400d2044a01e4414418006030071031030703a0310510441300401800242c130b00c1c090500078265540e004510307040c6010310041c401c1c91405858058040c2480c006400d0130803a080740e00500b100e41d074080a120040c82d0488802e02d014020300c0c00ea = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 738870170 1250 738868920 738868927
    0x31207201b0112090f0201050703030209030303070e030d020c01080c07150e01020c07080309090a1d07030308010f0608040507171501030302010b131b050d0209060c0106090e0a150b06 80
    0x1980c41002001e1440001c68140d104958080e000506903030010400c4003400d40c10a1100800180c100c0c24100000342c1c20b08000c2c1e101d81540c501a0b01030b0080c042c100d5007611012040009841e885410300d102800142c05551f01140c0c0100f0807078641a0403505680403075000000b107550001404004c1910a00030145000e1421040400c50183ca041c7c00d941100f030313134000c240c08520342e405208040050084600030761802041c5000b22b03440c01c0000f425540225521038116020003c1c042d0050030000040d02641d0340d02da00c0f8030380a040c8600c28041c1c251202c9904002007062401060100e004a0b0030100808002d498a00d10b07a0701025400306c01c140b507008407170302000c4483d4815800781c042c5101c4e800102d0350032505414084d41d4200041f14000e0241807010044550ba002401c01003034036140c1c038107103943c0c2c415002c01074042e100d0200e0b03040d0006000640110b01035010750280c2c0585450010074815800c690508982e80c40003440301030024440c6041c0007200c0c0182e40e00004556a000d00340509 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 738871420 1250 738870170 738870227
    0x9030102070c08010509030309100903170f01030c080c060403060c051323060f090f03030c0a0803011a0708030c09040906050703090201140307020a1e1b0801060602031207 75
    0x20381c0c1260320125506400070340280710303040e03003030007160385c0015038800650179403800c0d81ca0555591528031170b911400d65030300000c1090601c07440300c0b0f5107010700c2007601e0704a60800c0d14070110511000d100c240c0c2c1a4604503070102d505203000c0350007440f030600100094203150540e100d072802030807000107130018402c00304511802c61240441ca4001000c0300f070300144c9031601318170301d0136415400107207042d02c50b62080005a032484408800d41d2009101603840a081c02d0940000c28174602c59113862904c144a4403156800700561038004506a90201908000b98100e8080302c1ca0a40107008000b0000e41050001a03d1441900c0c0503022240e002480440c2000c5180c80f5041103d100f0707603240c400245c55259040a55030481c82003040800c0c0103c21904c0d51400079030080d1160030b6060300401032200020089402c0c400304840300405500800c0307180d4550405402d040b0800b00c0c900c0790701031a50030070710001005030010080e61410399542c2c89105403035658000807503100e100b080c5420b100300600f004011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 738872670 1250 738871420 738871423
    0x120f120c01060906060210050105010203040f1710021303050c09010e0103150b06070c030b0f0606090f04141518101401020f0a0303020307120504020618010c0b090a0c06020606010206011a0903 84
    0x13004203981e401501d0988502c0c111602035490582060341035602c100001c205045ca491002c1d0300310781c140408a180300d0030400c000760a10290004d000c0086e8004950b840da000e02d030405282c2200e00c00c80c219080e201c5034030b050100500c8240309410a04120000400200c3c2004464924401500400144460301940041c03040e8006440556030181c07100000d100300109043d90316089440a00100b0440c602840081c2052040045170747c0180441c8207881d425032903580200e0000c2e4104002c15609280041002203a5207062030503c0c4100005a2500304003914101d866010f0312942113a070074001d05112040b0300000e501e48105045200310320701c07000004008c2c810083c130144291b60141c3e480c104001c0c0188651000c0c1c410903045440c000034080181d60304811544004e40c00704010078a80a00001a60726032004200542601e041004105003060040354503500c66100e08800c0c003440d525140c1c101d940d0300c070403962680940c2c802001800b40b1103a503400e4000500e94494081d00e410108008203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 738873920 1250 738872670 738872681
    0xd06150b031314010b030c010509040605090a0c2a06200c060709080c03060f1509040b040b0c1207080921040f0509042604170a02120f120c010609 64
    0x10040e504152041d48100800c80921002c9020f0041c001c0c811135407403a0000f40c0320b00d101c2c5100f9060002c000361401d05615660001802068020b0400c41541f0313013102c0120203440038004000004025041c91402c0b842d1841c0f1722907100d81d20301190a4070707551a0740c4000c02018880010044503801b40360005100c2a8080245078114100002d00140c1c10f21507405004407115030411b0b007076900040d49a143c10f440c00904140e1117180d1030b0b5003032a1621035410043e003000c0c4101d041134200f591801004144484088076600451240d082c2c000d4550382c070b07000d06c9160701601c0b05010500208401140380c040c031070105a83c102c1440c0d002d07581c040b400104049480c1c202d040b0080344004010400300440d03050b4a04002c024581901c03c01114070b420b5540c610b80c0c2d010220141441d00380045c4180803200d00170241e42c01340c00c1d01000c00c03103101a6002040d40d901c01c5020100d01c030f50303003801c1c590803950301c0403401c0240190450010882485640d25804050b00a845e2001070303503680b010700241204a03030144 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 738875170 1250 738873920 738873931
    0x40602071101050c03120c04030606030c180204180b1809010b0901050603070504060c06090b34050a0c0312110301030203160513021b0a200f0d06150b03 67
    0x16a121401d01e003035510400c071003102505201d81400b0722000c07150701004543c0120308103036010006030b43e110300540c240c2c06242c00c007500d182c1c0340c08804400c000755002030304240d40c0030f5009441c074461207003080340c285d00c42d5000713241400400d021061000179a940ac0225144401410b440a14005800c107200c81d980032600c0c44070a0391a11064900c82c1040a8a18050711095800030f2131407900d003030084c01c184180c0c811841000000044241400700e43d501c4158541c2d800140c40040f82000d040b1007410026244a51104400303400a1910310829440d40001205464031051300f041203034201580e00310045041a01800004021118454440d00c91960322400718004039440c1d5040d80141072400500d0103000140061501c0f00b48842e076a0206140c50781105604096030310504001d460110000c64000d0000600c01c0c03c1b0300c0e900b0840d40340e60401d0302c900101040101da0101800300500000751100f1035402100c1078040a01256450b0850003200c101a039240b504140e48807101e0350b040e0300031101e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 738876420 1250 738875170 738875183
    0xf0d0509010c0f060c11060603031209070314031305010203090108010509070c080c0f0d1d0d0c0b0a0905030c040603110603130506090c010206070e030c121f0f180f2904 74
    0x50300700d909500410116640d0021038000c7c40780d854001c0100350380b48a0100f030101000322050002b214010200888400785a10400c10350010800030031141ea80d400005481100c040b0003440481c1325440002a206641016591907130281d10701410f0000a0402901143c10805200da95402180744107008103024034108000300f40d0700e81071050403424042d408010ba8100011403100b40340080030307121858100c05e400ca074030300030746140762900800381180c0d54041c9660362008261b401070503070404100b40480d04103901750351000141c00104800c80b12079000c018041c032103035000403400c3d0504c1d202442d409000c0b0b40000c020300c412600d0711460410111046001603100d80064143e650381406800e40001307031810b0942d107007070011300040d03254044083e2003030040c110100c11509002041003040c0564402160011f000e82620503c94080d00420311180340700c6090801038044501c0c224891b40f0b10ba6009100c145244030710f55240300d000381c00d4072030302c40500e541f1072a0b5080808078201d105d03028921800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 738877670 1250 738876420 738876431
    0x53102030111030105130506011803050a11030f070605030a0e07150318020a14040f181a1b0d230405010e060123150d0501170f0d0509010c0f06 63
    0x204150030740e180c58480c0001c400d0b050004002c640c650426a49180510010100e400c2e69600012100ba0014034840f00b90b80e091308400005100c2c0c04a45004400c0c040d86001c01c0c03000d0380105055560344007050038039407a8030550040201503c00ca0265800854001000c1401480300075070500d401810b070082c116014112491032403031394041c03182400340d0403000b010440a044580010b82d001d003040c0b0a094001c00400c3c9180c525699507440f10135070401c1c0035410010048198140b464984010800701e81c1008503c49006d0101c1a04201038800c4c012440492422218405026025005074040166554403041c00748440d4803003810030405116891420300d182c1c03070541000b500b52080210b00440320b411000c018000e42018460002d807084003042000210340d0200d011034040500d4000360490401c0200c1d8601d00d52040743c1005041302c1c40311418124060904141a031a50070437411100c256005804040585026101400ea0848141004940c024080e100c41d4400a0040400c40f452903940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 738878920 1250 738877670 738877673
    0xc05090102061317090613090e0c031b0d031418130506011422090903030509120301050114250c080109020105041e170a02030d0e06030403030531 64
    0x401000782c0c0300d00540e000c2e000907086034030f030b04e281c105800032114010700c030001d8060400e0701c40130221201070190030a0030076000e0f40c4603600341c001d111000038001c007801401c410382080c0c6800a481803541e40800246800f581e481000c008035400300700400c0f000d1100d801d40c0750350034808140c09000d00c010680b0030300206240901c10000580728207100c100e601c81c5032605011841c0da02501260000c0350305a40c050783e92426005008100d420303000401440d101d038650100d442c4805401c0030100c5442900c0a000d1134803880441d907207503555480300580008050004000b5503200e20903040c05610b2440c40c2e0340c030709a07140a00b0301e00310a01000c0100c04d00c4511400501300300540c480a00100035540080182c2500f660008010b441140f18041540982c030b5140c09a1103480d100c100020455003800c104100002c1440548410400c0d409901c28003840703400f00c0b00d40e0f018aa40c042c04d01c0c0000e004c0342c9990740701d540c280c000b0032026001d8650601c45d841c031041d0100a018110b12145011850b420134100203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 738880170 1250 738878920 738878923
    0x60b030a0e0c1816090b0306010c050309030708010b040f0c0f0c060f0c0804021516020f0a120308041b120807140f0f0610061e1419030f0905030421060c05090102 71
    0x2001c1c41c1e0400200e80ca08210291b115001e4a80110342440e10090249550900c20f1030350160344402d6034503002c1d2a0340080c105074150306c0000241401e413800c1c8011110b5090103c21074409640c8140880d40c000200c151040c4545400f0380070702e01ca500f001035040c0012112004881d1601107800100701d410052009601d020705904040603085c1c803009150254140320f8074980703003608900030300903040565040380780d55070400410003130900d0340d52203101c0c1c01041c100141002c4090303600b41e8165442d440101e044114240818003a148040300f40c82c050520780d500c4046a91010354160b50900c0004400c0101c060203101240d99095000010000c2c0f0013030450950400f1005030456503600319050007080700642010306580707015041107104a01042c441c400740d4081d41200e4452403121000102d090302c550f009502901102200c7d40c0800c50300b0001d4001200f160002403002d0225442032004000324000c69a83d0707034500d8129120804941c100c2d94410040d10400c1880030301080002c9181481543d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 738881420 1250 738880170 738880201
    0xa0c11150c010b06040e04020112181104050916050d0812090309010f080f070518091612050402030a06021312030504030303050a2003060a08030f04030b100f0b03070c080a0e13060b030a0e0c18 84
    0x40300010745002002800303a079032030042500c40c192c02014000602410311454100b1307214252842c6803801000d140000e90240c483d88083c0401c2c0c003040c0c142101400c060b201f0500288100303260f070881c4860342c8821401ba95590404420003c0304900500d40c400d454641d4080030b40201a0008280120600d0410240010106c0c4069400c4641f034101048013607a0000751401e02183c000a005941d0100840d45043e80d16054000d5107019500d031020340105135010009100b201c1c0a5582008103454250b40c440945406c20780d0410008908884622031072103010086800880090000c2e106941d070f00111402c541050780c5a120654011400300700740445503022503408540d01559461150410191043c2201c450042c05c0e505a400b00029a02e18080e0084038103041d00302c20001d4450b007800c04020025021060101d004800d422210455071131240203180603100c44040960075551120240001004102041c0f04544100d59100c0134986454160360841c041c0c1c80000719082c41c251906030304400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 738882670 1250 738881420 738881431
    0x4060801271b1b0302370311010c0306060e2115100603060303080a09030c0f0b04050706020616050f0d020c030301030c0e0c0a0c11150c010b06040e0402011218110405 73
    0x1a00102210010340d010864840c00b10360441d048a06e2503040c00918220a0310501c001c000c441c80511076001d05400c15408011000308038028818520b03000c5080701079030018420b07000403441b044c58000607071400d100360300384608042461000c58001112445e1905480210100c0504c4182e014002000745c50304805c00944694281448004c4c03071554000c100c0307100107001052465450803400e04152165003800000380e0049078580d0400702d181080c900c003082c180c2d81150307d44a003000c0060322a00100324103208400b94000194000460541503c481d8084001070342c2402d0b00b000a4801a205072000c0d1003140c502c0c400440d100e40c1145030040c0c0301621604207814010301c40e000c00044c1c5c20704004482d188500d524005180c141a031504540d0079901c3c0c1081e503404444640781c0d00960300e0f1040603200c6066003100a11840d0341c840c0610401d882035001e217002c100d5006001401550155003201e07000310803600d00103012144007202c03402e040b500e9002102c42045174412203a092816024664001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 738883920 1250 738882670 738882707
    0xd0608010b01080402010503150d140105130b0a1e15031502030c07020d150e0606040c090515031803070f031d09010905090309090907081204060801271b 67
    0x34001d450010b40b8410b002031009040000000009410315401204200c0c0341d28003510b601078404c0c543c1340443c1c204640b00614000c03503203084000394030380f5403014030078100640000c1068031075192840b4440c060b08004044d1820740c016040e880105000343d1140c1020f54032585200c12a8504520382909004501c100d1000e50500501c24026070114080403500c4890b8100d4852040340b0a92501c541c0f0441c00d04c0318081c0039894142030000c007040214030079100b10070445040014030300c0110299607040c40c5024207500b00b00c0100c041070001d0000801560007800d900b50100800e4540034004d03243da0312902d4211102e0707a00c201c048041541115120320480c850100f40341c2c039800228017184002c00148100b41c1482e40ba0f00c08a247c421061044500e01c0f0b00182803030503940351000704540e4a00d00c6120f10b45407807080c180c0c05041d00c40f2400c1030f10260340d00c0c0c1d80c8801c035503480c11041303a01d5004000060b69230030010708840404058181b08121940c4020750665110040c694405400814440c1c04140c40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 738885170 1250 738883920 738883931
    0x130302031504060c020f0c10030603120306050319150b0a030f05010f11030c1204020616061407020c010f0806010e2707050c070501080a02040f181503020a0e06040f0f020d060801 78
    0x5805000c901000c400d1401e65030030b491123200c1c03102140a446141d00282882c1c4c28040b1b848086641500704100b034602c142e00b15040c4490906080090040281020300042500020004e1a1015400c5550301038401440f00c3d100680382d4403108007105a4240c1210242e54640c2d41170381e480c2e021701600090241d0074004900b50314084a0408140c45000c050030002c08400b000030b02151344d220151401c015140010a451798054540301e03000b48592449941c03001c0c8400b00047c1517902c0050750600c50001a910768100306d51308042a80c02c50310140001e4184103009a030440c05442e40441066605208488403510101841ca00c5095030000362061003000000c0000200b01800040d0320001c5900a190044196076200740140c003d008a0300080c501c0d000b0484001104001081141c000344040401005942c102c2d02902402421030300c002500210190f40c00c212a400201d102a8010006440442c030345d80030780c014004032141200c204a24560100c0d02c003030030504500c03485001c1d1800b4802040f1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 738886420 1250 738885170 738885193
    0x181803050f070303060b040920070206040e041104323105030c010b1005031b1c050709060f11060a051305060112030806040510030305130302031504060c02 68
    0x19105a21400781101d00c0011210100f40c0300380c0c8240000c2403c0c40d4016151074803407034005c021300074103828591000301d49580008588030b068101c80059030300070100f0f0300d49407510840c680c200d00024415503080d8180c541185030307030701d40d801040c8511038001c1842044154209050002210004956445a01f2902005401040c0b103000d5080040d10381103a0f10007078503901c0b4105d0000b0818800615074040821000c1c4d80071415048039103152000c03900203c5c0003041c1001144c0c0303400212a810015812010802030504c070340802008003080c4501c11010440c030705d0120700305482d0700b80c1e04040019403e400411801c1d6000d5281210702c071301031130085003482211121070341e17800001d031100c2c108643d01d1010410b09c0c04698460940f0f95032000603902e080da905c810385659500f50351026404101d0320000201c1e0381c981445810f00c280d14054042400e1415034a08840f00d03001b0501d82a11403140c2080440903a500300550141d47c5540c288102e071500d8030f071604605464080d621078040d036015644604 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 738887670 1250 738886420 738886427
    0x70803160b01240e0d0c080a26040b090f060c060f070513170c09040312050601030c080a24030c17030903061b041d06120d0903111801181803 62
    0x80c0f0325051407800300100c60140c000140143c0c0005001490141001000203864401082d0024120f01458000000d0307c440c290080c800ca415002c0729045500c104014400d04511030054091100050b10307040e03449190501052071944007201c48100c96200c5010403c0d03143c075528120f035010009251840c1020604000c1160502943c0035a02a502603000d01c0c002c0303a1010800c0c810500310081c111001d500b014100507050711031585d0b008241500704000034010303500030f005c2c245e00145240e8800645a84108031400107004404250b403000340400c040c50207c6034050310300c5020354081d036980c5500c5c0345080c1e0070710f440703008140c8100301640090012028a27640810b49a60081501d02c8030300d009030500c6540c080c0b6200b80d8020700500504088601580900c082c000ca108110640e4020203542c03201d50070320b80c1da48030084080d0000341521801e00000d207520301201c414003c01b900c004ea00d00201510102500703406d801c4403441000c4201c80d244055031b80d02540451004260300c061103c0c0041d02c009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 738888920 1250 738887670 738887729
    0x705090c13050406051309080d1404050f15040308070c06150503070512071701090203060a091a1006030c0509034303020904052410080102030c0d090302070803160b01 73
    0x19441c2c5503200e0810007230100c500102c8405101162003001040c8200c1c014401b1220f00f80d030700781c03420312417250410340c070f0100041c2501401003000041b400e0799850707540461b03507580001c14000130000216440c0001803014090780614404550650803020305120a043c54548182c0c032191082c0702c0d22050005d55103000c1845001e82e589550314451000c05881c0017070140400c4440250144104030401c00206916404001e41a1251000342d060f219200c1010209007810f80300c40040e22000803040000c90301a500000544483c0c0c14400d003040c003840002800c02c40c4a2100411010000e40309690700e100c408115504c215290303c43c0038030007040e00e1135000c180900340030081c06641840007180501c9001c010b50311b0701c445900d08040703141c1c0110b950707980024803da619508824100202160428060083d00d22071011040d055007010070148405015110003034098096000b0b07420301081c60720007407004100f5403071444803021010141c4c0c0751080040d44140d12025100d81c4000700302c0a407184c40b040c032 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 738890170 1250 738888920 738888949
    0x71b0c090203090703140a0204050c090a051903080c0106170a050a030e0d02220513050a0b071e05040609050a03023f0f01050a060509070309050705090c1305040605 72
    0x1a103d0740c0e5603800328a045801c2c1c00c050020825a0101c00d110000000c0e40040d0900c207031001c0c0125221460541954011120304560102804d00706100c54100300c1c00d8801c100481d041500445540c90300c5250302980a004144a81d03512030405000000390394003460b80403c0c1e80c0c002000805c82d0750721000e8072003081d0307a001002c00400d08844000b0707950f1202104109034004048a05080e0001c1100c1070b2440800141c0035024100000a2140d42c1586486c2643c41e070403101506410440395a1036030b00c5d1500612080a01c40c1900600f02e4007180c02001504840d000c0d241c43c2d58403410800301800440850780500d1140301c1d00c000900040c0ca9000704d141c2094810800544407485100c40d0080b40000046c00d144442c40c1080c0403001031400040c03000c0c40b24100700081100e0340b00c00501d001680c205018464015803000086581e05100c4e60045503024065410758060903107034800614050b4040e542d02cad001c0d15012680b803c04a8820f21021300410048808204e118600404203031342c0b0b8060f00780c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 738891420 1250 738890170 738890189
    0x30c19092a030e0105060a053003130305100507050f090d06020a020a0b0108030703020a020d1104090305030702301e030c0301031b03051f0e07080303071b0c 69
    0x14111140860407403855051034071084074003420581440010014221150b410480c0c2d0300340b0700442d900f8209549018182c4102420031801e00c8440308011601511504001e50109080301500091400034805804104d482c1c000d01c912651960030114908501501e9014006190400b4000000e07003250840d010f41e021a00703c0303038880d00d414001400030859150301910540c0005955801c059001c6801242d16104590204e000d903203440c00790b6a40d00400c0070090144e0f1040c201c05000d490078070300881501c1e1149801044060311400460155003803440102c01250f0040140401e0b01d8050050001900801c000b040d00f945000d590b10303d0f8519840085c402824000449011032100c0310b8490701d103421301e0311000d1307030340d00303114a00c411290300910094660704055103416041c0302c510140c03001240c1d003080040c45d50902440d0f030014401c54501e18000841c1c1e41e0300c04011224400e01000d0010a48080510785030310300540090088001e007401820100c0018020000140c0d034024001c0c1518544003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 738892670 1250 738891420 738891431
    0x180c070210110105010801020d1d0a030318140106060e01020309030601261c02070501080f07081005030a11030d170c1b1006081506010e041509090809030c1909 70
    0x20784104450b00610031043d4201030002c0b8406905400400040764403100c00c00c102411128111101c00c8080c1e00990140c11015102011900c0780e04503c072002211a200105080e2941c0c2e002c0c152080401e800d2110b945079941004074580115216031900c5007070001d580f5100c81c601c00a42c84640501a070311045a043c580c0f03c1c40409600600c05100f0f40010444c2e88640c90700380c40f0180c146000c001c010040c4a07611000ca569449100710302d0003068001c20b0f42c81c55482e401002c2c0c803080c5006168148124a4410001c2d00303560403c4081e034003d005000c6800103080700f17820b0504000a21000500f408600d1148000c0f461006007410b5100d008903410544076911554800c000c0911102101003522881407091800c1c5440d5000b0350807200360008039514000e1001c010100c041040342e145000c07845881600705607040c5030708501d0080350703440510307c0c049841f081c51000321511650190342d1400c0218030950681020007009141c2e0031700711958611444034100c00070000220b40280041284c450 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 738893920 1250 738892670 738892699
    0xd1b060c050c010f0501051309080d0e0a1203021201140d021e0d03020304090e07060503040f0f020604120501060e0615130812031f0b0f0a02030706020708030105180c0702 75
    0x10802d44026020000080c401801000c0009000e01802c1c0201881202c404203030101c400c400d8418655020352081c0c20a00301311108484030001c01d4641064100d0740a60f181200000701c0602d00141d02800c00c3c2c41c0180c03200040b01c4140c12540303058201da011940c3e1070404002d04c0c0d035555100c240155046401842030600c050309262041c034940e1040b6000300c86074055004154000c4060001e0740c44044c000c2091074040961260ba51960b84108404241c08001150120308501340d082074803802240d10351a0300d803142d4003246040c1e202d5484841c0303d40c1402500420054280241401000c0c04091b00c862424038200140c6100546000c2c0c0030b490320001562910031400684040051442c0400d4500c082d00f11050364103154004c6402e80c0070181200c001098606400041301c0c107032094008128144103c4001140e810350003a91481c0030b42c4018409440000c2c1c81e40001e21125200d814081d8503035141030184050441c8480801031200d52200410041c120080c1c141c0f0b000742d80448000d441004c10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 738895170 1250 738893920 738893927
    0xd02091306090b01150f0203090a0e1e090706021b0312220b180d0b04020402250c0801060812030a05180f060714090612090319030b030d1b060c 63
    0x40b040042c400010b9000000d03a6403d80140780240315042e44640c5c00c4040182812600c0e80b10744020507502101d40704043c015100444071845d8080b018440c141101c0c030b84c030001c034071540c034049801090075409000d003030010650500107900f40060b101041407031112840002603e5010420b6141140e86c404260561040304030759012001d540249519030542e600c038400b079401d6038003200008888260141058440c1e040003c503075100c0c16000b0341a040c9640740d50b420800030754000049410044a00a14014000c4030b41100b040c0c0700b07100764a1080042d240400039030030341d0030940c003441c29a0000400c1029000a40d402caa602c004001d10000780d43d40d5600361011001d402505101c0725200300c80300114a503000084a80c01501c0c00e0302d4644950000d255922041e200b01000960800403d00440707000004151603580c0000345075003600d052800000c50851701c0d49401c0da43c5000661103040a030854101484955045076070b900d00482148562280c0803c00f80004500803c810360b607080c401d455920 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 738896420 1250 738895170 738895181
    0x11a2a070f06090311060c1c03020c0708100509030a0c060e011103010e09010b030f1005040611030f04060609020403110607022b0c0503030a08041e080403060c030b0d02091306 77
    0x1000e21800d046107850703102c010003640302c6000442e0544050050201a0700d0001c2c1030b29600000d1000401e0510305843c444540c0780b10000600c8203164080c41900f00b007450501c8601c01a1680000806000d02184a04001e4500190000c1e42c150000c011050041f5400100280304035000400440c0c40f0502d8101030f401020214100381440601000101c1ca1110140400b4007902c0844003d02070000310804050300d4464004c0c070780701d1692000c2d0320b05540103c1c0c0d801c21a402400360800056044001112040d03607441291210140090f0000300800c100a030310406002c1d00d5010030850405007980d44000da069007591b0140d00c689800b0440c40d0841d81d5400340d00303c1c0e090742e000591007102c050103d882040e4695800c11a00c4a40003440820386090000903261841440d40e01da501c540c8a649450b04400712048000349501808146000802e034032000410045116010012707082150131002405c80b160800894401c004802c4840c000d80e4401221300d070081300390b40d004203102d22203142c41c100901 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 738897670 1250 738896420 738896429
    0x19140603090703060510090c17220501180b01060305070c0204050a020c0a03261b0307020a05030a050a0306171f06090e010504031412011505120f011a2a07 68
    0x3405c100030000d0303d01c10102d002080301c0c0703812400e006400c119001590031031040d10361048010241e00005000c0c2000000c400c00c510440315a200c500308107a125a0b0039103840a80044204101e442c43c0d1003000150703050503004010621b005c0200e0708001000800c0c1c3d09020401920560302d030030204400b84500e5040f1a442ca2503402124010811841c0c060201c4005920018103822000407100c0c030b00400103940740c4a000107115005070f668000c128a0342ca500090310070f80442c419001490b00058003080100144c0c110790b00c850340c585100001c014162002c035000a010140c0310408882c01c00ba001500c040d41003100301d8070600103114408210020845944200501410315508807142441948801c0c0a00e0082d07440c400c106040a0703601c0004d12941c0010f81c0030400490040141c5683c50051201d403600134a005450242900c502d0480f0000a88000c60314601c44401002090f160110b864803804058504600f04642c0c25006101a050691f000d20390200c0b512040f0402d20b0140002c00291 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 738898920 1250 738897670 738897683
    0x2d0303050711100207030501050c1c0e030f030106030b04050105120a23030a08040b010608160e0d020a08030909091b1e0301060b1305060f040b090d02030601120219140603090703 78
    0x10001040005d43c1d0320f031140300a0381d0551800001c20303003c02c248801c0f1075400742404072441c2c0300f880d0190a1030041041c0e24a103c00b5000900c1500c06403007480004500901e950b41e00818180c400d041004219881a4803051244007502d21000081c0d1000c00c401d800d4a401903880b40c1c1e81c00318100000560444290040040c2c040064030a9005404c0140781d070140d801041701c0300030b0b6a00c1d024241c40d04002a518401d00001220b0795025a901c81c0c4400031000324090261182c243d0a64042420030010341c0001003141c202040a003114240701c0703451940072150200a010108548444059046501510b1405850034402e803000011000e4582e69103590041c1c020848943e440340c1c0044d06800190400e10018248000000c8900d42001078400c2000100d402d1032519203800a5036890341d008008094205910000041c0580c2c0d080c85018020b0801d110740c42a42400303881004100e524071600d425000100700f00601c0460304510074141c07416001e650540e540c0d2101d0030304520302034803640b004040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 738900170 1250 738898920 738898939
    0x91b0a0e25050c0c03060c0909150d03110c040b0603130302010603080304050a03140408060a021b0f07060e04020403080306040b010c12090509090105040b16272d0303050711 76
    0x10164000000d0210000783e90070b440c2c0381c0c02c08508040c1c4412080d505543d84560078040e080322450550b1000d908a000c1d102101c01c5c520031140032607110b00c50700300140e021440301650821442e00610065480003004c5404000443e1840002002d901000d41694402030f03003000c01d81c0c02c040c000d6025102a5410503101503d924051a000b42d0b1054515000c400003070040300a6090810820140c4081d42d050300050603190707441480d544000c1d00581c0d400724100c0b8a09a0200c1012414000b0003411001c20300602401e5061071806089018480d001c41c0c01548100001c00202d000c0d4400e07030350404022140814101c00f8000120784100c034050003d0242c01540032139404e001e400c005c243d01102c4c0c040d9001c651603a1003029690803a4002c5030b020309813201d02000600310320860740b620101c1141c0d90905009078448501800300c0b070f8415039951402103458030001e100e1107410080c5402e42c503250003e0350841d07000d43d00a10302c000e0303424400182404000720300d00d000c01804641c0340039074006c06404602e5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 738901420 1250 738900170 738900241
    0x6110714010e04151d09102a110106062c010309150209130e0618030417010b0f060703050711040204031220061e0604060305070e091b0a0e 61
    0x500740c0151240e800c0c041c404c01c401942d41036008176218402c82e909809401100002d64541c0c2c041d007010300b294001001030031204043c81d45502415000010b007a500c01c1d64010f0802c01d81421249650012030600000600100c829007041c10121100c40340144c110b03109042c03400069014003141d5900624030366418140c00c8100f104c55000e00b0048004a602400e181020f481c80c00403121440a00d0042d9040000001d903c3d9940440b0070b5550000c07101140d14090340e408508108682c80b07094445165114034100c425442c10805600d40440c04031042c525145013660f002e48a032166140082400001521480e400d5036580d060701c00a64002404084405000000070b003008511001c3c800454540d0502c07600001c00011580c1c8124a605030341e5888000301e10641a4107031000b48210f50094840102100050081c482c100c003c00c451409481e2074100035011a0900c03009036210007000008942d00440c0d0340d91400e402045441c03600d008102d98854122411996010140490058240944510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 738902670 1250 738901420 738901451
    0x41a09030a050a1a070503150f03060a0b04060b0a0f081513020309060a1104170115080f070605071a040201031b050318030f07030e0a1a04050a06110714010e04 70
    0x5891113100c0d110303201d4510108002e05400c2c107581000010b42c050000604070b43c1d00b07020000d00448003c0c0a18032400d68400000d29215045406201854559400d100307141418040c0d98090007003040c026080002e1040000c02800481c400241004aa8000300311500b000000035401050003820310610100d0100c1180040d510a4507945800e124071000222020350324407414840c0340c180a0200c0c44c03d0f192540a2900c01560400c01655541e04c500c02c418601503403655000601440002e401c4803c1d107a0480c0b07083c802158008020b1001c2000424006403600f03111501ca4080141420141d45070cd00048000f405100f016a4110310000144c0a4103904840594424041c0c0c04c1c241c8183d2012049254032030080300014840c4035001e124000003c2e0281788003103580c01e005081c9040082d607442d10641401401c100c0c0e2108544002814011420400303039480142106040c50100007010180d1580d44501da0304c1105001c445044d99051260303c1510102d641c1d0400030310501002001d019140d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 738903920 1250 738902670 738902683
    0x7030c120c030e04021c200c0c01090b0f0406081e0915060a05010e04020a030e030409020d15030b041410020f0d0606080601270b07030e24041a09030a05 67
    0x150b001c5410b00a0440756071a1030b00865120a41802844001e031300c0d42003040d0040c02d4603c0c0031000d0f5a80301c1c2c07000d000001c1d000c80603141c00a5030000407c2822003040024001d510b203078121200b44801080b031200e070001d50702c003228121803052070000b003107a9404410910340c0300c15030034100300c008040d024403c2040000a00c840360f801c1c4c4510b40d15480d00c5a40410286003080d1144901245114010807402c0c074040c0e000d06000d82e01800c0c04160280b00300300c224119481a00180c02c0360ba400324200215130719611070031080081e422840440035045464051070b1030700c024401041d95043c0070711005040e20901011004904128056482d0040d18003211a0358100303441e002c40f002e2400c030380001c090b0700c1401c4150040d00f06846842102c54a8000107030f080786e5081d03008440c10080c00d40021500d94040092103600d000707a5459005202c200100410041c0c440310110700d01c0b0010203a03103c451004011034085895038004001c48044000e1703038a551b402011056503050040c0e01c0e200007400b0f07010440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 738905170 1250 738903920 738903923
    0x1b160b060f030601180e0a02040c0c060f0908070206030a0f050a0c0206090109120f0915031e110d0e0a0b01060e18010b0d2d061a0c1207030c120c 64
    0x108400901d030414140d480c1000d01c96400c001d07080d00948114603406902011501c460801038801140c043e8000c2026503ca070302500001614455465050100910540100300c021075800d00000c800da88521146000c0d5560180c8115070000114420600c0340c0e22007040d10700c1040c418041c901e807400c40b1ba0010481c0c4034024002d03000f444009448404180b00740d50720f00c7d6000d00804101254107000b254041d02e55403090082c02242400403480001e00e00300c16010f81c0c0c1680d0003140903905030340700b405694984290428182c1c101000603813001210420b890380502500400101c4c0c0c00b5008002d46002140343c1c0c00b526444242001040455110f00c1d003180e00c0c02d043e42c01c0c1042141802003d440340c1d10910650302040e1080c0007945100210b42c0051146042e12211440c20740800c1c0400813401c4a442c4c1e95a900b80d03070314070080007031400d0003000400140032100407e0509240c1281c040d100d0265102c00f40c810840004e504041600810b940b00070940c203d8650744090b6002440501140c192010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 738906420 1250 738905170 738905179
    0x120f01060603020903060f040f080c030a200601061218061a0904171c0f0b03101505281d01140f0d050f1b1302030402091b160b06 57
    0x2001c100c07507009000b1101e03201009002403007103a886039140f01e4103001c09401100c1d20b60506103070102083c4800c02074038103909003030b0155540d09800f800180841e042c58000c40900742d9800c030800128840860001e04540c2142001080c00c0d190203180d00040c002c200d0014906007641d0095010b00c051603106c55052010b405519a0200308202000000a01180c006012101c00d40d0301c0c5160448110151218041d22840c1201d5402281d00c3c43c81500c100b651010003847e550341c0f1031520f6250402c030030003076403070405007c004a08407000724220051050213018083c802c5224030104040400894a030301c40044201104c00301d44a45010356100601410548264401e07400400c0302250054480f020010041640b58520400001e00215103040d0a0589403409001d0031541e0307044043c05003441072584d00302d20020303400c500700c100041078044402c554003880c03043c004c010041c0c464503c4141c004400f081e924a01244402107554684103d0b8100c3c0c02c0d1002c3d00d2111170030801c8aa41440c0901011903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 738907670 1250 738906420 738906431
    0x80d0315050301141e0408071202150106020c03101e050c04030606061d03030405101d090c0a0801080f060718030c0308031801050615090307151812020609010815120f01 74
    0x7004205c200400b0756000c1c01c440c4040040c9000980d03a81e01e16011400d060043d2201e0b02192101202521000d911000140e00680c0415051385018021422040c0040208001202031800b60310304005210b010080610390350340200d044800300d06c082d68011688680c0500410741c0702c883c018665030b00b1103108605480302400e00022841d012041c0d07029210042d0031008102c120710400c513440c80c030164000400340c0c000102c004079900c85100c3c0d00d218585051482d541c0f041b40c100010068081640700c04000d0300034103030b0508003030000300d103c80c1c2204451400ca6051003aa402180002c4001d90000b08100ca40c1c141c00801c04c00c8d038070091413040154400c0c00320a503503104510360994200700c07030007a4008008599a4076510300c010150180d00f00250844031069154180d900a180800b8616000700b52008440048400e2402003100a00b001c50320304100702c00c02c1d6000c1400740c0241e0240a050041d42e00c001074103c0350205104113007030001484034500b000e1907070485403211100c002d03940d06542444c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 738908920 1250 738907670 738907711
    0xf05030c0f210702090c0714250e06060309030c0615040f0504030c03180b040e041b0f0501080a140a06030506060a0509011e0b070309081501080d031505030114 70
    0x2d600d00c41c0070740510401407038009030b0303400c00145c5d0b80020b040c0c6201603401d014842c041500880d9441c000c90704c4000400a000303025821200d861041c500c6400c011724541c07014480d0000354100203070081001d5902d151a9181c2003a40d60640c010082448005c2c0b140004003c1caa642c80b0746400300281068408000918418520900b40c400071107000e004500242d08030000244034510840521080001900b1182c0e200c0341d5240c45644030364415440e503601101400305101c41c50f0f00304401c0c2c05552001407401840d00c554465159941c1c85610b050280b02d81c0041c3c80000160464124802814004500f520707281881d100100828042591588142d00000b03406080a44007001a03503002445401e043e8604860340c0390303054107060b40c5508003d055600103910b0b417078003010b40140e41c420340b6440c00300350500c4086850102c4101000d410390041c00010020b1400109000744020030070721700854600316502d100586a0000e03030242d50150310348544080000c0300031040b1802080241041c1381c200e141c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 738910170 1250 738908920 738908953
    0x3080606190e120109050c040510030b0711010207021c170306031f1b0c110105030402010f1b1506030b10030201170405010b150405032a04090f05030c0f 67
    0x40400507051025100c1c1c1a04065015840070080a00010648880480c80c40d4801d400e41c0c8440c801140ca5030300c160442e40407071626004182d0300080c5846070720035031491600ca002220034040c2c0070001f481101c0341882030841080d01101d02c000c0d005001e0102a04242c040c000c008a440402601c6000507603940e51083d05130740049901a860081c0180b00d51684001c99164411810030705450035681c405003080c0c0203109581c052030001c1d072600c400c0c10541c2d581c186441d8010040600030704002d010803c000040c2e800151095a1051030701c2d02042410204001d030004c0c0c084100f000d0b241d10000015a900d010b001e400141c00ea0b40b103503040310041d44402000c05021895400001d011076411004a03e00f4030038061200e5100e40141d0022030804044401308907144070307800d114040400001030501c01814100554140c1c441c00720841c000c004680302281c052030001c10310391840b50341c54552a20038000325003442d1601c1134004040d2a0f841c00008805070341d803402c2460144007401801c5520381040b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 738911420 1250 738910170 738910177
    0xc07030309050910061409010507120504080f010b031533010e010c1703040c1e1409151306081213171005191505041505061803150f010303080606 64
    0x40c02d40b00e01064484c40e8030b02c890b40b40c111f8005030781004000d104110206d111080c41c9210701d0b40c241c4441c2e83e42d908000c030040c102854190341801580c140342c1040b031251000104600c0103030350b56680001607213400004100e1480d50740d14500d041c07111030311030720f403804d040d080b00d0b10600c4000d80340c014020a04c0350040d140b50841d444060302101c92051540d1241382034400039640284101c0444400a4550b01800d014140b00c0410b07140e000203a403000c1c016802844100c40031004c08903141403480c64905001c042003860b20100500821400040542e00403894000740e01400d0b189054810744072001d200c0384500e8102c1e980641400006101c006183c99409241c811107080c4007010b090302d402481c042c40d0140074040c04903458550f0461000c1c4240000c0d101e0310003108034692520302160f20f0442080b06984001180807035010b24005c04101a55030003080b501302c1e8044a080c040360804ac1c000180c1089030440070030100071007010400c030355049800400c506aa1090310383c6141900e07140d080c40781c50300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 738912670 1250 738911420 738911429
    0xa060902120709171c020c09090c0306010b1911070b0a0804020310050f04060203070216060206070f020309060403030309081b0307050709020a050a0e031e0d08011a07020607080c07030309050910 85
    0x104480c5074440845140c40d44101c400a1750b0044401c8a02d4000100782148000c0b01d1000311500903158a4038203150900056004103459060746040c00c081c4041404070007250b00300c6109008100c41e102030342c40401d010350801820b280921a40302ca8200382c000d4108841150100d10a000d0514465a6280346210316030241e5a4134001701159034582c0d40c2d0a0007544047c02314015446480f40e0b8400103490b141c02e05c0090300e41a8060815400d001130080d0803011054000400e540003481a00d21907164003069400312a05450082091281e508260386103114840359415043d0080f020000400c0000000700483c80c415400c42c0c4410f656003040404900401c4200c0340082c0081109085a0f0300c81c0700003404200d00201034802d4980c40344501c9410344450162202140c11003220400035a400c6a052801010621840d1172400034035140d4900b54401c01400a10400d00482c1c0351051180c00001d45450a01c80400c42d56a02e0301c134180607200e1452032144500c5a000303440003e003a00074003203250741107a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 738913920 1250 738912670 738912673
    0x4060807060c02060d0f1d0c0901050319060e010f020c0d0801030b160e030607120b010819181202060105040b0d05070b0d020702041406180903090103050a06090212070917 75
    0x454a5070030004660301085d000e210540c0c4400b20001c0700c3d01d8174030520900d2420f00301401d2a00c012403003c51b0400a03004005445560150010013650720f020071160640a0003030704c0e01103205154a0038500821603107a03601125840d003102801e2545241d4028440000e41100311240c08030511000c49107200709010041000c8002c0300402d03042010031440800600311802d0007641c091000d00407074600907046980707400146c486910b00c0d103082024410f007080c86400b031a0118983c50071030302c905221901c0c10581c6078000d503154440c403001c0c503114140e100e00662090320920040c0c00500020354804082c0502407040e4a4024084a145006850043c0c226030210141c800285012260919038100d459505007441c0c08000b000c0041e40c883c4941504440341e05c80c1601d1500b0b002e4188400c0041000202c00441c0e080070a10081c8000002036a00c05942403034040b8040c1e440f0650b11020380501d6100c0190309001040402c6450048036200b0b220348200c0d070301e07121616a103100350b42c580700c003c1d95041802d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 738915170 1250 738913920 738913937
    0x408070e01121b05060a21090b0c16170409060f03050c0d0c0504110d050105040903091512090506160e0616111815100f0c020315090c0406080706 64
    0x40748400d03043c00030484100c1c40301c0d6080c1c3d2480070464a9100d50b10076000541004460291000304818451619041003003c0224403030030782c1d49240142c0007a1246c0711925020402d040440c18011591108907405100a50317181c185145076a01134125000326900c1030b06055003c01c0c105c3c0c01490380c00403a0f03081401000c40c0a03403003081c050400c000003002d1703400201d44000031030b0540b518000d10360107074074042e05190f580d901140c0c48012280181c02980c4900d003003503030001c046a8040102e409a41070400540306508100300290794251100d05525021400d0407d6403003404000320304a84190119400b031500140381041c210b80b04040107064a0b0f0200d03050024203000e5010700c130840031042c40790008241c05116000056504c0000741c032541801003408007003240040140742901080c0c034040d20114210b9081c8807010b41111100f0101c90204010b006500d004c1d990100001002d0581c249010025400d02d00121500c07a40ea10300814040c0f030418800007030035140010040300b2611165509901d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 738916420 1250 738915170 738915173
    0x60506030604081902160602070e090c0108010b0c1507090303030b0910060e010306031e0c0609120602030601020a02120615120c060c34050402090f041805120408070e0112 75
    0x113403c010b20014421071055440354000001e0401c0021701500c250b400a00072986407000710301d030250b0000c2c40445260843d0201203140d90300f011405055400c041354242d101e8540100d810320701111640325800241c5020144091182c1114038103090720301039942444200703c10000d10000721416522030103180c20b035000070410240300b4102e00310030309414076020510030358a80301c038800c8014104940002c41e0041d68a101001004881c6400901d00b90602c00b4045240c1000301c490b24080e41b0015009640000c005601c603842440b100c0c0d10039034014400c1c0c0381d44069440d004c0d40e5401c21500180e00254002800c842c0c0d24082a500d0500401e0000400d594451541481402d07085450f80035440e00ca0320441c852030008240a810054004180040110001103803802c00003009600c480d004610401c0b584050f038580b809000e038034050545000c075000000e084091080807070280c01a101303005034080b108040d00480f0041003212050303003c454a10340c455030203404d911000e2041c7c10328507184203410310 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 738917670 1250 738916420 738916447
    0x1306051204060e0c06030a02281b080d050901090b06060f0301030f05070b21060f032505041e0e0f0a030c08120112031205090a020603150301021606050603060408 71
    0x440020300f841510f040300e101c807012aa0a41068684100150300800d42030a04400039400e02c20002105400365070b0403000b030f8805825004145c07558802001c0302c034010414000b51008452880408900c00c021170b141c200c5a160091450b107008403016404500401c0080c54108192180c0a03000b81905203184d10319541c000e8801100036089505004541d1300085c00d0181e80082d1072070085000850011541c101d0702c4541100300105024401e4014003103e031160303180040d00040f544402c035500b820301109011075200d00341890380569880b50500e0680385025a0a184001210340444414016040803812141d01c034889510040c0480d030055541e80d003c80d118006c0c40f0070340ca008035012131600322141805141000260020600200021070040070168444290041000c0d5014200000c0c104801010b440c0c0e440250068401c01020012984074540688400318090004000710354800308020001c107090040f803000d031515860280001e0b0729050225459100d2544403e0941c41c1c020040041e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 738918920 1250 738917670 738917681
    0x9020901051206130212040309051f0e01120204140a0504020f030402061620031e0c13060b07060b01080115050d1a030708060a0f06050603010605070f0b0c130605120406 74
    0x19074451314500002c402d85509100400e036101c050744408000d440d0070305010f451620315902081c041c2002e540d081d541414000340c481a000c80c54909800041c4152004a402c845005c1c0e1019606e0f200250002e140f240181443c411000d05842e2a604142ea48080000302c2c000d11300c0308031001204100150040c03500700000c1550a20f00c007030a848030109912000018043e5001e12813010208203c0c41c0483d14007005030075820701880411501c44d1720081c54594607142e0440c0d115006440d600c0d5050f0050300316411100207802040d00c1c4c191120a01d0034a400900185507240d404a842c0c0c2d400815012105810a110485240c64440c03915804142c0e410041c00104214a44031400120080701030780c2c01d101034001003e6400052446040c00c00c3c1000445c0c078241c6500405600d030400410080e194802617030b044a00c603052494544003281007010040c181e103400145180c50a60400c5840414807014060800249008900700c0752202c80c155414451a02d00120f00c1e01c00200040007d000c58103e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 738920170 1250 738918920 738918931
    0x5090102030f0f07110316090e030409020f03010603270f0f020d0f0201030b0d020d020f0604030507060c03020c010906080a0510170f1522050316150501090209010512 73
    0x40740d1404800395000302998016030704038580c0440c0018214140b2110061810380100218094220394507041301c0544101503a00c18031802a072116200f248030601030003500d0040c180140709559600200e64160070a07402401a0808a41340c64640340380710301c0c03a44011300781030007000010164507242d40710300c40c1440800300c1c203d5100a00d604500c0041c0c84009403800303100d1086800c040c4401c4588005419103040300035182c0564040505480540c0d038015460010f81c1e01920702919032110361000ca0003501c00c940014102d846404400100c00d0761100c008840d0f18025801e480c880f0060780d004441c008018410400040c3e17411780800c90700c110031b62040380c00030840000b41c000e07283d5030b52944c00480050154019260800800102c183d10140402d46c03c22807002511410b80c98068080e89002001c1d000c0c0c18018204e90304d0f40d00c01c000c010421075084c14484650050074a125241c40044080580e4064032064180000010968040d0007a141c51110503100c1ca820499111451401800300504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 738921420 1250 738920170 738920173
    0x1410030f0b060c0d0306061409120109020603090a290703020a020a02120a1407030b07120225061d0d0c0507212d06020309150f0702011808090105090102 67
    0x800c05070540c0c44100404004440f0009000b49541031040a4125080313036014900b80300041103540000d44070032046078a609000ca455050360342d102c1030f0150041045e844001d40140c800414441142d00c0050f610b58a030b4403801b20f4000c10040c0013201d4040011040c210780c459116140403809860281d00a42040781c2b40e441290181c072303803903000503c810390b51079014023858025041c4541444580000d4150480e85207008141d480d00e59034656001783d00043c420b001704003008009072520405c0e42c04807181e079054034242032190300c0920400700000070810f0701115004d19110003010105400406440000005805000b81055100c1c080d9014040d5500440e2140030304c400201d03446100480404900d075580004040b005140d142030000156070101c1140d0640c6030707101c841141070a04500b0702005034012009078031b0fa290820a43e00c1e01c03882010104404a00348100500c91031010007092007a0082d50003803285a81440c0c600e51a04450b48c0c000c2d00c070307850401c1042019405075000701917195042c030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 738922670 1250 738921420 738921431
    0xc0b032401080103200a030c06140f040e0c0409020307020d0f030c02060720070e0105040c1d04020918070f0323040228081c1d0f040b0d0510061410030f 67
    0x400190030000c0340d80084840884190050000d160710010801e400e040c00030244e17103408540000c412603030180d4400c0c0c400005100c130000302d510031480f0653f0001c010380c20043d03441b420711450107911a001c4003000f50020703e5250124408611034007442441c000c0980103040c044d211803508440c400d2199203141c034400c210b007010602c01c44041090400502001d15054900d50410042200341ca8220b03145008002d40b40c850900c1c44001c1140304003080c8811034005913035070f1403174010500406031004140d090080400c00c0080464000e642070b0700e8641980c1d410440c058480d0110f604400a0440000c68100050001401400c1491074034004603001c08001941d1411f0142194644045400124142d00701c00b04141c040d2900e011000da9091980c14072410f007003060590240028034841406100c1c40c401102080d00d40c80f103a0100e02c0700800036120141507840f074100241d6440c0b99406902040340f92880008100000c0c0d04407500240380100260f803503106500f8110098018036208040c40e030b81c1c40f0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 738923920 1250 738922670 738922733
    0x60a0c1410050103020a080f06010e071704110f0a0b040537030b0906190c03090204020a0e091302010c0b150307260604121b0c0b032401080103 63
    0xc21010244032078003900401c50f03604520500c440000e141d8011150703980090f1500b903c400c004103c480c1901ca00240c0007006546079013007141d15800b40710030004004003210500c014040c1403960941010000c0d10080011801201800594201407003000f2000000b80402d201074500b002c908800010450700d2990204c4111603450000c61101c03103e500b1000003100b0810400c120980501da2003480000074080030315000059800c1107281c101c00301502540c5400c65038465000350f014000e5140c019204544072400c0c40380150000034036003c42481110b40d000043d8003000c00008581003141e06131744500a2071042d41d03c0040110001c1c04c0f0044580e04034415040e01d0b02c0070440700e0010300c1c5121a1402211030344100c2440140603180b005030390340001c03003013101144800d641d20ba10280e09203040003045208e81440e400340b0844041c014030509051740b0010382c0d026424055802500c109542100c464040c082000070300404070161800710300c007040104041400c3d0611725144c29440304e5001c4460b60308 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 738925170 1250 738923920 738923923
    0x210810062f0f01050106020d02011b110307170310050301050103050a020108060a1d0a0b0108040b0429131703100312030e030c0d02010b0105091f030204030c03060227060a0c14 77
    0x5081c0e10035074030fa56800c01004510760400c01060441e98600003001031082154000d11007205101e0300368148444004142c036880001c10896901c2c0750045158901424001d00503501c0e98020785207402d02c0f0401003408500b034501031145604072a030000043c06030408950041d03441e280f000340b0040c1e01411040c8005228404a13564445200e5031720788481c1c442c58003110880840713440b000c190303040200c2c2404101c002240d00e002550020380000307815240c0c15404940102180391010f14140b143e403100c0c1880005a196086d480c2d085210786183d18a034082c0080e001c0c0680000c454418216010750000c00114100058540801000346004118400c3c0c000d0036a00d1940566030b80c005a60111403030b1005168288a4458078500918225140540c107400195211000e0220040e02c10300c01a2180c0d2618001e90403034004540c80f001e06503840790b40e03050000003504071403040c1d00c1001c005400d030421121346584030105500020009401e0038107031074040311400e060f00000c58084480b0441110346140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 738926420 1250 738925170 738925183
    0xb0a031203060303141804090c1a042c0a0f0f18020a090c0c110f0307060504030b0a0b10080402280617060a030f030c210810062f 57
    0x1416140802e0040c0340d8500142015681d1903140c03501170003846002e48451000101c4e40021404031000b1580e501c1505103034001001f1580600c070031484041c2003100307030040100076000712084004040790294030320050301c420506007410000f00c008a000081c0700c1035040e512020024030f8000c1c00262540401e012003003241d00d410a0055001171201040e011490031481c01800f070700c52030304188242c2c502410003a120110395040141709802814030700443d6201c0700c104881d0100c0050445640583e07034840540b156003d8007056a4003601c070000203140b03502c6409201e403c0880a00082d851030084802140c02040c003030000c90344104a48206501004035a1030408030011400a64140c140340ac0c0c4050030021142d01c00f18000c01d070b24010400c00307035036046030202180c0c2c100d0324407000b0058074681242c05060b4614000c0407a040c851404903504040a001000e00e80240c5600c1b2031500c50320fa80c40f214100511880001540d1001f08101402141502803405023010101e00310300102001386a0405a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 738927670 1250 738926420 738926453
    0xa030312141302040f111c02130e1009110417010b030111090307050306101e081c030e0610060f020c1206040b010e0f16050c010c0c0b07050c060a0b0a03 67
    0x41c00e038501ca0542c03810340308200038681ca5040400401d40e00160b06c80407805880f40d1500050b10150b00f61300700c070160740c0407100d5500105a00b20f8400340c40c0c001c0d5410008040c2c0b0b800b06410032001c0c01090084884c81150f01072440d01000700d082030318240c00603642c03102a050701c039501e54880704221150b0300c003405941d543d09000d8050507150302c00901807614040095100511903070110042c402c8000d200c1c6115005da80402e4001420381444140401401a642e07108400500c40c90b0241001800603140c0c2c0b0840010a40e010322507040d48003141650784038141c94800c00c001c10204100000340c003540e0304404200709030055411703e041550000380788402c1000740c550789030480e01c10401006111485103002d0140d004080300708d410250300d4291a080300500f02d802104e140507800102c01e004d10107440d400b161080c020b01c150001544001e001140c1d041080301d000300301a010801d0940182c043e1420001010003c081a40da1015038002522151000d01d400000000c40400801c04e100c441e1207c56 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 738928920 1250 738927670 738927691
    0x90b13030810120f060603080d051501050304081b120c0f010b010507030507030f03090212011d0105072c090702070f14090a0b01030b060a0c050c030c0a03031214 71
    0x21650308010782400c038001d08150410390381c05800e01882c0d071070305084082e241d0450750000d2490524a09440100500e40000e4200c240200da2007847d0ba4480e000a44078461581052038228141c1005668a000c11307100240f8281003440301c880c0c0580d0304c00e070040415404a00b1201d542200c2510000b1942c0078401041b0207411808030908020000d00402607540303003c2ca0040d00e40292500d004246009000b0000c08211107519050482403081d0003c049007600201200e107080040310100303000f045941800f2030307421004840c54181c800d041c4a610320a024540321060b00c5100c6100c00346000188050800112141e08140711072500c6c5d101038540302d0307482a0000c1503081d00b4011001300c01c8290340c5c03241d03164040c0e60007000a16210540c0302500141d5071803010454615100041c1c010f400501e0900b03070811408034000d03030780d01c2c1d02c10510402d060150080c0c507010307903004080c51340b2450040c0005400c03401c464010800648188aa900414007040d0001180090b000d0804c00064041d50703055020b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 738930170 1250 738928920 738928951
    0x51c09150b040506030d05040b0a050c010501060c030305150a33030209150a050f0c030714031908100e0c0c0106060c0b0703090c05100302091906030e121804090b 71
    0x641400d11416130070150450090400c0100200c0c020a20300c03032800346990020300400c0c41c2c00703424002c0003036540042c0310000900680d0303140e00005040f403420400540c000b9080c403000c1a248203a140d00d14000b6039001d400070000908080c203002d2400060844000c0303807041c408042d04611406000303411001d03600e54015a9039000c800801c800d41c4085500307003200100401c540b90b8026004412104425040d0900d651030b2651003880d0342c02c50040103400350580500c039000300c1110382c0110007000c01c4107000c0f4045c407001a804004403549003040314680507004a0741c20502030000c036010400d90008007200380a24120354000d10509482680e03002c50089520080317040d0400800c9142e59610000c64581000b000315103845581c4851020701c555405040c112006142a610a804540d02d482e0302600301c1d4007919451050b410041c6852040a0000c1d00e04100c4084c0010045804041d04400000c2c090070028442505400d001003510407079442580c84100c40c000504401d4981c0c420441d44000740030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 738931420 1250 738930170 738930191
    0x180501110d050f090a0f02040b120d02010e071a030c25061d03030f09191109090111310305030a11060930040803041e06051c0915 57
    0x140c900107091031205042c480100131804200007034503020141c004501e80f8941c40c030350010800800d02d081c04180c110751611211a0948000100d115610020364001c01480c00c1c501c0015407105558003520041c04081210650094080c801840d040181d41c072042d482c1006d035038508034513121041281d0020000c0e0300a0382080c0400c6204e650b18040641400e60300c280b821008032a264400240b00140718944c0101041c1c0407039003003244001c07001070761960b000200c0301418024440703020700c49242e02c50314078800002c62150040c09102841d00f00c4890369410038040e0031070f0440351106004000c2d1641c400c064945d619004104000b4000e41c05600510303954142c60000400d0b41e84815042030f82c5502103420310035420710002d8071603a105001c00c08440d400c2d40d900348013044480c0115800e10036031004100480d42810100092046821400758800e4004003801c041c5481e01c42031007601c021072014040c107040b44401c584005042403801500041031502c1360740e0f0071040742c801d4110003051540e8419400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 738932670 1250 738931420 738931447
    0x3042d0608010e0f10051002160b0f0f220608011d0f0112030c02180f010f0e062709030918130201031805010509160605130918050111 59
    0x203061180341c00384031581020801006a04040d000c0b115401c0ca4500056440708065107031801b40400612021075004100002940c031801c28901800e100c0e1034140003c0d404500c034080703036201508105481c1c18110340e00c880251680004d04400325580fa00e118001c05c5200898440c00076001c04c3d1a8150f55506001100803540d0140c0240c040c9201c5641c00d2142c0e4251118580d411103408800c4c3d8070345c00301a4602144d50301e100800081d0050408200e08000180b03000d82070b481244400340868443ea84c0790040d9110710414413a801ca00304645020441d2410143c980c8d208001820201844010040300784d0210100100c1e42c406450308046144081858213102606c01d102c0303c41030442c2181000180c401c500d51303540c100281459560320210f900482d50301c180c000b040307400400801c000c0c0780100e66181c0701e642d00448050442078520340441d10307034050000d659080c03840130840d10001d82000304e044000c105070351b0501a20754100c4441c00001e10240250031054407100c202c680c175040e2680350b40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 738933920 1250 738932670 738932759
    0xa02190605100b1c0b0105091507020117070c0b060604030203101a041a04090f0c0e070e060703170703021c150801062108090402040801020309151603020c0304 70
    0x1151000f01003182031100440c04442e8441c8490801c03000079898030410043e100e03841a4900c42d5000f07010410080400c210300e00c081c0c20382074004e07201e030b580f4100341040724100d144003101d02c500030400582a400100e04040706260f8090406080240f0f096117035000240707410058018200c200c2c0c4c079450443c03503c05982c4083c245a010607101881207e05440000c407a001c3d0303008440c0e001c0c5e5070b0755000c070081c040440d600d40ba0094200c040fa803240c640322200500c81000496042c00030420040706010320b42031041c211b40318240c05035104c5465002c50003503508480c40c0034100c10300301602072000c150140c903e8880d034956a100080c000a2010381c034561010388008581c80031045914100040001c131703005450381e000012843c4103101c40d2803420700c2c12503090b0041846864006101082c00704c0c3c403e00c154021801051440100c40103d8241010b6500d0071004480050101c243d070100e0150840c006d070007038104110340d60296420540c658134ae601c50000400344207041462490080c20121100c035850 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 738935170 1250 738933920 738933929
    0xc09180c030b30071e060906080c03040605150a090902030709060e0106050a090b03040b06010e0d020a09021303020405100509090d020c010c02010e0901030c090617120a0219060510 79
    0x200c24000e03198a030210054000c4031920f2442024015000b481c403a0280100c5000d4400018019004000350b6205111403516001d10030100710002c20110b80b07a070007820214429651000100d195980c0c0313036681c41c00340102522144180b140e0b4180c100c1995111003c040281c80c113114000307030b11400d41c01058504645540949101031600005000d001e041d10485070650b1814106680d036801c041400b1034101034150310400f200b05010040c00100280740c0c500f01d010750300c244c0e1400c15862000f0300700724800c178010308020360150040c0e0080110341c01580140c0001d148a502d042c10107566074000c1010344074116106440300800c01828061441c0541c9540d070410060340040403201d001d490083e555401c0081c44c103050010002c80d50703045a1095410300c46040c00640701070503030b507524500310300400414003602014506218020410702000c0ca20716141521400085c404224090b001e55504d81c0010f03202800c50185c0d00311039842c1401d0322407000c0428440c03800000c00c1d150404606280e801c0c160407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 738936420 1250 738935170 738935179
    0xc0b210c0c010c030b030a030e0607080409050703050a0c210906020c0303040b130f081612030b150c03041217070f021806010c02121e25050604090c09180c030b 70
    0x61748070458070300081d03124030194103041850300550b4650006040d0300a1190050900b1b600003000300311802c3c0341d00040e000b400740ea14148942c5d01c804180d141914550301c1000300050390049021004202109048080d80400b603000910383e0594460f403003a40e000d140d24441a600010602c01046060880c0b00d40c842c1a035414842c041005a480c213190413010b60010340260008544c40d030b0005102011881e03143d50080d800583c00c9503014000c0c001d0b05c0d80100051041e0708280c1130b10038005044c0100c451034080c05024515080c18043c52132030024210360240e9400040c40b07100301130b414250000384820f074000c20700388681107a6441008080c0c0b655100c1061200d0100041c415180d03040044000d000703030704503400310f84d510a01100714504401041001803561000300c0d4902d001d200801d5a44044c03144000107815881c40000450b21542244a80e5400c03040c1000b041201d030603664041e4581d07d1061078580011790b035071a1186803610015041a0000341c1d507168103180241c051080600e82e0800380c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 738937670 1250 738936420 738936431
    0x10801030c0306020d0b0604080a11060a05120916032003030a0503070305130203122703071e09050a05090f0106081c030612061e05040c0b210c0c010c03 67
    0x20740380488490766120040060350042242034141070389400c00151400060030064546070b5560303402d5030b40e07500c170744040e541c00100309010441c6007418800c44000031682d460b124580416032800154480c4010078140c10790007440c0c9400500c5070214200383c0114007440b2154101c01020078000f04134030404020a1083d4000c10001101d207400c00140d036800704c2e03107040c00207060381c0e07012105204000c4004005c1d07043c0100e8001034440c0d800c61001c0c10035640050034240c2c0300007030f4458480150061501b0f031580b5500c00e170420003440d2034500742103070204603402030510701d20340c3d43c07028805490b42512080c0d0280c0d107500030040c41035030400c032010310319a4000081c0b02e12803a040b0340300d41368004802110040f400302c840040d0494000d40010000341080c080d49080b224450801e580100819501a4841101c0c2e286607005400180602e5005e640c1014091210078a004401100c40e40820a002c1c240c1444120301d08804040200451165031281c0d5150b58914003029854211780d2100059814145800c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 738938920 1250 738937670 738937673
    0x1110307090b120c0f09040c031e05090604110a0905090109020f0f09010303080a02090a2c010f060f0e1c0201140a120b01050903060414010605011e0f09080a0804050f01080103 77
    0x10030150800007401c0e1485c0d40e00089010720380603115440d900c036005404c0104036107070345506070701550586030290000d10f403013400c0d0b68500e42510703801d0382c110507140e000e94080340208200b4212440700078801000400c01d10f43c1c804400e015503804a50b50446070f55100c940c0c4080d81000700d05c2ca10026000c40e2903030440000d07000000c400c4e030810300003c1d0404c00384500040000b00d0396411101c90010082003448501c0d0f85881c808401100c200c64044d00c0c905400c8003038030b0b400607154414161150107100100103130500380f08540042a0303403800000c01200c01171081864950503188100f0601c0258801201c0701580000341c4003407002990380000301c4040002e4401b13554031488004414180701e00204120f00102e0040b1194010f2240450740740c007541062100700500d83e00c28600300b15100c4024003c00366240c00643d02c26070020009480e88a40704010031041b03100e02884041240e450030001c16454849900c00d00c0c059842c901110303d480005000e020390320380760f0300300d0001107000d180629103513056 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 738940170 1250 738938920 738938947
    0xc06160e0d051e0c0d08041d010f0608130b010303020607021c050a1101060317130504060605221a040f0b1317190b06040e011a01140c01110307090b 65
    0xc8140324615103c075a019180c000c20306101c8416003000042054820b000c482c1820003aa500520404d44103489400e01100301499907005123040b56203183c005500c440c50440291034001f4018600c4040110207180d00e000201450340300c0380070b540a0b0340107103401e2412000c0640340c0b8851042001d000c85640c15a0045070b58090102d61071461b40d490300d0300f0140007284645014124a400003440d4550103c010032402508d0b00c040e01c011440041e03c4030510380c3d580103200494800d4055600014000c0002041a0401038900b100d0f012040032200030303203655104090003880b030b01090300c2c030800400202005406c010800c0d18000d4100c201100740b62040e6940055080903440c4070342040410304404840382003106000341c509141d031000c9004c9a600c03841c0b40c1000300b81c4044903900d10903407608102004500051003010840c0c00e44065241c9000300600065849004c0006000d0b4010400c001310108203c00380035000790059880700d800d07140c0c140480050088034158000b0389551030300f8091034070482034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 738941420 1250 738940170 738940183
    0x3050402031e030c03030108010b100c0c051203070b151801050a0608090f010e030d0528050c070f06140702120301063e060718051201020c06160e0d05 66
    0x38484880a40c0c80403039040c0ba00758020030440606a02010000140c00b801c19001035030100d000303d07a4440369a40c035513000c0c0d6052807000340c0605440e1038044280164105070528140d0f01a400040303d08181d1030b5a61608090411509003a0f1101c11004000060500c48011344403008400081d0030349604090101d802d0b054a4894001048501004103200410520400d0000703614280240015000b21241c0c540e20b900480d4036a050614207000249034180b000010307800b228040c000b40c01888010400500607040142004d49041e10412400001501080071205101e215070700100300503e821005580380c2d14000c01c0700d4107541003000313200f11a10541e0120f034195030b81c1d805d15180d018403294406040c0040142e00006091b000650354040d800300c10400c5a0000400e0202c2e145580c42010446d885510f0000b0a124004c601800b8803a501d004200900f43d1880903000601b40b482840c0c4640c41c2a81c2a07604d881008580c8015605007580400702048020007a01d14603d6122555101039a0b6903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 738942670 1250 738941420 738941443
    0x61c0204020d0b12070609060e03100b0111100f050705040302011704050a080d020318070503030d050919121409060d050702070f14011e08040b0a02070204020406030b0102010506010305040203 84
    0xa40c0001d42c505019500e601c6a20700002c0900307a0b8034080c2e0a40241613444103a030044002003241203400180c1580b2410904000200240103004820380707121440d00980180c400c0281800110020080058400c012208440312803101c00304005000e800d40381d00b2101d014007201c1c100300c8200010310160b604100c142510603504040081946e4490826505105140340000c080300d00001c0c03142c2c482c10680d0055802800d4410f011030171230304500c80b082c1d91a10f60b4441c01d40c15410030700071300302002c203690302c0b1640c001465005e44510450443c10988415a003034421039801d4403900ca40204181c1c0810780c000410340c0a4003030b030703d07011601000540798001c1e00e001e01c120548460000b56440c4c0f09105860040c09004542d0001c15101e50840c44003014201c1e00500042c02010b94a44c0411440d101c640c181e10192200800c07611036032180582120014600d00722180c0030415100141c0380d5200600080c00036540010b00c102814000a09562024102c6810182000d0901001da0f401144581c0c80c007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 738943920 1250 738942670 738942679
    0x50d0f0e10060b0f1c0e0a1227090914010c03021c0506150a020109050d0801060f050301031a13170d0b060304020901050f123705070e0709030f0302070e061c02 70
    0xe0f045c3c052090050700e540000419140994082d13001080703050081e07103201c98107940b01c80c480c0c140001e50840144074458207252420311880001c002261960340030400c1d1602403408401c06540841030542540c85403150003000a9001651b0700e151020451194454004a203050055041400000c1c01d000030b0011518000c600c0083c18030720a0f8000d62010300b01c0e56100c0d0070313503040c0c1080020242001d00c092240360b0201c1d030200d0039440518407440449050702c0d400b19410b25207140340b5001683c0a000117101d902d00b80e0b200161840170446884003d41d10520f000007040e61000a0501002601c0c20814054001d00e030910a010061b5514a03183e4159541620310061100803400054120208041036030501d00600c06480a510041c2c55a400c43d448074507111141c405456400f1154500b151001a080742c01840b0140300c0003d04141e0241c10036402c0c40c2904000e45c45e82c0341c010303040020140c1100541e0200b6004c02c116490040c05543c040c0088030200302d85903071100854440841d00f400284a1b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 738945170 1250 738943920 738943957
    0x1050c1906050c1801032d06090501050d080f0304030918020309071203020d031a0604080303040501140c0301060c050c100509040f0e070506090604090c0f030b03010516050d0f0e10060b0f 82
    0x803803c89100700146c1280904c1f50084060100c8240100741501600f01035500b03010001c0740e1828040300c410740f420390061041d46404200e5050304820742018204508100901d10000b0710500290300d40040900420801070380d03404d160b0125840c0c091950701090726890140c4484010035004154007944261a0601290140700b200c0c0c0b900d1980e201204095004c4d0001c5004580c00c9000005184694030402c0200030018074020101501d040480750301000b90030800061140e10b1207059644111841281210005002140044d00c00ca0560843c20000f680c04540320300c041c0350034081d0300414400d2510070080a501d5482c0720b9252001405100d000b14400031311280141c403001c1c2240d0081804150820042c250007034000c20340750f048002000041d0070061100b4040c075062048070301603241c510f803c85401d2120300c800c6e5034513005a44d030109071950702c12588000c4112070082540700d0310864007900000c120b01200d9003c44200b034000500ca00410b0290b01e000d035105008588080b02c626450707010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 738946420 1250 738945170 738945191
    0xa05010309060f051306110436140a1a091602100e0a1709060a0305130605040c0f0e040812060a0b0c0304180b0d030e01050c1906050c180103 62
    0xc1d00c040200581040d21348010080d66043d5400c8500600d80b0950003403102c085201c101203094000d03402010f100001c1c0c00d140205900d000403c04070b850050580c5002d100742c06859070000c0b00d0000c10303406010110641007002d0403240c2d1040d09038851400d41484d02404955001c42c070301610040c40c2c00384489400d8040741c0194001c11080c030f820070003000140603420100b405070b84c84100401c8200c0c1c401803c0c1c601c0070f2000e011075080e102c00441c090000380c105505010200d02a110141070b000648070300b00c064601250387c500805224500440b24a42000c1c076084858644025913030012809010a0080c0000039003050201c0300c5440c5180d95140d03564942c040007510100c89a03010000b00c800c002810088414003002810446402041c442c040002c3d88414000341d521031000994008003a2142000180c01903045805055042c90400c3c00c15000d00126441d02884903801000c442c00028120204082402070680c01160070300c825051090514031082d50380c4c1206043ca0605450340000403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 738947670 1250 738946420 738946433
    0x19050315040213320a080a06020a09171501060c0c0e040201090f0e150612190e010603030302040e0a020405030607050a21201611041404150b030c0a05010309 69
    0x4020303000301ca0b0390034800304d030b1042081000c43e54200c0020000016010101c05440c10b18802c004565026000e80f00704807090342c4090095010501420a000c01a5800b0800484408403200700c00b645070002c18406030320354048019100705038003c0080024414109000a04040c5120200c404007291400c1507180c9100681d03050341c2903042041a038511180000300801842203c034040c1441424070f110308100b642c01e1003214465180c2040003608042c005c01c055504030201c440503d11361500018403800c08900e0380d429100301358001d40000382c0100d03003800134600120000e034000362882011480c1078503005c04640c0351013006100d0310a000b400301360080c0481c02034503900c01e544080b40440781550303541600369000740614054000c0c0010000c52800005000b0021a030b00e2264150606803801c01550311041d050007030f00342c6a41c2160310b880181d00307080c2e0b1008501e03000300c3c801c4409251010078104039508403030101d903881d8429400006504140e44800000a054680038a00420030103018103110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 738948920 1250 738947670 738947707
    0x14190806031908130b2101122d020a0906030c0b130b0d020c030403060914070621020c01022a0604030c030e060c1608010c0503010b03010b0c21190503150402 69
    0x401c5d0386400007980c440d4076080581030038000030030060341c0c5455036264180008918404900140300708020396840d80301012104180d14a120000014100400c2c290302180080216502860b80e440e21003c080c010072038100030f804013030007507180d0301c0382080c02841c0c2c1d10a84482c103200d40d00d400480000e20350840ca0032a0102c402d03403549070741169070701d940d2031901b04014a03212000360740900b1010204000e00c0700100341c040c115035607030b500c030301c4c818141c00c0d01e580f100704e00c0c0c110102d090307a0b0801003c03840750028005820140d000c3c84240c0c5034000c420250030010307101c40d2034401c2c02c4d4000c9800c100000c1c2d00020702460040e01464040f01d04480080400c04074441d016280c0e000c4d208440c0c0781c50a40c0705104d00c10007503951020080c08200189541516103010a00900c409000c050006000910124000d01400c003000b00844102c0c031000c5400241d03810300f080300e10f42c5032200003900342c51140741c2d941c4000c2d0058140c9041461850003050380c103d03034410419480e00c910713000a40f6651a40020341c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 738950170 1250 738948920 738948929
    0x1180f030c081309060b1c1e23010501050f1602040f05040c031b120f0c0e09240603030a030509031e03270703121419080603190813 58
    0x695070351400d0514400e000c5400d00c911340c021420140041200300e0b03040d082c0c1d203006a00003101513122a003041d000024003000f81400c02516041841500d500400c1c0c05a04440304908580407030700c111044000c4810001600f000d81882010081c0d12081c45040e8100e80c1c0c0c54001903008050246640f0010340a00380c0a49520760380e5007000c00b80300903c50b100c0340b0700c412284107100313405a400f074808418002c02c0e00e510685005526404c24030b0045030b10728540401c0341c2e119400700ea00301522103c40c03210783c1c88107a905c0850b5502c0810321013031a4901c0b509001040140380003500044c5013460000355640b140c60075190415483e00c011400104082040c3c8a855a4925044000c00c61a0680410607001262102400d5801481440310741140700541c201440110001d080c075281561580481c0c01083c002003010407a0841c2c40c04200317060000a8030284002c40e0300e5540000d024600148100c5000d85828400e070002c07854038041244000c000c40301c0681c040103083d19000e44403003034181d98620758403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 738951420 1250 738950170 738950183
    0x10b0409082212030f0c170c0d1404030f050111121506120117070b0f1c09020622050d0c091506080105041a03070306050f0a0908030f040f05151801180f030c 69
    0x8034604444201f90141580c041070f501102c40c8020400f03003c0303421500c0a00c15800c0020100070520100b10081c0d092000b640c0500e0011a40a05800780c01c4400d9021448910520f1025824080c001172044c0d01c4111581040380d5803030070701011301c1c044041350780d040c454019540c40300715840c1d07400442806841d009083e42d9120b01e4a942260b1321b140025407004c1c010f482e14281030a80700d03002c0111071041001040e0080c01c000d00382440c4940c4490180c070716126051043ca040100011155104e03010354541e50b00c103016440600349001c41c01d00550304141083d401d040348001062250341d90180c695411501c0c00c03240424010582e03482c0004e4045400c2a19405000346000402030243c10b400c018017030b82440c8950310080d690070060000711019500002d0041d2000c101048a00b040c1200303441c0c00900400f06201502204c0e901c0d80d240c05a125a09001740705100100711300f000401e0369020005514000906c110080c2c10345590702014603010052600048540c0482410b1003541245034031980b200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 738952670 1250 738951420 738951443
    0x20c040507050d0605040e06010608040206130f030b160c08030c040e0a0905160b0403032613050d0e030a021003110309070302030c0a12020909010b0409082212030f0c 73
    0x44002c05030392002400322100c500307044001800342040e01c5a02d800f11400c0018000e66420583d0848550700050000e0323920020521007800f800c078041503500b008103000900c44020520314500902560300041ca1040c2040f09c41e01c6e201c8046800c1420300e08420340c403101e415520ba03203e0502d0381040c040d03070300b0110301907140c98100000d8500035070040b05000d008500b00d40100c0b02d8549500c560100d0750003070052240c0c3c180410030000e07002e00c440c410022200080303070000c80a14078900d04040c000b110b10450f108401050310060200c00d05c0410014403151525030703824034059003c80d61b501042d86000307001d02000e8200070f5406100751b220b02516941041c0d1075036203092034074000ba40c82109000a0744a070285a610394040c1c5005640b001c111940c08044e085a1a045d40800603035405c001c0900700b1a540f20003880381b00b03a58038801d246c0d03014810b03a03c10f0348642c5c001610784121114514003807485100d80d8403c0c0102400d00c504801a5541450501c40c1080c500304100c03151003040000034410b01200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 738953920 1250 738952670 738952681
    0x603010f09031107052e03020405040f1a0402030105061b070e0c0c0d030b100c02041512061103010311060705010e0607050a080615270603270f0c040b01020c0405 71
    0x403808241020300c3c0c000c80e81510788520800c5981040b4405060118110b04c0c3e145806885625112450310824203005040540d60700220b410380300540c03001d250056a800812420400711600d84a4a000640d421030035907041c0b10200307072640308091900c80d0fa103504080c510025030080120f18090300440744101001c1c104245046c1407604904980d130010f00a5508000020344203110719601d80c0d000410801b100100000196a10b0100c40d00a9801580315038014007190281010070b0020819856418a0f004003414040f0485414607105400c1100800040010a4400e815995921001c40b05140e841482e0725009004101202c220f02440c0103287c00c01260301d801c08e0140109018946481c0a96030340c0b101041007210f00f81c43c2100c812130051020f100b0014413541c0c02401040c0f03103540b030013400c03129130002000754108542800020599800016010044909988200d14034034001c5c141d41d009000995110a1500c480f075014642c2c454195005130310810951151a0b400380c400c010900f0070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 738955170 1250 738953920 738953927
    0x20406080126070e0c130f080c040501050a09050903040306140a05150a090c09080303180c0d03171009020d0b1c0213020f040506040906050a0f0e0f0603010f0903 71
    0x34412441c200300000708403004070b4000003402c20b04210020180041c02d00b007070340d6850340010251031407a04020a106803416000ca1140502c09000d150401507002c4e4680041586024161210103000702d042900400c040d8a4803408202500c0c845103000c11590b0390546c5480c81c0d40515800508654104102c90110303c0118003068041d0b0f01d40d06081c001c51b0748030900d2900651244d00e0684c0c102042940c10040141160b03c0311901c5416880c14207191580c404010785150820758584202041751104003248220820140824040c180d82d842450134003070b1030150201c00e540c0c1760414200d1000c03001642e015132054100d0060204a0700440d224014240c2103001840d500010314020020114001059149100421815580140001c101c4a81600c515010b5000f48c51019118201444041491f82d40e09020f03001a241da60000116070340745c0420009601c0c0c4a61160000c404484420712096603600c01c119400181031030a020303203403203400200b401480500e010080701c510704010030040550 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 738956420 1250 738955170 738955187
    0xb060103020f1909030b071403060f0303071a01140607020f01032a110d02010c080408090105040e1305060c0c0307020d020d08040b0703024c051501140c1c30290d0c0306020406 77
    0xb520518040b8113047003d802c0c0150b40c03240407806940007441850020440d0721070b80102140c0784080505000052000085145a05c1a081c80700c020401c1c00300ca11882310410040d01aa03d91240300070f000b10045520058020b0340f01500c06005d0107000200d1100690107142200d0040c440d04204010300d29003076590000b9108690021241e0b40100d8010070101d070b0b02c103019100c2c1200000050b40c50843d4560810000f1040100100d802c8518802e90001003048079000d40000c2900300c42659030f07a04245030090400e41c91000a113015801c400104406030708880d41d00c03040e25920b80c0380c003140403091400804150002c402d254103045c18902000305e03140d010014400724600030f885103ca600140b00504806004210340218aa48001030060384a411607000c503041a03020f04048644114002241c0d0351008029141c140071040c290302c110b001034581c0305a00c020701c00b810b510813011030080e0511141c03c00884505101e00031038082e100510880e04030071001954010b00441d99142d030380001601506 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 738957670 1250 738956420 738956429
    0x40302120d0203180c01080c0913020c01020a0f090b0d05040312090606050a080a0b0c13030f0b0f010e0f0f1008010e0c0405060901030b060103020f1909030b071403060f0303071a01 79
    0xa0b141d154010307661000207207071171210005844070750180e510603c0066003500103034150703640705022070b8007018002c965100404003d0081c2c000540c1c1c603540e098020b000c185171030368000100300449204100112625080e50600110644007142a85030b6040482e103a54480083c011183c3c6040018420041c2d59400203007210710076504140c6031540c407003255840b407030440c501400090030440058204010200103021aa810342c455025560300c9031201c4034102c01d84041210241d1565090000075204540418018071501003c1011031501c1c8103000141d51001d40215801c0303100c18040b0703840c0d290450080e809001000008c11021b84040d204a9490f207801403030301c1c040d92900002c90040d00344100d0760b45c142c0c3d80002d01d0384626122400114001e5200451703036001b108041c02407003614030710340c0c500410071011a86c40c1d40a190850500b407030581000b9089401344650700b655030186405c1c884c117603984000c0441d0301c41c08203e03210022070f0442c81085401040e140c80e1011030503102248211080c1600c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 738958920 1250 738957670 738957691
    0x50114040209090343060603150501060e0103090309080a03020a150504020d08030402040902090127020a0c02011107090516020708120d050403030914030702090f010608010e040302120d0203 83
    0x1600d43d42c61031510ba03ca00340c40700341403200c42c0c50038000000c07100218080d407000784171110007a43ca01480b031035007a0081040481d5110b4461070f0030010300100407560030940316055004c2241e94540300c0050101308050381d815052645484090301072602444410009085c801c056031034540c03042c58000d4a40c11051030440d081d82c00d50080010b074030114070547d88503a50140240305e40c030302c003500d4009c8641c00090041383e000fa01ca140e07480068660000c40c078020800760001e200b0802d00160381d248030510984003090785a1050204005103070740310f800320002036028240300c2413aa03120032042d418400c080d04401c0e8070301c1c01c2206008402040ec020841084a59406d803020a6160031140751070341211000d819902c0001e10000c134102109900031a0098480c1c00e002078003c2640da0b5030300900f904441d68901e035800200e07001095042141c2c00e00d50201003e64200550b41c18224080c02d91801805880110018880050308050007048589071004048080a4550181e07009042c0690320407a642c181d003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 738960170 1250 738958920 738958939
    0x1908010203161803051f061e080d020c090a020c0304030203060c041505042301020a15050108010b0d05060708040f1a071407030e0909070f081014070f0503060103090501140402 77
    0x1003d0004038002c140c0f44e0181c00f9080f025072450703500080301e4142190060755561a940003460040350b81071806130070b0b01d5025504c041803038421060306082000e12400c0c255040500c22404980d0b640214581c4001d4031a00162606102a030340b074910302036138000a425100c0c1c001070112003448400a4412144c03d1825200301c050707210300880751805035214900a9000c03001550300c2c81003074444104d20044040c811600c14903003d4903000901600c0c150b001c203046546500502c10510b00380030b00c042c001015a0100007421007581d41070350342c2c07400910100401a880d80490b04010f4400c42c3c0c10b810582061407519442d2012400011f160400d8807000c0102c0c3d5807103040201c1030000010707192001c1e01038850000080c110710622504403401401142cac00d00550101040d00d603400340292015240c0b45e4020804411110041d03000c50b000491419858050081000380d0561321051084000380f0340d181080e2a07454013001600503160900d40106a5420042c0300e102440c01ca4000500c95402160043c00c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 738961420 1250 738960170 738960197
    0x7060213030215250f02060d0c0f092d03020607060506101403040204110c1615093b01030803040204111611030f060f04141b190801020316 61
    0x603280f04c0e24140807446013418504801441c0c81000781d010050142c02a05031880c80e03a030000725680d20442210740425543d8042c400e005502501c04075070750626082500c0b6070760814548641102d04002100d0b817500302c48150313200507245002000011540986255103811052820001500041340d50b42d0140540b004000000b5209030b884d81078045280809500e140c0741c0b902800050f2007800c403418401c040802c540d07561f010007048a40c00129020f10f80030106410b00601004002894070b9800400c01d40c0c00d0300340007940021000c007a15003890019020302c00c0340e822044400e250b04214404500303e0510000091040303c0009503c01d91003103800300100c0c80e1800c80c58446008000070302d819844400c021500059521003541050030b00142228080351a004d001c0d45001070850344200c40c0d8800c7c0c8103020803c4552011582c441d030189000e0500c0300b050312000b84600c0960140e161007900910800800780c003804030600090000c0c40001e46d500d05d0504540e03c004981d80710b82000181c0c1e4002800c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 738962670 1250 738961420 738961459
    0xb0f180603040b0402061815070c08030a0f0f120f090308180c150903060a0c0f050f030f0c09040606050a180e0f340906080f1803070602130302 63
    0xa110b654024000d0b041030700e0320b8003030140c16041003840d580100701001c0a4403c50b950780d4100020001000d07201544c0d100d880c0750200b03020016500001050b481440240e44454000e041404280644d252101203002c503000222000d0068580c0c4c507401c1031400c0204400e07001715400c034821080c000d4032042c1150721403c5c103888402007101c005a480d40c110360280d003244e00c1c0220866126813480200c041c108014980004e081c0031050360300c40c4070142c1c2c6403200038019400c1440050541078500340030b418646014040d03807c0340f00041c012020150540b0002c2c01804800041e1918240094020002079840d01d40141c031580c0034181900c081032420912050818a40801c64150380541419440c503484204122020b1000605076950010408444e80c00c01000a404140750303c0c2007415800924a02c03c10150115100c0e0b04403c023001405404c01c01c00300e145a881541041078614002200c2d01c54041030340c1180a0000000c140c40d00004036004110060041c20050300d00880f04080f04500014004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 738963920 1250 738962670 738962677
    0x1050306010906111204080f0c03031306080423010b0a0b0702060403080706060b030c07020f06160f03031523030f0604080306040b0402040306020705010c110304030f08040b0f1806 79
    0x540024100300050210764130842804003480300101c11500b2000140020900c0c030780098001d07444541c050a941620194104888a18100154040d500e0a410314501b0a45020f0718001d00c0140468000801c023005101c0c04000c50042a040101501c50804c8a08502a00200700c0e4140702e51307441a40801e0700b8482404852600354001c0100c0e02c0d00d89181c0d40c0d010290001c2c0d00c19141c0700c2d031780c90000070320407440d0004521036070048840e160b50b03000310320400844580c0110308a010781d1050041004080e003908034001016001b55001c1e1043c5020316045002d411a40e078007030141c0d005071400044442d411122140c0b058001401d041103014002d042c942d0701c0c0f58031311007000f065108002150108006130000c5812580291005c50f8001078030b0080341c01e9a00c294421280d00d03a00241c00300030b000e000c1c4560a000b226500d0004245800e0990042d030340c0c000e500020f06195030556528042143d030034111802482c90090a41c1c640d200150a0600c41e0808080324051103000c0c955120240f5114084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 738965170 1250 738963920 738963931
    0xd050f04030e0a2709050703081306031a0d0f05010f140a0e121804050c030a0b0405240d0f03272402162702030402030a0602090a0e0f0411010503 64
    0x5061610404103081414480701e00c80c20544070340ea0305d080d50104001f03115280180d4080e88034036075180c000203a00b0800e1042a4050001c01d81341400f00c2d440c28081050900b0513410440e00006201d40b14280a06030486a03a1300428170341c40c0c1603e40c41c01c00c10310707000600c0a520b5000d00036215070302c560861050f104440e5004a20b41c00954003109540e40320f1028014841c1148103092064440382c0c08030f403c0b11b00950310102205008000c01c10070800a024042e10b60100f0340c1c00340450f08142c1101000b007940e00a041e444c0746025a04000e958549894402086070012184280d18030340c1d0502900c1c1a5084114038055a406504000303074060350000300b411102001d03811a010f02c4030b0320811a118483da0000c00441c06040c3d03081100354003041041001d009040c0e0041040341d40c0100d00b4246000c1a141e090109006000300800350b64007003030107030704160002d20140c1d40d00c0344100096003d0310160460320014428000f1f002d05444c0c088102c602c6584100e6234034140381902d00064400b030008032003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 738966420 1250 738965170 738965189
    0x304050703032010050a05153106030c090e2107031e020c03101a0904020315070305060319080a12060f06020114010504060e0f0c0d050f04030e0a 64
    0x1410070000c0e2180c0100c1c03400200c0002101410b40700702c08043d007414800015550308544070024032000480c130340310b400c0d001203180000e041d0440c10100424030300f940187c003d10001d082d0a50520324119900500d9841600400b01007000584916100c49010954001c0303603c03007481c0038a0102d40100c0011010304074030140d00c9031000700c40c5d80240491303107030703c040b80071820400000c1c4035448076610034528440e60000c98011b8080302e0028400e062400c4074443d4010070319400e000c54100e83c10b803100100401704809444480303a0b50b455002003440c00e10b8150b5800021094401000b9080d039050344598055034049050b20440801342503660f10156000a0151030590708001c00b508260103a2841c0758126900c1002084443e580c002035050740d04071354002c4016035118210341000d810010803d5000d05401c4030204241403d14440004004005000881c1c4102a1011800e4641090151030003010100000e00c100d2410240d4121480320517141100412200c03100b0001520b085c125040c01e0f200c00c0d1a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 738967670 1250 738966420 738966433
    0xf010f020f1206030a020d0b06010e010f0e01230301180b0a03110d050a120f030e0303010819030905190e061f1d03060403111b030c0d02180f150303030405 68
    0x10300e402e644001808681e4103103d4500090010b8540d8001800301d14087c51030140c13240303000b0700090480d07001000c1d0b40741000030048403401010f8000b03e800b060310200b032802c0c1c072010b50103110000c1c00344840d4900b000d1904000c000011003d5088411403101100290184940040c90041c0034a4102500009145040030401c2840c00d04202d07000300040b034024400c40340807003030316150744441981c9980ca00c1f00241682c20340e001d94035014003400020301010f5000307600c0d56240c164100e4561040304134007400c14002c00d12a20500d445141450301800380140700445103450128250b1111546104510501c100d00c40028020725085508551403401c0d00c502c00c800300880002110424110140e01034441c5801a021203151010041a8420f80c03103600c41c0110709401c000c629182140e40b010b810b90b1800041568161500c021030446070b071000a0310f101400c8011840003598442c0101102d60010500600b00318285051410350f90040c505641540170300b00100061640320300c01100c01401d60360010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 738968920 1250 738967670 738967687
    0xc08071e050d0b0c070605090c0f0d0f0f051c05030105041b21020f0c010b031c02030702210d0f030c03020901080114011704030f14030129040b04080f010f020f 70
    0x43e400c2541c001c001c410070601c3c1c0101c0c1d0303a4000c226142919004a40e80c480e260380100c5007040f01645500c410308940500a648050361451620000290b0041000c0c000869017003c0110030011080403180300340b1481201c6084400c000c225400034465140f040b414845100a02140107011450b061102d0b640c004403200341041c03c4c004070f910540b1345920a5800c00600550352958406850380760000300004c08c50190110030585841540442d0f190313090840d144a2414a8000040320041c5905a512011901d00c035070700e0860020106030004100e0189503442c5180c40d0740404c003121000f00c01d450401100c0445981202240039080c4a28003007441a001406030780f12800c0c400104000c140b400c0a0302c2c1402c0c5561011002c001e031011004280d002000c00403c2c1d821070480480704440c100001e00750361502ca940c0d203400f5142d554080509010b00900204c402460040b02c01178100b84c4607841da2107070340300e41265545822004401480d40307803c80070903015003d402240e18030729040f45843e084c880075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 738970170 1250 738968920 738968933
    0x90e030d0504150609050103060b1203040e0402030705091303093002060c1617010b0d0303200a02070f0f08030406142b05090a0503030703090f0c08071e050d 69
    0x2d0710603242c0800c0110340d40c1001803240103601c05081c055001082d0b0307514601e08401941d0030148094071400121000c10081c0740700005440c221070240222106949943c00440d00341903058000130b4002005404008020305120b5105007564802c2ea14200b860380d0b24160720041d0001187c0140da040020303c4841e41e9901c0100c03000700f140307000a01c220302e08108e8584061400868a0424030a086031541c200302440900d29109405107080000340810020400080c861645109000301031503902e42271021040041001c065112286689060356066240740295649815116450200c00030b41c6001c40e4034403540d10b40404803001000214141400c3c80416a500348200030084c0420800344401048500c4206030740b1682c07402d00b0031501c1c1801c0c1c804180c800307540000f0305540150380240d034503030000341000040700d60000035403400103041c04041c0b811441e030b0101c004010b464010011004900e5400201d441000c550509003131449801460b000c0e114600d080e4450541e10158207201031011408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 738971420 1250 738970170 738970181
    0x6180602062802030106020f160509131412181e0103020f0d0203070518040b01080420061809060d0b0a0c111e010617121b060f04030207090e030d 64
    0x41c80c1a110100741d9403002d1601281c00036404200164072013007400221090074407004500a202500c04420036051801189022130082d08050b240f220900400c000d104008001c0858103161500740d910507208101d188846410802c1c00390700c0c0b41003101401d00c80f07143c184506018408400c50580d009112240150f0003500300a9000f00c80c2c1008000d41c1c000401c0c503200440c814589500e0307480e140c1111a4842c11070b180500301482c0600d00c1c00c2088082c983e04810890341c800d0780610078103a001c0e0030070301140c44000391446103500720f0300120340c2c0d420f501043d00703a1224070801070340c060300c4980e114801c2088070030000c54041c1c8800e02403000f05001d58001c1d000071200159606010041280240e0410300d005410b0564241c28408401802a034201c00e004d04030040c80d50b2000b01d0246a2041001ca0322188884203102c40c07401d00242e1600c0381003035000c2404c510545202501d040345400c1c0003a0740c031803800302d50032401402800c0d0b0120f454103403446051040010b0ba4025810600003524400c0240f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 738972670 1250 738971420 738971461
    0xe0a030219020a1203020609060a11220f0e091b011409031204080109170a17060315010305060711061005010f0e090127060501020622050a0c0618060206 67
    0xc4038070f40106107122a4035003850b1080c0f280e802440c1514103840c40320304021001d0055403005040504004c0b02c40106010344903a044078038403003943d601806517801e12450300c0d58025484140c001800080034801c1d004200d1040c128102542c1803600200d190014a800150f0111b000c0b07090b90304554000c2c00f080015007220040074088541c1c1041c9000440003540050b4848a91603460300490008c10111444031610210680305d118245404d0740c2d4041d00030455801c1c08481e0404031800240d80d42d4080013141c4a10102e45c00048085d61242801d5403626012031b00423010820181e40d24203881c500150007441804c43c101400c1550341094011205189014109000c00842003070195640c0e0314005114002c0c0092b03508088900f24007100d103a640800e81d0102c3c65201d28221040100340d03000301da0298014020302d007800c08444030050304d0f4001421080007030000e1160096140410080e01d0702d600560f10252500b903410b501428010120310854002c90006801000115128009004c00710780c3c030f103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 738973920 1250 738972670 738972679
    0x910110106030f12030e0105060609060703050906070303060501020d0504060c020904060212090d020f0f070e0c070c080c040f021908131e0c0803030103080f03071106190e0a03021902 80
    0x296543c0e1100004190b80f0841a42d8409900742540a881c2d054481d1400001000300284400e25101c00001e44900070300c85400d016000c0003606108140c4140119204000010720150b00e0302c20a06001f0b0050126000d154003622664003500683c0d400380c0141c07030403600c0580d5521100341003507007485907011019008a440d29001c1c444203e0715a400384410340b0412059000780b00941c11902d0007032400b00c0c000d0640c2010f03041080c01c03265800c40400e058080d81c1800c07403203c0702c544030411005241d20404001030709030b8451080129684202040281c4055000c460900c603e82c950306114040780b160318032003001e1130001001030301c9580c0074551035580160342c103120b58480a0203454000310303014640d1b00800341030040d614070310070010b1901a002c040c10440005600f9903045a130b42c95802d10031800040744035070001c1300040d09988192156220701c0250010344c2d180b41080d8207403501100844a000c0007607814070380801194480000e0402100d40c240e401000d4101c0300b0444200c10004080069070071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 738975170 1250 738973920 738973931
    0x70f0506070f06091b120218070c0f08070b0115172706010e09060c391b12210415020604060f090c0b0a032c0f0309101101 54
    0x3090013840754490003800b0780100f0413540404020380c0b0521080760041c101c510002a05c00c00541c80b001020554441c8030034004c4096100c03a48e00b07581038014120002c1609480940c008104201c150141036628461141e1125690b20b4207120b10989810181e2030000901504c0041503028001201e0340d001001000500c503103000c4180341c48030f0308401c1c80380c4848940c010801002a14140c444194ac890010401b9114504010848001c107105000b444c005154a103100b16044d990a1007840c00035400340044007002c007a440070075a449100d1005900720303c48001c4189100350408104d40020046404041c1c0401c03484e0754046d01102030982008407018400f400046a075064580011807e06802c1c0c0007000d2500d454500402550080700c105600b442c10654a5000500d403000600300792505110017a17200c01c2ca2403000c800078580c2c1000418000303080d1600c00810181442a1610441c0700029a00200c0344246040e65170302c81c0c1e034040c41c1c220b44c80c000442c1b001c81c841c1c3c43c6023130f036450802c001080703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 738976420 1250 738975170 738975173
    0x30207061d0915030d020a11040603020d0213020d09150c020a0302060718030f0b0f070e0f010c02030123010f0603020c0d08040c0e040b0106170402010215060a120b060909070f0506070f 81
    0x1070174245114a070056800540d100081c89010101030204040031102030000c581594003140e40d0a00e010b000900a210b0188a40d9100d00103405440c0d81c05961001000003900c54200204100700c00085000c5440c13401c4c0100315101e02c041111110940c00d40c00070421515040e0f4210344400ca0702c402e110160003800b1020000400031b01106039824058216015581066071041c029140060020300500c500340f280030841e52900720448030071074401d01b4280960009800400e02402d04031400a804255a515206011030401c9046040c0d1702d090051901203602c424003031b0120701c54030b00304240a03070250100580c81403284075140d900601c214070b400c001c00c0d96480f01118420040d90200e490021000041c0003081d0300124008111350b00c0704880c012410140c002130b403264501d00018041040d824006107480e03e406582000404860700c2d450300c2200c003400d048565040c2581c00038828070320400400c4e40c100c000560a000d4820301c030510100c540c40c100800085030301102046a1141c9409244070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 738977670 1250 738976420 738976423
    0x90610020c06040b0a0908031e0304060b192607170a0203030f0d050606090d03030c03020f0c060115051216120e0a151a010c080f0a020a030207061d091503 68
    0x10040001d82941c03a02e1700008440a0140d00c419000441a50b01c14000b050980c41210640180410b00100307103540da0300c507400c00300084c05a01c0015034014030011180d841e0440481c400d83c0880c1c1724905411599000c01e403001842541c410b00c03000b00399128000074040000e1034000d20f90307002040800c95a00e500150301103400e40d000341c2c024112050001c5a44001c180c0c06009244d84903200303c2d41d191410b604540044c0000d83c030008098109561100708103d00d038040c0e812520031011290701b094581e24001030b0782d07940303400900030782c40b042020600c00d14017203000700b003520700780c3c002e1b6070001900d550f0301740c03030520710072245d06550003000508044424412010701c90401460741000107041c0c40105403d20027107060721a480c10b044546448072003260504010b8140f409280309103004210302115003001c2c50180902e01200106580c0090490161074000803c070322082e100f40c007034542d82540d8800580b00366141c200a540350040604900615244c1005103e500c6818030000300d01c40c500d5280845d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 738978920 1250 738977670 738977677
    0x110c07290c1c0c0309060507020607080913020c0a03120b100f021203040c031e170a11030d0204050108090f030904020706090c08210c0d0f09030f06020d0e0c090610020c06 75
    0x202043d004081401816400440c02c130203440a802c1441ca00043e55010800070b201d11000070301030000210708184a5512901020707050a0010070664880c5455002141c480c04948012404103100482050024019000d03c26250400a00380030030494203517416500120290440c00441c05642107165012180707901650080d4000c44a66011605614140440794106007000d001110000c041d600001c9103910032015846021040c1030b210450700c40207481405400520510074080400c28951a41c134a0b40507100b01d40c0c0c00d980c0c4084545501150680300c80e06a8100c0156400400452100303081c1034000784001d512420001844101719281d181088500d07030003003002078100104100144001070483c00980c03d95140842c40d003819026001d80e1190f80103a044284145c042d1507020540c0a024207030000c42d0412011001303805c081c81c0c00340003503102c0c0644011007460804005401200015100117401018015030b21036115a820032180e040703440080001c500c1401d80d450643e0302e444029 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 738980170 1250 738978920 738978973
    0xf04080d0e0d0f030e0a08060109050a051b0306090c160302010b040c020106051e1f110d030908030f1f0e06030d0e060d0507050d110c07290c 62
    0x26003440100600000c0050240d2032059108102d903060350030200302c044901115a0364503060000c03905901001282d5440300303076032104105000c3d0b0000080d1001903904100c1c1f0a01c41c2000412490f51054620034090f041c8e404075403800c0383c0610020341e042c01d00b0a000c3d60002c0078102c0741790400c000701c0c20f001c41c0c03441d000d282180140d464414587d602d0406e805103d240c4150340c002440b0403409c0101007001c0c0184a1092455004080c07106402c54661021502c0d000c01c0d00b821205c804075011201405035400000084418440c441c1d031590114440e00c2101c58040c0c1c4161024610b455151014410510280291041244042c2d00070140110030203000014030450b625410640350010805040c248882c0c0e0900c103100c1c0401d0307100080e45d151400c4034404443c1c1040050300b40c64a903c100d800d8012185422005480c14070040500075031100a805803c2840d4112034559444901c8000c40041c0228a04001641d0080d07034000c80140001030103250000c80c0403100b41c4900001c00c00108455040c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 738981420 1250 738980170 738980173
    0xe030403020616150e0a06050402040f06060906080705041505070c0e0108280f02060d0b030d050d0c020d020c04113010080d050c0a020d06020c1009260f0408 69
    0x70030400c0004404c110f5503a2240c400040200030291032110391a12180742004002d140d40d9400201159503540c0480d90700d80c0443c404000c2c0c1c44e207407407003d84101d016006800c0070454850000384000c2c4100c04441c01e4030100c24031441030604200c800e0f01c0e06e80103890708880c031150100f00801c2c0c481c854455036008040700d00040180c2a070404c40e40c442e00110942c0c07aaa01b400d8522032001040319802c1000c265a07040c0d4a0942d07929881c40200010138180c1d02c183e47c18068040c005140c1da80c040003030041c05010706c00c2000301015440c026685d4070f03000030360480507030007400e402c40061406911244020034440704440c9084030b600400419a0710703d000c0c81e41100031201c410141c204181015690100c030840c4046803490600d4082c81e510050a4641c10400070002140001d01a06000c1541d800398090103000d02a0303490b10340100a9041690007010318410b86001084031280ba026040c0c556400c09107040d8102c40c0e985c0080440e58a80c194201d0480c0308010000075080c2000082009010500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 738982670 1250 738981420 738981457
    0xb040606170f0c101103040e060405091b090a020c030f0301150203040303021005100302060c1b0102011e0c050c2e050123130e010603050d02031303060e0304030206 72
    0x1014000080c8400c500010164058201c01502d102d0028801010503011615608203600445084941c5c50341c0c50900400d40c00003280000c0d90440d420f008502404040f60305010316078a10082d5541c904a001d00c002c4100e16002020419007815101a45c000003c3c140261401c0300c030380e00e4180f440d40322106000003c00000010440000d03030100300c00a040a92020b140741a1550320001d50356200c6ca11107521955071007001c40c00300e40107140e1280085030301030401500ca00c1003400e000c2c3c55058007000e00c038030360060100005281d803062040343e400c505151036180c65031107288200380003050305203980c009118003006015440030003000322400e681083c0c18405014242c07418420030700f071800c0c04100f82e031604140040c0180f90480104150b400a0244001a50a1080002403043c402030b0702c0400c18034a8003070b40d0940740406400c1041031b24042c3c030407511001101c00080380d6034810005e05064010348442e05000240c1150054031000c10725100710f0782020b803030b500001d21540c0641e5100d41b2514488 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 738983920 1250 738982670 738982679
    0x9030910080f1308041806030f0305130b0310030303090507090905030301081c0f030b03011b09170a05300d0212060a06021902010903170301030b011707031e0b040606 73
    0x214200380c1c02540ba0fa040f4101160541d9012000d000c1e50003100d0a4030260340d0010f8040d80701e0b03449400255002161100024854200584150720415040016512010012504546010482c0d00640c940ba250318817152460318210004d08002c442100c25000c0e510b00001c1301d03510780c000d001030b0314024000b865595250082c2c2d6468100303611003000425924608240b2403942217902c4201115050402040b084400000030380141034070200704861445070600c0c2e150b0743c2d80c4100990140c131000380000391040c80184401e640e50b5901d440080083e4400c28600c00c031035100c40c000f4000c49002c10001c01010107041d01110182d0841d9610040459010a4001842003000013454101e0010355241c3e02242c14490003d488190750003210011031050340d440c0045920816a1500664000070110300f15141019030505a41c42848107a44840c0010008160303c2c500c62500884500001d0091500c980745550300b0700401c041e0f820100403540c0c04808140460603032040c0030710587c0300f0724000441300e0a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 738985170 1250 738983920 738983941
    0xd020c07150201050402030d1b1208070f0306150c020604080d030f0c0f0f110712060c0e010503070e1005070503030a0605090c04050604090509010e0a0302060a110702180903091008 79
    0x185012804684c106018040986c8001c500c400208a941c60300090010300090900f508585901c1c00420549524500d5004187d000e024280601d88540d10804485800d01d402c409a800310b0180c60a20308007003101544050084090894162010380b085040c540e4440d03010381000381d94110b00000c00d03214019886400c0c80e0744134006030080d0500745600c040c482180700402442d8000d8020090046410200309456010000c410041c10b8203401102140c0381803030b203c000740003c1800c04011407095403115100d5801a01030300d01c00d02a40da034280301070848008108001c140801d000c4148031081202c4004980b05200551156400d008089038030b518290034014010f000604080e1000801e00050045030703503c800311012142c9a20001c5103603125126254010030002e00100801d200d11401541055004600c1c18480c480c400d2040003d1203040300043c020b0320503002c0095110711070714040901001240c40c401c0c2c024003090126400e055040380440e0344c030341e80e551520001c40d10312010000440f00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 738986420 1250 738985170 738985199
    0x315022b021e07050a0213020d0e070e0c091f030917030f1014090a06081903090602031315020c04150e061002060f090a020409060b010806010e1c080d020c07 69
    0x2214001c00e032603c5590b8403400e032100742c8144002c0c4a90740303a0900030703228481038040c1c1302c0309642680c0c100665071a0a51040d038420051165000505a07040010640b00340c1038165448800041d24410a0801a0201c62404000002071600b4103a0358102d88000c15050100320745589040240150350342002829040a0000140020729601c040b050a00c00c071903403000d0680780c8080c15900c217101912242d40e81c0d00542026044048a8411006800c0440a4103d03000401d40d010707441e078041444c3c03078034403c0740c032807003116200c90041104007001c0100d03414402c1d4003031045400d0310680e159624860001020340380c107468070703094205e00c2010074040c400078201181c0e040102103808032540020a00301944401c00142241c0c03d0220401c00580b90706400d001c01000d00d03900800400c610410b51500400416180e007103280068018400280c265000303d28154080d400200001001c1d9600085000c490201c440b0896542000344541c1e102018240064032021380f60102130b1004070b0601e0880844a203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 738987670 1250 738986420 738986467
    0x3010f061715010e123313080d0f0903050405040c020a0b010b090d050d030515062b021e0901030b0a121106070b090a0308060a0315022b02 61
    0x440960a01c40702c00007840c1e820311466401e0034001d10307a6040e0780c0099241c078600d00c4251018010040084402610101d82d1074444d801c99500c5054482c3d9801c60581034201103079696201c1c212100c80c02c0105030320401a11030500788103400b0070b24054400307030102520800c16040380804d0700400c0a02c0503141500480000d8095480101044602c2e17494000c05400c06200d03d410444c000280380189841f142500880907400908695002080300001002442d0813072b420445024004e1a007046460541c04542001180c14201284020359030003420014400003102000c440e0700700b104500e011000c2030350031310008940072456107907807203d070000d400d494550018034855060000280b00d41ca81e04600b0103105a0844c4272640d07650f1410020400a100d501e201400040e9417604004201e54000703950b111041c840e81d030b422040c0d110a400d1100c8006140030050244025100741103068405d036024001070b40b0b0f5000a085080b46004140510045241c90341d07982d150001040300d0f26a800c48451a03a59 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 738988920 1250 738987670 738987707
    0x204031b0e010611070306110c03040609090b010f08340c060e0303090a1b0302040f0b03070602010e0a0b0903161419082d030117011803090512030f03010f06 69
    0x303e813444c0c0a141c490071031b800000c090b6640d5059000c203610010b0152030414130001c040700d0b03480e502e41d00003904103042403003079110260501c2d85221041d40b0400540d050402503232914507058980910900341c840c649400088050b613240d03079402601d001080c55060000080d119812000b0385400d044c0141c80c0950001d051640c820018000852030010381d480c45650400b030f110760788508040d00c1d4401c4803440c1e0310180d8400e0070101080a00e0003960f0060417880e03408c03800c0390291695070100360300380c86080c3c2c652011900305804030004a0202c0e40c942d80d01507003c0068920741701044401d1082c400340d1000c2a109103450b1020261112010440c6c5050401c10f00311407901c20707101ea910b40085100b262000710390180700c60100003241345450003d481e5143c0d0140015181e40c2c40d440c40d11314084075241c1c000015800d2000d00c401c48007600340c50110031505a42c5d4a04418245802c2c1700186074440d20b01980d6100802810313800320300c690b0240d8041c10710030007a180e80301e1a0880050541403048055982c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 738990170 1250 738988920 738988937
    0x1c05130533010b0901050a05041208091309031209020102010b0d0b0f0718140d02040608061005040501030206030c09060f0409060302011103120a0c020a0501021c0608030a02120d0204031b0e0106 85
    0x1103c3c514400d90300200c0c02443c00c0b9a07580001901210380303010700c1e4401b16160354800740d803004010418020380380040055444100d0108200c49100c1540c81e2990044d02250840c103007100020241e81181041e54010700000c112840356001040040c410303d00d0645800c9182e006104001041c040c1150700f056803031504140e40020048900c129900034494124a0042820046941c2d105c0e03245000c600c81c0c00800c20049295180180c44d11460201c0d15811a01604400450686850321416040e80d4024046a045a481d1051480654000f13940641c0c0501c0905c204107110040fa0010409007121880107d10300f8034503c00541000d10421119620350014401c2d44600340705000400c1d80200e41000109604154503c1a0700304080c58002a1580d4000124400744403c62006814806040f140030001140e88064040d2640609500e0707000603080202d00b841c002660f000540744100c0b1402c801131038580d0700e5a44e884460400c500082c03880003000000c0042d050362182007401440f103400c00f09013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 738991420 1250 738990170 738990179
    0x904060b0f2e20060f010f080a08030601020a02060706020a0915120b1f0504080709020c0a0305180a0929010c02190b12041103031c0513053301 63
    0x140214012600350402d4410034003203482034415824001e00ca4140c095407002c442201d0b941c00e4a80500300d48601640c011302c8000164010403403062401c40700200c024100c482d92503900ca104903480030344098114441c400100002d81d440b000103224051242c1c4005944050404000d029468560700140c0082000a401243c1c00d4204a9150001642903400035a03c3c0c100c42c0090986a491000c2c07600c200e03049810326541c0d5070000001c200340da074170342c0840310700320364508021042c1e220310b10350300405410208003a4002802840500f40c64554060140d588001890106100c9001130348403040d1a40c9808040000c0a5201214400c003902103503207041000312040003030200c829040c802805140705c00a465410150040918007400c000022130b07a80d500b400e00403820498003580e0a84480148900b4100c0a01c0d00004488003248154804100d0401a1400c1002010014408110b40c0c440c050352a001034020b01119124024009074001d0040e0805121951010800c02a95071210b07184018007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 738992670 1250 738991420 738991459
    0xc050d0903080313020d06051006081015050a05040803160605100b18010215040309060807080f0601030c0c0501240f050d0b1806010e1801051303050c0c0904060b0f 72
    0xb03504c84e00303010380000401d9a502c003080d5012800701c009002c485c0780c0b03010300005020b600740038400c603200c40e60b03001c032580c41e412040c1e100c0c3c040d284201201c0b110000c1c044403c81d80584050402c1d5482402c1a904043d40c44e943d4600355072041d201010916025850a01081040e1241076040750850f100f203040d0a003052840340700340c0b1a181c082c10f03041080c01c0305250968420040046084070409102d56141400d16001e000c2e14028050103012030310341400100c10034400d010075845221a101940400e484805c010342c014507606c5400302c00c00c000d20b210f01003c60008d000c2d10288902450448a1400845911990244c07454005241e04503540401300110796601c03001c0c0840c1c40e08214030780b41d1038680000f1145036840714150070b00207002d01c0e80005240329030520743c01d100c0c0300503072601e641e02c14010f020f050032513000310f5131300c0341041c048400140442d110704060104d015405045607440002440040d42800003200c04640c61505c41c4452a44c50a210b806101c02410940d5402816164001ea22 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 738993920 1250 738992670 738992677
    0xb10080d0905060c2d061e0a0908040302100207140d0503070602130e09030a1403130b060411040b03060a080102120a09060227040e07150c140105070c050d090308 71
    0x39842070001050413690242c040c40b901c690042040300e2904403003003d02c3c41d01d20200d54590003203414000c0d4400644864688a52024000d00010780071240740e0762418001e00500c1d0100c000d0b50454814440840140c42d00031501603422401c1d00241001c5107080c1d580f01382d88a01a80d8a070040070f00314850400180004141da00c00d540c070020260712070325418410489404d4a17844030b88a110160140901480f000c0010300205002e40c7d10548106843d03c2e62200b80c4c40240c4104407404060240b08000c1080480a00d4200d44001c0020504100960899a003a0800e80007c0003600001040c0445803800450180c02040d03000300039414115440d560000468004000d00a5652a00813240801c6601c2d0f0483c2d88040b944400b0004110780140407450481c0d1021b1558055481c04060035013001000692030100ca0485e4043e1152206940048075402c21000c01102d4070801907080e8aa03101080c02198800c802c26900c2040481d15800d00901d00005000040180520340350240085800c02044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 738995170 1250 738993920 738993929
    0x50f03101d03040608010e0f040210030506011413080c0a030c06140706050f0703050f0609070324030f02130203070e100e03010c0503063c03070f030b10080d09 70
    0x20480072540c1800800040c5001480e254040020082002908001d4041c141c45c00300c10ba035412681e9844481301310113400c0c0d5010f94442010040308003103d00c03036044103500043c18986800312240104401d40550050107100264920030344091000010030040c40690220484450480a14607100c206075040c0a0140004122300380700c00c081120303900421540d1035644954200620316000f5150a10424203507041d000003402d00e800b0031080f80303003c1071031030140800404004440d250306206400030603840c21075150a000070800d1561681d052160305000b035004446469103620035104000800c400c0030360501041e4414814000c00b16848071444049980556144071032088030b82e02603d581d44904507a544c50740c2418101da0110381d00c42e003d0f500485060b40c5040000d08024550142c18072030807040980180d0041100103110400c503d0300c01c1d112000b40550b406c46071038881032500002103800640c3c00000810a001d400c5a001d21048002e00e425405055459100075000f00400e919115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 738996420 1250 738995170 738995203
    0x5040f052502030f030103110f01050c0c060904090501090b040b181c11100c1d030a02090604110c030a0215060f0121020703031e050712200304110901050f03 69
    0x2040d440e41c0e00800c03c440266021110342622980c0d24a01a2913440100d04110f0041c0d41d22100442d2950080003a1126110343c00040c01da03401c010001d02c1055000b80c0b642c5503005464005280100301d080c85140d46a0740254200b60b01898507007050040c1d0480544130f940d141c200d0a00404255002207006001e208210910700d00a40d4428021140080802038000b428042d084404021031100c0d813200d2010910f903100c05128003d00311b19210034091134081c1a4158000c440351300c00620b09112150b034080001000054122844002c00c98150851a13440d01d056000150800c6080d8041120308510041818034812600c2c00b04003080044582814441c144440e10041c00c00f44141c040d503020641030004021901c0e1010340c01d00901500001614a8810005282c1e416002d0304030b0081500c0b64013941c44618004407100500d000800c400303402031407000c4c1004c040c2c41e000746041d030045006500403000401c01611702070030000380b0081a441607124080508401e1000d4402080e10804091400b5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 738997670 1250 738996420 738996481
    0x9150d0f0204022a121c021606060b0703270306051e13301107050a03061409210a0e03030301120507060309021c02041d01050105040f05 60
    0x1001c03a020f4040c4035800842a00040450501049025610001c901392201119070654101050311014403890703244030703145284c444034508810160b40051010f11400441c2c1652030310a038840208440040d0800d0710780f00360000341102817560001110340010030ba545100b60441402c0840440a2018440148031a403142c1c0007034440c5001c3e1108041c0c078800b813040c0c52018030f4000350742c0141100d1414112a10310264580d08110fa030f004208031040c4000c0f07091170034401100f004c16203181144142060300c91198038004211030301d07040c81e05c0d402103100c0d1a021070513214000d060342a01d2001000b5055642c4543c0607030745100c1114455207052a11030300c69585d24100c040c401c440c1c001030b03104500c0c0c1503c40040005000c080000510132514003440907280b80030784990b01101a030307454081c065807240c051a130071400f0740c5460480360b10780e62005200103900b528020400d61100850400520300780d558a00406c801e003850702a0303106900800301f04014510340035000c8041c074002546000c07141220003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 738998920 1250 738997670 738997673
    0x21609141b0c100c030e15040f0807150902040b060306030d141204050606090f040308011a1207030b0118050607060e010b150408070f0605190e13050609150d0f 70
    0x440c01c45400341c00800c151100403c200c50f40c04041c02c1e07000c008000103842c0503d00a01c0c074102080000b1106d4082000c81c3c40b03031712503498940350714990344415650804204640e10009101d00384559002403814004175400d402801040b00f120111034000c1d009490402c01c01c822540c01065030042c1c1d03002030a00c00c41c100d51400031007903940071b9164500c3c000702c0c1c0c1509100a0020025045100d40011038209030590350382c0b0407604009006880080100300400018800484054042c02c82c11203440c80c03143c14040101582880c4d50029074100011980d506406021540c0c04006010381000095000c100d035468000401c40c94418070350060b2000c1d0303a550004205c80f0080d0008008140020844042e4203488800302904c1d510601c1444100e103d0b1040005400d8145003100c0121040741d21480d0400303014520320000138140c1900d04082014200c0c8090840d03903180302030103e080c0780410002e4949001c805121701c0e40c0c40a01524151281d038402455581d640e003200000d0a41e20990750100c08009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 739000170 1250 738998920 738998971
    0x1141009080f060a0e0a02010f050a05210f160c02010509040b0612182805010b060d02040f050d0c030215041a030f070c0c14120d02160914 61
    0x2190804101805021510b0b1440c440008045000d1074000108110404030928159614184018000e002c1103002c259a0341d034074000c0b40038000c60106030405500e80046540814145814903c45041e800d0844090080005a041813298041400708078210030001d45100a06401e04140c030090400000152084054a07690094180c90801820090b00c9802e07034004030158100817a03c84a8030504180f05076503820740000c440081c1c0c0a1441c010086001c1e0b0865051a440d584600303990360b64864654a03010b4807400014507030224a010016112400c0c07003445441c6922980c4101d205035003003c0a10041644800c4c03403001c8130b038100c0c1c0d005054450040010700502842c1d00100c050203400d50210f21080490300154841e4400e0040c40040b81d9440c08155104160030f2300c0a040c00106c0c0c242449224008911421802e41c000e00100d1400495030b01c0e1880d11b0004a8000c0040cac01c111600480001007d411002405103d03c00303001022804051500181f0300506503800a4501480c203000d01c1003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 739001420 1250 739000170 739000187
    0x905011416030c0b0f450703050d09030c050111010902150306010f1103090415080610030308011e0302090601090308180907090b0a0806042307020607030207050a11011404080a0218011410 82
    0x81011b8030842c00d0100e6900c140d1544004d2205403218015030712460f001c43d100d08412810303aa40a00030004d0103042800454440b4013080c652001d07996a03000782409030780c80c40290480c848842c6440d030360340e14140000600107044180d8003010b00c202e5010403905400c001c02075449000040c1c0c2c0010f0340646039100910141c4007030f0320550b280c2c042c0c0c5d010721242038407824003d4142e07800380c0c880d4041d03640c0e10922004003507008c40c01d51604c6100756405100600c0c00c400c01a81101052616607060360301c1c1d44884500354088407195039894201469900c5a0800c0314000303034080854205103c840c0e10301628120070b442817450b500704020261b00016060385d541e9000324900d1040d811600200035581c5200819454103803500000342c42004000ba10140c8030303000b105d40c0141c1c40700140a09103895500d000d11101716942c081d0604c00c01d5107004900700a4540030b00020402c80c4d00501615801d4014400d00d0780391045000307040001400140994100c000c241c01ca0814180c8900c0108085408111070815 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 739002670 1250 739001420 739001521
    0x1805130c060207030516150f050c030d0e010f020a050d02030a110a11210702090a0b0d050a030807020a110909100608010b09090c010905011416030c0b0f 67
    0x140800c000301d155a800a0f41038260313481034045078005d0350400c950041d130301c02d140b24000c0d07080e0380d07000301c41c030420300c42e1a00e03030450882814428100301500030060704580040c03241c80784056030f130714206070303000400d02134161142c440950440c0f03480b0980000511030b100d034080a40183d500000400c418013516071012420351f001004094882c121400c009007055000709800d20f4070f20070070f62841c06468000500c0014140600242842c025882c0c0c04c1c0300c41c802005120300d200350364072000784495480344880302610a01c500e0250030710269601e409402d03000064190b10856100505081c002080c8040c0d050005004641040703c56640000c03a510388809074400b51602c4d400d0850001d580f210540010354000401c0700e45c491599100b50391960b44004c4600818000345c48250204165401a0b07000803180001c0038805240644c912003140403081e94140442c00102c02d80081014400100d411642003c050300c0070764a6400c0c48400d1038001c8408031940a203e084211441c000e140d49a406d000750344 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 739003920 1250 739002670 739002683
    0xf02040501150305070807050301052404090c12050c040e151216060509130e190f020f01050909193306050a02100c12140105040b030304180513 63
    0x150b840340141441c040b001c10180c400709082c5004604540c2c06440640d21800107640c507103013181e18180c20070601c00c0a0700544107c0010510010b010000904000c01c0601748142c00401e070940350240080900c2046291103440c40d2800c002e001904a207001210100e81d510007407080f41c0e480308000440380908507542c5651000c44682034810030000070400700c022040461380380c141241d45140560f80345c07042103112503000050070002483c00945a01c1024015586811039021801911b208644025170f02010345541c41044c60500031450000c6605012220030301e046801e00c000380011601e00140548502d0404003542c43c55000000194480c1e0040802207919580c02c0b288004c800840b1000e120403d04100030314200440e12502400450380481540c1d4000e02408080340620001450507030110001c10007000c11030104070109000b40001941015100034080d40f400042000319110b130290140690420b00041001c00031b1400802c041140701000420135a44000158015980051005045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 739005170 1250 739003920 739003931
    0x2416020f0334060c230f0a15020f0702040f021c060311040b0d060c1808010506011211160c0305010501030803150405060f0105090a032003100c1b0f0204 67
    0x41d0745640e040322807102c5000c02c19106001c020801c03115460240180c10124002a899800184036a881c4020218129520300940c40c200100a4101541d4440c4403409602840c40d40e028011403600d0203d5200c0380c45421854101c81c60700d102103034010f880b00640f14583d81c00034401c880c0c0054040700c02c0100b0200407502c5581402240c000103003104d00042e18003804001001c074003401c003442140803c4100a000741d07600901640d40101070030070300e0044010400080c183d00300b00e4a480c20840c01038044500045000e20300b4800042c1200c900c80c0e14010300f2803c2041d00403c500c6040c04075074114000700c0c1c1015101c44a4200b60b0f02a40c2d03594402013887d80782000000074004410095402010410450064500020100800c0d0340b0b00b0760302d1592080c01200c400e0415030141c80149281d810190541400c65583d4071003851203040200c85070316403060b10060312158a01031218610040e811041084085141800103020210701d0720790f17914801c004030742c800c2440302c56190000c0703083e07000f0401d105 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 739006420 1250 739005170 739005193
    0x816030f0e030a08090a1113061a04080f0616110102040b070609020a06030b0604140423090f030711090403090e090304030c050619051602090103112416020f03 70
    0x350b9038042506640019404c2022030908140030800c6400075404c0324007561101d406904000c02600501f04982000f59220400201d0a0112141d0307400104641007040e1034a01e0240c0040c02d011040d00000b00765000501042010f5008403000012051103290003408001d50081c61802845a40c000403689040400c1e80800c1000580080142a2080e91005086542c1d00d41c10381c00c1c0c6400d401d10b05d42c400d1092109000c540c04856001c41d441000400100d407a0303548941c01540b40c42159280e02d43d00010070108550309800f00000ca641d040c0c0100114034100460b00c0b010000101c080090f032184040d0800305052511400c000d402411031100d100d001810300e4016203640340e0151100710380c4088512070000740ca02c0c1a5003900e41c4981c03100d0414001c421110b0003200d40385e00055660b010006081c080c100540c64a0603810702940c8503001c1e2107048036102c0100014280d07100392094513024070145a5055201d29400e8400390107d2076242d10070804240300041e00c4504040c000c9825201d0403100d2038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 739007670 1250 739006420 739006423
    0x50303010e0109111303080d0f0906090201022806092105180612160909060305070e06030c100503090709140717070518060405030304060f0914010816030f0e 69
    0x40c1240d284103c00c00c00541d0b01c00100d0720b0350054101e0040b4840300b00c0c2c1c0400200c0c1c05c03107005202600e6140c0e0b00080c4109405041003c0314400305046d100d01c3c0d41c43c60070008650301003041d80191074241100c070f25020144030180e0220341c0d04180c01081551200f840b1010804441c01d00c0e00b921806c0341d01211710303030804c507001030076500402c00c40d03000c20702d14006034a11414040129050540c440e241c2000d6903031a080c41015072802c0900c01c1d010030281c07440c00035620016110300009944070700064001d00e0314045480340001c038046c0546100341c20010034008955903a54080303007840210300b8419104c0c1d46d00000142408403a900001c10710b0300302a05500340e000d15000c041d102c0e20b0030b62222041c51451100e01280c41c5001c072280c80100d0741c01c0054115080051090302074040009120b03915240e00c4401007810b507006035002802280c1c0108040f5076080d0400d01200240141441440c1c41785200000284803480161501002821002032051410302c6900544c680e460400c4051105c0c84a120f48503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 739008920 1250 739007670 739007699
    0x250f02100c0c0f030f080a1107060306030506180303060909190f030215090d0e0a121b082b03020c06100612050c04060e1305070504140607050d05090d05030301 70
    0x40300c40704001040410700c009910200c03c1501c0d04a04049403543e401d035203a840036884007030904140000071042289144040280002800b0307950707000f10740c0a2541c548180f4102000d410a0040f0581c007020540c031020000c01d490344908102c0e00320700d45842722245a4101030701f9035501c0052400c0100382d0018490b40300030540501c0e10035821a10f400014603e002c0b29850f00343d07414043d03504090b403c2e0402603c40d00ea4203010403402466035036001d54501201100340c0e511002120b40341c04074070303c104152200000280c010488038000c0c04100d8039041001120f401010071a880b081a81013001f20141d01c6981552140c1a0303100480344c1e941082440b034034029440f407007998001031003000f410b800260395018041c01002c1c5e4494103801c05060502c16a03080000340d1009d9044200c4103540c109408140c0281030007014603864559560382881440301c820210901100d00440081004800090780018180c81140036842c0c41f544035029a0001a04050700d098040c083e44004000480d5a001d0808003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 739010170 1250 739008920 739008923
    0x60403140304050607081b03150108100b030f0403170a0b1905150a0c050312012306030711030d020a0302090a1a04270504060c14250f02100c 62
    0x291541000014840c500c148021200100550001008030710310502800d855900702112002004514203130296550454200711101c54a05640c1c20b0242d8880d40c0084409801840c0140d200d54854200490000700b44405014808004e8440e0000b40905104104a905100302100306039014144014040081c01c903c640491040c1480303002c81ea005600894428222030300600000f41c80f041c01c0410300055007200e034003c020b0080503c00c000005106000400d10819928815045035050200350009111816403024243c00e84401c600c6096491206696011140d8a00902d400080d000c68a040d4000c020680700540e001280c0c9070f59031074058010b41224401510810001581d49512054404c001e80000b40349803030800c014028072034010341803094121480c0fa1002800c041c2c030b6800007280e030212030650741e003a92403500c00a82c07503001055019541c6190800d900386040c50b48480101c0020350745100000c0300c549440b10400890302d0303200c0c2d10190028107041c1c070032581380c40180100c511200b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 739011420 1250 739010170 739010177
    0x91c05010212221104090c1502070605040e0112030c081c1401061403181605100e0a06030c0c053403121d030a0819031e0903090314060403 61
    0x5111810080301d0b115007815820343c0c003444004548810800395040b40f001900203440391682008520940c850710001c1c407000034800a410070114001b424401207070400b034200102004200b2505080d40c40c40c60544102405249004140d85001e17900002843c0c00102143c40100d400714040c1690394890100240703001c0300b801504c416800d600003c01d800d002c2c1c03a000c02c1d0588620b0150070000c1003d15800150030342c0ca00e4410b64862905403504992004010011a03030386028881400d100132400950080303401c00d227400e06490303130024084a010f405500200359440210800305441032040b2034400f03402c501640e484005136080b81c554a108035401200c0010342c0600c80d198034240034440d00442e5040484241d1000c5401d004686403c561840c0d86003800d48915482000d68081c401c14586511620b8003e07640c0080764007001c0000c4007141d40006040c03808000c440c0d11864046840040c081e14140021551760138541034802c41240e0b0006030024604e0708600505160024200740900d0103500d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 739012670 1250 739011420 739011457
    0x100c020c0a08030301141f1b1a151c03111234050705010e0f180433020342101d030106120606030c0609060503010308091c050102 57
    0x1d000f580d247e82c1c00b10395011504401c4041c104c078822181d020303140400d002e060308a07003142d803a0800b5101034140c00d6400c140b401c009002c0c00724002d20700310045200a907150040100d42c5030b544410000072150103002e201c00d1304070340f2007002c406010424060002c001140c2c0ca0305040110102d4100002c000c0c1e0403142c841d50041583c05581d00800c0a0465100e00107240081c02e00c801181d14440e0301c480c160f00150040500210395854825042d40c07000b1400050800e03103058240101400340f9400c0580c030036204103c4448816000b4144505040041170002d0ba5948465100e541c000c02849040c000003075210b03032601d000704584410b500c2d01005022081c1c84200d00e503020000900c003292040300c01b1070020781e11820032110150400c0d6081c0c2c802000003a03895659008481010080c09003201e02c5036a98000740100b050088090014000600c0e000180d80c0c04c00030081d00724071040c08050141d42c40481d4039a84d80e80e410042c200003005d07611303901302c003030040307203400d50103900000c4c0d080701c80b1803c4a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 739013920 1250 739012670 739012709
    0x723071a0108070f09020705010b1302030a0501090506010903020418020301051807091404020d020406031b240813061107030f030c03050403050d022d0408060a0509100c020c0a08030301 81
    0x3d144010303102c544031841c12407443c11109100039482030000b03c9465494040d015103582c0e4602650400700140000960340b4602544074000302c44050704032084071403502c030612410766030112510050300d505880016070b00c0381e422000156510303032890095066007000300304030f10000740c0c42c100e9200c244008201c80105803030b030307140200303840c91550300b005408521f500141c050b29009544400003030028100141c9076860f41c4890020040b00c498050121400110410407500d080b44841c0e03640d040c1400100115041d03c000410015001d0001d0080388071100d948400c0c015075910042c20b00350a140341c155900c905207009819103030094031040102e480c00400c20500c4d030203409501c0c45568144e49aa290a040300d035164001c1d0030000c48004120708540c1044102d15641d9101100c20307020120098135540780000035468018020500540340d401c05c410300000a0000a052509800c1c0d01d0000c80c2c4060150812464a8584440c05031f0180810f1000120280080010b41c140d80310011822290102d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 739015170 1250 739013920 739013923
    0x510110102040f3023070b1909030f0204020c1006030b0618060102070320060c0f0f0307030507020d0614040303060906081f0507030207171201060809060723071a0108 73
    0x1c44e0384020030b90003c981100009031107001210b880c04091010124040e074030300703441880d14100c0d4001c1c1c012454005140729002c0b0a0b0030100c0c05465562810410003401c6603260741c00410720b0724000303000b5034007ca030840c0d0b5002c1c28840080f01102507113040090990701e0815141d0b041c1c094419034050b0070f03020300344003025900801e081c0c456007043c0c005100051640da50b40c5502000381c4416a105580b031005030660f039a400005081c40560100201003051382c5020392420700841c1105150143c0c0b080095000194100e01900c0c06a030301100c000c90500b00e40c0c00c2500191024600e4445047c104900b00001c25815074482070542d03d200c6000c22003e034688140540e0340e4000547c41e82c008204d45a4407812010716000640d000f101c5140c094180070080d528400c088140950004000a01281c800580900b9030700040c0103291504d845502c2e41400d4038500e84622018100c281041129281241007400d404040383c00500540c0056540e000181403079192010010840707507005441c60000071301e2650 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 739016420 1250 739015170 739015229
    0x10e011203020a02010804050c15190516061e050a0f050610050906070c051203070b0702031c0510050a090207060b100504061d0d2004090506010510110102040f 70
    0x1450b400500d0030781015001134a1741180100201c4e00d13482011182d06040c3c803490f90000c00c0c028807a000e01d8441060146c3c14503440c02100c0904208801800000c040750701d400c000402981c0c000d980007a40220541d03500c17259002c41401d00d8411401d200a001445400381c1c016900c003000c030301d420062078441c4070410440609078404480003820034400c2c0400e0345407800080104c0d038400c10703605808a540318013040e07540c000004000016000415224280980d03903405550290541c40035614281c403144002c000743c3c2011a030703071990310381c2d5000040341c81c2c082400f9000581030040030116802d03903440c210400395019000441c5c6550601802e404241031a03414190a07a215407a2a401d007401c00100725000303101450008100b4400064220302c61f240c0d600d225500c00e0080c420400380c81c1402070a4281d014002c440b41d4001d501d060410004a80089892415a50102c0c1c81e0074000804460032a6488074400064105501c000b80000c2c070510f80c01080f000321440e0f0140c11240111130141c1018210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 739017670 1250 739016420 739016423
    0x60804061401170c0307060f0e0604050406030605040b1608040f14010608030c01060602010b09063102090f010c0b042a090903080711030403031b05060708010509011a180102010908030f010e0112 85
    0x10702c16104c000c20349000352109d544141c0302502c407a041683d0350000506842d401c1d0310540340c3c2642e40e010710007405080c40348941e100700e00c440d01c0150011000f900501c00072000300041c00d040400c1581004010284175969985582c2c20001d004242d241c4c0140740c0c49030b0080554141e2076207003480000345107006029080f47ca1000900355181c81e5030382010701144080c0c400b03c0c82040040318892008024400c0d40a40851448140040c1c5501c0020103120401c3c0c0d1890410741805a0707250004002100d03c0c071031a52281d03100d001a001290742150700c2d9520342c05d50002301c02c0140760310004601082954050381c2500d002e0f99a201e25515140320039150081d00d10603907201c0f60010401800881d020350b41c09501e0040781d042074825031100c3c0e12071508000098484c0d800260a06004124500c0d040c06030718007628140001c94548000c50100c2034091199403101120140042c0142081c1da00039440450001c1e08030050b07903031700e25141c05202c000402c00d014541080032800700118103a0310b520507032003499 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 739018920 1250 739017670 739017677
    0x603060a1e0b0102031e07020306060409021e011e020f190206041505040509040602090102010606050306030a0b180109050618121c0e1f0f0b010801060804061401170c030706 76
    0x5001e1140302101401d0702d420128150f22080119003000040c154050300d042006581c0241c84507503e1042504011001d0402842241400440d9000da99a040701102e0720503104241d0541c84a03410050f19241c2e04000180c44041c0c1280c1410101070b00400e190301c0014110007501c03280b0494000c0c0300c1150100c80701c00b80d000b03038050105210050326110740d041c0090940c1045030519940d1f80000c0e04500088404503041c1c1d40110f065401942c090080001400003420b0450544c0303800404a80ea6020b250000340c4100032000105011100401e18010b01030a082e000307124954890428999609e02541d000060720384200c40e0340c11894011803025051007082401c80c1c50030b40210b4014101c8058001c9104015603900074007060030b8010840b0f240e8035441078411800200d00441000211100000390040c0117080070b614248981e2300c0140380d8152012414401000d0b15030303090000080135954031041c0e1a1a8100c0041030310805d4000c15170700344003e82d040702c000f004844189a00c2d1907203449902c002c0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 739020170 1250 739018920 739018961
    0xe10052d0301150302011809050103030f080f06060f0d060810050711060402130c020c190906090b0f040203190e0a12050a020c0105163206010e0402040b040f140603060a 74
    0x11b41c860301c2c24607054064100aa003116448108030400c48000f81c2c800c4010a10300c2c540c41c0d1016400c840610b90011512401c2490740c501034020039900d100d6265050949400040e01405550b101c0d800140038000340030403038a01041c50070500005090949900002c2a141d818002550000103080c52103030b940504003504540c010b4071400003610b124079548044d4010003c81404031780b01c03c203814140300805581c500c8114a0480300104940710340d000342d2816401e02c4200c0800d40c96079044503020b03d401b40c40040e629034900c135a01200e0b4200300d02d070440450070588108882c000c006040390310300e030050303c00c80d41c0c0050110040c0d4291060003440e101517001106800110740c052805055022a0700000d03107100c140d2951200c0c5150b400141c81d40c01c0c2907501ea0140b030600d03810000002c4c0c02450130000c1009504000740e4000315880100020300c00c50316a9000c40301a1155000007065002e4080d0030300030003041c080300c000454001c841d014040d114040010b81c0b0b200d100d00070310220070f0314606000c41c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 739021420 1250 739020170 739020173
    0x150b0706090c1a120a110a1709010b0105160f08070c050f010c0b1b21011a160f0303020d0c02100e06161103120c0403060c08010605040e10052d03011503 67
    0x9913400e0040809007020350701c00c00c1c0000c41001710020034100301c0d140c2d1901000e003940340040300c05a00203408824140c0c9440441403041c0d0700581162f071200343e0318440702c4210046281c41a048900f0002c0104800c6000c40c1c407004014550342c004080d6403040b521803400c0401d180c01141d410f0022a0003070b001d042800e010482400746030880c0700360184d01a2045203031000071545600d9114641014168003542c002c01049010300107481507280c0b0058420080c80c2016101c455507501d8041034000e4808072540c0c1d10f00381094001c1e070403034101602004051044569108020751684800b0b0994001c031810541c112540c10b501003189880380e60b0156240000c102c021000301e540c440c2c130000b4001188410000c110460507142c003860b204039104903040d07554a085140120582d00803400c0c1c0002c1c410300c44018052181c003c015282a1a1640c030303032042c030b9035448402800641c81540a541c10009041d0f000c00480c002c0c44003229170a1a05154401c03a200d0356060500300c030610544540b0304004441e0030300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 739022670 1250 739021420 739021447
    0x6061320280f110327031c0207091112011802041d0621061902070b01120c060305040c0b0a0e04050a0b1c02060306060c0703060e0c270406150b0706090c1a 68
    0x46800c070080c080390020031510307c5680404103101101c0000d680a0101008401058021904016410320203d810070380200746414401d44180507046401c180c140491803410307050360588004003c90b5072a44018003080c1040d41449009444c0c484c000e4000358041141940741c10354000088905400801543d941e61900c0d01502d03074103558131607036603400f0440c40c80840d8442d1400ca020303100601c01001c419400340b800095001c0c01c3e50242d024142044104804120f1f0001c0711022101c004402c1036035800c0b04002126500000211ba990140c90321050007101c6c40703254043e6000300c50070347c1e03c1c00302c44000c59984181074640e200c000794024010000a04c0504081740580071088500c800c07a51955101d41e5480183d8841c20308548030b90784500305940315440d21100314022031a9011510b41c002c2845115503821440007000a051203407510388503160041040c000706c0040c54024000794542442c1d107048400b0b000c26000507681d076240d8180208058800b580040e4400c1c03003180340c043c60205102c80f8a03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 739023920 1250 739022670 739022737
    0x3210a0b0d03300e0d1b020103150815060307080304080319110d11160503150415020a02030d0b1005160807020d0506061320280f1103 59
    0x40c0d8440d0500d0b0a020380b51403e1020800010341c44040419181e07158a0403910b070508082e2008100006c29411943e060a1904a48036154080c03a000c105880a00c03802200c42040e031b80900c0062041d800301c0030b18001810030050050104905882e60030f41e49260385980c030b0143d40140041074004100707042c2c144c6082d0145005801c03ca06016a150401d4170f50305003031041c84103d072004100803071902c040c404c6003400340303030580301642029000c0d50f400d02c0c0200c2d50340e020f040c0012000c4040303040400d050150b00f0120710980220501c0541d95003a42d0b1500a40300d8104aa003411828148204d070452460300b00c19000018035903a03031789810b00c141218004110403d4a0094480e10400c020713101c0581c07222844080303120302840060103030b0305192041c07040c0c00c0c0c900a0110559032511a00b1700d940e6251480041d841441003000704e442d400190440201a4400c0703900305070400558085038601a00000030343c02405590301c58031440e0300d07a511910f840c0d105100f418107822070080b60060b009aa4500e02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 739025170 1250 739023920 739023947
    0x105010e0702101806020408070306061a03070807180f031103151308071a0f062b0309050406150f021b1e220606140a110f03210a0b0d03 60
    0x15004040f40d05c0d250002264400d8104032902d8008406c140300b0b029541c010300b0000e021031100542c882d01040c4c10a401d034000036010604004c1c2180128240d1449500c0318080b05120445060203242c1e150744821040030544402c0b540d00711a10190009460003050040c0c05010082e4041c0d910303a80c044581245d2000568203d811010600042e008188003203001407184000f094082c1660520060503000d2400c02003805c0e1060400103503860a2544982c250300b0481c2e5544898141d81606d4034040d503907400a42c10190704207107040c50000d18041160b25000301a540ca49a0684000c0a54030032030300c1c0d5200440541070b412082c0c00b640401e04002c0d0a050001000e01d040120003a031580000303411194a0012000c848400080c00c03aa10145225600081005050000c0c0900c01107d89000383e004a00f1980705001c003c1ca40408512401e011440b0607641d800d0549a80340030143c60320a150804480c0c241c88a40c40c80005100c0c03100e544150720204030001c183c00c20000c0103580445009610481 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 739026420 1250 739025170 739025201
    0x9010f050f04060c1b08090f0d1214070206031515040e010b0310090203090a110f010801050f0a030507060302030a060501080103020d14010b04020403080408060a090206040b07020409020607050307050105010e070210 94
    0x2c1114105c01400da51107401841441c2d00c9541da80721404111000342480220352060303240110140001d1018110540651000d00f843c10032042ca4502100070380c041c0f05000394106030700008001d5040c040441c0d03d14030700390498208c444881c4261200b031031130140307024240c0189032400043c0305c850a0340015603402031803000c4000c410754443e40301c0802c1e60025542095a03521401c0404e0410640e048111022001520212103988445000a001c15410311446001e0b081184d9422003a403101c0088401440d00700d400c03105403560741d61004000f540111369a014080c50311501007182d41c400c101142c100e13900180380800f46501b41c0c03103107512180c002c7c0c0303000c0b659961603040030b6864030f45001500c0218020390a868072149001d00c001d00740348008100500c06441c0c801c3c00c43c01a035904007954181d90f83c60120075210710350386c400b1400034200450081d50119000c1550000c004001008100d00c91140d0020301490340e948002d204007c100780c4406001da00609801d9400300300c41d030b20102e8015011207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 739027670 1250 739026420 739026437
    0x90a0911040603030c0c050619120e06040b0709290c0f0105010b12090105072001150e16080928020901030602041a0703090e04050a021809010f050f04060c 68
    0xc0014080701c0780341d0300850200d52600e480005000c1b4035460100100810790310a0b240c5003080c8403882c800300b82c1103499070500110807100b01968020340d10a100e0030303002c40100c514a09140c14092b403088001c070303800f8001590400c004aa40001078148203848a03c8030007680d1900e00310a800881a0466a481c5106202e1100c1c060f100f42030034020750b0b009141e01e1819a51b0307100a105030f011141c41c02000c01905a04250600155507070003410408a282c15424007a10021002c11060240c840761212010882c95075074080b5802d85282000c45c0036285c1d04090320b806c0c46603100c1c140c1d07410104450314400750304907400b5529000000d440100441a1800310100e07200940d90024a4650f0300b82c0003a91a59400724003400b080d503403641400c604051880703000d0709005482d50000d090360350301e0140040e045208008a0200315041250021460740101801074045c4100500425001e0481c3c208440f036003085078003054580548990b42c040c0c0d0f90030100224075551070f100d440140040d04500020040c001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 739028776 1106 739027670 739027703
    0x30b180627070819080f0a02010c030c0e030606060c07091409210a050a11030c01090b010b0703050702100c0b09010606181511030c030d0f1109090a09 66
    0xb13004c1d03520104102d10b001d4160f401408002c03501c441022510780c2c07100c2d0701904800031886440e54200807000d0140001c6504c0c2c2013035041160150440d801190260504000400305100240300325140b036903079203000004a0b8a0044c425035100028014007107060b20502001c2070bc030000e00c2ca010b1040c10b0850380b05d015417260144a13400e2100004507841c0450007440340c00401791500c001d883d21480b2443d03039140078250001c0c086447e1007a000c004980c0502140c2920b41131070301a910345041c41c0c4990f090029a54403038041c0c0c420b000c2410102c100080c0c1241c0c6a0344140d0284002184e034510304071028220000c0400604a810781041c1c050080c21800040200b4520081c6050f4516409640710941184078103501c2001e01e000010303c00c00784280c150400d100962040b002003110b1500211180c043d4010134440310350110668000c10f05000d055008400201e0080f104900020500c = true := by decide +kernel

theorem cover : BRFrame.Cov 738848920 739028776 := by
  have h0 := BRFrame.cov_init 738848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 738848920 ≤ n) (h2 : n < 739028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
