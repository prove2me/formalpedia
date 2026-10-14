-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0327
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:13:56.814325+00:00
-- url     : https://prove2.me/submissions/ce113e16-8f46-461d-949b-7137ccfa8102

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 58633096 ≤ n < 58812952 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 58634346 1250 58633096 58633103
    0x110c101b060609110a0c0b090a1707020108010602030f030105150c010f06050102062a0304110d03020705090c03091902040e010e0709060f06090b0c0a0c0801091103060702100207110d 80
    0x40b05801d100c460200e115107651041c00d000740504000050b40000c09400242034024031201808011540c100020402940020351007005090000200d140070707a401e400a40b0181e00142070000001313846030010040341d50784d4031a403003401d2841c1e0a05080c4106021100c80500c51198108039a208980c7c080c802d2680208000c640424017600d41000245041000f400510040540302c10022000f103046815031500460054460303100e50351410003641c103800c0d00c40c03116000864125104201a0b010543e60142c0d00c1c01ca90185054031801f501107103d020898107000540d100c45903400e03105d02440d0109140c1c9100030804a2003861910401e403e6400c501b120302c00c01e80c0001c41c00d102c540c6550080c08041e00c001020b0302c44561070003400a04d50300f1180710fa41d4451000160710520f85500b880300d19215504484003901c05543c0d40c1c01300e0700a1004803404d4900e03100009001c09a40f4000c01c1c00c0f409004254018000c5082c1d2000c41c600a5220030000c035034130a29100224115142d624651400070302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 58635596 1250 58634346 58634351
    0x40501020c0c0303090105071e14060103120302130311030a080d27030203090105250f021206190f090b07020705031501060c20030109080d0606110c101b06 68
    0x441d0031002c0c41c02e5210303080300d4402e80041c4801001070360b01005444455800c0310000070281c54000c0307407031a17040a00d0f00143c00513040130352400c5107810000d04203048034860002d0030944050541c084040740282c0b040d0005002105208002040c9070400703091000c400101518030700d04040e501c202c01d81d404420140451916410318050308801b480441c7c0703100740e48401030780a15003181c4e4025241d103d0441d0303003818004017181d008582e01500302c0d11032021201d4010604d80c0b40840c10130b0024051440e808034031622042100c004191008a0440d0080b29900c0f05000421907800300714000e03220000d0003003829a41d176814034000c1104216960302600040d0040c2a00c54200828107080c1760100d00602e8038942c0745030040080c540d010b5070860140303070082002000b8888041c0b04219502e070040c0c507640e056003070a90010500c00f81d10001c101c441034104003008143d13981c00302610000042c140099042d0130174507280f2028106080000420b641c40c2c82c10407040c0b000c0303040c0d1000e0503484645c1918442d9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 58636846 1250 58635596 58635607
    0x50306040f14090708060f01030b070c080705060a1b020c130e16090b0105030403020a0f02060d0e0106090e01090c05040902180106030e0607030b060a140d090807020a0902040506030c070503040e04050102 89
    0x18802d11444c0098580e15010b005640313001c50b0042c00c40e280c10301c40240104401000220500c1c0b00d44590320317425130b07c1403915668400600f400c0b0340d40da2003030b5103d2491a00d04002d403130281d00d01031001403840d6000c2e0050401c83c0c070130604000600034801d011000c020780b5a800802000d0040c0404070702c500454490301c0c1140e0030702d00c40d441115180740521f41848820414000860303000110414404d03880240407a01c00c00c14400f040c198003440301c034005600d0500c080c1d1510990107400400c161181c2035002c003c10310222182900b0f0b0f0b505d0881c06019041901d80a04c50340c02d10b0f030002d20310103001420300c2d041c2c144081c880d082540d000741d02a02c0001d5540c0a8142881810b014640c1c00204030319003800f050104400240e082d00c101c854500c24000d02e07040101d18154140300f501c414501142c000c103c407100d60300300840a5400410120b10441c58000d01003a410300038800e8400307948000d403100c1e0079540c5426000b40154400401940ca600c0244800106007001894051142d8440c200168849 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 58638096 1250 58636846 58636861
    0x30a02010905010b0402030f130f1e05060f1501081308030103080301060e0414070810030c0b1b0607020307031101021c060302030d0305010812090d12050406140a090501050306040f14 80
    0x10345040960031700c41c0d070040040c404c00c8218103a8180c2c1113038203c800e5103130311a524a4005501004081d00601030003440c9008904c0094100d10a01894003841c240c494565800348440343c000d200311800c100446a100f0115a1944030300001540010818200c9501550139203c00c2000c1e00264401c076400c0000000602809501c510482403181d020b44050004501d0188a00004000180114108030011000500300900083c141004542002441d6400d540b81d00d800c24043d8851500c02c070a0f08440808166a402d0001c1c071248107100580c00f4600b401c0c1380303a03412074403030701c81c00c0000f26159024440048400c00310f1311314200280c4a02000500f10746184180740c10044600c649005052070507004110b16600461075010b00340e100345641d44c2d5a240d080c001a00c1c140700800240860101110b07081141c0d42002c000e0007a21101d03210410b8800c082c1d01951300301d201e07120780140000c0c1c8d0000c04001c90b502580c0a1608984010400b0840c5145d040c2980101c1c0c008200c403064650b8400280042d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 58639346 1250 58638096 58638101
    0x3040f06030204050603060906040b0901031101020c03070e010608060a030c080a140613080f0c010203042306100302010c08091e01030605012c120303070305070305060f0d03030f060503030a0201090501 88
    0x144036504055082070718040004800d404028801801071050782c00040042d03445038001c4c040810020000c1c0441d50b100d05100e5484446402e8650262007443d2580440b4600000c085007100c00c1d4005e200f00703980c00c00400f128051000f602041c3c1009031f80380c0120009144160480141c100070f40101788240160415640b1406d10704085a00b5070048400e00c40d06506052840d0f000c150040c90b01e903540d07400001c40044600c038500400040754408010300040280301d41017001e0001324020031742c00d076000910120740c4a0708151000c00c00d40c80b08400410065008010a00125001e80016400d01002034003054410000424910900c43c028007008600d681510403d0f01601081c604a81051020705868a0700d601a43c1070140082d41d06218181030341c0e0703160903010303219150003d60f602c80c1005c100280c094841680c0100c0480d0a1070005007960500c68404500b551b0001c240034a1005903132410341c000c203442c000031041141c59034408608d0b9141040101007c1401e40d000140c2e0003407609240f0708 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 58640596 1250 58639346 58639349
    0x30507090909080306100212070b040b090105010e15060403240c1d040e030d02070b010f05010509090406020c07030507080d030b03010207021f02070e010e0114010c0308010909020a080a0503040f 85
    0x18604550384000ca0003c0e026603520000541d440e400c1520100810303850980034800941c000403000a00c00e0130070480b0703228680500e10403582d2225a4462403861070a031503003400341003000e8400200081080c4680807281e0b40a96002e07200924160316501e6409800c1000030414103184e01c20f1a141000f903059204200c818181468240b401c104406442035007005a500c03550b200e5900d504001009110502c225445050392450865032801d403403500c07100703542c1c0922541525101c1d0303040008055000c0c404541d42d80da030040c441501961940ea03200020b405c420021681032040078404400100f007084090701804000c0000d00c03c108241e10000c040e64040030589001e40d005024200058483c80942c2e003040b4000c1d204103d0b18010320718101d10b82461030780300352070100401000107021180c0c50040781c140c0f4099500011401030080055030000c6088000a00140408004000300c00c0c140e03001c140305a20040c002d240040e03072502254030701024208151401d8100050800c00700748021010790 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 58641846 1250 58640596 58640609
    0x50a051c05060f040c14090301060b041e0f08030306060f09030a030203030a0f09080a210510050103050903070201090b0306030a080705010516090f03060515040906050105030d050405030303012108070303050709 92
    0x5004517444009024000408100550390000324032856a55000e411510140203203520b07440e2910b9980c4588403c0303070100000030440340c2c003582c00407a072460400d034a4001c0d602c1c020029840e5845150078803820b03600c07403031020042d11420b01042d19240c2c1c0270300440c1d1500c0d00944c000d64a074103002c0d083d0f100f183d41551160918520341041303940040d0a5506a40c2010b000707041c841d1034401d82d80036130941a04c4480c080c40c1070910308010000881e1000307101c6402e541003070340c0030882070760341c0b0748420b56a100310103019001c510780d001d081000c2d9004000441c0d00c2813003c2e059070020462541c440d034403508480390032910369446104202c076070309521005d04d60380340c0140f07001030202d490075074031152925880c040980700ca522500003030300c020110190240e102201810400c69006a420b001000304820300900748240203a15004c10341a125000b55803d603a4005c02551070b50f440d056200000d00500400c40402d10b0034000c000001c1405031000d03040d100e010303440100c0c1f20b04e001d10000304100981d03001003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 58643096 1250 58641846 58641851
    0x50105061804090323070606060e0603040f1b0605040e0a0507080c09041104060c05120a020c0d05011104030c06030e061e0403020c10050a020c03030702030d050a051c05060f04 77
    0x400304507186440c516020802500c001491114500b42140c07000008001c0e0083c3c1341250420540c000c801000a20245000700c00800c00c490f12601c007281c01d400c000d806030340d02035024004100480c010001a060451140700001c2401c0010100c0c1000010640d0001011400105003080740244581c0704651102540404010034074011a01404d06403000d41075414a00b404150082d1540350740e071002d1011290800d0b81e40d1904c1e902d401c005c003c00301800c0111038901800d0038140000d05503500751107240c28030360040c1c080c0749000000d205d01c6003590309094490b5902c46414040380d5180100074800345005044910740c03542444030280544500c1c00070b4041c0c5500400401802a1a000c04400c003482e2851181c0703996159800d0880c54034542c024019031210032403d8150700f0325001b03030007400396581ca42c00b51004c01140d9003c041e1240548140a9059040503200b10400380c85030300142131407080c4c3c0c1445410401d603891000d00ca40000f4004102c03ea9071f0b5404e02c51a843d01c80c400e6070038942c040354107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 58644346 1250 58643096 58643107
    0x11090105012007081b01030c0807021c180603020c0d02070e041e020910080705030319051c09150f020304150b0f18040b0c03090304150c05030c0d0305010506 69
    0x8003140410001c03003044801c9030001010340c40c000c2c440c003c0180300301400c039507184d88008000340907040f034020703030502091505010403003190180000910500080e0086c008000100d50b10340c1e40809450704030700070001c0b43d034420030b90240d11050490192440d5940141c5401e80206101e26002c01d203510300080d580084400c00c18507a01c04480d5030b120b54003070b0a042c10007500c908116180106008025400180d010410200c01214407404044030054004c51700c00e41e5803081419200c1c0710b080100507102180c0700c50002c0840c00307200140b00c1501c0d265140c2c00c49071202041c83c4c080f5404000d00302d134051445040d0b04d03c0b00c1c079180100424000307402c070114a181440c1e41c40042c0002180e100442140d141c0e403540f0625a208000e01481182c080e11003200c81c0045040c05c030380b440c4100c4040301c4d0109168085881c100c4e590341640d200d112514015482d0500f4014186e041c03595944203041042241c42c0c41e140010800d00c0a4185207261100030b02e42c032510404060241d40058000c82d0140806110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 58645596 1250 58644346 58644349
    0x15010e0a0c090807060c140a15050c0906071b1809050610060e04050c0d0e030d05091207030c020616030807030b04180b0a06260c01080609070e03010f0507020a11090105 74
    0x52800865170b250502003820109841c0c048252841d28010f2492030203003814100600c0b107009085003046e00c448074100166603034141003034214001c0050050b080001401000000b80702c04030790301d1001440c000140641c07907803506c0107401510b074000a40c4100f502c41c1108000c002c02045165080038050400d0307441607060590040a148a000a2038402c81c2c68001103065600c07881c7c100e914034212107038284841d03039000103901da076940194000c08800c1c0ca0200002c00d03001000c10081c1005108000c21441d28540d51003c032408846594240d038040c500f085240440381403c2c04480c40b040c803e0319181c0083c079105802608582c4905001802181890f04049100320f1340e8034081035240c1d112106030700c80c0d12203903a124010306488d000044c8440c015800722007039102050403903403144141c60072600120700c5071004440300c0700e042d640c41da0414078407004581c9031401012080c0f894030000d00005411414881d000c8259007040d5144409604118402070610070034909502203054141d40307800055140a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 58646846 1250 58645596 58645603
    0x108040201120f06090606020a0b0907032a090914010c1718030f0409022d160602070c060f0908010213060806010513090605130c120e15010e0a0c0908 66
    0x210410190365a81e01603503030f0b014440d48202c001e0300c0155000c0025580791030300030395511100a0155070001c0c4480019009100000d0b883d01501d03401141c08050100c0c103121081c45101c0d00b042e103401c070041d186001c10f8209440c82180e411600807081620380082d540489da017190301c010034000421618600034821140340d885600d412180c040206050889160741e03250031406a0000c040c20f0b03600004001a4510880d006001600c0d50b488200e50340103460403039044030003681d6140201d00d103004e101204c029411500385104039070003040094502100c1e035980c1c92696036070b0b41040c0007081b0b0b0034070b07013022041d07000f0b0055000d040a81d00862511011044a049c3c1d0203051017080104200c840020720346074854420b844622020780d00120000b510b4401c0900a0300080c020305020b00c81070344030350207040f4690041013543d43c2d01c0e0300c2d016203521150000340c000e424a483c0300312842c8151710a056940d0a01201c80d8000c182100e00c090796410801d000a05880b9007038009010866880d1090041e40c1300070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 58648096 1250 58646846 58646867
    0x604020d1211070f03170c07090504020117191109030a020d030212030a020a1b03050702090703020405030f060417030403090e0405070b030c0a181409100503010e1b0108040201 77
    0x124001d1181c0035000342240c00c0e0040c0c05881116010314075000909110100c40c550540303200303448440380c0c50700040713000816014070070b0305812550156404010080c502d9114581140c011700d02112500700c008003c00010300243c7d14814800d1001c10106510b4070b503842052080e0440030020b5140902c01f200280d41e8042e01c0c4000b9200d41d400c2e4100108050003001003044004100314441e841f4680500030900a4010341125003719201d016507520011042504c81450f552644981d81004419001d01a010a0040004050650030840420240d8080201c0051400042c1c02004586000d04c0e2002d036a0128412402c8036000c14802d0100090700000f0324016500705800c00c030550354032810023528104003a07020b07559040c000410301100c400b202004092244140e12501005408124181c20002c2d5921510382c0410700513520a840d89004841c068100c44000c0244030080e40b11000242100d038985240b1449070300112082101d00e02080451007501800d0804145601c4e1540000c1c2866148 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 58649346 1250 58648096 58648103
    0x60a02090f060f090d14060f100b222d0506030103030f0c060606031d0607050d0207050718060303080a05040218040204090c06050a2a080a0c0f030504050a080604020d 73
    0x883d401c10041c00201c1960004003006004500642c401c0c01c0186901c880d003c6001014001d000c0041c07501410251200d009018940340500d0042c41d0001d4030100e904030807005146102050500700002d0307034030071031100034042c0f0607581d0000c80940722013815140b090580b4a40302d200f0b42d60040003182d803900c09603411240c1500304442da9074a8454100c032038004040008005a00d4180082501581a030000c2c00540e4842c005d90103481001070519641e0904942c0100022410050541c01000f1600075128062282c0210b40c00c1c1500d42d441450003c0010003482c8110b80c1c1c07004108140350f4400107498016807950310030820780c140741c3c000c200e1290000c203510007146071040118003151030f15480180c4980d00100c560701106d894801c0202154800009000080d2084460b0602c44001c1c203102c0c80b44a1036107200e801410406e660b400000d801a1a2030014060207030813000c0031820611000c03408600c6580d90725030f9141440100300c01803d150300709035100d5004601700f00040c0c50b2170302a039120640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 58650596 1250 58649346 58649359
    0x32a021c020d080c01020d0c03020304150b060927010b0c06040b0403091503090219210f08031602070905060d0b22050105090f0a0308070f03020d02070f05060a02090f 73
    0xc600200e000000d070020010b012a00020b44600402c2065003e0200f40e10300c0d21040c8040c0a800f2001c8003640001d0b18098000007908901e50159203959001e0a91200090010f80c1000145800a2143c4c01c1c24612000c16010001048540d00d15045200e4050b00750100c206003060110380c40f071035031240001c10003080c100c030b81c1010805050155040100520f54064000b030341e4582131500034080c00f5940c038102d0207110f0b006001440566508400c409607450120064801c5c41f6031031030901c444c03070048000d1b01c00d000c101d08502c1c04102440010342c07085841c405103807540041044024600005035201c00582c5280c9824005190f03525100420717100c0e04491024004e0701ca11a070b2248039142180010440800c030a0000100141074011600c101d10b81016101244101c00302140c641c4020711000380000c512400159141c2c0c062060a64580d44070f140c0103050200c40321081d41260311165040e540500c84101a20400c41c08224090b40b1500c2c11400303506280c61030010514103092010514030501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 58651846 1250 58650596 58650649
    0x403110307030f030309020109170a020d081207090e01050103050c0a1805040e150c040305060601050a03061d090105091203011809120302031621020304030e03060103032a02 76
    0x40e020032005000c0c5802c61440907801d005850080d005281054049022078100440058844110f5026054402c03401c8040d1020f02c651364200107080d605035104464010092001c18000d400c0d4100c414400c1c80640c881c007510900780f04a55020031030580c040b50400d810301c0100700c0740509400948040e13600b01c0c10310b080e0071100102c05040341030309904104c0e00245400c510312a03c00000030035510920380120341c5092900d820418001030720580c00f010345564405e6000c0340305544a90020060304407186070000b606525103848091003125055a0017a40002c4001c0c013101c800284141a008032007840107107141d81c0560080300560005118444568001d010380709000c5ca0700341c114014507131b40042d05803110780702030a0240003908103550700451007588545003143c940c0286030144685510002802035200d400003050065400100128100142c80e0740311001070b2810005240a0f510035141c0741b10300c1543c1480400e59081141c11401e401c0040c008903009a101c083c80301038040019a0050407d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 58653096 1250 58651846 58651849
    0x5040c030b150d1506060c080708030709090905030702150c0703020108060102150f07021203040b01090207020a0914060f03010903050405090709080f030c0c0126040203010f0f0203090d0212040311 86
    0x980340c1c2c0241c5030800418865081044001e85911000780d01c81c01d010000e0903280d039802c51758502940001044d104041100c8008540e80318003a40c5d001c070080c60207d0010791111120003d03284461800c54040d44007049a008601c0c0c0f41301c0c1038100040d440d8003281024031400c405a520740c2c4a100180c1440040c0d00402e13907030791003400042c540400300d90700030b91f04d401e1071400c40c06441d004488200060007108400102c010404085a000310b401c042090b5040e400d101c04440254000c803012a8000c4d0340c0880042c0711105d9010325414403d11882d80040d0385040300174040e02d1602c01b071a4601c2641750407c102c00080d0000169400e80340f05a480c11000d0b41c03048410340e10100e8541182c00d0902c81c1d9080d241400000000030410056201d017907940d40d081d0840107503a0082c0a043c1134080d200c040e01c1070410f9405a004040d84280014008620402e1004c003500440d40c6540e0754880b401c0d000410052044c00805c4000d821005903c0202a005800340700609140154040248031b81d0078181c4c3c01c5101d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 58654346 1250 58653096 58653121
    0x60b030c0912101811150a03020307030212010b090a050402040f03030e030109050f1c0206270705130902041103090316050a020604090614100207060f0507080705060405060a05040c030b 81
    0x900c2d0454100541c0307404d1114035414010100b422901e04200f84107054590070088085d178113040c1d542c45000e04146003246c00764041d410043c00442010340c00d01a03048206003003174070213000b044c002d80b0649e40c0d045840d0502c860400590400c0d1701550040004000c142074166642045903003515016242c0401d010009001d804004000341c420710030038610300f10b80d44001c504a0b0301c0a607070100b084108100c051050b6124281251256082d80600c1c1052402140003070315414000c810300103565240340c0350720010f200380e2007030070342440065542c4c640c04046007041d1007030107100e07011000c0d680d0031803502e2070305282c0c0c0b42705580320700d08080c000315820401c00200b0440c00c0041130b40181415255a168a490002400244540e054840b510f9100c882141045050320810710155030213031078114282141560b0300741c100131186041040c00c11072200801d10b03403030182c8503035482900903001500705414601d1825201501508187d85401c0501c070008454500441c102d0303600000b0744c0c400e50754250060350f5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 58655596 1250 58654346 58654363
    0x40b10020304060f03180b0601032a090801060e060103021c02030c07110d021f021504060e01050705040608060d17030f06031e070b0f091f03060b030c0912 68
    0x20004604a565041180c001c00604181d4100fa5196401c54104042c12802c3c1c1e2001940349460148039000c1401103000ca40d101076000d41c3c10b04011410540c6040f407040c428200900896000311905045184254800740c41801030803240020301c42d2a04106001c081c0c0e40e00580004d040c56400146007495240e81c0980e06c490304000c032001c40d1a071400340c944007141c0c0e00140003203414a80034000b10301c8616168500581903038000c1e1400240d0700100d0101080c0034501400b01003075104000710a024046103800b02485688620004a00c0c0813022400f6400e45802030000000e0240a0105012481d400f00d001d560110080b503525007407406034100004100074480020f000400d000080190a4580b260044d0240205408031075101180005004803800482c408142541282c0020001420142c000d00480201103013a03a20300040d0070300141054050300389a0550141c540c1114400d542c141c483d4100030030413900c20501d14627103484003400318400d04100b64480c440001d0028800001080b81c7c95 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 58656846 1250 58655596 58655599
    0x20d140f21030901061502060a0f0507020a0201030c030b04090311060a020913020901030f05010b28020a081e0403150e06040210030e21040e0603012c0c040906060e0a0606090b09040b 80
    0x304140d10f06e0900075150740044503c000030908121441ea00e1400d1482400e01c02c14055015041c840001d0380110042d02c48440399134205521902504c070a903441e482142c0c0c1e4140700341c5800c0c02c0d46614061113410004018541095140f060040710050b0701c9240e01201c24001d605030069444240c0300059005200c500e00420700d031860440003140304040c0ca401000364040051040481c00103c3c412000311130785c0017201200680004a03e0340005500c4000b400403109540b031404103001a111000403250403e51060b5400900b40c0ca20303d046201600c11021030341c6604010705501d107081c1e004150b0b0703103030340f60024400c00d6980c651240042d90140007808209004141410000c4010f1200d0b4880f600079000d04801200d404c0d009c56824901403144031041401c2040c082455205101c0b03500d1141c5a04070820414040c1c040c0240603a6105c3c403540740b10602c0b5200000c0d455003030070150040220010316640c9a1440d250041c42811340080c942d200b120310602a00e40d8640b51980814007500764052401d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 58658096 1250 58656846 58656869
    0x807050709050618090c130608120a090801060b03060607050327010905030102121302030703140319021615050f16030806091909030309020d140f2103090106 69
    0x4680714240340c01440c001d040c1103514aa00582149601c4480b21050f43c04858942c001d4290b103c4a003059001d5000004a901d0001803841e034403088107040120030035041091082c001150700c4015040047c0d01d028140d070340020406941400105140380c8405881d16116680119803c01080000c00844142ca61882d5010030002d00c034030074449c1850780c006a21030100c0d82204d404591410b052080e07940151075074500000c00d4542034080318150035000001e0fa0140603404011000c140290794000f03401e01c1550041d507962007042c4002030140010f2094a04641201100005140701504003e095130650040500c3d06080300c581501c0c14400d02c1500f045185001c14000601402e11442c04211030281d00e40040c9a81c903030041000c121000c85043c4110080c9091106409400340d11001400b4440d0900140d916415000114107121480c000c40b508603400503010000681030240302c1561401900400000f00c404034006400c032183c0000350038070400840091840c00003500510000d06000c583ea = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 58659346 1250 58658096 58658099
    0xc0c03021207030b1509010b070606050d0c05130c1d040e070303081906120f0f0804030f02100e01020705010e0d29090a0209151503010b0901030b030d020705090408070507 75
    0x11034907070803240720694640c0c8802d000503101c14800005d65003400d50040800315283c0c201200b204050300188401c0e107401da910900801c031a1540c0d0588100b140c0101c0b00000d1041c5850b080041d038452000111003c20300300359141d41025044005000c4545070070140703024424410022034010503c4800c2c8070250b110b02800041810741203298103000380590a844059a1452442d5905488051141e4049440803590b810701184580000900d12841942d60340c00d6684241c4404602e500681c00aa8502141844d10000c40c58070982c0807078603e0060810f08a940392510020b9111030300d5100c1c0701e0501840403280c600707507541e5000010b0302079403280300d5480c0384410400b0600d0300707a02c055a03030b031501e510200800d80702000028004411a801010a4456680e5a01d07200c00c42c80c0c2001210b030040c2950902001c07045a070009180a00341050580340c0b18005880010706a405080c40c080c000c3d00032601c0c01c0d507250303404503200040c0d84041c0c64140d025201c40c640140c00e845102e03000741103070280e484e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 58660596 1250 58659346 58659379
    0x90106360e2a04050106021f061203090e0a0c050306060f040909030503060a0b070c03060b041b080702010612050604060b030a15060302010e09070915050405030a1209080a0b070c0c0302 81
    0x210780084001207440300c10780c0742d0850140070841348203018207400b5074032040d01c1160750040800914049032400001042c2941d4500100c07070041d500140032008101c043d07000b4011582c1c0c2170300c0f04c2e0303125003030030400d21240d04100c034090003500c80504003074000c000010b2030540c3d403600b14003101d000b00300c203680070043c1ca10a420010265002540d180b4490701e1070200000d40302e80c500c400d030f510785030308041103810f41441c595500000b000b441c0211030b0400d8889401895000309090300c80008212074445403e01d10700b10b04000c3c2162610340143c400038403c0466400850000200c00f43d01692146d000240050a0800030b0315200e00984010508408180940a98012500100b08480c0b00380c8540a521504400b0080220b81c00c5442c10002400050204041200440f01c001c005010b0b00304149001e440e000402d00b0081c0d80036098403180c00b454403080b01c00b94032000340c3c0001c1c20000c0c040e04071400c043e9124040224050804010020070394020b100f400180c8001c0402150300034040c01c18501680c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 58661846 1250 58660596 58660633
    0x10602030316051206010e0d1e0b0f07021203070905090a09060b01111f020906040b07060b010507030507110111010e06010e070c051002070c050402040e09010b03030a0f121112090106360e 82
    0xc03001c031002c05a10012170011240b03020307072f40d02510309a0040c05e02260000355009494100070210300400940d050001820384600c200c0d1030080445030004901d180090400d4820b031142c2c41512410417140c0100c0d07040186010603030420320380148031420800c10382c030104880a8000d000e980d944c0b145000800007801065200200031716845648144003410705ca40041d43c0d24001c001c4058080b4404212150004000811746032808070141003007813480015114160031621030b0210b1340003035030000700180600c94003408183d501c0805450004600a06961059152001c04100c030b41d4698001c5a5031302009010090400545405003086449907a83e64402c0c082c410180d03401c2e4115407038111146030324200401140c0080400781c60351802414003103400c603564900007040c408441d0b47d65088604000d01c0c0130080c605e801e48240c0c429401d0800c221100e085a000b40e21081038200030b011503041e107000d0960801c9034411601c440032489070340040c1480c0604030046142c2c585010702810f12000841c1e05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 58663096 1250 58661846 58661903
    0x20c120d05010b070b0a050403020a060c0e0f06040b040314010b0423070c020609060c01020c010507020a02090702150601030c1b0308100b03010e040215040e010602030316051206010e0d 81
    0xc0001d0100e642c0c2c400c8080803d106511003d019014401d00003640010150040d43e0004e00c01d10480349002459281d5900700d82c00001e00400180b17072078201c0307161443c02e10070752003104000310303a89442c0074600001c2901500c19407000910980f880000b80c1a042020351212481003000380050124103071030008602c09030f90a0200c1c450a180201c0421103080c4600c180b90030b143c0c0d000e000280f80c403589000304021034200d1f1140204940d000c208403514840c0a014450081a040e0000c01d5111890f00c1080030300d0304010300c0d4404641c4008400301d42c282080d029140c1045080c2000503030700b40070280407280054100c0f000034110802d411060308050b4402d60141c41004071000e0b17040d0180e00e404401045110078032403004c8035040480410b001d460710700301e01202e100815000c0340c5002d0740d90010502c22202680b140025070400b2041020380058003201094005203803400514281480e017102e44c0a00000d4101e904001e592400b0400c1c0703440b020469413500b600040314001045003c0403850032108107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 58664346 1250 58663096 58663117
    0xc080304080a17100b090d02040e071521090f02031b03060a0b06030115090f030f20030a0f060e01060801051b030912030c0d020304120201060e070f12020c12 69
    0x141c2d02c0b2110008143d40e6214015001003800002451400c411078000c1c2e003000c10115806201e58035410010781d82d0f031040c40b8000000c00042c100c0c0c1441d00e004a8075068090700c0e51b0b41482403ea00c04aa8108510665000c100588600080750f0800d8208040f9401c0f40b00e03802074051042d031200d04048442c000512a030118100c048401d16a00c80260780213441140711801e4100d0410300040c84040c0800c040c12085461903d0b2060120f6650b0a4a00070052194000d4174195520b0f41d900f070601c070f1801c090500c182403146400c4240313810500801d41d5400741a50292084a0107405941000b9241d04110003240b0b0500003408079a840d4081c2600a1105031544805066581c819002181c4010140d0344280000c03009000316040c816206c4c1c44603440185a0f02e01c0d4642080b40d000c0041c120310146000d180116409840b501e0b01c0300020b400c56040341c0082e00c20947e41c02c1000000d940c80341c0311070115502813400c003c80c1c1d10f804905a01034010a40000c009009400d00c3e88a9040040094042c1090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 58665596 1250 58664346 58664357
    0x909010b030f0d2a080f1306030605132a270b04050d050703020d120e030a1e1511032406040603090201121401090b060301050603160c080304080a 64
    0x40d40004580e511556440100842c0c0300d00c225020701c02d0a0640c0b0b5100c1d11007011101d86000541c1da0b10740c003030780c010800b00c50391080100c4d03203004a02c0d1040703200c0043c08049c1020000181468002100c0d4001010002c09003911303100c44c010203520107852914540701c543c44050b400c0c2c0b0007550140181203c08100c5043c01c06c541e14190507113200600b10801c5030280003c00b443c250903d0203201c0e24043d0300300c0c145c1d4280300d0300400000517150725038090803850103040b90311100744003500003d0091500e0300d11180b0a034020341c056000303d440f8000131100912521b015007400c01d524600b50890300c00354660016002d10f0035003039007480d092940045114880c4800c052044850007007403104803100b500b10071500f1074007d10091041c41e002c2c2d03002682460050400051860b8440904001e0b25030005da0040c014190b00010003a0758058010080072090448029045604220201d56140401002e1030201e0390200d15181490b40039a0b204000141c000761419600c0c6402d00f0a8010740c1d0044242000050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 58666846 1250 58665596 58665613
    0x15030601120b0a1a0705030a020102040f050301020c0c210601030c050102060606030906011a07060e01060611030702011205130b04050d170405030901121e060302040f0501030b04120306050909010b03 87
    0x160701e072103a5100c07850001c01c008500350919142840b000181c020486000000700450300201e0020800703009901c3c80c07640096515820300c0b0b130081401e171045d0b0056000e680144529100b070003021540e00c21000742641e0f07400700411121888411088000301c0080f0301c1c010320002009110255080b041924800e800711109500c903d018403205100445241c00190801d1006001980703292005d49101e02050100e5030900c6a50f440321400c4610900c2c8054440e95240d034108522900011380803000e90803500554140902600081c022100802044c40c0160380c07140000c000e070140c01c1c4840300c0180c0000044c1c0091805203401555851081c40b00804943c209111840320b400500103a0300c00da9010300a07500349052074005561031124141d03003c3e40e00761070b5180d28680c81c00380310f540781009140301400705240f441c41c0140801c944200c410300b13031405d0524005001060410059540050340000400e41142441204800915898000580c09100e41092225504e01504100908802201a5002d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 58668096 1250 58666846 58666877
    0x503040b0103150b04230c1e220303020304030c050901050a0605090a15201506100c020603010314010e0a12050c0c0a080609070602030403031706060915030601 70
    0x140021200104682400c100500000315020a410881a400000440c60480940c0040c09079070044421842000b94960b10441900d121040c81790415411003125142c0120b0151245103541707449407050110500013030314800c0c0f40d40030b014040450010040448140c0d180d1038025107d9101d84010346007425020700100340752805024240c1241e1004040c9840030b40380c107005030742d50380144c0c407d82d6000400702c00c00510742010391440d009907840b13942c450b000b00d90b4540d19900100f010307d03640c3c9900c0e03000d00212507444242c059810f400c44400c81d0301c00e0042550400484982c0000ca100039000500400004104003610075030440c1889290000d01588090264440d504ea6207540d014041c1c0d1401100c901100d030090004004a107500d2041e681403076034400c003040300705020b0391140d1181c2d0303c42410840c1c1440c0134007190001d0026071000d1461b00340f4545009040801461000309018140404145039a0300c0070201e60b0211409428031000c0c0a602d410840550030454055010030740c0c2c0c95410800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 58669346 1250 58668096 58668107
    0x90612091b0102030a21060f1e03050607180b220509060904150608030708031005030d080109051005030a0f02010e100c0803060103061a04030c050604030321060f0605041401 76
    0x72201a4019801c100c1c064400b114103107140b05005100c665070a40000c1c0102c1c3c03a01490001d0141c4201113101c491a281e012071400031440d80b56085240c20880070b00020324041541e0341c01070301601e0000220881886801c422181700e41c800c415008001030001400040c1c9850300004c01100c0010440d025580d205000c0225004c070b4103180c0c05480000010002060007500c2050310a13024070000d04561101580c5203554400f01084d0f9521401004011441c4440559a4007514043e000703011300c129500c0d005403c58106000707058056840b400080d0440c020407048400802d40103080311004000341c2041c2c400c0d81c4010b0020f0380060010001002c00c1d04116102080299241d55003001c1c405041d140d1040c0c03074001401d407604140d00d4000010b1010317064103141d9407043c00703103070550342c3d4620b103143c00d03411f403102c0c0d5009502440c800d00c410004250003522402c070500c4062030040381041c40c200064004c2c4525040383c801412079100c04a038003607225000e0825929405e500c050100c0ea0140195070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 58670596 1250 58669346 58669393
    0xa0905101d13060e0106030510151d06010e040606050702010f02060c0706020f0c0618010b01090509041b0b0c011d070b0f0c031213031e0e1509061209 66
    0x11140c030900803a114014210341c2c1e5000e42d0003400f001600e2191a4a107030301391102036000b66101e40c402c80c0b526000d211903204600c0940f03181c80046000074584118403410012035030840d4130b105a40000100282d0240e42d2940ca0510020420006986c0f41c48003c0c0c01a000310005a002500c00103400703d00030300003d602c07409a007482e4219806d01d0181d50b03c0d030000c4d5105e04082e204142c400e004000032000200042c03401040c07060142c1c0000c10402c001c10b0b01b100d41c0c0024080c104441144100002e4681000568002e0740109440100e0010344440140c1c036001075101d03881407a400950b050811106610100103a00c5581c3d01164411500303115564617402030040080c01802008038221000c00100100031a030380c10b2040d00c0c01c0c80c04c9180c00004100d0210742141000000140752010168066000300b20701741c0814600b1409a81124001e040d4038042900a001e445104900c64000c0c1c865020b8a1078035000625059490344154201050001c060790f401c4640c2c442e401202c09101c2103641e8191 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 58671846 1250 58670596 58670639
    0x30213020a110706140a110f0607110601050a060c020612181009050c010305040311030a090905010e07080a020d060323060108030a050a1d130504020109090603021c020f0a090510 78
    0x401785004460302c003650340c40304942806000b401c1450400202082c00741010410300c81019082c0c51400400107400c41e4031044d210013003600150b0050144d0794660320f842041d28800c0c900313000040300500c00f0a00612944100b0f1044c3c82c60341c0204400f090004115480300c04402080d202000c250b000610140c400c100401400d60b0401a0944801e502c66404154418000e180c05060031164150040c10360f4441504034001864184090000ba1581e014850051000040804103403500c040300520b00c071006840728000d5900020041c0c405040b0b40c104101640e04121001c45d0210106a800031144c213841c000c3c2c40354010f4400010b00384d00044180c40b44100c241d21414500360100340304a52040c10503842e90700b240810882e41000d5140c401c541100100ca003140029a420300303000142244446600104c500383c1804410700c016101c000d140c001c00300c030f001c208070041c00341440010164043d4001d0701d500304515200001e8240082e422260164a01c1e0703119040c171686403803500300c4642c4401c0d07550 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 58673096 1250 58671846 58671857
    0x507050f010504111e0f010509090709030b070807020309040b040f1a03010e010c021e07030f03050309070b0f041206110f0a031107020603013c0602060a0204030b040b0a06030213020a110706 83
    0x317001800c03c042086600c1c113052400c01e107481d4422002502051054030904005034110800b8004c028459020a07081900c2d0f050010032454040310082d0340b846000c42c0d1a000e103482e401e2000103074885401076050302e140e414003440080e1800c4c21042c2007015582d8058841e40c04d188158a001c0f8040c070600c0c4e4140940d034041e081580e400d2910f500d200305030091395107961150103000001304600b00c003000c41e02440b84e61483d550707050003103049240808a8001c491412020014446980840300490741243d2851030040314500480c10b0100040c801340b402180444000604002040c0040c0010301e504000c0703480401c1380c9502210200014098000c00940040303003000144001c6040d8240b10580c03419140c0450780400400c000b0040c0300e0300311180b1200640c0c0c0d006d024400f8540601107580c0c0599048002c50078140b45464400081d1405171018000c0718040003c50381130300c00ca4200102a580291072240d0341381e0210701440c029480820018000340340d08640420304a80443c0700800c0781c14580d030340c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 58674346 1250 58673096 58673149
    0x10605060f070b0c12070305250912080f0c07060210090b06040b040b10030608280b0702160e060907081014040b0904060902030f0d12020a0507050f01050411 69
    0xf282503185014210f031203d500c0a00c01c2c07985013100f40c0da050380f14600d140c2d4041500d0411084901c0f4000400d901414115050240e0352209503011103240e044a1101c0c00d058100201810003122a101e01d0703407217080c154030025107152000c500144d004111a03a41e0b0840b901d040001c1c1100044413002c030343c01009007a2690100380c251510b500843c0114400500020300a020b0800062440c8020305100c400309445110401440c902030100841e00d280742d22040600043d8a03014994008580b07000501249191001c148454400c020031402e10160905811840b0384461500c0c10561089411502c01d481d143c0018006900c14810705028224804107100c815040940c0300814032143e9881f560095503e00d1280855520ba64403035000318081c40300002c5ca00c00500500d03061080d45040100c2c41d910211086401c20750104092000d00303408140140c0300c06590204482c1841021400b41c0ba510074410203107069903040d8000c41c022442403a40b01400d05a40051007945010070f94000f41000030b211a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 58675596 1250 58674346 58674353
    0x80c070206120f010302100f0516110303030f0f07110c0d05030d090c030506130503040e040507030b07031b030b060708030c04050306040f0b0c07120c0f0602040902090102010605060f07 81
    0x150409500c000d11850420402c101105490321084a03e060321042440c01082542440c860320720f540141072070140e640224814028090348500580000c6450755100d0742000d205442070030b01187c200003002c1d80ea99040981d170540001c03000f919800c80309071000d804075003068011003145d00d107800100f0240003034000700820004640720f03424003034420340410800d03000818028400c0c180b90a114a2b00d00031442e06509101d403401c9001881d40c1c04a401109000703001c42d0300042034408807000340040340342e20358503031a060342000c0c44c60b4002480104150248541c0c036805810420425041d00307112040b0071300d8600c0840c2aa800d030401c65070405420090100402e844100a40d80801c1c0e10400d14a0715640300c0c042480e001e011101520000d040365401e42c01c1250450040f908251101011410510144c0f0380c0300c1811020fa01400c180481c0d0189142040440d2445c01101c5400000454499588800140103580300405550040d4079000002c40c0e140703045002d0b43c00d0300c90100842c0341480913036907 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 58676846 1250 58675596 58675621
    0x90c0d0c090e1602070902040f030c08010c170717040305180906090c0901030213141503150603040f0204240e1b0304031404031b080f10020313020d05060402150a08 72
    0x416980031401800c1c0c5c0481d0382d2200340010300003400c0070800d00c400349141d030518800036091030304505203513410f1406c0804e01c40d5110f40c10500c0e90a48ad50040c0082d1034240b07054540c8400703001080300c0e0b4450b2108000500d60800c002d010b2402d12030081d640720400d03c00800059000c00c0b142e450744118004046046209200003038480010f041c1070052418215005e025080c8031168448d03c8000e2512106002c0c50502c40c9020003c84141c408103405e604052203620018048001c000380200d5011000409000740c03e2480101d01ea00600104001c0412070034242c4210b00398142c01365441c90305480005c000e91202c5d1414071807014006481c2d5242440001c11000d6807024009400b044564583c01c0e06100d05a00244011442142d9150100381c01d414025100030042e4009422504204240100010701040f01c3e00410041500140e6a9842480d1103120401c0781f080a50000e0a607400381e800c003e0300281450103280200c1d90940d20b20582c1c0007480140c801c10515030000ba1120b80812074030307107a88 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 58678096 1250 58676846 58676881
    0x703050a090510090606080a1709010e090a0b0a050d020904020f010e10020c0102011515081b040602060a050f090a0b06060d1803030b0102070b070f02060405090c0d0c090e 75
    0x4510104980c01692a030510746405a074845020380e03071321000c90081203814440c0c103004201c208094020361100d80c4036214020310314456010b440c4000501022168428035894500020044c00c0b03041500300304c04a000100900c4401a005500d81007010030340e0b140000300144126401014501c19540301c1d400d00208811002100f41806158011010180d40d840c011003003c05455005002040c40240024251101c114040520145850f01801205150041411845a14140f40c2441d495810168400714005c11140010034030105000c101540e02003642030080528140901854a483e100451a880281d03440011030788040002000256107001c100da000310014401030404070302c0d807200d40640d40c03081400106950b40c05803040405030035100d622820351080c80140b103403e0030094840903d208144000d04006403804a0318215900c0c2c400300c038003808024054803075509103042c0b21001c41e0880d90608002d2810000c803800100e12810400b801c842c404019100d082d203030a8890041005003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 58679346 1250 58678096 58678111
    0x30708030f04050d17070503030a05071b03110c03011b030609060b16080c01050a0c020f01090b01060e06041206020301030c0b0c0606040209041b0e0a08121b160303090e090102090306070305 83
    0x10a5442d550b1500c045c00a040d00900900181d0303542d00d44250584121903005000d0028025200180000b000d0151a90040c06500d420901c8070020b0450b4014505404081055810340c2001940c1c07501e0002c039121204042c8440e00c080c41150b440d400032206031001c0f0301581403400401d01c1098501607a4003083c03881c8501a0a45601d81840c10224a0940c0c00860394040100e4452202e050f003150304000c0500c1c010361003402048409070560301e100d1446010700c120300030001d000b501c01c3c007640ea03440126001403000281480801e410ba240071030194000b4801690080720000c00000c61880d0842210103901d107900c00f07802c3e259940d004200085d04016081600659035054080010410030740529481c00c00e600c540c0c2058000c4420883c51006607040711500703070010599022808051002d8a103541c0100703409009072001f02d043d1500c1c055001c1d01d07484071821240e40001c01e00d50010100c809442c0558403c110175500c0c405e00741c0c244d1042d4004a90980c0c4007400040d02c503842548401d400822 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 58680596 1250 58679346 58679363
    0x605060904151d070f030905060106030c021501080c0f0d0c0b0a2001051f060801032604060918090203031803070504020403030203030f090a0b010b07030e040905010b030708030f04050d 81
    0x440d40c9425500103902529858107040f48400e11103915081200480007040d41e03e024040360025603100b640301d500600c0341c40c040c0358980d801080b1640c001d000c9846220125101d6001540e5504141d036a039a02c1082054007070248070944c1045400c010141444454005070b0909090740b50054104555202100303500030015410380d0f81c3d00c1c000f4106814000314085200206007402c0c5000310308000d10285610000c0310700001410050681c00c240e8290440b034011940b054100c2d000c6051740108015246690840e44002a010503001d410541c03134010388d91000c1c80713003500304007c020071000c460f0b942a01079850707841440a002e901c4078217442040810005010b4904803070b510030105d8180d0300b10350011000340e000030041010818110069a0380000640d004001070320680d110392200c40c5040c05040780300700b000207088040c9401480f00f00c1d0601400350041002000344d0602c14000d107003555200d88240941040080c03500c00c001700b80e0b034400740300c3e0003901c3c6414a03120420013540c1103428101c80071003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 58681846 1250 58680596 58680599
    0x14030705061206010f031b0c020d02100801030c050d1e1403040b1206060304030f0f0302090901030309032105090409240e0601120b060616050604081903060506090415 73
    0x864240180039a00410101c00c1c440381000c000242002174641c45c0380041514000798a01035411a83d058164a0482d0405940c0110b45001103410120540c6019400030305800214440d5030384266154101c0340181181101031f91201e0820035006c01c404030203401810301810703185981c1c42d90914036080358814201a0f00c0d4040b41e030001800c6400640c4042e0300e102000c02c0710036070100c1d403110040d03001c40125041417840c0b4283da00a88a101868070b448104206020f110300702502960407204116001400ca03c400d43e0740f481c000745416040c0c0002c0762041041d90707402503c03240703608405040300c3c215100d0703504004181003800001c03c0c002c041661003100040040380070741d001c42d184040200d0314002c08607011180700044c070714120707042c1d01502c045500010340b100401c0d90005110380140c01150302960f01c3c2c03001005020005545078001e0010b000c0c001c148020400900002d00d010514030104c0d800404410740164100c40d840d03c205600701204000d2000e491905511103081c5005040483d454207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 58683096 1250 58681846 58681849
    0x1b030a0611070605040602030108070504021905031807030f020f010201020306090c030604061701020304110303030106020d03020f040306021b1b0303040504091703130204060f03020607140c1201150605120114030705 94
    0x4c40301900d0030f407811940040140304004041c40b0f020f01601050344d05620f0b004070101ca800b0740c4141002000f08024000c80800d1740d00c991401c0c0c3e81c14018598040701d440d15224201018407421600c0224414504200446021350041c000e4038800e1300000c200724296521090420300b075510040805a019a40e4103000c03031716420785480b81e121800c0d18400141c980ca8280b0b000401d00c2070030700c46544603610a00040001a81c00201402c103203000e403401588a10fa201c8580c00c441c041c5404c0108480e0000c202c110800c0e480d41c6400d900d2030301480880d02401309003802c1900980d4a5074440390160402c120074000350400c2d40081d030f5858420010090203408200284015810980d015003407048080a0001946450300400001e04402d1402542c2e080c50750780054182e201e265401005801d803c030070141c0c1c002c3e0034042c01c00c00f0b5802420103c0401d003441d901d28000e00b240400803c602190301404207140d4455010f9510318011036808010300d908103002d2020714580d501c1c0ca241d142c03180c4840860103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 58684346 1250 58683096 58683101
    0x10203160309050f01020a0b0a0f290f0f010e1207120b2d0103031b06050114040501090b0603040807050115060801060201050f10050105070c0509090a051b030a06110706 74
    0x1150300030b981d02d000c02414601003102080d6521070041c1158480754030140422804110150400c0101000085407400ca00051001d8000c00c44151031019000c424006103520898201c2e80800c401c55102d80020120340410041c0c01030500780078000340000c50310201504005103160381d4210a6401c8500d07403a62042c0412030750201c1203045035403105440030301041c83e90313140000d000030600358809581c0004004455510903014030000d8200040380c14681d81d4440a0030100c00c0c00f40c0c00c88020700043d81c490140b54908080b0003816805185030800005450243d0301c100c0c200104020159480c41e240ca40b501030a9411000080d1240c0d540c542c1c1001501001d807600b41c00038001501c44100315850018040e084a00003840d100c0043c2c100c908000021a244154400340c540c2400c0080c0c681d01c00b41408900810036400040d0024000301c00e200c0c3e402800204030b045c141c881c00c112401c41c0220203100c00c40c4002c4028032034040e48520134290020300305070007140d40d010311316102e84c1c04d000858460105 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 58685596 1250 58684346 58684387
    0x406030b040302010c0f050307140304030c0506100f0e0c04050103051803040905060f120709020a02190c1a040609030f020d05010c03091b0501050301090c09170f01061a0307030b010203 81
    0x542c0d135810481070217903004250b05084410300d007459400d500d00b40d1400f5284a40041c0360034183d450000000c2c0030140162075010005421800b202c200f850900c3ca00700311320300c141c018038496480d03001c0d001600104986d02c103442080481e5215060a11300401034019010151899201c010003030b04461202d072080015000408400c5d0010400d42010700a004840d005100000c0c0208850410003401e0000000d0f00002c81d10400c00042c2d480c60360300402c0342894070302c4041c4610807805002150900c00d010484031b0694481402d0120f110407100900c040e50702c01c1d44105000f18113041000c101140300c0000010110380042c005448072070481d924642164414110b600100b5507550060050001112016004c00c0181c031a0912643c2001c0018081e80014480d411105441d00001100203110300f148c2d06c020555060b41900c00d0809072246510b0b54a03120b4001030039840c0000006c0d0200162428030711401e100e00f45186140c4070514200c0c05805200c461505500c001c11994a002454942860 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 58686846 1250 58685596 58685603
    0x201060806040f15182003070303090305070b1c0f02040306051e010603020306010c060b031204080a030f051804020c010b1f020f0102090612071e0503070e030109200406030b04 77
    0x201c4280356854441c040206a1000c1103819142400c50150711708003441e046103050300f1604140031500c651000344184254801215010700451000004041d00018000250380c860420740d0381964945580340d84074050300d14046032400c590200c4c200a0a10b603030240c02c050f401128003520300340c0c8a45940c01980d03400d42d2016200701c0220200c400604000a106000d0041440e0661a50403d40d000800c03075450040c0240c40340c0d0703032881d03002c0700b41c1d800304000004006a4600e05442d10b030b1701c6c0b48040d240c0200f0310742a0007141d103240d8200e160318441e07000c50305040140190444170820200620000f508180c0351610150340e503030821041c0359203103c540c1018178544202d8514940d04003000a060a00b601d54042c810703030061040c80450340e282c00c181c804084c008100071030329540d00c105c122800746401d142039101c01010310b07081d02c09036030280c000c500c9800c0989951004164400038542203500b503840180c46c0031442c0c0f0308401c42c40800c0000315080c82008001180791038480d1078000d210740c402d4400301d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 58688096 1250 58686846 58686863
    0x80c030a0e040b01030903022e05010b09030616090603020f090405041101020c06090904060b0a0e040303050105010f08040b010603020904020d020c061f030507030303050601050d02071412040303170601020106080604 94
    0xa0034240b90500a020a81400307180078400380b152982c000e5903405000e6000817140066001184858184a0b444021107207014414441c80d43d440d01c03034260b2680103480c038a01038020714000403e569141c90003400303841510f90b030b80701d0b0705490302d00120000c0d000009030161442d002c210000d0640e845001e03440c0545e0084100200d9000c000c030001e413902c507840000600824040c001542d00e50b0b0b07401151588950030082c0410401d90100006040c40d60a4100642c0c1c48450024017041c90390580c0001c2c180c0340280c80301112103000300c000707640c0014110b40c0108034410303200c010310075a842600a0204050080c0c0007600b4031049020001c240e03008035903440c1159020f84204484058405918030b219600001c29400d103d055449441e102c0c0326601002e418561120003042180c0d20500480f003203207030721030340031901c1c1e5210f49030540d000308595408130321502c2911121071000c40194102c9046980c162101c81407030345524090115003030010300766419950f070380f42e00084408040c041244180e1082c0120b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 58689346 1250 58688096 58688117
    0x50d0206090607021f0e01060302030a03030b0301230403110c0a0e160e010c060e12120a0608010209030a020409230601080115060e01050d20090306160912080c030a 72
    0x14940780c82802800d000840d44581d00e1559245695403045c0416610010040390f01c01c041c02d4910f0140074940c0c0025014491443c4944c140b41d41075005100701c8d10f003100240614a160015105818600450400301282d01000b26000a010b941404035000350001541c500d0028100004d450034a01d6000c0d03126040b00c1c50410a95003510a00c0500310900d1b401c000b45401c401000007008140c6c0828004d05640c1eaa0304001a0103404100b800c2d9000102c94242d650341c00252000c441c422415512f104071079041050109116406000f0340f015100003600a03d0490a0380c1c080101410380d105003520802452000c900f41292055410355510200e200103021a51402d070a040c2150464101819000201002030040540c031200d0901248002d20700107465031901000c0e803005000c818044d01c2c0303020100710545d9050304100042d0201d80b0044081d00c640da40e40b01c043d0b4440c5407103883d40000091904005120040448041d5440d1138015a0400e080420324803140d45103900a0b4015404190890308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 58690596 1250 58689346 58689361
    0x509061c0501080c0109121e06110d021207080601120c0507060507050901230f03090c0d050d020111090f0d05030f0d0501030209060d170a030b0406090501091104080309010c0f050d0206 81
    0x1075146c020110f40c4d1104c28442e52a4884802200904040c04038000410b0b8081c02031115a42026205020440b16651380e880c103041c0d090000d5012000307921000083d00001850f141c05186014443e8106840d0f181c541074440c01546d0061102081c0c42c02030045c144442c03c00324140b4450540700310510340340c541e80c582108001526880040d820200741c1d41000c4220012a0981400d5600c02c3d12041d09081d00d0b6104c07a00d0460910031841e410a0b00054401c0d02c0d0030038002c0008600055106603002080700000e16007040c0014400d0180c200c1d044170424074000d080d800c01e440342c50003107800340040d281040c0702400c50444030b6004135288108940c4950050041d0310380480c0090304424200d81301820b0345556580c0301c4400c8020110354000000c007150664100e8000e801c01100c8240042080041980b511005c2c0c00800003030060b030100614015040104444070310842c6d00ba609417038000d604003200b450045031002e00d5200121980408a40c0460002c1c1d0208002c0e46070f5001900a084d0301c0c9007851 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 58691846 1250 58690596 58690607
    0x140d1505061606050402120d02010504060501051014090a0e04050c03010c03020703021b0a09060605131a0d020a0c061107050d090f05060c0102040f060c05010b010c030509061c0501080c01 82
    0x100510710038802040140c0c10402e04106255141d0790118010540c1e6450b40005500c481c10303009450001e000c1e068001000030f81c10f6002e1403045101c1c04c030070000d50341c82d00244164084251508800b10301040500d2010302e084c00064051110001c0110300243d0310340c0e80d00c0c030110100340c604541c1c690203450300d03c1c11440c00b8000e0b0266030035145002c5051660325240251b40341080760212002c002900e440280d961611402e5030301a041920b01402110703170700d40d0010720940c040d003420030200419a10115038030850040050355045a03401e00d904041c070303042c00c8000039070005000c1c00a00031441601d200042e00c0780900c0d50400c080311101c940342d040c01c1c00c100341800008010001000036a48050003030210803401842628020740c1ca141d00c40c500d041c000b50091284c0d030091542c51420034400644540d214030f140c40c1d0b00388108024040221400019104a056608020041241402818428100360700901442645281408285084d880a41044410a810801d4580c100d04c032004060f50700708 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 58693096 1250 58691846 58691849
    0xf0706020a031106070c02090a0e120a0813020d0b090a020316031104050105060a0f020c0603090a0c0e070503010905040f1a01051e060d0c09170303070f180303050a140d15 75
    0x201e001e130800c0c0c5442800182044a0344400a00c104441004a00404600d522202d50001000b08a81403903090f5416115150000c0c040d2200189291000609290b101d015860b607140d8041e050122030316075952522054200200614498414091000d025a504122806a80c850000310052103030031420241e0903103102c001d1707c0f0301950a1600400c00c584494003290300c0c1c50f10616120350000c1d801c00c400c81c24100200c4070240c3c4401c011043c0100c409001c2a20b100240c41440d5a08102d0780e901d044490210048840b100803801c1440104003040d9607070045a4454890861240c1702e020704da0ba0ba40c0307402400000c1c480240c802000600c05400c18071145d80d50b0507001100e0380b41000000d0005041c42c46644003000540351a080d05040311802600c80802410140c25999052810410210b54030b400c11158400014142d0303d52112041c012036400911440c94007100022904540341078550f17600442c00d1404120444da007264480903483c020b08803080c550300000c01c24a11420b05c0c080702c403280c2e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 58694346 1250 58693096 58693127
    0x2120f0a031d010f0e09130209010f0510020a080703181203030509120f040b0703031b0302031905040b1303091a041401110a03080a0f09050a060f06060509120f0706020a03 75
    0x621519000d0705410640520006070100d4061b400d50791610314000408180351402900071030441c00119100301001c07a220290b800585101b41f0f0300c3d4104200700c3e9a07203280440a06500c0b820005400824030503070011401040d05910100311039511100002206221a0140c0010703984100348044490184a03050003004131011103420110b44810340c80140c41644500c1100c071100003000000c00d8002d03007004481e00d9a090500710402c500045c0580a944201c0304203042c49030407681040d9645492081307601460304a66904919540c6030103c1010009001043e002c0c032450300380004618681403114080858041605a00c8070700d0603c6850780c90060300035803030501c100c98028449501002660243c4250103140041843d1241004940103280140c030052110781042480e00a01c5000141071141034404c51040080070b407280001e8003229040d0240c5000100108255421b074940010f62803c040d1425040d034520302c2407801054a02040f5602c4880075800280b8001c080c141c002c0307140140400d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 58695596 1250 58694346 58694357
    0x12060306160906050903100623041a0f010e04020406020706080a02040303050f0a0504090f02030601081506030606090613030f020114040b0304080c10050a06050f0406080a02120f0a031d01 82
    0x100240500b040c20a0b003d420b04104001c1010249a80c0800104c0c41ea01039100007040440c0e01ca40e0030b480c5071f20a00c2c0e2105100391151581c08582e080921400d41e0001c0f440082d00d1010a1072820000c1d4040074190080c104202408924244e594070b2000740f0007006950001c1c2540740c0f60800103040418014005d8142c9481070104001280d0400100c54412109254441d035694625005030f481d4040c0343c100d103103403a18200d080c0c00028110343c0214021082600d421002d56501c0d888225500c080390303c02d41d000681400401c1580c14681302170300c900240181080d042021026a50400a0443d4819160f507507240f0032400a5580040c030786200120001410740c40c1c00c1c00d000c000703159440060070091a1300400609000341e01800c1c0144140044c50f10400c0c445424842d42000141481e03001d020301c11401c5107954100ca05d024440d1804545034100a000400f51540030482812030607141000103019081030b2a01083c010f00500100310b110b82c0b105960100c0181c8040d40004030940120b05224 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 58696846 1250 58695596 58695631
    0x50108100608060f011e08010608070f14031f0b060c06150d0b15060d0e0d030e0c0108011202030102091807030b040902241e0903012403062012060306 66
    0x5029182d845c1c1502c40514903241c2e809064044c5170b6804041ea030010305a0b5280c9070380801c0da8100411400300703c03264505910a41501d9030507003840d01d81400b02c291792552068200030b07100d031810380d200141e140080000142201c8064041a000d03400b107004100140c2000d800c03c40c07075651981a40c1122101524140d074a402c080d61414082d0002600541103041c41010540b81561410200c1d400c1420b8804184a82031403400025618000500b58201103400d0850040300280c0001c1c2d07402104005a407241c140c1d918102101590703d0f100d41c410398155400300408103143e200c41c0000c401c061400680e1f41103d2030100001001c51b11031001a502c5503043c8400c5101503075554a201c80c0404010f818201080300c0c441d001512407003005003051564501407440703076200500d580504007002c402d40091003125134500b032802c0304940c050303c5240c40c0b00484c4014004103800e9403000004c00036518540200721354003240c40c1d1603a04a00074115400c442403041201c01d090034410350740c1040084009800c02c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 58698096 1250 58696846 58696861
    0x30506090109020d020f0403030201142d0a060305150f010e04030f0509010c0209010605130b0309030f0d060306110415140d02211e0c030103051b040b0405010810060806 74
    0x3440622500d071005402051310321303a0f140680c0c100c4100c5241d13a03c0c031554403962458042d0203403901c800c01500020760140018141060150304c03001070324110fa070040c482c000d54850070451580250481045c1d5950302404130005034108800c0002181e90b500000b40c0d0700c6d0140744144a11f2058200300300215921040c0000030741c0001e11040148091b0526640316452000103d5998810000182d0b000d05c1000000900c40e402600130524844444102c2091546550801a25210540740004030303500c2003202031445504480034103080303540110045502a580c2d101c40c026038030843c0001d0229540010b040081c444100d6900d040300c801420000b42c8a003d02d007000480c3d0149106102c1c205400242c0030b09110240c41c680403104204240e1340f070303440c1002c10300c25241704041041341415919010101e0000f6070000103490489503c60010141141400c012504941c441d00c069904652500014005c659030390085d24080c107a50001132143c6050840c510007031352055440b01d05260172103400d11010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 58699346 1250 58698096 58698109
    0x10b0408071707050f1807030507030c0c0507060f11010501090506040e1b01120603020301090609020f03071202041109100e030d030c05040306110909041103210d110c07080102040f06030506 83
    0x40b13034412900c22803802900004500218028007207400c400d541c10341001a801d402d503102c6400380000b55401c11441e0301040060f607914140d040054410380c40b81c41c00700700d200d21030060146008000d00d4400583c2c0c040030101420340d1002c0c2c0140f030720280c440003040030608140c440c0010f0310f0000c000502c0ca031480340524003482408008058104001305039030600c03201440c0c0001e4011b40c0c3c050001c1041901d24106103004052903181280b1550a5a8204d8464500000c0080c00e0310404020310011800b19400c00006181001c40703003000c14410710500f121a0350b02406141c5024458540d41900340342d40d0f00f09401c184090b1852424185404541e01c0f06650107025501906d80c407410005a0b00c20201c200c3c00b6a00407289043e07440201c8100b00400c1052410442c044940203504851700103109590740100d04070305144c03540350000244101600a81c0c00e030064682d0302d0401c1403030340c98210ac1c241c0d03141c00c0c0007060300019101d0f900087c00700030706242c22038254028111072804214a04009000441 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 58700596 1250 58699346 58699349
    0xf041b08060f280905060105030705070201031b0c060510060509040906021911060703050f07030b0109150c050609030901090312051312022805010f0e0603010b0408071707 75
    0x420801030300241d80d988559000526020009100382071500d0b824015410f07940c020f00c81d18007030f0143c03500300045034491805624003450341615502d08550b0313078440885103600050002c0c0e0405d502c4420500003407010b4003460340482e29964403032035496584d0a1100c1507490140413401c1099a5060411003140d0203810b03500351f100304440c086415000740c1040004dd000d40c02000c240c4100d01c10351903102035084403268106c280e07140300780c646965612400b82e080b140c04665191000d0740000c0015007091017540100c0003000141000d140c5540c0300d25001c00300f484180c0d1404046450400341c5410703c4030070010180d2018031140118a040034200000b03000c600c0e68840100502d00303910142803494052020b9a00320350303903803800c81001380d5500e0200010001984c82640a41c002a1200080c40c0702c4025004c00c117448501146606490304d00112000c06440c3c0c00b410401c6500c00c00030005035107020003107000340203110920740c4540c100159242800c4c0c5a17448040344030f10042801000301c03000703d4a0070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 58701846 1250 58700596 58700651
    0x20a0209061201060312050a021513020f0612070302030a0609060b0a08040503120702010b040f15030b1e0f09120c060c16050a0c0305071a04050d0809030303010609050f04 75
    0x2c1100c41c0c0192280d025202c550001411aa41807641030b80382c641c40340140c00341d0700e656802c0302d003450200c54020b00003690035148141e02c180303003003c14000350030301001e607504007a00500305502d400100b03d19183d0944056a0307083c00283c0000610146080500600015191050b020010a8a0461085114810b05050106001442e8009001d002040c0141c0761100c0d00000126514038002c01c0080c028401d0800581c812171601d00d05820800c12442182c24101c2c0c8031900810180c10b585070b0200e1010300411034580c800c0b0403954448600d2540103601d002e5244d5149402040c10011119070800c0c15106002600c20814041d03202804000215150012601c0c2481691280c0041000d120114007207805081c6110324402c0c0c500700300310b070000401168054000c1e01d04040e01c618051046074548002c14000380343c2400288510316000d51200700c418441ca00d00c070f00e07140a03203011030306542090380201c0115070301c0c1e82c3c100f00d83d05007410101d0310300604031420030850f080e134910400e02643c1a030b90f95 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 58703096 1250 58701846 58701859
    0x90f03030103062f040501030c0f0e0103092609040605030d0c0609030c02060f0315100e0603060d1b090e031309051f14010e10020303010e28020301030210020a020906 73
    0x19924815507038001c01c1350b40c0d00403504100e1104502c4407403100d039200341704040c002450001801e884500c1034501a01c441c10f1961800d20311800e00c80110080c02022209548a10350702c2e003002000e016841c01c017004030000e14015074543e50070604000841e45c85900c958020741001c40d400c50b4007039005032001180c9500140001d983d01c8075080443e001092180004d410250001f0400c1ca07030031344d000c0914400d81001000c01042c651103010700240c8900ea0000704081800c0c418100312610344a0040c643c00000541030854451403174440b2215080311000e440359403800000b0030300000016024290444807181c0080d49088540a6060f0074001b2911407408490343d501e011030765404400d4060543c495540603160a05a01c40142030a120440305005000c1212440141040c0c18000c5003215142d02e680c01950442e03280c5280100d00300002040384402d103048925100400c84c0b20282c1188031201c1d03c00c010386940c1107205003d4140c4400d0100002c0d5405036002c6001661510207640d070103402907848 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 58704346 1250 58703096 58703111
    0x3080711070b070803060906030109020619120207081c05010f05221b030b0904051015030609030206041e050607030b01030e0f0f0c06030702150c0702030d17090f0303010306 76
    0x40c141400c150703402800811000003214400d011180c00a14000c1d00100e0300c10340c054a50b0341c10542296540600290080018084400d52503a051898038403130515003820056030180b920741d60202ea12881080340d20100106040e400c4244c401c452600d20346124000b0411035042038092003c00500b4030525110780302c2c2c61000300c145040040b2800c9500180700041c808581000300d0700840048001035007000a26090010080e8501107205600031034204002c2d10b5191000c6480602800100e4901c204010800d200000060b6640c4109204039000e0f41c01f610031400d01e41782c4010090000d1524449401035a0142400324802088880d0400201d08002614011000046e005031030340c048103410354007031741040500c26003000c202c84854107000419500132002c10401c2000d00d00055038108010385c80030210500030221100101d410150407183c65080040d1540040c2c40c002c6c004003d4030008280f20050002032029401c001c2d003100d00c44028240550744180030f59500d0005210240449458459 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 58705596 1250 58704346 58704377
    0x250212070c031b03020306060a0303170a151215050103020f040e1207140c040903020a0308041e140105010f2117030112050c0102010b0a0b030618100305010f0207030807 74
    0xe681008603400083c0c00c030b10803120300c551108401c0600c0300783d02901800f800101c02c0c0c54207100700d00980341c1c19250800c100c04041d040c0421405d00070040c04000e42d40d944840c440061113400000240000c03117040503030203214900414a5420610740c1d01c5d040d414100144010b03500e03007150314130a0364246d0300040c0400403c4061880c11310110700026015000040707940901c241ea0007a04098810034080310740640711101030104a030301c070310000b4005800000d180c000282c812485540c120313001710000b1014039441c0880380f8003809410300448070500e4086402194880c28000c0500503e0150080c0c00c00500d003003d0b01e0360080540b1a40307a03c40864a042c40100000340c00c5400040e41003100c00c079104d41c0c4901045031406400b0703c05680e20720904da009a19584140030721458601c020b8512112640f800e283e030360f81c43c1c0028185c141c0c0010a84802803151003400030061188000607070070040c480c90b41c10220f084640418443c400c0a004102c0800441d4125101c0e5030804803519103140071803079005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 58706846 1250 58705596 58705613
    0x606050406050706062303010509030f070b040312050f250203040611011506051213050d030513050a051b090c0a050c12040b1209011e0b030c04050c0325021207 70
    0x1c03ca000c20284443d41e46988401d0001a003c0707846d8140d000b00b1080d260a0302c0c055880c0a140d001103101302040264100040503e2555a000f5100341454822492041100000c3e11030403202c18523220700700c00c10064000c0d4040c001c0c0c07000f10041004007002c0441d511009440b4402c1c3d00a0340280720b500c0240184070002580300782c1e030300f8015140d103440e15511004000d080790b01411080c410110322501089540070005030b0200b0480e4031000804e1045420541034001d4440202841081828001100007248081c0003c035a800e105001030f04940302950a1940050703024090f1070b00075401402005405401802150144bc140d414401d031a1820032414900c4d000c107502035a8440040030400080d042403040c0600404106000c28034001d83da01c1112a003280c06003038007007000c8281000828101e24043e48954a82503015064a480803a100081410351302c0070385040200d1071002080000c010302c40c035480c0d000c980d002c0700c0c040390b410440b0707200a6940a140c22450505003000901804100c50034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 58708096 1250 58706846 58706849
    0xf092202060c0f010e0303090705090a06090219030509010e06180a05031801120e0a020d03050c030c1e15010311010909050705130b1303060b0d0c03080705070504060605040605070606 80
    0x1051140d46044041c2100d40720a418884180f0359820480b051040c0e10020003500c2c411700b4910000c2034200d2130b050030002c50b440003034181c07000f0695401001c1520303449030009010700c076440d005040030300800400003811180c000340013414991400b80310010018000c01c0c00380e0404000130003a2036030398a1403404c81c1031582c3c140004000f40f000050a010005031030410818228090b22000e01c285003000c401e44c00e581d560400340000c0c1d000818210014500880402d89482c0039140103800d05500c40c50092441d40309031039456040d40014400054181114840201d0b955144080c5c0201841101c2d00d0711000c0041c08000c20245681d0094441ea03442080307403070010b2a14030020700060420120142065000c1c3c0c1010040c4203001402142c3c120001080b944003031415105084150b14503181c6000510592014070360103101c004819021800340c203545805140900c0c10196104080d18062f03250034040d6010a0045050480811601b508201034030211039207810456510001c51500c4030040249 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 58709346 1250 58708096 58708099
    0xf0308070816030207082e021305040e010603050c0a03020d020120010612051e030315030703020a0608061801050108060d03020a02041508100b030309010c0212010603030c0c050f092202 81
    0x108550400c1c113500041e56000c0345c2240c0f00341e40e903c03114103081015400180604618005800700000903040059005050700b0000304505590f841e00c450002d815699504480f00c0540e44444050041c04400c0c030202108000841e42c010f0042c0c595404038102540200020703060240c42c010b0001c0b0703445040310700f01000c080d1400800c501da407183d4003030106007194282034659105074104694000c00c025101949120010000d5003981da9641c15548002214007966406024501c00000161540c01d4010081c2007186c41c0d64049103484020302c03a90700e00302680015806c43d1a00100001c4c0d810110786900403000341ca0b810414811307420300360700e03158207080001e400514080002d4080d0480903400300a81c1c244100f641c0c240d0f5811038400040cae89001040662540003008140107d600071705503500603502c007502c400c0e0308880c044265400c440ba5584143c002c141290351074404c01502c130f91090b0103442e04aa680c403041c41890b012920010005100e00c040310010040240590710714010700700c07090350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 58710596 1250 58709346 58709377
    0x103090c03060e07061202130e060307050d060f0e0d050702010c020402091306090f060501090510031d01021809090d08180d0302120109062403060f060f0f05040f03080708 75
    0x4000d5241d070701c02c1c061145600281054501030f181828900845e07008d003c0701100b848405080c000d6400b241040074100c0396242c8111800082c440d199030b03510317000311801809c1c00600c0415000d900c400707807080e07280c4400440c1c111503207203030107a80c01100381c0740c10076028a0040000707a01840410000d100c3c00c244e0f10792000c1e46564000c001000c68106500b0340705180405d0002d440400044001d555030350141c50b002c5511100f00340b12605002c8600122703a0160b28001c994420194000950305601601d0b02c00940d4002400e074844070302034501e40350740c110280c854072030030b142049005480d403540e4203102e020400040c010070705810b4841e851140d114007031410703117603100a405070160081d440395a10050f0350220800000b00e000c4544a5442180c1e044841c2d00800b11030042e41d01031200c1c1010340d6409250380c0d5100031078000125402e000c0030b032030161101250103011030405411940444922000c200013040148046403849000f00304587c1d0048401c2e454071000d00d010400f500403800c0c6828140c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 58711846 1250 58710596 58710611
    0x3080d060b0f03040213020903070306090f08071b05091501031d010510140402030408030601080a0e060f0609180c060c07030501020d05011802040302030606010c0201030902150a0e010c020f0103090c0306 89
    0x1600b41d001103008034421070300d40049031100c034022030507400b40040403030745500031a8042010070001d82100401d64881c0100070320060b62551039400c0d54000300d0060f60942d082c90204c4641c1742c07102a40c18054002200c3c24a15441c2841180503007071040710103141055111044160080f0b0801c0c0c0b44242c2043c268003d10962900382c0b055081e0f03041034072540c5103c141a406551490400c1d200700c0c3c0c0a29001000f251865490000540c5e00c00c80181055115640e60800c1150400c0c042c00500d00401c0d02c403007071004034104441003010030300c0c01030001c3c2159404240445492039000804801800041c0c603400d07122041901668201007081d40007524035400050801d04401c0325602042c10b0360940c106003c24121112131442c102c2c0202d000085d095800000800c08d50340c010305448601d288145404140145154041400b80c035010885048410010135110710039a0031103c1000886000e10b881410541c41c2c1d0000341014100004076814196102c00b00c000f809a03925a0308003071500310f0b40502080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 58713096 1250 58711846 58711867
    0x9090f1106130e070f1407060c05040905040302030304031d01020a030e03160e04061506020a0b06041d0105040b070e01080a0509150108071509060e040c0908101d030307020703080d060b 81
    0x1036012118030700014901040c03d58179501031090550340c0c0c4840b9007030600348030660f42d5210091444c0140d103020722034207100c0000d0a40541c050248201c0c801d5010b1a100c1c2441d14014201504802108103541500300030b024060340d0000b80102020382528007640c0703400289020034100044c2d181c2c0c50f0ba5651140402144040070800c00502851248030700300075201600c034000302c43e001c15006c0d00b001a0055941c500c00714402844194100c0b0b40100000340c100c00d5801c4030303c400b001d400301c10300c000e9456004010038000c506004540c40461420400c1d941d07040000000c0403141300514a160030796462000c21401a81000700d6503400701021040c20542d6120030946688007001d115102c0c00e403480a40210f00306100c1c103944c000f15900c50702c07011f50250810007000043d103641031303862003004202200060620401c2041c802d80c04081030000540794080d04059481c0c1c8c031079203035011055008206001c2003d40c005070107130480e604801026101d64a090480340685056032144003102d00c046881c0c48036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 58714346 1250 58713096 58713119
    0x30309090b131a120708070e0f07110115060e0103060509090d08041b17010501080c090604020702150409090501050109090201170405070b03072016050d080d020409021309090f110613 80
    0x6c0d41c141801304c03811a507032202842c00e10203003203c014142c007c6000114104074010b80102c040c00c0c3c0804004135103c0d03003064880e000d840301540000002490301e810348900d543c25100d40405000300760361481607403602011042e501e0410445900820840000103000d020030341501071840300944400f000d40e656a14950540c0100c1c0714403841c1654644000050415800640310750101000741c070102d0f01c3d90301c5e6420840290003142c0c090780c011640310110080548104020070240c0305040e40011703031104609001b030031104141c00c2030308850316200c1d00c0c40c00350380c212401c1070700c000c107220000c001c5a130346280c0b290410680da841074a950f1004070a1250710f40e00403000004817050821040700041e0310407440390356a070840b08a2115124408000c4c85103060000186501c01e0150421a25011500700d006c4106c0c1d100341d020b81c1c0490b6000c40c3c0f80c0250b035145803c0d20024505280300b4401e103100ca44a9848050003804014040c5502c0c50700c201464a585c400c0e142e440c0d000d45401c4a8880d92045034181 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 58715596 1250 58714346 58714349
    0x1c09050a06030209120303040b0403050705011b20010b0603010302040b06070c0801020a030e1501061215030809030c150d23091501050102030a080a0b01051e04030309090b131a1207 79
    0x4a21718078558007046200010980c1d01c02e5801c660410341507280c07a2000e80c0c540d40b101100362210354940d0010098640d0241c200308000b081540e0785400501090940c011001000c500005a1b90414000b038440d940c0d01d9058038150703601203d0000e00742c1c005500051440c4145140205005900c12000503d9041903000c1d01b00b05902c0d803030522103a80a186d00588514141c0451100a0200c50050200030b20600182e10301c00c87c15180007a8000d000500d00800b01150344c406c5a0401c0e00141140c0c0728201800b02c0c0101c030406941d40a8cd0b00d02490844041c1d01503000f80201d00f03035607000c0501e5019880701e1000b012507440114101d0b80d040000c04e0075114800702c0650414914a9400000c0701d510010841c0d001800036a0780c0e50142d15104c1ca04000341081d17a0125040040a0001c07840410400c003501800c45195610a6034030f901e1407402030b00c12545544000c00203490402c801c091511001c018140f180c0301e21800041c50041290a441707240045020143c000260100410f1000b000286400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 58716846 1250 58715596 58715599
    0xf0207021c0c0e010e07140c010e0303010503280813050d0311120405100302070203120a02030417010c050409020307030906020d060806061009030308090304050301050705030105090a0903021c09050a06030209 91
    0x40310b582c1c03a40c09859007081c0c203200b0f942d6140d240e000010780c07181c40313455048601c080460304030b40784c07400440354907003500c2180f10554159000000100a9403800b04884400e4003a421403443c460002030002c024268011800649000c070b00080d0444591070aa8503000039040c000c101580c03200c0103003402026840070010941c181e2140314145d00000640c141a00d0446100601c0c1c0161880b048100310302035000b090049030180310f80e110300750311180a64040c10070f0a40c0c4d0360080d62250301e40312543e00d201c0703e19018101c941c1d15020050b45100d6000702190140e42c120200565240c0310700c00d00303c00401803114060034881c0301240d000e0000b4003d8002c001281c40780c0c000c40d1a10344590040203a050424501340010907858103003000002c1c001c00b00385501100f81001d4900301a80c501c042401c3d10300460b003400008400100601031841d003001c095800c54443c4004001090003550013a40c0c0340000d201c07131412480d05480d00040548104040d00140501800f004031040c0c0d940c07400380181d0481c0c020715 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 58718096 1250 58716846 58716863
    0x905011403010506061c020f031806010906050d02040507020f0708030a090509010e0406090201021c08070813050d0e04020403170903191502030601120c020703050d050403050705040f0207021c 84
    0x810080c0707014040c0038020140144028a0801081120700c0712201000c1d034180d080b502800029070102000c0080c622411600440403407803448000801d042c0503058100300c01180c580101800b40d9100c41220b0b001d25503050303030300081d40e4964601c107a10340260040a092030b441140c0c400f003000c0c40c0102c0540031039903071384d100d6040d401d0701d0b50100450704009011b41032040701c5150010300451035507008200b41c03e00600664182c0e01110042c0c22503850f0240c2c00c1c3c404240103100303200e0070643c0014015400601c190b00000a03071802d03a103581c1c9481032128846d0412940840c0c0c00401c0d550365040b00c0c003c0d0740c41032611706504003110b28220281c00a050881c401d0107844070000c0c41e00011132121a070b10368019803542154902080303800003500040c200c0c5041041f0001400012202e43c41020303210750701c9400524110b40b562514a05d05010102e40c041049001c0c042040007400014031070007554012940411a0b01000021070028012108080c0d48201e1016403201080f004000c0941c6250144902 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 58719346 1250 58718096 58718129
    0x304090b060d1a0915010228050d05120703023c041d0a0c051204030c1403031501020d171b04151107030201050a030b0f040f020a080901060f050d060f0204090501 71
    0x902c00c802d0800d1000038056005401c11462030402c05202230040702c40919060498a050745401307150110008403000400c4000489004010400403d142e0001592a00b545484043c0e9074502500c220300c9940d1004002c61600d1030180150010036043d00d104902843e62660b6580350070410038030110480b948032010200100f11060f0260207090f00502c880d8841038034025400454520403400240103a082203201c01c1e1810008200c1c01902d83c0e02c400d5078004540324106610340c0d40440c804410410b041d54010110317040d100c1c1e0081c070b100240d25080303011140c0b2a614010341c0071003c1c0850030020300d540e0300094082139640c4c4003483c444400b8141e50307803030308007044500e9015501e50281c0006404034409200000e00f03d0300c01e17081803415000c082c0803a508400b4004c08903064030041c41c40401480e4010484210881d80304100b203600411600080c04124030b41151039603601020b0041c03501551000b8400c80600c40990050070003203d01400456440385d0b01c25810004103000e0060540b0300d040c2404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 58720596 1250 58719346 58719361
    0x170307210905060705010f020a0306031b0e01050d0302010908070f03020d0203030f01090c110d050d0b0103150b090d0b070309021507031e0c050105090d0912050304090b060d1a09 78
    0x4031540300094a0301c4070300000e401c2800b0004280c001650443d2659201e420f501c820084d40e00162003074009940b07000c94001d08600e00303603010419003038a9428244c4010002c1000002041d80141180d4055811421008003420100e0142c0018200504000400a00c0804000742d034500c210146000750f00340d4407032011101d0100d03100c2c401510081500c2010310018010000346078010304c50b151301800d01040c8112146005820300c1e04c5049507002041011405403a0b00d91075008030300400c071b42403808100780540744580c07030703104206806182c428407004248824241c031124210086c45400444103102c0d13107800c2c140103000c1e11603038034100d0003040c1d07182d030750918051014191801c003545510b412640c00c101c0c4a002c1d8042098010600c1081414128040403c00a208a5004014050141034240084400a1b000c1060b691000b0407910707403d42c110020030360100684040e5004e005000c505441c1a00001e0414041c80070740b68501460f1807030790f040200f00d4a101d0090800c060700c0740c010319901c40c2e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 58721846 1250 58720596 58720643
    0x80723031b060d0605030f0708071202030a06050a02070206030c07030f0c08030414070504060314010e07051e011e02010504050127080304020301060f0e01061707050405060310170307 80
    0x150306440311222081c040351035240c002c002d041c401450b54800603500d0b80d1040003038980040e0621040040c0c20020b81400084414401c0b440500910080342980100f035501103603541c00d022001070580d69980e4007040d5446020b804403a078451f001050552a070a0000c0c1402d903a80c05000e003200801c8030614650000c0b8016800c02c4001c42e00000700f282156201d86580c000c0f000000b212607420301a014000c00d5070307500c2c1d101f03103005140036401e918404800300107000d08581908022070b400354803086c020000d66442e6410103011007d0f00b100304c10b00425400c016220001c3c0c401240749203102d800e80c0002d500341c1c154441d502c0790f80620024041c40d01e4070b1b8007602e05240c406003c84034190621510304003080f2040f0003190031500c05000042c220b0768030031010107075050030b80003640710801d01d0004101c3c15038070400301680c21405a00d941c2c00303400c01c0320303028005105d00d11403940141400700006800519001103140100311106100c03d41c0101c0c020240d45a5014803800c07150390050743d61201d080302041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 58723096 1250 58721846 58721863
    0xe03190615080607021e0a0807060c030905030f070c0f05090c0a0e0a1418010302090c0c100216020114040e0f0c1603030204050a08010605060a033201031403160201050c030408072303 80
    0x80c40c103910740601c648420015040fa400bd10050507110a52000020820030041c141c3c4905034078401d450341780360301c4c3c203854000960384107054400f03403030005004681d0b03019000f5820041c140134651382c89080c1701c019142c000c1c000070a43d9004030b200d580041c40c1102e5550031304800d50f00b260515410356440b140d910354050207010180d08607851000003444079010600921075143c0c03041c01c660405c24141d0030b400c16a442030010b001400d100004250440d600043c5600d031003c1c0d2814414101070400c07035a001d941000400096908601c1400324101c92882c404580a40300c40780d56805914001d800c000e0084d501a108143c002c90010b48001f40d20b0506115400603108000c2480e450102e94480850180150140240900020300003200c414600c1319605400441060b4039900c413580340d03081407081e51a404000b1b0750280c0081001440309070540b02160900381d82406e00c9900d49181801040c9180034603041016180705401d804219149003d41d107541a2901030720403045018001c06240e12080807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 58724346 1250 58723096 58723103
    0x6040b010f1203320301170105010b03040308060f0d0f050606010801050a06091206020f160203060604090b1f0906060804060b0a081f1e050402010e03190615080607021e0a 75
    0x550744111002200c0481e40c2184c0c040c154005610208126203d100c41c0d00a82c800340034103000c0100101218400e008607401407088580d182d080d458951000f0f07042c030750b0080149200e50b90b13101d0351003210340e18110754003281a082a10080e4844e090718080b613481d4000c0c3c42036800305034170000008103868807014080c181d40981d80c90701a49803910034030b42c81c8800301500450b21182c003032040c030b010712500401a00c0310034503459000c455072407180189030a000010742341d240658106030526012a203110b01481d001100116542c03911703004400062221203043d002080d175541040c9000410b1070384145034034043c5000c0c4030104801502041040701c11242c502c80c80da00d907042815000c0410b407144468030440080d04001181002005c0d820b265201d40c40d00240b18219500c80a00095580c40301c10b643ca08241600113000309641240c50103030307401ca00c0a004181c181c881c4e00c3c0035414080f0303a0090004002c0c00040315141d081038035010703403981c80200044407580300e91418041310100001e00840d08541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 58725596 1250 58724346 58724357
    0x306060f010c0314040914010e0708040b011205010905010507030917031512121303060e07031502070c030203010e07060f020c060708070201110a03030515030c03030a08090a0506040b010f1203 84
    0x90f99015948800014124400070206000c0068015824011117420b11001002a10f80d581000d400000c0c80307402920361010481424104000a501d072001c844c192400201a0a5980d982d45040c40c0500f840140040c203550034041440046505070f0020f00c3d07814401c9110a11034602049089014041200c0c01c0907903400500301c80d80a0700b0f0072510007075802c030b454040d40c100c0a00704040c10f00541c0f000340310316110b450121703040090110034401c105a180400026000d07040c95070b101e050600104669802070503500103a20070030440c200e00f11030002c607030190081c05001340343c801f4036444005030b00c20030020070303580d054580d45607101045105142d070f0001c14203410403006885100c00c40d000003904034103001c40d080c0c0e80710f80d01100b0049481064840d91300801c1600d002c0c01006229001c1d03a080a00a070f20000c20701801d0f075800b0041c0c40b0086031038076240c40707140e6410400518001122002400ca80101d10901040c00140d14116060343c1c1c07001348141c1c044ea501c1208107125204804003400080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 58726846 1250 58725596 58725617
    0x10b030601060e010915051305010c02011e0306080f01090b13120c020a0b13080d02010204030506131e03080609011203080f1005060408010207050d02010b0a09050c0f0a08060306060f01 81
    0x50080d000414a40d40605d17100c0201034461022481c10030990750404046440410b010400762040f10385030009c1d06c8286408103034411a580003070b20380d8401e800001d180c1250042c10300b080f10302c82c0e40000c000f81400004c4509000e0008801802480401800c1d110305100a000403100311a19040120280d4414803c1c0c40044241d4821038003400d40c400102e91083c00204006a01a0084044d21b04078441c0100242c41d14036041d03910380b514032411081c0040d64010b00c41000424004a440365000103d80405440c0d400d5520381007081c1252100040703044140f4007c1002419880980d181c800c1c0016102803901d0b90300c3d0000d070403c02586004c007e00007038950000600c1d6040f16040240c101000440840000380c07200006a00743e00190840307070325a075021a0a0040c00000c2100240803c2107000802c00c500400020403100356580c001d400e0141d40300e6012480b4004000c00300e032820980300201684420309144010100401562a28443d1240c240407038102c2ca405401036019a00c140c407049000d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 58728096 1250 58726846 58726859
    0x5060d0b0109090f020a030318050a080c0105030a0609021c0e1513020d05061f09020301050604060c0c1a030906160503060118080604060203010815070504170a020406080c010201060503010b030601 86
    0x6100d591004c0b40da0030b0001c0d01500040c1c44005442d80514442c0e01e9002003a28106240c4140081c0e81e88514400c0e408808208119040483c60391040c2c202807800d10b9030390351000302420241a07990722820206100003103034490707030308122405080544480000e2002c044001031055440c0e442c280440588000308000c0380310001807450f10a0101d1010380502c00b05282500c415080c00001c40c5d03010340c41001c5100e801d9510000791104000350049900860a5505090100380180201d002e041300740f003101941e10381400b482d5001c403c020154203201000d5110f00240d100625041907a0b00e0040c0c0c0303c1e0f00045070708103100d10001585000b8035030700c90713045a80c1c079801100d4440c1c26002405484c1502880400d91260074880144580d004090242c1c1d80c1d4540600c0c0c0c0d2401200c212408004881d620a0040c0282c1c4242290202c0d007002c0700d07400890030320380c022a01f8002103610080d40180751660001e0100343c04540b40c08040701c01d1f0005c114940d0340b041450700340c445076032849a040d0005401030280 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 58729346 1250 58728096 58728101
    0x61d12030f0a0f05010b040810020304051e030403080313030f0509090c160819180605070f03030f0513020a0506040b07081b0f0709050601050a020a03200a0b01030605060d0b0109 78
    0x220101c0315021421a003100f486a003143d0302030300720050311080001d041c0540c440070460050240c80401e030461851034181c455130344409154032143c014801e0100c031180a03041c00c100350f802031130f04043e000e41d1b64200300248000300d035100007048021036054480350311030760f0040301950f00080d000381c8a00b815584011b01031b0b03101c0d8041001080000d00324510b98000c03500c1c0030058940d49003040b1390f010100c0403880c40601520b5030720101050305801204213000ca1030b440801d8074001540f190318014010402c0c03230150080e00002000440300c03441c003000c014911850401ca104c45034000e6900200c0503450360240400d6200d18002c1508200041045c0c4000844440040c000c80c02c818000ea40303c002c1010130281480841f5900d0b80059105817801c1c02480c0701d030306c80d01f03811030703403d08101745880d40d50740c4041c0d2108403000700a401c0c010040d199408001c44500e010070001c50701c0c003d840800c1080d00d0b02060310301e0203001c2a070780985401c0000d052824141c0c5240c050f1038000c22448030587c60700c28524013 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 58730596 1250 58729346 58729351
    0x8060405040c0b0403030507020a0f08120f0d050c0a110c030309010c11030d0512070905090406020307030b030319080f0405030712032309060a0c050306101704061d12030f 75
    0x14910030b41d900019807140144050000382d0f2081e60f5080d650a2503004104085d440d582201c205025002000c02070a5000600d0704005644034018540b160240000004c050040540b1015a00c0c00c1134200810041d05200402100c865a02d8400400c020101d2059030b510b1103440d00c42c1c0550041100710000d40c040c0c032000d007561b8420b0320402c260307428400101e41042e20403645880420404030f4000c030201800309025030310204501e0f002054a03e0980000d602040141014180b903a000010850640c448e80109152100203001c6035900c1c0501984218000035240c2c09400298000c404100c9039001c4030101401541c20800031401c1807116115582c0c4545054117000903d5551a00103402159200d100070302014030203500001858004203003824140700070003103050343e45002d0320503400381d07089810359810230011ba800e000e00140750b40055079050745d440c084148a104500c2000100000e40e00100b010b0400e002d00da00781001074a0b0916a40d0f005011054600241480000d1207040d15103901a07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 58731846 1250 58730596 58730603
    0x6030f0515240c031303022803030507050c0a0e060a0909170a050c0a0606031205160b0a0e010f05010503010e071503020a090306090f0204050709030b0c0f12070c02130207030806040504 81
    0x10b00d0300c03c1c00d0b50001c1c516801001303440c3d46030026990401c1513242016041211803034007000300807060150302c1c12607094400c6000c024103000c0082454001d00c41d04110310018035402030841980185c80f06036000142030f044410b580300e20250b20020914030320602801001540c082001d200201507413007009078582050000070100311061003007004030701040040403d40c0d8042d0200180090541c02e042140e114010459020b00604000442d400c1c1594030300c5000c0c1940000804a054440d42d8086014010400042c0000d40c2032980d002101000b13a800641200c0c011002040001e14034240d250f101c14180c032501546000a50340c5483e200c3c000d03001000070562521b8002d07180c0b1b0b01c070740e0340c4000ca880303100c000d40e46002c1200f02e09045040074441c01e070b00b004160600d01000c0c1c0c910b503078002c1c4089005110f41c2e00b000000ca002c03110310010005461042c0f030a00049000c0380b8040500070601004400140e00c01d1f1258a00210240001e100f21040310743c140e91044859034030103090001400b80036000b00d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 58733096 1250 58731846 58731919
    0x7030b0c0702030714010f03060602100905070b070803010914070503040821090d0908070b040302130f05130b011410030507171503010605030111190c06020406030f0515 74
    0x1c001640c062000310701a2251a06500800000030001400c40804c0c60b848030502d864624280002030f0005590340d2000320480010404400c2c61030301d541040d216038002d1181c0b10000c64040c1c10861200041e606031001d00340308010040000b142d17884c400e40213903041400315500300040340205a81c54000e0030191044014982c112160084254110710200e840d40c01c1d0303402c40c8040c1d00c0001e61161170700004158460082941e14100303091600c0511079884001c0c03250342c010001d02c1801c605500070140ea01583c0384100506d1400850181c120307280f034041140c400c1f0503c000810810251a190300d81448042c101004240d00f850003a0020140980101c0610185401c01092030181e0394030b41c0d2160445001855824600d0b0050500703540d00c0b0380101d44680d040c5504001c60084100542d07200c405104410100201005400c0d18004840c4c0d0002c3c010034000076010500a405401c031102d15031666008100c6035450910101500704100c03002c41c1e2040d0301d030b0b141040000e192000f25a1418003480b80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 58734346 1250 58733096 58733107
    0x60801120c0f0b070201080f090607032007030905090703060b07080d1e1a030a0f0b13080a051206090f0402060d020904050103060506010f140a0503040f06021602041b0207030b0c 78
    0x62203030380c01c0b03980d000c180c0807600003c424007196030048807640c10800f4100300721840e0800c002d9060700c415005003190300b01540d4000e050005e030908505a24556850300303240e0741e6454107080003401110240145400b401c101800b00d8035072886072045d5411100f800c03000e903041921703035520041130354020070120721015124001042261039100103c500f40b0b101d81e030300180100e2450003041034403850f10002ca00c240c00c60500320340440d240702c500c081d07029841b039168038403a0b031000340d080c1c0710500c0514041c00d00031000c41da042c50140c01c44010500700c010360081180d980e4800081100e103000455180301c503408043c020a0050401c48050132100d8003018025040549000204045501c240c0c01620503075218024080a960001c040b09542c0300c142ca081540707058014402000340c4503c820040411a00000040c10b20560141125a00c0d510102c15569510700c00b92840c00380c84050010780c40f0314540101460078050502d80d4002c828800d4020f40510381c515222100c0f1004000e00c8503020361000c005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 58735596 1250 58734346 58734359
    0xf070f110102031801060b250c15020105070207050f130507051e192f19060f110406020c0105030c12040305070b0a02090d12020106032001021501060801120c 69
    0x40d610540c140f4510500d02c5144da03443e9030a40310181c0c021007200e2010445400011054041070034070303c160140c01c0205c8441031400c0740f42c4180c194005a6401c0c00d89100035017055064002a004406070b500310703920305031243c08022501c07540040b03442d070101c0184420500c814694002584c09600342c01c140307042146011140070f4401c4c00000741c2c0000e07200007600c20107040b100d94068080d60494075084c0c00c2304c290031030200a50a256031001d80801061080e40306405001c0064040c8201c80c0310101002e5102c3d403400b0405040355100c0c000d0864100b0151340004c0240c4404d0728211041136000340302c401aa2001510136a01c05084210895001c00080a01030000441c603801588207a66403603503807401e81884646110041c00c0d80c0c0701079004000c484056a1604400c078803132a0850f25803103556000381e0041c0c1c01094150300041103c00e2210710b8100c28129242500b000c2c070402c5e0285c0c0d41c184800341242014031000d0142002141c6180d00601902c00b0894007092058411202c41c80724a0301d0b0030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 58736846 1250 58735596 58735601
    0x603191407050a090b040e0619030203030712030c0206060306012105030708120c03041101260103050610122a03170d0b060304030807030c05070611040314060f070f1101 74
    0x294000701089002410689041d4883c1c22140240012029581003030b040200355031040c800a0a078500c9034007840e0311a440c0e140000c1803c001035078020100c03541c074520b46c50b0130702d00f50241415610200b46800340450b80140049480ca10610307000f40540300b503a0130b026840f80c4c4800d80709c80c0700c841c0c50284143c80000407800c000a040641c000e195032601d0701404c90034a0301d010740040c84000d010070300344180300006445082007007000000b420440304060204031940f19803000c80c01c5540d1080501400001809008509207006000181c4002d140300c3d02e400072164a281d022800510001c0200d2a0000445204c072011903034890703030407000c00300d00d9490b150418801071184070341000c0040000c048455207854801c540c0601c400750f90700c40c2940f400d41c40291142134000c00d1501030684400805005522680c1125111507008a0030030000e50041d0400201340c00c28001156600c1c864207003900d610300000740ea50b111340c41212402d01169103e0800301c6500d5003810b00e18040c400408c5001030485000e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 58738096 1250 58736846 58736851
    0x5040b04141e060f0106090303050405060a2706020105060301020c060402090411060307050408070501090501020a023a0510140c090307030b090109020316080a020402180414070f0e06031914 83
    0x1008105a04240000122132181039200b0410710800300c804200080e0070006640860340704584803626541040010345035003106004411940c91004020140b50300d8206007501034401c02d80c020400c0d940c80c203091500302c1c0f2801900300710725070040c2d00282c014134007032040d168018802c4240741c55491820001c20001e4200780c2d0b4880c04900c012605000d849020001040140001d20700030015038601790010307480342d10303070000a8056251504074100722010000c010f000700c80621014100c91454601d100300450702d002c0308071298005c00051191a40b403e009840031031103104803044030b6880754500e003400d50b4000d02060390107019801000010804602c0072a20a880301d0f40085448000d92042505080c075603440790480d2000600d080c0980d000009070705004c264184d0780140e48072807000340800f1130008141c2885e4068180107604848501e001c285034055601fa0310703041c007c410402d01c240c81c5820014441a0051402e0000504462110001c05460640c4040009814411010074040d12404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 58739346 1250 58738096 58738153
    0x50106091a0c0618060f040b01032003030a050a02011a031903030b0303030a0c0e010c0809040f0e0109031809020406050a050307180b0927040f080d020301060903020f030105040b0414 80
    0x302d584c90a400300003841800d80c4885a5107403644946404ea5902030703408030600018240b00a1820306000d10364201503540e680940080c100c030740304c24142400070025800740c210700d401542040b0f079181000c11440501c0036420b000401070444c001d8602c0d9002090310500200303908240e03d600c48500583c4090008502075000b0171408200e202020402800f56500306150034100305451410302d000c219140b0660300028801c540100d0315145121101d4083c000c080100b41e9603510b481414020145c0100c646140201003902446926641e01d08a00481c0a14030411000c19230400203050500c2c825001503600240e9401c0c010503100603440013081c106140d0704071211f252400520542d15140406030400941c640c00b8529035249951041030030312580c01742c00100029416500c92b010400841c041d034042c004a004119102d40c1d440ca4000d000107d0b500c001c0c1d0040b007100640e2101d0341410700460b03200b140c0000400d8819101c5a0b1f03180195505a1101615401102c01100c501038001c1400c0c0c0040d0b41e13 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 58740596 1250 58739346 58739371
    0x3020c030d020c0102031015020714030705130509061806040602070c0905040b0603010f061a0a051e03070e0105040503060403080c250c08060415111308030a030f050106091a0c06 78
    0x800310383c43c1241f84044d03006981c140300341c42aa030000c1a070008100741940c40112801510151107004030380703401d50711380126600981910850a00c0361656010314411201e07181255600d0302c9101041070081020280041366820020004020032000e030002d004c01da105d41d4000d48500c0d0b45640c41c1d800c641c015070b030890b000d149a07014000546802d014158030501c9808007040310f42e00c0e0800d009082d0024850109042c1d4002c56000c900a0081c02074645101041420b04180301a00303040d0390140d84112a680c002c85d69480000385154400d0301642c0035110083d00600c442d440d41e4a050351140401000f00449540810504140c04480490000b5800417400701540d510300516080030700300c48a4200c1406075001c0303c100300218504c2c50101d600d0060702b00000920420188007154103100c0c90102d61941c00d805400000c2c03080d00000140350b541802d40d01000031f8549180d1017800c0c0ca90a01c6184000340c0150000d00140f040468215940d040b9a0940f44c030741400301d02c46a042c010201c545882d0b20381c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 58741846 1250 58740596 58740601
    0x14120d0c02060604051003060f020702030f1609050411010804110406060504030312020a09030201120609090c0330030c120f050f10050102030a0e01020c09010902030109060501080603030a03020c030d020c010203 92
    0x390100442c42d000441141c09110928180e1410f18082c1003078030000e03064036250307129554051b2451341144d54080e00170301510466900c2100040d40c4140e00d1104003006060780d8030002d0083c0180c46161300444e4030031401c40d8034040c0c6800440d400d80707000c1d0058a601c084281d0780445581da501c00c1f60001c08294940765161884c5050140c10803030b820352049030480c010440c6001072035001c50030009032682424862107682020f251000101001e801c14494a450304129070117020306407103807004580c46500003480307c120b094802c1c1012035203401810294004000900b901354000d400c0742c003e0205034503010840d00c9203038030a007081d21540e0b4804113100d03030740741c050005803000d02070607981c4250310000c40d500315890f01000035560310454000408100d0703070105400c2968800c1c829242000d00050000000f540c4032040b0074020b520a120b179070b50307640c501a400a0954040e00c541c905c036003c02000385040a070040001e8001c0e60100c80c0e60441404100074680c65503805101628009200e2000140c0341c2c0b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 58743096 1250 58741846 58741871
    0x2060d11190315080a020d030309080f03040803163009050615040e030316030f0204080d0f0801060309050303011205150c0405030106060504051c03020c03030a05030f01050604060c14120d 82
    0x440d21504540308540004461030050f0f07d03004071703081d0100c0d40b41c40d0001d00d0b4609800d140c0c4450182081c02905030310700009002c28019810042c6001d10200300c42c1d80d507185c030442805d03500700c40c1c9021003805000f5461444c0e180310110f1095814448007042d401303c0d0313103912940c032507041c4581180d803040c448c2500700300903500303007420710510584048a000a500e1400c00503c0100b10a0303290354650300305901c0e01e8214044071010340584005020503004c43d40c1c6001300320310141502d03c0f44082540000e01400002074403030311070b00401d441540c020307002d1481d603420314120f4030034400c10030000d40d00c52140090611140c00000900e901c03460709940310b90340312801c1c00f00701400d40714950b00c44810484284424846c3d9a1008064848003050300384442d000b10300c9140c00c0c1e040c404040302d00d552501000c50b10b0420b10780c01c00000c40c42a40080c505254aa8030760b0b04107e814041c5020340000101e070034110710001684420b950b81d40303080c49800c80c0c00e43e003280c441c0c07007a942c0d00c141ca02500007922090050b03c003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 58744346 1250 58743096 58743131
    0x30c0601080c010f1b0203070e07080f1005010e0d050705180708010801060e010909021912020f030105070212030709030503040f03060e1b0103200c0a150902060d111903 74
    0x2062024079001340081c844c3c0d40c0040180003000b2441006880d94140c50b011503800300500d600500406c0c0401000c2d18140fa0050102c20048a2014610a00d140050105510b0350110f1040e10b41c16151840500181402d00c400320103c1e607001c42d014400c4401c0414580d48001002404100f0f50454522910701004000e100d45010fa200040907030612405124443c00b5102181c19105164800103261407240006020641d51641494030102c0c1441c4c04501f000c0c0702c4107076030725250090321044100c42c2c101c0c04ac1401c841c4102c60b07202c0180c00c80480c104003c6048130046810096a00d032a9410540329150300b42140c1c083d0340441e400301c0c2004000c0040007024014222010011001ba0064482c0122080303003081e0600310f61410107985440811039131600604a07440ca02c0c0e400175160300d0701040d8060590356100002c0648041e990442c500640130b0040c010061300642c084c0400f401c002c440c60510b80501b070200c020303080840052052003055200041c1c0c008020310295000f040c0d20306054500d050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 58745596 1250 58744346 58744363
    0x301030311060402030d0f18080c01030b0303040f0e040213060b03061036170a0614010b040b130e04050106090e03070f08030c0f0c0a03020d030522050c03030c060108 73
    0x20301c0d820050403c0003503500822850300006007400c201850b041e8401c0216540b4551030800040d0402d02c01010500000004051706405000e880410405c0c0f001e0040607500d0246109040301141f08031803d001c521200c2001c5030b00180b0242c10645880c81e20740c40c010035220030360007806154902008110231840c0040148004001034104822410118244000c03c4142c60401c3c01444809000c1010307a0002d0a003003e00030600c80303a030010030b405850002e6842d05c1d6102c45c150f42070b5050100c1f03020300c0442c444000b41200d0814aa0f103103050715090880c01c842d086801050000e103444a0b001411030101c1c101d051003148510000144c06051517804402c50b4a101807000d06a40107100c04070019011b10b07214980d4a4008880e03680b00c2d40d54a10002d11803041040300007111102060101d02c2d000001000c40300300e4031030340a480e1074001c062000ca0841d502103c00c0c80000d000c80c40d40440b440d081e01e42d10382c080c601034000d903116200300d240400d180d5071007540d00081130b6105000411140205210664 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 58746846 1250 58745596 58745627
    0x2090103050c040e070e031c180609060807261305120c0a03030504021c05030d0b010f0c03030902030109021c0c0506070503040611030c070906080c150a0e01030212090303010303 78
    0x742084e0815001e00c0b015a402403d4905028482c00b8050503982d04202c2e80800403000d1903020503200c44010018032803001903005c01d03515400c000700800d400340140758103410740e822a45c80b14120358503100221050745100701a6150b4070090201403103449421001d0f180302e012010441c52010985240152800c0d1805141018179a018041002c1410000c182a02d80700d4140c5004600b0342c45500020f05501c86c154144a00d00c07501074019010410040003130080342a040c003081080c107803c040190341d010f00800d44403000800c20300943c00068002d500502e42140003030000192441c1550118400d05400c580b00c00e115240c41030003208201001c0800d074080c241c1a02c090b07084c0a01651403a589018602464040c04449030758929082000c100b540c03400c104440c00c1f5103031165642500801400103010300030303041c041e40c0b2405403281850a0711250868200c2c40051800c0f07074804044605000452003181015020485040c040304207200d1140a1007009010359a02d5255207009130580d500865001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 58748096 1250 58746846 58746871
    0x302041d0103021003050403020606060705010b1008100608071205090f010504110406080c0d08070f0b0f0403080c1215010e0307150f140406030903031d06040c08010603150f0e0303010305010209010305 88
    0x2200183d270102d225508228240c8429846030200d00d00340e40500000e2241980203042c07450328000d9954402070780350082c10b496900e1021144c84810484282c18105c90f2480452200c1649202d20080c50340000e900031010410344000d031015000e07460a650080d6003e44040800d0803108146140502c200c074020a507400c0104034481240340454540444404040e0402102244c18001d002e030107002e0300c0c162903120008071001d2402012000301450156420740000c1e90700d00c0094002c60307009080b107962034a100c00701d11483d590f03800d204098074440e8032a50304000e801c21302c504c0d06860801c214000b81c00194981c0c200316144071b01c0200300300306800c4480704100c0b81c072076400a0850b11004550036186070303190202d601941801c2c264081d210794480a0561580e1415082050b600402c00d18052885001806000c5540301d0310305003683e82501024004045004040c4408203c42d4054502402c24035070201d04150303e80c0000b811034009900c1642c142e5000038a4244560b40341c0708055001c050492070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 58749346 1250 58748096 58748101
    0x10509030a092c0403030501080624040507030b0a0905150a0f0b0306030a080f03040b07110706270303020706030c02030f0d021614030405011209020d020603070302041d010302100305 80
    0x1031202c0a507210b01c80740040c0d8902c0312082c101000103890401c1c05000c9060308181011302c0c0c01001840309200301007a03402400041208900c401c1c1202d00c8020411410074541c0148400704001040c0141202c01032558444000d420307900c50445c0040101013031140011203107040f51008650b5401d140c640c902c80c940e0007201340038041001c0c0256082d12028290f4540b82e98800000c80d00d000610703000030307003001008588c0c07200c07040542004510076886201ca0070500e0b11407080603201d030f82c440e21003040140c100c004244840c034428003200c4044803124203511041e0900c0c180000002c00641c005400680200a041c4425070b054024000441c0e4988000c6103002452060f820305409030101503018107800284000411241d2000400d40c3c503000048c0e442d465071080c000a540c0d0340148655070204906040d006081e00c1240304480405401905010241b1001d5081000c16880107001d4424143c1c20701c000306540b000c426801c02880c01c80c2100717104035411801000340d103040c410a02800c040c1001c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 58750596 1250 58749346 58749367
    0x30109170a030204090203240a0303091205120307110f070302010c0618050f010501060320040501050705030f0a0903030e03161703040308030f071713081804090b06010201050903 78
    0x108620903041a4810340d484120303141045000e880b80794865100240084113004041ea11440a120105403010a40040415000074060342411034031014012a062000400c02201403801d442003181c414802d0700c603803140062001c2e003603420641c0c0080028807905614420b030241006000d02d42d40a132002040c0701481d40d80024003210300034000515050b25000b07110b402d03403000b500c0e60840c50391090aa91034000103010040c000c0500b4424100000d003080d60078420151411514070206850345516403401e400d202c015a0580d0002600302d41c28032040215089c00c808a84c094941d00c0f1003542c030458120f2540c20001c241c00300c0e0700d010034401d8110940220484c4030894803035080340c11610b80c10342212500d080b9141107000d00e90014045110000c1000203041c103405105101d00c4190325888041203d0100c81d1400d03200c00c0700c0710321a0424001c110404603801d400509548510080d080b420303000f4203c0801d0036244081400c640f000d015806110b895a0207000d0103070b02a40c503800035401d0140030807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 58751846 1250 58750596 58750613
    0xc0c0607050a021c1a0f010501030c120213031a040507090507050d090201020304050402040f09050106030207050a0b060a05040c030903110303090a02190b0412030210060302060906160b070f0905030109 88
    0x1002032046940c48400d00041908508204e04140c01091001c031a00d201442d05400300c00480b030103511710301c880b400070500750f011344201070015000c0d84c2c40c8507260300d8800c0141c009512500e20040284c5490380d0000014100158003088a05400000c0b15542090314145103003130032a03007044400c075041004000541d0340c010180d6500310074124021a8804403400181d0a51195820441c0c20a0000402088c0344500c002c11504452070380f2010010340ea603c403001ca01700c2c040c0d00340090040d0022205c010200d80580c09013900520000d1403a000a6a5038000400b101d0b040100903000c207488030010b40915800031100e00c032941e41900510301d180f81c0700d40c0803612584e081000038803401c0309490030104040c1c02c440d220043e1200341c001c01d5403140c40e010540083c0b80010812001482800e0310150703005846d00594045a501130400c9082020b6a0100f1a15800c148822500c2c200201d03107081c045803151403800d024583c03907210f2030110403000e5402088110070340c004601aa0401043d0000030b042030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 58753096 1250 58751846 58751863
    0x190206090603150301050a0b0102190804030b0a020903030a030c1706090a0c120203042a0605040b070609050114100b03010803030705030613050c030f0a0e0a02120a170c0c060705 78
    0x44810707a50341d036243d0041840700303a10303c0c11094066203400100012541c599000444151090f001c9a80118103107450301104070300c4030300c01040b0b0716045c402040099090381103d50440604840507081c0b80301500801c0c59a00010344600003c1d4503148071002e016080310f101d402c610300c00700c542c101d0780c80c0600c04a511088081c000c440340d207a440c4101071a09119040001000548140c01d55583c02c25042211441d821107042c090000004200345010600300c000c0c42c4100c072100e0b1511401e062400710341002c10340000070180c500c941c0310a000d0303001600a00c0785a01e080905484100c0e6400c00142c00b200c02d07805030f000b014502c8820001400364036000000d40750b0044d00b901d00640d036070380c441002c165460358150f44480d0301824a0140050345081002a40c0306121040c006505ca40c0c42401d00001e13038081170b040443d1034105200d00c101508044064241d2110000100c4540321010b03035400d10302c000011448100e41300080f402c0c95500300d05015482c40c441c411102d031400c5c8049900c07110380741e1165 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 58754346 1250 58753096 58753099
    0xf0105030903040905010f0806010b0a0e04180b04120f17060402130503070b070501110702100e0a15080a0606080c0d0f0612030e09071b030c0501020906030108070819020609 76
    0x3200041d2031103000c0045402400002505200c1540d5800b000c60040c281401020241e019080010a510b03401e04243d450701c8102e0354540c6098500b40041c00001c10011a0003080c4440c14024480410304c402d8180b400349200d01d0038580c1e04025881c004000310790300104502080320301064090904400c11145c2d4005004407001a80c41c0e842d0840d44108205030f0340081d4040c0541c6900290640000c1d0241c026140120000d01001c0e03001d010140e039912430940000e611a001003080461184a0b0200303c1210501500303640b02580c90760104c004441c20035018400142030b24040210783c01290041c44020b08076818111064201518068480c0c0201c3c0c20030f0102d41d0f9518603100845690382c012a005102d030a1030502c4000c0d1f10300b002040b134400b0700c61701c50180c1807050128802d00d108036402903110030926031507904290180c0d070444d810001848140c0700c03913400344108005651850000d500070f0000f2802040b54510b4801c1e00780c00d240c4000080700d0007000c4418504096120304c4112001d2140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 58755596 1250 58754346 58754357
    0xb0f030a0809130c080a050c1c0b03100510030201020c03060f16170703140f0402060a140705070b04050108100e0c071407030813080303040f110d05030a020d09050306060f01 76
    0xb91408281891815002c207126241002c030554812900101a00d002d8105000c007808159224040e40c6224460241000b00310310a20500032003d048507404800160342c01029036000700c02680c8400251481568404200358206200f0421980c04002001d012a0182d010b13040714504040000f1900c10001e00d400c0c0e00083e40486890300394820422040066840b41902c00d1508098000070014000a880055a188158042110850480551449594000c02861914041410442e44581c0c4495001e1043e5000c1c008100060400d2003a0400b4105da418015140c51074103000410300d0402070700c50840f8262207403050160100044101c2c0d8412140f80e103280c1e5640c01d6140c0340b1003034000b40d00c0e00d0701c10f03018100c0b0200c1007082c590001d0510300700075035022440544550181d0f89074481580c0060200b004441c028000504000d48d0188005008256107541c0c415515100c0c110b5110b4000a801600700301c026514803a04090320320086d10b81580100441e203000c202140c10349603a0001d441c140704 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 58756846 1250 58755596 58755607
    0xf020303070c0303020105010f050609030705100e06070b060f0a150c0311010509060403030606090e060904080c2e0504150e030c0307060e06011e0e07020a0f030806040b0f030a08 78
    0x1181041180c108560100600500d1507907401c00a00802080c01140d110113150b140000300344c54440c042d00c41c2c5410050207004500d1503c0c0402c60f551030800018001c1c02034000911143c0c0d95800042d0101034040d20300840d03a0300e804001c202069000c0000b00d8402c0c0780320b1034103104a20f103102c40c0c4c2044d01d0150404000401041c03c040d00d503003101e41d4015090b5801e040c20828040c4001c01e903940110b210740c90030f001c855198441500e00c8501401000380d1030115500142c01703440c1c0722980540042c01000403a00d02843c802c007690034040000b07071031800d0140d4580030f114864100105042203c3d4010400c014130705190707071204052058423002800341c42c1c45a040445010082c8211200700b1040c600300c07030303544c0300c50710b03010b00901280d000501145c00346000018800000340c134691107502c450038140301c0315803e0103c80031491364041d0000c021403140ca903900c00020105c01c1d41080d15030181d1540c11043c038080040200703403110011854010103501c1c41041164400145c50034046500900407034407035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 58758096 1250 58756846 58756849
    0xc05040e041713031b0905090c04020d1404030203040e01050402070f020112060f080a020108090c0d080a030b060d0e06250c02030a02030d050c07080318010311122706090601030f02 79
    0x5010340303d201c1441c2c41e0800400410881d032412140c4a0040c03510098607529500c0c9032200c102c82c0212360503101600000310759440e030301e01580100b1801d086014005030850369071030180101d91080b1070031070240c2d000140501414005904841c0144002c41e819440c203801e40d9192506002180c10081c14800c0d80354820f0740041d110b0300008064101e1610101c0c01550300d03c04503a03548288102a40450304645c0460151080818404070502024110121001c0d140e0358070700480d0300015502c130405503110010026565440d0080c00881c440c040041111445603000301d04200d00030380740c005a1400803403404940601001c030003803800c00a080075080842c40d030010070309003004c0f20402540740c050462400e03071607a0040301400c40c200c1c0d01360480e81da41c0d0300d441c6081d0f601e01c01d004141000c416460003100840d84203030411198442c40344111420306c0100c00424011031001e403410898001520010030b50f03116015400d030400500c6100410300c905044086588429041c0405402d81171000312007401c0d0f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 58759346 1250 58758096 58758143
    0x82107030e060c1f0c02030304050c0108062206090c030902030c0402091309140d0207080312180f0a060b0d0804031106090d0821072010110903010c05040e04 69
    0x8080e203200507110303401d0006558442c0104c1d00e031051082103107001c070482c00741d510002c1900e1186030f001c0c0050092082e00001590024001004290b229030499040408000e01d0900c07250043c50b4400007190301d030b04100e0310350251740c10703205034400301490b1409034009030b600041c0e02c00c4000800c1d0b50041e642d00822021607460003c15a500c11114100100710341004030755005404041c014a0680300b0409103400b00705d03129482ea00c02c80a0503030050080004c1c082c043c14106802142207034070048c020071140c502a003450010076401d0b985400100110341401070500910300404001c1b00d071505040301c036035a00c5400b80502d010280110741104200c41c0b90b85c90780d01c1181c1d0b20420043c0b950382024282e03e4003030699404505100c0346481a405540d06c10034440481a004800648603041002d8030110000e070300c420700d020400c0d03140c0f0455406031191441449408403d156560b440c0369100c01410515082d80d00b034030b030f81604101e401c000030004441e140c372500c1c0d04280d02c20042201080300700000d481 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 58760596 1250 58759346 58759357
    0xf050904181502130611070312020a030206070f0f0c0807080f04090b040603170a02011e020a02070503030301080c0616020901090207020103050f0403050a0c03050415020304082107030e06 82
    0x20040c1c0340c420340190440150070321011a500c107075038182003081d1444481042c1e00039458440c103100c506840520580340192681191010301800302e03080c5640d00e4413043d0f07003001e841c00010090380001c01c01605055040c800140d005d11942481d4854458041c00101003901c0c1d90400d07801c00404600490801c90103500b00c1e08001d070801f00c040c0d200c0b8500881c5a40710790040c4900c6080c64604402103449003010302072801220307041464041e408400c00103040c00b0b80e01040e1a002155610403510000300b80c11582c001c3c52521000c0c0050300c038032010001a1400c403903134208034801c0d40148010402d003400003d040384c00e0bd1050301c1d22074440060400303115916400c040003d600000346400802c210300340350f02030300d00d4038004da0742809191656407850710890015500503000400402032202c0d0940101501c3c081207110745003103403400399240d4071034003803200c0c07485140010780000400b004400720030811100c0c0d1110142c3d03090025580e2105600c2981f048100007418040070784071080581c2c0d11501500e2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 58761846 1250 58760596 58760599
    0x11b0803011d13030912030c05030c0f0d02010b0a0e0a0219030b0f0102060105240d0608100c081314190506100b04180b04020403050d0206070f0e03070e040807050a06200f03070f0509 80
    0x2511207607003072f8060b5111000d003000c0b440b007803060054000350f072441400b8099800c10f01170004416241080302c0c1c0c641000b00205003910003902007007403000038204092030000c0b2440341e9500043c03c007006001c000010454804150440d07103c480184820341c1d42d040641c0c81e100c0c2c0d1220610f44403130b4a101c160b8103405041e8164000514040001030241e20106541c15000b00440c0200100301005006441c841c81c196280040007501c41900400510100c0482c5070040f6800201c900c01000c5103603000c18059800411900c542201080c0b12150952201d00e00150103e4509075041070300b0428410128094491150170654036940844865119070341260080c2d9045015500011000b0801940d0b032542030310264006009141c06818092182010b2424580d004014145103490100c0030102c2c082c0140040d102c2c0f2804000d2000062004c00414440c02d00c00ca1010030700503200d03600500e03403800303035000ea441030007041099880e1351496004503a071003156030400e8040c8413071014080714540a19611503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 58763096 1250 58761846 58761853
    0xe040309120b09060109142e1205011d030d02180a0e100503010209060406050c12040e1515070b090f070603020405040501050d030806011b0803011d13030912030c05 72
    0x65007807125480025110f42180411601c041e42e03603178806801c403081410720130480781d00300022414200d08401d281c00700c43c20000260001c900d0308030f0031450020340d40d449a504824500d0700002045030038000d00b40c0c0240c0d14090101d2104010303402c0307078503445036103c80c03801d4a81c00a0300a010001d0062004482c00c4d0191040e02c40d0b030786840c00c540c0901820342d2050005141e0314030000302480c3c1402252007008010300000c0c185444d0000944141c1c0000c658224107008442c08080b803074904401400003880782440001082c2071a1446007020443c0301c400b58010007100c00c2c1d00741507219290494a000d54844102c4296646886e0031a00340309128800881c0b50080c01c0f40010100c0d4150064001e442c01214100401e036030b01c0d001c0045800038600020301003416440068050b60003820b428100c0721120001002e0890a55103070700b001d51013604100105041104144200d11000301e215500c0346041d44458404003d684029002aa041c032801c01c5e4018085d140c0300c201445680c01044650b03205084 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 58764346 1250 58763096 58763129
    0x6011701110313032712140118020123030c0702010c0f111002061003080a050d150906140d121101050f06010e031515010e100f030609090c0e040309 65
    0x890110014100050780001c10780d080348444000c8800480915081c1d03240d0b01704070b00c0d25003c1100c40c62130380550141e03520510b81030414002d550a004481c445008200181c00b5022540b001400401220a400540240c440c80f03a020710900c01d000c89801c046a00b030101c0d2510107070b2004a59942c1728800083c55250f551000804000c0322006120341c0d003808844507002c5421500f41245d0315041104c1e441c4444010000c2000810310280040030081780c0c1e03241c038500c5c1543d002420016a48101211512403510800c100290fa240d0320409019040d01c10f080b48040ba600400150725890b041e00160004180c0c814040d9001c0c090200100301422000091141d80351040f800b12403c1c0c000c81e050750200f9442040080540b034041061a440e4249000c0d003061501e420b41c4100750002c035500040d05001c003040c041c1030390f907480302e0284c000b81101d580e41340e141075900100103080c1c52003035100b0001c80b801c10580a0005401ea80002c1c161203000c03840b81030036590f50808494464040d488605c440f088082c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 58765596 1250 58764346 58764361
    0x80c1624060e070c0209060f01022416030606020a0b0a0204091e0c050702180702030d0204080d030f020901050a03020315040207050604060c080402010801060e0409050708071701050108060117011103 87
    0x400c000b150750240018695a68440042d00c0c640c0110030000d50114110000413242e20344400915281c0754184111056041010f800904807288074100c0d8400303194800030080c10141540114064100300c1c5000c0c03000a20340301c80a562850800c0008006c071464000207032840d58a5810344000341811603041c021240b903160040f5110b9121040d02071014100400101401c0c0120110340d0680d038041e000c20100a980c0540030591440580b804045000800100c080c0203050b00103800580022809001203821942d40502214a940c0c105694180140604052603802c1800d40310202180d090240c2c0d00d9985504540e9980c4070780741c0d040d50062010500700144000040d9039881070344204000c21502c82803400903a16520204d0b0300900180f1260011f0211900c03031012646544405040440c038a40280d86441c1002140c0c1c00180b03d0360302c1103000708150008031801d030b00d1210301d01000b00325039410500a142c440300d05004510298036040d48078050f05500b5480340c0407180c03804a84a840381803905 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 58766846 1250 58765596 58765601
    0x31113030501050108031201120503190f020f0601060801090c110706020f06180703060f0902040e011a010513060e03150103050114010905060904140304030506041401050106080c1624 80
    0x401c0d10309610b0f110000c0341341080002258101080019031150f540c3c81c00c0d9a030b02208400301801c503468001030080c8c034401c0c0310b100d80a07801040191101514107490a100a2505481d40710010b080d50102004209854210440d541958081d50010491300a280002e40c0c5601405088a510340301c3d000000078011f60204d8581682c200305070a40d070381c030380b9614880000801c1001c8039211640014104000141e82036100741c244038081680440c103401300c2d0700060202e40108060100594503125424501d1400078603c00c0302407003d00b000303810300700b0724018182c1d602003030f00a450034041954900821642d0401c00192902125005619290307100e103041d41c060515820084040c4d0b815100202d05040c00c3e0181e40c0c400c02c0c002d0041181c2c0da582d130b215010071800c6000c000d00701780010000840850024031600e032245000d10007030300f03c11100404003808c41e03005230311010411510500740f00d02c0c9050300d411900c4410f0296104050742a042c207054284115800055240482244a48203012a180c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 58768096 1250 58766846 58766849
    0xf03010303020c27071b05070603050a0e190807050d0914100507030c14160503060604051b0a0302040b181315030807060f020703051306230a031113 65
    0xda00b95242400490280701e4094401c0c601c031311000d40b4045030103100c1c40c01c8007030550b80020140340903000181964084114802c0e018416104c1d40c001000a00425401d80540d64000f100708104202030300030110341544414201c242c0500203813000540100f1b1000d08410756000d00c1d0003078140d03402e4564110300a41311b1390091203441620000040d82d4085c901c5c24004036240c3e444c2c40c0d290a445c1180755034040340c0e21485404101c2e1145c218010190104100304101b4900080d4034601407419410102090f1401c00018100b0740326908160400c11b42d041c0d101100c954540c444844541c41b062142001d4019000c0d50b0030036034a02c9030100d40b403155100c40c200e1130354171004141e40c2c080d000038603054144241c9401c15980c4c010340d09804800c000080355440101500c5002e620006251104035a03400241d170b001340c9068000420200e80b00c0300c041100400d110040c441418000d500d04400791000520401c02d00c1030840341031010032040e1300107000e5040600998000c1100964a040c00411914201000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 58769346 1250 58768096 58768103
    0xd02060307111603030f050c0106030606060908120c030901111009110108070c1716061503170703021207050c04050403050d0e0f060402060c1203101508040f081308030f030103 77
    0x7210f1000c07544000d2a8000780559801d030b6aa10441400403134266030f0350380107040105d003540d03944e607002020540c0ba1107902c014110580d10344003d00d217021603182c0b5100b0542c0da6042c2081080000301c1c90780d1000030803242060020b00b8a80002d110300c440d51420f2035a0442c96410060905441c0002c00400080f000304480c1c0c26280c40c0040d0329001d60498090095800040080326008148280103900c00301404030007000c142c0e00c2c80d240f140ba03525002030b203c1e003001401d650300644005004000d0380141480700034003640d031402d04003042510025602d039001d03a510048140000b4180051060901400095a2003c0d1040c0702d135040c40c1c036009006a102c031085800c0b807458a50440c0210304003003800b51951813032030b00501d15038580c1c0d001c108450348507507132168440c422008a0500328007802c000d5441090300a002505951402170110110f40c83d01d0f0428040114580030000003401690104407a40d4110206540702d81ca29015090059965000054144404203080420080100045050b03d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 58770596 1250 58769346 58769353
    0xe031b1005010803030411040e031308030306011103071203050c0d1509050601030e07030b0c070b0109020316090501020a031d060c030705010b0a0e0c03190608010209010914060906090d0206030711 86
    0x780c1d000f21a45900003580c00a040031000800e0001501d0141c1000c0d410724011300680e880c02581208659000c010b03580b08910310341020042100c0756070081c0c011450002d10704040c40ca81402079031003000d00441500c0c9070007171540e55801b041d030441402055412011101c0010840324504102c51003485859110380071040c0e042c000000c02d154824000c0c65002c0880b003000740380306c0e4196074074008420401484007400d49010f00291012464405803240200810741d00141e803818492042004100814509418070481c0481001640d0740000e40c2404990585410045800000384004a401e9003081082e8050004152100c640e80044000c0a206108000800a0904280c00c3c0081244d007807207050002c4540b640000c205c03210040c029039000d8461b850516440c0400c992500c201c8481d038005440c3d6a601052007070580d40c00c902d029002d804045109904150884001500c912440960354000c04006c1000072198960441c1940c22950043c001c42d240c1c030780500e006000c030b0300c60f01c2d10711740074030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 58771846 1250 58770596 58770599
    0x30803060405060604150e04140f010f090204030c14010e03060c04180e0c1002010b03010603030917060c03010605090f06070b090709020c0a0204050627011505040b0405040e031b100501 81
    0x11340903044034100c0e10028129149101d0b000d030103640d034030f8070300f1140751708a600e54220311a801424084944202c0c2e201240d59801d5051018015005e2040e03006130034120310401c021f10100d803107029400201e4032200c0d6019001e10a880c0105c0301c2d0340340c12406070f815208250501c18860020006441528400b0a00e0304889541da0781c8a001d03550317203141d0f0352041d0300a0744100c58075041c200e8006100c25000c0c0004912502c400001c03074219202c9500a0300000d6906400344a243c92600700c408400d04444000d00880c20031000040e400d10040c42100184100040c50780c0792a21181c54a44140d100109103646604045c100354036501f00c110358000d0a03016404002c1145940780c400e542d1041c2d00d902c01881001d080741e0a010041c000074121583c06101c200d14500d04005030400031042e9400751380c0c1c002c0203500d00042e00c605075109030740b04010701c2410f0000348008042107041c1c504031101150041242c01c4001c54085c15031180265903001100c42c19069110901c001403a4048016100b4040102c0e0307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 58773096 1250 58771846 58771849
    0x60708150a0317030705040b070b061512010501051e0408030c070b040602062403010c020d02100b1513150f090501050901080f100909050604021005040803030c030a1503080306040506 80
    0x300e00006011103501c40c810380081100c6000755611086909100f1714143c3c862311a1640d139080782d0707003c030b490b040c000c1c0400c001410815124103040c48640d00190601e41d61600d101503030070050255504000004c01c16040c4000142800580160750311111940c8984810101d40c07a03a10201c0843c00a12800e0b6001840c154001d00302e40c2110f148be8040c200c03948540e4005000c0c0c0c09070718900082520120b21480c0030f541c080c13158030703920803140d0003c140030080c602e0068240a415414600f50038903180c46071703000f61211501c026084040542c03455803180d9003008200101e0340c6812241504000240c0404010f8202050f15080348960301c80074005a600c40045481d8490102050300281c58500811044158010040c1e008041004642e4040d030710307070304904100c0e84201004e803100e60003001404290b041c180d1610040e041d852902514140c104884166a40f10280112014050010008543c2d40903580f000c10f2060a149400649540d203090007201500140c540301c0c42513240c9400f00780203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 58774346 1250 58773096 58773109
    0x20f1507031707090b0406030908120a0c0314190504060219050a08220f14030d0b0405060604080d0c0c050a0b0a0f030905100207050a150c1101020a1d030a0506070815 73
    0x2217030403410019107031038107009003100034003101101220281410301c03110080d0004031554610650041c01d001484031481c100040554860101208020100d141030060b040a040114000e040c486400410300c1e0b161841c0140081c81043c0d19000e0420401c0e1284420540c0100105822140e0f5079454146864071840740d41d032940030304034403500c80b04008041400124a8a10103205a0142c40f20000201806842604650003501c0003581c4079036426020341c1c10718040c403c0b5030300301000391031103420581030900f0070303a5441c0300ca40901c041c0700c40410400204002c92001c500981000350170840c20a54a602c5240641c01080d07040f00881c020300e0382454550b01c80c3c0b040b1000e558001006080310380c0c102001400079404180b05560300e004030740880c804141c0d417000162070300100300000642c001c100d00c4014191280c034000c80c107081e4010880c48641551008014003007500c20394444202040c180000f920f8820011344c020128041d1804000003150008401e034070030342c041c080001103d90a8820001e9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 58775596 1250 58774346 58774349
    0x30209030d11150a0203060a080303090a02060c03040f090c030506040902030a170d0203041505010f1202060f070b0a090201020105090d140a0c0507030615051c020f150703170709 78
    0x40580c44107000e4003501d0b200b07141400380c14415a06540042c1c0e40e50210301c00c900c2d01201e000085a800105102681c01c0c2481190010608200030710700314280240c00315141d003010600607100da140410301181c18101481114000c041c039125952080d035407030100401400402a1b2607001c649008009030b41414540035108070a0341c02806091821203070f42d16614031011030f000400924100f407040301000b0b102d6100460084d80140180d460b480c1c40b81510100b6a0380503080800002c5d014181004201c41c2c10080000056049409503200c00b11694424114014240041c0292000d0030504c00c10003401d6101c071328482c1c000e070300a02080d41c592540c10307582c000c004161400641302c03240d00c080008890000c0c24568113507140170004010380c0c2d12020320340030090700140c0f04941d540c1610000313644c101c0c98180081c034098949003028003050300c032901903000c0c004d4068004d50000480f00c007541c1d1141c02e448440c0401c01102601c900e03090500a000d461502a80011007800c0808205094010a0500c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 58776846 1250 58775596 58775599
    0xf0305010c1407260d06060513061106070c030201090602030109050402100806010e010c050c030a03050406020105010608040c060f030f050108030a0207171c050c0727060302010906030207030905090708090d030209 93
    0x84c40b2030301c0880c0030303000c00e451101c250000200c14003510020315054050781c401000a59a2a6260f52901c0350517850191260300c030724140300304e002406030580c00108a45511403078034141554140f02c60700b01039025240001004080610001c001f25080803a60720090055000742c071006080c8403454000d076031f008026524103000ca040207130083e0b5250710603100158402c1c46101074a41c00e182001c04a0b1600c108107904401042d00481d050010581c244140d6004000c240390802e441e051984450840789414081d050400a4080b9845d02c0305000c0c1c3c0088001d100c411000f04481e40c0e40784001600d94000240c04001806103c400007076400040f5004100751b607224002c0e042c044840081070f00d0340d92141843ca0180001849011100d440a10812005007281c04800e90003a00c01c241a4a031400303540c490a0704549003407800e10140c1d81c40700c40310040c0d420500b00145c6e1681c4a0406175403100559001e10b070f228100b00d08000c1002d60103520540502007007401c071120320340d40c2c6805501380d00900c9c0000c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 58778096 1250 58776846 58776863
    0x10e0a080d0905030f030a050f0a0605010903201002010c0e010503040b0a0b0310020c0a0303230a0b010e0a03110a050d08031605071a0612070b040e060a0f0305010c1407 74
    0x1c0d20080c4059020000c140e00c2038044a203000c0480207a141c481d0001c84198010341c0c2d55104214412001004480e130020030b0120030040c2c14203100000e024943ca07800090400b00c004442c041c80c20328030042480101000802c2d80042e281c9003c4c000380070b80300459400d00022080f82e012004ca5001d041620b0089502030810b400990382c5222040c009e152030b00d189a0306200c0d4000c0c002d8500828801840c9406004020700096403250a01505a0f0407141848020700020b170750808100b1825540a1b81203404150085808015040100c90315000202c1c01903001050000000800451000e016803002041d94840c50450380c64013004080803005101401d4280c081000501804006502051401090400c80d0415000e620740c0d25905800c0d004043c800054041400b01d1761904001902c1ca01604600030101142416040d9160340264810f0b110400400d4001c5611a030320200c25802034140d14840043d110750300d040c40c3c0e0107001501080004280d151914100c034040c14812164040e4000a25 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 58779346 1250 58778096 58778107
    0x801060b04090225030507020301050f060f010807031d01020d05070804020a0b0a05070c09020705010e010c0e270f0a05010915050108060103090c0b04030b0a020901020a1704080d090602010e0a08 85
    0x544040c2d484a5006111058200d5003582c4121013900210585030103039031600d480b03191610500d0300f1030b100600141c0c108402d1004005540c5c0c1e0b000b4036411441001e00e01040b80f030300c4003101a0050021600c039100d010511103401c194103c070540c0a4100500303082824041901c0d030180c2580d26090948029401c814850703400e01c80b19800ba0014aa0090949806894803846450f070001d454042e8000c00d4405400180f20400d10400340100c02e0501d200d9002000059050344003c1c0280302448402405051941151504c3d080000800c0d00b180070403e820309401d19002c0980081d41c0001c4840f690314500d840d0001c9000c8241d031282c50160341c000b250f00a02da0741428019601d003403004003414101a02ea0291034001503000c1144401040703940f1032162203504615201020f000000c2088410f540b05016190303140c0e9000801c070101c90307004030013000e01c3c00358200c00388014030441d000114103100301424401820f91101602081b2030341c42d4002c0100d070844a994039120300c610740c0058104c0e4030a125 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 58780596 1250 58779346 58779359
    0x18090f1b03030306010c0507120c050102160e0a0c11010903030203010501091406030415090c0f05030705040b0d02060703020a0501021305010f020303100b0c0705130b01030509060702031204020a05120607090801060b04 95
    0x600c6c5907038000c008807030340c1c940e07550208070b102c040001013254098400d0500304a5960100803104503d5083c0300061076842c1040441ca02035140200203c50458644261503196801890007950041e5040006c1c0140e24203810050046c1d4000c0c0700343c0303002075100c00001030f110f48078075400b1107050380040101c0c0c0b03180c849840e2000318000c405103002034280d0b50401c0c80005249800130000411100c0c9061043c9803400c000c0509288607075101d540282e0821920a0082e9640c5441c0304031a0b40c119032094070740401c1d0604130700e08440111700401071340c40001d03a8800c94a01d0896901240c201340e8a00c8000c0c0c046080490b144d002c1580c2245d85003d51010500030390718a0700161490903c01ea04440e60a640c840019424002e036282080a2580c0c4800400555034540995039010760201c0040c45281080341000f9900d01c07450b60081d1350001c00d900070808655400322110002d10000388030100c034258074100c1076210141500c010020500b00800000c07c0c45040c09200200c1d142c2411950400d40703004e0307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 58781846 1250 58780596 58780607
    0x1a01061b03030e0d03050709050607020604030f06020702090c030a0c0309020609040c0509040212060f10020a0b1f06020c040b0a0f06180801060f0312020a0803070e18090f1b0303030601 81
    0x1003080301895180c0c1c40032040e944040200f520240d07425600460070741000340c00a058004141c01050240d072042103c5805600c9020442d011a070380849040c1c1c0e80490380c20580e000340107100d002540510350109101d8481c98050280d0302403d044c80b41009050498030007a002c580102e480250071050a00403104c0e549410341c441c030b13408c0606085c0a4a408040c82c00135040760300c10741c00390030242502e40078040b1b00e040c1004d840c41801e6041d40c44982c86e414420010b5940e00c0b107a0300c0141039404c1003000070306203007414920240e04131401c8c000f85074003519510081e4848081c066614096464040b1581305442c01000f510102d0b01500c070302031202418238004a500030042104415040207281c0b001400810134440c01d0020114211b19841d164114900400c00c1d405d03040412086500ca00507031004070340c4240071686c11024074103050250001080110304c150004040000c1e8005023203003040042540801e00c50501203408041e0340c02d40c114549050b00300c042541c103140d0158000d00004e03900394042c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 58783096 1250 58781846 58781897
    0x50709031203060504051305190b010b0313021c0203010b0d111513090507090b1206040e010b040e071e0f0603050405100c050a0f0206150f0105090a0b071a0106 70
    0x285400f1800544034400709080d12801d54568030a090031000c0d1b41d007880000c0c088050880036102013a80c0c1003800c0d07201e1207817400040c02035a40007480080401c845803818040d10002c0795018084071805000d0000c1c3c82c1d0007891b00902a400b81d400c0005c034042030324150380d41d050429801001040c10050f04420711008490303194004800c41c108203c14a40015103810346c00013403407402c8000c95685402c1c940202944201c3e4803480004609124040c2a040441c0143e5400101983c000504d8410f007800140901003802425801c507140403400305840710045401c4080c1ca600b406911007a510001d0400c500f10302c0ca104d401881c40100130103020f003601c240c0185030803d001c0c0d01142c1604401151007011180750019403000f2890008201008a40040d40d8840f11303240c83c00500200c1c074201007803503418118519418030402c00d0201c1060582c1c010000c2c0c030320420028200b042080d490310012801d03a8440340b02035465010781d10201c4200344141308400e06035032140d610034403040c45088400300c642c2c480c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 58784346 1250 58783096 58783133
    0x6050c1905010603030e0607030e0118090207030e04060b091305060111030d0615090e1302040f0617070b0c0304060c050309100e011e02031b0106080a140f0105070903 73
    0x640c040c500034011480080c155490080000042d05441c5143c00340021100700c0d00c070360240c2e0301403100d500800d070014a100040c89080c20410180241c650b80304a295500e9000042d01900c0031580d40309050b40102d481c558050196400c009007611101d403a42d040c01a940b810798410f500885d409110f8001e608007a8002906040c01c07010968130f0b158486c203581294004560880c0c0c4c680d410020025140003d100d48802c07420700e80300b00c90070f210707011218040c000c000d452050500b45c0c0e408215101c0e0390004110a04a500401c542da403942c01c48026030141c8480e000552051440c00308102e00f00c842103a103890b5003900114a082e10342007003070714001417030b1a040e030f5540030902c282289078603041400350380d4403000c0c1c0d02c095640c2201e0300054800300503040c0c0d00d094440380d000180d0043d80c0010440300e200f8030002d40c0096030039418107260f001d4540e64201d003c0c0c90182890050400c03c0c42c1d044042c1050003481075920180103422514225101140c040c000641221801c04c0480c800f550f10445c017a95 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 58785596 1250 58784346 58784353
    0x806101202190f080a11030f041b0f0302030c06030c0301051302040807030b2203050d0e0304120f12022a120601060503010f0b18010f020a050f030d06150906050c 71
    0x100c1e4840c41c0303007a0903100714100105203e1007042c5102039205a41d550310103c084410400c510210080072041d020040c07003c1442d10031103000c40d0030300c0080354042920320301a002003603805440c3c128aa00040391840204d01070306c240701c190281c030702e02032003070381d2244020310f6205040d07030301c0c050800540550814403200c0075507003000b01140191003030200e14080c1d8060008000d6a06181d03140c1a03043c20300d149910130f103001080c18a400203600c801240c8890a403076a000c10f62100c142e00080c210700c2180d1042030b5901da5100c04800700b010320409140240d014462001c4403464009050741c46200a0240000b0346035000440c0400c190010324004803480c0141541038401c000100d040d00e0484280c02c1540891000b000402034048100c80c00409000f0410703e0798205079190184a1440d100c0d800c85a0610a0210110b10414420401c04d8042c035040b100321034140105d0912243ca80d44601110303a1254241315010541603980c4019484815940e40c6640e1024a082030888294001c050800040d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 58786846 1250 58785596 58785607
    0x170a020d14010e2d1209010509040501090c1b03080c07030c0605070c050c0a05090c071e080a090f12061a030f031909121704030b0c0304020406060806101202 69
    0x4401d1080d001120b0316a0f000b070494404c03055040e01140e040c1c0795641d1200341c0b14042c0340222100420580314108481d84141e4072140e00d040161602d0084030304c40c58000f031400c4000591640c0d550040a840e00b03154844202e2000100740d5801c15800200c8040d012400e0800030414064202c0010b00341c4500914200e00c44030201e54440090b20010b880d9000085c00101014090007c02d000c5084e2403502121a410030a24140115a00101c0181403072904200442c0100c20721850141c5883d5000102c0703107900c0780504529006120f0f400140182001071407101740880e41000b00401c10082e02c0b031100524070105815a02e039405002241841882040d800c4295840390700c08001141501082101a50311001d40c0322484150074440c042c0c3c2c0c1e04100201204110400030341400e854008d4000b02054082c110b94103c10b040b45c4295400142019200420090700c000010051402148225018031007290b451008441c0b0703070f90035035280307900c51854441003088500a0b40b01c803110301d04080001d810f10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 58788096 1250 58786846 58786883
    0x30210080402130204030f0506010b03011a13030203070623030f04110d06180302010e0d0903080f0c0a030e0f0406230a1214071a190e04050405010b0307170a020d 71
    0x17a0000d50049503481c1940000004200060124a01612581132003600715854401940d60042100105200d031002c000361010407284400601400395801030103c4a18540c4d514009015010142910001034410380f1200707000c1d0310141c00c480c0174043d103107581001522903407221000024031007006a4040a101210400110a8041c0e1411071070b070030b80c05200d000010b0401a0a541d840700b46800e45400c40011201419000001e40d403e8a4002020944401c030b0300300c800019101c0d29544e5030341840f81c0c0010100b05607001c818079020b000d041c0c410440140b010f0f03003408180c6402e4007a141ea8000d2217410014403550036845003514400051001d06c0c0355540380201400308a0010301500c1488881161001c2d4803c01c00c000001450850040c2902404c1c805e00c10b4028000c080907001710100018490b52039501c41d8a40d003440346e5000b00100702c581820f00e0103600130000c0c1c1610f00d00038041d10400294040c500407402c2129001c5c800070385020200d903402c111a14151000c01c03661859207000c21940c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 58789346 1250 58788096 58788101
    0x30819021b060106030b030a0b04141e0a060605010f0c08090406030b090105060f09040c0b0706020408030a110706020a1502030405011113030204140105012f0109050303010302040b060403021008040213 88
    0xd0705070351400380070154107000d03008003902e400c1c0e50010300a80c030002d00341c00068250002294069001011442c0c0a02840d20450525010b080c85005145103014a6610180041407010b0503900c104410081e85554000550b48003300c0841400400e4000c0c100c040410351349030040a02440003880090041d0b02c03a80c8001440b1010b40c1c14000c0d60399944100306403030509200c0032407028006c1300c01090a1915503201c18501a190080040c00b20000c110801004003d405403401792941c7c2c002e59458004442c0d00a107040075076158241d651150642c001200c42c000708800c1600c1350001108048040346d1380304580070b50700160084901c2d660750b032607070068616258064000305840b404124010fa00d10700400007640c210480c0045403007032100040000d40e82083c150500c01c3c42070310b40600104001100380c0f04030351600701c001200c0e5003480d0980d010008048003c1d4180c0e807003100c00b040130481e00d0050110900950000075088800b850603032040c0d500880901c0c3d8094070090880e00c91801a810600c00e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 58790596 1250 58789346 58789387
    0x8060102031e1c02360409030c0201091703070602090d0f1b08240403110d05040e0c030103080702060304080403020a030b01090f0902060307030e2d06070c03081902 72
    0x3680c900100346a40d01d4075400400d401c3c42c0c41ca45a065041c0988803150840c005520040652100c041c400c0d0a039010388018070807206800003e008100c07920351410f0141c6203030a80c1100701e001a43c90600420b0325241001c641010420300d0000350304200460380d0b01c10080d44503d418a5118800300d40725000510200c0f400102d59100300c8071200344030024402c041d1030f42c0654200158513082104403081465540711012810034820030003015640b2542000d0351403190360103c9a20303a0260508980e6140e1300000100b080b58a640c5034044c1d10340d0781240400d0703a4007013800700400d00b030b200304071100140c074080700a190807500503054a443c2503030325400a0b46101850b4812900b0000c0000100305281d114441d5101240c1a5142807002c9080c50b8006001480024445018550b0720048111411010003908140011102c10354410404e6000d0b06171101200b281103400500c5900e0008002c18840c01854100507899110006142c41d0425900b501405580d003c9815036400c2c081c5503114074841179a0074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 58791846 1250 58790596 58790647
    0x2010210060b041d070f050d02070c060302090f0102060c03010b0304081204050a0605060f091914040803090708030c071a21070207090b18040515090705130603120806010203 76
    0x3a80c682c98041314200711400d061040000040d408100100c1e41c1d001089203000c1c0708640707800e40d50380c032025003070100034042d821000c0d04180300c21a0110b291900b41d40280300300c2070702303c809140c0e542103c401242c0d0340d2000c44001a00705428001003000180d201702458100d0300c03800c1090300340085c40104410300d00040320281c56036406000400240b0030203124150700714400743ca0000e80009200c02048005401502c028104241c1248415020030542e01694000b14881860680e0341424103081560350026030b0030310503900641c040013920036000000c80c0c002041410150868518200c2c07604620700300101030701c1690303a04000e019500308034840c005515000d40340100100c1e040200f40285000f2007900b08203e0341d46811680545030351881144440e00100342c9605203540d0300d0b071070450b09103800c0864503030070401800140f0070305040c0403e801003078484c02d42d000c402e000101107400d01a1070303140c40702500e1007400b0200c042245200e0103981e41d110006004072407030700344401c5084c8130841c60034481a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 58793096 1250 58791846 58791869
    0x204030b07020307150b010203071b08100b040b03010b0d0f050111070302030d0b090105030307060e120412050c0105030c12040203150705090f10050a080406060b0307050c0609070609050d0201021006 87
    0x4001c21078855030f420212281c217941044507001c5840042e50303d100e5844058101c0540c03042c17445000c01c40744600c070040c191405c01d50303130042c030149400005082010304051003942003a550351114101440703120904000100b60012020030780c3c0700c0e143c0700d44500740c040e01c16540316a10300340300812240080241520941c01103584290018038003049841c1014054030030b10001004000395034000046d1a02d09812483c00900d1428019109103001d011110031142040046800102100c000c494a446580103400b030792212180000112841d2008491400c09010240903142c4100c60903140c0c5030b441440502100c1810403140403200200400315003450000300002424a218103048002c000d0001043d90940e841c1403500d94050002d001c2c1c044d2950421045000040601650b03821250017081030304860359172401c02e050001d1065100f101030000f64030942020070000800003c880085800507662010702c0d13420541000002c038413107a01a81140f04404101e0050507162050000411681032003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 58794346 1250 58793096 58793107
    0x1020c0105010b07120309020303030a1109040c020c01080903040302010804120c0b0f0703060e01030f0b071b05010501050a140907030c0212030f090c01021b0d020a03060f0618021315030204030b070203 88
    0x459a0b114805c2e011100701400c0000500050301c0000070b490300041006004180c800c4a011164450300035640000e03485400e2499030035910380c02080c95054400c003a070b64180c4503501c04881d59a0780c4150304c0f0003030006249400060110f50b05100390381e401c40c0d03285043d6206071042e071a205060a01628007001a0700c0440611020329007503c201070040c4140580c40c1002c1d8595240d860107401c0c50407018040c80c010700c001a10031841240985080910901520408115814064028074090041600480c11081c0104076a808020a06c0350f43c20020400100e60344c031000110050604854124254402c0c2501d0b0201c684500020714894028100d07920000e1401fa102c051400c01c3c0c441e140d0381550020f00d007003081c0111a050038034191105850654a000035407011502e003541d1035102610032071802d6018201d0700100c1c2c0041e81200c01700b0300d401500303901141010040b07204045c00c120007114603600400c03150032410032441035544e043c2001400c103030b500d403a04031400700708440003001030300b00081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 58795596 1250 58794346 58794353
    0xa0b04050108070614031510020102040617011809020307120503130509040506070e0a0f03030302030a0c051615060504050f070305071d0111010905010c02011505090708011701020c0105010b07 84
    0x2001c0c0180b211100a1507414941040a000300503800c0501c6896180080014809800c81c0480d151220010b00301c91001101c045000b8000e40041c040d03500021030740d031b4420030002c15002071141a565140140c000b840510b682d05c43c01400b500000320b0305070051000004004020b501103040c180e00900140d907a0f014500300304c420186c1c2d590801441110f00701c1c14440461000604590300802c00d0420080c7c4c04140d41c00110010712a600a004024912201008059064000d140034115680007440300a4102200f0790f224014040c448100c049101d40710b00124a00d1a100340541c0f280c2040010202c0d110404981511402c846600c83c4221041c1030001c2d6983c1441110b5101840e440d085110b92806c8610740ea14103d26a450342c1004110301540100c0d160a51041c9840c0f548030008002200f11102d004e400b80150381404902514030903030003d400e003070030455988126026076406400d81e0800c107482c110340c0002c002c2464030750b41c20b001c80c81c0021401d100d424064402c131401140c03102442e20303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 58796846 1250 58795596 58795601
    0x1e03020f0402040308040512070503031b01051e070e01050714030406140408060601050903100c02010c020d090b0a03090512072003011a040f020c15071806020c060703050904050a0b04 80
    0xd425000e10b204000401c0030891150540e03090b1002101e18141000031005070340e180c4080342d00301583c580000a04411041649441d030790f010480360b4024416550317034884a0042d00f000c200d60040d03039881180000c0505106040c451070101d8141004e50a042258460250b00c0380c00044495041d0700000c1c0034010390f50862901582003210300c5c1c2d0340c2c0c586070030801d40544444019000606201001c600d00d0301e81d0342d051000b8080585008000c100c0c10b4840e190013806405540415405402404d100d600082e10500810042d10712a8840a20f024001c02c011002007505030030a55441c00344001c0a0909a1350b4401880748a004546460318940002c6482c0c0144c0c40303081000d8481c0e89441848201c402c80d20480f2020108200c41c000740c800142055003010b442854188009402901c1d0f01e01c40107031071200941d0040d55195252100204000101c1000179924041d10300903034441d1010010398900100100000e52080c90102e081c504900c02250903600144c80d0760851541306c078800c40b494145032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 58798096 1250 58796846 58796869
    0xd030b0301150f21030e01080703090f0501050105040b011b0f0c0506070506060427020904060608030d141503120a030212150f031605130e030403050a050609010504170a091e0302 78
    0x32412182211450707035010b0609501b151010f4180895080000c8a940c000d030300c00e0803c20742041c0303d40c40141d5140f401a00805003401018401c524100042c0c4441d4841e042d02c80100351541c4e000c480300945619807a400e09100f01d0300300c2d01101060000704a03034803004054002107104d88000c0596092817000c0000380c480d2001c6103608980f4044004d000b0003440980c1e910044e40540302d2612a403102e041c481c1c00390400790811000751000090040b08070703416a1000d80307202a500f0195100e501c4500b1403a4504071547c0f00140d26901060300e4407594404c100041102e900b95003001450903496940341c0ca5040e40440d014200e070300c02c0001070304503402c007030800201c1d014044021b003030655400c21015008a1150041c280a441112881072600714180e11034134480000c00c0840303856585d03d2802c1992841d0102c02201c0c503000e040d000c40c20000050090500643d405150703440c155060b210031055a030882c0202904010702c246002455071520340c0e010340301101c004507460625095006001e2400a01c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 58799346 1250 58798096 58798139
    0x30050a09050d02061c0b030118030e0607050703030807030b030607080403080915070309050a05011503031803030801050609010c020a0303050306011805091b040e0709050f0301020c0d030b0301150f 86
    0x112942c8800590302c06044030001d454040b004030044e184413031a0340051440b48001c942662802165220920071400340c80905403080e03603000d1403032070504240320303041c002c40300002c1169021500510011303006443c0258400443d1400181704522000001c0c505a4181e410b0000b29501a05000c00d141d44003481641c410040001480140807a003402c0480490062040c0209582c402d40c6004104061065248485d08600288150703004d80003c4003640d00390384021004110343c0e080c0781d403140d14401c900385d0449070907480710030440c3e103030000f801020781c40040244e04220412602400680ea443d50810246000780c1d1040d850b0300d001c40001d004015030289690316135400d080100601e50341c825900b580b15041d000041d0b40e01c8007072540d0080c03030300442d0410580c60249108000140b0350100360f090403644111551100d220701c60b01858201d20412503540c260703402940800c0013081c000c0e00f0003c45088080d000050f03a4076030500000c605036803504014101c0310401400c00c1441040210710001641 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 58800596 1250 58799346 58799359
    0x24120606140108040b1512070510090e06010c020406031a0103051603051c020a14100c03020c0309040506060d1a0a0e06010801060f03022703071e0330050a0905 70
    0x108500003038181c0b00b00402c01400c03007154000241070806e1820b1510a10000540506107806900400790303150100303402850301802c03200300c07100025889040b42c0c0c003c44a044a00c2c0c90181c6420004441c911640e0101741d80054846038008002003164181881310624804411619419450850f007400c0c01411602c01c8941218030500c080380d001b03d0a104a000b03a0809108040a078103801d9040c48485032025006000780c00c03810a0200c0c0104803217004400308541000f404c070b80c4013019412400f4401d210000ba502c24014038107141007550025400160081c03940c0d0030408040e032480300340c078940c29078405411800c45000015041c1541c0030405000d00308075842c0c4074502100000e04402051050720304224050641e00d0360240664111101d40c1c000010025200d00c03e0429141040416001c05000340300e03000b00082d9041e030b044a6410071681410401940074510b40710000e84501030b0710900000700100b080001d8104100440e504900001d0319000d40302c080b05a00500588aa603010700c0c0a20b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 58801846 1250 58800596 58800629
    0x190308091302130603050901140702060916031a0a09020301021c140105031225110907080907060c0203070503010c03090b010602030304050a06050a091a0115051c24120606 75
    0x580c1030150544065240c00552a980d441e17185001d0030004400708810949c101c14012500d90100d001c510602c40b220031144071080c04003100e0603007203a0707201c0070300244401c048041c00e903020201c0054002d680c1401c045507074080d0f03800007400ca9001c8103450710300c14600c000c1c00d047c0344149e00aa03c070034810004a400f49600d0000420380b04d860f038981d2098a0b11000400c600850011102280051b04103800c081c640e150625180190780c3c3c06410f03080c81144004001740304940f180081c1c03880340f1200030141c420989452400c0c3d40380350083c0800c03a41800344150205243d01c0c244210010340303501e82d80120750541d950070b00c6c4075071510680290045420401c204400f05da400500c00a499030300c0358000900d950b80c440c052004107008800203124030b00d030060780d0010300441071103a41620740382d078008540030119a206a40710b128001460b2200c414001e0070043c1c0100c0f9520070000c800205402da04ca1201d600c00c001d013902100d800c4a01629048604031042c4195441410003900311180d40040300c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 58803096 1250 58801846 58801867
    0x3010e0f060402060f0408031c050a0506030c01080703060b030a0615020a0506190906050405060901050a0b01080f07030e030406030218010f08040b150d061d0d0518190308091302 78
    0x1c140090010340550000102041c440b03004008503402440305e6010340340c07a00745440340300d100d4102d15a160385009051002140c80702c0703072a11803540a01e800800625560b00007400544000600404560078940d031a00e0018503100c1c094020b502c41c008408000510900302001c2c80c0e02c03011051543c5085601c2151038100281e00001d5840d045110b000e08450414205591900504901c07000204200e0a1500b8801005000902d681c01380c0102c4000b80000e13521081c40c0e80444610200590005600340045541030900d0075116030041074925001c1003000135111042d11359405940b0442c0060f0f80042c04c5185145502d100e02d2400c03400f40b0f0a12101ca040f090000e051010280014107002440000316045e842e04002c403401818026003090442119402d101000301055100104500701c5403625101c3c0d1040811070400c05803140e220103080c161041d40320fa1041820b034600b02e410040d408403407100300c0240450480118861402140d8540300382052200714160b9a4038980ca6170700520546c15007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 58804346 1250 58803096 58803103
    0xf03070302131203020606130b010507020405040503070c080607030e01050105010504210c090f050604060828170403050114060a09020705070902040909140f06011203050c0706030b03010e0f 83
    0x204103140241c1c4602d00c0380c42c05180c801070340e80f14100442c194100c840815401080039489802e04551821600540800305016101c030031012500103402040b941c0010318096000c20380080c0100c08490500a02c0d5640c0340340d65075142c12041e015800401000707821940340c00360000c2070790210300034440c9500d810006004d40c029405407a400384060522805206001c900070fa500c0d030342100d840010300e81d903079010100038210381410709421420710700080da01d41800d0007268126664000103000c0ca501c4080c07503508858402450307104110b8442c0314803001c90941e007400b410383c90074005031950344e40c075600d0b00e542103888104450300125081c40411a80c0d5840d07641c0da10486032074a4000d030390b0754011301e0810b0a0480b1500551826440454041071082c610307800343c84254030896541d150454011210355481d04c20202c05429070303020100601c03800c40c8007015014414441e04080d41054200361865082040b26001074000a035a420b08550074035090241e41d1a807800d4101401c3c014210b0301c0b0103a01c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 58805596 1250 58804346 58804351
    0x30b04030e10031a060706020d1d070801060308120907030b0c0901120504030e0114090306090f06010f0f090b120a050d02010c0e1513150c0303110930070303020601080d0201020f03 79
    0xc2118045106e20a0100740c0e0100c0e402841d03110800c0250500c01c04101e030340c800c000d041d04081031041c601c000c5542c2070148038034000d80e5004681c660030712441b031000d84844000100510a54003c95100000040180741141d002d42441000ba603181d5000c00001086068220203d42c3c1031410a018000030a0b04a09801c20200080c40c00c4a00311425000c02c40d00380c8035030a84950903205200c1048646000400d40180101c0c1d00410388495992301d100703401030610325000d141158000d089040112518aa2104440b284054803400d01f001085242e5824110b0302001a03907036070013045034082c40a40c20f10892813040294140107c0512000d404181c1a104600384140d80400001d00e49940800c000d4420300100541082e03080310241e100c0008100d0401e02c0740071000b183c2484854890540303204144d85c0c0d20700000d415000c8131442507420b4504040c11200c15000c1241c4400503408500e801c0c0450f0028500a030010301c025450003a0300d0745480428103115085910501c44a280041000704503038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 58806846 1250 58805596 58805599
    0x61401120b07030e0708070302100f120b010201060302090103030507020a080102180609040e030c03070308010509280f06080f0601050d0c0e04170703090512010903120c09030b04030e10031a 83
    0x75000e54070403105070001c200d00c8080322985d215005000502c60000a0705009403131090f02c81e00304c0059049010f5454a03203c0707003002c012420b40b003140e403403d144581c49030760450414800810155580e4012900d140e4003a002900007031000030b26001542010422030000b08080ca008510b03082a1590703c1c101d020003010f4452007080c000910003040c3e40c0c0c0303070081062416030070282d90303459441c0b000c690796a52040400b140802c10080000400c0d10309800d001e480ba20600c2c1500c01d004103006485410414181e5030061060340e0f03928451804200303407044c04090301d02e0000400f41803080d104101e1030310380d050b03101c1c5100781603d030320303444c0003c5403030410400300e9002005282140c0c845242c0400c03044030098603800040c20200c0c070383c0141540110100111003040d40c80020402c0c048480a09a41350340c500500480c00d81440d11900701c0750340d4001400c0103c64030f444a0030544a6403120150b41045c0e5041c0d00040200b07000c050f103894580c1c0c1c000c0e40d911880c1410860245291940c101074011910601d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 58808096 1250 58806846 58806863
    0x100506090402040905010e04050d020c01020709020a0201021303150605040603110405090a05030f180607020102060103110130060e040c030f08090402031003050730030c020312040306140112 83
    0x6a2103407525010b0b1005001e03041424403541d80c40b6040f101103034004503003e40d194890392440d4505a0300124001039280c0c1c2c10f0340a0f00da25828004224081d5001500e40c804542d400c00003507001c0c80741c03141d0190165200344501c031070140403007565005513541030708098800c40c5800b4040000414210b000c1d111520141c5d00800d0b05d9856408260a001211802034542c0c04006800600d101c00780e80109180b1380c1c0d01d20509130110003102802031902a800c0000d000d40d216900600100c0c460140c034028008052402c1c4c071001c503600030111141240140415075541d00b0078094000c942060103040c000e41041040100b1926160301d5500d2200118032000d0300f1300c481614024140035004040b01c55000300a0010366403428412217409040f1082d10054940e4007860b400031a0f4201e00d5008030382a0010603102d40041220008401001c1c5110711084050000048003400142c8060010303074002d00324400c00c075407514610300300281542c0070f03024111400700340800107120400d80d01c80c4854200c2d4010007030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 58809346 1250 58808096 58808107
    0x100c05090d0203150a060e131a040c1214011113060f031d06090c01110a020909030409050907080c010c03080a05070905040203010b09030114010608060d030903120305041208100506 79
    0x7180c10081c2c00c000c0405030030b8048040008085c0c01c0e0300120300701c460750714842c030356039691100c2010b11450804000b4611a4848444040340042d449400d8100380140c00c150601c56a4200e0b588008241003000c88803001b42d4028114401820b1060b00700010410341d0302880c000040b0340918405c00136001d0b03071040c030a02801c5000d00500c00c1d48003c02421021604450020002d01c1182d590502105c0054a40c8500440c010080d4800c04056110250b034000800e0410901d5080091404000b000707003042e03120a00c80052400713250300909010b03220b58409807114030f0422800a06003512003540c24140150004024002580101c00030350052400c40001819110160101c1d0741c10441d40c05103502a0010002264204004008100428040303008120710030410940c021120b1091181502103070203600011072506241e0110350540380b080c6804043b0b03940740c2d5a0001481020300d800d80c00a0340d40c0040004004490b040c204140482c0d00700344c00300c0d240c40d00d6400403641042c00340318014100442c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 58810596 1250 58809346 58809349
    0x120316031b0b06121c2c0604120501090503070605060108090606030d08060409170405010f030515040506060f03040b04030906050c060c1806070b04061503150209010e040e060108100c05090d02 84
    0x4c8864225040502d9008103904000b0549026200700d140e140010400007001b084a102c6e80801100000d085181810b00d4824a40885504c0c0d44080e6029529020907000141d800c1c00280307a007512450002640e824000001004020300400054195101d03505108807541d00080d8503050300d043d441c140392160740d07880c00304000e4406442c001f840e524010342603130b2507030f840c95000d803044d11020707a281620011520b204901b6075400f42d83c03414540c3e0300d510112009040a03000301b540207030042c22182c5441c40d42c441203655644211026500110000140300405500c22a803c005003038900e0302d507003043c41850303940740c8a500160050700348620000e00c03031441c03450007a144841c801000b0315140e2561100c0c108500203900c200d5003129070074500002e982800c90340c94400c0003900e400580c1030590070502a445802503115000d040d050116001030624a50f541c0d0181c044c0c0f4407101000b4213280e514200c0007520f4040c01400ca100000d09140b182c1c0c8410b948541541c00701842140c111007507440600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 58811846 1250 58810596 58810603
    0x9120d110a0f140901090302060a09030f0606080709050609070c050c03070f080601080a0506150406180b09090c031209060d050106180602010203060d02010c02120316031b0b0612 78
    0x11a0410400000c00c0030342070190000000110584261201c184018060b050300100d803044181c1140072030300d0440305001601308280941100151400c000310070503201d0312040e4211442400854006807551014402c0300414051900180201401844103080002c005035088000408120822a00003c0c2000f803010401005216040207400e554002d51119000200812140900300c12441480000200030780d000031468a02034000c4003924150329103c009845002d80b8482041d40261511404a200d85400148c3c5840740e040e9680000e0300380686090101902c8020030390000c5811102c03110a180d14042921040c03084007000702e980e29808040010300038020b05901003491803516001050458110070703514034500a2409904084d943e034030080707082c1c2c8804c0703030070701c1d00081e04040680055000c0c050030518a440101001e07507001500e001e852458101d0741d0009801c91302046040181a044079030110286140e185034031040000d902e4107030f904070000e40350602440c1b4003004c0b516040010f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 58812952 1106 58811846 58811861
    0x3070f0b03090c100e01020c040b0306060609210109030207080f0d051606050a05150301060503120703020a05010903051e1801030b061204080c070b0309120d 69
    0x80004100c0c0d07000506101083d1003211240e44944d0b80780c0c2ca136808450043d9a501d1140e0014800080c1380c030b07254040060040386008503140d120f4501240d550b500480903101240e071200114081380c050341100584120501c901c01f0490145c00040d00800f244901a40c200c0d0005c90f1a214030076107840d451101c60300d05910114081d10454080c401500880800005034000d15880380c0b501c0041d0b5004542410340c403969079041100c040e00441d520b040700c0d81c081d0001c201d198140303000f00344d5910240c1c98008640314041804010103108108900078a030303013740240990000c501d8050400c0d0001c400904900b01402c811402e0206480d06079002204401c83c40101307240c1400c015030090000c071380c0c15900134000308090200219061106409944101e24050303403801d45170400390810803070b80c0158030940c03001c0062000e0300d00e00040009013011583c460550310320082c41c103c001000d55 = true := by decide +kernel

theorem cover : BRFrame.Cov 58633096 58812952 := by
  have h0 := BRFrame.cov_init 58633096
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58633096 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 58633096 ≤ n) (h2 : n < 58812952) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
