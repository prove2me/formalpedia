-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0668
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:02:07.969303+00:00
-- url     : https://prove2.me/submissions/388ec790-5b78-4030-b5b6-761333616b49

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 119964028 ≤ n < 120143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 119965278 1250 119964028 119964041
    0xa120e0109031d06041a0c1c0f08040c140307120c030320060106030b01020c0301020426060108060a15030206070b040b060d170306060c120a02010501090501051c0c0504 74
    0x88a0380d4441007404141a800070b80b1070305500c80c01101c1503564200c0000940e040c4214030600354604298003420140202e07003015281c00d405844151203122485c0c017214600d5030900310540e00407603000e1f283d000045101e003c4c081d200303540c081040a81135041c1484560400030800000b9814403c1100104900c0e1042101d40a500c0c4550701045c5500c0c1540783c05001140d0f07049a130b103180b681c00034101020400000d0842d044580f0790500041031410000102d04048900f00c44a40540c00040c00140c05115646040118911682c0280c3c01162420a1302d803280c40030f10130728895030300040105000349000d80c812480c11030a000360403601e60b520f5001c104980c020710016a0310540300420002440030f45808580e03c4101180c1c54250318a07242d503070100482c040b507428940b00001000082d400d40b5040111039030340e0401d1081320280d10041c1c2c440c2c041da41c800240400117500307010001032026070900419041e91030081824000310745030b4141616a8501c40d030103451101180c20000368640310391050301c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 119966528 1250 119965278 119965301
    0x1003080a031e0902010c110312040b0414010806010203031501090504050705030a0e0721060e03030103050a050d020109022209080a020a140d020c090c120f04020102060a0c020d03020a12 81
    0x105140d01c0302c4000952200b218050300c01d0190501a8620041c5c0c0e2046021186940c4145412400044d46000c0307883c0c10f44e182707648603c9900004012a00003640d07000381048030712003c500c070240a101b038011104100300b03071026405070740140013040003092800b02d00e02500e0010f160001105070b4620015050300c1c410303501c0d04003044000041c4900c000c4240120701150f020341b00140603942c03901ea00900d242110340090400020850b4100080200756000948004240300c1200e850356100d0070b0954440036214001c55941c420000b90950007030040c002c942525030000e100f1400000c0004980000d508201c2c803400c40c00350750703e030440f000500311005040e03200400da00800e81c10b0b2491a10f00343c00301c0003c54200c465440040c020104590024880d4912581991048034076154001c0750b03c803901544032401811444841040a08a00e0f000d100e481075000340d00320340080e1204a10300d41100c00d507666101c01a0001181c2d036501034082d4005205420032403070111000c042044100c01182d5148840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 119967778 1250 119966528 119966531
    0x60a0203040615060f0f02120d0b03160f1202030c04090b07090e010b0901050a0c05010c0e01031103100e06030705090f060306100e0103150f14010305100902010c02091003080a03 78
    0x90105104443c0320b580111072a188042c40e54508014025000213508400b120170000301100e1183e00c1842846102440349030f02c920580ca806218403410050f1085d202002c0c02446400d11304000314401d0034440c0111428442d5a4407c072741404011030900050240c00c0e40c245c401d05944c0501074407a03200300703881c240c015a1050164180b1203001441e03030005d80d005054492004005100d103270301c00003c68082c1d02007401e10503922a001c050a4443e5800c069000d0102d510340880100d0300d9401001001000d0000d03a010040100b46509060b400c1c04260b900211000029100344034040d0141c0c5880c1e00944014216070400340d40b000080c44800c42240ca0442d01c642c85014005903003020051142c02116042c1042c460905200d181c03000340005102c00740140d000f403509486000c0040d0301030011955130700d60900018010b0480100220342c21f00c000c954610400401c107080c0c00007407190307030101a030581d07484260105e035800300014680040e045054504500c00000b0020741c44500524040999480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 119969028 1250 119967778 119967781
    0xa0b09150f040e0c0f0f03100c030c0512130201050c010f0603110a0302010c0f24050709050103060b07061a0907020d0905030705181b0406030e060a0c14030405030c060a0203 76
    0x9000d009020004428051800d08000c0080d21002041103101c4d82c2007a524041e08000c090b0000304440d008440042e09070040059050000400f600302d22803200712034400f84012210000304990520941001051440350701f00800ca800d440c440304010100c1c0145800c13800c02e8081800c1078211003046818410301551a8401c10401090194681e500b0000301c0d0034040c41480e60300040d084034409803004100c0500680080108200701603c00300010b6403200d004481e08030001c04200811003940c200b0045079031030701c001401d98824010300c0107640460003001d0409040c1d40e0303564082c00311001449101e011348072940c0034548a07095660301c0b55a880c2e004017560580200060280101a00914007a811040040c002529045112026008400c466081c182e4410142c81180c410804210200720030000d000a24654940c01038403200c846074083d01d860740c0303e19501b0422511641404000b05107011490343c80d4414000c069540700b8000c0007900d00e03148001040504056080301c0111840e5408030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 119970278 1250 119969028 119969071
    0x30509040b0a0b0703020606181602030f0a0f1803030e010e0a0e0903130905060a05090402040e0105040506190605030703080a0c0804030605040b070f0e09131a09010b15120a0b09 78
    0x403602da0410300540d02408544001c2a8445821270300401030001c50808464020200b0303c200210740058040c0f0840030784940402d81b0003400b0920249050000904081440750042010744c03c4034110782e4161a070f20f8441e2074280042d00c9003150a0509a8803800d130a00001d122100c8003021072040761040007540d6200301951010030b94425680000c443c1038602810018962240c221290540c2c8088600c035109640764030006010f805005001e0789294240001c1c042040380008100d0f000c0c0d4180841908180384500c00041203c15034894640c0c150322084082011400050040150100505d81140802010344a0034442d032701c10741c4211050359464040209016480383c4581c4c000b200c42c50032400c0c550020700024007001150400318483e407414008034070f80d051003d4918800c1644408034400d09500b40028840e0041c0c101c84402e0b407942000d24080c00c500c1c0c00510403a1103000c10200074107000c04000450354a000c01801c00c510303190b0b240c04402e460b5031a03a00461040c819240400040103900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 119971528 1250 119970278 119970283
    0x30509030f1305040e1506090c0403080d0504030813050703111f02060108011409100e0f0109030e040f09080a0809030f0408030a020106050301050c07140322210f030509040b0a0b070302 81
    0x3c03100509508031219044003580446c0840c0d41103d411621034059031211000b0903068422544024070300800010205044015900801c1c85140692140710f21540c81c08070685100f01002c0004025401c828001d10000354441d0382e840030540f0182144501c65080201e04c0c1100162003040710240e4405001048400800d000b156523068014802c0c0c020350030014002a624410f54007560b030381300e440e020303240850741e020044101c1c1400103500038403aa0503c0c0c1800703819254440e0040d07018500700303031640d981c46006004030014030340d00540440c43e00701244030880340d00c017020b801c0e070f03500d400100302075050074440c3c0000e40003509984010350313600e400840020b421910190302c024004e90405003005680408541515601d54000a07035500014209000303a05500c600d03048070410115581c030100701d0141c2480d114080d540c1d0030136000d10171400b05492925007091050300030310399841400303101c0c006880303030002d040c1d1a08007401c0440da080844001800200c01030b00401802140407860109145d0304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 119972778 1250 119971528 119971541
    0x3010f15140306040c0c0611070309051203030606030703090b190c020705060a0e0d170c100506030d0f0c0b0a05070e12030a08040503070b04050c1816030509030f130504 74
    0xc40c20080003104072640c0d21001800000c0640d88215035a003076140d4014014138039900c002d0751200e4200016100b40f0038084150300444019400252002000328550429802140311f0120807001507055540c1c180812406500c01003070a02010b864007a82e2000528035802c00d4000d003280d483d00850070041c01c840c0012100540c03603550840d8000d410402c000c5c0c50b03041c1220407020940c90407003000142c80b4003103200c03118180001400c8402c000c01036041000e0000c0a045202002000d0f540c0003800a0014420340e1400d03070b006641500324a07224418a802106020408086801d010383d0440441d106d442c4800e00131210900c0c180d440343c0c104011954005403030780c6101c0e01240c10440403000f4200306c070703500c2c0070700c1180030140211100840e0034000c042042d11042c0d98020310b0b1080f140f5141c5801601d4484803801d1501410b10808030900c0d0001c0440180d204201019640d90170740b00001d0103c025280c09007c85201e070004104080035403601d4001482a000107170400320740c4503c1d01c400c0c0801c8544 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 119974028 1250 119972778 119972819
    0x80405011b020907231b0f03070b01061b0807030216080a0b0c0d11040f0302040606090e0a09140f030c06010e01060801030b070210020c010c020c06040f12080d0203010f 74
    0xc0c0c1541440183d4032021440c4d040031491600704800c040e56002e400011480310081d00003ca8003003a000d84c11104403821442c2a480744c01500c080044021034940d9034010707580700034040c0ca110710040c0119845520605680c0e00a105801c3c040c9185496904440e44140d0b800d90058121450848003144103a009500400da100c00404580c1c215440e00c0302240b0014210f040780200c006105000f031120780c2c010f11005041c0d6442c1951f56aa1400c3c0c000d0036280501c41280981d00304000021780c940940070901c11108840442025581d0340250306004120800c811106120354212411100104109040c1c0b00200b200065907281ba9600c80181740980507885102c01d0b490500040c082d45910120090460b030340704010452580340d6500681c20184c1d1603100b010018808030ba103400d10760054000c00d01d08029a000c0e2401200e0450500a10f84254000c0c4182d41c0400c0600700702909421602d103444c02e004000e09828501c0768005007083e83e0003a07021501005c0106814030070203011a02e0b00c0d02400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 119975278 1250 119974028 119974067
    0x9170102070b060a050303070303051f0e10080111030109020901020f19060501090b060901200328020703051b0316090b0a0e0f06041a10030507022103040821010308040501 75
    0x80c40c0a0000361f891242002c02800c0584640115030710890111100c0303001c0006c5c0c990201400c0e01c44089025030b103007c4031100c1629080c1c000001d8281030620880601c100008070341440c607800d089180020750300103590390f030451041c00c0700800710312009d009004060250350a01c000c032600740d0800c1001e482c0c06030400c50810b807402e040700300682c0d01c44007240c21444003030030003a45440494401800f85a000b1402038068000041e444000d01c03400e0214005c83c524605400d9001d009240301241d503214680001000d80d07204c1c1017a0050346820307005400c041d03000281190950780b008021b864011000b644134100ca9501c13a540c200b4945000c400c040c0103007a2140015486c1d1801c0c20b001181c0031009040c0c02d01441d92844030a00c41c103440d41074142441c01c0905081450012000000d00401c0d089401d4401406500b8503030600d0070140260745003403c0c10a800e41e0440c6c4031521140e49030392100252011000041e400c60060032280440a8000d6016059054640c0c0ca80000580f00d9944d0504510300780 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 119976528 1250 119975278 119975299
    0x6190b03060a090807050a0809040c0e091b0405030319170c030a05130b190606050a090311040b030f010e1504052125021306080304060503060109170102070b06 70
    0x1500c00103800c9600030a010703400301d084180d90900702414811000f0280650040c1344003041880141c9000745407800c010380b410070050313203d40000c036102904041502e90050082d004541d444806108044124403192101c07450701d0759400c0003900d903510080721410021280301d441c80030315800c055148616018a20814900e1611082c1003205100040421032915903480100e0a0303000401e420740d141c140c1c08896191241014000c50110707440b072020508030760303007042000300b0a10b100b0304c1a44d215550700d44515950380d003076941d2400641e04403c82c03290401d03a42c44c0700b03030303100da80410055110b82030130030000030280c0284002c03d04041a0300841e080d10311092050100150000a01e152095440d501340044248098460700c0c46200340e85851500e40c4465100c2141c1228140101c1183c903c2124032001c100903044101d0709031030241c8510801a0014041001a07600600040d42d1050701454080512502c60052000d117080c9500542d90982d404100c050402010115482d0401000c4441203000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 119977778 1250 119976528 119976551
    0x2061608160c0f39060e01110a08040b0a270603020a02070f090b18060901031202030409092f0603070c020a0308040602010e06071706120f07080619 65
    0x40785404101182000251007007541401080d40100b1a5a40c0c002028003503c495450010701e0350310394469a240e440900c400d030604c000c45042c2c0d01d1003180c105843d10492010440c005580000608400c001c0a0090900d4140000d110030300800c003500d044400580c40d40c0501000074141300360004110081004885500b140b046000091000c403080d600d80580d560203000c204a08080040d404038050450090300810140106d42122404120680711401c00104040c21803525180c140c4100e074124186600501c040395150308621031401d0640110782c981903980c400c44c4112400c1d56415034002884541d040803d490385070f00322a01040c030781c0c10240881094400540740c1c1c8005050306003801400390b882c034210344034030b401d45008541103c1d070396403100e54131503010f4080d0010f08c403000070601410300001c01c071034050440700c0c5800d0203050310540c86503251014000d040c000d00c54070908511a01188502511042050a010b000110090000b60a04000c0310580c0304000c100f80c0141030500c80807150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 119979028 1250 119977778 119977801
    0x4080303130510180b0a0e011a0f04060e01030b04031103070f02010f0206060117100305160503070b0c0a02010302091201023123010c0203060901060501120603021f05130602061608 79
    0x4401d6001402c4454940310b00d01101c00400031000c0b480039a500b0000802781044510110044109050351086920649102003000f255924011040300d50341020041c00418104119658498070034201442c03e024500c000b03c2c95a0816030085032190080307160007003196400780080281040e9800101380381d040c42e0340040c1c00c041c40404100d50300001c210002c0d1201240ca9076400095400c01c0c07c0c0c8030f51104181464408510714047c0502921801c0400203162880c2421075160f418403030042c00404103250300450180d07212001003684409016103074a1805400e10040480000c1c0c5518210011074000031000b04001c5034003000314595415004218000220700901c03540c440b003001280c1040c032860016152501c01d030001039010302c240c800f045900e0005510900c1991402d880c1d071034000e56000c0d42a0142e581c00d00001390030049442150031546642800549482038500307002d401c3c81c40400c24608040c13070640c04180140d0001061100b9030405010000c0180c605d40b0b0205040e00d821b60b01d050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 119980278 1250 119979028 119979071
    0x120d1d0a1202010b060f0c07050109060c06050403030b04020c06070207080f07060c050703050109140105010504020406050f130306020d09021503060306010303050d0f020301060302071e020f1504080303130510 91
    0x204289528420781000318400c3d400b00242e0407005280944400c031001d5040007a400c246081605803107804c9020030650700600310780003200c1507a500d810003004241d4a14001d440c020304110281500c4907209030700791303071140003612959284200401c0c0390f240854009141c80340c1580001c890b03401c180f1341506e40d040701040240655000e401c0c040c038104041e183c55403034101d00e60b10143c50755103041700340d10070004c07020043c220000070600244001d90722001000100d00c140e00c08c40e07000c218104145075400c8244000741034040d144601e40c1443c107035642c4504050742d00c40044d001d26a0b03600d5940b401140b0304641280c11441ea012007a0b4207514004001c2960b564040c0005010b1040200300c01c25800081c0e00300e80d5403196003400a54807940d441201030045d4000798400c40c1e40c0b1403450750511800c90f10601d6030b24151b030020800801c401c443c60500c0900898142d00a034031890400000ca1402400c0006501820000303500b01c825001c01d003060b40c1000742160f5401c0300b40d0704020b020389143c001d821031072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 119981528 1250 119980278 119980283
    0x141305100b070f140606090106090e010905060105070c0b0d180b04020f271005060a02060c030901020c06101707080714010e040c0801151103030406150503120d1d0a 72
    0x155450046080c04038503c0000c1000a0443ca6030100c0504070b40700104001c0e0207032109840000481c0d80350711040d16103042c24050f030107800c0d10120042005541c1900855000501030504510b00609a00c400089032001c1d00704070005940060700521154091065200c0e100c0c0030103094004400942d2410710340103010300080c0c401d540350f01e21810166a0000b2501607843c032504410f031980251100500e0500089a09a9060b0018040050a800d201048503d04040c80d405480e00742d55440c0d081000c2d800140002c0d000e90350a202c0001042c0040091a014440132800f0b1154586031607001940303140e024800715207a401940342000640e900040d01c82c02d840b9003090300e9200c426000c0040342c1081003111025801401c0840c400b00c9a500140040d040c1c500c1c0d282e000c1800c24501409565850303c0221003100d50b8410000680414481c0d48402d00506104c0c0d4021003e90766540064507020200c2001c1000c0c1d07034002940b0304060b102c0d22840c1003880c040031088410034031684980c0c5d01c2d01c5191740007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 119982778 1250 119981528 119981549
    0xe0604140907031d06010801060504090809120705040f0e0708070510030b0607120c030206160c030e030f030f0c101503060207060f020c030c060112020a03230714130510 74
    0x4512454042c0d0013100c01c10b07050441000f0946a10409596280c0c030a02c42d600c0554a8a5404140c9052034018901540e401c00141071030644030005101142d0740c2c007104035441d801944400728040d512801141104201c410f004a8044401a01076041034420350086241d0350080500f0049910391110340005400302e402e00258074482e62011504520428100814580b100540c6007141e07901300304940b01140c00382e401c4540303d40d40c0c807140d0701c19030702402030076008070f602482d040000a2140b154600d800d030b0f000e000c1e0390b011400c000c02c3d03511b96003051801912189000c11b0040c4283c0d010010403602d1000d411081c001010034206c080002d400d18000a001c03140c001500c00e080c07022a81090400d810250400c40d0703909403190000381c8a4124105c6600107000d181d000103002a02800402c4445030014095046680b0b16036499004c4094840c2100c0300b00070100e54100c0b07170b40050041c54001c201d000c440e1a40000ca02c420002344404003410292054a460144901c2500031000b401c01d54095480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 119984028 1250 119982778 119982781
    0x5060f040209070f03180305030106030f09050c120c06040e091002130b0a030b0d0b0601030e03130501030e0f0601080307030801230f0102010e0610050a05100203090d020109180501060e06041409 85
    0x181180503254001c0306e01c0e00c41c0c40181d02501090350242c0110304a901c599020000c0c4281241d10301c054a05448016045038029515008207151510304096134000c00800c60710581ca100000c50416002a1300242800c1107a80400211520900211b10b030405001021464074000400c1c9640300110b40c02547c080000100f0b00101b83e6010b580802d01c0c0c1c410042030704188050514040243c40c108407900d80c0000e0600f5902d98011b80300005603400ba62841d9510107025051400450060400150704501845440b1030350909050501031180642440c0014581e1500c550038042d20389203069010461282514400764920700d141072545440030401c0b03403100c9500d40e6802c0100c2c0076061200640d406401500280301e0f88003103c48400c0300301c54041e6140304540b5a1602000a021414145071025800400130000189092113243d64003030310505050b01c80310740381ca002d032854801102d0401400c0780d0b07500052204541105015200c40030448038581380c00d04110012030701900f083c0c80a03015908480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 119985278 1250 119984028 119984057
    0x6011203050c011b02100204050a0317040b130302090c03040f020108191d1501030503040905091204091e06050d1b150c1a130b04021f090305060f04020907 68
    0x3070854592070403100081c414412143c031100d0045050701e154030094030607004114903020307060003550100e070401040702000c9480d50b05c0c0d00c1d80c0b8454801da0400d14110800c00400d44241c0380c4003a1190244501c2c1d91005c281c15807050240b00c8801524a04007840244208400280103904e0b0b0180720b6420718084e2484e8442103400322801c030b00d2010309450181440c0d40f18140e00c040888040440c035884040701d04024003921052021079080c040580141c004120034840410503410154001c01c3c818100c40001e24041481e6406030000d130040c6030400e40b02c0e04000c0420302640c603000100e0440000403c2070744d00d0040011218101034600401c0482c9540d5520403019207040c2c00e100a00c8032202ea00440035154030014050315441108031a451650b01c001020803404000f03880c803035000b650310364900400b50b803541440360000a0049a20903070300b00c1111100b20903c012040c3c114a0368448a41260031443c1690030058018802d550140c84002048056640e10605580126076400e01c10440d10030076 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 119986528 1250 119985278 119985287
    0x80f040206071407061809020403030215040c03020907030b0103140907150c020d030c0c08060f0a09320d030209060901051608070b040b09010207050a020603070210060801020c01050c0c06011203 85
    0xf00c05010030700400c0e100040164100300600000380c040b00e010060b064941a8000403030040b4000070300103038000807a1040c081603d40c01070381c008ac0213004842c88130b5681e0307000510f00c0070201c0700301001a44520a20416503014065040c081880070711920252609000c2d441d0b58100a22601e86d10014022000c00f100f0702401a01d40c00540181072482d0b55112402c001d0448420540100d030300311802c0030300040e400740100c0d03c64003603011f4815401c0140c440b0115107010300303004c4900f40c8400c0856031880c8a84c000c05020010359143c0f00c100c4c2d02040e01d40340c070b1982c1444110604481810b0040040c1441341d1b031200c0894a8000d401d0800940f1014042e082c0c420b201c40f0098028070561b4001405000d2107150084240b155100b0b1403078441560310121014241d00402c02d0040c403a900c40603170306c0c0040c50004003950384521680304442512a440d034596054a0382c591003588140d50020307007032420500a0007000e40c0310000d81c0030145000000401599507030414414a00c0e0076040d0740303103401098442e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 119987778 1250 119986528 119986553
    0x6060801062309040b122104081b011101050a060501021b091f0509092d030904051504020d1b020102040e010e19020a0e010305060a12170417060412080f04020607 71
    0x2d855210302460b1000c105940302c00301000c917003001a4a0044034542e02e001400c40d4284c6603400c4c040c240a8880d0300319005805402d071031a50500c4000305844240440900c07500380308fc0918140403800c0c03441c0800290034010f50740c07080406031800c420101c4441c0c40d12040356422001c03607055004541404041010703504059001319078071220307400602450210004603c1c1c07510104020701206407075207090621514810707046480041d00700b0b110b03466407854281c0c461075110094403e841500054032000034126844045035148090f0b840314601003001090000d072002c252030380021450035080c00d03100485400c1c1480b070341400c641403c00180c41c440144c0c4105400035440f400c01d54451050740000340c052126414801d001914140000303080d8a08441c114007221219114110030344040e85400701d403c50060140c002010081000140f284a8510f0301d001c011600000b034039107802c051400c050b882e10505a50400c00c0860000c0c4041d07012081c1d240794001d981102c800ba56201c051900c00d5a00e1035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 119989028 1250 119987778 119987801
    0x1206041506090e0108160e09010b03070b040905090102040e13080c07030303020306040c140901030c020a0b070c12020c1c150608010213061b0b06031f0606080106230904 74
    0x21410030010303190703820007001d0060b0391030300351034058603030f2516004c170781d00c020422403c00240e0401004120740f00140b840150031420701d0002203a00700c10740d40800d140941ca5403000780d111800041c02c00c51f0803c2d900c1195045440e40000794030b00341c03404088100d83c0002030710100c0b06891070202c0b070f001c114004040f640004900c50030344140c542e4908001d0000d4208482560040d0300f41540d03885101d02c00c00c409102001c000c1c40e9039041100e0100114000c24452085a00354807490400ca0003203202490400c0c03241803039030307a8003020404a18004c4c449400c0c90708400c0c159801403208214035070712010925121102c101408144201908003500c0103c00091001070355483c1c10300100381030006400a00020307100c0c82100840a07a43c0c08102d46d4045c2603000381c2d013400b080d03080c1200050200042140c014600400316041c6452820b01c014225084130845058256205d00402a49410024490040400d0b00b8107045407550400600c03400e40009440c81e45591000441058503585d5500c800c280c1c62 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 119990278 1250 119989028 119989061
    0xa0210050706290306040b04061d0f010207140a03050301060309081911010e0a020906210f030702030607050a050d0f1d10050c09130903051204030c1214120604 70
    0x61450b43d00d28101007480200c40075211201c84400c940c180018650f0107242d102a42940c11ba68686421000300031084401c658070440d03000701200d80070b0400102440862503400140e958007603140008030001c8024020360240c001155001c0400c0e0060309890440300300381408540b17201e071481c0200c098854060a103110040400700c0d032105d83d0340140082c41d1100c0030002040b041d43e0703084030191781c2c16a0300e0307000b94020003181c0040d001e4105950394002c400141000032130600d1400c00d81c5820184030040c8181315074004940700080d0b103410828145c1114560820034034040c003840d4010014465900e6150110361180c3e00b1201c24006a80310880305121802c2c0001803290f101249130b00d400004540703001c81c03410540443c41e2003014504480e91220300514444030f032030419508401408207898294107000051094182c4090201c40682c8140e00c290307075045801196143c01210f2285a0000d90f00f000224065a400d07881c1c400c040302d4010f81405540781c00e55488000240140141000703119101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 119991528 1250 119990278 119990291
    0x4030606030f0302160807031e0f08030a15060503040b090c060a020d090e010506220306050f0601080f04030909090c090218270a021803150601030b01030203090a0210050706 76
    0x20b10100245140c61003542654009400d51541680c030a0290150007910f0304101300c10800101a0381c4c0c2c0c44180c501c05509200144d483c0d403540100700311115810303501420004100441c000c1705100f0f80d013003c0702100c203c110880c03e200004106000003000103200c007803580b0102d20880f40400800129001c010039442e036500d15030360003d4461100d81084000315039611408140414a440c8103410b03100080d0400c0c1c2050038100d40e42640320482d1408844030700c0d0003003010010810500915209648018964901d130034540001040404014102d440201c411010b1200085d8090117070f004407001e10001140070301c07480c1481403400c07045500400314107100250807401c0a80c02c0408041d0a0021640c0c0d401051b12400c20b803104c90b070000158044820f207000018410701995010f05281d508883c1e106028080a0010078900705288541b91a0041c5a004001d075035a410301a207002402c01307107825411400c00c18403466841d03552100080c4a001501030162400b8072503c01e880c5c0043e0000b400f48040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 119992778 1250 119991528 119991533
    0x3130f03031a04060302060a081b0c0120071502030a0b060706060602120310090f0905010f060810060b03150324010302090a0207030e01080c090409050304140a081e01020403060603 79
    0x78440a02d8851180c2e030300c0700b1070185501e0300b84582d90880303402801303461030002d146508076000c400050905a01c441e061006000c81c1c03240f800500310101d0750100002e40c0100617440d08055260441190110704010031604000407078241091f074903003044e600c001d81c481d214103002d40080d00b811000143c0065000c600c038024051180c000c40c08545064003a00d000071400750b0705c0c58142c40700b181d540d9144140329608001105070303135100750360000f030070307040003890380c880e40da41509660700143c0382500b9503255401445110f00c2803190040c803081c04a01000250318020400780180401005103200061004000c40c1c5604e041c030030060740000e10008200904285c0c46c90b4200180c1c28002640250584030015140c00c901b40300301c4074416015100c01070256010300046031340714801050743d0b804081c01d000c041c890f41c969010f030120f080d10510141d40c4980c1000080348101031018031a92140c54801c1d010010180003140641307170101151651005030701d8407004940a072003160310050207985041ca00109 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 119994028 1250 119992778 119992781
    0x190207230a1d04030e01030b0d060c1403070207090b2107030c061b0609050a08130806100308090d06090506250305011a070614010602010b0102100c080402040203130f0303 75
    0x10640049a00207401c54964a907058800c0b0300300303020103030b0952840218021034001c25481307800340e6051501040403241c078008501401c4a6043c101c0c0e140b51208000c1c080d060700400b100758000071241b60a815460078004c025a1080c891043c6031500c0d03500c01101c20140c50300300010000400d518020034100210b01c12965a5441ca0701c410b80e011960700c40045569803061401a84554002d0803011404696454504c02800c2c074201c03c44192280d01038500000d00e001c005400000e11580b050103c0703e240054803801c2c400010a607041e0f000c40440c1c03e00010f41200c05450070072905482d000c101400f02c1c130b07103640180456000a441c510030a4104081c61644145500325403268048a02180b0300340344050742614028001c41203808252110300780203111070805040ca4078000c81d80407441c5841c4100703c0500c5e500a03000130340141d450b040440035550301049504102559036600b0403400c2c0d05100000e10119000d4802807140f0340000101e40c50400d280b6110704002e400c46031306414194949000b0b030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 119995278 1250 119994028 119994089
    0x5060d0f0e03040f0b1201050f03031902010203161814120f01050402100c02030a0b1906140102060c04030b13110618010e0307050d021315030b01180b06190207 70
    0xe0101d071130000c010911031141803d603030b507808104a808240c0c0e401d01d400c00c21020400e81a00d86c16201c02d01c608400107070610f045100f00101d5400043c1d490038807803584206135060356204d10601c81804642c00f00ca10644000c001190f282a03828603c0c80fa40900107048000a0910f40d00e1f00d01c54060140000441135100500403882203605c01c60900f100f00080c0c4092982e104040e516030418441d00300400e80c500140d0341d00417083d480300785940100b00420300840d07855400c50f0107205014032400c03040b5601080780f9031300600f40c1c1e00d00c2401d00b03183d5955003001b10350007405248014a0404018100f000c08010035080107002403a243d06d5000b803030030515a00c090005004d00145d051401602c0d5802d010800e48117440303002e4040212065183c003404611840c034244102041d03524210f0010081d114440b110145208030840c4c2c119502d40913124280000c0f1004402c0014a002d14848444e60f9080071580ca200102c1000074005059080130f0f400c2076400d84c0400c00052500d906030403000510706412 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 119996528 1250 119995278 119995289
    0x31213051608011406010c0305070303090611070605060a240c02010203120a0f1b0c1106070204050112030305060414010e0709081603140f070b0f07050d08040302010c020604030905060d0f0e0304 85
    0x1031300c69690080111804400300b80c0c0a408038104125200101c1e1082c0c2280d1401401803a012490041d000d0394a440b40e4084071080d504d440d41c0d0801e01c8518501003c5c81030090682d16000d080390b200041035000b0101c142c050708018811140308420840e40240182c56210352644c00320251460000900c501030b00c0c0034640c0c044103d161489a0200b0890409064280c81d49a80c1e141002200e50b40c4860b8880f0703407001103960000d0180580c800594480c082d00e80a000c69864182e040b003070a1802406860000e0505031045003440050080b00c424058040d04503203140410828549070050241c07001d140300e40041029005250b00c00302081410701030202141e00c21341c001d100364250004042d468462100c002c02c281c0e00b0000082040c0c410103c0a007050705529103089207003c0d40d075039880c1c1c64008580c20410100305400100000c2c181c0a20425100c1803050001d000f5629103541e004290311400c0c040c3d07621481000c40c1100c02c0010380d0340f00301c05c08044000d080100000c0300710400c1e500c0c2c0062065 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 119997778 1250 119996528 119996561
    0x4150e06130305010e16150c080c03090306011a0316030e07032a030816211d040504030c0308090a30020718330509060303121305160801 60
    0x90a85c04000090280c5038146080d910080103042160074201140200c044070200f0862301071420100301c040009080c10402c10004540c0c81c41c8035420300d400e00c01c05070320814407460040300c032480211070394003120380c08409181041c90700e4030484003e6005003544a4440b5203231160b101d000c0100007510b2401640e540610602000034041d60288101c0501a03000c020142d02c424840d4441c3c0140017090703860030070700c10721482204041c0c0150714034015426200c551b0000303a40c00d100380040c1482c90040010b910040d6001e11851816803405441e0040b0103100030104429000001d956580520a01000075406a080e0a4a00200004200c200c000529046480341c103240118410b500003d01e0784221804d07a42d4960200002080c2c000051480c1c40d50343c201200c888030043c40714801000880c0450780d195006940e19400e22013804a800c0008203007038000e134000c03c030400c004c40c886008036030701141481c601c0e6511001450402d04109a29500c05004501e0700c40204905030190042c101c0381104107203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 119999028 1250 119997778 119997791
    0x71b03020102010e0c0d022709070e061503041101050d020708090306060d050a0b1308040b030a0f02160803040204020915030702010c081608090c0307060201091109040804150e0613030501 82
    0x1803017500e9418590a50380c2c0520101c0304940142071010000304844d1000c44050401c480c0300da05644410021603c80d0307005c0d00311140c00e2100c50380400c5404d410000036503400e0410503041c00e14080e688406000600841e40010700440c4584c400e20071a1076151140405640310707106442d14100d650040ca201c08d10070701642001405600301496501e90141d000802452090b0a9071a222080b14019240d006040807607482680450603910040000b44050380c6056034910303024060004841900402129013401003184c1181203402081900b41c0301d0b00000590350ba5200c620004009100e4001d04c83e0304900101b05402178004800c024510802094009100802d0311603c04c0302d40c0c1c40200c441e80d804010304e480180f0442c0c0f103600e90725072207042e6000f11011580703e800002c0c98051550300640c0184c3d100c0c991202003042e03540c8000c48014040e5103c050794202503803070f80e4060040d8003c0a1114034030300202d100702e621884100c4a03494024080903074956074125581d02d0054240010f541c90740c249031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 120000278 1250 119999028 119999051
    0x1006050405010e0f04080703020c100807020d0c05060c0a021c030b1201060b0403080703032009040614030a1202030d020301030c030b0606070b040201030f11040f0f0b0304031407020105071b0302010201 88
    0x60301e10b10604e4594102034190780c41b075540d00c189400a400c00c2d41144104050700642e500c0d4100a00031249070380c0c50b07070106440c0018000b451b000004129004008000351110700041c40010640d8109440b40b090603212414858100c0c0b0340307003114403046911040141440340c000d4040c1c2c420764140c035042e84e0071384000e0b400300382a509032042845034809055040000304007084005000c0c003c05031191030b001c81e000c18400701501140034202c40b502c400600001d030764002842d092091800170306480d10881c10b0b0300000c9002a80315114403102030003001c0d22249506480e4800e00c1241d05c0300f90f16060454803944c40b03051040029405020455a035149100480d040b0300d410415aa0384681c420030003402507465078011030282000e0740c5031900701502da444450030f90000c3c002410141c44401d00b4040300a02e00142007401c05150307401060b038450b0030014003020a600400003101100c0310692281c0d81c100500c01220070340301d07506026090800c81420752101c11750010800003164000d90080c00781c40d4100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 120001528 1250 120000278 120000299
    0x906150807030308010b13080f0c030d0c02011e03060e1305100203060d0318090f15090606020d1409040c03090507050102010c1d0d020907050a1d0604170f100605040501 74
    0x900024011801d61320041100325800001011060080d400800015a403500070500e4030024562600094002010082a60404200c440700c45252481d051154050540000e007070440b190241000d001c41004580f607a890103034005400401490030f40342840e00e04942040a001d0747e200f01260f8a010b8003190308018415402542e010f28801403012040003d01e81d03017a41e030350005401b20040b0307181601c00080c12826512030701451b280ea00c3d03c04194040c20001d007410b54102508800010ba103400c405001a95000501a078080c24138149061703c003038403141290440c00381c52001d40d0b0190a14254030030740d03075050b008240d0302440b5604603200d0710b0711a07005a09a0301c08560b07683c00203040090944030013814903130020071540080d20804820800b500441d440342e80c1166070b88080b400000e1125822503000700020820f41c044001c2c480d00f0480d4034001091403150344104001204160016060306109010940035185440104d038010b600307a5501e480902018420148501d1900c400016081e214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 120002778 1250 120001528 120001543
    0xc03020d091a0a090819020108090f0304120c0f170f07061d01090b07030c0b070804050607030b030c090a291c030512090303180f0703120c0609061508 66
    0x880b215040311184619620500b0b401c03079600076041080c00d10300040d060390188004000003a00b0341031141506242c0c000074140d00390103840000c00ea0b210452010020340c02109640944800d000c005c41154503605100d11000801d401142c0402c40c0300d0b9000842003801f04175210807a003000c0c140e1701000d01340100d554854901d0b00c117600c0441d10801c0c901030b40c0d00404402034071600d03050501d500c8254540307940da1015085540220081030320f1910003404d114882070101d81c05182d6150a0304649016030721306e504d602d0702400103014140ca40e14007107000d039402d0000341ca0b19600038010728500d15040c25004080c0020402da103940d802c40d01e030b490318100b0080344403a0840001401e8120b0090202c51a2540031000140a500300034043c4200c26071046c01c41c42050041c00c0c3e5900545d12800c09204a13120340d000315044c02202c1d404180840c2446901041341c0c41141e03008021b103000040034490554060620040050807079140a0454082004952007490359807282c0070011917054507400c2203540c0d01c08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 120004028 1250 120002778 120002789
    0x6031a03060c0d020403060f060306060b0c0a03051e0a031a0d05070308030a0204050303041d06010302070f020f0609060c011a0a0602070902030c0706090609150510050d020d120c03020d09 82
    0x7144002440300045240101200041407200602d0540c0d240c4541d400c40340c103942c0a805680e04e0f410304009104440c0940d002030250a2220380c58040152491903962208602c01070500002050340c40182c81c1c0900c1d440c80403117020030b580366200d8002e03000a00030f10b102000000c102440050808050078103804866109034445c005086107400e54450a4664000600d1052255002c100100d960348050000d00000c0c014038084094225003003d40d880c02d0003000f82510304061040c004030010520250b0403c804513015116000400222008180144200039007560010000560101c401c101584417241030144808149800c40c507807810016800b565204100042e8403090302440b510000e6130040d80c00116440d4800e1030080d0a69030b2f00e06807945a80c058409659618217581400b0001200403041c3d08021400c001900d05445000a000114002c15000c0c9079460703084021910f07003589c04500d294016481160001d50312200804401310302c58101d0040c000d421501c50703483d0044101009480 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 120005278 1250 120004028 120004033
    0x8010209030c01050d09060e0307141203190905070b07051002070b0c03100305120d050603010506061902030f0d020a0f020f030d0e03190203031501020c060910050f0a080106031a03 79
    0x7015000444081c5c02122044001c560b41e00d014030001050b42c86982c006d052084003a43c0c9032126814101c0c1000038003016111150040186050840034503022260311048004002d0b00c040803403050b8a00605007108010020301c1510300115249032000083c0c1800340c4a082240c40c20b00368040c1c0f0a0036809590b000800490185011514035019500a540d100b2001c80710548400d50301c2d100e26107040703890a540b084c01000094000307880740d0607006d81640040107400a02c018200a004100c0d50701c10700c580101c003041c0001d00c00d0880d52080c801c84d84e001c81492000b640b01c1c2d902d449140001e6001240703e801081d94240b0780c0c1010f50012031005421590900590700300b0302e00340c3d080d1000c0c001703a040400803408204070503501c203504c0030401e9091107001e80c010358a034501240c0300c1110851040100d030640d84183c402840c2540e9110440742e0301d0000752020010004e400d1170966850154015507801810003041429555522007903081c1200c4a550f018071941030441003203507081000841583c0c058 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 120006528 1250 120005278 120005293
    0xa0b0a02031b040b19030509060109020a050408060c0a0f0c1505190e06060103060503030c1b031903020303060901050d020303030708250804020907030501060906080403030213080114010801020903 86
    0x901003640519804440300750340460030140020100000da010b500010201c210100c0c540c002c108414035002450040707800c041119003054001c0b00e03a40d982c1480750841054001800c3e000980c401d6094a004110503802c842c41c03414610048903007600031110301030004051013080d4803846d200301b01c1e1305c0701103400c200f450b00c100840d1804038001d001d0090441c9583d0100c41940008030026128034200080c14001520701c0c1e00b4040001800c0e07030403c4d84514840e0b03101b805581d512940100701c01c0c40c41c110854417240c40d040c001000c0703804c10917400200d690605c580e04034803062640120040d841188210b412500517a00d440030004041e0310000060f405910030b20005070f826011360100f0b9002000310511450801c00c0c002034281056003891903200084800c01840210305010203c10f400540c1403c0c2404039604280009290300340e54898101009044004201818000e80c11958084c1c20810b4100c0c0d190f07250b02040c1d010f84012070031614201c040200002c0c50b03080c18405d0310f083d844010040d01c40c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 120007778 1250 120006528 120006541
    0x100e120412020a03230606030102180603060316081506010305190504020103110c07060e030a050607081801150602100b1c0309090903110610050d0201080c1b0f0c030a0b 74
    0x19444296080381c10900300800030010850005c800d008058a0301400684410318040c260f08201d0301424950190b80184010600421307000b050b14813285040d14456203d64401001907e01149a070840000c240303404004645a400450340c3d85000c1494415500c081d110f02e8011022110220b03580100300c0d041d01d042d00c6000130150006900140140350100e42c2241c2000c002c401c540c400c100c0d10005a200e00c00c1088280d4010001440c0300d1402c4024250417402500c1da0f0b610381c14020704150802030440c001505282010000e1107285c1d0500000304510800d42040c048595400e00444000d417060045400a03d1028080ca44084402910b460810404e20300d00c07000ca8666440200c050000030b20380407601a0b0903216a1011900954411055103d1501e2141c1010009005001c1611403d44107000d80d03100c0312900c0c0c40032503081ca0646880e83e13030313034404110a0107404601c00305026545203100071310100082441b401022401518410b0340701d8003c0580c0c0d80314610004040b000340c0c0300015403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 120009028 1250 120007778 120007799
    0x6070f0504090c1110020c15010506031f1212030b030c0307150c05010212010609050a0f060c030c0b07092610050a1509090309090605030303060409150e100e1204 71
    0x2148041c40c10020b5100b509480013500f00343d9142c01c3c2480c02075000c159a074400d041040314408103e0b04c1c0025007032650501002c2036180c80020a002d40f0582c2c0b074812501040036150780640180200321414621031100e00c0d0507003424000b00031000009045c090308070b0765490042036a501e80440180201402840e04142110700360813404102e080c80050100c4401089084c00140304a405d551000f44040d814610b015148c51103580102d402040c2601082c0800401305800c1015202070b4180003017160014902200d49061103000100750019a60501a000f504965108103480307500c1a40c645401c0340811403213444c5441da400c0c441c1503014100d0750999640b282d102c1d6400882d00d640100750004500141d5002011540c4820351183c0e44030090801c0c16800340450010b402860418000e051405000035036a02002d40154400e80d624004881080588403040d1080c00c2110340c2400085000744000f5141c618040e2070711405070405002411040c00802c0f4061211076500c01903007490b041c00074200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 120010278 1250 120009028 120009041
    0x90d0c300213150905040b0108160b0f0708040e0402090c1602041d01090c14030102070b041506051c050105362802030c1807030b060409050109020c06070f050409 71
    0x801080e526080010f422405a520401030308104c400841c2c030381440c0c60401c0c100c01050b4480341c510b41040108401c010340408940e1b0844007114000c40d100c0120300350300e660a01c03580000600380040002c001880341c1910b003049109034004c540c00d00302c1c0d80e11040000c480e44140707100e200041080720071200040c0f8041c0d012805040400081e10041405002044e0171903182e44026969030340c80c090100b1150072242e400411521741030b0b0095003001201d940e40e02c00014003a0004140d8070f888900d40159445a5011000501c001044070146082e0f02c1104040c92000410594070b550901000030020746010442c81e2010003a03012940609000c00d481c4c00400300d8500141466014a800e060f03900203a40c031186148c0c01d0390120048000301c40c1d1040602d44003030300d4407107130080d04000e0400c000d440c011200694403103810700700812141c050a0004099100342d403c1f24141070710300400441c410740e4075405040ca80107480211941a1a80c1e4025900300c1c0303606004e040040c2c1e081106000840c0642c1104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 120011528 1250 120010278 120010309
    0x1e1305190f0e01050702070e07020a020d030e0409121101060501110304030308061f02070f05090709150c0503030906040308060607050a030e010309120e0a1512020a05090d0c3002 78
    0x900d0394042d44a45003515000c0c0c03000e10050b0301c031500c14041e01ca00b42c01d40a4211800d80010301500c1d03c26404210b841c41c6200000d01030082c89110000307180c80d540c12070048103506c03901c0f0503600c0000e4000900301301c100f0380d405041c9628054012a180d401040d6801100400d440114181071a581d402c42c0c50f540010310190300040305140c1c401c0801d1003010101403d0645030068400c481c1005030400d01a552030348218460301040e02030046207a0880c2c02d240580b5280c51034030600c0e0030000825100300000c0c2e0001090703448000308002c0c0001006c10954000e500c2076440d044191664420011140030782e04010308250440003c010029000c0e16480d218010181004100f1900a4485000c81c1c01500b1900d808600c8000355040580351084000018188160361580041c3d030450000303015090b40b011049209074005081126a8051404e0321046580106450483d1f42146440c003422680c0d880f4080d603807941d03901049400c4008070b040500c030851000c03400c28030b40e02503000c101e80160400e211 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 120012778 1250 120011528 120011531
    0x60b0604030206030a020909060414060909030f040306020d150e010b03100b0f030405010507030203011a0906070615030c0501030603020105030c030406110c0d092c0702010204051e1305190f 83
    0x141c4071a0090342c4100e0171010300603100e05000c4107200075031074002c2982c1c5c0b04501d4074080e0110b1000ca02170391900118151044443d039501c204680e46184a050800c2006c00c1001c5800410001c1c41e800034400420364007010b2000303483c090000c0d0a02002401007e100d805071000511901d40040051503000b5004195604c0c5244d0f6052089055400880403c0c1c43c0314001042005104090003001e8221035140303011450340d071409041d81e0740d00341000c8001c0c01c01d02c4009135000c01a9188000d580c405e9400400411003180000c0d403540040e4682c0c0b00072224000e0041e000141076002e80b142e002141d406840d4945556a404100202d0385d1009004a6465a541c00664070f12a80b0002400340c11285000401003050710141c043c11112003035021500d0b445665040301d100151007901c100594008507003411554450300010380c003901891b000150480e80e200000401c42c0140984002d00f080d050b903075680901d030544003020964008917440e01c60347ea901d41c0e14180b4040554000c00c0c600031b0643c1c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 120014028 1250 120012778 120012787
    0xf1b030f0703090302040b22020d0b0301020301060f110318010f0302161b0906080a110616050a0326070e04090204050f0f06010f0815040905060f0708070201060b0403060b06 76
    0x80800c41038202090640024108040503c00c500b440c0c8108026980100d03580c0c3e004a0305413105070075620045c21908811500801c441c40d81010300d801c52a034000300100255107968645a00521150b62040d040f0002103d0001703480720383d8004821508a00c5910038000103400741d60005460184200d40fa400801d6400c0081009070b0b241c84007500e041034466101020254400000c0c96592203891304810605c80c94900100b08050001540d400e0303440e171080000288600b1080001c226028140064404982d62042581000008540c90b86098484d44a40d95140500c3c00b1684c200564580c43d5000b03105840003040c2003070701852082e621844024030102d500201c940c003207401c1d81d0301a00ca08000c21018028042c09130b150445165000400380390010510000000c000c01c282006040d60070015140c004203a01754a031604010003294210046480c0c904010605882d0000215040700000c0d207500702043c1601d10602942081704c003180401d0381440c8c05d5441c1c080082c4407040d0520703030003d820070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 120015278 1250 120014028 120014047
    0xf180d0203010f0f0605011803060f0204030506010605031f0e040f140111070501110705120c0a080a17010e070c060e0c030f0706030615171506031302150f1b03 70
    0x3503803c440400f5880811040e0002c1d0840085d100079030426810700c10740c00322100f20f590820007460100c0350070120104244a004a101000740704030780001d0403500600d0000708205da0003d000b58014200820050a004e20070303c1820164201405569441d13000103001c038001c44e030040d0302c0c043c12030b0040c0c140010014491038128215201015840c04182000c00d0020502000380b2519020111501070a0319100042e03544a03100c10104604069141c0082950311f25400200005510300c0e82c011080e6995000544000d407520003000402d1034800640d100114900c0603d403074036806a407454503510a030f000e03107507038000c05000005183c162900c44c1c4070400c202c40c0e80401c002d00701030f410300f40548403072814039030b008095a0242d00016000310165801121180c1d00841d088041d80074111144504e071101b0880c03891071040001da580d8801030100c20f0080701c081d00c4880082c1c041c400c032101034600aa034600c019980c0680c44000724012004d109121501c032400c09038001d5500d40c102583d1a00c2c6080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 120016528 1250 120015278 120015281
    0x60a0806130f06060e090121030504030c091a041a0d0317010f0510020105011212030b0a0e060a0905041e021903050109060e010219030c09032f060f180d020301 70
    0x110102c02e501e0fa201c00301004601d801c6140d41442c200e054a040f0910740c108501c2c100301e040c4000c00c0805401d141782904c030605110f0f07429540a943d00c000101c0070b141d601c10386003000e00420985001e0788100f2064854030362a04c3d12440d1481c5038105040116039490800700038000041311802d406102c4200d0003620503019070380ba1507018080c1095504039960074001401111181e086542c029a0326000c018403010b2403641c000f00e20268040e103d0303c140d101700c0304120007034001e008140d60405100e26012564040d2004090710814090b1074080106a55038480c03001d40f20f042d140980103c01c001c00514003818110390407083c01e0f00281030f10054582d403005030410600b5580c41960306940d1036001d81c00b04a907e0060000003017924000307608028241e0000b06040340f00b48240414036543e900c004240038000d43d1003100558010b400c0e440f00c000a44840f6094004104600ca03107882c05040391021403074040d080d80d4605105882c002d04042e49180843c03040b03011050349039030001c2d5000c1900d0040c0e809 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 120017778 1250 120016528 120016541
    0x503210d0608074e0c1e0312020a0c03150e061801052410021e0c0301050a0507080a020a2003210105060f13051f0f030605060a080613 59
    0x342c40c001c1c0c8001c01e1024900690100d02c4090700c4c218054100c1d400403003240340c10035108180040c81031078009461500600041550780460404d1198150851001584481e81e84c1103034058501e640b144020075004907260600c0502c014503500b421401400400c80e000180d042480041e0720011321058020740c03c0d0716103081100c908451000c3c1d421240031150342170154581000241c1c1804404080310510b00742851082c03203140c0d00942c02140889840c0b40b00300461007e030907100312900c0301c240f092404c2a4981c1c8201014501a40c01d0401148254000703110b5076201d1150344d0b42d080d00301d40701c1c9014540a0351107903a18608100803070409081404598110348a40d60845000310b0b640c00e40c0e4848503685142c1d02c5048514008400e0041021392680422601144942280c1d25505c4030b1485c003500b0868101e40060b84c00820040740c280e0709101c018519a42102c83d921400141c0c00c024a080382600e841c0d020b2103811010910582030107e004444c1260082c0700148a005031510390076016080310358 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 120019028 1250 120017778 120017789
    0x4050c1203030a060504020301061b05010906050c210601050901050a0203070b01120b0708070503130215070302150c070510050403020109062c01020c0d0c0515040312060503210d060807 81
    0x2000060156010300f900c2100010f21043d50150700f190703d858070240149400a41056485801c6201c04042100079448001030a903c160108640e0401c0a11000141c0104c44024000c0740501182203c14542c0c212081c80350405a6400e40b03050300900045403244c20010f00700741944014844100064901a1a85d029020507140030f00b17010401c1c10b02c0e0010700000760168040c0300c1800c0c01d00c41d106070300600304c1c0e6000d40516100b20742e0242e24030100d4407544003041448803206020403103008150340400c1d070021303141502202201c0c50301c2e06c50600350a841071442c0148240d000c000d001e80030b04101d400480d8024001d000010320714085440ba6019241c0318030070b8503095041d1500301492a00414518414a14044021802c0c400300c0480c0941d2951204891411b00c0134000111f020024200f0440d0b00a43c2030480713040e124181480d0180c00520041e00c100c54840c1881c00108490800007040d15200400700c2030300c6202d074600f420b030407130544c42080313880e1089840d01c01c081140e110401c0500010039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 120020278 1250 120019028 120019033
    0xb09010207060c0c11010315080102040b09010f080c09100504090e0106030501050c180d06061a03060306010b030408071b0503030403150b060306030703060f0209040f0903110616050304050c12 84
    0x1c40c03a191040071221190024030602900000c1800480d04140c0424010302003030900080060450000c0155030740140d010311660760000901046e12688000138160400d02030321402c082c44c42c01001500c1e5401c08841402d4120806c1c001c105680c903045080084a03000c5007405440c094441c55000103554904003403000a039151041001005400d00c20194004174a801090170300c510402c155a08040101c00035119450448a2078207110706035120b44000e050000780d111084911001c500c58541048402c540310780100d000020354503188901300ca01c641c0d030088001d4500700c1c15990b05000f40016190340c42d802512860f0124041d10100014409180110400c5488445010540f010f861007401124012182072050100725240080c0c0d00c01565070054000c11580342420440c0d0080c0200742c01d56a1082c06c0910324000828289d12411200b4043c1c0d0f0b03220804040000c405a5801042c0c6510389d499820034001c0150a03c80d81c044c42d00184520103407040401840c1c001010f103508225503661a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 120021528 1250 120020278 120020287
    0x1713030206090f030702060711040612110607031707031b12050c090d030c0f0206030c0424051b030904020c25060905012706030506040b0108040c030f08070b090102 72
    0x140d010025142e001000d90020404041c24072101d80c0c8038001c8540082c09400080b031440708000d41da440e900c4c00e110000d081080016659004001200e6469005a540c1c4010f40c04095244c2018130403184101c1e096114000b0341c40d00c1e09204100400024400c2c410559101000000d40320344103a11103600889a0b1241d40300c1c054400f401d8200c0d10050404002c2400410000d003080e229a540b04001c4d0b601410030011007041410070744a11450514007e40c4a2030020820088040d00c00250058441c4045c0081c1160b40312145d80d00d03600388400c40180400c80c280980c00607860180e4035508401d140b00103490404c0c101c503002c94240d03008000020078036004904100c24100c0e42034481206038000d21120f1140f180b400001400c000410301a440c1000460300640c0300c00e0a420640109005401196002895032114010000c10040c0c5010f480ad078180949a039071507100e80001ca00580d000708403a903040c0e18542d91b04800030101102214004030501486c0d0102d20300841d001d2041100310005070380c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 120022778 1250 120021528 120021533
    0x1224150907020607030b0103050114120f0a0503070309060804020f04020903010b03160905070804030804120509060d050f01060c0803010918050d0809060a02072003030405060412140c06030f04031713 87
    0x542d0064440c11b1f040501d0040104848600d0b0003804541c02003d84841145d200118005400c041c07220076840c0e80c921035001d240080060000c0101702890090755030900c4207442d0303c021a6070084c1524041d5220700c00d082082070300e00e0281d00402d20100000c1c00001c00d529010003090500f5004c510044a41103030103401c014030701c40c1d8022164003108e58a070045040c58560303000703040c03044007500140c4120318594000c0c0c1c100d405041103903610600242010f441d006140c01c200c1c05010102d4003800b642030350a0001407024000e00a440104c0da0040d912402c580c20041c215004000000292461710326804910700801c03401c4c860542d00c0d20303207503440e000e46240c2490150328002d4050300309040e0350300c100310a401241c448428013190701d1440070307071038411400724000910314025904801e601520011340010040c10401c02406410302c1006038000704404000c5107903c4800c00c0300340a40003401003000a6510f03000090306a8030611038141114202d030612031a45c035401088031415554081d28800606 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 120024028 1250 120022778 120022781
    0x40b031c05071b0305030703030b03011805010207050f01020c0c1c06020f0705190c0e070e1002100f020f070222090605010914071b02041e020702122415090702060703 73
    0x219110400f540100d0345107648040d038030b108070f41c1c000e002c00d5501c5140244036642900280701c2e84907101c8064852100d00d00301b02c0d00031760107c40b081391140304221700081c0d40d130018003d41d41404a02000340614038011002e10000140280f41001c0341803540c0400c1c00080c0103840038004048500540c0358894a06242031840d00d007000075400a05045440078000242e0450001c0040e5440300900c444140c4511100750362a042c1d113141c59034000c0d010b01c040411aa40080c0c00921140002414880010910003820403440703460381c0c800301c486040003a0401741c2018813011550062002c004490243c1e0b542092048800d000800c42e500c0391203200401054800f405604802d411030380f580d0406043c0510080c06d1080906400360319160680300c14015035841d0340c8415041345d120b22640146d00c0c29180813030000c0d441010100c2c480c6070303040c080e10ba00c048000740411150400000c0040342541c5426181e0f584900280b031401d01d1800165a04001c0d1219105a030117040680c0042c40141080c80000e030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 120025278 1250 120024028 120024053
    0x100302090a060b1b1f0b03070509061f050d1104030c0501031505040b040e030304120f080403170c0c03070501060314010b0a05060703030b0a06020f0709140402040b031c0507 76
    0x10840703800c1860a002d04502801181c044400e40300100d401032020381001070400003070b04900310328400c0000804030600e506810041402c0d0046040d506010307112010403090100588045030070456041c00b02280c1c0c1c543c2842c01cae598902d0f07820094180100d14141d40183c45510220100d5042d0224040042210799451800603210908050003c030850228084502c180c3c0e01c00d0500c070700d4550015800c1c0b512603a1026900202d80c8068954929043c01c085e1964800c021075038001130b2005005529440c0f09240850285515690301034103222900c5032000845000380c2840d040304820003502c65181c3c01007005000040c418800813070307004d00c0e5007071403c07070802d21480e400e070540d04100c00f40380303d039440f0000700c41035600495886403a00150b04084004256207a00541c0202e000000424951303000941101034401c80d8044540c241d840d031840c3c0041d6001e00c2d101000301d43d02030b0081001443e168004401000b809001c032403d01e4410843d0701c0402c5c405c40320100100c1c0001170654180055240c3c1c54 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 120026528 1250 120025278 120025291
    0x403120f0b060904050c091504081e0d1107120b06030601150c0305071505090601090b061218010e030a050c01110c031c02040515120a0603240e0610030209 68
    0x208841d2003448049030309441014000d030b208030341c1c810004d1101c200c030100b40e038003485001d81550040003d90021403040e5000e03002e6050315219101154a00d485420a0050603015841c040c0040100c011000d50b102e48540c44051014051460042000c0b240203440303039049030182c644c900080c00c1450905041400607044109074509040300012099044031000d0009070740f5191540d558641402d01c48040001c4d035055100090514040c40540c07400020000e0507a031403140100305801c8880104100303407060020b000002088800040d094020302e09100c4001d0300d4400002c47d002c0c0f0718112031400c5511261003103001c22004254100704050900c52220380f455196001c2e80f80085070031156a680c0250080000400400807440c0140c400b103806546c02000050700d400f0184255182c06c03640c641100840d54020a60365000401d002e0280c001d600840c0d40001001440c00c00002c030310702074000081042c036205910307a10909101d00c810007071244610381c60400b299041303084d40304100d42e01c032024004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 120027778 1250 120026528 120026531
    0x909070303050f09060403060e030319150501080c090406060f141c0518030310170d090501140403050a050705040c1107050103020703120c0801150c0f0b1803030403120f 74
    0x10320000703070408202c8400700010903000761541c00400000c2d400303102c0d5800080141d130500c461100400c4000010314040c010f01d00040c03002100902c60742c41112040c0c17414074012162018100200d50140c260705c1c0e01701c96031445541c508641d21b13001c01e0030786007958407050008010252200100740d0040e00b100d1502e522840c0c0d146001d0000102c54491040800004a03241d55500407412188802400c0310146410000b030b41c2d240d1620020040c4101302c580301e40b07104e1494011011301002000308400c02400c4180c2c03904410700342058011200080300c1ca04150710441c04220100110b17008100484080f0f00c6000108510b908000c10b00c82900c40e80b030a10b20030300c90010411520042c0c0400c0c03580940700c1c01e10380103882e050a428101c0b40c1001e0b50800d039000d0b51400d41c3d0b0a425a0340900c900381600d00b55207802c0d071150740444045420341061000034200b4040b5030b0007800001c5103100d032140c00907404001010090030706c086281c01c640c81542d08502050520200c4c1c3d000d42c19502501255010100c0e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 120029028 1250 120027778 120027793
    0x601020609011404060507020f0703061401060e09271605040b01020a051b032b090b0405030705010c061b050a0306060804120809011506030204050a05090c1603030204030f110909 78
    0xf2942038100040d000500072038035540004d84680c420032128098692900860b44001e5503410810010079410054494903440440042001030003181c99000300a00a0801c400c2d40d6990304400801d010481890401c05107880344010b550982000713100c1030390103c9048480c040c0d240000300001c480718a40303468150340041801c80041a000315040030018a5011010050f1000340c0c002401d00903201d40c0070300000c0c00789112600005d0f1a030280c0b1281078581e00c0b008a101d8584500c4000c0303001d14801c0650551042005000300e52290440e001000c2c80b84030040f03000e4440c6c178801d51140c201c04804100280700403d03ea81c1259060007180000c1c1a0740c1048019828162104c207040c98800442d281030040d0000810080042584800717a4480701c070100518094907200c0041c065401441070510a0700e00c034002160b20314000b00c40a0090086905643c83c103141c201e40908205e1040400f50181507082c0400004510307020190030140e0b04ca42c80c01010b4545103400c00c80c803c03402400c0462075501100c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 120030278 1250 120029028 120029051
    0x4060f051c020a051c0f03030c0215010b04090b01050f030f10090603031e1101060806060a0614070f02010c0c1d0705031902090f030f100506010c050d0c060b09040b060102060901 78
    0x43c52801501c5007545c019030210b8024040003d510b051030070050101401303600404c149681a400700e011000107074280c8040c8514131f00c1e50584600300f03005070522081c2c10001007151070034541c8103114100040c14039038184440789510480c1600100c401e500c0007080301082004000e450132044015280c5d652040101c14150348006203508244400c5084069176103a0b07a02109010714198803802001ca0000c0c000c1d1502c416150fa00c4260a1305c0403401084161408140b85018a0074501c0846150189909018454580b00b101042a0b20140d06110529150101090b90aa5402d0241907401c004035682c110514035060b81030001082c403002c020080c41440011503d04101d64220020564096100e100500000d140c2c0030a00039505e516101d40c50b42484d4050b40440c1c411207110a03080100065a503480040d0f0b039030351440000070901d4120448411000740204400e001c1c0381d016413030004000d4005000300d40103880c02d59007500c40c101810200101c039070341005245ea20840c03000c0240f006200c0700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 120031528 1250 120030278 120030289
    0x120912071101030b01030b0301090606030204050c121303050c070801020307020c0105070b070e03240402270103030f03110714061b040504050a0f050c04140a031a0a090204060f051c02 80
    0x81401504154503030f002e060b8241e220381c1010346105401230081118804614202d0300030605444100e02070350401e0005000d40c0c0c080000c0d100034100c407400c0101541c1d1203981c1c01401c1042040100c003842414040104e05080410104000e480e040b4001a070300d041c4580040d20f801950001641000820088400020a007a40443d00710b0f04074201001540e001100180c18644000004448425803220262040c080e100d09540240d0003900c1e03001080c07881100082020303602c0310f42034482c1b0390f4981c01000081d201f441ca0b58480701842c5800078600106030b494149a1b4030144060f503e4407441d003040b81c41c044040c080d15801c20354000e1400340003007441d042803c5900484c4100303481695070f0400201c10201c9034210b05c04c1c612440a040000b0702d010160000e02c1e400c64001c002c2880c0e140034403489142008110070003a2508691001d000784c071039445017204100300600c04202151901c1d1a0070060b20b85001c1d040161481c8010100d0040c109420f11105101d502201900110881812005602c68 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 120032778 1250 120031528 120031553
    0x504050106050d0f0605130c08060904020303092842050a05070203060f010305120c0a020d02040e1f0c0207030f0206071b030b16110606091302040212091207 69
    0x22400c01060305100108100010306030386e07002035000841038034060b10003803455102c40341d600c11548510507135864410501001c86402c5400a400d80e00401600d03056240445902c2c0624020410000042c0d5403452442280041c640c800c1d4180e5400443c3c40364003a1000319072100313413609241c0b00480a507a10030a42c41e00845481c866062000000b0745540440c451011201869006400c03506e05080005818044c0360007440709070b40c24002d000100060360780e036000302c4501d9030402000704045207003a0200100f0246c0c0d05001c0343c1c4150303542d800d20700e000c000f400402d444854408007103450b00d000c070306000103070b9003070082140464104d0203080c00014068450741c1c2d0015016903602e03403105e2207450b005800c0700e0204002c440040c0600d0000040200400681d440790800000018641e20b1490041c4c0c0c000d40d903661048050307000600056140d04052080640c04a090107802048180c250003007000c83c1d101c0d54400340301c02640ca041005240003007003849000110200f010b45004582e850f4084c00c10178 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 120034028 1250 120032778 120032797
    0x9070503040203150601050706061403071505040311040e010507020105040201110a0816080f040308070302010c0804080d0908040b07051605121e030409060801050402011206120201030209060f1201030309050405010605 95
    0x140c4003262850740b01f203041e07400c80d80c1c0c0500100314617600c407541b00c2c61004880000038802c1c0302e100c9020854900300f94040b09041800c2e141c503802e1a0442d0340714400e4207403011403103410968450903080c02080c00d008450041209400010745800c050000605003507211308040c00d40c1d03110700642030029180008071480a0000d049503000c9040c00c4c944030780c052090350b4142c1c0358010701007404014040c0c004010815140310b600200401c2903010029580e4101c2103038040c00300382c01400628094005600000d1100e4810344989140c0358a40c50154081c1e0820041680c0b00c3d802a003914180701e2080200350302402e81151400210500c4c00080d0360f07105500d14201d0280100c3c19950b2107010020800da0b4058000082c0500c006503d40188038000c000c1160181d0003e2050000c51220b25481c0c403405e420358101c1303c00e450000e480d540040d00a9030000340600c1d04054204592120784d510b440c00f4141d407400e844a0b00740d855266007001001c05109401c0b0500c168913040c0100000b0b60000c044644210 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 120035278 1250 120034028 120034063
    0x10e03071503180203060907061d01050f0c10020a050c0f03250c051003020d0c0908070b0906040e130b01080d020601150c0f060b100903050d080c250209070503040203 73
    0x2001150281e205070b040303e8000c0d094482c46081c001c600c10045881000d90341150759800510007000f80001c2c800140c9481c081c0421010405a00c882c058000189948000d4104403400c0c0c69442c2c11002c201ea0140b40d40740e0009070b0100300003084890a01c8900c002d0900c010046042044988204000101240381480c10700300a514040c00c21071500a000c0c000c00c1c00608150146440400260196210041220015240030328201030359008166803c240e8910500502a150600e510207282c0c2c0c0c40342c1e070425400101880700284040c034244500f4460340031a841c0b02070305056450500500201038018142640042000f08002e9500166007411030f041d41043c004200d80182050361242003c54010b0014280781c00c0c203a0900c4826003040b08120801c1e80c90741c1c1c900760000401c0302c2c1c400050000803c6030704114101c81c02a407040c0c4005400c4695968003d181005050011049030302002d07024a0f442440c91203401545081d40000b54401004d0070100d20310706e010b600090b12403249a200e00d0040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 120036528 1250 120035278 120035291
    0x3040236191505090a0b130f0504030807020109050a060f0e0303150906030712080304060603120c02030c10020a0b0603070519080c010512070f181d0603010603080a050307052106010e03071503 84
    0x30750300e40007d43d4038152000b000300000da00301c039000805807038101c8055000c13540450100c1c02c06841480703003000072074111020b00f1011007241c0c2d882c0b015010140f0244a429192003504d00091010f0000b580640400740028031400244030a11251031001401d040c820b0300000c00400600034130f003181000e01984a1034456a13503032a80340400007892513400242680c2d52001d0142402c5820000b0000342c1c1b8000c9007124842c011030713004c100303001152807845401038210112030070000315400c02035600700b4001426101002e49401c0880d000014580c0079801c0c807203501e102044414800e00c03509145000c00e103811441d04031115805950b48201074120001c002c03042490700a01440307007190180ca1202c12206440740c954a83c0a80e40010722001000702146d1110081000342c98144600c104403075116401a003850b940c50400d0700e0a070002407051041c1b143c10042e810486a0002c140002ca5003e4890300c04103040003400104034864544006021740d1010809103c03c0d1350103111140210328a00d40494034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 120037778 1250 120036528 120036551
    0x11d01030312021908100e13022103070503120106030504200d0804080a02030c0409020a05090403050d05072c0a21060608060105031203040236191505090a 68
    0xa109418085110f144411504c0c0d06460307001c420b0034080da8041058142d01c0352541100201000143c1e0a12078543c0c01000c040c0040c10170780c112042407102002880702c001840194107085a108100403074807504000f465403080e81e06c840711540900010706c0c1c03c00451901e547d0703010b10001c002c0303410840c00599103000c4c41c462f501c60071074100450b0303c170340d525854903642c0c4040c0d50340c1d210300e80049111780030320300c3c0c040c0740c41c00c05119020034290000c050b92105c928180034020b4080001d0001d508028080200f4541d2030b01c1401040d0096560350b60b00304007011128283c004018070003402ca500b0b61008407031104203940d1406110103031401c9c840b14140c8040c000003d006c000d200c140c001400d0f58101000060300c6030010603990b0480300154180c45034058466902c494920088500a60040009480800801c00c1c4010f1240a03020007001a414a003115000d10101c01c08483e640b24014401c2c2620707860b0045030103a10a0140394000506029051000041c80710304010901e402041c0d83c0c0289941 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 120039028 1250 120037778 120037781
    0xb0f0705012405012a021c08070507030b06100909050604020417070f0f230d051516050a0206130507030b01030803040c05060909040b0711190209011d01030312 70
    0x344541c0555100102c000d8040052070301c500948070306800300e201c01c514400c49217610b2580c80c03410424100042400304a990801510041980c24403005030b061060740b00006005500030686c0c1030203940280740d058550703e41481500c50080823240a188000004231086401150701c80075640c4900703010409039158004200240541e070710619011040c010207205901000c681d00c070540d1804141011065121028004041954032481400158403029040710018440d001c500301c0c00e0080004144251340d0311801d10b010010b107040001c1d00d03214000d00003620946081611001c00600740306040c10101e03c8003079120071000b0809001c2d9a1140040c0c020000140300c2540659404022800340f56100c4c1000d51040d08100c0303045075090710400001c60207140c48070a6481f0f00c44000c00103d00c1e60341700da0361044005409003c40c3c041c49191200000032403000d02848802820702000306150b44402e004201c06044180d21080014110040340f442043ca154500e90540e5007500300f642406101002e40700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 120040278 1250 120039028 120039041
    0x10b09070903020f0607082d04091406010c121b021201020c010c030b060919031b080111042d0b0f07020f0a050102280b0a050406200306010e0301060906090c080f010b0f070501 77
    0x184408c000070082080280c592001c11b84801150403000c41c0d948200040d540c104195901804030403800c180349810602c00d008120101643c0e0000c1150761380c80d60701046806010114820072650042842110a24244980c5000c62054903044c004c024940c00801c0c282e102e584210350245000c114143e00040038242000700030344c0e00501d6482c00c0154040c101b044100c9500070500f8950030301c0180300c0024083c0c400c0d50705403018031100c901038001189144084a45404110042e60140000011901d80c44c0700607000c2c00314041500c03507503840280304109130750002e221540e00ca03440307840301800282d90004012423080d8480a1401142e025050300d0b0344500411080246402a44e50810030100c50580040d80542e00c100c00034450307040480d046031039031002103061510341c0c0750900c0025200d40c491300c080c206410010b000091041d8407900305000340d900581001281c580c960741000406a400010700d81c3c170001200000c40203504000301c4814030301c00c5010b098006c50001c101042404803c0d030062 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 120041528 1250 120040278 120040357
    0xb0a05041503050402120d050a2114090c0a0305030406050307050d06030303380609040b030a110f0a0b0708090604080604120f09060206061002010b09070903020f060708 74
    0x40000d46440c03070003005030004035401c0340501210034207144d921100058401c03a01c0404d440ea00c3c00c101c4a81011140100b040c007070100690303400b003d140000801d81c07203038290310080c101048059140004a01d868429804120340c05810380003030070408650040b0568042d180d980c94680d5594440c074004484074081c408a00f07218070b250010000405030150f014104000c4200030b94200f441403850480c4030001c0302019000020905111a906131500e04000c0250002c001c00c0058112481d1002c20b1410f05032150131240b80040035800c5d0300c1e500c0c10b8041540766980845030707044423f0521000007030b10702428070000c1c082c900100f0720503019640e20023910003601c04001110020f252904004014030a190500340100d000b00350488520351207070300082d0075102103070001d1400d0744a5406001c48604402c0c420801c65503111180156a03480181c0280a04420b80d260715880d070a50040050000584420910400041000c100025859030036a440f100c2211502000040c2502d101c215170790000812 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 120042778 1250 120041528 120041549
    0x606080d0c02360103060c03020304020f01080601020304090903090503300d0b0d0312140105011704051011030405010b1f030209030a020907020102071406010f1205100203040807050d0c03090b0a0504 87
    0x10112104280c3c6014100e80c0207500c1802001d00081c1c0581c201e02c030035178000e900448680050504e950085000310780010b4188126460207540da00e1980440c1e039070b150228000303954000104050b1404000e0785480c2d5000504040f000000006910415100071100900040307010031032407200700d220b60220041485c00f0b0a010441c511134a00105081135020791030000f9454070401000341c02c8000c44c010706a8006071150410072450f51400d0300413a500030000c652621a20851119811490141b0036904555008c030607100c1c01c2070302d007103401c1d5030101c2d00060245a8121240707941064078200b1400b85090742c100103a540b90740742d0200c0d040880c00d610113504104850180700c24503905500611340d00d030040c3c90402c0b1045062480c243c075408288290941200d5084042c00818029802103400d148100c007180c1080310013170f03041d40c183e8001300c40a480c0300304040750100505c04240045d4404950b00d20306030100e020103503806403100300103018080c076044010902000b01030140e000c40d4064500002c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 120044028 1250 120042778 120042859
    0x50a1e09110409051819020402090414180607050319020c010606080a0609020f0711030a0605090705040507030219030e0c0a170d09120b1b03130606080d0c02 69
    0x8030501c1c1c1d6030140c40b07181049883d0200080b0702d440c0282415a241c00c4503005002049114030f54112a000c000350142ea1103a402c000d954542d54aa102d0300032840c41c03443c0c0000c01d034680085100b002601c00c051183c02c94006d41c04020308075912900322988443e614011110009804154500030b02504030303115604d610b84000030a03001c0e00050340c81e10400700420140081902d4102c03a0060b0300070603690110341c410030300100c0c3c0051400306100f802c000000c1e00711900c8070200d81710581618426144158640c200c44400c0c00759080ca4000c15030f0044144c10103500d0b0650300a80b5801c076070012103000082607070780c100305c015420091040ba505d40303900070300e103c40841e12040b013407200b4416000509043c2c82002226100140600c5814044904400c00502014041c0e01d40441080000f000c48030303e54949080741d0074103059040514010300c1410815109000070f03180030720840b40c00d600610501c0d8044900110090350002d070400c00d50742d055545a610001a05d070115204072611810080c0000b6502c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 120045278 1250 120044028 120044051
    0x7290a06050907020106050609060f0c0d030b03190b1b0f040605031006030605180606070f05030c0105010807150c060e03070f0c0506090d02101e03020409060b04050a1e09 75
    0x10000c0d81581c4040300c501519884450080c2d08032580c9110792074024905006521907071510901a1103203c2d455042036150003c04203015051031981300e0003c002c00d540396020001810f00708650003080c0000560039525482a4940d040079220040004901416a40034194400070590aa0b00b82c09040d465041c2c0b26500c0d000060301580003180c0144001c000000005803483c440e002e4501140e001a1000b80c01625001c045d44600c0b40c01000e15422040402140c00014002049802c81a00070400703162102c0140c240a0b09480060380401000c2d40b00d50024007003480e812008690840071400d018150b150309142040180c104228010030601011400c00244246004c1c80d9040c184a0240c12060360385030b0003003010070300414010b1508403007890a0000141041c03030103428291203d01b0f02c081011000c40740c1100086c40150317102c0001c1c1d00414108010240d5006071400760901c039490b01d0501d07040c040030403007140080c803d0b40307540c0325200080014080c0c1031500a0240c4003011040c4107096806 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 120046528 1250 120045278 120045281
    0xa11042c0108240f0c0c0f030720030a0312020c010b0901120c0f080a060b030a02090c040810050417070c0f15090602010c0215070909050a0608010e0f0307290a 70
    0x59440743d07810301650200c0c0c081c514540b4250702c1200c50030751102094846162510044e0000161600c03c2e00ca8108041c0d8080e000b04003600310ba41c414110034078544c58100303403141010b80414501e17001c1c1c4c1c030100703107480080d4000a801090401c41d00c001078a513807040e01c2c62070140503030b4290f10b0340040049001007000e051580c10309401c81d005602d1401c8043e528103109040d03845074424445e207908046000c034006500368101040158000b412240c00292f56000207110500c2622400ea41000000f070800ca40c44c030601004201510380c540411803454240c444551540c0e8103090140921000102e0304100f119541c0070300060a42d43e8954980700e6142d00d2504c5c03050800414403000b02d502540c000031024814000c0a103411015800341c00e2713900c2608005079070b00101078142c1046c810034882c041800b840b1845142c0c480c0044010129115181a0980307003100c844407908591500f0004038910340d41f070b002045a500607030061000203c000c0300e01140c40303c24044404041580041d800f80074600788070307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 120047778 1250 120046528 120046543
    0x906090705130906060f0206251215050f030d05092803241806090302030d0c260c070f02030102040b0f0a030e06010503070605090a0b07030f03050a11042c0108 70
    0x1740d89034011700358450402030703030b60720300407502c000a5901c1340c11503411207540750003600070303444540c1003d520020403101d0507400e0312901c0903a1901c00c0c04a07a410491450309a1150403180c4050380a48100504030310001c0c0144580400380c1e004041c091050508401a000003003140c45411000740105512490840054070400c1c00350008800b440c80d011510170700e00d10400701e041c10541e002e81b4419103076555500c0a0300c80c005040d02035000038480c407241d00c2c07410300030310b0080c03111a074414442135000d030b1940440c000e4160300d00042640c0b541c20000483c1461013161449038210507003a45150061000901a100b6900a4400d440307011881598521030400505051038003030301c051240390409008680d03550001d20410350305900c0398008101440c040c0740181802c50b805040314031095240e03c1d0a141d1588400d81c201d00041e0a034504018840c1d040c441d1b19044800e460741030104041c00ca00c81f540c5801540a8980302c1442003944021150403d81b40c0a0820450704d5507003225a501c0e513215413100030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 120049028 1250 120047778 120047789
    0x810050c040e0a090203010f05151e010807050c0f030403060b030d02010b01020c04090302010b1903170307021002031314011509020c1914030c1006080a020906090705130906 76
    0x90001080d2800d0055098906540d08014900c401d55114030085014003000b01080e60555030341d000c03110040c0818002e85204240f8601c040c0003000c0868107003e02150a00900f611482151059641c0e60fa40042955040584c0d032420944035014641143d060850070441255540320002c3c0000412100d03800ca02c1c0b02e400c0031016104081c0b002c0c0c1c000d1f42a0f0baa810301c00f80c01600b0444808500b0303d0a035121004080c0644000a808403001012138090015803040191005600204204020340fa582400408222840d2a030850034400b502a54505280328105d10854012000880d080d120080c030010140c0c20040000581c031184d11414020003100b16281031000d440580442c3c001454000c540c4003050540040082030104a1800506850540c00f29061241c0940e09103890000b00302501040e44000003a28190310190883d80488034103500191598002445060150b51000011a0301c404162420704103640c031024110b0340b40c0716001200c0882c240703800d400314600c140d6611100a0b9107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 120050278 1250 120049028 120049031
    0x6020c01030e01050603070315020c0a0b090706142b05070f0207050a0b040b0901020f100b040501060807080f0c0d0f060306140f04060b04090218040b0703060f0b03040503040801060810 81
    0x30500b6003500c1c01d0b12002c480342c81d0540c1c0a07044c2000044d0f60f100858507000761b410001030a14256800300c5080c0310309a5000d49a0071040402e00900c0101442050001c0045040401c60000104d800e07840600134801300e20011410400101d545070141015000a200c20b1001040369151040001d4000d0032034105200052050000c04103490603c80d6200701501d00c03a40e442403c04d4034000c0c840100340d0040700010304500034030301030b05e00c0d058003040a1016909400b0000c210b0300c04103428007084600590080080222080520064582180c01147c2084910001c9c00741690740204a00c607034851071400c480038901e41507001d03110318815440101070307a20601c01880311807640d900310010b81a0070342d00b0040b14541c1402140000f100c95000f039203007020150020907407108540014945c14910784111044107000c0d0100030411441040d4280c0c030500c0d82c18104080c1c1c2c2400c0c026442c0b86450700410310281400008941844010000c0da0b00034440c8000a12101c0c1d110f0391103a80300c0070014904220302d0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 120051528 1250 120050278 120050291
    0xd060905070c0614010b1c060509070903050d14090112110301060c030207050d0201020c0108040501060e04080a030e01050f180a020306090106081c02030d0b04090b0403050c0c0f0306010b0a050f0406020c0103 91
    0x1480011150f6040f129000031031410511138221001c08402c87d0703042c5030f011039a1502c00040d44d880741c0b004644500740d0768803007030107041c51802c005040500200c003460400c10754107d0f01e080d203218001500c0e40400207103001e0001c0c40031807846900800aa4404903010032020000054443d40400c000115621940c00d840d41c0a80ea07905002e03050a07005030085c0944c01581c2c01e03440301d500c544c241e103034083e02070400410040d945140010001300282c4080da03140030000b429083c000d4260141a440c0c00e0918020041c0e8a00481c081003d2907018129000c0b650003401d00c4003502d8400c000e088103450700281611801d0500001e4030340248024490300c0074500038658085415000407504c200400e41903005586002e49200355000208240002c55a03c9540d90000b000400c2c00110381e44e200d40e10175141d040c0c0c2d43e404206440d28107804411f01d02d1251184400c2c0200d55280403856904642003c85066143d41243c9810b0321036000e000c0048070354080c00704001a00f582e00298280314480280c0701003192 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 120052778 1250 120051528 120051551
    0x13050109060e0712080f071a040309030b09030319050a0f0e010507090b040803030103060203070c140f0601090b0a0302090702010b0613050f04060303020c010c02150f040e01290d060905070c06 84
    0x18110300c4806084417806001c01d101c0004844001c1c180c1c44e00c901400748202e8010003c1e188284416030b001c1c0c00062081d0010700c20001a0030002c0c0d0440c184500940c25454054005c1082c0d03014030315450300d5107845001060120010b50401c990b011001d110174008000055040c40c006c2608644c103d000485404001485c03900d9941202e090360a04000f540ca168256152640a540058501b20801100c07a03281c81c007042400400c0c0048031040c0014003008014100d43c50310b01070301a048043e4643c5000b01c842030542c0c500090030100c0764103a60b14009641e13000000e03030040c85c0c3c002042c0d03000000020b0359040440480c0007002500c0301120030003890304111040c0002c8446601004002d80e106000e901c041c5d6014506c6d810040784014600c040c1c40b040c2c500070114a801c521403104480d2800b00302031108680c002007050140410400e030b48615680000420300000c0803903000c600f0f00200003a14035103c000c07904880301820b0040720500190400c840001c003459402d080a4640601d000104541c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 120054028 1250 120052778 120052799
    0xb0604030b0403030b0f0d030c0311010506030307030c050304051804050d0e0a0918060c050406081503250f0314010b030703111203070b07020d0909060605030a0513050109060e07 78
    0x29241c000c1e03451541e5545a41d0180d004200fa140035079400320b003644441d442d6944500d0001c9a252007561640240c0c1741b185405401200d0064910043d40d0401d41088004d843c00429251000d4262510700d15443c0203041180c03d61003250080d0760405000c1160345e40c7d28141e0003c1500841c41242151f039000d51700c3c00120f13180320303005000c9030340031201c1d1074104114035081c1c00411440c50f10510340001000389079600011658406e62843c00308901080030444950000d00581d84183c5440110900c0c045d00d00010743c5a026040384485011440345c0c41d00c0c1e01c0040910f002c0042c0c02440a00040360f5124109074002c0c03048501a100e4543c2050728080c210304001c2405030840c0da100c852401342507951010132a0340b202e00e0200c00e0440c4001d001c204041903085030014010483ea401030116080801c0c4020002241d07a00002806800c1c0700080000d140e01400301d80e809a01c0e00000144d0b500c40b452960b11004080d04060300640c20105905d007480741c4e030703400010b20000170403c40302d80584c0c0b207204e400d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 120055278 1250 120054028 120054037
    0x8090102030609160219050607140702030a0b270105061005120606031b0711011b0b0a0b011403040c0906050a03080d0b010201060302030d0810060914010c050f010f02070203010b06 79
    0x941008850300460344c10a5080850202c60b00c81e4019600041c102801a000c0380540140179103d65012906215a254021b0310a900c0800119400e900e032150076000700fa62590718000044c100182c0b0341c0000c403445414504080042242c840070b40d255405a205a401703000192000e91081e1051041d048216026000b107540c00003509a80700e80640e84e1804000407504000d08181410341506a2420800b811500800819118a1552030b220429000040c007803490030014449001614040e03001294405403003507409404010081158540740340101e840d4071030210711064080303000c401c1c081000942c1c03121000390f4407480f20800140e076a0340b0030460091910320001d4980d0340204030b0121500415002018909010300000c00d009599a020a2a0504010307010002400c01030038000160341a4031510000c0019190004105081820002c140c101420324141030118040340d56040000600c00a0456142c040c001c00c040105a41e50b10080e510009080f84030b946081d032508414a090030948 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 120056528 1250 120055278 120055291
    0xf0312030c0a031109100c110d0609060501080102131e0510021f02090a0302090a02040e07021e0c0906100c0602030a0905070509070203030c0705100207080910090302030c100e06070606060809010203 87
    0x302000c0c00404015141c4414020b01560040d03400144448d081e100c01d0148034816105400c000381d0381030b890902d58203c2d5010b0f08281480c2c7d00401244c5101102a040c00059501100146444000c4048202e50003041c0390300881d0450803610714406030355008203400c1d42d07540000101c03002d00e078500c02c4448100c1c1302c0d952030241d01000d680d50038405803c00001d4558400a04c040c010724043c0c1b11915041102c80451b401c100503401030140200554000c6980130003c2545402040380c9002e0a00044484000070071031401004446170780e4030403600c901c81c20444140c000f8000c41d81ea04042c50314801601060505407a24410944009201e040092803d441404154051815912054094881544041c0302030395140f2030010841c0c4123025a100900d5028817400340c00743c1d2175000d00180950f0a500b4501e240612000303403c20805610701007052507004400311405209000c902006840fa0f200c0b000042e0740055003c50384a013002615071111080e6035040d121050746990700c2ca8480c2c240d1204503050b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 120057778 1250 120056528 120056539
    0xa0e0115031107050c0126060103020a0507020d03030c0f052109120c010605040b180c0a0c0c03110a0b0a05041a0408010903080609010b0c0c0f0312030c0a031109 71
    0x411800384000a16a00e008140ca00400c070b420340d20511042a80000d08140d440c2d4020140c007000700c2d81c02c54088651055222058800300783c21844181c03a800c4020109414160002401603200784204115401254020140c1a020f0348902b07008000344009201440450105c64018a900d409282561510b55a50341980189815003400030303966000a02514a01d01c641d0944140140780c9501034094244da11000185a900d03110400044c0d90013601c030180995080d0114124202c9240345150744070041211855682000078400c8a45201d0150094841000d03080040200031a05002c910404811588030038982e40b54061040305104a034a060f000c0362082008110300034181040c5495001d40321101c50405544041c3c00e42900c5a5080c00c8000408a01c00c0210501e0000b5070f55004d44040303000c160800d026101c80655440c0e00f0b0322001e101340404400c1220075542002141100749004050b20780f00d04018503d0701982d003001e401703400443d04204852480b006030100b03a90074501c00514 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 120059028 1250 120057778 120057781
    0x507030521040314030f070b190204060203030402010f09120501090210030b1c1b0b1905030601230f07080a02010605030a0201121d070b04030b0604060f23040c0504140a0e 75
    0x4071400c2510a0340101c0100340010711446d00d180260801a003074407400341c07042c2502c41ca04480c3d0100c840000302103030074450344103010911203c1d40c0001920b50159080c00d0000007141c06000540d000402031b40718850713035280c3e00055401c000d0190085094503200350b50782007074121212805e400741c48000b12251781000f900502040010818142c0f006010b0084600c4d107140e003140101c0c1c5140d6500c0390003803012001300051240360a26501d036040d494142601d031040c158181000024400d14220066680c00c20745482401c980b80c21000441d0003200340007120f0b5545144a141150300740d0402183c007400340d460203000107003e0601054101455030b0580d03500c0d21422803184210010b14000307209802e00550304c0c2c0301040d400406c00c20340e03020340710300014a0b0720782d8a0b42ca0b060303221210082046016604004080058983c0d40e00300500361416803c602c03000070740b10980d50784840044400d2690040c205941d0b4070916030040010b10070386981081040d0013000c0c0b08140445407a00348a20407061a00b01c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 120060278 1250 120059028 120059033
    0x10f02041a0304121b0203030406030c080a06030b0a091110020a0c080105010605030a05070e1009080d09120321060e04060e010c0c060209190e160807140307030b04050405070305210403 81
    0x4154107240307003081015007000064000c08d1851304203400c41001b2030b035590070000406400440b12a4015801502880340e1805c607a0b9003180440040c3c9800c0140b13403120028010445104d00c070030248200584030b19680f40341500000c0d40c4606600c1c081d94041819140030504040c1801881c0c10388807692100f0745980c4503550080e00a1400419841c10004416000c1020f0390b244901c10011001c0703581d545c0070b000d007081c1301c2e181040000b00301d20060094230b100170000c031046000480e800340d402d030502403940d400c405424112060300c2c4582100d06441c1901c081a0200700103001c60160340144010011003100d1521182281c0440300d400000c681e1040d59000041d2443c2c00419122038040c000a0781804640a150340c003000310703040344200c03000842c204501400800c0340a84016820325012016041686014169244089001381c205a0000000303e08074040d8104c118003030000760041001d4a030505105813107020038002214980a503200c0c03101130501c00360b5080280c0c1c8070070380418030303080c5950f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 120061528 1250 120060278 120060287
    0x605012c0417040e0a09120309030c020f0111060a05100b07020303030a0902040209030a030507050606010e090c03100f060f09060201110912070803071511040f1401030b03010f02041a030412 83
    0x2d490b0050500002c01010039404a1035108501841c0f00c6000450440c10b2464508520401c40c0402000c06140c00f80e444d020030307407000404600d640c054400070100d02011004803403010720243c0b000c00c68800c0f0344c00e01c00013101301ea216a100303070400d02885030800c0d2100e8041c10644100b13079019506620510219542804603409004024070041c401882d10725860b02003420909419030580105801142c424117016041c452142d0045092800050709402c0700c00081c06410042c5c1030140c20b140c0440055044002642c610001e040b0031302413216581d41d1000024800d42000d605100029490318000400c54014000c1c00560f5408010b6103081a40040038851391104400a0803483d201d5800e00240e1504144024100240a05003100c000349010a150040d1000740103140c0f44900304100800041707920030511016603106e800e030001c0501320180120060b040505856a1551801c004004800d4240e401001181c000a007940c0b6a105031040c6803c0c0c0c1d0004840c00380440c6590400000242d109 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 120062778 1250 120061528 120061553
    0x1d010e0105010f0e040f02071a0606160302030c1204180b0307050d030c2009010e090a020409030315060914030c060a05030705070f150b030d020c150f03040605012c04 73
    0xc03490420784a0b8503450000381031b40d0032640d211400d80d60008420061154011400340602c03440d6400151508040000c2203c0d4403420ae42c100e0103200041080c0d00305807083c4210707020f181031001180d0300b4039029881d90840d503119100d1105202d82400c45481c0e1f01ca80c0c1e02540c170a1020007405400303502d152105104e071100d05030300b04030704110032030014a0004900e001c0c4000040c2c2120500e80074881703600c00784640c1041c1a005124010354010800c04008400180035101583c1683c010510341217a150540c060080c00415901c0701c3c060b141c000c07036084d5010031a00100c2e5410760305200b444506905041c3c85100349030a082e0441410401004918020f000440d000300c41d91800600c2c041c0d454507130340280250400304403660881440700018040f09030042006a10048014018941002501940d154003008116004101858241e0b0350051a18150b41041d0120030400795607290a10308240104024010729620500300354500d20b4407445620510901880c0e040003400a0f01d9503250060007a15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 120064028 1250 120062778 120062807
    0x30a0c03122304080d020a0b0606070218070215010f0f0b0703050c0f01020702090a0204060c242a020c01050a0e041b050a080601140901080a090c06091d010e010501 72
    0x8030101107001c0302c058120007004000e0804040d2201e080c13000da50300740003480302c00c0c804650110168101081d000080300303410080c102ca20541d1003041d0b1004c107840b40700364600300f000110494104200c10750081501c0a856818100d5900160303259100e0f00548a0039002d0319580014013101800303103a031007200a05000c1d001f400e0550610396066203840c40c003009006802801d94000c0344207011800c29220352a0000038602c401d60030242400030040652201800c0508444080d5000d840440c40903914450800c806074400d00001d5090a4000c000ca0b0401c11111414070255280d82040d03807001c00d01021010301652a0303460500740c3c1d5801c94480415980b031503031090361005100341064080c0d0703039a2520100c98031115202c0400a1018000a400504050501c03074101203d1418444040489074843c2007401c008400d034452001100007011580c4005041e140c840a0200704d03107070000107810846000c5a0a110900300c1d0803104208180203200c1c0307801e0001d00307130014062980544500c81c40c002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 120065278 1250 120064028 120064037
    0x11401031a09270309010813021201051f050a050607020d030e1801030506060409080409091106040906050306010801141302030a150f110903070308030c040b04090c030b030a0c0312 79
    0xd2240000314011416210094244a52003c5410800c018550601241c0006000c0d5007046003000000e070507038000400842c002c84a08480300c0455403580900105040180000c21281c600880300004804c480300c0c130008074640c401000611450041d8007a400e55101400d82418000c8035401c4c040000600c0b0021000d106125101c8091921520000901c1100340c040001c0c65514505000b030a104000d803a0718041c0e804c080703d00d07010a480c601140c04845a0320000902c1c40c0c0c3d1070904900c100d600340320a5901c12400140056106820340000081da9012401c1c0e0b526640c3e00e188260803940f405240c8400c407c5000c000646202041c1c80702d40300d05001409841444940d0754030702540041c41146031010b25650301d40480b40c8201031103580c0b07a000300c1d119024a04030750000001c1d42c0d204d40b44001401010000001609607000d40c007a64000c0c41820000307901d440c1c413998440d001e004403258600c002441c1002164541c900014806c94454202d01100c100a041d81c4403034041070b542c40203074020300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 120066528 1250 120065278 120065321
    0x90e0a060e0c100c0f080c03090303040801060509070f0909021602030307060c02190302060f06030708121e030402220b1003060f0b0c030f0706060306090321020301140103 75
    0x20450300412600c55080800350690b0325042d0b04004010807090300f00340030054813100181c0050242000c0b0301c0e01542040c030403504c0b0301480454900c0c5100e11502541c00d070102080009030144150010310903250203c2d4088241d1352050b0040305c5a140004140300041c003214401c1140c400e0642c010b10345111440039442d25405a034001c01d1075a0f114010480d40d060740c440c07441074510b6041c0084210303440c1650300340d104450b0b1501c000795201e4015080c0c2c05130800300c0c4003044482d5000c104040042031203d060710714400304004000b500340c1000719500030311840c541c03c0040d6000600d0483e4810b940c010701000309003a1030a00c21140e90704e940250100180e4480c80440c066031074401c901c060f4003480e9004140ca50401040c1a5030f074005511a042428045c40700d01d01c6942d0210a54074000d0b4840c0b0460f403218003130308042c0040c020550003c1e02c2146420030b01ca0a05a0220507204583c03034541110100700300c002442003c0707110074412404001c00d425106440307507110f60003c043c80202c01e40f5904c0312 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 120067778 1250 120066528 120066533
    0xd1803020402040e06030f0304080a1515080601080f061e060409020405090d0224070810050411030a150e07030b0109030c060915020105010609030206030603100e0f160f090e0a 77
    0x490f4050f400c201d000d0800c4804022607407504010400a0082100141d0f08203854101c2c91580e91400b20001002d8031780c0c00000415450441e03000407022040350501c6068103945038004c42d10b84101707024080e601d0207100103041c0801c800042c0607024089881c10320b801350202088180313801d200030700503a6000303807680f80701c02c09640e55000e424014004071010340f40f200c00441d0007a1802d070721442c030076280c00505180e04540d10305400946a021840b4180305115a03560352001004008175040b071a070080c0303004100c010000441c000703188a084054401c000328200340c03104030111495817180000c0c000b101030006003620700c00d4210841424041c100b03a07041980340d039900c40b00c8540301d4118a00150070050200410400c0c982410107041c4180000c01c10780d41091401416110b440c007000e801500700001181043c6c9041100410340000102d082010720154100c4545400f16981c550095104081d403240710390070b0000c0150f049910211013411464501040c440181c400445064600d00520044be0003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 120069028 1250 120067778 120067781
    0x305040923161d0906060c0a08070b1005091b0c01020403020a0b0c010506011b230a1214040f090c050c030705070303120203010b070b090c031504060c030e0d18030204 73
    0x2c1d40c4840601c2222404640004001181e10038501804502e854062a2261680081c05030007400a80d14107540380040a2013a10703120b50303610001c01044000036844103214541a8142c010031031061020b400d90766410405c44c507428281c45c3c034900e0510300980400c402c0555070041c00e00084042c00503080658940000c0c00c1040d1742e0388081d00c001f800207403161001c4020320071540d11185c00d0a1002907501001c00119851240860040200020030003046800b0f11719003501341c403036000004581c0c031000c041c544481007041d9030008101088031103258020450341001601e090f107440d40480c2d00c1251400000601a00e1450942000e0100400c00c20740494010b1009117102405800200001c0c1c0c91490000c4c41480107010a40d01d082c4184014424148d000d02160141038100c544e001041d10b40103019828015035040a9a06108a06440400314100380880d84964000d50082110030a102e070207030160f0b10310b5802d281040e0004101d5101d628010446120300106182d80c2e405003d842c0d501140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 120070278 1250 120069028 120069031
    0x1503011d03031807030f0b07020a06060b090a0503010e0a2307030b0108100b0a090f0b040608011e020a020d050313150b13060602031c1116020a080a0305040923 70
    0x500c540000042041d042003020716104601e107030b0030003400c040e4038585540c46c24500484009003e41c4140303010998051080003e0104140c01070810056956a1a803640540c0e004016803801503090380000940c500d4107100d00114805004040d02940c0362907910041080c1058000f01c400041008000100000400184026520410a40d00e09504011100e40341c41c4100040350b4585003031050380c0d016070726001c19072070031102e001d00d02044200c812003201c00907005980c06290000d00d4441c0c0044c041405412050142c86034401ca9030791000d400080ca0140d100e201451005039002c2045190100e1107000110791025504c4401d000c00402c0f176a6481d140ca00391120480b8160b111010105146404140b21200c900c02e030200700003d85c500000031f504c80c0224683d1000f01000038000c02042216500402d07000d610401074140d66100b00440c5c0008070394220420381c0903203420500483c4e4008001988c4c072009816880315401d1502c1c04024102038440c0b40e0001854020020f81140305110140805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 120071528 1250 120070278 120070331
    0xa020705090108060405070b0a0203091905010e010503010f03020105070311010e06070905030a0c05130902060c070f05090c0715090204090302060105010f140403020d0201022d100207020108150301 86
    0x180901480c05041021421040c0c00c00f10a540041d410710000500002c0e0f24012550895449030701c034411031400364154040c44660942040301400501c130640e00544a00042d10000d803103040b40d9a5086004468501090203516007500458409101560282003d00b001d03074400d2801092802081c4000e82c20360303c803800141070540c061014002c0c00d582103034124001d0305040d0020155a50a51912010102c1e42d214590044401d080307100031040d45900f01c0c0010395009050759981d1a1301111195940c0c8661007144505505050003040c030303160070340c8901e01441014082038100515601c0d154810541444142030040d03850304170000589850050b580e21600039009440c3c1585000d001600d4135514541601c200b022814034088500b00e08401d0302c0950350192241d401202040c40141d00e051450540d00701d0443c15124401d138074240010394911107500768000c5e52260715a5090305810f90080c035078021302082c0e00c080080e5a6408016084c070903410000d001281104070700c00c81460174003000e64003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 120072778 1250 120071528 120071533
    0x12010302010f1d0103051b0703120e3012010e070e040203071407050f06090d0e0301150306050603010b0907030b030606090c0a12060b0301060e01020c0321070311030a02 74
    0x4006640c0c1003091251000580c3c14810781d042c1005046640c0d0005403048681896a100c1c0803e00000048981c140d50220500101e0750780c030140d04003e0000710745c41981100c990300f080d840001205001c0740c413008070a8000b014500c001e0503108103003c4912102444845480c00740401440340e08442102402030010159903051820b040700d00810070610318100602a900400c244681141e00c0300110040d146070190302510f5100341e2500ea4102130441801404510404007400303c01d85020801030290f03034194580110b1074120506250070784204200200207180602801c00c0420607030780007246e10400040001920820450000d649036109a59050019546884519640c2804c20060b81c00c0042103034160001e01d0000d40214131482483c407800e08100303054803400c03010217454000001911102180a03229a181c100080c43c0c420034406060052040ca030311241582008903801641e240610500d100c0200600542500c9906c6020200c04020711b00b2402100040144060315101a00303501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 120074028 1250 120072778 120072781
    0xf0308060319170c0a021f300b01030e010516110a080307030902060408060c070b0f06010816120914160b03070804030306080d0f08010605040b07080904060b12 70
    0x600d4901010111650700700140403181c00003146189598210704a145240290713608658141c450400c2c02480c1d0094000d100f0301c411498071000c2001001980c151961406180c900d41e030721b003000c00c1c41c00b840280e00c1e11031442181c0001c400141c1107420500c02c18100407132003414403a00700e8211541200c40406000c44c000c0018903090340410400344c101d20410040015443d03940307510401d41700c06000c0038141aa0f4080341d070119291241564000c002c04801e4039094a4100340f103051662041c10102c1c4c0d0003100d01c0c002188641d080e2412401038406941e410582d941d0280504494844030554409000d06022a00701030035140c00f031110120302c1006130b82c0c002d602100100d803030b044020f9003800c01c1036130000b414403139014042d00362507001055140c01d1585407594107080d0000d00c2160424507490240c004c00c41c8415800c80703072005540410344d45048442e03076180411525409240589828444200507503c0031460542c090442c01e08010400591140d4070904055540d100305c824100300c4602c1c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 120075278 1250 120074028 120074041
    0x30c0509060c100b01090506030a09060e07080f063405040b0406030f0e030c0a0807060605040509010207020a14030705090406180c0801060b0702010e04050403020a12090905010506130b030c070f0308 87
    0x2d100c00c084c1d403c0c2014010a8203140c00910700c1c0c0001041e8030340055580ca10781040c046142c215000907143c1038169030a50352100d0005448030a1220900c126118a801048541c4405c0c0410704405100c003000e06000100750000d2108420b09407074107010400c060101042076801200148001c06154a00003440100a00c0c04025142c00074501d401c02d41040c404104841c02c082111100e00340e000d10b40c144d46008901d059001041243c00064000f8a06030400c050040158002e208040c000c82d04421403d50740e95480703408a640000c1c10b909500a80010415803c041c041d642d0000d100e0800402c0301c000558203058081da4258043d601600d0440040020150a00c42c00e800b402000074000e00e0062150006891210b03680c0042d0300550b564000a020f00d4820b111060710654000781d4000034800c0b0300b00040c401c40150040216403803801e400000d16181ca54201d4000c00e04013108120b9940c43c0c20107522072030300000c001c4001e400d010045030000444e60101d103200d162003602c88510504160 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 120076528 1250 120075278 120075281
    0x901090c1d1008030421120c031b03020d1103070b0408130f0b0913020c06010b0913050108102f0703030f0e07030b060604030204020d0902090601180501030c0509060c10 74
    0x41d00c034aa0600b07802805210107207000c01183c0946110302c68a502d50900c0c20382c444070060400c6d0010f00f01c0e8202c1c08862840035481504955554025030b101c1c590785200070841680071820030300080159000c00e0702d000809008419071030a0410740c1013940c0c00e04803203440700901410212802c4400031400102205500b041c1c2c0f550201420503640e00320300060800110111510600301d41d244150344c1d2002c42c004400f81c80c1c04482d03d000d6080155811540d480c102d01d8129000780c211a40715040101c114010182e5901c9840e0484034440000c120f2401014131010003860001110b04610842c242014a03100c0034405000008983c1d5a40e0340e5204004c2c1802002c4a00728410140160b081404071248042c002071484c05907078002d0702c840c0b001c0e241d20001446610450f0b1000b03410a0000c070310b100e010611980700d61032803802035034641c03c19a40c003c01103075a90168002e0101240030040c0c148030702e500c40c3d4418184c6185c2420b00500d030100840002d18280c011401804c8641e000307e0301000c400031075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 120077778 1250 120076528 120076531
    0x30e0a03080c0a1a072f01150501031b020601090203041703090c010914010e090a020d2306041112060a090e011a190b0c19030503070906050301050d02090901090c1d 72
    0x28404141400c5c60315000b0700700204007441c801c6241400101c10485019038450740701d038410480013084443e290702008159080d45119941c0801e1804284c00a0fa0325110621800c140160303020b4005682400e812400a40018009a481d06642d0501c40980385040b002580100c01e030343c0080c00c60340381c440d00040005086070003200e17039181c92080d9018680d810100c8038502100c1280c40c201181c0c1c0d00d400640003802801e28006240c0d0501401184215400c0c2c0025402e401c1c840480700c080d903884080c401035419203041e078107100c001045290f9135440841c440742d8100c20010200803a0641d210811410748506990034142e99640c1d1030301080d00c90700d03c00111601c01c400e80d400581c0b81c0d80328007441030461051207007061400c000101c3c4500b4100600c040d00c040c3c404c1c0005407000c2102e5081c0240180c000300d8200c030100b40d26590104829000f502602c0c106c0310b00402502c071041070707170f03003440301c0b030308000d00035102941d22103651100013080074042d540074003822000c107000d02018907480e180700c010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 120079028 1250 120077778 120077813
    0x140d0804050621060f06040504020307021005010b0702030f07060203070f0f050618060a050906060103020903010e12030106080a0603020a1403010f091101260a09020d12050406110c010903030e0a03080c0a 89
    0x71754a100310034640394202910111801118010f840b5954400d040e030034040300b040569056031030b040000c15120381d05400780032050300036000c0b6109994810410b550302c40752401150302503481071094100088a0502c5000c4052081c03244d500c01a08039503440346003907800c0e64111034422030003d02c1d45034102c0030495154499074118080c0118200303080380781e0302c60340064691810036800150030161901d0035007200c1c5a8002880407903610941d92803156225800c01c4c084e180000e801030002c1101000180244420b0301d4000317101c100020710304000c4130b1020704042860303500f55494011008040495116041106000f042e000c0030210459000415403000f041c1401c0e403000b00c95000c00380300410440c2440c0c0c007281d00400000e04080074000110758840501c0010310003454803a040b641503034481c01070400c840c1e50341c42e00c54800c86600440e903110b0802412560000746941c2c41000460b1203107007080075118000e04844101c0d6201d440d2041654001001d40701c0d982d00c110038800800441000a004511 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 120080278 1250 120079028 120079039
    0x6030c0314010b0c0106050d0812070c0b13060f0e0703060e1f0515060a0c020a0608010605120a020913020910080105060706020a171e10140d080405062106 68
    0x70000d50420150358103028098003900045040180c1207002d60184028000c0101507152028035454102c00c5640002486070010782c00e00c0100d04014004c03040d00c4003503988400c1451240d41c5407003071710801801c00c020680302c0700d0301c0740c1c04109480c100e0301c030b046202150500030344602c6085007421400d4820601558401d81e2065070004000c101e506d1003400c511402c3c03070f4086000d480740310001c0c05010745018003590040c0001107031a8800d8200480c4d00b596813080c0d03070f000c280a030748000541d0b00b4282442000c02086003044891a00b1010745100781c1e01040c02c0d040141442401004550301c003400020070801e155001800c02c040346486c07071200041d0000c916015843d5030620020810502403a50014403d54010a09010150041102e102e40c80088082e0482501d084480b000b85448202c82c1c0e040c10b04000b8010594243c00c801880d0183c03904400c943c2d60386034208061142540c0c41c1141603490240501007c40d9641d940c1d0010700c4141c0541d8184070f1020b0390350f0010b00078a0740c0a462035100c1c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 120081528 1250 120080278 120080291
    0x1020105090606010c110a080304060512010614030f100317040e10050f06030907030f06050f06010309021f051308030306030607020705090c0d0906110c0c01090f0510021608060106030c03 82
    0x6031703031000c0141000c1d0b84c00324402c05d91020300e41c0482e462507030541106c1043c0c0400700c2c01180b8241d204028001740d840584100300f0700d980e2820180c803011224000d038440624200000b64141d5000304c1c955400238040508804415940c2c2c80700d141c031000c018a030311103102c8002002c01414a04160303064001807055264140340b45041c0c0064004600c2c5c9203581c0c06680003000085100500740268002075400810b0503503248030324a0071200034002100c00060b030700003404c0442d12a52192258140842c0e010740169104250040340d44488003141811108100c4108092603241c00d0407407880d002002d041e80110b0301e90410408060401800800e100110351001c00d04110355503859510b16002010282c1183e540c8605041401c09007120304400f80c1420304200e4059200b12007400104220f0401c1426149440d00c0360004640c0e4000da4410407861100e166400c2c0b00600c0d040300391141c00c43c0d040c012602101003c49644800240650003d200c0d600031400401409816001382c0e10814610714007049038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 120082778 1250 120081528 120081541
    0x1050c0a03052809020411070213180f0c0302031c0801091503120806030105131a13050a0309050f1f080c090d0b060f0306010f090b010e1c02010201050906 68
    0xa50180c140080200340e261800f0606851003419050100e80000b03141105446020320403001403c03040038101c0c00755103031410001c000c02c0c010068820341640106501c502c404040d5010700508101c0401c0c00d0424401c08920001800b14000b0444183c40307501003400042c03640c010181041080700600b000b40117080d43e800000c0c0d501c00031060564903000d00c0065200080c0042081c011859000201006003010010442c56000340c0500c0c440c150880c02404103a6801101c4c0c8030101107024000e04280d10401c1400081a0540482d030f840310820141c0003107040d86858151901000a4055000c500106001d01803410881c200100740c0348140c03204d04001021540c12142c00440f580c1040c200403c070b00c08594403020384d40440300f510707100a144020741a03907800e0140107924140ca10f02c1c4a9402604540f106003000b140d401d0483d2075400c0304082040c504441c1402800380b02c1032890400100100d8890240c0e034034460106150500c00c020701800709588006801c41c0c0010700500031070f07413100c2e0030000f4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 120084028 1250 120082778 120082801
    0x60106030e0a0605100e0c0d0501150c0f020409020a031b0501080408070b060a08030c0705030106080a08120c070206070f02030d021513020103061706040c1d0601050f070203070e070f020105 83
    0x2c41d0b950001c0c000680307958141d0b100040012039004161040b030000203101001c00251f01901c03400780c040e01d0411490341e039201c8903004d07144480d0218010450002d0410b0104080c00b554400c200d0003d0300220b08014030744d000460301c003100e40040310314164001d541d883d007003658031703181e4080c003002c0c04c3c940040e040944074106c86000d0303039100402c500001300c000349a64850340d030b20301c00070224441143c4c1c50304a411381c0310380c1b50b028500a490007580307041da0001e90b4040025101400d03a401000080c80c1003481110f41903256801010100c0040c000c00c0303104c006840c1d20300140403603030003582100301101c0c0e10301c105420504443c15080844d404068403840f280c2c2010400c0ba0008010139080c20702040c1440182d0140c100c5d50300c4a0030403944000c1d80306aa1401040c0700d4810ba00c20020796651507180e0f10445d81c2081c66460743c1d840b041c19140041c03081c1d40944000c195201246003040d081c40074590010f49016000c1d00180c54194041041c400d2503604075000e0030303030015140000e0106190800728081d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 120085278 1250 120084028 120084043
    0x606060207060e091602011d0c03010e0304050a06080711240c03190c020c0406030f1a0405030f0d0f0507020a06050901060b0306040f090f3005030403110106150c05060106030e 77
    0x20203045c12078115030703054000d6202c451103c4401c140d0038800c0c03034111400750f2140d0381d0540d480c0c041e500f40314001c517140c00040121016036030700a100444032414110100c400d40c400400d98410311282150986402e5810440000c9225500d2407100720b21200c204004400b03880030b00200b0014030184184440503140d403030035083c042500d440c006603182c26400128070700803206104580146c42d080e0f0110500c4406680801d05600903000305003031441d40da50b4544502811100500300341c00501c9a4240c0d10201e00040c410701d03006ca01c003c20212182c200100c100c41046d5084030260340846442810088180202507001441c0300c001c100c2e1030302e49000e070003080c40001c003070900c50750781c91608800200b803030350180460a0f00110601004900341c80e04034402032425007003c0050004c00f80b02d1142c108842406070001a040ea1440c0c01c40c0c403641d8040d11081c29200c0c0c81e14a55480324404031f83d00c00e1400510102a460355540914198541400340c10510103070000000c15052004c080b5410f04001202c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 120086528 1250 120085278 120085291
    0x30906110c01030c0216080f0f0c030601090c120e03030f0c09130203100905010612050a0213060c030212160c080309010e060c07080604120201140910110d090606060207060e09 77
    0x22920412510b0102c1c181b4401100c02801054860008210100c00198422001850008076207044003040031407640c0c1c0da20101101c0e071640c00100140602d403000d030480c01484e155405d03d42000103002001009880d150040d807402c60f0301c04010400d908818620030740d0025080300c9420300d0702d620400429025140940000c0c03140c0e4000002c140a04c41c071000720002010394090800c90340d40c645400400b141150b080d880c90071401c1a0220300101814401c4403040315050000320002450910240c45150060000342c041d8002c01c0f10000b0903c20a00003800c101c10304c610300310580c0036a45845000103869801c5007000d0703807080c040c280159070807603d031130046181150081d8a9581200d40307949049034580205a442c0a600280400c002460390204d401500d0358000740100038080d50b880a0b0303850201d5296542d079000654610365442c2540c000316544401d01405454090258850303025100e52030030403a07049a84220400421703905101c11f001a0000385840044246403000003181c40101a001303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 120087778 1250 120086528 120086531
    0x9010602030a0311040504020c03040305070e010e070807030e060f060a0e01080705010509030712060f0b0612010504020f040305190515071232150402090d0b1302090c0403030906110c0103 82
    0x5a5213a2610005031001040014825551010701000990b00e0703801621084855100340100401d40242c10104ca60682e0b050305030380c4000d0307034442c0170803100100c000c3c0150090580c0d406806400039818013115200e01c0c8000429489420004180403000c4aa5802843e41d080c00d0401400b1580b00800c025045540c2481d00f43d032101c0191000a003010565484001400c090f45038002c10400107411107801c02d1003050341000701800c010306014062180c002031851880c0860010f0106241070b034050800380c014100c0290800780c0340c4d0389141c038012840000444400e0600c40d1002000420410141282c803188090503a03400c000d000075251040c120103818a103503c80001205100000070b686001e40321000a824213416843c5000703141d80000e07a04481d8a481c88814011181403c1c021502910381c060210114910320361501903c045018140120030240f03210a04056594008558016a00b50b0b5209645a1442c0340c041d00308107240e03010b407041c4005034030300800098002c1035242d040c61080c00d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 120089028 1250 120087778 120087791
    0x92d0607081e0c07030302010e06071b02100e0d030203030402091501080118020d020406050702040b150406080c09030105160f030506010e120106150504030b0a0b0918011b03051509010602030a03 85
    0x2116010f029072500282c092050141c00403d06134150000380600d07034010280d48e0f854540c0007003111544075440b0304490b4007540000c2d02c401400e020044001d000082e185c040712500075080014002c0c003180d0710a90060f44007100b0b00c800c4d440e18500f4075030400c06041d8000843d000c07410010300103030014800e40d8444890800b01c50b0401d65603030101c5030003400780c1c64115603a40d01c1e92000ba019400c07200c0e040c2d0003646003841c2100c41e41402c5840381c0207900800b090500340f51604204864a410081803110003035030912490300c00f80c909000301402604000c102400c1458800d40082c000c4e0300c800c0c01e04042606080c2031107030760b03600300410310b40d903080640381183d401c0c9000140f00c0c00b4004036449004081c503582000300007140d220001d04180d91241241c44401d03216011944269081401c5013607105150f40082181c003021048001e042031508800803550b60007110091401020410345000442c0d124030801c2181c41c08142340301c1c0e01d944201d8900d4250f50506c4402903a84c0203081301c010602d542c07100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 120090278 1250 120089028 120089077
    0x6050c0114011a22030b220b0c0d0207060f02070b0a050f0f0408070f0309060908060105030606061e0d0204300312060b0412060c0815090a02092d060708 67
    0x104ea1080c22498003540080d8650301e2801d402d01030411a0000c210300558051750701016191040c903050660040e1054060351101c6014414541c04000400000c0c0e03400c005000024520340900040407000b01d10040e00c0b0403985c1425003984400416152a0500d48030801542010806240d0340042604010741c0640e911840c100700c0724401c0035800740000303052101d48010540c2c0328101c10203680c0c1c2640c0318029582c1d10041039554800c01e02500e5815003009000402d1820800041c0021031080900c0c41e0041100401c030b400181d00071000360400c03e40000d1b060261404013441c5403d0b42c01805503040600040c2b9a40c0c2581480240004082080c81c140440340c0c40500c3d0000300c05040444030340e41d901c81da2082c00b00400d4141103801c0300c005060034600c04081d802520780501c070341d100324048203c20113a801045105000105103d003050350a000c1d04101e0389609415a04052540751442c46c0b0f01c03c4002d00b01d421042c016061031142008220800024071040103840d0540b00310b4602c0c1848000bc02d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 120091528 1250 120090278 120090307
    0x30608070e010b2a06150301060807051903140601030519030203160c0b0a0824031906060b0c0109020a1a070b1506030702060403030c083601020406050c0114011a 71
    0x12074181602200000c8044404c0002c00c083c0e00441030106408000810342042c5400c0c0c0310240725215403038001402c104964200210120340c40160100565030701a00c0c0d035100083c00c003a00603060711a0780030000502c1045010001d4075001d8101c0548241900010f0781c0c000d40d681310703000700391100c2001d20113688104001e517010080a05031502d400c545403254210004c109800450750200c00c0301500c2555692140340b4855003440b608041c010740320307100e184548200d00c18803005040300c2c1030b5070394403000074250340c00d00290a07485231401c008078205c00c2c140108124049990005d0150303814024020a450204034100c8400d25401100013034155070b034154455500302c4032a0401d402c801c0c00820411000e5000c280c083c425480381e1020405109884d0b012034140d4004c031440310610900c814580d0050344440d40700b003050405000510030f8585240b1b01d6a01b660071981c01140801d5001c2907500075100f00b806407034a00c485000d4820515890802c18010a20400c00c600104d41c0b0300044021000107075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 120092778 1250 120091528 120091567
    0x61504020a14210109020403050a301115010503100b010302071e02090109050403080c07140a050303090c01020105040809012105010b0405010f021504060b0f090c03010501030608070e010b 82
    0x7610a81d2640010450f0800e10301c1c0c3c104503400031442d4a0f002160702c6095100707690950350881e004000085c0c00b59981e040314180603208000110740500c80024408450200d01c0c0100e910307030f0318466551b01910446242c01200745150014401c0707440188071030b031800648612100030000c40450000d44940058009101d0280d018001008003110003001d46c510000140416109032910004c40c5e0303071440d68070115201507030018002080301c1c0c0420320550300c0384007620800e0702404601c0302454000088a2408527040c40403103c1790800710401060880c20310084c060200c081c0020711142c9080d40c2c40b00c8080c812100024144044050000e1070f19100080517038a01c0e0b08414100300c196100c004207035868005124250005160180c13036164548041342021801c1c10325a6001000d840d181c1c2c0e9a00a8102481d100350042c071580d0144071959a01d1010304d000d10240f03034080340d883d41444001020f680241d001011b055120900c204440c8540c070200c10b044801640d0301da030308c0e0300032040d81c566550309 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 120094028 1250 120092778 120092807
    0x30d0e0108101a03011502030301060c03030b060d0905011a0a12020d030306050604060c1707080d051909060f0501060801030206030a0b040906020403120f140d0b0303071e0c08061504020a 82
    0x10103840f182c1c00245503801541625100c1400c2c03280ea140340501280d0720b01c07090150b0b0380095206032003040020b0203904001809880100894200341400c6c80d0041120445101a111a9180d1040d10036400c43c00035403180047c3c0030360320302e000181020f601c40401e04100d0402401100c0080c650740606103e84d00100c09004000d0030381d41d840340d5881c002890441000c0054524000e43d0b09014002c0c1009030032601042d41c000400707820000b030604c0400007008010324810040b0300484040c86131218034030401c5010744c401d00c1c001070090b042c100000110741058000c94203002d407203001800076949110035258030a10002c00490260800c0000c10007030514900020580f9002007404410481d0b07444144807070030000d40d10403015001c1c510084030341b41501d102d40c1c00c0e085401c028406204950f900446072299001c0c0c1200d00c0c0444568500042845162007a0405221205c542e001c0080c070501140080c03002c0d00041016090100082c015803c4600c0c68611451340000c019451500462001840c0132 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 120095278 1250 120094028 120094049
    0xc010204090e0703140309130f090506010b071e020f12011404140115150507050109170a080f0f0112150c080a0b01020708070506071b03061a030d0e010810 68
    0x2c009003140d5600c00e902e0008941101c1000101c0c840032400100761056844000c0614128503580360105008003991044501d0940e100c0200701c001c560300b00040c038001d140180e00d00f83e1700d41003070a00e80302c43e000e6441c0102011442c08450360150703480c4540190090000c64411702101408070815005203c1c010340c00e031000c0c55500400040c0100400451419001c80009002c003400420350b0a620792000d0045030b007206560546146984e1041001d0090710707100360000164580180c86005107075103a404030180071003000076030070300d010352009415801440b0301708548040d00b0014403990901005001e00201040d40c035401070240001c0c1e4100d201c580d40900f4040240d00c0000782c0060000500b120404d40f030504005210085503c0003032780c0022501c55501808071a410001004440c2d40f2580050385c5102d0200000c4540c140020010402544130303000006160781800e9050030b144503042c06051183c0c0010380d411650360780007007c034480c032071091a08060039500c0c0b0403210007426540d001141e404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 120096528 1250 120095278 120095291
    0x71e0b0114010e0f0102070e0c0c06040602180306010b091005040b03151905030715110312060a0f050d0f02040f0c08040512030705040e0402010203070f030201051506031b0c01020409 80
    0xe440300c007000100d0020a903161003840d844003091041d000702c031110351401a40322501c200036006501c2c40b81e58202104444a91030020f5040c182d41c500300098400b50780941d8001145203000101000d12101c562007540034002e42d6150500c80d000e54025070409a000b01e055410304003101c3d00c01c000300c0307014102c88043d07075840303003419100c90300d18000303442c0d2480c06908485101501c098101400da0304640005004258813070a003101c0514580071aa006418016415540d01c541300051001c3c0c8a5104400c5a07083c0a143c00b004201c1041c055a21404001705c841c04144030350b440c0d02d0800c003106034002080d2091001e0302e00c0410300034030741c1a0004141914200300c3c00c2c1030550001c506401503015004892044a050b81507042d10700c804c0c0e40c104003185c030800c003c0004501100c481a071160050054034100b8500c8d40b10b80441e44801481100103075074617003c0190880d001c44241c1401d100580746a402e616040c24204000c403016018100301900202c1c0603c005da0003501100c0c00b0340345004060010307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 120097778 1250 120096528 120096539
    0x902070318032603011a0d15060f030f09020d03030b150c0a0204050906070c02010f0e03030f1216020304141f020109171305060306130c0f110f03071e0b01 68
    0x20320241c0f0400200065004058000c00c1c4803403000d81e41a83c58400b4484121100c0108400881c1e000800c249440d0b612802c030400e82d0341000c8150030040007141c588010081e0650002011119090740712a41c13207240035001400b688840e90070291580d418180001c951008100145030801042188160031000060681450b00f003c01e00c100628425a0b00303019944402d5201510b51000b140e020707002400300f40039040175600c40e00c41c80100d45d80904140b050298030401082c1107500244000c2541f02c4009080001452907041c50343d40108034005048401001610003502c1e4850b034400c0700104111100250816502c1c80d500003400c0220f080c7d00010a424540301074080d2036461010307070307509403454034456410081c20122140c0c40002c040107065581004100101c0e070300060150341c1c000411104841e4021224030404400c4a0f00d500c0b030340060360404a00030031000c0091b6804500e03400c85082400c1c0305400000703503101d49500410350445802200740ca91000c51010201a04c00c0d003140d000000d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 120099028 1250 120097778 120097793
    0x1a090c0a020c0105030f0a05040206070b0709050f060a120e0f0f010501030c06090305070605030c0c030714070f0602120315060f0a030f0501050f010f0909090827010801090207031803 80
    0x110080303680940c0e0342e8960000041d5920300048032881e001e01c941c0c200040c0703101c01a0713120b41c0e0302520082081d8184460380e12200d035915000c8422801080c982c803c11712591400550b41c1039444011502e80d45000702500004100c001d80e46038815400d0b0321403030341441c4420284898400c03080d40e601100ca01c00c00b04108140601420b201c1618030205c56040403951501c1500c52105a035040b100510400b031400d18101c032598001001c0d007055900c1480042ca116400340000c0c0800b40c01550164049418180342c0c0d81094010742c0204645d01d0400c10401446030081807101c1070b05410070706140c42c1c1e40d40304130844480440789000d07640a08000b80b00c05c0c2c0c0007007403006003002a0032503404010044010a10a00f2102700f801640d5000030701100241c4150701c18550079080141d603161064040b655800502c050701c44448040300c98440100e50030043d01d0305200c401200c1e0301d6001c0b10000d18501940040e01203601806801c1e01a600010104245400b840450b05090340741e14403c80036550740d0901c00d6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 120100278 1250 120099028 120099037
    0xc020111070c26070b03090304120b0604050c0c0d030b0a03080f0a02070f050d0204150e1303080f010303090b0708070b0c04050f040504030e010509030109050f010b2107091a090c 78
    0x182840201003000c031024104050079040c0051100802c1136604000412881e908001c0c0b40600c1440300700000724000030031003000741c5000e124020b181c005007050002c000503258010807210125a081c04024a10140050110b044261034200050200b142c6004140001016007029020b020002207580c510301e0048000c1410342100c0e07003a20b07105500c03403400480844580c8645035024514040b5880580741c45c1e0301608100c45858a45448240d07181e00f00d5024a42c102c1e01103101e030540c9004041410f0b009064598049000c1c07032112040d41c155903000d001041c0601a20327440c02c0b00402d0350800c00c54420211400c40345c01500132042450038200c4a580360303010303020f26030040410500d12016410316001d41e50040d9495207807840226241c1c00112025001902620303419900c42c407241022039820f004130044d80301e0307140000c2181da103c4000e00250300110b000c0802d00c42000406c202c014403011820005444030520085140701c980e0422100e40d4004248459000c00041c0500c116440f1032002407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 120101528 1250 120100278 120100289
    0xf0d181110020604020114030705070c090b01030f0b0310020c0a050703110f010f021506010e0d1101080c04122909060108060703180f140a0f0221100c020111070c 71
    0x109103401c0020102d07200d060503280240840d0000c0e1001144d41e44100155602020301c2c58014249140c0b82c40c0c0418504056004403240e50fa10705c0d0241255a050143c10f040b641b04c00c1003804100300d80e50100b5580c0f6402c011746161982c1c04604403000c04414824006a160010102d400054880c20402146030041c00700c0d1b481444081050f0300c90354020b881c0707031342c0c503a0154014000500c654410600c0c5520001d180030704000b10580c80400c19502c070900b10b80b42d2801489800100d0300701d42c0c0003514040c070181c0350a40c036001c240000c104a080f240700c010b8100703520807844440d5a503002d012043e9030203032314075011084140c3d00800041c404000f80042c100c13400d8100700ea5054442c1c507019011a034440d813240300f1510000542c80040f41c00350146003c205c0c454445041c5100900b015203042280154048402c0b4551148032419031a01c610b00044d181c200070b0041c580c00b42d00680103952417400c280074040c019141c00f02185154003e5111030800e801c1c821480341e5450007498181301c400780c503000d02c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 120102778 1250 120101528 120101539
    0x6031506060f1403060904150c02031e0c060705090a090509100f020405280f0e010611010516200601060e030105010e010302030304060513081002091807050f0d1811 72
    0x20481d025216a000021440c01c2d83c1c9018a9525128240956060018010346881100200110700f000b407070f03c034010300d08403a1360295403034484c1d070039040907030b810300e4005207010900074004d09021b180007059294010f4801e00b00955a0280c20001c200c514066901101c8c2103403270301c010051204000301d06010a050a80010449180043c500f58100e0096000709900300180b03240c4064a8130025000b070441030b03003210015241070b036511100c0c80560501d401800741c0c04e62040c0104602600030201c0c5a2021044000f441249411a50b00e1a000310700c1c1450000c00004090464204521000100c0790140f44000d852042d07854032400f1741812000c1d13903581d01a600e090000138900112543e85d0f4140d0368024040d6140a00e4844120ba40790403441d814a8a1103400c10001607a500c100558200109000030160700d80402c0c100308881d0440b5129001c0c4018001010010100e9201c412600001100a51503031101c00d90559070009110001645138203030813441d84201440180104040c140401311039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 120104028 1250 120102778 120102797
    0xf07030915060315050412050c010e030c0a0209010f06020607050304020f0a0e01050f0d080405010513080d09030b241012021201030506070219020915100c050606220c030603150606 79
    0x180c135400c96004507170141000725441e221250301880344000701595a041400420b000241155080c110362015500c005c080d400900342d00c0441c24403241c0503005244010710b08051b6842e01d0000303502e03200010984420440c0c0040042e04540da00494090203c0000d0095400c4507121441420012002e0280a2040c0340714010f1801c5464401c0c8000c501540c004e20313844c20a4506001921503800550308040034014035940481d800c08d08002e4600000311682d20751542514505091071020000707481c050039a9035a070700a0000c04000c04560350540307005d98010707040d02a10001211800070600d0030380070150000510a94010030304407000d06a0380901d0680340300751901b038000e03aa112041c59035448000c408580d0007016203860290641c0c80100710185140072448500050352100e9251a0b44010030740c8003580c40d041c03050401440d0f030b0285083d1001e080800b0610365084591200800030b501464407600141d950610940045d030080d644062081e180702445c0c002903000e0007a500498001500d0740b803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 120105278 1250 120104028 120104063
    0x606011209020a05060702011b202b020109150e03070e1b0c010609020403030f0206100503031c0225110303090607020d020f090a022503080f070309150603 68
    0x104030003010340c0c0281034a00e00f92610301400400c1c0c004190aa043c04886850750410360b2210500209040c4036810904510390030b42c1c888281481c5503c0668000c01e22140d80403000d852402d071000e101700e204d07804040f00740510320040350760502070741003541902600d41c10464501d802101c54101d804080301a14001c2c1e4403039100b0852800220b40c0601415254a00101140c501000038090300d900031001082082e1603868000c05c2e07901c5907100303c2c0010492200201c0f56503040c0403003034001d4034040d4003280f140d14020000342c0c1ca00443c40411882154216180800030b205e42c101c440c141c14441140810090303240c60445000ba041c441a40c0c000742c900078039005071030080304480c2c0a1200034041410304120303409204011203906400c07608070758500c402000e15a40da2800511070710201c000035940d02442030310301032001d880c2d050402101000c80c10b1900001d81241c3c1d03e580c091140c407080606555038403403c402030720900b10080d20301200724003110450100d0b50000410340b402540e0601d900190301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 120106528 1250 120105278 120105281
    0x2130903080612010e0d121d03041413060303050405010f05032404090609060209040b12060708130b04050102181002100b030120210c030109090c030501050906060112 73
    0x2004010001142040003460303a00d40030750074907070301c0b030315403000003444811000d400340b0300012510a0004101c8a04540e1441c140c140240c84400e00006105c2480074517162a081da01d02440c02000400300019041c008962900c8030507001050800a02740010766480c02d01508541c0240100c0e0300042e9020ba40c1c81500c1c0c000d00450f8001d4440e070720090200d41800309c40203581c2c9841031089520030b0300c8031102d0001ca072541c0507d9050900921006940390b1186040100300c1d188070340c48178060304ca00f40e032040c0244004101c01e0f5100225050030003e40c4e136828200e854030101c40300700501150300101070009005055000c0d0103d131300c2003004001c55202c07060070411850308840c4418010b81c404100c4600c1146180c000585108000d030020800580b2840c40907521518121004a54403000ca07040b950003003240910581100300909101050500c3d01c1407083e01e11050080041007519564103504015030001010002c4ad040030080015040c82c0c3c500c40d44980b001e42d20b40d4002608009401202e8819 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 120107778 1250 120106528 120106541
    0x210f1608090c1003020d021306120e1203060402090a06020114150607120905060c1f0b0a030602030601051e030403020705011b0308090106090204030b01150504050a090e0a0503160213 80
    0x210300030100344540c90100804003039803420340d000700350b021b21956511000300d0000c1c1c09004011740c02400b043e4141310300200004101441d1105d0f060911980d030701d00d41d00108042e0700014000346443c0d40c1e40d0350303040406c010f84500b5a40c15000640c3c07a90008401d5410b40c440301e162902c001e4907001944030140032041006881d25603507408401086503000081038041106100c1d0f100b81090f41040e9a00c3e00010707000c2e0010000d242094200c020341007498002071300404801e4a2142040205040a10100b00d00207181d0100820499000010a5560380034405560058070107048801900d0103800b40b04000e60003e9400b18090310070b100020419601584420040c1240100300c0d10300e540154408403031414002d05112491b5503103110100e40180c0a00090000c0c0d8054002c1d0360079540f40024918102415086d06c034108142032100384402d6480d1800d03a021101050700c0400c0011110b8810b40c2000d11006008280e03202c0020604000031065a44051050003141d8015018102c03c0c41d0340c064642 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 120109028 1250 120107778 120107791
    0xc030c03040f050d1106181005090109090507080105120a020607030c020909071a0d090c0605070309090204031101140909040b0a060803030903070f050304081002091c0b010b210f1608 80
    0x3944030b103145d2a820314201612200940500c200214034400001c15204d200d17540064000a03c000390041081d6001200d04004010110303007005a4944250000d00141d03041c041c1e64403900c00c401c05001d41c00340c100020285240c000f802c080c1c1c0c1e1001490050054424000301300c4c01141c0480c0004d449050204e6203408840e42a10003105e5003e44014507001988003400c5030040b19616403401010948205040d006001e640d19940c2c0d81e04101c0c200a814420707141d0195003024010401403000400c08403564070084003c1c03d02200c085c404240c0319480c0e0103000d004a400c4540c800070402170007030b441f08041c0241003900040140310b44400b6850741700d22045421468542c0108003090024072024003a0702914095000d41e410603855010352810040100300ca0a5000e801140706c201d00e10302010a486600c441848501490100c1d40d21110b03200c00c14850000d01c210040780b0b440300d4095442000e0407181c203080300d101042c500701ea002d4105d04800d4400102d441400003a0b000c50728059001070740141d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 120110278 1250 120109028 120109043
    0x12405122e060306050919030c0201211e1104060c0f0317090601080c0d030804170415020703111203030a0209190303020a0533040204020c030c03040f050d 68
    0x403007041821100030303050622610003001242207004030070954802c600140d40702d01c0002c0303800e007041c0c5561071030001e0341d403030341040b942d000c0b0000e40000e504500107601031a420f00f4081061306103868400c04940d410a07965403441e0910381651031048100c00c200080d5030180c40100f20040d080b454050460246000f90004110095120008950150130516542d071080c5040e84012910f42500f4603c01c42c2130354400f840364000740060280100c281718540e07070104180c801c2e40142070191001064120b0150001e04000e04000d4041282803410342250003030100c104094101d411807400c000d586004502c01542c100c4240c81410403140b4140210340c1c9031400300001907007183c40d2144504000d45c44000f210f071384491000c0c80e4400d000c40481d0750600841c000c3d0040c0c10304c40d20740d00704542004c1e4102d6074100e180707000c40d007100b082400e0250750241503112414440340319503e07440820000d10401c0900f288a200108600d02c0c10003000000300251001d182c650229180c0d40c909010b200f032000c000040c087d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 120111528 1250 120110278 120110293
    0x806060429011407082206030b01050912070503030c100e2d010207020a0b071a24060f071b0602010209010c0803070309150209030d05090d0f0305040801240512 70
    0x66200c1c0f4464107003504094507543c81c040031076440c04a07607030003031460003008100c0f1144502c1c205012102e1000804060405119400c01d0400080c0544903410b02c030b91207500c40840c0070801c0e54040003000d010740b101500701c0c2e66a888074800c1c66039844041c0035810340300c0d081141c1c03080740c1180031801445007034010010b5929030090700c0c068003e402c4455a4121300f50350a0050320090b03500c0c0880c0d14020101000b01ca6900d1500c4c0c20203002c02668160003c3c10041540140402c0c018140f00311b0740c1101000b075140c0c503a6024a0005143da11841101c1d9a400300041441414440301420004920005140030310005540d00c030141d090b400b0702e41e9914040b0b400080d42001046052004607404020b42c80d00048c0e1011308e944041414200e0000291a2a0f01042c0407400d0300f0704100e400458100340c10820304117142c03200050300f94450f41c4030041014bc0c0030840001014090426203002d0030000c130091141e081f03104020904060b2104046484810104c3d0004c0c06040a202c2c24200589000103001a07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 120112778 1250 120111528 120111611
    0x604050403020f160509060906130b1206162318010c0203100504120c05030913110307080907050d050d030e0c0303040b040905010f210507030b0108060604 68
    0x9000040003501503000744020b504101e41c0138000181d1500600980f040140c0c24401840f00703070140203059a0180d04181c1c1400b1440d5607070981d40204098000010900c001154007186043e400100003002501ca400107100800720210941c0e481c0d00c0c2103544013a142da1105004010902c001c02110034142e40030450300f800503860030035101c1145018144460260090303404246085103101c10602065540e03014031040003118034851054041303914002d41c80d011a40c8441fa1248141040913204450485c403010030099547c1246410322805545140c9a14001602900c84502102d103441795001d42c02d07011510b4945840031002c900c7d004001080c082220f02001d0f030007040c0c0c90b46540a180f09040070500e091b40e080005001400c2c0c400d29840d01e81346004000c5054502c180c211002c003030000314090011075a112a0160750100c2008031121034219400d1060501c0070307540002e031203d01c0c1c0320000310303454000007882070180c0f1042d2410065a04006400804c0325405c0318103036400303881d0030b040064 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 120114028 1250 120112778 120112781
    0x509010504030f2307120e090105010f030216060518010e0d09050d0507050a06210218090403050409061203020d02070f060c020604170f0d020102070201120e010e1e0d0c08030604 78
    0x282550005140c50302e24068400c842c4c0e0340d0030900040b142d05101d400c004002d80e030701540a80c01003030103036821086541403200203003411504407800c0003011b6020a04000340400b0003500306c91141c01180c02c001d603040005103043d0b4407500d520004103660810080c0c2045174400100b00c69403100c03d0769080007003030130001001030000440c241030b0760a101e650004140340c0c1c2e481c039644000308600d480301410380518150700c0d050020102c50800c0d1280c410b20400c51298141503440c0c0408030100c40480c0c10365501e2605460500032500b0045c14070346001701c003040540038440498a9076000e03408480034078444440880e911402c0703004240d802c09030341e07908129a50180200d111050710082500d42483c0d290030550041100400f40c140b042e80c0f1502503c1c0c0c0040c0103000402c84e02c0540d00c000c0d403808500d5000a41020041e144c110509655401c032040303030300c1080d0b00c407140d2025080259109a0340b42241c120015640110447d078a0240b001c0080220713000c0d510b04010030354004080380c2107565034001c200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 120115278 1250 120114028 120114047
    0x601020a05011e0c02031303112707031404021e0607050609010c110f1504020109030b1006080a06060c1502131205011a1c05010b130209040509010504030f 68
    0x14150312405040038006007080c000e910071a030b0b82000c061601c0c48140e040c3c105440c1e068074010b055400800400b102002c00740903502c1500d41104013900f6850001000c6400d080c01c0404168031250f1200345c00284043e511049802000503030b40c14442c08005401a403c1c0e441d0641d802540054045681c0502c0502c943c0c010004400081c54141812020385074103061036402c0360105066550740c00c1c0c0c0c45065810002d0140016864801044122440520195941c200b40e102030034410600300090b0441e80f1070f03c1048003540e480042030a19050804028510303043da8042c0f11b0101ea42c03000084d440201ca0305c1580115040369440358070000082e00c89021001119140340c6919408106002a0b0000044a1001072052040110244a1a04010342105c00f2002c3c000e8000b0003001d030703801295440100030540070140c00c6003410340700c01034505070340104010032809030001955048030aa003100c44d4041c2600400948003030089984503242c040c201da00c1114010301251800210014041c452032942 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 120116528 1250 120115278 120115291
    0xe010504021c0b0a120609020907110a03110c0423161b060603020a030507090507030b0d020906040e010612030e03010608030f1c1416020601030305270607030c050607080103021305 79
    0x644e200381c071031642440740d0803480e80554070b040c0c450001500f1802e2a0301c8441e40300e901841c00041801071508903a480d8849200043c0800141d07074215096610b052008a61103440140100240c4641c101508280012002d4000b400d046000010309000348501d00c0d203140040030b64400c1c04a11001c004141e0310100c95005a94075a603640f80400142c42e0040d042003e9405080145041071410724444c040d0f071401020304080600384034000b50760b83c07036035410500c40310346c100c400202603560300001c40c0003481203071841c428541c2019400030b24200e480c1103280c0640e000f0740d41c00b40200c004038141802e170b541c9440f0b098200e90041000c13049501048002e0992403c04034601d50400c4604141c203000d0360a0f901d0f40c0b44440a41c5420b00c107032608001710301400c0c2d4615001a240d00e40c95501d029145006940c600024030003160040035040d094914880304890340280a640c6440850400900100780240200c500303210304000b0561050084030154100c071340c01013461070724640000101010709005403d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 120117778 1250 120116528 120116539
    0x1501020c01050d020f04080d211104060309110a06030606020c03030c0d051c0c090f0801050415150f0e040314040807060f05041503050421080a1a0a030605010e010504021c0b 76
    0x1240403e810311032090f881c03034a50389e01c105444404540081c440245141882c03000d14009943c0c8400000900b602c1c221040c0b4100050012158100135441d41c000a405a1303018102e18800f2490581661050003a034021b81c0c200c40d1040742030342c145a540d216041c024038250b407204140c010014481c5e801030102e040448201a103404510f6117040940c0e0042e083e01012414a2a05210b5034540c0c1c0c12603002018100e000f0302641c01d241d03c4003050512140036107102252101d180d808142041080400180210040207100542d00c2080300300703c10050714218000303000918514007a034a5201036400362040540035080d0f0070b10700304080e501310a0b0071900b901800070a004c0020510904e0311405440e4009841c0402d1624040c5000041003070852242466074032902c00400da00c0358091485c0394041030b213070750009420649406490360700d401c4407a0258172642288000c802c20000b43c200c82c4c1203a5100b60000426601c50302048268040c0b090011246828440e0045100249800617086401c01a01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 120119028 1250 120117778 120117787
    0x242090d0807020d120305100b03060103050c1e22240909110a0906090803040e040606031202030d18080904050709170304061707080c0a0e030a06051501020c01050d020f 74
    0x1141102060f40c10988400b117000343d0900c8084d40602a0301e034407803c59a0208616802c259081640e800082d0200f810180e40d507000034803e070048002c45001c10543e403000c045020001040400c16400107481c0030110648001201c14005010b141c0419603100c81d5a00d88029050424001c1000801c2c10510401c07001104c0090001e02d0b030310400c1ca681d2004d40b58160703a080d442001030b00b0010b03550311480810069090400c090703000841503c044e1184826a3714040d00e45060040240c800742e04040c10380b4010f0080408030b250000002c110030420b544017444034050038102480f60085a180240480000700140201403130554060383e40034021b800e00e1420580c039211164842c1c801d0003c200001e9100040500000703410500030344090804c41a500c48901d02503030018010040504802c420040c0402d8001d03105009060403140c1c44800703021a582801d550411a0150a040d42c00c6420b0305500314411700d0a5201181d0088107041c1030711900c1c5020203081080380290b1110707000341310b4a80300342b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 120120278 1250 120119028 120119033
    0x301450b0103060c11070b03010501050f0705060f100e0103020312030403120e0f070906080c100c080f030f0f2503060b070503130b03130b0a02070242090d0807 70
    0xc15180a1030040c0390000d1500d8036010041c2485404030403052080d44a1342003001004000c1d012281510030a2038210b1300d0340070030242280d150085240090890081104200f81341d44291801441506504014080c1c00d55450442802000a01000c2d4054200b03081080c800d150020086801c5840f034504003030303440041c0b8200c2c804c81d04800030424140e00076040c1006172030300401911002e0301080078100041d070310704107965a40c2d80040135520b0143d20658000c1410900601c1150151900660000d81e82e00e04400f01180c0d9501c201e4280d101c0c42520340c04074080d01103000d543d51042080c594012001c06014580d1841c04458030301920405840380300108080103110702511600e407040f80116260141c035052410f4010440e000452844000e1041142d00301c3d004610040c074507000440d14010340c88a1540c04060305c190031002e904055809044840c8184130590f030000c0c40711607480b6048184010042000207813400303a0846e00441c0501c03001d131030703490031040201d8594414500c070707842d01d02c1c40c0c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 120121528 1250 120120278 120120293
    0x71502120a12200304060903080718050f04020c07091b03060b0d0914010e0a060b030a0215030a02090406120204050a0605010e090903070203010c0504301b03061505030145 75
    0x200d80486e10b450f22090700d0020103800411581d000f00c414241071039400b400c0240d19610200d50b03c505441a01210024049034a8075412031f1704860842040d2a103241d00d0348100c60103030080340a90010301c524803800c174058074031030f1040344240c0d541c2179012450090940142009816050f106845000140501814106003442a03412440e20000030b811255030a0500c1760489912002250094103c58031100c010b9075181441c160f40310742c810a1039100d4980b1075602e8024042c0d100c1150700146003203000f01d25000c81c8081f045019108440070f00055407440c1b042416034510b403041d03a001c102c404d004c0340e510346410403a440d440b04100c800c4131300784102034000a0a4520181940002c40c900090038440100542114603e0001c030040020300c079800b5501e03680f81c402e0031020180825440d4501c80d240d01011117417102c011501300405000700c2003000b0b103201c01c1760701510445120398a040852a0b049482060030481c1000745d8424020b02206009a1031070040c5e140541c00042d02c580e038803140002c500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 120122778 1250 120121528 120121531
    0x1030b160e0303161104020909070f020f0a030c05010c030b060a030e10050408030f09010209060f09032e06090b13090314030c030a0c18090b03030408071502120a122003 74
    0x1000d00c031011041140c00d00c5e6030054050b180d041d00a9004125405c2d11340c640c200c4031500190340c1e142c11403c01c02e41d803504a0900101c2210702285026007400d49060681c441040442e4034007810081140c002108020b40403a0b2101a2294000d8000d000d00c6030304502aa200085030040380064a0180c50b8a520203011a50300b00d804880384940403050142c0320052540f62984031130210021850210320340009102806001076004e0b0014000958050540381880f07414481c40c0c0600140c0c000310640d00c80280c00b01e0038007100000d10f41c40d0180003d8a181c05003d42c046c12940608864142c01007003414a024281050003503042c020459901d004042020004502c1683d01084e2262a8145005038134290f408015400701041158001d04111205001c1c01108841401c1c000140c02070799403001c00c0c02d41c019940300e036159008031000002c10719a07814445a503044160f0940b01105a109580112030040c800400c00081342102c5003181101c05070710801400301070744900c90012801c0c4040b02e9041e0300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 120124028 1250 120122778 120122797
    0x1308031305100207030315030506060d02060d05070c030815092a0403050115060c030813060f0908090901060513060503060103020f0a020d17090c0906040b04050711060f01030b160e0303 81
    0xf400aa8942456070510404070a00c0303090a4a101d0035141d519000ea58a1001c2e04145c0300c0c3c918650080e04650724441100c2d807200070b00300300380034030300e00140c010b0113855030030100340c0c04030b0080e60014510403440b10700080c50420040c541d02198541c44802c1a003001c0000c90354a40407400350412080c6800140a44000c521803000402c1104840310072035035183c250f030700400c01d0100a80011000a4004407026801401060040043c185905041c400341860220351024689070422140c24055154001d10350f01d0340030340f49020140d0380c0344400c03240e600c101c01c552081d2003160030082c401c00e0b1107031004582123801450094201005c004000c00503078802c0344000d0150744841c20074042c094015080305a040002441c0b280035240940f001901c0b0001003125920854660001034020768a99001e400c0c80c590280c0701700424a40300b01d000d044025841c060702800d124820004500400e0305100318140c4ea40031031655810340b0b401d040085105110007107101800000310611340e45407001c1014005151 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 120125278 1250 120124028 120124031
    0xd140118060f0605030c09010903020a0f05090c09031e07030b01060804030806010305060609060702030304090617070e150d0213150614040506070f031206030c03060e06130803130510 80
    0x500c0400d000c100c0708642d106070044203446008020b01038000c0140c4c1c6e44115589aa169140c80e18030040341c80e0107a039007000b5400181c544000c01c82c1d4689003900300c161a01564408101d49403600500300600441c0c01a83c1d1540c0604014915403d10164488540c082d0384229106192266100140580700740c1001001425940420081c03650000f4503a030050000c0c201040303603080090129440c1e10485003c0c60117443c0009081086440800448001300070310703103007000b0042d100d0100d204050340100f0390540724886c0040100d17189601a10841c080c00e40f4440e0801d06110100500c945585082e100307907031094081c040138224048501400700003483c1d00310740740c20007410038401071b050440e0000754811802c01840288000e491b00b008541040350803202a00114145217400c0300c0402c40010160340c0141003010000030030644900000641e44075400500070300c00e1035a4070568801c411100d440001c4090070030100421010310041d500005400800204001146c403141c0c03600031800f802d00ea035107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 120126528 1250 120125278 120125309
    0x10507030f0c080a05191505040605031203060418080a181202180604090f0615050402030c160524010806060a08060106030e031e0a03060b0c070306020d1401 69
    0x40c0d458403868a1404445500308841c8809440043c09080e0040894100c4c640e1040400c070141e02c003280c0e410303204030420021312050400c6942040b02c40f003540305150045040220204403131601050340024084d9000c411400c5503038810400001d41120150660b0340e000074100c15004c14814002070420440e56201c07281c031055070620501d2400e5003079024400320714050700c0182c0141c1d81d0303003003601d40303c1c4e0080000c40258541c5400140100348401c80100b1500c42c4026030700030889d5a4120652265090428400d12580c520601c001da1004440403444200c0401540030030b00c10b4401c0740c0b500c103406102180e108801d00079244040b6007046003821b5001c01400b0041002c02e1003040042e520020a6560b503003034516081c00780c0c0ea10b08041c00394005140c0c0300c5560800380403040040d00c020040c00103811401d51040044002c1d141d000d000c407400040e0900c98040307000322511046918682d0703032000900c5a2491500c03110001e400900c941d4560325112050b900c000c4440303101e04c078041e122803003000c40361 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 120127778 1250 120126528 120126541
    0x31112100608011802071a070207150203070809010809070e01090603020906030102070309060f0c05010204060f0e0a030203030a0f11071d07110604020913050105180d0512010b09150a020105 83
    0x4141455204034200441180144031361644102103161125445102680301e00191401240c03041010700300642c5680003a0030403031a1a40096054101e992a2030440f5031800e1300706040381c680c4030b0b19901420301c003003c000020315544030b01c800550013032801c019500c0682d1214800100c0c1502a448842e540340c540d90103009515182c2d94442d00710320708030b008510b008000c1d903000e40b80c1507047c8035000c01e210514010071002c1d4021100c1401281e0b03c14001c40d0780780c1d200d01024004001d810b10500000308042c9090200d402c0040c40c400c180c03500100110300b481e41c1203604803021000016950200500f6920a40c8241e0302088403c000d415075600c0c400341070481901d50701141000170040030810070468504008003501040d9141c202d0b030107444072081942c8850b15030108804c581001040c075840c0500f001040600030012030740c51441441694640701c06900110707034500a0580d103c41da40c02180040003010380d114014944044083c20100340c0f540c045c5000301041e044a42e1480250351a0704c200074a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 120129028 1250 120127778 120127801
    0x609100c0201090c050f0607120215010602241017060411011e031a0d03090303020f030a050904090303140c0703080c0a0f120216030207030209010803030f07030b01031112 75
    0xc0041061000f0040420380c1e88070140b0078846031040c58010340c9681800121038036200304131401607801c000131003180c24896500030340d0b502d48803407502c4074600e162001140813440030403c07140c081c0005c44a40507681e0300b100e001c1d0300c0040c042d140c030f080030750100e100044042c050190750351142a280082c02241c43c1504094440da15100c0f841070402107a420b9141e2440c0e4444420358041b0b000c0d18000502d034500c0c1c4920000007180109003940501440c4ca03a2080662142e42c1009807441790f0300b0780302004018140349a0b80c0c0100301c1800b0103e60b00340241e8507070b82444d60005a8940c028038012581d100b205480c03d40600c000ea460101040d00068454185034015460640202600f525240f8054030300000405050880441808021055000c80000000c607010345200c02024400d41114074428900656a0203140c40105d010700f8040340005415640070095911a20f81d003142000199525001240181950b0b0012810301d540c45003d02d040f02c2030b4001074094002e0054000090742001c500c0c025 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 120130278 1250 120129028 120129041
    0x12301080f010b060412050109080d020307030c020102090a09090f0822060c08030127060f060206160806010507060204081906240b090f06030f0708010e040201050319020903060910 79
    0x40c9141e041c001d0300d01c43c03525100c0441d0101c0d0314644a4803c84a079600d00140909140d01019000300c00204054190000e15030043d401000c0544040126528030304e4142d0903801a01c3c94030380d1011a07104204010009904481c4041c1e2146004e0090788040303681c0c01409410096500507148a00e900b0010f0b04c000f088014000340800342010b10081c0195074400800e440140a84200b8240c60800d0a180c0718964090540894000710184011500c60081030050141442100010311450303010030520341c1011442d030040585a03440480c82e0380c607080192483d91103c0700496100e03a08100c0000c1c600014883d555925000c02000c10041c2e14508124050761050103028480002c050110795402101003180c00845031420040b540310303d1184001509850300840152b080b901c00410000541c15500341c8a10550058490190a036280c54132844008001c983c002c3c045401040414280c0006058124440400c1600545407180c00d5004c0303801e006054402d882564845d552450065466001e02da = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 120131528 1250 120130278 120130303
    0x103020114070b07050d0e0a053403060e03071203050118150501110c090115031b05070b061315030203250308090a0503033006010509011101230108 65
    0x21030a1082ca511948601900a0002400d2110009482c0401c0101e50040b1178481b02c44000d4940641040c10b241391a1003041e2407580502c1c0e0541001c200344c0380542120000b000d604488000c085003181c3c0d48500400680007100c14a1100380004400038040015103d840f04543d907001c10b082d45032040030b0140007122040c414500782405520400c125a40e1b28038030807600241303444680752040120782d41c00c12001c0340140350810304940021609802110202e050346100313660400840100085040c0c004210035082d80000e6002c020000c082281c240740503802000090081d0a040100001541191a80000010102c41c404c80810039031600303204030440703254480300005d401400000b2100c0003010600000b0002000880c0c800307140d8441024640c0604009011655208240c1482d5414005404120710307284060307011281c024084103200501811040c2c41e00c906026900d401510a451007007580349175507580f1070038007446c220a070078410200c081045c5824501d504040304641008441800e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 120132778 1250 120131528 120131567
    0x414040b03031213030f05070b040201210c030515040605060a0806040b0409051b090105030a030809010e030a080103060b010c0f0602180307060e01080117030a0c0c090f0e0c090f1303020a02100801030201 89
    0x8040821851710000e82d00136824600481002d0417908033701e406001c80400781101c10b180c1b000e92409140c0603401517009020444400e0101001c0e00e00b00300546880b0700449400c580f050050b0f564240c0204030241d04028001c10205e44c00195401040403100000360503190b9034400d04411001c0040484000c07403164090b6601d00682d810007001c640c0d110440107004042110b8200041d60810082d0310440d45180740ca01500d83d5a07203007440081400400b130006645407450320740c00d4101d96002d03240c4500141d500c100d45490281140d22010002d4108a80c200703007550010040c40c003103a500340100005003070789844249030030030484001130042005070080301ca40c41c0301450b0707001e901d9000010b4888440091a02c1000d005007490142142415548509680340c00c055030881c40303c11340e030400b4205050728011620408e003403d04029543c0d0040d40c0d41ca1602c0440404282014038081c016403c0c107000380120f070340c0070030340d80d021a402d503410941d0100083c3c5a200144115039000010820f505c901141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 120134028 1250 120132778 120132787
    0x901060b070c1814130201270e010914130201020a1403180f0303030a0b060c0a08091305190c0311030c040504051308090907141306080702030414040b03031213030f05 73
    0x4c05408081c000e030508070640781e80000c4504580c0709003440c10702c0040071041034030103000c0c01450171003d04030f83c001d403078100042c2710021500003a41c1c81a005803203881e141082d40760b254900d14101c20340058205a0450207580f4404d004500060108442c1941c010700a5584180310205c9400861804148620465445c5246507465030000107681c0c0182c42d03200002102e03040c990000300e0521a80c0c00860107401040e9140047c8401d2101401c880c020a4030090000102c0f030390404116102102d0707440d1a80e001700804202810107900418145515041c0041d040404594442c10f0340c00032a0250b607035210000c2c0030710540c10640201a00010701340803072026816070b507640405034000c0814841c000c0296034000f88429220302c42aa2401e0701ca00190b5680b200901d5068905459034064240804c41040200701c2091002003210700311390001924040c07101c00c9204000c05052600e18159062006020300100d204003031403941d0250305810f0300e081286141c0d240103440440480000b40a0010902 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 120135278 1250 120134028 120134051
    0x605010903150513051e060604020405180c13170d050712030504111201050a0c0e03073503070c05010c030917010f020c0708070806090a0b0901060b070c18 68
    0x103110030120340d4003041c08a841c0e40ca29050303001c1c942070140007400c1c40c8030701010610a00a01b0a03039a80f5400100c0c10380c1c206503100004e0105903c114400c8036000340c100c200490b8044c5502031401e410203030b65010b217071400c20001001c0b40251000c0d00710501c603400c2e81c868810008400c000c81c001030843c0f410100d0400440781c88021318229100002803d043e00c0d04c000404200c04100441c10303054004090301a042c4030142a240200000c51314007480301d20300404488614028504002d00d00c80c000d0043c20041e040c405010810360721031074803131410088400328214070301810480d644201e42a800441c0c0750a01824032014a81050384102e05000d080600352020981c416424000c0e2966100b0f07681c44010100715503801045203001c500702262011901103241c0101141503021212041c04540740c3c0b43d1510f00d4142c5440d03090b075110040ea40a48942c00c0000c0d1560980d2394405020400010340566600002c401580b200000710b90300703d42d84806214007a68030348035174010840410b00704545600304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 120136528 1250 120135278 120135293
    0xb09061014070501020405041104090e060906061e090f070f050c0307030302160b01030c09140903190c08030a1b021c14040f0f030303050105010503070e190509040b0603010605010903 80
    0x1d4466901150002000014807000750100c0d401007801420810010207041405042d58001e406429070180c240021480960f4001032241d010b1008040a042e040e00d48500b041428440d203e8080000301d4080000c03003180e541c00c0845131003550407040d00e85851500b0800207004013150b90402d801d001c01401800c101040000590b1503d40d41418010781e203141c1352403450010704e0050801032800700d4150000c41080085682c403400c49003010f90500400c8e040300e42040381d861013100d40d1002c0341c0c0203100031030000d013001000300c441c00030f5800d0032403135400180c4811549038421a981c4905030b8035941d040301c0303040d90b0700c200c03180310042c51024000b01560106050500500354070002c080281160001c45000c0d0900c044500412081020740300c01950f48154030342d1017196120690100b850320700000342039402282182c0c86034040d0303a03803a01042006420000140d074101c0c040d580e120301c9450042920384035050700d40c0c05640a07a48110151070018100350950b0000d0700064104403041328100009802ca = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 120137778 1250 120136528 120136547
    0x605032d070f0216120807060f0608100c050915090a080d0915021c031104061106070302031003080f0405061c060816094d0301210201020a0507090b090610 68
    0x1702603580c03102641c18091130138010288040c0c03013549019080d2038603451a83c0100100d0b045c190940341450b940940c017a0455001c0304000c03000c90001c110542c0689803c1e89031202e044a082080703030130248041c0200c0c1c403101e0a6007050085a0002c1c080002054000c0984002010244071001c1203c0b5541e9000b501d40c82c4c541c5221444007000100c0e100010701a070001d4680c0340014a4107a00c0d25500c2000400c084c04500d481040f900505000c10b440d68031034004c49108034854200703c00c039a0301d15a1240d607184c0c42200350b0a41080b0500c00800d4980c0c0d44d074018400110800240c02e444140420008104d03945984a410b003940419000021a40c03420241d400f100c10303070480083c454840d00500090f011698070b440e42d0500c20500e00c2001c4090801c0300c503c020b1244440c4440c8109070040302c141d81c0c4828000d840c140120783e180c2c2d03c8812418031401514074410f1042d41c481d0803950392540e1a0a52a81002c1541510f81204400500300100461ba108404a503003c0c2580d0800d840034003005e00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 120139028 1250 120137778 120137789
    0x4020a0e06090120030409060e06100507110a030303020405032e020a031d0f0d09030c03020f01020a1a0a0c0e0d02040525020c0a0503030a090605032d070f0216 70
    0x40105400030a68055070030700f0200340d1401e0b0402c1041300d5401c0c801d5141c0c1c2c4107024140080b0b14114000c41c1c1002c25494052140ba00541011100441d0741d1050f24650401e41045954501d202c081003034544413034440c0001544240c50150329142040d0401d41440b2680c5030310349180001c480c01d03440c600d01c84d0103d2340e030418448100589d150050310048014103203100d800da036902c0720a40d880003024000240448490008003c2e01d544696082c4111a2754903544400b50444242103010f10261070070004805540e030050040b60890020703a0b0f204030500301c0000c440320404881c8020040344209078025402c101e000c40c42c0090520361024001680c130381c12401c01034015640c4100050080000500103d1907000750301c0118607190b61481c00a6440021154490284010000c009414140017059410b280042d8580c9d0403094100001264150401003a500705105026442e404080094a03401c120003400450302c012403802c4103014264192210040c811035111906c40300d54031310407a501400703481 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 120140278 1250 120139028 120139039
    0x4030e0303090a0803030403110d090501050d06150216050102010908030115020c09090105010303032003040b071e0306080c1906080903071505040b0604021911010207120f0e04020a0e 80
    0x804280400d00c0c6000300102543c0083d82c0b25404501d2060020143d80300b039200b03a0b12030599114011100703803113011140d1742c54003060311810140041e600600103003d800c011103c0020700c1b503607600070f034800a03454044c000c00560045550345c103802c843c010405018200a0000b0700140103541da030302400744014400c4454215a20032072841f014424080310022101c001e15030244c50a00ca5280c500a04080c07004401003403600d80c500c100b101d00e40030130340b0340702602180050840d912a1120700c070100c00240981c0c01c001401604400c2c641c0b030050b8192800045590025020381003c45562410401a804602c9210b043c1f54043d00000740790001d030165085031410f201103464035128145107000d9204000c001e59403124030700f0b68210b403d0f40207038030950241e2804a60fa444503800c0c00f080b441000d00c3c102240c5c08045186a52034016229030b0500da098400051609085440740440c0b9a51215440300041d140b1840b0341000b81e010481c503420072003c40d0214604000e05074050011030505401a000340c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 120141528 1250 120140278 120140297
    0xa0918020402210f01082407030b041d030c01050f01030f2d0b061c11120703020306040b0f09150412030207050109030f0f0801030b010b0304081315030f0b01080403 72
    0x106408020203e240080b58402e52040c205000c8050b940c11090241101c0e61040c0b0680c1100c0f01a41607405481004600c0315198a07213a1030011400b52950080c45600540c4408860140c114003944820b5141c0141c00070b55124010712200e81e0031348001401c1240c108522500520206070b5070310306001020707400b01c2c000701c0d807100c07510212a000c00082c2540856042118801c000c5c4644c410404c0d106d0602116030280341070520f4135600b1181d141450152442d09480c0c0d090802e13091501644503000008001c6850b2079640707500207480d0010490f0102d41c044130f10010b00911a800d00c0c8501d401c5207030000500040f00a0108069100b180204054074410880199620300c5000764104c41d4159005002030040700a9428003800c050081c0700f80324000b49103204858000f40c03143d0300c0c0c84d0680b41e2010700741c0c100d0391030400305000540014005407050a000c2280320340148101c11500000d0860103003143c84090725820141c100d410000012180c0350801c0a1803180780c1c0d00015035036007c0c3d411705010450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 120142778 1250 120141528 120141547
    0x2e0b0703090b030c04090f050709091a060c0703210804230a0b070e06121b0f041502060703020307020d08040309080a032c090103060e15040305090a0918020402 70
    0x9040962100400260010034004144c01c40d40041c8181e41c100780c020701c0880031100c400802c0307070740845003c0c00040030344000b4030050302d19410045c0344128206002c0b03111400c0200150091703225207400e82e07403a80030711030810030818654405907204424040144c2c0615800c28060b210120041c4000d15904203102e001c0301c2091031403c030100c03e010f21001c80b1036041081c60101c407960303002d50700c95010401003910f1400ca03251403011902c007450040082d09a80d02e0b103600e51008040d031001c900c040701405000d0030300d0b81b10042014200803d84406040100608188041d09103039001d04828201401041000b1007070303030001002c3c2840c0340c0711300d0130b21426600c1c4d0070101e600450642180c1528040c00f09020181940200c2190105095900940801a5241c0061983d0300665092034110050070300401c0030803c107902202c010100e1405451608204072014250300c0c0342240e0442c00705a011800340840d081400c80340d40540920b41e030400c41d13910981c00b600301030425448003d00ca0b130780000e04946d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 120143884 1106 120142778 120142787
    0xa090b0c1011040306050c030a060509151215090d030605040216120e0d0305120a090c05101202040909021002060f0c070602212e0b0703 60
    0x404940c9404071014080ca02030703051815809010001c0400d0301e41c0540f0788904140c8040340d5592802400100482c0c0307150300103e004080010030000f024545084014040d08102c2c0d02c081507114866045103002c6581c1d030002c0b0302d0807864041c00000d6400040080400c2c0280d01c05210041e19038050004070b0060041386840814200c4103480440ca81020b5540205540d04e8a0002100362001140c008492028205d0003d0400a41c424009500f015505d4200b40401c00a0040401d20746070702c050f122130350190b20f20805144104c080440d001d002c1d8018111140807080d51260750312803011004041c21070703060340a00b1900d00710b001b803603201041c07070f500c50041038800075140c0c0ca41d00041500d42c0c0000400300e503480da00704074519820055100e103000300090b10209075440d1820741c60b1384450b040ea1000c010105008801031203804400d000181c1c050b112034951f05504e4020701d040849 = true := by decide +kernel

theorem cover : BRFrame.Cov 119964028 120143884 := by
  have h0 := BRFrame.cov_init 119964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 119964028 ≤ n) (h2 : n < 120143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
