-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5136
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:52:06.754974+00:00
-- url     : https://prove2.me/submissions/db58b49d-9695-4485-b4ec-152a44b011a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 923561151 ≤ n < 923741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 923562401 1250 923561151 923561183
    0xa0201020f03070e0a1403030318010b0a08010e0709051b070812040516080319080406090b010e0a0e0307020607080a200d11120a0f11010203070804050f0a050c1309 72
    0x301000d034100300c0442d4219004c54507101004440301b4001c62940c1c06030f00c1407010441d98040149150390039a2403500000b481e1500500090b5210801c3d40101510307559070745110031081d0b00b403080303001422418209014034180b00701300b100d080c0501c20b00c41e40c0b0605d01250000810540c00210b6403501a02203010403c0e0501c0e082c8541c9034000c00c1c01800185124060024401ca401b00654240700400085e0080d030a807042d4068420501c000d10445400b60f039040c401e0001208240c659001e0218038840d88280d1412003094000c5441400e1a814142c1c002d10500e00161f5651045231001c40c5d00c002c0d85030f201c441207401035072000106000520491403065018030b5800b8006003101421215a54200081030b034424015101d9145101803001107000f004004407507400340c0f030803080001d904c0c981203000289052185003243c0043c0d5400c80014000c00500043c0401000b0b044080d151080240c4040c004542c9c0b4980d07106003420805014401004203400e0403011070703104080007900304030b0100017a520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 923563651 1250 923562401 923562407
    0xb041b03080c013605030f0403060b0112090809010c030c0606180c030912180e0f04110102031305040b0a030b01080115080a0b0f191a0a0918080a0201020f0307 70
    0x1406078407840c0d031070021440c0d02d00e20204001103030025280f10001686501301a0070301c40c50b02c4640c00f030f2403d200403c0007d141294510081c00158003030b81000540c4010540010f03e220030061820700c5003420303c000d50011a860ba012988a4042400e044046032554039040d90958282c80b00a0106890a00b00294201010108540500101c1c1003000f1a410b5810260100c1e030710b07418098440089200d40550490203074000b038141e5032104008516180d514509410060310071265a04118103c0b410f1000b004500d02c1003041001c0c090002e142070031071100200c7d010307018901c1414031031a142d00d0600810707201c010012000d1500441d00640030342c1c446000c1c1d07018080003100e1000100f80c00000140043e0041032800c14180d008024840302e403034440840c0c00000018202c0c1212801c0c000b40400140410b104030120201c1419142c0f403c00311500400c40000b0703c82e40190034540c200030851440741013072040a00d1150780221f8864407410300040403030083c019141002d4100c80000284111550 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 923564901 1250 923563651 923563657
    0xf050d1e0f0c0f110c10050c0a0f030807030614090402010311043203070605090f091612020a0f110a0f0b010e0a0b0f0d06140106030e0601120f0b041b0308 68
    0x12180c40701d0341159690303e0b08a451410100300c0300701e650403803400d1001c039140c80c0c071b0080828003451070300b5410030200c864280c3c201001140211000b480c03441400040580009440d80c3c008610708041201919107a9401a8800340c1000184036016a900103400c40e80280e1183c0b00c000d802071111a2250740300c030b0b1001070b4072a001080d284244600103041d0710300b0603c0c10980c0104c031005030152640ba850f28505945a0300200409a0b1140090300c0442c05511000d0741d451080e01280342582c9503d58219014042c010700c44d0b05861001d0040014001d0b454001b0300041d0741859034034041040142801d110350908407000783c02006c0c900e1010840f0148500203100d00e058800242c006a2607844036141402111a0945956005100c120100000e80f512100b103807020b03070040002044008018400c40107030f000907007080020a80c2c1c1c1100d03003205e6008101c1c540c0503203000b2002440032440c0e81c84000a18071806002407110028000240401000032032510b500484241c002428030b4480c81d210440d50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 923566151 1250 923564901 923564921
    0x21f09031206061d0a06050a050a0c1a061f0e0d0515070816020d0914180108010f0b030c061b070f0609030b0601081e070302040b030405010c0f0f050d1e0f 68
    0x5130b55654000346a24280b0501c4046a0316611031302e140c424007000a59050300108007082c01e200d44044058042011141d20900d0907403400312611851810b0020045c600b03403003030301e85890304244061440e9903d4205501c00f44039002200d50302039100162920a10741115004408105099082030219190f000400c10f402411800d0308a005c068800c03034126542c000982d0844001407581303808011480a521140a5101010f8121240100782110300100c0c40003c5c0d110600c02e0b999070a0742c4032220814814904800c4044028160030210f2030000b950a000308100740344d5401c000105050090410001c48004180b03000590031010758a0801074204201c80c44103442c4040d110001030120340c406c016180c850800f1201000101101c41940d996090307004202900703041d1300700004254281c8180186100d02d202d0700000c5650070010b88024500402810600e0038802c9000c0d0380782400d030704a019036110044055001810581a9000c0c0d03800d065055500c0e50510324100c0c3ea000300315405d0308035030101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 923567401 1250 923566151 923566187
    0xb030f061803070b1302130c0c0201110a020906040c0903170703080c0309060417130324020405030a0f020411030106050d06080309060901110312010f030b0601021f0903120606 77
    0x7400c403880340780e45920404000404405013400002c202c607100e828142051800600110b009031205001c850417606401026404649012040402c540e4490f8594981210f95005001c80c60000d80c0468200c640141c105d1b48900d4480c1650101c582c481d1100358001d5402c1600101801c10b0002540042da01003082500041c800d074001410700401c02c000c80f8005d400d481e000f098103a4840d2500c1c1030b2460b5481003c4a2044100550454038001031700190185000b0702c4280f010421040c410740c60300380150607411b076880c01408100080d0744d010454105058104110901c248004d20019008020078070090999070004000802d8090340200900140e0301d04004c108802522810103e54074000d000c0201d0f4022410402e42d900765104046050300402000c040321b084c203898500031700800a00340c212a00e1980309000810a1180c070354600768108030b007030000d01042503802d0b45450030f4480c00052036048a0b15031759203804251240c544910301c180341a034104006070b11044000c05440180c0d14124003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 923568651 1250 923567401 923567431
    0x90a200f040c0e01032013061101091e02010210061e0915260a06020702040b1906141b0c0109090c05030112080c060f010504060611070303320a1403160509040b030f06 73
    0x2027401441840c17102c64110903822403503045a441e01e061000419022070440c0105000c040381c4644e68000c2101814143d85515400d2a0680c016803110626900c080301d102d04021f90307112114021100c900503135060740c400b90b0056880002c8800c00d80303851104202c152040245503420311603030740c3c05042d0700c2d0310890781488070181250403c418148942508109200807040800c140b0b40640d82003072180c02d4406c0e249041050000c44035055859141c0300e880160015017044030729607841003000c400b8088040d020000e4007071002004005000c140150f1040c02c1040010304280150501590a0b9070001822588945011050703804ea0140a119440c0150308101009c2082409040140c0741803403070000801c0424070319101251016000580000c81185000c00e02c14134400740190501b80b645510300840d941c00c12000b0041803440d8a40a513144841c0601c144116080d4034182c2d900529110b151880e00c860311500004c004005145a8039494858070246a100190204601c0d105607945901d00d40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 923569901 1250 923568651 923568677
    0xc020312040f03080105100801060503071116030b0f09120d0204050415080f01020a05071101110307030c03090609081504030905040603060911090c030f090a200f040c0e0103201306 79
    0x480c4020011440c7c040b40c03001c2c0040c46413612a2010315807010040c81e048540e50101e800b81d0342480800c41c800c42000d220800140240320800340043d03046544d10a02000d10300d030030310340c41d922811103a10007822014001941b2030500240e805a90207840b00404c00c01c07036101460380140b810b150724030818415000d80c00d22605051010b1095845010164032864900030301c1e580d85050400c800018581030088018160b01d50b03032010005050300500c07a4507001d0020a19090242003c030b200c0e40700d40304014421200b4000c5002c04214041d046030207191030b041c2915140b03025038039609140c10a42e082441d00c00c000013488025006035030306e5801400300f002980544420b2100d04801200d03404e40c9880c0c1040410445800075411a500000140544105490541c0d0702c6401d1601e00c0072802007090b880542c0e024519040303a1008514600729010400d4907000030b406000010300e1703000c19062658ae00350000c5200031594001301c0280301004000e503140c0e03210301c40064601c0c1c40d0003030034005940c09001c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 923571151 1250 923569901 923569909
    0x2031c021c050709121a070503040506091f0f0b030f0706030b06030103030801180209060703050316080405120c07330804110405060d1a160207180c020312040f03080105 74
    0xa000d0150f42e99421011403c0003c254403102090303104a40c022009400b1900307100c21030030520300802141d51015504d0803d07041c110301d80712000c0c200085507001140034002d10280ca0118000b4206204e4011520500015454004003440c01d40c5a40500a141000400c040d0100b45138094030440d4074104070303000e108024440607020074080180800c440324014003242d800341625051094112801500d84140b042c085600d640082004501150300030080c080c08202e0100b0814000e0104d16040c90f00e40b030151100713943c038040310305d02c07451807400040d400a183c4020700085015045580400c07031000d0601030b0440c484115194410340381c40e404a4907001076413281040c28051500000342c0c1c007003883c2417800c2000030030340070b415968484044120100005c82c201139807484501c949120b61518036040058841605003110303c0011174101d101c00317200e03140c003c00703401f48481c0105e0b00029540340d401d00180c2c5140b00303030640143c0c0ea99918040004003c8007411009449121f0b550b0700d140399903103074244 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 923572401 1250 923571151 923571161
    0x60911120303361002030115020d020a20030303012603040b07061121010302280e070c020d05010b0a0906060c06050411061b010b012d02031c021c 64
    0x10416400d1030f1007003680d50820440401140e01d600c0c02100210940c21400c2460035103000d14281ea01c54010004004049158030103510b0f01c0c65600190131520480c50b0001c0d200c0c03410000c02071103400c090380c0f0080c030310b290307a03585510010b40a0103c03503680d41c441d0380c25841e45101d0002e4a215002d5070400b81b000800200c150340c22108504685810080b49980d1710b000341000701c3c84881c5010040c0202d14800035200411044003a0003140d0103d65411401400000340510a8404100410a280030b0b0b2070200d94001204494562408201940b40c1e140125500d619078030010758042c1201d8000b8062010661040074416012a00010344c503584045a5003a038001e4818403011441c005074030b5005c5601034200f1644180710740d80310009101010006103031340d08820807440398130a44041c0302c4428030091148414400c402d00b01000240343e400041d8080510b8481a00d0342a000707405080c1241c0e0080054454030843d111203041012111990071000790000b51101171443c2c0381c8440e00107503040314461 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 923573651 1250 923572401 923572411
    0x307120503040b0a050d0204060f080a051509090307080307080f0f10091d010213301e0204050708190c02030f070f0501140106170c040e070507060911120303 69
    0x107503007001c3ca4500501490703007010400d079040c08020840845000ca40c1d20060000d4003040c0c8030303850358407405c1d4402440f4900007000100303658513010600240404404c5185039a003022a180216a07031103413001030a6001d003020082481c0703004010300c0046a00800b54910411345204000043c4e5500c03e4411004242640c400c08081c2c0380f581c09102e03044a9400845e238841501400301000c1040041c080d00b245d11510000009442d202410300444c84d060501c00d05141c900c8480c603c0f50741c584400d0b540d107011400d0b001082c0010409109500802d80101d00d011241c004004005901d0640c60183c5031a5040714001c160101411024015031818800c1d01410000d640c0103504240d00300001101503400340c40c069517007840c00500e850005100340103124070040c0f8060380c0501c5514045010381450900070180301500e00708810025070b0400702c4191002c8400c04005030b00c1d00d0311200c8094440e841800d40262403241424418000e100c03a601d00c0520440080c1c03141307001c90114000c0e594407808241c40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 923574901 1250 923573651 923573653
    0x180307030c02040f0b1302191805040923101107050601060809160f05040e0a08070602090a0305030d060e10030f080c15011401030b010306060503040201120b04020d090203071205 78
    0x410002d0304150340051584400003500140244081d800140700d8413080403075184542c1c000528040d00e100c1462000c0e500406c40c205800f441c0e0408040804032000c600035140520796030107200052007640305a0101d00c1201e46000d49541c05507281d02515001c00c0019000b08030b081c001864001200d603c12141e80642250144c0f80b581d00380303e012500501c01400b1180c0c3c0703214140d0091009204060500000d104100c005401c16151000344000e684d00ca0072540c002d03410031800480031455050440722266801540185e8070405000090281c240302d03007002d4190300c4042192000c0c4001640b00d4419100840c2440ca15555051440050784403207000040014041a000400040300c2c81c0140102d4030309040dc2d03a18071036400203040d14401c0264002c00d0320740c5c0e80e03090301489942c00d0f200b10310540d502072030103010302d0303040c02805840b80c030003d400241000074140080140d01260f500c49600414004d200355034900841400c4c1000d08940d001c260710038080c4500000700d040e0103031a403180392680031f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 923576151 1250 923574901 923574917
    0x1f06050901140403082a01020a180503030901080a0e07090207050a02041d030711040b06030f0709080102121311030102130611010614090702010b0d0320060c0f090607150518030703 79
    0x351021103180e100f29844108441406c0b803107140c8040a00150044039800e40e55403032007040d40b42c00b0711940300c3d0300d030f11160080d0010003000510f664028210345d88920010404500c00302c544214500c0c02c0c040f9403102c50200d01c00306440081040c04900c02e4250350084034180310000c00c1c490b03124951045020745a9659004010b440c00143d0450341901101c6d00051000610020030000701c3d946078000c68140b5590800c003810440130f5500105202c1c0540a040300860070841388940c802506030b400741010091011101c0440100040f02009034014100900259210303440d0742c440413140005800380350042042200d0b6503100300014890942220a44200d024134020302c80e040c0480c00f08060000021552600c240c0341c1d50707881e1850342e0300b882c1d840b80d90742118804075840302c04208420400b0326526a00460180a240d040580654480e07807002c0761116692030720100040e1103842046e00061802d1000246281d0301c07052503000c0c6204032690200f000d6038000914955880c0d00c01ca510040c08140c00e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 923577401 1250 923576151 923576167
    0x270f0a0b04063b03070c1e060c080d0b060c0109030201060609051210050402010c06090308010306050c03070827070e1617311b0801061d1f0605090114040308 69
    0x100c3c2c61040d005604090741d28001c0a911040384c0ea4550360070410b086010100401066007112041034020032040c60007101464040d501c09400d4412451141506511003a8107000e40ea129000c4440d020044030080050307070506c0c640a0301038046e600c00c400c0420f0001c1c0740001c460408030000300307181650001800501e020058500001d04000d00140d041001c500340c03075000502c0034420a543e85009403190b07035281d855403820300182c038001000c490f022041401401403903a008030303c482c0c101600000300300303400300081290021aa141d10003100544142207000440c546400c490314001e210201c440b9084034418002610b480071144402c044948114000034049072250ba0f201d1486008004040d1440d0040100b0314000c481609007525000044491340c0c03200302c0041350140090040368024002c135446c02c0400c504084070324406818002113103000604c0101040c00c1807010914a030703801c1d1000c40d01c2d0f240003082600008481808200c19010700c0d065071041c0010b46084940c003680c290f1038881c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 923578651 1250 923577401 923577491
    0x5032406030f030d110f040f090c0318150e0304030308061011100507030b090a0f0e070503210d0608030c0105450d0c0204060905270f0a0b0406 63
    0x203a54010004c9805c10b0011400e05080c060061001b0700c0303c1c01110501c46d09103d40d54003210b200062000c10f040c50203000300f0008520500200c841500a2a00e415641004a6080103003440101d014003d00000402000f056040030b50b050040c641680d00c010380074001d5070241e90b070140040718038a041e800000c110308903040d42d07080503034030901c586000304880180001103000210140c44c151444c0d03840350180c01102e0b800388034400710042802e0091250504d00740c00710782c64801d44050749025600458450101c120104111918a90710a2040118582e901c20042e12a00400b28025081d4208000300e00c20282c2c0b0450138140032048079503500301c1c0440d0001c0803500e01d8045151040e101310719503c918800c8040c0140800748145803580c1300c1025241c8100030880d80142c000c410490700c0d003418003c44034a0840140f124a498280340301c4904000004130b4500f0304100070910140c03243c08155001c1042000074030340207511460062001a5654150b1003205400301516103880c42003442c00c003600346c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 923579901 1250 923578651 923578661
    0x90a0201051e19050c190b0106050711060318060a0203010e06010c0303091b06090911041a1b03130905040222181115130302041505032406030f030d 65
    0x110b0441e0740c038100c1540b00316001590301400000c0420004988011060710911140d1030003e0a20003240919016540b0044140010300030841001f0000c6035140400c402c0c0011305a01c1000108565140d18119540011110700301c50300e069940100004030390b0416990007642e050321011003400b140c1e55a45801198051030700c0c4c405500f015200c101017804203e8800c140d8071b40020a000c180341036420301c480642504010380c001001540380100600325081180700707031010349152403a0743c0d85001400c001c501082c004d00021031a100070030600c038007a15000000900a00740865000e11100e0b03a20110503040b541c0855010750415588010440618000d15000700c6100c0402000100071040d11504400e050259400300c0b076959000034100c1c07c515040703000c000403000b0b10000342d282055910790140d003103880d031000a010b240c480f084c009841030750055501c0a88009006c03180d0f40000000204051460861b80750809140c1c00082480c504003c01c00300070319841b001c01149004102d41059000704 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 923581151 1250 923579901 923579947
    0x108070605040b041202061210080c060a02250506030703141602030319020d06030302070513050c1602040b100509150901020c0f041503030908060f06010903030c0510050c0a08090a020105 82
    0x7c4041040440074007520a20f10b02910098290706901070600001524003255034108a100304000c0c402f003a500d9900140030400030701181018100d180c011501c05641a05a40019512000210420000b2a890740c48100c00c03a564812403841501c8090101095071280150f110060300100b0018078540040c00040c070104812030130044c075000603402c0140480c3c4131604204e0058024074010803a0b407400360326803000340725080820421404c00e84a154501c0c8144004180105229240d590075583d880c0e01600d1180703009800070320450801e000040c5203034800840e4a00c950041080310b0303004444102601e40311207041e00200800382c290410400403e4500016613400342d1a5040c85024804808185c00103611a407145209541048511070501500038030003201034242d01c01700a04c0340c0c3d003c1080030450350141040420030307030f83d070821508044041040440301c0741014240003070408504010590440d49594008098860315001d9455032441ca0b03019001903402d101ea400ca03500c000030306800103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 923582401 1250 923581151 923581159
    0x30402061809010f0302011d1c0303060b030a0b010f0c0b0a02090a1d0609010602010510031403120403020c2b080307020307151a030606010804080a020109050a06050108070605040b041202 82
    0x40203074000000c030064000d0b00001e4040c20103100400443d6040650fa081a0720080f9402c21420030742c03000300c1d405a01e0a181c6c0345c1c604011806440034540681e1000000d04243d545d083d9076854007148a1010301414419140000c21050040081610401040c0f078036a60041495405807200120358003e90041d250480c0c0c0711400c0000042d24038014200d541400c045480f4103141450103030300b040800f84059000c881903905007000c01000280c1c1d06030b4601134030b5024070306080105c116400c40b40b0314040c0f2801c0d04002d00ca0340040c00300f40b580000d180c0070780380400c031004140261b10040c41841054a0a100c18425104149100001d810007011755444495803048a0602855884003400c410540182500466a940d46c48004d07041d103070a0321800b440d00b5002070901d42082e00000b0829000100301401011000c9641c6483c035200b90422a902604042110301044040c10404010a82885101ca251244060010301c0e1801001a078040301c400640f040e080a29084030b280034940c2040c012130b88 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 923583651 1250 923582401 923582437
    0x606091302040816080703050c13091b03120f080a0207060e240609010303120c02071d1f031e0f080d090b010b190e0607051f05070309020603040206 65
    0x3540540c4007420080000300c1c0205012100715400c0741445499401c0380075180c01180c000d10200e0000290300301d502201340d4035084c960200c1102c0c040200110480206020b40b0114280d4101e42c01a1078441607034007502c0c0500c400300141c441562850700005584021580e15000140031982641c0a001c01c903000d05004565055010f00260600e0714100040301615202512524000052102150f1141080c0c03030f081c180754156107024111042080440c803401e621442007803c994800c1c08104010803220700000c080510301c60320000b10b240100c5207914400d90012601c8840200c050341e20040341c0e041010107028000b010090246050355841c269440598112004000f0350740710300074103001c0700c01c00000481d41c06924107400c1c104810780c0901e1000c4003c0c4034415003488807101601d00c1c50380d181021f41c16000d851001c95210300070303000040e049008a0250840110104500c1c0b44c05001d052820095641d0b81d01301038084450503140030750842c0c0280700042c0142000300081000d0383c00c520304160313 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 923584901 1250 923583651 923583679
    0x60f37080d02030a030c0503190b030f062403070302060304020d1e0c0503060a290d0b0411100f020a17070f03030209030c0a051c1a090d08010602030c06060609 70
    0x1160450441c940700059000090306180154588600c0f07896000c2803604a2030750614408812040c4989814000441e940b01c680780c02e070365000c000c4070036103001440c00c2c0c4a540c07829008c64403034000204002218004d40c3c2d040e1f03081610700854500240c0381d009008904503104e80c4c003032024908c030180c8102d4071205481c1c402500440944e1203100001e00c07035401000c1d081c2c2803600349414107001410303401d215802d103481c0852680700c0300c03608242d4505c040410302c403c903007003000551000c0a0043c0034040020b082c0030f20041c071030107804060a2716015118102601c1403850704980d0404640300c3d0f1801038100b00307131040006540000e4000c003020800c0d50941400100c0d1664543d03540e03510011008254006034180c2c3c0f905042c0501607443d00129481c4d8111441c04006c144074921070441c0c40640300c84d04104404204582840c200a204080003003105442d140d80340c0f50342c404010001401082c040e000001d1140d20003c00c1700c000814086c090012030f1614424451b09402042080b0f07403018152a440e2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 923586151 1250 923584901 923584903
    0xe0c0901060c14010e0d1205091b0609060d06080c09010602030703050d0905060a05010801060b311e031505041505091e070f060f170406140708060f3708 67
    0x8505008000500a0086e01c40e4020306030030b080102c0791001c242040100320723500c000410403408008280303001c50094545d03070380000c2d900c2c400c8130010703680184049540004208550300207000e80e0308240840f80815440b50401000e400240716400c0103030300401030380e400030748114082c7c24506038801c00441d44641543c1d80506280040352008030f160b030b8800040000303510034042e18004242c3e41030080e00d4010102254405400106401015000300c9800d10480051040c408802040b000d03031041030a01041e004c040e40c4285500c02a0703060151284990000e100a10526009543c40324070083c0e46010042e00001811004000002c14000d110240ca5145a1440c165010980b00000340c4059801c00c1d982203400b68054101e81e0402c803505000865854000c0002c824034403403903011714019507407450010040e20145050781e04105548040c490255040300d201805002c048480704407010f9184181300090128449003409070f660b400b450300041310300e28403070701d40b03042494070031000c40340c40d1020300d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 923587401 1250 923586151 923586161
    0x8070c090e01020a02071a04060507050c0301060612140106170402010e040c0507030908030307140c010e1b131b0e010c021e0109080f0705040c0c0c0b0d0e0c0901060c1401 75
    0x500e41c681d400080c03820609034144005000b421034020b00e044071542c100c0d40804940a1801a1810b2000c00241078060000400c40c243c80007100400070b002058440c43c0003043e9442c0c4c0121017486504105401c1d42606100e0002030680b03071207a503555000050032152818405028105905004620900070740640380c0f80240e043c140d00b079071120740e511a29890f00402d000010f41c0701c14500d80051080c4100c00307030f011031040c2e9228120703408980c8904100303003030780d0040901c2152681c161140b548600140700b900d1000750305442003141d130f0021807180c500b104c1c4c00344c0380d00c0c0c03904030100706003502c0320b003829030060010300c07186030f418908400c0c0507100ba4042103d400b0070f2007210320701d0304030109010780943e801040c640103007190a02901a03418880302c010b135150351030701400d40310b2a1200c020019039482800c48c00d03101070704414804003a0f60780c0e88600107141d00c1030f00e200310350508015640c041103c001859840c036001c050071105031b0384c0c80c1a60032a086070740948203c454405501c465012103d0074021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 923588651 1250 923587401 923587421
    0x1050d030f0512181501030f0b1008070f06080f16080c0706060311030c0d150b060d02030a05010807080a02030606210a03020c4e01020c01050108010c031808070c09 72
    0x280084e81010f80c519a00c0c2c40e1160700c41310501c0a040e401030001902c680132107030200d5404114501ca0780c039107800d1408190710503007000545200720540004c4082c4907a940a0485000c0d8417002529180e018050140c01822943c0c0c0c08011484501604d290b8460104203a20880d44240315050410560318030f02a601c403070380261001c4402c2d0302615560310741440202e50841044074400a44995580c40c050200e814440f0141a21b64442032110300e41c035450f04480ca00c844030035045690303161002c01e00c030091400f1b00038a0a5445200004148000005820b01030550010010441c0d5070300c0c04100320185440081086801582014007400c1c0d000c10055100c0041c030036009841358142e10010f00c0154054044100744048480300c1030283c007c800310522200302c645202d404207842040c0ea03c4081c80e00541b0068825600c00a80d18503005810752005050742c607000001d0111290305281181580d0300010660b280c040c400c0810400900d502c030051850b24801c0d103450b610181d0354559a0101ca0941c0d00d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 923589901 1250 923588651 923588671
    0x2100f020115060504090e1528141f08120906040b0a1e080c0f07140709090b01120302190f0503030f011e060f030b0109080f07031a01050d030f0512 65
    0x605110340b480c540510505120060b00401c040700b42c2241c01c218880014100030518200214180c110b106540552700307003540c1c041004d208003a00c6120700c4c1d0444004907164880d806000c04076103400d03060700382242d0407919000000c04101095400c104c245500c02010350703501c041304000000c0e1041401c00a000b01c0c44a41c0c55480c0420141d0b0503880881400600d52020085400108418442641c0c2500c8064254183c5591034049514003e448a02c944c03244d03070b85500c01c401c0001000b40c02c580040c040ca41c41114100000d99175130615000d403409100b4020050303040f0a940b0740b03444425449004007280104500300b80b060300d0351961403c4d41c0c82a01d100c007119800340014800b01808031040c0c00035801146080740000d180c1a4018405001034023030710200340d2180f5066006a1003500480302800805040d50744440000040c01e40c0c0c4e2100f031008484101156040c2c040710900998200e040300d202500b00d0080710466541120350030207000e0f0100a102d028000030121348a01ca43c040d00c503440e404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 923591151 1250 923589901 923589907
    0x90405010e100c1e0e040501030c050a06030e030301030308100b030a0b01030b031f0c0c1502030103140d020601060f26061201020f0f0d020408030c030a0e040902100f0201150605 78
    0x2221240c1070021100c40e2070895414403c10082c0f469019603e14400307158280e6940101c21200790441d000303101d07602c1140c0d10a08260020090001300171070300040300c004490303400c5030b20f940d0401038003501d40d02140c040043c1c20034001000420f018800d00d40c0c0c0511444032504000d52603000000241d0400c3d00c4044c102d40d5103a207110003950b0140701b0700d810100224000c280c5c591144c548801c42c82c46400303001040d1030f2070f9800b00a60a00416010440c81e50059034400740c0210585d961000b90002d21058481d1100750720440314024001c2901004200c0c0f56014005503803c184041d94845144514030082240700f0b0112000e008159441c2c00b294090310080140343c0c1031903c200081d6041400c034810035a441006254070303908880e000c0b05c02c42810200d981d5162504612241d00030702961b40a48805d010002e41d550380f6444c00f02c02081c0811007510741020800da15018002280c5903804000c0d002044a0708070075259005843c1d42c0840c040030320020501c40280008840e640401c0e5004401080001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 923592401 1250 923591151 923591171
    0x20607080c04080a11130221010f0b0307050903100c02010e1213120206211b0909010b090a031e0501051b0403021201150314060a060b090103020a03090209040501 71
    0x202050780140740010750342d04090900100b0360320b0f4110004001c0010f00c5040c400440c60b180c544802110890703440d021901e40d86141c5084010354008001041e000c040d010020600300c18210158098400c0e00100c54116034440c00b0075240382e480b04094540c50311940141d01d03248030341c9000391500c1e0340c0140d0000c12500f0050b240549001c9000b503015000700f03c180520500d043d00c407182c0380c044400c1c80b09040703112801400400c41c1b9100c0c010400501040729845164004c2c0e20301e0a841c0a007034291071800e000400092801c40c6805a0080701342d00c040d145004010300343e200f50281440d488002c18086030f00d5920754501100c0c140000031101d90740d20300259042480003c1c8601da510070201d055600580c0e003100c1e200415440b882c04024800d800c80681804140b00950102000c98140c0380354036400ea0306c134100022810300d0015030303040c24401d0300d002585048035400b442e02182c800c8071440342081100300054000e5004500b05404051307403805100056510301004a001d40d019030000900ca01c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 923593651 1250 923592401 923592407
    0x91203220614150f0f010c080408060106081501050405010e040e0a03120e160e09030403050115090e03190e032805060711060105151611040501080a02061804110a020607 74
    0x40103180c1580a51035000588058584c0c1004002c1140d04070b4410041170113200050311081c001c080050002c503030106000c60b003020b00041d1035050740c010f42c82d180041e03038440e03500c000c1c02c400c642da085002807814130040100d0f50040c10745601c40c0c1c00040002c240280081c1040d480c0c03c0b000d0100b50001250344a0680c55540c1c3c41c400d1040c1240050080c120748030340807045041400c0c65201d00f051460400c800a2122802030040e600510380c08030081c001d5a0703000308060340c420801c0c02400222454002c034904926000001c55540318002144d000c2c0c400002803066449401e003050380e903014011107404940e8150500c40c04001500340c5082000074840e5400c10030f01c3c0100080542c1c0034828902055001800b000500c9070440c0c200b142d40e580c032400ca0201615541c042c421010603548100d82e4504200111724402e840080c4064030108a1680ea8000072a91119400070203500040200714210004003035100c0d15107e00e8025001242e40e82c401d54102c2d4869020b190080c0041e00316605104005034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 923594901 1250 923593651 923593691
    0x602070308011806050a031707020d0f020a0b0a170a020904020703091d010f030b1f0b071203053105193f031d030a02070504050912032206 61
    0x1d814004011050500000c52604000c0380005811111948c040c2044214103100301d030300d01036014101c06403071451460491920900004120b02c83c104118001c1104020f12050f10f0f81f8900d01da443e80c00011440c0e0311003100c40030181c02012036035000c100b21000368a03030340001c1c0360007813103a07840080340c610340540105510008540b85103809050001048191002e100000c1613a030021f150500a46a144c000009240c29a504032501280080001108400d0801629010303015841182c1d107140c402d403044040f01c50031a608001144141e91000b04541d0250801e81810701400030200600303c0da4890f43d1424200750390321440c3c8040c58288004010070071800c000b00c4100d914040020100d55140807901311404808030004030544410104810b200c0d410401c85000980411070703c00950364110741d2654080084800940702c0c454000405050502c80d16108402c69400f42141c124012085000ea520203404245034800f410007200002c00c0d411440c007462403158100041840701d881010348450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 923596151 1250 923594901 923594939
    0xf0e0108010902010c1709031002300c0d0f020309010b1c3903050c040c02120304060e150108030901030e0a0b0114030a0609050a020f10140a0507060207030801 70
    0x20b414404080010317600302c100d0154055210000450101c1355440b0300700180100d000c901c0d407500c6400642d40400c0955401890482598a50324003280032880b14042e1074694103102484070080c1e14005803a24201d0005040c1d485d420203008210240515200b41c2030360819036100201e039544480100342803601c110b00070055082805510303100681c0d41c031540344010701a010600309800c0000392002c080c441e041e403142140d071003440610003603032241041a42c5408a4be0300c0c40c002d40c505030302d4070300550000840900d08850014180d2450740c507551200080d01030b407445006030740701c0d0491003040d14220b070a42d640a0901c0400540d04c401040c80014165001c42c1c8400126411034002d59001c144942c50141c159903040340e05412628064010910b092880d8201400c4649425900410041c0110b0b03280802402241c008820600c0030042100d115907141322900800c8034040075001d15130a14010380806440390078540c0c03c2ca0043e490b8031003a64050070b02140000e99000050001015140c03d41d8811 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 923597401 1250 923596151 923596153
    0x6030d020703050606060a0c0803042d050601030f06020405030d2102120601180506070803010e18033103030f090f05060f071106040e011d070c03180509010f0e0108 72
    0x50310350340f101d5441c1c000103018140581800900320316018040d2003200e1800b9400089903a491801d8240200880b8041400d5110741180c030100c100088080c92020008503003040182c90164030316903518000402c440340440d22503400748000a15039405210990a140d1151034031038101091a084200340b00951015080c154414403040c85c500c60854460f0b540400c0030b08084141950b81600400c0c100396613440320341d1103e40007235404100050304d0301450407100b0052209103581c172590000c15600c044500078a01c1c40d4001d0000004041620318000a80341d0024a041c050181900080b0120f40c85900300380d0100d1241390a0600407030344509203100070016402007109071402c0c80002145032094149a00440350f0202d40d0009015000b40050b07035084c00241541d680799034071030700b5101320f18092040c550441c0d484070080307402c070560085841c0309404070b64820b0682e40741644c080d0307481c0030b660401c3c444c00c48100c3c0022a46413103460769140a405000310610310149010315845181c54141c10410355 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 923598651 1250 923597401 923597413
    0x606030304350d020a140109031704080f210601090b0306040915050a0b0a0608010605031303021c120b010c050303041e080d020301090b01051306030f091a06030d02 72
    0xa42c1c0b8200790002e030540c00b0310101c0c50007940803641036100c404103510902078502a01c2c0c11401c8240e000201501070601c1041149210050702124900f02c1d000c2e9134002d8080b90403d0000680c1c1c0c1c0c08081a194414401c10f50700d0308182c96082c00c01c54030b40200c501400011048584101103004040240b540038030246001c02c0c2450505044c8142400040c007400e000d0340d210350500040000c0c800241c88501c2030b0754001c021500c1c0c82d20a1801a0000707140c40b60203528180000b24006e4840d02c83d05040c0e5416485040c0303140c98402002b40c54410040050b402c50003040020a81d40e40400003a072441d030a01d6031f40d02403402181c40308d1001c403000c0b0070b03400b4144004441d5140000e5000b0059030761040d04a8855107203c81c1e0540d5503034a01d403c45200500d000f00000b03101d400340f40564050b50680301c03012020071114645400640b1588200c4151858203502080c04015042c03003034020719498010702801103080f2529a032084015803e088610711040301da0b8041186a0404200b184820761040c401082 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 923599901 1250 923598651 923598659
    0x405150f040210030e07050d080d060b0f07020f011101051008010c0c0f0f0302011404050307060516050d090221060a0b01030504030906110c100e0108061212090f0405180606030304 79
    0x143c0c440d1040041c2c802c0c19110303100a0f001d4442445a8801010040d221200c60012341c84c00b084640c6c0140036045849180620114922074910306941118040100051030981c6a400304550341d0a01011541081568051a00c00c0402801351900841120851110700c504000140d400d55818104e05001c00c0500c003803400125000441100d88640c1164041620070107a0400301d003d89903144451164012643c00e01040141c00030043c00020300409041100b81c80e0f03c0591618210f400c048800014801c6c801d0411080741c560100c0d071041c5c03005003226000040d8054051241e101d40c0c85d208415085201041340c210418040c1c1904040b00340303004c02051600c0e070740150100040340280c0040220002c01105c103040108207035114103070010100b4441c00c0c840d6000070540d400c2071501d2400201e03c2e00124007507007031404440a403900590003626240803602d40302d56440c1c004e6802e6541c40031601303a200a0507100c40c450b090050012110904080020b088070340d2514501a1045e402588204001c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 923601151 1250 923599901 923599909
    0x270a110f13020d09020414070f090605030c0c0709050901060f050609011b030207030515041a070207150e0d0303020a090f030c03060e3f0408071203090e0405150f0402 73
    0x14004803100790005032250201c401c0e05008040c1400c009411034a00b00f0982840032002d9002c0c1e1040c10300d0f99612903511302c088002c40303c054580c8184400300f0410b20224001580050203007241018890480b1000360703036407040000340d43c008c0c1c91040442c2d55414092203400d11150300707900500340a680300d62401c018100005c0a50f030950385005048001c403c0d1440815100f84010001181c100f0129105041681800042d800741950200d61400d0144c4038007164020100b22540b04144540180030300a1801c03490300c0d802004044000c003040f002d00030b00c2800341e40310119a41514026600140c865a0060001d0305184168002c0722401c04035400070000550800c80344404e881c1d1105022440881c40100c80346070414400b99622100710000b12002e9003210300300403101d0003655081504029131040009034891085000b042060340086805002e031103841c03400d41c0d200c03e01c00e150070510f10740e43d04901c55042205460480395600040c0b50304080d6055010741640210540402d001d59040c44d03030000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 923602401 1250 923601151 923601169
    0x301060e06281208041503050a1a130e1f090c0e041502093c0415050f0f0303040605034309080307050604060f0501050901030b270a110f 60
    0x840751a0303800104040030440b04c6802d8800400e82e0055825a84a0b5540081d0140000300c0784460568074044030031848010120250f80050400b510a200040906942e80f02030480c07192004001d205403026001e0200d03041d40c182c660350009810001e60040646403101302420b881c0c1c0601c240f41c0b4240c3c00e00021484030b06200c1d9104610201c01691ba80359403001c40c60001d180c00f418942943d01d0462444070902124050f0b100010601c42c9036801070804040004907030b00541400645541c40d01c0c180002d040c4451001c414101c01030a00b84154008130000b4650b501039001800050808820b00c0510030030344803503003800c011300081c91070320540000302d16442c0c00c2c00c0109214562800c41000c01218018440403020300750079010740303075115181e04080d0742d82c080075038046503030034505055003c45080a1140b54180e420003408900e2507445c5442d40c400c403190203426000d603e014000000a00703a0402c402e400724500600191440c80d03028103100b8807000170f0094241c00740740700d003000320a10f03070f580052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 923603651 1250 923602401 923602409
    0xe010b0108061c06061203030b0103050912070204020c0106030203010504230a03170601031b020d0206010b091f050d05010f05010e1e04021b0706030603020a0902040b270301060e0628 80
    0x3480604801d130911501400300c580c040d8211415032280041890b03455000a40c5801e002e0306c0601040c0c98100c1c101e5540d148178207220304059410300101d00145041d800a1000004600003c2452907c4c1d80010b07085403019602211310a809801c0c2e400700c2d20000041341c92101ca860080c09501c2c42645014146c9a568056081d05620340400103555070f0280d4003616401d042c042d0802c244021200b40070359030b00200c02d0024003500c0b80c07100004070002000125002d401020b00b511410031040540180c540380c07003849038818030200380880050b0ba89548034031402000c882c00a40011442e0100141c9412000c24200e800f48049000c03403000c2801001860b09403201c19940141d0701c03400c1400040500001c100b11020900680380c000607600c0c1e041c0c01c800c060724002c49003480a1951482250224400c40c42102040030041c40303904510010900c00c0031030f458a1020848001c140480002d0840b0960303085120301c038102e9410701115080504030b4210500b00b003180710041708031840c00b2141401207031207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 923604901 1250 923603651 923603689
    0x906090402074205060303040e04080d0504050d0e060702010804140307051005012408150a0b0316110102040501080f0709080f30030402150f0d0e010b010806 69
    0x40d84004020070010450034440c01c1c0c0626514140030024205403520049003200c0c01c902e0b0300f42c1542e40320101407080f44d02821009000b5172402d840d0503028400e1072002071050b10040c0080c0851024603103076024061145208201510b040f442000001c1c6c55501119103250080c1000c0c415040180d800c2041c041d0410b4205988821880702d00c039800c3e14604c01c00b5170013003581c007030a03444080c04550745d0480ca040e288860042e0041489074161031801c4100144800005030b151400b08800903c00040300a44031b00c080c00481402e41c855141c40300079807081d90b0040920180e10108240c1541c004540104d40303c01100a40c50309282c400000c0c240b10003d04a950301510308400706020078092030a840081980780d00f5a80c040942c09481e03515103c082c04c240c80103520314403001c64190500e190300c2c0701c2454010030007800d5443d1034007489051410088034101c02042001111607503062107010b04503403040c071a0301041c0345120380e40d010f082d10000e441090611420206120155076a00c2d84103001001441e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 923606151 1250 923604901 923604907
    0x14070f170c011a0f2215172508070605031e01061d010c031e0207090204091a04060f030206030a1506090608160e1216090902030f01020906090402 64
    0x5180030300d01c6041c216000079840c1000311088020428140b10360560100d40c440c584050b11428000381d4000c2101c2c0c0c0d40103442d52002c54120007281c2e4040082c144007002804041d6498011a00891b9071600b010051a444448803905503105a5142050501c000c003c03000345c1442e241c481c039a038203024000c0006011b008000a00c800e036031000d250344901d40e58855103283d56566000504103015001201d0020700b180c0c00782001030b502512070700ca40f1a0340740e03a98030f044000c9a09518020a2154601e10850242c41400078400445002800c003400c0300010020f10f07018402200300c08403a0042c552402281040001c10a000981d000c2c8011290155a0300790369a40c1c07030b0f04405c02020711b40000c002c000c2c05503002003801079002440c0c1081c1e480d66140c09006490301d40c140c5408601801418002a14881c48400203040c0081c0103001070b02e03071000726205694200040703000449a40c0101c2641ba43d070b081140190303d410000019110002c800841c0303012a800c1c0070411074460611058080c43d000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 923607401 1250 923606151 923606183
    0x100c020301110403080903060a0b01020d1103070f1401060801230612060f01030212011a1306091b09050604030309030b06120d08061e090109052a040614070f 69
    0xe40040c42c454110090456459840780f0382000e99410480f4200c0c06481034100050400080744900c442401e816001802a180007031811507901c100d082d10419940410b00021700025a04461144014410500202c1c4003440c80005401c441c80e66208880c207a04042c070403a1506543d0b900001807900b00d2400c1b030560307568a00403e9981491400d10b003020700c070700750410451519260721941680e00c200c0318450619181c03c0c51609a039038003041c4e01425400340601c102c040c54280d034120190840f0345404203106a4404408046484501090100c20104844541241d50000d501c4016150450f0414207140c21510000d01c0c060b0030f408024101f03643d00d00850f40b00c0e59658400d100500041081707801e015000038008110701003d940c018055103a905040450040304400b4074030111015004074a16840e00b206c41014000c09000f210040c440c2002c0c5060007240031400c0310b20501032046d05542d42d4a80300d40140100180748030882c170b540381440010b0002d1300802c07410241030303002150010003c0360 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 923608651 1250 923607401 923607403
    0xe010914010323040614010308120711030d15090509120d060b1c0b06040b071b05090f25050f09040f020310030b010503010e0316030c02060d05011701060302100c0203 73
    0x189010a00c003918601d92955280310f0600c42c0510951240c1e60074406810070038138a144000b030030700004086440610500b100810400300c0e10354098070600c0e00c0d13082500d48900135400c50b8820702034140c0b49915182401c519549443d0f06100a100f8600b04220314a80885415120360000341d02c3d140c42c50300081e41740060310072030700024041d2001c09036280d910890903440d400030200b00b0812980460500c0031a5003149048010384049a500300038403071502e04144e0390703107a000240c085802c20000c01038402040301c0d1280e0b040c9074800d06203148034121a00304100d4054034441c464007035950940680e88412062940542034690701004110001d03100e0401e8000680501740015030100400e101008000c2070503886000e010031607005070400c8150341d8840c0249800e95210926000b07681e40100942032001040c9028654182d0007450f2070402c086455001440c6540001052070205846030018031040c000107201e60114561035008210030b078516400705071000300b401074103c24018200316403801c2d520 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 923609901 1250 923608651 923608661
    0x6221205040f0e060f03010e032a0a030903140a050d0503060d060c080a0b0a140f030307060e1605090601090b1c060b131e050f18090c09070e0109140103 67
    0x1510702c91108032140c4403c10515440803c94041d440341c184e040640140e4103041c070410800c4400c46018614014107100554800d40403507008404840b01036868107440c01d003c1c040801c1e16071080d6221a0f00a00d1410407103c000064985e020300d640104101d08c00040d000288266440c405040258032907550400245c0058660200a400c1c035007840d52801c0c40a0340109005e01c00e81f002030003042208003280901241c00f586000b102c40d12004444101110728201480e040c043c00014100c81c545a100e07a19070055942441030058954401c40301c05161080e4080c465000c2c00342600d00040300d160000c0000d0405a1ba40709540b05504001b550780030780d2281c0400c02c504106408001d1100e00d50301e202c2000c40703600010000001400a240c00b080000300280f0000c45e22501804544e1450709280410214a03c0180c0c030300d41c4001442c4a0bea0b050b100100000e106180c1d07070018205a0300028144045030300c00400c26000c2280e12105003c090784c12070780901c15550001d464081901c0341c1001600200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 923611151 1250 923609901 923609909
    0x50418060c020109021215191806020414040506010f08040219030c0e09011b030c020a150b04050106050a050d0f0b030307050a11030a020a03060c1413080622120504 72
    0x141000101d41c15142c05402041400d4804e8a0300d8074856210420f8a0b19080b203019000c1c0c98034110700104105880c00c12104106401401000644000d0703480f1100e10000040000c540c1140c02040030003581006270502a15804165420b104074581040000c005500c04c01a480030b0280060200d002c0d91600e0074a01051001034861352207894690510404000080c41920f04c080401c400244402d841802840c0414402000842d82841000700983c060301d899055801140319400d511000b00f0448410400490104400007850f0440d20043c0710580c1c1c0160801c4050200811920410540c0f00d03040b2041440b0b90080010824260300014014102210000b9070503c00403400505010300810008076542c03041c0305004280300310b441415224228140040c3d44104110420008111030f0b80181c242d02400d482e01941e2000044141420f80d000b2001b40e92074011107220501000c10200324568200170381028420282c000d0314480c80301d4039400745000706418054508011501d00802c1990094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 923612401 1250 923611151 923611163
    0xc0204020d091415090a051504060e0105070e03010b0a0503070909080d0c050901021603050c010518040908040f05010e061e0c03030901020d06060c0302060406020a0c060e0105070810080304050418 86
    0x221070030030703440c0d9851102059810301e070540c130ba021400c3c030040000c01c180e116510801600b0408078140c4005080c0d00d009000b500c80c5c80d1598000b121502c02842524405e400681790025000c5064062500311048001d0f09800f5556904003404103a42c0041c0f400c08880440d20086991072062030050102d0040380030030030009061080354a542c5030000060040e009080e822118030741c1c40403242b070380c4041051001400300d812044030b000b05544110010700c9a0446010504210307858900070404403a00741c1415a1920404201880040c40d0a8401c13001000c00b440c1c0440081c1c003040c005001841603440d0b108051610000b0ba42d01d01d02c444041d124950261010760343c4920b05800e01070b010703501c06080f040c81d080c900a40854003a000e864101900c03600340d070082040e5540d6927a440003e41c0502805006e1101d031284810018416001c0d074501115080000b05040c101740001030b0000f10042c1880794103d0442806104c104000000d450403036004030b9010a00400b268a000140042e90074041d02d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 923613651 1250 923612401 923612423
    0x607210e060903091518010513120f06050c040803030606090d0b0c040e06010f0f08151c11060412060b040f09050a03080708130605090f15250c0204020d09 68
    0x21800010000d014424001e9811003202680d031030f111700c0715102e40d100c0440801441da4540e4060f5101c0e9000c0d2650311480c511041c016600c6c1c0780810380040c00b51008844592031030305240201b00041c011a50861610022141002d04003c06c00707440e40001010a800b502c40420071046aa0b04c003442804141c0d0804115401030404404103102039106002d000030a1042c180030a1a5501c0f40c0300301c40d0000012340c0c45007660346800324107d0b40d07228045d160010f110301e0080500026550750402800e0150b098003050036100e40f501d491800f00041030406803207071a00384010400c4103040c0c001d5211190b4000320005006e211400024000d0604246605000d40b40c02d040780100240001c0c08459140aa1507101650307850351821104020215513060441940c194284001200d03078001a800a0100040d0f401c0442507032802032030400007850301c0190200100901c500300d0040c2003000a0404280a000100030345a00042d2449648560080c082c980c00600074078001410f40c410001d0a91000501e42 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 923614901 1250 923613651 923613661
    0x40b0309030c07050f06040905180105090c03160311010c080f210622022803090311160b0306040b100509010e090402030c010806011b0b10080607210e06 67
    0xd626040700055500b90300c10030700042914603201c03e10b240103881c002c105600d024182510903020f888003074228122103442c1d04c1c80c00010030080c06103510400142006001c46c41206003054908200000322a0b2125000340044c80400c880c410718900700e070340030700f499401408640b03820310320f622606c280b140c0100c00c0031580580842c03050400302110011300551000319240e41080080d4510402501150811440d003030a1107090076402800094141850602ca1019a10404828200f07a0481d140000c4d50743d1440004054002203048c85401501d002031004034100010068814414020707040e034628040001160f541c0e858208080e072503000740022032007000c5060042c0042c1c1003442c0d80c0e8041464807910700404d050000c0068411a0001c0041164025140040d540c001d07001e0801d604209070404401c810201c00c502c0004650f21440140c0094600250b8401c030007846034210701119000401407003589503110240020703413603100c101e25160501111008000f808041d10844440c018001005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 923616151 1250 923614901 923614903
    0x910440420183d060e13020d0f11030c03040807140d03050405071502070e060414011e170c040c0e180108010b01020304030201080c071e110f0a1a0c03040b0309 70
    0x82c0c0b560700f0241ca408601074000e070004030610220b09a80c0c1103407000041c01c0050318071840303081c04020b074050314212000c00c0c1e52903068141d900950300303201b1141e00d5038141d81003d0203500c5425440e1840c41c0c6418210704001e1400a420b11029001074600d82003c0b50300c4007403142101008020441104c121020705c011210007401800341120160703a0b030301414000040910091650250703607500e90b03000d800520300707007a01d00d4640b51002c0c1040381c0040e03541c00c0301100c1c104004041c90107400303200c20700d140a0103000d820580c2081c150b0401d840403c07084010341140400012140120001101d010404810420301251091000250b10398054403051449003950034646110341071311001c000074031004844d100160707a203108521000340000c3c40340300001d6005094101400c102d9100e80b49620150611084e851034042c4290b00a41302544110024440fa20f402030300c148803c4019034044c9646440c055814884c02050b600d180703186c050003e10701d80d240405008072000f6155000450f6100d0810340324003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 923617401 1250 923616151 923616181
    0x504061203031506020703021e0402030123030c0a03020409050c03010f020c010615090b13240201140108070902071a09070e010812091044042018 64
    0x80e00400e290507000d200c2031243c1008202540c1080d0024507070640342d54240a82001d21551200343c0081500700c1c8001c41d030b9a4001180205003107a013441100301c0c2c0161502d00da00c41008200e102c4d03032010300da01036103865000307103d8112901120b00190420681c10b00b142070603000314003541d00d54600650392191409540c05001003d1000d4000c100450701c0d6031032100c200c1000e01c107a40108002010070400980b0f00c038001d21400704010452038110360703240310350031a01c04409807040c1143c2c2054025440554240b0800c0032034020b804108046514101d000c1d0303102d4075680070340050103400155641c144a50042301d100d003400c012100c80c060389040e44205485130840d02500e14404007210000403861000038080303184a5280000500c0c00c850700c02049041c50060005005001e4803544100180341d01c49a2151400c1c0070141d40f907005280c40518183c008403200000b000c941c00742c030030704c0041101c1884003c1e14404d58004040d00c9001d580c00516801c01c0e42c1c07030380d04400356103504024540c81d214002c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 923618651 1250 923617401 923617403
    0xc01230904052e05060306120f16090c2f0111210f040503040e1306021b160602060c0307092102270619090f05090d020303010609060e030705040612 65
    0x40c410f4403400c4400f0100407004180b060590161060002c207202e80f4003000c3c14030000382071800311501400c0340074050303043c0201142016111b062600007004003016500800c4091491482c064588102c070400b04103c01d141a468940c100c00090b14001c08200b09600840040403500504c5859045e0690100500034515030300114090803000071410381000010000e010340c1e80304002d10b041906151402d01d89080c010400703c8454601018480425003a1000701081d8045172200035552115480d03240c40c107016854403c007450303a20071007003000b6603010030701e05e8002d50f21246650ba01e8680310300440e40400243c20903110441c0310042e055100c09044503420801c1d1095a1801c00d407518650f1550300e1202e000041503080180b40b00041f49450003030000500441c0d0b424a8418054559034040111200034940e111096503460900507861400c00101e81840c80510040d880c560414400421000c5184078407014000c99858040107075900384050070252901130010041541c1d00c5441810301c40070900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 923619901 1250 923618651 923618701
    0x60a0c1407060e211b2404121b240c020616030b0f06030a151215020703091503060e07030902190509060105071407030b180c0123090405 60
    0x801c0050304156848511344003020f60222400c00c03a1086a518641c1c01e6400d50300024015035840100c00d400e00100b0b00200d0291802c52045071410f85044100340030320040280c00d01a4008010780030264a0303880b0410306a0142c4d010b200582c502240c4500c0b00e2035008040c51032410508000031807a130000d0b00714400c1c02c10f00700b18150000114015022100c10415582d007201c10802400303440c0c2450002140c114915840011b0445041441c60010021580148001035a030709a80001d0010340550341c5000782e03110b00218a026081c0d50058400d1825100c3c415801200e02c160008a500035803240b801031118058001441c42c01d200c0c02001000a150220f102d12095986030040846040009007542c10161002581785c407100c006407941d07003001000302c0e014800d10500307240c10082488880020b500c15000010b45007081301e00c1f51401c607400810300c14241e0015100c544647c5e0b11288507148c0f4140300b401e2603850a40f03a0243c100500ca41003140b5000703418802480301d61400d032040f807070380054800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 923621151 1250 923619901 923619913
    0x80a0c0f05250608090a080a02150117010605032d0a06020a02030406080c09180a06030c08030304021f080430080a0f0c0c020609040605150304030201061403060a0c1407060e 76
    0x43c4140c43d014010780c0c6844080d444840e612001401c000020103c3c480f15004403040e01d24440e0040d40c041c04260422040c029000c3c401a03c0e4040c2405803201501e01100a0861703100720b1000345000c140040c0582040b8840c0303098204d8002d0080c03001801c907a800c940c0965071641d00c1c840c060350782e900500c207410008140100148100740c5440079124150b45c002c00c2c0e2000242d10040c00c2081c460050a841c841c2690703030340004001900c115010005010240146840f0b1516004210300040d501c2582181424446080b50200307910540590f8050743c4844001c40d04590403150340400000c02c41c0504011403100e074124120b58002d00c01c0340c0b140300e10301020b0000199051000302030341d1081d02c140000c50034124084d070040c50300e01c014000c9600080c0000944135900d0000404408101002c2d43c2405000002d02c01030640c280a4580a8154507160380f503103042c204086591160000c2200710740345e079102c1c070328080e03144203420a41c613078105422040d44032032080c10f106005200710340c0120440e01c241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 923622401 1250 923621151 923621159
    0xf0711010e01050406021c051b010b040b0609150705121612260405010207080a08010e09011b05030403020a0512131a0a1d03060f180a080a0c0f0525 65
    0x50804c48040e05c020703038050841ca01d80007036000b1705c4140580c924401c6c45800d001803100d10410807100c4d0b440700c046200101c0d00b600d01d1414030045031030f44020107002d1202000508419260300010440c120701e807804450fa140e41d203040450a10486040d200001c202c001005408000c01d404000304c0c1d14080c1001c0101d411b03142c481035071070500416150f400c20821003030742051000b040300010760060003400054500902641c4690940c1e020b88a01804269074100500c41003e038440d02c0c0368407210b4200200b015a500c026007203042e40010b1080402c100001000408040c030034030090403626445003c481940f200300c2c03a05100c42e0400301460300304004940000038503251a4031881c609c0ea210302002480c040d5072800c00c039103104c41b0030542c0350758880c03625a2004540b820402d503440b880701201400b07614181910114038890010081035541ea204800460100c3c2e0000200d0b0340c020400c6c1409650034240c1d10344502141c2d810b80000e04503029a1180c0140940c2c410841c04010990b41821030b14a40c035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 923623651 1250 923622401 923622407
    0x20f030a020405040b0d0c2105010e0105010e010f0807090908090901030602041a07111002031306120e0c0109051e030102120403020606090106050d050417030405100c03110d110f0711010e01 83
    0x6405000c0c0100d01c1f001e00070402c800410741c042120003024002d150185910751030311400e5608495424195a551760b0040203142d04001c00203000d0041c09208541030780c80c0c070001640d240303424062800c0299072602d8107010031503080100c2e906400007404074400703580d5a003001402500144a070103401000181c07248030000071070044480840c1d210180003c9060840c080c0b001c0428081200300c19072104220210100300c56445090007001c2980c0e800300200d11021a000039182502c1e201022a030200d00e89a0b0142e030405015015078130150303429071200844c0514014581c1105202523050f510001e804214101c990302ea19108501a0302120801e4460b142030080619003442a0000a4000d10811515034103076004184c0080c015411402d1a01a66548030750640c0b0988044a09a00c10711a4031114203003406014600c80d25030804001c0154031400b6004140f0404c0d084051155035144054417940d01e80041c0c4042c00201c0c0c4004d80c80c3c1c2040d16003402c0c282d02d170710074003030108403000303094203543d88 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 923624901 1250 923623651 923623669
    0x111b0f102702030a020306101a0a051b03041208030a1505031506010e0a08160b1903020d060f030b0906010b072a031e110603060d0f0501020f030a020405040b 69
    0xd604494441c40aa40340078401c460600c0c0102240d05005010300f50b00540e4042013401c2c05802070318628a6520319198902e1010131050401d1074600000384540584940c00c5429501c41210740101e40c1d25544081d0042802c51045800a0f40c05640240500e000d004803070019501c2a0720b4108200070590082d05500d42c0300060b4426554554000d0300a068580c851801064201c017042c1855400c0c04c41034000228210020740280d83c0640c0501072035451a950f4101c00001031100c101d0680c646984902100d2030070f420703419400141030f0006481452a18254000310051141c401000b054030f841780340032000640c042d1400388842c880d5100209a0300303038500c00c42c0d8401da40040d05d484802214501d22003108200d003240702c2034002e007440000104101640034141038030000c0d041c400721a15490101c22450800007507500410040c0b01f0818030391104165406055040700c010800b41140b860b0081c0a44a600f40b0118204030100902641c1c182503005003060718011142070111105503001d10803045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 923626151 1250 923624901 923624921
    0x51e0603092802090105010f0302270f0108150105090303040b1911010e1b060c0f0303100603060b070b0903040b0c0106140d1110120e0d0e0907050a03111b0f10 70
    0x511a01c0040041f0340c012101d84a0351a01400c01606000b035244000c689001e144842c0301004810700100d0340940341410403041665007d0800c41e003d0f00f025142101099244c9020030305110700082e420302140d60410a0304d00411501884503640d144040c100004001d07800c80100201300c0c00c10682d411a00180500700d1903440c010b00811501c4800040c46045811242225400c131100700001d60030b080f410302c41100b072502a240116540d041160b0040401c00c120b41c8290105440c6c01d40074055090003034200c4000c2504542c100340103448014000741144100e40c48005201400118001021819002007040b00c6949040e0342942d0b000f0310500070355035083d03000203100300d00381034640c5490328159410032204406840c111802d01c1001031000126191b039074034400c1a9219850404030340b50310040c0d039428601c05a0b8079555904041078060700500072408202c040c9034464070100c1e1901880402d5a18490020041c6a4541c41c441141911155001d403040428040d0010090010000340a14000d803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 923627401 1250 923626151 923626159
    0x18040c0e0d0f120801211a160806040b0f060a03060e01170d090b0316120914100b01050f09030c130c0206070806011d030c0603281104051e0603092802 66
    0x71b01e4680e01078045851240d0402c84104c07002c1ca00301e40c9115285e82001c3d04c03d0a001d04d04002001d91000007900801c0d005064500c101d0070f00f201c100d9140c407100d4205001c0402a18030725140e002c00c4900b500900450f401c0b01c49101070040000440011407031400300a807021406440c046210f188044031201800e00075220601000c00201da200a1415113491210300146081310400c000000d000e41619000c0000b92035846000f0040d01e2003041c14808a4084042c1c0b12040100c8240d42c1d0002e040b5004041d00203080d01008210199030f82c50030711409201e904000c010084039483c41100100400c211050280148502000200340ca40240011030103070405864098052840002c040550383c0701c0001036800d4058890101110340311a80514080c00081007088507000010800d5000740b40221021000309040c41818584125824215410b840781500c1c1820781c0da404c41c1c02c1e90210002413900c60703004080003003000504000840c0c40c420b05014074020711603290b15210f1020807052080c03001307544 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 923628651 1250 923627401 923627429
    0x61203051e090901060e010309080a021b0301150b1e04150e010201151e050a09020903060f1918140c1c02060a0f021207030f0306090218040c0e0d0f120801 68
    0xe500031b81501c241e521051401103110070466a0b0301a2176080151900050b034010b000d030265031074186401c0001c1c040254001c000c0200040b80036868822a4410903801220004040812540040f0040303180402e0032102c640d5181d40b000f4080d40b040b100d406240015082115031842584103014041d6400f44d08800b0304007441c1058813294402c04940c101040d002c41078000000e103600e4840c203a10040c407000e00300580341c0e030400d0705050130000c0c02030104803414403440c10001410303092007121810f103404a1002481582001b451030902c800042c014200c1c8450035551921614002001c900e0f200341602d810101d4858400f50741c900001d60348000790b00c61010710003216030520605207029030b000c107481122000c21500e83c1c05e2a0070340c48034206a000034000f140480038103030180030b848004c00040d00c1c11880c040481c031b4184030504030006602c1c440c0b03848169105119200c1c201c1e88100b51001440120220203034500205106000e050481d200e141c040301403d500e90090201a04a480001e02200307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 923629901 1250 923628651 923628659
    0x16180e071d0f0f1c0f050d020312011e0806130516140f15030901091b0510030f0b0a12050d110a0303050c071505090c0604050a090906061203051e090901 67
    0x29a0307040100352604441040c07405440d128140c0d0740e100100e170081503112008842820501d0038555600210010356008000007080e64a03228056811140320350f00f03c11040341d0078946040ca08040350f010020621a90051011071144c8010340c0084500ca201102c3c4a94482640c140180c21203100b03800100221020180040c02c3c0a034a42a10076030007030907003640c80d5141f182640d20350800c4c0c81484190795615154420002c0b0b4182400c500120820031004951801c800104103038000d010716000c250f00c48c0c00c540802001ca8105211000009100c4289031741c8403580340180003c4104159958420107a5042e1400d015001102c50741e40c4200180c0304640c410f4900f070700034010150200a10040411010020840b040c0803002012081407006c84e1a04024441c117183c0240120f0b1244120010002001142e844030b04039030032a200002d010a00e00f2103402d00c40024111503010700d0400c454100524109a032090003441240e04299120360f002c1d01e14840da0f207160003030000442c0c0040c84040140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 923631151 1250 923629901 923629909
    0x30908042d08100b060c010507080f1e011806150f0905040204140603190203161805030715140406080118060b04180902031c02070801020c0616180e071d0f 68
    0x34424a0018200c40d1800b0342e2420b442e400c4236011100200058101418003240a0100e00417030380201d034240c0100c0c80200c0e000b5881c10000c0040c0b06540030260380c03140c5210041c481e60003510050040e0451100e610480303c8001c1c10b030170401c000780400203500060100b00c510300b904c2914140c0704c06142c00424000e0b01e40c244542c41c0d00103001c9004201e100003581400c00700c68001180b1801d40d5607070030140c0b8030a4030405440702607075180c40105100d40c0e41080c8255140018a80101e80302143c003550680d20540c0140c94401081240c0c84602f000050041007144c0c00825141c100c50900303458072041c400c3d900c50007086034407070702070851402c408010401000c3ca60024036820040e81c004001141c40c1d43d540001d180002072032000307d03031203d10807400e00d05680601c200402002600000e620b804500c4801a480e510000c1c0400101c0d0207800c0c003004050310071800040c0c14210b00e82c0600105131100d50000180004840c8480081c05a180a207883c000043c498210316030060007040411140000300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 923632401 1250 923631151 923631161
    0xd0f2414061507050106140901050102030913050a060503061305060c0a140a120203130b130507030f170714010c05070b06090c0f0f1b0105011a0307030908042d0810 72
    0x280c80e42c4041407094001141e42031044100401c07602401079607004851040c004081c40c1640128150b420074042d41207182c542d2108180070402c0c1c004005802d07500c0000e040010515504482c0e0035120302810032040e0040c407810415254050001c452995a41201c02d035800d00c00c4680c0e64000454040c00d501c035201e26003010300170101c15800c08003110b024000105d01280c10032221403280301c42c035001100600c1036240460b60030100000d600b500c5028a03490780c5503101044e02c001040c5c5400d02c42e148041c008032110048001d24044911a135501c0a400d001140404104000d4070300e5107005c800114050250003214000b69000030010102e0351414200685104001c001c00c94500080103454960040b4500414804140c104071319112a601150300d0b104102c01a12000300781c2c07500300140701402c0c048415101c086189120203907660fa403514110080c1031801030007020600c0124001c0382c85204842c9107078070000070082240303801407502c03a01c80d4428254440c10085400c45441510321441e26041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 923633651 1250 923632401 923632429
    0x708190c0b070f0c05090c07080310030b07080124300213030c0e01050f15221401081021080307181a0301060c020d0f241406 55
    0x540c104a955482940007940036440480c0c403c41d103400070b0010807140d402c0c82806850705507844007680c605600020068450000050301e007907404030010b012500010380200183d80d0001048440d4242a200070b04401002e01881503487c4c025051100711501540451905015a03911a01c03001c900c48403021816401d110201408060710003d00490f407818001009011111681d20140c14510304080000d9100d94104a0907840d242004011550302c48822040540741150403d90483c280201c90085100d54820085244c1510b400803402030b2261400c00f04441ca222505002da510001c0111084481141ca1000c0240b160500381f140030801c11101019080e0200483d0020010352100c941c150030440f0790500003041a420050403044281e1684010140000c15030075401c00c0850a01c85400140600750420140e01c01c0301c0d080d592010345d50220305403c4190040b05065600b010b56490014801880081030702c12000c00900382c2e28442c283c600a03152540f000280c66030010004503c5500f20b03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 923634901 1250 923633651 923633663
    0xd09020d140f151308030603070e040602091302030402240f0d0c0306080703050307030f050f0315010e0126090a08040b070c0608010b0306010806130603050303060a08070819 76
    0x320840014460428030074040d0680001000100000d012403407403d09014010410200e2140621851588025000201a5001e85100e40f40d98950004c245400e000358040203011201c0414002408125030040c0342c290000d803810300b54840d08001420903440305841c025041060303000f18050049191004112400e500c0103924601441d4900038169a000051f000c08450340d100791030280b05030188150001810030a01130310249146888440d182e01800102038240700800c03450002162140088612080340c44c500c1c40d40324240b0014290448051400150200f00308030346116040d8099464841c03034281641d511036142c240f03501005100c45019100050070321400132080b0008440c20042c002401c220700c0c403182c403417070281000b12a01c1d265a1140c014400200010301c00c010308003040365030001003170801007115140c2202080080709603040b41c10348a40313424400b00c03c204011000398090002200c0d03190f4505d4039010803944810040c0f03e0f502032540040d08040c81842040c14801c150740c020a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 923636151 1250 923634901 923634919
    0xa08130309150504080c120703060b01140d140a0e0706110309100f0807030203040812190606030903030e06070e090907091e0e16050f271b030402060d0902 68
    0x200100b0380e840c1041205808510081001c0c41140010082070100585c1100c1c4900407007072048403651111041c1c04041c1040703454860150082e401080300c0c64410031024a542d0303a0740703440b1600d84001c0c601e403904440d0340080403010801444260041c40042240c00002c0c00d94640340800c181ca017082c10b003052000c80e00081c00f51030441d581d010f201252030344190300c2d103040d4104a201d008008103c001c1c8110240b43c410300600c0003180c84001912881040e00d0044d032615146c2000201e01c504501460001f00c60a040000c551540d058020b43d48051081d201441158003910750f441d12004115400400509450a80c6101d890711200042e0081c401c04240c40907203444485000c01c0d2500250402d400f245542c00b0805075001a220b2441031920032000381c20011100c540b114840500c9100f031a03c580354003903010260b40d850061104688042840d5048510400f0150300b0610104489015168460b00b410765a03805110046a00c102d5008040b01d20344002c000c0140000e01035854207a811a2040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 923637401 1250 923636151 923636159
    0x1311120c0d060522030e010813061d0d021209040c12090c1a0307080105091b0c0c01030c05071124032809080f0c010b15040e060103020a08130309 64
    0x2650321107000c5802040c01050500d0801802c10020501d504855810304104200718082644070141c0443c80000b464441c16a407100040c0002c040628080030700340e2490524100d80b004007400300c0b2121050880f060796000402c41c40260384031400006d80d003482d1101040756181602d45503202044100d00c500300494024020381e10a022503244203801c54240300204418006c00840c1c28100070540c08808440e4a94501500028542441841181c1c0543e4031000851700030806144590a100c008030b640d181c542405100142d0340348040710300d540c00319203030580c1ea80b0920b100724120b410311b0341c000c000502e803191031105004602151120107a200650034a200d015912100700440c081c030b450041c1c4410240400c56507501080d0030302042c91000c0d1406180b1400a44520155010150310030342880d180c0703100428443c0501300313150300d03290702101c140440c44c1c070504100c02400503500d504110000955138100190100d100c0c029019010540850000b24031801c640c2089200c00d110340f03000040e5a5603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 923638651 1250 923637401 923637409
    0x9180503040306020703031a060a0e060c0a03030b0906060703080121020a1514091c050c150408062406090d1707051615050c010b060a050705061311120c 67
    0x7a03081101d506030001840410306604d8007650300e01c0800100480b02d03001c514030000d0b40521403107501e00e080c000c1c0b401940450380c0c0c41d0f0f82941c03c40c90703242e0140e411055007890024000c0c40c2d480c140d20702c1580ba075008079590717003088810b680c10594141c0303450b851079003855102e1080604101c110200800140c102c400180c0364155840d00403c442045500c1c0010441c3c000b9003080d441c2002c06882a02c1840060b40c80d680b0f0140c4030401c640008c040c403040c0601c5040c8036080100300000f01f50060820b0702c0303e001c40b503c3c8400402c00c803209102a01c0b07540d00c80100110259000650061443d0744002e410529407070075000400304039030010300d0070408003241c0d603d82c1c0510794504104184644003180d204144081400146074181c0d5800001014a00b040403404414016854540070000702040500a0401c250b00c41e454041e002030a454441c8034003e0300500c2130b4041d0030112054020079000c0703104900b482e0705030b0054980c440d034820041b03c00002032284d40114001d0f01036052040f10001059625 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 923639901 1250 923638651 923638657
    0xc030210030509010b0f1f0e03010203040b07020d050c0a030503071e03020a1202030f04110d330e0d0f020304050a09020a1403070c08030403030615090302030c1909180503 75
    0x20894801103840e00e04400b046007121901700c1150b0040341c0703040050029941e650081c00035a02c640082059181c003031030f02182c400c07828103103c0da0158400810700c400d0100b40000b0034400d12180e03080316003980d0380c05001c690501884050360b91a0707116201071400640240040c5034404024504101e161a000b50b0481c02c401d910008800070a90000b0300c400c200b684403240c10f040305e11000d4107514500300310322840c88055000b403000d00034084015501e040d503514818107014280e000f000c080a05895100c014101c1c000540d84100e0030340310000400790604c0036006609070005030038003074401031010440030b5400340c850480c90b5086000030800401c0c2c5681d02001d00700500040d0f000140c031414158005042d01c40321222381c103041e280501c2001000341d0300c14070603001c07184e200c0001038407a21076280a9001d0092030b00007614403010a01c41c032400c5507100c1c0c0c85a040305d00031000c81c0c00b1100141c05101d0b00e10210302180f020655000014049074030740e0f8001001c5440ca0344090003600c00540c4039142150 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 923641151 1250 923639901 923639929
    0xf2202030403050c060703060e011d0a0c020f152706070c050705120609011a060d0f0f022b05151c080705030409060b0313030804060917070213110301060c0c0302 71
    0x954440080c008849e41001590141c02c9a8660302e50315031440c5402c44007a10024210720402e52500342081c0c005109004031001103c40c1c2088900c1c600941e080c070090038000310b03010544e00c0700c481e40225501d08030b00c80a055512520015041da601d0b0007904462804200790241d07098400c00c140000c03a900d800c1e0102d00344100b601c0c003826041c18008100c60a40b9211903840794810101c400700202c0d0b039145001c0b1414102242c00004d8030f44001840c00014040b251400d00d079062005c1075a2948496515074091400b50101502040302031030101c0b40c08072001a0b8080000c44092082c010850330600a900b242544907081035842400c555500708007581718940858aa0304041010041200c080c0180405441e00c0003101d415480c1c0441d858844840c03100e00541040142070101e000c0c400c0c0d41e0b00420002d80c10030258100c200c80020406810f0b407011800301d0148000d845d12070003a07803c500ca855107404000410720f00d940d2a02400725111040003e054460b00c1074103a0010059480c000307409010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 923642401 1250 923641151 923641157
    0xe030c01060512070e0c280503180604120e060f0a110d091503020a1e110f030301030f0f150c020a0c0b0a020d0f0201150f050f2202030403050c0607 65
    0x1042c1801d0030310500406608040707080ba40802014442000310310310070f66014205201403629100905601c02001030000003019900850003e140302095216005510505010103114450b100080e40595500d10444020313004850300244820090700c1a030070840340d40401050395041403110511205640e102c1020000811040e00c0441002c0070240300032030340c3c0c80441c2414642c3c0c42c541800000400b1745480b41c07200309a400a408050729008080100301c031160070541ca0340b407050384140a03145082690725188544600b5001314204c00f000801c0780d0599500c21044420075900350303610400284010b0b4101c4460740030f00c030151010a003074403400e401084103a00420611310342e17042c01301d01500240c1042e54003000030000000c41580000d03401c1c2c40980d03d494629900305241c1004ca00610400d85815000d00c0d006d9000916103c0e00d80c0500d065883c1140c888843e001e00004200054200f40554500d911003202a48503100c010360140d40d00c41c1c068101145061109a5501e00b03081c0201d8401e004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 923643651 1250 923642401 923642411
    0x1020c0a030806090708070e01090305190b180a0f1a0f0604050a0b220e070b071401230601020c090405010504030807020606010c0209040507050301062603040506040e07030e030c01 79
    0x14164025000c0340c0046080e04c1d101071301c2c200102d004014200043c15613047c00305c21007070301649905c65070030703100119000400d5500d0b07a280e4040d20058880400e5040c0d4450343c661001c40c0c5914440030f0803e01241071000202180f04259484549840842c50240d5600a8030040070fa070110302842800c6c07103445042404641403800070100421034030040d14400811749480c880780324036110614040b030244204a00400c1060900c4205000341032422642402d9001e4544002152485400a400d64030701c10041e01c00c034460a540e4603822030f22401845001446005a84000503800304c1205800440c10310543d105242d0900c00b180c0814000d5408480d669520b004010034541e015280ca03400c120310381b014080c181000d000007800c240e80000b01031b210ba4003140205041160030000c0314010413018000b84400b640e268190b11001c40b8019483c020384e5010740c924000c0d0000403040303c00b5a030f07000b00514141400c040310b004040b20018010303001d0566032080032024600400152288600d00000410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 923644901 1250 923643651 923643653
    0x611121210081b0607020d2f0d0203030412140105010b090102011506051c0e1b10080601080c3001061b0c0b0c28030813200303040801020c0a 62
    0x40c1c10030181d8000015900400101529010310441100e02640c0845a0304d464105500000703070301d210003110050940006000000281e02000d1943c3c1c3c0782c241060512269646150610140c1035225000940c143c0040005202740c62444041001c124045c000070b0b508651446619800c6071000e070400b25024002044410b40c030b690900810300490f4410501004031458407101509a0003401801000710010142a401c4071801380d0040f1516140031013180e01c40b40e504000d02d074510b44001c0c4650f02541050320842c0600307002d908494015441070b03460040c00d9442c00340c7c0c0c8426401a60385000031049508001ea003010004603c20400211000d8070a56549440000ba0041020005050031001100f02e4800862080424042264550040342c1d503503495542150f42070442c04144508001d40907c80802c031130303421100300c040300c501c280c542c07038051307111001002c0d080c0d801944000c2c90712901650b024010842126180c0c420500601202d080503200d011480c00d98104121049456008110b124 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 923646151 1250 923644901 923644921
    0x20a0f11130b0307090c020114180c030d0804020103050402040b0909151311060901091802090a050d0f02041d010c030e010c0f0c080711101116060906111212 69
    0x4082100341e10400c00100c2003000100c1e840e248240b04210341d182d5281055a507440c000c4d040200c4250356907071000070300d107005004401e00c1001025100b40d14400d05020007120305001810a89030781c0030f0348580045558944c01100070340310051040381c00940341d22060031a44c070b41008036402120a0400380c8070300710b4030b0000081424801030010401000c501154004070342014812140240e0030340c1c00c1907803250648016a03500c402584101c460a0070b0203055210b206242c1d018214082003143c41c565995521002c0101c0340710040b5020b804d8001c05c00d44407005143c070345c1c044040003600c50302b8441a0f50401c6402400c40d800e5860b203001103a00d4030311f00710301c16400f031003440107415842c24000010100301030300030080e14058800914403000010584241b00380c0c2564203410000050055400c1c020b460001840c85a1038100c06016104004c00c0ca070302e405c5604186001da5606036140380006213888401c449110141100f94054064044641103000041d4014842c4c28404084642c175030414282e01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 923647401 1250 923646151 923646169
    0x12050a0f02070b070f1b15091d1602010605030f0f070506131e09110c0c041406060f0708030a1e050f070c0302161401030b0301020f0a0c03020a0f11 65
    0x10001c40d00020350a001d00d003c2e1000341d135540794010440b903a0110700c0d8038000b041d84009050110488a845600180310301c04044482d0399800903580d0400748580d07906a04100c1040d43c0c1e603030138007008410f000410500010540640d40580c0384004034506e0740e82e0011900707010140341426410b8101c0c4c0b0180f09003400c200112401001c00f6222203141084140b20300680d108503020342c000d8502d18001c1250032180700c51043c4042c0c0f01c42c0808100000c400c1c0d031011416400340040c403045024010740c01d200340c0350500c100414240070800d0395000c0d560340c60400a49500c40c492484081078248140030100c3c4032407010f140710714070b82e03c00006c65a40f206100c0103040114202607817107604200420200344807400f40117820810904061203085201c3c50241e0400c4a400b007414030400d000c0000080c012104402e5202d400e00a880801510040303100303040c217034402e18036003036054802000b0940c6464401d2800c81035241c043e1055826054103a42d078805180010f00c02515405525401300301c007842d1007110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 923648651 1250 923647401 923647427
    0x10b0a080307030302091522061d060901092714091b01211d01090b010b0702190803070b1302090415020d06090914010903090e040f12050a 61
    0x4a0099245820119a5644140940101003580200d0118142d40b00d0044400080307800401d06a1141e00359025040008005034015103042400580000c1c00340c050340d81d00998402c10380750034036640084014014940c3c08004100d04224a0502c00035000300901e00c9041d88002e500d000b02d004100c55101c00c0150f81e089125610850009d10500441000000384c160f6841480001640350582c00b50060300d100004000d25001d54480b0074444001c03110346d03403195055a1314002c0d40000281241001402c0742c081c1d0200402103200e43c1d00500400b86000003500c12a4801458182012305580d070b1100c02c1078080e4003904450340302007030100400820040440d441401804583c00900b12a00050380b261000b91001c1c120119552070b14aa81e00141c048030f800d120000418071080340d403101200d0080604400541d00c4007000880c44000c84010b000b0420401e03019038401329039504016075504181000341c0f0888070390110200f1403001410515645440040f95155207890342c108400180400d004071074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 923649901 1250 923648651 923648659
    0xf040f03182408070546020f0f0307080c0f010e070305011a0f060a02012a020c040c2c18150a0b1608040504050f090d09050102030301060c05150c0c010b 67
    0x130001002d0b4020700765a50b40d51a041c00d15817240c00446a4401034038141c4880100602c082020100407010b00410303d17550446908566540c0b1002003000d4680c502d440d402413040c2c02c108500301c0850341a102511a4038074007019110401d1030750030f0f1a070840f030401001c0c4240f0b4009000810500c082031084400074443c01d070000704488155070000d0003513280d000100f0311602011031170400700c51007507010681c00c0c0012850050062440040c044500e1040f04501006105030010120541058052020314102c42d450f00c00c0403d01812613200806d010a402e90042914041038241940c1c0780038000400da8006044c035a59410f088054801801e155401640610050803042010030340001c125880c0980340e20000c5d40500c442e240c0081e4600c155802540d0041c102402e01681244c1840b220f406051520100c5045829580098503400541e00c00c40340560401d1004200281c001e05203000581d20440540f01d4415840c00507038410442034900f881107580104110b004610248240200c0000c116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 923651151 1250 923649901 923649917
    0x160c03020d11150f0a0f230408121005010e040b0108010303050f092218030e0d0f08030a0614060708030402040e0703080307020a020a0e0f040f031824 66
    0xa200699a50440c00200082000440c80b20b00792070801c1c03103a507443d15100556079045061400c020107408206a0703220240034034080701071061010a2040300c00742c1030651124004000703401c00444403801c005000b910049020006602c0004c460451244a00030101d8914401c0e4104400149109080400c1c24020781c03800b4024045680c00990303860449270b00d850840c1c0d076103105800c060100d0080045d1650070404040113040c4c000c00d0700c00f1480c45c0300c0340d51104000e00880c2024040303a102c100c1201070045040700c0003d100346d09180039407150703081c02000b00200c120180d03070700c802071b50b0b0084841c060f1266466106100d02001460768a60050f0212505401c002940e2180201844080c0c13000b4421a981c0081103c0d600c0184501c02c019500030741d406440c0d00c3e11350300107911024582c6003240300c0c0410321004112004100f650790700032248805403611990b92641c03820b0303040082e00800c0c1d060107850300b40100f1480c032040c80e40d030241c14001d1002c0c00f4002203ca80040c802c001c1e62528092042d01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 923652401 1250 923651151 923651153
    0x302010b12060a0e03040f1d060109030210110a08030f0f01050406080d0509122406040212011419060e03010518062206020f0c061501020c060d0b18160c 67
    0x41c02c68220650b4140010741250a0500c285188120344c00440c3e00b00c103201000848400c035112095044440310300400700313680c94600448540c810b82c040251f00c200241003410b0712134440d131020160340f064142140c02d00c1c6210789904189801c111401c04038480528200010741103160185801882c1c141c0d0b0034070500c0e00f8540c0c0703d0b40381c1c11916804010050042824950b55070384002c07003901e044094081c1d5051210b02d1315401010070040f002d803030034000604041076180c20a8801c0b95901048084071a1159003800c0101c0c80e0511106803990b404030750800001104102124160010400c41e144d881d0b20a440e01c0a0500b91180101048003800c4646c5d04405240c0d008110a640321511220b101100b90084203039800c178004101014140c5440801c44004000c0c0c0e040c010840103140740115005a6612a1039448100c441203080e40181c001c1890740c0300b14100000640001568020089400c03441103010840140e0741817441c0e188039600c00f050045140780c402e41c2d485e4035013591404280192103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 923653651 1250 923652401 923652403
    0x61f02014a0303130f020d0b060a06050a0c0204050a0209090a05061503040507060f0504090e01051008030306010905090a09020d0f030e09070e19090f060503061006140901170f040302010b12 83
    0x200b001c0684c240300c103140010494440d100d903020b10383c000c01e000c001320800d0501e0180d001c003c035000c50103a0f00c1ca080c04602c543c06007080c1e406d94031495a07601e50002156003480091300015051b075682c5a000e21840b0003a50b180f140c1d15100e007074007240001d8107251031000c111014500c0b0034903e044000030800d21000c41d10201c1c4074030a80d0101d0070070240d1000d840c1e408030740c540720740e40c4016403440c80c0100102c4000410b400490041d050890500782c455110110651070b40301c2900d107035001c1804408d0402250911107100c96100c607d1880008071003a198012034807000d2001d40440301c1c440d082c0f02c01401c26800041580c029001a1280d41c49440c08201c06000c2400303a2034541c0c41035100d51042000e090700590403070040c10503000b00340003400a603a8502c014101c0707809294442d000340400510380d0f00c8070758032940458003160b0301c00c11b800c40083c0003001c0a6020764507050400c001034000901c0c2240e003010a0b4003507020000c151480b032800e420003d0840f0015202e840c440e5503034044085120310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 923654901 1250 923653651 923653657
    0x40203070b0f0409020a0e0d05010b010f08011512020d0603030c1505060d03110c150d11130b0706060b0f07050d02011107020f030c1f08010e061f02014a03 68
    0x40907130016030b14103509000760760f03540c100700c1c4c0242d000000d000354004012040d00400e0f4a19401e0b203401d44548440d01059620240034090002c0c00d12070302d40c030186403a200350300340c0081480500e001445c00340075a1100d0705980c1d19070000e42c08580301500306000c02c80101e00003107007203002c80c030101b1040c01e05400207400101070700300103400c01c40307d251042e00c0c1d1501400007540c0302100070034260301504000d0485405801008080001c41e20700a64021850600e80454032030420321928084454140756000d0019080b04030203549580c1d80d0305000c2176400d101c0000342001ca51485072561116030518129140c410060000c1d411039041252002c100c002c8442034582c21541120544489805840481e140c131104405441d841440f48200c40000761701811108130251540d80c915866030389541c3c001c100000309a0350103400c200700440100344007840e10781c220b004510368030011600da002c00c02c560240780b01145407101c005c844603510100c01166407404030000d1880c16111150b040c18441c00c10340383c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 923656151 1250 923654901 923654909
    0x20613031b03090522050708010317160b01080610080a030e0609040e0d180501031406060a0909060f0e0f240102071a1e120c09010c0515040203070b0f04 67
    0x50200700750303201050302038220300d0050f09002d80511240c83e112601c1c0c201c2d4402140040420901c2c20000c03515051107058114181c1c0d400602900380b42100400906041e409142c1007400710b0082e202004c001490f070340701940282070f1440104400c1c1443c00b07070500c2c20861030b40a024982d101c1c1d80b03803071300007078100118203411201110400d445a00c50804140549080d00d134603035103401044040942d03503806c03030700c1c0c0046843c80310306150a607601c2d00c0043d021501185018041c0078034a00c0040c80714074000b1b00515140016103000550b440c1e580703409509a0700c85412010215209080902a80b0049140e0b1a444003a40f44455201c1c101400354203034070003494103840c00c03400c070300c402c2c00e03406034000c22004000707040440399182003540d100d0008020307030441c10404455004d0343c81031708032031180b2009031090000381e41c0820100d0b03220520200900d81c082c0d840103040c03203040c07000e44020440521070409001d0b41160355912519107403040501740240307600600c282d040b003803040121146016081d181a0307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 923657401 1250 923656151 923656187
    0xb0105210c010f1b0317090309060d020903190f0521090409030908070303200309100e1503070f030c0815131d0d03051320010c05160602061303 63
    0x50303e52010032120501141c040c0d03007140400c4000e00003010b07449003080c80c0f160010100080c183e100d8421040d164801d00c501c80354095001c0c411503446403205d03802807241540c001c048405c03807a441210000031440aa4003075400c2603203605070760305008040c00780e00000d140700c3c41410b004410350104142c1c80e024070f0307580c54012592003c0c84400c240c0102c0802d0b000d81807200444074039941d2480d0040c49111a40e400c41d0109000d084d0303020001d00000240d42044100038248010380d0035040003190301c2d0301c00440203644241008900c1d400451500000d50148401c0e03650342003209010724026080c0d4012880d04000c00c114001042080d80c1d0300700c0580800401140c45e000c03c1e25965441e50007412060240003001042035040ba4110f034800560361b103034081281c0382444156524003882580c2c1101c410054548000302c504a441c0e2208540e201d02c0812050400e444c6010b92a143c0fa49001e0010307214108403d8201001d1003019010486942c1c4100400c0030060412000e507401840e520f1412519005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 923658651 1250 923657401 923657417
    0xc0310290313020103060b1809150901230d020f10020f2b050f12090307063602030d1407080a0926071415070b0105210c01 54
    0x2100039090621040d00358162480e51a0308058004250600035044100d010a1400000094a1001f002601c00307491400c210341281498070014061214030040c00080030448032810000d0070764921211901a0a9501c810440120189440d000755000d40f0205031050b1403c1c10002e00680c3c68400d091002c600a682000c8036111032402a454980303034280044845c060590701038010300000c10b99442840e2641c41104280346000e030f043d24a4825980d03031020007134080210b00b004c0f00c4075100c81d9800110280071249084007903182c800c00c0315a081d4001c0c401c18603003a1908105508609440140d482e03041c1e090004004540c0001c5c0d40313030100308020b8144a01c071030280c464040c00d4029505010f82040c19181d075601c1c02c42005210040500030800c0300e4000e08485241401e45d150800030944028000b8500c080c1805080c51316109240c101ca5406000d01850503003840c0030b2800382807150b1184501100f59410441041005200d0301c95004040c0740c1e81103810603d5a000450038018035080c240444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 923659901 1250 923658651 923658689
    0x5060f03160320120c090c0a0210020f160309030b18061906050d060c031508100b0406180e100b01050d0e031207080a06091112100509090f060c0310 65
    0xf40c1844600509900000390207030404004404203020b21458411100f4034110b40c1c84c5e0401e9011809a8080d00b00140e1100108041c04000d6074002c000c03c01e1084466424050a10490b00c1245060201100098000c1100b0001c000c041c03003503c1c0d00000e0150034000111006101c959a64200a101c40b225410080004240f010310382e026001500001c0d0180380303c100c0301c2c10984043c11a01c110680020319010100b145982c0e00101103040d18008006440612007609010000d002d091400030741c042d0340e03072000203206c2d10302001c1c002103c0003d20300422041c50820340c460a00c4000d00820070000d050401c4015141ea1140c00c898011108202c005003410200300001d1a50080590800744030403003d0500400f20313000b81020340718810146040c0300c2e0548500f081c3c002c4e65000085000040070074443c800f01c0302800201c05a020340d1550b902c42c5026520000a54512826130b00034070590440300848403801c800b408525801007040f08841d1450414024106940240344500e606844101141c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 923661151 1250 923659901 923659943
    0x328020c0901061b020d02090c0a020d080f01030b190e0106081606170901110d14150a060e0102191202070e0405030f07080903100b030717060a0203040314030a05060f031603 76
    0x6d81680140c000d800c0c914000b55220481d621000f8484003600c0340c02031b10070015100d034181e24844c604009903050071341d1840d0fa030809a803002a259907441103100c0c0301c4211001180c8905030410840314008a401403030540d2690070b0010501d0300151045131800d0030301c0680d4125194001d0246c0c07500903070301d255460203e001c1c010103883c21442d03030344080010405207420494010502083c0e118454196546440300e03802441d0300e03080202500485601420001c203805003000c5e03046003006005494000203c0c0c04007012a04146c00115400c4444104203088107904000d4400a018622158241d03414143c070340a607240155001e5120100c40068844100a404415245440406030456000303040d00e4031030700c01600700c20042030300901c80c0d69000100380d0801420074220498081c043c203683d85a50303480038081d500051080e000d0004480d41d00c030101903080300640c444d030399911000070f071400c1140c108421140c0d070b030b02010b10a42c40506031058010039010b5000c200c0750b0184000241c4032044807a0f03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 923662401 1250 923661151 923661169
    0x1e0f0702010c14030409060e0702010506030a022b050303040501181104020723011e0b01081b09060307020f060604111909080102040b041e23030328020c0901061b02 72
    0x14011130001050019612200b03402000030707a084440750350703201c0d510807004900f01c0d40b04803049981540041c15140260420000100c0704180c1c5c8001d221a00c41c103107266800f04200c1d41d0044815034000000c000900c03030280315000258105050700d010011300c0d0b4550000800c80004811311030742d0b0004440c000c1150401b0200d0340f1440500302c004405030201e0682c1d0003070800d1011525160210780380e40742d050040f40700714240105d050b11190242d890305414081e14400200d5003c811724400c02115005650b1080a903200302000d500805142000c04082810460003030905801182810401d0042481030f90907200c60311614540810140900842101d80c90704039802500300303510020b030224100c1030405c02002512054408580100c00030041e0003804107840c843d40a09800e101200158000c502d54030718440100201100e06000a41c1c6a81c841c542254000c00c142486107031440713485640601ca003254040b01150700c80295072502802410980c001a904c030030007045014131030304650300c4e020a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 923663651 1250 923662401 923662433
    0x6100e011a0d0603390e18010207050601060314070f0333080c0d021c210c020f010f0503011a0c0304090606110606030c010516060e031e0f0702010c 65
    0x10a00ca031a03504c0c104100542030402580a0041032642d180d0712420301d04201442c1e06000d962130f64115850802106511b200c00361003169015a4808501030109090001d000d9850090001e0515545050300260403a003414400f90021240d600400070705581003040020300c6412410003103682000086000142d0806413800c41c21080e00841c41440c00710b08121140036500342c10115126140c10900708017886001c224000d60048140070b400c2e805803c1c600c0350680c1c1c40e00c0382132070903d12003954030f60540442044a250000401000d507203400c0d898000041100c020080c00c0c12007070b001020200424503c414000c60703059600030098422845c0d8410112550207041405881e100c684456440c005070413644100340000301c00e9003100301030a402007010b81c0144c000a0082400a4500c001507420340c004030072655032420510355100110325a401002c1ca20f1910002035940c5101c2800355604041c2d03280110a410f64090000b41040c02001c412150b0345602400d10215030b00c00c038500500c0146450300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 923664901 1250 923663651 923663677
    0x20703031517120f160c09020708090a061b03081b030c040f05060a0c11060912100f0b090f0c0c03040609030c0b0c030a0c020f0604061106100e011a 65
    0xd0004050250110b1031100281d060141c42010540d110810010b004860750741c4c0140b4010000d5203183c00440c11010003480c811941b0154a42e034400c0b000040743c21018058038007120000f035200c84c9107032601d200700103480f990805042e00d0341c50750420001040c82c040000c090000800116110000040c40c40b110040d403080307071685e6440d008a548900b5040b510424462400602020401c0e00d00760003503a0b2480760555401010308041d4540040740c0740c1020203690006810003954090351212031003407020f264000000e00c0036403403042190342102e4400c103181004501d006a42030a503982c40c0340054100c428808446000d8a5045c9422001e01c20001440310901c00001c0c0042d00c29045194541228040d11400140e80d698480100591051091620194100300010a405805031500c0800240080c000c40c4150003082c001c00e607503074010303049500440ea15074100100800c0030880c045d8001e0009043c0d0300780501c0d10360080307020314041c0501202d01c06000c8448200011103c00c1c7d8440c010810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 923666151 1250 923664901 923664941
    0xd0c05100207030c050f130f0b040c030e07141e0414040308100807030b161101020301080a020a1517180703030e041407080c070c0b12180a120302070303 67
    0x31010b940c480c040d2104403400a00c002c40029035281203401003151210292a04180a1940d229600203100003060020b0a40e501c201e0658240c88070b00c9000d10546403030324000303030300166241d03050314103011544004108040d245ca11501502c07002c881d05808400c00e03503044110003405000902a0040c003400802c40104c0200701700c2819070003900c00703001d85000e0303210305c100b42c1d2a2040161940712500024114400c1d40004c01c0d180008540c403c011145189020820880d1541c0b100703007a6802a40000001d60219503043c080d0b00d02a800000103203050310000c80d08544518018049c00032590720306045884c0d0100003034400c508910700d1302030716550340259491070b5120f18000e041c21500c0c0d07040500480c1f6000b12156510881000503004401c5074560b07200507a501000442194048241281d031481c1d290ba00041d600126000f6190115039400d100446140c481c890905071201200c100b4810760041d000d80c03010465003040d4054584c0f541c40c0159498903c0e060540240a5a230714a00c2d040440d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 923667401 1250 923666151 923666179
    0xe0307021005030402100c030c0b01080c011b1104050414010603231b0609131803021c050f09040902060307110705031f051806010807031b0e060d0c05 66
    0x4001014158400c0310803060400034104122854002180c0080d0041007840c098941d41c0d0049102490b020310901d002e04044019603200c40690740c1c01e0303005180300c3d404242e0036211503810201c018101c04000840c0000c0d000706440300b0740f1041c4411103042c0074542d15804a0180912031400c036031088217078002803168982c3c84c900114207102a12034a09801440042d01c0d8a244d0045070000c416403103200020511401c41041110507801000350310781c010400841c0c810044001c0c011ba82c504c55140c46030380c0c0d0101d0340f81070103814511080304109446010310301401c2d90703e030441c040e10b000403d0500d03c0b5444407101c0000c0340c020001042c001c8e5000f4004400c0115281c2c1c04142000500e49002c103940c8903503502c1c03081c5075a174071521080f01681c1b00c800078090050083c5500036940319052030040030040342041a050b0805c007080e0081c084641000100340240600c14001032540689071990507002498141d803442060b001829032803056110f802c13a18240b0117501d201d500600b00003040c0500003495 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 923668651 1250 923667401 923667403
    0x150a0b06070803040209180c10271802040f1401030f0912030b06130306020c10091a0f01052b020a06090504050a0c0e060703031103180c0306060f041505040e 69
    0x840c1c04030320030b0210100052030110510b01f0000040750a1006114208000d0b081290400300c1c041e0040810003111000c042c81048048a032202502c0075050703541081c100144001c51028a190040d00280104810480010300d100504200e407852003000459000c0303400124061300740b019944bc46170f414401040144078010180350194482c41d1420005074004e0303810710a1a01460303c0e540c043c0019840e0800c00b1032100e400418403100030b14250342e01010180e4480c0c0451300903e07000c2c0d5a001d808400030b00036540e2a031400b034210075480144d2031a585000c000498480c81000e1608645845100c02d000c10326985042c80f6159500410800d41203848440c0245003010b1b52140600c203070309000118550301181d100300c1aa0000c240c0e80e8810400d501c00600c511a4070420088003016501e03205001d4169241000d0741c01001400000000341c115440d050b86000c03640b0030603a220340c2207901403050641d01c000308165034400649000c2200040c0c5000380165050651117940c01c541025115030000314 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 923669901 1250 923668651 923668657
    0x903070501050c031602011109190b0301030606081002041a0903010e0d0503220c0509060a0905010602010b09090f0703061d0a0f1b060905041505060c0607020708030c150a0b060708 79
    0x1707298003000009001c154022420780d00403020690300d2250401c0403145a08094107003c5c151402d4105814170142c2d81e1034040c020390300c2684151800d079511403092040ca04248400c1c00c9402003030200b03504141c10300a001ca5001440500b21184460006000c819070300c0030b40228100d440341c14159482c02d0f0243c480541258800c80f003540f203c80d4500080f0307141440000301c00345141d4200c0c51140d1403509040c14011132407005400964000489034001400c02d0703e0740145806000305500100306417205d801071100d0703800b02030001e9055400c4000220403101c40000c180b001c03650803038004a90344500504580c01070543c2c4524841c14041e81d4458001c0c40781c0655404191481455214942041e110f00403503080101d0082c480081c0c0c104100700258a0300f90495001140b107021906c0300765a0303400c005002c07a030010040590907004403040103e03158043c04501c004118400c05903203040207070500703d40c940440c0e07a203180003907580001042c0c0f1705040340e201382c0800e9000707461103a03120410b04180c2c910760 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 923671151 1250 923669901 923669911
    0xd0b040b0106090f06020304050f0303160f170403020108040f031206030308060a08060c03040f060b100e040b031903031d0601032109050607150915140c18090903070501050c03 77
    0xe14003c0000b0718090203a500604807000e9070302950506051404102c11803201104030b503418482800782d404404c1e1b260950614aa00c600881400c00481d440c0a40007410502c4203000303004010703c01040981d801140055020398490010030740c400b2a460261244c140701c444d90701c005450700c2004410941c2000ca000e00a420882c3d2080038643e0742c4003083d0341d5060444012111140500215000035044e5040c144941c0c0320300008034000c0003140102e200c02105113520b000203130040c4070440d15418107214245443c8001d40280010b00d85031540c45444d01e040300401400c02d5511001940c0b144003081d01d0b418902c00b0041640c000c0c0d40e5a003445040d808d1044030100504030760030614250107004200d2007045403030107404982003000c50740f22030000c0c010100850743d209413101000d80001c2c080a034458140001c1c1540001c0c162900280c90030554401042c401b00c031401008011289803c0d8400050707001011a03511015a5500f10a903055000750403000b05a5800c010501c00360000380c1002d14820 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 923672401 1250 923671151 923671157
    0x1060504030501110a020a0f030909110d29120f010c05070308010e13030309080d0c09090f05360a150b0315010e07111b030607080c0313020d0b040b0106 67
    0x60341d2130300100c3c4254454407100401580c000c08082d00041d0101e0808050340340030341440d42c419503503039400c0c0007030f074686160b01010b8a4001401c801020130a200380800c42005204a00e6107d0a9026103280e030340b40001003e1103200d4044084080f00410800c006a6841d600c0003484140540c900250260300051001c601149004002007100202140020b01c65070511005010140080d07d0590050810001c01d0b9141075040001d2008100c890003440c00507140e6030341b400c03802132030218030030300700c1d0300c0c0d400c0e20300f0064240740a00c00c00e1803803540403950f010407108804411a1500e034001c01002d00c40094410180150150b00c1d00303001c009000240b41e001d00d20380c24004441c0d10010591148140e52144070088401e40041c004824000041a4403070302c1402c0c03041105480071700c42460458445140c29a071000700c0810310b4a403c0501c41180c01c03010f6400c0051035400e01000d848260f0100415104618442d003110405654501d42d801090302c2e00000c10815504040c10000302440c000d000301d0f404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 923673651 1250 923672401 923672411
    0x301030204180305070b0709081509072114030c070f0503100c08040318170715020309010f0807120e0309030f0c0f1e0613060f0906050a0c0f0b01060504030501 70
    0x26000301c001a825019810faaa0074581045d40d5110300d0f800d0b4010f0118420804a0000803624100800c8a107001c81e8959801d11580e2502e10507591800015030015003022100001e0290b00e0070b1401b0051b80d5041e131020400c10b10b5802402c01c039165000b00f1070a0300700c40c4a50500050b0404800c00b0420a0b03c0c0141c0a41c0c06128940c490700040e100ca8a5074500010f24030b00014000c17901c110000d10f5211034041ea600c509580d20000381d01e107000320b0411b2410582090108001e5002c03030f600c0c0307540031030114005541469000c200180c03d03c01c3d110200018044582d0018801a1052890000210b08070000f0410030740003d94840d03680c0c000d80c0c21a4044d00c03420313044104274240002c181c862903800a0040710000175000c10320110550200042c0c485500c07000d180c1c0382c0f60352804040c0c0984078000c6a500101440d01e05d00806075400386d2249000e1200301c8400303101469000c012a03552104905190302c22510030310304505422100c0b60042c018940070000414007540c010000d0045900503802401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 923674901 1250 923673651 923673671
    0x1e0f090f03070804050d06060b0f0c060f0c0405010c1a040602090909060103022407020d03020c090c040605030103032a0b1006080f06010807120e010b10020a1505100909080301030204 80
    0x541d0b803140410140c02420284420001c1d80b07080d0303281d001d1440c4112004110142d07200708a40ca150060140749420400100348003410750420401c0a60240303621003440c2d200c0c28110003104a52046014044c10400082240c0e802d12490401c035060041c1e17203075040100781c5000d0406000a410864070644224080c0000c0348040307400141290503a60002c24952407a02c2642c00a000c0c03460081c5002c000078018482d52016aa817018507000361030182c2c003e4a40c040e4214104111150020020a1856000d010601030302d40c0c840c00b540c1c1529418185034101a06060003241d0071000c100e40c041d02100f403001e15104201080100b140076501d800410300d80c840d01da002c255101001251008400c40c02d0f0f10010700598414401c60ba00b01c401c40c10145000c004d0f40044805942c48418140d0310b50b9103901c0d84d0b2101d410300040f11240714200b48090081070a0796030360f0000d84001010366101c6162114003040c9409507034100100180072000c02001217183c1032900d0380558000740301c107034401d500c0e040400c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 923676151 1250 923674901 923674903
    0x50403050a110a091b050c25090b09090604083a0605100c02060d11120106020c090412031d030a0207080609010608100203040807022d030106050102070e1e0f090f 71
    0x10104176003001025080880300b060485075504401c403030110303c1c4110306001c0c10141e04603004441c3e00c080d0101003800d039414040e81200752200d8075170850250080c4003c000440002103680364005500481041e034136031044c00b074502c182090200305200c142c0400408581d900d00c00085e41141c10110006200d0156204100040c2c040c03040500e101003031103880008014541f0f40c2c0101030b04440c91000043c2108150711000040d0407502003950310880080040c003c03560100851800300204444480407031410b9954502c2c00120480100e09254480340300408a10f88020443d1a83c2400811070343c0720723404180025030b91011071103000c845008582c013043c02e105060042c101550b1010005180d22000d5500e0f0800940c002007041c1d61860007444500d0040c3c0c0c0f104441d403800c0003e80e2191501c1d400a41e05001583c0040312420b21980c5000d90802003a40c0104024040b00c6080c0c0110724150b540c0b01404a040c1500c000c010404901c6a08010032590b420030240e0150b808101140c1600103a80801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 923677401 1250 923676151 923676161
    0x14070c06021e120f0f040b0a0f030f060308040e09010e03030a09140c0307170a020607151508070b2104030807120c1704030314011401141810050403050a110a09 70
    0xc00c0303c000400440c01250302c014014088801800c114611702517039540210800c3c0c05c402d1000c1c00160480c4698545a50303d07008000c0c035110340d460304026040c503541d2124044c0c030903481a6004070300c001c070000e501c0440039030109980707240801c25650340b03190018440d401441c41072070440c3d0011100c550415030400008554101d5840540100210350a04441903400c844d580b960319040c4c85215001c80068072020041c0603401c0c820021350582c1c0c69031880c3d02091b41e02501c4000803505030600c1c00c1041300341c001882801c03030320349050181d45d450340a0800da58100700034564641701c20340c2d90180010141d003c0c40f00c034812803451303481e002c043c00940c65900c140e4011600c143d00142c8181c105503903817a01c00360140e420030305c0b0f414009030500640000c40340d884801d80c0280b0301c041820054400e81c1d600000c40c0d51200e0340c1d03006524580300d0000044488101040c100034000c1a5034800e2240c41401642141c02135038000080342c000b000c00385445440900898209800707403403110340c0090881858050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 923678651 1250 923677401 923677423
    0x14040b04051f06090e0a020717070302070312020313032006132d1a09030a060b030c0604050a09111308030a02010b0409120c060615030603020a080a1214070c06021e 72
    0x1000b041619280c41b140065005803500f520b054907800f03180c2e00d812030700388002c10560f032007038000d00070803480c41c00c040d0034001c05007041d01d083d500100b0505107150741240c0b000301500c2c0c0c00070b03048006040849090a001041e0450141c1040002600b4a6400464042c4200303c031045481508030007032203111306613082d1170100c07110724860b0761803000d015500c5120702610b4402e07180300d034460600b400c00000070700d4500d0702202902d04543c1d4024400b01810180000c80c202001903420510781450240424910304003446540322484da00d0f60328002d20340541084a00e40e046039050241c2103030721440340b1038032640440d28500256290494041807410180580b004c0bd942008000c2015070700d400050f10101c040b03100840308642d855102084100b10800c001c020301c2155500058400e0851041c04640003140d0018003050b40040300282c00980140d0400b03990030514134100c00c0300c02c481c0c082290140140c120040c8240d02c442da002c1045640085c1c001c503a8402c100c0d481240c42c5140000359281c09030002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 923679901 1250 923678651 923678669
    0x606050301140f2526060310110f040b040f14130203070c0203010e0c01090b2a03040b030f0f0a0603080409181727060414040b04051f0609 61
    0x1c0c0c4480b06001c400c1e6131050b2000c0e0101c66601340380c1e01e02c036282c20143d206500484c00c1d000b40100c0b400c102030124049261088401040b0781011070001e955013030211401841c090310b80c040a00f079a082c030300030b607220b0030828a5001e40325915241a5282c03074126001c0c040607003540080000c1c1c442c00c414943c2d40c1e0684040c06000349103510604410207980000c000105104a280300840141c50910404851406060251014407034120004008a000c0e40c003a69a038401400003105990a480d50703043c3c000072020f8510703402c03240c0d540154118000c5070300450f281280030007040308007020080c046109500e00307400100942da81802d500101da0841c0400b901009080c4401e010811060384041c418420680e01196181503076039034802c0c070b090051b8110010400120b400700b11541031054010344c07210b40800010082c0400004030f002030195215400e0300020480b19050369895a500080502d00e01038014412480d06141a24042807040b00e044080c0301e0107000020614414001c100a0300c1c8089 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 923681151 1250 923679901 923679941
    0x5101407051c091b030c0617040b0609091501030302030d0c02010c0c1235060d0308070e01030e1501150e0105040306020c07080f01050702100903171b040308070606050301 75
    0x401a9000f8510f030a011a0007031908020a0034124990b1096001140328200c0025110304203400100300c4214403425403012020700c4103100008458591a903886081030310804450343d590b0003d1460940041403d003a0800c0e01000401456400f000525419910900500c4000c1c0488412803c9521358a42c40780000c0a09045400290900c6d840b0000c1c17404030310701030304104407150000b10600d1030309a003280000c03040d58180500001800d03085030300c1032040341c4a4240b003001e910060030340c200040c0181c080003042440542140e010380c3c04112026801403c031188846094001d900f5890280524100030b80c8000d034103d0128031484220180e441c040e5281420545199a00310194104144c10411030180d04000b0034210410011001c20400031400411282040c4034040c0c00e00d4203425004205038103200782407000c65040324240ba1500741c0812004016034030300c0314001440806140b82414204005400030600110201500c0c22300e001e01c0040014030768480c2094202d55000c09044c00070102c213 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 923682401 1250 923681151 923681197
    0x41131030b04060b13110d0c14070f050a0b04110102071a12060a0e1006030609060510052a0304061107080a080705030705010501091e11090f010306030510140705 71
    0x65001301456081c058034094400a0b0750007143d06403084401160286240441d2904104d01a4008c00060b0360144c01d201606c03400e0b03070324201b02d18460180c1c0030300340c100001c42c0d501c100b00c410080e000f16150010340d144020b04041c64107240403810300b46024010300c1092808103403a61120041e41107c84d076034043c40e1801c18100c80d000746041004002c00d602000310300c000a440e0490101c8544188206111440305908200001c1c00b1100c094000106091404030188025217a00c0d001d01d000c0c803528100145c0b250600000b02400c040309180b503000a642101c0f84401c0300500001900a4544a0b11a0301c1c000010560309684d035041441003880540c844400d03407001c108410000c02d04d0600a201b40c900e0200703645c903083d0945000f80d0048003030a6540300da01040030b502082e4801d035510501340500c2501500c9c4001c40721070045120062144840c40c104807460381c069400500110342c800140e844ac1401200880c0041203080071005400c071030325000a65641c400c00031a0b08080c041081c00c6050844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 923683651 1250 923682401 923682413
    0x1081b010503070c02030c040203310804030b13050d030606110a05071e0b04080607030c05090f060f0403020d060b01091e03060911060c011e0b010c02040506041131030b04 75
    0xc0c43c6400e90b003500031110381f800161190b00055210b58907440d140c04450450f6062a030b02c40c440d00100c0c829181c8040002c000140a5008907401c490704160b04010903241c0d07001e21078078900030311402880c9200304009210043c0d09600076000f00c2e00795465002105888441e80782e15500503460061581d0449a0305010034113032140e000000b0f8613118000c5040e140c81c0c06106080740d01c40d400c0031116a00000800c40015458010321004542074030300b0070709015110000c141c0340141c1e03c0f01c1c2446110042505000300c1b1040c010b03200150340040584041e01802c1c20314400400c000e20071240041c0c21800d0214511110105604201346801c1c00b403080705180d5110040140400b11045070408404060030301555505000340c42503c1c801000066a1900c003203400074880350706003864940c14204442040e09030703000003480180903016940070801d9510314000400030881d103d0012660000030550850701c040164094580c984040481c0c000a95501028a440072042c4802000e10f003030040040c00280c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 923684901 1250 923683651 923683667
    0x60614150f07051e0105040c1502030a082d0103021512010306020702131a040f0e07091d010606050c16051e0111060c0c100507050403033501081b01050307 68
    0x4052003e82d4400610402c42160050320704e403442d400b0384c0d100c5040c031091046a03400e140083c410072442101e0f80c0703092003000c0c4d00c0340500720800c0c0611281c0b100180740c5803040000c00c042b40c0c090b804403140c0b415a940000d01c20b110300b0f0000703901650940b00300fa075076640c40700102c1d0303503001001070540510b80c80d5940703000181d400301600702d0300b01e420916038518800c0d40f4003400e03412a0407501ca09400202d0901804101d9041901002409040018206202401103551429601c510a010405070603805260899031050741c001142c540c42c0017400107030943e100001d4501c40340507400b540e401890400740070085015a008031035002034001209000525900040200303071300706050256079800442001d90501390708440090385d01c072000038271349605034040c460f40d1301ca9a410f980800c55800c15a200420301d008500005082c42004940030b020b081440d55000c26504145070030030154038185040700301c9100d00307105081c582c0c4074401c0c0000c0c1c2c461103208041180c0710103135a000d04554416200301d49810f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 923686151 1250 923684901 923684903
    0x504061808030715110304150e010516120e030c070810140f130f061a03010504082209050a02090915011d0609030a060b01270b1b0a060614150f07 64
    0x2a5205500c5c0181d03007a620180d0b10940c003405004941c41900703c13600b030540d00450b02285445c0d2400e03041150300c40d111460246218100c0c0740201012007418200d17001861004403407690351001003502c0c844031b90700181c010141c603242c00545685d01148010481a60341d07600301301020054202c001000380003442007a03540207121081c9640800b0480d2217041000e42c400304251902a1156902014900700031800c0b02e2020007070303008104619083e1100704240c013811210005a0703040a14940d0700f81c0001800001802c003001003003040f4141020302c44020f62021000301e0103001d0b08000551044060001220300b0304040e11152400c5841e01500c10701c4030b8003200040c0c1e21102c240141e14660b03c08104405000d0300c80c0030001881c116040001d00034a6120500003044000c06402805440c01103504800b01c90f0cc040c1910340300e144c60300081c814102e081044042611601220341e00748110f03074200300111004400c80721212800a428000c2142c0c04400c040c001d200104010040581041c000b0300c1c1d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 923687401 1250 923686151 923686193
    0x30105090a02091210051e01030b0a06080f1f0c020316080418050a06080d122a050307080601031a0f03030909010b0d0c0c110409050a06060605040618080307 69
    0x440114005070134400812500e140642c03000e101d0003840000c1c3e1250700e8000480a84624112030f05038084c403580300c01400020710a2840710701241d01402c150704000c0c094071021064030707105040c40300c585a441c002d0030f0403502070080c000c0711020701c2a0240b00d000e03802d14140d4083d40c9021080d1280420a40b2a01d008856643d01008000342107580d00400c0c03084030091400c041820b040030016103090b9580398100d0b144070340000110711a030b15042001e13000c10071040080800e4044042a1981d031580000140c089620302056000c100107901000540c03168000e07445034240c07515084011400c4421180402030f03800740490341d030800c6140000f03261801482c01403c40e880d090f103040124201c8882a8040c1134003150100d0200d000084500441510180741d10b07100c0300d914101d0b12010448041d07031402a001d01c2d036a8041b2024040144800422a41c00400900c81e882d69100001d180c3c0c1e00c107101d4440052110022040401d010781440002c0750b00c840002c1d404c11380151103080b040d0b031503000c40e1100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 923688651 1250 923687401 923687407
    0x160e010f0f02210919051008040c03080f030402091303080117161502100c09050f030322050406060215070f2318121b06120a06080d14030105090a02 65
    0x111160401c40600f44040d028484c0c49031074510a10428240310710492031207180700c41e0140441d8541a030b580c1c82001a615003017201d500d941c1442204260280c01c00f8095042c005022403004007a20025405184240c07500101c1c0d40c0d030350b00060100350880200800091403c0010400d012058818900e40807042c02511584036180d803d0500000e05588040c440c030914082803020315070107203d081230b41000420144111a030720100107281e042203015036882055160b48070312958608005407403800702d002a5080a03403044c882d0a002000d0a03100702d9205a00f046404a255880400d9009400d800c0f00100079480d21051015110b0200d418603140070030050319048107119100c00c200c00341c461000e10300319070f84001c0400e6500f03410540346011802510114100c20304200c0004120101001d980c04802852400340c000a1507842811003044240806c40c0c14411805131961028041b80d03d040120f0b80c1049030240207031010400020410000c00080c0300400503400d00e002074580c021146480149 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 923689901 1250 923688651 923688673
    0x515090421111e0105090712170f03040303060f08030c151e0709090b01090b070311010209190503010b01080903220b04090531020409140303040803160e010f0f02 71
    0x12401030f400140080d40c4180507061400b1910a20505410030168005030076500c5c10070b02c00f1104801c01080050a8201c5c11401c40344507a0f1510640d1505000c4814560741d030305082c14014054a4140039210b010f0a00740700002c1c070000000211202c01c0b000c24090414401102890452500028a050161640f4a100d8022171403403044441c841c42c01600da10090382d041c40316031400c603082c03480168180558100c0c01d0242880c403174265210309a0618050b601c07560f001c5207036806401400c6445400034980600c2c800302c00510341c402e2040d03da090303000300a807203102c0300119640f280070b0341c43e003c50360820000d881040464050705128111a43c45101d03c1c2c5c3d03644d6540c202203030b10550007090000d9030341c0309202c1880b80143d2a00c00d0741200d071920f0b55540c0250340401421944500b00244134030740d035240a000f000504142028041c0340182a03d49034581802d0443c40303a03004480e460821000009280e00060241c1000c40c00c0c1c01c01a52404820041c80c0700c01d41d80745a2850708601944a0010408 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 923691151 1250 923689901 923689903
    0xf030b030703030804080c01092406030c1211040516020114060f060307020127021c0512090409060f02091302040f09110d090302071406040810090c0e0a051509042111 73
    0x8146907100304280e14014440c3c4002b03003014a00c40e440107920a00703001003080031559485c06501a160374054840001d030161400101e41e140c00c141c615041800c11080007561070601581c041c904400d60002c0c44100030305481001065000c80e80b6a1b80020481040d4080d42403000c081c40d441441400000f4400e00c0c42ca484540c1941c0e6a4a80c001059207610780e0021420a041c68400340c0d400c1150104141119940e56900c922084a104c05485004929541a980c40d500100072494101c001001901c2000620798042e612071480140104241c22490700395000318400c40f002c07105103200400079641031503021030240c100386140f940c80c10f00502510070031a84510405001d43e200c0e070000d202d0707549000d01203601c000a00d944039116041c240300811103040c0c040f840c840c040040c254000f03607524040c5040e100c24403981e0010820604045c0401c0907a40e00e60b03112900804c6c0754420031036201800e1040000380c0d8000c0b20001e142e0313240c0805101c240800f10400030000d006d6400c0c240c06000d42050a9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 923692401 1250 923691151 923691161
    0x10110d0b12013b0606060901021603260315010c110612010305010e0d020709110705120901080c1801031122030b160807051c0e0a030f030b030703030804080c01 70
    0x400341c0b40c0a141c8804009403500c40300c0203c0015003020b51844410140300d2544500004110ba80101000203802c01c00d40c6c401d0048800400860002025451b1603003089106480344c0c1c1c084d03215a43c0b9445140801c16000c0c41620720581024092801d0031091800442c1c4e080c00412080354441e103c4005400036983d1940984242c82c0c4080c40c0074031640c5075003000742c00d4500001b1900801c0d0055500d00018a0380810510192103585101103010f02400101403002c3c460740e00023074418090321a92060820b4424010215050f0990350303070308140c40b0102d4000d05440b40c401280c00c00002002441250350203900b08640c001d0300d000d40e540c1031040500e112030240540440caa41001d00e000c1c0180104071a070700201350044144815090405c5d1848806090f014020301050184100407a049440c0414018038072040c038680700040c860f140403411030345c0c0d40f003514210450124201c8529107050b50720034031034490003920080042000038030b10344042d503103008003501c03e0b5070400d420880c0c400042d000f4054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 923693651 1250 923692401 923692421
    0x1207032d0f02042715050d08040312080f060a06050414120313031a0402090601050304080c010207030c1a07090b0a020304030803040c0f0905090606041d01050708070210110d0b1201 79
    0xd00b01300c084202c3c6001c3d42c1c040c250010010444d160902843c0004641090340e4140e0700256014280c50101e42844480d500455000030030070001c00002103495a403001e4058003643d05512016007588a1104101c0d80490a02a07140007941c28401048100c0343c808400ca04140050b043c203014040700e05885040d940401900070b84100d00600800401102c2c00c5485180001303203c0400c1ca170300b4980d0014904070009050541004070100200b818400034000b1200350000e04002155141c0007441d018000103041ca40a580031124145d142c17001e007404604e035500c101195074414240c503040180c01581500b01c0310b418001c511082c0004000100c81800460080e8001c4901c0302c85076181c0740004c281e1014030380000302c03698107007403e201005a00140c400d820110858020403070b0001d544444241c4005503802c0002c1e50308090a00200c55004145240101c825038241c1e0685060503004c80300f038a1100c0b0415807a0603041045500546080d80485080900182083d030110b030382202d21401d595603010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 923694901 1250 923693651 923693669
    0x1240207030b430f031e021c1a0a050103142805040804080f0a0305091e030d0c030315141903050304060e0f0f0303030f0405031e1207032d0f0204 64
    0x40f43c500307266081220302d080c61203949020300c08030038824401102d45400f0710413002000e1300071500c8030551803e0405101c184001c0e00b0200030150564034074540600030418118000c5c02c04a20204031540309001d02010320346104a8008a92911010100150a0000ea200701d90b200d2525140c032100c0b403401104e008601035043d02d9121030500d0001400e00d81c0300b29181c040c95002c0d0143c6800690407030300351200750700121103803200d50040381140d1829041c155040f65040c007031400329a40319908204414036203802503604104110322909040b0f907510b0302c0e0042d062000004000e9009030318280100c111050b94112007002e11655a940b00c80c5550065088100400e15448680d00c0a0501c00419400700780c0c101e410044803080030380840c2e10b034403003d80300e0a40c00f4980c0e0001404c0c40000c108a5440c045141415001d0b10345a40c0c4250b1950000c9491a040024401c049a8003a01c68040d95191030b12070545205a003041c6640405154980030303100e16015102c0036401b21880c446c0c4054070040c11200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 923696151 1250 923694901 923695021
    0x5130b0405070e01140d0b04060b1305090108070317220e060301021e0c071502071a130e041406160314010602061308070b01240207030b 60
    0x800c829124000d199204005080c03618295907a8070039608a80c4c00b03c00602c0359070310b80e0214180806050400101c0d0f8019090000c0018031940b404002c000d0701900e03000e18104c0940310010001404020310807400b0076400070f82c0a04c007040040aa174140410358404051402e495030a203080d414400c04090b01c10002c148c2c808100c40c90349a69034590014003180210728141244c40142144a0445080b110716000400c14101410342084540050810043c04441c0b00c082c0a1001b9625101c0303000d0a110b2600b0080e018503201d0200060712120304966000c240392504000c40c0b042e030200c0c014010380f140d20004d580e5a011407814441540900d01c25218006d540110300c41c09803d80e041055480c0710008901d0040000c141d0101d40390741c0108174020220851041428002643d005a2001038100e0b000d920001503070071040204e2034010610020b04c00d1b61940300da0740981c0c4684680c48003170000301480b000a01c1400440709500c00c082c0d20400c07047c141e80030b46400d01404114004c0b030543c1640c0c4c3c034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 923697401 1250 923696151 923696171
    0xa050a09051c0c1401050a08070e131b02010b0f1c15200c0604020f0d0b100504200702040504020d0501020a03090302071e0306020a030e0303130b0c1206090903040513 73
    0x215001c3c0c010702020b200e02100c212541d00000c215218030040700c82000315981c0810910307403240e110b10302030302c03001000175a4540c58900614020301011030000139065148056481090040c003440505000080c00580b650798050244072113010703001d5480713183c0c030006425400040d9100c0c0003569000c00117800003d0001c654201c2c841c07009147d2048044600c030a0100f8031000400180b40e50b4401d506a554904001000d408255500364551004240010340c20821580b2a075984549084a80407a0148100e4810721070790811100c445000714070b0f030b850421400000d8100f5403c41c90308648080e000104541c01901c44a089822103c4130000181d101e902020a041d810014400a0b0200c0e050510050800f00e00400e10548644401031140d600810300c000d82c00d000342c1c0407600329022a000e4075960701e410f075880341858a400008403852a41d1102092442d0840d1b0240d52a02c2003081c2d500b00c1c02c2d158174040002010b00200448010b00c42084041815250754400072000300c0d00c030038089641c1c400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 923698651 1250 923697401 923697413
    0xf03050408060c040305101e0c0c05070e01060f030b0f06070602030402090c0306030307030825020d03050f010b04051c0602180f090f191103011205010c0f050a050a09051c 75
    0x10b0010020f03900180010b20108402040140c0c1c0302d0200721002032440032810b010042c1c0d074541107038020701a25060140726520382115a240d080c41c800c0084d611065104d8545c58103260083c0600400190b03941c040720402d5000740d20170328030036600510442e00e1400282c00904030381d000c2e550889401c0d801209000c114100381d0245600700590016040c218984000800d99074000c0c210f001d0100104400403030301c08201048003001c0d03603405d40842c405110031000d010b541c94000841c024002450040002c1486c6841e94440d410303204c081e01050316140c0350500304040001500b50344102240b080c004000016030a1004141c0d0302d0342003501e02c0c400d01c160000c1200d4500540701c041e01900c94041005640103084404591007800c0c0404030803c100c00068010003801948124204e14100000200c0ca440300c070b1006101c03d5119800a00820326041000c546904404c3ca0040c040340b0180414410580548050401c1d55154a00300c4c442c10394400010722091110f802d15018900c100c0821024065 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 923699901 1250 923698651 923698663
    0x7030c09141302150a050d09030905280303050c150108012c070e22230c10120213031401050601170a020f0c01050403030e1902090f090a0f03050408 65
    0x546501e00700305548030f4001c10002c00320f48010307203500c0c140010460511400386055610701d20b941d540421021240d482c005d8400c407800d005161264030b402c40401404a195040c4d000c25071400307036480c000d480c0345540a49083e000045504114000c10080780d00401d0301d40304d03d60080c12550000f250380d0300201c4200320b003560903511480d030b41000058880000b180009000b4103c982d02c85501440741c0c0c03183c0e0a50b501160b60a040c142c108908030160080c88507072540361041c1c10701c2c0407250180004100d402c0340d4910311050700e56044804045840c0340a4011940814440e0ba03001015107440300380601c820341c48449410440f54401c4c0d10b0b98080c01d00c1002d101c2d80754011001e0a02c00c2d00600d00c040d840c0d4400c00b00038100f44c03c2da500050850314520f015000d65241242d940b00030300241c00c0500e0081c0c042d003c260034030485449000c02481010612107180140305030068007440b180c1e1280310302d084c0380a800030b22002e20ba104d49050000066990020a4046401303503451302e407104d04100a49080171 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 923701151 1250 923699901 923699911
    0xd1103161808060c0703020f07150e0604030519150618110f0415020a080f03041a3612030106020f0a2a0306231e160207030c0914 57
    0x1809080042c099084001030080d0054080a403140d101d00c800d103800c07441d02c0c0240c201e024040c0299400001c500041261101c00810f154682c07080503072240040c40345501603444098440e501903910310094a081c020502c0c20345000d4809580070b020b00403051030903034110764040c070924401120b064450100c2d603c22104034a401400e950320740b080c5034000b11603900542c01180c84852a440c10101114005c2014903a2147c4c4110007031b0320303a0540c4008503226001141c01391940d000d00301e00701e92032145d0002801e200c0c01003920340901101e545910103a80141c1e907032800c0c0c2c3d4550342401503905200c0410400c103415140d211000d50b03a6050000003400c0c0720003040c3d900042d42c007500500c0001031044801403030348195a858480d000d22014450090900300390f002070441031610303c404c000c0e15114400d1403550403588002003041d0711069051413426142c1c1b40c0c02c0c01004981e0000c41c10251482c0c045c0800c0e41034030710494101d180c982c0c03a01c0421038900d900150070b207a030300d5134442015508030a036241c0c48 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 923702401 1250 923701151 923701187
    0x504170c01020a0212100515040f0608070b16050a060225020a09020d0b041a040614090a020f0403082a0a03081807180e070b0705120d110316 62
    0x30641280010b0754440e4004070003842035400480390b0b6400c4da07003003266003024980c0c0607061085050100441044001203820039000b9820314080c01d2600005010301d07411a05800024100c040c030302109400250480c0c969450101d101c00c10550224008014100c0d40341d000700300041c3c0d5182400018848810464000e01c1489140115000980da81a40701c600311400b440c03001d81c0c1ca20510a8400040c000d95855583c080e2074036011a00c4440041020030000c40c0c140c408000ba580c079802c0c0804200c04100d42d0701e0f80070341c005000441122180e005002142c840700b01071800c140e2240d846041c103400403111806500b01d00304104504c0e400c0c9507541c01510009c400034040d4440d590710002c1c10620f000700f14588000002c0c2c03e031810030340d0801c520001030401c0c04900001091000081018015402140c140b9202c0d4040100c1e0043da008201c0e03001983c80401401e0311584205440080e81180e456448502d99419000c4034031100300000318403405106000c2e2203621007403d0081c006000c04913880d000c2e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 923703651 1250 923702401 923702413
    0x1501090e0115030902040216050708010e011815020405060703080901050711030d1518090c1e060c0203190809040609020307090302010315030501020c0d1e05090d021f050417 76
    0x2e00d1000071068000c0916103000f1803c1903890020030068840e000b50000d510002d940769030148003000c1102000d44040c41c00030b00644e00301e0445103099450003c180402001029000b00c0024400b10b610301e00030403034020160525030746400203001c0e5049050185d010074003000400c2411042841502d45c170203e9420944c04518540c0761480d624041d001c4002001d40c0d8403080c003406510906024002003944005a000d444040354041c030151180c04004c498102c0244400b14400c881c80d00c01c01e5010f2061240b00c102c1924000084400165040042c0d0701402030703902055002008541020b01075000e2040180d44284040c1800100c1c0c02e15403210520b070744144180041994890544412690240303404958140001c0380c004002034160b0005007150303c0081e414600704004510380c80940c0300e50300c0303042d440700c0d2801d001c2003502007600300b14001941c01c2202c01c03410302c1c10020620300240050a080d9000b201d035184400e034000c1044084012420100b0100003d041303c02c15040700b0001c00d030150507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 923704901 1250 923703651 923703659
    0x2707020616090e06041e0c02030705070f08151e161818020903070803070b0105090f13140c030114100603091101030c170411130510141302031501090e01 67
    0x48824010708801c0c801c5d5160130b0b1484c944d0840d1040c0b100d101401314030070803116130701c08400381d665400380c00211814004d0401c0000c0d101c000c5400b81c0b0031107000d00081c04024408000340780e03240380018504e00b002210654480c4500151032074140c40340710003503580c2d40342c903403c040050f10595400002a5a2121a00c0b09000c4040f20341d1729407001c050003000c056112490346c1c0c006803c1c00115008040031744004a412001d003c10144440e0490308140c408510644446002050056080356030000c200c1030b922901c80041c2603001ba00d4184600c132029503d51911141c0000d0035503000130f20b5003001c40c0158041c001d401032104443c2004026501b410401c503034003943da40a9600e070000c5640d043c90340e500d80c1c01c07a46034011981c00001d02488012410146020720305011010354840c2468020011210318100d415454802c0318024441c1c40101440946005405016018810b28668008101c2040d20480c000180050350040082c041455610004100010b2a02910754800c0d0320603051500100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 923706151 1250 923704901 923704919
    0x71206060906082a1312061a3a02101218020d11041508060f0105040e0606150408030c010605032e0c170109050912090f270702061609 59
    0x3e84892000c450f15104c0410305c4400d40b051485a0000024444800c030741c104101044d4401c1c001003508500100301041058140005802c000c042600048055500300e10070700c1013149070700600d0340c40e820750558001e0640d01203160100c81c0c48014021556200a0501807019405102c003031000c00e006031142054141c0003d07043c0d01c103080c2c001c2c100c0102c07080301000540381c540090713100ba80c421486040141c2d07100980d650b00c400032694410580c1c42080007203203d16007070054202c0c6240302001004251240d100704400f1918110449040c1c1008100c005181241480035082e03481c0b0080c000030328640751030b06046c24121281e01d404501c191340804a00210300101d2041c03280840254005010404891b05450403803d0050780c0c0f1400d00c01b04000107405031701e80c11080c0b15121040588603210314120403404035019034000294840c0b13100c82406840e06040050300b1000c0c4000790b442c00c6210f4001c0422422510540784030005030440d07410810310a000b91042844502c2c140741804441c2e01e048826 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 923707401 1250 923706151 923706211
    0xb07060b240f0f040e010f150e060d0c022805010b0d0c06050f0405150702040b011409060705010b060307020d0207080601081209030a060c0f11011107060507120606090608 75
    0x80a0010b808108070f21492416420344000d411694000025540c41e034010340e8060841c2d1203084d507801e00c15400c00c9140e070300c00c052200c00c680713002d02803508005845140300080c125401541d03046110b245d6089440c01540086c03800a034880d115030480042d1a400c2040c01c0d00e030102d142c40e004902111103c8005000c01d0048000c50b00c551500a131245c40503038028407079105540c0441d40c8454000d541d600140e0900b4004e0211501c200d6040010f10706800c010f40f01c09118004c042c0310b240041c0100c00c1203092080c020b0105511038000018a0030f40040003c0c0700384c00c03d5a99100503802480100b0780690100003060103020084000c0c825580b5124440d0b1f503541411440c00048000800d000407661400c01103034041c980e1003102805208003404005203003c2c1c00d0410000014040f1f564410002811b101d0040c0c20702d410480c07640307405079a85401f005041c0c082c24800401410481e11074a803407a82c410400540207035511220f40303614000001f051000041d0032090003924102002002d040c2500074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 923708651 1250 923707401 923707417
    0xb1306050406170c2407301e1710050a0e040503030604091104021209011b120908120a021206040212040f021f08010807080a030804030c0c0b07060b24 66
    0x40d40941100d40041c443d54010346080c580c5c42c8040100b00c10003003101100041c0402d2414040d4010040f50000100c101e0b0b8080381d1440c004114400811a1015090440381d50b0f01029400c2808100080d207103801d102c820111034507035000700c115038240194985030002c50300400440c40b2810860415071a0740e51203102c0074003003d10859940301180300304030b03441d0502c000307880d00240f045480740b030042c80318040100211898015546000640c4c440840e509008848002803079540c04404882064203a00030320751094240d407120b00c144805000c00221020440c49480348250150312030014040845502e9009424584624014083c600002c4890101140e0164000c01512007040007800840c1020030025004840d694240446409140c0c114801d14103e45201c1c1c01c448003c1e0755000c0d85500d43d160054001d000503418804500840c0c811100400c01d1381c0075444005e401c507501c030050803d5030f1101408071046038807003c28200301c0ca4591103070000c5000e81c2c2c00b820111608607000034240d03c01c4000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 923709901 1250 923708651 923708659
    0x10020c061b1234020601061b0b060303090a080a03080c1828091e0905030405090712020a0f1b02030c060d020705070605130b1204150b1306050406170c 66
    0x10020302030b5a01c6050440c802490420b2415000e0110510b0720b03034101c00301d1500f00143c4108000021003c0c131400540c0e51040c0d1005954294008590794148814005040c186e03162109001d801c41c683d98030840305000703105140051142d04194030300501242d5009207440c0c03980106204000c480313a966000ca0a480c4000c0350b031440c0f01c0f8014008600d07000440724900e1019206c045012480040c03941c071801e00c01e841303446910240c0402051442c00c0d00d90140300142a5001400200214103091200680082d00c0e4100311040380c0b0b04031501e404982150018000283c10707a82c101280c0da821640b02400c43c2c14480c2d601585242640200f9070310b12a00306c0183c010074001074061040000c6a054940c49a400700684061941e07601000305503420242c1d0503040c191800c4070000e0746c1507040c012215500903003141c04956a07a280c45611003074540c1d541145010303841d00c00d501910b60303683e200c0480c10404110002001e0341080309000440b455500250302c0201501296100c44400245500b1041c000711 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 923711151 1250 923709901 923709937
    0x15040c1a0a030b0117040803090c030a1a040206270f06090a060509040209090108060403110a1a0a02040305010c18050102030f0d0e030c030406032403030f08071110020c061b 76
    0x43c0101c0c0d01c084845000507400c4205414001005801401180640018000c842c0c5404a8004140c1c0b00c4060600040201103c90700504808c10510700780c65000340010822400c1003440b00f40751082c0032958184d01d02d103003d011490a01460300902500c80709105403409404c0c00440c901081d1202054000c0c1c10070b0060218502940340d44070b404a0b8a00384015150806550390741c2e5030076070740c1c4005131000c07030114281e2160005c04200c000b0b0307452119038104401284ca0444c080383c1c80c1c10074102910403c82640c0070400480460800d00070388410020b10303a03d44404150740d1101c00b0b80410950401c034115041044405c80c50080c1d082962500307046a0310024003a10f802203600d2445c840c14202c1e2130240808580000c100cae4144d031108000c00c882000a80c41454042c0d0301c0c1c40540041d010081c00300f0650003020034440d12801c480c40d408429401c00300181c0f01c10200c00c074039040c1002c40c0c0d201c5041c1c0000744041c80341c0052001e1a009150707444110028040c112501016000d06890444003200c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 923712401 1250 923711151 923711171
    0x10c0e130f06090903181d04080c120c1c02011e0f0e2a030a080a030207030e280806060d14100f02070b060306162015040c1a0a03 57
    0x1d03a00020003460351010800c010122071801500842203d543c1c10002c4e9828240041c00500e481d142115003c0e03160504291542c503039690f00e055402c00d401e040b00b0b0b07114000c3c881511441110041803131100190080140f4044030348220300e400340b0705420304116410400000c0c9203050140c1c049215103914200415400002c2c14450010100d4414200d85c03845010400010341d844105002c40c010040308114ae0160300700c000703055403612080e6000b40340140801100e00210b20a0f07010301100d034864540780d6440c079007010004c2c90100404160070401d0455600e210381d11201072910758010981c59014245500e41200000d00000540341d002d4001c402c0d0340e62440c140d90052003206030b4221001d904008164240c030800300203402c41c56080300d20b90010404168180b03000104a8400e1103111303032011054101d06411541070800ca00c41000c400308181014018080c02e00081e524044841c2401080d460a41494442a14150b0061f6402c542c0c2040051828113000202e40302c0c0300305410041600701d22 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 923713651 1250 923712401 923712431
    0x21b0d050a060f06062303040b040206090d030504090e0f0d080c1207020606040c0203090901291c0b10090614122e12060c0c0f03050408010c0e13 64
    0x48081c004102c1c6240c042003007110400341e88108251031050390350340030505c03200f04241d0100d90b060103412940d0500340700103000910b03c5511568801e00c060290303800d08580d400407030100405440203c000c034001003002c0c0032020851240300401d5000400030450100c49860b0181c45061507aa9001041822400600100011012607000c0d6001692101003454240e00003902e0f40002e0b14401e224500340319014240510020a890860400508501580c1d01e044c0c4003100e20b0300c600301400b4408008080002c14540800003810062154a043e14005040700d0041001c440e622810349102e0072003442120110341e405103500307040c0c0c1d8450a00a0143e1400005907226010b114586110b1100010401841c000360445442a1a206210046a0480c11a50051104c1c010302501c007030f103c40c800720040400c0c0b194002c0c035404030740e83c1081c8107020402d4450340c0c2a11503009060b07000c00d20020b0204007a010900c43c0101151a031301c0c2c1002c11003d400c0010350700c09980c8509060b581d4489052252101c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 923714901 1250 923713651 923713663
    0x4120b06190b0d0c11060a0e0607140a030c11100207110301110a1202190c0b0903250204110301031a0903090907030e011515020f030403020f0d0501110f03041101021b0d05 75
    0x40f460040760f8580c9803504600b0090a01c123400300398035004010215904074001d000c092544440c42c050541046034480046004000800302c2c01e0810040048191201c02c05001303000036011031580150380d450350303030402c0801e0807201912140240e01d00700304100c02c00c0c400310a507003a07564141740c14021900c2210403034019000f9803050903500000c0f4100c0d4524141c1000040da0002c0c8070301c500a043e81e81e590b0403540c40740241c2e5004400c00c132000d400c5a29440d042e480c0e0b10074992009200150786c40341000e01003503d070000d030001c40340403440e00100d070000400e8194040d1b00c0300680e4025442c10101d000420394688010300290103043c0c070358010f1000d10b603080d04520f0b04158152780307241d20107644c3c540d02c4550414100040000d4050b4041606070b2090110840701a01d8010b00310000d081141c80c00c7c007100315036110382a60195030f1841a60319548400006101070300340c18011a44074203050404207003410aa0030b42c28199403009980450003160000c80030082403045a0b04102c61440d8144241822 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 923716151 1250 923714901 923714927
    0x21f0908040b1210050f130f060b09130204030203030703110f060403260124050408010f0902150325030605060319050f04030c060209010504120b06190b0d0c 69
    0x428007107030100b00000c030403000d010760868120080000c0d0320345000909040391140250341d048101424105034500701140c03201d40503080d400c0300103034402000814800702e43c2d080d00000850039002850395207510341003034190a1210380d0081149428a1640000c0c0d0302c0c071450030300070300348240b000d0400c0c800f4800f4003408046011040a6940c41c0c500382c54010142d81c6003550b400c0003100f00868a40c58590ad10f001d8a040e1100d03400350203185200c400e0540000740c543d018601c2040b004000c003107000c070820301500d1b044c8000c0c0707000030420160a1041080032007540300e16016140003842000a0b04101c05492105a0301c10070200030032024404044000d00107541000b41c104a0001c04d2000002d1440c0501c071402d12440004c120944404c840300f51a5581a20050000303882ca401103004581240d008041da0b2b001418490305e402c0e91818007070403c0c42107039802c0d203000c0031805c20800541410312461a10800380708080744450b0406c40300c04e14074014504100c800e140d58a01d07208046000b42e410300303101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 923717401 1250 923716151 923716163
    0x60605060a03062301020c0f1f0c150c0c0303091407030f1214030c030601170a0218090c0a030f0609051015030209090a0b011404141f021f09 62
    0x1210500c0c00036000d00680d10540c8000030407045030000211114081d1203d031034050740501f2400b00c41804000d17219418421660740304400d01e00c440c07050b481480480640407080c2d10b0790310720842c0506041c0202d6026031007040e0054100208910110751020900760090361504001494100506000c0810204036003410712074030030113001201344030401103046112403081402d820100080142280d29070010011100b1402d0144003140030000c4110145600c04418500001c042c81e800c41d45081e210000d5405a0748a07500144145c05c40811024204800d03000b0b5610002c981441c5060060340d100c1d4158400405540744028191480103030441c0008202c407410900050504100402010800d0300c1540690810710100820300e9000c0d00075242c00031001000c2d408942d540070204006054442c2c8541e04002c241000c0085004000700500b020740009606000e058411005100714940654580d0129003105145112040d13400500040128400c03000a9501160b66128001409090b00000e0407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 923718651 1250 923717401 923717407
    0x10f1101050a02130b0a0804020616052a030714130b060307030c11120f07031e0207091401080714120d02010504031b150e030d051006020c06040b0a0c06060506 70
    0x250001030f03000340903036414400f803442c400340c1c0d02e6081e807000d4420007a40601242d00c400019016152000c0036110700d03041081c403000311b001c2c80e551f01400c04111010007001c4c20180e014000c0e00300b08400c00f21380303210301c2a401000b18505000d0859200031140c2c00302c503c00e4580381a030107410780c2c40d0340124125a801500c966280e0404900140191130450174503030000f002d403080043c51820019605041c03c03600c103106850001c105852008942c0548029001d00440000c10b040f00054110304600b480007507030145c03a03014100014002910528400c940c00903103a44018040c94401140300b40c01c5882001001400e0881a00821a4001d0749018840309006008040a8003501034102511a501c00e40d07841e040344828080301b2400a40e00f100c09032400401440f96003090840fa8404101c9541c200200c07401c0c64102c2041c40191a01112032001e41440c00c035041003001d0b010485404102d8040340d03180d0500c2c1c1080000030311802402a800208021142c180083c8501d41d40710300090880a04007680e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 923719901 1250 923718651 923718661
    0x60f0b091f03061d0414070b040b0f0c10050907120305310b040801050708040f0f1e05030c01050112031e050403060203090102031515040e0406421202010f110105 71
    0x111310b41085905682241c015815022903100202d0604143d81a8808803401c0c40d0800401100302d4200e51480d4030b061401300310300b0b07805000402007d10b4102c00d246000c2143d10344400c11500705241640f1a142c0103020700c0b00d45e40002d41280a0360501010056004212a80f005070785200320b2400408001220b0084070218911040a00400994280300000d100036107400000b1141140100d4000e01059620f0850100158084a0400e1b005000d4001d5501007001d185844c40c100607402c00803106a40000303840c5540c01d40c20b00400d401044080d4400f21086615100030b040440c20040e090030354440c001c1c07170300b201900403c01e81d13001d1904600c04549900c0c020300200d000303603c180c030606510785185408140c1031500e4038250b100c2c014604980b5040516100b0b180d080c680300540b0854610391500102c000511013240341000111015480400d5218082903407109212000500204000050024804403009200f014505a42841c1200c0050b501007000c44078a41d011401150075420700c41802 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 923721151 1250 923719901 923719949
    0x1002030f04061503170c07050603090d090f06090302090403020109080f07110316060509040b0d030507020a0b0414091906081e0312130c0b0706060f0b091f0306 70
    0x35104034840c075030030028902400c1141074641d0580c40010038203010f44c3d01c8070b2168410070f000b4104d0700d0804400c40d40d034a516100020400e80003103440d00c9403507000060a802d501d5001001000901409100002031400c103000205403622500002e40074041c4071010a0406100350b1006480b1900014071548901d0743c4014802185d00281054036100904500c0c00e05614000c02c0140144d8103240580c001c0514101781501d4941012140b254066507814102001e51034514080400521a540c0c403503840185104004208d1400d4109a1103038905020520003040c00d056801c0f60504210b990802c1c030b503500020425161400d401281c1d00340d0403c01c0001c0ea040c000216002d015409213665444417404d44119590703405141d00c0e00c10007801503070220700080e520034560309441c0d01a5000751342544d100c3c4065903442d40f006a04403180c0c0d0750351600708104c286d814858400343c5071880e01c4a181800d940001444a44c800864503115001c90540d1005540a580b1071001410440018910700c1841c0740e4003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 923722401 1250 923721151 923721181
    0x8070c0302040f020901080604051302030307060507112e06051909050117060a11040803180102191104050c160c140604150804051f05091213060809100203 68
    0x4900850400a50350f8405403d40280c4103d00d1069442c00174690b501400c10001d000080c0100b25825110116080542c03000e0008000c001e014901c04213441c1001c590040a0380003282903c48142c22140011101201c5c080701e9121301381495049034840784030403075a08000d18446d400240d001c1c06444008450500f041c00390710490f0050701040010b1b81c1e0301c001e205d070740106c0b0741d94500a0f90040d100140b000c030029030011358041019200303203007000c0d100c1072100d1a682c8900030480030003402da00311403410345e8104040752071120344116150b5503040310b070307101c1d030440035080501d42c402c9031074500140305080301c0d07015111a85064540401c1c41482400c11520407441c5008110b4919814040300c1c92a0420728100c1c0c0807103c5486108031401c1d01d803c01101d000c0c1018204079001d024800582c410307200800941aa03ea40c0d003240029242486030700c84c1d190001012000510340420f2180900d4121800310b240202c0706982401c0070965201d12700d103800c11b40c2c0c034410912018030110510071048010109 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 923723651 1250 923722401 923722403
    0xb040503090a17010e121b070803160b160c110d081605010f0b03060705030901020d060f05030607030608060c090d1406240a032306090606100e031905030708070c03 72
    0x7000905805c03c2d51a8680588030220300d0504020452080c100c0050205490414081010f0301c440d280c41c1c0b07405a045a11020102d04003168a0544005101107442d24075003003e441404d0341444403a210700645808d80340e00d00070f0f002a00f0b01c1c541500325240c60141d94030442e402411181d94100355003090703c25909102041c0c0e030542c40d08800e403a8859a030312900c400c04900074024403d95031107200460302941f0082110203155001d1050700201d01d018003501c1c000e803050440845040307081909252800e640140084209801d00804221a2801040d0590045000100c859462800f10007051440040900003009140d038207200006071380300890114041c0c98a08201480607418000b1081882d40c240c00044e805030040e03030700300700148428400c242c00350624458030f900c40d030f04040861304215040302c180f0800c0d008a42002514501000b1100007035942d42403030b00340704034543d000c42d6845d0b04684605802e450091482028060204251100564401000c0740d89007d90b1400740341c07e11107440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 923724901 1250 923723651 923723653
    0x506040b09070810080f030d02032a0703122903150a1401150819090503160201021002041413060b0a02070906060c0f1b080a030521010f030b040503090a17 68
    0x9001700316040d0220300c0400b890071001c000c0d414100d41c908034400035803002c0c3c20075444000e49003400c28101c0d54100c001300719004a485040c0c032004c550402510100c50118001d602ca441c00e461400c82c0320074400ba44040c2ca414054100082038100d0201e0300c0d00390b04800462080c4401c0040000e00141508410880c600c4d00110180c1644e81340303001a070381d482c084890300110701c840002501c10644980640201c4180c0a40814806515180c16007194403442100021900c105103400555030100180c04410099000031840e0500d8810451079000702e11510901c100140b03041c840350304606410080c040c2c40d00321a040d41d10b11080300003a40d00c100a02c07445181904204001848034014400e404485400c032010001e050816690344041681c810503440a48041900119600303200b007041042451080e11080d40e1076212038030764500c00010380d54034407244804100621030300d0745a9060808403580300b5010341d5107841d145001e900b14083c8d0102c80e90410002c1900081c1d498000480703c02c0521644 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 923726151 1250 923724901 923724931
    0x70b0411181b1e0a03022104020102070f0b07030e030a0203031611030d140705100606020a03120911010f020a0f0c05120c0f060d020910030b09100501120506040b090708 74
    0xca00c500034020824001d0039031a03050110140143c619008106045962500500d03020307440840d10100d0a10394030300200c0c0e07040b0504120855804118110140107485040c165103071800041c0d08140c45010001010410700c55040ea40544040250201565005081d0f03500c8403924071486018416064040e294000a03a006400743c0c1004243c0001c031f5001603a444100c408108080d20090f405002c08450074466030307042e2196002188100005401540d01818031108107081c014400822511801c00d124030340410344000503001d0030314182d001e00a080002d84076444d681c0c140c0c1003404800c0d000d00354520b09075840b010000381c110b20070162031084540d4903c001203080002c2c3c1e115a01050313141c20401000340d031031030f81c0b918001904400240c0c0b0009450000d0a1000c43e004198017213514000c681c483c0700c0b0b4521450300c0c030700c81c42d4044100f01c12004582e00d46000200601c080c1900f0b001300d26511800f040e0319449070f4004054910000d080041c031805c2c0756000a0245e101294183d00900040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 923727401 1250 923726151 923726191
    0xe0c0c120304030206040f11040c120e070e0a0b010512010b12070c0201020705060919122a0306091401050f090f0f070e0a060e09010b0a0e0705070b041118 68
    0x4041d28001d41c0c15500410070341c0c0d995620781c24590300b5510280c884200e0348212000640d02c0d0700650b425141642e0350740240050702c0c2c0340d00050f01c00c490f07032501342c1d031300300001c03d21a41c4070400c0d1082d4050800f034408600901218016211480b41003040c0200100c00d00010600011b0301c40100880120307007607415403990740c0f071310221a028800d50009006030042d1104020030314080014001c0c80d00006c101421100c00a0701e404030310740c404e80c800d1514010801484013401200c5482482030900314010b00c540004094180410300b45e03d0100400d41381c0d540c000f04042c4144441034410389810500200a582011411040700710412242d000c038504c51031440c460320780408180307c1b11300c2c1c040900420707205050141603030014200406800040e6039500780050404030040951b4060204d0350f0002034a1455030301440b914a0198004418849010040c050031035800070441c0d0300c1c550880747c001c40549452400070401c11295861550000030003052686243c60722040e9401086070b070404021171600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 923728651 1250 923727401 923727433
    0x1a0a021314100e03060a09030e0d06062619050a0803131b05061b032206030c09060e06090312030106030209120d05030c070f02031014101a130e0c0c 65
    0x1601c215404d0f4000728046140c4d200e01e90410082c140c03003420411a1020702d2030202c0d2031030240d10000e8903001d4031000304210300d034619040d100582c011344203405411000845041d550f201500c501d0300590501400c83c000f44601800740d81d0b40e203a8802852503480c10b2410311a04200114041034402481840c10b0080c404011001041142d001038580344c24004901c1040a500080040f828054002044080d00382003520121007800300d200a04852810306040300141194103619502042c060300e894180440c42e04420220742c00c1074100d494503034590307084000c01e080201601c0d4180d0095030110000c00c8007609500076084848042d25a5000c585200132201d665625003001203011036020000700b020501c7c9940100440e60043d82d189858821b59804207161580b101e1040358640d41d0784c120200003064041e0550780041981000780034280c20f006c81e000c03880d507560181001c850340c0007403140e030346640d00d824003401402c0e407100211051500d82e2082c841076001840c40c0d0014040c400c0d44440041c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 923729901 1250 923728651 923728667
    0x113a020c130b0d050303090304081005091c031b110c0103272619031a01030c020f0304080703110901180f180c03060b0d1a0a02131410 59
    0x3004040d500c092500c001034074020728810311599041841040040d0204008100950007810313190000e651b1140303040c111605104071105044d03403880c240350900c84410030001e1030b4120009000c11a1007545205801034008040c2400003084403504074000090300c0d50000948c01c61950751200382c03003104140350300440c201c0c3c640070140040c64041e8541e4803a20084038062080d00703031007014100e030204a900341040520101780a400c0c65a0030008681c41003101000038040652860b04041c01840240c0d140000d1803000a1140c60403d070f510200000885c1c820004100102c10741d2059039501c0342c646e402203840e070b0080e01064404072030680c0080600e0038103208a5040b07900f0151a0703400d00840c14140c9010317000000413003a0a40d280c12443e043c407400010346450070b43c801ca11b010341a03451031600d00c096030180c04078140b04400c0d404100d00800c0da00b296401a9600d490102070a80c0e4402d00e00340e00a0184400104000c3c81000012581a0910355902442c0600b203139055440c00095038201c40c5e40b2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 923731151 1250 923729901 923729923
    0x14010e060903070308011205160e07030f0204060815131d010c020c0d1515090b0a090e0d1101090b0405151501050405120a14030a03060e0402010503010501113a02 71
    0x5010b10340100001e51f4110507503440f540c8940141d1b00204850810282000d2554201d807540440c00301c24000c07a81d03010f21030f070b00010140c804d0035410700d1f2518001404417a0001d21080c00b404c0d0b01103404010703942c0c0320b124141c0480707480010080600c0e906015101418040c002c0d034541d61902000c5141d140c000600c2c480e100070020034050b0340c0d50040c0d4030266083d1204491880f21504c800981c024005c00303008060103450f00c40000554038a4030002c10440c0c405035030040c1040b600c2c01581056030303d404113410074849000d00b0804041c410016015005028120000e0706040520050108025011030200880520b52809500586071010300404c050242500700340800d20420082105080c40400762850380080000e40307000c01c016840b4040c41007440c1c0d900000da81c20000300c4c2c007640e507010310448010f0300c845050ba601a103082d500180c00c6102c10b004150500c00f0103501c0015109040000c0884901201c0c178040780501c2d11213050706002c05120581e01704403015220f1640040c400107a50280c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 923732401 1250 923731151 923731157
    0xb09010806070c030207470d02130305030c0c031005151e040c0f0909020403260d020f0426070b0f090d080307020105010b120a0b060714010e0609030703 67
    0x2035190040d0603a8018911103085080d4090f80310b00288001c40840161499181d08461448601f00c2800350030503c08208091003058100c071944101101e260401d56203a40e07541c80380103968005e00081d01f40548055030000340701c1e102c00a8240c80c14070000c6500e8901c1d020683c00c54004100c01c0108209580c4200d400c44040d109800248920b0f1030000c62841c114500c180202019064030b0700402c05881540010401041d0311028400049a201414800a150b0b0070000c50400b41140d0364001820282c2100a00381d5040c00302007860360f5180421115121030b0701004540d03444a03000c2d44003242d0090310a8040e0603070310303440c000450643c086411581140d40800f0f05842400d000d02d20078507802c103c4c400180000c042c00300050f9901c503e400000d0082c011004c0a80301d01d0407800007070075200141c11060720f0b6603051000b4071160503034001c0c07150010054400451003c81c603c1c0450303002e004410014000d0200079410110f1104194440c8000c1c5000c0c40c281c80090340c41c82c030000e40d2031086c82401400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 923733651 1250 923732401 923732413
    0x21e240703081003020d0b040b010b0a1b02040e030d06150503041211010605180f060d0f110f09010b0a080108030c0309010e06091011070602010b01090e06151b010b090108 75
    0x240302d601420340c48580510300c0b04a007901c075004030b50b40c05d100384000c8603540100420701c018828403a00050061022410b81031400c81c0d21030300144160200d402100c401c4141082c04c1c01150f89136004940da042c0320800312501e03142d441c80d551019001c0c9110307014810b010400c1c51b80d0600d10403400c0f0b900c40c640103945031000c11903058080b120140400c811120955031500003207100e41d2011740040c1a110381c07100c0e00c0414189600108082c0c0c10240c6a207210340c2035240c121001800700c85124040c59005844140200000341c0402c2005800b418569801400500007040e4010103401810480400d950f0304606c0360380b03824980e81c0da88940c0d1548440f661040c40540d1540d80301e9102d4424551000c5c201c0c5040075141d5000c40c1c0c00090801c40c46000c1203d8903030b81044604c0400c240d00040c59148000d0296514070070012349180340e2801003150f11601c403c00164141c940c041401e807600b02d0081219038500b807050b0101c0011101d0002c0307178981e5091610540c2c00c1d1a1002903141a101454060a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 923734901 1250 923733651 923733653
    0x3030928020f060d1b020d08091b010507080d09140d0f050319020933070210080a152d08060106050a14070c03020a0608090d0305070c021e2407 63
    0x40c3c50380048003154080c54541d4099000400f00c08015101c2c031503d41c0061004030700700c680260100324020032410740396000c40ca28182d8420304a4200780c2c2240c00303003051540d4a00341d0a00b99514410300070781b0b81045040078514000c01c85210040044404800e00791a06625821400c54400314151403450000d031003800400c83d000c02d40c901403070f024003900c18018074084084012450034007450310a1a2101410b09000060095040d4610508005060500d02d404440d03800151881e2200990404000c200c8000481414141c1c1c000454100403485c200111075230340c01a111511819110f170b03440910a1282c9020b004408020b04040e2615240a002580e09000d02200c840e006010000308000100081701500c04403d001040100e004404e10f0580380e00314010b01c0418a0203030721210801800c00200400380f400410301420000700c0c1e24001c00c180c0c40e425001c0b540310700d80220107503100780d034071307400711070a000315901103c0240040d2280c0c00d11011140d2100149404800b0b2021110b2040000070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 923736151 1250 923734901 923734909
    0x70f0f020714010c050a0803010e0702150403120902031c09050303092412041a0c0712300b0406121a070318031722022103030928020f 59
    0x7507400b410302d00514144040e071240c0f4034028074a20240c4803010004014003108a607140d070642d00114600041c2007076907039400101d10900008102808111600c041190158110b40115a120780c0050488040d103040605640c940e0013104e9003440400d040c800009001d04007c01900c0c41d143c40102100490b00305480b444c0c0d94491400030000b40040c0420030310b6440481601c1301805180515801c4404a40c0d1409880701c3c844050400502400c0500030305000400d10351000242e44c420389400c80c001b100d60303a402c1d094803040c401140030403010300017140340c40200c0e0351184407500c50448080c0701050f511828035035204000e080113858101c0c0720100c200b1184c8c42d016050b400403690f10b40040c1c103402024140c101c8032010303913084001071038410301080e1111140b802c003a04200c03501a03c554044105090300b07014401d04030000c1c02080701401c010858000d04030840048000c00083e01d58030310b028001507846408015162102c03040c40080e0985c00e07041480d03000241a030160024520200c100208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 923737401 1250 923736151 923736179
    0xd0b09010b0906070c08010c050c0d0207031106090a0b0a0f080c0708030c250b070e1219060e0307051f0c124d0903030403080c150708070f0f0207 64
    0x82c0c841c4035400b00d0001d4043c1007485908c800700c9055503503076110301510455904202d51701c00f80314210740c04048141b01081c21010200c1080310100c9540c1e0743c544e101c2c00454141c104691160581d0800410b20800e02d0390020b07552004c00301c4980c1d601c005543c03192022515405141c0001e0a18901840042e07100e0b42c2c10801012620386160495032040e1155410340f0007034050361011210103154406000700180c003e4846103031460229042000321101c648021b503500f20b0050a450840700300c004403000d10440fa0b0145c500c40781d110090f00e03581d102a08140d1365a004034218810324180f00408601c0344555446003003075030070345680c40c900308100104102000d00300400c0034900460b8003440d80350101440509031120002e20ba207000d80e106000000c0285072071001520400d6945040140040359a0013104881c10f0b82d030b021b0419030701c17580e46050307051500740100026070360f0810007030074465950340110300207105400a40d11400e43d4040d00608441c100303d0308011a016034041401400041080115 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 923738651 1250 923737401 923737403
    0x100f0e0403080601140c15010905071d15040314071505070b04020111010c020c0126011e050a03050708010b0a080c01121509021903110a03240306020d0b09010b090607 73
    0x2045d004820031001c003038560103900c0b0004036600c0318403566000340748070000390300402c8101010003c918000e5405058005100300220240022101c501c8a59650312031080000150000c200c3e1919100c0c640050406d4411400c102c96208404c0c00240d030070f9040f201400c14560765035800c0d04089080c1e8415101042c041c00407030502050200000c601300003449a6061010194010321603c00c9402c0054409041c08200fa5035001d81d040c10b0b4140080400340690440d4a10b0040600d001c0c820704844823401c2c90380c1c00081c1d00100c180000818000001858400c5d200d10000070400618840d00300800078140c0c1c0300d00b49098111500c0c102941d0b004038030099500064140c0441e84161004140081450a030405c4001c1a07010501968011441c018024840343d00c1c10104682046034030b04042c03600401041504240c0c48400300c0300901c0041140c0203910b00000e0070881241c0d03d0b80b9000001c3d40200100d50b80c880d241110741b608518001c07645c3ca0403a201c2d034201074035148401e41030143c0d9a0200070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 923739901 1250 923738651 923738657
    0x20403230129030102071703160801230a030203011509060f030c060c14010f0e0c10022d1f0f1e0231030c0b04060207091d0706030203100f0e0403080601 67
    0x100001c0407032400041e041c000940187c045031340e49409004214903808801c2c5a00070030841c20018402107508000404e4124901c4d10007050300c441c0800090351011032a00700075059420900c2515800002c0c403030790416505000001c1c07250a4450f02e810220445d02d1101810b49d1064203070030421a4021003c20318034600680101c210304484140302c07400e49100c2d01c0f0591a181c0d89503818200f0910031b00c0b00191142d8103c0e8103100c030070200c10b0000d547d40e50784000d01c00500d90303500d1041680c0e01220342605c64945207400399010b80a0303c0741032407509500003c1c000130707103414501b101d02c451406100782c0b13280c03c280321100d000025a01030940000c1d006000c6640d46640c84000d4a00900e90030491206840380307500302110040e00b075242a1144e18000e03407201000241c10b0100344041038002ca404401c0c1c1e0b0401100203160f0110805003551003000031510142400f81c10760100c0c0c0e45915400551142c103001c02211151030f0307101c1c3c1848020b80d2074810108401c07003a2003c01c00080c481d45149802c07800500d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 923741007 1106 923739901 923739907
    0x93c0804060806010203070c030501050703110c250b07050a03030e1b0d1a0f1b1309020c0102070818040f0608060a150801020403230129030102 63
    0x2000d40000e201c2d5100006025034801c005903060135401004681d219942d07401c0143c02401c0a9074400000303400c00d0281482c0800c20070480782052a1080107112084a02c240741d0f074170680d5501c541c408080c48c25400175085200d0701c090074810303000e00040e01c1240c00320328026045440c0c400c21030109400041c2010004040083c2c00c1409410945100c2082107003450039250080070b101c400310980f417100d018000c124486c2040c041c490454500a00003c4100040da0285030242000381900c4000100013400306809a8010b0098a407400c000541010000d40c0c406406400812019400740c0300060481024540f900800d24001c24042041000905021070592100001428000610344500200785c40c9101d90b40101d004102d81c200031034480c0d03101e203400200011080900181c00f044480c1500301001c041c440c1c1c007020f100c880380c107241c0c013145c403521402c420780c01070301c8180d16560034 = true := by decide +kernel

theorem cover : BRFrame.Cov 923561151 923741007 := by
  have h0 := BRFrame.cov_init 923561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 923561151 ≤ n) (h2 : n < 923741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
