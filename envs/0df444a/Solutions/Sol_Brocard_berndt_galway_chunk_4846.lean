-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4846
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:55:31.408599+00:00
-- url     : https://prove2.me/submissions/27f22b51-04f4-4fe1-92ec-d773c1249605

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 871402877 ≤ n < 871582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 871404127 1250 871402877 871402907
    0x111203060d031107170c063c0f09190501020705121c110715020a062a050d0e0f06061002071502070e010b1204060e010b1e0102060c0f0307 61
    0x143c0e00b941c41240d49420301e8500d500c040c14004041003001e110b86410b105882d6810001c0b20510305041c3c2600780380c1d0380340c079120180c80d03458010740c40403070f5100c040402c5502e681c5046400391680d814040f00700d10000c2d0419801240500d484e101d4400304442850f0118064910690062020a01c2d2104110680d40701c204140010b0144d003090b1111030500d2818050395610326101c0000c191030b0300c80c00d00d02d009156406550205840001807084990210b0f001d0041c541207040400d62801034240c44401400291401c218002100040900710790000d011f4800078000100030040151943d1081351592001e0344d851855030003500c000303507242c41c0dd0203050500704002c1c4125803a950705c690f08403440c6000341c52007801691009804008803520183d1031800b51100b50b400c42d05010041c104450b44130b4000d00000d0040c0d45800e00112080d100758016500d054004000da03107442e03900c1e110050301c000c0714040540140911400240556107402c21260044100101e40d8610364074480c0898841b00415656 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 871405377 1250 871404127 871404137
    0xf0c010f1b1d091306090614160203030f27010b12010e031213021905031b0619020c06040303080f010e01030b130501140a0e07051002030909060a05190303111203060d03 74
    0x50011a2092040c141b030705210345c0c0001000c2083c10401080040020301030100c012001d820110b083c5c1d4007009490b0802ca441041070b203191503a41c8c1c40f59a03d511ba01c00d4003007128604a444c2c403515415002456801c0c01510f01c0705030307103034080c1800d4240ca400301c006a8180d03204100350f41700160303003230907031030f4403a4038040b00c00769410341e550004d00e5a9400c840e01400761645484144410720f01813090008000f1a0f0031041040d5a0041c0401e80c41c1c068403c60f41804034481900740c2415009205422100d0401480e96565a807645070143c90301c40151502035920381003078004981480010841c5040c0c941152640d0601d40c0c07249006400400b031800c0c1241c4c5135480e02c41410310442080d036030038062620518085250303965400d80c1c500d04469603000c148103480c20300000c0100d903004802c8a880c1d420556a00a6642d01d2002085191035035a21031504070000ca04074800c000e54540705d050039280b0035990a0380082c3e04007411a13852111b2101c1c140710301c0c01080869420310b010025044228428200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 871406627 1250 871405377 871405411
    0x902040f06121103041a060d020f01050d09080d021e0708040b07080d02120604150e0c07030318051e0703240e0d0801050f030a0b0c0f0c010f1b1d09 65
    0x41981e1340094904890100b5215810104026842100703540a5801d0760506ca054001d03400040b401034241c038001d030503c4000a0200812051500030034040c81d0009121139a0b05414050040254000e01c0c40030102080b400daa1071000708000c08540c005500b00003490b0600c0e080c010340044680c00000304032006c030420003e0140d0181140040c10240d440003407080c1d11454404207010544100c0d0711551680d414071881440540260401550002092411a41c80e18442d107420f400034011340b504201d40c0e0900040490401c00000b40b0308940e0000060008060815840764030703503031000c2e03000003040c40b6611f401449120514800140c0e4408100b240405d42042d0944480e06042e1254024000540c0c904018065030500c100d52102c1c0b031134180d005081030500c0313440b40ea4845e10068107004151500041c2d6001080350300f01501da0f402c00c00c200801c800020703820040014130394402d40b21001c8600050700141d86004040101c15100741e14560b00c0018800d8042050010f00144070054407110619 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 871407877 1250 871406627 871406651
    0x4020a0504090f061d060130050415140106020307110a031e020901060f02101d030a0201020a031103060d06111608180306040812090a06020d020d060902040f0612 71
    0xb82c0280c0300c1d181000004e913941403102e000244040c80103c151041d4101090051b103076803000a10000e520102c09079082e40030301e20f240c0c0840d2110355802000c11130403d4244818002200c081044080340304204202c00500c00c0b0b45100c04040034480c030000760300305010f9030b00810075400c4241c00e148002000b01592649a40d140c45400101403910000140458040821070a0080c000c40c0540782c142803941c03105100c400c0c009d603110b001c0151100c80c0354407130899005c4426178258200b08400c1d0103054a4684c40480c2c0001c0c000c0d0031446240300002c0c2008464618440c040044a00a10340584031705040340b605c0d19540c0c041c2a41e50a1011844020880c0c0c200103d00c2044513004117205000b0640e80e1400c001d18084500d40300c2806c0c920941050041c00009a64001240c442c00c45a070350107a01550b94020640c24503400036006410640005000c0c15825202d600410543d82e401c070b801c04c40700781c9501010742203003e940107061104113002c006104070303405101d582483d41124480844c010008030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 871409127 1250 871407877 871407881
    0x60605101803031824021002090d150b0604080a1b0308030a15090e01090b010e01350a14060f0105010207060e030109020307141e03030405130b0d0b10050108040803010504020a050409 80
    0x174050001518901003d60903065061001c0d100301d1034400c2040d400c15400c40d0004a0808a40d039000b40184441b116001e184c0075180c100b20f103601d1005160300e84640c0c2c0c0746d08170380c0c4034556101e00319451a689c0d0304d0000f07001c14001295080d43d4201c211942160744d5050108001c042c5050500900880c0d541c0024821a050081005101c071144c00810b1200c05854110303201d24043e0400d22400c0e40f00d1005001d4140c488040a45401e6841440301044032844600070030a180c6104008040c0560300c010018005107042e690421000d9004842180d6a045030303a0303114400a014003801600241001c1100c3c900c44c00903d64071480040c0005205032284c0e0010b80b501d20541d001400109281143c0c03d018078200c1e84610381c5480643c00a1100e0740b03041d002175160f10550080c54455200c541e0040302c0300001c1da10030098000050300c850011f030700d070741072030584108112020004429444404143c030351040014a010b59404002c2c81c0c216402c140810001e5013080c2e01c00000c0040074070000414130554 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 871410377 1250 871409127 871409159
    0x902031b09130908090a0e060d03032706050f0a2d141303020d050703090e0a060e040f0506060613090b0f0a03110a0504090b070804020f0d0606051018030318 69
    0x1310344040d40c998a280c14404a100e0760350085880c9007081007004034070b44851040f4080390b40d040c0b40008454804c1045000140c038441540b45e00d4020601c038102c2000510360000d402813188101030046555985031800545038580c0c00d00e4904244232140130343c494818071800309204400d00000c80c6a204032540c010f40410129000610072003100102001e0613018071540c8840b801ca840d0042c90701c00541c07000341c040c80861140030701807118100040e04c1d805495011001070015203282044c241401d007014800199069403c3d1040e014400c00b00342d080c82c00308115401091048041e02c000c070310704003c130300041c5400014150061f000818214855540780d01140141d8401c6024104803101501072200440319900310310b0160345801403141c007080c04500d8040d4010102e18003001c5c15501c61000c80d84180d032020005410014a09040c0f08021550308050140d5500b0307500329030203005a800886201040345070203124a01102020f1000c64840d0a0200000f800d0081c01818207544d044496008402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 871411627 1250 871410377 871410383
    0xe0d111e040c081b03041a150102010b0102010c121e09032606300316021c02060a1103070206040f061206080712020a0e070215010902031b091309 64
    0x9400302848540340900c20818004018581080c80c0c2c903000b03900745202404460f030042541c401000080401204025a00340d442610350300e5002414071400034010b5000c0205101e001d5401d000c0390003000e52051250303201c0311125559019844140c00b800d0001000903041e0031641000a036940e10312190139000780d1b0400c602c203075101080404124188012008412034544110782001c0610020b45c0c1c500310707040c03010417007942c40c401c500d520020080ca004031011400079a9000100c1e07651501000004d4601501c2d00960b0b074900340303c0c9102c140181c02d21002c80e000354007104c00c0c401021224030030040840307030075030b80c0f800c691500701190002005504164480750080e00d4540040c044560300201a1081d030715141001c1c402036003840038050b180e0795035019042d507064040d030441c81995a034540c0c02c030050042030400030143c01e010b1002926147d42109910361001c0800000950204a108580c414441c2e40698050f420b410740e2844504e5004142c85544408501040e0b2100c0e159481030710f140da44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 871412877 1250 871411627 871411669
    0x609030f16051903080304020907021c09060e0d170705030f030c040f0902130621060f141f031802040e010f0b010e09040210020f03030702060a060b0a0e0d11 69
    0x1141404010407000d100c0300100c83c1400c00102000000e01080542c1c0d00190b0403a080315043c0d4038404100c0c68807495001601c88401580e07034610342c0c3e640149030341007900d00f59540c100700c02140000f0712000060500d80100b440c8061002c0c503030002800d0303028100c501d200d001030320302d000e48a00c50046c4903001034490351a20348000504010140c01d6104040c010a01600d040d800d21600b907000340c00fa04031700d11840c070500100744050401c10041100403806c50052040801c8031580b40e4141014991041c0100080138408110601891038000f62810044815086004443e00d9152080300a480d0000b66900400445061440141d4407806410010100c010000036650040c45680342503034100360001c0c0c1071103040c441815035610780740342d002c0d80141c0642d402105500e40400c105e2420390981d03000039890202006014465601084050180c905810b06005442e100d407420003a40c440c40fa01c800104664190704601401c0080d280403601d809035281d584d0f6041e028002c41c290540043d5440c06010b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 871414127 1250 871412877 871412879
    0x3070509070e12011509060b03060405040809041a0405060901121e0c0815060f030d030e0c030d091706071704230c01200607120207120e091509060609030f16 69
    0x20500600e180000e01982c3c40031f01c150b520b4810841403520000d80003030b001cac9480f030001906200588080322a03050010303108000c0e4054524802c15071105a4000724403941c24072001ca4120310304082040d060b907958106550b81e49059940d450340001542c0100f003d0300ca008c5030030b070300840e000b090b240004240d010b0241010344200902c07000c00d0000140103d204400348101c100c1c051301c4c0000c0141040740f15003070026003480342c240c48528001d80280002d5251084180384005140e000c500c5804480e500118039041c244114950b03519004116a03881c0040e15440d0603050080d480300c0540d40080c00365840103a1410320750308032603030200720300d01800140d40044044500f0356400021802890000d030307a0842d29011058850b511180e000d000482002001c03100c00300700702c9903a41210110740c0d1280805031050300c1c2c0c0e08080d10b03500700201e200f03111380844000590084541d02c00080205001002c0050f942d03038038000c000e00d40c2c1100243c0c0d90180f00798998075031541010051009a5000c401c0c9001c1d9031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 871415377 1250 871414127 871414151
    0x302070e010f061e020c0d06090c1415120f040f0b041b08030c0613140303011511010209030a02060d1d010603140d0e01120906050a05220203070509070e1201 69
    0x20441011480700c8a134454a0054410360b80404d28484100e421184500b14000f1400c1c00800ba0803449009810404010b6002600300c0080920355201802134a0b09031145144a00d280e075180605291078644086200000324149044003000c3c1e4000d11031060a10015260f8542c28412042224200e03080c030b2250305130b4020b5018414404009109020056140c049220812a1100000380c0513040d0048004001c2c070030014070130080c00e0520364510481ea241e69641003200314988540d0310540c04111003608031300b2800c2d01802126402c1ca40600105a80c40c429400c0c0107542d84030255801c0d820303503629020810000c1040100c0c003510b40c224004180941503007000e41c0d40000044141e860b0340d000030742c4900c0c40760b0400c02d0031034880c0090820f400295024000031000d000d503004010b00c0240341201f044034040f100ea00180c0241c800c01106a185100c14507140b81c5074141c524040d500d6801a6810869803801040c5030740e2000003450301802081065020545c03101214007070243d41c1e51124031103901 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 871416627 1250 871415377 871415387
    0x411030a0c02161a0a0908030d0501140d111203162a0e010902090d0204020c2104050a030b0a14010303050703021c09030201031d060a061a030915040302070e010f06 72
    0x184448039110b407264a2030184400f07a0390222a414011082c00400c2d2400e00c031b0301603c030306401030048038107580c0d848001c0c0780c910004000c24060f94807180c5070304402d18a14108461140b148580c010001d902d00701c219070030041c1c4c0f0782d2409500d00c46031104003c5468001e90a0784042e008921031282c110880d1070000f6001813040c4203c100844040d000c5104100c1643c520282504544101e6001643c1c1c01c0300030007151520b040300402075006400051004498200010300c5104240120310a01212040da042a91140305500c03034181d0002900e0300c140041400640e0f46900301e40c880e54009030b040356030034048038400400d91043d0082000864075200b41034041c8042d107864081c940c5a084480600c00000d01200c41a00002c1d041541d2188003501900380d1602e8040c18400305070854000c0e245c42d0a011014218034020a400486c10340900f0a41c1c1c0d03621000d89018000400203800145400030fa0180710b1140104150218404d4107c002004c4030115417040c06060509010550306045c5103000d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 871417877 1250 871416627 871416643
    0x903051c150801020a0908010b210309030a3e210106060c031e1e050c070e01060f020f030a03150b0304030513080f0c062110060f08070c0602090411030a0c02 69
    0x1da641444030380b5119542d070500302041c24ac10441800d82d42034228641c1c51450050421103a054440e0800250078002003800f545103a08541e0750a20143d1480020903c4900807030040f16041c485402c007a20842c500314610b2103204468907400510f4114180105003541c0350f0358028000f084c0c1503450f050a1640c0581200b02c02024492000c041c0084090010003140340422841c000c0c1c402c1c0490300040d94411001c035100040a06c0032141c103030b51240b03150f4103460800e01c078810100340003c0d21090001d00100d074860744051b4090207542010f59000c02600603215010108001c0140c140010550b40d2581d8082c1d80502d00950303840d0f84603030549001c0d00c01e042c0710350050002c41c0d100d120005601130f0000f481d030100c1d590941c1c105448042d81513100b03000c180d18050104046103041f00304035003007420414101c03c83d20f06a807001c000080058095800c1e0005455290014100041d14800309884d034004100282001d0800030b1221400c100c034040d9030304103480d100c070107a48070f4450070346232641045024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 871419127 1250 871417877 871417889
    0x7021503010f060908070e07030b0306040c06021e0613020d0c090902012a0210032702030d0e06030a020a052502030d210f0b0306010b1b010903051c150801020a09 71
    0x700e5a50a0850071596a006d61007020316000e1703a400000d0645200350044819410b010b0100c9882c0d080c21326001e41c00f04a2802001c3c018403d031500030241681d03c1c05000c0410441c10050106500ca0203020341044801c100143d03004010125410b000400c110003090082048203c0010444181c1c400101003211501400101040040d8544001110700c200a4131060b03048642c2144840202d80507000382042c01c00c440d04441c030208200c000d08443e030405e5078000e4401c030280d42808803002c1c01540c015404a5074950810014000100d14030604d50041c0300783c684c5c81c00d081c1d0500c1c1a400300d0b002d8202c2805000b8101440e0a0074010440c00c02308400c0745081d0031410100018010249080304151140b40044a916142e10f49085002c144d540240380192024096440303d6844541400c22031b40901041c03500681e24113004080c4c2041803291200d420340c1a0f0703442d272511103125440e0003210098842d08004555480311604660882800038000340b0b0000000741c0c44500c2c03050003802070070440d0701107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 871420377 1250 871419127 871419137
    0x8070803271504060e0301050a06030c060c14010c09090b03070635010902071406090604060e1915060f0f091112040b06090114010c120507021503010f06 67
    0x916a07500c0401d00c0444252120404950403084400c002050392200406400c0304000c002400700710554401c03044a0340c03070002e17002400705440f103040364000c98080d4072000e440000d000d14240840c1d40b154000403401400303000d8286068042000c041c1c02c4407450b04400c0040f030300900081101e1401401540274000d011800b07841014034010700600000d40d030f841e4a1040c3c20340d0500d00b410340c11035400104d000c0146d00015021660716264101d00941c82100309072030402e0031740005070341280000f4089200703510f0351000e00000d449a5540c400034140c2c011148825001c0d2201070115101d1443e880c0a500c4d00400324081500709040d4484200d074016000f0580d54054002d081c061140c07009844400c50350035020014947ca5041300300c562a016079528500685801024401803051110071180600401c0302c2843e02a40c0c0d41c070111044001e01c944460109040c02c4029010030650180340300d51604a04004c1d04d0456103600213110344ad0b090703180c4488070102000500100c4119007001c40607101d14108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 871421627 1250 871420377 871420387
    0x100213030b07020604030e0f04020708160c05060c0a031202090306070207060f05180d0302010207020a1410030b091504060503030c0631080c070902070609110306070c0b04051203010f08070803 84
    0x911f005030b90b296003401017509900503000c0e5256a8105c410442e00f1009660300c0350460201e1884003800c0c0c100540e50f070740714904045414070b00341044440300015180289602407441c3e800756010109002c403211407a9090140340c031240c80a0028510942c4e465006d494145e0900c0d0016041d40c070101810010020103014000348004e425841906c46441142c18088800c42440c089001e803103480c00094014440b0040010001d607281d0001d4a40181121007008600d0840800c80c2180c440c0072890b030303000d04014003003031186181044241d01403c000e407001c02c2054591001c245592302031214885d04d640403204004640c401180420444415140003207650204071071041201a4248405030904c030000071110b038000b00400111000b0f00f1205d00070354a552583c180400101303903030082030b01c08001c103001500b40c525000c511544205007a8842c2c401d0a00d55031035420850304018001c9800b44100c61000c60034420641c040d5000b480b50001909105003058803c80c2070403804d6000700f009a0092003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 871422877 1250 871421627 871421633
    0x803070f1106060d0803040512121504020a050d20180102010f090807031d041a1306051c1104020304110a12170309010b100216050a2402100213030b07020604 69
    0x1444042d800218061b02c82e115410a54200300243c00c1e012402c520004104903844145181c1c9840b0700d0312180d112444542d08014841a03200c2c1421850000e4000c00841600700425404494292500c14000032180a103005140c0f4507440b440c0004500344448a0031419580c1c24003a581821000d07007414007a03000281e0f20000c0c1402030010090a0140c0c4444074074a00f08035052100022030028401d11864003144000e11354005210756150140114003600701d01d444150058408a8101500300303203134803103a6071315900c844030440400c0b100f1035003448040d241a0b5450002d5401140121004011405030360304100c40e00d80180d10100508007040000030101d9000c10300303000e81c0901c50303080035a20390b51031610340e00509454084e05e40c8071841c0ca6800d00055030009852540d100c0d0440a400c0c8513489008020541d07802d4403941150b129441c2c05001d07101111402440c0c8004540122044140c482981d1400c2e60012f88542c103054544440410030b00c07c82d1078405822190320700103000306061a031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 871424127 1250 871422877 871422889
    0x21c1d030c0a03022211070317130303020c0f0106030b090c10120f1b02070603050606160611040f1d06040b030a1416091506110607120204030803070f110606 69
    0x44406032043d500c01940d50301c101d04115041c02d00d00340c140010441340d075110b40340d5146c0c0c6c0c00841c0207500003102e1803001c480e0a00030390203150162001c10012160114165000c4010354020360164203140210011110114000d003d0700e4061846050b036041e85182115244e4501031f50f40d0540d0303101d01c0704044440010744d0005c003d076540080c42c080c08201340395120307511000380070042d4181c4600c0f10981e401d1080c85038041800401d940480d9001c0c00952208001c00126024400c14070310a0b048009084000070010b6110250900c40b2003001420700e5512540c0d9000c0c1d09141d40200c174803034201044100c40c908407a4000380e000400700c904010501c81c52010070390390540400020804902c0401090345103038100a528046c20300b00c00345110a580b284072070000f41c00140290101051601c3e00480d000d8061801c1c01a290b180f44000c1815544517403040703603031004032000685400d60070880400841c8001008610442d040c0c0c4038002513840103a8000c0800d901118050820782042c41441041d640394 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 871425377 1250 871424127 871424129
    0x512040b18030309130203070801080601060e1e091003060b0603150405070903210806030705152d120a051b0a02010b0913020307090207080405060a021c1d030c0a 71
    0x40034011540800c20202e80b8511030300420b258001c0d541e84403400c20041c99002584105240d550f04849130740e994584e10360b00d460030700034040443c40304e051190490500300c0d0742840c086852510700511140b0380c80800e12000341500e01c40103508021000f441800b03810700070744200400a5030341d030303203107150140000d103880d800202603901c2152201c0104600c180b14003000c1d0080d58221a1100101140c840721400143e2000d8110010486c45000614a403402061841c01c6480180681500b02000c2c40310740711940c000512480350241230b8010074400c04c40040d4080410007600c0c07103640d80d00084126080a1040204109100c0d2308050130081440060802445440b034059862a10303104072440590240c900f06040b2a0007001100802c02a00040418444001d000342c0548582da5103a50ba1141644502003003d090003408000401030381c00e000e4001c1101d400144195900150f0f8803154142c803c5030800c503000081c104a800416010090402c41400c640460040c01c4604810010030054042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 871426627 1250 871425377 871425397
    0x1e05030a0c020f011103010f060c080904021b0718060b180112110c061023010f0e040e0f0c04090f06090c150302040311012a061b0c0512040b 62
    0x281c1019900c4203008002900407005508004c0c0074074041c1c43d214000f81d402c2407140040169610310700280141c015000b064419401c10309407403a015510080c0f02c080e500c00d0101d020400080320789990070810501c00e81c0064801a26103d14058030448001c1c141c400340d80000496074010011b81d15181080c00c1816400482820020b500401d400d040c000148600c0650a40c2d034034000a820b03107905000f14a09226030403040d01d040b4059120495502c42c42d019021200010284011880300380d8010306010b00000342e10325200c81025034280104055410f030200600c41607008529114804400b840140c11007442610308001048160710317442807070025444040c040541c2d601002007440486040c840240c0381940010401c10074410b402030080d40035100c181c91201d154400030407150301c10420b8000298811600000ca150811070003046403492080c100c41450b920791144010f075130849070402e85100c158482d07010003403103401c0c1070707046c040b00001d038094100e0200414046003114409444c08000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 871427877 1250 871426627 871426631
    0xe09030a03050a0204080318031b150d0b0d080c0705100f030e0f0d0f1823130f0605090c03360a061d060606030703020c0a0609080a1e05030a 62
    0x15041079402c001c3c170464000146a0200181102004000c1c95280c0360144054085982c2440d01c1811012618050b03044140c3c81381c10841c20800c580000000342c2040c884409000441208020001e60450034114080321142d20104812900300000d00040300100b80503a8520150003ca4800034016042403680c10b05050b03a6501001d07550200300306a26482c06540100d0301c442c020030501401c0d081c2c000c3c1c2d134000056031010515400210400c140c4007182c2e2920043c041521210a41e101c00c00840440242c11460307210b06103043d522103008400541170140400180c4909042c24880c54440007440400c5040c81001400b8607800401c0e00c44c03040d4980b0010b2841b290303101045946406c00081c5440800348034042442d818043c0d6075000307060f411100341d0811156046822619112082240d00b194003000c20310000741e505009400a1203c0b444501c1a82c041251a9070b45078100c440e01c44080c4c444400204d249092641c000e50000450813000644d00301d01110702100a04521006102c02c05d980d0f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 871429127 1250 871427877 871427881
    0x2030d0213080d02031911031204082206030b010311032e06120506040c0c0219050301050420011d100c050105240a06090e1509041b0e09030a0305 64
    0x40c036515080025049a01c161803a00d4610f810082d602d802511a030010034401e0709030220341601803000c0210400d220f00c0590300703000800340d9070ba000307620052083d03c2c211010040d141c800c0400c2c1c13403441102c091030f204045290b8101103005044400a904543c14140382006a80d24400c10ba415079a0050951856821300702d000940140091514103501c1c128019008002c80da1980101c8180001030010000308000e03500c0b081004180d68070301d08070501280c02d4001c0380c400740c2800e030605d100f0714011000c00840c0660391030200b030864100301c409503411240c5000c000007180c400d00e507250341d4580910300031084ca005c5031184c41e00c4400d0b14103010f111364803603100545038500402800c01180e070414001c00c064940780001820451610701034440d4001140300810152914520240540d2101d41c1c4449829090019a441c0c040c030240070884644901106501f07990366095200e441a8800d0b0301018400f228941440d4503003199800070100900c0c0318080100b28600042a6131001e0340500d40800c141e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 871430377 1250 871429127 871429147
    0x914010507020114070804120602030a051e0f1f0e0123060d180b0a0b1005030c0417011d031222030e0d290c040f03020d150207030909180302030d02 65
    0x2d102d82d500a044036208188c0900c28440303107074003443c460f0001100500c00345c2d41c4c0b0400c44912400c0808000300c4107246a001c41d0014503411086688107920800b20000ca038030328441c0c2e41904100f540844070b19000580144240b59040c00c03c02c0d002980e90102074215183c400000304240640b4106924a60740e8160300c601d5601c1e5900502019034004407609010304109445201401d12100302c10f00500e007031032408201520920440c0d22070000707262460308050401415040340b60550580c01825925100c004e0a2640801c440401c00d0030004c000f595698041c076958015044c00034403c0602c06941c00220300c5903603801014102555161600e0050300f02d680001500c0d00b1304194000d05080140114000041e000a203003010f0780348000c0080d08030390360705403040e0907a11550003140b0407240c0d496020801820b041c100001d0f900d1107924a00c09001e041000403049801544050b00000c02c0c1c82d01c200040c50040c440c80a003891f0000d9481c95081c21504d003c3c1d0707a489891151240302e0350005d442c00310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 871431627 1250 871430377 871430393
    0x512030703180e0a0c0e0d0201080a09080c0105010b0310060309030903060504020103200a020c0d0512030c0f0a0f030b06090a030305130f120b0907030507050402070305040e0403091401050702011407 87
    0xb4000394850441070381030001303518000f05a000d1516010402c01202c00141c0c4c5401e44441c0c3c2c116605a542c41c000f41e503032413454000f50502e40e10031905003030103000110106c4028050302d8040c00340ca0061507264a004000901c400800e54403801c241403401c0080400719034410800700c1902d0300100003094a44852004a004003a00101c5005009045858000d07a5010f8001090014040d50031244c229080004000c1c01d105005001000c2d544640040003070441000f010355800070000e038216003082c1841c540e941590b0700c01d1031120001641c1085107141641c05114051020302c06035481400c04800720041000f007407550002601b40300c1c01080300005418070802d514041c1240c0c0440d65801c50b6601d4603031982002c0b4540440d403c00b800360000740b03108400a60002103a82020080103050b00c0c0009110081d44a50300c1501041802c020208901208043c4607018034800c0d0343d1a11007030700d0124280c400c6d07258241c40d1410000c0030032450025031391008825045403440c80700160341d18003620302858 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 871432877 1250 871431627 871431629
    0xc070b341a10240e01210e0109020a15082508090106090f02070b18071401020a1e150204060e0111030c120706061d0408090307031b0807051203070318 66
    0x8412800f00c488071504446144440310400316a4941c1d1040183c00e07001540c07001e03501c0042400300704c0500030340a0720b0405a00000f14242ca200000180310b0a60b8000c12000403081d0083c460100b004000104115486541c040d8060303a085171458a00d0b010350000c100881c0200641402c0141fa02c0c0481d00034a001e40c4401d0050500180401085180b65001c9000c0e40003000700381c813120280c90004240f156080261520260303c5000780c0003c03800c00d81c1d4900f4603505000c1300b0381184103400c0300400241c00070710301140005402081314a540340d203180c45610712080001508080303005010810005801070540d071808082400c1c642c1084801c031442d02e141d400750408032020b038441d00e218945000d00c7c0500078280c41d4010041403081e00d031180c61240a40700040305000d00b1940b6071000801095001025020300c0000600f55041507a898680d40225400707508400000920684c0c1007103040340811910004080644070001c42c010040e0032951607016010011b0148812224511120851400090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 871434127 1250 871432877 871432889
    0x605030411010e01020f07080718060b0901080c0706090605250e06091203040f1d090d030b040f050403030b132304141204060f0e0d080c070b341a10 65
    0x2440c7c840da16804a40c1d6081184204101300254100c50200310050340503a40c19900e083c1081132400020400440380c0c143c00500004c2e00c00003d2008400080c00e07405075002c1d1a0140101180c1410808001c400300c04114021842c07846e07420300319640840e0000350100040c3e44c101c0340c43d03458541f003101090b0744500164090a0340d0100040c0820564082100c80c81a04c11035030008050340031491264000007825200e1104582c00b01d40b603e1041842500842d07ca818041c002040c2540c441000a0030380d402540d04502081e103403011a102402d050544c1110302c03441480a0101a0170f260b104102c0225000e041004884c11800080c1402120100641c10201e008103c0704184e0040710341d005140c0240c080c040c00906803550414080344560408014100010300140d4801d0380c55440c400c065001c00b5444200f03008000e4000b034003601e003202601c0d65450240c605112010001d045007481c2c1460307403a80080f0404100782c035011030707404a0b4000f0350202c50826500d4036101c0100711100c0312580e034011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 871435377 1250 871434127 871434133
    0x424020705030c1b01020706020709050c040302030f010c03050903070c05060c0f0a0c0306110f0a0c0302160308040305120a1409150c0f010b030d0c030c06020d02040e09070605030411010e01020f 85
    0x70700d18100040411203004e0300c512246402c080fa80c012038a0b070b1701ea0b1040000580c001c04052064503a203502207604010030b105114030b080e0303803a80400d00300070403104105020b07503650310302504094043c00780f50360054000c5c0c0510314043c01550344c40840005401f405002d910082546682c2103020085008200314001c1140c0c039103a0f4603d0410003040580c00101d0303600d801d0008205013800707010251040000315242190070540525000c07140b00740401c50039801c501c90318072003030584a64075100d10080c50041200756562411801c00c50f2901440e1481034400e1001045041c4109901503d6041d6942408600d0703a07484034070000260100008446043c03140c1400103421044800c000b40b0b450109003001e000713002010216003010744a0080b240c044005c2010442c0c1c05001a01c2820030000e0f55211b404018101404060b14004980140d003081440713041a0b0305118245c00d0422503400140000c1c0342c03c91031441d0582d11503800c640030110590500c0420359141940d60300030310161454003404012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 871436627 1250 871435377 871435387
    0x3100314062e0e0a060b0a0203090f060702010504051e09010612050601080f06010309050f0a4202210702070f0609080d0813050f01051905042402070503 67
    0x20301034403a002034410142c04002c000c00000011589604a030740e403901d80480ca9007442c5042d28050510b00000d2007544803e41d20840454081498030203880031140741e90045850b48a440284000787e400249464824002808200c0042c0e07807201c1254182d84003070b21a04100d1841c070300190360808104000c0b0b588801c2c41d81c008241d19500c4020824022105d410601c02e07615118011340707000c1c00a03112901944403100024043c3d500a80021520030b10030412141d91416101020b0300309079120304c00b1100140c00c01140e400c00180144400c1300c41009054100035600d1402d880c00303001c0c020615540c3e44a40100306506000821440c8010703100c040c003d101b509140611000f52142c909008030142092136030780200310584150040419240480024100c580710040c058070042304c010014590100000d60b4035002890510451039041d13071807000843d131030425170002040400003880315034405140808100c040b030300c1492046140c282d90714203002203e03225103158001c3d01c2401d401410900c00014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 871437877 1250 871436627 871436663
    0x9090f0902040b06070b040209151801052701060c020a051017010603020708030609272d0a030309031b0c03150e06041101020705090c0903010c1b0305031003 69
    0x2440e45107100700c4040008180c82c0041100b140903ca90140016008000180041c14081c052039048070090f0012898200440005010b20703615015001c00741079000010049814108912002100c07001c0b458205412190710100c83d10005102c1e207401c02103440344280c25515181000009448083e001e0780035824401c4010385040407c60501e540292403000008000e40700c3c1c0309850000e544002180d141d510342008105101c00040e000c14401164215004919004402d01d81ba40040240180000e00c15440711007070080101e5081d10a108012250b20480030008a00c02c5080ca03403500b4006526982414100c59422000e0306c10003c99103007419030350502c042130f140e50045034800c201190030955903401c0c0000340ca1104030001126804280400d00040d40e60304d607040f0810040c03045070000f48e55031001806044090750844d05441000420840300c2c1801e004407038004400741001c20f01422125075040001e075401700040c04109c8040082070f20084000440070046402c02071041a080b443c1c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 871439127 1250 871437877 871437881
    0x180218280510060201051005040f111c0f0b1c0c0b0a0315120215070302120304062720040209030d050405010225030609141020070803130309090f 64
    0x3582c0c0300312448410000155851050241d03070712400d80806100101ca25000500c406441c04175000c0008a07111000d4204c0c804107000a0700002800451004072140000a15800c41d13160154520a403801c0c070140014a480d071211003030b00c42c044c1c074140850b000c0260810001d401c00c0f43c0c000c42c12000001034a405981e0741030b0064030710030208005c00d003400c80e500c03040d0030340c225091030780290012441c604180c49400050050204c1c940680151040400002c101480c641c3c400c4404a40c200d0f940c0ca01804100c410360b0008286083c61403880c00c864205480744c41e9903001010303036500c0e0070700c040c000070b4880c5d02c9940582d65090005011642c07032180d030703070300151041d0498001c2c41e00511544129600e0580300310418544450021a0503038102e0540d15104050121320030b00341c5a03d151610f050400c0c2c0403c004100b0b6201c11071000041003050800e01182600280d03a410050311414000348000c28019800c494200f004001c112025060926042c0e4070007000e07900115007185460002c5211403895 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 871440377 1250 871439127 871439131
    0x2e0b030702100c11070e012607030b0106030912030e0c042004090c0e0306070509010311040302060c0703021f2703140606090604020a0f0c0602040f181802182805 71
    0x1130401d460b0342c0b60300e4081025041e6000d108034000070320a10441000a4400c2e8045110819800191190a5101c0e12152082c1e05c080c0c1c084000a80e07581005400e00c04080c0d060300018100d49014003284101e011141c1c1c0e01c081c8400305c1880f66585481121004405c03010341784441048040c503640f01e550341c5011800400c0e01c01010404101c10303400d10303221031402040c002e2188025440c2d20b0f08144055004500230281209100e0b0f00c03640410010000d40c0c0d82031301401e082a0510300070300c0814150310601c90740200c41d017482501e00041c004007801107a089400072940650303004c40d080c0d0764000001045280522075101801f1824854440c1c41410404960188645000d4031244d0442e111003041c03004034860f0300c3c0c089001031442c40c00105094859001c0119440c000d007005818181c54190610b504851940407413017182c580801518058607500640f151400007191a40c02000301e0380101d050700c1424024089520360f014002055a04003503558406000103204082520340f040070031200800d41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 871441627 1250 871440377 871440407
    0x70308070b06030604030c06020f040504020f1803070609030204091a042d021318021507020405062e14031302120a082508030a052e0b030702100c 64
    0x703801c0000b0007504000400704e018a606503075660042e506a00d4070002504a00810b8844040820001030599960f00203000c02103110520181c3d1034000015110108281c416418020380200c0301c200400c540094110381100e40545001c12001d9051070f082090b8102c0c050090841c4000c034040c04240604018090492210301403130340101c00503944407140008801300001d40c0502102042070500e64240c0100c050280030408441e80d8544650000340c03920084803074507820400c0030840350150b20300341c05074940000b010b40f00080440410088646808188071b21071940000d46803052041c144078101c40c03160104460740c850740340d040c9107001004a4001c0c880a0b841600812031b00040c481c030110f4032919085e03100382014648012140442107024000800751401c0d014038070764001150b074007070040d4440c50788007600140c54949400d50682c00130629607030110540d40e0f0190918004046401030b01071300e0100420503101d80d194101289805000c0b40d58002c880d0814455004158000400541d2064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 871442877 1250 871441627 871441643
    0x1060801080d0801030b070f0c0506040305031e090309011112070615090c120507090509011410020f03040501081005030313030501050c13140102010212090c0f09060904150e07030807 80
    0x1021100c1111906021700000d0a0030691401140186001c2c0440324801e4210741025030802549440f003a040c480101c5055011031000010441c0d0045842407400001e0110160000d49040c00780da120340e030b0b01407000381030b041c00700e6952000f44003401041850b0f803060101c2d041a59400c240e00d0310b440584821041e801510042101c0896000c006e800780780b0020249946080700104402d0440300540b03406422201400000c03040030a50303407a6103982c0c078048d000d00d840410307041c4214000d003e008502204c806085402c00c401481d9844004006c9070100c85007440d1000543c3c07500000103516140640c0702079454400018404055201c1d110f85e041101d005800802050341c0344800c00710940b00c0e0900d0447c40080140040c490566010301188084006200050400c46400381b007860196066804074010b0f0f101112100c036614024100c000c1e801d070150b900340c200d03041c100040b600300c1c4009031004000c0300840380e80508403117403503208012070b80100040303ca40503a2402c081809900c040c0040d11800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 871444127 1250 871442877 871442893
    0x203010f0507051207050d2f04030b0f0712020c010c021605061c0e010e070f150e22020315010908010509120c070923090f070b070f0206030106080108 66
    0x205aa1080e07610502481c0c48080c909089500d000040b884002e0843c41840807d12204900c42c0e044d2107542000160540f1141102e0042c504022410101c094080c0d03c4890400040c00000c2083d00c0d09908001c00e00e5000300310380c8404805a400070410b00810703445904c04201c00b218210705400c01e505503c025026121403620f01e001c4000142064040c140e004901009092541c00400b20341380c490403c04440016080c0030013450b64203648034040e0365010759020204c02c1c80350360703910b255903c0200000b80d00e0440c207945000024046195404515124201c468640d030f80000c03400c2c1458140a055070070442d52480c100c00000c118299214040b40040c0c004003001c1640c040c14450708c2e01955030034005068120103014260010f6001c544a5541405050400101b00440d40500212704440b6844400003129217a60280b240364024800c080c1c07688000844800403801003401c41c1510ac1060010380c1d610711a04051041d1001e8000081d00300200100001e5202c2c2e1011246050354003410540e902c2c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 871445377 1250 871444127 871444151
    0x315061908150a1512050405010209150a080a0c0203090d060203221515080d0305060f032e06030b13060b0d0302060606090d0602160203100e0309130e0304060c020301 73
    0x818500704540280401034280458441c0d003114102c00d03981031902051240e0405c2070b580c29a0816601100d540e90003043c14552440d03c15004400080b034081c07414180903840000500d4054003900d1492400d550b02e40e8108001d2081c8100c03000b10b48050000d502056040c03400f00000e600894554000021131004035517021a15540c0c40501c641208002440076803203140e080c0141110003884a01160f44c1a00280c07610b004d0041074a00c5421341c400046618283c41403091845886a105100360004010b50294030034070b0030802e1144103083c0c0380e80c03a01d070203140b054001031009420180016110104100c403000d9803028650130203100f0601444a61110070511030000c0c010013004026810200004501d4208a8044e11401000610b90303180882c3c2515104200d038440c0c000044a5100c495045040d401c0401030078401d030400000410cc81c4140b41209500c9010b00a0102c0c400c0e03040c55000f03030126a554000301d14140d40303241580d0b9a159070ba140a01501e070705c071404174080d500300441e001036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 871446627 1250 871445377 871445401
    0x4031a0f150312090609030d020d020c0f060313030e0613210c090b0d0b0405010228121109030712050105010e06060a0c060615031a240315061908 64
    0x680c00001d0300503c02261440c107440c80a420995400d034111200780000d110300e41e4208205036210320240c000d01500d00946038000d0920701c8510b0400e0040e40001c00040c1c141d195030003120f40c0102c1d09824010070007800d140842c0c44a5400070503642c403190128640902c2520503400d403085441c1450445419240152074129481c0d1070348007c5c001d1521440f04100341ea035690032014100100500100c0d00441d15690580e42c1101511300f542d02d69404200c55041c406058200c12444481c2d89171480035051998006182c00c00100007544e4064036020fa0380d881c001c0d01c1081d6080217100030161003080d501c0c0d01c1d1844054045041c1a0380543c2400000034141d600c00002074000d40740907204620702141c20074240e41880100004850b856611f1034001610071402d0819540d2094980c0c0100e482c40e03802104c000c0d076502840308a403040c203034050103015018103900015160700031002c56a07125501c44d05003114881c108010320b80c00c494006031228030000c05141c600c032201116140d800e0641c0359140b001c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 871447877 1250 871446627 871446661
    0x51e150a031b150809010b190504091a0f190506030705090619150e041811120a0b0709090b0a0509191a10020a0f0609020604031a0f 58
    0x10304120545030920210701c614071900070341c061040100e412590754010012400c00c42014000018a41105000c044d240030300448007281011176800104500f80300b580e51000803180700d418401c980c0c0c0c55000d800c01a0034000d0f080ca0b40035070103032801640f9203036040b40c3c9103a000311a141d10301608036080e200302809510489000b20005401094074904000a01c102524058039042c0d105602c442034400b25a01c4100780c2014020140c90b40200b0b8039030000151240c1d0003004a1071056042a5001f006228041c20400d905908075001c07a06040801010039203200d00b03501101c40502070301480c401880000003642d4003800c45a074418120581e6102c166085891045906a110303006210401841c07610201c4590030246008a00702c400c088800e00b0f40c200c0340d2180061050307145449841d071139407034540340007100c00250303002501040460f942d440302c3e11050a04c0040603960f956081c4419900d80c0001d4074043c41c0d00c040440014403c203514074682d80300441e035500f42d9504000000e0410000d00c10001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 871449127 1250 871447877 871447879
    0x150e06091b041203140a0c0506090307050c060d270309050a291902211201060c05030d0504140615101b0c170c1507150f051e15 56
    0x2030825052820a4400f0f82d103110042d403c0140c5900e11403109036a41001300210900c036116400d038075039580b600030f04141c0c00401035445901306200441c0458804a0414100d12088802c03e0f80d41c2422900840140050364001104d19901e003200c010070501884a090b1060194903104490f660319001c201072224207000348200c1032182401d980907602c641d515500c2802d81c10042d07501344840710305001011506c0882e0500141d0050100701c10080c0d0b002c48000c581003400403000d140512480843c1e4802c0018800c0308104001c14030058207020b800e10070386141c0c0e80c1c1d00c5c00c00d00050070182000c007002614100c40e1801400b070900440e0a0486100229400c4800904501005a400710056035901043ca0300400d412800020b000300060840100001401d10310044c8040e1511003080c1d01d281500007040d641c00746801007516001004048140c4000c65403018800d624032007660718030300c05002c0c98a0460811401c100a001c1c44810281200c0c040c2041c0000d80a4203984002c1c14980d0040724140301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 871450377 1250 871449127 871449181
    0x30414060702060f09011112041805071407030c0605010909061506020606010e06040e0a0e070f0506030c0a02032835060d0b0403020123040203061504150e0609 70
    0x1c00c9507031136802900c01c008050411003110600940464203000040000100140c40080c0a218011b01400801d62071012420304105038607060310b02510a01c1d00c401c0e000042035022520500b003610030f040156101303078090014012035075500d10a00141c1890382e01182c4103400c1122440800302c80b00e07400030445641e50700400e11615030314019601e00001001d81900310b0707020000842d0065131a41c07030b5406030300c3c8032a00080400b015050b0900703002103500000c40c004c0c0300300000c00456490905485d001001181e03425900c0d44d0129060380b0b184602d0203c40d6048440340060a0001c0e5924900094418261030b20000003c0c0c000003c4070700004103004000e503050030794540c008401400d50242e444480908041c003291425110854070070b000711002c42c0143e444000741105421510350600034190f0081c10500729041030f500181c1c4a100c020540350318481d510314143c01c1e0fa0b0319600031800c6912000040d11085e92030390b002001a000449a142c000e184410105007504180e03c0c41e405103407045040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 871451627 1250 871450377 871450387
    0x4020621011a12061c06020712090e1506030c120709031b08030f090a0302030a0b01090c030614131808070605070c0c1e090f050a110307050a0c05160803041406070206 73
    0x1002103c517042d95101542d41d00c521181c80005205100405045003c0c01550101d4200e0001c0284288000e4228190007200d00044c401c00c40040c0c880c00001440031103c40c0c0c3c0320341d159003d4420501418012600c1c8402c2c11043c401d1054001d1410070a40740501d90412400b00070080034119800d840c4a480950307402008941040310004020306045232005203030440041e47c980000f4a441144003080c0c40458410004000c2e0051600c10707405144d80504003441207030714000c034500b1500c1012042d14042c0c000d11219280070036440d44040503c858a0800d28840c20050400344483c0e04607420407206203203844082545540a0054841c030390f940160f1901d415030621500c90000c80140b45075000704140c006020801244034081c0c18903ca00d00e0300d00240c2440c0c02106241030350394217a40500c2140e810424420543d40c00b004a500807141030030003241640305440e001e841c0248000086609090400001c10007040c04002401103600c2903034000f1040341c00b001044010701c10620002d62100d02080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 871452877 1250 871451627 871451629
    0xc030f051b1c0620031905190e1606120b18070f020f0618250902180612010e0c0309151909080a1803021804020621011a1206 55
    0xb0303190141510403c000304900d0b008520b00161800d403484403401e525400b00401078940441c00e1700b0040030312449014420743c204912004000a10303c2c2d0b40e05010364440c00300340d01910007000b40c444120b40380e101002c410380d40c0c0d41c002005241d100d40c500180e107003000400c107254642440308040f5094240d0494000c0e8556100c29a8540c2c000c860010942c082d143c000c02c00503605205284c82102017004c190000400d00e40d0403820020810701a52902c2d40008409400d0b030450001e80060b21218407006940d88031a00440d02440079032000c2c030358040c4000540f04c000c0c1c8001c414160480c0c03c2750190b809540c803503440e9518035000444180e0383c9a48102d0b096600244203480c45504044100c0c241087d40f661583c4600c242c40c0d0702903080d5261080001d0064030554440300101c0c490031849154207820b42580d00062850100d018942d20980c0c1c2600810305654400007110b030140803800550b2070030100312000342c04242e0244510001d800211050040c90040c1c40210707140000d002c88141a1603603100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 871454127 1250 871452877 871452919
    0x803040b09062a06070306081b13090b0a3c0914060f010609080706050913020f070c060318020913110a031b060201060e070305070c0c030f051b 63
    0x344030001683d580c114100446000401e188001d0703040241003945000c03040034050340d0303075544082c6030b507840b075030031001403802580f100c84000e08101e51404021141030f40000180841c0340c0045c050104100510441c8000381d48a0040104c000401fa07040c07850414017400032650403901185009040c002914501d040740d404105200c0c418a54000c91050365074040740f41c90000c4070064000d240040050205c50740041204000700300d800010b2602d1424110300a101e40100c00129000301001400303600c100d43c1e1038060318500054031f10000d40b1003082e414510701d0068a40b103a18082442c00c40c01c0c0ca5800030801100b01510b4001d0040e00068030f56003130504156682010a68070005101c00d40a1a940d906d4901310040d405070000e03e07180c294036848100200f2a952080c0290781c907000c000c101210f680f60107140d11882c01d0400180baa80c42c4442610111000c08000304080c00f0800007000300103070b1105104805008804980200744180c074883e90032071034590841d50081a108005010420700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 871455377 1250 871454127 871454137
    0x1119030e060c0705190b060301050105031b121207051b010813080d06030209100509010b040509040b0910020f0a02011d060112030215070e030609030703090506071a0118060803040b0906 81
    0x5681140c08030040c0e406002d40001484500306e071104400d02c2030100e586400d002c0c160143c801280500325100300601e603881c1c00c1c2c003408400c80c01040400c240c80b11071002032103960350708c2c0841e0854640d00c00e414a40079494803a10240101042e031180400100355102e01d0000d0310501030540070756280401502c030160150008030595000ca900c5a80c0400103031541700c15103018100d4042d41c407030000e00340410040540b20580042503031040078401000b456991324829504250484001d2865407103c03008241401010030500b000c050001a0401c0c40c0c00303007280100169507260b4001c01408010302c0c0c1416440700d58404440c1c155102800612829080c130300381e406584c0c070a0040341e80394882e40403008940c040032510500443c1d6045020340e03860a0502542d40e00640d0940910310309140c90b5400342001c0401d0081502518002c200c00003040340c0ca40444100450325540105190782d60307004520614414134480c9001400c7c6540051980000010341c1c0a595680c80310b14184107000060003055008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 871456627 1250 871455377 871455383
    0x1b0204091209081207080901080402010c05160905010608060d02010f051201030c03050105060904031b020d0209240a05060708090411070303020301061e0206070e12011119030e060c07 80
    0x5192281000030380280700041d001d03540c0d0b4980700c03480307440c101c2d4841c10207000704011015000100031080c001028902203801014003400c09140c1030f00c3c0d81c00121184464184018414851155041c2c00f0100000b1000b04807019804140010380c2c03a110122035070002038030425003244003202d80500642c040d040700d0044080b24a801d90038142c00d00703002e0b1141d0f1801c0c1d06c2035518400d5450180103101c020f01551381d0001d4291010612030609a0300240142c075600c141b00403403210782c0b031010110350f20400000000c40e001417010f030407410100d90045080906502071044100001c0c02c80300c460a000403123508641000348001d040c24010340352400d80350b100903280c592055613000311540700c402c980b014040441c0265001a240d42c1050401707020508000110500c003090034801c24506035002070741d00d40c0000c141c90011130b00010140420212a82d441044040b94203004591012190041c040c00b002000c040c0c804516989000d0184e04071030401c001820b046c0c0003000001c0b074085111008008280c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 871457877 1250 871456627 871456631
    0xb131211031c1503060b030c0901050a0e3d060806180a020c0319030605010e0901050d030e030d030c0801050a0b0a200d2606060301090b01050408060108031c05071b0204 74
    0x6507a0071890b043e40d45070800c9071441d81d5940504624201088814074105094a180c40c07035504050014030641400c0c0b20312007c043c4100c00140365450f0b2610f80d011800c0050444006110195510307110000451a490610110f5444c0c001a190b108500c1c090081901400c107108174026a095210441002000600503a03000c0000310703a0442c040009001c20750251340b84c07032014441040000c0c140c40d150b80c030143c10400680b94084680da01c1004941c116501181c0250004126160590383c030b80c840c120190380741c02401c40101d00705801d9044049144001c1d594210581e0301d035000c01c04182c11500031820380400a001da030024034000d809800680344be44540e0415109240802803600c0c0d0f0f002040800502e00d845d500070320744009a007815901075003100084061802d64089080c3d40014130546a0a0344c45181088950b40600119005098500140e40556031248159035407544038541e9013031035508000c0600070304815481120b000e08101da139808402501c4042058541c249002d080e68410303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 871459127 1250 871457877 871457891
    0x72906120f0d03061503050405120c0c1504050a120507030b06060c06011509050d0b0406020901050d0e07080c100903080a030e0d081602240901090b131211031c 70
    0x1a008102c1070b045584035035001306405040179025101e084882d1030f100181800e080c07d100c001180810440d0b4104240f007500ca4a40c0011541c861602181c1c00c521034014012420307041c5004000030050007a26816915050a15541d28850a015001c160058213641090000303000181d41242d005401c40d500410f02c83c1458660b800ba00e0401d54207a1211445070240802c88503000c0e005000c0c4001004116048031004460352900f2030320540003000100f00603030000300c0741041c1c0e00400c1560103503507120b10200250340d4014961342d034890321401103801d148941041400c0341c0c5071002903585040101d69076280c047d4990754429109411403100c85007496102c542156411100b008640c40d1425680d072091403504001128181c40710070a000e00c0d003107401ca0a07044515400c129009900303580c80e0015200c0315990208014010710790304800600d00b42c1c00100740401d084802c401100e030b4900900e40603074024244507094945120100c01460756400c1844040364483d22100c2d0000303141410f03200400c0c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 871460377 1250 871459127 871459153
    0x30a0203191703061806190303030501050310110406032003070f231602030111030f0103201305071e17100605070f080c01090807290612 60
    0x220310207000000e00040107080303000c01d0045041c051450001c90050a43c0356003000c4001c41d0342203510a0031030030341d00c2c0400e0200c0c1c03994603668014881c0079681103402c4449602d918004014260038800c6511900c41d04ca0010340714503045c0b0411080030507940407180340c11300e00340f0103a002e02a03500019054407880c14650101840c0100114410091655040012140b24201801441032685440001081c413030700103907588840c00445e145a5007c0c26401600782e0740d40300007800342c00c90000c1d44c1c1d64600c002c03091040d042c84908038641600e1040c1104424024003a401d4420084410080c540c06403880c81c45074500360056000941101151519540303a001602001d504a0005003181d0002940005081d10303e070f24070f00d00160004040040c180d0310518110004015009488000d0b002e44415074040007003010314030803918880341900007407100e81c555041c442001e42040d4401c0e9145c0c401a00c41158885c202d15260700f0700500e00c5103054030741d00c82d0024040b41c0c6081d08150105481581e03104070103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 871461627 1250 871460377 871460383
    0x230901141302031005090606310e07060c08030106081306060803191b030f11060f060a12020a060e21030c1903020c010f1205070c0b060d08090906030a0203 68
    0x1c64410300e5551141503480344140752418080e4079140220901c1c1c20140a801100401c4c0303030781c0101080703030500c81b00644c212400d0040c000e1100c205407010a00c414014400096400840f45110407005035020301d41d90b40c0b81541c282034000002880c4000400060007260700592580c7d410610801c840c0507214041e079030702e004940c219040b0210561021540d0300160140d0407420000c10414500400c8160092807a8411510500802401d00019142c84443c41e0b00c02d02c5204c10140c201c004a0341281445e202e80306c200b00d01661518003c9240e1030b00440c03e40052081d024000d070b409414030301ca07980747c031030101c1d50034010a0100742e00040028001a82d20b80e1101000e0103132801b00061581e4100c01c0c001c640c5007456404138031030301c0d02c0d00070910340100341c01041d03480c0b94000030b00f00361140e2204044202c0b1700c040d24070b803554042072810303046c07010f9141c1c0445180c07069071062002d010f5030345441c0c08010000c0700c40c5000a11074001040040c1381410400902074200401400700c800c49007580c1e0000341 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 871462877 1250 871461627 871461631
    0x14122505030601062309100c020a050a0b07060c0c0203070905150a06020618012009210d0302030a0f090809030f071202041d01180506060a05060a0e030717030a03050a23090114 77
    0x1c1c00d06038403801034ac50815107050040c08116019801070340391111192144c054000b02400141ea90034502d0991402031907483c825550080580f038000345c07150103440050038299a441400031031a0030700744140c101a070303131002628910740041281d665040030f6400c240010f1146407020b5501d41070186264030301240c41c0c0f54440802135006071220b01755014000208c145a4484100c540d004002480c442d1020841501e03021a030316000d0790f203549000405000c4c11401d44d01c0403205d0b10b48a0084248090000034051240b4210700313840d444081840c083d82c1d80d1a0f00d0041b03d480c034000106200c010b1a00c3d9024070046a50000d100c2107100d110900301d8211402d0341000a0102c030038030341100c04c00c4420701c0060f81c0300720112030f01c04083d420a4003152507402402142c600313008420641880300d990422000c80102000d04080c10601d40075092030341c594024a11050100342458042014810035008281d40c011000584001c046030650a980c42010050840b0b40195a0382800130103c20102180038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 871464127 1250 871462877 871462909
    0xa02030d020106080f03070b0714040302090106030e1c1b02040e03030a1b0503090d031a130e0d1d060a140406020304061d090114122505030601062309 66
    0x10314030310b001105030401c01700c0c2010380c0c5075410810040780001e030307181d4049400901034640340010482946404060313206030b0300060f50210300c40c0000191a94582c0242c3e0492818406440510510004140d082c1d90000c50322008504d02c8141240210000380c09680d1450000f08081940d40040c5403144c2580c2c000d48001c04103d485035030350400c05098a6030608510300074a070040c40c3d8034100d500320b03440d403000700f11903020140c803501c1c0f1900e0540003000c03200c10301c0e0000780300b4003c40f200300041200a000014943c038540c0103803051010214054484095020a10344c5c40d000c0d49000402000b00310351161407041c05010700c0c007100d5804404a80b000d403000c0e01c0300380c000b180e50750304200c806402c40c00b4060f007801004007900c2c41c00000341c6402c1c0d0540d044408282c035046000348000000390080d1030303108090f10700d0311500610810001c041d94400e0240c4034001490b50000f903c3e40c0525071203080900880c4040703110800f05501024042c030380c1e0710f00082c5910740d4600307003030030b900c0041c26407082c0380200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 871465377 1250 871464127 871464131
    0x1819170a0606080d08010b1809070314070c0b0a0b0a051c051c18080d0f030f0213090b090403200114010b07060608030309120c010f180506010b070f0209090a02030d0201 74
    0x10b40c42174014007a40d000d09444150281005091940f544100c02985101130013410494040b41d07030385000c2d4001d228200f25075061291140f0b000b900060003240340000940700d00221401161000c0e901d48070383c000c07242000d030484003241c0c181400e1000c4008a6040e00d40c0c0c20400001403404682e0074400303448040602d80104520169021004003940f01102c0d0410320408a010100b201540000d04002c0b808950f003403031007040700d8090054004001e2110402040f174000980142444e0390a4489010b42d028000c04000c0070b1200c00610030343d5001150024081640780705440703242030049000c0040c6102c4035002146054092000b218a04000e0b8040c40d0a072a000c16040200041c030300a5402810164008600314503000d40701ca541c6062070721507550b6901c4001071144070140203420039407440b146400103101040703072400001092200c6c00020340d600e000307440000ca1000c4400d806c5454441c1c00414510700011070f50200310081d040900014024802c0b07080340b0006031020b0044d01b0f2008429000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 871466627 1250 871465377 871465393
    0x8010b09010f05030c070c12150b0a05012d0908010f110f070f0609060b040c030c050301061d0d0f0b0705070c0e09030c0a03050901260a1d030d021819170a060608 71
    0x26005410b103649d004419a0402d0907003207030380d222060050101c91091a00e2081d100398070411203a6070a603502021654013041c0302101c2643d8015601710103c8822000030882c0350704650703101d400c80c1c1810219086180f010402e038071010780b03880003403e4014044e501132160001141e8440d003c4030310310b07038084405035125102601c0c6850188192101101030341014000c2c1d2420030700c014020310050007200c1c2070004e030003180c001c0404458994680d45c3d80240c5240700054a6003484074030b4240307291742200d0030b03440100000c442901c1030080d5641140d10040e81d104140c03c020a00420f600c1c018000c80c0103210901010601e08005c10204140902940f038103030307484400e81c0004110041600300413501090554001b401858910003003540800c08480026105400c84d81010020a50002424543c40081018501100c065008140110320b441c030070017455510300309000e000c41232000700044822281004010303220f68452691240a08881030300c81414071692000121140780d0401042c6a0004074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 871467877 1250 871466627 871466633
    0x12140706080f0c03070c060507020327040c020f030d02070611130906050f1c0c0b12190b030a0f06060902040b0c070512100c0909090303020a08010b09010f05030c070c12 74
    0x40303840e000f0341c80e940d01d41e10394603011102401652684100030100d40c2d84d4000906118800c0c025949443c210841d101c00c03000c084030007022152070410007180710740d24200d8000d0400d030002400c1e50414195201541c14801030008480085d00212010350f49030b5200c1c02e44091045100005004100d800806d10001e03600b003100c0d00040300c1c016000740f402101d0074840b10311b455640e030b10017820300d000002411076071036024036101c5076010340c42d4041c4d910441c0c00310b54483d511714010031503845602000790007404901c800c0705050a842d143c898140d010303002204240040b4030305001300000709004c0c10010a005503290008401c903840741d40724040101e8007140400341b0900070700c608002400304548850031800504007107611051a03d1421b00465620400c1610003802201c07950300500720180c04004c00a001d0502402a5002550907400503800000102d9042084c1c0242e80744040183d40e41081503516030703000d955603070014090030001282444000001180c441c5400054000d0300000000004645 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 871469127 1250 871467877 871467901
    0x11e020a1e061506020316080412030503190513030c061e0209040506040501030b160309120302041d070801062d0504150503010b0a05030c0904060f1404050108071214070608 76
    0x140e283d80720074891035040180e20b0340003083d552030b46610251140116000c0c41c00b4089449258425a06504600c40c250245900003005d58880c08112134421b1a0f003c2e6510700314200c0d902120b41d01c08040c0e0760000c1c500483c0c850040c0c0706032940f0413000010300010074602000103e640340e234000200e54000481c641c141c185805a160008016201800a13504640d07400c0c042890082c281c03000300d0100101402a40e21907002690041d030005002140419100401030207035010b402406144a1081010500304811105103071295500d0356a0385800e90802e507040741c046065001503096104c003440140480f82280020840180241d10340c956518039200c0613030100382442e0480d1040c000144010465003100c1030464091958a24089541c1ea071001c803003941c14051101d141c0d030031916000340440c140c12180403502c242c410440c0641c502c1360f0070b542000152503003400b036104250004481080b01b0300e640101c1c5d040c40c41c824260b207100c0110b1780d48603d1401d038042c1c0c440000142c0807424004540004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 871470377 1250 871469127 871469141
    0x302090a0b13170a06021e0a030f05250e030a02130501030c050a0f0b09011713140d0e0d0203030f0c0105070f050c0a020f1f0201020405130b011e020a1e06 68
    0x64a003590f1000040241d40da02c54240c0ca1010b0844c503000602d1150440001094030113501c2529503041e119103201800038001c0900611542181e46064042003e020404010082d08070801c0540503004000c480119032140c014140541c0522801c201180140e41f03241000300ea84c490500b00064561550910407650342c06640101c0c000d00c4030050601c040352000340c9100580b85a0b45075140da40d0f44201c0103c60351095030400c0740b4159201018000e0604c00c0400551256010b02080c3c481e0300880d401e05070b1146560009403010400811590140d4100b010b421082e00c1c0c0000c003564140200c41a80710400c1e800041c5804c0a42d55406c1000a21500044000d07640380310341c1381041c2041003c3c1c00d07942e03550f080301c2c0d0007a04c25040c110f4007032916038601c1d450308404421a041040300310004d0001902035040ba000300e5120b203640403d404418802e40c0701d20300328020705030341e6203c0540b20305a154000c5404500d0050841c0103080f030750800310300303c3d00c002c1807141e49917000c3c08080403141c02d1000c202c40320 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 871471627 1250 871470377 871470389
    0x7140c060d1515200c06190e0109050f130204081204080d0203120c09040605030f161403151302060a08040b1f1505070f06050403120b030d0f0302090a0b13 68
    0x10842e504400c00e43d02496130603010502c500321400c000a41e1030110300c5d01c0b54108000341d010303c001a940107490544c0080c0c0b44d51a10f9a220000b1024602c80191503100003070040300e4003d01c3d01c2d02031501602e00159042c402d201c0104d0014a482d85403400182880c1c4844000b000200c0c000404100918082042042600c0c5510141d03003000c4401e2003581d40d845e4040c1824115410126400c0c46a03070b42e0b40d102c82c00410004088071aa040d03c44110f9072690303031200c081100100603410020314170010641c0800e00710380040261203150300160f00b0080300b20001d40703a110101600c03400580141c0f51078009040700d0f0840d45030718003949401d240240c8040c800400e212415100d202503004050070102c61202912241d26030032102d0002e0b010100c03040d02418901800c20f003150041103060091590100d402513000f9510301ea4040c1b044003500050f541103503502a003691180c001810070510036070410090200c2440d01524091000e00052002c0f1195003100790010000503400e8210a0f180110900400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 871472877 1250 871471627 871471649
    0x4030f0b070905030604060b01031e0f06090603082b0213090e010c08010312020a170c0607051303080d1803030506040e07030c0b070305070b0c040602010c09080307140c060d15 77
    0xf0a220200362190005000100f550391240304405060380250040c100300c070b02c0b0344101c00e01d0b25030100300c60b00075100a031601d90310315117801c2c00420b410116014290959400207041440c00a001180f01d04071440c4c203814143d9600b0600c1c6d035111911142c0000c0c80340c50311b100b840c80005424445804125914006000c190768076003140c1c0c01100c2d8101d000c0a0440790081003440b42c500042c0000c1c1d041406405006140c500181d6020904c000c0000c00317440102204022205a50380d0759109031024461200d20403c0200749190800005041e0302c02003080079060840424141c12060180e103008041d40c00803004070780c481c010450903080070321490710701a4015000f404200d146440381d0450710743c036014400200b100060400c06140c064030844040355880300d40040c152034201e0f4900403d8125016404c015400c010280000c0c510030701e0303060191170205000e1443c0401d141d2b1602600c80304031411011a00800002030709d59a11007014003407039800500040740070030040509404d800b1040c1c0094201907 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 871474127 1250 871472877 871472879
    0x30609050a0b0d0605070504080f0708060105010c150e031b0307020f090c090d0212030c0604120314010608090709050a09151104122f120106060e010318050304030f0b0709 75
    0x10f607481c40484801e507007050b400100e41e2034a04044801d8441c680080d5424440d441c6c04128504000540d4421111500207454550340c89100440d040f40b52000050400c0300114110303030b181c1c0c04c1c503401000300309420800c5a18010010034032084e408032600c103000b483d03000803980070150b050801d003221580204a0312502c091400b050300e80c04500980c440e590044144c00c0c0c0c480119114104d18a21680d482c0382140c1c0c84d2041028815a103800845044034200e9448200c000030500038003400051220850001d4000d0b820400221803411005100c1c0c00544980003000034840307400c0c8074880c05155a45000f0400e08400e017000400c0f003840841e2113014620304040e986c0652144c1082e43d00340c1343c00c41d490105264050510300784030b03d014013036040042943e000440f004a0950070301d001001080c0c54403040c4196280000e4204c8405100b03480105180805981166100f84d02070b6a140810b44071a04100b00781d900ca1620391381003504100c502c2c0d0020800002480b101d40840c5078008404e1508505076 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 871475377 1250 871474127 871474129
    0x301501090515070213180212060601120e0a1403130602071809240b040c05161106130f061e1d06040509130606090c0804170f030403030609050a0b 64
    0x4901000c030344040b12101084400441d074903454141c4d10390803090401d100e4485000103124141c0d0014030208d206041c1c044000070591001b290f102d2194005031940350000b007a40f6070100190510f0081c2641074024080013000180b070b0840c48000c101c404600a517241c45469041c071013051120382045040d980300314402c0001c814800c1402402000004001c01c078800a841e01d0411981d202c6c1c140d10700802441030200843c941c56000e0840304804441c03c0c03103a00300c2c020065505104940c0c4048010300e41c0c491082c04a040841082c08903c0098600f07890100300300e210400051054101c400705c2c9818800810290758054080541000008150300122000130740c041d04016602103103007568107880f4060121541c1d00c3d0f040d01d006100142510140e1f02d0221040040118805c0b03040f00c1d25850120042403120071031044650580d925100c2c00d115403503a0700c2c0d1008607115680d41103420001004900d2a04070440007550282d8425180800c4880c01c2910307880c10b484008024081103803400170350f1101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 871476627 1250 871475377 871475389
    0x41a0702010c1112070615030c030809131119050f120103050d08011d0705040b0307081e0105011d030a06090b0a050c0306090a0c0908070b04031a15063015010905 71
    0x42d05912400014031909402180d0750f51f41c00e280d0019003500e009410000030302000e08000d0104000c00c0702d072004c0013004184131808580d4990380f03800c4140c206000f00215070341680450000f41e8000d080c01c508041a00005001c50340c40350404907285000003004008014040100b181d02c107595041084066060400c404540f40c0c00c6501800000003010110f04114016821036000d000240c4074590340e4074003c1c0c0040e02c00801500d00c034071002500c6540c034a00743c02030000301c0c1c1600d805035a169004d1038030005584030b0448004000754903004039820800081c10381e02c2155085442035504155030320f40311220b00308450000b0014071030008100304120507503484452050348002c41040c00203500c0c00041080b5100025500000075500c225040410400100e41c0a030040304d110303a40c19907105203200d4102e10441004d1b07501c00d104490742509002c9078038124000d000741125080c500c1a840fa007a82c52061241541c0c1220021040720030b0a01c0400c0c090010f82820803902800d040135528500408280 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 871477877 1250 871476627 871476637
    0x14030705100816090305070e060f0103090231141f03020306010501050304050a20030f15041403160602120106030c120c052a0c09040b0c03041a0702010c1112 69
    0x6203090040c440f007183d99001e01031510146030000c080f42c1c2c0c07090701e40382c682840c040252045c03403046da610303c4411039540c807a00981c038140d68054492690112200783c4000e800d008481d40c0940301255140352010b0045901c1104504428039891440702d0821264030392340c0d4207801071000044124400e0510140c0c40008001d0f04688003840c28503560342d0790381046070a050780300d0001002c014113004040c070b225000103000a481c050440a481c00980086c4600d40d1b80c025101f4008030600c5000d0005010038000a40f01440e0001e04040c0c03440c0c20321601c0c1019a0718501c4400b1216a540402d18011310700c03080140d01e008d071400d414108940703501e11901a0100c2c0c1c0c1060408615a29071076040c201510504c01c1e10410207421a60b00308548003040d1900c3e108010032501c84061007115041d1046141020b8164041e0760081941c28140d10ba010b101c0c541540b0090060707521058003959039036503002ca1400d49100340038a90000036800b545080c02001400c240c8403014046c0d0094038085008203401d02120703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 871479127 1250 871477877 871477891
    0x10905060403081204060b031e07050d030e0f0d02060d02070b0a050c18011e09080f0607081f210203070605030c160c0f0303090602100612060207050c0901140307051008 74
    0x4c84580d54905d0400701600048a110360180100d4141d030380580c82e604041c400072600c0f05c09551444d0707280c1c004d024075001c0e068005800107100d03035681501d600f01842c00e03480180d40a8043c400480c0c446d0042541e03584090b40121199500046190a2140d43d12a01d0380000300e8010a0156003055419000380c1e01030400c0c0340d0740c1c00300f100940110382da00a1504940074640f083c00240c91310542c04020700114064483c2440302d000724403511038258804188640301c2e0307085490f50502500e0740c082c4104458107200c04402000d140f04800711300c0025083c0b500505010000d0061303c1407a4034410b2600b000d010750301c11401d000043c0140610b10540c44165211820b12a180540284050800404180f2258040200150604030100c28541d211881b0402d50b030940e0200c4480e4054248420101c5a90703101d9502640d0410b520000000e01d25002031003038a01031821501d102540b4000134414442c281d001a4109026144100141c10140007107402404116070b90001c942980780c02603e8554020611 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 871480377 1250 871479127 871479157
    0x90111070b0613050717060301020427060b2b0527070302040908031f030510021c0c0201060807210b07170712050c090a031b0308160201090506040308 66
    0x10300141c48600380340085010044013032100c0d00b05400040c125452094a204032060b01c60001051800e0500031a0304941f00091850b8600c01004140c5034040b083c0301c0301c1d15041d0785a040000c4c1d80c0320750b840507005a540e841050410300030f03820825038078074060242d25800141003408102094107510380d10030205c4444032508120f0580400020305211070340d00001c2d40245409111000e020100000d94401ca14110140c0d00e80c400d04990600110030318800203101c0d900403100c40c0010281034002d05500080d2400c0b03101500d49001002051f90781c2c002540c00180e54482040045581c200a07403c02469482d1805401c11028201150f64000800c3c01a0000c641c81020814041c41200d4141c0c0342d01894410807140d0a14a00041c00810346010134050241001d01207200902d00d08101c40382070f84010f00409509145580d0ba1002d028048258101c801030305c100000802c00b010014210703016500c64124003107083d44000341420302c01d40c10083c0155011300060000451f00004c4a507404507019107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 871481627 1250 871480377 871480381
    0x31d010f20030c03130509131101050702040e0105070e031e0a06090203120f0702040c110c280906030507121203020f1308030a020d020d0e010c0f0209070512090111070b 74
    0x18518510500a40206074803000030744501c03003c58240c45d14155501100c182d52a40c50790740c0c0e040b4020307440e00009801200fa120b0b50883c04e42c0580000d007030140c8042d0011031900c0f0f081000c50300310307202164054041041d000e1540050302c3c043c031500c06c400429800e69101c0b00b9018003c155200500f0a00507c20b81c0d4a00c1a50195641008421054184410956a01c95503d518819603401601c0c040340a1800c1039000e64019016029100000c11404010801c11031081c080140d84031001d41034140400001152018103003159503018042c02c040540400e030945145401454006550301505c401041082207000040a07035000d0280c0403002d10780035850b0400200b120000d03100b402c4200a02c5032288600085018002c405440440c20f00c0d000e441141d51101016a22428100d0007080020200e042c0040345602808141c078105014100300c0075980e80039070110b078a82c0310176601c0b900408c80121702c414000d00c000300d1155112810310f000b403201c0510804444194081e40344001c00441200300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 871482877 1250 871481627 871481687
    0x1104050c04060e061c02030c071509171e19020f0a03020a29130b160519030b03011d0f0a0218190f020306100509090c0322031d010f 58
    0x2c2d174030705a9008100e046507682050a0108501d5210803000c85071110641c3c1c4aa010102ba03124000072250042030505a0b0702c034000c1880b007a5841055000c19140d1280c42c02d00d410001c0380082c2c001c107000d1417040e4211000580b40030385002d0030800c9003e80e0754402800000065400300b0741c011119481040039241040c21440019504003a84090a109108d1020072681080b4040309540d410700038660203025440b140300100c420483c00946501048081018807160040d01980c180b1002e520f140001364410810002820360391000103d00c80440325911034040312005000001d40118060010a80d1401503408218403030a2903126043c08058540000c6001d00d104a50100c00240003400304035958484403240000e40056603150b0141001e581840d203440e01900032582e01040060564140341e54600b0a492a640024080c0c08030029141401703c4400881052861041c0302c1d40b60003080210500c841c400c07103c0000c00300c50400c810300102507003c0341c1050b242c00c000b507040501c40702c14451100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 871484127 1250 871482877 871482907
    0x50402031806070c03080a0b031b040b06130e06030d020d03021b250807080c0f04090b041104050a02070201080615041e170f12031308071104050c04060e06 68
    0x95402407280100010002401e5218046424a500c6602d481d08252990041a4122510b81c0f0600750998044c4c8010041381c1c40300041100c4200c0d0040000c50807220041c04512143c1291507409203c2c1074845c030038002e05008100e4141d02000c20780c01010301a2000c0700095a5141101710f42040c540d0000e03040c020302034880b484400c1c403d80074049440da00411210314028504005660341c007281e090707401044100d00403070b9003001c0b0ba04840013000705400d002c08102c0088940700c1150b83c0103a45014003030000f070030619524411030140030303c1d0700413a07203c030140400e5480003040a00001c0c410442000140c1c0c10911054200c1420f07500c0d6a03c03580c01c80c589404910841e00449a10303640c14206403c0f00303600c03100450a940340802907406601d00c21081650302d00d00340c0b10394203044e08404000c148202c101000b440d032040c01a00039007184801525070a105a002c80002c2c1c4002049810b03080c080d04040c001c0c550807001e410985842e1a28151000300304001600d021440b0365000a0090607145480e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 871485377 1250 871484127 871484161
    0x80f04090207080901020d080606040e0c131d07051213030c02060d020403031701121713230901080c060a02030d020c07240503060603070c0c030308270705040203 71
    0x210350119a50300c0e0034189107a00d070308a2503e50b030040c400e200c4280e2400d4850310125018080140c140c81c01c260a01444800442e0020300500d0540c50a01450303101c1078170708043c0d400621143c1c001c00108075800003030f90410400201800c091090400140c04405808141564417401c07483c00c0d09007403412071030104d079400205a4003a44c0701c000403c400c1080c080550040080360303c25210f2860003c1d0035151170031924400d11494402d00c00310700c0c590b03000c2001e2802e00485607400034103061510a01544068100311181c0106001681c0010066614903110354410031f20201200e507010190f140c403070925940c4940e07540c030900a101c003080c10507189008106540321400f10910664031490307050780543d912642803082c052114800100324080003440b403140202d2310260341c1e542d4a59a2100c003405220350000d004101040000d21482c4045850030351704802541c429541c0300703502d0070030784140b030030321244410868122085024003803811f40b00040e05800f1a41c00395000360703c036a00c41880020001907 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 871486627 1250 871485377 871485389
    0x30315010e0a030b190b130b1c0c140d05300f09030105070804030509011409040f0506040e010b010909150503240c03010e0f04020307180504050705180103080f04 71
    0x282c000040b080000006100744a060900f06400c422065070701d520303040d61402c08000360021482120740100c00601c2d041889491009405942e4a072074400d0905960462840c06882c040221842402070100c413584001c1c003114100c58405030f1500b191142c40d00c0c0c820b140041c1c50141c65a01c0b61080c46006107803000a000312008055445421860075406103610241da0360303120354604000145814000d90b901c030b01942d09035440a007440a481d0041d031715801d8a91703008512420600c21703050b20703550b60701030001d22018408010400741840b1084c041030f203002902041c116410040559460703640700c01c0071002c46100034404112140350b140c04884852490300b140d901801010750320281040280e00a2014003078a500c60403e5588082d51450300e40005e018004003051054042002d1214501c4280d070007a00040c00c0e2002d040e0b0b03854030071030180c0c400010080140e4881e801c00c010b0003414483c0c0c100925081d68a2658501c001030134400ca0801404014058a00801c1e04424070502c030003510090301c0c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 871487877 1250 871486627 871486639
    0x30a0504060609020706020d0501060f050d09020a150e0f010f0203070b060d0f050d0f1704081b240130030203090a180f1b0311130b13060f02030315010e 67
    0xd1700d0070004003075404005960a05424880000f43c040e200c0c3d5004016035245607100c50901c05060b000001610403040180d03800560210040742015000408049036145600d0300d5802c20082c2060004104032094070906228584060f06002e03034021040383c1c00d02d035100518540c141d07101c90004a44070460780016041c000c8100c040d00401c5400214040f01c40300585442c0110401104101c5040d00c42c0c0448014003900c3d800401c00003610300c8007a0040030620300504131101441d000c001e00e400c43c03d0f0354910201c01c1c80011140c00c1440b03550707070a001d00341a501c414005044d030080081e1340413411038512400500d840e116014140709200b03541c1c50850060150107100d60703c884040341c1094403180903aa443c54452010004c1c44148030301228801e800d605400200d6a0b00c030143e000b8008009100e12800040042c400e06049401d04600580800c0c1c0c4055120a491004074590000580204040c01441411112240c0e0004181e03a40001c510311140c6501c019100120341c4485190000b42d0024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 871489127 1250 871487877 871487887
    0x24110d110a0f0f03090e0103021507050a02121e0610140105040b03100504380402040306090b011e030f1101140a0201051b07170c0a0f050c031006030206030a050406060902 75
    0x1440c94240f64083d030095a54460301526400c400711204403e01c40254000c00340d010060008507901c1c0682007450240c42500e094044c40c0d0081244015964503c600580140d50601d6100d800100120030281e1480f00802280c03411001c036155122729400350183c4551419075900c0642e00c150100c4014250044540740c40c0e003032031410a070b00c3d00b5203406054030650522202c0c4040e0030f08514000d117419002005899290300481b41c0490040b50041d000c0d070015000c10011000c19164064041103511460200c08158501010710301c0b800d58088264000030840d01c0108049554030410a8507240c0100e00c259154081c000180c960b45040e41140348000c4022603441c04a58042d484148500c120b44040c8030a5200d4581c16039440c4103807a0300901981c0720701240d07000e0007a0407000d000010202012907440081c103468910403a452031008a540d6413003854260481e040c2031205610000b4120f006008550644e0b0002c1d0300f600000f0048103020759200001014010760345c00c03110080c108030ac2c04541e0740c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 871490377 1250 871489127 871489133
    0x4050d06050105031c0507201002030d0f0b0904060527060402100207060f1101060302030f0604061401180209010903140706110d09031403120124110d110a0f 69
    0x10340003d2207094420b0180d26080c2001c44c400c0b1071400c480f40a5680d909251030788556544101c812090041030100031200d900e44980d880d6100311410010301da03002140c6400844aa8505031100050850750075820840740300066102c0c15402a0450383c0010007080325a1aa070039911340800124ac10040c1c08010200000e00e0310010680e580103078026240103040c0100080240d03915611881035000292800d003888540611445500b403001e10b031400007081e8030f0390381d800007407a000f0071100200722a0480d0040c0000c0000c03038800e541940110b09210302140d0300d80b4403401009240d8450000805400191480d5541e1050601030b01071544035140c031801d05c3c0002030031131f541d145600495021a9a058100e0405400014104030642140d962860040d086035510481d0390580300541e061480305005c030f24980c4c401c4503d100d01a2080446964604401c0c00c51604407100d01120340d001d0052001001405031004035600000c4442400e0a070110b40201039100c0c40c041040d10003a2640007164038002c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 871491627 1250 871490377 871490381
    0x3091f05060f091012050f100b010801090c0f1b050f030a0f051e16081c06140d020603060607050a061a18010e10120318090b0d02040b030304050d06 65
    0x80da030241c1e50360501140c1c100070300c41603030816518014000d002d0340003048045d881d01c2d10301700194405e0050351102d1210b5103007180b40c8128058252480ca0302d5510010076941e100352010b0042c035150310248600750a04030064044c01c0c40071074402c100a54546402c1c800304000c1d1a060780d407540035044403440d03038100501a0b100c3d00000c40b80000920841524240d0a1052041d1071707030b81565944010f07a508618024030b1013a4440420842a454000552000300380d49101802585c9404e0381d6080a000c16130300c002d400c581194102c403007584410a80f10300161180003152000c16819038400b581d075214800003c1e80c2d409000c5006240c0e10500202404015140e0801c3c803003403031103100c9000030001d16000c201e0100c8005000da5202a80700004202144aa218103a00a06004080c0c41680d03191039852050001c0c99070141d001c0b4521010481a000507455100c0c02003c2100c030030004290f20100144200040760b10291140f0340b20b020500c1c036075030184120390040900030040000d0f48490300d48140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 871492877 1250 871491627 871491631
    0x30e0f0d090906050a0e04020f03060f15041407030b0105091e150c2119080f0a02160602180603180d140f1305060408011a0f010903030503091f05 64
    0x1e402640004003455a801003a003924001484a881030703081c5100c04050000003002a64010510782c1d5410344c0c1e031018440d4600490100159170450320b0a54401c221041c0001c03200c40c0101d18180c0e01600801125550907000507841c900800c90084801c0102c4160042c17802c0158440b40040310044001160454245845019208803200300c2a2080000050103021540681d9400c214454003188a0fa4409102c44d11840b0341c1c03117802e01070208800110300102540203404902a0000d00ca110000b400b24a0f50054020300c09602e0f100c01d07012401030751820424010070701d58001c83d4552035442060404000c0707010141000da10382ca407042e2994240410100081c2603070080c0c0f40115070440c458100c0816104010716150701e040c04444040d51282c1c8405044a1360900095010810340d0781d5400800c020840000040340fa0351082d02d107100c4d0342012070201c80c40340c900c0c015584860b90300400c40008403901810000e8a80c0d84071819a42000c4031408010004211560012003200e0070f130b8007840c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 871494127 1250 871492877 871492903
    0x10e1e15060f09090c0406080105010804141c021c0914041b030c11120f031801050702030c0705031b060c031306020709050604090b0a1a041b0f090321030e0f 69
    0x610798496140c105c5452050303009290009117428014000c95002c1e80320a50414030812041d017040716000c9003181804c0f01c4107070401481d05100c2d1484482603040000054883c842c0b00840b5461070030f0b138005054581c2621591624681800000c40d040d602c66110049072034292103500c3c1580b00c0d00a0040081c00310312000800305040d854090404500001c504004080c08400c003403400c2100120302d121a04010001c0c819680b10403270860760b801083c02103034001c08441d00110345801070f440e0054141456504068000e0348042002e9204d065005c0120074035440640d80290768414201c50700e425440380304c0500139800d403188000039005900150070401c0301d59048040200da119a01000241c40500c0d001420710b246507008186000c2c801d9100011003401040028603a000c580d0104003a15600d50951601000580f92480740542140c1c08030052411882d003c4034a41c1960b8a0f4150700800303801d1010501d004080c40c5040038003075401912500c5a40007140c1900101d038842c1a03440200104103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 871495377 1250 871494127 871494139
    0x20108010e091018081222110d02190605210f0a0b0118141801050303030c0c0718020a020f01150614040b0301031a010e1e15060f09 58
    0x92500714905550b0054041078058405400c5500040020740b5030421039041070b400c1c2c0c00d510800598484020200c1e070005500203889842c0c220f1455122500c2d06801d00745801001c0350140c000b4049821701031181c201101c44828000a0b4000309810040c05003601c0c80d00c01c05101302280d115040805011200302192000b60700c202030003003141d010407042e00d1071031000c080c010106602c41350130341000e0400581032520030700c0c00c0114040400d084826601994580f160858601242d0400390500c2d034000c03d456000e12001d501d0311000c03940d40c0c0f0008104643c50343c1c000c101e4043c80c0b10103000100c01840200080c4068100c0d0303000c1c400c000e41c801c00040340588201c00f1540181070060280c102c0d44005981c103841e242d0714203c011340f0343c2d8210341c19442c8001d00c100300c049003460000c8080c43c065801000b2820a24142051100c0e56500681041041c0f000c100100007011502a0031454080000300c008849a282c3c0702c14900c551880c00c0001da440380c404038031010035040358800307010a00c10131501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 871496627 1250 871495377 871495379
    0x21b1506010318260f070614220f050607080f0718060320030a0b010807020303220807020909100b0117010e060d060612021305090c010e0f090f010302010801 69
    0x6404890f80009071205140c030010b12580803038042030030342c954024400c100c00000c02c0300000c600855401001da0b0701504078003103904400d003d003500c00d5101c0306c03010f05000300e82c5091108610710202040001d4181c1802c1e456150030030003a20162406201b41d00000301d0b003240c20814070150103410110f4594900c0034445000842c1c543c420401102c0f0340079030a040302c58403400c121089000d03183c400030068500c1c40d030482c454141e904201c0114450880c8400c0001d003040a0000107045020251584c41150300c14418001e9040407041d416a8201e0103590300c001584240c07603c10b0584c0264030300a50300554a404002c1482c0e0085901e54410080250800815000c00019240c000b10045026a180d1710403006204a0340440342e129000b200040040d51030180682e1000b041d07545981080b140c3c010701c01f030040214205a01d681c801c0241420040c805440c01022070b03030342c1c0c0f58828805810002098101d140d140c5400b080c9111080024141c40e8040c90200400c0303044000a00c0200d0001e81c0c1c0c000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 871497877 1250 871496627 871496629
    0x10611010903080f070905090f0f100e07051303060504060506100302120606091801090225150b04150f14040510090c0516030e032107060f021b1506 65
    0x205101d200c0e0341c0742d141c845281c0c80d118a001d202e25001031141781806090000401d0543c1d503889242d10540444e86140c0e0f01d0716040420081005016096a00b40b00455000707210801d98030111940c81140c42c0742c41a1a0403c101c901448481c01383d0024060919101c01d2200b484616000180b00d05000c1c1e03001030070703c0c0343c0302011402c80c4140a9120040d6050700b001caa020700e0a5402041600001815200c03a030794191054a01a4400c1c3e2025194982c0040c4d140c61011124000300c40c030020300c000410030304030213449014000903c021083c111075511480c40c44250f60701d9201203109000e49036210726180e150782c6541d200320081c2c052200030100345040c1d00070f1850325006452082c030b82800c40410a515000c0c501e0050b04000c00750906002d0305114410075503c0700106099818002d03510412148141c509060501300d0f01c4030b403a14501110405110010400344c11a02055801940003070f0f03500e1900031100090055410758800b5000e10903104c0e01e0342c400040c50b01c5010000e001000d03851b4903000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 871499127 1250 871497877 871497881
    0x70b040b0403080f090301230907180c031b0309030e0306060612130203030a0806040b120303011a1903020910080f0a090f0219060f09030510111b0601061101 69
    0x4030441010040402050000892660180c1580151104442e003407218840c0042d00703440c0b030f0302c1d441401481801e411200e0341d070900e141260008104006801130707508140c084e041c018804200c00b40c00b185c5039081c0f417404030f1090f80300c4489e101c1c40303c2c2600130031440004002e001d000d501106030001518185000c0040c0b40114059004040c0107000f03600d4640c07443e03078100707600c48020078420040c00611202401358501303000802c4071500e40c4e030343c69a06140103010071084620441c8010b01804074058007510f0108000704490542c1d420601100d0604030301c041000d6184584a2454000100b074041c11f0071964142c1c004c0d290b000000c40755540c64804d10282101c0300a002c40b421840d40c821030000c175001851a501c50000d05020f40e43c0145003180c682c0201708440000c003528003003003c1c14ac008100080d0b104081035900045450580f103901d01d1500d82c0c0c0e9540c40d0700302c0c400501968440d010034440b10b00c5402ca9540710461140e0a0601602804c0507861340300c2407160f81c01007440029051040394040c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 871500377 1250 871499127 871499129
    0x90b03010e06010e01020709020d090c06080402220e0313090c021207030305040f0813090b01050c030d0b0a030b1f14010c060b0a05211516050a0201020d061403070b04 73
    0x424807100681c0e40c60b00456855560070060341c19070050583c0031454010b103000800362801c0e202c03c0425800064600304140022540c820402c121409003448016620350440220307d4092003100800c0c51003175209140200f41000e0041010b100c006201d00100f00c028007020304031242e84c4020001ca000620007682c940e01c1007074103114001420059000007074043da03c00c030342280c0510482070042d1070701c0d42d80c4d003c1a40125a040162024810108900c015902603201d80c0c0c01c0038030b0083d091660818403175030342c0c0c0603801c011002943c5a152990180c0c84150104005607080b01c5030304560304100200800280280210307450300c118006000c6007681902c00b5500304042e06a40c5c5091182454460000520600c1803069000501d42030003d0141c0d02c0a440c02c10001c05907003d286840c0e0451049460031314130441c4000d4010785c400400c0204002105074580032400d42c20020340e2044151002c90080c80b40803811905146040008a4840340300c201843c002078055046070f60380e50b00c030b2004903014019 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 871501627 1250 871500377 871500389
    0x6040b010914010920030705071101030b1305040528060b010c030816030b03030a03150905010503070b340b070903080f090409021503040c0e04050c091314060601090b0301 75
    0x400b000402143c00c407507120203c012540b400603001100894102901d542c41559200300140b404a040b42c1400309800c1049031081c02428200694144030000c80c0d00000c10f02030900c00c0c0c5980e54002000e010003440441401240903003101100800f90f440d480c0d4500c141c00d02950700901d0015010815402205c074048810303059181c9000b00e40d140074503201d541149880610815480d5052007010f80c40802c0505110b2840340c0740420381e0000d0700d0b803251b8007407007a80c000107030b103401c200c0100102d85001c6107a40a0b03641d240b41c0c856541d03040c0100d00da180585019082507807040584a0502d406600070906003c5124a230020b0040e2a408000c641e0984140000740071401c0c20072868020303840c0d441c028102c00d0f9028101003001c5c03419400203481ea08803840707800c0c0c5054001041100704100803454001034520401c1d504031608040c6c680c0ea46c2c50a4a540e4a4068400100420a2010030140c41100640d0290800b91190321184400781c4645082d40e003180840c0d202000482c4d000e8525003581e0507590 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 871502877 1250 871501627 871501661
    0x10081803091509030109150204142202130e150114182107031b08190303090c211502041a09060c100903020c1f08041b0806040b0109 58
    0x18000c01c2d40d40d81c00f4110140e410741d0303176242280000304038650f0641124543c107001070f1100d1800d9032404940300c0107640c40e40700b220201004410720710241c0440c0c101607094040181c544d201402e24103445c903405c0e0015031044004c602000360300c9503103420030305520308281d071422900d0011f011181c10501408299000314003212644008a0a01110a1254200300d1411407640381d200d89602d81803100d180c101361403503540221020110590030250b03030010310726031008104c1110004088680452410342c01800c064442141c001130140c1045030802420418002e055031003658010b070491050b669508072540c01d000c0c01c4041700e00c1024400d440483e80c410b6a51150b000342c0e45110901d81d03200e039491079072102050202840002c010492018160380030301c0005481030441c00d000e481d00d020418035920454900c21980407042404803040035102090902c001607884510f060344483c0041070204424121002000554020000b00380c1c1c0240d00600e001c01060b600c0d080903406507032900c012602a21 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 871504127 1250 871502877 871502899
    0x8060903130609061e05190c02040c0507020102031c0b1c06200406110a06020c210f090405100b1603090f081e0102191205070e09011401050403021008180309 69
    0x81400c0307940c0800855a446d00c603141c440d00c0e10350704028100903414640081c3c140071901d011418248500d48101060303040840c207002207580000e6503845080c110800c45c4012402c80382c029101d070740109056140007003d0310381c41c2501d0b8000c40b413450001c442c292032a070308141d10307104c1d2305200310342906030131085421040c076044c1008000c1d01d502c0142410966984550780c0000d011412600c05840d06054942c090400f21038210b001107540502e072107000038a240200b0003901c03034604010031580035510644000c603003a40c6404002914411aa1082d001080d0001c3c03442480d007408260351064502c02d4980c842c24a03200d1104410694a5004034030440d48982c0503100103d4805501403c200040070000d8500910741050807017000350390b40d403035011544d0889001035108880c02017640c081da0758500054501182c5001400d012018410740a01d46a50b0087d541164070590448003d5500900f19440760301e5141e000600e00c06040703c00080704100c411040b4000240403045507100080146404011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 871505377 1250 871504127 871504157
    0x91005010326040509090106060f02030a0e10050d0e1609140a18050708070518090703020105031b0301080f0f0703050d080a2d0c0201140415060806090313060906 71
    0x316911800042ca0103400707000004281e900d942c005442025034800100e4501c1c6804006811b00300312800c00c80540d00140301081095900c411100004501150424501950f441c0b06903214440c42c0200364840342416480c0803105400541c6004034140413803030b006680d83d45d4a40004032004201440004100341c0d0129241101d1608400da0f00900740b1561100041541c1c0e800e45080c905d94406c1c0300c540c10280013080741e880c1808120600345080e403901d020b2845d040e800343e84c40396101e001c000c0c180080030020601c0244007884107a6024560940b0503aa0358440081d2981c070207a40d80d001c2124851420707140c05004001c03410350216a400030003451880c801010596107161700402c20840a5075500080c3c2c0c40c10304001c0442062009452034030040400340c00f001041c7c0b80d041000744156030424018040c88100c80340440e0380941c00240c0000d649604822820150440e03a104295a2040c6400c0c007a441c000880103040c40740707195411001403945e41e501034460300d5280c42104003051a90702d4030050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 871506627 1250 871505377 871505423
    0x30c06121f0506131a0316032403060e06011703160201030f02070f200f01080a231015050f0903010f060b0706050906040f02100207050a060302030910050103 69
    0x2003103112500400d0341d81c0c96a0100303040f5001825030104002120000300400c5408030040034040d503240340c44902d9840c02c8101c0c20084012000c400042613a141c84449d44450b41002c5507003148411201c5010850b56810f16601030072551150031030a0113804000904581c503140c0000d603041e04803025504003020071403810741112540c4070a90500d510740704241c03103003c0c4500c02404a10300c52110301c04240240c1c108849090103010030702020030403803020380c0129076501e9882d90f6a46000d19004845980392100a4040c000341c0c007500402d164100c030203807000c07116070943c80d10030302e40381560803c1c00b80d480d0400e0a0a501c85000382d404180100711240700c0483c1600106107840c005400450b208410f0250b8500b00c0f5100ea0003140882d1020480000f003145070b025054200f120b0500425180c103080d2280c403a60811020024803c0c181d00c0402c4201500901c41b100007050001d00210a0ba41c0d1114040c02961044907214101c0c01100340b15200300c00503109403416070f6044000451012001c415001e5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 871507877 1250 871506627 871506661
    0x9070801120f05030409020d0b030d05032202030a030f020d1b0212010e1c0e0103060b04061112030c0304110103090321020d020c01020d14132d030c02030c0612 70
    0x1d00c2030b0640702110007242c01000100006d001c0c1e4240141e403550f180480c50112002045a05e11035003240400860169100c13023600c2e007103207448206c0c490410052013040881703045110000d405000380301c0802c01b8542c200791004900180e50b029901c51100c1d002d02150803020521807540c4651200300e200000d42096075480803490450000004c0c4041080680c915180d800c200420445000440f102945541b14103200200c00c02801c3c1805001d0514218000e280070302d004400030011858200c210145080011001d000c010300b0015039a420b024410810302d034012202501c041c5040001c1d2203043d4032911031103c2c8160941e4400ca5083c072150000b100e5101d4100d601e07103d0607000d00102400150601c004d1881100180005913175a050712418400d454400000034a80104c0008010041e0f03584410a66a10f9010310802c00c410540c1c51140011011080e01c41078500341001d58108141c2c00000754650306008030308844c290205001080740910400d5200f40d00414410003140102d24000b070000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 871509127 1250 871507877 871507883
    0x50708070e06010521040837140f030c04030f06020d15150e0105190206190506010507060b0301060b0f12011a0a0e0f180a0501142803021f0e0907080112 67
    0x910b041c0f10b41c03c031002c42000c41a002000c980208c403070140011842c407404500f1130103504000d00c0420001c0c40b14445405101800c8a038001700000213075030341c4101d40c1110042c40d07104078480b4480c0359034180701000b0b42192448901c800e03d89000115011640006042194a510b01820030440040c070100c03950070301c4020060501005000420208000100c4071f052500b55038010001d602c0e0411070600900c0c01d201070002d1031850101404000c2c1d0f4030204480d141504110301088146030f40011074010401075000b00c0300c80b0008181c2c5903a4200080040c402015448059541130340c03241e080b0003100d8800308141c50034003010010208220f01442c0d46074000c820081054007030320008400300320700c1008a00d2101801c1c0c144800c00c00302c64010300c90740707014000b805d04495009213814081005900d09800c81c0c021000c110702c45840b074101c0c4001d04405554043c000780c40f43c000383c13091a911200b06103005c50124000c150034440d503062441b00740d4450b280a03500c84181c0d92034080c80c050300c512441415 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 871510377 1250 871509127 871509143
    0x10e160324020a02031e0c06010b07170301150210141f05151312021005030405010f0e010f0b09060901120201020a0f0803070e0607021503060d050708070e0601052104 73
    0x70464528030744040c1403208429000b440d56200a400b09004407010000003102d4250203011120249030300242d09819503000103007155a8648030304000c4008a40c8107044e0260410010021507452004400301618a8807502168203100107040440103031020b11001c3c0d40620031000c00284540010441708000c4070f102c800f040061529540882c6c887c0d141107004a0803170b034000803808181100190068018441100010745810090303000421035003089072184200304000c400704090280030352000c4030010111100b00402545048001c1c064801140e0101d9443d1030711242c00103604005402c54403c1100401c02011a801e142c5941030720302200c03030180d04511818041340b001034404009040c0301405205225182d1500100040001c800c03032180b140145000e110580050719017443d01c0c0d8000d8900f0003007035141d03901d400109880080301c0c4005021445203030340c0014040c80c04640081620f04007551508281c1c0c07520015240b0b440b501c49885041b80720020300019005400c01000d810074802c4c690307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 871511627 1250 871510377 871510433
    0x8010e070f05130506040305011d07081203181b310c0215100e0a06030803040210030b130f0b01022b030209060d140f07120e030403060c0809010e1603 66
    0x2c45c4840d00b150300101c500b84c0d51003c448203c00d410300c0c01040080d043c6030050044a00b4402d0701070b1245a0f80d06110340c03c40c03002c80030039400340a000052807030712081401c071000780000203241020142045d50302c5e8040c50441001c4206049a440800303010650380000031103021000400c10010301400d90b201046000340006c086080d0b24185009004a0f444810507400509028005020203406880304000750300c0d04804100241030b0505480e0311680444030604000c1410000360080c0c001d80b95203942c07007501e4900902d48600c0356405400c019407910b07801c1001d89000303c0103a03502e28072141200c00108512607059004010390030910007009641c076025007401c000f20040341c5103400c8030041c0720326107482d108130007400c05c210403004d40d00040d1001c0da000503040520018000c50700000c13030350b01c000c0d4a5080c0c3d4440003070208121801154440d00030000d85a1240006040d440d050b102c0103015401e203c1c410118603c000f4440c4225102000c003417600b5481c41e9a080d1110802d459880090540d12203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 871512877 1250 871511627 871511629
    0x150d03050f04081509010b0a030c140d140a140c1c080904050c0405042414041805070302030f0d0f0305090c120c270a090f140d08010e070f051305 64
    0x790590304d0035400709090503040680d010360030348050080903070040b16026020404114403100302d6080314200e019000c0d103608060f0115003100700b41d20000e40540103002c1c2d00302140300f00240c0c200e082805a0a20040c08110f980172684036080100101d80c0309820840407080c0c65091440312000034400c1c907643e80f6100070103020074103961049074005000740010030200250304281c012820818490521380d000e990360404200c000c9080c6015000d500c082003034141040d40c9407036002d10700804c120101400c685065180c00e0344e6803406800204c5c0a402054600040c02c00000384920038500d0311b44079201e10100f4803904400074400284601014850701d4440c80168442d640010f1030700d2103450203040c00850340014414000800c460001000c42e6000707000c01480380890b01035402083e140000700d400281800c0c681c1010011800140410a81041540244000050345000e0107281c2e00c50422681c2d030b40d5409000841c0c115031034004518250701a2440398454002040020015030242502c9600e6030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 871514127 1250 871512877 871512883
    0x31906150e090c01090e09060a0f150902041502031c0911120a05122b0207020918060c0306130e100608010204140d0c030b060f04050915150d03050f0408 67
    0xb81c0d03a0025600300a0495441e9644803820402400312608002c07501e043c0512050354810f0020001004c542d030b940688000000305070420084441c0021400c1c900c95142c1445400940c050700c04c041c80030f01b030154003090003070001c0259070380c028801c1c0180d01c8900e20300b9128409000b40600c122503082e001030f40120b241d680d0742c540c41d40c02e0807804000c2c00300701c0341c0e8a000e9180801d52402502c031400309010b9690410380d810900002500d0119290700b000039190586800303406000c0000f9841170611f01000180c44044190380468100d18085440035111080400000d22003076032819080440c5046807a00100103800070485c0b81410b104481a4540960105048801c0f5806c66a596500000c0801c9030f00206000d031030748280e08444904400701c0950310010302c1401c51000500480c48040002c100b65100c2940d90f0200c04040c20030b00940c03800503031701c42e124008a501d001c09502150081480180d0700e076110301c60f07500050401d540c44001c54806a6041c0c00c20b111410101e0000c10021800c04018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 871515377 1250 871514127 871514131
    0x402070303020a020106060801080d05130f0605250f2415080c0604062003091c0203012f070503130306060f12030f2f0714031906150e 59
    0x30380d0700141c48100e840d070020309460f910b900001c10880e01c000180001103000c10420420180c03810303c4c9a5030543d0791011881c18400c0ea10a5404440c1d20200052058105000f415507602c11034036074061592003090314410300400c0001a00c0000c0418081000600302c4000d1418000307052400054405a400341030700b6208400071140c1070500074841080402c1082140790b1402c50700325445400c02d0b0920a0003419580540320480410700d00c1509206107400500440780d40d000041c01008050448814019140c1c3e00907008078080d40c6409600c4580f884071040d885400341d50421000d200400030280c0c4051500b10000030360710350104001e0300c04420012280000114071501c4003180540c64006000d503484140e178420400010303510091800030b540300c00c000c80324803801d040240c0e201110703520b2880d0000c5120003810106000c02504202c402000849604980c0815248011801c0210615403505a900c0c0000c0c00201079042c40c100040300340d0407406080ca034803008200324a6540c5e00341d030348028007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 871516627 1250 871515377 871515383
    0x2a0d2006010b04080106091806090c0b0d1d0307030903030e0117040f0501051303020a02011409040207140d0905061e0f03240f0315100b1206032404080c0c040207 71
    0xf003c000c1481c0c20f008410082803504420415005180e210032a80c420fa01c0000301010340d02c00c207040400100e103128a0141c02d0582c1440e82340c0011288140080a0f82e54141d4820301464480d061154000022178034078039031566031400305519556041e1000c41142c20309a0501c180c058144a91030b6042d040c941c403940c02100300300341c050400d051088c2121000b810091342c0510071036181e804240c001514801481d07081c82c0000c00902800b40003040c50081583c8194054000034505003800841406a0b030030403401c3c0c0540d04100d03000082a01d0084041c480c550f080716052000c0005128030f405082c002c0d01d04654000c0c40c10310070380508469171b03204445403141c131401c1c1d900c00361003400c0782c00055000c1c1c9016180341d0060214400001d940310148038000d441e45003c800040c18080d0340b003480d4030051052041080d02c0300740d615070a80f1a0001152080c0c001d00c01c03130400d0007050121030040c2c0050880b102d112134060b152a164900c507584042d40d0f1410307520840e1b50010844e105e07840185030884c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 871517877 1250 871516627 871516649
    0x30d090606082a0a2102040617011d0303100e15331201030f0609050d0f172719030503070815100c06061a2a0d200601 52
    0x35048488481e1140d200240c0522110881803001c54200a080c0070b88003548845c2e0211a692440010054203554103c51541602980c940301481c0054101d0040300900e2008240d13000c0d28400c4440c3c0c0c030700003201d50050715504000c041110401d1501c490b0b810440307440701e5582d080c0285001c00e600c2c105030000d000c1c5282c840c0d016090b516000c928192894400401054a0140c40d00c88210001e072040c00013428018194081204012143c3d01514641e07a1041c00d803080c03030300c002e00090300e01002105040081172080c0071800d80c90100c090018800c440c45d21400041e5a002c1d00d601c9055204c44144040e0761007090b0030001c0011240c080240154402d5031015584d2500c0c2c80020316042019102c03c0545110721112270065442da003880c98090340520300f600d80d82c842c600f81032015045961001c004e519070300306240c12130094280100401444000e603900404c41103180181e0342d0000e044605090381003107c8081289224444402c0000c0403011014a9180c6d664011801d02c4004e9025042c440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 871519127 1250 871517877 871517923
    0xd061a032502100b041401170d03020405030c0906032b0f030506030a03110f01050c0a1202070209150a0e0f06010315031e03090b13050109050102010902030309040b060f0d0902041409030d09060608 86
    0x1e01c081210349c006202516080d810075280c1070100350b031140c13449400f0703110b0b0a4500000e58691070801009440c0c003d99802c02404003040707101d404030408040c00d403000044030329000bc0c00041c0030b4000d0600500016004010300d00f9a0b85044855a85031840400a4040c1461440c1d1803402409071a01a9180c09404c654501c0c03e403002034a1000341d030801c82d002c90b0043c002800940d0b1542c11442d030103c50301008845502c0ba0600090030480079400040980601c907040c4070a200071201041d01ca0103082c1c0301049001107981900842c1c12943c800209403004801d54040100c00000030401864400d01340100e020b5210283c8111941250528480b051000001041030b582d1110548000300000e00082140c030700c454001c42d880e8480d41401e00d0055403519442030843d260642240c005044442000d03466141056081001e030850b54001d80c8038270300300601c540b2900076a03a020b600a8031440019490400e1566021002c0c01611800340c54269a44000007103140e0140300c0d4610012148280355114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 871520377 1250 871519127 871519169
    0x10221031b190306170a1112031309061202150d150e0411012f0a0b010803040314060609040f050a0b0106020c15041202060d061a032502100b041401 65
    0x1c65840e80501c1c807124145e50391400d00400404c081011903009038820f0298004600402c4084504241107030407844000349000142d4070030042a429181403410521205540d031600c50707100043c3d00030180d408200441202c02c1a1800d00040002e1003501c1030201e444908074451f681d509085a2200544100010410041000000700d140038402d003420280b80d16043e8a0280c1e00591103111099001c100348101c000c41207a040000d80c4103a0f5002102e840706e0340c7c40700c00ca26201d03005440225002030b28403880400c0d1210100311203114440103812401d0f123a80316100c3c03c0914844c0041038419004005040001c02c24059400c1c0c00380080713070000c000c0d160300c0c2c50621a10020000c00c0d100300f050180024000d0110080100d40c0d4590110313241a00c81c41201c540f00b000780426445030003901110011002c2c01c101840203548910150303140d03155540503100c080308048850200510060b08040340071400c004d100c0e805060540382c0900002444115204c29144c0f1b07101c02e0f0080b03c400001c0c80151420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 871521627 1250 871520377 871520381
    0x20a090203060f0d0b0a0b12030307090602100e030d0b060c06161404120b1905090a030f0206060d06020d060509040f050c010c080a0c080d0c030e010605010221031b1903 74
    0x3e0394103840d12441e0400646458200140241c5250340b1951101008103159561042000150201c0400c0c0c0c0d80d281003196000e080091144280c2015020701000c800503c102c0d4864828400b070080d01031440c00080c00301c030800038030321306000940c031220078080030305049400c0241c41c0c4211800328112a12801012011b00320a000a2150b44280307002c01041c00020f044104002c5074035884007400d2180c1d241ca50100321007090700c0714100c411514200410200c0300b000110202100d00940354600d11914005d0100e881e00e070102e84071134010300b100b82c2000000300ba0764001c26420390700b4900000d8150321000042d0341442d0586060700c255259450031018006c0510080706014800d00f08030110f045581d44500701409880801818000f403000a0300c14454584225003c00c0c1d8040d408200802217001c002d0000c0000b00c485264075841d0190100307865000107030301c6042158088200340c1c411510031000d0b5195000038114141149468400c4880c010242c0182501c42c1c00021b040050001f51a0001c00f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 871522877 1250 871521627 871521649
    0x1b110901050a051c021f0e13091a07050d090305030604060e06010804030f0315080a030807030b0d0f0206090406060908010e1f1503020303130801060f0311010503040c03020a09020306 80
    0x4071907801c050b8104515500e59841410103901c80c6541d6000c1e14071400040d8003008225085130360900030010522a01da13010301d8002c04110110f445000118800191008a403040e500c0244042d000d140070711098010100c802d40c0c86056460310501e400c07117081b1260103449030072104a011440100a03c042494a801402c0c0a462107400741881c51608a000030803805014101509001c0c0303220950000610036000154140954544040560303038a0304510344d120002d002c10340005c2d4841012980c1c10313201c0e01800da6070b000010000344081407152140510300d0140007080361f112408001d0b0300125215800307044010811074484c03426a910f000c02c2942520300e41060034100c6c3e0031a00c925000e88078484c0c4210702c105080a00011904500c080c00340100000740c00180d491b100119845500a640181071010380782500d00030f02c41e941e698000f404a80215000c0148208010408141654420809940c1c000e0291b11185080c5a80b900401c03d0402070780c0018900c00e80000401c0820b04264800c49 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 871524127 1250 871522877 871522879
    0x90812160209070314180606010c0203070b0c2103040c0b070b01031103031e0307020f160501082502100c0f0801380307020c0d08040b0a1b11090105 65
    0x54603201114245140c00c00c06288024821000d140110b1242840f07640522450150004807800c0ba0916642c001e014038402071041a1501c1040d0000b6030340d502c80c0340300c811245d034050700a044c59410501d50803016081030201c0c01651051107120202d001e000f8002a901d903400310b200560340e00b06070400220450403600410141001040300340000744c4594103903411aa00b10328010489404400040d04501c641454441411451500b03842d100440b04015130003513a45808445103c14034001440e2100322800100181301a00d0000708220350040341c25581c8588050b40d10300c020040808046901941003a03043c0c011b0f40300c9102d041940c01c9611070000811a5410000710003030300f41038020504001401a210b044000b01880c10f442030031030030426a4803ca641c0341011602081341407076107d41041340c0c440c0052240208803521070a2084007080100d800c218414a000d06010007440315610819051003003103105c030850701500c000b4007000303070549210301e59100c0c5035210101088a03400040c0c00c95 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 871525377 1250 871524127 871524163
    0x21504030e04020d02070206180a140915030109050f0a060f020f07060c482d082206140a080603070519060201180c030b15060a0908 58
    0x100000c40c1c1c100414000d4600304407009030791844403100d014041c0c000c0e10750003500440003054803a242040341c000b40420300c805030b038601c2e140e82c3e030754401d0a942a04a40c0182c0c2010031200428034071181c0d800e95421043d4017070300101360100141d07100b500e02141508081c501d504072032043d40820090780204654150703469429420050183d420210605c680701000b80880e40e103071a011500380c0500c1c10800e2221061140041d5411048418090300300b600320f921101c15803240e0800d84a9a0703041e084030305903070813541703c000a01d02140c0c0d802d0f9181101c01540c0c0c6040041d0310240003c2ca42c1802801112800207000d0401e880b549280310040410b81c0142040c00101103801d505420036105580c0000a41d01d0140000d0310390801080c20700c05a034104135005840014251004075886044004031030895000b000121f40340380602c0d406aa810f48014000401061b040020a0f120b80c80700e43c101603010030408007074034085c000401c1540003107110804940c0d14041041881e01c103014280700c003607601c1d00c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 871526627 1250 871525377 871525381
    0x120506040b09160c0c0902071407060f05130b0706020904140402280f06030209100e15093d0c0506010918140319031e0c0c02090f070215 60
    0x94840c2000800b114006008250034070f41c240e00c0b070503084a68681100540740520703102c1c0d01e82e41c00b9501c0101c4c00e4a01d21651041925264000100c2c0d40485005940705841210043e80444640e4442000040e00300b0420300041540c0d0451002450820b20907580160f444c00c2800a02040d110012500e8549207205410031000da125a65070002001c3e8640009030300f5544403840b80c0c201712071500401e44075002c0c0d42d000f086050b0150700070241d482e421921404551020f610890f40d42107244010754200405030360030000341c80d00c3c2c40503206002000700030000980e04a140509501c0046a0944c289407030345101e0070070840e0309015450110780510f84000d002d0655121282d880741c1c18821081142c0d61105505808407417a1100d00340664007c03031552495080004281c1d0700c3c2c0190240002c1d0014038040707100380b54002e01c16880d4000c5c0b070031414181031200b01c680c0340040950315040028019580014001680c521012900c10600790442c1682800c00140082c9000c490100b501d0100c200042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 871527877 1250 871526627 871526629
    0x130b032d07090e1f0e1f0b070303091104050f1501020309210a0b0f040b1018090c090905101409070312020319020c040e190f0c0b03010303120506040b 66
    0x880d0206842005400b03850f2a100c40701e401c80b140410303e00d003284807122180080f074104c41c80b0321030754020801c10309480080c0000000c0b4400c001445c4c41102c0000741d00b00202c03c006802900110f90050140c05000d038034418000100d8261801182c80a40c006241405c018003c500f11400f20500b681c20b10007541003d5841001c11031034420210038200c54440c25110745d8900d10104005240154022034103102c600300406a0014120150340c00c80320303801c41c200016207802c0710340d112908444001440a08104000c280080106419131003595034006200700820440b2190042c003140364464001000640300c42d043c42011102803050798000c15011a051044800001a10000781d03a0848201c54070400b042509a117507120b1580d0740c0845511041107a40400d40225070030741c0c0d0020503070b801e10050020303010060b1510103080703900f034070039034541e03580c02c0070502100308140c8091294050313002c4241c0f01c0c1c800ca0207a030001d070700c00c400007a10400500d10040c07280c01550380001040c0c42c00e0041c0402c1c04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 871529127 1250 871527877 871527887
    0x170c13180c031a130e240901050f070507170408031b07050604031205040306110c0f120d0c02030d0e010c121103070c020102010906050108011a03071505130b032d07 72
    0x7440078440c150b13001c402c03844040e082c1d00002004041000f1a061a0080859600c5500361003c80a0240b130284001509041d41030050b98850406807500030110f60341c440003038403641c1051100703480807200c0702d07188a400c00307850000704054185c200096850344207800b0294034203400d0038542d000980264904109548510041d03506a0741c2c00400210b1581800c03008a41c00e019651000e45041d0074044070a03a25124000146007240002055178a02500340058035500c980080b61a0200d440070407400307002c10315039445a0444481441a01d00c1c0c207510001002c06d54000038181e90711a55250302d03100d0a540c004520210b510010b1005004028803042c41c5616400700801c20010301450080032400c5a100b9881003a026901040c100210b50f150300007175000340700c81d0444804500c0004903040300d82c600054101c1c00c40e01c1c032001c050b04100e10000225115000402000c0a02d4161000801c50403124805180b0518031a6111500c2c0c6400140305504401003500101207a2142030030b0100c1141c0c01703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 871530377 1250 871529127 871529171
    0x7020103020c030f0a09030c0503010c0e2803080406090807080c010e012006010510031a0d0311060106020d030501090908030403210f02070b06060406170c13180c03 72
    0x9003001600c034415000315a06512800c0e030030607a03003600003801c0198150410340381c0c41070300d0082814469107030710b44084c142200c1e05000c121011403048490500c0f545003c000b400c0a406521441001103c50700d000d1300201300403038000b01c48000000c00d00340b00e5142d00c00c113510300501828000b065810724044440b6190400465160f0400038140d100201e585d02841000ca51035a0682d495000078003024401602d9a0081c01420b00c9402d0103841340501074480c0c0a0049010a000040e4188080c4502040004070300301400b1000e012000031008034201c02400007038002e095a4000c0c1801002404009003103490580001c804245801210380c080360700c140c01c3d40da02c2541800e15511010030740284c0c8400c4000010806c0046040c01e47e904080031154001d00000e40c402d038440700441d100c240402c64640070318015200020080d40901d51804030b0548015000014241d40516000300720a10b1003085c40c0c581c00854000140c0782c11591441d41c00d100d0411056140e180030880c445501546142406135 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 871531627 1250 871530377 871530379
    0x303050a06050904061d03090f19030204020f1305090c2215020d0215013c0e181b060a030e010f14130b01090507020c04050103081e09060702 62
    0x1584000a4445210754401c0014010040c6407101034079151911002920140901c0004224030301c0d00390801010001c1603452194000700581d41e000040414040b16000c480340f0290f078681e1409000001d0b807180e100070100604414912030341c8080c03046003d18040e2003548800e025101050410001405000c182c882c14081c1d100030646585040580d034810001d00e801a180500e1199420130341c03650001510180350003641c0a9501252482d8542d02c0a81024403549214030f103025000b80d85406c07020700712074000b051800d01880c490310f0f400340b41048100341e81050620030644400d201042c202c807500c05c410500b2a1008280848640090041003007a00f6155400b0350000706005400701e0094014202946034131008000c2a443d2101003806041d1906040c400030321040082146001a075840c1600c16400c00a80640c03a441c00c1038000041100030035060841c02403100c03220941d40c030f5004403802540035aa0440e2640d05003880b00362040c7c407051482004d000200108560b40d143c90b41540c0c200d6030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 871532877 1250 871531627 871531631
    0x1b0c02030c100c020907090801061703040608040314030903030403030e0a1a130f0503040509010503030703090501050702010306171b01110c12011b11010b0904020d020f150a020a0623040303 83
    0x40b2400d44244100c3c3d0002940700c03041000b04912180d0225215084501000003484120340d10110f005c10304a0101c4840d102d40c108100038092580541b045c260003910030f00e400e082400303070781c420b21074150003e80d071010b6076030000814070041c075030716009600c1c04200b51009895140074035aa61140341031350005010315141403070006042d401e200c0d1440300803681c101e0491a508034030b078545075840c0c1d4003900070188101d4000c0c001044031b040c000151643c05501d034882c030051a040030019510354010b22412410540c907840040340898802400702c0d01e101d4510300405142c1142086000501031a486403410094108400500c8400024240403024010b5842c81801c2e141c80700518050240540003100380d100300044001e103154041d01d40300129030324070f0082082e018070b0010804031034410398000c1d5000480c100010301524014415407030244008010600c460030748403420030250000014140581c00a04100040c0b041601903c100c0302500a140e1085600e214005110b02e4005030019041503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 871534127 1250 871532877 871532899
    0x4050c070b04031209050609060f01050303070605090a081b010501090b03031e07060504030c12031406010e01020c190f0f030c0317120103081909050108061309060507031b0c02030c 79
    0x1d8007401d0f004c0300784212140c083c48000001d0078200c2d566801641c62101c00e201d900c000500f00740410700a14141d80c0300a007d18035181c0703140c860740042e05019016400034050071646000050220006090307403420000921103100395518070303e0131540c0c145d210700392060400440804c2640c002c03048031528040a1021103040d00c846800070b07150f004900000b04000d24180501040c076030804961142e4078400c1e0740380c0c40c141082d07440c11410b031508a1400113082c403240f400310b0b80c0b0303600500c0d02549200703041c4120340c0104a0000002c00d2069151500244c0705a603000900c0140780c0c05640201500407001207800305807550b40c402150b441c0500c00600124807000b500b0b0740281008080f0350b15140d040900d02d1081d6144d08001040d030703018400c1541c0c5a01c40c141801d075500e0040070328a080b640145c4419115540c0d138810310144490555810902c00d603500c90000002d1487c0c17041c54040c8030a0b80c1d0004072030343c41e5a900d11030442c2c203603802014000b1200e00a40165000528002c07031030010342d1251808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 871535377 1250 871534127 871534133
    0x9100e010605040e15011e060305040305160c21081603050408070303121406030d0e03010e03160c0506071709060705030c010c030b041103010b0705190c060e04050c070b04 75
    0x1405540c0116a10a080c4140c9420001c40040c56074600f02c545d200200d6142d84e242d14490002d0303982e140e45490103013050020805036009034869940140a410300354070341240074904501190f582c20b0300f00c40e070805103802813140c113541700e5014845010021107640c40385090380b43c9000034000c0784590100d00c014070001d03004062250080c1e40080030f007002114003040d100d24010700900300054103d0062441c3c1484040d0031181c502420f400307000c0281c090611000700100c102d44088800961913059901c40d2030000c0408020402040c000307070154610052001245040950200b240d0700562081d41c09000c0c1070049207400c0000500307201c0489401c0d66813a80b00300403132102e00a6a4000d0700b00d01010520000c40300040d00401c40c1922195000c008800d141410001140d03034206503109040d4050005003c0001604000c14443e80550121910b0801100345079581c10200c941c11079a051185204009071508140c0000c1d03d10400c8805001614014031400c0c1c140c0200e15001d000303103c020303000c9828 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 871536627 1250 871535377 871535381
    0x90306010b091f05120a09020d06051b070b16030501080319091505030a0b0a120311102a0807050708090f1005070b060906181506190e01030509100e01 66
    0x4600000f8081070804000f200c064050b4000382c540400031440200001c422403a0b82c810700c44500d600038654031181c0465103900b80102001421901c0400003015402280741c81c240c0a029818422051859a49085944641000300c200b6400f802d2504090040c4510324011061b11400601002501580c18182c402207a00980c2a070020800241c03801c48041e000d54403034001c3d8840c0900000c2400180511000d100c018a000d2042090640da2800001300080c421194a600e40c0000001c4540c2000c60950315001c03248241000c201d48280c0d01480711604818014901425115092000980c9488880501030703104080004091002c0080d02a40d10741e60240311203148500a04416400010315070050055840303244140c0c0d21500c18000140d0b1882d04421540c4148009454807140d10710841c6440860039001e04441041400215500300507200c010103030540d862101440e101400054001402003168000501d04250920342001001034001901c0c2c07107400e03c10800001c1c031407150a4501c2c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 871537877 1250 871536627 871536649
    0x90b0610020c0415050108060a06080703110903060108060403120c090e0603030712050a1409030d0e15030412080601020d0e130e010e1c18050d1e06050708010b090306010b09 76
    0x54070a281411380d440c140e00d0588402c0942d80d0a88a0103400d41701c03801007080101c690321440c0000f410010014081900c2504210400b00da03034104a401c01001200090500c2c2d4240c105941552041081209055001c020403031070f8500c0c1e190400203d0360017000280a0b4826000d416101c40c610800b00351103031000c200700c610007078101c9001700f0890510880202158843c1d40c0c8880042d071a09010070b52303204010219025000010300030038403c02685400c3e14014100700304103611240306400030100b1060742c0000c510607481460040501c00388070300094007110000e8042811544034102c0ba80750140c01c03140b8622400e10840d1010501060310300c1460181160801060465080c00d00002d26800000f403030250827000c0b81d400141400c810f2108540b5681641c821001c010000b100030845818040c000010050284c900031000d20820001c0703409c00304201c0c5040342d02e01c0d0780301d080082c603d40c0400058058041182003d18040c180d2001903070f2000d041c0503a400c2c9201c0041c1d00381c2d00e0765070300f04811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 871539127 1250 871537877 871537879
    0x60a0b01052701080c0408150c0f04080106050916020607031d0a03081006050c03070311030f1b120316120b090f070806010e0112020d0b040e0f0709090b0610020c 71
    0xb40001d584041032400d007009400d103081c003050500000c05d0401d0a48000d4909844803840180f10310b00380c94412010300c40d4050103000242c5000c000d190707060585d890040016221940c00440c00501d444140010008020060240d41c24143c0740450a16400300749035030024518a804260f01d168151500c1003001440306600c2c15120784d00e80c000030140c01a080d42c1c0305144a40d506103603140e03900b500ba9014801c042075004c0e503800801c0000d0009001e101d6030f081c010036020440742828000c068480550740002034a4a00303c40d22081801200420007a0449504010703495a017903040000281d030318903002419034005c1c0401c0c0030007407000b409180c1c010340010074018440e018506201e400c0f00c40000007502c0d40800a24110000350103540600781c403103880792042e036800782501c20700c00d9150b000350010107841c49080e0b118041c070710041d80c8901a5013401c21009010b40011546060700e649030180e150700c9000d8403418280140041161189460f51000003520700c1c04034106040012401c0038480c49030b41d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 871540377 1250 871539127 871539157
    0xf0603010f08010e0a05060103140a06052401020a05030d1109060307350c0c030903011b030c080408030c21040b070905010806150d060810022109060a0b0105 69
    0x740030082400048110341041000b004907400107032032183c0b01e141c45070f0050034a500c42001040091501c04044100345170381070036290301000d29034030300040c0c03030040d150b50080020601c0100743c008642660707542040c800340010070408841c0d90b6106d890f40540c2414014441d919602402d444503441d04950315060000d012907507910b010b642c00b4007000000e0840c1ca0051918101b440b0a0490031900078203010207072840a02d079651400c003100c14542c00f2007450f4805000030b000c40481ca440c24010000006d40b0045062200b10942c2e034001c0031524043c42c0a41000704850038400420010380440743c018041d0702c2c82550b13440446880600d050003407401c0412400d191002c10007840080d01815000e00c3c076541e11541e0040d0356600444014000b603c615620149a6501c0e184a81d507001c01800c10910010300440c1c401e80d00c901407814034000d800681d02041c2c00103801c96401d0b41072036421025100304e22070140c103424000400c41d81c468005100d82d5035259104d05030a1280c3c082d0f01942d581c0b0b00241c0301 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 871541627 1250 871540377 871540379
    0x11205120903010f24320a0527072a2a0911040b1b010b0d06020d0b0102010c050d23041b0515070215090402040f140109030308070e0f060301 62
    0x138040d842c425048000741c00780c0c0040404107000000c0b2400e5009441c402d280c1d51103c0c4a4885038a4081c1165a44140c7c0035840400c00100d94542c40030b0000805c0e840c9004801c0c1522220422020030070080079841041420900c0600801000390b000e8042804110128402d10302842c049070b450300c0019031031400701ca07500100b02076080315500b0502901c40b1700e101400890302c4d119a4035101d000d01d0050030000301c014414940340d503c5107007aa180e201e4000c400819951004008102d08400302c9070142d444d241c0000c2c800409082c503003d80312950800f07100800959080303800003450740c018035031040da40a85400c40724041c030344d01006070f46000d24140c0c000004c84c00d11b4a0b000420b00100308500c0942444004c0018552034102c444613000520041081e1410341c02e0307800c01001690408244003038140a02243ca100d03100da10140000d040c00e0600e804090742450070b114690b0102c009000c0c10400c0c10b079001d00c00a644462980c0d003004080c1002c0f1521502040000c1c0c40c40d9460341c00527003055001c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 871542877 1250 871541627 871541651
    0x17010914060a0c0203030402011b02040605091801180503040e0903190306140907140c190b090f0f0304030b0703180b19050c070f0201020f0105010815011205120903010f 74
    0x1948034090000301c0402c210316540c080f0103070780701d00003118040e02161185103911140c004101056019600c01040062040e850f80002203007210241c0340c0c0ba0b140d191a000f0340003160400d102d0701c001c8112049003e05a07080540d6a181c0d2841540a425070010509005c01c0e043e1808009441d6142c20101600b2071105845100400620140c403603514010201140081e042c01c11300149070003001c003039407a86520350300c1c610508601c2d80081b003100402d1245070890315841e10020102000369100712103826030742c106041030514050040c400c9500d141c1110348080c54400c4000300302c40031a40e10501c000e41302da881c100150018514142120141c0c5490111001001800e81540303202e00b00da155450403420150460a046401c00c6408110b6201d08011140104400016100e01d4078414170441d01380c0a00c05141d00e0030750304280d008901d01e621554248507241251640903016204070203040c0c5d007205854131040d03905c1c0385007810810140740c0080c1150321500d080d00261801c0c000b0340c009000c5d10035000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 871544127 1250 871542877 871542883
    0x140c0f06040209071b060b03070801090b0f071403270307030f0305090703020a21020d0602040302010e1818210d0605060a0c1502040918210917010914 66
    0x120101e108400d000b000601160040017000314259021100e0915860107607103440081480348942a4144110200054941c13000d008234500248105441c1015007032140c240f503000740340039089006000d056035050740244420350640b03902024000c5103010800f100c01d850808840241c3c20142d16000c0002d010b824950006501c1c2007010343c0c0c0d9410007499852034502074032440f4601009521440380710041010b10034041c6100e0380c070030f031118105a220481e640010f01c1c620b003e1030300711181a000705082055681080344426003030820399086405d0f00081425030300001c001807015007120190b841c610b40e21300d0104134500302640840c82d10028102c0d4081c0401075070b0003102d070b8440480c3c240b10000c500c90600905540b48000d041d00c407140414407691b5940300750018000b00e80c61860713080c440040c803030700c683c050041000100101041a000141401c80700114074046803900b400c000340d81c4109441c0d1001c59031049400760350032181c203262880d12076070243c40c250402411801c11070f143e0050102d404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 871545377 1250 871544127 871544131
    0x3030806030f06010501140d110301120302012403060507020f01020a0201061e06020312090a050a06051603060522020708030f090607030c02060c0c0102120103080901090909050706140c0f06 83
    0x40301180e407030952601a0300d64802d0f003401024001101481041e0707009010101814a84240b09408107107000c038050301d403800360026440041e110f48000c0284091540a02c00d03010140c3e00c500045d440503526020b1440300d5060742c8001800c7c0c503568000500083e20901c064050a0703203440007590364800107080240602440d014241c68a0b50945804c80c0c6100103059040884040e50045c42c100017014810505a00d001041543c0b140a001800f000151041c0f090f11031540c49845c00040c0c50501c14684150120b009e20b19905251a1900034403c13541e0384044e89050606d050411075401c03401c1c4c07041d00007902840b00c000303000e580d000c01440300d8035103595600c501c9240041c0c204d0b1840d988a103012821384802034248405a0840004645d102c2c81801c0100111102600003500e400095040030203030381c100341e01c250780d14100403504c40c03030301d690045039800105880e640c14818425a42c455030303280c1c05180f29010911aa10069480c29541c40003540c0c1c070415084299034a85001c42901500d030001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 871546627 1250 871545377 871545379
    0x60f1e041a040e030705190c1502070e01080610051e0d06020c190f020904020d0f050d02010c0302040503060c03060a0b0c0f01051e1b04091122050105120402041503030806 75
    0x82c220303c0801558000140c400054002d00140307903801501d0081440c0044612041d100007199090100b4506110108040704540d5580185900341ca40b0224001440301030300800d03203e8100f5018800745000c1e541c070350410340c0c408070390005880e0791203072038100500b17030000c200c0d9000901d0000740c006100b2250702404827083c16005070b50660a43c00e1007960302409400004210302101801a80075041800c0c130240e00034800303002d5013036501c03c58640c14690110740c041102c3d95030045620094040e4203008844007590981001c0d81003909000c0002d490300300080810903e2080800000c40c6030b9109890741d0001c0c0074800d40c080c0d559552461168491540007104480c1e9800d0401040000750f031508515080f10422524060944452800a480030082c41ca1080700030350a00000c0340c55075040c0b26429100724001e0703640d9902d070a03410002d000c071000604038900c1d2440440c2c0421035a40c001084500131040e603015070074582c0e15440002c0040888030f138014403041c560b2001004040c1c10180060150300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 871547877 1250 871546627 871546631
    0x1b202805060703110418090206030a0e162d051503070215010e0c031e070e090105240307030603081812060c04090c020c03010e0303071403060f1e041a04 67
    0x3403840b000707070241c0e41d6451100301c410104220402804944e941a01c6076840c007004049400c4845400090154200b921130610700e40d903914440c0b041010801542407144000840391450714541001080c62152000840750480280c181d2038140343c0050b500d910103400020032105c4c01203490a00d00040340c20407141280903114903002001d40c000202d02c024101e550408043c015552034406080050300701130716441e03000c6280d012008006e800455664410000e5544000720a07802400304100c180041e130025000310311841108501c0c500b99a0080108501b183d100c0e175803500d039408203c1c0140506d60000d85001c2001ca4842c0c50f80354400326016945404507505a42d8034080b40e8455200e800540d2001a0450200410441c04030b440d048250a01618010740b001c0d80d2059011900f51900e040301d10016800c00030821404507004a100c9100c00d0000800c0d41c21494200042031054138009601c1c1d1043c0c45440510100208581302e400209401800030b002c1420903150401c440e02980203190f2041f8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 871549127 1250 871547877 871547881
    0x6030b0912071403091f031a03070302040c1709060613021207030c050705100c0f09031a061f0201050402040c0c08040e0a0603080304151b20280506 65
    0x4000050492050081c41c114245407075125518200e810700d040d00f05102d213000a00107914142c0e540800c1c0d4400315010412404008010b5000a0890b540415120444240c40c1131244050320000390300000e0b03e0341650300003400075960740180e4404c088a891494403951031400c22080b0000400c0e46d60003030304191450701205101c21303540c0082c0d00032035881c000116139090010710702d1031081d0048080d45800e4103141c0d14014640d104c40341014041801c3c40111078035908429401035208149045c035107050f25100c1c54280c00c6940b030840d107142c142e0301030f01100c0964000ca500da55903100c540d000158000ba030307030b8800821460080c1c00380104035020782c8914a07146a800f20b080c003860310115080d5000302d01c0b034542810640710f080400406485071007501c0d0b40700d10100c0001e111500860041e07015003403500c11b07950419004030a550301280340b6030442d0382040345c902c0d00f182c01180300c2c81041030000d090040009400c600e81e01d0204500780c00c80b0244880000003090405112111005d640038030241e0f02c941e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 871550377 1250 871549127 871549141
    0x30834030c23060a0f0209060c07050a120f03050d020d061d0c03070e040509150f0103110a18020d09050732060703050a050702090403080603061302010f0309050a051006030b 76
    0x25808a003892030540d00300c840065100c5044d0352049943c40e1995200500306595840852038a03000361a40e1300140e404040240a249041401c100060182c0e1100c0060307601d0543c0c4405003202819401020b101001c40c1541e8a2503941e01518000781503035104002141e0741c0c00c04c0501852003440c02a401101150100701d820030304208a80c0300d200b4030349402c96039045000c02d000c028003005052480c0ca0040880c3d03a4101c2d50b00400310b6009a030301d1038041c2c0403941141454019132a003c40102d01c00d0240710800c12880c1c1104625040c0c00380010710050f100d40300c034840748000e40510200108540110603010a010344040d03190541024840c6610710185985604500481c0b2001451940500140194000688103200420131040f55192450401440780c0c00b15050460980c0d044001c1440c0401b00509418100501c55100200100b0780762000c480342c0021f0711030510358500b4030426440d048070f83c090200421400c424075502004a44100d540c8801100040c4811301044a0600a01004c00c4070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 871551627 1250 871550377 871550423
    0x4112502010503150316090615090602070506031306050c04091d0a08090d1205190206070905190b0f13050904151a0d0c05040605010306030834030c 65
    0x12156060712240c0c6140c0341d618040410500c40c400c460380c14801e400103040d110302c0d00b586500060011060125602d414034114070300740c0c1d401028080401644500070800d0590001c0e450084600940c0c046503170b9154446241d07200800c078040640b030796003000709020610400303000520403594000c6c020012030350390702501201c09031540c000354201c1d8000b200c4100030481c010010050341d440240120319815080c0d03035406078040b1482403140811404501d001110b01d80c0d2502e0345840c007261000c0c1800c4e00e41104007809004580c00741a0040c0c81030407000c440342001801c400c0180040005c06511010079800313076580d50340100f0141404c070a116100240c0c40c200454114011030b401182d000650301d1610079040108840144052a60094103952400392182100da914081c090a10b0041090510050100340d686a81c801c90405107000810804199110f096850f283c00044400c1005276074896400c4c0011000160282c0100e001c4112004268205600c096030f9441040300d80754444140c1107201d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 871552877 1250 871551627 871551697
    0x20a1e0506010b0c160e06090106321c060f082e140c0705121306121b0507051603080d020a170108010603060b060306010c0f0c050411 59
    0x81a41d008400501903241e844000d00700903940c0004039648200004841c8120030310b981e02c140d03001040c4006102c8a81000104580500014208010008a4000343c4080882030440c1070b410840444035090076803848004032942004d076030b030300d003540b040442c2c0d03040c3e00800b0070340f007034941207001d100c070005543c08003144025641142c0078a420859890500031b8003071820301060712007100d545509090f44007050380300c460b01031460580a50f40301c10613454107070701e009020410228428418003502500004030403c05055680c2840c0581d0042c01603901500604000c00d2410060280001c40c40d2240e0740c0100641541c9000e0012550b06284160031a00414034a00001d440303c0000c0011011010031a0001c0c9604c10440c40c10504c143c02000840d00c03102c5086c1c200b602603944820042007404a1401840440f40e0121130203071850424500103000359860700c034002c1c40741040a919200703000e400c203002001448064024012803810b160100200c0d40030b0001003800c0c074000a131500c00e89401010b404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 871554127 1250 871552877 871552883
    0x10e13020409231b0906040b0405010f030509060c09400b0a05040905160b03100504151e0902030403030c12090c0902091c0507050405181c050c0d020a1e 67
    0x8581d030345505130302c1c0c81480004903400054502c100702c8804540c039203400500003080c1d2091000c1d181e508042c0014845141080524101740c204020701c1002c05000c5202500b001d40a4459645e440e182c41c0814a8000303404003604000182129480c50910440f2140d103940315a2000307500008003610b075100440f04200e0b001a00410845010f10141c24958044184070b030013482101d030b00000914404480700f580742c0140f8100340c004401e010700724101c03e8008015040c21201480742c0b81404809046009040c4260300c160348024000c40000300d080d442c064068460498103542e01d1520f414003901808003143c9410015001544030140003020b80b09046031030341d0144c45100618030f4510800082e40019041540c80020f880d16001440c0152007140d1401e40700303038094a00b81c1c0c03900e030030003089a000800ca01e0103400c0065410881a2000c5164403c142e6524210040b044094400310f502d030040052001c81031107404546010507800103803090741503101b96980c200c510f2401c02d160301c044146400003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 871555377 1250 871554127 871554191
    0x518030a082d04051506240d0e07080c010917030d1d030a08060a0f05090a0216171306031107030c0f080f03040515040803060d02010e13020409 63
    0x11550044820310080c01024110841c6000341a035010518510501610f0441c0d8070380c019450845180c60412106a02c0202126110700b040780b1444084101c4e0040309542c0f001c084002100490105c190f0710285807440c0880880714040d440f2046c007941c6800e207145241c08a41c00d0180080c00004090405402c108030b40c2c0558200b081d071150b10000350090716001c00e8141c102d988201015202003001c1c2020007031656801310181042c1040c0520410300341c006000b6410b00d00ca05100325142c00101541003803500c000140e9640545908015000717503194020184164140c1070080d951124014080440d0f00f0003500100076942e84054045a0003800d80e556144000d00c28003010a0107000341d01c0d00700e40a058403003040181552410126071114072500082100802480107016003081a1600070450085400d51030400d41ca54045ca4000101070324490b2404595050031640b007003942d6003442501800d80c0b41305d0b09040c40640d002c0d4000f070240c1d111041c178064030101d502081c1180060400d04a183c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 871556627 1250 871555377 871555381
    0x20114011d042301090204291c0803010b070210080403090b07050c030303040305040312051806180d0b0106020c1f11160e040b010b07050606010e0102100f0518030a08 73
    0x15410a41c0140280c44000308264420010b14218019a0000f2034090000070242030502c100011100079602000076144091265400d142c400c0440582c214411241604c8181200070b0f4040245220305008010f4100800005070f00c074011400340c5a01c80c82200c100019102265080301c90359000c9501074000f034406a0200301c0d4500450081c1511402401903c0f184001040480d103158010b031412000240005020000e0180010030040001e04074a09503103450100c0d824075252044e10210248074400c00070741c407242a00d80c4030071402800740142000341e442c00c05080461507280b00340304110142c020740f100c4178011700e407208003044071450b000b1030216100b43d00b0400b218080007180b101c680c984103200181c080240d50311a120020005040d00810615042c540321003002c1045c1e015200c1c1160038444100025000308078558418028a407204501d03185100407484c0c0911408113210851800c071800c07640c2c649640110741300f220005001021400c540e007225540c0d101d130b46800000a1641e01c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 871557877 1250 871556627 871556669
    0x160218060a0e07050d1401030302010c02070b040504020f0d18020310110f13031506060f0504050105091e04150e0f0601020a0b090c10210e0a06052203020d02011401 72
    0x180b1903800990358034100741882c480c0d211a904a40b007640c200320012000c0b500400c1055424010034010307040da44040e0006600e4440d074910340d4001c50040520540c2c020075001a40b942e40d0080e01d0003100b502c40180924000e031200d00c1b60707507507403071000340d000e405007000302c400c0c041403401507281b00301c0e580032070920305042e03200c2c418000c2d00800701c6050340ca81e07040700010100d69951080704040058410010300c580ca400c0d00588490b40070400141440750901041046a812000b41c805c076a80944a00620001000c40004d0310200316001c1507005140040346a480d00b02e0f105190256a0005541d0344203480d400c0082c01031490440f4964010780c0031804800001e0b4034054050b810010950480366134044603070001c0d07038801c11402047c000030489110011041d001d280054050001c3c18010420704050440036074a50b5603500d03001d0041c58440c0089002d500488942400440c150654071500032914034000351502d24840003a4015800c1020303281d480e003c03e504442c101c883c0000c0c00c0d507a0005201c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 871559127 1250 871557877 871557899
    0x4021312080712020615030a08030a020c012a0908160314010f052e0b031b130608010807170d0f050909161101020c07141302160218060a 60
    0xc101c99181d03051041c02d002a4524150940918107a00030704440d2074000020456000007803409803280c1c3c040d001460125407010708998014142100140c3e4800c809aa26400341403480c10f00142441d2482c400a120340c00000844c10600056861410495580070103654030b0004c0310208114103440802000090601707100080c0c0c5082040c00494034013144500f0030101c5d101120310b9075146070f2200041322050700501e40e072020709402c241d16040c3d050402508101d82d010007050001030240c1c43e070280f81d54501e00002d0700c0880228903013182649484840c0107000860a00c86c0903568840e8160104101d041d000d80c0c040c46c402084024007030b07048088030455020743c03181f00308000e1100c00c02c81c2c221151101410503100d460056442900c45008950040c4040f0040000030300700c4c2d1051142d1745207203c0109a100c00c07110100c02004002030b10790300090740700c1c0b0001107011000c1e1000401d9008040c400400ca03489900842c0c4603580c0d1891000c400014190450b240d9074081c400110034442001e000e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 871560377 1250 871559127 871559159
    0xc170c13060e0f2407030507061b08040b0601140309070e0115020a02040c0c150603030e04090c03140f0604030206101d0f04080c01020a09090b040212010e0a1b03020a02010605040213 80
    0x180c00d030260201e07004c1d4680b40f8035844120300b503000400009819040c42101d0082203001c0c0414902520001c0c0c40d214000d0804802800013001006120046202c5030722031301003510b603071042440082e80c90400e00c031419691000c1707225180340030b2006000000d00c503414007040102d010164029000800c20755007044000c06400c01042e040c0f000e00c0d1a90004540c230340040c101d64070f54001c000034500b411400c02a00084000c000d044c4070750705141d15440011440d071060310032280c2c0f00d220300b900003e03a0701d0035a0501980c0b82c8074210340e114582c10441415030009240d409008060416090340780c0319440140f00ca08800c580c211040300400100e8030818400c05455407042c0500c034201d0805011440031403d81e0310003d031820028618580030720100015200c1e122040e101114110700c0e1841d4403500340341d100014824921070700d8130360000501c07101c40d81d00040c440001106403508150942d6202400030b401c16045007005610b0068003042c82e0906100b102e10a190740b81c4034094140c41e10380b64030311021403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 871561627 1250 871560377 871560409
    0x723041d220218190905010b01020c030303010f0306090c05040e07030c08060106080c0c160b070203060c0403120c03020f06010e010e0a0e030f0d0e030c0631060c170c13060e0f 77
    0x7a120780e004c080c690701c9128542c520600c004903a207000b24000914120024400b0340c0309400800040103854105421f42e02165440354000ca410392550405111143c101c0c1d02854000b414903100c498441c1002c070301c0e00c0c242d0f403090920b0000d50380c0741c1c001140d99060901410004c40c4890000c21000d04007513010308290044201190309284001c000700040901c2a404010011004140c03081149000c0c48800e60001c543e40c00c59081c82e10f1a1240d81250714030450100074030401d594840306251003800f103410b41c03448040403a002565581c6005004103401d202d450210b6003900c000c900b80590300c0c0507400001302030740c00950401d114120008020360051002c050816903400c40951000003e00141004090540c06040c5500d003d4011040d180d50186080a603c00c18107a588010104003d00b820919005200000c4a106080094902003064490350740c40d00ca9010810020f01381d00001800c92070300740100201c0c56640c8038800d403000e0000c1c00a6a52029101ca2920810705101c1460044041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 871562877 1250 871561627 871561651
    0xa0809060705010e0f0303160513090e1029120604031107091e0b0612012606040b070225050f01091505030108070e0723041d220218 58
    0x1519401381450118251103402c155013000c4200003091030b00803a9483c4100710390030654a04545c08100081e04809030003941c0005542d482e1440e01c0300c508000c4071a030101e0b07032031041180c0c60680d0511000c0d103261365000030401c16103c02e41849818036100504604513032704001c0116844aa40035922406094440c0905104503c1c3c001a00c2c171850091200c0303030725a034603c14681e030b24903011607040c0c17071900040c64001d403010400302d003103942003c00b0f5038112084070640d80000759100000244800102000500a100b65000d000601c0926286c20b8000e150980072034140407421710346007090407c282d000c400d0500305d80381c04120904040c54060740741001450000d99030358407800007034000229080c14200003500803005001d150000c000391400741041040c0e80b0403520740003100030030b450039000100d40c11088843c502042c48002d035064901800001811000700c10701008044411038088070146031b1405010641100c415004107003481564000c0d18840f05103112030350380342c00f000d409411f24403148 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 871564127 1250 871562877 871562891
    0xc0a060c0c0b0432031209030721080306030c060d0c031401051c051213030b06150a110106030501060603021e1303020603070e090c03061f08011a121f080a080906070501 74
    0x3517018800c070040704070b400da05aa21340361010f0174146011070310b80141e88580080c075800d40d1000140c2c03102d0540c80ba400600250340723594104c040390038900e07600485500800085440c80c00e90340150040c0030410842d036020071020701500c3c15803400e1070080c0310302900441d541c0f40019400d002e0f1012282200e00810846041a00ba5034903410240d0204141c0d641e0500c1c1d540c030510400001c4136681c5e422140444885c611280019151140740c42502c03d1882803040050186450400079006103004607040350013044010b551f40c1c0058040e40c442405030036902e4251400c041d151031103005480e8001c5c28895025122811a824461180d2026000318103002000555113410756440f22498880c0c010202140e899040440074004070b09121a200000c01640036070b40f1a40c564021121030465094018900c025000004200b40c14861214850144280b103410045803042e150352000c0b0003247e030320540107100c1c0c3c0c41c901d407505c840f012540101031003000c0107a00c0c00c910701000500805409480005041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 871565377 1250 871564127 871564129
    0x1506120906021b011401090b010215190c0f020d02030c03030a1e020304030306050f090402181b030c1909030b04030810080303090d030501081902040207050c0a060c0c0b0432 76
    0x4903c2d420f090510b40e455401c000c081d80001d00c5098010101e5101c2806450391400010b52504401910130200d00c814000080d54050113001d0035000f80d1203140300300007c2c503100000409202d440002403001d44650442000c50903c008101d030007028891000e1815134407003128000191040c02e50b150b001d034010151112001c42d00c1d01c01980600e1194500042143c5004180002e80d5200100740b84034041c40020000035803116480c41c00c3c04c0c0c2140c26801a103a6844459176072840c0c50800d08144080d002c41000345000540008120f80380400721000300d900300c801400c44900080c2d000c006c00348d0f03179000c01041c0001e0042c8182d90b000300341c10500706041034880b044180342d40c004445000705036000761070595005e90540f1420740507140140140404027400d01c41d41c0300700001c85000a002e241d0001e031601c14001709100a02c2d039100000c00020302030740e80b510000d00c0704110500c156040f2200710000903082407110125411600540b070410842054900d1004603111769440d0b000f2501a040036000c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 871566627 1250 871565377 871565407
    0x40e040b280501030209010e06090708250206010f0803071e0c090e060402040e030a0906121d03070b0a0606090314010906060902131428080a08030a150612090602 71
    0x20207071010700005100d40c5540100710003000103030b00c01d000c6501d070318060021503107802a1103030340300440c0e0900f400309451b00500c0b602e100d0101c07450b51007000c3d040000442c0055010480da4101c4036a1002c01160030340704d01b0f015886c0e1048250040000c0811200d504060440380701c440d00541c010b01005114581c0c40c580700042d181e501d0b10000403600240308005c02c51074184504d642482000005504008a803000903021000c94010710050118050800a8115030f98000e000b1120780d2001c02404151005011a0f4a0300007a00403a403403804d072400105c01e506540316100858006550f0303001d040e4650717242d8019081440707904280b555240d544810105030580500303401004060401030382c40c82442240550780480340c106059144207000d4902c50fa81c1e600c1d40030350a1180640b41c950050001c0410100415555889003509000d00303568041400a280c0266104905903a8244800615060703101180c481034080c21010960703000702e00030b01c156198491004a4400c83e0018503100501000040e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 871567877 1250 871566627 871566691
    0xc15040f0e07031a061c0e0307030302030103050d080f04030f0507140c0109050121022b0504020a14011e11070b0c07050a0b07060906020409020a080a05010506040e040b 74
    0x81e280001d20207100326940d00d80700b0034885411000120200e80044000203103030b88035110131251001640758001c000c124140c0e001600c03044183d0226503440d052490040d0282d00300348410345079170050402ca0b120725809100c80317510a41c114018062541d507513a0307080c1d4109846081d0b08040050078415400000c0503045800750322000742d0000c1040110140004158240710f4110504012254a5100210607018010540ca0940c00f00240c2c40e000c013860050f03178500c030400384400380b6004500c603500c1c0c0041310340c00716005034001c1c0c4280a1050b201c8900c904400c541c3c0d40c1c1c1500080c800c481400c080748072024801c854003900d150a00d0400009000c0a1508803140c00000c40303030300c0018940000640070403455005150a9030b41c81c1c5130350f01e0040c02c0681c40c09003400103480c0d2501c4085800c2000742540c100c0d4050101903108545603583c5020050240c1e80c1280ca090304186040000f00301850705100340e500721901740340400100c2d070341c940e500b0441d480040c060300440e02c10100c1c00f503041c00310104a68 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 871569127 1250 871567877 871567889
    0x1080f0a1a030f0c1c11040f020c03070b010509010e071b03020106082b2a03031413020f030f3705061e070f0f12050c0d060b0c0c15040f 60
    0x50105201130401c51300000011000403d081070000002c006884031074202c1c0c52410032030300001c0449181c86510045d11580d00401401d0000060714010014030440c4503041e00c00c01c0d03030041941d80e00c2e00b1040341e100c901038035482c0c0807075441070810803030710f6400260241061117480081045607484003d94900b50102d000b031080d0045081488850880b03425900f5a0909249010b007891405454414004c461070702d46841054803500e1410107150294024101d40c40340d03458100c40d03503c0c02c82550030341a000e00008074401c00355040081428980010001e041c11032220140610110000304141c0c141d444070040983c0c1002043d0b80f0b80d8982400383c40b0101e01e40a84054240c40c90070901c244c982e00e00710120b010201c1c0203201882111741e4882200c03042c02c04141810450300c80d000c40c068503c00c070ba440c4507603413141c102010006840040d10140c555418040710078050242c54810101c40360040ca00c04d072a007640482c3d0030801500d04a000252078104c0b07903002903c4e00351141c51203100049150404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 871570377 1250 871569127 871569133
    0x109051314130f02010507032a060b1f05180d03030c08070305010803030a021b0708030d0c14031b0d0509030915070f120302131d0601080f0a1a030f 65
    0x3408003030400c1200a9000d040206180b03108040756541e9454040140c1e0068100500440c1600c101800b8641e140112460402d050b41c542c150400d151000310102e0004a1f005400c2c49000c1d1141d0501340b10102461602c000040e00410b240d9034121942e802ca4040000050301010a500e40d9450302c06254000300d000b80c2d0049115013070408040c06a24010308074000301447d020040218030b00120580350880b04011000d692100349420f08402281801c681c40940d00450303600140503c8004010706003c500d14038280301400c00318900382c0e007013250007000f41400c03141040080c5025101b0801c0740040c01070782c240719040401100100c1c040318802c44e000d00c89a440000c0494880c0307410b088040c0d8421044403214031b08226903450a019901c00703600100058002d0388900f000c41d00175015218081d0580128410321903403611150001d402c10002c40d5100100030000c504194482c842c0f80784510074600d4031406030345400148800801c1c440e00e0070058110b0386e9103400d01c25a03003030201d0ba11f055000002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 871571627 1250 871570377 871570391
    0x306020d090605010f0b03010909020a091d100c020307060b0a1e1d13020906120a030c0c06180e3402010501081606360608010602010603030909090201090513 69
    0x40700040f503206030041c6446043d92042004078950007811603065803200c2e040401ca10315a48049a186a40c41d00840b0f40c0c9070410304801e030f42c5001150741c01a81c2882000701c580b03149960180c03900307d40400781c034507006030402c0007014042111501b0940340034002600b4500203640c1d514140301c07218003600c60424044500582080b40e40a0401d800803041400d454071412070038030200c41401710b00803100080c060b404040000c1c190399500003680a603c20400c0654804004a26000704400325142e0708803020780c28030360041100c2d886844408aa2140488080d50050a0590038803249500070010359403061046200f11506584d12900c5ca00b030a400805115100c8030500c1c06425204140c0240f6556405510400c1ca5881c0085402c8112101803c1c41c81024250710b125080c45a00450030004625014008034003031400f003c0f101086900c0e90380e500c1c02c140d80b50344080382a24a10b02c40500020345d440b80074004070220340e0120042d00e2050509500d0290b503040810a0541c82840c00601c0710364601d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 871572877 1250 871571627 871571633
    0xe03120c16060f0905121216061a0a060c11041d0d020a0b180109080a11060132120a0303150501030501031a130b041217040b0c0a090306020d09 63
    0x658070250402d401c1420700d03d0307052140101072044511480f482440c84014000403d407007442410070340481409110341d9811114a5240b0075114038100b102c14a00e031500701221503100c2088182401c02c01040340300194a0020103c038150300854041e10383c1d0700c00b984a400c56546c0d501c0b8012b55450300b40711b080d942041440c40582011130036000c440954002e01112030005003107000c59548180c003400b41c20040c0e28070317003080d40c01412120802080b41c1400a082e01507650004e8468018030202d204480903681c0795101c07000d00c204403048a11b019042d8410b04440300b002050741c00091078014004003107800515004610300b00660310305501003a0796110740100100c0100a11001d00300a0805004951556036000f1401c41d041d044c02101110303000c042601c0114000b940898203410450501003401e10341440c010085000da070407030105580d03000c400c000c802c0410b0001c0c03113036410005c0c0e011660388841c02040c041d0301c505109020404c680401000144661014250501c0000d00c0041e44103807a107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 871574127 1250 871572877 871572913
    0xe01120b07031a150c07030f0203010c0207180b040b2805030714040c0203161415160e01050c2d0c0303031f050405040807110a0f03030e03120c 63
    0x40c01d250201410f100b444243c80350340c43c0f0382d8070041d20159000d44a9482400701810180203d00d400d0341c82e8001c3c0a0000300340080d000c8618038542c0218001c200034116180240d90724902c0d403140ea103003515441410000307c0d805500080d103880c4050004280c040700340c1c0006400040c0ca881480140d5400303003400e5000307c0b050f4060b9024201c19001000c801b820010f070590703450746031042640f0454030380b2891010203200303009a41084003801c800260580842c40c216140702c403070030086089803158a80c0141180007907000c07240a0300070001024a000c3c1e80940441e00c40c060324030045c1c1840030802c90183c00850400c80d504030b88010440c01c40d04035244490100c00310f1811f0340100c1040e4000d516008003076802204030b03508003039280c60030081004603c111141028040e488164024035200400c0306110ad06401880c9091045903500022460034080246a035441d00030301009160301001400082c0c0902079000e8030030402822214469000c2e088002942d000004480c0700741c21840c041c5082105207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 871575377 1250 871574127 871574131
    0x302030c100c270b0c03310314070b0a180b03011d071211041401030509100903030905011a1f12021b07140f0f03030403060908040e01120b 61
    0xc901c0a2100c000070700402004480164000079480d0690100b4003101003d03500400010210002131300c0e12070309089240b030340703a402907c09600011155081590ba54900e14003203504612004010580f150842e101c0300030b0300384842c030109814822400003158841c0d61001815072140301e6070750001c40c20321070000c030240780030161310600c01c900e428001408050410805614103940310581c03150280d407040c4049800c05612041c040c00c20746050444090300600c070000700f0a0b500038070f4000d49042900300c01102180c2c0308603583d103400c2e0084002d41815060342d0300315420f064028500491051076030740b00d4508507801c07400d2020030400d2915201c0303003d08115150f4001e480c0c031141d410340e003254603401c041c20018159008403015680020500300012181d4003500d000d0b40c0c01c008680d442519441035030182054907403014440c0401c0b03107094810b468100c280d170741c0080300507000c1c40c1001d1550f5540e501410807100112002803051001151408803040000d0092803c041c12003401200c50800280303e641c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 871576627 1250 871575377 871575403
    0x30304031218380411191d06120d0f1206180b01050703050a140403062c070302030c0f040612031d060909040b04081306121107020a09050a0b09040302030c 68
    0x240080310f4281d00d2225106030351182c0c000542030100113210f0000703000c801ca4401c980120903041c0d4000715404400000f030010441d40f00d2900035035030b11020108410380b401ca110107085030303002e11001e0040c01d2117910020182d80490900000401a410164003907030036a41200d440c188401110050309110750050b08600842801c1040c58a40c407520b0003081842207030507801c1031004800e10b220506504804403002103811040030008203025400f803605141c4c11040880103a01501e0071024910000300f0b40700112a0300500800c00341804009110070322010001207903200d42c0d64540021010340140700000024440d5a1b102c02030301944041d655001d603000ca09502a590a12080409480d000403840c0c00c21f420211010b03403507540c2c0c60f00845030710881030000c03804208144000b40b455040700d80c00201c0e6984002c1800061049c201c00c804d14010454060752213018a001000b548100c1d600c0690050068000419100101c20201e0240001624100d00580c030010b803000003880240b10007061202 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 871577877 1250 871576627 871576703
    0x3010c030207080d092f01030e120a0e0a09141e19050411040218030709020703210f060609090f090305030117160605040501140c030304031218 63
    0x8610744500049005032130301d01880f280e40700459001c1c00610741608071000440c101c04852642c0400c1755440e0f442c2c803080c0c2240440d003814030610f00300c42c000c2000f9041d281303c600702c1402c000341100201e071046000001d01d80c2100e441103020607a01c5c0d00d80078991040c80f01000d541480d040160f01ca10312030031400d44151102e80001c00380140d1010311303000f2541044d15424041000d40703d608007a0308001d003e0079126409071001488044030000d150000e240c042c011416a000160f5644248060b031203a1803004001400c25038082072040c03400310041c1700744001c0032000140d14580c08240b40c01c84245170401000318000c000108070200d05405182688a6218014131209420303a401400307c1c0810300405940700640f424440c15410200310368140652060720b01c5042d05d0b960b40c00030b2301c0d80e03005001c0c0500245031518034100b03049501c3d04846500c0d07014030080d440c40d900c0352402c0368446401b80d0021820340c2c40300b24089241c01341c14030400b00a0f0060b07904a112140000385641821460412904513403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 871579127 1250 871577877 871577887
    0x406021207020112091e050f010f0905190c080a151109030703030f030e03040e01090c02070f03110a03050f0d020c0f0f040f140a0b03010617030a200f0c03010c0302 72
    0xc4d91004264800d503410f0000441c103211070346045c02d44014900c41c680085003000000b00144000091000c018000d100c0080210149929060b0141c41c8085800f51040d80a4440038401400407100f11002d00d003d907c03950f00355520380c284c581c00c10440f43d1042e01c159000481c004800d1a8a218a1009031180c400c403620305038401003c20340391039040c1b02c0542801110040d0b00c00990081c1c01c404580100340060f41c1d40d840d19404252a944000e028580c22680303040040c44242c0c0c0009443c1060300c0c05021846a142d245554010100011019054005001080c00000901d0800010400b0280c0401904400c6400540241752501c0b0201c0d051051121203110700311501e4010540b4041c034010350340440e55100c0c0311100c0014211000401c0c440d4801c8408000030041260300c0b080b0705050840092080e5692007a0741210703084520b1020f2880d030010030401015030f001340212802003c5c0c505241c2c140806000140b420500c0450300c03440c0d1500004003c42c0c1525082c4100000f40200e424114200303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 871580377 1250 871579127 871579129
    0x2091303080403030b0328050c06041a1608070308040b0702011a0f1c05071806060509010e13060f0e010b0406141308010504290f06060a0e1203040602120702 69
    0x460003800240606a0301c10710704600361400d00000b03007041071b087c00c08188445014007080900c0c0440c00103480d036010b8000d41c204140f924504031002c81d0302d002c0d54041224809400c1c1482540002810340858411008860006202e50040e0001c5406912a15110301d45030802403541c0b58020070940c2164903110300b1450284501022190713203d800ea5028165001c0c400c0441c40309650b581d4040d04803841c04010740200840000d000040c0e50842c04081c51417145445032100f654204d02810000c00c9080c0401521540302c1e2204460350324009005466010103015003404071461074001c00d41840ca514000d218018030341030720074010001b0004040c9070500d030800c0205600301030030840812410001e00041059015409540070305802002000700d42418070700000d81d45c0d0030300c000740f50342c60b42c0240c3d20b10161060940c00b403049250046290700703039030754401b002407039880405488284080d189032082680c640c2d03140c403040d10b040d01d801503903501c0c1003000191410122034010281140200160001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 871581627 1250 871580377 871580387
    0xc15040c06021e0723180709240806010e15041706100302061308030a03020a030c0203130e062b060b03061306021321033905032502091303 61
    0x21506080111800170412a01c9100c817049000b4146901100101200b00c0100c3c0d542c40180c0221042d44402065560711040c2d8541c02150041c2d0315194401c00d019061114043c0c0b06850707000d101454400c4ea40056940018442c140d0070305a40c41581001c6000c2c40250000340401c80c0d098403010003440645012049d50b003c0c0f241c94080280105030211715441a03860034518003020381076070029a905c400146400400a42094500100103405c11004422080c0040100c03a08401050584441d41d401d28140050148002c4c0540307400070b030701900f5590f0220442906540240c2e4480050381301e24580c1c1800d106681d418000e56100341c01843c01c2c010444919841c00303100a600400150326402e171110510001d852031f500100003001c00c402043c2c030f0ba1a4010028174524070036282d0448005c02018110720898405203061410080c050034012040c50003105004250b00c243d04032481c14122020454065680082551014590890f4003085241c01ea05040d8060110b8008a100240d03589009103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 871582733 1106 871581627 871581629
    0x2090a1a1f0f260c0c0307080909010b040602190309050a03050c010801092009060c1608010c0e010e040506120d02030703020601080102090a0b0c15040c06021e07 71
    0x10070343d0041020b089898108041800d104084a4001e904064082d0609642c00070910a5218030307441040101611403040006039201c409000c140a6540d8068000300e420b03c80602003400700325070010b481c2003078216045c034a10f070381651401c080d80d810056400c01070b0401300001d070200c14000001003d806400d402e0343c0c0c201050303030f84200300d80858100380080200c00304c00e00c0042070150500d0000c1c0c201804000d210510300404050080e1909a200140800218456000f000f48400a00c1441038110207401d040c0100d00b24100000c107508200320042d4492075940011468544030000c1800c2c83c80c40c1c11040f1151000300c58000380d1740b80c101103801c400600c96030740085140d010600aa0320847d8015181800240c2480131142e41030708040a01046c0748100240c4c920146440c0c41c900340100c0c00746001e808182d041c100001c0c01c142e000c4900502080500c1c2e170444000c100058154 = true := by decide +kernel

theorem cover : BRFrame.Cov 871402877 871582733 := by
  have h0 := BRFrame.cov_init 871402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 871402877 ≤ n) (h2 : n < 871582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
