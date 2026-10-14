-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1609
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:50:49.806907+00:00
-- url     : https://prove2.me/submissions/bec4fed3-dfdf-4ae5-9bdf-89bea9c2e3d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 289208633 ≤ n < 289388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 289209883 1250 289208633 289208657
    0x2151005030105130c050d1e0303020406080106020f03030103060b0418030503190510050609180f0a0605060c0d03020d0b120d0201060e01030807031805091609051009050f0a0305030d0b01 82
    0x101010072499502003001440c0915010800041d2030039511f0942d03650b00342d5041e510010054600515115200b5140942c580c1e00d40783e40640ba07a00140e105030155040506040f600c0030006c0700b1241982e51001000980760440e0001c2002010701d85544130010b581c880c10402030541203c00b03940305147c2e04005a42101e107a440c128160381d07040d6807900c010096003c09210614249001e86100000500740c139002c01c61303110003402c4000c8240c42e40503d645001041c000c0100440c001c4001925064a0303040c07a010310354000960710091030580804040c1d0107e45601c00c48910303041040c1120005141c070620222801c2c00c10b450b0101d1445030b00241d8a00780e000030b0100f07003166885040303d0700702c800c0d20f0a18829480a80381c0c6113240100c08540800e03408003107a03582d03440c100d10b0701070024005e14100c3d00101c640058035001003034008c10b1203400e0500016106030381c0083c0107402c0e100103903035841d40322076808003003110340b45a504011b00038000401c0314030155105600071103039080f00742d03640e40344a08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 289211133 1250 289209883 289209901
    0x31a0409140d26130b0103140709140a0f0e030d060f09061206050405030d060308090301060f3c030812010b03070e01110c100504180203010b040e0702151005030105 72
    0xb4000540303442404400010560403d01a00f034194401c98950510304035224654a050312500300760001c0752601e0020076038030801101046900c1c098010010108200300344c0400e1610480f034020214050a82c4800f0380f011100c28a8101001c0c10444504403911549000f0f581005050345002d141d40903026114009010049070061504030742e07900882041c1300c01c0548030000034020042050350244410040b0813107500c04c510828000358000c01200b51541c00c103008150a60b04250700052407200364081c180b000301d1a01007100418280641464500b00e001601004000f41c4e89500004000240d100003042c80003440007410742d007201ca01314541030780c1c940d40d086205000c182c038440300142551141404a5002d56805002e400450084400d8402e04000140002140c41440340003d40041030802041a06c5901031441d00503400c0154115030504420101c00e0055220318805c034400f03e0701240d4100e00a1002a48121006049110358a864908500c0444643c400c0324002d61804001503840d0b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 289212383 1250 289211133 289211147
    0x5061911070201140a030b0310090203010b0a0302090613090b01060801051003050c03040204091b080d0f0801030f03051317012003240604050315010602011103010e07031a0409140d 79
    0x607a050711515507004040130300f401e00e40c02110488040c940e50f8050030b42650703003c00005504403c40040802c46002c3c601c141800c3d204611038540c0501c9030b940081c001640c440e1a621762050782030f41d00600701c12070581000c01500d0300c00006010009048000f096a9901c4201c00741a64425152001001c5c0945012412644100d40741d12201d9000d10101d0010310740b030b07007060401c40d0140f411940046544d0326414982401c9d98000c4000d98002004052100c0c0c004c10f08805107403103810840d02c690302d1519003030000001040010b04100001451021481030240050061720840011381c4030055410700c080d000f002c03280420030308103011951810300000031800320b0b4840c20070100c050384c1d8107462018030075440a0003080c00354092014000410251010084062410901c02c4c040999524041000e802c44000c5c400b503811003001000180806684901c0076600003041e8030300000c0d03249000c1101d17608140c850000d29842802d000445e4207000158040410961101c015194000d8001506581c4a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 289213633 1250 289212383 289212397
    0x106080708040b06090601090801050a0c1101020901090b0904151203020111091f11010f050609070c030c0311150c07120504050f010c020a0e010f0f090902090f04030c05061911 77
    0x30200640016541d400c000240700e8011b1818144072981c1e41c0c61f80e074142d0030342e0b100310349001c1d4403951030b07074202c2c000d541c02001d0f0b11004011350300031450601c41e50002064411113004001c4c2080e00011a1860750300d40c2e030300003034204007444120b07900c8580345e2038019284503481c602a40150308042c01004544142d004032020500f006106200c14041c1c0074a28207440c03028509482440307903034258070706240400c2c0102d02d170141110900050510b460410001a0040a0078440401400d4441100000d422101c180030407901070400850001103040b0b99440c2c900062040e084844407801405148a5000003403c1c0c403034814405022030034101c40b000c8030b86000b0303807081c0360b80718410a5580c0090f501405002c98014000b80c1254166901c445100e080ca20f0203a01115240d2a8100108400000e42469074003500307142c08140100c140076000285108400781000d140c046c036210101d4101405643e621400c194040140c0e40c00c0d00c0c2080140c089400c01105240207a4205034409040c14560303000c5441c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 289214883 1250 289213633 289213643
    0x8040b0a021c031b08180d0207050411040b0a050c071d1501020a110d0c080a111003090c030204020904140408030604060807080709021b100c03180f020609030c04020d05010608070804 80
    0xc2499140d500311005d03900034104c030142883c01560030000190034441c80c00c2205640e001007410f00e2410050000700e03195a81100c4804006020905c91020484100c03104074003685070084d00c400400c031105003420a1a8840040a01210300b403010700d02214088901c6050054400448403100d00010f98950b612080001c1143c9800a038a89551a00d01c101504d102d0090b48036a2a0325100c0166518101040e08281d075009a4804051f049203860070381c250f41d0100c1480c0c288481003403503440072201400d90000902c144d401249441203515039601002e82c450354034119007442d0038607040c4030f49298400c1d5981805141080004580010001103980403646890000c01d2420303d4541d00c00001e40008991031030720b030307040308990030007150400080d0b10072810780c0400030701607107503000c0078007151220074449016641102400c0e011a1200c954080c1d0142c05a428507920401100003e00700f004000d085c0b82d000380f021844001400c10faa01040c1a98602c1d01c40340425154050142c48502d411900102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 289216133 1250 289214883 289214921
    0x1030309210c050111070801111b0f03030a0f021207030605031603080f0d181a06040603030e0915040207050105180105090307170d0c0302030a06050618040908040b0a021c03 76
    0xc0c4d5106800c0b000707840c00761708103450589440360f03982805d50f08541c1240c1d01c1080b0125049020b0300d038008000d41c81030091401030000103000e03080b40c0e03140d001c000c00911645554a8440886c2c2c44150101c0c2c1c030400060098826503c1d04010203070042030140901d500030300c02c0d0a10081100344066a0f10256508034001c181008060300800000e40d0042a600303005a0f00c40e154940218016110024224898800c2210041010510368602c0303400400c95442035040c0361003040469040b081840d9021000e0f201c0303d04542d00e4410460854280c1556250060700c001400c100740300c4190301240c000e00e2040e4800c0325501a421046098030802c0d101c0403419041081100005030021901250103400e0400b41802d00104880340c0f01101d084d401c81c0d50100f50000100400c40d400da100b010040c2408039042418200c1600200461410034803029018690327074100d090500c070204d42a00d00038414410407568800484200070340b15030340303a00c2402118000890b0726020078002d008100400340020859a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 289217383 1250 289216133 289216139
    0x140304060e04050907051f0816120e0c120f01110f090d051f05040b06011806030e03070f05030a02060f010e040f030c0b010f1509030503030a05091501030309210c 71
    0x910b009808444c5611034240009400d45500395880c2c01d044c00f480c40446210300b246030250002c00004d00650807403d4508071028903680010f01c1d148820b407082000100a5080e1a425292000d021110303175109500804005c2c2c0d82d02d0010b01c0c0501e591032030000b8000310031501c0d00c82d40c01d80174520644c09000010711003030569042011400c00083d002d10101d400c0c0402088540424001102c8c0c880002915207003048240510314a0184e042442842c0c20340d42494404100c044502c6140561810542c03988041c0c1c41c03285003041078070421608494011014a442d20700150750760b10051001c80940114400942000f040c11310140c100d6040c042000c1040d59140c2e1400c0700d075054003500f2420b00c01d0b14040075000c101010786c8a8080c148240c0011803084c2440c402d00703c0c906c014a809020030401e194140300043c07020098a4001001d0580460640c036240d58060404c078448024000001c850f00c00001032581c0491030f4422200485a080d40e040d500304044d6060500400b009080c402c0303001d00c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 289218633 1250 289217383 289217389
    0x60114010203040b161739100c1103040f0902030c161103010b060a05070f030905030d03020d0b06040503030a0e0a09060801050f06060c0a0f1a0108010504140304060e 73
    0x8001512051040d24600b58803113900035001d4000c0742400c407040c404a05444100070081c00d0701c080b1a515124180e040c0040b02441d0640085075045040f045409560315005480d050000f03810202021020ba6034400c4207052080010281110882c00041580203202280d01002c0101c0d01511041c440024005003028400b00c0a507102401120130b1201c104104c000c0c40950000031220148115682c03d6405030002c101070965001c44070407480303600208116401c141d0008115900240e2290006148c410541010340303401c041640243c1d014011020515140307549a40100000075100d402003042c4000c0304140100d60041780185500341d4010000c2c48403250092039203c12603540200403c00d425200d154000685986502110383c0717a4603407060101030b402c2209101c0c5c0c040b80550b400d0782002c00c08403030680c0e82c8003400c4010f004002e01c1e80300601480a0307032001d0038290080c1c40c100002c03569102405c034000c080840d0700350740010314400284401c500103c121012241203580d01c15040008100f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 289219883 1250 289218633 289218659
    0xe0102060c0f190509030f0123060d050604050a0b07022113031506031a150904111903120f0503160507151508010b0307090e01090b0c04060909050105030601 69
    0x30340c441d02e0003401042c050162041410351290b25503564076449410420506141560701400600d481c0d0500036036180302600c0d030402c0d409038504d03002c0d500e59640700c00002c86c10652480304c0241c0580601d03010802031040c0083c1045800e8410320301e482c0207540d542400c980310001c2c86004010107080700c64035407c02c0c19083c0500403910b1000001c400c2d00b5030340d41e219541646001c5480d254151141400c0081c02000303002c8000c83d98045442d0304c4030b49081d5400d1030b220312340e03600c80c02d1042d100d00c80400c045c0a048544800c901074083c2140c02080000003140844210b0391104440c10092840b00d180e00714400d01c260b480c0ca504549640b81543c40b11404002c08081040d40a0704104051180001290480c0256103080743e0f00c540c00541001020605a0301070113075000390f5800c0e03042c89044d850301c2d140011000110b550b146000209000d1042d46035000d003004032405070400038034000380705854a181c03004008640c0640c079a01f442941d1001102d05a8100344201c0e681500319000410820702c0d0004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 289221133 1250 289219883 289219897
    0x5040513050f01081513031b050d0215060a0504090c0f08061005040c0807110309040f02040e0601050f09041a040c120e0106060e21030a05030613060302100e06040503010e031305010e0102060c 84
    0x9080048c124520030b0300b20001d07207070501076038598040e25550b44841c1d01404503070b44241e813003a0140036034541b280c003180300c0030070600c680b9000300d6032440756005128150781c410b4094882002000784680e5200320b09035803814140c03406940c600c0311040001d114a4544990703082081181c0b248221a60b0340441540d009900f45060101030008200b8111107982e203100b52841c000b01c008005840d20300301900d402c10124024101410320204018100f02e18400200740c6610303080c21640401d02c54651040e01ca0040003050200340c201d81400d4036062620f42294403581d107a05a40301c1006217200103d411400d07107505200781c0e0042044480914400c1c181020800743c080724440850550b607038106005451a8085800a000034002105003d113078503051030700c00720b01c80b800c0000388a4103003185c0010310015401c2601030305002421908080d0340d00d41205036002440c00034020010303040b00c00701c102e440c0d92003100601c101c0b00142402040940c092103c102c0200010f9000b00203542d42e80103600d00f41c0d48101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 289222383 1250 289221133 289221137
    0x2090414070b0a020106090b0604080604150603120509130506130504080c071e0911030106030c02010b0907030c030b030a03080f1305071203112a0105040513050f0108151303 76
    0x205020481e0306221004200f180703500c1e40000b6009290481d100c1c00c4404415000e84030b11010842008004000207040b60083d8005c0c1d205080b60851103035074401444551302c0104070350203030b0990586494100025020302802515001500c030400007401d811140220b8003580e1028200d54490341d0b900f1203501090340180b090094502d480c00207e07246d46012059400b42180e141c20a400c940c05c2d6100d03a40207002002c08230b90501030448030842c001c030503000501808040641c0e5420001c9168800d4201000c1f0f0b04e005400c0659a04010000a014011020000003c00e080041c58070145c200040c0c10155180c06980d1280140c591082d100902031001d000016002d82c0301d200000807900c00d00071680105400e074020080307042d052401a03c0100440e110325a9508101a81e40780c5800210308040f01c0c0000e850501303c0c40340a1001a5814041d540000c2d401c034a1041d45000000d1321680518081c40c4400c6203609644e907150703c00ba503148160000c908095000c0340110b02c025984401540005110b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 289223633 1250 289222383 289222393
    0x108120705030d050408040312030c0e0f010c02040504060e12121302010c0c150305090a02030a380103020a050907020c0d060b040920011d060a020f1906050c030402090414 75
    0x3d030840c605860f0203680c01d4500b03480c0001c0410800c82404800702500c1f03202c0c2014041408400d6001d400c02e0b50f0b82c12a1030041c5004021030307c41d680b10380c61001d841c6a0040c41084681440d0812800405103603514404600c03410300110740401100c000d542c001d1030000b6080c407040d0350f105640303c190480720034200d06020000b0110740020f00b5a034500c2015006240850a0113040011f005090710000741807521542c11103811840561004610141011341103101518812503c0740030303100d4984100d0001e9174482c03080010100052400b0101412a80203c035905442c980341c7c4204143d03404c054a41c0400760703003e01006e00040c02c1404210000b01d0141700c00040580c045401b1074180c95203890104c940104a1018140300314100c15800f017800d500303203080600a890400d081c51022107100c0d1791446017401003034402d0b0581c400c0080e064031480c240e050351100700b61201034400c40c03104002c04440c0385042800141e0400e828400352446183c005100f41030b15191a240c02c0c5141140340c40d007420341e01030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 289224883 1250 289223633 289223647
    0x703170d0e0f0c0907090311010e030c0a030507030b01082a0402070f03020307021801261618050703021e0c012c0106080a020105030c131203030e0c010206010812070503 74
    0x705204052508480c030001d0301449072158200086520000c00c0c020601800e0705050000c1741c2e0101441060382d0003828600c800480400002c0e10744100781450507031214002c1c0e8088100400840c01c00c040b28402c00c000300c01c90740c0300c07005261611100c52030140f01c0e0052501150458241c402e0600c066000980014a0024182c4800c900d6454401d01039025130310002d400c4013142003004107020f0b0320340c40b01e0840300c0301c1d41444800a03441003482c00c0102003040c0304200300b034481028071100505030001c0800c021015078540202420600c1c0c10300c0000400d1a14000407036141c000e008503014401c15030440b589452920b9030942d4a608040401c0300300d590382c0d003260705110303a0b502040c00542c030305103248400d0103981680ea40e017910400c0d0050111900800c0e070500043c0d800030281c0303410070680880c80d500c45202001119030f48034a540500c0c0012a4860304500b415055400042540d82074016540300003441001680c0d654001e225125141c0c1c05204403540440c1c560000d08403082c4140c0035240341c421 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 289226133 1250 289224883 289224911
    0x212070c170415120e070605070219062007050d022709030c070915120f05100c0807020f0a14010b060309010c081e16050405030a1b080703170d 63
    0xb1a4000708610034894169098480d04407041c0e041144515200307001e00f00507911400e4039404103200c1c0b00e09000c3c0c0825204110350303808025100c8444a0100c20003416600d9030000e044821041814482d030040e100e001d004c0311300100788038082d141e000c0c1034108100360780c1e824800d0040006002c1c998019600074900f40503900d0103000e500034032240d00250b444c1c43c01d44035107030b05000c100c0d805408178600c1d01e0030503c44050310921420407103203801c2d600380724007096080000b04121038504c024294001c000350180c034001b55610440f48034129648010f016981c103201a66209000b03130f043c19059001205001c0020010150003480b0348080700003058000c40c0d680070a8064109844100c5c50741d4440c03400d200300c20740c0503800e42d52240c006200c0d0801b60500c2c10058002540103403141c90220205a10745003800d000c1c0044800a0502070b003280d221440070305005515002c1d100c00b50002c48510b00001070320450024143c030641c0d80000c425004441d01507948000350b032021081242480e103030520314000e66 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 289227383 1250 289226133 289226137
    0x601030e10060501020d03060311060c0a0209070203220b1606060906030302060a0c1403041506030f080903070605090328050d05070c050105180d03023309010212070c17 74
    0x1281d60000802da40d4103042c000782c01c1a017044850401c02d4601001040420b050452903441840142c480640d95840f405446040c800c04201c0a504510324000b4407e1040d800001000981c802c1000860083c120242c075100c0c19400c0e100b80003007003030180803a008412070640c68882c003500c103000c0020074907507484a1a003a1642c9500590141e0880010046240114040e0030002441881c0c40f643c2c10801010301119404050009400c0da100e04500d04059003250b0700140265800c040d075500f40722450710b00710915511111701540070740a01d40c3c000455601440641c0c0210030000c000c4e24030002d0706808036602071062941089a0041c000c0c6090100302d09100d2001202178641d81e9540d41d104070304000360700b001c117603211504114040184440c070901001079100f44041c100d404d00500807180c202203160041d8440701d203002c4a004004807030034110003c01c0f4050103a00345100c030f01d2580d030784010508074080e1003490084003250340000340e000e900c43c45098080c6031080481a2150307204212110313083d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 289228633 1250 289227383 289227403
    0x317190501090b0103050916060809030c01020d02091f09060c0f0209070c02031501050d020103020d0e120a090905252102030403080c0c2a1201060519080304030b0601030e 75
    0x525070300c00c29000f032540c0c5030040075400a802c100504020190f0803428544119034800e810412214001143c810141402142c400d6103848000359190000303900c1e408000c0d48100c0c20320388100b4040035001000c1e050351440c00c618500a4880d03803002c61912000f0342d0484090384084581c42091224400141e590310840c500400341d960700c861101a0620525161030403102c1c51308014842e50004000f41c1d034444c802e4100080d42841c0140c0c40703281c5400da01c1c0c068004600c001d540381c000c101241c4090040d81e0090401d03802182c0c4c1d104003c80e42d800c04101251400d5030104800039001d1a42003121000040980314420f42d40b40c042c2c0300b840b00d420006080800821800110394000060205069001002c03a8210000d0003020303151440c0071034155a1510541004600e40071868511b2640545414a04800e03a2000c3c01c90f080bc100c00c110458001d150703030302501e84544180c0c0612440c1e00100036150301990b070040029445e2504680b41c0c480341e1100100001c8c1055108e00d40c01e1072101042c00441d4071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 289229883 1250 289228633 289228649
    0x20c0307060e07030510020703050405030604051507110a020418020612160806090a050627100602030702100c020f120d0f0f0c0b0912040e10060302070317190501 71
    0x2a450545030100030703201c1d03441c2c2044055111100500100d00301141c0d4444286010800507501c000301c0c43c050b100c0d07000e203034002503050140e50f041209201000c21034059921460305500580d640b0755a060360304084c00d440860300c540c000070782e500060525501000b401c0310350178446060708030396074001409a802005660290f50101d014081914402744038807030b128410341003001407881d2071320100d40701210042224081d01d481e1030220701d05031078a000d08010b01103402649200b9184074103084941c0c907001c0d60703000f1440f28480000601c0500c08402e031000300e80d006010b1043e1401903401110001648101603070710400329941c8010039075800aa40d8181c9078180302820180b00741d24400307000654115078100034030a94080003026107a1054508400329030049040b480e58803030380140f914002c0d4210300001240400a00400e201050ba03814a10030405076507802038084e140c40045060b401405c0d00100814541410300141c20740f004042c692207400c4004030203812807440f84590565000b0307401050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 289231133 1250 289229883 289229887
    0x70c0807030303150b030a0b040f0606050901020c0301050906070f030e0303100e0601031529120f011d010b0c01090c180c050304020f040207080705030409051005030a0b07180801020c03 81
    0x301a007500481039141080130b4824049450302010007043d12000303015540741551042c818a29582ea036104c594000005c20003000180e4076103038041c06aa01403244140540314000c0c1e083d8092805010321889210f0b040e020740a581c513440815642411524551418192600f8010601d480200051441003c0c48081120181d240040c00b00d40d40c2c1c0b01904960400d414103180307185030000e1108035000c441a4484514611360380c020624a196007103060700c00b110360001052062002084201805604640c03c51804d40e66110720503011304040b0006030510401150041141e5020000907001000d10b11001140030241550b841c00000100c0c0c000380f01341c10821034140c00c11000740c801c000148086050071490f42c00c00340c00103000e003204454080d20851f00042c100c402c0003194803d42d844250f00030112038071151650303001805480111428028014001800601450000f40400106411880c00822134582d50000c5802e28031010184c40902407240c4002246002440203043e06002000555 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 289232383 1250 289231133 289231139
    0x32d05100c0e2409060f03010e0f0112030c0c0e0a060602010501051210240e0403080a11030708100b0711030105070f02030415090e1e0f07020d0806030102070c0807 72
    0x40c2114040c0c8840c604000d14101d08182c00c0d11012440001030a00482c8450f01110b000071251041c490500140d421940105803d1040b4102d1070196050f60302c07102c65801e0035580c0c6c01c4450b404000910420180000194030200840d0142101c80304482c066000801c3c0151510001045950f080e111924415503d820401c0a40d034203104607805003104541d542c101101641074a5a211070405410030020b59440c020307003410114050031070103044d0500e1590712550741c1c2d48017200307404400c4800b82c0100d0080b00009000020502c988184a810b02500d2402c42d25808422589544020004900c00000e070340c0c00f040c2c0b000d6900142007541d1003030300314201b0080071a05050968402410150030b1103416100045080e40110a41c0c0664503005041e901440c004441280c00b00e1442c2c0c010601c1c900e44030103010580480344040303000f0056032000c1300c0c0d064448080090619900f02d074240300580202803031074581840342200d0f42d044000180050f0034408203440350b070020038541d4080340c0f003580610010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 289233633 1250 289232383 289232413
    0x606090212090f0111040e0a0e0a0c0801060f03150b030a08031f050d02062205040c0c05160b09100512070c03020d0804050c010302031f080102090f0f030304032d05 72
    0x8443c05001c908001d2010240e81c01100010340228041d46240c00c0c203880c0024500c8000354882500a18900100c0d10081c4203810a8841e05c81d180c043c000541d402d010002c50300e004480718000c01c59a0042d01d0000505481341d50703100400304920a1603140c0100c00141c0007080050014500444184140b08021000b1501244c102c21280d0b10144c0220000900300001d40e64400c20b542c065400d0311100e80303000c0d803210309400d062003081d080355a2003407405250b60000b41d0b0000314038408611070780c01c6400c84282840b46c0100c91205215500d5a04010400303440c4c1801d20604c22510045141003950818100720035464500404803921400070307100415002c140355041180c610b0584407401d083d10300b4240b5841da540c80e001c2c2c0c0e000311418107400102041035401c41c0100320711111048000207005540f41d400e890301030b43c4a07101c0750780310300c4803a58a41c10510705003d00b0700d081100107000710b00c0c1c6071450765004d210780f0002c81030b0111401c920b07585507500110801d440f0b41d01e0b03120381d001d052084146420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 289234883 1250 289233633 289233643
    0xc110a0f05101409010804020d170d0c0c05100f14040b040b161b080d020a170a0b090f0604090b160206070c3210021305040c0516060609021209 63
    0x60301c080003640c0c0d181c0e180c0e400c104000c50703204c0c900070300e8901c0f0583e603640081085000201b174003c00324820f650b01e400a0400c00d80c05464521480081440030150100e01220058001e40380500960801005088090700950000090009010002c5042c02030180209500101110b007a540b551801c001c11040042000d03c2030ba221a0050b865850900060402410400c4100c6128205029108440706114036030064402d580080a0103645c0d8a903c3d4070000c0c2070f0309480000c0d088551121010481c192241d0241000700321000e000522207680d0120701001240010b070595410a82c0c0f10342c01307c0401d2840c1074503442441310031003039080828000c03002840c02074001d044004101640460400260711003007a5095080347c07090844101d4a0201040801c5401201c45c45007445104280304a1500c3e5401401d18601c1800b4903104140c1c1e1754042c1700580d1000d00c070513030003e0001c00a14626010114562207041e010300340c00291640c844c043c0908076807086481d0440850080104042200d042003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 289236133 1250 289234883 289234909
    0x605030118060b01031b030903090501020c10051602040c0807080604060b07120e0307120b09030301151409030106090504291501030e070e01081218010c110a0f05 71
    0x20003001481101e0540c052191480a401041d05803074095154980e882a0040240029502c541d1a0324100741c01018000788818801100800d810700c0c0002940c0d03002040c0702e12050700c082c0404c401408240000c0710704d5484800c80d00c1c1000e100610300700242e1901c7c810541e50b040c680d200c030091400d02813009000600006c1115120f503050200c10305c4050980008d036144103502041d10200981c01006c1902e040780d202c1a01a054810702070002142a4102800500903004000307514507620713170f180000d88a100034000c0d102d540496181c40c60201d40b18810702d40c5180c12034400103003484c103d18002420350f42c007039106454a50b16802030006211000901c40700c2089540035444061701809080300b60494000c00301440d140f2000111502a40241c10050710780403428217403009561544031000c002082801400c41034800d0f103800c01031011130a811501d010b0503a82c1c08854514280c40115619441150b04843e071045080d003c0d400c41c0c031024100b201918044d00c021040d503041c00c081c84100c4c11004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 289237383 1250 289236133 289236139
    0x327030210060501020a06090f0213020a030b0102240c16110f0303091315120b01031101020303100302060f0d050a0608010b01020d0e0904060e0604030e010f080103050312100b0403060e010605 84
    0xc5007001240e0300040e90441b007581c401c402090004141c20000075001d8107200103034004064410000c88060550f000700a042c4094408016041071007004a030340e40f2080c150711441010200150040c0d104400d1000c2e84501c20507022881e00c3c810103079080d0301d010072040c1120026010340c0c0441c054603113840b00041040c02500110300b025100c2c03000901c1451a401705940d0650741d42101c2c4038003801013201e2400b800d0001c00d03000c60341009182110070701c50244026181440704060400d1076600c04011030b4082c40c03041c003c11107424290340800141e0303806809821140501000000340390f90703060049600c00c250b0300b8000109686004500d60958000300b0ba000c0c11504a28100010642c111041d406400400d035042e83c803d640c1e61800340e00400c12108000030324401d0404100400d0f80c00300c07842d2442d407000e0380c418a0f07004e580c240c103030303101102804010913540040c0495040e11700300f5804103901245084203802110390720b00c06200c00d039100b80c10a45546482c0c03182d0002c001000d00840d03004250a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 289238633 1250 289237383 289237391
    0x60304170c0604060b120a11060417060a05060a05060433020c090105030f1509150f071107030201080f1e09030909011a09060d020408060117101a0609010327030210 72
    0xa90540c80d107c0d500c6000060400e14100703840b040648640064070003070403c5e0640c560450020708001ca60b01d0004880d40c122a50510b000103000e800e22082c2031003142d10251609081c6410808042c03000140d04c0c5010312054562001c034803001d03a4414440d806146140c020304211051201405036002050f0030060103680400d948030300d0a100041d8143c0d14520842c1d031030708a519106013507805c0c21144d50329180121403100074082c1410105214600a00c10381d1100e11100c820203080c1500c941a0384000380c049020701000a02c0c040c101400994411041c1c91007543c1604110755403070781a1402d0714107a1003944041000c6080d030500310708150141c560f038000d200c01c09100348031098035446070385811401102c003c02c2c000b50a80841d01034801500b1140c080e543d1a41c0c684104114800c00c044454189114082d4040c02d00030652040c1c004020a52a80c0351000000d0018010190700880006040664503040325003112041d08012090314210307101e920940c03030b25003002407074034628000c01c40b5080d00c0c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 289239883 1250 289238633 289238659
    0x405040c1103250602030c1c060605030c0304030e0306040c05040b0603090c010f02120315040b040b030a0201030509030c0601150206010501080702060103030804150c0210150f0302060304170c0604060b 88
    0xd0368400c800316110070302d03c030180703c400b0040f102e1460b01c0101164000b005129110422102401084880080e504038034109440380c0c80a4624038030604021400400104801305180c800450380140281490006030b034249010a10b4003c04a40994019022800c240300702e1500b0b0044849070081141d8035070540c1080564640c4400d805424503040c05006c60441501c107000b03212003c40c409407000010313200e20b0031159410508112815180c40b8600d810105a1180b82a1003020f954040140c01045002d606a00540041c03c01070250380061009110100c40505c0410055000e400e810004e5104842c1f802006842c100303068101c58188510001001400c5030b00044690459401d803030010074607142c6003000c0c0043c010400445400758104590342200980004500c030107081c1c500810040c20b0400f071010354044580340910300c000500140c0410242c64404061034109001d600580742d40345c0c0c00c103007049640d07114011221254002c9002c210600c200742c456950607000c151000e407080c1d28 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 289241133 1250 289239883 289239917
    0x212040803030c07020f030d02010c020706210b1504060914090403170c04031211070806160309050f1603140601060c022103030702030706151233020405040c 69
    0x8040103e80391010640d4425990b48014803040303a04c000d42500d50f001c0c8014002406405a00030b11000b40c0714504001500602c52000c000702807403d404200401010420000080c0030f0820a40354002e8407020030b090b0303120340701000b0702c001c00864844050307461a0169800e03100a103207001f14400e0007040108004a900444200907141104410794201da40d0017000e0794643c01a504040e000d05200413801c1300d0940c0000030500382d070101c071007207901070b0341d84204c8142c2d6007100b1961144007101c000c071801c0741c840c0030b5000261389610640542d02d200301030500700761500508a100940c840d00301402007090020103030300d811640c4807400c0a0400341d8109403001c0c1206180100081c01292914034011010f01019502e030301070501001030300d0b941e007071425000b9507a400c42d000c00d0b6030451410320300400d628541c000400c11030318100c40d4500d506070151588a203403039035003202d030181c5102c801c1071505058016445040320100c0c004016102c40c20320b000c1c08100c94030b01c01040240b200041c3c00740c13210b02e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 289242383 1250 289241133 289241137
    0x310140f01050301050d080c0106060306090506040e0c0f0111010507030219090308070b0c09040606030c181206230108030406091d0606090d050a060f230c030705040513050105010212040803 83
    0x80e0161207443d4000440c1c98400481e03c0323041e441180c2e0703510b445004118603916400a01c1110285030041c415615200100011559030090300e20282e840301c55400c0356400c207042050b0040505050100e04026040811425900202d40c0000020f500168003100d074070320450007a5800e091440c00401d1941160f41c0c0401610940101078158064500050048070750f035400c40d01c6404000d00144075031a0350b0f58010b40a4120100d101c00400d08000044000c0840008068120740c2c021154001540d4140c5500008103440300c40c6103115104250360318401a10180458024601c42d0010b6039205e00d0524002e0104c1c2c59500141014083d80703120122894203000704a4004004803100c1d070340c1d01a59000684004020740e00103240f406070059040074403001c1e80c040380024030300c40d034240104841c43c6242c40c1c0c0403560220b8182d0310031545000c944c482c200d84000d59845145414803d29007922003000400917505402060300b075644a50050005507810700010740100348401c00281001c4c10903450a40b24 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 289243633 1250 289242383 289242389
    0x90f070b041a04030f0506010521070311180124050c101a0d0309032102030d050601020106120f0c09110a0507050c12101103040b0a0914030310140f01050301 69
    0x2018002c2041001c240104503401143e00c51880303449201d00b4544030ba11020248101032044038100741650700800100080800303108510040d00019040da51402190641501c03400d0f0010308888181c48202c0300901c03003c1c00391443e44c2840c1e00f580741d44000c24110240d10001081004024020590900400141103442c1c41003e64042030030854415401c011180e480c82045d4041c040510307840926400a9071171040d28010814103510700094081944858201240000160b00030440d60141e901d895000c141c10400510010422965a01c0c0c04c407000c0c1d0803140c041c0d5450350304c5e14255040204440c650300091610302c1d010320000c01210b00040c818003401450500707100c000240681009414444080b121000030450340e0140442050307181da8142900400204600c0e0030030b00b41074130520500b92442030380d220040d000a0b41c0d41c1d801c250060040a4001c907085d1841c203803401368401e800e0020f188280c0142c44941e8400785004042441c4180d281c1d101070045d50b81c5d4400d003c40343d92000403a415 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 289244883 1250 289243633 289243649
    0xa11042003070c06020415110f0303071107090c050a08070c0222020903030a020a121d0607030203090d110102240a0b03030c07080607030b12100b030a0206030f090f070b04 75
    0x100d0761142003d58560740e9108005011520005012803203906031403000b411180c096030f1750f0341034007480410241d0b5020307007505409140d4020700c0041c0000344601101c1840c50364103400e4030070b55640d030742c0d084080e01e00144c005404220040b410240680d4403030f003290380c4001e1074607299611001c0340d008035100e00c2c20214125503400e2142c4080305101510340484914500250480355644000d134802501d507030703440c18202d038520880004180070328811105204211603c45004000180d55001c00001c1c0e07110305001c0b815030100707000401c8c0311342c0c602c140503400c84d001c1da000c003485c000b284000904202441403000c903c03103811141194103030000c0000b1903021450f2800060781c4506c003800203140d4040c804401002d40b10f82080459407200c04104039006080301d85051080c1821001001050003050700e107020b00340c0c0b121100d1154500c4a8008551420001c0c00b50b80202071503402240072030b84200c8550159216038000d11401003020080340403d0460780c40a0030700a410034038421300718851803182c10300c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 289246133 1250 289244883 289244887
    0x10c0b06010e090f010302270c0703141303020a051518010e0a0603060e0604020f1e0f0d02071e020901092327010b01051c0f0e0a110420 60
    0x30369026040c040b0094200505518251a1003142c0d000418400d00040303004441920004031f000482d07001c000914848003400841d05c2c1d89500400c1c0b0180c119003026010000440b08003400355980760018540c05050109000500381103005001c000b910701e43c8280d005031340300b0802070160402a402e8035403101403010700c40705d914a0000121800710700c0c6c804981d444000b0b0070b00000d1194060f400031040701c00c14501100b0f540c1c0d60324108000c0340601e40800403201d40c10050410f00e00601c00e082416114100c103c3c50502940f0000c0211340d400ca809120400740d0b00007103440521040d05400c00d1901b00b0f1302001c1426039415808a02c01c0c240611504202940388d042080f40c0945405010440c8801e0fa03500c12600c2c90b200c5685245c0304220b022038a810a01010510f913403c2043c01504480310040c3c460918010154201c10190040106400c4080740e580d065214000c11030700030301c00c0c41014000140403400d00e81c10616000e407600207506118902d411001c000700c090500a6044c03c18803e001c10b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 289247383 1250 289246133 289246141
    0x3031e011220040204060804030e0f1003090624140303040f0506030a090b040606062303010b0a090b1303021305090703030c03050d14011a0301080c0d021c0507061d010c0b 75
    0x10310311085400060f07400b40c0089004070b1500d40c441c0780303075203d90b02907991055040303900c00912000581000d21241c0002c803008030308003003a0181d00800c0480d48903200001d080091549010140781403c1e05c8503a4061441404115000c400c2030080c4145d4011005146043d2400d100e410418080d40b144500a10b0040002116180d05034401c940081d00b0100300c0c1e006141c40d1400ba001407049010f5100810300301c3c003141024034503505a0f505210380714800207203183d08000d0030740c140c0c0c2c1161301a142042084000407840303045540150a40c850a840d107074601904520400027120011000d42034240e01e01000c12070402c0c0c0000e54542103e1301414006004d04403414219202d20920300031102241c2003001a950010400f40264102d918141d0700340d2442c0007000f4079403050f01c42031140c510140c0c884000365500f441d040040c104924402042c046141c172038600c1c0b50440c1b841c1c140007a1000e0300100700030002c098000304c1c3e510110452010303244480d078003040060401c403a03651b0b0150500792414006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 289248633 1250 289247383 289247423
    0x1703010612141b040306020703050d050705360a0806100b0a020a1514041101121812110706030204050102010f060815040602040909080316090614071502030903031e0112 74
    0x650196410200540d500c40090602405078bd100840d01d05c515840d100000702100d2042060782c0c02e002c0010010406d44c151a101d84102c840c19a0755012411410207100d41d180d0b03a000f420034000c2c0f20f9640540308501d8030343e040342d1051203554024000300748c040080c00c0001e03501096491007150b200f4101e4403414024242d00d8014501d9450815018541d0000d010070b00041022103c1c00405c01d0340c8a00c1c82e6a01c01c016102600e17900450000022040c1040d040010500122000c034103445181c00d0441502141d851898054107911280100354001400d11465a0a000340d500b0030003840402d002e0240340400003640e8018000c108a22040703003001140400c4403e8040340c005011f400d60a11042502e410700c80e2242c0c1c800c2e5802007281c01c9003092079020342e0084a0010880320f0076102c441c0c60000621f070800c0c0d90340c80144c00300c1e140030052105819003003052010703601841600005646901d002e042107430304219035015100b0302e040d0400041060441c400028511150b00508900d4480f1400c0d100d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 289249883 1250 289248633 289248637
    0xf060d080a1e020307020f1e060913020f030a0501240f0306080d020c0103050f010e13290708180706210614091e04020411071703010612141b 62
    0x1500b044402030301d810095154004043c045141c0200c80f030410041c4141c0c01c1060401c9420040e9800304122002583e0a1038510060690500041d101e4241e500802c071100341241c0c800707401c000381c0c11004800d00841c20228410b10b4094600f0041070107840e2040f02040000b411080304200801c98645600c001561083e00590001c0c0000c0c011625400c40000b0065240d040241c0c0280c00030b840c000c00206e04c030a000c45454101c42224010032000e4845030180d582c1402940d900740c070740c481a000c8100411052070711405e503000748a601074209041034900240080c4000d080318260681c01070703020070704040200312a0100c49030303814a80c00c0b4640034a81c0f4610380c0a004441c100300303850400000b800e801043d04080001200711090b4115a030f800ca11218001c82c9400a0344e1000c1c1c181c4000740050505600c100c0030f441c0e40f02489428030150380d44101c141c1250052500d8030340e6022004000d030682155900310714400c110b205004014a61160100c4500c0c000c00004500c407c590002c0c2d001080942 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 289251133 1250 289249883 289249907
    0xe070203070b060f0d020901081c02070f0512151906080f06010509060a08060a0b0405061c0f03110a03020d0206060102070503060c07020d0804090b03120a0e09090106080a0f0b0f060d080a 82
    0x807e0682c0d039454024549038050300c00d01030010142849903813006480401c41c603044e1019104108141c03410903090100310384035400b070f02c101c5124002c0c0083c0541d5020f2000e43c070075150591104c0c0900e10326090034041d901e55501c554070039406503561040721a4042149415140c090b03415040640c0c0320400181010103540c8050300902940c0113116400495810050461409407000e00040c1c44101c0bd000200c00c140040c05920001c812520000854803101c0c0a80c4a000745000452070140c0300c034850409100030000c9015034030900d41d0104141d01882050b500003401d0020b858002d240002080d21040014507000e11200005408400c40d95034410103803101d6005400e05840d10f440307015010090840c1c200080c40380c030411121b141020202000c03903120240f581d4440e081400000d050116220740074100c60b0f01d40d502c603c030218104000300b04440d00e6034000c10054042c101e550601c4002c0c048090114036460050004002281c0c81d070244030741d4401c1e2302040aa1741d0f04040d9a0454012040403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 289252383 1250 289251133 289251139
    0x108040224070609140604081b24090d0302040f06030216050337050f03040609080c0321040506130f05061005040e010c090603020d0b030102070c0e070203070b060f0d02 74
    0x80b030740d80c080c040a0360000540d1407240460080401c0e00400e42c0380c0c0c6940c01c44009084007001c2103400c07503414520010102c141d07000003c0355400340400c1c0c81c2d56500f003000004203107a404006c00300100d64608110080421829040451419050904051140038240a25800c4c5900083c1426200700d01040f039140e45a00a403d41e40c442111150340210b80e0a85001c81d0b4980c0203208650500c47e5855140d50030b641e00c19182d6502d001c41c110030061058000901c11756030b403076031001c20602241518008000300f407002c1d0050340c7d072610f000c440703030080706890010700300c0c140d01071070030800007034000a441c0d504444080c80302480354030b070351402134001e10420f01d0090103030045109004e10007440030034850944d1000c860500c82420081401e03804c0740d00c4211a20001080548100701207400781d4010008004c070400c0c041203a0f090381d0b0229003680d1000c0350490340e000c0311220401c40702640541a07500030700b5510243d0318015071030700e9405100c0406401d040c800d540005c0c0d01d18080c2d44401c4100811a03000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 289253633 1250 289252383 289252387
    0xb01020309090109020304020306090d0509092503020a1103040806060d02120a05031b010b0906093301031503080d020912010e0604051c0203270a0b04030512090108040224 75
    0x20b4800d004c06034109480c100c1c020711442c00452841000810041120340060369010f085c0b143c40f4040110000f40541b40400348a8140b0045010510808a84c1c040b0a000e4030b016075100020300000b400c5941c98407100c0c003150000e11042c0305842c4041403c60704800708135040c0b0103402142c00040d4160940e081488114801c41601400700030011018000d0961300d681d00700010074041c4c1045080e40d901302c00841d480f10055001805529003810b15580140e0260103e0140104812180c91805842414003642e210412000400c0313607418002c041c50000c10300d00540180c1d10b950344201d068041c00c0c80005601d600440e462405440d81404111004805c01c02030000d0796412201540f58001a68250b07110700074a429041d00301070502c422110140310354001e500c0c1a200760280ba403009100c0018403407600031a180008199142c075000406080c0844505c0d99840c030750710340b41d4940104031030701d8800004140300020890b03804c4080194003031b4040d90140c02c0300d901c1c10701400401703c001c070008200c4000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 289254883 1250 289253633 289253639
    0x30a0c03060f081c2d020f19021009061e0507080f0a030f0506012a051c0210050f040f0303060302030303270105090d1b15051504050c09040b010203090901 68
    0x2602e403e24441401003006503041504003202e41c1d40011020754020144001c80040c00c20445c004440c21110fa0310650380170055003910b46040070305103001d5240c0c8c10b02c401d60107400c1d450803904045c1103c00d079050075000685041c03400b5000003c0c41060b03141d504203504034841101d0180c0c04440469900c0070145540328000703600a00260485d071243c400091400c030075000d074401548116030107184161035590742d1907106001c180480c1c45a002000724240180301701000a501040580701c40302188501158040510fa4001d14084514488541d000d041034140720301405408019a0002d400c04100740320b0b5a802d04090300540001d91000b5018400081003007000030403140d42d80c042d0860100240b20000c03a40d0f114a00b81d030400e030f803480e07115008401480041ca002e2400e0b01d103030f0500c0c00e0614291200945541c40c1a5840014034401c0c0c5480e0070030401102040345503180403110032501040300b400e140103265180e00600300f055010701c1e60380c152240680e000300305071030121000402940c103541e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 289256133 1250 289254883 289254899
    0x40609060305100f05060906040b040806090d02010b011704030302070b0901060f05040524030f0312061c03200f06130212060415020307030f0212091b0105030a0c03060f 74
    0x1003441898002071a00c2d001c50304041016003518112a400000540520300701020000654002e050007603110030704200004210354270101400007003c41d080585841d103400c0210794200400350507030008591400d1343c08129a0303000010f455050001d0b00400c04550744520b400e40082c0f2914001601c4950400c04000f071110054120f0b10a44601d460301841007a91a801c5c44144ca50503035507441c105005a080707400240351400b40800c3d0300b0000301118030340c0c0d06410645095030300c104d1040600785503035800c21000341841440180509402c00b440e4206510302d8070020700c00000414074202d11040098100641e40b010410b68406003803041c01d4915909060b40f400080c220080022800b075400f000041034080b42c00301d20544240d401071200b080e019900a1010b009600080c8000c06240c0d4441040c110b85809102038200c0942140240d05c00381424041d581c500209054800d070f550104c40c95840c02030360709c40d00b603d82110404070003207040180c401c0c050300980704940249001105610000603046 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 289257383 1250 289256133 289256147
    0x60d05060907170a080f0a030605061c06050a050609040f021b1011190e01020114010308090a0b04120b04140a0f0b0907030804030b130b0c18030a03171b0406 69
    0x120160f1040d1281c81c40d500d10b040d20b81e64030040151101d00d051204549846080000348202062440c000a29075207460015a080e00301e01100d428100080034420300110a0740f00c0e5201a00c401c07580300e40318600d0000011a6841070b44580c030701907910740844595502054054821f82e094194121808041c4285000e54824420b5402e50100e4201496100d0401b003400c1241d5840300c912140507a04101c180058910007407260116045650fa2840c0448100c0d0351200c0c140030314410b82a0316542d1425038200804c6200303540160000300d800700010410b84109440a05c100f640c812460629540d550600440780c0704000b40400440c0940303100c0200700303d0040340e0035965511030741160042d5258281d02c40d0f991101400000c050340420803040c4013013999089400c0c0e101d20a0750021100f040d840d561075805040a17100341c8140c0c4e9002c591001110211514416982d01c15401400d00f0052030f100201250500c680c0041c114140740085040c50752540e104107852200d141260f590350340c0e01c41d0014004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 289258633 1250 289257383 289257389
    0x1d01020307021f020309060f07020a0501020a05041d06011b141b0a0603060f060c21180b070816050307050102070803012c0c0c07081009060617070905060d05060907 72
    0x1950780001d1011000c401303100f40c90040b01490010318407035a074039002540303801c1c000d04118158810000d02e10f001030005d0005042c103800c0c907502c1c55141c0d1302d8043c4000c00241c0440e2143d44031510321003007158603640000ca6034003402001701c00c3c0e0074001003400d1810213905024445013160040e82002a4081031808500032044c4041d681604002d64038907084040717807000d001e0a0b00d00e50044008020780f6102c1d201c8401c40500a1880080c21750542ca9030307441c40540300c2565804540c2c8014101d4814495003a482c000f0003c012b4014075110041e40e0799000b0f807080302c468806080e1208102d1007441030400c266076049601100840d40c405080c18840b980d03800921605140c0c0e01e1240c480341d01d440302030b01c000d0300010141c09210f0150700c860ba851b20700d03604035024000c0389104036880025483c03000c102e001040c4640b8240084e46440314101001910800e1b003002480340741030300410000c0d40d00007c451046030076140d00014a5151000050040c09440c0c0b80640306d80316260501c0602c0c4004500d0b1012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 289259883 1250 289258633 289258663
    0x5011d0a2f09091b03120703030b040b19060201050a06080a080a0201151d0a09080912011112010306050a050601021504030e0a1e080d0c02011d03061f061b061d0102030702 75
    0x316040d0005c055a45164840c02c840c066070038440ba00009009070000920842d0040c0080ba01210410205408100305002100143d900e40f0082108580a100300364209207100700520030581000c4d040c4d9078411026070000c0c400f484c00a0b814800354030039806003407402c84813050303150b030a0341da025551344210020108100b200c88840100d01804000e00c0741c05907032640941c0307541c1041346080400001a5104007094071654880100f0504030820340018002040012000741305035045080802c212000105060001d03843c01c000c2c480b59a070001800c2d00024031800e4a0a0265941c0c60112141c1c0c40e0506001e030441051940030070708050540e0400051184150a242115650006181e541010f10a000c001c030b0038000c00c04000d54864031600449080c800143c010481005002c01e1418008036001d9901c000e44803003460340c40f48050194001801e41d46014041040b040035120a07010024000501e290703620344e5280d6001000c40404510450380340000c6407a450500d8010b0348500700f500180e40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 289261133 1250 289259883 289259923
    0x1b030e03090112020c0c03061f051e060a1803030c020316050f130b0904050114070801050a090e1f02030a061a0d020f0f040305011d0a2f0909 62
    0x4150280001511050300c8140d50303401207040014010b0340254005108554140502c20741884c4513201040700134083e403400e01c1481800034000004101c04c1d01d01350401481000034000d80c0382d10101c07040200c031070702c4400c07607203903a98421910081e10340b05c0c4098600617080d01c90032000801e02d90820720140c40603000b542a2407001c0c90f0b200d00000c560344213019031507100d03d461000406904190440701e40303050544000141940665001071020801214200c2e0660f46500c002040510f000201c603800c40b0060030244120b50512001600707501460003958100c65455140448074202040800c6d0f000d40b0315000c01300085107442c00c1c000a5801100c44d00d04003410248001040101513034145207480d45050340d40c1c1042c400342c200d00040e503c10707244115480d070305200c08103582824070014070003503100b4000080c40c1c121008000c11b110700d00c0c2c82c03d001250843c51420f000700d454403448000b44803a1014001a00c0c0d8950011846502c401140c580c01034044010403545400c0010014010f1000f030803070b11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 289262383 1250 289261133 289261151
    0x90b1b0901120c12110d0b06040806070503070903021c140304080a0b15120a020a050d0206070204200408151b0a0c02060702060c060a050c090a060c050102040305011b03 74
    0x85162080c0444180016001c01c1a2661800c069015182801013403508034200c120071129039040d0399900d050118814000a910f901c03505042c0300d50404a00280d076042d09052070b1a20154448600422540031311100100050500d4808d0010b04007841e8000c141e540c1e0101d000c00c0e0402c1004510f10200c94240c1e081c110030303440b081c002040e11b044400c50401003801c01140c1c0d5030070840040151030740f50071451082001c0429075801003009880a0346000510707000080c0d0042048034620b991007a401034150102413009610380c00e04440c6200d406840115001c4541544084090015100c4110801002c500401c040350041201543c004010206071400c0d02c03106c3c0288030104035140008040c0d6003c124048001d80103048031058540024030046c1020426000f044440d44901c1c415070b1240c10210810854000d01d1003110b80124504146a050080503000304440d401c090042d002072000c1d410340d1070100071003501103801650380300d8000d0081e100e241040840703048240b58403202284c1050524 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 289263633 1250 289262383 289262431
    0x21070512010b0102010f18140313082503030518031c0207090b0f101107030602040905220b01050d14150402130c080f04050c030f030307032304020603100306090b 71
    0x1001c20182010700012030100c00c0e90303c00010011240d40c08c2404c1c002481420028040803a0b15401065413401a000d860111b02c5545040c0c0e110038484543e980b410101400030070380c0f0105480c0c01c0c0c3e00b04410f08824030b41c04c10029103400741d080d84c08020141d035164107003055079011658104075034085100340f00c000e0441003041400c10010681a821505c030a16a202140c4030703c0190746c0258609041e501c04035102c2d203a03502a03a000d80c10402040c0d80311803c1c031046d01541c00386586082c121307910300000d00c480c0d9550110f01d403d040c41214401d01c00d603001c2505024120400d40051803110084407201c40e030110201c0c81e034070001c80d816840703010072049004075801c06011300001c80e52642e80c1d050303082d0303500302e0b22107a04c0d28003800640340b501c60b6500d0821170391806c0080fa04c4441c80040210b8891404c1e141c010103503080b00c0720301c2120741c072141e41ca01c008140b45051240c1169040314041e13100e42d00c0c5d00d100746034590141c2c00070f405181030014020a000344980c00c07600504602030600030074840c1d5420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 289264883 1250 289263633 289263641
    0x105040305091309120e010c0804060906120203090a15020f03010f061b0305041a0702030114010e01140a0515090d08070203150441011a03070521070512010b0102010f 73
    0x3170041c007040c000c40c243d0f071480341d540100d02010504103030a5010381600d400a05820a800040116110302c40c144100303904041022000d1602503010f5146190221138a5210910000006c0814019199521810801e43c0544010300d4251010544a41e5201c40344001d064151044001050b11500341c1652003003040340d00321140c1d41585610b0b1910385084c200741010140700d41440d080d500306008203c0181d4003030080154500c14940d28100c0f82d41032001302a02d119069000c41c2082001c85460502600c803000c0c074a08468040319407075030000700e94808141c02d00c10346260551040c050752140c42001907000c00b401500b8001c0d0100d9294084404207034501840a640280c0b82090700d82503849901c440c4184421418401002514004551000280d041d80400114500c030b944940c40072820401c800900381b80d070380044000b00781451a102c00b213001481c82c981e08200c0c0f544c84100c40111940c0400200c001440040d11060000c4051003156000300321498282c2e005500700340030f2441c41c48803030007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 289266133 1250 289264883 289264901
    0x60305040c0e06040b041112060a0632040b040906121707060b041a01080f040b0f0403050c030d060603050a0b03060114012304030b07140301120305070501050403050913 74
    0x44650303010303401c1a40545021100420f01c2d40d0080d00c44403000100c1e01c2e603014000016203408810390701d54040d2800d44103511030003004035004a000200c20000716601c100c2c070444485480e40301d030101c890080041c0440d114500c5030380500d28000240040c000b680180148100c3d001c1400800140703441b0071200000c1d2140305405045038542038804404038007910000c00c10148141000200c3d00c1040d00410143c03030300f00c505100c9800c2d08242c10000365070880c100a074840f081083c80d4186103455518499001c01c040d0a55070b20b142c4560020b8201400307801140c80c401500b00c1200d880c0c400030804c10000c0d200b01d00442001a0400300480d01c401c5040c041e017141d00308000c0c054070302682050800b00140d02c000b032004d030420030f990090001031240580200b1018403091841130b034a90540c10500f1050300050031000c2007181c50352600c480007001c2c46c10340741519001600c01d0103008603420200c5603400750040242c41d40d4030b050309210405401c400100111700080d02c005081c540e241c2460812a40514 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 289267383 1250 289266133 289266143
    0x50c060f07050f09060912010f180b1305100f0f1a0a061407020405090705011416031b12030e1b15030901140103050c04060f03051009060f0f1506030504 67
    0x2100004480c400c641c044e050104000e04440c1c14421007100056268101072280c04891355640351101c402409030052074003407001d100555032001e00d50b540c1c45200b40c0c3c0c020001c10400f0300303002c58481000400e104180c04c0040214041c48410a0b12504000801206100004072890a012500713001c08144105800fa00b0062000ca0f14034034121080d910403906424000410404009038001a43c0b41d2050070f023303019140080140905110000d0304100c00002c5416014101344280341a00d001128504895941840c2c18194a074420390510401384881d10001c1040b0290303c0c00722060383c0d00d80e00551525021204603004640603e0204d48101400f00c403564100c44445007124108006100941e000900c080c00055a84007840001401c002d081e00300f103602d44c02c022200c030002c1c6400d0081902400800c80c0c03951640d80341d65502c0c0d560b5003d8941c09400e080c0c544000324240502c0c1d90041d6684403060405200820590045800500840b48000803520a80c3c0c00070400d01d11901c24548a15401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 289268633 1250 289267383 289267387
    0x6020c0f0d06270c051008010e011401021513030e09012d0b03040f0303050f0c09100903050105010b090307080d1b11060f04090c0f0f0509030a080a050c060f0705 71
    0x41d15410060b01034108040c3c0c8080fa528000104401441450451140140291641c1078107050400a928144110050030040c640f0014008100c401c810507044810f5038040c0c007119203045c0010303400c0504032042004c1002840c001c20024540300700e44a942c561007a40c907403101c00781c05020408210f0f400c1c00345d203030013100d940d510362401900c4c1980d00b40d01540003424802c0b12680c3c0d62781c04409510440d4121a00b101c1c2e801c1d02e40c10160507010f56500b0041c6080f40405914101814101c01e0284401151140b2404600315046a000341d9550b0045e540000007880990b84405c1c07900c14591010000302d009100300c0c01300007004003000c07071107019406941ea81d840039070300d94140000444080341c40a88102184039200003442d521440144898843c10b03a0150b01e0f0392038440c0740000c6a843c07980100511003502407100030300c2c1d4001070061024a9600b00183c03514480c102007498035851000050002800043e412542a04140600305440c0c00201301e550640d54000581c81007101516154042242 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 289269883 1250 289268633 289268659
    0x1506080c0d150905101104051c120c03030e0f0f0d02060603070b030601050f0a02011b03021309020d110c0c090106020706020c100e1e09070c03050f0901050f0c060106020c0f 76
    0xa030f4102c2d80089000704c049a0030100e840000c2e41c00c4812a1030850000311000408008508008903000004440c1411103088142c158840c8c4003204030903c8290104176081e80b5443c2010b00903408003000070300c0c040441e02da041c560410181e81e009003d0b004003207441840d16520b036462001a0030b80c4650005005811a14a48400210303680c101030445814031000340a4024036210303220180c40740c07501c940c2c000301d5911402c101d082e054034a114403000405004010307100000048210440403248100c00050f941c00000c111000180281d000c0c000b40d0290004002442007800030300c44401d5641203903181081d0342d0300c0d0000d9903104d180744170350070168000c00012203c0e440d065484e8800040c140c145444100e1155000410ba030b5100340042100c2440751000c00354a050800445501502c103040500c078508070b540300900280180b24018602580011f42410107903c03480a40e01e40d04008001d003512001d4050340251140c6007402010014804c440d1003110301c2c41e001110240d0007074007034040010411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 289271133 1250 289269883 289269923
    0x9080a0f0201031a03100c2007141509010c0303020d0609050105040b030706020a080307020c10022b200a0b0403081501030606080a05070c0c15110a170a0207031506080c0d 75
    0x5440c4100900c00802440500380a20020001e50a08c00070b0107404454202709100940e40c07086604940900b2010000800300c20f585c8044804404090030046614121031070110060712a00c2c89100700c040c10030304001205032482e04518103aa0045030144201404c80c0103040d40c1c0c144510a0600591280300587c0200344194000c60b0400c45500c103950b042c100384030120304581c881c0100c034001648612102200d50701804081d43c0c0d124404400c0d81d64555241400510804101c041ba00450554240e01c01011808001d41c40744607500c444400c02d54905420090185c040884000340e4146115014101d10340c440e01c920300565a040e01c49010030786409200c0380c000c0c0b00007003001044c0000c5418100c0402d4892085100070030360101c0380004400c0d074100081080c0342050380e442d65584481c42a0001405524045010350015000c00f621050040b00c100e00d0108241c1c03000d448982c2c02c0841c140000a642c00075401d07100450221080100c1a10502035030005018015114540d50311850344518 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 289272383 1250 289271133 289271141
    0x305031909060203011d06010c030806120703050607110f120301060e040f0e010e010f0e1504082503081f03020906030106090212100503030a020d050a09080a0f0201031a0310 76
    0x250140002980080c55840394100e900a0b00001d04266400490886d038100344101143c3c0500c003032038500586d885644d00034201c0c4001508075449510025044041148104000c0c0c00843d045400c035486401c192401519550070070b400c940850150301154a60f149000a0854100c00345c040d104e880d5a203011000c41d0030100b41502294890740360843c440c2d465256008166403c1d04000000032107609402055003113031604007105074800c1c00c002c0708240f1580d02150410040c41d12244040761582c4914007580e030303407003211401e01c1910007808034604400c0407020700b880780c075109464050040e2a05501c4020714408038030b800b11806601c0200f4801414448801600704030040c001240b0f40f5241d602041c00c0e42c01414408003510400c01c1001b1600ca401c1c41250010310040d400386150003403210000b500d0780c80c0350000000b400400a00702074040e1090590000810001050794042c1d40c5520300b90b5588006420140d000a0610100c040e083d41807001d000c9140c40d00500420300041c030320016101038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 289273633 1250 289272383 289272421
    0x2a090103051906020d02070b0f150901051c0b0403050405041a0d0f05072c1302130b010c120c05120307050d150b031e0114090601030e0c061309060909030503 69
    0xb41d005d200d021030042d00d40c009004860f10403034075140c945c075069803a40404a0000c00300c04203420440d01c520400e4884601042c10349109a4060880b1600b031070000c103901d01c0c2c015001707014840900400040c15401005001070751800c48081c40781803005030f094080c003110b10403a03940c0003503a508502c0c001100380000d402028402c00030384020942d6100a034102d68051054040301c800a9184209400700140c1e20561040e40c3e0700c00c1c40d503408816008600b1080d040c404401c1c1071541c541c0c0268250303014804c03098090354024016040000c10b5840104004040c10b4200e506200c0c5407541840911030354156880b40d4101d030ba0321802c0c40000071030440a800002400184a040c5200c0403440c420120002c501c40c000c2d503080084c22070080c514408036400160722544403a000b82c02255481c0e80c441000e55080b08003440d0200b0031040d100030f194240542188115842440000c12088062138451100201c9110072810407005030364240c11800d40301c015a00500103002000060185100c0c0b003507903540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 289274883 1250 289273633 289273643
    0x70c1e0501150b09151602120c0402030c09011d0f04022802030a0f020613110609040c0914190905220c030c0501030b150c0a052a0901030519 62
    0x2a08542e4070001d1a924280c0c1001c16240400102d40c000350811043c148650750079840011703d803905466108500d1040702000074402c0301000700c036816807030040161070710f0b5100080003150703a030900f29421121035110101d160f0101d010300000140c40785644000341d0007500e026000304040299001004025440452500b07400040d814600c0d0b070010700310118040c0d0780e07900e0f001150b0700d030344c14a40a07101804000c540411503001c1420040b901104050501110390300004c0d1040b0201480c001944030b020309144070380c00c917151020007809242d1000d241c0c012244c1c01c481100300a94501c043c450b46c14030140c181032142040707100c104000d4038503900c090b40c03085896130f0301042d51b0301403546803038081014482a10540c0c400f14050041c8004c0394404402802e09007010419000d542010803000d0008501c988001c000c00328003d160400280280c2400b140d01078240c030080040140207244500d070300d440da0003018089424801c10b0703080080000d0306990b0403500811204403c1c03489000258500784044032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 289276133 1250 289274883 289274891
    0x14090112050702070f0329090a110111100510140d12020c0603090a0c050604140d030203131211040e1c0519030e010b031207030e04020c030a0503040b070c1e0501 71
    0x152001c001c0c401c44040c0d1f2003425440c102074100c00c032000115542209015030440003405203c8056000581040c071a5070188090701f031055024016190510140b000342018001c1e071410f0b41c948410303030780101c2c4603846d140b8031241290b864601c4c1c00182022042c1d45600107429084d03070b00101d12014421210310341a4811036468a01c0e98000c02c009400960b107a020543c020504001007011340c2c040c590140006541e554201864400030002c07000c4c1c40c10040c0d004030550381199080c18428402c507001d592103c3c0024007681d503110341d803c0705416100001c1e10369104000810ba910b00c0c041c0203203480c00d5000e4008004a10f2500041901150324a19142c00e10904100e0081011b407241986040015161400100010002d040f142900c0300001554800d402204000200102840940e00d60340d8140c40c048940355084004500244214142140c0754070010604001d0300354810000c52007103101c0c1180c913102d41c94250007501c50414000d001407400003c1c14201b28000c0c00342920701c4401d8002c10000ca = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 289277383 1250 289276133 289276139
    0x9020306190305031b0d0c020105030714210a02280203040312050306040c020601060f110c032e09020904150f060f0503240a110c0303070801061409011205070207 71
    0x24854070542c1c1c001c85041e040070512600d12410890600c10201200300500078864600703100030554014054000e05004010000c201000e11a500480d0b4080215030303469600d050010000c4a8154a0107580e01c159070800001a0700e52558000d80d0020581e80281e0301041c41d11100b100e505400d410740410851105100010100c0d139851402d0307110015079150182c1c1c904000e0280400d4500300801c40043d5032082004001190740030403950003c2d8821b2604a0070380c41c075608414103111004880da90301d442604191084201c86900541c011100032080d0b40720860b00142001c1070342c0b1a004065801105400000e010500103c20b003c040074a001d0700142a144642e21402200c07455040040c030620b04260600c5107090400225040b60103010440285d000c010b080003e240708000c20340b511045d2640d0b490138000121000350b0b083d0001003000d50b520391902c1c54008001e504244603820005046400085241d0134803000c8801814041c4e6620f02800c08069000c0094407024050707a0452292202c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 289278633 1250 289277383 289277419
    0x3030f1205151507030f080a060803040305030d0506030f07050d0215070b090613020a1a0f0d150b12040308061f08010302090606131202060f040b130b0901020709020306 74
    0x41c0c1e200e103040301c00d41d280805003002840008005081c481901078020440440441e4000741441120003092405100e16a01e4402e1070010781400c1d400300d0300070712011601008200022001e8492803803c160100502d50b203450415540b118000b0340d10071643c010940902c01030810b500d405842e07600142004589a41c050311201280e417201b20b081d2120340501040c454030741c4044c08550b402200b1502d095601c0000c0340c00040100f0320302d00c0703149800c0ca080c030f0b50303000840900750544000211641d015038507603015074045000b41c0040039148400e41c0c0c2d05500810441d003034000f83c5032010901d01c880781441d90f03a594107441044025214a030f005480100301103074405000a01040c5407806d5842c410385500d14270602500c00c0015125912860f400e00c5070b4000c0c620102e003110101e036169116a4030785030050020844911554010388403e60740043c0102d0b68801c1c0340003c04440b2134000c19030103042d0b0b03620042540c600030300450b240143c00c142c00c100402e03c0e40c0d4000d10740040303000345001e201007104006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 289279883 1250 289278633 289278641
    0x1103040f0b07030305092a0d0b0c071703010e180f1f05060904020d022101051008190c05101407030f14190804141608010c110703030f12 60
    0x7200298007800036007002090f40c0750140c01e8210204a0050650900d104d100400d0900e2040610b0f2031507020400d452920f91743c000e03020002580094a00c20107080843d29599030343e20106c015921144101401e030141328200c1d048074100d440c100600070783c989464400c90054200e41c40310041ea442205210000b80906120074021a604000ca00582580c0c05410000b601c5004180c82d11819100040201607158450350b034174950703030454009a0f48220340000000440d41c41d02502d0582d8a0030b0b003005030450b814002003060b5041d1104490000e890154171160000001a00924440a54904001b2402c102509031402d520303908001c48040f2002c03941500c2a0002d000603000501040320041410303800160f0007040300121642946000345000b86a0300c0d1110711440401000722040018040c00103c0000d8441e200006080d6420000240d98041302c07802e05004a81c56540303402c3d2120302c15030003019440161061341000c0c000c2e4600d151010b0b507144a00e056000207001c0c1128442d601840a032003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 289281133 1250 289279883 289279889
    0x603141b0112150b0a0207050d050c060307020a0b010909020a080105060a06110708101b0c0c0317040e16110c0109050f041103010806160f021504080f0c011a0f060301061103040f 78
    0x90045c0c40e0045444024681a02e903400035001e03e2082110402090001c40c840e803069105698450384c0f5202d8a000324502440040c000c0c05800000380045000410fa4224940c210b0003104e41e01403240d21002d10341d080391015200d02d13038440c0501404108403805103242c820405030031400d40e4146070347c0d02540c2c0d003040b001d01c407007649065541d10301104030006000030340e04444207486c21217840c2899580d244c411410500015209000305a80b00820344018400c6a018081c500daa4180034204010100c00c01b601c0c0740301440106141544840c00180005104448410165651700c0c00a01e00f809000d05e19520203080c03500161140120005404148011802401400014181441e242d01e11039088500309651030100800c0780c1c07241030700560008000d0900800c01d0f0b903506490700c2e103150505051240000740180c060020404031030014044d1f0000501120003154034001680d41010005814070741982c1380d17400300e001d10061000c00d10481c8100b210740c4400c01107a240c00c2c3c60b14081c0f00c108800340c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 289282383 1250 289281133 289281149
    0xa090c080f06090105090c150d0f0212090d0e030a060504150c110d050406080705090d0b160e040216080705010204051905030f06090c010c1a0103060603141b011215 72
    0x2c2441081042485000d0340140000f003c0c007060030003c40020b840220100c020f0805c4c041c0894686109207284d0f1100e411840b800b44110340d01d08071110308000ca000d0480d030307003540707802883c002c0c2c45031500544d85ea400d0076000a0180c009610182d84103401440060015550201030310445000d400e000d11441030007402940701e10440f203034018104d500d090500303c01c1004125003031200f00b0050b070300003501603000510389c10004c0d00ca5001c44041031100c81210009407942e8030503c00d1002c0c0542032800c200034a4806d0742c0d0400f0074a0b850040c0816481070406515602c0000079110000c25503003030250085034401c40c0090325180d61a030004e41044184c3c00a00c10a011354081000b0600d410484100e891814101529040c030f0218042e0b5140c2070801d204906010343c4111210400020b6841c08009407000384080d00036513140c2c01c0a000415450004454800030580030305c5c224070002400440424450000146140c5040300446840318405504c81a1503220724403044d00260f0030403410003400d002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 289283633 1250 289282383 289282393
    0xc060905010b0310020a1b14121305030304051f14070b0a0507031506050c011e020a030b0d05030403060b040b030a030f1d0d020d03090816050906090f0a090c080f 71
    0x30209418024001100c244245c4100503030001c450300814038002d8926204118072443c0f55604040c107a4a000441424850003420b0452a40186220181c03038040a03030704590458030345500503d0342d00d11032402041d500080504504c0c0b11707284500200e040400ca40d107000001480c0320078001e44d80d600805012520121000c3c10450b2080591083d40d0340220545410720881817000b01004403000d0038002c074410880002640442c10b202500162038030080d2000f1030b65a566111510002034100c0c40e030060004c1d0030000c2001040c0740406010003415001700285107098a5651250000d0041e0f00c1c2154100c0c2d204c20031900703580da0a00081610501030b490f181c0f85442e00490081040d200607821070071041160381c8080341911540200d200640e816a040e000c10009400d0648521845070b2100c40706101d00c000300300ca10049440c00b0001c4408c181d1303045030741e138449508000030010304581e101080604080020381030480c0350460300f0014094212020743d26198050326081102c1c00e148001c2c1940a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 289284883 1250 289283633 289283651
    0x4051c0303270b091c0201060e010f0323390405090c01030f02070203012409020301063f021e0301030206070221031c0c081b0a0c06090501 61
    0x340c010352541402c0d8180c01100100208258041c40304000005807014900c031000500d0756100b00030b0380709074601d051210210310303031a054000c2c041e20300c2c0e01034601640c041000000f8040d084044010507070340d100035078008a01c10b00755090b4400c035241e1010221441745800030080c90340000110000c0980b1551a103034010400110b450340e5482c1031200381e00492511040000c07004c030100782a80b41210919010803550710301c0a00f0350282c091520007035455460540e0031040803285524902c16079400d80780d0b00c5040740e0751325280c8040380030900c1f44502103003020a01d00051014907000794201074803010b40c000b100d141c5181240200400743c5000152030fa0024012042c81d015002c900c03804606d2040700c078a19810b580c08941d0078040c1450081c001ca0418201881d20130807514014000142c110403651544e030f4441c1e0b07860130359154411600d0100c2c038260700d455600c0d20410940e4451a190355055118210f0b01d04140c4040e4019241c240400c609007505900040950085d10005800342d400030840c0342c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 289286133 1250 289284883 289284887
    0x213020a08090705031002210115080a140c280801081608030a03090c090c020a11011b02060f09060f0c120307080c0703050c01091a181506030304051c03 67
    0xc07010703018180a5000e450b00304031030340d000503030000100c019070b90260711410505a8041c0c0c804080362041055606032001042a008420130030380350101c643d0342c881103516203448240807034140b0b020908508400034000b507000d0305104001c142c200502800a01c440742001d2140040c20080200b4100280c908001000f07018010000e041a125030345501f000110304e0138071817a54070310650004205164440d21000c2c00d000e1260341290003844505018880c823103144c4c000030b4403101c0441c0200d40b0ba02c036007004042103511414040b40603200c0701ca00085c0780c0e4900e4003041080e40141600e0a0321544c20000b4240c03c1e11004003405419000c0110f064407452040d0005040c10140340c00d96402c00c0b0b0601c2005802076208281c0c942000b240b004c100c1d694686170030112210720036544103648640c01c1c005080100b00c0c00c0f2801500c02110150708081c1900d50050790b0001500c03551800312103a000c0c00071350f0bc0c0004a0440c550300148002c089901d442c0d55040454440040003882017005000c041c2c14005143e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 289287383 1250 289286133 289286147
    0x31305060f10050301020c031e1b010f1b0e01180f0305030415020f060406020c070e010b0304020f04020408030d0f06031a091c05070609050723041a0d17070213020a 72
    0xb42c04c80003076003000354042c44160340f805600303080400107092079030145c003141c01c080456100a09060100e00301c2e040c0c4524040c06849042e841d41c0b00f00341380c030b451034591381d004114581001100303075110a44130020000454907110f84a00129a9280503a07001aa401e40905030400442c03140c8059038131a4502156040103040f4003080c2d405542003043c807130454900100c0c0565010b80d000100503141e010700c83c20989042c10b2a0446036815482c400042084042c9a002d07511652007200c07192a6020503c00f4002a80520310a4001552080c40103030070b6001a5000740160782c0c580080003d0b00e580d03903101d4440a104109584104048600170310071303103000600202d0502203000841542103104034200610700d11400e0340162a00e40d461000b001084814000c0800a0080301c3e041541d140c649080340c0400d0062446440c45185050001c0c05038024034280c000c1c031010000c1602e819504141c40e030a6220000045500004404000c0400188e45040d48440408840400140c5521058101810403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 289288633 1250 289287383 289287389
    0xa240303020c060c0a0f151d010e0a021309020619050a080a140c0a1b0c0617150907021f0b0906091312050d0207080c011508030906031305060f10 64
    0x300000c1002103581c3c130340043c500b401c0c02c4d40040490203805842c2400150390306600d12a03400c0a0901034042d004100000c810031a070b10480000704070164040e0070075943d030340707880c0320081d00105415041c1c2d199003129807101c0c100030300261a9a02c1c2143c1c0b044c5003000f03840c17014120404118081a01c41c03480c0d51007260280d100e000d1860403c100d4840e000d403203400c07150080544070542c1000840040c1180700c1c680710102800110a50803004c400da00d08035807558903030b0045400103003013601c0205480d65070000b094022807075804200c1080c17501d04180095440c00038221001c3d031055800c10014100700104070302d08994800d20003d0003141e230360300300700c4902ca0141c60035124501180c28400d66242c2d84462018455200200902240070440b00b030364140078400301481d90f035101240110a000f040001095034007402002009505400619030751780c0c174120b00404165500030b2103c18502d042c40340046800141c000e14580c0403042982d50949006012a06a002402030000703019984402842d91000707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 289289883 1250 289288633 289288639
    0x6130b010e01030c030f0330050c04180e070f03030815060304031b0309050d030917010c020d050a0302120a0903020d02030913090809030601150e03030a14030a240303020c 75
    0x10b5450740c2ca481404010b2400090405012000ba8804060081140302e01c480700380039402c01c254800340c900076800e481140d0a001d400f42094001120401100c00711015100c502c80b0159203188007042500080406281121a03442414000304411307035400c02201c029031080d40d6010440ca41080d4600d040e0300c100070070300e00550050040c0000250001c01c0c0c220300a40c3c43c90301c4040c119203424211400d0129134055034014408014007005e00d680901c11343d0980d04542d4000403841264035009080701e05c0340c0001c41c01038000c2a080100640700342d005040d00101d6150250038200b0100e10310b14074540680700240c5041c3d4429001040640500040c400010075001450900d00b0541c04036104603000046c501c101d40c3c0e01e001c650100819103058905228000d0200c0b14250303150405003011049140c0d000c40407542d44901c100c00380c503002027210000c420b03550302c640380da40c0840603100381c5070000303850807070340316103916240f001765403440232100c1400e0240d1102c13043c45255040181c01d00120741c1c11180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 289291133 1250 289289883 289289909
    0x3092104050904080304170f0c07050901031119050301110414030705062b0c020c0a15020a03080601030e0f030901090b04050607080a0c060212010f0602031810030b0306130b01 77
    0xc5141d0b18555010707031080c0c100040c1380d529a00e9250810340e103a20051910b4030490003042c502c200380f03020006803088010210031200301c69100d4041080f501c1c000d110091914081c2c0e2045c11842c1401e40c880705800c502c01403501921034940300000e081d0745a11845c01d09803031021404102040b4800b030188880c20044d00902981410400410094440c100005041580c076a000485645c4580207202441c08264005c0116900d0000025240c0044559040c4900e201460101d0080b410720344903d140390050b001021401d1a42e6010f0761150710080c5202d05166860020840030001400464418102c22000d19a01c10b01e030170015261032110340006a264600380024880b80d00c4900c11204602d8200d00315544403440b07400c08540e035410b000f00080481c0d001050043d03441c00c40c000154141d80d0700341d54481c461070b10f498003280c0d41d004002d1000088801c081d00d0404600b0071815100c61541c3c2c918000c00c4503240c800119151080988028022858844010342400750b03d03842e05016050100503d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 289292383 1250 289291133 289291139
    0x160605010b0901143c07080904060501020706050304122105070318050304090f0207150b0102061b1803070b0a080f010510052205040513050105061c0b190203092104 72
    0x45c2030b11a46050b041c1506441114442000043c00c0c60260301240c0316903504420301e4a0b40e641d40000c50b01034000c40c00d14002046a43c00812640c081d62415624142035030394035140c40c05107003140c91500e0207002c1d5036904400192541ba107400c12100741d0001c003003030505008400804680c000d08040b038489814500c1c08000074000b2084804880e40098041032021001c04250b0013441a844010001c00380c0358101b201d8111035401181001c40c00340c0030307141c50343d1b02c500341920780000c0340c0080b9203029410002d4000000f0010010640702801a04072161603031680d0301000750303600c070b5079800020603404000c0043d42c1441c01e04d42400743c20b041c0c8801019840c01031024000b800340c0406800d1744c00180d010940030160003000c410080000038028065420484065012000c4000056070f85509020000d005428641459036030111003401c500183c05441c0c8803030560750809054003041c10210f039004130803190503001841c090384030080074049010900c214482c01d01c0c440c0108424400d0b080c0300070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 289293633 1250 289292383 289292407
    0x30a080f060d1403040510020f0606180109020703120507030e120a0807051602060d090209150a0b0702031609050f0a09110609010315151116030206160605010b090114 73
    0x240e540d40e944182100d2500f03500302070b25420360007142c201c150880d0310454196143e543c0018480c2c4200007010a44400b5241d000a103c4100591450420050f030000010046115658000e0002c1d03030007032070b0410322200420107002c1503600c02d603aa0400207480e0b0030400015002800039200d9584400c00d528980401c543e8040c00c400e000425140600c100030890b885450000d206040203203074000c0585a0721200178039040003c0140d43c2c03041e40507400100002c0d80d161842401001800303001844038083d00d01c1c2117401f0700c140d40145030032070b010300960500c0018140325002e40000703080c00c0746000c5403624080030f25048403007004020204407400c0440703c01c0441d00c80034000280750410746020b0ba94102040058018040d152084c8a011400c243c0c00903207455030b60180250b540b100d0341d6555005005800e910742d11031003980c03000c0c0b02c507040d02d10400c010301d0600d0003002e032020240d5860100d184a40c940c9012103d09138014400140001860813883da80300f08552490308030f9541d5203080c00c50040074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 289294883 1250 289293633 289293649
    0x91802090a020307110a03020616030203060a030803060420030f0c03040309030605040f0b04110f041406040f111b010b1c020111014703061f0314030a080f06 69
    0x70300d0012640000816402481007422002c16401801111100ca800f85030003035517560100d403030b040520100110030b02260f20a00841c2d0003a07030010440040c050560710b41600983c0b001d80001d0b800703642c1e05424001580c0601d08507840c103480070812501c82c41c0071442c40c900117100801041e40f1b00000c20030000002d4010000c002900d810400019440c0c0e1180790031410890804805000203440d07808010400c10b000c084600480019203402d82e1881010040c00161010f5448801c094504100028060b08007544101d610b02100360340803803a1030001201403036641c4800b000d00c0344900801880c03006103d00f4000c04482c54000e46020f011070310500d0a00c030801131042c50007410801c0300a20103201002c04d41003014030300180c5d16100e401d040a2640301d440076402480803c080800c0980043d050340c030202c1d45a10741480a4051310240e517a02c1e00f090310a003d01c0400c502138500d1040c0200c04999142603160519407202c004550b540e50010f00034103500f900610a2023042030030b00401c503964031500c030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 289296133 1250 289294883 289294891
    0x1080d0c120516080d0b030616031a2206050108160f0c06051501081602070e130b070512090706020c01050c010204080f06010501120606080411030a050706050409180209 74
    0x540d1a1948622001c100c500e0300c54070034401c000400d07078480c1c0d03c18042c000c4004d14001c03014074010007014210380b0501d600c0d810202d8a000c1400c401c0104844200d020380c01984807130024080710034100d101103000803041d0701c00c10340c40e070040c0000d000e020341d0b0107009104810241009003043c54552800019a500c02c1d41002d185404025541c2007841c0000c0c0210b542c04074031a4800d02c180400c0c50000d444030700c0300300d40440700d03800100160301041c130013000c984c41c41c2d0100b00b49501030b040090400d02c0c419200340f005854070840c0d03420000c00348040344000d001e041c0102c50a60303c10f42d90b040603821601c007007070029044401030b41200000b04809600060f0b05840c0020a080c9a61a400c003158841c1c0203004d540e1111842c1d015407484102070311004600700e410b0760002d0b26112088282400d0000445440e40200d1b400b055a610214021509039440341c0642d43c1d00030b048840f821000c2e5141c504240c0305070f10400118101003014040340300c1500a01182042210140340100003c2d0005244058090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 289297383 1250 289296133 289296143
    0xf130c0302010e010c06111c0b03030304060b0a0905090114071107180207050105010308090306101d0604020403120c0507060c02090402150403080301030f02012a0201120b03010905070e01080d0c 85
    0x8444402c0c03640217040c4420715035000541004034403528401840558044848031408450031511030ba030b5052070344944e1249882c040c000314290b641c1c950b5500020903503082e2117a1b204c8420b402c0041c80c03860034060742c0d22030b0124500101d5a40d141d5075145441107400f030801000d03c401c00100341d041080c00a074401c22a801d64046010311035640050100034071601c90301912650078400003000b40301d8104002c01c039002c016030445641e56a00c9250000da2102e0340259540681d41000081c012500020807540000004000510f00303680d0795200c50425092851311404600042030840c140700c2e0622151000b001d090404071045613150b40041c0000360020802407184201c604004090114a01580c0185500c841403695a5841e4142040c5054070160b00302d001500380f56543e840c02c014030141c005481c018030391350101c15100380d00540e18034494001c2004d0040e9030700760440c0c2ca5a42409100d240314010009450401e040034400c04801c2e005801010160f4081c400904e20b4950100044010729009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 289298633 1250 289297383 289297397
    0x3030506010e03030a0507050c0d05030a050705030d050103050f07060926010b12030d0b0a1a0304142508010203070504060f111b13051b07051e060f130c030201 70
    0x100040e00d07011140801c590b010304c00803035603400305134201000b002010300800c12541406484402c0010014408800400e83c4c0c00500c920703035481d80541c0c09469082d21941c1520704182c218180c04089036001d0348284c4540d80070b0000000750315000e00c003c0d4068610341c43d00025050400100d0301100780c5146410ba4040440b000900405c1400e510081c0301140042403900d103031404c00001d6940341c0020910a80491515803041c900e8038000711000e04880f1140c012041418182c0030080709508003c00c00c1d0341e81c070889400d0707014141c4107001c9021900403400e4061040003211303411455107600c50300002220b0380f040061200c0c0b01c2d04074007035808943e030720f280c240046112040c007114941c080c00d10b86402445120200c6441580d42d1080350851041500c40720b03da00d502e5000b00c403e4031020303500c0020100c5c08206075400d0484401c000d045550241d03040b222416400c20060308001142d030252041e84d00103000380030102c0c8050b482150084040300042c120940292a00c0045104606c0024184981 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 289299883 1250 289298633 289298641
    0x2250314010e1b0112020a200f0a0206030a180503030702010f150e0903130e04060f290303091206060f0102060103030207050613180c09080304032303070b0709050a0f050d030305 78
    0x10136a8080c00000c60004195110040400068040c078905208039004c103218208c0d00040d07072000281e00d005c1181038001440c1e40d052640038011280d001602c00e842840e10b41441000080103031000c4a2102c0c0305100950750b03440e154000030308440200050050351420113038104054010800c822095415140c901410742d00d91411b014a144990500c1c40c0e07082c0c514490000703c5e0700d10742c02d000344030b14000d120a0201d150402188012284004242005682086940c0002c0519180c64501c0c0d2480030742100c0c6072001d65000078000c0d034210500f03c21154024410081a0f04104004075214503082c001441c03d0750459030003035110080790080b0303809802d0110b40300303043c15480c5a4150040c81418109400c5007a10796058001d02018404807011480c480c900241041000085400f00d81d080a1080c20501303800225410002c3e030500d408203688024400800424951464580500d0094031184042442c00707041c0080c018155200710b02d03d9088d04010865a1034021403034000c958103140004299503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 289301133 1250 289299883 289299887
    0x20303030a0b0d1e0308061815010504080f03070c0e19050703020702040c180e010f060c0501020d021c0b03010507080414010e0303090d030e030906041502250314010e1b01 75
    0x190b02c0343d024081c05541484014500e004a00a4142d14001d54610701c0710ba4402c2c06005d0901d1002c0c24064409002070b0010300d40038080004850400d0051602d01d1816075100b02c51072030312907001c58000481e04006043c03802c00585001c00002041c40b03440c052043d00d4000d101c0c54031a01d03110400d124064545000601640c820b504650390264014400c00200074100d070300904201d804e0310045100000b19034080340c04100114000d04840c103040301c4003003007810400201c1c0c000d03120302000c403080c0d134003480261080e00c20743c0042c2001443d880f01d4aa413804039100400140c8031078050180c080e9242a007400035075540300305055441134201b284c01c580d00c80c0e540c10050051058100c109901d020200900107054004108101c0c00001e642e02480440010340d407164480c802c204615602020401007044103c80c4a1000c0e0008402030040c0c0720001401e40c014030001161400740c3d154161904400d108200140380007460400401000708141901d103c1003a0f50340a482170360b02820103200b60700e034003180c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 289302383 1250 289301133 289301149
    0x5030616080619080615030d03050103170703090815100f080c060903030c0709020307030c091214070909120306120b01050f0f0607060b0f06030c0a030f02040305010c090608070c020303030a0b 84
    0x131003048500f1881d0807281c6400d15500624468440e0107480300c2c0010040c400d0094606882e08103040c40980e000c40c03038240445034486a42201400034248d000501d1720f40520034000050760544690103103160021511307440503100d800c44084542c1c402c1090002c01000180b94000840941e641d9036184490400649140205541c8a40501c211030340860000708030340182d03001c1d50710340c0c409000c80341100c0301c00d45280005000701d0314401203c03d00403011480c0c111050554000d8501076071062904c540070308081e90408441034540304002c42c5000d240c0d81c5e040c400c110090810550610750b0b000a03642c0c0308142030040c440c030b601c43c004050b01140280e50322114500c034070b0001030a40b66a02c0a03440e0a00c043c0460040043c0b0580101441c810582808030840303104008415045107400f4504000b0303001446d2102e00060f80070781c00d00010001400034803884c0c0d200c4245454141ca05450200c009140c2440242640200200034a40c140141c40020a40c0c6d00500751020216008008d03402081c1c2d45 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 289303633 1250 289302383 289302389
    0x902060702040f06090e070305191b06110633031006030303061a04030b240604080303041209060e0d0f1a010303030b0303130e06210705030616080619 66
    0x1161800c840d0403e16452948030300c048a03500c1105000340c90561042d01c4d00d45446d440003402c5074203d203040c0c802156040000c032840038400c2400b01d619102e1002052018600ca420002c08070f2a8404000c90800c0300308150b40e401401a1405150b08014211403805142850b00c07007500002a254491040e5400303100300004100e80790402c01c140c56603418010050840d501c907a0565010104c0f4031200c0c00e001d0703800c407420740e60020030001040d180c00905604a90051161010302d2040450201250341c450000f0001418488015500d0b41000e0800c01c0e15440c1705600d400601000c15810803409403c030719020160070086031954003141c01801c007000043d0210100509040348800c05511034400301e103020341030300d01981c1c04100106002f401d01d41d036407094042c00407030310410803010402c02d40005060382d406480a0454281c4501044d92070020300180c840c400d91071707007040c0800d001500b010480380745d00c5500c0c01c3b90b5140c03084800d00040c0508201070407460080b511610039005003565040c688c402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 289304883 1250 289303633 289303639
    0xc180e010e0c010e0906010c14030f04031109100807090e0c15040303020615090a050403030b0d050c010e061c051b040b0d06050910090b010e0604080703051509030a030902060702 78
    0x60900d00c0071a44500e1254455804036695416203069400e08510841c820792068444400c000c072583c4412140d02449060807410344805c000b0302d0080345003600a4002184503518601c060401c540030040c254000070081c099203400c014040000500c0001c460301200d00c11003000030410001c140f410b0504902180c2c85801c2005000010300c2e00110f00018000c0301c0c0254240d4001b62140251881400c1188505545c031203004004990741c5005d03580045e4010340b00c0c0c240011f0b003130503c401082220704030100540340e58015141d01c52440d40c12006010006200706c5403c1c1c540204030001440c0b000740070720070700c403616619000250700c5c02c071102e06115102c14081d081c58841e941c07421220115413040520300c811070300303002c1c00040500304444014001d00c10f140c0074410070741c281415400144000320380136040040f0070203611a03580f281c500400190001c000030740301c135070b0460404c82c1c58a00e41c0c0344403075180e004003420005010700103c20b4903000300c0c051601140002c1c042c00004d11a011324035010798 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 289306133 1250 289304883 289304891
    0x41106070c0e060111030a09060f03140a060509010f030b0a0507170c03041a01140f01030b13020c010501080d2c0909010e06090f070522020f0a02010b030102070c180e01 74
    0x41d100003240c403640e1007003e00340d0b0751710200700120a12940328081c04078960302141100f40240701c1079004500b80c0e040c000307561a0002e01415071184040441c002560003401882d52190184241e0404190b21030140c4207030b007100c0392014a03699400c2c11041e03004008101c5c5590700d401084180d4410b2507520303038406904000002c9410f02c3c0d180c1404c158400ea400b200ea17084a11140703080320141d80030041c102c81c040d660300054440f04c03006121b104854900c5150400d9511201141c0e10355602500400b044624000181c441c402145070a003114410f8110508a901c0644c03090245903003c0542c0604101444102c03002c241060316500014801d042101d9200c84060100110403205502102c628100e071021224542c441580058807200804008041900050018415400d081c1c07805000441602031103100560001000380890700000c1540318154000190101c151b40e090091549c01c8e90110002c610300402951500c030150f070144280c0c1a100c0c50b5000701421100b250340403810f00303482400244 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 289307383 1250 289306133 289306139
    0x13060507120f1403040204020408070e09011b05040902031513090b0907050d150e330601080106051e0d0b19180b0d020409140709050c04060503040804090e0a03030e01020c06041106070c 81
    0x22622900440f00c02d0301c0c41d84fc1c01f0511842c584581d01d00450500c20b034840130724040c2010b80a00c044d5000522080307440c071890030107034400d44915044980c520400ca03000130306c0b240c0519040da04c2a0703014040402d5584903032410300c6940c0ea105001105d6503404a140000201d0400c200000380100910700c0050703004055050b428840c0c02c2d56803c4005120710030f04c88500820801005445000340d5030340d40007515080c0140900ca00460040000069000d0300425140342886a66410707070046903030f0201281c075000d4404050810945116141e01002c008c1d810050901d4281d440c0800784100401e019070702c80e00000555141e02010500f040d17000380040c01450b0590405044462500841850703602c2203400004914816200d4140070b5990030800d949414a05502252a0381000e002980d43c6041040001100d40700752141080c3c05034403101901519180d030070041d0440703042c6100800c407640104102409800080f80d15588144d10084c40e0340c4102e0540c0200e03200d406989001040c00517901808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 289308633 1250 289307383 289307399
    0x1c140922060b28211503080d1407170402220b0a0503010e06010302041a1003050a0506010e0303090d061b030504060b0319080304020613060507120f140304020402040807 74
    0x100740d1903001c1020a0280410340d105030300d03030f08007602d480f40000d100c101080c41540031240d0409507000c42814041000340701030b1355217030502c80e01c0d6100b120a07003000544502403044500400c01500d0200e20040d080340703080b00e40541086c1d007101016103a0f589590014045507501641c80d09040a5482c0151564280c00030110091078042c0704a40f14002409000400380b4050090501030a00321000e4100b592a55082c8000740070302100203140c12003207000c640c095032103a2a4000030b445456401203041d0810307880040c01c840001c0e10b03c0e410090540c084898680b000412a0035082080d00c8022140800c0e0420200601c2440d607043c564000907108941710b154940c0150740164014401003010785401d20426a5905019100b840c0c03181001c10302c00046500d400c040c543c410b001071b0049103040d062020051802c6001e40040d80458400302e403a0b01480111404800080381608114009242d8881e0140580d00b80d0000d02c0004080040060115150b58040e24001c011000c202c80030359480d0416 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 289309883 1250 289308633 289308637
    0x30906210f1a0616060209060912030a03060f0e011e08070f05090a050f06060a0309050105101d09060114010309050a0b061f05030c0c011b021c140922060b 68
    0xc00e241040c01c0403894403520f021422a02d940301c452040c0c2c02c88140f1513070740f000a50070180107143e022800340504034003034641b0b00c0d040c8000700c0c040d8080c6903508000b200107030445080780c10200403e48003400510200101c02812419901c54008103174040c641c9603055400e0b52050380014490340106080060707004512004802641c008030f80304070407656130803590021100201c5284502c012084c000c12803034108840101468101f40c600403071100c0440d1141c4d42900c80c2603548008100c90b00d4000c02040078a4101c140c83c8100180e040012400c007444800d56641043c0160704040e0801e00820041ea8084c3d445460302941c44030076141c5403511801c01d10844001150414080c1c075031281d4256054603166420500800c0d162111400c540742c4a960307042030f4106000c0c03801d442d90380380d50100800002940100708504c517075005020020100301c2c8040c0540f25501c002090011643d507092004c000641034403510345c82071f92100780d00c00c07044a4002c2c55104400c2c40c0014039140c0100803d0354180800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 289311133 1250 289309883 289309901
    0x6080a0809030a380903040b03040c030c030f0605010803090d0b060a0e160f05040f06030b040e0f07080d09050d02090601140a050310120f060b03070812030a05010501020a030906210f 80
    0x4138000400304c600241d1001c100444003821160030421090002d80803140155130802c0c0590002401c0c151203682d81905201d00e50815281801d1280c0e480d0100900e50281a001d000401b0103181004004804201c0019401c0e0004220f0020800056290b0f120310070810300502100011a906052869480e10314010140031500014518180911024090000c0350101d9500202644034507151810441c000c0c80d000d0503240c0d004e61107002c0c801c0480410032646002d01da035940a05807a03860030b21943e1601c00c000310201d00307104026004111964900401d61240c1c0d8050314501850742d00c00004903511840341e40b81120768500850000c400c5513020014520841100c186c40111035181c015080e40d040c841034009101203483c1d00c8410002e402a008240100c4000d02211340700e5440300102c0e0b06005564940007105200407080008100b0b1500030280100f4083c0050300300e1088540f030051014038035018401c244490200039100705040741c451031500c1c1b4007101003000304148552180e409002905 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 289312383 1250 289311133 289311203
    0x6051e0612181b031203090a1707020406060e0a050114090607110607140d0201060e060d03110303240405151215011508180303012102040f0509060a06080a0809030a 72
    0x885c00c0c008440b00702201e0007068444024402102c0c0d95032074000075440050201f10300704050109000607251405410054211034503007008060a420500c980300c803096006c03034100f00d51001e415802096400c21600341410a4400c1d80c0d0f07902150074100c20790036038484000d8000b02d000505206006920b144e1a6203015008255580b05a41c160202e0a0f030300580180d91110300140e0110311685000801c01900c5031184c1001d100d40f541ea60821400c50300b0807a154845080c0d841581c1800310b41a48040004c200202c0d0104100d040c80d50041c9010b51f041121180070313203161041e800c00c1c95010001401c0950140901240541c0c45904806c04003080c0c242810214141030003150868520500040c0350b000b11000460860f0704c0c00c2c1d0140c000603081507020005150b0341c9204400360b1580c2c09548041d409030305010903681000100b1602c4c0030b00041030314005918003a8203200b00038004c983c585c1000d070002002501d4402c54400a41484801301c0c1c000e1007541d03540480c100c1c90840744078600c4018055 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 289313633 1250 289312383 289312393
    0xa080f060c0705060711100e0f0c0402160303110d050c07060e011a0f010c051204080c1005040501141b0606040b040903050304060c090f0906051e0612181b03 69
    0x10503071945035000b8004001e0198001800080304c00d842940761804c40d1501038203c030440303800c8610722030840d01045035600b440e40140705c2842da44181001400341c400c000791070443c941010501d06910360b804c0140000c08143c1c5450641504031000d009695400c0d003561001c02403404c09010020fa81e030b1151008654690410f100c9240c00c80b8184510440060601b00440c0380200260422a2686010344503505101441c0c0e2040003003101001032811451680940030303541d03070626145500d00610054007500c40e00480e15034014046d480004ea800321607082c00c00318894541c20300400c0503030195014024042c10175001441280c800050460302030581507030108110302d454130600040c0c9061000c0a40840d50070000300c1c00042d01544074450700881843c03c540c01a4844d00d840314020219400348000a40781d20040c401841c03c048120395203807515540c0d486d01e42a66012460301e01607007520080c060705040001d44c0c0602d995106251001400f01501e0901081c841901040d030700322000c0c28068828 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 289314883 1250 289313633 289313641
    0x7030b0630060f10180f0315150b070314210c0a0518040f06031202102703030605130609051303140304030e0d0303090605090c1e030304050a080f06 65
    0x449060034000c0d580503268001c190f00b010188031001c4507100c400020801c80c4140795124903d803183c0701020b40a00c1564443c0d0750b2039400c1010211209007000000c1c0d51034448400f0510050641500c11141e0011300d071f540b285501d090036074486d8013030f02d0501452200054800100c101d40d40e0b030078803e0341340c0303001b07440c074944031881c0c03945850003451314407800301c3e00070440c1c01c440306004600f40301c250500030030100c1c44012054000b410742d03d041d03000325100d5042500030a10160103104240701e004100704100000e40c0341d080c0341c29841c3c1d44404491a01000c00059030145842a044180a000081d215482e516030140f5150024030442c070420818620b4103002c106081c0014060301c10854142d81c94420b4803030300354802c540d05d5001a004609019010b80341c03500544640750030b44035940c00323074030001402440c60400c0760a5900040c242281908061402c19032640d468020490420342410105072882d107040200c0e00d50700c26900942c4d8464030311900040c05450004919081d101003100340d03219522 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 289316133 1250 289314883 289314967
    0x110309030318130e061306112b15210b0106120e0f06070302030c0706090b061804050a1203020f03010807090606020a240b060c0106080d050903100507030b06 69
    0x2206152200c120381005011610882841c080c6e00006805402c000400520700c103d0500c0d1940301490003c00f010b03084d2802e500c00d40c50465600080042c3e07035400d004d01440d010494800c0d0603180140c45043e100240d4001502c1360f02e0400190041d80300d0840d10079541c580001a02e06148100403a00d03650402c0f000e9030318a00d02260600c18400480b009160035207031880190065080100f0340c021400301849480040f8a160090309480e501412828519043c5901803103170b41c820003420b21680150000c14440020b00025100d8601c0b904160510400340c4401300c1100039200d40c1d0703000c89000748080000f1920b903401141040880f008007004111181c1d40341000e0b600e581001c1400343c9900c0c000402d1a03445440911400c42e0841000d40001d014140100041d80540114206000d603a548050600221104000143e181041c0b810321504012404000942d6040324042215183d80c452001c5a60301d406034101c043c110000908140c7c2f24060314861155101c3c15104000800d05120f0754518a50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 289317383 1250 289316133 289316141
    0x5010b0307150e060f0717070c0e040803040609021309240606050a0507021306060503040215090f040b0301110301030f0b1b0a081b0c0703020a150203090111030903031813 75
    0x54074a440b0500f0ba8481c2100304112500711001e02c00b08004100250b400080c40c1d0111364100382084096152145060704228040c89419009400c90f105010148030101e010300c0c058a80c81640500007140b40d00c902d1011810307076034040300c1d0300b65000d00f13110102c010080e00030301817520700e03850082040d0810346502d880000e41e145481184040351040220040051080d4010511a030003d0103404601d10b4040303001c1c04892003944800300103480801030204528080804403000c01054034a2400c0c006550b00142d400e40c11612400d100d41e0342d5507548059510207410494000000d9041541c8940e56424850612042120215540443d060000f04100c480c0243d66100d450341c602079a00b42508070f8801c1d1800180548101807407421074001410140c40c040091180f0000e85003e001080e1940c414004050a21341103188218101e4090020f0b03503a001054410800c0c007483d10003218150354200d941903100700344282e5094040018026007004128507421040c40007a95142c18040010f507440c8121 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 289318633 1250 289317383 289317419
    0x90204062604031206030b0711010c18050415080316020a0608091509011503030906020d03180209040c0e0408072a060e010e120a020301180c03080f0d020705010b0307 73
    0x501d0040c0118001c288284020021500001030000e61180c03203807a41088100e0032100900002c1e0000181c1249101c2070044013010340480c107008a0103d00c4512144210103280162030089a48600000c0369400e607015000080180806495482109202c41c142e0702c981140c3c00da000700030042d0000781d118810443c0c0c038030482d40359028084154814880c02032820014040c0d1840d50340345c000c840c0c4ca08c0c215034890801540b1035214250241c0c6441d4000c1d06055407100c4480c02e15250001204448015040d041491075044a69007202e540c2c2d0325040300262600d400107100b0300c80c520100710070449180010040c0500039001d6170b8480d44501000210204a501c10040201103600100f001600030281c0d4102e10005040c240001c03207181300454800c040049000807542c0c8200c1c2c41209504082c400c0030b1040c200c1c07010ba06090101034541485510300391000418400000401000140395081541e0b0003422400c800e40d550709071810014081d294008000788603004080c40001c003421504103007845 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 289319883 1250 289318633 289318697
    0x40b06180a02090d0203012301093608030a02120a231b220602010912050a030204031a04050c06030601020c0d0c03050102070503130506040303120209040f050109020406 74
    0x1180d03207541118000c1c0d000340030965080300b4404134403001a50203000e6184c00380741640c0512034482d84000d85100011040c0e01c0180700318a803103c2d66060780e84201c8000842c003007215a000d2145880c0800d50b4080303040f0040070b003410710040144403010060350010554501d120052009a4a5491010f000c99805c0d01940c01410085608014140940c4113419070003405040c1e038420756941058001a141c0c0801d08415440c10101d615415407080407403040050b041c0e602c02000300250682d00c1a154040011411060004c00728171550342622940456004c1c1d03034800c417803040c515455041141100804e80303048916028400004000d41007103030643c2c1c403802d4146c1c020014243ea4170140009200964402e0310044030180e800720103e4424001004032074826001940d58260ba5100c0a034804010f4000d948940e004200c1080820342c845083c4c0c0e990780c907640300140d682c4940380000e4010040705840411180c01e000c0000381c607540c3c541c05801118426242d6040c0c50010110394028807042c1c0720320f0a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 289321133 1250 289319883 289319929
    0x30c012d110d0203042111120d02010f0c0504060804080d2903061506091c08070215030405031c0b0a0603020d06120f060e0f030d0b011709070519030812040b06 70
    0xc0c015000022040805009074070200c3d174440c0d000041460003087c191f0301440380d48100380749c05c501c5909120f0300c0080003400c3c80801c050308403501c0081140c0b0451140900f006400c50100c2d00340800c0c4800c484240069040410034900d07040018034400504142200300f0070f01c0101441102c0c1004604944039400842140481c0f880c1e038010000140c0180c04415001040d588000d5102001c282803035901d5405000103030385651251040210700100129404140001401400002000003055486102c0640c0d140b0340542504802000142861003450b584000b5060002901e507405500411031202000414410300c2d465a42001c1030340244c401c010242d90002e0101c4011940c02d0744405100c00c02401a2001d1288508a251554110200d000102503842c0341d11243c941c0c0103440b003041c042001008045610f44284941c0e100c01043c40380c507003d89292030801c101310361088500d1000e0350348485003640701c22402c10a101a07080440c3d00300c56510740d2002160032032034010007030003000c240622120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 289322383 1250 289321133 289321169
    0xf0203060d0303180b10030507050102070315090f050a06060603050901090c0504021305060f0a02061806041205130e0a0609090209070f0918020d0c03020306030c012d110d020304 78
    0x5004090285115070003404c0400c1e088000f40303c4080040c0984000c1c03c1c141811800c609000b420948140c2c4003d055610244080000035800e10000044001c86040003d0b115818100310661000c00d15005145000304802c8a0803c03059038003180560388182d80401c415559088160b00326050341402801e04034407810100f00c1d92405d60018103880c02070001d030301007503030752800801c095810a0440e001e203900c0c00b26807803000b1341e410004c07654441400701c030300301651042c88140b03074480001910140000c411106078590032405841183d2041212a468000555a850440e0300442044d6000511300742402000100c0c0e500c2d40c060919540d80080030440d41f03440741d40c1c040c0d6417000b880b0004010710030b03070b07540020301d0400040c1e00384050741e000300e030160b40c0b81c01d48040d00086400040f2100141403041c014003050303440c002034005c2c0c00310003803e2a0400e1201c60080607081143e406051880c21075041d03086803206c1d40000d828000b207500f0f1044520082940105a0300c9009a00503654404100761000f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 289323633 1250 289322383 289322387
    0x10e070501020c0f0904170301030c09230f130b100504060f0303021e011104060c030210060b19030b0303070302070312080106020d120b0306010f05180105090406230412030f0203060d03 81
    0x181e04075100d15802c0320307e400800150303205504240d1056600e2003c40c1010080035580c0d0159040020303a4900a04c00c0340ea146420048085c40604030b55039100451002804c0511442c204045443c2c00209800652601d401c00302480c010502426014a040920010f8044d524080c82003c1c5ca5040c0c018180c43d80c0840007030b46001c088204100d40543d280d100400320b101051004201804056448054440d0241000b900c1c0c0a01969031030703078243c5440c808111500500055908000000d01e4030340c440d007210f000407400307401a2200d0f00d034580400140842010b4000510a040368418911202040c050440644022209200e080003513080815a641e09a2207414180c4888446120001e04c4004100120703140a01c03d0300306014845d1000390a00c0b881c40c0100300c2c03c46400300582c08030b100c0d40c10480442c42c04040680010202500c44000310314103a92100c000e0b20a081361101e480c49031815040c80c85840000c81084e0300401d251603a01c5202d91400c0c000c803840303004080e00140c3e81d0380c2c00e6941 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 289324883 1250 289323633 289323649
    0x504063507180212090a0c15051c05010302120a03050306040915020a030605031e07030209220b011a160b0c0f0f0d060512060c030a02040314010e070501020c0f 70
    0x140151a0250941c00709040c05204030320000c9260540d001a11698144030100644602826034900d9610248942d0005031024017400b050307481c40b00111402030318441041d101c90181000c8000c40c1682c1300141e80c01c40d0250b40c0418101e0303000300d0300380d44082185030141d600c03052031040c080c0c0080c00400025015080540040602510545680222240121041c0102e0f08003c1c0090006a02d500f0100102e00d0200014221006c6a400211030492190a680d81d21029440000c0c010014400003c180ca5040c4106451a402403044c1c460004060300d00941017100074041e25040201454810700d008401400382d070328501302c2e0b907851110982c640c1c4503120300c0ca00c02030042101d4102000210354001601024201c0311a103560302c10f03114102d041d01c0c1410743c0d0303147d04100c2c040d1002c034501c0400ca0400055043c1c010345400da40e6a525203ca0b64200c0c068030540d08041e002e0441214100c03400401507005240c030b0001ea4040d107030007e8540307004903264403500c84800d6000d03454002c3c01e102440d02c030079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 289326133 1250 289324883 289324979
    0x10e070c0b06030c06120601030b090106020a060f0e011e11040b0a08090a12031509021e1c0507050a030b040b09010605090105091806090a0b010212160609060501050406 74
    0x10840c1c1d540f15900e000250340b94400703001c0801c0c20b6105404c2c807c072542c01d40503510140c00100e8801e140c235030510100954804840a001d4560394032803910340c0071074001d544000700c48240c2c04024460303142803802c41c0d6004160306400c9145a881d0200c0120703a014180203a0303040d550031030840c901c4d0074140c4038115295040542240180d004000070348000030082440080801141c0c0c5000c84c040b503082007240380001e81a4455500c1c64010020619242d106187c030449041949080c962505060700c40442d03400d4542040800c810300e003005102e441908600903103c40103059030b043c85288d1115082c00280e841942e0300542207601000140b000354014000780c02505c0f01031400074203182d5858002101d040e801d8504403802c42c0c101041c05490b04000c011a94054100201030006c580b181000035071301c0c00c103651091941d4202242c91441250181c1d000000c480e08018244080886410f2040c000e0a0a110382c0f441207103425000107601a01c0a8410020300380d409240e5404501d4502070402c24240709 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 289327383 1250 289326133 289326139
    0x160f0b0c10050f09070501030e0c010315080303041a070e03060a11090a0b0406020d02070e060904060905031b100e0c0f0411120a0f1116050102040b0c15010e070c0b06 73
    0x698035451103051107070034840e030894a000c083d58145102c61904010190300041e0415081c200100e0640d90002000b07582c1000038680060380d1100740c01000d8604403030f90062034140c04000140320038414084607600300c20150752822052502c44070340c1036036007010328054a60160450400034001140c2e5a002d1602400403a8200b0716101490380050b4a0050b55045090100e40201d014004954100030b0404007040c18001406075038102112528001c00c0140700350703c01c1c41c0041c002800c0008540012303021541c0081103a48600184503099440300e001c40644456106180100c02c030300300300380110401e81403003101130861502d0040600c10007601060790340350040c0e00c40882c0c8800010910007800d4034140c8003140e0806049c09084001522100c0104125050404151080d0301d0044800c49040c9005d60342e265150407540e02d440307400390040d075201000400000c184c24134a6000411504a0740704410190703809a031b2608101c0342c1d5044207544000c000385c482c40b100310000301081031450b0030140003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 289328633 1250 289327383 289327393
    0x308070c02010c140f0304290306060d0f0f0207050c01080702070609050d050a05070b0a080109050c09100c020307120303150806040201111015030b0a0e0309010c020f060a030e160f0b0c 81
    0x207a42846d55100e07030b005510703280b003102409560b25020300c500301e02c07002040200307881c41c03d00e40c0008078940119202d002d42244c0d0788401e140280c2c656401120500c1c3c081006645485045c140795848400c500512070208400100080710305101150b446c090322070039110480403904000910110b03590b4200120741501c5050304090104d1400c0224000034441d9000071552880700f204018100c0070180d2248404508003020302541109071001e4403140c500513190900c00d6a01d8001c104d40511110001035014000c140c000300f84140d0740c42c0318041282c00f13a20140881c9203503690752481071040d4400c2104030340000d40403400561294a5a942e4640c40b10200c4080c01e2407a0035210480d03800342061260000020303001c201f04081003180541c000c0e4154010044482c0c208440340d1030b8441c4000b02d42c10030100041e418210f40e03c0d10700b0403041c0b16000d003209841d40caa804002d00201013184a0030000d210b5500d80941c9822280c1041054600580c01e0160141c50154244029000025918550b001e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 289329883 1250 289328633 289328653
    0x1c02041401080435190f02030702130504031b0b01090e0303101a0d0606050301140105031306111b06040b22020d060f0510050f040c090b09010c021206040308070c02010c14 75
    0x10013400752489011151031408603490010b405007a04070721010503000d6410511442c00940c0d20f010034160901c039050070200c3d00c0d0356070b40340883e0803810701842c00c030568442229a00610043e01d5885045c1d800e0050100480081d50303041507a00d0008580200402c000480c007840810465004407140541a00c107140c2041002400c1500b5206e1a40101d00022400b1004001d040303660356010300840d03000e08281d0300c2c5040c5090051208000e13100c015003c1ca80700d510b843c1c00356904d1021070703410f03049a01c3d1081142000034001d40c0c607100c043d1819030705841003002040001c00002e0701c5100003d14042140031030603041c3d0030310032102100c482c140c900e1980c2d500d502000501e5805800d1080c881101d41c5408142424100a850410f21030340c42d02507841d050325104001d4200c40101c2c04c2e60310742c44410f520390507500300407601807011000081d004100c0c442222585000012081d004510a85031504141e03101030040324044603505c03001c1d0004048800c02d1000c10406141c83c4043c0724100d041d1410096 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 289331133 1250 289329883 289329983
    0x30f091801060c0201080a1b080613020c160f050916020c040c050c070f06020309040b040b060a170109110702090a1401120b0c032a1c020414010804 65
    0xc0300364440c40c0420315032002c0d0021136034440440d940c440c041d0401000140d2403540b1b807000910b0400c001c1018081080080303001c0c1e6650a00d0000911201c143c01d5550b9121460f4036508e40e61010f151804242414001003880019103c882c6c044d0b03140a011026241d81c1e0031460f40c0c0c0302c03964051001c154010443d494440d0b859a0003503206252076034840c0c0d031f6038100300038105190203603503841458601e046107014031205902008a0304504006c9a01280075000300d07000070010301c105001c29034000c10006803011210703003011061032200e500201c007800e44d80e6102e4524003070b60320780c2d201ca1a164104112003001868102c2c00790b0f4008802c082c0015841d904581c00000d102c00a0304100e041c68405c0c150042002801c0d69090ba00401c28034030b050550401d55126407040c600c003d6098102e80c1030400d50b0411f2150b2400741c51030861206103803410784100e4240745c0d000b9441070203a60021181c7c03442141e00c2d54041c54102e07000e15400642d0444055542d0b4801d5040944000e2004c05201000141a41d1103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 289332383 1250 289331133 289331179
    0xf1b010503071803050715121b0e13050703050103031103030705070b04140a060f06120c050103110f130e01090902010c060b0103111309051e0c16020d03020105040b06010c05030f09 79
    0x14028154007003484da40388024095800c1d5071230015000342028200000f203030f9450003a40075002541046551840c0c40000146503641100382074a10f24602401c0151783c0380d1581140b4101c0c0d010b510340d01c01c0c207500303a10010340b648021240880030807820000d18001991819125605c01e008100034264445299040c81c00d01c41e40319400e841054540d02442814a81803003220300170030b80c060740e800707402c0f01594804c4640345075841a94180755540c0f00c1074100c00791a41c2141c40d081031240800f5681e00200c104000300301c900b405045650402c1c07400103d49045a4030496207529016101c20b405d021069850b50090040661050304040d10340e4403811320540490050321a4040c4050340c881d446040100700340071074400030305052030b199100c10580300045602d0915604070f92440d695641d2070300f54944060303440c1c41e0144002d4020070800341d6503040c103506501503401140b01300141c84440e240c00700116061003850034058002d4004001c0c0070303500c041c4c1400504c40c020703000c3c01e0b00845000640c0c40c42604 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 289333633 1250 289332383 289332389
    0x11a0a1202030f010303140a080c0a050405030708030d050106030c1d01051e07170301150c0c0e090d090f05061611090405030705071208190e060c0f1b0105030718030507 74
    0xb101c03c1c1c0010300c00c0541110030891002100c3d4040c90500300d007244010990400649043c2c2d610310001084401644030700110f0300504000741c203e0b24915650401203030303a980100c840700301d161700c0c0c0b10011500c0d502ca80106595900c0383d50b203040203010303040040052200d41ca81c402d81444010001829040c00210040d45080b4405219039128041c60412120f2845501103200c0301402c1000180314103005106070303191a004904d8403c804c0302c03840c07820074014000e0f0f403c440f4900700c485040045440d0001041c0701c1c036504039611040c2d00c40d510321880c04942000c2c000c0076480901445948100b0280304112840a0b0017000c240c20119201004649110800d88059505400006001d403d02104005d0728000b8004810b12100c0c2c05815110192540174800014140340740700401400114071a4a404005810041801c0d03601c0d85006040e07a5940a042003041c070300c1c010b10508211301052128222055081078582c00c0c0703950740303403982200c40c51201801d07260b81190468010011034001c21540300a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 289334883 1250 289333633 289333651
    0x1208130305120d0e0a02060406050f040b03040819020f0c062d0901091512110c0d05030901110f07110d050102070804051810140f030a2009011a0a120203 67
    0x5110f040240580980d030484054003015400414024016240e2500b1035045030b503285040d60b01c0782c811a01000715840f417680f00714100d103804020702c002c3c00540340003031074940084ca81c84808804070400690311001c01c04400d0742c45d03130030504803581d103400c00da8010702001d2a4850340940a00b5802400103a02d81c0380d40719a80b0310a40402c0710310a550300a141140500440110075602c0030410030001c00d000d55600c40082e84c0d540750700304c401c6800507250558022180031002e4420504070b041009100350002c80d17001400c3d608026080101041620454a1035036247e112540340000c540c0707858070060515406160010a810154008504284040d02c613042c450445240c2e1607140c041045440c8510707030102c040d00d0b1001400d2081032034072655810121000c0c0300210341c110114000190720819502d511341d40600035100ba030810030240301101c0081301150209404150f442200340702e0446400d0140c9c42092801040c0c4900144c5400c01401d105061703458180101180f81d0703403150a0b60000e94807602 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 289336133 1250 289334883 289334887
    0x3141e0a02011106011a0d0b030d0e0301060504020903030702040e0c030619060e010b070b1f0f0312020a200316080c031b06090603190207030f0315120813030512 71
    0x110340c1d108054440c0b0b21000c1d0f004041650408840107800720b001204140203800000c0c412030510580e03000640041c02c01815a0780385203900c2c82c00380c01140c80c1c40310544203500e04007001c0340c103141901c252021514054001c6060200c6a801d10000380011a00c3c01c000344550446002250f40c02c0118600c41d0320744031100304900388005202c005640d1036400040341c0d401c1ca500144030700351000013503036801d039003011072600d5544030032010040c00041f20074020382c200c0c0c1400002c10f65540c02030500303007203070f105881e04006581403550032a1120f0300140014030b402c620701e04801d4000c1c880d483e020078420008050741d00103003a001c4081c2e0351100c0c5511442403600000c64110141c0303001c1c4140c28070041d0540d85060300c020340304001059031081200d082d1007028080301140800d400e408091211886141d0110740e84d0205c0e0030094042d10b0423403290800241010030101c0c1d0008074809440844104d0010148004140d0760b44000b66002128503000705000304000101282c0c0c200096100381c410072158070703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 289337383 1250 289336133 289336153
    0x3070302010b040902011704060e060a0c111203010e07052a06060d02090c0c0f010905060412030915021c05071115090d0e130c020c0405060f0a03141e 66
    0x6800c0d0b4a040640900c0340785032051020260340c004000740000b01608030240b2041e40e852811030020200100d24845c288544402c101903011507500503040740e800c6843d9070403410209188181d90f0700d1040c9180380c1d400b40510042020300d420fa91000c1d000300b0076040907030a018806030134000002000410030b40d01701ea8101745003003c0000340b020382d80148094419000001040d0003007010104040c05890110b1000034003c8401c040c203001039100c0b615a240240306900b000d051103075480a09650956285e070448807203010340e50080c0700c0c488016074040b143c190840d22003a8020000d402c02e02c052000117080d1525161160340a01c602842841545c448038201a080f06074a450064203202501045002c8020710465050025079080c031241c0e51320309840700c80c0b143c401041c0e0768030805400900a80c2000710918581d40c021980c0b00c00360b40145c40800c0140d44104c1045241030016084a800a886d81e41c28400306000c10003050192440704212100c88016426505440041401080c0644c100d82c2c2c1e04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 289338633 1250 289337383 289337387
    0x15150f070c03060b01030509060609100317041d150402030402130e060907080d020601030b1015021c031a040b01050405030d0503010e0703020a0906050702031002041401030e1606180e0702030703 85
    0x40d03d404c42885c0810492500341201561698003402044c8980c1d902c200085d040d211942030b04c809903a00a1086640e08003003907040e585a00a8020589641c2507405580400c034000792036280b00d4042d06c0c0407190140009401d210003940003a2040e1f8001d00c0440c0d01030b22812480c0104904008902c00900340f40c5406140141803880c035400000702074000c4081490603641c00101c1354103580c0c20a05680c803036161003c4038184003034198010340e00744e001140c0b0141d600303801041d410070b00740101101050300450110300310203c0340c400540208400058101c0340050070190300c410791070f00040c1012032900d6224800285404500c07220f84000030702c004014807a9074035000f95540c03c40d40a0405604000c4502405400071029018190400001084100030340da4200401c3d400603880500455641d03440341c02ca500c03000c0c1c46020003401b01c2c0c18480100031700e00c8002408400038101d09c1c0d241c0c01c4681040c0c0c04580c400820f05808070b80148004012a00010706003045001e03402580045940b90308910700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 289339883 1250 289338633 289338641
    0x40b2502031c061230020a0c14100e030a08040807050f090903070308040609060203180d090f05220203092506090302090403020102130e0703060e15150f070c0306 71
    0x88070700c803581050030410000b094500c6091040754810b0000e0700800e00102c188030159021700f82110342440360034024654980200b0180e90a6001701c440e448802c0c0c84a101c400100c0c40c107e000c40e006541c200112101c14801c00100804910042c2920208119510742c001f00e0341007600806d42580291804205618014214400b02541a80d9520315407600e0140c0300d4503030007135074000303000d200a01c170000d410000540d101c100d10542c0090115100e00380440d550010245d2103460b0b080501c2180c1120121134018800b940481f140141204000e40c00c0c4001d000d4001b003003110504101c1d404400c015101c05550001d503120300511801030840c01400158080e035800c401c2142d0050380c026003024414150320000310015aa01030314600c3d40c1383c4642c03404a00922601549034003413000d030400442c03240310441c0307100d0150400799001e0186945400ea00d6008031070a545180d075440d18a1010300d41414034560542010b4141443c0e94103207940c0b103500c40110340c00300d0b00440348541c41c1c1d24140100401841 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 289341133 1250 289339883 289339927
    0x60304200901090c1803050d05030603070b030a0504030305070c0b1f0810020306010905060a050f161406151002060f06040e031306170c2b2306010215040b250203 71
    0x50501740c0c919103400c0e07103c920203003140c002c002000001503650f46040280300020284041102e50300d203807a010980c002c003029503044001034100f80114401b94411340e0300040786d9070050b24900050300c5c3c0c100100d40c00e01a80c0c21450320441c480000044109080c440303900320340481480540c0e2490b00000050007890183c1207244103c0f4144059110580c0c0041078900f60b0344100040b641c1c804a00403001e482c23014000c002029000441c01c800c040c808089121400361400b0703840242641d0790300c0d04105008800d040c040300181e01c810005102c5070f0110038510340080015100143d4180e078101c42c42e040d130380204006510585400c4042044603400084103001505220402d0040c0c00c001c00740070120700c16859100007810744200c00000d0704090220490701800c01810400808000f8900050304c1c444000050401c2041d10700060015400441e03404008640c0c4a406080d80e99299a59031031410040c040003484802003500749601540d00c2507152b0400c0c00e5800850326010906d4112503040c3c0101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 289342383 1250 289341133 289341167
    0x504090501120b0f07052a1005010b090609060c24130b01091a0a0f09060503010204030c0b0c0a0c03030801030b160909093f030506060304200901090c 66
    0x588000042070b1a002c01c3c540104c2c00501c50169030322909412182030048400341c00c024152001040c8414407551241440f1482c1c45060350800c29410080c00c0444109210381c8001440070400302d107891400c0c00081c000300500070010b0f03081500142405241000700c0c9415152400e5070101841a55010300440d5405010b0819840300c1b2026561402c80b15603042c820600029180d407440c0f034000c607200744200800800a020764140f65554141c101d9181c10501c554007602c0d01e024000b06050034180200c80582c0e4119598042ca18031303000ba10641c60317005418242290245c0502d1100244001c0381036001940290b54070326040d411401c01d06007034040607024410014001c01110203007034001040394100e5130700041c000380754885410b000880c0c100114000b2000003840c144658101c038180d400c05001d9845216014014020034800e5041307070003d50760942d010b803007400001c0015102c0307094506c050389843d4401c00040d04034004101a04000e0700100c00c42e41c0ca52031503590302c0b07a2182d80e5803403a80c004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 289343633 1250 289342383 289342409
    0x9140a0b0f06010e0108060d150b040605011404060e01111b090c0306011d060403082d1303020d06060509040b0a0e0d050d11040b030901090204060b03011d06030118030504090501 78
    0x700000b0340400311345013407241480005000900965146200740c400c0c0380c0c006000904820040f800d420041031070514a511507403500780d012409510482d804d02143c01349020a80c60941021801e40e4142550460103040146d00100c1d803112000a002c0c2034840744104042020786040d00c0100b03d40ba400c000c0c00f01d500c06409008002e0580e908c491a54150107505a40124240d100e00215040c0d204a410103080c00d00c000681e00d8100c800308000b290b0000364851040c845032a1b000408119111704200c0620301c0c00744003000e02c05441c2c00c0c40d1003105c0301c0c85500c00044c200d90b240e000c10301e04082200e080d40c80b1041d180410050b80302070300a0810085025024144411146002034a1030081e1603601100342d40c0e032400c11800400303503405c40b00134145021403030f0303100e00c2c0140186020700b0410000700c0c09a810b205c0300040010700799007544d0503074106144400c00240300510341d070300848005100340e905640b02c207945102c06580d6030b485621a4060b5441d0342d0b41d60b04100e00d08e019220181d001105000e04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 289344883 1250 289343633 289343641
    0x120901060b1206040905010219110f030a1707030603061b09090b0604030f0204061212020d0203030621010b040635030a05070f05060c03010311090103050c010c02010309140a0b0f 78
    0x3800b00040e03024004480018004179642409402406a0501030110b079110242165030346410290030342c0e1540000c82203400d0b500da04420603440f8010f0908900100d0800e00c03803441c00520010710140e1041b018030300020003c0d62a154001030b25003080d141010803d2000c0400d040c603a000c014400a091104010300c00200c0d860007241180c4198031026000c1424000303600110741e00c0e50400801080d03c42d48200750604141008484412600c850710050702c545030b481c2d1403140c00441074a105800087c600340031219101c140d46001024024051341555035040350300300e141e17180d1140c2c2c40504900e02c0c141c138030502e04200c40e40e5001720444501051230003401314054004000422a507245c0e159241c01c0751a170b10750f403401c0300c44041e200c0707001006d500444082002955010f00558106e03401500801d032110f0012040c4039405500b0b003c082c000d504604141c410139406241603030083d910625000505043c0d580f03034103290341901c100d107804c55003045a48905000259060310780000c0b940c0a6010a820 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 289346133 1250 289344883 289344907
    0x30106050309012412080708040b0c15070903120203130906080706080f150613090b01080a0513060e030904021303051c0c1b031407060f020706140903010b0303120901060b 75
    0x258031603000941c11001d05c0380c2c01c0201d44003d40d818240d00c88883ea8941d9241c000b05440390304039500d0420944100003c1240d012440c076000b41c083c07200d54a40403811811070f1118114141e811000301305500c03007003282c450003000c03117007118008114910001400c2da051403000b0381000e21541c4031a04004403a42888003a00c2380103009504085071103203c881c03050011020074128041e10111416050b0800d400155001d21900b29544131070027640d42640355507400e1044000c0f00d00c140c9210f601d044900f440d210000b18540e00c0b25141820202c100da0902c4038581c005402e90388410700c1102e03e1259510300b0000c0120801c0302141e043c0f23040514044030102c049006241c0180c2c510094450010141135250703807442015070502a50308040020301602c0c03100c00c01952401c039440740c0c0f00020504a40103168a20208030401640c0107941c841380ca500a0b40203941700d40d0466003085505558031a00e40c2400d58040005100c06032050000300c110b031418200740c5017101c12607408900221800c210541c4244 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 289347383 1250 289346133 289346201
    0x806040204081c09080d0305040b0a110d1d0a050a020907141603090b070303021201050a080d0305041103030307090609050303090f1306031e20010507141203010605030901 75
    0x200281c00f0020303d440d400c0b000c50358100c255010840d940600c0440d50f88442d80740d040148038a019410641064440c00f01711011104441c10004000d0014003a500301f10801ea0018034856128020141e48c482404e1046410300c1d0704041c00b201d456010761440d000318100144007a60060a9042030602d60003840069109803040c50340d1201c604000e40c080608050068103048007801603445110b40b0ac0c0450302c0c000c0d009500600f10401015148400051b03580342103900e0070140c2c0c26141c01b03820420b0f405a4168003a0901030401c4409060444010313995803004c1014501c600b605035220a5580e160100240440c460f980001e0300030b0b042001500070b10f8540b1040045950016985407180c0680240c9d5270005015070380005203018a01018034040640580c01c0b2a200350003070340c60071816803402007903600c1e10075160410381c0411002d016000115681400415103861210161150021307598402d00d000c0c1e000741c04c001d005c641c010040c8035030135a0074418080301240c00e031003041d960202c40480f040b00e4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 289348633 1250 289347383 289347403
    0x30f0a170d06030b0f01050f090103050c060c030c011b110106141e040c120f06050a0b031008030703031d0303040c0b0c03070215040504052a0f1c0606080604020408 72
    0x180304002504a2404038981c0a10020b580004030801c8a0500300a83d00f4000400e1280703038814110b10303113150900d1074500f620701c0c120795002000f410056801d5041c0300440c5c00c110b00039015400144054114040d00f0702034186500300071004480d60309003546000c0d100c04445403540c0b02c0d5038500340c0d05010b0405c03600360800740e82c4011074040950398180705050400c05510400e8030b0300135040c2031104c4c0b0241d03005101314955800080091105003206601c50084580e00e1180d80d03402030b41d0b86810042620741c840110f41080050356035903119078440c81e40750f00d503a024900480000741d030b402c0e0406840c207850071400c281e01c0510b0041d40c034504003a15610316012090081c0f500090001031450483c59003001100c0301290701a049031a01c00d501c01000009030030a10401c1c0c060350800f40058060300340003403020300302d5610840703a11280c0301d107a03505100c40e04a00c0c1043d42101c010460708044481c2221440c0a01c000c170100030861303070300700100100500303000b0b003000d0301860062006010740390001c10448aa = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 289349883 1250 289348633 289348673
    0x6260d0507060f0c09060305090d0801210b01060908070509190c0324031502281206090f20070f05030708070803010f0b0a080f060d0b15030f0a 63
    0x160800740c10031100401404a1080c80686045603180c034007600f20b0210411200151020001541d8501c01c05440c1c038804c107004c5000920307410040c000c070480415440c035100000310f0070302c035400c200c0d555011080b002031300030001040090804001e403510230400e0101918003030707a070760801c2d080a549410341e83e445102040001511016000a4107220341e015003031003000d03c400906024051041c900c90454070740410f0307030410309030304040b0740b61070f800c0c0225050308101002d400c951070036a950604c4804014401c40c000c100e400000001c0350441c600440300075041c948800a5282c1001e80464200c4100030728440e00708885c01c5e4000b204201c5041582c48180c0c116106091018083c9481802c0d4480e90034002c01c210404905842444605c0c00a981610100b001c01381c4002d440320f055000318000d41c1700300000a80c0c00300003d01e2280f000b00e00250401c0d0080c104040c242c03299a2061003c4000321019818080402d80c003090328a8100400c40081c4810030280c07a0b01c0e0761548030340c0e008651100c0c0709a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 289351133 1250 289349883 289349887
    0x2030f0904020c0a0804091409010513170c060712240512010209060d0e0f0f030a030e0109050d050c1e330106091502030a0e090702030408010f06260d05 67
    0x10101030a0040704c401340c0d80b1110b800d9445850382105402400b00318503400484c12940000b4404000512a05008040c02d80c0c00c510b401d0010703555520140440e0020500011040c013041a007070404106c8a070144825032500d80307018170101d40d60307411500000702d00e00d02d00c01c0750300c3c52866024500c3e4000301a01d0082c2d80f014580400444154064425141704540020000981c0130007070040d079014130b91806c0e881d010344040031440d035600b9070740f100e084514803045d8008110742c519030340c081c0e8001d84401c05000c00114243d00305440b01c3e401c03c40b134000d1a0300410000200d80e0742c0840b06009018014040d012880002d00c21705182554540280400c564400790161208003412001e001a814100506804042e103685948005207894554884c2031440200715000c1c0e00814008429100303588001c0c1c0c1c501a1040d0f4000403c031071100080c01031070550004104c0414a03070420f0042506c1011030500103d1f04c94509003090502d5441c4941421459a00840300c1c1d803190700214040e00100c04600d03000e5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 289352383 1250 289351133 289351147
    0x90a0603150b0f0403020a0e1509130503030405100b0d0c030f060603080309031e09030307110111030a080907150203030a05070e090112020102010e070f0e0901090606060203130602030f090402 84
    0x5503244002e810000340c5020100c2d40c646030048500007882602d00c280c4040760503940d0307812103000041098405000c040e950301d10b0b601d42d07800d040f00c0b1640d00c050a05500c2c2a04116525114216070003644c054481da0405039101005298600881038103250a40d90a000c14440791141c480401c00c40c08000c18248540f00d00700c05002039900504007641d001001d141e0303030f4244460742d07039601c0e4000e19102902d0580e6013960240c2c980311109507030a10030054055031600f03009070b48010940c001940d540303040c040b0440d882403841000f00094110fa40c2c1d40e4a4190013402c040c41820324000d020f5001d5416151140003100031241e0200540b40c009100c41004100344c5c85030501664030454a1400740c0d000b1444000000b141c0d0314041070280520f00031380080003000235100510303403100814000c8075400c16032200e00304940018501c501da8029038220000400c4141951182c0a0314650384c007400c0140c0c4003040c880c5c11910f0f242c2404006084038001140341030000801b0041d28010318241c076120355404030f0b0903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 289353633 1250 289352383 289352411
    0x20f0c03030d0e070902031006030b09010501051b1005131403070f1205070609030f170114010e01030207051501060801080312010603090503070501090524480301061103090a0603 78
    0x21130241031780000964992070800000b410801c0c003842a600040d050008211060405502d41d90603541d060b5039444c07524511044843c41e207002402110f540744910004080c1d8200c0b10300c01e035800340c00040c0c0a80c6030390000781480203040620000c00b903080c0c2c004024050021308950850404260700620002401940e0300c8269414002c40e0809408141401c05200c00c2540c81500c6115080698503a40516080b20a900390355802c02d0280d03a11800c000d840103c1158081c60b00c101c0311000500d8050302d050a03556501d402e240304070400008080341440148061900b083c0752501401c1c110700154102000758008000011041c4030380d105050f9070710f000100b4001e0a20440e00e4036a0480001c0c4a095140e2500703d60b650600100d03d0070202d0201441c24090044c0309e0414002c0c3d0b9031400c541d021201141c2400c641d10f40c1180e1205d40e200a0340a1001320501343d99902c02c0410803414915140c1d854803401410130740340003e410242d5001000f0003025662004180c01c1590700e60b140000b206c2003c2014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 289354883 1250 289353633 289353643
    0xb040e1c0813050d0f140a0f1206030204020c06010515130306200a09140103180b22050d020d050903060f0402062a07080d020a0303180804090507020f0c03030d0e 71
    0x8040c00c0ba011307541c0c000d90a680c004102050111896480c8050403c0f00180c0388810301500c00b40c10001248441c1410303409114500d030380c0741d58540a00004030a6965400034049921070300b0540c0d240e4011100400403850700c80c000b180c2031401144500c0c40c100200f118031342e00f8079041c007005020a580384510410144168002480012007400050395547c080b00050403d415500c9440d103851468450840217500c41d02541c43e070503a803000b00c0c2c546035442d582c480398030000c01060140e5595118034840c00e0003070b01d0510040c0c4503004101a2840311302c4080002c2c01c20001c5250401440000c10a4412a07140050041d0f489030307481480b613606440724800580f55204034641e84030141803005c031611115160040c2c030300c00c500c0340070121644140c0e13910780a0f427542510007e640142c4c10800005002c02e00030341000c0d03090140034030340d484c04c00f02683d11100103410641003000d84594610803c00d080e40c042241300c07000742042006141918241d4002980e0740309400c4030310f1200b6110b809072090800c04200d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 289356133 1250 289354883 289354921
    0x10050a06061b050a0b150405010614070803130f0813061b0b07031401060306081009050309101419030509070312180906030b0906010e010501121802030a060b040e1c08 73
    0x10174022603040c0091030a0784500c16404062050340341800000b103903400380322003c05090810744210b06012158031400c55079080240f00e5001e220602d4240b44c002089c1c000c1d4001c0705c4e84503001158071100c503e0b40380d0740506055000350042c05030520004101004e1010711441d025400300c03840c203840c5d85060007103000d4051aa103c44017010144008156030790160005003d81d04220704949940c175000c450724050311150350b0040c005400801464445091a83c841d881e16521824001840d840501040903145d00140312241000076603665442d806034140540c6802c01d2840e8010006c2e40c0c1151a041020104202c200e0248900d80482d480c0320751110100c0002011001000c2080365502d00340000591130850340e0a009000e1000041111440e0b400082e05855043e51a44200312000400d5002406502c82001c0240d000080c140b00583d1f0812001d40211703c1440c0c0071840d10280410f000c15104c414841142c01c2e0002c401119a50703203503c44150240200746001d5000d034a40805c1201e6013640c0740d07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 289357383 1250 289356133 289356143
    0x3070609020f1801060e0102030f0d0c111501050a0602031c0209180c0304060c050a1d0d1509060b0402070b130f051b010801170a140c0a030510050a06061b050a 70
    0x1401c0800510f4080b00858102d840c00d40b504507403080c0c4030004903106d20600c104159a1301c0d00f40702c0300c000c070b00440d48440015101230400b91101d0032000351080c0f51030018a000b110740c404600c0107000a0400040810040c10f55000441c10002c1004000d000804a44800242075a02043d0030480e95180c1c2d40b8030b1407603e11405a000c46042c080d0000c4041da0040f6401d60300720382800c01c0c519440e88030300c044400f00700046c1e6460161300c09501204043d5482c10a00a41c8210348081c4000426080201d00c40b2407055404c0000b02c12200c1c2c0340090035206d41c6d02c1818805c031300c103104001c0071491014000b030348030154a0030b1a00e91443d51621802039680d41700c01410610501076151040e49031608440244042626030403000d070703600d020784110089540c140601d01e4100000000015220005c1c03030000f0001041964210340324140402c0301266503a00c1903401d40d012185291a060251040d1a005052004140403407420400003401c5032001e200d0300040307106080740d1309050090600a400b00c0a40c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 289358633 1250 289357383 289357399
    0x2090f0705130303050403060605120303070507030201090212060717011a091306030f0c151b1110050a1701080d1101091b080c0d02130e0c15040806011703070609020f 73
    0x20341001491a0007500049030500d00d2714101096910b01890403401031b41c02c44000b1031444d0703035002d4100c80a410000f011004c1d5900d5072000b000581d100c0f200702e02c8480a0100900861030010401406501040001040d080d031000c014011034a041544000f298042c0c41010365500c01c4e080030075180c400281200d81450316189000c810400c088072842c0c40c040c014604071a0741074650048600158040748048042840520b0810300c0c07145038103001c82c0c0d49020302454802c5400301404034950300c05180c0300c1c10000700006244c050b0150400008840d407285034200050700d605101c00b01c2c4d62401209003002c18405908081070044600b5045210460f07480418590070040c28049a5055501401175580718020024801164200328078900c02c2c03540c0007421170384100c081c52424401000064034000b04c500810100000b207460340382008143d1000107205541d50340c50500098100703941038116960700c03002214001c000c2280002502c80960300f0890014007490706200040d00c4400301b201480c1c0142031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 289359883 1250 289358633 289358639
    0x503072709020c060a1e180b15031e1e0a0c0b280207030201121508060603010b010908070312032405040509070b1602040902090406050405120702090f070513 69
    0x46900a080045000f104990341902c1e44180c000c2a5051402c2251602c4c0c02e040042c0b41c0781000c1d40048440391103200c4103060700c40c801e0f11601c04025044070f210104002030404d0b18a103090421456405115030b621b6030342c1c1c000d0410816500c50090b451400c200d50b10561092503aa001844004146503014203511140c81c0d503040c60900310380141114242c100d2821044000c0d4000300d00310392206083c0380e8061700f41d45003140c0c01980c480d01c000024a80c1a6510303440804c80342c4101e034284010b0800f6900504052070316104242c00c3d5405840c6a034104800c40300b00f003040c1c0c03070700144c010152580060380b04045d44a99030110700500c13080040302c640c00420703aa0078280c82c1107020b4140c1a15000d40d1300380708650711160900d0b41d4100310b22030611040403c20600150120014985892910041000c1860503642d0000f8505120548065543d65651701c140310800c1810000341540e034902d10901800d2404680028411150003070500414443c0d410028000c60307c0f0b201100e0003100e8807100d0200d6551 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 289361133 1250 289359883 289359899
    0x30206090f0d1410020a08072708062205071203030906050f06040c03180807080c0a03090f0f03030c06050604140a0207150207020f0112020706060e04030f0f05030727 73
    0x1d040054040c0f80d0241c60151a000609402160341d07400e66601c50803225255554201d070f8071b07e00e4503990807c00000ca00d1070000f2030f9604000d840140341420080c2114141030504488411100103001d9000708401ea03031a0002d80302240c0c01c0e044407011094161080c0c09810158040c1100b1500140305c240303030500b0010310854031916503002d00300035202041078131030b01001542107401000d6103034444020808a0342c0004c9543c1e0091841e02e1040c000542481031007414689081584030003140030564040c018400020040c000c94010402e20301e048001515544025201d070342d43d10030113001c4503100d5000032066259504a41d04181d0000148160352a02d4088070000b900440c0b421107a0303050030b80021400b0b00c02070003a01e4000313400400c09402680080700558001c1051001c100e46a1380a101d0340010410314440c01c8010604011502114134041c0f900829040584c0c882c08244400303000c051003443d5002c010340340c0c030a6840c107241c0081d0040382080342c50500b105c80c03140c6213101e800d400420f00368 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 289362383 1250 289361133 289361153
    0x501050c070b16020712081905030712090201210216050c0102010e0703021305190501090606080112030801210203010213090b0d080a0e04020c01020d0c0f0c0804030206090f0d 77
    0x900450071000702d03480b540903050021800c0c04025005921500e418000c0d406070041811510348142803061602d0091140000460700305044600031039004400c20030f080390403000d14149072001b241d00b00098038a03940042c2501e5a03e016894070003043c5119181e01c0c54550f41141c2c5004100714403585030950030724016692780c626001d41e42c0103500301085a80703101c000165443c262903005200c0c200d03039001420608010b05005040101640e854444044003c01e144181030107000700480104c1c5050414002402100b01070340030034004d40300d41c1c1a090110f03604c00c007c0c60540390180c000c2c103929583c03110900c44404160703c010f541940700264484a901c40500071500b101d040c0003080c000703044007c082001c0100d0055016010640400619003a40c2c0b003200103080090000300f005040c11000d009081c2240c001c19411a85030f03a45544507620a90070a84042c40528140392910840c00c0a6941c0e66a034003880c80700078040e003000700703c011060b0f80d0820003250140d400b403d04103080e03525042c600805 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 289363633 1250 289362383 289362397
    0xa0b1305070909060305060a180209090303010501140301060e190f090b0306070201020405060711011404080a05100e07030204110706140a1107020a030f14030a03061a09011413030501050c 82
    0x4640c4402d000101c0c28600c0c0908003c4135000030203000756982e6440c00c072000c0c080c0c3c0e100e02c5d8040202659020010b90f0b9000e140c60203008104002c54880d0304060024080d480a410880422403003030004025032640300c550340300c905078251070b44a44004101c0414546a0301a0060050320306111000310b51035800d9440f500c0e511000728111035840e03c0380780b801c0c1d080b4419405840d401c8141000180b010945140c83c240b8481d4041c50302c001e40c00d0622030b0100d5190072030341004c0050340041c400641030040411030191201c0040d201000700910240203c3d90310055480000d00444d00c824400601f018500240e82c0925009001071000b100319140034a050002150046003035490521034201590320303002a00e0032940d01601d004d2000d800c507101c680c4158449c020484460348151402280c0c1c4005102501c0f00c121aa02c012405a047c240300d9407800005000c1403056400034003031000c20341c0c0e0002e8a050345013603401c042c90b80c4000542d400703810514142c00c003030b0030343d820002405128a5000001c20030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 289364883 1250 289363633 289363637
    0x1031b0e060f2e183506010303030906050702012a052205090a020717090319081e07200120030403060c0804020d02120f0a05070302031912080a0b130507 67
    0x41c00c13181c0442d040a4041c180142c070000c01866120042051030081e18201d555003940c090a011851206a42c2c60303c0e0f02600100c00117038a44203190104a03007802480d0f002032450000b4005000c0e86800b19007500008201e0144840301c458185000600890480d400240e420941e8100c54401c00381c82440d075040380c031a06000d0315001002030550306991082d50034441d800420301c03203120700355016a01241c102c901d907283c2c180100302e2032440d1606aa0043c0c1040c80c840d0146580b6a12040c06a1201d0954103014411900b02049880001503c0101c00a039001c0d1880404d89442502d2004031111011a00c42c00800714048001e00ca1802000014208a904c264801d10401d240000300f160381d010265002900701c581d8118610042c40c203516032a1040d516442118081d4039152803d5203480f81d0040c0a07152600007070824400d604050115210b155141a640303496402d0540c0c2e2800300702d54082e5440d0030000d5400106800c00615080903010080061001200b40381d0204170500520b41540c907100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 289366133 1250 289364883 289364897
    0x7060912020609030a021902130911030606010309020f0d06090b01030b09070515120c090406171005070507030f02030f04091a1504140a050a080601031b0e060f2e 71
    0x2194940000c1202d4002c1542da01a00241f58003644244c181d030214074040360b0103604412000d50079078803445102a04ca0061844501868038581414100b440244c100d0341098142480013015807500c3c9402e08184605680307080659605092101c000c0c00708031002000d11032000000010b00c0540000381d4058021101074030515641c0e1000c0028000c080e00051980034800d01c141d100b00d1401140d8140c0c0280304502c01842c00306010000350440b4450340101e201800c8081c0d86002072401041030a40300c400c0706100304014241190090070900a80e24000e081000030020007443c0742c4207009442c2103000010301c440d207a548441e19180540007280010740c02041c041603290203440c1c90200303894074100080810349003d0912444540015030401c40d503130040c40001c070004d030640307038a50000000d040307080140c0125419458481c410030b03044e0141500365045a8400d01420250114403600000e040760340303e882035256404140c0340d8a80a0780301c045040107600800c1003c0740c0c050303544032001c1e071956030030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 289367383 1250 289366133 289366141
    0x30408030a060e0103030f0503040c091e0b0a0b251a0601030b09010620010207021f02060711121b070f06020c190902030403020a08160c05061801080705070609120206 73
    0x41203000c0c00341700182c00906031419901400e40560011600a030151a0b19030300720340c484188030165a0042d11070016800080000d031040c411912649070000320403200750120754030702004e001c201e004030005818840a40071102040105013001c059600740e206071402fa91800f20b090710200d003079044842c1d9011034148400800076103046107009042c3e0781b60751100308c000d071103d860048042c200340b82c461003259401c02041c40075030f0710491780003c50582170120390b11449244c4c00003400c0c051701901f40d900340441001107002804000c980d20403000d40c00000c040d1500e451030b140e030f0315030341180320f40c1d039020b004104020404803403c01c40c65060381e1090b021a81c007800c00805111240442c05019440618081420b1108803119001190400c3c02841140d03803511480e01d030070249610005d03140c2d11600b03c000c004001c210440310240002c000403582c145c01c000305801e0401d401001003510780e0401a91000203110180290261030907140c00000070402c2a1883c03034000040000c0040020151080c58005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 289368633 1250 289367383 289367399
    0x13180b0a050f0f060d0308061c060e0d08040512030a020409022107050c0a290a1506031a0409060225050105060316030f0201030f0c020a0204140912030603030f030408030a06 76
    0xd07a0003004081d1580d11700c840c02c0e032400c54680c6800350480d684102c4103c0712070101100d102d0b21541e107a0181c0b00000d140207036101d4051800201c2940b8600380030206081001003500071a0300c0c00e8000a40784199626a18880c900b0000e1155802030b0450502c042000c841c20303200c07040c2140103c41748480c0201c20303440303184c1d05a90301e004804036150389500c001e01d090000750301c0320303019404512404070304035400c0181c203c4200200822200185c0c42030752400c00032004480e100c0643c00a01407070038104403c1c480c0d03048510444810f0000240075689070303480b4008012840e4120b6403c1c014440d20070500000394280800c0e4000000010f98081d820030700030400718076011561008400b0407031141051300b0324541e1502810040400280d060584c1e60381c01e0b9494505a0180e00e617a94082d6014000f541041c0c8100800c884010ba40545040555020420403004c000303800b503911403004c1e146545a94804000a00d140309640344444603c81c08010b0008001381c031400385000d102000010f104060300ea00013 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 289369883 1250 289368633 289368661
    0x80d0f020301050d020d0f0807140d090308070b15360c190311030a05070f080712022a070f090207020f0609060c120306120c13180b0a050f 61
    0x9980d8000c8800407254010321b4000c3e1146980343c481c84004021041d00d0b00c40b020031382c100700400d803904d04502c81051403050b800c0c06807100d15040c9042c6039982c903081d9124410b441c040e81a000b001c2038910300100d00380d62816100c112011b0310080044003803103540007400c0c03040d524240e1a50201e1441034408244002c4e41c040e0386200305441c50300e040c1018070510401540520540300d44c0280f40e61031806031002146540210b2103481480d4012900342417079080240246c44103420740c010884120b042c400d09a070310007401a82120525405a21a101c88107035a45404280303218030000101000c0d40d0f010380801050301012205403400007003c295441c0680c000768030403c1d000940c03104003c0c10600403842c103030340500f003502000707443c03541444080110300e407500d6451807a100151202208000061519070119400755480f00301400d03a01c40404041a00700032100302c0003110030b4640c0c1486640915140c110307100c0c070790405049209030500000c1d05004101c00e41d002021198420000f44060340242c02e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 289371133 1250 289369883 289369889
    0xe0a061e051617070b0405070e090a030909050c04050619200c0105070c0e0901050412030209010207140d1a0a0b01050405010804020111100207140601080f03120c090607080d0f020301 80
    0x5102c0c958071020720886004541800c1d0000340aa9804284041e0b05c55114611640040000c0317400c0c8000201200c0000700f03c00d80a501800b200780000764070564850440e22400004912622140784d000228080ca07004a504580c020985440c213100780007500310b80300c2c40b94a51640d180d0380454a06001c00c498200c6056039401001c25050651044c8006c245d440c1c01101c3e50301c400d0b52108c0c0b000b019030906462402d410303034484061000340f10901e1261844082d44e828110f10b0140b480002035259100e5101e10034081202807440c8140d92101c1500c405031030340c85124000c440b02127a0b010b1014806c1903038101191864640190707142e5014200302c2c2e003900c00503150089155615801101c2d1150480082c4a43d40921460340a00c40d41d1030000c1d10520b4407850340e138414110740c00d029528049059000b511107502caa805948001404401c840d021741481c140c103956952400c0d240034443c07090525164003e9400110a014021420302030070658071480000e0282c27010f8841100b040c1d000c280 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 289372383 1250 289371133 289371157
    0xf060915070209010b0f1c110c030a080a02040f060309080c031218070b03011511030309010609201e04031a060405090105070e06070501090213150603090f120e0a061e05 74
    0xc81d0b9190802c5e50022001c00c80071f48800803585ea21850b41e00203154008840c0283e2943c4046400c51706250407040e580e900c075903518400c40c10940740601815402e45648118818140d88415060502603c1405c44400002c0c2204030b9030b433116101440b0480c4481126000d0000e68641c80c00781e102c0401003082012901c001c1415415a406c0062051b4490103209060041c0b00f103901d08426109000c0c00514031401440d400007428030b01c4d0000110685240134590390360607860115914805245905950f2109148565010400c0f40350a90851070b100b65000901007900400d03114914204c104003442c401c1c0d05c140c40034401501c40f0380c0014203861003a582c81c40403a4cc0384821045a04081c2d0140003203900a41c0045811821a008110310141c11140b00d44419150404521041d43c40ea02e4a00100024a01048100c2d1140c59a402c102d110000c010038084a402d44546c8841c80381c14107041c5410010402d40001d5503440000d0103d05c8602a204034102d0303402202e03003c25000d101601c1b070b090010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 289373633 1250 289372383 289372387
    0x203210a0f18030308100f0e0114120a06020d0c0c1a0a06090e0f07080a0507180f050a050411011d0409050f0d0c0506010b07020d020f060915070209010b0f 68
    0xd0506070349148512441c0e00c1005414007000000240e4a002d8000840c00381e2540001404c003500840302d250380300e410401520340040e0040010035441883c090450391810114480400c400000401c682103120000c001407144d401030405010f2168001c1514030481d0700204440c14104002b503d45009002d00540100d030101150600310050021895000070b628800041080e00c5445803401c607294100c2000303640d80040702c400a5040c082007414040d1890200034100e92515a80c1c2950b100d54900410010f000c04502400c0c0345401134001142d2480309040078001c0d49800d090400045c0030498050790540d004110401c481e5018041050b01d960841c2e40b110602061402444080c00c2600021500d0348141187c540b460b0703005000e51030340b0094030303920184000c41e91f081041c40c02c441a000b41105101c100084401a5a241480c007513442d8142c4844400c400b60b000040c9840c0602d170b13441c0f030300f006000310194003004020005104c542c0c400c440407a4980d032191115916405031100f174140c28441 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 289374883 1250 289373633 289373647
    0x504020d0308072001050412020609060a0f0f0c0e1f09060305060d051e2a04090201110d0c060f060308070212070f0b0c0606030a020f01050a2604020321 67
    0x2048100c03c0d4003080c0c1e41880008403168010714014020200345080160b59900c2c00d1208002819811b58076040c142d2008200724104001d01980340d20740a40010302856036801c03000c2e02131403c0e41021600a440c0313482042042c600c0103001d00324011035502c2c1e034481d030000007000c450f8074503900c0f03402c08010b07503651140c080c181885426002010040c0450754002c0d00203080300300041c0d0070070411404000c00791003940c0590034044010328084403200001c0e035152109002d01b10707801d51404503e4610710100c901280b056514001680c030044001e0309441d85000315001102680d8000ca00b40c50038078850303541013020410000d600030884119000041c8400020400100075241013080040c070418048c041e140d2450342c8401116881c000c41c1d2040742c90ac20040394a11039540c0611185610890a4000c5c01c0010304950000d0244255811880c0c1805008039541800c0c620440b420348111003030080030818079180c0080c00013401e0302140c08900c42e100e11035407880784190f40700004800300d007080701090418103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 289376133 1250 289374883 289374887
    0x6170a060b1e070f05030a0f020d0813140d020303100602010209030a021504090c0e120109020d060203071202031801150b04030b15091515070309090203060102030708040f05040f0504020d03 83
    0xb018a40c021044541403002e000800c00420140a40070710a800030340d0351b11103402000d0540c01c4420390b04415034000031203055900343c10094090307002014045002d010041447c000400a0135042d0300c000620a1108030032015400000941c0203075040c41011100f599144400c078241d2048034001601600b20003480b0005003803002440c1c491601090980e401c160b200c0142c03104603110014a040090400c860b0f80c6050b040045400f1410400080240503000042c0c000c40d8003080c2602005060541c0040083c9609108403d040750059504e5020f5580e420a01d620745451500c11010400a5103040742034030400c200b4440103401c450b010701c00e880c10702c1e2031600c0e002e11800004180c41d40441000740050116034494040171710545200d41e1104010030f00000340300781d1581f0011a004070700b000300010307004179070000b61540c115200b007980980c1e20f58642004034111300421a008140210111340854800b0210410509441c0d0540d010807504495800c00c138180c0700240e801940200006d124500030034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 289377383 1250 289376133 289376167
    0xe07290d110309070e01090c020303070e1201060b0301030b180706030c14031e01090c3903020307031101051b22080f10020c030a08100503060106170a060b 68
    0x40c204400190441101a240855442103904002c0b940000d1818000b0400308019680542000d403c10812040351540107952448060000d10034041d46003120074142d50780030200104441c2e01002401019660f000d01c0c24290003c0c0002c54540e1020000079140060342c21001070554404001010341760718100c030590051060080c034104114603004c241c3c46944e2184010b501075030025241c100600444070300c881001c0c0e01071300300451290809095290f0541d0001500c26141480307102140440c4402c0c00f080c00c0c41541e1101c1340c07200c0940c0c01c001c4040c0768000c0050000d89000e40c803540b01e0381000d4414507080f25412180e104ca0320700400b4045c6003020303080f005000000e941d80ca00f0703c4200c2c2984e8000380c52101513401042194019000c07060308400c2800b0715000640d40d00c000703508043c05e007140103072a401007400d03107010040300000260040d82c8562070b0100500002d81601e0b040d5850700001000c1c2c1d082c16210480400504002c100d102000e441140116081c13211480c3c10600034160f448200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 289378633 1250 289377383 289377397
    0x12030e060909071b08040b1b010c05040b090a08100b01020706090501090b0705100911010314010506070b100308070302070f0503060708040b090a06060f050f01260402220e0729 77
    0x414060b03c0d413400040c04800244041c2203092040d907241c05e60ba41c219030302e07030100c1c005005681c2d0500401d02a56508401518182d59024003080e440d50301c04008120400740d20350080010303224034010155051b00035841010100c0c0c0c207034241d540442e120202910100c240f4811140055001c000c1040400980340207000b040c0c0c400c0041c0c0700c5500100030800140c4405031000e8a400c00d99503404a115a0503101f0101c4000848000030203a41c5410001012405160360103421080b00c1d034000ba4024920600c080301031a4007130700c00741c0c862046040095441d0a02c0c06400f01c0303c80500e901003200d2600280e40340c440c0ca815524082150368540e1000000300e009000c800551244031001c0300000c40306c1c020345002d000c1a4900c9140c140c5050100072109a01c0c0402605000c0303469840c15880900803240303040c03d102c1c0200d0840e41e44071031020a119507562461038052940c4000d0f00e4000b000384c2c0d0040c1000f502000d08450107544c403810f4905071011240800b02c054541c010b40081c00f40c20b064007800b56 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 289379883 1250 289378633 289378667
    0x80705040507052109160b0d0e03070206030a24030209060415260d050309070e07020c1305060a0b16021e04150e0901020f0307120b0a12030e06090907 66
    0x1401c428000359140007020380c54561204d803640003040a00c0604006c20802c50340c1886003499801d2800c0003041c000d22590100440254031440303444200c0d00c080045800b025030103031105a6a140c274071070010043c40c000700c0d00031110b000000d10311200016150303d070060b65001003001d038a60300c8110030000100310071114007490404045000840292070444542c00725101c0d2103d120740600d06003014103080a6558410034402d0501c18480c1e03030200051004140c91400c0a001d00c071380c4a143c230a030315280d6a0340300e880d270010190a0110680f40c80d900100d003d40b8003030300c0500d192502d8050610083c020078101c0d03041008409440400341c030b032680045054020210580c144480300102040a8525103200081d0f4042084800c1000098990003503900144600c021401c2c4440b844010503d4030000d808101044031010600f20114440e601c1901d5408004184480b041e42da200424140b281400050303012031105d14402c407141c01c0c098100c03408038000074400e12aa5031095402d5903c82124804090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 289381133 1250 289379883 289379887
    0xc09040605040f090303060915060f0201060b0706090210021b0d060f11190906140a03020c0d1116033503090a0b06031501180b1c0c0506030108070504050705 69
    0x911510b9502c289280c1c504546004268100300342805401d40e0754990081c10060b20f846820009220456006d8055903010b07d04000c1c0550a080c049016000d6500716050101d00016032500300f01040c0d1190604c54030039500c1c0048130704c0b8100d00740c0e103c602ea0fa05407180380c2c1c0c04a6621401d4030f8818007201403144900c20020313101c4001d9070484220b4103240380ca98100d42c0001150703042c0f41c501541440d261045450844e01690a00d4001440c025250700004210721010610011032400791b0191041290b0b20390440b2548020100d000b0554052002d03003030024000c0c001c3c61031300c0290300d00d044010360340c001054a02c0c16445d03100903070040c0303c8040140200c0304150301051803010340c00c000303500402401c0300400c4010740504107401c08490182845129a0080002c2e41104040c1c3e407c0c141142c40b240c01d9121080341d1013110201034201c450040d0340c0a459000c41041070044c034440992024041d906050a00c0e0700d880a20915100038003070701c011a4081c0310204014506a0040c80c0e00c841545002c0d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 289382383 1250 289381133 289381139
    0x1090b0f010801060e07021c270311010c05031204062004050301050105010e0d0b090c0604030605150303090607110f040e0109050105160e0f1906050309150705030c090406 75
    0x20001564a0a82081480e0041004810900940d8090b004645660300395040911010f99a05040110313240f400300c909000f9040795000d0b40842c0700c0c1c90400c006190440c4000350b551840000d0b40e02080350f00081d0941423003125445000d205c0c441c0c030380c0400250314029007007180482c0e080d00140101d500603102c0700065145402030310802e900c1c1b861107050a4542e8148010542502d0b0141c0000d810048120b9000c1a00d580c0d41d401c402d200d5170010351500003a1141d4060034201060110400d8200320000340000c2003091030b0748044d1042c00b841078060810349042d03080646038451071440702e81c0110288560700c0170442035410b01142c654028240c1c0c036a2816080454107544160884e00c1450359100044810310800307014003a8400320a0402d0950000c40c00c1000c0d21031503140d04414080c0d81d200c002d0411030b869650703c841f00031440c4408060f4140d035400c0300401903401103909c06428000c41d60035210072611000c13803030b016503c1c0303890b0346081d90744030054026584c000c0c081c40e0b94000d468100c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 289383633 1250 289382383 289382393
    0x230a06050402040f170c091303020a02060c0304050a0509070f080c0904061206050f0405100209060d060f1a0f09010c03030f140703060b090d0204050601050c0d0909061401200109 78
    0x8100030225140c9090007585840900300210605c000c1220355600400440d10f4a9512901d145601001903403d26441c02c445080c100d2030725195820080d00300034001150b207107002001014100b1184221884031495842d081400340e0641c003074076510045030010b0040401e00e07000d0805c003540a00540409070070403840c84002130981391268010703500031522610000030b1000c903008055009008000c03001e51403c0c6581e07102c0d40e80000c462001923255011420031880d17541c0c24229102150345880a024480d240c4058000402d03a0f84202d207200b02d00500d410704451030032411303070715504622000340c4d040c0101d000064500c8452001c1c200c041640d0382c140c00141c403001c2d12582d901c20036142145043c1c0e09d0304000c0502101e00b25000b0703040da40c41c280130820030340c2d40d21307403c0c00c1c1d04a0341683e0106051319014016580c9000341d98040d942d50045510480c0510b81c40210b120455414a000340041592603010795031132507929100c0d60000c0c03030400c1a60408035880e41f400180300c0c4801d0000590500319192 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 289384883 1250 289383633 289383637
    0xf030f06320a0b10090621061805010617011a121f1d1b09060f0705010f05060f090403020f070608101d01060804061d06040510230a06050402 62
    0x704524007440303003030121803002c41c0720360300700a035054940b54007003141c050700508940418885e410410010822089034955000344041c4600c0403403c062040da0b44803440d824080301810009003d06143c03400006106102e4104259002c0070351070380f9989030742000403901101c1186080c4420741c0d401044003103603460001107031901c034031000305480d42115110507846540382c10701d601a0040c80c5100902c0c0d40c4c0d0181194000341c0000d81407803118401d107070300d40d01c03150503010313245030a0307031240e004600070034502050030007400001c0c4a0002000002440d110020440b1821b0320102d0700a192005280010b041c4041c88581190083c0100e80004913440030091078900d41d5040380340007641a106200c0c42c0101c1880c001c01600a42d82621011090032001002c02541407250f14100110b8801180500155034030003c6048040c558074086100a82e0201e82c8c2c950003a5001c442d03074410311060845c0000c082c0300b1115800854019041002190f901001c5035400161400e0b100030355070000041d2565a503c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 289386133 1250 289384883 289384961
    0x30203040e04050f120903030418060f0e0712021207081320030705090103080f0307050d0504080301030201170910020a110607020a1a0c0f180411090a0f030f06 70
    0x400d0803130310b1900f400c0e090031040020b01103080350901081e50b407a50040295400d49901e0003403124092005542c02010300066406080c12040c5c943d0081141510488031501c210f0203612408200d5000e858010304910920803440c9058180c2004201010300c00c40c2001d8005052074a4001c4c4061542c96103407038030440082c1c0e0b02d81c5202c04440c414144c141848104018801200c00503007562440d180c554143c403480e0340d482c2078443c0002c0001e990034060419103180f1114014204218940307443c00c005958821b00040e8007060ba400c04c0b00e0110325581c2c1149100c0c205a2000e400310381411445203000e9005005c90f041800030459148410b2401001090b111329400e40c01007200034140d050100403442d001801150b0221084100032001703c9240c00c036034000b4449414980d68486841c0024441c4890390f4000d50b0250606500500070002c8102520200c40200c41048115544100000c65403401e4403000f02942250041080419070a42c800a110b5001d80e112034080315400082d041c030f04100413 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 289387383 1250 289386133 289386143
    0x2010e01170a0e0c01020a2a09060b09040b060a0212031506180f03031206010f03091a10060c030c150b0603090109050d09051f020f010e0705150f0f07030203040e04 72
    0x1200040c00101c04101000320b801e02800a00312007074140d2a1094400310b030300d00010300181910880b406d003c2110b008d0800521050740304018407a201c001c0185554841c0d05440d02c1141810320300041da1030084103c3e4a490f2a82c0c00810f074640c515021400607410007000d505002590050444c202e481e010010710025440000c102c803070321000720421a404d0319010f03e99010b5072044c40100c00283c455408036400200c24240040f542114803400c1340074024006000b0000075443d29404000281c0d911650300600000d0b001c46034403500c42034102c80c60559203402400003003207401d400c03000c50360030322840d11600d070003441c04a85207110b100414016801952900300a03076407100c4035014490140000100c01c0010714001042c00d10740070019054085103d80b03000040305c0c01e4000f180c418002c00803203100c1c4003144001d01401c904004e440c1c0d02c8009a110702c0e4010285001d1155082080714122044102c030300c0380c1282000302d40b40003e900350704100400c4081d88400c10010480410781c00c0d2a5206038444c0e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 289388489 1106 289387383 289387391
    0x3010f140f0606130e0702060906100e1512030a030e030a0c141509030406120510031b050901090504120305040b06190302060f0a080106020606010c02010e01170a 71
    0x24075441d0020144c5650700203811107003100014032450894094442e143e541c801401c0c0c46800868501011b0f1b110b64030113001c1c11110120898202c0d480e04100c0311000200000700c1d080f107040c1400003c296001189101b120f0b80e150203080c0c924007011000c0c505041d850070024041030607101c40104080b9a201d1006441a810040051904c0d2140318004260400a0308507440758024000c05002403c400d031440340c180c1c51402840c0c000c00c00d4107040c40c41589035890f8502c0385850210080507010001400140c4c5507559070555010b050354590005480c140780c03a11514150840e4062000e040c102020040132840440c10140d011400b40d50b42c0c2c071020b18048a07600320100c82e0b0002035100c100800c0b03042810344610040c1603400b061341ca42e50104d91700c0b1300007070707030340311803c80c0c0050008061101000055104110444812506050402504002c02100c081410040f144451001e9407 = true := by decide +kernel

theorem cover : BRFrame.Cov 289208633 289388489 := by
  have h0 := BRFrame.cov_init 289208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 289208633 ≤ n) (h2 : n < 289388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
