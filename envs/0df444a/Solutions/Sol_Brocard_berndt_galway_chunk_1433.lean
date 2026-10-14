-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1433
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:58:00.784783+00:00
-- url     : https://prove2.me/submissions/00d55338-b82a-42fd-9b7d-773867c997e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 257553956 ≤ n < 257733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 257555206 1250 257553956 257553979
    0x91b070602030c09090c031003030c0201030f0c020c0a05030f070e060604030c12051603050607030f0609110d0b0a2904150305061912030305151203030412080402060301050609 77
    0x250180300440c807641c3d9400046841c2e0015500744603045000a26811964804005101607000b11203c0d4000f00c0703505240c982120450351004801411000c0c0c04c0c0100c1e00d017807a0080c0c51680d00461103041090065900c1d0081654a80426a882c000d00702180d096401caa0402c0c80714a80d40303800f081e400358010705641c0c84e1030340d80d40d03aa481e8545294081c8641503660610b60040000c144440d0000d0710800300b05078005419921140c0e201c42000c1e200b10b060540e02c9540807010002500120020006001c041041010403d0032103c82d621550030010080d1400c107840a2919158030003d080c0c6034aa030340c0e034a10350016107800004d104075600760001503109210001d5400a000302860480c28207550105940c2000030522200d881c2c0544580d0042224a02c244501e0035200f03003410030960075107804074468441111040ca0105440c0010341c0001c05100e0180404000000a6001e540304924030100e00c10325110448071182e05940007940300710100010006454184080c10074440d00424440d200b4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 257556456 1250 257555206 257555213
    0x402070c120308100f060e0f030d051323120708101e0e0d0f030e060403031508060c0f070812010e06040b09040c0611121210080c091b07 60
    0x100030581c4807154085036009020201944880000e070058000c0d10132480c514203041480712020090f00601c0e007000040c02c46110141c0d2103580407540c00c01c0103416a101201f00d480000d00950003040380d0300101845080000d2301000840d07507004c55114220700701501c004124200b0070440303000811802e01d44a45440480c007184240f00c04038032070100440004403001c6c0c41c0406450955035083c9072140700d182c00c00460307c094010481c0307801d0846030300c3c103000c5004c1404c030160f0041428522500c41441100100420141c0650120079564100c01c1611000380d03940c520755076946001c50b9a1800700304240b001c2050086c0c240080c0c01c0d40c0f80304005407411b01c51018a40102d01c00c1c03d0340105207089088085c402d02c4c0c01c0c41d10a40c061508251030b191000e20b416210001066620b01c141d40030031000c2075a11408840511502d2581070600351116560074000d0030343c40d611481174445081850000000040c800f00000344d51146c45000741c2480d603250345403040c0341c0c0c00b4400681000e040310410800344001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 257557706 1250 257556456 257556473
    0x1020304030c080106090606080601080a0e120438220509040302010b04050604060614090105041206060317030402010f14130e1b09090f06030a02130b01110d0f0e040207 74
    0x641080303800051014038122a040c140c688a80c044800d00890109101c01039338065813850740304800d05000314461312081249481c0441e0031411010302071011034003003a26005014518840d081e00c61b4400c142d00c20307014444501044d414850840210104054210903102030b11000c0026561006400381070358030030115203a10350072030b0b007100182d41d212070f284000c0c607280c424540c005000780c8041101074240b03a809010030640001c0d14a80d40c40c040381000c0168419400c0340c011300811628040070b00c966140400280403180422200c80300411150300e496120481a00d1040387c05a4a1605082e103140c070030755508a0f084512500300c1801c001e20840410680c440c02c004050300c012400051034104c803a40310a1a4454401390b41103020000c4121a50b00c50031031030380003142c2c4101d80c0401c0c0c031884000307407503c4411a070080d04441c4142d0003200f20061a072005203000c20070b80700d0482c44a154114540c840d42d0450107040407503640701043c3c40e000c1c03044100c42192a00500014a0100151924910b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 257558956 1250 257557706 257557709
    0x40303061205060612071a0d09060623030109080d09050703050d0f0305010503030403122601030f0201031a030d0e13050c03010816030b010e061906050c0d090806060f01020304030c 79
    0x4440e40582c060007280e0174403161041c0c1e00c440c02400b0705205401c00c02c8100001c1d010700003100300044003003656600705025600c00141e20345e000d030080007001da030345003032102101c6103001c10b410840780410403280341e040c180140da19040d0320010640c81d181d10f0a201100410007698281e038244500f01e000310014a0405c19900d040346541c40302103c000b882e0b20000c1c1921130580005029400a210810020304400241c0d90050b00a00f80060042400c030704040f902d4442d1035800c07e008100100000c18007800541100c0d41600070317a018812054005802da203d85c3c0c0805034540c05500981a400c1c0c4541f040382141c0c401d107001040500c50581d5a100728003541c6017034440c400c4c0400004010071034504204403240850032406c4481000030f24603110b581000d84140706040200398540b00003006652061000c8100a03c0840c9001c2d200c4e460311382c02011900f0403128001c2d6407140c0220072411a01414580c0126404100186000ea4521090000e0f482c0100101030551109201c080005040c0501150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 257560206 1250 257558956 257558963
    0xd0503090307082505090402061c02190305010503010c0806040e031b01020301050f0d0512031503030a020c0a0902040b07140a15230702060a0509030f0703051c020c0706080403030612 80
    0x100720a0090013001103500703906100703800e05500c00700020b850b422800b960098040351036a403200350305901c3c810000a20a02c002d00d09200149060000c58103c1c031031a802d141c039130307410416a0f0302c0714180b5089441400074600490880300008510b8036003904640001d01001d01a2800c02000708101c9c08090302012214201d40d4002c4018807590802c0001c5410103103003150303502d1090400d078403403035151400000143e416800001c000382139016001026180741c075000c2d045903500c9401c024002e4a42c3c0c8801d004510809500300c000551340030a00a0700d05680240c5070310352910113182c0d1800340c403100318480107115000c1e10300034802142c4070480c00c0c04141d9100c3c0011400b03200607020a80704280940e40b00f00d543c1c2405090220303484c0c1c0054059801500c1c800009110f442d1201424036501966200310390714a40015418105503008001c0c110880702c88000e43c512000c89401c07581640901c0801c3d880c6980500c00c00c00401c2d00c6883c1c143d8015000c0c1c2800600d00c1e4841c0c0381c03120111000071058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 257561456 1250 257560206 257560213
    0xd060c12020d0b240d0213120503070c0b0307050a030b040b06030405030d050a050f040b071211090102060a0605030a1203090c0b030402010e01020f0619060807300b060d050309030708 80
    0x10388140c1080c1c0040c1e9168a004194410307415204c035000040b901401008810459022904282c078a2540760a24050204100310303680d04011407809540c5da03031155008031045034100c0030009100c10000207480c0962090f4035414105104214118014000c1c50710380c90340315896254900b203076210b17a0001e50140340120065590790407044006000e03504050001c004280c680b004014140f20009401c03600264018006a01500c40d69011581c0c0354103890403000b500e1a01c5401c0d003402c0080c20041c48040c0d82a02918000c1da00e00e180e54084400c00d10940750950021842d600000e0210702042009040b14100040c60f00c0ca1900d070103201400e15000704040d12000800d20080d5070b085002c05201720b400340300900051001104040c3c640b000904840103421840082000000380d9030000d0380075040754007c4030a0aa519080a407090442c021600f40040d401c80c800c0c4004180400110b00460b00300302004521b4413010140050780811308826a0240010701c00c0141543e010300ca004010f01804006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 257562706 1250 257561456 257561471
    0xb0d030e0312130b07060f050705040807270507051e0d060509130803062106011401110304060503130b10061202040513110405120304150302090d060c12020d 69
    0x203251501d00204120742a60b9010301001c55220b0000b40040c00b41c512802c6120f40ba82442e01c2c01c03070302034030b2074001022078541000200141c45a000c000b40088904007030413160420703030b608103001110b0019072403591141110b204c3c0000e4034401390415038010900d840c285291207c070302c522424042050072001a200d0000898048180032402280064001291303402d15a003003160103a0f0406590f28030081c000f402c0400020440c3e520b03000d940c08080891507880310070401d40c2c15899100e86090044902e4400c0880007c0510751061a4655140c0c181702c00652074942408815286c54200505c008414104014030b4400244000d40c1e050083d250b064404208500f082000b41c9188000c022118132a88140701c10841035644880c00f204079a000d05c03001801190380345c140000380c45030360130140d080540021110b4000030004020021202900003d0003d00c80300e440450586c0b24000c401640640140300b040003140b110361010b245011141030140b41d40310061507801c180d811045078070620039542d090 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 257563956 1250 257562706 257562709
    0x160f02060a1d15070b04021306030606090e01110a030905030915030a0b0f1008060a09050c0c010507081b0a032702011205130b090313230f031c02010b0d030e 69
    0x108800035240c103d45924200407a229980c2c0c2c1802809130141c00000801d02040079501e40d80301600440e8451802401069224100301c0c0c05130049200f2900b4640c58404000c2140c0018400c61194030000910700d4540307031038500101c010b4602c0c0c480555040c0020010300c2e08540d01d072824a0490114803400d25200d207040d0000340d080311500d4070b03803078081d030341c5400841d40350303613444002e006510054202400305480746000b150040348550090040300380b40c6014445104180009032101000c407500074802561103070f0084138520002d075100e0201c0e03200c145203102206118409010f8100c5d1501e80014441c4e100c4050101e4802c2114041c0402c50140c2e90010640d64000d003412000c1560500501043c2803a50886440404542014001d0400000800c044140510403900008a42105490070940f200c1c1c0300e44075001101610a030041d004c550621883c01c02c61440400030070000c029203441c1080b074502c04845e81d020005a01195038815030406c0e15903804900c1058107006c0d50303c6900e00f000860 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 257565206 1250 257563956 257563997
    0x12150616021908100f0f0603061506030b060a0509040f050a051b040b0a05071514220507060f02070512060406060b12060d020f030d030b150708160f02060a 68
    0x442c8601d0b8149110014000301070001000700561400b00b1000642000418030f040040021008808105080450000610a29410070280d0b25051181182c0e1103982e82d8003078040711901500a034010340d00344110a800c038043e002600e40c4010241000c2818030f0a02c501800301e8800316000025241c0d03070320a001e0b03101c20441180f01c80a9000701031303601c0e207800c0c0702c55044a401015060001c1200c0021481e082000f40c0e101c1c00c4141845040a00c8120095441c0c81656042114010307148011312884131501d25001e10a600403982000281400303504003282180c80d640c2c5900c124080d44038010300003507152202c0d00380d030a54080c81005132115040a20f002e2040d03c5480c0c3c000c0800703130014020f4103034032a284100c10303030807030320071a680109400c091010030195072120010707590501401489070310307148e0980c00445444204175064210b110716100040694010210013a0400340b00b40f020344188055800068038442c0503986690b094202030b8001000c0d940080c1c020400151100c80d41421074031040d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 257566456 1250 257565206 257565229
    0x60506010f05070204090c03050714010f030b0609010c0212030d060509070e03070b03070c0b0906040213061206051503030c0d0905100c061e05070302090102060a0207081215061602 79
    0x7403030024041081e11000401901070310348043d22a95a41d40008100001d006141004583c49000c5d00e40482c0d66a41e41800c84503180103480c01318aa04040c2404e95220741300d50b1f0b206100050142e07081800403801100d03000450307c0100d80140ca000030001c5603000030406020801d203004000700d0900d003008103100c42643c001d0301c6a8240020020f15203143e64002c1403820503200702204454076540d6501e0115102d560081e405042d441d030f00d8050080070040411510312581c000c0e28441c6028203942c0c070a508854541c07107000038400060ba0b0900000386142c21003070304400003000700c0d118515901c00180c10360b402550790b0481d9510101d40107c81e40e400c5200c03e4001e110840b88030501c80790306907026080d011041c0300180315980d1404200390903410402c590740301500101c01080549000000a00290b0259899030b01512070100081c0c800c0001e4000c607070101c0d0b0f0010845080003c110345181007240050210040c1448849918020740c8611014041241255600300e40840145c018800680c4a6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 257567706 1250 257566456 257566459
    0xf0402030c040501080406090209130201022e0b040204030606090b0909060c09010c0510050106050309070b0f2a0a08030a0c020a0f0206090a030507030507150f090303030b010e091003060506 83
    0x18000c100007912100256002c0303c00a007400a0365503106d103049030041114840c02544028030b82c0a10503482c1d0002049400369100303800700c4950021072030720515486c03400c061101c00081401c1c651240e4500300d40180382002e00182000d030070310792259501015100700d13801100143c0d035114042903062902814440d04441554007401e698141440c1b445481c2c0324904400d414004c13205401420024100448034000801c00340401240d6160ba000904980c000d4482c402d582c480d8050208480b8005400c80d030403401a24950b6140041100c0000204410401c1d4176000708890740403608054424884000c015200300641507403440e042da0740c201140d1031200008115030107902220006158070400d012074030b8044a0468648110f0303000143e0344201604000c0c1540600c4c10300100304100040c031142a9420305441940d15240918120f4940244515070740010f5500c01007040400d029502000c000310062500524603503484007c64644007059400d042400c0c0d0100301002404040c3c0301d0309410540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 257568956 1250 257567706 257567711
    0x11040911181e0f0a05090405060702120c3c03040303020d03060303080f0402030304150e040b1903080a180602031b030a170901060909080c010b0a031a06040f1a0f04 72
    0x811035882c2ca40070007031040640106141190458140c2da842d10410050000510503100c61405103019615098261034a0b009441f80c8400b200f4811080d03001d03188404041402403440c5459507060602e100200604007a00100591035140c07000c0c0c42c268445040c0d10104006d603a41c030310354a00280380802c00d002120806150034000c1c00000e501404054001d680c508550401e41c44d1400001d0070b511465203e0300c054943c10000d44c5880350014901c036414403084804101e0502030009100c451150342410113102498880c00303000182c054000b5202d108850720f0881050000d0901500c00c6929541025000d6030002c92490003072013100c0c0d0b0101d040000d02d00590700300b5140301405801e2402450078a40f40301c0b5241d00083c0d03902800d41c06480200030500d8244030420307840c01d0075560f503031240701e00c102c107942000000c00c001d0419941e45021258043d06684c1010081144804608009082c1c103070b115884480810414145008013b03000440407144000d070003080b420032002c811386904441c0600d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 257570206 1250 257568956 257568979
    0x120207050a0f0902091203031009061205150a022101170d05090d080f072603070e0d03020c0d030306180506210a2f0405040b040201031104091118 64
    0x4107165002d404a035240d400141e01e8000e0b41c00060410086071484065900c008401c0200e840d884e03c15101c1100c034400001c1192031344442c010784d180c0b6840074001c1c107654400000c45882d0031041052643c8100e070368000605003506d611500d1054801e101c85001d01e460503c0041c0418090a03901d01012a441d03401480d05e0490710b40098224025880d08502c00c40c0b0056044040c095082c0c1141d5114044110456580c9581d181c6141d0b5812000000070161084180d54409204807004480c0101081d8480f41030003070800b41002481884940d00b20110b0261028941c040d031038203042800d0551007601c1c0820a18101031001901507056208840443e0402080c842182c5070f0a9500c10080c0c40c0302c1d90400140d007a105d0765407401c00350703090080508400c1039000c54100742c03982c0b00e5031525030068400300d2003c0d400001c0000380e4106031000b4103c50f400c4004980158020b42c06100c03000c0c0c00c0e52440342030079903400c904030866001081c1070340110400118030788144900256100c2d01c0208681040782c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 257571456 1250 257570206 257570219
    0xc080c1303081b120a1701030302060f0a0212190506041109090903090a0305010b13060506190e04020d090b070507081b0111192a08030c16120207050a 66
    0x420522000d040500b0009000c10203016000c01c946441c403503182203445110042203e00b03110760044035103500140b1000070300c0d01c0c055452641e01c3d040f240c250340200440e032212a010702c20b03c8006880358480070750070449414100790584c0000d00c1288131000503c90311240e0310034003081d11002040107114610313010700b41484224100c1034451154040d11000540d13640c02003400c0c0b0794420b000316130368802c40c5010004104001504204d6081a060700c062081c0400d80c655082901d07142e006050b8459000d21a40040c0e030703162580b86c042c00ca8107140601043e034400f00801c0499016040c180c040c02e413141e00b1302040c015549441d0f504800c207072400615045043c2c0b80d00e06c481c054201002250103404804607001c0360250402c50110304022040c5540d00c80042c1c0c00200449410b21080c04070300032480c408107a00d407056400401a828000c01c800b400340644d1039880a510040001080510601401c400d141c0101d540140035441032a002da403910b01035801a28010160b07121038482c4600e0801480103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 257572706 1250 257571456 257571487
    0x5070303020903030405040504140d0915030e21090306092d010e07121b05130207050106090f1512110d031704030906030f0207050d0c030c0b0a0c080c 66
    0x45a4161800503200e42103140001e0035440b413039028541c024288000d000500021603036000c0300340102c80031902d11452056040c1d4006000b0b125800051950001c1c0d04440c50103a049070384910003020545603414a100790b04c00341e40168600c0d01115040105042e6402c0c2400c01103240c20042c0000149611202c80c110002d044540d0102d0f481001c010b201000c014140075000501106440019200f800d51100807410800f444001c4c1611900300c00300320b8803440048980441d0545001130411080c9440b440481006940080f104441c990360741c550000d5003038418468801441c11215011440d6885441440100c03400740c0c11408480c1001c001c243c00041741001d03081c41c54901601d180507425428101500c03214444440c001042d042441000100740e480404802a40c100d5141003106030705101c050402c90086100007006030f8001803211107068000c00709107000c14402e2400c1c500300101c5555500300c50509640917480181c46891a01c896900308080582c001260f042c02c1c0d06084d0580c014501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 257573956 1250 257572706 257572717
    0x906030711030c07120b07030b0d0b151905120d080a0c11010f09050105100506041a040803040605030109050c0c0a0f050c0409050604290703020d1b02010f050c0a05 72
    0xa000d1079200c07a14040c0d03428026030302d200c031140064498482e42d4400f00e04828035030620894400c5100b40004020501038802d20034954170140c440942d00190360b031110045200070f04001e00c100d4101881c5003caa56181907403082c080c40151102d030a80c50070092280783c8400c03030b065008a422580144451a900004495210148080c049441c5040c080c09886108982101e0820341d4241a04404510155001440158400c000070001341e0354a0f1600301424805008a5600c020104010085545045840c0064181d084482441c040e40c1d100b8042ca140d00a50101001c0340c000720042090110a10886500c442d40030051071a01e840307004019140c04908000610420289a48005204d07003006040e20029000c4d0080100501e0390800ea030390366004036000c5400100c90b64590104229105814641d00348904900185482e541010380c00380d08102e1802680d144d403085e544030417911800310120000b82613000003425504101d11103084e0b420007807802d107280b20100201444168408110f59 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 257575206 1250 257573956 257573971
    0xc07141207060507031d0603010e041110051c0b10080910020a0918060b032701020705150912041d070c020105090f0d05010203180d4b08010f0b090603 66
    0xc040100c0110314809400e0103900c0076400c0700c400300c000b01c0c00403a4100c042f0301a901070240000c030325842c80100003000050502d0000050028041e000c0c14551031012004031041480002c10450589408606000c03000c0d100c0c1000691003106000080d5414400b1507286003c04d01c0079840c040310300d403000c0c00062441c440c0800c02c101036010255450301135800f5101600d5003d445035517030304004a000d0880c09030106a1580716038402c1c000070f82d9550500c21524030951060140c919641c034140d0494002e41300610310755150155002c80501880341000801c0507004100800c0d04e41c1960124400456000408510a00140808050143c0e820006540c51a10226250841c00e209080401d49020f50310000500702e40c004000e00a05403070110181118078100760440b061341407600012190807c0707801c80080501c90320318000b45941e0103110b246509603e4a800e05000502c2c100e484460f00c00102e807a0310000341004014486d806903945400020580c02e0f50250500c0480700001d42d15110142510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 257576456 1250 257575206 257575217
    0x90f0501080f0c0d06080d020d05030f010308030618040b041103030c070e0a060306020c0a1106040b0a0305061206090c120a05030d0c0207030503030a05010504051e0f07050c0714120706050703 84
    0x211007010309002c075113003030200c0c0c030090000741d83d00d00d451980c40c100903c10344058050791070103240c52352060040c0da1182e804003640c0b072078592843d1600f0b512603001400030364004407130713100b402603200c00704081d9801f9030b02c503280f000038502c2d06007020035078881c0c0c4d800054400e4204010060800000041c600c4c103441682002d10102d03120803da08004001980c0014011400440d0240000c02d010440c0944540075403141040804100c00b08440c030300c25400780d02d8050805211001c28503209502c03003688410042c00c419040c1c41c100c8003451074894202d0340b40da41c80d88200d4001e0a5400e061410b000c0d5030140800030f00480d8215681c0d15140c0c0150005076102c80e5680700c8422086100b013009000a640003070503241c0e6130422002c0c0d01c0141038240601801a41084089814000b00e1506805081c1030956a07200070746030b5846600c6200f03801780c8241c1c200441440103590314503051251070024044060001c091141800030300c410f82c489039801d5030683c0c100c180d082051540003022034180c19030601d0304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 257577706 1250 257576456 257576461
    0x2010c120306051005030114011110090204021e0a030b03160306050603030f0c0f190f080a030b0a0f0302011d10050a170f041b030c050d0204090f0b07090f0501080f 72
    0x3100201220380c441a4004c80090f40c600b00399403c08001e5051b103405100300c20300f0307030000300056400a0000c0d910781d0007030f801110b10101d01d001d2030740002a030b030340300410144ca042c1c0c0150288580005008107481800b4000419804280c2c0601c1000300c0c1040a8019021070b02c0783d0a4009144aa68400a00340d00c1d19140001c0b001c1d9014411188040301181e411602c95940c0b4003400d681e03442c01e05100c04a07100d051548804030402c0307142040c01550007003014011501c7d0baa909040e5070403c900e00c1040c1a121036802c4082d03950740700c620000d404008020443c080c55800010f11800c07408c0d41d205031100c01c1c0c1014003103e03101e40f414600c84e1580d84c10520703610b0310689801c0750410034460481050107881800c0c8030520341032030702c0c150040d070080780400c01400882d103501a03101d00c6448010714001078568204094108825400001b60009000003103044a64540e801d0710740d814001107645004c854204066150046020720140002c84d001d5840c0c142000c1c0040c021071005441c0d42510300b81c1400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 257578956 1250 257577706 257577743
    0x40f1707031205061504120c120c0e01080705030d120e0706081b0721120510060e010f120c02010905010203010b0706061d0a020d090f050d0906110715140307270302010c 74
    0x1d42500901500c01276038407045003801c0245190206025800e44450003070300024109400060840c00c1c4c61000700940f80e6a4069a405e031281000c04024852458481224580d40002800050010300641d140c08040d407601c178840e072400c80804c00345918007549c2881510045000b038035154020304000301c10450321194405d415030707803200124a07480949040c4000c00040485d49900c0d082101c010703417110300025060200640b10380c04002448030000307501c940d4001140e0625040140e4403851400000b44403611a251603081e40d06c260002d103540040054103e0030000503109200007400340711185919078024100065031040007800b44240d00b500400c602d010442c2562010050b01e40c051001042c0c20514502580c0b03840d030141080021410107000004d60a0080e590380135011150b202600000e4141442c0481e061880360b80c403001c00aa81f8030100030003210304011801620300e0349600044828031010544040c00c2078141003030508600c1c50400060b42c00c00e042c01c05540e8086800e222a00141c0d2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 257580206 1250 257578956 257578973
    0x1905040b0d0f06020c100209060a27060201060f090e03040e15120a0b06010504120f0f0c180e0307022110060603091e0209040f170703120506150412 65
    0x101c000c0c0c040000d8503a46402c02580e94014a03043c0c100700309440d082124000d801d802c034010500565009003003006070b0a10544503040c80f9080740a011480d4108512035181103805004540102c0c003d40c1d5500d0052208002401d2594000c106440701801024050002d464607400789110340e614100024010582420001d4429100004007401480f248088413000582d40e6043c801b00355184a6080f01150041d4810001c403800e40f480710380310101c58403003551014a0041030800c16a0206101040b090001d1000f2010000500c072440e00304180b030102d242103070102d800c490300d03800c00f035482006001d0040e02c5452145001e4000f40020070b4a12000480e11820a08015111100146407440104807960907038440c647c102d00a0ba0751520180c5d901c80c20000080d0880e00203580303c14110002000115002c0004030761511843c450302e00303043d02c0110010550001c25045006c00c44038005011503c010744101944150b044844000c03040449407080024880c0e03014801c0d0b0892030041e200140704015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 257581456 1250 257580206 257580229
    0x7060f0509100504090c0801030209070c110402030a090302070801090c06030903020f0f21031b090604080601060e130b0d150b0918060c04180b180403020a111905040b 73
    0x18040c10a0141d0340c60b0000c0803075105010b0740d08510300e081e54200120348039003101c2c0e05880c1d000e8001682d5442d406015103126048410480d0400d46055051440351254006140103031014080421901013038a000b82c1055a203400901c0c050307140002d110040f9081d800b03002c0480c0d2487c01c1c001840300745800c040b03052069107482e480c1d03a841150003440d20504d00003052038205419901c101602419080300e43d00307a1005640300440401c0c280074210580b080e600040030304d2940100220701d030a41e50100ca500f0890264002e101203802041040c4040c10b0140101800800140c1c0c10030511101c50006034034505910806012117048501012520303013658002c0f6644900203015220600d0b01c00079205e05040c295800c000350307008202c08100f801000809a5003520b031841c4035601820b851409a20050500007e00340e48038a400401d034007418064030815000c4ca00030707401780212a03954189042640302440d0014000d0780c0d82d80d101c0030140b0001301d4a80c260f4200300c0b0089810f02c0580001114200340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 257582706 1250 257581456 257581459
    0x1b01050903010914010b0d0f080a031b020303070f050405030a030c0309090f1a0301050c2203060e0303270309060f04150207063f0915020d1401030507060f0509 70
    0xc2240300e0f07003400504031000a010814a00a016000c15001441404080c40d9001082152080641d0f00004e0300c50f40542418640d0389400100012810f844980304042d08242c0b4015800000a000300c1507032203114140440a1418082d28051914010a60350f2101c10005410448140e42c2d420405228900c14401040381000502071581c13200c0721080200040c0c40d89181b032501d880d0044610341018013400c3c1c070400210302d015003005084456070814800c00000c0c0413140707070400f101100040580c0320344148817002d04020340d01c9107000303629803020120508403611205008800040c0000d00002156540354040d03e44586440d900c95071070140c1d0059400a041800d483c07032a8912450303001420004840c0e5550354400405100b941c4030031600c2990b0706204103a0000c07000c010390084008420f02c01484000340c0083c41019079201c940010300510140034103d500051000400d8500d8003c1e50170060280e824901c95515550718250340d11004c1c4604024003a0040281c0603113801201940c002300d10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 257583956 1250 257582706 257582711
    0x80108120405064501110d080714070204060f061205060616050703140a02011202120402010c0f020307060306090b150315030a1707060c022d0703140105040b06010f021b0105090301 79
    0x1084d82909003080881035403400148903040d0440e12440004a040302010b454a548030262544917084500c00380c001c00180d810a0200048001619140320b000001e0a200c0251140c00d070401c00d004040d0b134030200d0380c180858246020b11130340e580c0e42c0b000c0b5110140240300c079404511075860150700f0014554000b40c5010402c1e22440142500800c045011038402d036250301082d26103503180000c030702038101881d00041d11480020015402503600c03040f11805000c1300900c840083d80000d15081d803030f8006400107601c1c1d079400c02016400780500c128080c0308a80c035000180c030010001c0403500005014210081040348550541c0e02d05001800d00c5070340008010305e05000305c40f13000b000350780302880484101d4542499034140ea072010409036410b01c01c92030f45c1007102010f04540554408240380102540c0210741001000030034065402c4070210f5032030000f040c03520303160a00141141008000d541440401068515070f564045074680e25221071014445030b4080290040324507004c0c0b0400f40e5010361 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 257585206 1250 257583956 257584057
    0x90b12060a0203060d080d050f0c0301032111010c0908010606020c030613060b03060c0705060703050f060108070212040807170102090a0909063803030a0504030605090f0a0308010812040506 83
    0x2101d40c1c021b144259051440342000b40c8ad488c4010510f03201c01d04c0050117020541a07030031288140c0203222410b06055180c08031035040201c141a08440c200c3c2d8406c00443c020030400c1215041c02e0050034028116400a8401001c80c10086529070b8401402d5130107010b856110311080147d6980003040041000d07080711010b01d49150501c240707a0258100713075914451480000e01251090040e503114072000340f009229074407403500540b988540038111800350300a041c24101a446500040d1008080c0c003c010240545011861050000000f00d0140241d004201c50042a00c4596103002241c41c000e00001d010500d504051000f88205940501402c0f8030b010070b1812040200c2500520b40d40700d00f01d508685104030101031352882510b4880010130070602c0f042011601d158450f076408104001a50301c2c008400c81d0031400c0804420b0b040703020035410380060011103401c200e520a18503508220070f242c14244000034550340160180b00038103019042020480b90801d1004250016800b2007140122 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 257586456 1250 257585206 257585227
    0xa050d02060f090c011d131509110306030606010f0e030a0b010503061303390f0b09030301060c02040b0d020d050606100507020f28030804090b12060a0203060d08 71
    0x40c1d41c15038001031a0070081010036000350000c514a200c03080c0585a00988840074803c140e0341400440d2083ea21008500388000c000340c050141d0f6280c2102c1e8441000000e0400070000101c558800c4400e40c2d0720010700030807080742c900084040e0040780c2400c0c048507c0d40c021034101c07420411000c0f055014018000303030804000c5880c0c1d6040c1611400c42c181c940590b12000a64082c0101e1003000d80080d1561807a2141c106030541203030b10b030305006200022403c1500c624854000c2004108070b03400c1000c440e40d003080c000003040c01070f04164040081c51940d49400401090480c42c0324010f80300301c1d030300c1c000140d89075100b40c41c2c0b46030980d001d4488030301d09a070360400030b40700c0f54120340c458003401568141e0940c147c03240301243d880c55802031080d110081c11006001c40c402ca04510f001d03020810307902a454810150f211280150700c5000b215640c3c50402010b60159008180e82c540184032030602040714480102e40316500a00700a401030f100d0307450000142100008034005410f400c07000401e003518 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 257587706 1250 257586456 257586463
    0x501060902130806060d0213060512030702100207080601030209190f0b030c100512060616080c1513110a120609120516030806030c060a020d021c021b030a050d02 71
    0x19000e072141001e0354034218a500c40b0b0341200c41760750121850140000515052401e1715201c82401c400240807601c0c1d00109001a00403040114150700c04910381013103241481c01c0d20b06c114414400351104610b49903503503541d00018000284621070a0340000c1600d40d04103c1c290244403400b0060001c020001c01c104000e020194400340280100d8440f81142e0400c0b400000071802c0c141d4aa074034100242481c007105a00250580c2d6100108105541003c0b424017020040c00380683d0195503120008402240f03814044880d9041824101c8200201d643c0d0350300d460b00b05640c2245110607001c40400015070720021a0b0000300c95042d80081100a1088983c46031000d20302c500011b2491040407c01628180035a6611000005081207030100180c400d1001d1508210040c040b90641c4416000084003500030a030101d005900080700d00c9402c4d0303410010340c03070b0741500000e5498034030a4445009444600064075625a04030b40407490125841c100413440000d5001419a000c01860b008001e44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 257588956 1250 257587706 257587717
    0x912050c1c0509030706030c1b06060506042706060c0204020901140c0d0315050f100e090a02191706040b03031e0913061d0c070c06090801110306030703031b0501060902 74
    0x85d1056038000300d040d60080c85a0400980240c0300c0407603c88210a41e83c0c002040c6000440d0020303126040040c454a032035020700040c01c054500b0005c40d4010740b00741003510b00071000e04480a030404500f0803100d60040400c40e80103030140d0703000d81c0e2002e5a0700140e4481c0d6044010146c3e0440000e4408003144002c24110300b0030250741e505000d241641c800c0101164441d004990380b00501c200c041f001450141c01d80030880a01741001594080460700182903920122014003101d90005102071440200d00600d004080349800d10501002888040110b1010b004103014011a501c081d6a060755800b0001c0e82c010201c1e5800c3e0b0100c0560b2804806450b0304480c011074010346012003280400b2880b801201c041d60b040328000f0607000c0e83c1501007115400058a0720101102c10040c10011440b81c80440d03001e45011b4807494901441d05082c00c2c211030f41c0c880c2c0801038850600900203a9500801d082048079094901740651030004801d200c01040c000100501a601e040360010304450240c02a01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 257590206 1250 257588956 257588959
    0x3150702010209120736050a0212010504051e090703050109150b0a0e0a0b0d0210020601050307061d100e0a0e07120204081c1803060f0605040912050c1c0509 69
    0x103a03100a007840c0d8039074034400c50040412031100100c80c06c00f03425080c505210303090807811600c0a110b07010404881110402d0b02c00e42185600020010620355081c0c43c4603004120544003000b0b1807038015140400020002c0707081c120302168a0102c1c1141200300300340c00265401600030000c542c01c0e441c213890b902c1c00c60800c8448407403d00d40090000d00d000c802b02c50450340440c400c42800d42d40d0001030001490400c10080d800401c542d4800c000da11100b06105035800c864000300055410312080500c0d11722580e02260401404145460301c8031450040d40e400c420742a619000b80d51200042520701c042a011300e0380c1c02100c2c1e0480003500f1140b0788a843c2c01070708640c407448003000070061004c2c183e04c03d40c040e181490b0701070300e210103000c08007011034500000340e4501400c455a801410151110443e4000c2d94041e0725901d101180a00031b01c01c1c5001484226410086030407182e9422460400c03500c0e1040501802040212a6400030720030b8400103580e0132070400d1000b147e15406040d5400042006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 257591456 1250 257590206 257590219
    0x30a110601210609020a0317030f0f011a0c010b040e0d1103030f010e040f06020406050405040b0a060c120504150c0b070201050f1303110601080f0d080105060301120203150702010209 80
    0x38610320704124160b000a186071200300762070b42912000081c00030024201d810412260000000c10711802086204500ba100380795030f04e0400d002540c4260902a00010072881013000401419409a000040c40c81c60307020001d49070790858000703600400e0b002c0d0009800c43e0800c200203101c0007010403004074040003615600d00c10f100e04082c0320342c0ca01040b18030100c400e40c61001403008504025040c1e502900c6449100c210808035030710031040c0d811030b034000404201e0200e0140071901d001d00405c030440906803100c1800e40d1034164004c01c84909103001401c0c4034004544000745d907200b030088601500c40498441c2601c490040001c1c03070700340540003c5e2402c050101c00314203090f10600909020381d2035009103010a80f60101c000381c03081d0509a085052000000702810041c0041c48228000d124010282441c1d04640302954103054400e0104410031000d80010302686d03403044c00380d0b810b441c1c8841403090020114404680380401c0c84201c04000c104020400610f5903054004003c0300d80700b62000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 257592706 1250 257591456 257591459
    0x30610050a060e2103070203012a021f150801060b0d051e040201030c0c060f06080606060c15040c080a200301060e160302132408010e1f0503030a110601 67
    0x1125140c601c44440d42c4e0205003104100203041c620100320482110990036280341c45c01e180c2c0080d003120415400110305074405810220040f9280c041503080342407900151080189465959548070f03810303c0304000d01955407824031802c12940c0700000162400b0320007004400c1d21a0725400035078000304e902a42007828003000a195540004c40460910701c40c00000041c1d8480c1d0340194040d0285015010803c07e0030040e8801141c3da81c0180007402d0900940000c0d1030341803258a9080a1380180307510f004860801001c41d11020001e080a001407540322a0180c5864a103062010100d1a901944980c8101280c03a400c0c0000006146040b403111501c041084101c030041c1426981503104400000b5a4140042d1343c41540804400051959140c0186014031407540c47c42c540450fa0040070b04083c5c02442c4401e52461413032031155545160408500640c50b01294100d1450010454500100340c810300c205482072000c000009800014256612250000740042400b21550b075603c04a1181000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 257593956 1250 257592706 257592719
    0x303041b0303020a0201081902040b12152803170306010801060315120606051005180d020a060c1403180102010f0507080621070e04060e1605100e030610050a 69
    0x38018201ca81c160013501d051800c9800564502400418001241e4052203c0c0d04111b03000d44003c101401480074030544480c5110328034150204010410700c2d03201240000130200756203080c0361207032400b51040c6540d810960104044040301e15640002d0088000320202c20303040705007201843c4544800c0c0d840e2802d41e07981340d904a043e01c40041e4a2401c018680405010181c02c144407142030310702404001c514150f0701d001194a024482448400143c400300300c01c00d48600c044074020641d40203e0f525100f400007500000c080901b00c0c031400040c4030103003808030104840c8150031500780c407010702a2500c1e21079000030074501d13200b88483c080c015440d0401070384143c1880d2240500071410359881c8074082c2e6500040c05100450102d080070084112610713003410390410408040580001c0406c061203040520300360055403d0074a0182141c1c0204045070411024041000700b1501e040310b4804c81c0701d440400a44864a00f0380b00b25415010380c0c400c011034589201905001c9a000399a01030350f0075075841 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 257595206 1250 257593956 257594003
    0x4170333060307050a020304030f03080103030807030213060c031209060b0f041a04110c06190b0904210c020301181703190906021614010b240304030c1202030304 71
    0x10640740e0010302400482e00e031a100320003402c0041100d004803480c1c143c403915414203580300d40300214005030040c001401010390140e407903038010690f420250b0901480d000c603000c071442540a420100300c0ca404800003418414005518224600c042c1040790741343c1410080058050015810300858045600c441d080c141403080001c091800044201c804480c1400c000c094000b645013903221a100307210740c00040009014040c080c511100b5142c0380941c5243d643c40603902030200140c07150a0716010040030802c011603010840b2103100b250800e880c00707050706031140303000d40300c000c3d4056180110755800c095031451003110483c00741950000d4030382610614401e03488115420f28a5800100d11001c5c001c44a41019804901c103003070140c01c02202c4600c1940d2066048020b940d6410303402a0351040c1c44007031040103003030b8800307841c1c01d200662542d5011840d415000e5005400c4503000001406041c415a080b03800c165200070100582211204004e503603410541d4140d86041542504c0c1c0500074500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 257596456 1250 257595206 257595301
    0x9080d091709280302120c100c110409060f0c200d0221040902270a080a23011803090801090b0612071701060608060306010f030b041703 60
    0x203098403c07076001052007032030744400c4114801007901c5a841c0400160f40701280500c0106104004000c1e0705140e8080124161003c078048003406460031640011500d40000602403042c144d6001c209141a441c01000415211169200107860080041b800070750000c0c147c900c07108078051200310348680421140c0c560203480d21503c00760740841f0b00c41100110070040900160311200043c0d0816584103503c2080e43e0000c02e0001e01011244800c0f20041e03540340a02ca141441614031000f01030800c00400e5a6000540015246400c140c95160340c00900320203400500601100a00180d14403d0807800000071806084001c40c602e02d401050281c014801c44203207540109092040e03440780c105014403c0000d40801286001c0c070b580205a200100303445001c0c0101c0c0718000240305150080c020310082003e00068400c6e0407000040042e40202c1c1c490a0941e03400119440081d2182d192204000d0142c00840e0030410b000300412100314240700054402c2094444510300c60006440000502c0700e10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 257597706 1250 257596456 257596459
    0x62303012601060608010e07030e07050607170a180b0702091611011a120c0609041d070b03060906040c02151003080301080105090f0a08120a09080d091709 68
    0x6000411400c4024a20542140c40220032616407407020440741e401d4034126005140810350790001084460003103a0702c80e50081d46482d0801c6074a165041098481e80e0600c9207602c229408686007040c040c0141a01281c0c1e4000710b506d6594448000024002c14403180c2e2002c500301b0344d0600011640891803c490030300354020159149560346050700e220b801240d040c58030811516000140080e80b092041415042c5a541841c036240c94110410110307600f1000744500d103800c240e200150b140c40d802e00766405070f0003c44011035540010200e0b030b251560382c5880104c1c0e52050260000303580400c1002140a0041030b211901141d56800c244400e40e00034507030b100700580c00300d1843c086404140720902d0308010410002c10603680e82c0c0e140c8030019082030b00205d540365075078402d00800740f82c20014910b104041c8000b6101c0c0592684540740e45022b241740a8107550f540c04009031f5640181da00109000360f1111101d5291a411a100d500920303044a04031080c1181400300c03620002c40c113065400c1e0150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 257598956 1250 257597706 257597777
    0x7020d090f060807050702040c0905040507110703080d090804060305070e060712080a0b030111031008070315090809090c0901020c06031009390206010f0609090e0f0f0706 75
    0xb80440031101507900605241c2000030911080c001a9114020b48960015a0b0340d90095281072a040108444000e400c0310148000c05020180d4010007059090071240c0001c455074450106200000c09011281c0c002000c0e410001070100303526415600c8640600c1040d60742c410300314110401e204051062400241000303880c0700d413200010303119505080d0b010b4001080850300080c01000b190035501141550280b112000c400c0050849100d07030400000c00000e4014902c1070300d1a10781800401c022071034606940d8031800c141090220100c1194042d00002e8104140391500300c0100840c0c3d0802800350f8018002c4000d4032085142450983e8010204044c1410200b440c0c40c25030801040b40d0300c02c589958688071014459090590007008801038555415494030309100d00090508005030810180d40c10400424812658000c00c4074084e00c0507500c00040004079803036054540b90b62200c8a00f030611031108400402c8001003018011100b4030f44401c01403400000e40c000307207442c00c403042513041e48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 257600206 1250 257598956 257598959
    0x1c142d060c120411090106051c020f041e0e0412020d0905010f0309050a0803040803040b07020a03020a03031a090a06150302030405300c070e010801091110120203040b07020d090f 78
    0x421541d800c0750480d00c21425290f0620a54003c05c204440990005020800104d8600341d0a002d22403100310443d040e41045140030080000c1c05914007880c01081d090019a003145a070b009404600d0308054814a4410600c84c64686401503a0004c1107816200600071444040122409114810141d943c141c594001c4404e044104a00500c4040400c0c0c5803803050b01e4510000c1030700300c07006501841c00740030f24903542c3ca460f0601601904003e4503010456001041c0c1c1000710303030b000c240525416894940400c5c1c403400c0b01c6c0c12540401c85c00313448640c4120280d0901074254680e40c00b0340d003200c054200703108504500640980880c00111006801500b1203603502904034030404018005002c801c69032002c045402414010a0b041108040d00c29448010700b40052091451001c1c010038005000b8808241d99944010400c9a5810a01d001c6c060220810840902031000c084140c007006d481103490389481c3c10300641035501078604802500a034052500102d110300c400070140d500036000503003201e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 257601456 1250 257600206 257600227
    0x131403031303080d021309020c1203040b01030f080405090703140a0b15130f090b40020c0a061409060c120601090b0f0c010501050406051c142d060c 65
    0x191300000403149102e81c00c000c851a998003071400c60000e0700035100d00588903058210301502d80031001007291940002441000001882d034940141503d5220200b1040070845141007510350050340c0110354090450b204202600354558080c1014240707400c0503801a449100004048032640140250030104144c80c4a1204201c84020314141c200d151078000c000c5c0d9258078450302002c4c19045240380c0ba40b124000d40d050301c0c00c00700c20b04040003c0306c03030b408001016103500c034141c0350300c100b071741000500d60700b90842c484405506aa0702c0d021040159484000d01d4600350004028120b0702003e507450030000b14070180c10000380c852040520b541010320b4440c90b07002003442070070020000c60400c90800404220f20f41e050014001e070b82000a10344e0b45486100c80f109080d00c2050b041140240d240680800503559295001134000c00f00c0c2c41000340485060800384807071202c035141c002681c880c90030078803060307403048441c0c248450f00c0d0130403c4c44070650b00300100d44812098610f101581c8040c0210801c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 257602706 1250 257601456 257601473
    0x51509040506030f0f0f0d08160c0606050a0b040911040e0f100f1205150907230d0803060907030e030a0e030f0f06060a050105090d110d0503131403031303 68
    0xb044008003190003526401d400d491504800041640300740e000b0140d102c000c0034082000780010343d244d0612103114904040106403690303c01280500308045005001c0510205034001c1d8058603014140002c590b4581c05240203503806803046e084094039100d402d040b8690b4100940d010344462900a08142e100c1e941d21001d55040640510f030301c04010000002e145403561406d83c0204580c0ca10980c5041160400508116400c15502c8074011040c081180c024404950201550040c0c2d030030802c02070070401880210010400180d82120313200c9904024416100d000d035210351011a42d1440580e00c0c0c0c18103d06550034401c2c8052194000c6c860b01c8401e0f400340c0f0f606200c100000d011508502c1e140c001c081d140040000303d031480360f0080b00a1100c90b08015854502030312007070034220700d0030b105c10000c034149910002000c1d110901618640c44035a0b524612060400e0300102226207414100c081840c0d00c580314803034030424281d40203084116080c0881621450040d911803002868a5a12103060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 257603956 1250 257602706 257602711
    0x2010309140102041517060102070611010f0e1020030a050c160b0601020d0e03031207020a0512030702060601140a14090607060b0a0b0708030c0a0c0606090f060515090405 75
    0x1da01c07409500c90500c140003440988010014224050070582c0d00c000040d012610030001814060f86c0070003040090390f000100703c1c00312400c5280610710b071400d5503441401042c6441c1c4445255042030f250140d141d00014050414440c4004100802d2840c181ea0006109000d103c01350841818000503403241c034a5440709034420014200c03249020310318180750311031b1108241c04030756081c00207050200c40d59040200c0540c460b124145805400c1d09040020303541d024240303141c00d54030707031580c0050400b6200b4842e00c81100c1d4030400301c4d02c2001d2400d0752001d10303410407281e800044c481c00002510300d40c41103600072208109088050700d4500600406c41d9141c03001840340c000c1c94010401000d0300e807a00c400619040380165000114000c11004103c2021665030000e500074405002c0035010030700020031680c024000030655a40e45202c114103032a94101000e000c9c00852801c0c000181401590304611160301d0381d103000300600f50725102000300780c005940354401c04500c00e0005c0c7d0580d00b4280c1c030094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 257605206 1250 257603956 257603963
    0x9031002070f0b07120608030a0c02061e070b01030506060402030408040b131806030b0903071a090c04050f0603010b010f0806010e01110105010902071407030b072106080f0c0103050402090402010309 87
    0x41c001ca00c80d200c9414143c015106100090745018000e21000e4191107000041d1650328080e42c0381410400d0b005220000641c40640b0858000512003003454800d40140c03980740800744c802d80c60b42040d0070081d0098200b403000f511503006060004142d46018401c0b60310407031348130035450304060819000c0500c5c0e400000c00303c582c0e0b07056040701061801582540d041e03030342800c003000724a1600b9803510300d01051014180e41e5a82d801070108500150703d2000b8155002d06441c0440060ba80d01e111161422030b4055031643c0061410301030180d0080c158007103510915065000740042c2d2050401150910581d04840002400303110110b0010340c070a00012100140c140341054811000380744041c2103400c2a0310501030030b030340024007a0400c4864004029032041023030140110928545030820a04001031014081184180200b031520503411403070340899203070120412500d40c80b1403403507907030740c000180c003281c0c9118182048180d51b00c80c0c00b455100c1e60740940901002e46032030b80150007807d801c90089 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 257606456 1250 257605206 257605223
    0x3030a0e010213152709180b0c0a0e010509030d0315031b050a061107090518060f0103021f0e040908040302100905040501090c020d0809010f0903080a110903100207 72
    0x201403050b4100300700740280501219100c200000120040c0c046854001c841c00040e0301240503410b50140d17030761001c2c01c540a9913070203d91806c4200307142e4000042d602c030003016000035401f41300700404198003424024416845108100a8072001074640f0b0141110705541540b2a124042c8800e210303030403078210f45c00c10b200200c1c0300076229aa04035060400e4070100e9100301d4490380412070b034034203446030780d00500041c01e1002c4c5103010080740c40c0d1140c0c2c1c58080c0b00d440d41d494101144009a030100c0c0b0003404602e003400c3d106903007030400710790442642c20310069100e22008010146045100100100001c009031035804040c40600d0911001d0100d01000f590815000c0c400003002d80c4503c120710840c4d140654990302c8113070504c0100300031542d041c0c2028811a160002402901e40c001407012181d1146051540180d03031840d01c6c4501401d104400c5445590404e07031000b04140d04411014052107154170203000717055949800d03c20030b015101070390354185d0180e07801d200c41400d55070090425901500703a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 257607706 1250 257606456 257606467
    0x702040f1805150606040501050a0810030c0305010e06010b191b0230010902010806040515061c180c0b03100f06050301051206060105180a090501030b040b100803030a0e0102 76
    0x41d52041d00c41c12909a9040d00086000254003600c0c0c01071591014045410900306800d000c0024003500035500450140124031010070140f0551019907001158400c13000000d540d184d01e051400382c1142881034000b84141800800da94820005444c1500102e004811b034410100b00d013241c07911042d002c000c206840341800712000d619039502c45210000803034880c11030304091001c040381180c0c049001c4c2d4000d0749421002d10042c0c4c2d120300f07450303002002210041516150f8420345607540b41410001c55100380c0c0001e003088500243d85080e585142c041400700a042d034003410042218100c004028078607030407014140008500c01c0f0207160880c2c900c0c101409400d49a0041103030940581d080301e070101e000440100701070f02d4210001003020f14403c2c00340406003403d500103005402505c40209280441140c6841181c458078109c00c02400c10300802d0240356502c0c1003050759000143c070705440b00c52440000030510b00302d004502d011104c5200c0158030755981e0314040350081c451180c0a02055408025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 257608956 1250 257607706 257607731
    0x140a0809060912061e0c0a080c030c090d0302010c02070f030804152007050a0b120f1e190e060103030903030309060207020d1a01091406060f0f030a02040305070603050c0702040f 78
    0x90b1900c85c666006820350120080810b004580100901481b071220f820031422a40b01d0b8041c1d4415080b40003404c0303194588e1a10524040c0301e001d0f02414540010600c4100300034554150064082c520164080d074210300d480315924a040a0f45010143c10345000708005c02c10940e80205103e004c14207031070546900170700c0c1d443c0d044000d041044c0d5807820307500044041c0301c1d030724103009150018001800002d1402c82c002240c10b4483c0c80040800014250410014825803900c0c1d10b91802d0b540d402d549890b05207000d003504048841c0242e131030301c0d86d9490061502c00c800700015909041e2034040c1c80341c0110a00d180e40c2100988246441255030a4080c000c1000507200e1540c0340c44090310880800f00b050941007030429000005030300c814401420883d00303180d03494442e083e054106070b0507034038190354402d10007070108984900c582c4020200300c0003040000c44c3c411079000d001501d01c20303030543c1c000d10350340d81f070071025603400703481d40c1c08000030400004d4011325050740a801044a00140442d9080b00070700c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 257610206 1250 257608956 257608963
    0x70213060f0e010317030f0a090201021e061f030206033408060102010b010206130803040c0f080304060e040c1b020d0203070909050105091504030815060a030603140a0809060912 78
    0xa102c9000b4052180040c820003010f9900507111040c845100707800d62070543e00802513140080c00307140f0381c0d0fa500c00c068819a4401e02c80044550031051b41a0803480002c2005d03907940c08100c42203004910002c10b0040c413502000e041c0401c9980040404c1e080d600e8407002c80501400082031030b20004081c20f03e4000580e4141e02c5946110810f4560103480c1c42c00000180c00d480c0040b070281e046400c12002c001d10404420a80480c0940000c07601d5101e80c0c852402e0500036805801460048000e83d0740011100000030090040e1615682c03000c010b980400c2c00d10050314459612880402c01136581a45826021500c418141c1e00084c501008261560080381c05c0c403c0c02d030003004d03041d500c85e07988030140282400340a4118007004010701ca8441051220b202c5100050f100808121034140480e2941031060300c02046150000c100d180d0b10305403c040940105500d10044440c016035004c860110000425521803032900100b039246003440000c1040f605070300503000303150302003110000300c0564081007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 257611456 1250 257610206 257610209
    0xa021c020403050c010c0b011403030f03090f070e07020607030207050a02040905160b0c07052101060e1834080102040306050411091e150303070317100308070213060f 73
    0x180140d0310350860600d41d040101443c4114107011120703480f20002020780103039a04641804030440140202040040d066100d082d045103600c40e004001e100c6241d03000710b002e1203002c6282c81207410440c6d40c7c68802d11b100f0411500d031030168000c1c000184206000e0b400078074169104400342c4440119650005003100c03410501611107a20038081c0c05a0392845900c5030307001d003824010b09803e14035410741c01665074000b4000c8a02a9082c001031345012466410151009400310009200c0180c03601c0f040411804d0440d003444000d20044102d403001c80c0302203280841381e074801034a210420312890b59240c103e80c9100021030840c17060480001c5a0b01d00307102500145200d4007011505092504200c0d034402d00e40c5a54a1095030311800388180c03520000c0c900c0501d25001d98000f9051f58801003004030300d60700c90003d1038041c000010b0744001c0542c0680d0b40b00180c00d008408040e55101c802d00e0130030950342e80c0002014040200881e0300503260080d218038201c10b11002c08500c00391110422034039114203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 257612706 1250 257611456 257611507
    0x40504150911040606020a0c05040b0103020418090314091f11010f0504110604060f080402040f0606020105040b0a06120b090c030f030406140708040306051506180909030a0807080a02 80
    0x81c04500e400030710f058044c81006002a10007030641c0c05040d214101e45c81040d20500b4800c44e0784420301815a4029010f84000b01020000e0110091160329000081c00c01d01c20110b0000f040240c08121042c01c07982a1501c00c034001c0c0c8501082d00104c41c01c09001c0c0848103220041c4800080f900e09a00002d004d545003c1c411407002042c1424580340101c180c82d83c1d02c4c0d8052250f078051000780701c0c103a44694241e5010042e40b900324226119800400c0c01007048c0040014528100305010542c00c1d015000680503500c00c0400c0c03e80e40e80e80241d5002224081c0c0913200b40340002c509104042003207400102c0e002000c0000351fa22500a18000901d044520f03820410183c01c0400d00300800c542003a0116982c0c0e00c40c4885619012013983e070903900b44240c6c04020800d030754500101d501c502c1c0320b41e110605514013909466449010403210014030403590120352281c02103200161948002105030b62414000d522000300c0ba803030b07c40c03050b28103580040980c12403607400d02181c81c1300120410894074541c0b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 257613956 1250 257612706 257612723
    0x10c0f12210603080a0513091a0f0904050c0d03020c041506020f0606091b070f0b0108010b030a051005060d05060420060910030c02190b060f010813020405041509 71
    0x10641e1240d00320450508804511442c155042020840040c202c490000307145c94520303a40d0120181030b482c0d03d0842c1e0042c509162802c524180507610380c040c1d01360400c0b0229160b003820040d680822801e001c044800810b541c00c80817100703560f801d10f00d401305240307482401030301c001115480114040740c803e001c800141001c410807c1014a070148404820011200d005c1c2034946040008600b0a00e4040c00040e545011071600302e458681e00015034802d264000102c0e60128242c2c108010004c400b805400d4555103410aa000d403072900094404074554484083c16001c180b034007181005080040c0056085820f0307401010000f0780c00d100007881140300b1b8072400c410a203016000d4540841705007456008050402c4980581e641d0b0340340b60801601949008a04007840701400ca040002d004500000580d09156030400c224040302664411031041d200c040305e418110004503105042940c0c100b28800c1c0100b010005810182c000c254064080c1e042c200040108240303420840e01c1c01001030781d4580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 257615206 1250 257613956 257613977
    0x91509110307060f0807031103090601140a380708071506060507121b1109090c01080103080304030e06030a0509061018150b0a050406180e06010c0f12 66
    0xda1200c109454010390080c103240307041c200c0182c403003e041609042400007400014002c0c034842d8215400c5446070310f6016840341400340c00b80d0b51302c44083c007940c1400040e000450ba03050500200d034200325242c1109001d48020048031103158081b0308180c0c02c140c0011307080c0d141c52910907200100700e600d10402c0f01076507a032140d051620100c40800c1c0481c40450030000c08000d46948241a610707599004031640444603100d0b00250742c000382a015800070885c0403407904040c8042210401d4884101340d0b4800c0846e41c855061588a0350091640ca001c18018001480443c019a000d19401407081c1484c0c1702c00044c000020722a50011610300d003480c1d880c1d800700a40031405004507508040b104054600c2e050802c00e00c000310320104100303041c22517614066503440c032000d02c401500500b00700074600d0351944c2400004281d540240680c1000c02c280049001400320300c013800070200e0300001c52400c01912220011514821140d03400c0e100784940c0c44500b000b042c4043c41038020329004e915a8100314 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 257616456 1250 257615206 257615213
    0x703120801050d020919090b0c0c060f1003030f03111206190e060402180a0305071d16080901090204240503011a12160b0904050c090a030213091509 65
    0x2200140c2101d030040a903140e0300d90058170343e40f541d41e42010f0706610b80d12400b41700c4004000204240301c00a4900c0038490f0034481d0403450040105000240c54080d81c1083c1d40380b15590840a40940f001c0c03d540d110507008102080c450314a02544880360b1a000c02c412140c010000050340000f0f491140f4099020300344400361500014103403e40d100c9400c40c1e80c0d03075032514451402c4200010411401960002010b010038104603400c100b442000624403841a80c480c240320b80d0b0b442590042d241d0301469842541844a100052188148207035030040c40510603050f0102c640d600040d0402c81991f4881c0040710050f03440d4000c0158000c6c1b03002c442c80c00d4a000030540f031032135803c60740420f0080c1d14140001c42d0340f9558401e0782c107081d0f070240d4008001d031036480d0990749008007191320040c0001d080c09012038108031ba07030000c00920740700715410300003515030345032200c420301c6440003a50340203a00000800041c108030310503000060207a5000645046c9075294403980f1b400001401090315565903c0c1400c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 257617706 1250 257616456 257616467
    0x30c0602100e010509060117070b040b090906030a050d05130504020313060b0607200a17030403301d1315061b0602091c1a010602063303070312 63
    0x2c014240e8028810780c2030900780baa03125801030203a00400368803030490345001041045608010010407180c10780c1e899480c41103640d40e410144010703115455400110b120780c038000901e803400a030400060800c481c0310038416142ca46c48070515030800e1945481c0060740780d03201d2020703507c180b41e01c0020000c02d0020745080c0085900310340209105017000d020790408508201461032905481c0c9034030040451f00580081c001c001c4503070043c15040b100c00101d128004020001d8021648a0014120300107407613400048440a54058807456480c08049002010700c6050100c060b240d0080b0b40042410005010922039590380f22090300064582a0502544200441941c01040d01d80b40ca404031100606981c18500c213441c9015155a03004900c200090f40e45031407030f45c4042c00000c1c10220546042c9003001d400c2000c00da03241410f400035400000c400d03001041d05803203500c0061819250030001c0d04440f95110511400f00380408510740c0c0340140791020030201018501840045001d046102001080e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 257618956 1250 257617706 257617721
    0x9030606060e190b07020d050a0605040c03060b0105070f060b1f03091a07020d0c08040b04030c0306181101030c1b030207081014010510030b150a0e0109121b030c060210 74
    0x150303040101003000b4140f0404c00f61030000391304072130858103141f035420501c0c07620b4600036001e02420f1810081c0000c00c4060342d180340441c1c0c46100244403400c00071005403014040c141020300420800c180310000140399a00180540c2001082202c7c5041811b04c2c00000b40b00d111143c101103950b403070a480c1449a078010f080389403981074400c64954500240001d442c1c03410781e00748a00717000384070341000104441c00d02618040e002c6030011640b1160740e0f05203155801801d10060301e240b0b2410070346443d4122aa40061085900810011680b490181c0118010b0ad182c150500400c10343c018401c00c5030311800b01070340d18207000703a0041400c0c6041c650403030305003123903681c03d055041d00d041c0b0f9000f103c1030b4100225044510071a152444000410020340292000e070381101c2d40312000d484c804101c1100e00000e0003410100340c0e9048812503941006448005039030244002c0e41c1000c1b0800400904445070315040d82a0101004e840d10380d5039a10380c06002c07020340003280503800c00540840d416069115601 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 257620206 1250 257618956 257618989
    0x601180b03010b060a0507141c110a020108060f030102040305190605100f031131110909040609030c0209010305010504170f090f120706020a02090108011b080709030606060e 76
    0x3c00c01400300191041c0f04070356284050040101c1e0b078905110301004100320b000903260039207003090004024102c051002d050001c0100390001d09480000c0000140d001d0000c0d41a12920120b4540c0400c0145280407a400702e80d040d0340820001c00010401e01c0008100d0a06040040468426140c2076041d10750080080c0785920101d8010030810410714041411250030000364160400007101081440703103103d0080980804c0030f06600382e481d80002010785111a090001c01001c05007004c114144d1240c01d0f109076110001201140100e42039070b000304101c906c01e05045000048541c0481d5001000360300c16074041c0d5440c802c200c1440016203003041e0a4214508003446c014001c5034509803809023501345401039003090010b1105854030301000518415100440e944a603544030025074410491100700e0040e0042c4000290021050050000b802030821090f05000d2a5281c1110701d0710b0010011b008100740e00c40c0000100361a48962070280c521039640e25003601d40041030101c50b030b03009540714 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 257621456 1250 257620206 257620211
    0x503030313110a0e01030b040c0902040b0d02160b090703030e041b1d040501090605040605060c0c06160c0b190f1d04021b0105180a02100e0409050601180b0301 70
    0x80003440807520003600155111050071140700a02001c20650305907a0072418903c0c1d9414004400c4c400184c6d91702e0f10485c40740d10110800e64070340d44800300b6070003540701d140e41515062040e00c440444c00c2d006802c020f118544403201c1001b0644a41695034801c2e1407038000c503003001e0300900c2819408040c0c8500c0e1142680c0a10240021001c4015000213110a5100f0403280b28280441001c2244055106c0d843c000c1040c42296124820000184027134070409100e14500100014a42030641c03e4449600d1a90302a2880910103801d0010a41c40200b0a01410802c00d591000140c520741c0e501d0050407140070314503140c0e000e01d502c0301e43c103600c0c0b60004018060044801d03200142c4c8107a80300300030804030110100c10044940400c01034003500c6030b011900c8180145040c8040700551080b03110b50000800540208a480317a03883d1641c1c0305810180d040400c4a82c0c0d1080d41c0e00807000e02d0310800b0003401c0084c50b010151619802c0820031303003285005443c2507040001102060182e401e035188120000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 257622706 1250 257621456 257621461
    0x40f08060c0f0d020903100c110c030c0a031b090609050412170703020a1803060b0a240e0a0b070c050a1a070b180a050c01080109020a0503181011090a05030303 70
    0x1c051080c0518000d070f440080d0005400f0105880500441404800d54841071040002410010f8031111401841010074451100a030041b8a40000c0f101255800507001c246983d04585820041c8002d4015405806109080008000140d03108000050040e160005031908107482c11400c1d040c42d500a01c4c08200c4503170341201586510f156803036004000c030704006075100c0c1c800c201030f2014020070b0304525440400704000418442c640d0880d0310302400031100c20704503035101c42e5115168040c1e003201c1d40241070240c14400b42103005541e102c443c41001080c0c0e00710596641d500300003991064038201d403000c0d5440001c10650612580030300207001c80d0301d02d6000d50301d034502013a02640289030001c0c2c00240850045114070b895000368460700c0118000380c2d0781d00034841c2465a640c84405809900041283c400090490018400e482c1e542d541a61040d01d1034494014190030f440841d480000503000321080d285410480f441500c00b50610400d0ba9616a0503803030810103d10f215600540c080c0d0410001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 257623956 1250 257622706 257622727
    0x5040905030d050a11070503040306060e07021b0303120a0c03111e0d0207080f0301080c0a03020a0b130806151804020108040f0602070204093e120c06040f08060c 71
    0x1962846400c07032000298075503c0c000341002030515805c45e00c2060314009a42c1090000120046c429a40100d4003032142c5590340e00c41c20714210b802c13a01d0300016045040c1da030b11801d20b04d085ca10510840141120b04203019074044288003c0207540c2c80e01902da40d460b40038800c80e0036019545441100550742c0e1b040180080b640c00b122080d03000c504010b201e0004201808800f130740e042d00e02050700000300940f108441c1c070082d03d8613403081c0a1010f143c80303080700800c0c2c24600340d90f03180709072503025002c80202460809050039541207000847d48038540d0b140d010466203802c01086204491404550101d000c0a106003c2185804201c0e141c40f18150000c000150360000111074005a00c42c2080341d2080513418a05c000740202d600080d481820540030005001003406250301c00c1c0c40c2480c0da200c0443c001c03280b08006074502024224007100328015108107180c00000e40000c07503001410b8402081e00c0c4000600302d540690001841c20416400c1442802000c2007017942c00001301030618500b405100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 257625206 1250 257623956 257623963
    0x60108130320070902180a0b09030705041109041b0f02010212011a0d0507050405011103031b031906031a07020708071203052505010e01091e06140708010f05040905 72
    0x8054900702c014010b01100d00403041001000603c0080780854031005014202e007040a02446458419201b0680104a14181c0c100703c4001d0000140244009032510080c0030191101100c0e02c01051424048080341d0b07280c1c0e01810700c1c0032131346103014040e9050503035000c2e0101742040009011684140403404031840d0712001e16056480c1300180049001c80c003118480140b0440e00e0341010076013003e050085650b000300203007003540d41c00d0302c0b103800302840030034a01c1e40e0380811a0302e12480a060510440c03814041c03002580c12241c00031128040050702d01c8204103880859000f168a0410848c00004011800007110380200251014054540c0b500c0f5441380c0c1c880050041d050800da07034491900070140075004540c82025000340d000c11022000f1818103490b140c1403003d43d0254204040b00c4420b000601c504804a688508010000009100ca921030008512411281c240d0fa03401d00c0024041102c0745a4481c20040e03495807403039030400404003468025680120300485c10322040310300090020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 257626456 1250 257625206 257625227
    0xf020a05120414070b030a050c070b150a08010c1e020105090601030b100905130501060902091e04090807050307050c040525090b0c010b1509150c030705150601081303 73
    0x20241d45007a140d9040402c00a800ba4030280a20302c22640d00103074202149020314460500407004012503910380145070064850503200428440040001031013800a0745001c024803040034000d80c00303041c2c403841903d084410b24030700240410040d03030620450002c0c2c02100d007400303103081c4001d000303d003803807104c3d69503410060000a10807000b0400203800c00740040710030782c010009400c2c00e001d10b0405240e50004c01c9000c80003a24103500300707000070130410820b00840c1e1022001421859205020000b814807159030801d6807584240c403110801c0100d04050003070180750b03000704051a0758041d03502e01341d071400d0407010006005604080811112b08441c5080c444103079460783c6895148a00a20304542c1c25a05401640c289500415450315159056115008142c001d440c6407000c1c1203800a000c2b018020720307080f00d50045520040d0714410901310b020f041c404180108a03810080143e90f40f5050010b0342e030340030b00466180002c00c0602d6910000303c541002800350501d0080310580c80007081c2c980320 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 257627706 1250 257626456 257626477
    0x504151203030b03010c17060102070305030a180519050a0812070803040f02100f1211250804141804030f0e03070e09010e06090d0914130f060602010f020a05 69
    0x9252040107042c0690410300040c00018000c00042c0c05010019181e80495100585d40f5004500020705e154000100503060700e8204000f182450072612044840e00324500440c404040c4440000a040d111000c3c080c072450303031031000310b4860380c185805d000781c0c20b00c83d40c010281d59104a4141d4112000802100d20780d98200080990ba0359031410070748400c0401d010003c0d0000c1080d840d58504a9101e40d4409180d11140d0b04ca5000e24007004545c401d480d800454054401410800c01111611110803180300e24034001c114030282d200c6442c0e00301c913504503901c206d401d84243c1001d15018030304248256000c107100c541c01169070030241c030001c00d58400d0005410a005c40b1a034030030341c1994200708070001400e641302c0020300c03842d00d5420340d8080e07c48500d4000282c4600804070b801c40c075000c00c41007288000781d6035228420f0f242490281010040c0944c060300520380e510300c9100c3c0d212a003c1c110880c01d044a010640d03600d404002402c4880c8046072001d0b1a2060040c03e03241c680c000101c4030310303540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 257628956 1250 257627706 257627729
    0x406050d0c050c030a0e0103050a20130b040611010c031413021318050c012307060b04050c07020a0e070c08030408091807090815010b130504060f030507050415 70
    0x1c0598050311584124420110540700100c2c0301079000e94045a51809400207136014050b07611403400e02c00035a011741460000d200b8210341500205034900d8041e01c4101c074041c080d50b03001561445801d2590b4443e400032000103186448a41c5099001d000d04080c4402170f180c10043c10303448032400810400054070041c0d41e40000f146601c295510004c210b03a250f0728190040180701030038500084428a0428100c40501480025156540c002c0c41140582d00c6982408d8103a2075031400c0202d41c580c030410080312869503440038400140c89621035680300e0394482512699030b40c0c15004008400d45154480c4901c103c2150422200d6076105810100050784421100d4a90311945800310032401401031054209010b11f10040351243c40c51802c9000d19800d4a45444003601d48982d152a600003584010f070442880700100311a410140081100f400fa05054041c01e548600029068652681c400548404214014401d00c0411320951000300802c803010017410044041c2648004414800d070095482e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 257630206 1250 257628956 257628971
    0x6150a0e0604020c0c030f0706110c0f010503092805160b04122906091b070f050a0210081f03020f0f01140310030c05010e01230c0f01050a110406050d 66
    0x14005c2128100142c030003002c3d00d1117030a4200407242d03100c48a110b140000b40002c810a20100c4021070041c0c0300d8a8060f000c0c070790b0a540c00005541c81d03803025181003e5442841c1661090303030310040c20783e480c6c50405070014041302180d091152400780c01c0356600b00380d100b03030460070442c4071545811101191081c0d01254418105410310310705120848015480155032a410441102803003031945104038000c130b90150007521040e004121001d1801c84400d0840381c10002e44c0f0118180f14218001e15110700120740512155274003050f40380c6565924100843c0000301800904a100740ba0a03800c0c031f0514910400082c40c1d40c0014000403d002c8045001b800c030000344684a9124005811002c500141e503545e40f4244002000a0380340303288020707115003181100100e825881030701c0c0c24000031b1050751008240c2d085041040201d038841d40f000c0c003181d030041040740398075542804a65481a00a0000074003442e0066491040c0c0d000d1072540c11000d44100010321455801c802600d5158418601c0005d100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 257631456 1250 257630206 257630227
    0x90a0b090402211504051908390f0c030109020d0b0405070b0f0408010606050301061e0219030806030601050906030d0f050403020409060c0f11030d020309030f040806150a0e060402 79
    0xc0c0898020003906008803200152203000413190280204d00c1041200c00509280102103500b9410308802032120104000a8081d55815210202040f103001e40e40848003044101d074024a4031381c082ca6501d55081000004c0f054201441075507031608043c1c1c02400b4464469000030240d0424850045c41801c00360042010b003c0d08118041c06040c12010302c90751038901c2c00814420380c10034818240301c1e40c00c1804c0071510b18400c8095038100c404a45408061000300f4892880003004170041c2e00851040c16003000f10765400020341007042e402a210401c0b00e080080516080001c140c2101d030160980401380308450b100001d00780d40b04207451030018105146000121068482d6500c080d601504013921641800700c29400103082003100d071510301644040c01c000342c40c04d85000f106546907810a000c1c100c01c0c1c00c82600119480035000050320701d404080c1c0001d12240e00a034014140e0356100ca801c11092032800004000d540e4422a403400e60031323141c00110103903507100500990141da008160400078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 257632706 1250 257631456 257631499
    0x9011202070f050304090609020406090303110109060528020c0c010c05010b0310020a030c030501140420070c05030f01093903030e01140c06071b050a060506090a0b090402 75
    0x2154085009219030340e250034010380e641c001b40128660300d450700000141c650114401c8030100c4805490701c244191a644007912100b2034650881c2c99035407580801c2c80011030390311400344281710710f018407985841e4032100c13a40758000c00c3c1d420140161040040d48001d0300006250100007409107003c082c1004503242c268050071003503062030742511551901803540c035415000b50042e0480c03039800b0400c65110450450075100203104031030500c104002810418141030f000714442084d0380010703000c0c0303d20f01d000c255001d501105094500c0ca003c014148514a401d02c0404601c0001200a00400c0129118400c2c208004400380f040e080c44040c0d0b0319071a024526503080c5180c2d20480d04003003150baa04014141c503903405503050018500340c001007043c1d91a00140d41c4000c828000030030281d55420b406450103035843c11041180150920080c0018004000c1388400d81c0c0306420106450a0010500020a81c00f07040c421085043c0b0030102469140c1c1d07940e081d4000e4049130b03903540e0346244e14684581d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 257633956 1250 257632706 257632717
    0x5040f030b040203120f090906222003040c0603051b03011e03020d0b011a04080604120e100e030c0405040816080d060303020a020910060f050903030409050703051510020309011202 79
    0x400940806c50340d0104020308098507942d6801d0386c80c05000d43e6000104031505000145005503256409034030301c42c5001ca40c5c418848140803000403031812001554404083c3c104540031141112201004e001980c2d1602801d03401c00c1d42c440c0400715201c1080301401960105010301b0083c1d452501020a10043c80d030301503002075030080c010803c58401424642c0e4618824002c2c1c12001082002c082e407010400b80469040362140b40241c503240d01c035030340e4000032010b90b43d080c4020016000d44121440d83c40300700072421904681c46409070344005000b81824601c0340d0300080e101d10710704002c11021038a12422548055111035010a1075a0a403801d104180107a22074101e00c1890864040101600020304500b0755000301c40a017003541da20b0842c1c401102c582c0c0a42070020301008030182202c2d02590261440307000040a5a05180d201c0000300112001150b101c8002901c0f28180720707500e04003e540094510041d200d011b01c2080c2d070742d00071b5601c0c0300780c0c810b0368108030b02540c0400304407542da0f06441e03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 257635206 1250 257633956 257633983
    0x3030706093e090601050d021e16050705030105131401060b0c01020d06090506030c10090905070f0806040b0a060e0d02030f070303020d08060a03030c05100f021905040f030b040203 79
    0x901e00011500010900c820280c01c2001c01c001400c8560b006140a541081c401c2c01c0580d5007900d017440c007244100103900b242000b100603c054549100040c0c0105000d80303c0b141c201030304034075003d172941400d0345010040e07405903000e64580741c01d20481f07545604030b503045c440d004020b21070010451825a80101800c4d40016110240400d040400701019001041c0d0b00c1d40c6c0c00000d200203034442404504548041c1c8005502d944a40308816180c241491040b8155019003032116034079544540c0c06094031400c8402000048000341d5124a00c0c0c4c200b01c21a4000d102554204494595a03012800281c1ca60041105001c0d19031204450365440101f9042d000c0c1c0c2c081d0964900c3c0b4808400d203581c8000d07a00048015015000071031700c0062140c2c60f218441c2800034103502409185480c2510402003243d003c0c0e0b244d0003820070b86001a0018091014032291500c2c005a5424990f20b88144888450303031030000f04107082108004040314218040182c9030081c48000c11621240f000130b11340800154880c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 257636456 1250 257635206 257635253
    0xd2d0f081b061014181b1606020706050f0f07030506040b0d0503030f010611030906030a0b100f112b05130303020607030f0506090a050403050c0f030c0115050303070609 74
    0x945481c140c990001180d42491414100c03229501c10001001803180d41e140b03205c4131800010b032540005284446408913a55115071401c82420660f01c1200e00340d000544405030001486803c12085220321544040c141c1200c18103803c0c0628545c20000d00681030000709a1a003001c00c2256450750b00c4070301c40d840b000300141402e180503d406520b0380c100701c070700c000000040c1d00005541401001d00f0396400c0305074000356280c000040204446134001400241041c0e948a0f02c5000300e032900d44c030100402103280c036405044c400c003060080c090b00d02c02034900030036002900d00d6200407039410304017205a603544441800c00402990308441d18007900c1181c96407200b48200010038503401090550140b103107580c2c184503007040c041c011000d070b075130968016400c030301000001003150b0300503846650090b02ca890440e00e4110300340d410700e1414240d400d041007981c0000a0604e901203091107144e408036184c0f031600c40101d1800d00000c0d100d0142c05c3e405040c0548134000c1000701304d200b40c0010000300b202d4030304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 257637706 1250 257636456 257636461
    0x60409080a0c03022d010b0102010506030703060f0f0e0c0f031603060504020607240608030901120b0f06190e030a0308011710050a0608101103060103020d0204050d2d0f081b06 77
    0x121105241864482c510346d5113000404e900070b51060041c5481198080c008108003403440ea00d8000620400381c081303801a55940d80380b11040382c54020350458602c1d140051440d05680c000700042c14404000c401c0c400e6004c180c044014110941d1400b0480382c00c07007000903855595001113650340c07040002c000d01482d000d40178000c502c00400c194401108004030108552604c5801003503880c0300303040380d56002c18800c000c0343c0703d2180650072030030400d000a00030707002100785a004101103030815812001d034281c9580c0350110482e8400c40140d010b1100320024001c0c0241030300c0c082c01c01d0300b060081394203200081ca030006011004226544816580210130812031030030f894500d004040c24044c0c00601e0245000c08a0840881e00a5181084010703100501d9516030400540003580481c481c040299000d0100082c039595006c2e000b45440d00411801240e80f426241c0c1400c41c60b5207040100c2448084036114001c54420048040c50b5070384144010743e118603050310010300d08000da06282652245604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 257638956 1250 257637706 257637763
    0x90c020a03110d020307081803070803040515090d080a02030705060a062111040c021005090604110306010308030103030c1e0f06110c060c2b05010e060409080a0c0302 73
    0x80d0034600301e01a6641d90295880d0a41c0d4588902220b211040160b1060181380d01044060313000b401881201061800c0100c1e200b0042400d001a6a0120005810102c1c1c2003042d8104070a120704200a511241460500c0d400000f40b000031f680361018103078810200300641228000c01c1103032111504801150350502e842981c45014048501403031488010f0018400500e564007001300519030391024003034524060301003d0000030107009138004214801d480c046884101c10388034080c040c0030007401411700c6103468101f2070610000070641d41e000750300040c01000403039414000c1d28103503903251500d000c0203005420104010034984450300840603280702c501d070800c084c041c28410303043c2c4101401d000b401c2480203014000d0090000e0280140c1000d00081d1009001c00002c1c030740403060415807941c40520106046000454100c902800c17039507400148401000900c2c25036010130211400d100300d02003541c81589501900c2004001c1c0f040c100c081c041098000d111003480301403a1060007080859000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 257640206 1250 257638956 257638963
    0x1d060a0605061815040b0406030213061b030e131d0d0f0e090606070506101a0a0c080d09080d0f050f01050307050d03051e0a020d0c020f0d0606090c02 66
    0x480001606180c03000c0050181440b200b6290b0190302030034403010359800b2006204a107442c404040c020030200b0800401c0034404140600301a003032a40d001a00d440da16803028110031030640102c01445003420010004411000c0500505d60345490260501c2c0c03602c0d0003058011034031a000d02d100b141060440110094003030b604002d0040d0b414100d400101000c0c60607110318084045c0700d0b0008540c686000c1d440e04051240c0b980080001e0000340c582070081c0c40b014200304080d56100c00b11120b090040104020a4440700e000b9070009140174584600c549000d0000c005e0440c004044200108040b45500c0c1140c3c0440c0c0e12a8002c3c0c4c500769503002038522000144418910444000e1825002c1a900342c02c4100d01c7c1e040e60b0024005052140c101020041c001e650b005080701001002c120308080c8145c449450040700309002e03a403d44502410602078103268001e0b01c004200440c0141240160303490042465800d00c00b40c0d0701c03000807140342c200100074000d107170014880e403400d000c840050b031640007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 257641456 1250 257640206 257640211
    0x80d060b1809060906100c0503211902030c1e1204030302031f050f01033201030b0f1005150403050318030601060f08041b080a0605040302010f06030305040902070203011d06 76
    0x21103202d2038030b5a580c03041105005043c0c2d402508261340e031003070213100390080107501e818600030821241007103a9004500d00704203054840005003c0001d003800642101c2c1600c0c1d1400d81e80c8a00d0545c15450103440c900c080f409005407025807003003400d000d82100e20303546003140c80e0501c10305000300e50742c0382c20306010700654400d071401c104484040050307848000030581c580d420b64078001d0080f941c8040d0840110050103402124a0013008104181c1c240b082c40845055940b400f561270354682585035040a500c0454010001185000444200480c88204c45d29520036240112503110810041e00c0f011781650050b0b820041940c8800500208400f20301d90247ca00c1b420101c0448156070f0300c0301011111081e0340100302c2e01182c540d10104002a132403000184100e1041042c0d4641540d0f00c46c961490611070b0f03901940d01503907802c103110600d5070a0117204141310000d00f080c007020385142d03001012482544200d036021540403c102e01196800c1d00514401400a150720010344210f130451034580605 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 257642706 1250 257641456 257641459
    0x10c0806100203040503072d030506040b0f0f06010f050c0f060103060608150118020d0507050703020c100509010c050708030a02030c07120b0109020705010e01110d060e060904080d060b18 82
    0x141c90700c441c0401e1000044509490b0054050034000780340c6480b10102c06250780401030340403001ca00b000c41c0041d40084120095000d00018031217400d0a040a00140e04064040c3c403040800104109000144442e560742144007841d0000e25170505400407a9030b4090490030350282d016015a0074965030001030503a0607a03000381800c001240d650703c9450f5540d030008160760902c001d420f004221161905458a400d09440c1c140545800c1448000e0811150110742c0c48000c688041110018168100590480780d281503520410260380140c01924074002c105000707041008118910781001001c0c0407110050401c401100d465900c00c0f48069102d411a40860840d84500d800c0011040d1224640c1001d0980081c607403504c990800030464081c0d40480d000303541c03c3d9201d45810705031100c240b1032108801500380182d40c6840f66509002c05a0743c03a03501c2001c4040042007400102d40e61903854582141c0e00c0b82000303650b48244181000501407079402482c1300600441e0451a2800c00c11345420300060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 257643956 1250 257642706 257642719
    0x807110915010e0307030c1205030f070804090f2c010219020c0907020d0c080d0207050610080c0609030c09040f080d02030106080702210d0906060b0a140307020613080705010c0806 79
    0x4180090590b100e9071840054940088548200500c00c981400c23015500d02a01c2542d150580724048180241c2c8a00e00032145128009000c00000003184607040ca441c01c4484107002e1480503c090300d218050003141a00d907000b0007181c021204500f58120b44202c8904940380800e81e1140c140a911001e003051214050119100040c50007440810080c3d09164a03442d05c0b4182201616680801d03009a124031001c903902f0030030000800c1080107000c3c0b0a0300c2d210090032500307092a202d1403c2032450361a980c0102c1c003d000080c01a5004504946111015a86103059a0b280c0c24041001c400510700540b01c2640000c10101010303240e001036040e11810340703422a1646070105c040703030b803810911151000c20220108210b07903130003482c0090404519903032001c80c1942c141d40b1601c045031040e0703100411060000036030000c07003604000c0024074054050419800c42c80e101802a4442d0002855919849226042c5d00208011181034590b465007140080042c0340711010040c04020040d20014070890307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 257645206 1250 257643956 257643977
    0x60617010506090906150a031407031707050c0402070809130507031802060706110904060f050411090d060c03020f0d020307030e0c18090304080f1506150403080711091501 75
    0x14410b1005000705240c034010400d81d030324406c0c44151aa0a50b00c403a521460310803001001c81c1c91008440c1901002d800a0084c0610b903103404502c101c0450400ca03050b030300600002000c54130104490781c8400099401681e6030215180149072407240003074041d4000c0c045e0161650714100790740014459001070f20100308003601c05c4800e190b0380988600c001d510100030400c070300020304ca80e04490300a060701d0085c107051034905400030381a240c040c0c02142c544584050108032924144c09000340011016101514050300c2c800810200c04115a0241206886240300c0b43c0282c0f0990444500780e000400c0b41391900c0060010b50302a41c400e45408001030b00340705014542543c00301c0e2000704280020069410701c8058081b81c003130750790003e01c5040b40c1d0100380800206064240061003c1c3c061040c00b5000219050f02004039005010300601d0103081c0680c1000085507441c022a13065039000304849841769000d11704421885804000b01e5000107440061004500501000e00110301003600c3e158400b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 257646456 1250 257645206 257645209
    0xa050912030a0207020f03011107170a02030306060a020a020a06260105010f2003070506042607060209130e060108010c0503040507031403040902130501080601020f070605090607060617010506 84
    0x240e0403242488448442003010890b150b4442d030081c01c00520213440c0301e0040030304500090844d20740c1e40880b950381c00d001a100c0e0410036036006613944402c4040d042418191501c1d00203541c0c0c00700174a000c0c0550400208825500d00812204c0d80d1254014042a031441d11148001d0840c074840001d18662602e0f014210413031250001d020f8141c2c0c0040e0743c3c458008180c444122000c036070b1903202d41109140e1550b2034140010903c000c2c1080780c0034800600280c01d15191145035041c1300382949242110300381d00c1095807400b5a0071103041c13541110380942c41c1d00d103170300c00500c0e00390511460f804924940580d9070030b000300c04200a4121080d00000b04060442483c0030f035001c1c4802c070b07001401500702ea02c00b480050a9600841a4800d5580440c3e04050700e50782c841c012644081c40c1c0c601c08043e8054100229a800031890340d214501b03101070288914401001c90307544d5030342d000384414494045040319254861005031074117a0b400c103009210781c035610900700c08885d22007000c3c8142ca5003041c00042c00ca = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 257647706 1250 257646456 257646463
    0x30605030307032c0a080a02100f020d030218100f090602031309020a030204030b1302100c0302030a030c0e130501050a09111209010207020607050c0a0614040b1b0304030b0a0509 78
    0x1003034040d04c542c082c00e038041d0f0900c0020b04040880500e003181404030480d031500c8078061107014002030030040c90400b038680100300e09810800d0020080003141d2660000c0307994007091296805899090242c1c850100d1503482c4203000f4864031490302715014004515140b81d0044402c9400903080e15a5a1080e441b24400c0782c40e8801d5442c10f04038440700c50760070000a5a41c1d80202040040c40c17a0050600391260b4810b10020000e07034014062040d01d0403a0025441c02c042d0300320031816181080030035107070155006500c90242e480e0321010b0582c0da550140102e130161030040d044000c014003201404401c84449402440e080c0181400740c40d1303a04001c902e2490901c200302881100441240c100241445202c4003c00700402526155409000f0280181c603030340c015060f00303849600508217410010f07083c0b12003006c1c20382c0402e0400020404075010500404121402d0703802c001022550b40103104445030304c44510031542d1340310f80300010300081445031071300e5901c1c050f2140d0034060007a5260302407a50356 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 257648956 1250 257647706 257647717
    0x906040b07020301020904020f190e01140a0903020310290a0b0a090b040e01240f0e03032a1c0f0302070609060603060501080c1804030e19150306050303 67
    0x4115504000a1041031404809000c0003031000780094686a0603a011400b03a0b009440f0100c45203402145039031920721814070740003091840341740000d02c0b42501000240441e42034070081642910000d11140120b02c6040400041d68014044400744c0e00460b0015009100c00e0480b444403060408480e0616500055102c00e000c01c02480d5841d524207041c07451030340e640b0030f0031507a051200603034000492481c00000360005003400f03d01d036440c561400204001400f0071305143c1d908000d00c2d19000050300c5d0045039a60340842c4c9072524400e0404841e010914600c66080804103001e01d801031407030f0b940004602c00300c40c1000081541c1c03400840d251000c50708900c2c1200d0001180c002c1c040b800281e4807039405030000e1070003074102160401e815212031007100e5154106948460321140180400341c410488000320302c005a45a012000b20340e113074420841005840101045044600e0350095510208191000008111904c0c03050b1350311064450501444010803010a042c507800040074600401030380c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 257650206 1250 257648956 257648959
    0x60a0606110c010f1e05070c0501023903160f050a081c09030807030c170c0318030c191a03040b0a09150609090b100308190c1a0f0108010209 62
    0x2440403140c0c01511044030204d0044104070104181c3c0c0d1342104411083c192924540e100d041d07035050700d03007000404400345402490640d0300824215403140d4500690444030000c506d2250380c110300108001981a0669903072035414030500038030400002c2070601d4141120203c004240880e55a00305000f2040748074480c122541d000143e0807094000400290101414540340800e83d10361030365100c2074560040e010540002c0c402c0f40c034050400010030402d002e40b08010341000d080416401d1010758074400c0050307840200e4103881c2c9124194404100a02c0300d010000c2004a8000064104000c20121031160104031561504d04c02101068a001c403400b640c0c00100003e01c41e66000801030180ca0f10720300884440b5901c441c846403549039845904068200403078041170590741418032080d1600b02a0202141802c005000c000141000040314603009080365032207a410114001a41d804503d001c0c00f400300c840e014a2628901c04540f155440741040d045501e00a0b40c0711840d841c05c0b0700400e105903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 257651456 1250 257650206 257650213
    0x9010e07140304030318120e040608190804030b190c0e01050304020f2404050102010b0a0f030b100f061e030c091e09020c0a1505040b0402060708160302060a060611 72
    0x15424014000c0c002d50b4400d00071300300411010090100803402c59121141038490440c0702003203610940c2d000744000101d00342228107020040c10b02e14565151940701c4041c5072503455003140b9504125504060b03400964000808143e80d1400c4c020030f0480f04048540b54400915041c2c0400a2074010700f8035102400c0180e44480c2960b4469090040380740180c428298081410342c0e08090541c50202c111038070701ca42c07648240e1240e142030000390940340841140f030300c10071b08400305114004000e00c0130030440f50803094242840e20358000400300c19a180d002034817840a005000701d81c4641024003400c40c01e51500d550003680e0300503a0110100c45400c0302480015103a60f07800c02c22901300786d00b46084100a120203c5030550745000620403a800421030a61581000308044248640746800200300c40e2000d00500c06841c1960324962440c2d00184000e128003401301c1c01000344117035101038640b000030501d5038445d62103240c14040e59541d0202c903100e519900300000494505d22034103240780c1407140134005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 257652706 1250 257651456 257651477
    0x1802030415050604090501090501020409110306090f0c0c0f010603020a1e15050c070e0f0708100e18030a0c020a0849050d060e1512010e01020a050909010e07 69
    0x60000d0700029143e5944151a9a45440070480a105590b000fa201d0400107a44900d48103600007900c1341540c50300a01e0f5400d0003000b0707039a1550031b581607100350484000070380382c0c1d20b203107208c00f090041c15498203041c441d00e02200c0110300e0540c40b030300a0b40e000711004040b4030340e03c2c0c0703810481010011602001080001c0200014400f0800c0d00c410380645041250034010300d00380701c0c2e02d0480700fa07010344090101182405280500c18515941140c01e51610503c5031812200414083d0303020700c5180e00400313004d800100002c10780030710381d2113925850040d240d55101502008103203610b5060103911410484100242c240400100520054004002512082c103d14a0140001c00900c031108402c1044c41c0301980d424201c490400c101c031aa03441c3d854a8a26032000c080844e2200e402c800d00e0700f241300c07082c4401c5007544401003450070030480701d290400703450044280c00b6040440c1303500d62540c0042454040280c01c64050001201c09a42c0180ea80c1c0e0b8400c81d40d00613030f500765500c60118122072071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 257653956 1250 257652706 257652743
    0x1a0702040b040605040f0f0f15061b170306011215090209060f04060801090e06040c0e0a0905030a0f02010b04060501080408160206120f09010b0303040909031103030a0618020304 78
    0x710101c0080002c10008689503600007140545020200540700590b54002d2100802d032117101d0541041d1500d001084101030881103546146118000c0e501800304d005c040e90f102c0d0400404060a0640c0010b1001a042c007014500100307070002d460150110708501c00390591480e592007406d00740012520210801c2e1b240c0b11664000394031000b80d15030081d4041107443c060380740c600000c0000702040d035280e541d690715003002e240442d2800b0190000303076042032003807002107902140800c2c01c0da4440d0110701d05940f955030054009040111004019004c04a020384803e0f070000c0c0c1c60031a42e884c0d0f80080c000545d407042004116480390003100d001c21301501c0442c000c68485030141065209440c6c040340401c1250700000c0a0b600440c629011a034042020881044a8902c2d0250004840305c000d004505250700040c1d1039004900071220283c1c1c2c2d9030540405d040c40341a032030f03030045076650a6035500d040861190001d4001401003081c0103014200d00c00c0e910300c46100300d0340702d15003102038540f18000d01e18 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 257655206 1250 257653956 257653961
    0x1050f030a020328120509090f011409090c0415050117011a0a1107030f02040f090510020d060e04050601060809161e0b0307090e090d021b030a1205131a070204 70
    0x20b01c0c2001851803001c4c00001944c40c1d050f112010404d80c403501e13180c0504c04204610f201004108001e0003081d1001080794682400c1c20029106044400780e4642c2d4481480903d041100c0040720f038090b05114030806011140c1ca0b642c010394500fa030381d004120300e00c06820030f070042003845921080b80c0f615400803064144680a096214054079140d41b07840e51040030700d4941502d07504140d400c8203024001c41d00b140391501c503100300160303503000034800c100143d10f8568440e10940e00e840502600000d2581500509501c414064006100090002d0405081141d500d034001d000c1c810106542d030000c24009a000a680105010318a8054400c00d00b00302c00020035544c8102c1c600b0141c0e0345113401180c103003c810003039480354500e80e9500d0881031034480f10b03c1d034009000d0b16018a0b5000041c01c0c070356143c0c2c08220b80400500202210400702c242501180c0741a0900320054010303403146600c1d071952a44000100110100c0c1c15040d80700ca9216000200541507181d80441000c100300140801420581c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 257656456 1250 257655206 257655253
    0x309060417150108060a1b050315010909230f0f010b0c1f0e070501090b0406080907051c060516080105130b040612020a080304030f23030a050301050f030a0203 70
    0x41c410b4921800710300b12000003080e400e0300003952580000e002c02440072034a220b03243ca540201c001440040040c0d03540a880e61002800803500c0061040008005900a20b504001810614010410a15000c8094460314620140c62000c14292404038908e40350407001c0c2c0c0d015022282c0c8a5815902e45600c1c001c10381e0100b0345039203550081c285c08091100512441c041700382810140072800703c0c0f814402c4c1c0c0c10004503402c01814030455110610021008009403000c1c0d03112400c0503411900c03128101c1e40750054680c8180d902c4110404445050a165400c0c1c9141500c1120180120380790008030303001c451080d01410001801002c0100305038a0f1104914a000f000100000b54800c001030200d020384115807c030241c41c00070300d030900c2c5c00c606200443c8002000d2010145003040d003180c0c0c1c0c81ca03010103a0b14010700704038000100010081c0002d0000c074948211a81180e07581c40c80403802a1103070700244581440b0b030107a558038069030304002c0f4170305418a6006010f03198240101065408007000d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 257657706 1250 257656456 257656499
    0xb0604090b06061b06010e060f010c0c0b0a030209060a05040e090c010206150f030706050903120f03011e090f0f061212030c0e0a0308030a061203170403031103040b01150203090604 79
    0xc4e14030840342e0f4041401014083c20450f80e44600300d14100052040410140c01182d0420011245142c0803549501c0200191144a20401d2f43c40020580c205c01a00400405230b41c084070001d080702d55550050002c20840348148910f00c550390341d008160b91203030808039506000d60010760002d01c8004140070388541e0500010610804c0190a9000c80c2c40d02d00346411110110300c000880314024602000710020500c0c2e21514603140800f100d401d0045800b040c4112640126414002c0c0304054071101031001901021404000c042c8001900b9800f40a440b041024603600e05400420045403a0040700c08094001511218111600008400908541c0061820014600c003d0301e6a03582c0c0c8030900d8001c500640c000bc0c0c03a1700301080a00122401e03944002d10310354510403800e00207500606242255215100101726030355841c1010b80282c00013a003840b00c00c40c0300000700002c0200c044c196038140e0380320300060b070001c1200c1e0700c080ea83c84c4555031034140e1107007043c4000c05c036441c82d107441d210500c41d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 257658956 1250 257657706 257657737
    0x709030812040303180b011e12110105121009150b070320010c0e030c0301090534171203010b04051903081209011b0519021c0c0b0604090b0606 63
    0x72860002c0051701c2107180104d60811101004004182e404109010405d0f051480068807910f0090014202403000b480285901d106110b507207200c0e030140003034854400c2038070000816450000740b00c1485950901500751054940310070200000f241240d1a010b45030114840c031b10740340c0240c606482c085102051104580c402010002d801402801051030961817a1502030703030010328a0805090040e080555400383c1e250075580b0000c075100040030f00904010000d8441c07865100752251607a00c092080b00740700703047d01c00d0001402d407407880da082c000d110441c0152030001010280e0090300384003e00c40e000c01e001d420b000130b10183c5052020095840700700c045030320015a481e038400c4903e803c4000c030070700c1034108101000408070081c02401502404030704903010076400c2000103001c50084a204a041c1c402c0802081c0c1818001c20030392038203c090035400140340b00100c000070f1140b44c1d080400c4407060401408507860341040d0043c411525806099036650fa6107117020300c55135400c4500904c80000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 257660206 1250 257658956 257658971
    0x602160b18120111090a090908091002070806011221080601030e0102070f0807050601090603050303131a0c0418020301120b0903070803041109060306040515060a051909050709030812040303 83
    0x10000d118659034045040b28968481701054100b041d40e44441d4400e01100e8280b0516a00144c407810448030401400c91704028402d1031444102e04e00b1409400056142c86048004100b00c142c0008101d9008e128040082003800880c181e04c0b0042241c0c600c2c40085028600812410360003500240d00483d184000107083c091551100c1010100310001903a019100082c5031042c00024440240500552441805028034650380d195691100400c03d40141c01180d50351230401501e0900410500c03440d607480740441c1003005207940198007d2040a800401d00c0b02d81126159403402a01d040720004050340e803080310301e03440301c542055008099903464041000701c000003a502d007000d50f00803802181504414200c10060044000001d0b00c002d2081d2f001504210000d4000a2402c3e01d030803c0308c05000c640d49550003c6a21000d29404c11a4416400380c01d86a11000301404081200c85000c4103103c1134490710400c3e6100400e40c00b000d40500c904002c404c210039600d40540f034202e4803a180008803030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 257661456 1250 257660206 257660239
    0x90e18070b090a1d010b03040807050105070305090c01030b18070e030d0f03050a06050f2e1815090e060a121b0603020910110a06020c070602160b18 65
    0x994112846400c0049151465400c2603d442c2000d401003100100d15031100310340d4001c004605114a0b900b0030341c00000901000019810703220019800402404242401480030b0082c00c403c991103801e61268003c110190b61082c00795980c041d0002e402070314500d107090310f04c083c0d0148c01800e00007844001e81a2109175103003084054518520b942c0c407000c841c4203070034000341502c0000d0700c0d60aa16040076402e1000c0d40d01c54000300050181104e1000381c0300b03100c5e681780b49040c5000c04c010807081c401525419489402c40c118400429091034641589034513840402c4109818286800c0000c5481100740580c3c1c1050741d6058104074024510380350b00c0c7e5159648003841c00068030032074115003c5440800b010188a40c0d4030058000c5003000d41c00d2207206c0000c1aa2600d0302d401e03103420030001821007101d103581170050004050b0408029580c0700105c0101d40d40e114658407a0390014400c2c402c0f10800d4a0340140c02605480704d003041c0781c2c030344400b17500c020b0500a01d8150240e400042000003e0740b1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 257662706 1250 257661456 257661463
    0x40b0924031903080103060e011b0e031f0e0c030f0a03050706140a020d0b0f060904090f0c0b0306030f01021303030305041a07030b010212070510200c07030b070f090e18 74
    0x361081d644d04d200c960440c6810411307240c0e022000d0a0300c0c0e0510240010005a03603040c01c4004409150000c01e240c8040d0009107010803254440d520b101400140d21035454807034120100d100d00b0720f4111203100086208ac5a80c3d08072803402003200750482da100c3e0001a106000910005021703440201d1401450580202e00f807400b40c800d05403d41d070014600343c000c0c6050007003c1d0402003c0350208030803501c035000704e11140300700501c483c4181d40c0c032807842c0100304070900d1010800fa0014840c4420726110744a81c0c40c0c0340d0060b50568400d1140122485484005000303e580d06c42c14081c076107012a103103641c2a000350401030400c0781d21b02880b44030440030f1901f9400d001c0c424055a50046000d8a0980000e41040000f18066a4001c002c0003039802081c00001d426541c1d00d505480081c0c4082980602c00e2a643c2024000c103d00100203280a182c50780040c2850030759000d18030000058541d10000da44000e107050450300803070180181007042e0001007030090f52040602030700340d0400b00040ea90908 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 257663956 1250 257662706 257662753
    0x503130b0306100807080621120d0b100e13270b01050a0f21020d0516050603061804110a091d0d140d150e06040b092403 53
    0xc03104020081180901c1c24054481c1004810304080101c1d0414071001825104020442c6002d182690f00e04156603c5000040c00c18403900303403d0b074440520b108001121680104001000d581c02e001ca0ba140c81d24200c694802400c1ca5a00c0c0c040544030110240600e0000d030317511416590345e542c1d00b00c2030542c21120f6a8080c03c00c461000211f480e08a2510701607001e8182c00050080000c00f005106035601c3c84014801c0e03800700035400e09656586c0d4110900903a81c082c0007034010780307006140c02c2000303c009103005980003040a140b10180d141c1003030001a00085a003c2e6000301007060b00d9000000201c501c50304103000d554480080203441020032038000d0701383d000215507a650f01c903d15400c0c09000703000346045c042c03402405480480c240014482c40c940d0389007124004000900c5100c604583c0d000c0c0ca040c007142924490a0340d50356403500d0700d850782210700074096400d200f0030042600e02034003843e01c070b02c250000c00c012510030741d03081e04c210300c506e004490340502c40d025195114030001d43d00d018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 257665206 1250 257663956 257663969
    0x50904061505060f0304060e1c03052a071104050402060a1d091005040f090203061f080105010b0c0115050109210203010207050a02010f02030c06130f060e21040f060c050313 76
    0x581d20704040c034101e0125050048c0041303846e00304420034403030300e4900700c001c0200010900c1c02160302d8a400000f503c1507050b860035403c040041c2c018828001d58444040c09a4a000e039002c9461080c240d01880195841120020342c040400c00c14402c4081c05040e00102c400074502c024080d41c140341010402d101c070b00369003c0b41000065801007040746410701031101031280d0014203000c40e02c0a0f50102e951010060000c0007030840840c1c100080807000300341c400c01021008002c0c030095030b51341100c0d00306910848041e03205500300801c0d11b90910000703451381704681c41a500d0400080c0341c90081c100c510000c0d012400c0a000301ca01f12405642c09002814901d8022005411180700a20001d402000c20071555000d641081c0500303c1030040c045007a59002d141c0300e036180f42e00156441c000010950541c0c0c001c00507850b00601e100650000130b0900060381021403500d94407a1140d0502c803903405244a48180b1082c4040b0500103140f00e08a4030010b513104404603420038000b4100e160304a0b1840c1c01c901d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 257666456 1250 257665206 257665237
    0x714030c060907090e01140f091002070f0c060c021e010e0a030501151e030201050a0e061605060c13090e03040f08061510050d0c0203131d0702060105090406150506 72
    0x140007113002441000386002501e0000c1244909000740d407414104010000701c01d18443e200041da0417a8148001031a0520520f0704551700c001d03601e0030340e15a41d80f091041c0d60841003100080b030340314041e03074102c2c05840d0004d151200150b01d07420208603404408100504010f0320900d00384041d151641d060000d54401c0c800480c207501c0307103021900c0e04610ba6004600c984803486506107625074822a01d03058a40a2801650b0750030803000a4984c0d460307030307070401e0b40011000405480b0304012504070102c06105800ba42d1a54480003410907003070250403425000200c07241c4d0304010b0031041d80c0c070180d0000ca64500381c0c1d0409070b461500b044460942c0e80051029081f070020000c2c501485000e0b140e403650116050002c06c51903840080441c00f5490452104a6650390024600d0b070003001a20325444190001e200e003030352617406180000d60000403070b424540342c1d42e0200c0e1000380080b90703407810307601d000d0910347c0580e5480c1c5622000d031400c44030140f200c500360a00416036484240007004038542e00c1006 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 257667706 1250 257666456 257666459
    0x90a0b10030905010b03070510030515090103080306041d0c040504050a2f150f0706110307050406020609060112260a0c110306100b07020a0e040302011b140714030c060907 75
    0x9805e66190400e82c522a4004a009020540d80c6909000c00c011440c50700003003660b5141c0c54002c4ca540840c00c440c3d40140b40303a00001c1008000b00045105402c02e9500340503c400c180100c00f807052240000c0c0c00e0176000202c800c500c0741803540c400e560050158040700d521401c161110200050307000c2c0142c014032403101086040d000016001f400000060383d0300c41f200e4400e03142c0540303d80155120404490000184103040c04243c6c3c0112482e0f074880300d00a981c0e0700b40120060f00c607600c00d204000240c000e4100055840e180031401b903049408400c0c03008642c0d03515949809900c00355111410540303a02d10001501c4000c0310000e000d02006944510004010350308203c25006050354440e4440ea0102e403c010a483e00241c504048404100a940d2581c9580c400162034110a4119113040421402008185581500515100c65003c0e054200011000000310f40444012108400e0107404001d000c0000740c50703a1460084244103001c3e6810800c00c40101414070000361020f42c09580a041c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 257668956 1250 257667706 257667713
    0x7090c090815060105031801020d0e010b040b0414010902090105070b0a05061c0c1710150302240a140702030f0c010201061e05100c081b071401020309090a0b100309 72
    0x40201e4200a82c220035614906040000c2143c4001441c481d40d005425403003089000003501541c0390407001d200305005101040b103145000307140710703c0c845104504080020140d401c1034030078004142e02045001510b60709042c080d41c060340c042010039041040070003100010554564450b8020004884082110306010080140803002408100d03d40041940c0046c00503540105040c101c40800c030103040307024089525641012a086010032a0301d04004400c0071707103000c001c05001528402c45078080d040119030540396040c90b0402801050910801070070651a0241948010001900d403206107450303c0d95010030304190388001903413036a81c4002e200e40b0041d0b80a02490b0040c00c0b8055001c15841441c0c94980c4e984049481258001c68446a042803628481d16913111982d42100099544001d10628590004414050002c440c0600c480204180518282d8070024500590081d0b04000540041196601020b00300b8062140d840d400846207445615454118507083d40380001d41500a00b07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 257670206 1250 257668956 257668963
    0x20f100c150f1407020604061a0618030d02011512061b03020d05151c06020c030a0c2d140a02040c0f030b030a03081b2b1419020c07090c0908 62
    0x3c4a2000f500005010081c8243e0300003403076984a50031890224899104c000d886421a202000c107603003000d0300064106002c0c0c4146071031f42d40600240c1c125110b00359124401c90807241d49049094625550210030843e018a103111340e82d10501806001815400c0c0061400d50340860260765030100e0b40200301300d42c9401c02071241d540e02500356440020858180030006c0c44030400b032035000c40300105580499080c018540c0c1601c42d254691802c803a074070614501c02400d041100c8100710f4105076038402e86108204080d03802c0c241c1c00010b03d080c03810051907607110129480404041180b61050903a0500580c4d501e00480303004400c0c913100c22001c203c0c0c5034001000c1e02c16040300103000340e0240c24403400180d444540d150b40401c09202c0c2420184004d11507000303911441c0182c070416087c0e0541405c00e41080740442c040811f10117000c00585034404041c0240003421103091584901c00942e000000f5215001401600c81540944d1403d984904540341200c264041141c00102d100c00144002503041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 257671456 1250 257670206 257670221
    0xb03030a0c12090305030d0207060b1e030f0106030c0e0a09060c21050f04020f2805041b0206061002070b04230d1518020d030206040b1003020f100c150f 67
    0x3c1ca403101d009415515a03039580d21520440b40c5450340d0014100007480020340c804211041c0081a0103803040590003140d03040c48a48840c0303842401035000c20f030074407001441030b402183e5121182c140c6a924064030400b400c90000c0c0100543e41d216454000000d140c0d10440780c03c1801904c1b62055070007007112444600300400c1030200b243d4504800e00500040440c1c40592180e03040343d0918158000f01c0c00b0a16024040082d00d03a403000801820490078000035890f82611000d441c10002c030304142c22420354200c04020200c0c0540c1051010410701d0802000c4144201030350300403204104c3c8e03692581e074900d91261b40504904034280010580143c0500800e81c51030034201c07404520500551100400e807850b509100070301503510310b0900040380f060000000d1040c0c0081920035450030b10b0034040c1d21035008990465041c8141310024034644200001c807c00c0d26005010300d800398525a00344045148400c4c414030034002407021120010701d151580c40c503440400f50b00030403030944e01290501034800b0b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 257672706 1250 257671456 257671493
    0x3050709050d0f2d08040312090e130c0f0f0801060506120a0209040f1b080a0615031e0c05130509071407020d060c180e0105030a030f030b03030a0c 65
    0x40030190004904900f80c194100c40d00010140019580079944405201101a4641240103072800440038172240d4030240c01224021061007881541d404000c40e15411107026a0400300c101101280300904800000c80d0014411207a215840751548402c0d00e41803046e40c8014407190303c90000340300c0d190382030240314003c10040d90b8050a103150308a444242d50750052030b00c0091a40810381d400e242d034039504206040c01c0c4490b010000c02065001718412160590001c002103102417010034001c030b44900c00c4808580c0c803500b81c3c149400d00300b1b10813006041341011070031201d0000010710100c80c00f1403148150781201a00c07115982c503845040041582803960040d4403440b14a0f0404c82c03c02c0d0440b000c1002403101c90000340d076a8403d071000801d07076040d000003d051140303004002c2940b50b0f0000c6683c0030101c002c207030000342c40750340307030b0050050321400d025068040d0000c4800382c00190007804003424500c02400d003c030b4114030260219266800451005d4000b0fa880c285810a001000d9024143c2d08103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 257673956 1250 257672706 257672719
    0x12020109061a0f031b011d090c0703030b1002030412020a2d090203070c0206090d12030e0f1b0d03021c09031707030f080702030904020408060103060b030d0c0f0c050607030305070905 80
    0x1a10420f18004801c80105d1414013002c8040a06090340701c1017240d651201c0248559000e09002a079031100340c0004c2803c50109140444444240c50000b01e1200301c450654001c0d4035150034440000c08600b0244000c0780c20001552010400e503c2486504111180070404030300383e4084070007400700303076600c3c0d911450f002c510410074021590b03440000030200c1e5070103940b99542c4079508070210b5911211014041c0040404401040c007190f4182c00c5025240c040c46c1c11181460441c00d100d07601d403148020500340078125000401414142040d01821003030103030050341d2407500c2000109070009c0303294828100255071050240200705040910541c0d003c03c1d00b48403418a0041c0e07030050040781e810030518090001900000340c41c140300300110ba43c2d0700c201810a40d00c40da030b80c00040307039101028041201c0060070301c00c59040b40d0500040103100c0f4011595100242c2c0302035200c0c1800d0300181801940d501039142da01182c0ca072500402010f801c1e01c00d0b80c00041c18030301400018081052500414414007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 257675206 1250 257673956 257673973
    0x50d121d030a14040317031009020309100c0311070204110f030a050a060909030f0c170403050705040c0f17070e04021207030b0f03070314010605040e060406060e1312020109061a0f03 80
    0xa400b000d486c20700086481c4900c0c0c2d83e0700c1b031000c02102c61146074080c0f20b0003400002045094400402c40a5103000c020307a081c8450811080154107940360303451400000c050a100701c40c0949480d40284058200c008250f528003419004041c805506c2225910000f684400c1480340d4014180b080350b00400c082c0008001c03450250f64001c1440d103148032a1800c018210392480b0600490300f03050902e0000c808002c580d40d0356681340c440d4913440c42d846030030b202d00e10305481d5035a101d0092426420038000780d039484119040030019801046170242020040140f0383c0c1c050401c4d07845500c01482c484502d1030030080140b400c07003401002c2e2180b1414541c0160418401d0300415180068900296a8480d00d01003d010714041114010041903216a61060801804000c440e10201e5883e001d10f000e51005d00c90203880e180c0041319000103071581d00c1c494002160304404203074464015040010144004104c1200f55150034041d6580101012940242c00c0700600e0a0b1500340c6002644410036030203001400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 257676456 1250 257675206 257675213
    0x10506030408030402040b120c0a080d08071107080a060203041104090b060402070f21020d0207050f27010306022a0c040b010203130b120112050d121d030a140403 71
    0xe000103000140150808404035046548540100910706009032452080101c0c01e17000d1540c882520a10b580990340181000c20007030700c08180140200d841c0e4540e02d0141c0c9541000300c0c1e41291141c4a171040303024400006c103500c1c10920101070642c1c0200000350703c0b420f00b401c01005142c400140703e0320440c981109200003498648040360f200c0400c81380142c4070300c200d0400b040d20910111740240380e1020724008106410b0780c001140c840300501e50032100b036075a000400342d039541002e0084592044803540740c17840740e11700b980c80e000e4500301d4403c10010707103a040303c00f8072801103003030b00101c40c81500410410b801640030580030050102c0e000c16541e8040000c1c401c0c54035881d014411900554a40d001810a40d000f0421075200e48069010541800d554604400b04c68015442942e00c0c1400c4030000540c0d41402c0c0b0107141056040b0b0064078110511007002d541d003010384100140c515881c0c4140f220014030008007001d0000c441d0303015543e00c80e0503104c02003035000e071380c540001415403c0c403042c40032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 257677706 1250 257676456 257676469
    0x18020c0a061508030f030708010f140607060219170c09010c0f11060304030c03080c030412030c0207050303040b0c16030f1118071112031b160501090c03030908060105 73
    0x541c00c03120024074100480c0c9001c80004094000e19920b2000183d040d00740303c580401544150816621034419988444480075040443d03c100c140042c2c6040c148031b1640717805001000858424800145424098800d02248035891190180800c5e00042c159250031422002c4540c414032003a00180780075842030000c0c02c070240d900800b40c0300c500040d100b0405c00c0800a48400c90000003000799442c0d150920300113100c208a044100c0008800e000030030900400e44041c3c1e0b00465012080140a050f07140c0100c000f860401000740451040c0300e400181c46d00d0a0004001a04450320520b0382e4141c088078540c80c10680307c0e160148504012420004500f81e052140b0025502000c0d800c1d030b00b0910b83c00101524042c1941010a5080105001940e074000c400c074a0040032030001c2c2c64205503a0200341c0e07440c0c00202e84180711101140c142515080400300180219441c114880c40d940903551030b02c3c0d08560700c5103012512002c059205000745034101204178002c00070314004207070a46c100401b0595 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 257678956 1250 257677706 257677723
    0x30606021209030102070c031b0605211b030a020c0c0303090a18020f041206231308040909080309060907080c0d08070f050c13060f290a050418020c 65
    0x4800104a082c826034082d0100c2e01055004204080125104d08010300600c04612201204408062000503035600907006e075941c403402c031042458070f03c8000801f641210301c028001601c141c180f80c3d5120304d000c5d624024601500882900580325400f1001462402c1001103416100e46c0c8288a500380030b903905815402903079640301100c00c22801c0344900401a0007020500c00c4504404140400c501d0fa000c0c1402e080c1600400741400040301640420807961520304062a50040c048005540ea080070201d81100a1055080503d415500e01442c42100c6a8402c1141c0580000040c0b2007500400c100e125048100c4801519142d0b00e00b085d1266103036036004255003d0031104284000f444182c0094480250300700b0013103145018146885601c1d0041034142601c14414080c440c424040d0a20845058030403007545001d9040c2802c640c0c0160011620079044080c1748410306441449000300546124807603925465100e034104182e6005295016504800d2523206210040055000080e240c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 257680206 1250 257678956 257678983
    0x21b0f011103190c030e1827030c01060303020d18090b0f0d0c0918020f2b0507050f040e100f020f07031706040b031506030a0606080c03060703060602 66
    0x45034000203103045000343d000441c1c842c00b03000c40100c40c3c541c004004900b202e109940c2c007900302000c001044138a03008506030200c80e036500800200702d41440d002c04000d5002144510100f0071000420724a103901040c4400d090765124541081003640400940c2611303481030030014100b040d2191001e50300d0f0502d1041e03580316611031000c00c1058440405510b02c58402071b00302e030058501c606050580306080c0c0315102c2c045141040c00b002400110310160340703150b402410880c41a1080d01000345003218160b02c1c1640c907540c00348031300a026451040c14040d6204401400300349141000b008a9042041e202d103004600341000c03122148004035030a40c401c40701071380024688544041460080c01000e181c427003240c1d0300003030384010303d03403c0001070080810705203105059a4a04048c0400ea4500c014030940660080441e1032240c58a000265030111000d000c40e05082281d44034201501e4080c2e100903000d8204800581040c282400090342c01000b034281800280d01e4480025544d004121000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 257681456 1250 257680206 257680217
    0x3070209130f12050c07050613060c1502120f090105060d0605040f0210030e0f070501020d2007030606030515070f180e070e010f030509070302012007090c021b0f01 72
    0x1003080182c0301500a03110b9802c00d800e41d011400030180a4055408902411003030711501800066138030b0407104544542082c0324040c20241d281c00750550f400684000e040315441c0300c3e030460040c039614610140120300c07040d040300210b40c24842000300489501030704060080c0d0608080000c551900f207010f06045a01c071b48000341c1551581000d0948000c4000002e5015118090119065905401c0341001c010500180e50502c9105050b0742d40e5900c2c54801d980c0035030010584460b0f40d60003400d42e00b01ea0150000031800410705c0352010f6040080f190000c03150165120303c14018000f00300070316010350f007007104010503901f80b0390805000300251103100001c00240145444484080101c0c0d00c006000800c1c883c072440c1000c82c4058081d4600a07803060015200c44c01070500144030740142406030780d0700384c060082a4116001164000e010b00815840e101d50868075517000401004054001c0c801c0600000b480f007440d02c030081c240211180001d00300c0308011800517050380c0311100204121800d0910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 257682706 1250 257681456 257681491
    0x3050f0105090606070609030914060c07060503071b120f0c0b010e0702010f0f051608101202040920010e06041410020c120f1002030f0402101101060b0d0e03070209 72
    0x13802c0b40314810005088a0810050074101600903840703500391403810b81041d0050b40c90605010702d0b4003c0b11070400740d561000e44208550f60203000119081b41e25072070190f04900c2441e083d00b00d2440e030b500c000c4940c00c2a0040c40c03c400b07540a010841388076440c1c90401c8004400c0d84801480c80018020b20101c41c1c0740a01154100707000758401d04005658039418000310a034100c03103000812007110b103090010400240d0200161041c01c0551256000e8408490018100301800682c000380f25400c0380c00c0342e0303075200c403402081100e94a07001c0300240f04e81022480c42c0d10000140103040c1c0b036003080d01480d0144818045690610200c0c0701442042c0c41d58259685004001c0b40340000462440350004060340d01d50000300340118100714035502140890752041c625100140032071104440120303907010700c03201180051405902640c2880041c0c41c01c2c1c2c00044848240700c0c00c48000e548003d900c2d942c002441d0031003202038010100c0c030203668400786081c401c0c181c0200343c0f54080140f50301140e43d450203c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 257683956 1250 257682706 257682709
    0x912090d060b0a09060803070b06010509030a0b090a2102010f0c0c17210a0c020706171e0a0b03210f0c01060b03010902032203020c040c050f070503071203050f01050906 74
    0x421002013011090034000c1640e6100c0f0b0b5900c96009542c00d555074445d81001038101c1d4010411160a400c3c064014202d21144d81c895184a0314090401c18060050605070804240c40b40d080d80540d05010010300f51045075400044d007101d44450208940c1d5041c05500d40c00c0e5900100c1901150360030076600032400740c503c118403c0d14071a192030038010003041d15aa26120280340481c500c500017000d4104803003040a0b03400c0ea943c070080d201e19000a00b6039918081d40018414410303401415100c8480c4080b40280c14588008034121401d60000d903130340d04401103620741000725486081e44240881030905150305441218400c001100c88400d0001a403401188401d5020800414108416603100e5031030b011100d0180d842a0b442202d840e2502c3e5800c800000b40040b00310700142d154009114a280207020f001c05420400301c50320038002d06000081c4d84c105a2002840c0303151188014542d600c0c0e03189456010054031240803030070503103032000300581409250010f9041d07410031034045400d51745d03040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 257685206 1250 257683956 257683969
    0xf0f21020c070b1204150603020319231b0d080a031104090e06040b0105060c0706030b040603050a08041d09100b061c06080f010b010e06160b0705030912090d060b 71
    0x1480450343c10030010b89418900c002c1c100c101e0282e4465100f2840c0080203003199800e40384d1901003c0d60540015a480340c801c05041d030451110352050404100b000c41e85010900d0340304c0c08200c0d00125420490398940480c003000150929500100c4203002c800105880d80802401440144410f0507641c040b900500e61890040c5c0d001072440c040107100002c080c807005500c50400303070b504564400180d0300101c1c01d45450700540c1c6428907620010300d065441c0010031030152a0740d1000c690083d0341c440c40400410070500480002ca8001c0040c0c279900c9151a06044590304440340b0311032400c00000c00c0c4035000301e000c24648042484000003261801030746001403410b02c2054028020b810b0300509090340c0403d00d4101c003049910038410398810a544901090a82c1c44c0c0c920300e51f0005004030b41040c07040c0380c07410140c2032900030303442029840c3c0b0f056901e50312000401d40345180498402301c2042403029040152001666826400c2c2c0d003050040c00116061024591005000c2519000320030f03002d454a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 257686456 1250 257685206 257685209
    0x10501180e1f060e0306060f010806011404080f06090610060c0311120d0c02070b0a0507021e040504080705061006080105210601060c050c04110405060a02010b100f0f21020c07 77
    0x582602c202a6034850700603108904081081c0d01034081c0c4000103400313140c80400303036000640603114a842c90361200011a900070110f65030001e03c26050001250b045010007004107100a805c0040440d410310648030743c60000c0040103000c4100102605100301548020500d00940c0c1c50f0038503284002124004600340001c4207002e1202a002013172842c440c1640d074005480d144680c1e02540e01f165100c681244052080c18060000704608000710030040c200212017610722012003c044029000c00000602558004c0e00c040d52003d00c0480c0c00000d11206011845d00501c01d1403958400e40d10300203000d00550014445d0743d21941c80708810304120084042c1d031000c0c4131b5842e02030f170391030f580c540340003820401d8284000d43c0c56110780c508516076818640f00756a0361f9000048a5410a0301c0d1030108552036104030000001c554072241c249082d0f840f107031080b003014595511600782c401450b010090080c600c0b01c40c00d10800510302c0c200c07902103000f00c0e005103102003560320161342c03640c005400c6881c18000c1e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 257687706 1250 257686456 257686501
    0x4110f1803060a060e0a0c1b1103060103080714070807150c0b090607021002250c1e03150c0e090619080106090e061605090d0b0405060609010501180e 66
    0x8070400c0043c8050345901040a5510b2050f94500c29110a11424112280c9010701d9021480003080450503c690308801001c00740302c0d001080010b800031000c00d05001c3c00303900480e03c617030001c5000f2003001084501403404416440040c1740d59460901e4882d07851a29206180345032407091004a80d183c4100c0660000c103801001000749820805c96296850104a60352001030141945c0d14131000f14074000c4071806d00041d2040303c0d1000300b942d080d4005607000c410403141e42e0b240304000200c3c3c0c0c2d1002850001c0e1060710925400d95840c41c02c0182c1202007070820a0340b001d182c20a01c02545410040081d00d030801a40c8004c440d0740c581c40441e0b00084091a1218100820480000c0740c21054204105a440740700d41808020825032896a95410035641807103111317881205400d00c00e21900103070500640041c451410054903840300d10204070f060320b040d14281c20403410002c1e07a0a1125042d0b00402003803a00c41206242c0072203040403043c480c000c003c1e01e030341894080340390007403030f020303c484003400c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 257688956 1250 257687706 257687713
    0x207031707020c0f03070503060c0f041a0304060f02120403030b0a05300a030504030303090602120a02090907051e16060e0a03090503060c030c0a11070801060f0504110f1803 76
    0x5003030300007075542c20049128504c41c424100c0d40b0300e02424045080e208440740a0001d002c40d40303e0b402800f07525044441101d41611007407200051b10b88071154800c003120160700d01c5940d41d003005e0500c5802c1e00c80f000080310f00580100428040080c00360712641d8800e81500d000504525800c001610345172942d400640d00008001c01d480c54507120351119502c040d080344981c000003d1252089849408412000d80841e600340001c00100c0c0c040d03000450540e1052000511701441400c154030005000d0314005005580498600781e14200044419041511814071a0415000d01119051410558190018040045480303480b81122aa011199562140d010300c4075010f01000181e0300c0d40819000d138001401950000346600300440c400d03005044011a8070f1865a91081000c06a4800583c92040048034416040030a100f0f202030009002043d0010891615011f050020f20360a0742204d03214500e84041c030004038940c0000c44060514800c10305403981d42070340c4180095100003054070381500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 257690206 1250 257688956 257688961
    0x70b03090d031506020a0b0a090c0e16140307030c0c06051510030204050102030a08040311060c0c01060806090a2d05010516080f04020f060f070606090c1e0302070317 73
    0x3080450090321155000c10211100328007400e4203211070300c5150007581080d2052004030304948441f0b58843d29901c000304030b44000d6a00c1c0d032000b945582c0000c220000c00418080700b43e0b40c9000300c614104280c5486100f10002c04d41c001e80501c07015164500741135542480d20380e00390041500e8050b00341c014070100600d02d00820340c0801c1402480900d0700c6144284030002c0d21a00070f1082d20180c035010307070085044c50f03e12841030f1940b9901602c240c0a019545000c0d9841650811225200e55003603544141c98840c0c18191301d0a407100c6420004c4960808410800400d40c0000c0003815560092801e43e0304c0d2513454409000405640c1040104100b00daaa00c010720005400c0140a00d90140e4460307201e6405010803156402c0564264070070925480104025140510015400c1803000700b20529000010380035000d079a000a90440351581c03205d40c200701c42c44151150710111401400c005018130285101b15240e007042890b40d009040c0c1c0800c2e0001454031403207400404a00340700e2149582d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 257691456 1250 257690206 257690221
    0xf030309060610020607050904020d0216030f0f02121207090509090705100f1d0301020913050f010803070b011505040302060408010b04201e0d090f11091e040203070b03 74
    0x6041c11240c4034000e003910041c0034141c80c4001812845031060750740381400c1181c54804c10010754480d20781241000d4013070090ba07180024241c60382d001c440c4a40c6502514468031500a07200b1174800d0000300135034001c4040f403100c41c400081250300505140000091341d81e03607500191803400598002da600b2035803010801400c801c0018049003038480449104501c41c031001801c1303541070000340212001410440d04054050300c0072601c4400700c24003c00240c1080450400308000500c1d2440300440740317031102c0c00c0c01076090b4684091405041c205000d1803030f081594448042c8171006100b0f100340c08412070782c403d0b4500e1040082e64040d503030042c60345945a540761445406806070800c00d40c030071440d18135401c03220039008621a00b803207421542c080c14940075460524030761000a04801d0519020491480c42e050a8480c21048601c6a40b031b00d84250780750304014000070300300b8000600030140c40c0240411700c041c01d446403210b40c130110004001c03a655031020904200c0300d6800542068000710500140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 257692706 1250 257691456 257691463
    0x908030108250b0a121505040e01020f030c03130b04080a081f1a040302090f07020708030a1b0201020a051b010f1701030204050408041707170114180f030309 69
    0x1200e0301d401c11103200c01d04090000442030101100022038440040c02080200078500c05003420640500340100641c025462110580c2c100703003000520204607050500c50762605104c2c5007101011200210b0400050115030421444064030380702c800c12002c80003580f000404035048400c02e5204c041d1600700d08251901040c0384d0040000c4101044c00d0a0014484600c0200402c154410310841201e10074541403034a9008946411011030400f010400030001d83c640e00c1945d802894030000c004500d1503c018001c1c10100250002c01d02c1e90810810511030702d510100d140c2c14403030b55100e0010641050310040c1d240c0074800b10018100c0c010082408000745404000c1c000444081c2c803050b8500d81038500413a20f5205500c6014030a0b40c01030011b20250a296101382d030300c10301c1091f080385081e4445103449820303402180c0b2032180b5407104a0521000190212941d00010400001c5c091000c0e0302c6407804003001d00522800000303144880f909240102004050306200700394058030340e2424079620030703608c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 257693956 1250 257692706 257692709
    0x309210703050f07150207140105101701180c05010306120f12090e240a0506030a0f0617160f03020d0201030b1c060b180103050303010e150a08010b0a050307051c06060909080301 78
    0x40b0000045a02d041c0e410040c0503185c8034500100c4454bc03100d051941c0760074202c0103090400c3d0030350760342d04045022004804652103514050b4440340e0400d4036000004060b5030701600100340d5035820982c2000003c00356901e0010b800d512a042004040c1a000100c0d070102c055400303694402c44913000e026001010840c28210b98030b8400d40c0c0703441608006c2c18050403808a01ca51a0401002c00005512844590003088207041c200c8010071400e980e682c41181c1c2c070300311011040c030681103031642501e10074080510400420320951004041403841d000641c507903051500181c1810b84072090038102c0d9642c60501c0c03005201281d104031b090b5003d800d040d0002c181c0c0c1c2072164000d4900405040805146018150489a10000444c43c681c20b06400300355104002e00441400580f0415120440da1440740b07101c0988002400025118041030810070102190b900c038500940009000b413015031603c20711000964491080380751010700524056000f40b6041d40310070205480d08404808002c40c1d40001c60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 257695206 1250 257693956 257693963
    0x70e1f1b0f06050a0209030a0803040512030f340c0c050a0f090e031305011d0301050103140c0a08070b16060c0206041a1015050c010c03020309210703050f07150207 72
    0x443d602c4d00300c0d110481c86440b00b050b070306600860080b0001030202004552042c825402e03030390054403800407120310741c10035141c2000e0340c0c128008002441e50840702c0485200c100440c460500c1220a190600c0840d42d2180ca4081000c00d000d6a000d00400260407401410040c0041c2000d82d03031200c04c00003201c2e003401500b48407401c0c060074410b00c100c004252052003030101c405061881c98007005544205034940c070b070f00080c0c050062524055a0078803a00b4021402500e044801440304c41ca030714106820b4000d05842340901403000e0094950019001c010b031001d4240b04c1d607588446130b4000300c040041010040c16503081858415040750f011406a020390310034084005401030340b8071a074800b414101e032030702012041e5035810410001d9034456001c840c109410003600d4035100c05105821b480c85045a240825000824060320110400c0300b024540701ca080f0003440d0703c42a003209100c034811280301504010300410200f0030f040000c0d0841d09015400040003070101c20024144019401104095 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 257696456 1250 257695206 257695211
    0xe100b01030c05030618041401140a060b120c0c0f0a0f0c211101030b0909160603090b06130e0f0a031803030509010c08090d0506010509070e1f1b0f06 66
    0x201c4a2500803003e1300d00401c401007039600c000380c14070020680003500070410307104041500c80c1c0b809510820300c940112001d11100c91806442d00f10729050944200f94012070503d201003003001c45040c105403603d038002034402c22190750b5006a2103138a152083c007003201145802101c07074103c00c00c062400c2c40c4030380900c1030340604002c0f5075401c041c403050a480c860114903c2d91000141002450711344481071020814100041c202d03400002040030120201c1e00b00d603c941c0054100d10101080c0e18044004001d03e20301403206441641e180e03d00000080e110302e005e10089420340e14000c403644c010203040700041d030403540661413003041150f42d000c00800540200e400780484400814140c2c9180b4140c903010340311103241000700f000441c0d80d54032001068401240912489003d40d07945018a80d00c903001e040284440e50400007001150840504840705029031030680c1e0202d41c4070069214038181c400c4102c1040e2030503c0800361020fa49640c40198512400840e000070000080f684d250701c5405007504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 257697706 1250 257696456 257696471
    0x19111615050c0d1115180c030c0112180204090308070318030c02060a09030507120b1e0c07080705030406030603060b040515040b0312042709080306010c03030e100b0103 74
    0x10384181c8541100000142c108510904003d0b0003420701407207420030300c03040319558511110000f00016050303c12442c1d44420199103e00c00b9810480c1c000c16241c110301900303d442c120f0340041c02e40420350040d44296602d9003080e00c115550b400480c000d064010b031040c09807259900d0300422040c0d0880309400842d00d00300120541c03810b2150050481c40c0e2603155000c07900783c15003c01410b074001083d03440030810a114080000740c1c05204910040200003400030f030f004298034040010081c0140b5204c0304050700e04079001c4942100d040d89400100b40f03841e450360b401850420a11510a040014005200000b0001802a850f500102c11240624403c03c0008c12034400c000a4810a4a07460181d5120091000340c5280a0740000c20001004084450002010a2021494003e503000b9098481c2c28140d449a00748090200d05036130300c029100300800085a500c01e105400040c01d540c0c10004911901401c06d030107a0700c1001640f080b1422a01d1191801c0c80c840060910003051900013800c2441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 257698956 1250 257697706 257697749
    0x603030216030b0417090406030503090f040e031e0f040f050a0e0403090b030c040503060a09111906030c030e0a0f03090b040810090305120415140c191116 68
    0x260341082c0e0b43c1c00400a07800e070700c458460024008144a40131448038007004008080e50b210704c6841c00845c41100510b03220034200e001c11509650769403101303005505119094000d500b010044603215010340c001c003900c002e22940c07290340c80e001d040425413601e1000100400d45100c802440c0341141e40c111051104c0c4c03a100c0e40351100c611401c0d03800a02098043c0d1040c40640d5a0f9070145a000d05c85204560400d540c0310002072600c2400d851445000c2d58404042c000d0107650b420f91050201e0680300ba50042c42c19040c1d001d00550140324003c2010b5503501241c002500c240c101d07030110382d581c0d001c945e130404050a02d624107507242f07001200800c3e03581364001400c008103010340d030842d00c5d020064110394007691078140c0a040007100480400c0800c03c0f800b403d0b14121078480c1c0c0100c0c0100c49181840d805a030700c4104035880706150442140180302040512904401180e003001e00800100c194010014400d49022110304410f171007a003c0c2014001c0b01c00a090307118012900d4140582c20000c60303049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 257700206 1250 257698956 257698993
    0xd0c0207170708121206010f11011a03010b04180602030403030204050901031119050a06210507050c1b2b2f0405010b0f1315030c030b030105010b09040902010201020903030d06030302 80
    0x310345c0d140d9041d03000001d5910f40c060741c803850456155040c401e281005450b2058216280015503070340b145001c14841015003024032038103a00000550341086030481d00c2102901da02600000200303142d0300080000c0800d803107901a41c2c000c0c00d01500700340480d40c45c1d280c801821100c907401103001e100700b048821034012055881508465001e0001d2041e5820458102e49252002e182d2603041c059482101d0060b034250701c503162007001641e0380c60303407500d802c82c10b0039050a42440846c0c2ca101c3c01c107544180641e66541c0d0b503000d40c61000c0e080c0549a00540300382d5020620f03c45003d0202661601140d2550300300e46042424448609890b0546003420350401007258800e000c1d10220389400c3c440f50080968402c001c041103820f860070700c2c4005a4030f100c2c804c017000c442c49400b40002c1d1a440724540e043d41500520030312101c00c030002d0041d507040c410f05917464007912119038461038585100c02c0c190b9000b0350445030180c3c0081c0503641d58040c241d00d400094203107071108500500ca409103071402c0309460f5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 257701456 1250 257700206 257700217
    0x15030f26070b06190302221503060b030708070e0f0711010f0203060114031603090c090e0c0901080f100b010306080601030605060a060f0c060c140307020109060f09080d0c020717070812 81
    0x51a51060040d01c2c1310f47c5e5940300380c0385107407600d5581d0b0300d1010041040c00c6400c04010b5100704c0300803d69001000c00d0508040d6103610084540e4080c0304140140c100100300d00b40d204410031500e500399510385104582d0000580480c582e55440c0c601800711520894000b18400e00081e2078600480d400b1a00c5800c491004890a801c007074500400054082d104c0d070010120640103102007022035450300e0115044545840d03d020752607100c03000c810b200b403d06440550061103480c000d000780070099600c160300c030302a45091101c059501d242c81503403a8040e60107040070344000012103c0542c1c403407038240010a42940c4482c030405e4410800100c4030320078055460400020340d202202d14125646001c05403410000e21001e1181140088000214640c055407040301203034004076070b01e00140ad03d0003c032648030b20300180540c107004008001c100300c40100c45e000c44070300100140221008008038100241a0000d2020700c00c0c15015241403040056070605032440e0340103841c00021440d105044d40d110b05c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 257702706 1250 257701456 257701459
    0x10c030503040f0309080f030301080c010323060301110a0e040b1903080705240a0e0c10140c01051f050901060e10110607030603030315030f26070b06190302 69
    0x4000042c0000d0f0b00201d002a19803181c148905216180d480f001d0500544810300030340c1380c2c07000c4010080c0a84c1044000d0f0056020309040141c1d100e84032024540038460002044080141000300308941c80035803000c40005d03c0000c0054842c40704080040084900500b240d100d1401d181141c00c4d286850100c0e55000030f008481003103005d2a69407103454035000310380259414040ca2011403031080c0c03030b80003109003460036000c0d00c03000f40350000080b001c0300d2000c0f11038110341d40040e0380181035485000701d039480c02840341000607101448002e041d0044c03154a403203007c00d508040c180005e915644181900c94140010401004e0781c0b10000c0c040003038401d20a00000500c13188002d80c0a0500407600f0050390003501e480400c00c682201c00901d0024296400000203a07910403c00c1450350500c648442005210700031500c41d8a5519442c51140881c480904008416003a01d210a9049001d15810300c0d00031900316119211824040700020003200c41a00505850a41c41c60900b084010903040d01d50 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 257703956 1250 257702706 257702717
    0x11060606031e0903070605040303060e0a050903040519080a03020a12030b0a0302100507061410050103110901080702070305060718090203240301060306140411030a0b070c030905041514010c03 84
    0x140c110312010454001e0b000d0203c41c001041000c02243d140d01440340700314020b40700030031501c1c5002c00200010700300903c100c07550b03442c1c003092160504c8040112021650225204034039291441d5a1840304002903229544a00c103c81d054000c054004c95100a554040c000592588581d1501542680c400038815503002d42204018801071420441d1340c1004101403030000d0900134159a00d0040b901c20108031003074030030300714100b01c940304500c042e08015001c20711301481400c48001503a07005004d0141403905000345400040d0000b84200080001960484200e8481c0c1c00c0505001d802c08250749580e070f1004c00104000304130300c3e0060080340d000b10800500e01300984a4444941c208012142150382d03d9501c4500000100d14980580114111070103d101242d080503d0117850f200200400180a5000352201c42c001c01c501891aa51041e070b5030604894106c444d240480c0c00c1c0300c0b913030002903210b440c110258840d078469000b00b03030503162a04040541c11400000544042c04a503d00500050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 257705206 1250 257703956 257703991
    0x50315040512030a09061404060f0603200f0d0f0201030f0915090c051e090f04081602041d030c06010602030f0708090a030f0f150b0f040902030a02030d1106060603 72
    0x2002c0600440d03201211410000310801142c0d1503a080e00d40f07400c450481c1c2d41000c4240814400302d440703008a08410480200b11992a40d078440030070840030340000c690b0055a44c040c0280743c33582c4412541e0084001c00d258840480c600d00618400b9802c0800c2c0d00103031600b0381c40c080803030441c42126070382038201210324a00100070395001c010300740586040782c5040713004c0c0c40000d05803610354606440c410504400ba0039000c1880c28046000c0c0c0040c0049a00b02801c014000801c40300d004880c114100890340e060907811a0020070702a00e8280320041400140035000c40666101001500c210201c02040e01c00c0ca0342c2c2d40c8801c80e5039004511130203e01701d000700810800650b100f002000101000340c00d00342101ea8988404410a4043d0020307101c134000000b65100f0004200c0d000c550861944804202800c070900c08070707070060340301202c1701d020725035400c1c6080039981e04001a649031540182200c500140326040203200480e0046020740e43d11400b8082001403a0910035031703100d6104a442d803840031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 257706456 1250 257705206 257705233
    0x80d0507060e010b091617060901210f0303061d01030b06010f0e090709030c0806070203190e190504060e130b0402060c0105040b0f070c050a110a09150503150405 71
    0x2d10001001a40e250758503090213845889010721140721b0907000c80b0401031400c26000150a501354034010ba0204c2903900e00f00180c1c1d03030b18a410345041d25641100c010010a13000c2d6660512074003810003800c1d14003012200010107600d074110078180e50105610f0208003c801a481c0da0110080c00003c00070140240090501d501c00c46200c1807180343ca290400b081600900030030881002a5141400500706200c140240034194003004004c0c10010024009413400c0303840251203028000416a0040901c11904050f912902403080c9500004021242d64054020f1420b040800b500c540c0340642e08020000441d0700d0781030700140c401c000c207410f0302c550b03110640d0f0b503880d4034034009004030b0740000140300c1007000c0042407041a201c0e40c4640c4000c003032030030f00400780140d0620060545040200000d140c20000b000894140350496200d001000710040c81000203825031b005800492001e4501041c84100b241180000001c82d18180c0aa070101e1008045003030326084200d8001c0c06540c0301181c030501c2d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 257707706 1250 257706456 257706461
    0x1080405060f060a23030c01080c2a0f1006060201020703170702120712090f051810090216020a060c0503030c030a0f05010303020a050f07060e0607020d02091f080d050706 75
    0x11a800405002406071109017140c60300d120164840000c41c00c01c00070060900b0200304021000000b42002d5031a803401144886c0b40b80308609190300640e181c00840142c031400400e489880fa400d903001c1d0303480000f04817046681d40340060080400303035080040002d00c0900600c2103e4019030140d4860441c7c01c803401c000b1100f0900a00f82e48110b200d158484003554101c3e9000e8144103100e1102c6088110301460000e00f0480b158000b4448684e21040400541d036030f048420401020040c1d0008190359810707414408003005034040d400d03160000400b0380016500030042e8841d20b200700d60300031400d40c84482c00c950041540c600204954802c0000c40c8480410901859016600b41008618507003007100c59010303104284e10450248e88283c0180d010401d003800580c10103000d4800400d001860300380010555240c003103120740540c0c00003c0798015900d81560201900d074014028030b880e030510402140440600070b2940451001c0d0010114080c4d00100750041122501da84603414848141c4a4800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 257708956 1250 257707706 257707711
    0x30206070f1b051204060815180402010f030b06030702030408070816050603041e08070b13210507020a0b040816081002030c0d06150216240c050609010c0e01080405060f 74
    0x800380302d80320403c40506a96402170002e0080c40e9a074000506000d0044d408121108034124840c140d402d0780300900c81d100d82666548075409281c004000b58202000364001e00300d011350341d60851800820003840540010080c8125124182152100c1d5a0b920001b5110020409400b850700c202074010803162070070001031600540a070748514803840d25040800a442c514210494005401080c10f60900c10341026695000d007695200d903002c0100c0303913520403030f0144400401000c024186d00c0c40000c2841042994805940070701802c0d2120345a0000c03594542162051401601c5070030042c0c620719100044950444402c10000d0242c8010014001e02039000180b082c0c0d01038106000c00c030030f404002c6c060500102100c2c1d4009032801c0d04510003e05000440904030901e480c3c00c6010843c04056110302c040121680041d221042c0000d40304944003039030b0b60f401070007502c00d4505000d4144010b50086550490b0358407030000030b801000c010344641c80c2c211006006900f2460010f81c1120010300d1440c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 257710206 1250 257708956 257708963
    0x40b09100f060e01062d020708060901051f06020604032001090f020f06040305102a09050f0427060219080114061201030807051603080304030206070f1b 67
    0x2440c20300014500401c8a80041c5103610036a02d440381007107a50f4401c031885016207401d19091441541c184c4014440c41e80c401b0ba000d0134040e08059102986d0304c24003924010f8a0040c05840c09400c102c0c12481c0a84030a5844a004802e01c0d400d607081080000c01c04000c40d000c07a00030b0003850ba21924152030f4100e6401000840510259084401c984282304c0c200300f4900c20604040c4095580c010312480068500c8542c0c0214400c01041c0041140041c20681044202c040071800303004590b1034800903480703420144005030340700f00382030f0301d490b081101724080d070380c3c02e848820214000404000690300100d40080710300c1040c11110107134139140c0700421142ea0203210090302d170013012211250b1040c1013084020001d40303600f0046c4040f40400c03a080801a5080340da240c1801044101c1d0315056a040c0b10007004120b001a0305010000705101c101c180001c0400084961a030b40d00b001d0301c0300c0d401114100d0050003404001364081c1d00400c500302041c40300355100700700317041e0304500f10070844000e03132068 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 257711456 1250 257710206 257710213
    0x30b01021903030207121d1512240402030408070f0f080d060906090917130f030f14010c020c1003090b0108011e020f122706190e0303040b09 62
    0x30032094281240740ca03928031903540140d8915541c1400c950110351801740c1c10030002600d1405c0450400b640220b564280110784800e0b000e0456100c441c1e452061110001c0640c500d1420040151040b0b16180d1600070851145800080c0040c1000100d100495005141c40c41c1808181d002c00e824250b04d00c4039174800d58049000c420b03d41c580740c3c00c580008000303032002030301c500301031000803510b0040030700601d943c07081401829415540c030342030101c84113154401e4510203c0c03131860384d0b28213156550003400c080d28080e51281d00c0b070510649200b000d4200395180e101d48410321120a205118000c81d1003010b034003820304c00d1200010007800c2516030444c84d0406884810740700200fa0319405590007005240f00004003481c400303040060720b12106610810380b5105200054030701454104490001000c4d8021540e1907441741d6980020a21081034603008c2c01c0303452100c1072244030010704540551a05490603030214541114601030b22111180a066030300244040350008510034041600039403070708141c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 257712706 1250 257711456 257711473
    0x12060209040908130e1902030714040905010302040c05090f100201141e0c0a050307030b01050415080f01320f030a0302061b0301050303030414120d020c0106051f030b0102 75
    0x9040d601ea282003035a07410b200190340d100080051300040000c1c544071a00c0110307460100c40c4a40c1c2c10100003003028076250000005030f5a944250300300602c0e50402620303d91150707100c0305203000404090100b03e0141d4030b8103680071062400782e825940c0f861b0000b040d41e41001940014041403800c200b1140f02035640f1080c01120041508140d98415150f03254119064a01c01d0036460329004007500704bc412540800c40178003c1c83d03000e02240d92112540c03c010801404400040720036100fa0740c4440b0141c600b420054010a81c008101c5020318204540d03400c159895007002d00c07040015200c01410301c5c8941d0000c0c03002c0e000b0042880101c200003000103c07400c0301400802d040143d110412401a0410401c201d69a81c0445072107541c00c8240f032000f030441d0b0512002c03d9507031002800103080d48141f1200300c80700c1041004412150f44078010701e952212a04c0c030b014070103900007101e4444a03500b440408543ca0400e5003400e224464007000c03403048900320050503001449078800440c11806002d90 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 257713956 1250 257712706 257712709
    0x506040803130b0a170403021002180108010504150504090f0b100603140123030f0d0509030f010207020306040f0629030c0a050a09150f03050a05061e0112060209 71
    0x14100500e034010181d6030303aa00030305925650010942000c40203100502c0850074880d440211003080c01c1c018601e00d069030b111400d090341b4213110000e0301d000103400040c804a10009501168208003000e80702c0700000c0c0d03250700400080d0b40298015102e00306100d081040546059041004058007407900e200d40c1480580700c440610380110741003018000601402c20031107070b00d0310958240080b0341c5c01c440150f5040112510528240030b0300d000c0c8201080c1901003190340d00384170b180d085400314011100b040c409981d000d04144c200c8480140710f0b000e07030420750541c0720b418002c039440554000e02030085543c60307680301c00c580e400401d416600c03541d0314400400121109841100d01c0c4d214003541040010b4440205440e20341d1507001d584c0614001c000c10081034035128014019201a07035404104c0c5480a4810f2801d80b50980c84041800c420840003c18418007043c0c04458a0044ac1034407816034840000390841202480741d040703417500a00042001090360303481c3e60201d5200d104050300e012600e10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 257715206 1250 257713956 257713969
    0x142503020d020405270711072705010f1706040b060402070302120a0c150e060c0a030f11030a060608090a021c02031e0c01020a050a29070305040303060e0402030c01110705 75
    0x21071789181980051241c00c2801d920180a40c400c12924003050700b1058101a00c0d00e9812901c40e02c00003c040d045c5028503850202480b040701960b040c4208159a03440003520f50325101d034412160522414074180584007808103443c0d00c074a8002d8040200c60700d0302d0b01884002e61107107909038114092201e0341a4040d42e4040101982213242e51440c0a00a8a051403035044da00c0c0b08401d00e565103824007152000001103016540032400040d83e40e100c2400340c03c01e90140014210001800c0d19040740841e0800303110020f54040c00300d200081080742d071280d8080c1e62619055600070751503800500c5010041c0b41c03000c210304919140c0032881c017041071075034003181c038124404803410011244400080e04180c0104510b105600c0c0c244014140c0300c5650301c03230586410260308003400c45030380803402a010101c02c2052141c142125040594030f072800c0d0310010000c0100356011000603041180014903120402d15450040da0020050110b522001c0019503c0e0b0817241d0002007207004801c0002540e070b0707414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 257716456 1250 257715206 257715229
    0x721080c010b040c050705060a1505180420033d1a060301060c0b06120a03050a080a050714130503370b01120305070b0a142503020d020405 61
    0x14001050415400d403c10041e240300245042c204030042c0024400700c2c10001c0c4642d0041d00031034000a031000000c4004103a085d8640002d5045002c640c0c0c00b0a4441c407410081e8816030280e1a001410701c41e42000c0206042c02c0d40d03489034181c0c4070400341e00c1051100207003840500e042800ea00d01c0344069040c010344503828140360340b01081d80c0300178100064402e00349a500d0124101d40036451903041c0180034141d803012a002407d4140c0d0a4001211902e5121b2443c011a0309a001c0307500600c034615000780903a0000d8080400a04d90001040d1508a1806900c0c00340d26030741c4a41039040800e5503220074030742119449090341c080071a00016540c40030f0144284030540000d9104a400451003c02d07021030340d03000710000d83c01c101e520860200b118071807003d0540c6c0070000e900d1030700c20480c10203e880340503034031010340081f03c4e40060010b4400507602080780b95002d41c54132101c0307650f16200300001c2500036001c01d001070f04114100282600c44d03030080010000c0044014107040d1914040740303810001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 257717706 1250 257716456 257716477
    0xf0a0e1905030c010c05060c0d0f0e07031e020913111206060a06110d140418050a0e0a02030a03032d060e060306010f180b040e10060b0c072108 63
    0x18030005004605051040c100410401e00b05000507024075079880b50788000040c41901c0d6003901007040003c41300250042d200c610314203c400e02005403201e13981078a449091108a800e100500c041840040d0981611209140c00514100036a9103004d4201c8003100028400c640f41c0801c001c3c030080654511034000f446c000343c200140320700d00d003084c280800c440c00343d0069001c0c05484040c47c0750001d400901c4007214ce040b403500b8400060040100f00280c095500000f0b10f040e407d81c443c0110444580c0903d1003814400001e10004144203a07183e225a17610401a416070070030740e80080440d02942200f01400069a1543c6e03002d0503203400b1040100d91054110301081d200c11042100c00d000c0e1181c203070030440441c05007485514102c8080200fa0492142c0e02d80006021031850495455070b10840c100780d0042c2040c06100b14482041d03848550a2200c003d0462402601050541d0303402e082e900307000008002062500d080c000b02110000d0110501d0b142d40701b1140d803d000060440024114a410b0f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 257718956 1250 257717706 257717749
    0x12060c0c050d111605090c07060207080a020f0d0c0320030408030a03090203061f032904060b040f06051509040905010c051e190e04060f14030c04110f0a0e 68
    0x7803215804e001c1c0c4061040d00f0344c42c50784424411580d555220541110320480c0d034a03920700d07541c42c245010b070040c0c02d00136113441d0021421406898011907890700d41071350301007070b20340070507107114140c4045040010141c001090324107698420801d140c0c800b1010300000c0b007200c2c2000da07900255491a40403986540002e81c481c0406400c40c2810454941c008850720945440e00420704802d900d8080070b03200107450750002038540c21701b040803019110085d8040c00d40c15240c0b458079007410320290800c142582e00991170301e033764030b0407a0031148520015224010030740003200040180c0000a50084132109034004e0380c2e202c1c5000003603800d2190040c186030302c0d1101ca0b16204a20381c0c4020f081222003040700c14801c01c0050b800c403c40100180c035600c081d03600340480319800c00000700d001003461380c0194084860841c0c0200b0ba4030b0404041180ca15800c5048031800c04400c4180800c0c0c9045201c40054004244100103035100100d02411540b105c1e403034080246a50503002555400740c1083d909400340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 257720206 1250 257718956 257718977
    0x1080102090906042f041d06100206060918010608010c080910020304080d020304050c030709061e05030d0e0114070c0e0f0f0f0714040815090712060c0c050d 69
    0xb418288540d105000729001c0125846520462041014008145444941038400c60b600c1c514145c040c0c402030981c10103074211140301241400202c0000f40d803108d1148065803075000d041480002c6081c4a018054482da07040c2e02c6207508881c003004003003e0798541d9525008007003280c110900c158a07041e107003590389001d203003030014030181007900141c840760303203640104204004540d07054100d682d4030000700c40060747c950306d84c01e0880c10410350181c0d050741402000c01c0014002c0d03060b0130001c141c82295461250059071481d0280c0c4601d0944030301034240d00404030300d041241c000c0901d00c40c0e904042c1040b1034402014501210a40d0001318102d5407810b2048050200e9510f5050480c0e00c50f100304801d00750350621510f848002000140807140b42a585070001c0c02c1e032071166044040d0559502c01c2c013501e598880e42501c0d00d030660350b4811060701409600295905000041c0300045034280f40380600000d8064682d000600829844030301849900e91240000900421440007042610780d100c004c000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 257721456 1250 257720206 257720209
    0x121811241e07240b0301020703020f070504060e182b02060606030705031305030913020318030405010807110309060c030703031d07050409020d0b1303080109110315030c03060108010209 81
    0x102000c8040707166a82442044001030403808680c18254083e08007808200e84001c1200150035900c100340d0b015400418400200350300000c03040c12a2072000142e4041c20b44880038001118480e2040801104460012488202c4810041035295800400f551b403024811345141004640109848000c2d08003540d50300640d42e0f0503c4425000801255035a02e9824900700080040c080500510399400344000b100b010014104204c80340490003410820195600c18030381c4000350411244500300c0f076001c40c0c0310020143c02000f100c0503100161183c0c08191680c00301221450302d4050340403000e200400070031645544010181500c0100b02000f540d6900315803800030255540c40142c07035160190441402d0030100041800415a50107a40c001801001400001c03010503030802d0140c00c0c80b0158050140c91403410926410060107910707a00803d03666010104c04641c02110384880328102071012540c0503050601e0303802a004000c00300e84c1c0f140900300000f800d11000ba4400b84e10742c0c0d4001081c43c902e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 257722706 1250 257721456 257721487
    0x309190302061603110304031d1c02030c030c031e251503060b09040e070b0310061707050d05060612010b0c0d030e0a0204020723010203010612181124 66
    0x1203881e0f40c42e0610420001100211031400047c00040511481d0b01e4a00119100d4051031f1900b800000c003600b504c2c1d000c40824228000703810030140d000e8000c22000342600e04000607a181c6945014000304507104000c1c45a0350025078804520740103000d0401100540d4861900d81c51415005d10b2031210130900e0811003010a0080c0d074401c00900d03003030003410413449040034181e50b402d0009a40204032203030742b191082c2c20800550400c0350340031000b01c24400030400384a011402d4030940c3c4c540c2c41c0d81c03100c004000c52101c1811140c80001540411840c2102442c9400441e0008009006242414141e40044020b44400d0b00151129000410460401c440c20000000d502d101824204000c0f9207024440352a2503598030060b001d07039000240e4200704101e03800000502500300390f5400048403000c404034040c1d07000784540c0c03000681c1030032460164845849111200855080344100c04120342d507070203040302d1091156540c00020301519003102c00824004032a640310b4843c0366980c95213610100c844 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 257723956 1250 257722706 257722741
    0xc02010b0310090212010c031d0604210e0409050f0610121518050c01031a0a140102030705070e010612050105100f02160608010e101d0903091203090a150c02010302030919030206 78
    0x9c0c9030701400501c000700b0504041f0440386203810304405284800c42c041500c4080941c415550840e15104940c81400004284841c003c074400069405540f2008948500140c15019400c1744041114244000803d0815071962003001d03034038080b50100408682040116514034103a5080c0c005812541c1c40b5a4548a103e0305480c085401364040c485c1d20011403001102c5000c0c0410240300991140060ba001b08140d03041607912000721088103440b8000f40c01e15860a108640114060540429403200720340203250584402400411011801ca074084800c1c008489404096020b1000e103c0f040407500d0052001618064a070b9550551611a04003510303800202200c0604000d4202484a142e40c00003c405086261b5840101c503103890401300c2c1144107501502e580844001c414480054021024020b004011550115001d58841c1103550f142c0003020b0103000107030000792810043d030080d4041c641040780c0c4011070315000c1c4c00c00c035509403502020906402580c814010060b034000321410504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 257725206 1250 257723956 257724011
    0x711090901021e0705070f1d01060206071403100509180c0402070b061005040b180906030a030f03020703030b0d051f0b0120010f060b0309010c02010b0310090212010c03 74
    0x185043c8010280310381151014003003c2ea10b40000604009000c010024031001e081143c00588196686138150b828086444020b49041c80308000000380d100d0000c00c80510480c940d4540c4615180007800303230712044c0d100410b55820b00f07040242c003180b56283c0d000c10600c02c0b0380d50403280090110300d0054a24040004100c18452401084a500052100c0c1651034110302c00b91101040700e44198810346850085410604041c0ca001c41c2d0320313000503420484d00004280c00c0e2690284d9868403400d05848101021010740899a480a080021840307540104102e030b020745800182003400c03100040001c0181281940d086e80411070310040140700005251899240c0c5904020944580c00042c203080041c000c1514460840c43c0d04142a0a081d00716140c0c0c44940d420030409151030701650b03401c68006036191103096180c040510750080c014407400007000b000400030074214044400b000050310502c2400c0348c001960300b015510880090107001c02a151584010825102d8003070f40080c2101c420010341c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 257726456 1250 257725206 257725211
    0x7021f0e07091109040e030c010c0804120206040f030e01051e040305061f03020103050613050405010515060a1d180c21010b120702070807030807023a0c05060711090901 74
    0x83d1030825024044a0310101d0075100482c0442d190b45d5070500f1401011140c00595081c04841c15060341c7c4504164401e034400e1514460300004503800726034a800840d030003051051600c042d080031900803030342d40384041014901546071a5421408040c1c044c40c000710040c4402c40030400b402000030500905034040020008800480c6d200c1400381c0d8003142a200280c103050351000800c1145d101c5a080120b003282c2042c1c248628201450074a001b8101140c1d40e50700250414210501460024129034a0909a9030740301056907204034030034081c0749000e031030a0340039122902e9440803c00700b9480d240701e400c42841440d02d5080034020381e40958986a0b051541042c2c90005201000d02c2205558001d080c1c4241c4084990325014140d05d09030258002e007a442c0314502e000000c0250b602c1c010030206100703030307058010081348480c6520549801c00d0b44800c07006003124003d03101644480d40005140c081c80c0941d41a9948402084007680301e181d050703038050036803c05c55210f0309045100940107200035008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 257727706 1250 257726456 257726471
    0x1203051303080a0204051e2803020f030a0c0315050106020309150a09051c0201020f030c0c0105130b031302180412030f020415020f06010f1d07021f0e0709 68
    0x15018039403110002024440a01c02151100580340d050380e001e00805014400c201c100300300320005070501c403010144681542d6803401e80141050540445140e07a400c0380080640c116400c02c1050000500c24580500c61013401c00d01103181000c0c8040254001c1640c18402400c043c0072a06858050b000403003994001c000c110380e240c45502d41c2d600c0003038000ea0101c0d1612181c060485200c0b2540e40015400501040540d50200b083c9884541c4c0314402d03000c407501c51401c203043c261240500c44207440203401c401290080c0354082d1004003499200480e8103034402e0b440c2d6114140355001920f141030701070310105001045040280c59010a11407080c0742a651b482c01c3c3da01e190001c40d00b1100780c0201358413112715007004421074040e50017034800010aa001502100320003546c90140141c144864030901c0000520b503011219400140c0e600103100720349181f1411964500240041d20a001718400c455402010351034140e44403440706c6090001240000c01180d16500c0e03c20304d40c002c440e00380d1500340c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 257728956 1250 257727706 257727721
    0x705060c0a050702030a0602030603011a030601050d14011a011704050c1c0b040b0604112d04081c02070f0506190306050a0b03041b061b0c17030403120305 68
    0x406a500a20598016640c1c84900c01c040350b85016160b0020340610840e0146402c00580c4e4010314400d013800d6000308690180f444000c5c00f07460050701c0c01034040d040000180b0031803c0441000d810039000d2400f07803601c402480101400c403440700a050b480140301e10301342e82180d80c0c4038100303000700306040403004010700349502d03940d0315050711810461050052a140903010f0322006511050340b60404810001031031700c2d04001d08003d0b0100e5805210740d01d030211887c01210ba232801d460b00c454090300000b917814408108000101c61100342c910360080d0a02c00080d5051040044489811000c00c669154070a0030101030f14203080754001d007024600c4014207000e2a1a0304042e98801c181c2d034104010980e0380032303505600a00d5141c01035900681041c10105001c92448001c5001d244100ba400410185151960500c4545d6001c0d0070002104401c1c492250310030040741d195010301400041c2002655107000c0c5150020400410005807c046406c000b840100c03031010350f031400c55040a0010380313840b02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 257730206 1250 257728956 257728963
    0x411060a080f06010e0301020408030c28030c060213150e100e010503250507030f180b07151a01080105040605060316051603030e06150f12011811030d050705 69
    0x181140741200c0002c0000d42c2d1a8800e000702c128907a0041c2c02190f076240c980604c2034881e444a188100790b0310901034880301502070415914140c14129000c841210091307a81100d070029506c000b5201c40b5002d00c068041d0849000340031000344914482c0840b084418203000d4010341260b081581301d10b00c1031154124141e041540d10030341f08404d1138460790360b82d1178130040c100754820308d0303141f00d0141103103600320b0314180d00940181651350203074840c0c6800c074171000021a1090040e0071201d0b83c02c00049002c00411110402400456204081102408002e40c400204444c6030b0344106580c059040c0c990705203941c10441e054007414040d101440400e040c10045061880060410811070302c0c61000446d2551281e016139107074042144400304050300904000b805429071b01444140f6000d0b041c0400c2c0144261182e6070030012020b4042d0160300171b001d00304101076440d01903c1d0210754031400a4034030940300240c4143d03201c3c03155070100102d0141d1414145000d5600b074401c4103201041007154003042c1c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 257731456 1250 257730206 257730211
    0x20108100803091c051009210e10030e0a0302070f0b03010e0f0402030a120905040501060807140d060b0d0501090c050705030306090601110604030c0b160c080a05040e09060411060a08 80
    0x56130520700051514142070784601301800090a02c0c0242001a603030f141803908a80c4d4140e0081031002d58a42d12690703045400d20808100d14040769548500000c0c0d401d201106946042d02420009220785500b01c08a0500014080480c01a04036031310602c03040d1500c0c1411005031201400442c155810100d104100410140180721a0030400c1c00003011035804110a249190340b21740300103030004c2c50247c00b5114001030700a552003142864004564a84140342c010b20079000b56881d0b2088542c01d401c041660b50200510600b526200c040104808072003400800841c2c09400d030000b04c940c5401d42e81c00c110395416450340104002048001d0109000205072500900c044404c1030130b941b034010041c2e5940c0401102d01805010b81010002403540101c0400201c0f4012518000d00340d58104a03510a1030104500c100410a125201004180d030b040107400c5029007401d1803860162941e480002c041c40440d0075000e07680c4108208001c2004001e160820844265a400d0411070010400750215200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 257732706 1250 257731456 257731459
    0x6190608062a0d0203091002030f0610180b1317060708100f0b0c070602070b220f1509080109170c01090204050c04060212040602060f1f1202010810080309 68
    0x1003400c03112050680c020b0140080300c404031440d503c42a039603142c400b03900222070b00306403805036406101801215008507807140d80e106108a0349955950100322003455500911010030046019000c654089035007400041c1424a510540300c3c0d90801c10051142200e41180c0034a44591540c070f440100005151900408241440c0e10a139941c4030030b000d20304900d070b4003207410b10079410000500640003800a20710b0307121500c03da4000d03075240c10042e030b5600b0503407181c4121110100031450580440040c40c8078280480d9000c0124079580310b412000040003600260030180160b1218850307650003035003907030003020808024801d6a049807030b50b5108044003003d14090b464005940c20800d0000c3d806400d02c194020800c200d241806140b01d006504280140701c094415030a9065103607500900b624201c0b03800398002c21290769010200c665148000c2c0c8440400c0d0301b40b050b002c0441c80c2c8001400060101c4100c103600001c030500006101c1030300030f0b1840c06030fa481c24a00303224001c0c001c03044540a120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 257733812 1106 257732706 257732731
    0x1060804060b0f0f0f0301090203061e0a06050a06120f1a030d03020c101d071d0a0209010f050915030a02040302010e2e0908030703020619060806 64
    0x2c2c2c42c102198458407090b0300c135001d40340c1806101e2021001800100c1c99000b07903808640792520030740b4854600581c40d6490b030460400007136400e52100c040b040a1010900c0c102c00315503400385600402c8200041c5c84c3c14140d10880c0368216a4480407041700800045194a98402c0010f0402104621030701031810f155001078400c1c005d5400c490400c1c0e018080c452002c6844200414203003541001c0d01907015460360240304240701d60801803a20750714162040742c8582c0c86000841005200400c45403040c40b0720420b590b4071031600010f40441d400c00582d10303000580000d20b0075000007402c5200500c0001040b00d00040b68004d4021030f4801c0e00c801c0014124001007140c0d00d43c503c1b0b078442c1000110060114112501e0310482c03503101f45820301c000e0344c030740ba054440e04580c01a5400e5001d0ba00060030321442164004000400008082040210070b040c00c031082d41741c08015001d15020301 = true := by decide +kernel

theorem cover : BRFrame.Cov 257553956 257733812 := by
  have h0 := BRFrame.cov_init 257553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 257553956 ≤ n) (h2 : n < 257733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
