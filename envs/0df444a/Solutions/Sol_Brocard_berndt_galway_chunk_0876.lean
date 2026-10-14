-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0876
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:20:59.988346+00:00
-- url     : https://prove2.me/submissions/6fecd45c-d8fa-4c8c-bb06-3438d5a32452

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 157374100 ≤ n < 157553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 157375350 1250 157374100 157374103
    0x80703080c0c060c1e09220603050601080f0114040b010608130501020a0305010513090209010e100305060408130e0118050a060503100902030706020c0d140109020d0f11060406050a11 80
    0x40e10100b0030302c02c0b1003c030314182e199110290000b80800b1490005000b0704005641d0103400c2e2600c40300050001d180c15440c000c3c1c0035003155005180c0d080941c3ea543d5022010540c10310540e4064103040c802014850380b2100c40908460780710751310f400019001400d000000b00c01d2881c80703044452518101714140c6074003085001800b40d00d00000c1c002d42c0b0001d01400c2064150300824100d402c00ca911080d085e0040c11050242c6100c190300a43c80450140180001a4000e02154002030302c0221b11000b140c603607988a01c2d01c02c05507419110030b01701160702410003a48800c90740c080c0400780d100b0b4000754036040b403954014000403902c4a400d0303191000030b144160198810f50082200070100d0b1104802003803104000c0000007001e9010303005400c0003095182c00020480c260070405017225802549039140c0320850044411100c00a540b20381d090009a9070366400b6143e0140120720070526034900b4034290304140100d0700c1e024052501440108009608482909e01001150500005410b904d040d02d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 157376600 1250 157375350 157375357
    0x1211030f030a0c0806010f02030d020c030d020301030503030a0b061207030902131d0111030f01032003070306020d140103110f0a050901081c090302060a0c030512010312020c010507080703080c 84
    0x4811404002c000c01d50360140c200980c283c143e911074032020b8030b9200044070b0781d034800c43e504009030f4020442d40c101c4464540c0204549a40101070364180f0035030f0742c400000d9920a03031080c1c4840d03001100384031040c02ca40c840c4850071681140c002d4500061085007140002004015200f4550380c2d102d9501503440309400c00740c000420b880308000c0840c60358049410340d034101480710420340c80c11208062400440d000c503030245078070200302000f6030318581d0f615070640c1000c1d224a10900c00c042a40c1180d44040103224013031171188002685985d1130b103000c40101c4510b14103540103421030400400102d4031502d04401031100640c0c100e8000c00c00000450b9000301c2e01d500003600807003804000101d13003a005c10711841600c0022090b194290182a04072800c0080d804080d5000d501008014a5580601c403060354140c0f00e03003400b9041c2510840f0b100d40c0709001b6882960201c410f5120301c0da42c65414001454491402d0801c182030a2142d00d41d51418000d4082c0101803002500c08124100070a00c144c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 157377850 1250 157376600 157376617
    0x901030906090b15030c0a05090405160905220201120209060c03070f05010b1806041508010207060608060c0a080f040c0e1801110a1d06091801080712121103 69
    0x501c441c0e22030303150401c804070003141e40f448000d42408061070b0301d14011a41b02d450402c01801030018506003c10800e006001a1089500e0f04c40c1d101000c1000e58114941c400400b44000d00042c41d00c3e0032090b45e886400c501c003008014490544510300184e8110300200101f5600c0200180c583c103040001c5031092080142c0e900d450f101c0400c0b03100c2013103012259280c0300d41c483c500074450302036040c0500c03075035140c10804001c2d0000c407036000400500f800d078080c110351041c0210401285544902c03050890380310900aa8640340c9460f002d0000c9c5400f00900f036005000800c1d00c62502560040c003c00061024007180350075010000410203101c505852007014200b40031a5882c2818030031400d03417210f1a589020000c1f5401c01041031041401c040903140032403151f0b110b0301c80752146c02205001040400300e1240d4020020700034060710b030715040c02c5020760780c0d0000d80340e0206505040e0304601e0320003140c0c007030420107031112128000242080c003051840e41141c100503440501c075102990a40c0588441c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 157379100 1250 157377850 157377863
    0x5151618050a080705040b060403020d0f0203011808030f0f130213140c0309010f0605090f060a0305030307020f010b0a080d05030405030d0f06060807080f0115020a02030d03050610030c0207090209010309 89
    0x80070a94003c00b14181089910131141007082088400602045004502c00a50b201d00c00503401000318030f42d1000802da4510040001801c00100500c2c151000c408003000d4504c0c04001c0100f01880b42401c035200d82140785548a2205031505010792003e810750300f2002030060b40b5400040e076040400b0303040350710a400d070800d4481c0c1510340800f24150701d42040b1892401036003403120340c609010329071068200350307000941102125502d40185c46c02d400b2000d09401c3c0c00ca2060000080440c501748007460040700e10780c0c09861414102c002050a49411441452040c1610142002040f00001e403d00040800b030601c652079903924107060b421800348903a25400c0c28100806802440000e47c080000d40d210341d1a60111038a070703030200301c0320000c0854540920704104401406014804200c00e800442e280c4115079034a811540864108000750200d400825220300c02c1c003500e440d140e040081440041c0c5403c0140c1c4c0c102070030003952420b035886114000c0f0ba00140c855100d0341300781c00244142d0b80000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 157380350 1250 157379100 157379119
    0x140106180f060201050402031b210f0604030807020c030c181b0307030902040641040e01021e0703021b01030b031c031104030b01152001090515161805 66
    0x80b019000c1e01c000c4504920a0040c0c91060b00c00030904120320300d03038040c042c0040fa8810140340400440345041910105507114580148101080030000c05100e68841d9444450604200101a16089020028510903000031301481740079143c00607000e0b500d0808986600840e04c0e0245610344540030644110350000000040110898142c0c2080c40210701c281d500300b0a031951000340c400c4c0020200580c807144d00e4032100840300c0c0e44030060940a482a001c404015400c0d030400001c0c2110204182081d090750046441c002007603002e400b02c0c12650b030b80a189490700756141d80c0252115511f101721076003070462081c0c024241c0d20a90011104490150480703901381c0c4100e9050f05128203e00d04140001c0c1003149810f010315a001c1170b101120751000346400710380d080c48030351072540780d1584140040120316841b045d203807803550701c0344080d40340094000100c1e00c250307060140c1002c04101c0703a440b02c0c0100b00144001c2d4098a00e031003038042160f240c4141201c01035a5400c0390800558041caa00c0b100c0725 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 157381600 1250 157380350 157380359
    0x60409020a08070608010605030f070f02030405030114040606170a030c170a0201092001020c0d080f031608012309040201020c04060801020a110109030c17040e040303020301060f0201140106180f 85
    0x43d11006481032a29101c05581e80c0c2c3c20101c030103110455031a1003800d100404515010701883c0101c0d420401401540d040c130f0340315004282101d6500060900002c04082400f0601000b0710031304002e000e00030b031100301c0c8103002c491a5603a0101c04c40010204110382d030520302070080b40d948030740c00040144905941c0c0c50500b40300034040c0400d20f00503200300684441298408242105d500040c03003061f005030100502403810005000d40b0b40b01d040d103514508200140451710490021407256030940101d5250b0703128240000c0403c441608a6150320b56a21000081d181c0071044c09000070f002150f00750354590311440100d06000c4442080740d007003400e000300407404810640103450b0040007569454100c0f220514268262440040085d012604114540003c107420003103030064120140c0400740350555421202001da40219002d0740061b60101c0140b05423a07000c00380080160703c500c002d1203a19030300c901c617245090f01885244240b00300c100001102e0030441c0740500040200c51000350409030b99 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 157382850 1250 157381600 157381603
    0x3010c052a0a061e0c090501030c0201060503070807061706061204050c1f030b09160f051905070b010605070b150f090f042307050120010c0c0201030b0609060d05060409020a08 77
    0xc2c64124a034405281d24200d1440100d4411030b914012950b89001c5221710304001035000b492b607007a680b821035480c7d94000c10692400c106120060502500400d01c0501c3c1180c01015945a461081079041441003400180c0e03450030140d0300104948446c100c0c007500c481c5409440c0606000035190070025200301040342ca0502d4005400c0025607840a004214000040140703801c0708451841d84500422401140ca0388160035100e60004681440c9107445601800e49100340c54421000340052400610903081040c001600740c014045800d10340d01340a215030b10403443c0d031002070548144002c1e41240c01c5403a9155005200c90100182070b200c2203081115040c00d450604550640d5103031000e00c44003203019401c0c03125600d91040c550250070060304000c01103e00350120552485085840c00c1100a140401e01c500a0100d4140c1c503408000d550364400581541c5040c40341c18458402406032008a07100d03042125014800c118000615036034941c00100100041c241c0031390080124000410304040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 157384100 1250 157382850 157382861
    0xf05040905040308150402070506130606120602070302010f020c03070201030c050d090507050f01020a0201080a0c091a030f0a0605010c0605180f0d080c030615030a0f05070e040b03010c052a0a06 85
    0x10741c5288000d00c0c100d41006c0c482640300e0154000c10304d034098030001d2540e20800201604103031040704089070a9a40e2240f0186846481c5c0040d100c042c5d00044140425409208104c1255605e001c00c0d030604403410455a102e010380c00001c1e0525448400d816140d134820f10407a21100d0340080104142401c41c00d002e503440e1030a0082c1402450f54036010511503000151022a540d4140c1d83d1912035682d000041014010a52101040c040036a07801300700080144c2c000d204a1003c107016130348a20700046040e03105900034121300c40d8149000c40c00d00c4203981c440340400596030450340200d41c1380c6541416040c002d072400e0a615280c080c504109040310001308000440301c8056944035525201c04103000150310055640342d03449250b40d121448207120a030b01543c0e0103502c6600c00500308000500340815908201c2e01e242c00105800c1c1045654a4135110f80038418405800030040300c450480080c05901c05c0e01d035030500e00b0014800c284002d814103031031403281c2c0b61102d00b5503444052902e0003001910 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 157385350 1250 157384100 157384111
    0x90503010b062817072c0a06030c0203070c170d0302030c070f11030a030305070912110603130c062a0209010e072007030b010e01080705010f05040905040308 69
    0x14202540003407a07190410a880700c0e211400c181296140d007400030501015080c420000c107001e0050142c25000b800401c48074411101a11041e42e0102e45c0500142404c015801050146024107581c81403922031540e5601560038a050000c0d40c042c044000341e1450159000050001020010115401800402c038030003208510044503411164a8000d50690004403038001e10303100c00780302890228012981030061b85001c0c04011901d6a840303401310342000820402507000c6a01e44040c0003c041d03011b05400010304502508004050707044d03a5804805021f088000d11070131021011480030f4940070b003200b500e070398000c4c0c002c40075035558540548144039200b82a8000035107081c6016036141049900a01180d0082000620ba0300301785003481100000b62520003042110290340c0b140c00c0e03540072090700180c4488018045c80b451864902803550050304116000e4088000402140c0c1b8001103ca090380c3d4242001405d202c1000780c216258007030399025034082030070101440280350704845100d0245 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 157386600 1250 157385350 157385353
    0x309030d0501060c0503070209070e04021b0f01092a050604060207090b06070b0403140c0a0804051f020d050f070b01090903110111070320010903050d060e0c030a0e010f0606090503 79
    0x242c3e0788000581d01d4071444000039119410400c030b00340051500324503291384403910b0700300844c42a01d0000807500300d811510780b02200c4d00554604c42c240540c1001003004546600d0000d014100340e980d510101050350001000d10341c139141440d91001c0181c181044064400a040c0c0d903121591038000039501c104620844001c60318042220205085c42e10484894039004412130000b80c49950341101c0d0060001850800c3d9034081c03020120008084c041c2c1d81d81c1d40d000e0070400da01c85040c80700300b0030783c040700803030250441e00c940b6480d144254003c9862090301d070003401c0040d20b584242c50101e0fa1445044801400c0d450310300004035121050741e203d103000500903580d0060810602c5400c908039807050b529003803089824040000041e111b08882c02c0740f103841040c40e030480307403500c0045420b55100d45000ca021074008154011451014403a0300c1c010141980044154103000c00340010702d110103407400100b1500c60324203c0e9494002d4001d0082102d009600300042d694071400202004030714040c00e80b00707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 157387850 1250 157386600 157386611
    0x302030d050a2d051602041b0201150302100518100305070206060102120f0d0f060e0f0a050705040e0402030307020901080f070f0b03010501030c11030301090b040606030c140d0b03030309030d 84
    0x101100c0000f0400758402d000c40c28083c1c0e20245056030181c1040030350b08207210124881e0001a203d90142000204180207200790441e08118041e01303403000101003101c0307150100f5080016a41c1c010819a46c5a2181007036966891440b41020051410010b5103400442d04092440705507415130041b489038001d9800c2c2d868a4642d50012a1030f0f4983c5040709442c150148544c0700704281d08001400004400b00001a02514000e075035025190300760301134602c03c101c003020003200b036000341500b9030300003440981089a0300d00984054030900644c081c142d01c00d030240000900f10b4034204111000742e0b40003004003242d580d40d03400343e42e9503c00c00e0500503658014082c001422000540740502601c0d039544259041d82c0c03c01004500400050304020100705003030054401c90f0a0a000440c00b8045e00c0c000410020318000c00c1c40700b07840903035120300704052801c180c00c0903607580b00d00028005d5100c0d2007101c1d903c0b010100080050541007427640c0e81404004240302041768000010400c02034099400c0c400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 157389100 1250 157387850 157387877
    0x100207150b010e0a0e0601121506030e0f1506040b130f0b04020711060f190804030932060d021c060806040201080714120403050a02061609050f06040302030d050a 71
    0x1154000c103c0225040194800103001e0345098202e02680400c040c94005003401000000e0000c0ea2080b412103802040d100c00140a035580c0341c09190400007030100200040060019400d956103a4940540a0b0300000004206141e40c5c1d03803c46507442c50010310500d1360107010781100f8010710030240e413810405d243c68460182403c043c0280c661441c2c00901c03407003040d015001441026801001c444103036200400c075546000d00401e041d40d034a01015030301d540c524030342898064100a00c5402c060404041044840700742c4c101d407801d4001142c1c40f0700c2c098000384001d20124026003c0d070052080101e001140c00e1081240b034001e903500c13498881d80d0901c2415074800500d03440701000c2d58041c0c0003070665000146154007c102c1e11010480d114041440c1405e000c03a4062900d405030b80c1280003c100040d10528650304000d0581c1090b030440c3e50780078030b031944000600b1318002441071a02508803885e400c4042d549800944004580140175a452500700042c0184030703038410440340c004649400140c41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 157390350 1250 157389100 157389107
    0x40602030a02060708090d050309010b040c1706010504030c050607060b06180f0406030201050f0c0a0b070c0b07020601230d0206070b1812070f050a140105011701050621100207150b01 80
    0x303000e40700c4c2801420800414040840d0755504c000c00342c0c0455920cc1c654085241c480e40324044151500759034285a0306419000f29200382c10241c016810040d050109002103880c07242550b0841c0c20848401e6511400c901e03080001d4001d1503407140c3e10860118501090321301c010202e600481d012200d47c12000c1a00d03003040100e94807070001030700041d81800189000780c0010020003186401c2011980e81e4000c0341d8692110303050446d9100e000540040c1003000f000844180680c00040c04d0028190b590305005180e0701201c0c00000ca8147d02200c98648001e6454034003410101d9600075020030b0340e4500030b06043c0e000c800305603910008000320315010b03000749502003202c4074102d002d480614602207254071118460440c2400954aa00440703211500107210503202c24140780a0400100c3c2c907602d040f00d2420101480340d503a0b4040e034100741c200030095030385c0d005014101d192108994214245046071510f06604644100c240e148000f560340184508120342c0358030b000b0031070b100303010000f80306c001107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 157391600 1250 157390350 157390367
    0x1518070f0f05150909070c060c02031801020d0c020105030c0c07090b010e1009090b0f0d050c030d0f02030409110c0609070f0501090b0d091e0c0503010c080108060103080a020a08040602030a020607 86
    0x10040030400c0c004e0450510780034640c05c0d000286450070183c00c01145e118041150350a5103804050380c00055200226045a40340f4103080c40b090010b0001841603440250080036075a0307009040100c0040042c410b0351a0b501525481600c10044030304058a0309801c4009054121000e400300c1caa00d024811181382006040c078604481c1da6500103503900c0d040752400900310b0341a044d0390080c3e40401881254403030980031145135021f00010031100704443c091508144541c5c0d038800401c8a84d5075610100340e000000c47d011680035040025a036108803441902a001e603005588581c00781c1d009100011900240100c1901d403030052a03a044c582c3ca50056031300358403510032215840b8051081c00d007035200d150300c8403103402c0c000d1022601c803100c85c900701340031000c203221704541050101e04140032a040905ca8000e134000142060200c950400000c542c0d035910520004018003c0000c691005030710074800754a40d6940046000c0e12580c4880020b5141e410100e000070051189000282c0b00b91b2255221 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 157392850 1250 157391600 157391629
    0x30c0807081005060402040b071a010b0301051c05030c01060308070c0608070906030c0e0616110d0209040f1a010605030108060f04170a090b0f070b09030c1518070f0f05 74
    0x80c100c0b0415451180054800200a180e015500340400103581c1070030300042440314490030307000402c05048503c2100c0064180c0140d01c0024041c001071180d920b40f1030310342458020f1840300440c0051035181007071440c03180c0c0c0b0f400100749d420721100204111021024005d058403d25211510039103940046800040440d42280000c071903840400605d0300a0340171460960b218500b0510104101d0f0205d18164004550141c01c0711b40e020410702401080c8040200104044510010827140c0340c00184485401034406406d02c80b40e905910104038030340c1c011301a03100314110710350050741e07560340060100c2e0024891ba201a0141d100011580c0350040c04191145500002000000c4003000740782800ea009111600b060044c1108089461100400030b8142c83d0601810143d9912151908041218020b8400300a5a00074084074014980102e0010001c240c0c1411a800903507882281420244004c05081418003400c0c2c00440c47d1014426070340b0640d00444d40343c20340c40743c1d02c84c28419480310384d411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 157394100 1250 157392850 157392853
    0x1c02040510111e060c3901060603020c0d081306140403031b1413090e030c12040e0f0a0906050702070305010c11060a0c0c170703090506090f040c1413030c080708 71
    0xf110440c4171800340c1030340c0b5820341c1e00b005401e00303500d241004101d00c014410260030101c849a030007400c09000d568041d01c040c0ca401d5003000c0340e00c05c81d19641d29a20007404203102c50700001a0400c4507006003004065004007042c0441104082c0c010044071040d582500000d09240f000d40c03244c4000110841000842d503141c018060f141c0c010054140c00641c100060011004000510301d4102e001d040380b0384145902640c3d8501c040d2036120b10b0640400380300800500d040c4020030200c0c400007201903110010b09103401040d0f503100e1581d40188a002d00c0103242501c1c2030306101d40d450b4006110815244a00000c100025802c00151407012040056402c0da07404600042c0d401c000340d070401c1e8800300c81030400d49141d04841d0b4032144229940c02e410a1248000301c1c0c10001c1c03581c070800c00e0004040035501d1900d0720081c03102183c6107034012940c0754040d5446100c400780f007611507480340c01d00c4103c44181c46e44441b6001c4c0380f09507540c8030f448292030701c0b5040280440d84510200f45d14045804140 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 157395350 1250 157394100 157394113
    0x6060509060f041d0f0c030f011e09050a060c032301080307140f0607020d12060b04120c0b030c0901140f09150408011a01020d0c081c02040510111e 65
    0x402029102c41103d800340b5003000c42100d0360002040003005c07400101d000103000c20810400a140c500646034510308420380c1001940480000303104401117000b404000041449001c0e401c210f8500030800000801e00b40ca8010010a0749a01d0b922440741100b844101d68000c000ea030240101d510002e000d080707203030341040158100040d10442c11b501d1018403082613030b00c020103001c031040c2081c40813030702e490141e006507400e080c04035400415003415041c102410403010341032154000b071070b00403030145121140498003c1010b0003d6480c0390030042865400c000c0c2e0342d1806000400e1941c00010805020840f00903080703200c11043d0050b07910049040d6001410400c10904001101300c40b00e0384801000b031300304070204507401c00f801005015019540e200c11002e0b1000002454944a48a14420045d05c96016800104014115002a048180300b513440201660f003640007071003a03a1040354400c042d00c08540b619a00f12421400300b402032000d8803d01c00d603c003615444002c0d01008000c90740c2014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 157396600 1250 157395350 157395379
    0x501030201020c0d05070308160308090105160f02151006030e011404020d0804080102220b13060e01051308060109051305120307050909040c030506010801060b0d02071b0b070606050906 81
    0x1c6540c620313400e019804031140306550751180d01a681c031103000582101c43d21180301c018150008520360300000c001d0000c10491a00d40a5815007401880e091010020001281d400ea00d01c01c000c0b4401d041002400d8211030b040c02d01c4540c0030030803684105408682010082c000e03110040c0700300c081c0c08440c88880003a07990b03107908100c02640400001c607a182018413011810203000d10281590000c1b0028035802503040303041d004190b00c0c20303900916803894100005190369510012136001ca40490400700c1c41e00f40d07030000685050060240ba0880d00220500003d1300301d81c000760460403070b181c507041001540c907007040311120301541c20341c064000d5000c0b000503600031042c10000c5a02607918901141480c20703420008003103000c142c8042c0d951880c091024414030509100d10341c01070415000800420b4a0844842810f00410650315002a804141c00c420702840c0311440c2c104005a904000d011030b2290402561500813803825140710703141c00004251420843c107840e001c1c440061428054444a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 157397850 1250 157396600 157396609
    0x6060504090b01050c33070509090a0b0d03081807080703080715064a10090207050708010b0607111c0618050c03010b0f0607050106081f0f0501030201020c 68
    0x95242d41084000c0000394101c43e814442c03120280040b40c03881a40540b840740b40024071030440300203108000303d0001d0209076030700702084039412281504c0c0b40300d20ba038420100200810101142c503401982c01610f4070b00b055842800c00c2d115041413250103013040c0e54002900c3d0346203400d002d807a01641c0048014004207207200046c001c21881100c004000032446505c80c2e0654081d580b022140528008a210304402448990644040541081c8000c0e4112003038003842d500104541c081c45007403100c0030843c0701490103180d4020b0b2201c800155600c1c2c0c40d07480c00903a2604c02c0d00c40c0f08429460321755096014a0b0000850b030140d90810f054290390b00c002d06c200301c0d50100002d043c041030006404944000b442d01c1c01040e00600d602540b40740c088082e070a10500742032800302464860391400b130480c0c6182c0e41300c0c5c5250211300000d1724596198a080c0c0783c8940145895006580380d4813a00381c82010140203843c82c0d800722101c0031000d000d20b12903030349038800742c4900303000007400360b00820002030003400c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 157399100 1250 157397850 157397861
    0x1205060a0303081803070c0501110a0c05131407020a0b01080303040201091502010209030d020f010b0a0b0301031e0b10140909060a020d0b060f070212031908190c0e130606050409 78
    0x84491310502280c2c02080d107441c550140301c04036010300300c04070108403075a046900c22000300e456002070444031603641d842c8840c0340103501074288124450000351b803007014545c1c4480c6080304921640d42e10350425a0020756112055802101ca26003950b0002c10100c07000b0058901071903040e1140c020182c1800d03046486c8180a690341d030110340d42404401229030b0100310210741c810458014000d000e1150b01804d094405444020b402071007088400c00c044010b070403c490460744c20074a1180010301170000b0300c405d201500006040800c150040c004170914061290b0b00300c68001483c402140030703031010301100b5003003103503941889c0e008003002902110441d001041d07003d00b2110300142e82d07200400095034940207904100406500400e00100318189101d0801142540b0b4000f1410400300301d10001c11600d285001c6400c1141003804544903110702c6050a49043c1d01100601900d10304890003030481a415484503c9403078040c0301c1c20354013441d910810f0165072182d910a442c03d800c10070b40e04050807 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 157400350 1250 157399100 157399111
    0x6110a030c030c15050103061803020c27090f06070c02010f0f09180608100e03040b0904020424021b1509190e0702100c05030a05040609060218011205060a030308 71
    0x182081643c002402c0404242028400c480001029410343c00e203d021150000c01038503441100440c100003107500002c05150304039003121940810b4000c3c40040c0d04038804030b043c40010600c05000d10000d5880030404699002041c4111061607a61501c112840d0032500e50182c0810b024401d01810507200380300b1098985000c3c01c02d0000a40c0d5590900c0c82540041150348403165a91024480e41005000c01c55440d00404000e01c2203500542001d6203901ca01c1c8101c5980090010b81c20000d911070340c0595000f410540795540e800324650661b04400c440c1c10690000602440c00c0b09a122248113041d281840c7d000380811178010703640240b1000c4e59100c034041c540d11280d00d2240c3c10118158440043c00341000110f40049800c10b694042e103400c010241001200b42041e00c0c184040d9030103402e8949c004107908012400c4e4a4070b041840041c05402c40103032a403400001e107004041441a50301050010070b03070b0703200010802c140304141180c405880c1a81d00c0490100c0c2040400d01c03c03076000d074001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 157401600 1250 157400350 157400357
    0x305030103110d080309010c08090c030607051b150613060b37030e0d0f1b030c0f0803070e0d020a0302060702130606090f060203030f0a15030c0b0301080706110a030c03 74
    0x280f5901c070b034850354100b11402545a9140c07000044040c3e806000e55801c01045801800010034900c0026203811008103000204400841c19002c80945040030150000b65002500c0400844840749407403504100c80e403901070344c140d078101c1c03030342040c28804d0030121900d20441d58141072440084441c2d00e0b5040452030000d04014800070b0003030b520403100300d50000c001c1e2400925122200c12071424206500c03000070900809401c500d09054110982c0c9100c07040d007104099811409140548020110807070180840500722000401c20110100540c0a10300644501d100c00c1d5024040100707109078010006d41045800c1810070050801c5400761030044e1008180440c910000014002107440ca6480703a400259110b408206203c2c0e45480840130740802c0c80510f1452034600366085080002400105605607a000740360a00849010001d000d90740c00031b000340c0515920000b40149420030301403017480e801620f4002412601980c82c2511043d1800c2c058492a011618161210000c488058050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 157402850 1250 157401600 157401619
    0x12901020a03030c0311040e060406050d050715170a0e0606060c150c0909090a0213091a07030f0c02060a0b030102040f0b130f0902121b07081c06061d0301020403030503010311 77
    0x1106c501c90045d20107001960314820061038100d04200680e9515403045000c1c0c20484400c00c04508003207101d0064807090000e0b80f618404014049401ca1001ca000b40303040c0c1400c105001c1c1c0380041d50041150320388007004403417464803031001308030552240080003422584010341000850841c64600355112030f404070040d050501000100341c200b0411540b0016580003028160114500080b5140c402c0112250801408840e41c0e9049550b505080341d0f955080281c4c0c00090503248250003445c95812880814045180e81440281d500d82055409101c0c45046c003400c6442030a0501c00e4404445d90b01003040055807030140c011fa6182d0041c4440b040d102e5100402050b48481444070000503e030302c1e400140d4510b5046101460100c0203840000b9503406c203038484181501890640302459040000240e0b28800441c08d8107599802d1100c0301591810258000303140c0f81c01c0b8240408400803035002e10248a01907080600300e206070301009010403000d00041c00440c090b4120031510703050180442c040b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 157404100 1250 157402850 157402871
    0x2101a060a02160e060f0d0609060e010b1c0308160203040816090b15090f010905030a03050309100b060d0c170a0614030106050904030c1a09012901020a03030c03 71
    0x35902650a54000d07a00c0605808002410180084010720442500c0c550ba4207003400001ca03d40a5a0420740c45884d00000040070b0241c0d551100f4050703640043e04001240481d041c460107022001045446004440a819a041e0488a0000f07002d07906030769030140c40c0e6864a81810f401000840d410440c40305100115255808115508000c41d11b80d49050f500d5150a560a06480740e120703d0a0150449440d01284d19010300c0a940c5000f04c112001c0c1100c1e5240001290400701c1d80c0d204507498840d01c1d42c00818035030880f0045007e96036038403d481c01403c003207801da0155140c0c118131a401c0041045540302c4c084003070740f000f06c85081030300c0c0c01030400940ca0041c5800c41020b0701d000200695584042107801e0300070b25101001c54040d0024440d00380782c040021300e0020300800250900c000788a401c0d003008815004034650a00681840045003070140c181030090a18000c401c4003616410340c28080c1c140d41c489482c1340d0344016801440710b0002c5680c11009880000300301814103854054025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 157405350 1250 157404100 157404109
    0x9030409020703030605270c090409060f09051606020a030f03060b0c061006180306020d02040b040e07080f01051c11060f09090105060702010518060d020a0201090204140702101a 78
    0x42c1090095a020464600b007000300b00300b4100c0103542c016014070501c3c080b82c0c484621321400c1d0b840400056119142c0c101903000c28068900510024801031500000490412450b4414800302d4061421151040207086203040002c03a036006010142e8031402e21000060720641d604a40c0c02c816180101c0c280c1d0740c1c0c994854a0360890050030010380c100c08200b04c038400b400350343c200040032103140c81d03505000d10f000007610540840c04041d007590b4001840301000403d5404480c010100034409070303626562400c2130311103070406562070030018240901080c04100d9801080d4143c400c0100610011180c014500d862401102022541e10400e60b0f40f0b104555205400703405038406003441d56030340d00b46030010803541e250140c200520800c030500a02015036881002d941187c4614a10411035199290014410b0301070710b101540078030300000d034520440f035064000d04c00b100e100341c40601903c0c0020f00c2d2500480b9080700c0e6080107034451004d19907040030070742108840c0300d40e081451003003c2c513250106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 157406600 1250 157405350 157405357
    0x180d030e030c0102031804180210050a080f15011101200703023a1404030305070b0f0114061b0304150f110307111c060e0d08040c05090903040902 64
    0x26008140d450600080c10704090060060350b0100344051407814180806001c1481c07502102e05002d02e954841c80810142c141c40403601403500108504a01100203400500640c028030141000545410100b0409100c0203610390149028039100e030140d91000c0011501c1c0a2032140c20b030159900da1080c010b000006000c201a00c60b040311715541d84401501b070203460710b80c064403807048400c0960041301c00c05507010041100000e100362600010300100c04219108000040350100a440028001040540000040032014411183c00d40240d03120719009140c5a024862807001d0380f601d0018914030b10f007200007082c0100001d081c62805905009490385142c0154000c02c01c041400d0f51007201c01504000030522a4089241642c01180e00f0807013691640150000182011007603092448146c2c1c455410454040e807820f02a0031060341c50038030038090001703800e10400c540911020400002c3c0b080604621954004e441880c11600d0641400880d04d40180160400d02050102013442d00070f40c0002d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 157407850 1250 157406600 157406603
    0x402090f090a0b150702030601150207080102130906150e04022508220f180f021909060201060b03041b0b0f07020f09010e0403030e160306150e0c030a02180d 69
    0x10304050450f041c03295141240c0358103620320740c01740103400040c0c0e0001506415209401001c5070300070510380e41649006040c0d001040036500119207080030340d40f10403021080361000d0300180303e01590b03006000e2903024042c0c0c0b9180024030f035100703441503400d164000741800804003500240d2540310301c4407038800020341002107d085200080c80d552103501c0309200d40e510048416803110349841e02030180041c68051045009201203c0501e104120342c81e40716418400715a4070665840d0926880c01002c000e2070780241003c2100342801051403031051048005a88c0210308072031942e111610303440010b660f2025244518000001c0125110081c80060504142c21036003082d1076041178030411a003081044042c0e405028044010001114012a0740750001c0d007501b0002540e60030381001c83d0a10101e04a88445140c18100010401520764048a840c80c1411822000c03642c4480540d110404191100344001c0380c284041035403034040d64007c04541c15140d84200c8100344480200c2c00c0424140030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 157409100 1250 157407850 157407871
    0x70609061706131a042003070c1e030215010f060509060d0204030c0f0f210201030c0306031b0906050a0b070b090307060f0507030e0a02030303070e010908010e0d090602010e06060402090f09 83
    0x944d0074242801516001907003100700c0046822600d03140001d030f000003040d020800030318148400901c5001501201004080c8286140c007046038100a543e500303551a000303141d040c101000240d4142c2603074200c0240c881e5503a0f02480d15524400300115070308030884a44c12581c0c01c100c0000080e000c40807040080c1201c03808000000c0c608800004400e0031540003283c1e60101002011402046910155543c1c0c2d090800040c40300724404100c000b49155040140b0500c0292001c8a4610038030801808998030703c002031002a4030b0720180070403011581305103400340d90240003c00c0080c2070b070380b08154030032030310400c60b41000700c1d80d01c0d018113942c1d07507085516040740c1e514203002c40c455150207142a1041000018007040205e540801d661f071200800c030a080002d18002051075a119040440061500000a201100f00e038860543c440c5036003500d890200b81182d0740010082d00600a0101483d2114017038001d0340da03010240310180d481041203940c040c03d0b8076060032555840070b19441c06041c4018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 157410350 1250 157409100 157409141
    0xc07030203120106200607020a03110a14060a0b0d12050c0f1f0b011d040507110a1101030b01020619020d0b04091406011d0115020102070503190207060906170613 71
    0x2101140c0e070717002101d00242540c001e24104084150009a0803201991616040c507044000b401c0d81804c01110107030092240c8220b040031000304100040341d5000f441035603010000c0d11040340070001c40e8461200010010b50440c41c807004140c0c05100940114410f800a445100e00e0400d15142441802008541c801c440000c5c0c1c10580003044c805e40481e58402e00303020301e443c0740c1c0c13128440002c90b9501e11544030310386030390009809610032030b40c1800ba01801d078111020202e461410f80c14200300360400ca4006031611108100c59880051001d01415441c1c0d601000100f8070296000607611000c001d1300d565031620303494905502c1f54400c022655014443c01124598000d0495013081d0042c0d11019050856000302070565010710030b41811100c0d030685040f550340c513810080c1e005e030094a1004d001400041000d81d1b041da50400243c1c03050f105a801e40345103a4a0317441c1980d441c136460040704002100b2a1341415880d0b0202e401c00e40003d002000d400314000710700f201e03409440040503212403280060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 157411600 1250 157410350 157410377
    0xb0a020d03060e190f06060e030d0e060307050a0309021c0309060906050901030b131b08070309080405040c0c0602040b1b01060302060910030605030604030c0203060f010305060c07030203120106 85
    0x5220084900c189840d050100c02e10b0314483c020507035000390103a0329000c28100c1801c00b005841e0701913205e02003481d400b40000340d40c804001e01030100010f002070080c01a41c001640040c40b5210f850620030740180007030308580fa4800b00700c2c1d6540000070200185950b0b4140c0c800545d4400000c0c0c194020010000c0a41c0b40e058075000780041e2250b84104240f125002080c0311183d0880140c0b050104c01f0301c1c0000c0c82a0101000414000c030100004440303900d0113003802500300035a4200c00d940300c0301c1d4507403003619101d803030040381224160840541540000d0202f0f1069181903042039a0407800f601d0010138009641e11600120313401980032817403942c0006418010300c040344140c40030007413511008010480c5103801182503442101c492604c12401c514003003d10320b020740c0c0030801616002d0112000c1d81f17814a0007800500d441a0203034031922624001441c60210300714224140e030f5009002c2d020301d4490800040355070b00000300440030b50000f80245420221003150184c0201003039681e152414094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 157412850 1250 157411600 157411603
    0x309070f0b0306240331050c010f170109020711040f050a06050a0f0b09060d0207030503100509060a0b0c01020c0f160e04030203030c1806030907050109080a050a0b040c030c0b0a02 79
    0x1085054085500560344c00002045481c007640d41c0320918100d200028180350031070030500d6002d043c82c440c0c41d44031480c00000740040014900f102680a807100618850051070613165401000350502032858001e0040c400b04405401601034a4464560200a211140000b030143c42c000000c1294107030f510340801003104101c2c09a00002e0105441d0320808a081c5264000c0c0590103002d903000d041c40c0014a0001a1280d2003100c600b5400e0540454440c601803078001c1080c0d0081d610208641071054001c251860101010341c012800280496001850300c0c110980640001d00d120350306550030f0004244101c003c1c01041584c490b414007070004013001d16240800b00300c03a40c11680b060042c0c002040001b940000481c0d4000d014402040e449204140e5a041c0e6140c40d03a1a0030b4001c0008010b21a04800000e00001a21002d0300c840079070b1505da0517401c0d61a403840038098020780c00000d60f000072480780d00c0a150441d000713004401d8015102d8a50f10420441a440351075a40c00004428044560 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 157414100 1250 157412850 157412869
    0x7030c12090e0402120a080706021206090c0d050a060f09050405010e03121f050d080c0d0e010905061c020a0503012c0103080d1b021f0603020d080309070f0b0306 71
    0x40c0c1404040c99007030610b03156400400510007406400109250846103604203c2841c184c0d0388412869a100035520340b50000e500803440310702c0702880b40c401040003440d2000c1051300c1408004181810042480480c1020b02005800001540d5803103801140b05c2143c90320740d20291030411070100315800d01c0c0c5059421030708103072408040c5410500c00400000310071090103411101025443e40c86030451145d15040e25003580c020303035000402c0e00e001c5c4c00704201d580240c50301e280101305464501803990b40687e0442c00c041225030009a140c8418000f41c034000303019240c1c00c6d004224003a4083c040340c101408a0303200ea99980b010401c00b200400003805410101400d1106140c10781140804041c0c11148800c3c060200420301c105c085007841515030140d01c0140c0440c2008104402d03a5041c0d03802a4132400210f0707124031842c140c000c01c1074150080d030161108807503010b00711240c180015110804142c001411903c154000c2000008085c540d540c0d01c0c0d005024140381c00c9603039051410030842000ba = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 157415350 1250 157414100 157414133
    0xe0708030a1202130e09010612200102120f0d1e0603021c050c0112020904060f15020616050708040f08010b1e0d060b010504030c080607020105011a030403030c09030807030c 76
    0xe00402c80d0501d0084c030b03c0e000d0740881d07000c502082c00c0c688940014a000d46170300c2e0001203a1400c400341800520201003940548040c1c0950001d01c104c84e0400120b88441c441d5140101e401810004e90b0328141042e07000301008034246000103500341e806c040401d805520390491034011a100c400520951414030500410b83c05e880000b50261043d03a41c4046d03c400c402c03140302d410b10110145643c20941c0d00d40480e022450001c01c04c0200c640c07944003c075003003651409242810211045040e10007400000c80380d01400d10b00e8002c010350543c0540485003a030100c0030031580684d0900c80021901040c81088020703010601c0085811000360050011a80402091090b8201551400881d035140c204606a081d0b40100000c2030605542e8016030303d6100e160b20007018155103060000e41c0a40126000303010303210a600030300c60750340e8400041060b01640d0303400e494804d00800c0400c00290099026160480c1241400c459103a0380380c80c5c49041e030300410f8080d40480c59840340001001480c254040c4240d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 157416600 1250 157415350 157415387
    0x507060201060816050103050c040902070605011404140a0b030a140c0103110f07032712051002070308072706080907230913020301091a06151c0e0708030a 68
    0x803400c0208124001c0240301c5c1505059a5001042c600d11130b9a0841c2c0190000810541d503540443c98441c0c010f110034403840420003000c1c81011a0f6113084d00030f5541040c00103110a1603500c4030042e40d001024010070f101d0303240c4100710f80c0300d00041911281020551460307002e03080c1c0649030310024055410a00204d550307200108a5152040040416100c03181d406281521004402c0c1000c18a500388506506001404020002600c03010300100c20454507c030700c0a0b01c40803400760701d070b41090340101c41c0c00501161030703140010459885070101101e4041c80c2090400c0c0640c039911603220000c043e802000003c0d035000d0400c450400b0070800b0800808106510f03010101008011000d003e8000001c64424000c500105003000e0045580900740341c1c000300204078042e140c0c0b506e030001000d144100d94000c050000019824030b13220781c900d042c55030f00710940e61601a012003506c00d5055030300c02c0d041985940d40302108500f00b040042d0b00142080750000e42d5200d02418000d07043c000061845e0030fa1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 157417850 1250 157416600 157416613
    0xf0601060504060c0b0604111912020c0601030201140d02031806100612110c06010e0103020a08060c03010302060d0f1a13053601090b0402090105031504080a0c02060705070602010608 80
    0xc903980080c000d44511740180002819032181d000240150a0240c944428440c010841d0004c2041c5160340c8840c00580d503c0c1c0c00c0401507d402d4040503030290000c0d025003a041400100301550041c003c0e0802c060078204003614065001455170100e820648141344040b10340802c5a01f520f00c00c00055800c25001440820100d00c0c11200401108a1203403190360385884641d01410301c81a4400c0d01c0000000384141c400303540e1a114210704250091105134841c0c3d010340d000040c1c4000c0400c086008a01860040d072450b0b00b150244031041e404084e111b03a403103a848141841c0d09040b4405c2c2d1601001c00c12200c20441803890401a5960b9038103100f89045181400f804040714403621f101440c0d60b0704001d06001034601c40c040031003850900111001d2035080400b204c04100c0350b416036911541c400c40b100203d598175102810ba5031a50403c2c07a21491103414041004142d4200213408580034914048c0050103843d80418040c1d04a40c8003184d95920410b0144034150702802900c0c081c00020b0000c107031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 157419100 1250 157417850 157417859
    0x1060e07180603110d020f090907090b03070c0f2001080c0a0801120614070c020109090209101409100c02130905030a030c050d0509030703030b031614041d0f0601060504 74
    0x1101d42803064005044c1c0e60a0807428000440080daa901640c0b00811510f46000000d5101607a2002d01002d1144509000189040d400303030380160181c4a0205159085681d41d19042d0749283c00c0850945112501418520009510242c000d0902440c061030300e04441d15000054140c0328041d020303042c0003e00703104110096a10031710060460701d00602002240701581003c030014000c0044444141c068103003040724490f0003080d14040b49100380c4c0e840c0107041d540d032649130803401044400c0e030b44220106c1c14030301d00d10300c942040b42403031403644406440d004011300054030b43c3d40c448040002148d2500c002005514105203c0208208500c10038070003d24940d4901c3c2e181d20448920b20181a17940e05030b00d250368428015a071100403581402c000a013080f035112075176a00061401c900007420f200304480141008104264000584001c20b480b03d804e1071840303075980c1407598881d1341007540e860315009204e041083e840d000d4144607000d46240050905a10b040140581001c01488070401c070412 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 157420350 1250 157419100 157419137
    0x90105012c1504030308070e060a050d0903020708030406090509091b0d08220e09010605060a030209131d0f0a050c130905100203180604020f0613120501060e07 70
    0x2007101000314010401514440001108a05082004044450003180100805030001d90460080c0850344031901c8036400c20b0100060b51095014a00005800784425901c3c0740807504501d40b414803d00540c0c040c0341e111065070f8515005030f440100001c4521208004030b08098007070700e4100c0100005004c0000c0800750000502d096226228058070360080002d00340f1142c00c00b5640821f01902c1500c202152a40c0360f000b101940d4010080765642d2540410680101481007404584024003843d0030100c007480c0980081d040701110a401c4100c90482c00c040d0b120340d02c5582e9000b001125909601c00001c8105460811a1080d02c40e00303620079a4043c000c0703070380043d140440c024201d5041d00c10f010b0000d15803005d440e0641c40207056109003031078000310715000d030046d51007042d24013141d48c0340841d10002c040e5900c50642e400380d0000c2c201140040c180c1014001403411200c404080c0e60704a40d40d00c4046210561054281d4260350f503172109002c0c07942000c0c942390304285c0030f04d01141b04960040111 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 157421600 1250 157420350 157420397
    0x110705060112031115180312011403071802031515030a0b1305150112200a0216060e0f01080402130e070513050108161206020a05091e09010501 63
    0x1c0c103620b04032100d1001014862510a801d075841340054070003040900c480485039207015201840a21820115020380800000079039445201d0b19181010076441c1c01000300801d003d090351039415004038200071404280c040d505079241d2940d44001680c0b032800b0003006001111401400703101da01900101c62510f003252040e290021200400012865a000c0010706005040403a1a016a04050030000118100c1000713454100e8280c80340c01c95900c20001c814101c034400390701180800c0140403155241c40082016043c11038650046514074000e0500348110242c180d800b50001440d000c0c80711006040c8aa1910200002800c22800310b081c0341e8002082d444814140303409103961100c00200c0c1d8401000904020803000c2c2c2140c83c4c2000c50888400505000d004000315031241ca402c0001000340081da4000f01c0f41d00781291a2146c045917900c9005c0d601540092007001801d21052410380e5a800c11480781c4c1d0071200e03041c4400821501403103512a0160720050503c04581c3e00f960941c1d002d40c114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 157422850 1250 157421600 157421609
    0x411070f260a1d090906150a06090603050406090506040503030a06060305010e07050c070e07030911090708040b04030e130c0f09030305090121110304020913080a140c1f1107050601 79
    0x1080520a001641002d0300c2d843d00c00d594040f255000b80403000c3c80101380e950051589082e106c20083d40341041c03114002e0588a010b0002d204241c00b042520300c0b030384c02a40c00502c1114003090b9450309440d09803030560242c8050390180c0001051210041c0c4c7c9108802c01003049003000d0180398500340741044414401080e0f2014082d001455403d0314800340480c030013410484404040074141030100400900300340804580418512038071003903d180141e14584030301d0141e500d01e5002e42d180e81e1940e02c42c10000d04110b051104c080160400360307885001d034030460208810300040c0ba00f540000284600740e249080e074140200300c801800445d6100045580300002800c0001e1416100e1100c088408450f0703c900112524200326586101d0101006601441c001c1301c0c0f42c031460311003045804840307541c040001c1050604210340e214050007102d40c801200d40003004113052031880200030782802c46010206800781c100746c1c00041d000455210f118201000c0c09903182c244800f60b940e55a82d0b1206009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 157424100 1250 157422850 157422857
    0x301081902030a110402120106050904060b0711010c081b01020322020d021909060308040302190609140a0305060405010507180605070b100b130f270b0411070f260a 72
    0x44c201094840d03404441e02018a00b00c621050b69480c54000d040350050500705101d40d04003440000e460701d50340240d4075429044448806c14006d61001540e41100141c03044582c02e030b080c04524005030307020324400710f844800c60026a40c1d10749809128404002e080c00144605140c00218003d41c646101d25003030f09905480e0900700d1300788050000d8400d052680700030113150030710701c0100030060004003610859209890007030401864642602100750ba81c0203207000106085010410381c12101c168100c0d80304d0141110a070b1980b20f44030681000002c0f10251000e070f44401c1480002c3e0760021104c4117000044002082041c18030030300030518131031501b0142c0780c94007a0020410350a460004000242042204950707100855511140c045909205602101903070100000c0e1103409080381a034000a030b40b400034602e54411000b00300508140c805990480c0d41d0302c0c18451a4540c9400400d00d80c0c2c09032281200c10106441c10850882c0702ca0901c0c0301d282120b00391400ca40b908a03060303508203002400d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 157425350 1250 157424100 157424123
    0x30203030f0619180f0216030e040b04141b030c180a0b0309100b01080c0906070303150906090b120712030c0c0e01090b0f1513050405010b0301081902030a 68
    0x40010903140f0400c0c06052001d8a00c080020750503407070f0001a040240002c4113112400d20010000124014101518900f046481e4a080041e124070103985400e02d00901c001601c0c22207902203030440700c208e04220ba40c89080c0c0140640300710300141c00c0030340c00c0d201c030312952540c600003c2c101c096000b0070515121000010050300c0895449580c40d41c00380c10600e000680704c0c50905885a41c03015120801c0c5291460410506025441003003142d12400c2c60041051410722040140f00c600d0340500c0d400e0f41007565840880c1d41d00314000064000034401c0f0310010a8850908034014216aa000d45862290801142c8811406004504401220080307501810102814101510b52200801c0002c2680304d400ba0003003501e5601004080c1691203c0c0e1080007001078000600c8000c03207554016603030200c0c80b02d090000e0a08101d0042c880320031803000059541d80c0d80c0010031f064403020f8100c1d661009000c00180b20254007000075000002d03e02c499148412300c50380100351074480414020308515a102e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 157426600 1250 157425350 157425361
    0x30a0210110a0803040b0402100306051005071410020408011a18060112090803010f0e070c230a290c1c14090a1104020c100507031d0601091404030203030f 68
    0x41c0400b400c6950040500c81da01d01e002c0c6080061800200d804030302c11517204070181860340c4203100341e90a81c1c0019215041007000c0200c20788580c0c001a80458000c1100e5a0607038510005014804d40d180c16010702503140c50501500c41d003510702d030310110700c0041c100c1c00e01c1000550f81c1011100000d0445248840d1a8a40344012510b04d9017811610035076a04200e400b074100540c04004604803843c1402c800d03407660302c036a1083c2c4107042c141c1c1c030400080c940c0d540480100703400354800d182d0803a0204101341a86d002c00103c9080c18580e49054440d800180754015900c10220216002d055685200c0011407500d10342103041d80c0115101488440c0c0703030102d005c01e0524280d0100c645503082e440c0c04041803400c549240c2d50740000c01d030200d4804520700700e00e01650030140207031003805195201505501c600c1e04500070003030074000c0041b42010748918100702c82051300c044480f581691040a098075605002065080c2d42205415900501c0350a0400010a07804020340c0c0c0c20449440405170780b910358 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 157427850 1250 157426600 157426603
    0x1c09050d0201090807030309030b010e0106020a060507030b03070803120601050915030601031415030708160311030313031b061403150a0e0a0b130b181f0b09010e030a021011 76
    0x120b4120380000c0c80360341c10103c203142e0407238440400c8038841c8c02c0c1642a6030302e40d080407400103420b21840300903a0110060784001042e54005940c0000c4510300010042d61240000c1e00d42070190340041d04607080024281c0e4001240403115a00c003f00b13007880c41c517104074440858041444d103d90200c0b000c0000c8007050f0141c0c8030703421050749071030030030307111000c034100702442e5003d003152026810700c07900ca248000030700c14002103400c0000088200d0004295491501e1300d1005560341038405a040c0000c08c040c035940240720301103a01842c000c868840100a40484035541084950022814410710500d50110181013508903540151b100304081c045111400101d40c175110180c1060300914000030800040490941c884a8411011100002400320700c085000864186404180c0c00494a4a010f4050714240c00c5054001d5402e10310080038054851003200d21015a030490030414a0025a1000a6038005007000c1034240403005451200e00d11340c000b4002540070071606050110000380d49040800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 157429100 1250 157427850 157427867
    0x7050a080312181e0129040902010903050303270a0f08160c060809010b011106070e121b0f090f0708070c02150406110304080a0f020f030d09081c09050d0201 69
    0x10060484000300d501084803281002003011150b04c562030b04e48143d00780300c43c410030161034080c0c1891125420210300705000150082030400e90521400d480000f00003507080000714030540d603041408020031840302000141d0f00f0202c04c001a140e000d507118101003103080c125000810307440900d044c1d40341220f03c1d400c1760303045480c800a000d00e1034250380015542e4100000c1172180c080c1c4002002444504001501e0351510b110100b8000d601440c00108010b0080c0d046410103c00200720361188448241443d2401d00744003d54000c010042c851582281080f64034107800f0070080f00d403201c07240b60003e50001400401000b2004006007140031595844c0500b85805041d5009060504001707001d9201000b117512a210300000540065540303c080c0e0404002c0c0d5040d11401d4004d81405691501c0300117039245082c01c20303684100100c8a4851903902042421201c1645031210300b01c0a2600f401070781000705da000420400c0d085540041c10140d032200d00841641c1040380c00d05070f0030b5032a0004840046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 157430350 1250 157429100 157429141
    0x20409080c0601060801050307032406120c031203141b040b0409050f010603090201050d051b03090d11070f03080c3a09031707060b0406061107050a080312 68
    0x1100010061206200442d48506039402d9441702001070766144149903a80300d40b48405807a5070b8070344858421014550031000340d0603820301400310304162540012610f03d0b1100b4000c43d64a0f0901c4c0c01001005074130000c0f01040f20382402e0070418400c54408607041c600c0018400f805001004152900742d81e685000d0303030085c1c0180724440c2c1e01c540e04c806c009401000c090341c4070300101120b0800042d0b102c0c401c0c000c0302d640701d83c117035100c03420700e4070040d22180504005451407001903554071300b0b41c00c0040302e1400703507110303205050042c40181c200020142a440c1201c860075147d03003000e07005200020b010013144c01165401224681d070f960311810941d041180c844920356008601c80f08044070f915a26440c030350090750b8417140c10207614a202080d560441c03113100c001d00965142c80510a82480710015040d890700070303980419024510000036040310b82070380200d000715444403514a9221010002d64001d014107035070040000741003841d140c0c2d481c0030343c20940002403080d400141884100e03103506244003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 157431600 1250 157430350 157430363
    0x6210204140907091b09170c030a03051206041a010c02031f05060109150807110a0b071d040203041130030405011202131707080a08071115090607020409 67
    0x90500d02d10b15500c2e40b0040c85200301160805416480103162609625448502c540740d4500c40c82c641190404d41da501046240750074003d1007a5141951000d00100601502c82e607a06581c4e0000d42815201c11040070f02480d0066191800047d010f200b150424440c20700242051805441c00d0b00c0068900012242c0342240c0b032003400c1090940e51802e8020b00c1c00ba1000340c903001040780d201da00818269000d1003a110000d5a01000302d000c450150b220007251003141b0064422450140e21003400c80d6000341c541c01c000409901100d41240b4400f1120328000d0000c950540c510304243d1a0003400b031285451280c414800c0e00103590010141c41c035802d28892030000305e00100d49a00758000d880307412502c40c0c0c40c081003003081c07000040070443c8220b5115000d4012441c8c2a00c1c2811940c6070070f0407881004940512a4980100382030008100364416148140301d001d55580d4603180c5181078051a181c030768041e4203c06a02d0072024860b1064035507291042d01d442e0346409440c000180903103240c00c0050b040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 157432850 1250 157431600 157431641
    0xa0203130602031b0f03010906050603070e1005041d1801020702010c06020a0c020307030b0f0a05271f0504061406060403061e05070c05010b01020f0a06020f0405032e06210204 77
    0x10445c0c440554100c90f80b40000708089940e070360600c03c403803104882c0000010124507c408151502014000801d240c0d85052400d2646034920410855955401c881c954054074013000301d01c0e0320060300707080e100d02c3c2000254204002030f0b0028041032a00b8000501c815004200058050720559513005101d40003400c0380da80310303641c1c284680b850a0030f945a0882d103840c43c00092500c255400362070b0040a012a204c086107291125040402050380c1e1414210301480c03803c001410300414031800040e070b1003440003946d41000e2401d0012100310a64a81521140c601040025511142501c0880e900810b0119520f40044003043c0503102c440100c9000c0e81c6444144803896a101c451090030038800c80c003c0101c4c00010300103907581c07400c41d00740c0d0b41280d0099100000080490700607001074009044000e05007078a0b0340000381130543c0110124000850040b800384130104041d5001440f41c9040010000c1c039081c0b811103582d00380c00042b054800c0c003141c921201103468580c401d4030113a650801c03500d034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 157434100 1250 157432850 157432867
    0x3060303070606030b0a0510120b040f0b1f3807150b0f03060606030106030b01020703060e06040c170309040b010c0516051201020f19090315020a03050a0203130602031b 74
    0x38070105c2600d088822520f800e00064000c4041c0000b00d040e5418148a0360455072942c2d01c0c0181008010801c44010303a462070f05100144030f0413902c60243d2091180190302c00c1001000c20070014450740400c8080700d070401c10701500c6285e210310802c0204542d40046c2400b000c90860f00380b9100300e640c0280361044050407900800e005a12044601c01c1c00c031118840c01075260201603503080251240381c0e00150400040203064005c0e80a03100003101801070340d0311a40c0d00d032200303000c4800480d2f98103030680110040000304004442d2000107002c4003500e40c0301988100120a03902d00444818038010740c0d031a442c9a98070786c0103600c3d01c244551300404850b403543c080c0309122413500c440e115050045c042008241d030001818003d6803a082440c081c401c2c1810359030038203006a64034014420043c42142e4001001107802e9004104400400c4030002d0303a15107202c00000c0850f40c0c02000c5a41c3c451040c414001e15a0014400700301c0d03140c02040141c2c80b6207071132000414a85400603080c41e103c1d0000354844 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 157435350 1250 157434100 157434113
    0xd0e1014270a0503010212070f030b031005010303020c030a0b0f06040603050102191803050c0405041103190c0512150901020c0d120e06010b030a0507120f02090a0609120303020306030307060603 85
    0x240700d11050b0b4880c414903540344281403e0b030069600150750001c0c490006401c41d48142803081d080c1c6000e02e40442c1c03400a07c00030a0030081e6880440c8409034480c401827083c590104081055004203400405480401e1340302c04158480140c0001d000d0000b95000c03826035921908168081d46e0410700840d903c041d210084400d0b07012414440020072680407620a094600140960446c0d4004004c0e0241d0107000f020480106030082c000c0350101c82d00e200d84281a14104400c281000c1042c60300e0858145030700742880c0d01e441c240e007c284a2001c0c410304086800b00030680c111400c01028844400d51100d81190740a4001c140d400fa0092003050780003002e0940c03141001122128103c400c2000d1084508269102c981c240039104121a081000c034003242a141e1001e544207180345441d1103030b112280909415102c041981c004040c0e00801c0c000b00d035242590b0400c004102e107003070000e81c040ca000258224611032100260615070b02000088031a18107004580d80d0540c800e1040008603100d24000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 157436600 1250 157435350 157435417
    0x3011d0c03060c040614090402070c150e060403031e0c0212070504051501020a030c031202040f0302090f040308150a05100215010602030306060d0c020c040e0f0d0e1014 74
    0xc074401c2c4100808a02c10b0342000d000c07201901d109079142c1e24841364141401079690f000d2440c060300706a00f0010500400c07031a144280180046c10461024505495001001c001c3c0031068903100c0c0d0420070080000a40003004252001305111402c0c00d0103005810664800401c0200a5089207020007078007141c0c0c2002c101c1c01e00fa1350040340c0400484c0c0741c080a020802642c910b00c0c3d80903030b200c0301c41240031a02501c1c841c42182c3c420301d000503c2d04445403000f42a038020354400d1024100d510014003c41c40c0807a0752550040403120003481d030b0328254400078048800078003034000c0a12101000c49854030350380d01c600040c000191448a03445d2030100c009540305214090b461565070100000705e14148007004680c05190002c05940c1040803010600008081085440c025481606c005003490780300c900581d00400c2007600a00941c0b40301030f03070310b078180440d6290b08010058603501c002c0450703a40300e99040910b111454039002e0a03103d010341d07082070301c40c10f50160b0015035086950340c4143d4039035031407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 157437850 1250 157436600 157436623
    0x9040f1e0203090703170c0f0a02100309030906080a180f0c050a030510380102070510081602011805030301080706080412030c02120c070f06050408070b0903011d 71
    0x4a036514003429000508038007050750400b0103070300804000c00100b45010a69540f1000e004d070b00d01e152184c0b0080151070200c0f10703e080281600003969072400d40c5002d08a6400f20541070605000c2080140e4004100340c0283c068102031103400c001003101c000c5650310011000108064400103010b0600b00303003441c03040e107071390407200030781241c1c030228080c101500440101c1e03078040003c00c103075a2090b0001c0c001d0600003441c0401100070f603003321303010b00f0041050f2403440941c070346244042d0201000282080c40940145018010400407515815480707540c00354400400070900e88040c0c510311080340948565120140003103e5803280000b03024000c0700640c12250030100f00d0703e925580d00c100744e07400ba8007143d018080c1d003800a04050340700e010350030080d2401c0851044c0c40100c000c2040701d12068210152141c0d035079018003410321141002d4601e078406044070b030a03742e007080d250100f06565003105018000c101580426201041d440c25001020120600413841c00c40e00004844140d40381800c40c01c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 157439100 1250 157437850 157437881
    0x6101e05070b10080312040f02090103080a020d020705010914030a02030322060e01050d0c02010b06030106032007080714030405060325171503120307030605010801091b08070509040f 80
    0xf292400d80019110070440b80020080e500741800f00e0101d0440d064020016200030b04203200550040e620034110314061440313590001d40341d0046e034000a107428040340366002135502207071060001c2d0fa000781d500ac0480d40d0704004482001c0c00c41f4046170909050740c9000390140300220f04464801d42c032020300036014240000c5110703000d40e603400c100d0302a4056004107000c5841000304500313003155a0400d00d0010220300012070010310380310108100380d20981c000b000080c2e50303c114141090340d0074001403048801107070309401d00c030f041e40300c00d10907202d040e2000340741041c003a03045144003509005a80042100501c3c02d80c40f460032203a209503007c2501103010103401c403034044070b030b00d40d004800e42c10900300356030b01c0c0c0300300c9035a2007000390340ca004c2030700307000758148a20f1a58070040b101c1c0100451203440e4658012840500c1c2100140c803001c010703000210000d0401020b2249550000d030011000843ca10317003000e40e51118401a220b42c428124500d8000b030903c03110100b8201c2d030f41c0000d0b811341e13041c1e42d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 157440350 1250 157439100 157439123
    0x1906020f0a0306080d0806060f0c160306050601030e0c0a051918020a030e0d080f0711060c0406020d0f020d12020d0207050a0201120e0613051501060305041a0106050306101e0507 78
    0x45c812195641c00300c80c0a90300c000c1c1400200c54040e41c0d007014007138040400d0704072140001c40c41d580301c401558030791080395225100d40800c001941c0c503026004c617643c40c0500512402c550180010031800042c001c45014801c2c00c0021460a01480d2081c401095050400403130b2003003c0c000500070354009003405002c80e04142c0c011071100c4000170300207803109030707076680340b08d079890305281241582c0001d82382c182040200c400303554040c03800348070940c014004040311560310780c40d206e4041c4c100303500345807150284641d02c104000c40c2134012500300c40d258014908542c000c001c815890700280104440c0610503840810300208104000400340c40b450b0003600c81500315100d0003000c03400d403450b02603489065040306003c5010540543c0400303005a1090041c1c802004500441104010f801da0002c00001d03214010301c03050017801285c0100c09203207403000c1103240d0305140c8050000e1002803d500d018001c06802584100d110700619403002d040d5030540090344211a90042254105183c02c2da045020786 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 157441600 1250 157440350 157440373
    0x918060411040506070f15020a0306080607080403080f0601021e012408100b1503040c1a07080909060117010602150a0c1e0c0203030d0212070306081906020f0a030608 73
    0x300c1c2501c086920007884246002020b540300859000c028a044034185803802201d503100741c0500141540007201e55000894a180c45c4800c0d10b0b051018080d0300c00e0101c62030900000c039520124490707102960034840806a2601c00040f444c1c440003481030400d42c0c8601d82040c0907044190071010b001c600c050030402c1204a114441344102c0140d1052020b1a0f03c00d0b04003048001c040d4211080c900b0f001480c04104807484001c8122135402202c04940002c0540000d006500c0d400d12030410054611160a081007a40e503901c0040788a10900716100d10450800102c90740e2080c420601d203180110680c00140d6540c4c0c3c03020f0b60710b61090440c680c00400042c0000c044201030b1042c5d11080d405035441b0342076118070400e1600403c0ca60705900007040f24500000340944c5040001f0000c1d164809801a0384034142c1164043e1180007030141c408150900c441009400780000e910503860410440001c1d82d81c0e064500040284a0101e8030000c03003102007100a0802e40651166086551101c1038440b8560341 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 157442850 1250 157441600 157441631
    0x1b0106050102060115030b0d0c1d13060515031c030b011103040e06060c03130e010909021f050d05010e040c1a1815030a06230a17010209180604 63
    0x12030280900580c801001003260800c404103040b00c492032824001526801100869014100b08200f42c40016440c402003004801101440d2000081c0d00504029410003d410750240080140003400c0325460b44003081c107200b43c0250008503181c0050840b803a091045180000155009603004080303494104020829402036054880348410400518500b608183c1d0750250060007419036600310405005400030400200001c0c0f50503048101d45010080c580348440e80d88160507007240c82c800f41410b291a0040c0c56464007240d1f800d901e0354401d1700001c50307000c003155280680341c42510460305003c000180d03664480d080ca401140184660070700da6884005120b03510801544c0030b03910072001c1002c003102201400308001001c800a1244107c0118010074180640003560070103400d5030b991030104040c0b0f00b0400c072900c80c941d1010003603050180540c00210700030f031584600600811421030040000c0401c1d41120300a1800420003040980c052a1070750440c8801c880b5a07000340e2030310f8001d408a070803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 157444100 1250 157442850 157442861
    0x60b0a0605030c1e07080301081002070201020a03080411150702030615010c0b0705040302090f0a060f0f062703050f011811060c010609050903070309090209061e090402040b1b01 78
    0x10140c07a518655216490384001c507910203400c103500041001c0d0418503490403a401000b003540101c41e11034482d41072000784c50400312200385002c1d44510403c101d05c0140d0b0042400c556035a014104100c1543e1039042c0038060b202160a415881911f030b0304407100d03101021001e01903813402641212025070f074900041082d01c800100ca00c3c00b003440580d003400042c1d415220301e5880100c914080d41026036940c00f04410400c107494000140200e501000701d01540c0e4072980c0700601c444001c201e4640e00d0007034100c000d69401d00910741008071031004644074150b0300b80d07a802d1485481c0294441c081c0d4a040c40c45d210386200814010650a00d5290b1442e10300202c811603c0c00e401104170600e603c1020100504c0d1b6000125a91617035486000015984545104961003140c1410146603200361619000b04041c0b6107810070300072a44140710031921030b02e45400381c502100138480d42032156400c9610b0211240540d0a440343c0c05400010041015002c00c0301900038049084041d2420803d407222a500740d50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 157445350 1250 157444100 157444109
    0x30303070c0b09161205030d0c0923090106031d120301060f05030103050705011b0f03020d1202040311090603160602010209090a020c0a0201030b06070605010f080f0f030d0903120203040c03060b0a 86
    0x1000c0e101c1807245c030840c4100100e0325880f6604480ca44009200301c9000d84012052510110f580356000700080e00300740c0107840b403400a04841134401c425010018040140c1070244104250341c44d980701c281802c410100004203000c0400b00c8548050a5900c0c503a0b50f4000d000d07d8001400103422030309400e01480039a03050741d81c400042e180c2c40b410f0000441c2d1050100c1445605440d215442c44041541c04030b036003800380d002e6405000c4860900c88094500041d9480010b8524410013041002c1204107015070740740d4400311604d44041d1211710001e49408078941c502102d21075244c1000078800c0c2c05600518a900c0c0503264203035075a5130008140308a004643d40c2d88500d4008031a0180150322035440361050100017400c160421001c0e8640c2011204260000e80440d240c0e18024403040108000c0022055020001804951001403100781c0700c2c0a86d07144804640d4a5002da1810980140488031140640340421900c0b41744c241441c01401d5154401612030520740090b180490420041200c144c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 157446600 1250 157445350 157445383
    0x1081302010c031709010e0105150a03060504030203040302031002130923061f03060302040b03010204150c0507270f15030b0901020d050f150901150804030e030303070c0b09 76
    0x2105600156001c0b0200802241040002100440000292100d981c024404a800021070580e00c4212a00310b810150010708800302400e802103091f5100c4903000c2c2940c0e0300c40390110f6142c8540c6000d91460149801c004e505008000c070002007000c69601500c01076070602c801c04800d56450700c0034002c0351a9201c48040c4260300c403484405502c071280f0307900d23002203015042a0880240e0746102c003c0c2502d241802002a4540f6420070a600c0e16010340010000700b20021842c0624041002d80c581c0080040034050001c030560700814000c0501a03080141480242c10200d01490035805203800240c070640059140743c00012089081c0034403c04200d50450307110301483c682180c568412480000b010041107640030811440c0525190146500036100450b2042d01410074681b102c01c2422200c00d070314081e600c200010003482562000d1342075000403900344410300b602e40b41000c542801680c0152034151200006201d0300c9940440040025405000701d030800c4c1d01c80215150300c4415011010707414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 157447850 1250 157446600 157446631
    0x91202060307230c0703051513030c060e0105010f050306070c03020303011e1203030209090a02090a0b030a091a070f0908070603020f2203060b0108160e120709050a06050108 76
    0xb41d00070b41c03100400c400c0c0b10b0741c4520510000403080718aa403241402076800e410034141001003210800c02040f030702c0a10720100d5550300d00b1000744407100315201c01c0034003000309149040050086503800340701d200034150000d000541c0c641c040e44548103054030419000307200350000a04242e114100e25a45143e140d4042d44c5580d10700403580d1010388500404254076401000c00092080c00541022081361180d00c2c0580c40384e1400d0f04001454400a250054140c010061585107a4038000620140d4800b04801c1d0f499403a9585500000e1501440040c00620669096140390201c52846c0c4d2091860380c1d03501440741c986440c220359003000c84c4148001d0398048842807150354000d401030044c40c0c8500c001070341029032000c1c1c0d601240c59030700414404400721507024028089039000c0c00341500c500382840085400c110071003c0c80c1040400c0c1540800001004100c069580d102010841c0c0c10450102c4002070307103410342800180010b03500005c00303d15007400020342c0c1d400b60f004603119101d001c1e01c2e02c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 157449100 1250 157447850 157447861
    0xb011704061d0129030f100b010e01110a020405041e0b0604050a06030308041e050709020a020d09180e161409060d0b04080c120c010e0601210204230c07030912020603 73
    0x110714108200e5a418002c480510084040c20003640582c00c8002c7e00c0800c1b080c4880001500500c0c0404619040017a81c040c40342d207402000401c07a80690b41600d0010719541d0f14101802d12640c8410210700309a0904e42640500414260080c010141118200b100d503ca482c080d204458040c800100031400e11000980850f15a0040310510f8041d00c1e1030f45c089285542c0e4070b505011090700610b807019404660302c00b80580c1000244003e01903801c1c0074038903c1c102060801990540503c030070203107485a0716410401d80a000843c240004440d000000e40c1d2038a0148940194041403140034405c4000052002c1c500140c15a00741a040180d00001ea1200d03143d20706a40d11001c1094940c2c401c0c030b5031421101c81824024140780b6600d0000051036080030340700ca410003106a0000011075103200c01d14031008031b42c1841d00c142c1c5604840001c2d0640228280c10060048002480039110244041058014121000f00451480b0360759102d04651140300c038400c03c030001e05003c0d4000700c5c140000344 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 157450350 1250 157449100 157449161
    0x1407030e031002210a020d14010e1e06220e030703030b0303180907020c030a030c020310051b090d0206130519120b04020d020904120f0c02060a030b011704061d01 71
    0x90f040341082001501d0700d1030741403c11f01922004801800c42102000041110161030071140f5000301414003003013801d040042038032800c2040500392600c07035060076844010789039010101c405c600c040c01005100882032500416260b8010060a9020034200a141f101900d0040b04444510364244070910390100201c05104211200805c81e005600c601d04418055a40801807520300511954446014041074814981044810301c3d4001540f400c180038050418541c0c000c2c941c09003000100c1c01d4840003001c0005142c1205001d000e0340000700000c18014582c0086001c0044e1102079840c18004501121030103410102e610030300300c0515041d42c070040002ea042c100190020300040114a2006241c3c0005480510590341150640c0071449600e51071500716501040c861a01e040445035505070340c001c120740e8415000490101541d803032032048a80e00076032200000d44100602c40c2044c2c90b25161250091600d022034010f2260940014668000b0502400f5400c940c039080c0515080100301502 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 157451600 1250 157450350 157450417
    0x301090209060d0204030606150c1119260d170408030c0403050f0d1209030207030b040501140103060911040218091803070c03060b0613151407030e031002 68
    0x250b512003820800034001d0452400944051800b681002401521b00800b2583c11038840682e502802a1211070300301203048402044100b01c801c1d5003514040755035401c03c050024560f044020405e075262903440040e0b415007207000c0000c104c0f208554510611260a039100403280034648180d01c41c1100060000703000c60081c5802010b01c0460904003a01c0703075a10303814412110b030b202e9915442100b48565490303004c032000b05104031441c001c000100140e00d000f921001c283c04003401014503c004141000800d40c402c00150a07444d0f83c000107961030740307450800b80c48440c10944d80d41c090700e90400c0c8140360500c21181654500d0020f204480c0c840e8090104001c4010f010744100d00040d4420078100300c06000030b04172144901c01c40c503401401c40c0360601c11102c01c0c010980c00303450144032000350544507400300c50030380c2e001800a030081c440a800c100da109125030720144402c0000700720340c0205500402c00d154010700803015901c4907492200440228040c844c105640310005440500c0041040d483c00f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 157452850 1250 157451600 157451617
    0x1120203160b030a060b030105060d05090c0406080d0207080c010f110a020301050705040e0c0f07082d03010608090f070b090a2c0f0408030402042c01050718030803010902 75
    0x192070300c0704480001400c1c9480258072200e4515000810010210700d01e2240002034051036198500310350521b0b0100b81e560041e85e06a440c0107a0794808900b1022040010400140d00207000340b08a0b80c40704c00e0741d230301d4108035480c0c2005442120000b0403081c00116420035601c0041c5e44070150360007410012282071004c0384220040e80101c88410300036880c01c0c00b80e0f612a80050f110036507280e01d070404040f40318030010000d00c014101808402028259401107c422542043c4400d44038509054441403c0c00380e14802e20a02e41c0075034094a1460340d02010314100e44058031180c0e81130f130761038413855260070790b400e240000c5401100b024011003100a020300120340d000340001d0702070390700e6440458032a61940c01d1118204d900006010304000507061896101c02e003542410081d04180c1ea034400e4070302010388024811500e0701e6500d155004d01c10510021140c0b445c58600c5190600c5904138000c000030b4484d080020201e40041c00320104001d0f14000300e0fa4800d000c0d501d142e1901d0b00d00c1c0c0003504003109 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 157454100 1250 157452850 157452853
    0x61008041b0e06010e0105120606030405070f1206050703050403140a0201020906030a09120c150911060a17010f030b0c0a030b060f040609050f060a080402030f030705061e04050601120203 82
    0x540042403804540d100540a0420741c80800c0c202000050700c000342c004c5c185410001c0030072804070b0541d1001030003078100d48243d40d40c546035280c5140840c203040c0150094101c10a080b040021085840c1e4016a0214040e080070000c1e0b4031941001c50940b0011500607010550607100c1100d00c60f0120001d04181565200050a01c64180009050f960090301e250042640310745040741800070b4001201c400b03451900f05090080c040c2d50f6000418065041c03912004c40d0b0b100240010301c00040100c0e40c500000508080e038445180202520103448070003036070a1101c00340e002040404c4100e0118050702d4210429801c1a9120241c4441d254028020001019120600428031703440340009441d0381d601c1001e025482d2410518020300f03e600644c030840c0f20361204100c01c006512000201c80c0d40c4182031410130a0b0327507203900100e45024035003942116a4407000860314188503004c0388e03043c0941d64101da00c29060031100100b510740314041c0d03170140480e006039004100d0600100d5485004a20190 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 157455350 1250 157454100 157454123
    0x50610020d120f0c0e030609010c0f030c050f0f0711030105130212010603050303010609150306050109170a140304090f0c05030121020d03030506030c2d010311030c2106100804 77
    0x9081410f9072081540d41c1c0105c1e074000c40c1c45005140038803a1f01c0d803081c43c51000b0040100710a1000308070560000d805024155220300c035040c018400c40407070b0503800e100269182d80f54148070044c5225032140d04265807204c00440100098907041c040c580c09040c800c8401d1142c0341031a02004002e1081940c0400159a10340c4004000346050000d94001c00d0951030721592a403400d074103101e0b03c5070399203070130000c240c500740090085a0b00041c0640540d50070309403441e00140d0035020180b5001c1141400341203403581500c414042d420000041041c0e4441e1241800201070120560302034882c10554000072800910043c0905880074480c0c02c0d1405841d04c001482e025650081400800200400d60000ea02d450400ca0706040402c107000030080141c03290768240313144c54480c01ca03e40c0c00904000f00c16035803440b90074980e84644c01100c00d0000621005641b410541d01955039a40403844401541d5410b030200c0c0c04004900400700d102c0d61005e4181c210750b42600c0001c4a8010380200704490750308600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 157456600 1250 157455350 157455371
    0xb0a030524011403210d06090b03010e120d02130b1201030209090303060d11040e0106080a030806090c040608040807051504021207060905210a05060109050610020d12 73
    0x8000158032080560400d8180c801c0d112100c4401100c160480d00e1804003076400c10b112a140011030000d50f540c04881d80d030400c03294501c4100e0302d10949420200040c107002c008291400340e40e0000e4056a011002000858030b00c4c2c1451303458040c82c4d00c0408040c0414882c200b50040b0725002080e0f12981c041d2602e0031135440b134500101c0e98000c0414110111100d800602c1142804a41a500144c14000850035860014001042246070b13060080407042c500814010760f0310740b900008115018403000340001b80d25414070a940350200c600550000e040b00f4040341080c10070406090180d0012420380c3e14250034900151822000640101c3e4800000c000f0400030510902c07134070114180401c000c20590902e40100300313810070b0341c2400406a800c20201004403e400000360800c0f00e500b40d844c0308402c0704140d8240c507120041000e000c0b5900980c8110000c00c68081042816901000803c0216440300b405002c00c0b280c909000c2c82c096801a00900d88441c0101e000000c6103070f0242002ca02c90208 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 157457850 1250 157456600 157456603
    0x4110411130315020f270a061110050103021507110a090f0608030c0706180302040e0706020f07150804060f0c02010209031e0703030c0f080313060e0606090a0b0a0305 73
    0x15056605007481c4001841040101c00191008292818055044c001c065500b8030070340c070814030a002d1200d036003003010420051000f00302d5207030303030006200300802c59880c200980740c80428420621103010700c19508184070720310701c80e0328187da4020340103001c05800045006401d61026034140d580d20340c2d040c6607548551310341b4000405480d041a01066800c1200d04031801e4070160740000502d074100740000c0f010328030000b80c102c0449a113480c1c142452585000328400c1040e20341c002075003003414000341607a280d0b40043c006040300d0750743d0300301d9030844c00303840c0402e460343c00310301803081403d0900300c480307001e240310b0240d6a81240c0174030b90000c1e8802c0101c8a10b400c8540d59003030100541d4002c1031002281c50306102860340004014042000c03003a201001700d4070740c00355010003010301010001e12014004071004007000707a584440039032b030741e42041e6444041c20710320000304480741400c0401d41800542c005c9030041c010340e0040c18071106a214241e007100030f005c40c22445a00001d5140000010480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 157459100 1250 157457850 157457857
    0x90c040f09020f09070e0418080f070506090307020d03030f020d06030c050f0f03060601050307170109090c17060109020f09060f090a0e012102041404050609010c020d0804110411 78
    0xd8280000689400e00e1040c031031040d8100050302c0c4195559403c001071503400005c5040a034500310342c00200780010a8088804c4100300d80081c0c0211000f10f034180006441c44000e011b030718092821203001e0350b103000d101903481c46442d0000f50000c004000d42c0e00041d01a8110070281503d0340e10141c00c2000800940c0c2c100e0302c2d10391052700c0d4615185c000700010709004404500b524020754102c0505c0c0300920101e03a803020060249810003100000040e0703440d1168502a44264900b207451480756559602c20006e00081102a1a80c64200c000000d441204800c0144400583d4010304841e0386031503c840002e41001115042c00c500c00c01c03502207141d071540010700100084001103030b112000c45003848103190301a00088070041d8814014400f8003401d10400740709003804aa1a16003602078800304002d812940580002e281388441804200040030507802c2c1301d00c60200c000c1003c00c7d01c5c03140c100d81d9000740c406158046001076010034045211005010350410300640042034052228070015017560 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 157460350 1250 157459100 157459121
    0x3090816030b0c040b190c0b0406141302010804060c05090411030108060a1104090b01050d0203090a02031606090506030c0f040e0403030f060506090d020a180b0319080909090c04 78
    0x480c828140100611080d58640241c1d00c41500350500f418588010300601c9000c01c80070901340c2040d411107609109842e011003040d030005043e403441c2024584140505000071015141c00d465100084940e81c14040d0007000c9074050b907402503036407225103800b8002c14030787d8485000c029080242401c591164014460010000300d03186640b076150038129420440d0240c28054150300300350040031000146070070b5800343c03810362500041e4074000b1001079030b4511034132031403042c1d00b4008802c02402e20404100311022500940940d2007601d60041d0440c110081400b41d41c01007115500244020708054000c1c542c09104066450b2610f000d81d8135041c41d0350440d5202900b00303c02c0e0801c0104060f07050082028039000c1880c00d1120604180000d40702d07010f074203240c5028111900083c01999070b1415440c0083c20000184000e1240403841c030400b030445407001501921806446d40d40d600d64200e05101001d4000b12220b013402641010002c0c201009407144cc000d20860445004550700e902c10444001d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 157461600 1250 157460350 157460383
    0xa090506090a05010e030403171305030a03050307030c170a020c0309060c0618070608060607020d02370e15030708060705030103060515090402040c05070f0606081e0c01030207030908 80
    0x5000c2e500e0703c43c1c2942c0740c01d07690640e580c1040c84200700164190503001c89107488809003c2d210040310384000d404154950050394580308045421050503000b078000c60003894a5602841811108502900c10103030540d00c84a1080c8103000007000c002070385c0d001d010510700702000e172807411074280001003450300040d0b08001d040e0400d42c01c0c071405000e03640600311b01011040280c4081407500c500070f45042002003504c2d001d0000001c0120441d940e01d603403080c1e03450b40144034180900c003950b80300c20030000217200e01c8141180140340e03228001d0310341c004d4801c0301d42000310b801d0550342d1200005a40c007464441e00e9014894081c0215503602c0910000d440340d8000e68450342c60f503240d4100901502e00180510700003980488040244d41c403009040d82d801501610301040701001501c04498510400d00302811400116980b40700300301c810b800c0390742210644003c4075035440c1140301c0b400c1d1400d13651b05070408a42c06100445601d5010350041c0001b18000d0510610580d40c4601032807c00000b0b40601c5c400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 157462850 1250 157461600 157461613
    0xa090303031a1306051804050604110f030d0305070807050705030301181409030304020f0f031e2d0c010e062502040e0303041a0106050901050304080f070302070f060203090f06030a09050609 83
    0x50906c0010f8085401240b0480c4c0d501c0e05180d1070340d617100c40014002a2603003244600540e03040c0c0302d6980c507580b804009012589030200741003008008000541d074500000c2d00f020b0110b014103129000f41c0e00740c940c11401844c41c503460810140c400f052800076101070540ca943c0141184001c058600d4460340e402e002459580c5418030402408000d004243d500c5083c0480c54001d86031800103200c08283c002642d900030a0328030388401d41c900b8000383c3c00c6024550880c0350f00405001c0c032507030100c111001c50040f5400c01c010345e40150798040390030034559080b1900303218221034035102c0078415903910142d2111100c54403483d0080f5040c0c81d65520360380001c1e480001440100002c90341440c00701014400d0340b9090754100b41300204180715484840d41042400300200c2c007802a2101143d482081c529820356030f13803101d85406925102140b1514038800242400010702d940040104c0d03079009802040340c40c03184900c07020000260006484e194845542e0344040b8001001081843d00904c0140004c292 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 157464100 1250 157462850 157462859
    0x60a030515090c09010b09010e03010f020a02070f080f120304031e0c03111501060e030102160b0f0907050a090c0302190509041104030b041e0c060f080603030a090303031a1306 77
    0x2500d0381c650070341c0c1c0c0121004c80040008400d07803420b540a07070b4000d29101c0420724540f0000b0b409400c1000c450003110380300083d1400000c0d00001c0800072288842c660800303696440c507c0c50780724035502c034800495030080d03125150740080c1d000045a0086c424104411051216120303524400e90380401640030480820002040c542c001400f8000d618a44000300390003141d04100719413244041c4914800d2015004c401e41d039981e07081d01a2400d2660101241080107054240001010f5080d240442d0003600c0c030020480001010420b00c09031200907001800144c60003003020002d00c000b03a800c00805600b4041d02448403940e0640006a80442d51080d413904800b00801c030403680d106054601c100700410003000029203081040e40e01c560400d07003000c8901020001c82455404580006181c0e20700c403c000302d02079400011740c03400f9020665900d16242d031004103055903489112031a9002c84c92100b820000240711347c00401c2452101d00040308941120404204910051443d02444076100c5c1c0c030910 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 157465350 1250 157464100 157464103
    0x30702150903090a030b070e180411030f12070201110105070309030f0c0506180a1e030801062a050c030f0102180105040f1802072a0506040503070e060a03051509 71
    0x41c0c00101e100059854040c2c072600007079561107184002000941c1180c0007a241c3c0c0d0107850030540500e806020800000c01d1421740300030291044508403199062000030703044a0800003016907000040000400d50400290f0300d507101c507040041c04038100310703520800846504083c0a02e9014090648003c515400350b861b028180c00c001700c4403101040014424100816400a141600702081314103d00803130300301c20000c50030000c1c0460007070301d10818644101000300c60719001d00d24180c082cae40c1c1e403812640c03100c03806c81d40352290903030342c02405034000c00303214107003840300e40d01251580f00e2400c80f9904039108004c241010a03804644440741d60100700091100c10351141012006024070f4824600f5043c901d290303042e11024066103d8003c4080c0e11001c11085542c112819541c00c851410154115030342e00c2c1c0b00480d81034240d142d0240900c00c0000e02d60600307006480030344100a014004060414190b0440c484000b4102c43c1c0c04a44aa0004003269050103511401061042e03154002e191550906 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 157466600 1250 157465350 157465393
    0x40305010902090c03150112060f0e0708010b03010b030f15090126060105091b0409022a010908030601050a021c05070c060206010510050c0a0c0e09150c0901030b01110102030702 78
    0x3c1301d1130042013045064a20340d400300100b001c003420880c10694040761030000901542d002440034005d2804e0215440c03041220240c450480c9a45446a0b6030300c4410706140c5010a1250f5000341e00280003050302e04030110b4115621107913000401596284480c00a42c1907842a80700710f150b02001c3c28852240e15010342c0000140788194020011949080c011803c006402019507000168060031420f084d602034003190000e26801006540b9540628409408444480724029105503500007048120380b040c0107001c40c041d0001200c0b419079071102c005440c1c40c0e0221203c0c1d41103002d030013907d101c0c5030206c1403008035010869580380d4841490340b516003c456400d8100106540c85400104010759841d009030307419004501d441600c0d40c8038810a2890201c266000401d8907c0480e008201f0150400c1d20600c2900e6620803200d032512802c101c038410200a48202042c80000c0007038444d154000e03040014000e0061604291920407041050f08a80040e550400140c00c1075800c40808000c54025 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 157467850 1250 157466600 157466611
    0x120e09101403010504021c0c0312031e140703050a0216050f2b050d060510030e0106050402092103070b040f0506010b0f12180106060201090606060504121106090604030501090209 78
    0x2c203c2824a60001004401f5041d82070011040c000040e20401040000301c0000719070200340351100e40040c0c20041c1c040c1035105420a001c04110484440820b40e5008001c4801105070502c60b90b900e40c400300318060071000300080e04c41d80c2c003001280741c410114158501130a01800c0a8031000340030001081c20020509070598003098516945c1020b5420240d0b044040b44260400039520028180c068010301682e921059001e007480f007446810382c1d0940c1049a5890400c0005c01141d178540c02004202d0007003e4007540c02039507600c4000100c080000244201207000340490b030600000769202840f504080704c046820801c1c650f49e510420904000c200e01500c0701001442c104920b17440300c003125000b0104004a0b140b4590040b41c0d210190348201110035051800a03c40c1c2a25544040d02030a200c0303000300d900743d1508000140700c91050041d1070942c0c9810300c580418080341d0702c654603104564007100e68041020003c1680540c0c4040082c4001c41c03141c000420850b00f40e004201e480d0760f0007040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 157469100 1250 157467850 157467853
    0x80604150606080a0209010207170c0a09051506091f2109080315120f011a03030a020d0f03060906030b0601030f1b0f0c02030f0610080d0c120e09101403 67
    0x1040c0b02c0c0c40e0700044180d5000c0a400ca0040c2c46903a6140100c1c83c1240b9684001101c030289100418100c00100e9829a074003019189586c0c001c0d07071259908101c800c220703091092031a110551410918103c001170010360b80c012300001c10301c1500d070600500c42103501f00d01d801084211180c1d6030340f010609850020204030020400091070780351031302412848010807038102007034525118102e994450140480200254049911310300d44210954003c1c11400c03040d50080c903259a00000518001049506100346030f03014220400b12b905043d143c02c001e80344c5e014203160329980041507600062013003c00031030049980f45c2450030080005800c9580092540090508101d0002448110031000d1000e1402900d00600c01000710b0790111041c00f10240007d40c940650a410100b954001a16900600c00e50000200712035503020303108c0c0d56108010144000c10820943d100129a03000d01b1258440c0207401c0102c2204c2c1610700050480400b1170364403c10b00c012843c107000400d09240c0701c1c1040d120135030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 157470350 1250 157469100 157469111
    0x604020a030602070203030d0606020d02010f05041203200703020a060c020102031b090a03140f0c0d03171003120306060e0103090507092301080f06060114030a0f0b0a08060415 77
    0x20003282a11249000241541e500000d2080440d201001155428088032000308001510740100948030060882d0520041d8207004003851170040a104440c0904e138805003007254018204415009131181250820700a0049881d144200c007100b8021b1091074820360203407003943c00d5480e14004840c4030034114000c6a1040c002c00140c0c1c0420310340e5024841d10003281c6a11303101c6010002c2d80701c102c15000101101d04141640ca0304801c0040d180c1350580f0000192031031181c0700001d10002203003c11002d00040c2e9180b10441e0440120059170750855428000107640586035101c1004014460002100113541d40c030b020400f2681c0000c0c0001068001d11342030242d54059210291349100c0c0c0c0c059000c047da03131004501c0b00c940301400c0703807420400c038604510007541e51003030410b1322100c440c14003000b68000d0b240055000c0d80701d02c0b414100242c450060a0550b280c414000004040b072154a0500c84c2d9550004251580d0b442002030041c40032200609a52a00d4134085034544415500100c2450522 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 157471600 1250 157470350 157470353
    0xe070306050d0311010f180b0c07020907030b030109120215010501020102180f13060b07050d080708010e0402030a0b0a150b0901020304050d0812040606090b2b03180b13080604 77
    0x1004402d01a8251901e039208180e001619801085086080c030141072030b02c46100020035410751171031400c034066070001d03440d982d070703440e004200d481410f1000750300001c4a400649294025840a0700b20100078000107071400a95981d40d40c607003488801d03100944d00c000c2e860403a1003005540716000d41421300c025402c0052034880d0052424903200100d20072440303070300c14034050b8070390801c41072110211560a011480e5104240798480d44591825941c1e401118090b1422600410b015806100c003036480015a84c41d001105400700c0d00540220f078940121541c207004200e842103014041d01d0800300c0010b0b00300741100000d01e81841a402100c000070103021800040c1e80100c2a50b04440d0103490302c126901d541e11702401184203041c4c490300a00d104205000600c00640d11130f03001e440a040c03081280300510030070407088801c0305503d00c1807054030000d11450b001a00410300d03201446400c06601140100c0440344019004ac0c00660801314007190015680c3c0060749503000600842018040c02d00f401e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 157472850 1250 157471600 157471609
    0x627050604030323400b0d1b350c090f0d0803010503070f030515060a0308040b070309050405040f1e0506040506061f05040b1c050702100e0d05031b071b0e07030605 72
    0x34401c001c8481d0001c50701c050380f0101d603000b0742401721082d8445084540780d02c88c0a40145000140d030300301401c1c90445d44959101d1824030780c0442076041550740099030740c4001140c8942c008405a0342112401ca40300e0015191042101d2440d440b80c0c950540300e604100a1518151140d800b040e41001c84e90005c1020410209040713528402c45d04a444503581c502e4045100c0c030445500082c80d606c0000b03000140c20004001074201385202c0d030b0710b103e159a50b41c001c02c002c0e15401d5130007030401d000702030444000440101c0c00300703414089800c203c81401515240c4504040080b40e050342c1070b803c6401001010714081501c0b4000c0400c0d56032420100910040050107401140980207611368001400003200c40b801250700d00e1040400e2040c440c1d4505410003e45034183c0c0401c002c0304e103007400303940a0356580101c6c11400000140c1d071050704596442c03807842000c011002050008140420001c0089150852150716a27225920028006803818030314481a150041803031007058074000c0d05100e2590b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 157474100 1250 157472850 157472977
    0x9060b1c02090a1404031d01050301081e120408010f050903031603110f04060e030105061c02011407060c050307020607020703030807180b040627050604030323 70
    0x40542e49024140d031402071420080003100c032070b43d120115840c100002c141e44100c469895501e2407480e0161030344480c0044d5481d01081c02201c0c6150030802d9141695000d4038040b0700318901004c02c440c16006804d0600c1d0b03050f44035802c150404c1e5180c02d66081c0c070240a00034135420441c0c0f58015495854103144010b0402c0405001c6010162105200c4100306084002c1d0f41d011410720b80702d244d40e15036990000e440f010a0051541c000d500380346c00101d141c03408030f500703405444081070500b903460b4042d40110340c284800c1c0d065140e610400e0042e800071590510401c0c03480803c60720382c6a40d908150130040c0c6440c0d0000c003000c0441d40150700c01e1000a91000301d05d40c02403654240841c80700f00c014988040040300d500851032016001c1400210b01b58010102030703481407028281d001c0f164011000c0c0740503c8060280c160401000c00007000028441c2c8003c14010f02564042c1020280e2401103803101d80c040078030780a4000740c2180440a1662030f45454150609542c0c95004201c0212414800940c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 157475350 1250 157474100 157474103
    0x501080c030907091b0e010c02011e020a05010c020703052e0e030d05040303060f09050405060f270705040e0d020607180e0f04030305180703020d02040f0c0309060b1c 73
    0x200c0401d500360b20070410350010348110203050154a511500a05104e40304515920000b8415114000a94050081404082c1d0182d42d01c0d0ba2911301481c0d00d00360b40350020801d501310300c11000d400c03010030801e00c98414076481da41e01400a851031400c00925020f51070107030150350400709014581d00751286803100800c621509010504e8200043c12a0940c02200301112241c0c1c00c01c4104410145e2647c403aa00395504401c184a0586d16000c1e15800c42e4022640200198031060100d5400e01441c3d40e4031754041d46001405200300e103032816901c04102d0b440040060780c1d00c150400e10031440c1900440449400c20401000380080c0f40000a5445a01a001c03d05100942390b490100700c0403013074034802821105c1e918000505000c0480001c0300011a02640001e25000100b6086001e5501c0d10100040c000c00801c52181180c081040c00c070501c00c0300326031041c2d0b0fa400e030403a0341c105030080d032001085a482c00690700400341030030401d0320210000284203101907000c044480b01800314890185 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 157476600 1250 157475350 157475371
    0x30204110418151203080a1503081209071719020f04151a131815080a0203010b0108072a0803010e090f0c090612010b04020c0a021207050108 62
    0x115040240d00c5914403840d00031107440c091001d003000662010781c200032400d091588014005559600c2c00103003a140c4c1180003000100c4d60000700f24042d455070810f41165400e46a03001c0d580340c0e00c0da546003003036101500344841c0340000c4080045211050240f100100703080349420740d500146181c0c4945074020740200e82081c21031a8410004e540b55020b2083c0e170200040c204011210066803c0718584155205100c0d240c8860302c01071414885500075603600c2c201c4480c000151300d0078540c00e0705507403528041042940d5076403554042c400c924400d411006041134000380c801c403031050042c075007580e21038042581030004840c1440710899201c0080d205881e040c0055001c034840c0c0741258403014900d0580a451150080008a100c1c1c4402805601840c03c40044a00221240482c0b94603000502c4606a2142819000078650f044c40c08509032050a0f200000481c105003400003030807070300940038510680d808a50310300210700304000c0c0451150011001803915503d4480001d206c2c180040c81c18114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 157477850 1250 157476600 157476611
    0x10606050a0f0f0c0203011505030c040e1c02010b03160e0601081501031d03030403090f1208040605030c0d060e0a06090203090a020d0f060c0c02040506010c031202131e0306050603030c0304030204 86
    0x720344035000d9079204c00d600030700a01990350900140810841503020f520702c00c0c01030381a40c8040d0b1602c1d2050380d2a40d040000070309550200310300740c02c501400805080055540b51042c56103551790034001110421186040c0502da1401d140b0a241c18480007805c0506100f0740f041408152940020603103203021092a02040c00400c400c404042c007280800304108a100c0030050004060300300f07a5401c1079030100400b90780b00d01d0392a003201e0315441c02e9640141c0181ca04000a014807841440250340c045440003866240c02c82d0b1400740d02c01c40c0e4180d88200b274280c1000091001d024010b00999000701007808065045041c1501655190060168020b201c0c420750250740b010080c6240a04e920a0707000041040030440d140070103040d040d0301c0c80040b880740e46000f00203003980d80203400210a250300365841010310642c0305075200080d4400c80c0a0081d0b8104000c0000d6403091743c2d24040c0c480c1103c181b000c150180307180740c00c501b5200e010301954400e4205009180ca1307004000160381c1220b030100c0340401e2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 157479100 1250 157477850 157477877
    0xe01031a090c090d050d020d30021b0109030f0e010e0f040e10020a0306050105030702030d0908040503030d15050a03020d030804060f050a0207030207080c0d0f110d0c0305010606050a0f 81
    0x90302e00c101511150050001204e000a0103000300300c10380c903030440d902682d03100c049011085a203820340749400443c08842c8291203840010b0380d1841c0840e28408480103203462181d413401009440c1200c01c507242a034507054001c08140d80101d44d170a0901085c202204022640c400182c0780060803180c0c103001d1400d101c00c2c00e01590f51600240700000040382501c552102c6040420040d5000640c4280840c0c10f00d400012a9446281140d1084a040d405141000c0b04200342c003010b82211041a9900c0c4020720010031140e07010302c01050741000b01080000e0f11035001e8050f40c01c01c1101d91140780700301d240032420000344c0c4501d042c0c0524150b040c541044950b07500d1a250005151100100e82058540020090612000c1e80103003a070901980841e03201c2691080f120b40d4400301e405500e030f080340d101e840400000d50103065156a4511800f60000b0107481e0034003090040070143c0c030980324101c0c03070b50302003062040038402d40700a4202450020b141c00101d540c05131411101460075000c12803110381514 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 157480350 1250 157479100 157479121
    0x61505090312030708010303111c080912031f0e060a060c06020c06010605030108061503070b0a030902100302090a0605030708070c020102010b0a080610050a0302182d070e01031a09 79
    0x121904002c00c0341c50381880c4100508981090000b03c0104000203400304182c01c002a15400703e60510b4020402442c8408048425690152039100c6901c594204d00c54800101d10241d4480c100b42407948101c0046c1c0c42c400700c0c2e08801c5034020403d000203002400700e01d07140c2015030801d9904030308250175092618500b80000348101c0c0b019000b58007980e03001252941c4c0c0000118100d5028108a401580781c00080402000108181c9507040d841003808212607806074028007511485800c0c0001c03004225004a200c00c2007130a040300c0001c0d03000910324154a00441047c001e0071071803409030704620700080060021180a01054240311b0b04049a004580c03007508003840d2520058101d1502e2580c6031030303540d50f4260540d80344003410081003000c205401c0c03c03009081125002407030114501070007444108003c001601100b0f20744c186e00003440c03d02145191080c18002080003e911510f000b600c01031002c0c0420917440d04050802150303146c4001030103540207420b0b200310343c05111501c0762060074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 157481600 1250 157480350 157480363
    0x6030204080729070b0a14090705010f0203041d090d09080a080d020408010f05070906020c010c0b04111509031b240d0e0c092d090a17030a0b01030615050903 69
    0xf42c0100000203241010042801402e6002d0303030039444180b1922100b1408445100c50407900d69003240c0c41240100316642c89820201c04415503401034074a0181c030b4035404060540c140100300900b45070b910030300c444885c0c00c20056820540c980750584501e400c009003940c4803144214084c0c02107001051105220410303904880c010081a8001c00821a10050440191404503403000100c2c0e80544002803190010821020342074050f55460726111440e502c1c451482c40107841581c42c4600089404503907212100249840b607200b11501e82c60300701007001c1510b400c040104202c4101c0075608201c2e101d88840111a500d4482c041c01e4920010032820310010a004414028a403507003051502000c1d200d02248404030000d00750b6400805907200c109030104c88101c49155020009618035034502c0f000781024982e00f00a040042d180c181e1a183c481e01c0d0316040320340c050104d0f1b075400028080913006520800310100c20a003802d20030b180c909404c0100b80c408111040c0309207c00001c05d42e83c6940e0a0205 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 157482850 1250 157481600 157481669
    0x1090504060612110a0e06011b0f1a1009020910050a0c08180a0503070b0f0a030e030a0908010f0b0f040b0609040f050106090b070503160f0b01060216060302040807 72
    0x103411490401c1e0810b1320f030082040150381d010700b2036000082110603040c0300c22403003240c0684030102c461060001c400301c0440041c00c25900080303250210030004440c0d5010340031700c1540c680b0b420a941400b6101c500c0c448031503030105180714810489003c1c10b859504041c1402c81203410002c0d1201d91681080e00d000c0424400144501400a96018843c60120203031404030420b948c0e5109541d1a203091554511480c000d4a44603c001d0016044241d203600007401c0703a0300f20f481c02040c0c041c00d0b030620302c4c9540c0010b42c0c040f0110340c40d0b00084c49004030903c660720300c0e1001504280610715812010400e08010000c5145c0038a441da01a6540c0c1d0b101c50382101d0500780e014004000010600a040d4000d15003805501c001a507819400030792a4010401d540265030400040c6140c000307034540740b8031a42c00354117088800d440c107800100041010310300564003c00040c0c0180c41502c1482c10720020421140c1c006a042c1881400140424440001d0348400c0d1184460007140084c1d01000504140e0001100d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 157484100 1250 157482850 157482869
    0x3071b14010c09060e191223010903030b041401030308070311030a02040806100f0905040f02031608070605070302060c03090120120106030b060a0e1507050a110901030506010905040606 81
    0x50880c8043c0d4009001402c40d03010381d0f00c40001c900d07064100301e41c504800100e000302c900d40a40501c03c0d107540922000b10302d81700794807826840410b9001c0c1011045101888d07c5c1030f941d40c4c0c641c03505143d01350041c0d0380d080d0405c41c3c08021960440d00e40135000001804007808002d541c00003d2103842c001c0c0c0c420501080b1079080329440746490300a0501030740c454058810350b4040e5401140014845140f80303000d0b5515403400840850405000200038a001017082d036210345540014800740c0c82c140019042d0342c8414014116a60820041c03510701042c59114038100101045580b01081d804650305d6004140051425078903195141480c3c0035021003400d0040854140901c1c0940c220302d100207150504141072079050682ea48c0350306a00b200c0980b0003e541001042041103060f61082209003040a002081c040c0003c80f0146021402d801c5490201d03983e6202c04040c81c140040d40d04e445084000498074000c6941c11035030b4958507280184140305140d07881d1000328040003110382040014200454 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 157485350 1250 157484100 157484111
    0x191104090c030611090108160c0b04030810050114090603060a0509070f080105061903020904151203090b0c070e04050c04020d02090111011b1812060902130203071b1401 74
    0x3800a03000755a48021070340306291003005511504144103907090114140c5501001d03617610070100341ea010340d0b200340c10100b256104500001070710a00300316000d03034065551040b0901e0007580403000041e00342c12250601502c0e11107400da024501007114001442555200c2d10380d1a0400416080003998100d00e500481150410036403a80c40b200e00c41c800c030380c40e690f18440da99994050002c207105a4200e504030351039a1070840c8219029800408901502030400a481100341c400010618402d811000b060300ca041c03040000e040d402000e0101410b2002c84003840c103c00111410303a00e00c050320400c03290032820070015050000a10005c600e4800140042d0f646a10100700c40000751701441040c0c2c00314640d031b454185054814032582d42861021000170b1200203001e4025908021342c0e5602010051991502003120384030b81004860b1184030324008210030704c03148100300c880c58070000e0b01200c162060080002d581e90040080ca800307149104c00440220042c02c0041040054180d1010550700b0038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 157486600 1250 157485350 157485353
    0x604140d05030d0c080f011202100e0307060e01020f0606090a1d0f0d091215050a060906090f11130b07030e030316050709020f041401020a0506070206010501081819110409 75
    0x350000713003c03003241d5070321010035035120030500c8400348080c052980341d10705d400c55140c01801e03c03070031205517204c007030500150a9040e10002071400429800c00390004600f0032414413296010042c01d0900350103075018003c24689180807a100c071000400090640c0d840d024650882d031442c40c41c2c104032500c41426252010a48901580c2d5110700d00084800501c0741803001688040c0b00701090755559000c014040d5102e6011141c00c00b03060044c0032500103d54a0038001864007103445514000d080c0d4650100f0514081c0c0c10407021140301c00c0301036020a8007007003114081c002c500b0500c419290b2b42c010712501e400d030505003100c45a18052809425210004a800c1e0101505008010042c401c904070783d1500d0711007101c6001e03400b0314990980f1140042c0020322590820a2086181d00d0307041c0f0484400f0f2a05448440c40d00c0c50503120100943c010000500403540e00c01700762580850280008030494ac00d01c250550303100d803c21803400342d42030b650076100100007640e4100302a6030700040080c07003aa40c00b03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 157487850 1250 157486600 157486627
    0x30e121e093a0f020d110d0b010e0a0506010207180209060d090605060118270c200c060301030b06010923090f0f060d0c0317041d060604140d0503 64
    0x1201c000601018450324100303500342e50070340703200b419030b03100000e020a040f140d07007030080c01a4140303000c5031991414180500b16445a003402505a4050301c0740100c00c1d45000d1403010204000340640e525030742440108107031a46c0000b440c5084075500402082d500000c2d41c4034400a00580d001d581c0e200d88006a800c0e00300c2d803a0740140c60040d00500c010822074a407200152256130b01d40844456800350071a040144000c080006a0001404c2580b905c00140d60340b94a0b040344c1111908401144c1e818501461010400e51980d0742041013200030400d032408640011214001484020881c1e607030540090b11070f0344034611300d8005140304103120306840d4400000200000c410780303200303000d0b0300782c4800240000000d020580c081d0688200510241d00e41105225500c0e01c10003042d120ba182903200040095280706103024a070368465038040d1614105400441c001c0312508600c0c0034540100284019075440d9002c42d41100d0020b001d0316440621940440c0e4601600d60014165000105403590140365 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 157489100 1250 157487850 157487899
    0x9070302030312040327080c0306010f0918150204080d0807050403080f0c0a03020708120306090f04030c12030b0109090912030209040f091b0b1303030305040311190201030e121e09 79
    0x11240c068030411023013041855600c403424480e1300c80c00542c11a0400010b50f5a074080c600840d07880c2000c1540d0300e680c1c4c0302c4084441d651080307919480e5001404005102c018418034814034001d02e02a030030f90400c0c1c00010210301580c00054144e010010300014060519401c0b28075445056054600c041094100651101d00300c0c407030000c16009841010004a0103241100e200314030042c0801450741750320800c08880c84000304124103101d03944040002041d45a4500c08142c001c41c0c0d00400c80b28000c00006000d04840e80c00444c8290524400340c000a401034103c03860800c040c540140ca80c1e01e4880041c2c06002d036a240000302600c0c00701c1f04824801010144a85201030a800341c001c0780e507416401e801849580c9410f9100c0d02410300070300001c2d10a0f00301c503400030f020349442e031540c900c0c0080490070300c10300c503e10f40c010b0480380d08402d04558260091001c040518409030160940e03034138030400b41c0e100340c89800c0712402440141030301e000080001c0e55080c0c1c00142003038011004544d4900440788 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 157490350 1250 157489100 157489109
    0x612041509050a050708060c0405150c011e09020a06080c0304060c050d29010c0c0605030703060506030705032401020a02190b03010e0411090709141f120509070302030312040327 78
    0x10700c2001a08e00c004000480e01144c1000d4410301d2103404d029411859900f000d0800c00065490313a011110304520303580ea4018a03080d0240004440e8854410821144000d0740000180b11030141001915691141500e83c0690000f101180302c801c034190844103441017008d01c07d1034074540310300d08030100002d103400f03001400503a40c0b06044188240065499020f0618020801000182c0503c46103103e580a56003141180c140440c8840c1c850002903811f0304201d4414001400200801c0074045070122a09503101c400d4a03a0f04030101c0000000f5140c401494000c0d01030112020100c400c0d0348000c04c0a00180741301d65086441c2c0d6100c0e03400580100c03064030181d507071a642c0300c1503041e103142c84070314a80594104e4403000e08503403a050314404803031103001483da84400d10104040300d180704601d0b810000242580c401104044681c810390440d8805002d072032071035000c15414030044c4c038000103c82c40d0440078143e8000b40e585e5481c1c112529203d040c1d4116aa0f00c87e00c6850b035040e440d82c070012060701c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 157491600 1250 157490350 157490353
    0x70603060b0306150c0102041208090301050a0603050304060309110406150f020d08181905030a23030411130c0f0807020609060a0c030b06070c0509060612041509050a050708 76
    0x255601c109804080c001901c480390f00031041c81c04140306501e48030061409040304000541416625000450344481c410000da400740b00004a4400e180340c284070f000c4d8820704041c8204405801d5480301030303690145004590a142c1e40f422a0018412a0010441e40e9030004105201450702e4008a51014203140704d802c0120300d031019070001c0d003030010038490000009039a0324011946c0e4107100100c4400d41510303182060241092140001301140041100e5034000d400640d03031440d60080040402016200100080421000e0403050b05555011a074010b90040d4404082204080024031100e542d800d45507401458882d03440c07042a0020b41150142602e600c8011302c1c0d68a8141c140d840f003074100c03000100b54010307c0002c1d031110b0a1364004580340d00301d864005038426111011030b45551000400350f950a80d0300ba410011032031b0000703a0a5011030f0a0f1038041c10b0005191040001000140000780381070b0b4010804407030498a648010562a0041c08480b0880c0b690f0800c161251260b01480700d56 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 157492850 1250 157491600 157491611
    0x225030b0903130b0f0304060b06040b12150a0f0509060a080d0906030b0a05100c060e07140f0103110d180b0a05060102010501080d050409020d060503060403020f070e0601080a02070f14070603 84
    0x304ca50003040c2d8000d10b881141303041c0b840e5107555034140146058000780f0b520900c10b20003c2060740442024080d00c6034891013035440740c01c0c4505414581d14202580038818a001c16060206e41180243d0004544040d2100c2031036480b0000020000c82061300859003d1080d510214482980121500b00301c0382c840e01c0800c1043c0c000c40c00d01c040705070a8000c1e0f85d0000903501510091911480307540080c43d0082d0000a00c4003840145181007100b954800140110055100f880174030380420505200c90090800300880156604005101c0c000d590822100544e00d524140c4c0d80e54621034109002948912110460703e000400d550042c5000ea41d582e00543c64880085640800001c0402c034484064450341e0600c0e1420801341c0c0a035001081215186458920001d80d54400304882c42c019882034020b413480c81907451089181c5402640000120400c10013031100070790f0016103c03500b00703182e68070240e50b902007400c02d510081d118440c0101a012806003030f200750140800c540302500d1540d45d0a006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 157494100 1250 157492850 157492859
    0x906181109040807120e060307090609080714100207030b0c030f09010c050927040f0203100204050901060c0f020d03050c010c05040b0901052b020a09150225030b090313 74
    0x20510400c0360001c0c60110100560001728220240d41400c03001c462800031503c07003400021940c15002951030401240b1000d41c10310007541c0106d03642c4041e0016000a00c0741c5071a08107113044502c881d00003140121309031001c1583d030303510a2210002954103c420301c0300c1804d02030b000e2000c41c0c0c0110b886182034034824001c15902c0070107016400f0f00c00c40a9031090b003040140302c10410280329008440c15442007000e006d80d0b6103100450014415401107400a443d1b142a005050a04800780c604205c550310400c0240416a03e103100d0030b066800a2400b0300006e80345140c10501c4400001c0d01070740c001d0391a0140400c069008008003200e90700a0020311503805102001d6441c0d001d86c2c0038002446a090007501c117035507c00c2014041184401c040303550b4807010b400403280d0680000d4000704c0b60a07000140003c40b544c01c5080e0720b0080c400158081100c00c4070500080d1203100298400142284182c0400c01824402080402458000c28042d101d8100b560707480d6501d80c0580c28000008840480015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 157495350 1250 157494100 157494109
    0x30901080c090907030209040e010f0f1b0903120903050f07031103070e06090c040e0132030a03031e1109040e0c090a0c030908031f0e0610050d09061811 67
    0x10b1984070042c241503215220f6800c182d01940240f591140c0241d07590708040c0c4080c10034050400d212006a00000306520520340304800d403032100354124900911020203000c40d44d441654801103d8211001d25803185042e54104d4405040740c0c03001d0304510400180300c08240011035600304503841a00f07901d80002c0c5440c24917071503101d80e1007000e003082245000030719039040c0000100d9000111051007458035481d07100d0f40300402c3d800c0e040b0310041200c020b00b08002c0110751024591085c1d8505a0f0310203c01d000300000d540300c45040f4014100f5407504d05042c62010341900e04010007146000c148419100329140c12000d0f049074440034490390a194000d40d00302c00200714420400f01c0649050b0032580c07954101c0000e0548155040c040555520080d00030481c040040c500842c441c050307a203001e014003848605012040c0d0009040821000c06100041d40c400c540c40480f90100e040441d110074107007050100510144402800450410611000a549580849509a100381c0e89099951024028030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 157496600 1250 157495350 157495357
    0xb09150702070b0904020f0702150d0f02070f03030b040f1802010206180a03051303060f0603060f0b09070e0a0506030103030c1a06030a03080a1e1b02061512150108030901080c 77
    0x1010f1204080140c04120f040c1031700200f141c4038100304150715043c41039010418814001d072110041c28004074948041c49400d001d42203c481d8541825410a415600c4541200f9401d00004060560311056418262030350382001542081e016000c0040070000340c4403103403210030507400300c0c0140101d100083e520f451014205d00010250001480302015540d4240c40e5039008041031704c81c1590071440000000c4c803034000d589002801000115040b883c1d450130303009441e40b0046007001c403400c0c0394000d43c00792908607a4541c4180a4544110b0050446022504403001604019000900000040300b850340040c4a060302c0340c4a40c00400707507a4901000d02c8404101600c0c01940754000c21a11004070744110000c1d81c00c0b0380c0100002410300c202030003d84800703800444080038185c6490350a070000044a14a41d081d401c035002800e80e070b241c4180c200450b004d05c1d040940c401c00070b03c00d070114006810005a074581d4116804610556118130605030b81e50003209040c0c2c001400c000000d04004000702c1036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 157497850 1250 157496600 157496609
    0x1506091412061b0d06080c0a05010305070c110a0906151701061e030b100c120512010306020a090509070206040516060206070819090305040e07080105100f0c0b0915070207 75
    0x3901860b200da1101d81002103c0746402403448005124030340035030011384145001031a20900400305e0741d40341424402c10810355817205050601d0034080000c0c01350403500c88680540c0c8440d40094490742c0034001088044507800400c88240f910102191001810401074000605034440000010301101101c01840c0700340540000070742e02404102540440202900140040c3d0070049551a000400304844507060300c1c0b0034000554009084060000c60780c403504604205103407607843c00c95201e107031000d100e0f010312000703140c9540025022380342c030f1196420710050400101641554101440000d50319030b0160303000c6d2807070f024110342c00c9141071582c1484400c03112543c02400050751480015603c1800080456609034104150b0214041c0f803481800d074100e110b40c480980721030800460142c40d0500070040c2043c81005c00040c041ca07540d0b050001c0d0004182d14005510201c0780000b212505558240106000f08400900811100100c2c1d201c181c040c1072025003281e40c2d01e00b402269500040c0c0719 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 157499100 1250 157497850 157497853
    0xd05010b04030c0b090307171501060207120f06090203030301030c03150203130b131401020d1410030210020a15020a030b04090809040b030c0a0b0c0601090b01050307030b041506091412 81
    0x1004c10211400d48007509403414020f041d0b5a0380e81c1e032082e482c103584000c0e0401c6000c940002c05401040092001005d000d0700c1c040c40144541401c292000c40c40e1015000090124800d00c00b08904002460700701e40050b0340d025040e40c5d201e50303481c80c000d250482d0b81d000450b1039491184990041c0c0c03005109682c402c00ea0004000341d889415203072a265190080c110402d070440030b44642c1c1c0410008070605442c1c0881100050307440f0441504c003000c86501d2041c1002c82511803080c409040e040d401d0710025a90115400440c0c00800d840581c80d000c52003100901b181000c00b0409000c2150394080e00280302d4603202409441792003c02c200c11248103030802003005130140401c040b00e00b8aa0b000c560305040242c00c03518100310100c0013400840d400c0d440f1008400000420300c40b0302c10144800d0b4010100c45034140401d1710050b0009e000e9010003090300c0304140c0c1d01c0507010782580d01c5402c0600d44030703420008a07080e103031161001040c9609030b01405009004002c00e100103801c15081c000d00d002c03803440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 157500350 1250 157499100 157499123
    0x1205011b0504050102331302041e060501230c160807090609020913151205010c0306060503040f0308060103090f1412040b0301140105071a1017031210080a0303020d05010b0403 77
    0x811203550036800b90108101c100b4007c00303a001a1145d00c42c00c4458070900840f1303903a51510044120544055800190400c0408540b501d080900d2911989802e0350001905444000d514480c0780380c4003080c0340901410090420000c0c1d9100c0c046840815a007126105001a98555122005a100703074640035421a40c200742c10010440e03240e0020124500380c075210381801e907640e600384001d03255015007078650341d544030001200b07150548145030040040c0e050580c2189002e880304031640311b4a2101030140552400000d420768465070021807200c8c1c0c0441e45c14070035052801c1000c0f540c41460468400b031710030f44504031481e000070390503142112079400101d45540e082401c2d51001000342c5411a0501501707100b03000019810740078010107000c80880741c01003894520700314054440c5560080c8040004440324441400d404400c4071349210800c160118039858514064810340c3c500c2e0300000a6006003000300d410968560002c251590209100b8000c50340c03183d45a081510940c40014107144200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 157501600 1250 157500350 157500433
    0xe04150b0711040e030409060e1003080f071106160c0501050301140409080405150309011103060109030b2a18040606020a171e041517011205011b0504050102 69
    0x1000803001e02c09024101244122144840030300d5500181c010790b10f4140c503054284155804828040e80c415000008905940c1c5140c0302d0703600a1241d10002c000b034200c0018100d0500c171140061045a14018003600d030fa4580b610b010400389a00c0300340031242c00702c001600107130319840340d802e581c142c5150580c542c40004900f000c001c0100700c0703000d003113903506018080056150703116200200b503034056140280d605d281420b501401c4403050780c0c2c5420016010b109004103668001000780950358000d002c2402515901c86540a2122070111240700100d410b0704c4803c12010035018012141e80203010100f0740380f0400c200801e4409900075040164012718195011511001441c5071403c002200d0303a1500138a05184110302c1e000100c08900e0f800000b40070409000303c2d10702600f49582914104503001c1c80b00c0c11200c000034040c454080450f203c1819201441030a40c003128608040303e490b0558070f82150300181854006104140c0580a094245441500c1840942141800c0240405111a0300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 157502850 1250 157501600 157501613
    0xb090f0c16060b090112120207140f0103140405011d0307050a0602030c0c0d090f0504050f07030f0b041a01020f06090d08070e0d030909051308030114040b09070e04150b07 75
    0x5200301620481d441c3c50741085542c55100307005002e40350802d003610001d489400d00020f00380454018400315403064208101560a101030100e03200d0040f10391202000b410030040f0003030018001d581144000c06820700080200c158884500803039241041c09421901442c407a03164004e0101c05801500080354403400901c0d00e6000b194024195000f079030820040c100200d29028040d407540c004146001300500c00030070541003200041c1805c81c0c051105162451103280b610720090b101da82896220300034010484000d4012140e9040003800420101e207600d07140b0708441e00502d49460240c012410004103000021402501c03030050322004003c1c00319140412164014020400c900300001d2186220999449060100d49207000740c5d1000c11580c14030b0340700302c2241c0700038100d0550500642640c1c1d002411a00c107407411507040031000a61449580c0204d400781c0822507107198460b181a00f009003ca070003101c00e4268030030603107007000f038180003000b0440e098806000740f0b610140f0a101c0100050079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 157504100 1250 157502850 157502887
    0xf0109051804140a0b070e04020703020d120b0d0b060901060201181b0512060f0109020c0a03030504060609181104020403020901050613170d11070e040305071b090b090f0c 75
    0x8180c003e4040c40211907206410302004800c01c9030004081401e1015041d4825185c20881d802207c003185842010341e4080c1d50f5038a031115030018081040d80c00704203503281d64004400300c2401f0b48078180002c594600310903150030840300c0d14400d40c9500c0001c6000fa1051048a051010301680c601c0045159240d001c030300581a150300020659507030002c9170544882d0100e80c1109140c00040042e418960401001030405030400c1c2892841848107045424000440b04c142a4040c140011152590304041000d0702c0141c204c40e2509007000082500115202d050300f4501c2d014001c44000f03060f1940c2000b090348920300c40030b580840000014071a03450321000500015011202c0614003aa5402c40200600032310100148160000000c2e09072050b0800c40d40707480310800d803002e4010a070130b103c1c02e00008100900046c0800401044040400000c0c00d5801e01c0c05170050009006641da03080c2c010090700c1c003110003c0c01441c0728030104242c902c410420705c1c0107130b003120b9482d070500420811086540e034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 157505350 1250 157504100 157504103
    0xe0718170615010503040f15020d050f07140d022a030a090f080a020402250308091905030a030509070306060f0611010c09030b060316031b170604020402090607150603020f0109051804 80
    0xa08c03500c692500c01500c010701550710420b0000c00e8500d811061001005070041000007401604007903e1820b6000c04200c84101c030b102c01c0e0050702ca0711104500070402d40111382003178181020110122001100101625a81c1c1c542d0307070f03034001540d00c0b68500c0843c581144a080320541c402140c020045c81c0503000742100f644001c41980000c024107500d03000651724804140d020401001c184003030b201d8140100c61001589100300d15141e1540d40e1a644da074800d01040038101a40e90000c220144c0b002d100a80003150090024406036840e102024001940c0d84210004941140e01c000c0c50341c0310602607190b1010407600c4184809280d601c800c00d51220081049a050042400d0944080120000386010b1400f41c044291810b13500706500f0444030003600850400c02c0d40c00c8803071600520005500fa070003941580d025844c3c0d101c010118040d07000d5900020070000d5001881c10400d407413580844100c07402141c2c00059042c2050040d141403106d4051303680c210100d281d240ca000040000d030f00307401c035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 157506600 1250 157505350 157505363
    0xd05040909030e19030c1e1205031315021603120c0606050406090504020405090a1205220b0307020114070507030509060705010e0609010509010c05040e0718170615010503040f 77
    0x100800300007001c000421105070500103035611309005002c0b17004880c40103081041c00b081c0c02e6020861000340e11003114420140d074079031450030b6401004004e0098030791400c0c0b84042a030351662148130103800c6020b4909060f005104092414003185010004a01120b400c880c0b0603180c80640ba00444001c00c000409a803e0340d11040005003603200c41c882c000c01003c0740341c0000b41c1d42c00c0c60310410050b15800380c180c004aa206e034000201161000000610040c000d0070311a0761031007066211013594403403451041365458000300004441c42d44c840111b20030311983c0c1c001c00c60824900b00c46200c4110070303129000010002c0c42048000307402400142120f4000078a998180f04031a43c03014255a40703400000780300d400010900500c0c10090142c2d0745c0004214000348480740100d80c000740a4015880361141c01855000413075010f501502e450103221915203a5903200036160300c48401c81c0a00305e07503501100e1181c0e50004103119005041c4102031001651a240783d5120744e16441501100801d003950f02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 157507850 1250 157506600 157506617
    0xb03033123040605060309072603040f030209091b01050904020d02360f1003090b090f07080105010e01060f050408030307090f08011806020d060f090e0f0d0504090903 73
    0x95448011a00c0303064500c0c12801d03481480301c00c0074402928010303804140240c20600c01c1c44403002001c00d00400342c035154885041c2d0460007403455000031009000d05149800001808038840302024071000a5034002e07501032101c0d8840c010040d548010961107143d0a0100e0200c0d0701d901c1d8810401002e602d800104094105417000044200b00e0340450b5041400010f0f003040c0b01c841d011a0729001d0203002c460149820404100c40100d030300762483c95201881034400c1090185440c0c001e80c4841225500608004c0503494a40242c69940c01172024456040c81400000640504140035140c1a585a40b0840c0080d0b481c001094030b400255501c1d07002800424000402c00801c00c002451156245a0303840e81d032945005030705103500303181c0d8000044a2341030011103490300049000000300c80354400310050b61805a01241c40041607203811a502441c88a940001d14010907080492780c0e01d0a0000c0d07500c17880c1d4068a5070b5030342c0046052140841c00900c0200000322240d400030078110f02a0801c0b188 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 157509100 1250 157507850 157507859
    0x5070b1b04180605040e030406020601050904020a030b090703150c0c0b0a1103090321040201020a02090c090301090b0901051f0e0c040b0f0c0706090605040314070302030316060b030331 81
    0x7035a048040110340b807103944107400c001e036103028051801e46010000140d45090b0a108009454001c14081d40c0d0184219401040464454407144402560090041c100074140440241d40b1003055100a0790805071061034100c8001c0c4910800c02102039680f1107600300655a540c01580d00750080600d5000c3d1358407010440d004c240440194400c00e1140080c0d5501d074102c202e07500c500c4044030101600900300c501000010707600001c04041c4a13404030b43c01600c90342c0743c01d00500b0314407641d4060398055080c404c0450030071491b9003110b4002c040007070090000da5502402103003a500b82e114822101c16401030100880d40600b031001d50001f0301200414034040d1648a603070415401100c0030003101c000024511140702c001d00c42800641102c1c5800d1807650b13b0302100074400d025600003c2c01c80e0780b500c42407140004041118100a42d40501940d89070440c0c100d240c0c241e4a2150350545070542001030314002480e000c0121106410b858520007011443e03019051079803d0514001c038070811100e030002c00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 157510350 1250 157509100 157509119
    0x5031e03070f0309060207060305010b03010e04060627051305031b030d050708060306101a0901050c1e0613051f0902090108010e010e01050c07030f020a08040905070e0105070b1b04 79
    0x12124065203646134042d00d0074000070700d40402d81e4030001c1050300d04001400400c1c110011a4112031100012400589543c1402c4000b03201703641c4120742001050107030340240341c04c102c11204007180f4250104599076a00c1a841c002c0640c0c42e400a100d508100f000403d1740496403454010b100e441800c0302d0038549012104021900261001404100400108407082c901004070aa04c18800400681040c1c5002040041c0c10010a10b041c9405070104819941e41d00c00c00c2550b51054030407003110000f02d41801c007250400c0c800c0303840601a005540001d41401c40c4800e80482003a888401410a554040c0781c1002c50034401415840e03140d200c1400e0400350307032403c0b0824040d08840f00005400c9901c505042c1c00c542035030380c0d07114960341802c04201c4001c03000020b441ca00b07070b00b500b4440258068101c00f00c0c10804800301c000d1200b0400f0601081031203040d80300c2407042d141c40e04c41110040c94440190742ca030250342c42c02480d40d1100c4e030001c0d640c0307081c031012113840d00507101c2d81605058681e4000d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 157511600 1250 157510350 157510373
    0xb1f090e0901050f131a07050f030f04030e0307080c090a0e011e05010503120d05040311060103080a0e0d0f060b0f040c03090c05010c02060d0b031e030715020405031e0307 75
    0x52040c0c0e4480090016132840207901681102e8140217038010510306a0701c246500c02c5035903060212900b0000010003c40c061000c4440c54078101445d9582c910304000f0704200c803a002e61301600000c03100c5060507403600300001e49006890708a4003c0c040d6a4070401000b40340c0c003004080c039484c1e60b11004411513000c0240544c61008002e01c82c4181c000c540116200112801648600d200c1d501c00e4140e50100e210701d200302c0d504d003142100d01103003540d1035040550300c1440d50380341c40e12507204081c0000300b400411070250072003413003581e14040161b41040410000804118014009040103050f21000075141d07401415064406001c1502014000000504482c0780c0403d881c0860703100c10015040241100303248002d4582400d01030201003d40e00480c031503028550070013040c965141c4001809a030200024903503085003400014152004109441d10790b00701d601d00316240c0c1c0801f000314001c66034900a0b1000d98501400420410007080040c0b040340c2c41501c84039500d4002000200081115003004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 157512850 1250 157511600 157511611
    0x40609320c0d0612150b190b090d050a0c03030f080621101509060909030c03180b0f0c0f120a0302070c0905090303010e0109020a050403030e031c020f0708010b1f090e 73
    0x2080c280d04005c3c01603005440011480e9442505c001d210f6807104003001c0b407a502980e0403500c0550700d03030b007410010500d100141500a41940305818051040144024030781d803c1da84250790b030180800030104192002c41e0141c500640c82001210b0f00c0104d00c0100712801c076140840c00c2114411509000200210350002c204010040401c00c03080c090303004580114001082428410800c0380e11a0300d005101c504200d40060070411074101c94903c1c003040b1001040070f01410701c045a528525071501d48416405001a840c50780102800741d8491130020800348290416502810710744848140118020360000c842100e102c04200c5010030980740030320542c0c0c46512824015692941460f0825800c80816170040039424010840c15051a5004050324100ca601d0b040103d0510302400001703082460880340011420038160050000c0c035400900020f514100006484000d5140c1a0060030f94807103490113500040d0344401c0d1b80c800c48100000c01c2a2002e82d1900114060b02c401c1c060f6520081500e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 157514100 1250 157512850 157512863
    0x1101020a1704090e06040510020f040f0602010f230103140304080f07030c0b0a0905090a1e060501030e030a1d0613060f020d05070515040809040609320c0d0612 70
    0x24203100d006624412460306004c0c280081815183c603a881580e24411500c460801d10b40104d000800c039400002a9409014143c5042040726205d000084c0200a00340c4440d0b1614104002e01f00300c1422001d800301ea80010000121440e801c54903012000000c10303000204511041000013142c01c1d043c4000000b8500b140050000d962460400c3c070486c038001c2d0030061801108114007416550130000c0003080301c40c2962000c50799551030704070100a03c00120302402c844401180d0318075058550303000200341ca030240c90410074003401c000e0b80755407405194482c10201c1c9145809407402c000391110000c028000030b14052401292241d035001c914074940c400c40114034250303a00d106050301800f080e608040603290441c105503081c0c41e001c0d580d004200542c1c20a8441d00085014817407580b0481c0c80c1c000c0040c01c1804000c0e41c60403100e005007416620344942c51141e0300d9802d8600b103c0a6005e00d414085071242c0480c4d1250440580e0650200300306098032543d80c40d0018040d05010449260f0900812 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 157515350 1250 157514100 157514107
    0x50303090601081515041404060209090c18040906180f0309080a0201051213020a0f080f010b010e091e010b120901060e0a02070606050a0e010812090a031101020a17 72
    0x14940981038004400da41c10031390102400050100c02c0d1036122200300004c03080e4002e0b02c404100103081a00650340c0001c40c01d400c1100f4048107030020040728100b0713100b8a0850f940c00800c1d06080c050100d05408010f40f004a035215490701e9040b044040e4041c50340040c0c2054044140940b0190402048480900100f181400d06070030081100c010480c050150002401d41ea000802a2042000c02100b1340c000074041000198200034212041c2d502403c075070006c1c2c0d00d40340454070a190500c02d41c4a20300c01e44840028040301070084098800068403a4004003d2900800007110b03001022803c50649540c0b07026005102d10700400d0090241e16126507640441c10b02d010410f400c018481061681409002c00000da0194561603001c8640140181c0314412403400001500c01503205562220804030007107400300b40241c0450403a00414211030456450003e03940441c09050682c030741c8100780c10f2040010500502803103c1c0c0304014030640300c60700f1003592010314184600c040c0151241011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 157516600 1250 157515350 157515361
    0xd230403030e0a08070b16050c03010c050904060902070c05061b0d09030b09030c0601061107090608030a2615040f150f05040e06060d0305120702010f0f0c0c02010e0a05030703050303 80
    0x14010f480a80034030070141140c181010160303600351051381c10300c8604c2e0302a08160000e001041c400e103c05607600400074801205003560080ca0b580141c0c4d02144210302d000d0000491102610865100503401150024210314290030001e054000230540028460300304000c4680782014094989407038103d4441040c544c0c2103042603900d982005200607020ba01c200110550940001111411594186041d65030490201005030410000d40c0c0308044403803e160300802e40312004005800d5407040c90b61140c00040801c4032481c050841c0c501300701c3d0f000700a84040303242030b43c00c15400c508591001e4800b00c0ea58050450030012542d20342e05010096131600c0060000d1081c010310700c002408225401d01901240f101c1150310b442015040a03c10180c07003041d00c04050290781903071080103c40e5100d400500d41000068040c0110402c0020f0350303454003209118a09841c40341060281413555218403082d03280e801526024081c200e000d90120300540c00249655080000e2405503105002440e12401c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 157517850 1250 157516600 157516609
    0xc060b010c0b1602011b020f010c090510030e0a082709091b030a0b010f140114040302010804020112020318120306010e060a12050703051e0103050d230403030e 70
    0x110588504000c0c804101c41c000c15003030011107411564150030300000900501060b4010102004840c460103034a50b103044855401003062000401c52030001e1011680440048501d40350a005442e4000c08901303c40c11103900c20b84c00118a03144240c21103c51810302e85840c3c59a80100b085505100c24020b8a500c8140ca80c0c0341481103120240c1d0410007504003406025220302000300ca4111440281030620501c0c4e40422441d440b40d50000402045541c58002491a0740c0660207400c3c3d5445000650314125440b40e8500d41d5400c5980106a0400781958011564648050016410000c044466042ea408603100a600428181048224100448100034104a0f11030120214200c051003048a03a90304950303031911042e4102c805590b00d0300280000d4030302c0707245180410020340c541004c10849541550115008514a42c40764402401a010300012107009000c0103045030080d41c5c034030041341e020300c01061203000b01d544000c0f8500900e1590540c581c0040d4001c4e40002d0761080000c885040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 157519100 1250 157517850 157517861
    0x306020702041401060909090204020706050703060501020708031204150902030d021c08090303040b0403051c0b0f06070c0e0901061e050415030b1605070b100f061b12030204030b01060c06 82
    0x240346010700940c90f0817000b038603084241c4902d200440d1940b07030450843da80c5604580003203074000c0003000603060080b0024010599401078902512546030702040c1c2120000c10358460180e46100310040342d6840da500400e0380901d05d04503c00603140c0c0d040b840160742c1071040c949003052607402460442c041c160120342c5030140040d600d0034031401d0010b02800300004002c4940c041c0d041030900c07201e61540d1600b100e440c480c650103042c59007600e400e40d03076440f10f03180c05c100c1c880e8400301d509164010300e500811000384544000103142c981044010080314551020780c5a0101d000c00001030550340e1170030390440a0070f58980382c40b081c80142c1c40c00e0115141c50702c9144680c600c000c080c00d24850560f03881212030100030380f1a617034130012540700c00d091034807a4049965060340414120b0150601c80302400310721754140521245001d8490380072915620400c4034401c0150350062440c41d54046849980c1120301010b030b41010113400300804404a5408100c10740244001d640780c1e05040c403641052000c540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 157520350 1250 157519100 157519121
    0x80f13080f2803120504050a08190801140904110303040f080708060c040303080a020919080f0615010914041409070303120c090b0c012a02070807031e08090a030602070204 75
    0x9586182d4207020070b9000340700000c400c2007442c0008007515a820640d1900030001002081e26000044100000e2a44002d410220038507032580006640c96445138414003c1c0c2d06035583d04550060002000300714480001910340b0000b41c1680c0ca00ba4840f500c98290604940245107681e0240d002000212020070025512a0060342c1c52410203056680c01821180e010301124442500411610a150313070746080c00800e80c4000036440389455461550544403107002c028660301d401184001101403160100100e102c0105a40d00614541440c204c5408818501d00603074000340d407613000d41c2004c0700b426038450140780e0715001000083c2c610300c0c1c000c01000e0392064840207903040c00d500c5042c8a4200d02c00c0c4058907400f90005407070302e5003203507004d006064102803506000001040000107922003200c1700e4904880341c0c240e0b03540c030751108a80d582e500c2030341c40b00400c40d0b1745808841d024088150720052109100381c224600e042880400111b6900c85034000f5514180e0001d03126045150a1040344c0802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 157521600 1250 157520350 157520413
    0x60304020109060f11010f0f1802031f090503161412030a0f0e01050103031809021c09020109030b1e0f07020a021002070918060b0d080f13080f 63
    0x14a0a80e0000740302524501c1031009100c0742240041c10140154028400c0e415854005c2050b0200b032072000c4054101c5010f817440b810300d0921107100000c03800d0b240107400381d009002040701c0e943d41d1441d04c0d101c090500401d2001e83c3d4030401400098014001001c8055004007031f20180d40050a0480c150340910784c48220513403103908482404c0b645041070700c0c1d101081e130400003055124020f01002401c0da600003000b4a5203401d002004140c0c00c55000c4d901401c0c014440308103161602a400124411002e0141000344040507416140a050b04149881d51040c542001c14903030740c0e61424803010051715a881c00f0030411001146d0010a01182684088440440009404d06000282d1121103100000e401154802690308065008121803001007081c50781c1040320f0032100500514501c0103c400711401810030701003c80314508100f5042c042d81d0428403007490140c2400c0c8002c06544010304821031488001da000a040c0818041075034240c0703424014040443e2080802d50130581040c80d01c8144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 157522850 1250 157521600 157521607
    0x10e0d03020c0d0c03020d2109030305091c0b040c0501140316080a060f090b0a08010b130207060603080301060c050c0301050114010503041b0326070305160213240506 73
    0x869070025640304001015510035403822030508001c04403240503000070303401c100020800410002000c240f02d10280d041035000c40382980c41c21003228003140c3e0b8030006d00020814490300301c6500c2c014510008090003005101401003003995050070105088806031400f12200208003c0c65820010b80b411041c003200321503141d440e00ba28040308083e030300360245c81041807401c002580c2c44503c1d4001000703845128402c0e603403240e542801c01c0c0941460026103004e64401c0030001006a0140030304a15120020120b41c20015403866423002500006000ea80d01ca448000c000041500b24004502801c0d1030360341d114494402d07007446482c1400d00d10101c2d00985c58100100329003100d00381d150261000c2445c256549450781d007480c400c2c4a040e2522a21220405132001041002c002248100c41c40d810113001d500c1403590494035158041e501e0040c010640410505031107550401c2c0740e6041b60320040004102000c11500181250f03c003101e4404080c5150a00300603440240d0110801010110740b918903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 157524100 1250 157522850 157522853
    0x70206060402031b030601020c120c030c180105130b04020412030e0d0b0105040b130c0c03080106050a0c080a11150604111908041a0f0708070c0309051203120a0209010e0d 75
    0x1d410314042c0d0b000c83c0d0700171010030700c2c0343c3c030034071650320005c5005042c0700110400b111403503120303803089a01600c02c1c414080b105000d400c01c0c0c0ca002803000884096044280c2c40c1405026050301c248800103106a40c0c4c02c0c1c2c8800300c0d580d0f80b014001500d40c0300141101c505061070090203044103407035a2441400244c503241c1c001014003a00364150f550036a400b051100c0e40d0340200b94802e4403018464015414400b0304000c00e45c0c410b00a03080c803070090f0b681c11556641c52409544602c60740c040d000004250360850000300d40714500600212a4a141a81a554000d0041410b103200c00f5910240d01040500344052880c103030045625400901c031142c3c3c07501c9601c109080c8980c144d030a103481800a00c0300024207010020701d228005100f10140800c0e14506040304880155007141d15a002c1030550006c2404130788030381c2440390a030f40c0c1900d44d10394150910007044121900c64803403542d244410041d05885122560749103000314420040903031988a1000007402ca0308044a400e8010401c1103030000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 157525350 1250 157524100 157524121
    0x3050903070f06020901030b040504081206061e09060f0c0106090b04061211030106080d050a1b020d2a031506080c1c020418050c120c100810030c03030807020606040203 74
    0x150b640c0e0340400010380c0e4100090058025040901380241e00914100820082c800c8840007842d280b2424280c01c2c040703960709000c00410740200414141d04120124941031503d6115000b040d444000405090600018200d4044a035100220701c01099444020801128116011314a200d481c1140c00b484528203080390045182c440b10b801902c0501c0c118410540342c0c60a501c440c028208110035103420100a41000d880c42d4803044034800004d950441003080c400700c410182040034ac1c000d0074040141500c0d21001e5071000103455040422203200515207182e03444000c40d0008512405401070b005420000341000c42d5500c0e0b0142006d900501450034665a1f640b518542920305403004082c04030443c0041001881940030403054481020f600400384000001c400c10348820484030302c2560140c41c00040d4031250401290794101180007900c00b165070103031004070b40c840c1c1c1012010410a6403500d84020300c6000380e005502254019050200480e4144019540304105440030f500e1405c1039540d90303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 157526600 1250 157525350 157525373
    0x4020414011b050d050307090806060a26061905011703190203040503010c050d050907030819021606051e031b160b0a022106030d030c020a05010504050c010305090307 73
    0x240c1000a80d41a11000600300440c02c0d01060300581100c40c58401d011000c0c1c0540d20645891f00130400c1d600c000143d050001400602c01c8401900840784a07190072200d40d110440c1c076001b218142d40700d000f008015007003040340a100e0113100d0054125070115098207011140181c0100c1e0b021f80141d500300c200131900000301c0e14070f1905200074259100003100100c0c158000c580000341c0c99400c0100c02d508030781c0d00c20082c00510a160400304a80d4075024010784c0d0301c082520001b410b100081c4508107100b100f501e00346185052600547da424440b070126102c2c441c2c40342e00170401044010030f0542c1c0c2c4c03080c0d00307030030340444c01021810305e14500742850341c030562090f519908030010000280415004030304001c80710403d03a0002d02c00c245c900b0103011031000794000c505038040b682c0c0e2010f10190f031288888215802202d0180181c405139004050440103041c803580030100354820a0120b60001c1d00034441c0500c1180503a02511070740d103002c0001000c2e00c401400c41120342c0d1050011001040e03110248 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 157527850 1250 157526600 157526639
    0x120506030c010f111606110a022805090901050708090a03080604020708160c0302010206091204050f0d02030a051b100512060f1201020306152d09040203090a02030606040204 76
    0x10300140e118110048404013090b2010070843d003c0d40b0f030100002e6070010740ca00e00b5160180c50701d2174080115407105540e42c0b80c0d048045e500003075144001d1811500c1e402001419030300c152410903015111008910400700c10350350f8000e01d0303544404004401d948010180d802003542400780c03900107083e8400070000a4050300c0349110b19070001e28a402c21030f100c01100c1c41c003c145401c0c1005142282031030142082d55220a1380940950703000115032500c085040000002c0220400e800c0034101400e101c951100d034030b400c50b0484168900e140159078104429900144100f0081c075600324080302c1d000a90300d21f124054000d2a0015440240603041410b9034040b440b0740e0401d02180e42c8000000d022a1000d02143d50488032480301c035030030507406400843c4120815560800e065400703018103845e40c4121a11507450001e80500890b40c514070101c030400644000900d0b600740550540042d0880c0e02c1520004202e6100c49002401c43c281401600d6010001301d404504262805a006032120001500c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 157529100 1250 157527850 157527857
    0xf030f0a020307020904032105062b02150304060c030203010302010c080c0111030903070c080703052107061409010e1b0f0105070602040303030b0102070b090307030602070f02030d0906120506030c01 87
    0x41031840a07100b002612070807500102000c085060600300585068075011f5040044030b444d1046a840700038601946000e0140580728442e100c0051803103165103210000c40500d0011801d10f900050b940d02e4109129007811103944954a0410707103403c1c422036401c04006400e140c0103000400c0541e030024450b540c7c003a0884007550b9220303c05049640149000412100203520200034858019000009403241c5441140011160f980382d102441ea074590511004080d540540e040745108aa64048034914440c598a11030a0004035501e980594003424101c20707207003114504120224501b4028160b800c0c40400c0540755002c0042d10040d1290f0b078490450f8000d0499950f04c03443d0364815401c0b01e5910783c0242046480303548030710300203010b0180d039540c1a00522031444c003c541a81d0590440b03010120007001001e00e185581c0d10304e406504404426124484105001400f607102404000340c481d0711981d410341d800e0306090303010744521484401c3e1005246403004010840d200051400c01e1001c0909 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 157530350 1250 157529100 157529107
    0x3080705010212010303030506030d030e100c11060903091003090b06100203040b2206080106020a110604090f050f0a06080a110d0503071101231c02040f0303080a0b030f030f 76
    0x500030301a100c2d2a82c400605119400004141b50f45036100314041d81c001c034140e4002e01c0c10243c04600b910040200d24602e41c0005100d079403003200640c03200b13070822a10f01300444c2c005031450205080410407330b000a025000007d6040f1240350125510000400d80c5c1400c105503566500d03090307040000100000c0c0900c10070700d02d140a05008100340e8000340854200365688607450135a2410346001d00c404812001c024420208440b402080343c941640c00e594001c100d03c4501e61214400840800c10300c50b0880001c00000c690131480703008804030b01550440200e900d0611300071240d250100180400700d11441e20340d041c004900003003032516490340c0010142c8207034048100014582c005c03c820040880c400003030982c0400080041080700100241c8903642e0030f882150303d0300440c144511850300d04c02020418144815007882c1d54000182e0300120040c01c1640751481075004510707540040c0c020401c1e035001c001c2440c0362030080c1000454154050800412101580c1d84c0c2c9001c1d061003c85000f0000c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 157531600 1250 157530350 157530353
    0x50f0a031a0307060c150c02060f06040b0a0306090506060307051c050316140105011e051c020618130b0f010c060209060a090501030c030516110307060f1d0610030807 73
    0x848076000074000003000e452100742e69803009042a2840c81c01250306030f030a28110690081c0600c2984500d01ca1a005171440e03940f20008071240c004c0003040e245e403160741c4041190840e2288441580918480d0b90001183d22143c2844c0386403820003000140320b9881a0f0040c445a1954413070241130740410800c44201c820300b4a0010704600900b00000d0302c0910300ba4050040c08480740405142490f10030080081d070340c0710050800c102002d007000c0074500004441c10403450400e03884c110040e11010b00d40c600c50395440d60028082c1d030310010030100900840006541d03249044a08491254122141001003040001c0070030400301c00781c8546414008010200d40601040340c040703c065640045c03d5540d143d114400103006040c603401580e00091500c0006a5018001d21409019070782c02000f03020f2050344450f04840842c2e401074180c1c603500082c002080090102e0044032405141c503500032880d0440c161240011441c518150f00700c1da0300c02c0051191a401d50a0b0250a40343c01000710355544006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 157532850 1250 157531600 157531631
    0x51506120c15180904080a0f0c08090603070309060c020d090b07150528051e0402030601090b01170f010311011815090e15040b0f030616021606020d0f050f0a03 70
    0x300903e413078114010400304010807107504d000303281c15050744d120b20343c0000110a0881d10302840100080440104101860300d80c070b00040510b600040ca4a40031400710f40c1c0e0358603042912381c48911a009640024500d1074010b8001a50f00003800d403200900b810510580c8442d80d084002940300406182d440021450010b00840f8a10f0154900100603010324440e00300c0390002d1008070340c80100740a0b00810f1500c0706c2210300c0024007e80d001001022644d0800014000038030304840c0c4141400303401c00100d80503c1c0c089081078810180071800502c075614600381181680014606141080700a550b4000182e40c01202c2e0000e07100d40c800300d4155603251580942e00900907030441d0702c7c441c44120400130f40b045c0429011024403820369041c271101c5040000d204a04d03040114a59154006200041c2044650040510365100c944100c600d01054601c03000310446094010100503089410002c2a40313800100c00f14441c42c240c80c4c59407a00001a180c141d0794000c0b54402e070704040d101d100c02c0007841e20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 157534100 1250 157532850 157532887
    0xf06090212060c031501030c0e041505040f1a060c0304170712060534120626060c090d020909072d14010f050304050a051506120c15 58
    0x541c00300c0d01c0a003000002403019410032100459190010071070039095506c00d025980b480c0310b00c2d03160031902030000c0c3e0400002d0a0940806566440b1321000020603582e42c0c01200c2c10030003983c500090881703402660f04012219009841c0c001ca20411002c1e102c0b0b10004100d4003150b0b070304401d05e000d01c114105050300f410303e151700c018800900c85c0d40c44000e1000c5540250700407401c10400c241d00c008284040c00b03a0801c02680150303c020030034030050191b030185180c0700c0c040c1c2603941e0028000d500d5200c660360040c225000855100404c104501500f1004c00625030003400e00c0ca4400c0c06c080b030000004225508114001740604500e80104d5225a0100560740242540c00300003100d2001001a001040d4990060b28003541d41c2d0100000300c00ea0020110643e80e88180e40c1e25200e142804c2c01901c680c2d00c0500101c0d80e134450340c854407021400a00854008038211900e80001e03040100400595900c0541895059080f0722242d400da0396480c4140b00946412101407600c42400c803907035800101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 157535350 1250 157534100 157534129
    0x702150c031305030c01020706140d09050f0a05060109051003080904091208100e04080d0b1f03020a080c130509060103020717070b0c0f071e0206070b0f0703090f060902 74
    0x400850095140e82d4115401c509586050b0100c851a103100c400480c0d59110303034860b40b80824850310110b424542c4072401003403151001c04001c80e20102a07503d451130081485003c1d002c80d0000c081400030054144040d41c014112080144202d007045c00c60200201c84620000b0242280000c4070040e903160780c0c0040c2c0207560440c40c01d0342d007110102005001010200e81114028540f040c1c042038071310b0160f1005001e150092209420501a0740d480780060480d1400796510904040070001031680d08007520185010395075000d0388030740b00803601400420300540f07a500320340300c24411250310807004203103a0111201215541d40da84c480f800103070300a115406029140120310310042000c8420300c001070060314460b6001c100f240e6030395400030b60035010f40391811000100c104840004200701d240401c55061b070328101c1c00c00c03d14113640000d080d50f02107241240c101748040c042010036402200803582c0311303600382030038013040155607074011140300300100040000d40ea51403440c0135501c40991b40070510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 157536600 1250 157535350 157535353
    0x405010c06060b0304120305060303070b0a200705030a0318030e012a031d010320030603160801050402040f02040602070302010c0512040605030a05060312030a0f0f051501030e01020306060702150c 86
    0x3d007020304121b10f00e4180405e40c180424200b5004c148503040003c00c903403500c1e400c80c40c041c4c0c8a0b02c1f1940400068400d407104410700c15008492104100c00200050081c030303100b000150754800c0b100760040c0996619030f1101c0c0044501e840c1c0308000c00e1b004040e40020307441c07d20306004180e01511285405804503441002100607034140c85c420190880c200c0c8a031b81d66801071400001c07280740011410b640d088030000c104070611161f650504810040510381101c0300406a80840c0710509440803920324035404241103030b44403001c5c00b0a6041611480c5402d40245034150325050400e82d000e1f565036203078400241000500c0c10541c1c2804018030100f2440e0400c40c110b140d4550b91800b00404036082a07404000c1945403001081152400040e0840b00b0a008080103055548a0b600c910042095041f03102010781c5817580007149075020312403540b00d6621b004400110410a00005003180d0030600c1d40d0350755070310400600886035604030950304d0540c3c0c1103e82103010100002003000c43d0080c903100c0d03a000e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 157537850 1250 157536600 157536607
    0x21e0102101b03050a06030c0b0c1005071d0a15050913061419030b07141306020303090708060903040515041e050f0906010e19030803090607080c030702030405010c06060b 75
    0x4104000402c0072030443d0790601c610b854901140e012682c203841b00601c0021031880c200211401d60700603140c0d48440c00141c3d081101d07201d941c0b80603a5000c482e5103001442c0303000e40c1d440c11001d908c1d40100c01a0140e4a4100791401e019480b00c50244210f85c8200748000071803413028603902c1c42d16960750032214460610846545440700700381100d5440626104502d00c1c0e54200d1108401d04008040342e030040301c42a441e0325543c900b554003100340c03c21207842c00020003081e1a00c040a0f5885002071411341e009558a14140d074880d41011469000a806904002d0511800b0000001520207855084030001307240c4000d1044604903209562111030f0903090407116031700d519200310b54501110419100030481e05240302c10850000340071601507001c1046c0722581d006a0401c1c803080d050340d02c0002c03c4144055140d445070011f41c1c02c1150210307001ea0000080145955000c06059001a54000c415056052011001e5141d020354000d003410000054524010b00c4010340040c0b000b050003212a41d603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 157539100 1250 157537850 157537871
    0x6090d050c01030c1806050703030b0303031006020c0301020c1f090c0f03030201060b0c0303271b0a1403030d090501021605010207060e1917070b0c0310050d021e010210 74
    0x715900e500003501e011070301e40911034200600400000303c07001100314009501ca801d1240c141c07056004620107504040c1e81d01c840d046151820002035004400d060303100341c6e070507140401c02464034800717006250099005100004204c0b50000e85400c42d4000c0e925041001c0240c240c0800040544075005080401d11950000d4142203100c103580680b4002c0d402403002e00c1d281c04041c06540b14511121130203920800000d50003181c00c240138800c0101100090007a00c0310560018078107201e01c0d4000005004111000610745020a11080203111000444500398990390009860340180d000c003a00f178548500c0d84604001d0290704480c0030102202504806056500b4958000d400001c0200d40041c82c0410411070300c9030000d4940e94410164040321007003000760740e443c0410100f1003404d1001d42020710881380004c14012079a84a650855070b00d030340301e00d804458071551180607070207680a102088925405619060802901c2d0311520050400c82c1075903200407450000c195000080441c6403180305607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 157540350 1250 157539100 157539103
    0xb03100f15030311100c170402010201060503030414090a0905070e073e2d0106050301020315031506030a080304031b081c02040f03030c020a0306050c030403090915060e06090d05 78
    0xa0038440c003034044445250185040c241190146d20013440070500445103400d00c1840740d2411a4402c0c8188000b0a080d40d03030b0408246590001e800000184140300c0042000d400e2120f1420b03404040a00240540100390b1262502c5801a010f12158088060005500180140080c981100c0740030314940520580b60381c0c20f1407080f10603004481c6d8090030110b012682c400061440b01c2400e07035001c50841d0200100316524150321003114102e603552140070003e250313038003032015512400c3c08180450740321802108140c1416056030014401040007410710070161000200d0588155205d600c150b581e4450b8201903600000d13103810342c0d021502d40ca41100c10010680c002c2c2c12010324000d5481200c15041c000503060707024034043c0400c2142c640c001000030a01c03500b92442c0e002c0c0060001c42d03980d40c40c0d80781c80b01518011036001e42480800000c0c0001c2603804143c100090192240402c890308269500649a403114403d1900304600d29004503440e50350b07281140c060240041c8089038030612842c086 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 157541600 1250 157540350 157540367
    0x4080d1e240b09180c03010e06040c0f20150a0b01020313090914100903030506150f07060b06030103060207020f0f01050304021311160b070e06030a0e030d020403080702040f0b03100f150303 83
    0xd070038023801c2c1c001003500741c1064018407841f11440c0e02c078015650503c1d001100c0d00c440a200314070f40c59142074603803641050f013881800303400342840241c040c291a00b410030030141c4201d83d406504541c400c014107500c0c0d8080000d5a41a5030340400d010904034406e0810b00c3c4003500408104c10030740034038111000004226444403000178840c0d20305021654030a020082c1c90b04044c1c26048011004201c4c0308626101c2c8030083c000a0320130040003d16590103000308000c1d4000b41c200f103c07000d5000500314107619001c1e0841410100c2121213640f1840443c0c0002d2550101900085c02445200c0b04040d00c415107410030013404141103441e648078203855100c5a14049490001c1d0b0300d0142e144003250315030344907001c0744003e140007410352440c5484a82c00d070030080401c400b010000e40010300200c214007000b400200001c2d4000d40209803280c0c400c1c0100800ca441240303005d1042464401c5e410181c1d100419070b4420082c103050b00040715081d8a60040241c6a40a0f002c48101c1241c00007008051300b000341c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 157542850 1250 157541600 157541609
    0x106050415032715020c0705190e040305070501150b0406030f0b0603071817030313030c050d11010c2c0402071b08071a090904080d1e240b09180c0301 66
    0x80c2180412484e002d101244601c008030405500001000c4c8680e041c01d44400d02c16000b13400c050b0b040181e8820074029407140a446c1100040c0001600718180042401000d01204000c090320183c107187c854001c0c8203211740d1045505060716156008505051036110f10b95101003c0c018981e0780c0391401d80201482c140f12500c0001408003030012641400341304080c2e400321043e400451642d22a0b42812031140c044040032000c0140090b40b460020780309102c45c1904600984518100d84918050203094a446c01c0c4c0800c02c100350039000c40b03007840029840300c00d01561014820105090100803034044e22494501502002d901b043e86404009051541021541504155103801d604c0e4245400c1401c200c1c1800d00d600841801118007a161050040350420b214201052400207001c0140c420358800441d20035040f42c01d070082508400d06070156035403a1018802e03a22900b00b48403044507501c0c1da40d001700d02009801003020201500c64032402080171006105000b141d107801540c065955100340038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 157544100 1250 157542850 157542863
    0x501062403050402030a0b0402120106031b17060402191a0702031213050402030a0b030609060106110c011707090302061b0d030207080a3912050301060504150327 71
    0x5200035440c401d100300c0f40a2680200030b89500b880d40d40b114a080103010300241d0388406584410301060800b441101c000b1072081000040c10703241a01c80050150340c590042800003021503a20060241c00f0900c20741c07103641242e403c140140c060b0f504c0b00c8007440f01d410107104000c0441804184072802806002c2a500c03c4048903024802c031140c8100318003440f02c09240c0801448000e00941c9440c2d00919805040f01c2c200040800915001a03c1c0c107500751220140c41d00140300620041d179100300480e1504610f50000d00501c400740300000c1c95407440d540c0d010b000d4403580021442440c0301d01c0b2003000454008207510345401d6000702e101892000d901407903070b0b6440341c041c2c660030450180c025a0440e6800c24009414010319280075103085600382c9500d488012210000b00c40800035903108400d07070b404c0d61586040c4100c50700d0550100b43c0d00c0c4602105221081c80104412075001003200c1c02d441c0801080a00c0b00c401c0d000c19401f411003050510010002015040707484490b4034007180c1c42e24028803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 157545350 1250 157544100 157544159
    0x18080a0302150903090915030a020603010902071b0513020723060118050c090405060d140f010b040509031b160e06041b090b1c091a07031a0904030507050106 69
    0x30540d030740740304102c2c3e42a0000c10741c130300081094200110080c0700c7c0304064107856840c2c069038001451944260040e002ea9603000c54080c060101c200075014500c100c070825010f859050a00007150300e4003444d040c03182130ba00000c1c650b0801c2201190302d01090710305401118803242a00d4400c2e21448240a441c003130031000086c0800719025130103894001c95001c0702c194034200c044424400030741303c02040142c004251108030400548032456198150b00c0c008003603e06800b04c861820f0a44002c18516441182840140a40440084100c503c82000c02561100008840c1419410540e4074440c5111801c3c01030000200c86400d6001240b0600d81101e0410540400484101010030980003180020f1092207040c40004c0c0351500a0103040c00740b0701501700140c200c40a4a0540d183c0c480216560506200030054094503422040d41200c7c15060a10403059403102074540b240c00c624050f841191284041418075000e032088038031701c682043c024060b0640742e84404902c01020013041c00080540c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 157546600 1250 157545350 157545361
    0x60412060b100c030c0f05011b03150e0114091305060c07170c0a08090103020c030c010c080709080d050a03090803090708060601050f120711060a05150603040201020d18080a030215 79
    0x1c0016003034556040e21800303111703141a180c0c42445e03200c00c607045401d59aa00c1078055060b420000e10300c919541603a003c14103400c1c9503100d51504085920040c0444039080c0148802225511a0340c000f00d0706580d41140d56844680c0c04c1c119484c5198054560b01403c070500402c490450001e0000e80d00850410f58165139954642e0424880d4015054468011194283c0060300d054000c0c02082d10515015085c404243d85007030450b403000700841c0590703544101c007443c420b4008014650000c0581001444e4a2030860520740714900084001c040000010306a040e8a01030b920800d5665040034440c1c1c0c036440c020082d181d80e4030043c044d01780d191142000054040d80b0807c12200b421550500b06d6061000b03440c100014480068542020b000c448103500b14405010030a4600c0b030740704081d000c111070402403040100700c041d012625000e5442002044050b1340c00240785002c0104900e0054400b44025010445480791a080303071010380102c008010905900141c0251820b104401144040c0c89a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 157547850 1250 157546600 157546607
    0x7051506030309040c140a0801030606050f01020304030f0204020d0203010305010507021b0609120a020619090801060f0b070c05130b01110601150c0c030602030709060e01030c020606040b060412060b10 88
    0x49802039071551042101c001c403418141c10074040c510081c00c4c10402d64580215140c1140c00140038100028405401007007406503e02480009010989441c007500718140c00003510307485280000b51108810f5544c8404545031941104c182c001a02003c6440356103900d07100d8041c103810348107200188a10003a10150000e022002504190000c0c2100e1402e4610014043c030300420540d0100039003d280d4040c009a1542d10003001881407400412030031080c100d40103003d51415401088030b41c0e15196061007803a100b040d044081d2030190310f0040d1151031514140491450039004141c010311f0030300c0045402072083c0c1003903103105000d0300c0304d4003400031110040c0e0340c840d02440782d41c20b0703440c3da00e9104000c2030140c80c513088124051024150300e50b8a0341c95500c140d070b000341d40040015143e4002002080e5000318a035000c680240f8042c080c11610203402960340e000609010f12a40e41e51200f540d81d91380c0c000803140146004804e0804604031400c0010051801000d894002c05100b034440340306a10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 157549100 1250 157547850 157547893
    0x8040b0307120c140d1109120a12080105090114030c13050604200d0203070225030210050705120a020c1201020d0e07080604080304080409330807150c12050705 70
    0xc50103101400c0500c0800317480050300c80110000c1054800308850686a12818071ba2065040d224006210103921854034000d1004011012800c2104400041c0031964404c00c200341180c241c40705601e5801c0b01030002a05000c8030184155020f491890a0065544241c00240c0b01c1d800444080064062042459151100c032500b03003003419808101c00b50300d00f0451f41c080c0d50400494070481d0708401600312003000c07080c22644c0555086e04d40d16420021890440003090081115142541c141561350b07543e40e660b812150340300c90000703c002c42c007481c0042c420004403282080051140510880c00d584160003540000c2c0c02e8200c03a800c010031441c4000c00025854100c2d83c41100602950350b90392140b4005800c068001c850003a000c02000035062494060380c40b0710402208906900b5030902103104040343e407450501002101c24104000c00301c2c0109480003251101ca048800e68101c0c4402200c80880ea424000c00c20110b0304203004803268054050041c440c0f088048540b041401100006a0304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 157550350 1250 157549100 157549127
    0x207060210051302060c0303060a0501170414030c010c090816030f03081e07020d080603011803080a0e0f0a05070b030c220305030c010b0f040b010507080708040b0307120c 75
    0x1d1040401c41d24112095000c0c540c0440d90524a002111403940040c40d154030500c0070701000e6201000744000c51030620f0803403004100034201f805a9044201c20726008620062019009405820550300300c6d103030910445180042c0100200300c955001407001d800d000e01401285030274031a000c201303000d00744549582e50603039410801d54902540301d070b070b812209114010001491041031001c001c83c903282c07000102e400383c1104d402515100c17041450092401000800d02da01c41c4c0e05000348a010030104019260301184c0500d0103050582d0764044000141c50314182c17031352030f920403030f508403d16020201d0841220f520039810f69180a54070031038a003c50006980c0084210420404801d00542d401415001c41842250030b200c020754a4603040e08542144a101c0301071b94498864550a146c42107221500450031036080125031032000000308030f40036032440103220320f000207052418000e034041507038002c02030840c20b241d41c0e2410344402003403802100c03e10700c0442d013094000001140145400200030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 157551600 1250 157550350 157550353
    0x80c0607081c0e010603080307020610030b0135010e070f060909020a02011509020a14120f0402031908130803030609150d061a1c110d03030b060309061602070602 71
    0x10200b625203040603064400d00103040783e8640000000c02e03801e000e484000d500074060705440389000d0001030309048004008081c84d10702c03018140300241041c4401410760300412410100783c1c00c00e9940b43c04c446148041d001d0501c80400c1d03000382007401501701e40b410241c85802c0d1240c071075860944c40d20042c1240916400324403501018804102d0701e901034080744490f0710001c2805010401803d0000000b81c2007940841d400203a88801d5a40000080d482c1034440b900030351030940c904009026420010b0600e0748900a03000105003550b90030422031000c8404a1400380c00e150341c40c688924258808480d044a50200440020380b010001c0296403141c040a45500b0060f41d41d08080d400d0003082140c115840280001a00d01180840c450b412842108803d110390003c2c1260404c69000c41e40850751031880c08e45a00d000000e050880488040c9605661244410500d89429401f4254981009400031408820403c40300c400041c0580900910500e00c1c0710360340c0d80d005c2240c5500d214004c60026 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 157552850 1250 157551600 157551607
    0x10c1412010608040f1b080c0d020307050409210203040801050c09030a143f1e09030a060207120e01032c0c0a0f0315051302041e020310080c060708 65
    0x2660040030341690051060320400b00c2e02c0e40541c0c9011075095a400400300c0038a01b004148508841006040701c89502150318611180c0d0301d0b80001da5444060213058010b0751078168440030050150402d541a1407800c0001891403002c41b0000c1d900c2e0064442c0704115820700001c1003071201d07240110b9001c510080e020700b00b109425218180721815800d18140c96100301301d0203810410f41407850307101c0c00040b981d0641b08075440c1d4483c0707402030302c40701d0600d50303214820415217158078403182440141040b4518440d072074a82d0040000d040206a80000d010540002803420422a0401100307620601e252510013801800300011411108840d141007d400172004c5070301902e001a9180340b00b003001070001c4494080b10500030034040c40c010ba00020481010301401d004112448050544090150f9020041440c002865660009509030040c0c0601d036a00c080c641c1c0c0a0012080360041180807030295500d0405c114030350700b100010300c2420864050b11031000d0103403416404503a0b074030717030403888042c01d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 157553956 1106 157552850 157552859
    0x304050f06070c02013c0c0b0a0f0e0f0322050411041d07053709050f030c0f04050601110a030f08070f020a1704050d05010c141201 58
    0x80d40ea40780c032018200e01017180c1c0901b01c00320030100220742c06001d40f800340d0f90605d1400c00908400707105002c2106040c91070308035070840e005070001001800e490051aa84905500400c11040c0d002040718072041c5516240010380401141100a070a541d904001002c80304492200d140340d480200d030401089a0b9a8105040840c200701110702c2c506d03091500800900c1068100c01c00c150b08001503201a03500e940b00c200680b403a40103601240f41320b5900c003401c0e40c070f460700c1843d100c0d400b4103e0a03c42d40c00c0100700a512203101074411041040002c00300005040700a0055042194050b20704410b0b02c406c020002c44680640c4540700d004a03c94002003203000018040c000781b0444514004410f5800110313540f0468104504440c0448243e0b00c45070103114551042da03008800703204030402c2c46019031008603a00900d40b24414000440c10080c03a090181c8a203c0054101d501e00400 = true := by decide +kernel

theorem cover : BRFrame.Cov 157374100 157553956 := by
  have h0 := BRFrame.cov_init 157374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 157374100 ≤ n) (h2 : n < 157553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
