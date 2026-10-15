-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3825
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:59.197989+00:00
-- url     : https://prove2.me/submissions/a2eaa1eb-9337-4e32-a99a-62ab7556a445

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 687769784 ≤ n < 687949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 687771034 1250 687769784 687769811
    0x19020304020f221d030703050903010b06070f05012012070c0602040801061809050303011e0b03010f0501020c0d0221070e0f04020a060302031b16170a120506090103031110 75
    0x141c041560f015204100125442c0002d042d004c042c10b101e03240d41e400c24000d10012038000c1c002400034001c000c0001600107414000918a500404001e442c840307400d182c10001c00509125000d00c50540000301c00d241042c2187c03a4180748501c0c100410b080203108081032045004e00340c11403026910413000e540361610361400900030485803140080000040340c5100f86903106212710403400380c00901462840e824100089449640540d40172000e0711140702c0001c80310080c0c000b642c041c00e86102c012891030f00d824002440d240c210b010380b51090343c032400020016034445814003081e020681c01d038500010300002213418200d05a00c07401d2030608500400454114401360a8411071003190b4004002e81c884500b24100c0c04102c3d0f104200710820800c07018600d403040080c1404031205081081a01038582d15000c1001414080490322034010400602054118200c0c440d418140d4400300000d16041000440d02c0406120150501982205000b0260303424040c6500c02d540782102800030301d002c40035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 687772284 1250 687771034 687771079
    0x7020c091f1401111002250f03051e04080304030606170c010e0f041401080d0801031709042d110915090a15020327010f12020918060901050919020304020f 68
    0x400d40301f950510b00400340154214150541c125000101807003588126501950268003001001c0d0340b81056113941c1c1155545c020040000d0101c510107140c4072071862030070f541911002d030000d070700c010800c029070341c0c0b85040000d0307103e501442407070f001d03118a02d00000f003510310319204991500306003841c0f28181080e620b060303220b040303480c49421140302054049040300c900303c0a0000624038003030380241900f13506240d00030f0508800d0040c400103c2d2840d0201d40e10600780340c041c1e0207030404050980d404001c000ea02c1a00d03000820640034900d451880c01c0010004450b0707c001d40e10443c4003042d42d40c1c0688400c5818806070401102c011200c0c100c0c410065506d1b0880b00501950740700b5801134a082818410308007d0501060b16038101c941c3d9054025216640008840c14400d5404e028120055880079280075812030120800e400a0801c5010300584001c1600458010000d00702403042a008500840c0900d040c07006c80140c4030f495500c00070b079404a19043d90390380000059094a500030703201d0f1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 687773534 1250 687772284 687772297
    0x19110319180803071101020c03070e071704060b010e0609030a020607060603020a24022d2b0e03010203070c02010503090a050102040902030f0f0c040b1e0307020c091f1401111002 78
    0x85c00d0901070f031004004981c0d5000301a01550950003825007000003008001a5580000b014146600e01c1d8220070600b02c038484044405a40712501c81b020a09a940c100f1103042242c00183c0d5440d10704070300e0402090740c602c42c50704024010030740069008107200c05513100401546d40280601a01d954070212605005a404a1011a0a8410a180103090000039031030400a500d00a544c0d12000d400b07044103401a00c41010062400f4403042d0724000380080701c81d84c0811081c800d645038840c1065030018009200c600714103000c0e038410010b00143d2038110035001b82035542460300c01c0d640d54a02500c20f05110807100000c0640d80041000300d6218455000b0b140b150292465101c502e5035a6a041d503199501a03c50281c25031080005002420402009101c24403103c400e11040c00c141d000b041800340d004680440c016004403442c81d22038601014511b420a001441c0240c00c0c07209080000e5010284d44250007900401c00c0007104164014001c0850a91102d01603400d02c06520215002950009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 687774784 1250 687773534 687773543
    0x1110020a0c0506011403280c0e01080d08010308031f0305030316140a08150402040e0c1e0406120207060e010212160c030e120708070b1911031918080307 67
    0x100001c9554030fa407202045c0040e078001d00034101e800107010203510406000030034424000b0140742c04808151042007920050403041d04075640c9600d02108c0c0c41c01c1404400164040000050041001c98140750580e50009070803030440b00d41c2031401806d04500340e0a41c4c0001e2950102000700a441c03814162004120245070701c403186104038031210390204d40300f850405c40103d0400fa0105040364102c0c0c18041100300050310041c5000c0c1c5900c400312012204503681005503500040060920001c1c002004510f00040341007030402d42085806803001c402c180c05d000b800d81d03001c1008010321085804c5803500f0049800215507aa06034800e10300601406c50f80442c0d070055411050005510400301e108080342c06a42e44030b41001008204071240f40c0800300400c85204864001c1100c0f0390a00510000b03007000308003ea43c81800440c0b04c0000c0110250340800e101071640d1070a081080030003200c0b040d9411700c9810064168042042d194402d258060308000c80b20203c1c003080039a4004000d240c0140074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 687776034 1250 687774784 687774793
    0x60c0317250e1e0927030708071b0518041b06110c01020613081c110c01141e0405100501090b01080606040302013903030614030c01020d1110020a0c05 66
    0x354035045110b02c003203040c0f0781c01090030703000150072184517090001da10f40c141158164440c0320800c41441c50704140e40588031103100041000800000146034200c0002d080c5c06d004c860b514000003c0d88280e98454034624409944002804024161041d0480c4441000d1034001c0309444560017040d085004a04910034403980315043c8042d0300000700b40f0301c1209010b00421048001d82d42e01541600315440c01510040c91100700140500306004094050f903500e84015102c02034410054203407011102602c0000d10404144418a050503540003210381c0841116555034442e440c220746800420a090b00d0101e203044004134040301c01e0340241d466150241c0c2c417401246c0f95074003041132a00c40c500c0b0007404518259401c22808511104010310405603507184103540d4000b020b1444e0303c3e0000e07501200002d54800062041501c031002e01c020b0440300394003d1030000d00c0c800005c0d544411200010084c4012403481000c3d0820030800104000f0000900395140e2082400141180100c0b11044520707005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 687777284 1250 687776034 687776059
    0xf0411030105160c02010e0604121b051008041a040b060307080106080c010c150906090c080d21180b1e070203041206060504090c0f060c0317250e 64
    0x341402410b0043d003202645043d01e1020342010342d104800880100d040c04602000721a0554443c0c018000500340c0030140d060030b4a041c076100c0300903210740e0042d03950360701105000e1109840c0c4140390b0305810414104880c243e242c1d810710303520a1051844903100c5841050401040004003a0070310b01400d016130448011645881d801800d98000f0300940703c180d440f00c00145246e62041240c2d0140c0c0c1d00510f100d042100d0220340c0f0a060b50301586040c2c403415101ca001d07800b0440302d10120002040018003414a002d0b8101c4018000d15018a60516280880d503c00c2c0c0d010000b503011924140070189a081c17a80700328601100905011120742040031099280490740480504042d80f040b003840e806585464201800141c1340d4403600e6040d1000c42d03880e42c0100c0c06480b144541d100719802146015159840d140b44034190000c19008a030402071150400e1000940009010416a00080c80c1400310386d40e180b180e1080085121000c0c14520032804080c0e010303070708500d0020454809860a408258 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 687778534 1250 687777284 687777289
    0xb0423010902030c1003090c0f031b18050a0b041a04150303090e04030207050411070c140a031e02042a050436060605090a090506100c050f060f0411 65
    0x81c0300540281d01500b00c1160042c0502c1c00c0c21100030000f81e18140082e43c07048079115083c0f903441c542c000305a40103440343c0c184280302403c039160294a16980302540d82070304114500740f81d000c006c20b29941e1680ca600101d548050603800140c03940d20301400810602c0095008442e003184014078082c02203280400d403108013206401e005043e01e426031108600d283c0b60400c61300744264002e00075411030141d0f241c080340d103544902521800c0d400e030085c1c59880b01c1943c10321a80566040c6e104035030000582c6440304140d140d0700b0301c2d142140e80208104403074203c900c000c2c00c000722050400a501900c0c003014548581d100071001040c500380351145c0402038050440640b0309219038010009a40441112241c020201b00d00006e14000d0300c030291104010000c1c40201036a035143c02c844d0210b131021a0b603110724180181418004d02684100b0320603414840c0108841038204161041000324000c14482442030800c90100340d003281e5800c81e106882c000c414490104401e23182140c03040c00f81210700d1210f1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 687779784 1250 687778534 687778541
    0x40510050a17070807030c150809100b0d05030a030e0f0601030f020603071b08030108160b0706270804060806030109110f27010801060b0a05040501050906070b042301 73
    0xc40000d0700c08032030030b42041080a0a04542d141041d00742c0300d2a0700104119030103010707a0005601c030b1782d42840b1103428402c00200450b1103184104c20000100d003008280d00c000502140c00c11920040020040340440102c2d19010311070401600300c0c400090040c4055a0652000804040503415514214007811641c0e03103400d02880b0240c41941c0c0b0980143c090318045008540141d0341781080a0842284001d2602036462440140c50050000c40104400301090103521806003141550244882c01c0611040d054001c003030b0083c1c02180e0710000c910042e00c03503e110741c6c0349840b401010409144989031450056226000b0040040e159001140c0141014040d5181e04c82d0b21400d80282c4001c08002d0000420b00c0031105580640000ca01caa981103140b58101c1d0700120b2284890690341c18010510700f598255440070790929020050152081e1340b14064038190344003464803940d41c40f0080e00284690182c10400703440d80c620701050004210111503a080c00000e500c06080d150a9080d0156089 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 687781034 1250 687779784 687779789
    0x303130606050d121821020f0301060807030f030311030a0f0c051815090d06090b060102030306152a21041208070203030c030c16230103020a0c0501050a0b040510 71
    0x1c44404400c01459a80154840c1c8017000310103a101811070303179a02c1030600c40c81d21020080503100e084018031040d41410302d042d1842e1341d07007078000b807090501d41404150350700340c0c510018016288450300356040501c01e40010000c405440082030304c80c14480080c0005224003010007004a10b0141c0030084580248140c0b008036990081143c9403040070800c1c80074048521800071445401008190002e5440e80c4845c9062030080000107094141440d0005030306c44041c05013410366105108111682ea56034418507030802c884543d01e62280d54962242c0107601c1c02900109240a0411003000601301c00100700743c01100300342e14030150740e0424005a2192240d4083c0c210780940c0e051000000c0f4218030014100140302a0850380340004110149080d80c00104441c806900003154542c4100d150303103203c0d005400c02c0f0094804404500c1c00d815200c0001410241c141500070030340341d5074180103268011185411100900044ca04510588014520349540c2c034801da2805001c103c441d03100740300c0e0805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 687782284 1250 687781034 687781043
    0x60108061b0307200d0c0218310b0c0c15010320060706090501020a0f080c0702010e18041b1e0905101502060106030b010503060a05011407050303130606050d 69
    0x19580f01c0784421140c03010f034014041180344620708501c44a035001c02c2584c8041149139500010700000384100081207280340a100c034010a4541803201c2c1980300b05003602d51884e00d4440182017001d131743c4002303119034404902801c039044041c1080304456602d4003d044842099080d600303124031132150340084581c20b01000d401e0100c86c106032107080007040d401c07500d4000001c0225041480c1d5640f48000d03034102420031135441e5004030700e02c0c2440b0340014814410203007500f401d406e42e14100c0c203d01e001d40100003019040003000b072454141a2121074003000c05d003802c20148101481d281c140809184030041d444072450b044014005031180c228101c0b841c10142c4003416800e854a03081204000d46005010618442c41100002402034206100048140c0040d00603007100e43c50306d00003800f2500c0e8018058140036040081091a41c0c80c044003100f0f50303609080c210310524034080841c556010303c0800030203038840002403144100101aa0b442d86911503103081c80210b444005104418994110040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 687783534 1250 687782284 687782287
    0xc020a1a07020c0a09060f05030604031202030403030f0212060114041a03061903030207030506010e04080a03090303111201030b01080a0305031623030604050c09011d0d14060108061b 80
    0x100100c0d1944081500045944115862818400c0004028aa0641c010704095170380d0b071010044071040b07192003402000c041b400307000d9a1030240c5014120304a40300304040031319400030016080500070f41c17002c414030642c21030031501d5580c488210344260750203507030716400b0989c451514501044d03840101d43c06d0301d2139a00b1840414507036174111500b0750805040b46911421040c80054441c0103413020000450296008110803451420558182007040c3c00150b46560000c040101240541c4200d509511031881e00081e00002410201c00034240d03c00a4000120001843c0c038040301c6240c4030905983c05440c6242d22030340d039111242d0362440d0400300200820008e1001030705400301d540b4000214943c50a14440c10800006088801100f03520b40b081c6044010050200a00b4180320b502d6000b0b031843e41c030501d04080030300041d1623800204130707481c142140d9064800440d100e101c106480ca03035000070140c0c0c00000e039111454851100740590307031052165400041c06092042184603000303041b0f0340d035103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 687784784 1250 687783534 687783563
    0x14010603150801020f0a1b0b041a09030306010c02060d150807090b03060402030c1e03010606050309010b01090b18060906030709150201051e060d12050c15010b03070302130f1203030c020a 82
    0x1601c001c1480c4822141c416407442189001c00d100c4a00c8c0c80c412071003034041c80c5030074000c1c01d007010043c030014082c01d050754018800c205890741c000305508401c035012652551100e0304040808003401200000b040e95020720803001600200c00580c12040c0d0340461424041292950181a51000205c030081c0d89030b0310400316828142400c0b000f0407800030460942305802c90a0001181c01d40d40d0319409080051000000c0080c4900203108246038641c003460049006072034409101200d008104a901c4110b1414411b0080703683c5003802c90304101006061242c80c2c0c03904440c003403c911164030421001148000a00c0d81041c03043c0b19082c403817110070844000182514420b0a006103000300f500303411108130380c0e0540200e00000859650649030f0340c0e03007036a140c042034030302414030491654941103501d04600602c01440c0711800d07243d100440c1e180058460119401c1d41090383c0b038a9100d00c0e0070417000c00003c200d044c44500300b245000d00a8505010780d100580341240d03070fa00101c0c0060104c12141440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 687786034 1250 687784784 687784787
    0xc080408030f040c09050708160c0c09051f0f05190b031b07020d050a1e031205090a1205090a1706070806010e030f030304020a0905010b0f0d14010603150801020f0a 72
    0x40980290050600b10b0080d603e170309103a02210815206600450058400c0100b800140003034808a81042e02c2c0c68041810590750300f0040c0c403418060b00500f1a160070009505441c0041d01c203581100c003820301c01c2c0c041c1e590089007200d04928004e03d8050000304401e00c1800c00e80c010a08111043e48114500e160303280000e0305c081e004082c0e19404e10007400c1000901603030710742a2107856140680094607030300e00d051030f081c80c07484860903c4a00c40e25140101d04007180d04803141e01891070307004a0202e0b0941c1c51318030701d0741410f201483c01410032104001d03104035194000040c04182c9400d03503000070840d40301e000c84088072106190040c03066008c00002080b1900c41c905541c0c0094041c10107682038412a000203007000b040e80280c9030b07150b0000c0104029032030480f81d280300a250b50307001040507505100717211609103d85205407c410000154449094006d81c0c080c1d4160002001c4201040d43c40e600e000700601156090302d121071302c50b14000b090551041c401c44004d002e840f0840340c0340c00280d2a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 687787284 1250 687786034 687786061
    0x10f0609090513300f020703060e0f07170609011107120e0a061713020a030807031205070306170607080105120129091f0603051f1502010c08040803 65
    0x548001210b1000f0b01a000918944109040d1100d1403151a2400300000c2183c0018500b64030500c1044814010100e041e6008681541529080500442c88242c0300e00482e280110080031540e0900c24050b001078a64443c0107071124080180b8103941c10340e00d42045090980d0603000c2050304400701040144001041e081410543d1826400e107041c0d0f00c503030400000c04405117648107501050440303404007620704078804020361000410325800c0c040111030300400c1d0f028120b0b00000348004400143c46090500aa045901e400031202090200d0700c3d040b140200900f900d841412001400c0355070b420780c840720106105100d21841c0e0f0704d0385c41582c070344000c12100034407174852a155950303219030082e00000c240030b1003114061800c881d842050224414892002030040c810301a0000c40200400c03000c10016601c0215449480c0c00f1886480741146903c5840b0b0586082c5030800c090540000c0c0c031040c21a0000030343c403160f0000c010000203140b0960700c02c2da08540c01030100d40d081001440403d140e95 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 687788534 1250 687787284 687787291
    0x20a15020109260f0d0b220c0309120c0807050123090303041109061801090c090b120105060d1407021606030b090115050f1c050a0603050a0b1b0f0c06010f06090905 72
    0x241c0410000f1160010801003070080d07c05444e16010a006a0a9400240140c00088806250820100c00d082d00c40c0c0c40c0040c80c03d03140104000882c0460780920402c00141c5500c0c941007070080001000d0030012107405004026130405046003a40000c1480c071010040d80e00c1030307030040c4003079072102410801c01003281c5004100301d5101c10302214182503840302502130350191007109000141e650700e00f070010b02804042c0e80304c2e05407814204418290301c503060301610704403441030720045e0300c83d00300c5808440901102d1080c1d401d8180e01c2c40070803848540c001146015011014800031426881e010128295207107000c0050304281064010080c200e41d11000d0b80b903400c05c502d041800e1901c5c615407901c1d0361380110b0040c29500e91041d462000104a4800c0300d4001022460400840c2d01c3d60342c0311519000c0032140a030841c12140c001545807142403207040c810401c00e039600c03980d90721103a8041105070819402c59001c1c3c45444000f01c0e0304010000d2000556841e51243c155180c60040c042d400b600b4020b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 687789784 1250 687788534 687788557
    0x30507020d080c0a200f0d060b04020d0e010b0f030c0d0314040e0f1008070f09020c010605040501090f060e090604080d181227050d020a15020109260f 66
    0xf0041800390700c01c1804003802c00780c4185c124805a0215000590465042032410341c03046c0f4280c810751840b5540d60901d0700707020394001004540d40b0001c0000034007e008415400200d2403c20400701546d14041d444454201740c2180d40314040d000400501d65101b9001608035085070740100d809010034015016030481031400401189080e89854044c80880b005503100220140c0780c01c1403040f900170000018014003c4400200300310740c40c00c464101e0319840361162544e9a0ba00050740e0311050020b41209001e00360103081031226583d43d030400c80c004c02c00d4201001c02c0600d4440082483d08002e14818003070b40b60311004101c1a01c1e161148030b100d5001005c1c0082e0270303603681000f004110030800c003e4070040c0106864500306110803000341102042a0f0416008001c0b40c0c04900340c0ba1042003001c1c10385005945a600d02c034050700c0130400d145c26035005005213404400352003180c01d5054001c44452846006080c02d2940c00b8141d10042e200004d1103d98003c80c01e116041541c052031016194001c0c00703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 687791034 1250 687789784 687789787
    0xe0a090e030c0712020102060c0f18011106040302060a0b04021c1509060f090518070311040222030c0b071226070f0305151e0105090a080109030e010507030507020d08 73
    0x2042c08146091200e0780710352410000c680764030040d0768052010a42c4500c040411502c3e210540e4019180391103210103829030084101c0c49a01c250340b02d07401c2212106240c078110f9015090505000c1e40c0e80310110340b0004942d080081c2d4840c107050a009844180e9034031000d11040210a80118001e4807150400c24520b80300000001000d03100740c0602c0c0000c0c410b0b1445203c616080050000640c1c1c0000d028010503100d5606030810407200140240c201c90700b1044502d104034107100058042c1c8190b400c0c41006d5100c006034890000c01e17048041080702e2040907054107945c8e40c0e07582c10809018154010309a19058007d1259050040030b6088070b00e02c01d00c80d0f031080c041100304c3c052171f04003082c0ea4030800540c1c24128200a00d8061140c2508005031201094008440c500000c92600c420100701587c4684c840e00d4040d0340e401007040d90f880750001084520341c15100e203956030080c4071500b01070700040c0350000e03301c11a500a1080b902600c1d0159240751426165409100ca9541c211408a509690 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 687792284 1250 687791034 687791047
    0x3190309080d02070303180308131b23121f110c060601080a0e030a03020d060b04080a0b13020109050f0121140906010e0106080c04050d080a030c0e0a090e03 69
    0x99000070603902d0b00d180001030711001d00d820000c0c106d41e890101081e507000600440f8011039084940a6440310300c4041800003050039260070794000400c40b445100c006c0c0c8050000c40c0301d1034010b01444035613603140c159410b1585840308001520070400c1e41d1800940040c2d0b126400e13091215000301c1881c24442011034842e4103940e00210660007105041c01030780040c4d05202840d0781c8404265080500200b05020100d89901007580b00d1054500000c141640016040740904464020704010b0540742c10690b184c5640e14141900c45040c41003c903107880c1181d000908461481ca42d0324526501a51440282c134108400e0000e9100d40030000c50602042d000074074500d403142020314280021520001c1071b01c2c61109000349142d03c000c2d15501c01a04400700500481d507405e1400d80c1100d000303242500d201d803074191b01e045c441d2285400c20307a04112040035000c00e01c1045802088400303100d03a000c1245c61070101c42240c0d1200d06004080e072000c0710540c100840e400d15009070003200c0201e01924608ad6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 687793534 1250 687792284 687792293
    0x50906060a05040e04110a0b0301050f0409230a020904080406021002040f05060d1b18120803150109030b090d08010603050405071503020d1401141507031805090a140c04030503190309 80
    0xc7c080da00250b104240000140064200001015001d0200ba1018001c1500a40e035800750484008203108085a201304040d013500c00070071004c68080c0d0044c005000905003420041c916038068000ca0f0b01605c24982c41d00a445414407c6904450805d0207103840141002e080001c81c1e4000f0040b0b200c52612038100f281c0d00c26200440c1038013680d241e1285881da1814a4000c65820010351025440d0100002c0e00404184c114003100c2d403120352414002004000000140c5084c0c1480e00702412a0140c00108a40d803000010f840c000d0f85d1032905c50304001e0380e13289822000e4540440c0c0045c159007001d10200b200410302d03c6021024000781c02d0240c24580c031001c84a0071504091080443c60030210300400503e00c820745200c3c0c66200c01c0c0e642802c1310740319a1420880d4440c00e0b000904105401403e6444810342c00551406000014041522401c4c0000d0603030117091184c03030401c1c8040320203020903501481c900c102c078122640310703003c0c2d81490116621101306424800380e9109040c0c13103101040004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 687794784 1250 687793534 687793549
    0x10f0918090309080a0c05061b030705012c150c0c030d06090c0315120510090609021806180a270506070c15050a0b04050a06050906060a05040e0411 65
    0x50000d480e000440751054100102002083d07840001d60f600407840c1c41020460380d0004d0400d0b20020340318030795500e8001d2110003460180034000c60841c0008983e003401c100c010340204c00020880203200401c48c54a8100980b03c0700c2201d804c038151b6100d440c100b01d12180f20508140d20882c0b400d8a0b0381050b111a100d0b90459002217a4a01ca07503944060070301001d00948122981142c45280c10451402e00c47c803407141050040c015603c00101c401340031000c100b030800c00640d0042501900303004a81b500d182090103001c64404c103d2280105070110750304c0c40c0f41c4001703880c4034141c01842d090302c2d41540d060341d10320708002406180302c660701c40d07407100841001000c0744501c04041074040f818070785540c2403180c00c00e58041c200381c04001c003d480600108409c4c0b510a226032030442000502900d6a11904004020090304c1e40d42260074441003041c01413140d8041e00480350309030340104c19a5182e40800441e480340c0c0941c00040352007840117208800720210303003540c018821801d101b0004031880004001d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 687796034 1250 687794784 687794819
    0xf1806090602120a02062413140a09080316140a05040305070b040302060910030f1109031902180907092901050c0d1803080d050f0609070e010f09 64
    0x4142126020400d9035410026403052110310018103003800c0c04d0400007916202d014240148840308121900c01030001052118100e500082c994050b1203416003490001e02452920a2011404040001c8140c000c6018122009a01c140c80c07510311703070340e07041d40300941007000c088003003000100540481c1d8078205100604420000303031207180d1128554945071f40750800d960485080448284401c100688070780c0141c42492900325a00e5401d400c0814048000744401c040e000305990404500e01e6081714500024803a0203c00d030300369844c1110b951414a001c2c1ca007820002c0d045082c4601c02207840b00250520b42c1c001c583e0f03206a441c0241c0e00e008240564118030000c888a5203100c0c07440505100c90342c110440b000e000e0a006c1d080000000e4095199898107030705600b03204400c1401c0408050900640d405540d00881580c0c5034101c0105e54030003440b080b00d2205003c800e00021a180785071078a04d50340302d280d5541c0c481800b081c80000441d2020380b01c005c00c1c0c0c1400150b450202c0c0202441c13004529 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 687797284 1250 687796034 687796037
    0x81b1308030304110312030103060f020c010f09050613170703020a020d0b0901180f03110c06040e0a050a0e0a1203090807031d09091e0a060c08011e0e0402010f1806 72
    0x1228140b82c106054240c46a2184e80d00c01e43c030251116580800712003e5a04581d0001710009000d4843c482e840042d212f101d1062146e07500e00882041c4544a95110328125800740c000c07601c1e580d94406900c1900001090090040c49400c251002000b44410041c82030a1103441562201c0c1c401e0b07400f00700320003c201d8003140c05100316403c000e400751092290b9003104000c0315220001000c40c1d183c0f6001c2aa0500000d0100700a1043c200b0b0341307490070400e5240116020305003a03a01c0c0e80e1141059801d10b07080d90300707110b0f080c100404101d100807036002d0142440c05040c050286201c50b40c2d02c4a4294107449514403d00d5110240000419271600280c40103d001343c8034a03041e4910411499140c01c01d07944c41c240701b400088140800060005a01d2401c00301442588a0391403001d440d0300c0c0303080e60241004011605000b103490409910003002d074100c840a10320305d151500d42541d58600700b02c02d40512454102890001400b542c8038443d440d40500e41420040000b5980040e4105c004d55143c00260 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 687798534 1250 687797284 687797287
    0x513060b0f1503190209090a090203120f07050606030102041d07020a0606090b12152d040c08060714030c1804050a0c0e030712030f020f0f0105011401020c01081b130803 74
    0x12024490304d02d9800070040140110304d40a40c9000040e200c0e1800b81440c49400c0c2e03141c80c3c460454030100140300030a0f04081c8100d4503240c40d40540d006560006404403010b004040205d1910b040c14001c1d20b003912f00340205a042c181105a1607081c0d01d0f0014500c00031407254a26520210b040303846030b440948500300011860901381810700105400805892840c3d0740b000005116007054442c1054201105580100240d0b280d1407450282003140100d20800d41c20344004e04c0104008a00c0b8901110545402d450083d40e5005069400c0d00340592259402030301040015002d0b5007880042009040840840b842d40c54200c0c0450101c450845032403d209560302c1c18080595080202244420021402026441d0034800c0e08001c2200e40c140c000c080c00b58920060780507278007d11022140103220000c82e17080b04080b0b200c0b14040c000030b1188103049500701409601951000c50181f03024001a140c142440c1c440451203047e03144411841c0c00c0241d01406480300d074000300c4100ca001008000e0045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 687799784 1250 687798534 687798541
    0x2030705070215090904241e0c09030b0103260a0806013203062209170c150c090604060e0406080102030f18151306050a0513060b0f1503 60
    0x101d800e0904080345018100c0038040595140e507200c81682e88142d2140800d005107c040e844800300303e03244880e40c242107040c20f444841075403548500030400001d03441c050204005007201500c4007030343c6000281403440c1b15001800400d00010081d41c001c5008a03941c002841c0e1070050848070b030080f001d0100080d4205050100d250385c8403108500d0350340d01d00d4100001803264071000d00d1411014076039140d1260701000080c100c0e80c92240f07041801c0406680b52000c0c1c48c482e54450018401308030101c0d00000c440d545d142860303202c00161503210007484010107162250704220384021500411891090310200f20707200103925420301030402003040717841c0c51030f0180405c010032040c0c44d01604460541da10501c1081412403550207603907041300c0c5441420200140a403a07541c00d165503a4180410841d60746d042c00700d410000017480706110b00480b820000303601ca040d410001d0310802d44201032140d1030384046c0741c0800c0b810b41c0010a060401008448901c400801040d0341c0402504490408000030040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 687801034 1250 687799784 687799789
    0x603020c0607020607020d030b0d0c0305030304170703050403030c0c080d05120604020a02070b1308070e0105090a050f011814070f0924050906070b01030b18011e0519020307050702 79
    0x10a9040000ba002405082c03400c020700a5894041c0c0034001d0815407103800e88801a207901c0048282c06030044c02d89009141c03a0b0034681e90f282c0c8147c408494a0400004200c07042c04440705480c03240343d00d55500383c0b5091464030122010390010405540d100c0230346070f00140080301003220350364000141e100c558903600500310b0040c40150042c46103004500400a205100e54049525402c0d074980344482c6c0d0300c80c528044040003001d800c2d048580035104081020800540c0c43c1c4803c0e04850007142c40d0f40d682c1c0c2c1c4201303d40c0c0503260280d451102c1d042c41080180501d50547e0040d6074024805072000070f9441040409204510017030f508140440c215040d07000203a0b03806202c0b4809061075403000641c071100308440050076260402c5290400801080c2641ea40d0740e1139048404898008400c84915612401d09882400b825501200d40242d070758120516000306000741003103220603114a40b5001e0010024001501000b04640d01c55850a220810b45490a00c0a5802222103503249515407a0500c103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 687802284 1250 687801034 687801043
    0x140f0f0c011e05101e090213080f01050a0506220c1106040f020307050111250509090d0905031f0b04180b0106090b1206120c031b030c0607390603020c 66
    0x2c580c2800c110340f403d83c85035140c0c4400f17450403203020010042e6500740c03072110f240900c175080d003080d8460701400703204c1113100005410540c000c034030060741081551030b00800c006000d41c1a40b00c00c032a4842240d0342281600203075100821002150a100600c03509882d10345050050071102107404c128004c0284096040c108034100c050a000e09000380c0340c11a0b0a035140d40c8240c0c6219840d1032883c008445480035060300404001004042c190304403508202c02a991110104c240e440001824002c00041a24001407602090140f0354010356410007c00000d00240981440141d08070791079521070250014681c0c880000103014100d101420350503c500103001003150350001440a005000ac02045041d01607010703007020f0f01700c0700c24070b54100006000d400d052a03d03e109505020384d445120b00943d000c42c0742d20710003400f03c040c1e81c2400320b128200103c40c0141c1c44080c005040403201614441c201c5205900d00d444944030b0000310900e0303501c00445140c2c1075000080082d40215003082107000411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 687803534 1250 687802284 687802289
    0x1e0309060109090201051803160b090f011d04110403020907090e0709030b0117070b0a0e0109080f0a02060f2502010e0f0f21060405030406140f0f0c011e0510 69
    0x802c28098811550002015405418692504014a001c40301441c3d07a0802035442540c9010500801040d9100c8110007103800c00072003980107103070000c1c0441c401e600ca00d00b803040c0f88040c0c0d864a450a0440c1044c040105083c040f03c8a040e0400c110220140c0d8404044038846e140c2c90f40c96443c00d505011510702d9040f000741a000034032031044001e10015100100c42415180040c5068006280340b9030369925240c0e0f0396020031031220001928a902d117503c03c010181c540c00c02c1e2608280c0590350302129544244214100c200c03500044191001450304074014003045203409103003818010003071032180c65a0041c41d841040c600c1407140c40da0440d40c1000c0c44404080d421658081e6481c0f0b5480420b02c1071340c100c1401c074426000c105030050150300d0340d00035038a43d004a40031100301d4a01440d1542e0b0340d41c003d004940104203401a4503528444250031620f00d103081062480c144016580280600e0b00880b000d00b81554841c005169401e100340040c11801042c0040882c40d41411440c9403d18a101c0c1c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 687804784 1250 687803534 687803549
    0xc05160c0303090909050318031504060510050a080c09060d060606090614030411090606071e06051b1905040e071d0604050607150615020f1902010210111e03090601 72
    0x5400101080380841901c220b11912415a8234842d0030000207424484030b8124a440301c203868040c403090044a034401445208581c0014807650389860812494080a116851066028210000d401c1c01e04541c0d15401c040054220702040c89659665011f80e0f040360015000030348400703801c002440d0f20407460303007034084144c0c402495410715846001e44071038142201c50145512401190954a031079048603440e039000030400721840c18900b80820810b075540c100b660401d0401c004250b0000100c0490903844001d036200c903141400d40081c113001425a0312400c020f0140a120004104d251480124400c001e40d588844002818584184c0f2109203001c090b402940c0a01003030286441e03542c11a40419000519241c00203088a0700c1e802400107908143d0000a1518020001c150002006843c6507050001e4545001c44840c900204852100000e40181d209c10006e0800070120762141c09040140c0130518a89000031503803101e50b29543e0106d4060500c00010009004c5050251501602c80f4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 687806034 1250 687804784 687804791
    0x50d0f1109040b060d0f05040b0907050109031b15021c0201050105010c02011202091518010c08071202011103010807080f07050604030b10230306180d030c05160c03030909 75
    0x55015003100d80901d12065010b180e031500400710355034604054580d8903d80c401c0a0143c200c61107460f00140c242950102c968101c01408216000c00110380c1405603441a03441c4c1050501d10745841008006c1d0906148189425040105445001300300d0540d0590044e0001c1040488401d000001452813107480401c44e458100184002d030390000301482e08a030246000c00d90014500030110003031281d0054180c1c480007400401e6202c181301d038080d0025440c05245046451498801518812962040100b02d010100316407000901410a40801c2d9030980c4000500303996112a080d840d90710a030021111603000380b03c100410131007048200ea050203040c010f800403d1802001c108280501d000c01482280590700081c0004800c1542600501511034040b0b814950905803117401c64000034090b0183c09000d0000d00300601110b09012421403e03801000c494149003800c500400401c2d104908101c400c02c21078204420410540790102c0c00b8015024001d0302d540340c00340c91014035509c9070300c04a06 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 687807284 1250 687806034 687806051
    0x51b03280c120c0f030f020f070c0e10053007060203030907230f1305010b1903090f1203090206040b0d05070c0c03060f020706020d0b010f050c0303180c0d03050d0f 72
    0x1400381301c03900004141d040c0403912400b2520014041e010700244900c003c8030120302542071010000052045407034448040010b0f4645400301e180c0c40c02d43d400350b184c0040e489012000310103000040e903030850314108102004101e04540b400c1c1003030000c1d440403006038000b00074031400c09001d0040d10010300741c80036146490708036018a0300d0002d000f510127900c55640380d405c641c001c0e10b5081d48128048200300c8200400e40c0c5070440513000381c1081c01e451444414501d01d5804090080c4682115140c0000360302c10140c80560311a42840c41880268007015102d0003100f0060301d03402c0c0a04068168540b05076102c0c8506103d04003221b01c002c1c4120304100c0048001c4002c9084140d48a05994010102007200c28041581c54044c1c4201c1400400c0c0c1440051055000e41040d402054141401d82c0c40749a03164801208483d58000c1001c0360285800810116035030000d00340c0c1107001c100006d030580c1d41d000384140000b09180b458040c00e401080b4001a6807500180e5881510012410100100111003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 687808534 1250 687807284 687807287
    0x130e0a090c170a0803070c03020c060708090918010207200a0e04030c110d030e0f1518030c060c0312010b0a140901020f01150315051b03280c120c 64
    0x405074490042ca802c0c1010000207111400d0040d50032007908a06002d541e420030b840300030200d0007442001d0340180075200d030180b42864001c04440d4616080046030b030414081c1c10810181c3c040140802d01d6481a030140c02c051080c0c20700140c0043d9020341d018040e90241b4441c40f070401c0008485242c46a141484240700d160014021203800682501d424008a6054a000941d042115258641c01241c0083d01010103510200004001c3c005542c19411007102d50240710340d90090400946042c101404141c0322201c2c942000e41c0044070007000c580c0064101ca000c504294071803800c0035426040022025407884242c5034103401440039940c024a44030b45e0210092250050307094400b03404030001869151a803007041442d010099440003041183c07810141a40c00c00c150388000c80710091f10035026141100315118451242910750912804510f10310703481b200580c8000c01e00040405205000868070361002809441c0381810b440c00a400d1031300580103441c80c10404030031010f041c2810003100505 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 687809784 1250 687808534 687808553
    0x21203180a030c1a160807061a0f13090206041e0803070b06040905010b0a080607090609050a06030c051b0c0109091803140d0207060204060f02071a070f0503130e0a09 73
    0x30b5600f4004004100d0440300480c2291042060301c80c5c0c94a40038500406200e4500c005100c4d81d44120070800814010130206d80303080f407144103003551042e0320100b1400c1e5410190a0b1110404000000140c002c4a91340041c2072034107d50425044007070002405080040f07105c40c1c070005056564019401c119242d62045c001030b000403c034a00440c3c445411808102c0250030403518054024462807440c4c1d140d81c20f0036601c01c0110b07440c400280c043e0a001805034003c0861006607a8013030800001d45003000c9003500a4150780c0800800c00070200068100310400312281585108048080d01c2c5a20f866000107040720780b5038004200704d034988103c44410031501e07500d45030304507410b0610395000c00c1c041c0c1c0a150540205819400043c0c00059140101f1990398000e02c1911016254440c00407420002243c3e501c205e40a4800d241c50403040f291520001c01c0003804849100d80d14030421034000c1d585140c15074020000700d503d00b594181082c01081900c0005a601140c01d80301040041801e4442c0d0544 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 687811034 1250 687809784 687809789
    0x90e0f011d0c1e04120302010c1b05120f311505070f11040c1806050405010807031104050409060c0807032306180708040308012702030a0603021203180a030c 69
    0x564841105540050681d01c0c04d40b801030104940020340c488403810040e000c0c0488100f104002008415400303000d02c1c1611400c1c407800d0708480101002d0403000234a41c4907074803480d0160001081032000320100e424010000d05d1114800710414400d4110792070364800d414054000300740d000300d030141c1d5039243d551050940c3c1c0010742000500035030360740d0741c10701d20f41e03030003031540950303002803c21071280000c40c0c1084031000d161030400c840ca4003041d55a8070440381070140e40103260001c0d0440d00810811032180c2c00032110000d460042501d4581c4e40c43c0020b0454002442c226421521000b010b000203411107003c44d03021500d41403c1c0300200d049048031031304d105065502c08030380308040c1c0032842c26180d03000c102c1c0c1c4001d00c0a510014904110030050442d40c3c3c1120103c00103280c4000200b141c841d10381c0e0f039042044404c212100d00c1611312030030b040039400c000c1080300e040c4d40e9030070004050b999603c251852242118051a42e900282d60841204114640b1582c0140010601000081c80c45074000c1c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 687812284 1250 687811034 687811057
    0x91c140d0f170a1802100c17070308060d061506091404050c0a05130e102d0312230301060201060504140105060a140c06062e0f090e0f011d0c 62
    0xc0481000031070013403da00c0100065002031140c007044d00c00a800c508038800003802440132400c0e2003404400340300c01e48203900c40140002c5408010449070700701514599202440307220b0101d61180c001580802c03c40c0c0d11b520103000203000071010020110141204280044203480501c21484c05882c018401d1103003807a814100300d80000c004030908000c410210107000185807001043c01d00180c800403408032070007080400d40307460400c009181c2804017000307508421918083d41c16881c640b1054155465080402d040c4045c2c008802c00c1c210281c0d8031400000202d00b8119100c2d414600000d003107400c0764100c580074901d0900c1e0310701c944560003c400d0440700102c4495076280403c15040f6045502001d416566910125820303110010201e101e500c92b40050301d80d813107440008200c04040e24000d41c01107900461480360003006134440d0545152280b007500342106110fa84581c050103208040310f00400d0409080e0041c02a204500010107801722007001d000110708040943d603469100700291101c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 687813534 1250 687812284 687812291
    0x60608092d06132901090c0306150c1403070203030711240301030209071e03200c010603120c05190204090213240803091c140d0f170a 59
    0x42440c441200c80300c24804440282c590504081107aa10040041c04040b2a03a1402d0f501d5010040c403456980c1c84225860414000c282e468414104020f140c40303800001099280c40c0b020403022038207100e180600c034140c1d50b0299080e00508026040161a010419090b041042182e01582e000819102c1140e00200001d800e090003c0005d10503250248004902c440c10170602c603042d00b494005036040742e000352420881c942d11402e041b41c549003540c092106200c04480c824000c1403080d4011904d5601c5a00821102d003210400000c068201c00c2c10007440369110036040c0204130006000303041a036014101004007040343d81da4991507030041c1c0401c000c8140c1040c841801d550311030308000c0d0040d402400107000c9240c0a40050050605a0a082110041030700c1e400001c80b0b07050045021158050051030900f0900003c000701035000c1092100090801541c0d10301245041000031080d41d04500140480c0c02342c181b0150014051040c040240405213441601300d11000703042d84e034020078001d13000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 687814784 1250 687813534 687813583
    0x90307150c02010e280306110a0914370b070308010501082d010806090705060901030c0504050a090b3a05160602370f0c03141006060809 60
    0x6038042c901701c0030240c4d81a000c00311302d00b2640a07000c2d2601902d010355010b10481100405001c0c1e584a4850030000040142c01c0c100001314004d15000d0819000600081c1e0607080c1c5241b86250384c102d607181d09039140080c40507403e0401145812001442c2c85032142d4100307201034401034002030341446004c3c14409040001103400c00b840300303000e00e10f02c40d07040c110f03007182d210405da50160780d424003030001c06100d02004035500180010701801240d41c0100350310720f80b41c5007400460142c02c1c0d9003203c4090100c103000100b0321703603070314000d07140584003502c000130b03c0c0304500c810011140700600001a90f9200b540c840b11048601e00054000c102e2041c509511100c22440c01f2880c102c139070b01ca82a41311070010000302c1c1c0070b94082280d00c1140e022800780c41c5400910075000300490110040c0307074004500826070310005450000040c03401401400802016541e03a1100a444061912410702c503400810901c4200030700f5104010241119141a8005190032005540c0d581c440c1c0f845440907605080c0d1070b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 687816034 1250 687814784 687814789
    0x31b2b020708030a020a060b420c0c040c080c030c0313120c030e1215091f0203010501170f0a0e0f0d08040213050c07030c0305090d08090307150c02010e 67
    0x24008102c440100c0f80e03100c411900c0207464505501088a482e030a00c48889424036200305103021041c41903240c0d000d0109066040c1d0100350a07000300b4002c080c00b40d001c020b04200950054100c6200003005000c490307004000b04422034460341880014044400188060030f0160403c0c1c0341c1c03149070008915500d44070034050205000d00010000c110030b00c00f00a10200700d40c86468044001c0c4240c803025000b1951600b04140c4284c0f81290000a81c0700c400e404100440324103c003038016031007500b5203400c4003003141c0c03411003000501c2c2498901c90700000100050350f442080301c00715020900a8004906140544206d1103c0181c500803d5640b14004071190a40911010300d00c400302404460709600a4800070b40742d042d00b150160321466034165102052000c1c1c0c01628403070f11524200c180360003a42e03a0300fa84c00441048040e0100304061066031120f4a45418100050f8051041543c883c8148820940303400c0d00350300240c010070045d40d4007107075441d000300300c10035410750900b0107461502c4004c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 687817284 1250 687816034 687816043
    0xd1e0203131415150108090f1515090c030907050103110904051906081e0d0e1002030d020f0415090f060e2b050f06010501080610050d0905031b2b02 65
    0x14291460300f004818080744488140c1220000e040c06e17290841c190361000703032940d11061810386240c01500506034906403001c01d4146580c1c40300381e0098202c40c80c561400815102c05003210401c0c1c00c03610000600020b203000b001400c0041509103003e0003516040026602c1c240101201e81c4d0059803a500860f00c070189500603010004030001c001c019441d900c0302c103d40d407034408480714440a080441101d00d4540003241000d10605603440b003d8041d42d140e03040c00810300341500e5020440c001440b1020846805000900e00100c1300140151201d04090040840d0342481032005c044c40010342d8100081040404400212420b07800d10440102c1040041080110860314822303125036001203195001e00041203140103280160201c8068400c1030030b80e0390740c03040280545030215901d0000a226440c100c00f8071050b0802d40d00d0400d003041c103610b6a810684003880001c8405420104030304040e644620642c00140c88100014803121282c240c5650103d00719251040800b220300703120803c003a00800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 687818534 1250 687817284 687817303
    0xc07050d020c0a0b031501140706050103050106030201111606050d06050909010f0e031c050717070e0108100e0a090804050d06091104111602030c03030d1e02031314 72
    0x41511000c6504503030094481c0c2c5200060b9120702c00303180300442c0310702e5403d040c0ca12480c4406a02038140082c100192080b0004100c00c0c010741108000c080c0018045000b104d0081d84110700100d0070702c5c11403002604c40148401e084030650701c1962059084c5c010025080110340550070260303074a03c0140c80ca90050f0001340c02064200c082081440074010301540f2007422071203500e10400001016a034040d85a00c5100502a01d024000401c071082c2004d42c0d020704d4102e00f2504181114160140c5001d00c208030858054002c030341003031210245560050041e0361b1002980c007081d20309600340182883c46000251504000551300c0c40c90000704a604c40880f406824001c080b5010241e15151000207000300318000c0796a40c88120541105e41094040c0e20710850114480300d0410f10b400c544040701c420234404c140d81c1481001c601004a1b2014001007000b090040360100307902042d281d0f100c081d1202800d07240c400e5441002003100c1d551981203101400b55200c2c490040141441c01500d03c2e28001c2d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 687819784 1250 687818534 687818543
    0x71518120908011d060106050c07030b070519020307030e040203280204170706030c020a021302211311030a03140a0215011706160e042c010203010303080c0a05070305030c07 76
    0x1000c00c8042c0024450a813402c540c40c9000c9802582e202d5104555501800f10018895030000380c0610004510520195016080d03240980c240003011a400c0040314240c0f0080001d0b030400507140c000e040d48040a400a0301c020f450551030340c14440b204000035a90290210044d02c00300c054403050b55181d4044a000b008100b205019406440c1b0950303856804901c104c1001ca4549520f00480500118540002c06d40092043da80d5010600c14800a503010301c44020001000034003151200080c0182107005a14200121036600d059150004e854900e801e0154440d03440b41d1050700c0007030341c02034215a854040340203144e100c042580081e4a010705290388984c241c1c440c0b000100780c4a001d00807455040c0d00120840d880b6481c0d8504110403451110006000503020031302c80303145030505400200c5050290801c9220743e010203c2c0c41c0d5074485482400e80401c2e50000010824554401d006a4018425201c00b07807811807643d00141a5104014000b81400408000104c1c2942c42c2c20584030103a400c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 687821034 1250 687819784 687819791
    0xd02040b060d0506031c0807050a17010305061e13080a121127010e10050403050129010203030f0f0a24030c060905031f021e07151812090801 62
    0xb02c0c0300009050300300d400a00078801c981046545910a4031405901c5226071100403003038880f42c034112980d9001c2c44826040c00450a1000350b01400c0e42d980e20300850045d000b41660b82441d00c0402d105d0b90301e00409210502705001400101e982c10507200010543c00484150b0795190301a041d01c505441011840c24140b910140e1448041620000c1250700d40c1400c01c01c4c3c3c140030300c400824404042040d0300380040e0640403010407a050514801240810b1424201d08013170342e81c2d4030103081d260403c2d40300031048441002500c40c0e118038075802c1d18007442400507500f940740041c50b505140d0001464580d03d112440d021462074240342d805100220380e04804d01d115441503011125041144d40310480d8030158210000900c548904989402d50780300801500c1c1c01001304040851188207036071454a0700c2ea00308104c1400d07940c500d000c40c00920000508540303403403403820102450059500c800301340500b00394040800c031005207020300f90641e005821143c28202c151040782d512815030041507240d0318 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 687822284 1250 687821034 687821047
    0x1b0f080c0607031524112d01020f0d0216060906090201020d08060105040902071a01030c0303081b032212051206100203040e2d01030501050f090303060d02040b06 71
    0x1c9411031107440e00e0745090010765806144243c21100604c0f0300d840030500c200001c880416800710701d100310407203854048102c401c5412424145040c00750b0032004402001217804c1c8085003c0c1403481038441a100031403c2c0000c900400840b4440c995480390705d20f60004400310591454403400481c0c9070080d104120020082c9407039001804030540a90140c0309102000c2206842010168800d080c180c0d07505007040d1601100c03101a401010048610b104002000300f08140d420001500850184161072546c9280d230601600d0b0321030103440842110b401d00c001681c240c050504403a0800c0507051600388030300701101c011110350142c5074000c05550003c04d45800d402e0f446005440f074030000513440c41003038030b0310801c106903000d907100c140001d03030818841080400054000150b000b1019940c2c4401105030001c1a4602c2c0c00b8403450f120601c00030341c01481400b00074410b281e4440e000d412010f000c4d00f403030405070740c0e80e000c000c0900d8400d94003d4102c200310f40f2950081da13000c80c0040d015649a01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 687823534 1250 687822284 687822307
    0x70e070c0b0603061015050409110a09141c050307170d0e0f1203090a05100906180f06021c1b030c08070905101e030c02010e0d1b0f08 59
    0x15500001d842031200396000c5509032601160450007049941c1d00c0305503c80c944848160681030721240501402400d000014820320315004810b0241c5c1d00c3e10341140d0b0f07520312090283c00381e0415003040b01030181d81c404c0d000c402d44448480d00800c1c503000d0401c02030860305203409480c1d442011802840680c54514402e00781c1c0c2c8160240c0a07030700b401401445801a00c0090310f9403003101c07020780c1c84c242e40008185054182c403500150b41108401d8140d50160420740c40e030500c1c000d1f03104210380c07480d03649030650310512034280304402a03a14419203d84810400e5128045664050003001e804981d0029810703128045000705c1c0d88030420116428007010307001c14044100d0011407090f2001107130809045c011031503c140c07102071180e50503850702c405090804040c031110120701c1d007003070050150000e0070401585000324011004107582c1d50105451000700002825100c130702c51188180e0b480412100c440b940c0142d540354000d46001008140d01c81541040f1a440e40e40d410040d04c0924002850404034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 687824784 1250 687823534 687823547
    0xc0b1201050f040903080f1305031b060a0501080a1b0f060e03010f1413062007050c03061b0c01020f0f04080c010e0607150f1a0f061812070e07 63
    0x2240101d516180c4400c140d400d003c150703907082c840100050b05040010315920b60140d41d007a0400c1c003640401d0000300940d42c40d04e01d15800f0030b00c14100307009284d601119002c001c01c00c00d0781c010b6405200744a194940420703142d80d14ad04460003412441403240c1c21102c20007914040e0000c20100880b0541c8613581c1c0b001900c580300e8030151a011b5400c22805203100c240c14000c0d82111610520290100d0741d40007150303100348803445070840d80280c0b40c0c0810003041d18200001402c0300920340b503040c4e9450f15890710520b888031403000c00d80280c00243c100107041c1c000c040310010450b546600030307684810300d481c036500a20070041c070032000320750201e1480354080d80d21019000340c441990032503449542050064803502c07480050b40d584140100030300c07800144c1c0ea048607400e03003032510808250b54401c0380804003500d0240d0900902411007591402d1145030415256414000036540b40e450028ac2c1600c0714001d114940400b40030b1007e000e0100c17212001040807100a05040c1c0303200c51b960a140d240200312 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 687826034 1250 687824784 687824789
    0x131d1b093a02091e01150e060d0e06100506030c070215040306090314251112010b010e0d020d030c1704080312090c0306060103051009150e070c050604020d0c0b1201 72
    0xc0c8007610004840c001301048140c004096000e441d126030f880c0044003009144424111000c2101201c01c004094440c28090168080b40c4070b0301003a108192128a407074100018a21140c200000b80100034903111031085075040031804442d10f40d21202c90002c540001c10851401d2040381c0e000070300005100141d8081c0034020301c0782c0c0e41c080c0c4e00088041c9002c4c481c05440c07030f0345413940c1d08c580d40480d0a0700480700c480312251140c0081080e52101c80700144806100981140b11a519500018283e40c1d004111040b841011180400c110391a900403d0400344003910040c24400c50315003103400c1c07050020100000ea01c2c0e0303031000c80d1303140e480b4443d480e01c98002d2410100300442181c0032840001f40410807410000002d00141074555030080110007038440a8404030003805448400b0030018204c0c080e0b01200f080f4040c0480060340307044510304525000501840402450f00400f03000190042a1690010b40441790141d405d10b0b241859994030080b50702075262040c0000f0302e0a0720384071904801c1d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 687827284 1250 687826034 687826039
    0x140609180f01021306020f0726060711011b170709050303031603050c03010e1b0c0a030309050717030301181104030506060102060c0a0509090903131d1b093a02 70
    0x25200da40b005c09903540c1307440400303104240c0c1005000b401400e02c91030001d99015050b60410030034801c00d1803040d050410942d10341c4002041aa001c1880c00c909001c0c2c03045101010400d00700300c50318440010500001c106448200c84d242d00c0101c0d1510f44601d40741405010010143d9135641402d003405410b83c0d00031114400800d0030080000c2640c0c0d4201d041e00d0482c2c0442600e20500e0b5a410548442007840da0417070038141406002c2c440606404210322a500c9200f40c0380001c8500c0d40b402e000d0b2400da590340c80482c058094584003040088040192411100040d100d450401048541800070780825100002e600401040000038860000f1311640a4071085e004e6440e03e031a80082d40d0303598401d4031000d1001c200304100200c0182452200b495100d4804c01c145c034103000c811049a44139404690013464015241c6800c0030f10110300d41000c54009034101c400c0e107503520329a00c945015010369a01c00b44110380001001b02142c04043d0420300e2010180c1c003694100d1240c2c00e810408503041d000990 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 687828534 1250 687827284 687827317
    0x114040b031017061b090a03080301080a0506060406050303040b07032105070f1119020a050402030901150807050904021011300304050c1903121e03140609180f0102 72
    0x903c4400450304c2401a070b03000d064140700010f00c0441c0d50306a804206210341080c60b0300400004910948003031030281c0381c0180501003140791800c0ca50310342040a040c15221f5840d0840070461590000203c030119800003800a44071241c2e400c1c2560640001504c10700030509143c2c038280ca40e000d03988120b01c41c0400303444200c02c080241e50112044000c03e00f0020040c1c8c4859086007561030b04820048a452005100320b21958803071011030143c0c2c00545260701c603030317440361840c428604058281402030140c807070050480c14500740005055000140002c0d0051281c10980009544581101190740c848141210304150b601e10805502c584100c030004601c841d0030030f240050101d0203085174080d85c1c00c01d004182e401c01800402060b18003505504014200c0c0072400000a14900d20120001c992030b1244c1c580d0b4900c03112441014071398070b0300c41d1003014601002c5000e42c21f0741001054100c00c06642849140d034500c500b20126145040c0d44442c54800c2601d001000401500100301c075614441480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 687829784 1250 687828534 687828569
    0xc190201051009050c04080f0c1c0c150309020618090c090904020411070212010501051017070309022719060b1e0405090903030402030d021207020114040b0310 70
    0x12401c9510984009a0001c0054410046200d10303801558015140e143c0c014506580c401580d8034110464125100c160801c0d403443d00b031890b0080c40181101d4a0030091481c070995a80c52500050540c007445041881d0715442442c0d0728440c0d840100c00b154080d00103a038480c15207000300340c0b074924041124801c0c0b06201c00200d44103800d0040d9809040098085441903d441d42088013620241140c401002d0080c841d03480540e035130b00175881012500000009042d4105024095503000720001d010910203142051140d1180300ca03030903a0b0084492900080e511705510000301d20700400188444102244403201c4094007402190900a0110f202d03100801d5400a403241d0035100b551262002c00c0c1000e00c030000241da180010340c0c00152407070079400d103425196400214259016a250b40c241d80c0301008000c00c6003400c01c101d8011075201e000405d01d101021042c03007140e220b203540c020704000090305181045880b48050710050320002601548a240214946600a655109507010400f800c4e092 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 687831034 1250 687829784 687829787
    0x80f060604060f033306030e0a020f2103030901060e240108040f0609080307030c0801030c06140c030d150b1e090d0b01090e10110a0f11060c19 63
    0x448003101c41c2500d031181d440610b19004e800a108603501d1000c2085614804007405603a8210500417400d064002e03404641008801030440304500d01a00e80c90703111800c202c01503070f10902044410310048800e00602480c40c80043e80004e0709080a80842c8408000d11101c1c0c08107421040544002044226503030303a50445082d420544106a101d007286090840d80c1d8651040040951083c0030f8542c2004d50030980d07030b1b001c1c01c44103005402d84000f0008410721150581c94081c0020310031280c40c0c58512035055407120207001280384a86000d110030000e035034a04203a1201600c0300c7c090803900f80d82e195804101a40003810b007101034550188030110003c034501076154140d5550440365054889004c09843c02403d040d8040e40950741e109040240240004442d481924081c108038100850f4528001e2001454081120b01890b000c60034a0600d820314118181524074032002460948055540c0700d40645540084031000d084d14042c1504100c0b40d410100300510400300308036901803218003842c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 687832284 1250 687831034 687831037
    0x50606030d050f070b06150d1406010c0c0b030601020c0a0305010504020a0e010b030109020714010218041505010203190c050a140709051504090303150f080f03040620010908030106080f0606 83
    0x110000d240c1e0240400b04c0441c04d070558241c1e00180c05041030180503504000303102e1903005900200034140d01d81400201c2c084440021540250081c20003500c01d0340c445d601c88107207000e075004042110b034010000a0300e0380c0c420854044099009070000b540d4544a003844c1d0b01800c0c040b14240c0c0070f8544c0c07041c00100b030701d1030001c207504881011205508507420411480065071060300c059840140c1d112442112480a00c000d056800c16010040009819074081c001664003500e0390b4a84003482840070022a60003208039403040564102c3c00d13900d1072074410242c525102882d0b02800c00d01c01c0310280010003032041500c80c0141101011a0300f1999a03c080c030042c0d49045a806075038210b03a0801045c10f062540110300340910a04000c100c8070184084407002c03c140f5401101c80483c40302c02008556000d01c00182c919001d20051480c080c03d00700c002e410202e52028095501c4140c43c1401d418441c207502400d42140c0c407840040e6a944c1d04d9400401400003944d51404002c090008244d0504e0b0280 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 687833534 1250 687832284 687832297
    0xf030b06090c04150203091302090901050102030a0504260a081806160f06110f0901180302181f030807060506010305150105180a0f0e09012c01090f050606030d05 71
    0x1c1c500d1503c2e08201110b0400703202001120107600c0203000412243c2e8171280100840910320a0060311820b0410400805440692150b81903400030007644000d180e00100300c405a400b00380c135900620142c040d030303000080d007441600d500358003401b001a030402c0192001409a68100d0041c40c1803081840e082007018443c43c02216005011050940700003501500310740700b860b0062000045030000812001030a40c0300702009409450002090a015a000f000314181d0310343c2d6001522426080d80d000ca1211590304810247c040704a0000403507070340c0442001c05681441e0011128080e9580c0b8041600c1c0d0003031030088804070306050010b2507951085c0328452040309510703c0c4080700c0400d01d0064405600100700e900d001100c40c110502182c42d440040380007480034007a048546460141c8035011414003510320042039040c581e880b42c0100906400c40140c20030490b6011190381103844460040180a02c01849a050401104240b060100d410740c0702d0034040c2c0a0341c080701d03008001100c0c14032645 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 687834784 1250 687833534 687833551
    0xa0902030f010501031e05100501021002030c09060708040b0f0715050702060c09030709060f060810060f120e010f0b0405060d0f0f050a0b04080415080106170603030906040f030b0609 80
    0x241c01003086601c46e0f00f10038144505045900100d40008446000741c5000311084000c100010341d0802455074100240450100c0c021130440c21030500348500451441441c458034415400481d00b503061264030011580180701e4440c0302540c0e03045071034421035039803c4030303405a81440d080c00c00b032050321296000d41445540c0355409021640d507511500d034296001b5010984e018070035030390040f031034000d180b090201070a807464040ca805c51400800034800d105c000c0c102607214021010130001c49802801d200c0070012036041000c19003c0c4291b1500080903d07220240c007075824890050544c40c040c0d401401050720a84060005a4410742884543c1580e014010403240c8444605004076000c11090199240b09a00390741c0004e03001c0d03c41ca103641906175402d40e081d401c009020000c1515040380140700511904240340780d90314009000d440c550101c61884035032a10f0380b0000b40f407513034280216038401070010301039929503850301e4101c400760301180000c03030700007108101242c07507071030f02d01d41d11885003608 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 687836034 1250 687834784 687834811
    0x18010b010908030717040512031e090915013c140405010c0206040e010e0a140c09100909020c010c0908060f1906080d2f25120804050a090203 62
    0x65542d0401c05145e03045281543c3c00c81440302040e2030750744c09400030640541500135501c0c3c5c1c010150f04a20689003c00001c9a49030030804814070351079214610340e004007884010340c102802c110040c4c030500d8481e0615200c10b414403100aa4040300018007850701200080301c01105a144c8100f540d508882a100c2d2200d450280406c101ca9807141042104640c8060030240c14242d40d5405440090f8003a0001407038810b03030604001c505120b40c8160300305600308c02194001070600240d00d42292040c18200c90003100c0800810a03864003400703800008100c0c2000441d640c20720f01600d80d000b0042c10080b0000181e0000001590143c0003a00f40d0140c81c6901013100191612040c20080300200800c161003180c495600242581040c00003030708103410fa4507203c1b40c16100005001d10402c2e4440e0842d1140a403400d10b14100d42d00245a040f601d1002c0c0004503c02c070422581001050194060300d17401b00c4440d2100104610340c409081140d100b034034107107521522004a00c060740811140c1c440c03003114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 687837284 1250 687836034 687836047
    0x1401090f0b07060e030339040501030b010201091a01180b060f0a02151005090601050304050c1017181903050703050322060518031201090e1518010b01090803 69
    0x10481e000300b0a4a00c01c1c0f4000810100f0445102d0035608200d030655a841403070340c0d00500460440000240e000fa0b840100d40d11284909045140c1d17014500400741095550901641164000d50010390215080700c03084000051a1140e90b00b80c0c1c07402d010b88800803440c114041034492a50040f14a28540140240c1c140583e00c000001c050304901d2182c0214418080380403044090842a00c2c0070321030000001804a0611092003141c0d030000e08030504005003007040002013100840c0003900400300300e07040b448502e81c100d400c42d0310106034040340344505500c0d01030003030921050220301c40000f50541900d20301c82050801d515540003801003c3d0104e0006c1284000003071150008590144000b42c2205014405c1c00c0c0c40d409002d03040c44105c40040e6618240408031400ca504c030302e143d200c90001036141803462400300d8010b4406100d88181c0c3d98459400c600c01c048140001880c502800310000103520b040390041c240c10a07c0c080f40d244035488c0441c1141654400c042050540e030026000314038000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 687838534 1250 687837284 687837299
    0x50a02150402010c14060405010624120f1d0c030c01121509060305100e010204050d0212031209150c0f040303110a050d09030302010b09041e1104020d061401090f 71
    0x40207000701e04015454454000041c0c440c0c0d4110050f0311544001d00315460300380780c120308640d07882d0030600340b00d01280d00720212001207903074100b1004032503d807035031980040d046100090301071003080699540c00c10000c110141040403296004811140c103ca01c0b82601e40b044c1515402c2031125180014403801d40b26940c0525908068841922100c1038044590b07554501d8003180d41e0b5800459aa812003098240201002d02134035050481c0f5800071440c0519040010b410032010b140c000b40160301281c19031900d05024400d4611101411040241c80d103440f54010b610f410034000f15402c04040040821324641002d001d0781d00300c444d83c4100e41d10b4581152030541e0744002100754121544980d071101e0002a5040c8140880105c1f69200c0302d48041c03d42c5006402e482c0901c0c2d18071700403060681000080760f2124003981281180d1045a0190b58181c2440c1c0b403003211413072040341c101e0700001d900c0c143e18806030b0281e070031104820580c0c0c901c840e003140116808074140c0b1501406100d119014030144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 687839784 1250 687838534 687838573
    0x20309121c09180b0105030a09020402070803100e090c0904060b1f02011b080910020702180c070b010501030902010906030b0d06090b1b0427140f060f01050a02 70
    0x2600340004403a00d0440301e440c4006452030a5600c0000907942c10000c1060101001d071040c90703824442c0d004c0c0445000c1000080417404020f155040194448035840d096407a554100c5000d140c0240300c040c1d0300d2403d00e11090142c99140b05000307000c0c6800000881d8580041410030085800400202d0b0719200c940392500980340c07600900c2d074085402c60b40b4330b032a81c000c00e0400741040456000800e100b22001c84580104419610074014004110b0070031a40c01d401080d0040381c88900030005864618500101d001d0281c00009184006450750074402041520809809039034400c441c0e9218580e00c0354011019940d401c01c0003408118004010b200740f5001e0740000c04014000f50021580090740d440302c2c0260340c06140140d9004440c0402e2150f0643d5202c03162048080c001091031410380341080102c858800c14955040b200e100311580c120850403a04241490f41070303142c1004d480d0800c280ca06140000584000d4403a0007000c80302e5079254012010f5494078030043d00035040c0f4444002119051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 687841034 1250 687839784 687839809
    0x4021908071a0d0203070f0f091214070f030f02031011032a070c03050c011107140a0f03050d0822061d0607020d09081b0d030e0a090c1707020309 64
    0x7482c10300010079440074902c0078620605065071020321380881c0440245c042281016030004100c040e000c18815041400c1c4031b9031405500c03110410109050901d40d90601240c2d07080054801002a4004188a04441d4010042d80210182c80c854039003600250100d80091245590100d03060000844030f4900b0402d0b0400300d05001c030102041006490010b601c1e83c442c000484e100c5200c03440500601004002280c3c42d21001c1c20b2400c0f10124688015680302d0042c13080e201280003482e170341da04580712840400024080103c0c000c40b03890b20707031410544504190f20712000080c200000990504480101d003590f0012006602c05007002c0d0303440e0180503143c80e581e0101c624510003140c0340300160030841113101d41a00c0c1c2c003810341c02420200042541c6034546c803504803548035071008915400c03079070a84110240d04a0b1401c1d103401c1540340581e90042282e074010340c00b031501400040e8004407500701d101c030000700c0c3d42c2d454004801e04c2903508031144e06894401c01684103010800d242c0c00c101509426 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 687842284 1250 687841034 687841079
    0x7050705070803030a14060a030203060f070c0b190b01320f0c06010f08060702060627160905040e0c0d080f21070206090c1c080c0102030402190807 65
    0x160039880354a01e80c40d6134002d03207800a000e9030314034841000e42150820190000c10403900080c2c2146141c0029617a0080589042660030138500441c404600808400d181c0c8c079805420306c140d80c642200d0701c04054440c42d003c2a95181440042c03d4203610684101c82041141c0d08801c1610810a100812107c04503020900d40c0d00208045044603030703008003500950b40010b004244030b6040c003002100382d42a076800801c0e40c0d4440402c0c0302d0415008140f05e03600110984045d0140400040f003032111a221a4102e080211000103000003d510002240d442840b25158911025681c40601046501c0d044464615421880703510b40c481c9004040000028001c2e0b07202820300c880c290308000c0c82d5000c848051034141500340002d1904801e01c8031759510a6050019203018542400c54a44459240e0202403181c0001e9540f03040c684008040364640607046118543c4409110340000c1c000e42c0207980591117020f0701701e0760031354110030140c01c44c05584800001d45030003860081500000d0690300c070401c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 687843534 1250 687842284 687842293
    0xa05060a051513050912160311070315050c2a010c020d020a11030102040315020408011a06191209030201091407031707050102040509090a021521040c030204060e0a0e010501050907050705 82
    0x8240002e07003030140c02e0394107d030b5950f034801c800c491038094100f086005107451140c2258004001141d035000c4034440a11410300701041d43d42e50040a000c0c103220700003400c50402c5d02030240207411100c03298605000104a8001c0105814003e01a0b0352014038805140050f1302000401c2d0018000e040d10311440a0301600150078547c43e035484605003059655443c80a1784c1c00700b0104040c0e6402d0158016480500c0711402e1307d0310801d40490154880c124580e240c000f01c04400c0000c41d03205944143c002e5000c00c0e0100040c500600e0b00a000e406607071410354007480302064a41070f0117001b10b130f4a4103c0354810584d4001d100c0c2c41000d0b11040e0892320301596036550900001032981c9407010f4151240c00c1c0781c800f40046480364410000f648040044982c258802803111083c04171541c0c480407209409004030084a548610f00b64103042043d82000b9089420007200042183d41804814021140c24005111003080c20704043d007212024442d481e03000c81410045000d05011300010100140580140ea = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 687844784 1250 687843534 687843553
    0xf1b02010b033c03120f011a030907030606080709060b0c07060f0507020a031406090a030e012003070605040b07020615060a030f0501180b031c1b050a05060a0515130509 74
    0xe510b1642d400c07000520a400024020060f05c840108581d07100010788200c0070107505028501121442035030280692402c0000410300700503003045031400456000300140940381c3c99001c243d44420701482003102041c107100012642c4882c402c01c0c1c540e26810301c0300610700b03a860250300300e41d4010300310026030038000200840c10158803500d01c6e04000e1070081032031603100c0c0c900c108100e2070050001d0540e070181c1c009100040010b603021f11144001d900919266030380d42000aa02d840400c90030040f1802d41c400010540c0c00c0184503080548a00d004048440d5581d072174250131b0f40c507100204d0701c1078101a500340d4a00103d14040d4041e2240e000e42c0d141c0050b20b0741c8003402090449a084e0014040c0103091020307454002c00074011b0781500c401c10390141101641540640c001e070080c0c2d5942c82e050102100c2031803d0715490800f00101150050300b2181203e03090304100e5141ca200340c440303030b02040c10080010111441c0c07074032502048002500c101c4500303200c018250000e28000d403003d05940039181e40c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 687846034 1250 687844784 687844873
    0x6090e1926041d06100e010801060e1516351605030703090f0515190e030303070903150c0215150a0806010f061b12020c040f1b02010b03 60
    0x40711a5a1120280000941000e13020400360403061088039040100b58607285000366400361941c1d04481086c104140021625000140700410142f02003820040c041904a0b0b1000700581c03c1210500401511801510445104641d007015166035004040b100c2c55690003119544010200081d000c142c03044450702a83c2c40c9402c40d84040f8040e40014801907003440b031104c018803860001c1604036441a8070f803004241d0088240114882c10311981c00007181440c071039008100351400004020b05a960703d143c41c4d50090240c0303000d0300054401541c2c3c00170380220001c02d4440e40c2600038880d0020301445804035145400c0c0c0c078004003440f5910390f00c4c40d185001c54440c0c0071100e02820311400508003542c1080706080c2c076245181e121a00304112081d41c01b0b00302405902d02d810860304420b000f4030f061b1800d032060707152201c0d0494668105103412814200342c049a401040f40d500b886c0600e90a40031858030490036a4030b0300780aa60306400103695807450020003c80e20700480c1c2000d0072284c0010f406c142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 687847284 1250 687846034 687846059
    0x803070302090a0b0a110102130603050c0f07141c0801121104060902090f06090108010b07050313090914341a030402100201150b030a0e0106090e192604 67
    0x1016002200104110704c010340c014a0050300084046d0086050249014840500c1c00f050b114a17003c0c190f4440c003080440c0e0060003111034010018a82036503d400320b2800300910204032807900001e003e0040c40d003991121809550714018825a40c10500c1e909018103c80081500c00701220724030400400789065446901a02c0020310402c0001a200c8081405010310900107607100741c810401082040e9030780e80c000400074156030203000700301c0d2202114903040f441c61080022001c40b22221002c0001c001980741c00c4030511a00c45c40d038041003080b020441c2030b910a0346c082c6022040410800c40890703551b108070080520b0200e4104144a50303602d60507102c10040c85503804c7e12101c0004200015800c0482c10644004040e01c02080741501b5113040002400041c01003403581180080414540031940e0018484032220340300070004103568850f004003c1c800540f8030500303405a00003820b140310600303402c01c14250f040071283c1c418082040e507040702031003401015255020140000300d0356111416 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 687848534 1250 687847284 687847289
    0x715090501140a0605040e0a06050c0f1305010e09090d030c0318052407080103060b062101030c06030e0a0206090312030703020c12040b0714120a1701080610030803070302090a 77
    0x484000b40b41407504240f402c2e1004c54010500850500f074044d40507001c002501300c00704e6004140094030ba00c0d0300700c8c100e030703c3d204880c164900200082036039981021a0139000c000c540090f2901e170040c0600384184880480e00321411a4030350030181c0f40481c494003940001014015528001890b00c0c0d020151f02000c0310801010380e286c2c1d0245d00e0240500c1c4030b901c00030450050400d0910030364078050500500004050100070b0955440f0304107441c1c1d544070f0b03000782c40142c0d20700c042c6100141d10b04c115001c0101024403080c1c03071418040d08000b810b80d000707115412070100703140080d2800020070b80900400d40e010039490741c0c02d0310401100d1684017030200e001e1401210580e030050f03900ca66641da0070b4a0600701641d58900c040040000f00180b02e805022514a2503120211405490b500e5121a080c140d0602c034804c00301c100050f540c0b1320b0590003d11880441c8642508a40591b2135910031540c840d02201c3c00700b201c0d407400c03600f0b002150310240519130203505460003520b0810030f4404103c43c00e02030b5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 687849784 1250 687848534 687848561
    0x40b0a0510080603061008030a0e040f0603083103030c020310020406020a140102031302131d100f09050303010b07060b03030f07060c08190b03070509090a0b011a0715090501 76
    0x1030107010f40c620342070001a401c01c410711401d10955044c1240749881e0301c03c4000300d1081c03001c0c100030201540c0b681d4000d01042c0003400c404110441c0d480c00c5c1442d541c0e00403413141c079540701c0425002c5201040703c096105100d0f903282d08403485074107664040e02c1c0a80404000d0380d1510440b080d107020082075000800160201d980500788580c41da1800300c080d090b1010140c6c14503401802001310f0100038400b8940343c10b80480b80c420080400680103c0100700d24222496580404401ca1420f83c80005441980e06142035040010401b03960f070300c04c100c66103408010243e410810040000620041c041e051482c0140000114514a0300c002842d60b880310b010718804000106045e000e00c4801c0c40343c1041c4c0303807850510800d603103080404903070b5888001c050550615514039010ba800d4a0401564015100240c0b02e1200c0e4140400c0341075550000110456401c5880000402c4078101501c5a2600300c031100780e00e90800c00940c2c0c4100100a50100c0e00d0b1040d696038000c0004100c0900403104d034041038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 687851034 1250 687849784 687849797
    0x16030c11010213170303070807080c09040f15140f040c0207120309090c1b1b0807090516050406050901030203280903030c030b0a17011d03030f24040b0a0510 69
    0x38401825601204c021410005400c20f1040142598000348056031001c00da14100c04242e8500e0134200003405005002500a071030069a004682840e84c80701c10001e8000b03424400940c1e0314500d4001452000a180341c2006034a191140755082c9500a442a1245401070741d4203e620759015029400c80940180c00107100014104001003042c410140c001741c641ca0703c150000d40e030003040d00081d05004001040400301c20140031740160304030070200141144000fa5214036960311010800f40c41d00752420706079040d268040c80600c90294040390201d4410b6118181030880d80c200542c000c2d000180705c03a030700b424881e4006d81081031030305a20f00800c4c8814070000b9080d825080003002c944020b07468009042c6003140c02d90700b030f5031001e0506040340d944085114500b01203420203405064180c0d005031491103401100e000301100840510b10411424034210f02c42c0e91107101542c2e41c0b842c8140b181300074501d00103001d10f041c02c0a8000303d020b96400b5004c031030150f0b43c0b1004500383d0440a001440001d41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 687852284 1250 687851034 687851039
    0x1f09020316030614060f1003020c07080105100f0e0403082701090507080c060f0309070b0c070e0f060604030816050f0c01170609160c0f0c0801050f16030c11010213 72
    0x20303144544e0b4140200440d400d01e06207407000200d2044425a032006124034854500c00540ca807203a01114006034039001038410042d901d00300c00b8041c00e8280c1b5048050441040003060460041114030100c0d250008600c41c10740704c64500741c40c0e20702c0280454410072090411990400b01410340e0301605a0b1040c000628000b0700d04000303007041100c0d08612003940205050003170031381c0c88100380c84158140d4081d80d80e80351038846c00c9a16003101a07000c0c10201030f01280030a80d01101068100031070f418020902d0107943c0300258190420000c03074007030358005c009200a01c04141460050030f00c0524401400c281c1c81007a48945240c03611007000b5002a0b41b0945041140b941c0c050a03100d4120a84c520a0646040601c001000d204000b4950754101420900e07141c8121301c2490440c0d04690883c2d05440c142165040c030500b4028113001c0c078041e45d820080420001e0101c0c16409100307a485d880b404980d1203240800f1030184c00d00ca2841c100f00003100d100c5015552007032005041400201c444401a1403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 687853534 1250 687852284 687852293
    0x801140c0f07050d051c050c180f0307061e0e0a060c050c090408040807090203040f0227010e0f1320010306031401020301080c01170106080415020307020717010b031f0902031603 78
    0x100e041e20b07203441c03460515082c4422112aa81a1f5584d4a420080389c071300f02002e8000306000c80c80d51246154548100d0340000b5a840e00300c0c04061411401e441a10a0790419100c152110300c100d03040c0d039421040082c2d00300441803080501280c200e00c00e1082c0c940042041c0f000036903034041541c040e41c15030800501044082010400c800081c00b40003819800d42c501a1a015052001c10074041d0103281d0207815070000e205c0410b110f80c500c14180c50380c2c0c2d0042d61100c02c101505c01d001c03075061030100554404980480440300700e204007540c4c894100f01c9481c41c0ba030800c4911106181030326040c143c45060100025502400f451001c0072071a00040c2c82e50300d000c00507441c05034410005418450105030418586610711039141c190340345400c000c03140d5140c0317103081040d002210004844451010040c0804240c0c0801d03070b8803c4070f241d80e0409150f1419545024200e8100c0202e07507900d9800402c0642114580002c00c02081c0c01100300080d440740341340c0110303040240c640d101c10319220f202c80050003041b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 687854784 1250 687853534 687853567
    0x5100602011a061602040e030315011d030a171b15011203080c03060307031403070507080f07170f010903021c03051b090f1c0209010801140c0f07050d05 67
    0x7000b8440c0000482c2507101160541c0f04000a075008030050b000c0020964907650441d5140c601c0390703001c80750f0b80c0c40e000360581804003003001d1090010f115283d500c445880c40c020000d0810fa4000c010700030350001ca9803041000996410070210141c01400580040038000f6011083c0b04141d0001c0d06859680100b02450040705801665201d01207545610110381d018070003c0d40812410f0b85d00d56a91034041c00039207801207692006082d4042c034050b4909544000c0042c0541e5071095046681140e00c910f04992500c0106001c407440b5071083d5401c00c00c4054034440c02e040399040030159a40c0310324100300176080d078034610001d038050303070041200343c070180b0080307000082c0305205240400c214100403900080401d80e00955140900020496100f1599008914010508002c01d11700201c0300418543c2c05980b01c2c40000d070f2007030349002d000050241044c0145200050195001c400c59941c00c3c1d416103181d00010b10380507801405002c0800092000c0007450416045502c0d0940c80b4400c128040000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 687856034 1250 687854784 687854801
    0x150907050a030e070b16141f0c0f02030a03150b120103050601121211031b061b1c05250e041b09060509010e0d11270403210510060201 59
    0x39480700ca010406540d5070403d6032450034240c0032004000307115081c04d01d0703540001c0103c7c2105000340c400c2a85405025038056810008141e8244903c84203002c0650b00c0104131045138000d41c208000c19807485100358090b504038549051101e0780145c448600b64542d40100c41e80e000380c120a400144140201048000c0c010408925407181c45021555032250401012015505020345160229880003050042d5070600c96050b50120300080c0b010300302a9185030507100f207980b50010110a4800140400841708140204018a406009461110401014024084200d54040d0a0045180c07440e907248d07510700a40d2551103030844005802000110346a4110740501143c422028101c030b603403c28220310490380c480c10150303150383c1d10700010b0f507854025000142d40080c0100301d80c3c0802c0801c81c64081c141400341d407040948030b1100c0c0c02186198402c8115840c9020a800280c0042c1c0300b107400b1124040c0d8124401c005403528036540d001e4800a6683c8041c02480c89414000c0170740c2446290310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 687857284 1250 687856034 687856061
    0xb0403110307170d240302090a2406080604061d0601110d0305150f01120c020102090612091908031305100203040b0405060703151a070c151107030209070305150907050a03 75
    0x3074400c21880b1702d40d8003034403000780201091070004084401c50351113090190400c071142c44810420807003d4441a10354001c40003c5291231000c0381c21030409114210694409580f00704140c0442c0d040c0014404008109030f040002040c2801c080c09401c2c0710f1a009220a501c01040c40c0c10f1440c4200898180406014000e0107040c1901c4e00b5603138440540341e0000700c44d40d0002041c0c1c41522040340640301c0c00700084c0c1c004100280c0d0b842c41c1c0c45000485881640188169640014000308c01d074600f501c90f03030000e859001e061010511114003034002042c0103104008490900d011511114244e070401c4800341c0e0b050780c1e1a010001402000e010b0310ba801115454204100c951603020301c9010030b01c5002e0801e03c0041e00006504c4985c843e0103c404150f0440943c440040d03036840d40700c43e020485500000010941072005250050001e18441607950082c40604207558001080f030040900820300e4450310900f41d440d90464039214521401032200382e59866443c040140c0c0901078818034490800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 687858534 1250 687857284 687857321
    0xb03030a0e060c2e02180108060103060f0f0305061605041502071d06040b0f0a1a16061524080613060f06020d1806050715050702010b0f010c0b0403110307170d 70
    0x610180c101d80d1106c1d003601c0909140455484040c0124020041604641031280f149030f0086045139502c10380700d048910407421101d1035034405d2010028030f0380f240194804204144818401d011282c0303120b403101202c520480b80115643d41c4590280b0300c40ca81440c4030180c0c50018010790b030034207000c3c0c010032207000c2d246540708401e9000454a844482d105501040c4c8512030030101428030780c421180d0712501586120742c0c4504a0400f04000d040c0e0030500d5030743c620084000505100c40e8510400714480310016410a00c0605406950107038004040742d83c001c8003610f02400a1807280702d01009450106900c0408904042c0080d04e09500d03c1008000d12081c40c5285440000405254080d139034989840c94a460192a00c0b00040800030b452810040c02d020800400ba0750550042c40c0a90f811121002c9034040d030707001560110f00000c0d01030f0124000300b0010b00480d00941c0f8044140702c82008684c1f40411030380ba083d150714070780c0440510030440090040c0c0f41c01568098000600c00c1c256221 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 687859784 1250 687858534 687858547
    0x406030209012705041a03030c0309031c050d150b1903061e03060b03030c240a0603120309080d15030b01080c0d0b040507120305070b0a0b03030a0e060c2e02 69
    0x40104040c6807103000c2c1710f40d8841406440050b031184084004c00005030840fa26480c5e0b40070181e440b6040000076900910030071860302205034040b65440340c80c035002d448091801c03442034013200c00b42c01184882c80c110380741401700040340301390784000b031050784091040c40484000c00180242a23480303543c45070f55403e991941c403c3c170031064803800c401101ea0044001642030000d6000c40c1c01d60007100f203084c00c140644e045400e6404d4442c4542082c00b55045a100041c0d95441d81000071100d090002a0032603181d04100d000d0349001c0c8e4080803070a80140d114a040c1105280c104044d130b401802050740b4440008820070030070103038612880c094009103001d80525560030011400c58040d400c009010940280b000c02d05119003485820003405241504140121320f605010b4410750014008444020b214400200c0d41c40480c070132030fa01d80c000140038520b001741c0200102e401e100d441100942c0204200410658807108000107000c1c81c10400c0000c090000040c00701c0807407141708202c001c1550040002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 687861034 1250 687859784 687859847
    0x90f0b180c1909180605130309050409031713080a020c03070812030403050d06150503061e031b010311030f01150201020301031a041104140a060501090e01050d17040603020901 77
    0x410b401d9074040d0b00002002d08042100e0a0014056440500034070b2415041c4588843d80c8400442558007985880700e1150303450f41440100d8080c0000580002c00a080038524580e92b480d540d60007101c008039071051518652145421940400e02040c0503030721071590306c1a541000d214410003003030110050103403054605112112840010070080070400001034040e1003100c01d85c881c80c003401071071b040300030b9044c02203070080c0ca507910175a409445820600f40e19280c1e10303a003002c0d101606801401078501017000c210184c2051b8000300c4500c3c145511405003006140a020103940b00d1301212000c0210395141003031190150103680004400c44e401040188042911085440352817008102008038954075801c0c120424003540f44040d600600700300d180f141e030a81108075540540c201c8001040847e64503001500c0b084181e1182c084c0070034030034004001c2d900c9d00141140185000700c10900c0311162820050792103501981014001c00e0f4041a0aa1103590103580300c0301c4408480c1c215816899020340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 687862284 1250 687861034 687861079
    0x9040e030c15071808150109020732010f090224040b09130903020105061c020306010905060d0b0705040810140402240a030f0c0f050d090f0b180c 64
    0x12503009100742c50b80410042d07031040c4155410041c07030321182c0020b00d449101090712042c1c40401500e00c400c05500100d031500051085a0380310381c0c444440c2d05226109a4099840c002c00c2410050300d0b28642203200b24141c080c041e000d940c15104000103000382d101c0c0304201011036218641c01c41d001200b11150340700a51241242d080e40d40448105840b408640b00180d075100340d00d0019620141001c2d0003004041e01500110700501c41121024075640c500031398003030303901001d81002e03506d075000d50010009042a54403023030b0040809403080c43c8104140d120500d011205940c01c400048000404110b4000d0501222240c2035080c00280240444010182c00064018001902c203c1c0c5054103e0342004500182c0a09000c0303c1c94140d0722021400340103030080c01c90a4020007240e08003100c0380c417468401d031003001c0c1c04403058456500341a4950070b064001d000b1413400320780c40000140f4000200e420072500e58807400100c651420030348105c013100d50502c44001e000500410600385405201141141d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 687863534 1250 687862284 687862303
    0x71d3712031d1903051609200d110a0801060e01020303163603031103030c160f0503043201020601090c12090501061a21040212060a0209040e030c 64
    0x2d008a4050381c4880010715200302207800d003035224401c0d5000010402d000c6844044090400c0580c49055030320290001505d00e5031110030b081301c0300714665080009803007000e0040035054180000b122044c034204502c160340b00901940c045144c00740104000c070380c0442c100340544030070301c01b031402d5041c100c4a9000c104221000345003481408030762040002e03c00416403405910462960020021400c958103030328110b4001034002503010700d45c2d00d24120001045901902d8040c01040c40c141e02c01949180c0c10440c001d04460000450030228041241080a8805415441c034100103800c64900c01242021780b0312284086107403040d1944210b07a801040e05070449056001c0465940000042140d2402031021f4040c01d241c07400c0b00303590500c44151720000903100002004402d080462420072568000c0301504250030105035014030398488182d1115412a1002d040303108000e00d2403c0407801e206044841c090160750210303443c0c0310b514103030007030b452130760a090b02640c80d048403503426039292051075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 687864784 1250 687863534 687863567
    0x10080a020d080909012301020a1115120702070906080f0a020105090109080f070e0f01080a0201031805030304060e060105121c090513021c0203071d371203 68
    0x72107601091010290031190f2010300108020701c10368441080d11040c1c1c504120011409032070300940350195000003004800310340c001c9243c1071444801c000b000800300310b680542c03801a50902107100d00302c411342d03c024024401c9802a000305818412800126011948001555805105022449040401d030901959020300c0c00b1960303983d00200594290419503c845507a07c900a240f2030851004030308901514840c1c035124206880b50300000201d4402806121815000070300003000560080c2e0181ea40600141c1540c2150103090701e9803402c580080340c09030b5400742c4a100c08140c200c0203102c000c3c0545000c541030444041108140b80d5213a0302030420000703244000c20a0f50030140980c4c4108001c140041c40c10a01640095a1501a400c01680300e079102e01d45400303405505a5070300070b6911030705180d501c503200940038220382c5090951401440f038000c5410b038a0000020f8844241c1c0c80307082d0340703042086810100c04030010302a80071030303001543c620020703043c3c1e40009900c03a407051000da950 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 687866034 1250 687864784 687864799
    0x50f03060108060619050702040c03050f01060810030b090606030f030a0905010509060903030418060906241e0509090108190803041a131e0b01090f0207050114060910080a02 76
    0x1c90001c61380500c05c5d48010100032020a03000c10b01554428000d01c20244281c0d800d100c1c0c03c0340c0d01815425510243c07009541ca0400c1c40052080c00d20501075a94440c110340b007440900c90341e03602c074020710320703020b950034130481e0013500c01c00540c0d050070403250030213149890003517280150700d0200400e0f44545000d00790400c400060610940c3e138483c0d058407071140c002401da07941c0715a00e0304203140541c498580898003c2c1070030000540f80b03400d840350908079119082400c50303507000c1d090208600304054105406202000860103415150403c419840c4007081e195299110608410070071400d005900148603030340802245814903000d0f0110200403a0300c008001c1e1651614074140c4291444c48003400080e0800004010401b01c4881c070300200d040c002c002d030200484100c484103040c828840c0c40600100720340740c010400024240d2200c04620301c20072005040c1000c40d40c0b082d00350f8820b040b42920480094050200901d0711003d02c5400120000103200b000d840c00c4101501c40d005400003070702c101d14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 687867284 1250 687866034 687866041
    0x206010b09130f020a1209050a020f011b120306080c100302250b0a14041713050307090219110a110103020702210d021f05090a0516060807050f03060108 67
    0x507050b111052591074500c0a100e6805040001002134101007210310000c0c0302d081c1d81c07040c2d10400c2e100e446801608600a8043c4c02c4c80c036001e01441c1521281c646040002014000480d0744074902954041c03442040280c0d842d5949810080c19600307150080303e525000240b90500307903587c1039140003402c1140c2c10301513201c12044580e280b8500303d90650040622156681c5400c01041503c01e034400c011065041010481d6586000c102c0c0350102c83c0105080b01610340c000c50301d43c050002e090f45009001c000d42c80541c03181d002c41e05109295110680c10341e004903802c0c2035042040c0111b50242007903d0045080d00981c41c4003941c03160006805016200022840c200d9640300c0d40442d40c42c41c0c0c025040d0303220700c0242c400c0704100c00d1401444103003030300030707442030103001c6101180051614080032000030000311070741c1a001c01080003401d810540e220711603000000900034000035408101410121045c180791030000b8102e14001030014042040402c43c5d002107802c0801903035001346080ca0841a10703034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 687868534 1250 687867284 687867289
    0x6020f07062109150203011d011508280e0c0108090709051005040219182318090307031107060503010608130510020d060e09060f040614070e0306070f0206010b09 71
    0xc0743ca80940a110004012006510b40ea00154103e03960090341d0306000200c03980034985d00f94280600c1c44605030302e282c886e03051031203540e0054021207007000584084110308070581c0782d0740c100403018190326103c0903c818124030500c405401c4d600c0038240404249450081151116402d001e00c850650381e9001150f0716550308042d84026080140045584400760b03203c08450b00700c011f02c1040002d0040c08405040d00742e0000c44400c884080303616000042d03d0420492800465a04158211010b040d03500b8000e24260a003034007a070524000b666540070345050041a000c0680320030717203580c0e10a14007044401c0d80a01202e044403801d01d0020926100d403051111816190034006d00207104840c00711025610550090044c03c5c00c1e14020082541e41e4441c412014200300e9250701d160f000300c00050000361420b0180382d4014451103000505c900c1d00700300340c040300e0403d8070148002441c0110901c1641002c1254540000e1142400294040071450007503881005000c0e8565000022861258071b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 687869784 1250 687868534 687868541
    0x5010603050607051b0c09060f1302071a0c0c0d08130f030801060e01081006050f070c1211060910030b03070e16030632150a030606020f070621 63
    0x10350303110302a0703103080c2000000285180c000c5845000300001007884449515000034102203c01d80241c0310200c80c2d80c49104011200d201818500d802c40b10440000490301618401052554401d08040d0201c4420f003190302c41c40000180184188401007101481e0742e0000215021400e130300707251a403d43c3e9203405543d5940c85034510014407241400542a00f00740d000005141601d2003a607840d03400d14104401168000702c03c0e5007050554072040c9040c000d443c07060006041462500c03509500d007000b65520804030030354a07071008040031079600d0050204698402042d02000e000c031201030900380c452000031900e980c0c0c40404028140e807151850100d8400348a914014107171011005024a4002e41145c45d8000f41c1c0c40000000c2d15088000c10703145a403c1010b4503010001d0f030340b90208210020882c1c4003106294000f030740074802540d000b110760a80c80c014454044156008123603140340c08000781c5051020300c100f415981100000380507603a48a41400384003030400040200d218591104030005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 687871034 1250 687869784 687869789
    0x5011508090a080304150504212322060507110402040303050d1e02220e040302030406120603202407020103020f121e0105030109030e0d02011107080109030305060409020603070c050106 81
    0x3c20b003810100702c280403160603000c44c102c9070316402c0c41c80e000279800d0441d465407040148069510403c03000a0780350f441c0101601e4680c1154503000740381481d000700c400f000c403251b03481a400500001450400c10030303039642a440c3d943c010f513010f5040030f045550140c000d0064100722118169a90001b45c043d0240303014580700b00b44101011503450404070080d80d070003155541082201c1108203400149885000d0110b80b1460301a8040c40c1824180601200c0d5818070043e24401c0546031040800131403c601c6aa0b081071400b0342101c8100744800c82030040c80030039100c00d03080784650890303a500103119160803036040903424600140e899012030303440242e90140030546441240ea00c41042004540c000b01030a25442c0a441c1140580c0c4c0c0f0420075080e12442e41000b00000c918100b86900c60a01640700c2040741e00c1410002c40d40b152282c240391601140d0381c481d0226039103540e011414540c0611036141c004000340c0c1c007800502081d03000b01d0b100748000f602400805c0314049203071003840800e5008101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 687872284 1250 687871034 687871073
    0x90d0602090325030203060f07050a0c060621050d08090c3a0212030903030703110a0204050a051017030315011101060323010b01080424020d05011508090a080304 71
    0x74903d40c00e2044000d0991180000c90003031207075001058142c01c03001040e51060949030b0741d0900c1c0413403401e411100c622034003408403101c5461b40c2022410400d06005130301050422545a0141d82c094107110345040401d2840d0400e03c10040144603403200d0204200c41040810344100c4c1d0184000101c4e01c4217690b6480040401d9a0070039200c080c201060111041501d0003107603442d56909801085507140d01c254230146506038810056007002901031002510100f41c01c80554140c0c2902b9004181030f20000c031020040150382c2c0c41040007401c10300c0309103406050050060301c01b005600300c0441c0c0d81d10000e4019080c401c60200300e1a11a0b11840180080c061088001d03c03100b99030b46412205003900181c106110820707101507240402d4140b041c0480000143d55104140c0c44588407404450b0002500d400c007001201810f200d007011030b000520020100c5440045e00d0f61510f0440140200d0102c2400104101242400070240e00001c0303008419810066165a13030f00c0d140351049407142c45606030b10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 687873534 1250 687872284 687872323
    0x9270c03060a0905010606050a050301050d08090d03090618080601091107020a0f08010c0e0607150213060c0203190b0a050606040f03120e03061611030d0504050601080f03090d06020903 81
    0x1040c006240c0000f44068031a0707000340f00d60b903100c48007541c0310300900300401c00181e4148010080c03442c25901c4c48071070358098040645480200f401044c481805000d054022a07010602080706590100341c20100150100354900c101e03080610086e1200c00608c100c0901c50b407500c080000144000c0121050a6402000070b4000b5a0703408950f010806203200c0d0000651a0401c40d9080d030b40100011421498001c004520b0102e090790b030b950980c5a44a100c0c0700c000c0c0d09010344401c054403496018003520039074540c0812071010b841011301d003504480e220301030616180c3e18000026a61090b46030070401400011850799900c0d404036140d4051680010001048810700006002d81038040c2d01009d070441d40c80218442402c0280b696139034096800d404280c1a100065000074841c404ca40d038802402c10649140100c2040c5010541c1c074213076010740d0182c00120040285a070100402078105103030b00d000e1802e00c0043d800190308800030540107070580360009019a041c0e5001d0100300c005909400444 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 687874784 1250 687873534 687873541
    0x1508060907030c12030e010309170c0f0106080c060306100e060a03380f0402161212060503120d090605010803131d15030709050c070b010509270c0306 66
    0x200d039a10440d11041c1d51400c1c080f10081106802c40b034040c40030300e4050320340f01d418022210046004100748001610800711082c0035102c0320968400414404241c0b82c0100580c2c0c580103072240c02c4404680c0714038441c0d4807d00640741e560312810143c1c0c0c0c0c0414100e400c2c0360f0740d500300f10042d01c094611203107190b8401070008500d180f580d055031003844420003142650700d420340000c40450403402e0840300311042c0d030034281c4210841e00d00605000740310030303000c3c00141c1001300e90640b100070888181c000b142c034200352041d10340c19240d0203d10f401400004100a020311494180440d8851403040d165200e01880061010701912291700440043d56001504003d15a592070881d501c86c1c01005185a0080f642d072000240320b046040c4408004540b4441d000c0c3d5038070741000304200900e404000c2c6805000e0150001854515032054502c51102e4480e120755411292510b00380c43d58050704482d02c00d010400500c081030061300c1c45140c012108569050001d860811203070b16000b001d000036581403080d02c00b007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 687876034 1250 687874784 687874801
    0x110c0a12020612070f09060503061e010e061605160e010b0304060b031608060115050313020a0305060f0708060d080d0b040b1002030903120901020a08090114030a1b0906050d150806 79
    0x441605c0c84850b40c0c0e82168039168401256a40b0003503500b0f03903000e040780f02814482c2040070300a805079481410b041101900c0700005c2842ca400510303034400321315003826040e42800b005000120000c0c0f20906011904e50a0100d5104054818003a15040e002c1c08800113040041030b520084003007200030101c03000c1c3c4240d144d00407411071003405865164020000001041c0c025510080c00408041e19150304699420784184611804010141c3c2e02000340040000411000d101d1240245101000359001d0b1601c50006090440e0181580e4016083c400701c80c030200304c800c01910fa40307880c00c000c003144181288001902a008442085a000011147c141e07081c58000000b800000025400da6000c5c04e00b104000c0058040c90000300e000d40c205000e48400070b006040100b003480d80504000f02001c4480c2000619a0412103000c040c669807600740440d07081c1d504204074a04000c600e00401d0385400d244000300240501d400311418191130300045c084030f15103188130902038550441210804e01c1e00142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 687877284 1250 687876034 687876047
    0x8120613021207030c0e0a03020d170408070915050612070e131d0c1005160804090e1621080f070b1602120430060606110c0a1202061207 60
    0x49910200b07140403042408240512003660700b1b40700090200c045149075409000300f80d55800f00403152401c610303000c190001d810f0400b40c0007400d8440014403060f13003041c0c004011120340e408520240e1011002c01c00a665604048600414201307040003210b40320484255017000c4152081680f025850701c84001803107590307101d44030803480180b9042c81031b180c1103501034407001c9004c816038202040142c40803c1a0140d0010300c40b05125100d00a02140c06031076800041c0c000da00b10f4400780ba100c480e5054000e2003001a18030780a4082809521503150900c03016442049004101c2020003500400050002c0d110694179000c4106908642d115401d01d842003000300e0841c0c10f07021040c040305400f03421610000360803607042c1001c01864509800c0c41d180030b00040c00035080c2c83c1c00804900e000a0700284410038014590b20500c804108a0f007041c50103008e00c891004080b94980c4010611007003692b540c803924007110550449905210068000b24001d44201c00031400410707140010b000d01070742c0c0100c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 687878534 1250 687877284 687877291
    0x715022d071235061804020315041401060f030b070305090c01110c0402030f0106110f030f250b040611090a051302040e010b130b0903060a0525090807080307081206130212 75
    0x4403901084170401007107428442c003c4d24040d42680c0714402e11216035252001403508280aa2203170701008816014650a540c6036800000c16104480010410000d2030781d800c907000009030a0034051854503050b07a03643c40240914060420800f603140005811052040b2007484c0c0019000350b41d00c1c9001111003800395002c0c07080600040d0fa54a80018001002c14114000340d00d02003c0d5150071a00803582009030011420008a01d02c0300f80b103000700c6403400da1a16401849010003003010f10745400c003181151000300480c1100f85c1d08210081c0300d96100040e15080d160101c031900f0b0160700d0081d81600a00031030304902540f880080002c261a5012009000c44c101400d911840f80c41d16602d201009000d00000c440c0c05034444004204400d0392a001140d0003100c0c0010700c03c44102d403502e01d2510702568885000402c260340d0302441003941c01c0c80001c0250032150003c503d8003415903503045c25031107900a1060700000200c04038802c1e990b40711090408454800d0150b40f12501042c26010440d0143d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 687879784 1250 687878534 687878539
    0x180a120c0f050312040311130e010507031118090406022a1002090d11030a02032d0a0b0403050a170705120f040201080c0715022d07123506 61
    0x7000001054600040c40c40e640d210070540e210b041624655030f40d138070103802400f40e580c081401d82d8040c030305419612601442d201c1e000c0c0046180d0901d100b000c0d0498000c00d40c0b94207840030400c0401c24000c0346011080b240c11080e904000e0030b94940c10b04900034010300caa201c4500040700c80150300001300803400d1005c405020f003554101c2c0720200d4181c0491182c2441c0d950000c03281e0101c400420384901411000820240640e40100701c2680000c0c01c14002c40701e1003e40c8001040380201020590000c00f0520f0701e00070090400303a0a9031101485e52500900c004c0c1008400507140b200c0c00e1162a91424142d5191581d200900304024041e04a811454403500c1c10503c400004d011340300700c0e420140c0126010703110916662200e020015130b60348026002d91f0540414075141e00b0032440ca00c001c0c200a0000001d03d00c0c400150580d0351007502c942d1101c8207083c141888040049020394900600729801c60a02e0070a0076040e0300031b500c04000d02c100380b441c442c0f0f1800b01c8100d001d04a41d5820b102e80c104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 687881034 1250 687879784 687879809
    0x61e0304030f2c010c0201121113050f090a0e030d0509150919020f010918050103020a050d1205030703112706040b04090b04060e1e0105010c08180a120c 67
    0x241907041c0c1c081161440f507a10320760b20341211a80d19501800858480d580107150109940c0500260b00040d100eaa00e54480c403050000b5500c01d4113114000d1110140c441104c55503001440c0000141104002070540341d200b03a035032142c00301900e0b0208220389000502c244140710078900903407050344459441044025550750140080e5001034003242901e0090b1400d01c00d9060180e80750280034069121160044c1441101f480204420072001d002d8507044c140c0c51004100c6606520603c0140d00d01070b40f15902441025a04e40c0000d1490302d514040d41d200d600c0d2980d100d549220045001c0c0c0040c0f1200c803105c40c000a80290031348001000b4076151200300c1c5411150440d0303807051003903d1160344500ca4602c50284030500c403540241c2c0041d5205a801000031440c25150405281d886900f80d400c00180d001d5540340944100300c44e10a240100401d080500314420642c5410106100d90803445040300d407e402c81000325941c40344240040c0084404401181d006480c0040d00e2100c0d0b4028048170300003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 687882284 1250 687881034 687881057
    0x1302073005040617060111070f03020307080a03050d020f1b0a02040b0a0f0302060304060e0106080f1c140d0905100f1103061f0c060906050a1514061e0304030f 70
    0x10341c11034040311070036602c00c0301a21090401030000c00d405002c141c100500d095801804400c1005003001402d041c48919808600d03610405103004150780c04031040b030708503010b0703440404c1d040701c150780c0318440e80d28015075281d2484500c60714a210300d85c1c452190741001c14000140d0f000c000348404010f4425070302000303012954410441c0c070030760901c9a2902d48020640510042c01c00401841e0068031a180204071450b04c0d45070a0f0a54409802c440d148ac3d10100c441041814100b100252803100c034103065200c1c10303c040b401420888101c0d10740201c40741c00155001485055440602511780003002e030392070386043c405003a000c0e0040840c0c0c040c0c503906040281208109440031680070740350040c00c41aa003001c1d0210003019002801400c010708c5103206601000c02c1036405042c000358800c2c000040c00349840c100c4c41003194000c9986031080c20701d2034800d1010440d03900c13051540b80320458003c0c0d20391000b14000b1308903c603054910b00c1408000f0051008140d0400c403842c51030955601c80200c603d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 687883534 1250 687882284 687882287
    0x150e090f2208030703090f0c15080a1109040c110a11040c0801141221040e0903160303150f08010504050105160e0d1406070909050a0207080913020730 66
    0x8840c0e4010b4a4441c1c108003040205000758400e100d00e038400c0062082d2040640c452802881c280e60180b40d04090803503150f08007551103540580d01c00d800c144100315010708e0888801c1c150160b906054040c80e940c02c0c1d44052140180d20300c045121004045a41c5400f031850200d041c00103051115010302d05101d07981c82c80c82c0c0035685481c1a145c00800b00c03004407032580d00b0000e80310000700302c5c04c403240145800014812020300d1101403c4042000b401d5803030f483c184200103503540052a1410350f4009000300c0340750500b150907907440349402d8540420301001407400c07102c080c0c2696002034861403541e80006950b82041d046541720b28010002005183e440032032066140300445143c20015000e46040f0300c691501c03800700c400080c05000003440c00100240800c3c60000190360110110f0000301040090408501449500141c10381c000d42c00c10142d6a00e00815000b01c03000d0380d1040d01c0f09056051000035a07030680c1c0100350045901c0400116580e015050700b5030391800b0000183e40340700c0308680035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 687884784 1250 687883534 687883591
    0x7020f0115060e090a0b15070c09050108030306240c0c120601060c08162f060405030307060e030c011d0d170a09020118060e010216060504150e090f 65
    0xb00d14540358600031001107020003a50940003010700d00041c0e91401ca803402900c030070b00a0b918001c403030606c041d5030343c00600307202e1030181d8181d00401c00107080200601c40340b54007100f0b40390440400d44084014205a00b00d16130180f40c01c20001da044070007ca03403000305880004200b072440000355136100072002640718903901d512090003210301080e0401c150b040002d095800812120102c0340100e08501010340d80c003881402010041c1440071000d020001540104184840c0c155504a947c03914092034100480d0701c900480c50090a515610b4030308180c0041c09000311800c00c2d0210008000d019045e80c41441c554542004041c41031041d111180040b034058984000581d50100110070f607a0b80e0002d086c8080d0038079003c200d040006043d0302d448440c100da1006030103000039450740c850340c40702000024038000f400100b00d0781d001034042c410070850f5040b4080358151166010150140030b1a108141d41008035000b50030380046241b01000140008148403d00460040e460366088180c001c4000010f0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 687886034 1250 687884784 687884789
    0x3031b0503061e04050a09060c021c030f1506020d120903050904110904060320010e100f110a0804210201171f1206050924190507020f0115 61
    0xc900d040012030140d1504100e50303034100c44440c19034014080400702080c255001980c0050215454005201c1000402c0c010405041807a200400603c0f9880e02e2120ba180344071510101415a90340c80d004864940d90405c10301c104c08510f9003c0003507900d00001395035000e0070b100840081c1e544c1e0a04410994640681104103070907994882c1400c1c0040200401002041e500302c10301d90080003c0d0a4544450088038010b50069801402503000305094010031400308005d035040003403800341041c03181c0d201c02d00f1910134101480d202100d48559030003958524a400d008840c681f00d0203404004024401008000740c070946140380d10b06289500c03103465a60300c1120001d0114014140070106403040d03a02881d440401400c42141030340c01111048807600c0075400048441d42d041010f03406122107801040c0c0c2013030640004001d81c6800d400310b103244100908540c09441c2c0b05c1e0740415405601c8921050780c41c4c03074550f03081106050030741c406942c4000c4183c4e05100c40d404c0c216201c0c0000f0f02910031608 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 687887284 1250 687886034 687886037
    0x17010501050306090307230a11090a0b01080a1808031005010905060910081f030503030105150c060c1c2f1c09021507080406090e1303030b0a030203060c0703031b 71
    0x8025960f901c410f24210462510714043c7c11000e1945a408001c02c03000c041e00380150104000340d502041406211a00102981001428a4500c031803a90b4801880c507486142808001400da0700e00d803088214940c0a04040e01503280031080c05030b10112808000d00300da5090b01c035800102d03516028455a4054180c02d907901409956180c590780e4001c0300d5855000a122035100c500b140788020a049408003a04183c1e1507500200041c049400d180d0740040070300c4800010300c0e0400507000440c40e0b4580000b840c022200c4004645642140703624450031820302c0344038505000001d9500b07061140e800d010078010242100300950901800c11580c101e030030ba030403195510038004271103c0548019100c03103403089800000c900b0941d0700f0000e001c0050080144211501c95640d841c02c0d40003060741c00c60b034101590000c20801404040303601c2103034010540f40e06042c08103008240d08000b80c1d00e01c070300b5480070390980a11340c01c00c54001d288038001d00e48103109440410107803551815110742c1c144e0303952500c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 687888534 1250 687887284 687887287
    0x60612030815040c211103090a050c060403080a1d06030f0f1602100902010e040f050f0108030a1e05120c0a1206081b0a0306110403060b010809100b19170105010503060903 75
    0xb00365884070800e82400303111403d40807484221b049001c20180d84200c03101e00750303a04400d0524042000034401078a0803c0e040b540d8505203401c50301c0c0e18442e8800c10928109000d11608440e8484c0c42000c00712680d080003c00090b00d80c41d1940d036034810368404481c0c48401141c108000f0b00582c108c1d9030080070188190f4018040d0f40098244100100b81086050f030600c8a01d04007a441d030b90ba14050f1404100a04e0f4021410f4100030758031801c0054107030044490741d00280f041701d46d281d500640030805196170301000b400c50088000107940c240b20314508040000702d2002040740c3e800c8000003e0a98400540e07504524604c02c4181078103d88060040c1511500152495900781e40741307540140c20004003c00c1c80d810305690342c5d640400ca88401c1e41c01102c00300089420020310900d0700c10392841003c20f0801c4d648030700d0601c00305a00ca42001301280e01e5159115242512521a070b115101d80342c020341e114202480d2102c12030300900c2c1c3c8004c08130483c0d60034040040349504001c50a1030282841d9001107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 687889784 1250 687888534 687888557
    0xa090302040c0905150a0806010c150b06040902070f03080c0702090103020906031504050d08180606010f14040e04061505031c0c021f03061719060612030815040c 71
    0x44007a14000301070380100403c0940c0400c0030396410f000006a00d802c002640d0313980411483c068004800104074505010000710741001040141004096003105480005002d407107540000303600c0e024030b40005044030303c080703210410402c020302087c0100307001342c841600c42d588001e440000d6206217003009400480000041006003403011641e600420b00605a490a468030800c07614216811a002e6540303a004070190100760f504003620039000300540d9600206480d101d10f250b81e403264054a4241040b5107050b00c0c180300c0c0d12801c256903001d28464099a90f803961442000b04645094806440d450729201c8200c041d404800e0401c011100042d0140003100025240c5588030060380e2b11800c01d110b0009916001a900c051180b00d030704090b22070001c01f030921008014100c41040c1c01084d03881000500c0400209000210b00040000b0501009400d80462805a02811455000001c80502042c0384001c140c0c1103d280c510411341407130b004480304d4500d010082a04c0031100d0351004200620703680c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 687891034 1250 687889784 687889789
    0x9210602090d081912050c12100305031c110910140d020a03050403020624191707030219050a06051b0f01050907050f060405013209150a090302 63
    0x502101c030401480386a62010b03940703c84036503a11a0080000d00403c10000884054003e02c1019814a20403820001c2d4648103443c11454810800290068003001000402c0365401c8881d4030090b59000301520b445206001180407035610541c82d000d511420580390080b0711080c0404c0e034070015001004c1e580da015001a064514200c02e03091485d0065007088141e070320000300e0008081c1a01035a40c000341c00c0c50030342402400e01e607002c3c02802c404010712541c60340524807110200c090040484600120444010f141203c05009a10084c403448a003400916400c10104e040310499000307540e5100c44440c2c00c554000d001c0214000c0303d5000c0443e000034020b070342c4508058042c1c405485030a03001c181030910f06501c0e01040c0d0f104070700c1d5a03445070b0400c40c0010050105000600b01590a80208460000001c4d854012409002e0402c0b81c19240d04541c4901d0a4800c0440d04a5401c2d1010943e54000d0940e01d980c80841c0050007550340307500d0303d58019500d40448000540e15681c04034164119400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 687892284 1250 687891034 687891037
    0x81b03070e060a0906241b0213020d06030f14060714070c031a04060b040608060c0a0c0f0507050a060518040e071e090605060901122c0d09210602 64
    0x2e26401c030400000c046031140041c030900d4040c1a0080140580f400c41220107801004460301003030802011880401c60040010002a0229411603005022100d0128800000e00841c820600c4540c207000d000001d20901e200402001801903a0803a0f812a5415150b5501c24094682900281001d007401460710214400382c24640e11a52808103020368984802c1a0055404010303004603d000c014401000128441c02291403026a424420030389440c21454644000270014000c550340080e102c102148039a4a4109065200e1b0205a0140083c02c0041c0e4071142c0c1c1c000d86015001e000004140540503c00762004204102810040c0c03004030403d0202a0800700e03000103640c4240d80020520a41c0c40344010324040c0382011420078185081404402d85585512a40c0900d200304203101080e40d12070841d038544241400081411106404400c8459045400d40c9072001c034000e0300d011fa00c03071010401383c410080c19035480e100240c40c0c20101c0e04854801c0407090200360000340c8000014510b80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 687893534 1250 687892284 687892291
    0x14060411040311031207061b1e0309150507050a1701050f120a170a0210150506130b2b050106050a030f060f12020306011d040206030c190801081b03070e 67
    0xd003581c4001740540c10350900380e0840e5408880c02602d61345850203244030600140843e20345854004c03408000c030400c2d140300700b100c407010500f050b407122000000c0c016000d00c400c00207048601c00300000c2ca0200b40040c0a608456800c80010b5031007107a409096440c500c0c05416a00024004c2c81048a88410002414070290f152042c0b03004501e40b03940443c09001c00c445140c8840c030092a500c80e040d40000303052a068200c8110300c0c52820400f80f100205100410041da07009903280744d6102c0c107543c800c0000c061030394003010107103100003000680082c0151001000c64040d480121600708070154400a482003401002d00140050102000d05482504080780d6a01003107030000380e41e034032004043c030f603000c99800080e2080c200c0001d010850900b00203039801844c41c1e030141c5101c1c0c610f00c08688071104003c0d00282c0300b07000120124840401001c1100e00042808192480710b41c10804007a04a040920030600796001d080035182c00d12151102045a030100103000e0200340d42001d0304202030b0f80c8050f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 687894784 1250 687893534 687893539
    0x6030e07090b0315090606190b0315031e0304030b010e0f070810030c1508240f0a090f060807090605030c04020705010e0601080307170a1704020303090a030614060411040311 76
    0x40c0c0b1102890304c0c0c01c2d042c80b0301800d03c03500601900d10f0000b0030f01c03048071114140154100c0e4a000e0401a041806013501d030000c08039028003525804050001e4a0810846110006414412889818140f00200510840744070300c114180341d0781e07200141460316004032024072000401800280f40c042c41b03403e03211340c0140f154523140600c545a03100c40390041042c1e00000364041c07440a007544030302d4100e0311442c0e04c41e80600840c000140140130503040201c90030720150080782c1c1340b00742c0421561803c900c0000f40580c0e5600b0464600750942c0c9101404042c4036104850246010100340c1c1c83c503c1c01044259079014005202268104040c040298003140050754503550314000f032980310f141840618020700c1c902000755200c07180344c10b200c420900f031401d452100d58020808981440c0d0000003450500ba0b1100482a4991380d0340080380c2188034a108a59000031100c2001c0204007065021071480018100e018445684d68402e0204650001c0441c007591501880108001401c0842d00001c14001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 687896034 1250 687894784 687894793
    0x3050a1b09020f030a18170307170c18120c090414060c03090c090609191b092405090d050f0109110906030c0114130f0b0a080106030e07090b03 63
    0x240c184a81c101d8000b4586490384450000c14440071703804601078441440b01c03858180164841541d56010b080d0152851110b400c1d00c00701c00903000318040c42c0340750148044020032041d1490812002519076102d445061042c4283c0f4441c8860341c04c052941e0300b9416181c01c002d111030050074040041c006001042140c10b990060354000000d1401d0000500030600600c003903403a4100b07001700904125401482502401e0703840200325417603580705d6050780c010656211615020450907540406408007140124041c038250b075880f2405a807122600045400e101066095400c0030b8403a0480549929014400514280601e0800340350800011503d0743c03040c0308076040c00101c41e2800703083d101f81120580d0101d51ba407040301d0a5050950300242d00410480c0580007403010781d40081c120150000810140c1c0e980860071105604107a680c101c0503100c0241d0282429a5802404026034040d112940c0010f460000001f2510f000307002c1c55607001c104030301500641d81040400d00c01020318120a5034140324 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 687897284 1250 687896034 687896039
    0xf061b07020307030503120a05040314031302030f0f0708060c0d0b121605040f18030815131505010c080a050a0504030609060e07061107091503020303030f0603010f0603050a1b 77
    0x10104240070013903110340d0255031984406108040d0180000701040c4986040500f0000040c0c0d001400901034003030315034140c0e241e0300c402c0c06080311210404002501441031a4003014404400182160f1600450048521060300d580d440c1e91200026109005903070014843c0018a07070b13180e000501e0990300a0000c0c0201c010707580025203410348102642e0172061400c04203010754181401506000211503a01b4412031451400c024808a030004014081121074000300344100c8030050342210542d40180007510180700c114000006205800c00c0300c0c1030786017a000c00a029406030100c04540764006080908041801000755959405480900d01708001000044000780241c4250425180642c9000802c8400400301c81d01d0b121183e080102440110b004410359000005000001da880b00302001c40d0710460418590035490f1541c20082d4923020210030016407241078005640714410803802405071101c0204100e003284d0f5580000392468100c60400004920005080000b405448406c418030341c6d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 687898534 1250 687897284 687897289
    0xc0c060117120f04240516060608010c080f180d0311090d0809040f02250203070510110105010b0307050a080601121109011202090a170f16060206090f061b0702 70
    0x2400043d160710140004603080c45041c844030340110b40c545141d0b81c500e10300038181001a045d401902e0581a141c441d0300d9000080040c1e58110314001c1203e03600074032080081c0c0b4030140c20640c040304c10441603140000001c10810001c0d00029104d484e50016100c3c5031400d0604070049c00a96074100d171220410080e0050a032a01c0f8440000c4030b000c0d4080c15100d801039400c00054540404640710024014440f07008444082101400070b0b020704006070006445a00c0440d0400d0f010f41d00995110802c80410843e031a0820307203c1c002c4540902c004c11160380c0792300800f2120302003039400000240c001d04c1200c0000703008640c0390b90000030506022100d00c081c205d9000079030342031600c40031015030080790f410325650700b00000843d84404104103500b04a01c5801182c0700300c000b4418080c40200c940d414400011091118240da4100380d800d5800f4074029080346007030a0303d00e10840303006200d460b00242400c030011840b072110701c01410141c22141c4031410026041007a11064010010003001074a0059 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 687899784 1250 687898534 687898537
    0x13020306040f050d08010f090b0d0506041110050301062f0a150b030604110d080d020c0105100b181005040801060e011e0b030c030c0d02071a0c0c06011712 68
    0x2140310340d0381e44a154a49240044c00c00300f8440041d024082c0c00001444010303c0d174103000e816a8520100040c0000600c00003d02500c1e030003070080c0040c040c98042c0024015100c6134072081501c01e50f01240c0b80c2d6042482110b0601c000d10940340000d508806c244481c0c107202001801030038650750750440d031012548006050004040302155200b5400f0380c1e5201400309801004e101c00b5080300541810b1420380c0340e151f640d110484c03e0034441e105000c03101c000c0201c0c040c1500d0034942403480840d100c2e405a0207440c02000262840980c0120280d03000030a050000704a45841a01e844011420704210742840303280c1c81901c0c1c2446c2070003070a00021422050134851100180111900811154504004080700000405001e0241c0e1344011090005058040440f504140e6809440381d0382c3ea24040e0818881c02110800d14003603000013000300030700c004202000018180b0184458913078039003041402c1341e03100d08050103071039400550041044141450360100e80d1581c030f50907509800e12480004031607 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 687901034 1250 687899784 687899791
    0x42f03060a0c090518060907051b01090309050a05011704062013080a030203030c0c1e0309040b011806050d0212100e0606180609130221060a0302090f13020306 70
    0x3041d964014a10b0302c1c5612500c040010070b8151031203030b41164010041c82d41032000600c02c6000e4940c0c5004150100c1c410412942c2d1071080307441d4012039016007081180641480201600054038680f408240351401007103803000c50700140c480d1032042c00800310030b0f102100010816034500740c1d510742c4441401803440203800c45100e50040241e07100b5480840d80c1444c051a007215401d50f10915103d00003030740001c205e980000c80881580d03207a0324131000103490016443c0300304105503a0b80a0410325440e0001c0a4158040c00700c40c00c3c8140001c05004489a1404001ca002c502e000310740708102d4107004000412050700300823409440d06082c42040c9050b801c0543c2c3c03c01440c048140100b00396410140000d4000300b00301c030b489143c048003100c004150b0302d0092500748a4240081c0444042d61101c07180300c20064130040540d21420210b601e10003240c00c214032045172840b00000100c451030320894002c192a801080c604458a401c40c50002c0c02800400e011402024590320b9405a42c042205911 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 687902284 1250 687901034 687901051
    0x3190f05010f0f140114070c0f1503241703090d0803091506100f110106030602090114091806220f270210030f0f0b011403042f0306 58
    0xba054030f41801c0344078200d0070740e210810005500456158076a0f001055156070000766401980714802c50074151070800c2d283d840001241c01e0110300140c103040d480000040b80c3d200380c404114905c8400c20b140140508510741e07502c4425500d81c14040d0a80c803260010080d02c80c4000c813400c040d07055000c100c1000d02d031501074070b11a038040104107628a081010b8111038100b220241421300740130340803500300502c611011044c0221b407008a03d1840c0318484d10080c4220b200000d10020381c1e03d0030544d0003540701e120103d002075030241481240000320000c4030b05115028092221282140142901e80d850243c505d80d807061074008502405d801c04003410500700c5041c1c0001620222401c050750480380b00d01038100030345400c4545028040b8045000021302d0360150f442a00400c1002c10440c0241400804550b5051074544040c04200207680300001c0c1d0756003030301c80412004140c203515240d4002102c0091840f9000c8202080d404401055200b100c0540c0c1c516500b40f00017103000a0801104030345200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 687903534 1250 687902284 687902309
    0xa050c030712030507060902010c05030a0809120405090f060103091506050301060909020904022b21080c0d09080f0703030b01030b04020306032a1005030a05011a03190f0501 76
    0x16103032a0a10544005101c0694400203140243e94003038860702402202400d07565441d0340c10025640101080404250b01506aa0790b41000e4040a0036504090b02c000320144160840d92446c60f001000b21001d4610041084500380e84074aa0b0f0030704640018003160405807528076510005680d0000740001b0507202c1408103001d41048103150844946900c1906e00c1c50401c205080940c681e40d5100f90010340546070020724210041c0d0b1404551100d48a5096000c000c1d4400e030248204502642c8054800010304104803171040c208a42e030420a849074109184104503044154040b44d10505281b445003105c1da00f80092049213401c150003d2000741d0200380c031102d62000640e4540301da1100b144040310704500b541004804a5038070106281890040840707036100c0e281548150a611180041c010010410031101a400400030740003075584007515814400040b5062045011105542c1d032800d21841c2169200300360071910a502d940002e500e10f90381c036848200303200c1c0c5005480c060102042000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 687904784 1250 687903534 687903553
    0x4060c050c0103050103030e040203070e060c030406020613051903021009031106100b0405100e0d0507050907112d06070201060602161412100c03090309090b09041506080a05 76
    0xd5080a042052060400d440c00c40148002608002c02030420f000c107940058403a501c41405841000300c5025040d40b001c00800d501142080010040c410b039842682500d6031a1a0700c0511103041d8031094000f4900d0b04000c0d42c96038052011101d2103c2c0a00902c1218500c0380600c505178201d86d1114000d0740004e00300703206218032a1040000d00e40007084009602c80040c50060030748824062405120b2080504100c001e003450302c14109001c10440042036000c81c81100e00d00180e0b65201e40c487d2074041c1c40c003a000205502e00601400f602c1c001c009001c3c001e601106042c2c1080b2544480d0042030400f183c2c0302801c2c03410010040a449941d0940000038001e05110b0060301c9c00100e0640c03180020030b00b40e4148000c9810100341d107501706054406a4200e600841c2c0981400040340190f40c0c12407401c4821104240d04d40c0114040d075000703407a032031051903d6500324415504803020760f6402c070030000d01180c0000c2211b100300c0689102002c00080064950311281d0038003100b13031b5098a03139500c101c124 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 687906034 1250 687904784 687904793
    0x9050c030105101112030702161509050604030b04080d0221072c09040f1205040303090e0c030403212d0b10030e010b060d09050f1b0409140304060c 65
    0x2c44075092400e04000481c0c040d0b150086541e4072080e021306140080101c003044445008000b02549c03080c00040560005484000180c4075603141a034400010305014000203031410039104840960350000300c040043e0350740e07440d24205a48078801d070810303056007040400c90709048428108425410b038103a011203414001070080941d00c58415446203c0d070008207113590512801081608103c066500010540e02d505100d912a1581c0c0d1004e00300554107202408030700d900c140100183c03840794441d402c4850b2584894100807100715514280100100003280101c0c0c0141000124200c4e03120f0044e41c903114600c4104281d6450079030303251901c4081c90000c001090791544403083c2c3d0503030506c01c2003038a1110002401d00700c0d0540d0380c0414956507400e94400c000d000c0d0003a80c480039019010694990341000100f009280442c1c0690b01c50081c0c0d1210500c1c0036000c183340a1001040c08000c07940c0310803004000081003401400ca90810048141e540c45070000d1014000425981d02e5959840e209400c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 687907284 1250 687906034 687906049
    0x6121b040e04060b1207140a091506020d0c0308041e1e06050a05220503071b05190807053105100e0c0304082203060f0e0c0a15050409050c030105 64
    0x200c0520a40031840c55941c0280002807680842e8440c007480701015507040023050100c04070307400c80100070707081c9412041e03030807203091040081b1076165003201e5104c501200d0440d0080d0101000400040d12200420041006c41c05203440d540040a440c528540301941c03041d4016401e2115108114120100c0005010041c1b294550101025a044c000303480c21504103071101c00c41510b4240900551080c030014450100f0907140c00640c840c07215040e074240c04100c25001138252061a03c80c01c100409850400c84801c2c000c4111180c41000b41101c81c03c041c10050a809800c80344034504490004e440c01c030220349105412403080c049000556403c02c0750518081101c2c0350443e94100340356000340b140d9941480102d030751058211200a032503803202e03c10b0b407401d54450514003500c400400404400d0003401d80c821040e8403203040c010001100744d05141506c030641c0c80c3e5150b03844000c1040811400c8051100290b00324500d03d840c902c0c2c20b45420a030011164180d81c2d6201c40000800140580e090040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 687908534 1250 687907284 687907301
    0x609062006010b0307110d08010f12050d05030c0d091109090d210207061e1a060409090302030c07090902150319091419110f06121b040e0406 62
    0x242800c103001030390352200e5600d10040c440c1e1a0b102500000080c1c00601c21141c41c1d240b500c0d250161002c01c0305902005042c0345082c014115070425040c0002920322094806152455200000d001280000501510f0742d41000b811000c0d4110200032010400d64148a060081842214992a2452404c083c8800200010120b4038180d000c01508000150000001c244203903800440c614400f9414940001a00981000800580c201032442c41903801044020201c141c4245040103c540c1d04009003400340b183c00c5604e0b400800402040c090164960400b11025001c0d0044a141c800b141101500c3c0585a5011424140d0f44a0213001146000c055496070362403402041e90842c24292411140062013418100003507656442c998100014400390030f0910741c00006440001d614000c5d00a5281d41c26242142c10f400100c90711082ca180914542240700c1016011a042070405030303a5210303044020301081c41021112141c00c902d01c50042c010006171151800240b1541005d24000043d1210074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 687909784 1250 687908534 687908567
    0x206161209050f0c01020c1c0f020a061106090c0d02060304080408061603140609150d05030c0d080a0e0601060f050412080a0e0301060506030a020a030e03030a0c0807020d0f110c0a060906 82
    0x1f1100304095a55040c1d20081d143c03006031100101215282c00842d240e403640d40290440c2040c02d00180045e006600c0021810020b402d552580e5201017020b526000141506a0b10602d0f0307910350005410200d003e190b00c680f240301880d1401303403501015440d2103421a030510222040c030305038540039a0304d402071001d28401142072074218104000002c120440082c00c16444112440e10010595105400c414181e900b000c10b903035070340300310042d0207446001c52808000401c50003400304091207207500c140e250140d60407015242036420210225500d044040b208000c00909100200e2401130f003004d0220803521484071695076422182e80508110040c581c1584203901d0540d0421841e07c0e400300b102e510070410b01d40107996205220041e002400982503080c010b21001c001c000090780c046d031214074a040f076900e0308482580c81606c01c81e80c03200c2070409007000400c89540900b00d0343c025900e01c58001004000d850008800a010408000d02984148005100b90808005158020307041c0400444803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 687911034 1250 687909784 687909793
    0xb040b0702060c331e0405210904060b040b0706110d060b030708010e0709060f12060308041a0304030e04020702010306150201200a021504052803140a0206161209050f0c0102 76
    0xb825101c110081600b17540303044007402c0b400245c1085002d01101c6040400d83c180c000034a00c00051265150300648041c90140345401e5011668420003400d0301c08507642c0d0f60480346890540c3e03a41d44060608800383c001c0240d400d0001c1501080f50f4050784001d040c0c480500b40d101d1070300036401030002d0410b034803a06000f0300800034816005c0c2e1040e2880195001c0e410209031401c15180203e0340381d00302021402031145802000300400c5055401002150300c0011355126011740704114000c10b01c0181d40080105100c1c140700600c82c2030980141c101240141800100d02e541c0c0c0c0c024400d000400340702000181d65441c03450700c943c100710a4040b045001d40c440369040c00c19404011b591082c10489500907143c1010000e010002c04008140c1c901341c15451001641007482248911034103c600308401144d811304c5d1b020801c4200005036002903035107a00400301900d8410100c914404100e001404000346043c40402c45580d5000e19090203100303138005d201028201106904017403800b0b0000d41107400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 687912284 1250 687911034 687911041
    0x714040b1215091606090305010b0f0d0b0604020702060d0203160e0a05040e010204050a0803040609051008040f030c0501050709091b0c14072c100b040b0702060c33 72
    0x10005101842d0100e0002c40082c41e0325109516890043d110b6003404001840210119000e5071107554181200d1007140280458a4100d04000000e9031150440d034100d00380c030404502080d0f510700070329003105000c0e00061070102283c011440703a5200c500c1c0210070f1038000080c4040f40300b100c1303080e00c40b0044520389030b44203865003400180702d640740d881213038840d54490300c03403d085860a5045800611004084001c1c446da01c03030722103840382c0041c0309440100b401400001003508040e0090500f20701c05945041c001d03aa01c0ea50420409541f000603410807403820709290000c1c80c05d101b440e000350030f6500c030400c042e031070459041c040d20b0401984010f81d94006100461443d0070414200743c2c01d03070118001300d0b80820000002c4c58842d96511180000c005180c809882c1c104292600c422002c80e100714205035a5003114028000e0002e11030b1907020b0208000c10014143c454020b404c030644010070041c903003604c820030700e031400d100b600c3c0c0c2d04005140303116141c00700019960b250b01e000784160070706031081c41c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 687913534 1250 687912284 687912319
    0xe011d0609040902060903010e0a23031c2301050f0d170705160f06121a0f040b0a0b0409050105030a03020303160c060203042103141302120714040b 65
    0x154a0201e40200c0d2195464000c5548090035514400c1010b8020000b031107002c1c47c0c80740c0e0b0703c5240c00b080d520300d0f1030b8400d221142c06662048245904690009514005c000c0400c0c42141d104008030342d001603960150070005281c103a4800e8411490004520115414202045688840d280072140f00b400c02c0d04040001400320100d00d1144000b6401140d141d02c528244541010a01d040007500511030031310108050400b0b1500806036100c5070f5400c114200c080359040112024600025800600e180102c2882e182040d409140c00801510105d2031001807008a0103860440c0c0000c40c106c240400d060040b00a00d10035180100380403070040c02c203088a80c130041d44a20029200042040030031840305503450280c0011941258800011566880c0c41d0038410040018021000b001014402d1240041d0380309010b07854602105410305ca0b0f02c0c0d21480c1080039480c078050012078005544811a07080203905204900003040f8414082d18110440e85c1000221074a400c050762051040e591404c4544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 687914784 1250 687913534 687913537
    0x6060c0b0414071701050702011401080606130b10051c0b130506010c12030b09070e0105042d030503040e0601090317031e01060e0a0e070e130603120e011d06 69
    0x20b41c00c6401c040000d02c800310000d042c80b080340c000904109545038000c416110541c81684503484e242e008101c10040b4000144e420702c400c4c401c81e0b450f94081400701c0c0c4c031481c100030300081c14900642c0000300e8040c041c010880c0240f00115000c085000450320141400020318006240f144120082150342e86050014003900421030700066059070750b000080311640141340c0b000c002c0350020841c0020042600000340640044410355010b040c5240202e000d090041d8418460034005031503480c2007908108000d40e0311180024100503070041e1502c0c050b00700080716030341000b0314091805103a5443c100050b4800c00715001d0701e0302c1d04000521804101240d610740c024000c0c10248500700d40d0329281d0300041c1840e0360003003078a8540002c26000005002d80c203c40c0400306608260f900f603542640d0b82d0942444040d04441c05400708440400c2080d55240c08079080304040303407071400021540c3d00c0392605180e00c0c4207008818042042086c0f40c004543e00000051502504e56283c2c5c9840c1100c1008140107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 687916034 1250 687914784 687914791
    0x51602120f16030509090103060623030607050a18030b040c0b03100303081e10052b0605041707080405120c0a050603060f030f250e011203110d0306080106060c0b 71
    0x2d0711031010b504043c800c90450346422170040201c003d5584904000f0b00515051080c41c1d59042130310101c0e803410700303484415020f12000a010f4000381c1d4682200381d85c00e610011845080104a501c8500c90b43d0360808c2140c01346000c1c0c0d0403070005103031514103e140407180342c1114a0605c01801000307030402c44107803054150b9605d0f2402c0d14031a2645030107030000850079412500c1640d40201000358018420024904a603400c0320003401034054104a902e940888401030b07c2c0d00e07580070394140e021907140d4000c40e030040d1007114854a03451414000c600c807500042000c03105c8280009041185142c00c0400d091614082c00c06005881c40030000112103003074600ca0180910000710010b10359681d524410560b90001505440c40040030b0903034144c448500105030100e070920310000c9074400c12114080d1054a603907251085503642080002d04048585400844c10003000e00d8004a07141e0062007203140b10b0f5485c2d1404203081d42022906400d549164004800300000242120b020403049240c0d07940 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 687917284 1250 687916034 687916057
    0x7062c070f03020d2d0c0f030308040611210109062c0a0f2a1b031b060f1506050c03160213020c03041805040305040513060504051602120f 61
    0x10071110f445c00d103800021103652000000340051a03104001808425214464800c00b048a60161142c2843d140041c00340009000220540d0004000601550142c01800f01c4109200d00b052055411503403101c50231102c0e08020782c2e6480042028000602400024051111602c203480307000401114035002c4410352595032507400c1b008200e0b80c0e1f41c0d560000b4100d070300c0e40105100c00800c0d00d1040c0c01c000707105141b00310074401c150044e4100c68450702c5108103100d8404400e82d0148401d440440f103c2482d8074990b000000c4040d48500081c05030701c1207184403005402c000c204481010b0100c88001481e90041d020300808216020041c0400300443d5100e844403010640860954000b0402035901040e9641c141c40c40041c400280c8a00000035100711403281038841030800071a159242514002e66000307000c070b80248020700c09890100b52144200032102c40002c0c025684600003025a03a00f07581c05228494410031200e6296030500c000340b0b814903080a07051400c0c04400841240d449001141c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 687918534 1250 687917284 687917299
    0x51c020702010503060f04200414032103100e180d0e03030a210e030301080f030c03030604020d0e061510030b09070c0804030803090606100305070c1707062c070f0302 73
    0x94645c2e03851f03000740240c80032901300d402078910803058803505034000e010b560040c980e58400c1041a00c1d00107248040702980b1078188800c0c14040258940c150030203400d8102e410080280499010016107149128050400203100f0300784041d5084340c20111490380307000c00c010581100f20341c80e4400004036040040c8502e0940a020100056001e60a0402d407440c00242d040440f4206042000030265050720b80f000240d4503408104a0142d07501d00c511803d101e200d400500c0007403d5450079a01034280800d0160000c10100d0b4218005030411034102c0e40015105116002c1018a04080080e18070702d03170705410208140103500c00000c18650006041c0000c000a903c445030800400d44c090390015507000010584070700f0a036141da42c444100711000740c040c001c0c101200751280d10a014082c01602603491b40001e0441645030743c0c41c510355003c550000486c04020f04070015400c1d00c20300c610400d60040035400d03812040301d010002c041119000c0c0342d07a4402d10042c08584506250181220303411601310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 687919784 1250 687918534 687918559
    0x6060e0d110a09020c060105010327150f090c03050c01110a06180816053706060513020301051c020a0b07060b1804060e031903180210051c02070201050306 68
    0x504244410f070044440e590010407000918500000c1d454140c034000d072424880c03400c1001403440c004034208036a240707081c5c1c407040c42008941d1500c41c4c604044090403001ca880c825000c2c8020503580c10701001c65400e0400c40c001c20510800780f11070904044246080408890100700d4140d46041074200a00345a603128401d0b00066099039600144a038020075a545070050710b81d0304054443c40351000c0c1c0b80d5014442c040d009040c00d440301001600e1105409802e400300100300148003118040b0111100d903a299030100c0c01c0da98010761050400701c903040169803581448103200c1c01303400c0383c4c00450b83e14503030030142c0d401681c40b0100201607070b801c1c8600d103484e140542000da019000307007076070550880301c0402d00e0680c406480d050a032040b4050b080c20711002c2030a08110b9603c2c03003060068001285110068000d45201e50441c0342061403c1440a0301180d1927000600c11400188061012400004290015603c580400980a0303140305d421800c041940e0000f030650b01c40100384920800703003004007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 687921034 1250 687919784 687919789
    0x140f0c0102072307060c0c1e090f0c020c0411030c0a030b101e02152a03070c050f010911010e040f141f0803070201110709150906060e0d11 61
    0x60b00d45107a00302e01c141d00c0788488180240101c0002100038003c50048030300104030180201c4000201a501c1a5030845142c03070240b0209044500d00c00e05402c15542c0742001480b01c05038090030f82c603080c3d9031030000ba180001c03242c0030780b414003200070306805507050006034100300e100e101c2640c2e03100f0408050340341d407881c0e0040102c3c02002903e103020350113101c0c1342c440340c0400c0d40310f04600d1100080d90a120384050f0000e2050303a0700c40d42889101021002d4500040f00346d00028100d40000c0c040f1440c075696001500c0d200e40498000315030389000528140c2c02c68003404800c000d03491506507207038000c00202030701d605c0740c1007402c00b41c60381c0c141401031409014000c0c0d103440e405140140d001c2c2c4420000800141416295081c01b5904014549114400301d80350203002501c04048551940040d0701c1d00120340e0041d544440200301d201d50302d00030310500003495045030184400c0366283d50400307400b50341841c41907000c0320425000203080200344618003540361600802910115040b0340140b4144100300e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 687922284 1250 687921034 687921037
    0x80c01111005180f070e010e040f1104020903190309050a0b0a050304024002120604050c0415050423060d0e07080d1107050f0612091c0c060c140f0c0102 67
    0x43e03030041e51240008100819001062200503108002d5046c02d0b0703640c0c0d91368071140c04081920040c00c00780810805400007502402d071200b550101402c0941042d844e1000a401c00030481d001807022507208503641d0400d03510201e50400f90604442d481e14003801c10414885070b002e0080c0310380a03c18000089401c2d590b613164128030b002003c0b16002d2010703c182e01d5154441424002c1d1402d903071240000e5403050483d0b4025a50300c111441c200042c10381c0c1d40000c1201800c0040d004621182e010000410316146d2001a0040340704150bc846503940c0c9082501d0303003c00c55a52504030741140900040110303a031254210380360780703807030103408912a0f01d850720f1141010040d5120303582d00e105250841c0b0090381c110300c090b26404d03100001d85400c19a61030078400010344101d0781992103601002000c0d07841c141150140d800c1903031074080f10561b0410301a1024072401c0c1c0903440c400b150308645503008215160090300240e002034030302030002615541e180005400385220304049180040b5102c040f0385000d50 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 687923534 1250 687922284 687922321
    0x7050301060e2e0921110d080c03031f0302210f0d090f0509360a0b040203100903050d0207390f18090501020912010204080c01111005 59
    0x54048400d50302c5501e6590824001c11032021139412140080c0e2a40b18040c0e60302006034500315220504501d50342d0641040c80310305040d90003004814544046000b040140c1040c060b00c500855980c289420705510035030261440381d800480748241880180ca4480091481c00d1035420080c4c9241c208804603420300e50308050041e424824540d008940c181d000f40c00c0f5045410002010280b1b0742c41d0000d100d000c8200f200c1106055580582050710103411325100001840c8030040058090202c0c0e071000d0910711280d4050b140c60b6540420300080d032a06100c0e8032110a6840006c000c1c0100300c1d500640103018040850b495661302181e410240060501114000c0461074110040503200031480c2400e104005003007020102052801b0136a0241e5005401c2900d08001c4142d10300b266003003000b0060200c2c40000c413502d54080c001c10f0000d448911501907440824800962201d0134040a14a00038040700c60604012a24803000544040410302514030703803180101207a07665581c1c030318140070011203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 687924784 1250 687923534 687923569
    0x70e10060f0201020702121f0e1c0903062d020c0c01050306120a0f120f020c0616050a0b1b121909020a080709050f06031f0f1503020a0e07050301060e 66
    0x34542c0c030602001c0482c00696104400c000041e0135003100c8c0380703007080303425440d44c146a5910401850b03c00d0000d089041801040525024690a449a607903600f590041000c0c014004000c481c0d220742c0d00c2c24200804c030381d880034103401c501700050500e02e169a0a001a1060705000c400800302e2281d403200040c110606008100315504020b07103103000303240e0f07070000d0780d081d43c00c000750012210b41c423445500c0c00303042101e00d540241100d040440400c00158054054401070340d01c650381c1040001d4080c41003030f0382e0303e0207504241854a4540d0030942c07110f407c550110340b00b035002c108240600300348203503180d0451004004054a0980e13a55520010125072030041c0d402601d2150015000c1c400240c4001503d0b0b0b030300000d200d980c03130b4000055081c50041d076049a041d0000c0c0000d03400303070810718441000a08420030100310000c803162840122500c07c00418142c100544040c000d50400740703601e800800740310940783d00354941044000d04a02042c080c0c0c500f007007400d40b01d00c090780c0d5503c10342d1455040038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 687926034 1250 687924784 687924799
    0xf080408091e030c03030423040f0507020c1201020901050706110702310603080f070507090f0b0f031207020d11130903081806010b0f0705030a020609070e10060f0201020702 76
    0x42c001c0c51040503454410452107031040021114050401006450480750b62030880b5a481d100f18004544440400d841c21389c101d6502d8400e02c0c11003401f8003a60340501c6990b0082c12124403c0d1042c0b01c17480300c201d10009401d0380104189800369034002c1c11a0721168002400161069a450b40b81c4058420b080d00030390701000401e00410244010303410061000c0314504040d95000f00803141c40140d0b82c05100182100c9800d000c402c0f66a1000e07001800240d210300c0689036955250349a08040301c0c41c0314480010203548e0b030300c801c0c8241801c103005c0a020358101c3c014441c43c180c01402022900c40c03480002d02600b90504810304005505802c42e02080d402890845410302c407070240b02c014403040c0c2040d400a080b280210714507030320f034031a00b00100036034601810240e030820425011030761282a11004560040180001150051000e054071700d00c540d020b4031807410508200e51400e09550000c0400c0c4018409100100114444410480c0d019042444030032003820000c3e0300a0207681f102a421008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 687927284 1250 687926034 687926059
    0x130e120705150c040f0e10090b0102012d1401120f050316200904021f0e03060405010903020114010602030a0e0117090d030606021603060b06042705011202010f08040809 74
    0x1c414004e0815203c16400381800959a080b40c507412482c01c1d220b22001900007041440b04003055000010094810f0001240092202d401607400561884400c03011040c5080d18819003002c41c042d101d540c46042c0a410029410300c90318080300d40c240200105215003041744041000380c21300680d400003403a0605c100204e402c5051484650080840b41f01200010743c003011494906030072054040d0381c000e00000f0084510444082d07510364240c00c0441803003070840009000d42d408002d800d00c107622800001c40c0754121440c002c0d09503410b00c2c02004c410450b800041c012140e001041e40c0c1c40303c03100d18010b041c404a903001692002c0d8009030610410b25000104210038900107940002900380f69410800250f030b5940490729883c1c289054a841c181031001000800c080d9045031a021000a00e8035207860b90b203c014103164140342c0050003c00502104800010655201e0140140b0440ca03103880b03412060390000304100056605201401210400315090104e06c105036007074180040c103048003080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 687928534 1250 687927284 687927301
    0x30c030a200a03141c0314040b0406021b030c071401021203071b061d031809060f1012050106020705061c0b0a06020304140402040807270218130e12070515 68
    0x84005034101c801c001c052803015802c900c60310525811003800c0c000d821f8191131319901c41703124800151084d141c041e0207000103088080700e000c00e00703c0e100300c0c50f0003150f907944800381e03280c10400c0a500041c801407030f0b040c1000c01a6008038032140590054024250b8030307030300e4500c29503502c5084218000c14020b16070603c000c0045030360094803040368941c8100400f0708040e10140e50380c41101c80e050255188000034502c1801c050361800e4010030000c0160320400c18910115110014200440c4c0010b0981c0b6401c1c0b208259522601b80500003d02c040d250507070610300400c442c1d00c100d4003041c030b40407040d81d450180c881080e441030f012400004e000020a40d0b0381d04009503aa0000e0007619298243c170010013801d494a88215021a6601000f90482d00e2409500c44111320b528041280b2500300507000003400c1c0601d00c000c10480c0a08046004512032140c180099a04803607001042c0602e00861050380d44400141c50b80c100030104249507903000c051038402e00749a00701a0604851440340144070065 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 687929784 1250 687928534 687928543
    0x81305190c030b0126070b0d0b0102010609020703081b03010501080609180f0706021203010302130507020313090213060201020307120e0712050124030b0403081506031005030c030a200a0314 83
    0x46166200100010f022a0716170b501e5100d03c1c8100540710108200121901050750070206c5010014000000c0c2d03181d40c3c80083d0180d0f48050b404400282e600c0f020403084035140b03000c6410040030460741034119818000081d24541e0301614681c443d07050000000e01308810300510080380e1000350241c82108155400b11943d0307840b076004a01c05070255000d800100038075801600d040381e0700207014841e00c3c044080040001c06010308030b0803c5004c208120b004d04982510031000805400500503074841580b008810410101d4000f001164010020711030301c03d504c810200c01340c0203100400900120340c420514504001c540c003205028902214080c1030040c1036100700010f000300f10410b003001d400c3c0200c040313400d2814000188020202d502090219118a401c1a8010480015019450b1903600051881e070002c944100701035030180c4090100e41002d0001340d04466082d402480b56181c00d035a1003a00900c100846c07041281c5103205c1e031645035200210100159040782c01d000c204140c010310f241d00e4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 687931034 1250 687929784 687929819
    0x15041211030106060e090f0702031e04050907030203131b09110309060906060a1806090e0a11010315270c020a0b0906071e020a0803090a0201081305190c030b01 70
    0x1e9468008001910382c007544415845110042c0110300c55070b80c03501d800120040c0507144c101188418040c1901c0e00c0c00c2482c000c01c0380c1c1c420183c4a900c070341c035020410200000042c014020140180244039420400c85040d10740e0f503900a10301d40e00c82c0703114144003d0b5041668402e400c460705103050302220802200c011401a42c545003a907126640d0503003c01d9440c0016034940703410100600c002c00088034003401c2c282440c90b18450124090fa5038260711000e8460722031b2000304a40111490300d0030014080c04c0d081c0005802c1c01c0c10701010111902c149010200f0348108540410112240544c1880600b100c1030403405a00c001c1105001c148002941d81c040807008646900f54400421095400050385510400460344d50742825040e2100305059102c0b501703170000c154481c6101d01c10004218201962240d2440700040160440794000100004000380030364110340c00341001000400d5000c665105010004805a00e50010614104000260b20790000d0241c0b5450b00010901310301582c4104103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 687932284 1250 687931034 687931039
    0x60f021309050c0702030307290a05011401020604050c06070201021609150b0f07021e0d050d0f0905060a21020c010b040b01031a0907031d0a03030606080405060615041211 75
    0x1d070383e0b1440380c000c0c060b11400034003942c5a4814848100003e1050a46141e40c0c00c40492a0021220034210302d01c1180003610128003040c1c40d000103129401d0307444001080c00101344014041402d2a458081c0c9403e40410403a005080000c0c0034015a4000c02c065408041c0c52119550000c5d9990400001810280110080c2c49000c003000075401d00c01c04180c500030b80911610518201e126030822407002107045009181c050010080503581d9200000410000e029901900407009401c1004060308414840c1100b4460004030a10940c0c0310282956420917080c2805049204400400e02c0c1f000080d0078513443c02c900001d8044002441034001c90190340c41600d0502900c400040150299080329044501070110100c0302d4031070703140c0817481c984c00851034140000c01030320140d50b889442a1404000940e41d11a05000040607072600c01d18004180515018a007410035545d920b40f01c410240c0454402c4290780c03800c891075902d5900301c0d002010002c8681e90000740b149012480410411102403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 687933534 1250 687932284 687932291
    0xc030f0c010e010804080f1c1503022b142a1804020907120b0630010f0603110d020a03050609060a1511190b0f09120301030f060f021309 60
    0x20b03154028502140299400300c4800d050404030407422440c1c1d0068009084443c80b024500703404d0710720600c0b85261711001200e030349900c54114014811295120b0004c05e03007003080885142c0c05201c41d0528140c405900000c80142c084000e50f9261816010201d400800202c448003540c48014038111100759020940d98806080400d1240e2299203800703c03006034001030310500254a080c4190350021410b0182200054403070380c1000403031156000f409240b10f8803d1800b20104050b41c03020307940d031082c09a40903400c00d15810049210b150ba652480f070201810303152003065004030149400d40e071180d0003640301151140c580341d00c000e0113442c2c1034400d640542c40a801083c1750741080000b040a0b103c2045140b241d20940b0003040390781400b030130b202c1e07400c50052489000c64100d1070f43c0b400000a00981c0b03074070040e04000031090540b402c05001301c086940300903291300b543c010880c00c1d20304481d00b01007202d812648509051010f01000c0d5000b1034002c0c40012400302d82130900074118141c515000040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 687934784 1250 687933534 687933557
    0x5060a0302181e070f030504051510080105010e0c07120e03030d0b010305160206060607140607030615020601060804020d0201120524060405090112081201181b080a020c0c030f0c01 79
    0x1e410743e20640381800000e10800c42e1445407030103604219042031051084aa8186281041220300841a20090749100564804001c0c45109000e080c0c090b209842d4201d07000d00300340065484500c141c082c02011010604404802c1a002d031403041900400a41583c1d690030341441d401c0c1c0108160445c036070101c1c0c03800c0046001500f4203444c6410340e09694004149507111203040151a4015500c2240c1c22000741190426400007404240e0042406440106e08076041a40300340c3c052142c205440d0440d0312980041005a50041400ba08141c0584035092500d8890004071000b400c00d0504404080c1028140b04010941d00b46010110a0040b0b0710b0924540030010441507200324440c1b141d1111302e1000602a00c0d074401d416582103845101c0c918a09500212070688062090344a107480540b14003001032240040e0062100e94200c20801c820300004000016011101c0a081c3e28115030b80400d1800102e00104890080f4103002802c6407400311855024942d550780030b0750014005440942e01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 687936034 1250 687934784 687934831
    0xf020414092203020a1e02090406050910090606080d110c01030c1707020601060909230709031407090f180f020301060f08030d1a0a181506120605060406020c0405060a030218 76
    0x6e480701c1a8001d0001c401c640f00d070f8582102030040905078403258000c0c0a81c400d0200894820602000d114820114034245080398442c1054003440b155018001c604034105107038440800e1006905009090004182d0400d2100f1184d410b4080c940588a102c2070b01444a600d8001510310b0480e0f80550702c0072080794949004500f83d680100500d005810610100c0340c00e5222026010740c800158a0911011542c035111700c0c440c42c030301000143c05030700585c0050100800b140940301000b01c6042080c060306c042c1c3d0380d80002020001c2009007068034070103031040c11542d0030342045004010455003884802c1d140c40141c1c0e1698440341d4000b40007851304a190300c1080c402a0b28a185038001003c50f030740b00c2e01d04074161100c096881c800c1a6416510407007208820720401140c000790003155515410400921201004c60300c1d641c0201e4410132027400200907690b8001011071503150103550204454a84101050b85800581c200940c80001403202e1501750105846040c420070122402c40c840c0402000f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 687937284 1250 687936034 687936083
    0xc041a010203120c070507031203050702030a05040608070309050d09080114040203210c0d03050108010c090302030d050c160b0a09120b0105100203090a0306020d0f020414092203020a 80
    0x80003405604244500d1880740440854198415003441c1e400345000d0050752031a081c80881e810031506402d401c110412030742c0d4503200c1c050748900280011441c0240740c0034054800e0003075129080402c58041d0014000901c2500188103050b80902247c100910300e80c80034108040d43c0c00307115400d601e0100025608800402c00302d0046402401800380c91001c032401c42409031441d034920300030100401030300842a4040155041c0380c943d542e000629541032a007c0c44c20b540500b8001404c22203d64014400340e42c0c0801c0600c14400d55040103540c0d02c40e801aa6802d0104444840c1c00e000c02c0c0310000a98405848000d0001644035503641d43c0070f036100c00c44032580b0309100c100174001402c0030005200e04c3c1010001128412039030f004407820503802c280040c0c80c110482d0400c8601d07a40110307010801c41c180b03001c0c00c1200e0640c8103065084c01e00304200101c02416680c56580701c1c0c000503022820090700d800c25144960008400e00310003d10a09029503951341e9060100c4000003c035018a558040c1d060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 687938534 1250 687937284 687937331
    0x51b0c040e0102091c02150a1106010905040c05040c0801090213030501061203090f0e0f04062403060c111b01030e1e0d08070e010804140307061a042d060b07050c04 72
    0x401811800001c420904100d401103042300c0103100f0000d054181c945010841d19000b04600540858140741514101c06100780c00d0f80014059070601c101d010180d0f2304812800e0568841e00801600c1d210510701d8034080000550000c0c2c81035203410800300301245015030780c00c0018001e03111001815500d1034001609020b078031440390b030300701a103000c6003071045c02483c03180d0000e008981c0030030410016a06c95154020b00400101c0c03500100c0410001c0103403034000e01e032141034182000003003603041c90350042e1111149040807131083d64442c100c1e00c0701d07802a401503803100900780469803201524261100c070300240481c0b84080703102d56203006545901c12048584105a0b0769660144484a03500554442c04040c1c012501074414144807407420702c1c104040c05d60280509000319000b00040240b85040041c00e0495015a0400c0c0c100390140c1110680c0726641004a0042ea000010064501e401031040b03820103403041d1000144601407060001e540303040400100c904010700107846d911a4941c000e01c9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 687939784 1250 687938534 687938539
    0x409020d061a0a0f05070b0106120b0928140c04060207090b0d020609030a1415060d080403120203040b070809100903110d110d260a051b0c040e0102091c02 68
    0x1040b12848103840760410300c010700c4d01d909100703041420540d60408040800d800c0700c00098035140890703048407918051402894010f41d64135103503081c1150034240c07000e114004003108517000d000001d0f440c02e407580b01c3c500e50300d00d0fa19503440c94103101c81300340056070052245100601c0b540c8404682ca80c91441041c16206d030060a07080415007660a11503e600203000c443e9240c000c3c030351500c001c01c201042074414501d032000585101c0155001c1c0d074001c100017610150103407030210a140005a420821201540d8114184800d0344100b007000324035601c034580280c14a0700c4003180040403c0007901c064400039004a0350281c00c0840108115202203003488041c0c20280088051398aa0520045100c2c41c6800741460806202c01400401c10130316680703c003143c00c00d0070000e030740010300840703404504000b0b01040c145182042c1020700801c1c80c011150840100002d011107455041010000f10031841400f82c0140f040380302181d2001d001303400c0040f4250050403d01d10038070042c009124140c03580c0b42d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 687941034 1250 687939784 687939787
    0xe2802121b1201050111011b09061d031207141501320f240306031603051f0e060717090d2a0b161205060d06110d020409020d061a 57
    0x4c241c011501001020344852440d5030f07803160749010714084401141ea43c0c0b0151a0004502d1810308020a03c46d0001230b12500c1c00c218140d0380c407940d5800300780c0b185901310700d0301805e40740d881d9030405010b841c0d0055107880c00ac0c403a1005c09007032540301e290f80760704880c0404410b0404440711080881d102c0c02554404400c002c40b02c1280d4814500030b07800c80401c0b40060302440b6180040c65281d01c42c1100b01c035400500385004810080e4a01c0c00300450440c030780314100041541e034070b185d0f01c0d140ea071500f281e0014a141900790f1b481603141c14a90100e40702103c81000ca8440303040280c8040c0002c08401e008a00f590507400000f26003007000035141030382003600e5444920076110011040041c8072842c50300034007000e0074a20540030a900d20315503070045050032032510300c03050850009407030714500b2a81404e4081c1041c040020395550743c048000d0325504283d01040600445044551520840018500043c17000c02c0118003100b65034043d000040d0032000c10003489880e01c8119011154444904c04131200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 687942284 1250 687941034 687941039
    0x140601020a0b180d110d05040806041e0213020c16060207090f0b03070b120f1504090501240f0b070807200a17160e2802121b1201 57
    0x840c07424030b9901a5040a41da0901e881080405041c1500901ca00e000140b100e0301d040c10301031061100c1c03640c4a01c01e0800614292904001c540c540100800c0541070710405418a038040b08900903c1d81010f86c01055200c1c480da0b03621120000307400011109070140300b410010004806420900b2040d00c03501c1c1c000707026080c03808100c14080c1c03200b00d040c60540c50300e0700d00300515500d04001c0c58019242020f10240c071403111040c0301c3d07000701c002007480d0780092940041c066011405010011095010303240800c0104007030504601400105480014055420419641003440c0003a50016500a0020456900d54401021841d8001c50300054103044c000c000400006104699a140400d0400703080980402100b00240c03682d14194444186948144503c0201c40400e1107002030109040038221040350904008610b0744400800d1101410a0b22014000740741c071026070118540288481595a0010910180a00042560800001c0d14202400c01c1402c100d01c0c02d6074400003107194940016803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 687943534 1250 687942284 687942293
    0x140f041407061b0507080a050304060f031503081b0604200114220b0703030f0609090c050f0301020f0403080901080105030a030f080636060a0503060c0d020c03120109140601020a 78
    0x40d02910440da140b05e8a80d00184402c2e003800401c50050180c0c003d56142c9107450405003980b840e5800303040416180a2442c2c55100214a14000f0b50360402c075259100e10120040d81d905003080d0449140c80d101d800100400c101703d000214500344c0a800c8440f4100c0e42a10055500c3d00c04005034603002c800c14005000c1640f40b003c0206920b82c0c441060060499031303240c0303401c6d06520594040e40000e07100c05000c008600c86010300c400801100e42c0402c01290a80c075100d80c4180d103030080e0303481680d03016441d0040b07139000d4043e5540c003200030b00c5040d9942d942e460302c0c00080d0312500c2e1080c04252420000a207030700e0041848840190140c50b07402e0190017501d03085800d4000282001d511814084a0600c9082e80030b0b050ba050340b01c400c03241c0300758040c010f40544980e400103100f5449240040014030640d01d01240c4190021a12040c1c6510380d42c0010340302001c1d024500920213288408030304070502050002600d4122400c5000402000d0a14856450195021602c03203015034481d9a9050005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 687944784 1250 687943534 687943577
    0xf0f0115140d1a0d0c0504090c05120a121b02090702120a0302070605060a0b160201020a081c050105060c100b06162f0609060307030e100e060603030711090703140f04140706 76
    0x31f407041c0020107407291104002400c07a54000c50be41100e41c0903072491b204110f10302c685c0214116450a10f24182445c1e600b12040180f00d9400c000e005000580c04645424002c000c20050510070040141c5c56a040050081c0250815a020360301d00342480081515400d2192010050745d40b01e62095160081c4000c10700f0650468290881c1140309105010020446100c003400320701d44c1c40116440007030361070744081d0103541040e049944203c004006000310744900044003008804000c1012428284150008038180503c18038101783e10409070f045c00804c550484880504032101c205041c2001103103080d0b034004800c0601080c1c10107820402d10640349401c00107107901a14915000c9002441034500740d061100e11248100e195840c0c4100d041d607548140680d6501050980040d800c0c8140e94845804e80310480d110540100c0c944000310741e0180c829000f015040705807410848203030a099040c405807005c00c4809840d041c2c0c40002a10210b10b020400004a43d015914010030b64000031070210034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 687946034 1250 687944784 687944801
    0x507140d08070f06020d0212092a0406081c090b091c02061605030406020f0f031210030c140a06021903141e0301030b0f0f0115140d1a0d0c0504 63
    0x154401c1c04400f80050214001040c00307401142c40942c44c0d6011307846e141e00c40325002d040010190065140e5030380d40c0ca107411030400701c03a0701b0403c044001a01840400c0052545800034034850007590f0761500208000034244402c0c40c00d555680c8802a41c030302100c1c1440c01110407160380104040c0280d000104800b0000030958002072415103028406903040304540d4074880f04440076040400e04000349501404402e035603100701c501410100503026603007500c03446110000c02b119540480420b8070031701c00919031809540e0107900402c11689501c14840e8644d21080428802e050341c0390003180851000c5002000552040307020940c83c20995000c1d10000c071340b001032190380102801030740d2000300c1e000140b002c1042c0041020b642c2c0c0d41141842c8454400081c034192285c10b010080c003441a0148000030b044403005001d07041800f802c14030803590340c1081c02941000a2010803100403050b480c1c0e0201010b1310b4600c442d030243e039580f0740a0146002032144083c1c401b000000040250307080c1500800341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 687947284 1250 687946034 687946043
    0x29011203111b01030e010c050d020a020a170325170c0c010609020415050316030e15070f1101060b0405041112090d081f05130605100c0507140d0807 65
    0x2421500d07098241e1418014200035074142070160b000003182d50f05403041c043c18008240003400030010300d8030007408070710500f440350031020750000703607089414800d0000c5551a5440180382110040c0305042045c2a0010b94070100b20802400103580d00020010049800710a0350b212004070180c000b00000201100411504c0307041c41c01c0122408400003889904050a610b04006031280d0908500e42e4580c000458072806004c0100203104155150f00400100c02c1400c1c5030114001c401141c0b5203043c12240000c1c0000c228405090240164100c102140c0d007800c2591424554171203450101d0998880d4810003003120010071043c1724074209604103181c1c0c19041001180b40441c1500c1d015822942120b489031141c003c20580b207502a0f2054029802c000b06400440000c1040721034010003082501c500c034480c0c0c6214190400c904044e07000340c0000c0c03400414041504c01d020030050044244060300311120f009002c004101c100c418401c1e040641c1c40a0003082100b20f50350356141942d0f102d00000c0c1e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 687948534 1250 687947284 687947297
    0x20d0210091701020408010b040501120b0c1c0905010b042c070b0301062304050a061b0209040c14031b010509060c1204060f020102160206090420030429011203 70
    0x103001d208002e25000340194590006030b455207000501c6086965100800c0e214038180350042190714800d01822075802c4d0488030903c00d5449041209400348508a051031a1590000b00590303004030aa11108180d80944000c1c4200110740c400c1104850780c070403a0484441030380c1d14100350f1114881101d20404903290440b60090b4035000745500e160401d900c94400150610034011140c10f08035600651444082c0c16241064144000156151018000c2000304810101445100000c06000d010303005d80280c8007524508150030190520411405a0102c554508104020a042c0000c1c8050b108964816002c0c44a01c0c000044a40e03900c400711040e4001001d0003000c5001400b405030712a5140103001c160b544519050f00981707122070190501c0c082d6441802180007410150140743c3d10305904a039800d81c1d500004002600600c0e8400b01031003601c43c03410b4100c510104600055000d140101940403107072502901030140d03c0107100300c1890966488004100c01e8202c0ca070b01650740c51080c20f120 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 687949640 1106 687948534 687948539
    0x1050907060c0b010b0f04120605011e0f03080c010b0303191403010e060d020411070b0a0f270609020d11090903090d030c0204020909280504020d021009 67
    0x40140d0307200003a1070b6498002050440b8040c8c00000b50b082290555410720900070442405554031091004138040074100c815540340c030840d403803d801d60001b2030661ba00c2e039407590014021041150b4031120ac4030380c180e5050014042d00c480140c42e48000610b0010010081450340c0c1503e055142c08200512401d1240c900b040c2c1d2003141a10292501d008920102c4e000703003442e001c01c000c43e84c0e003c40e2140401545000310350180c0c003070407001c0c0f0551090003c1c200c2103908186043c0d60503a03011744281106018a02e003400024000c2c9400034520815070041040b126080c407040300c01940100e501c50300303807402c400c51980000145c001541403103902d4000c24100c0c01985006410300100e984130b0003c55595030112440307250003800b04002c5041c076004405400e620010041d02c00d4003806000302e541a010701c11a4801d0390010034030a0a042c00c2c0d004d00c00307058540014a010048203000c00b = true := by decide +kernel

theorem cover : BRFrame.Cov 687769784 687949640 := by
  have h0 := BRFrame.cov_init 687769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 687769784 ≤ n) (h2 : n < 687949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
