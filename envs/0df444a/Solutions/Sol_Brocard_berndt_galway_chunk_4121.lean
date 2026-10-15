-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4121
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:37:32.048529+00:00
-- url     : https://prove2.me/submissions/f963a6f1-6308-4503-a1bc-794cfe289ad9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 741007194 ≤ n < 741187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 741008444 1250 741007194 741007213
    0x12110405010809070801060807091d07060e0d0602030405030a030e160e04081b0607020c01140906070f05060c03040201020c010e030d08150a0305011b050f0f0f0403080f1308060603 79
    0x902c001c0c640101c00d110450306090755605801e0b0a49640c0c3d04510340310707002441c04008181c62405102d4442224400310082c46c21070030500d580d60310081c0320380020040510b07091707480d540750782c07000070406604020309541c2c0e03183c2410315030b6481e8410740034900085d1810a90000505001c19011000303411003184034103c91030a280c00302520400340054410550410540204d40b10021803410341360b030485e007e0801d82c41c4c203103c060300f4007842989060500401c1440660910314003011202503500031942c8544441a50034071650b44c501c0ba11f4001c180b40318070014020030f182c2c00d002461285100341d0885100c2c000c0c82d00119541c0c440f60740442d826074054140744140f41e014540c055889072100c841120b02c0760010001480440180d482522a0b075543c400000040c5820290040300c50003c1c2051f91912141000c201c00d10300c41c0f1400d00031003200c0425500c5110942408550045421091258a40f944240280602d0b801080a20b070030400380400000d410102190aa1141034002c1c09060200b8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 741009694 1250 741008444 741008447
    0xe1902090130021519090504150b0f040503070815150603040f061b0c050115050907120f0911040b180c090406080f0d09230f060715020a1211040501 65
    0x10480b4000302c2e408044000305000b400303140700291242c0e0f0b5015040401240318800040c142a40c644c1081c1d00481c100102c0545490000041c00210313140d80c2c0081c1c3d070320b001401500c10b441c0181d811141e0705001f0304800291400000442c8621048440c5c203040e003603107030021644442e00c04098400e030040024000100403500002c0740e580c001e4040c16012a003000f1064011800016407004d020100d564000d100041c02000d20810034010905480341e50307030904200004030750b14401000841041010381e050503e00450703401c00f08094904000c248442403181c0f03040042c81c03c140309480d020741d00d045c6896032180740c891214a0500d03280100000203840300d00c130941ca00da11a00c4507680058840e140007440710410091188000c202a0213041c000180d401c00070030408041d400510107a500390480c103400c18115240000c4078508036868095820b640001c03818600806a0250081407544418611024590010208c0c8541d0b0303900d40748801030004002c009c0b0380d500c0309071451030740e02440180160b5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 741010944 1250 741009694 741009779
    0x40305100f200c161412030409181205030610030240060c03020c1306150c03081608060d170f09030d08060907080a0e19020901 56
    0x1007445080101e82d12541c1c024490900ba00c2c1d604840c2c100400103010080c0880c207202c650600c2d040c1042c10401d2910b00800103100e040c01c154403a02c1940501e4013a0150b060030011500148464101407018500061080d00708040030720094440c44100704201120758800c404a0744550001400e4490303504840c88100c000f5003050f0380d001503414046078802810003207100203c1502d07000302d00440c8840c4c00c2c0721400200040507401213023071040054940c0c0001e90041814860b41d0b0050b00d10306d4022005014000c081d000c0c0b83c2c8204888484580300d20001c5134082c92080300070740603445149071500c03801040e07000c6800c140c5202c1d001400100103e03e1524181006049040c0036a40301240d10601000c0c40a4990040141d00310301400000c5010942c142408014201019810201680d141c5500444c420a00007060340c0b08200345980060400c01580c0c0c01102600c030310788100c0d1000303030004015081c2d072540c000d0141d00c2000d50794000911010381c080404000c84040003568221900081180c1c1c03030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 741012194 1250 741010944 741010961
    0x20307080703110f0414040e0c0303040e0a06171c1110020c01200d050603010c2718060608010506040312050315090a050f060102061623070c1a04030510 67
    0x100030701080100c0c030741d6111130058806000c240010545402c4072400708403c850309902c000d030841d00310080310005c42c0d07800b1066134100c4400406030426a903074868840c005180c15000354401001b08020800c00ca0000039020448031f042018a01350112031140070f581140010b000400281e0001d844802204041e4001d06080f11540c80003050410000d04c0b4105141442c001c801710040d800314038100268150b00070540c21540c02d9008024502080c0c0d00200500300c4800b4200c0707409555900280c3c4040c600420b54000d19000d050b01d4154110b00c400400a48801e1040400180b0385500100d1985400411130741120340c0300e440c1c1b2501d400c411005aa180d0001041514600a4003e0201c05500c0f030101c1c2c1d80c460350724840c1c0050a80380004154031405405006181154081410001c5448406150742500c42c414148403603a0001540010310300704104411481000340031030448104003034030640300203480074801501c1403800c4406000d01d481c000d500c0080d0480d131084011940d0050039900c040b21 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 741013444 1250 741012194 741012221
    0x80c01121103150a090e0d05030c070605091024050d080409061d0a020a1d04020c1b01030b150307050906091c0b0106301503060c080703020307080703 66
    0x1051118000401c0c03440d0812241c105116059110b1503165140c00036940000d04100c107070400100240e60100355440408002c5481409000808103001c001d000e01501c220541c0080301b803106107085000c89482d86540c5401220540c20f01c10031104ac080c114204034485004006104800c920f00801c004a41010403000c0d12102e03800c0001251011907801602d02410b8031003c1d1121078a550404209202e4004044c04140c0340b05201031528031754440d05001550420120f49254801c45000040c001d11500000000301d202c0c116840e030024000ca0038540b61113100341c908000e2180d038201400f164100742030303521008100410009008500480c043c10041d44060011420b144000e004245441e4000300420015081907076030604001180701d1040c0581407a1421a05a00b070800c5440c01340000940c994150b41c115070881d03031041142ea40300e00c00354800301012200d56036407801c240c0010f1072002c0440e400a030303154002442142c000d0007264080c5007075589894641e5503a2208a0007801c1c41000003e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 741014694 1250 741013444 741013451
    0xa0204180b0421050a0807301406010c050303040602031308160506060a1a0706151e081501150207030b07053f07090f060906020c0a080c0112 62
    0x140800c000d03152041c8940d103c0c255140c11440480d80b08000e80300c4411180e03042040070402c0059083c1e01c140c200c1d8000c802c0341022a840603803500381ba11408140181031ba0100000fa540030a601d80d25006084202400198411103480c0e0800443e4201c2801c0c0d000b074515481003020070001f07002540255440074074240804c590485a503124061580040d506845803d84802c0c58000d0080c03d2024903084030045400716229454501d00f0022401d60740340030f8104610110318441840102d80200c0031080020311564421501c40c000b000300c4035200010504525600354003c61880b000096000462080ca280b041040e8a02104c5601c03030405820310f2011030054110000004c1c80350700d1030134011000ca85a01e03484a05020404c03c009000101d00c107205040380e07405441702c42004a19600a0702003507071700d401c19070341c0f51001d4503100704980c8400e5408245c0100080ca032640181128295070040d401d42d5a841c1c42c0a04010307031101c1601541c1110b402103040b119441d030103a00c00000501c2445000b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 741015944 1250 741014694 741014741
    0x10503010317070803010e04150b032508010531080d02070201030209041a0f0306130b0601020a12052110060f02121819060f0c02010c02100c0b16020a0204 68
    0xc5071241c10a0f403040b17903012a032409200800131201041c0c041040f040100301700d60ae580c203001a03038409500f0011245842c44040300c0d07010818450444000c1c1010340c00900c0785040014100902414a0b101c00083d50440e51081801c480d180218801040c0c1040070103080c01d4250b45000c000398441d5800b01d0506600704022241903e6074002c0f1b05c1e1111050014075140342d0302c0302c1401898070310408158801d4010004108802c1141010036482c19000002d040899590800603441c00c0821200078145142d440000c10314158030100410016456060b181003c20158442d241094000d0300e0000e035103418410709001c80c5105080f20f030f0504c1582d104460801040b4003c2215507030049900d15a5103800300d405201070b00b080352050706481c0210b0401c0140701e29040008108940340e100280c2080f55400e4041c06680c0315422030400d06030024030945019103403982c081d2020700e00b50001c035900d4401200051003400080c0c0704070308210701900546848125642000020503090318205085103c00b8202c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 741017194 1250 741015944 741015953
    0xb13090b0d2307060203042103020c06161b030503090f0f0a03050604170306010c03210509030307020c010504061d040204091104210c0e060d1203091505010501050301031707 76
    0x14514402c2d00680d007a80c89240c018141d81c1000e0a0382c10481c10355108010400141c980402c000c1640c040b0100720140c64406443e08900f095140000d1543c05070f0046000c00d01c0800810301d00d000c4500c0380040308030148030025003000184c2107200c0644607800034003e0540b58180041c00e543c00920080040401c2e2002d403001441440f00c03900709803150344c4040104401c00010036030382a8060400190b42d411880d040303000900060300d4040090401c0429400802d01281009880001c0c1150034020301203880d00d03038901c540d00d410032154440144202c40481c24694020401c840949100750303501b200b040080c096400802e01d842d82915003183c2e080000184c091414071a041900b55082030700c940da01d140c046c6084000420114420b200104408a0f500069081c0700000844540a2209a4507911074000881030f20289002406500000f12800b0100b50b065010f03c2c0d001c2e00c40c0c2145c1c04e402c81455080b8046402c24002c482c0418020001803000c6030f036203608044141c004068440c07a0060b40d654 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 741018444 1250 741017194 741017213
    0x150b0a0e040b04230109150b09010302120a0611090906010c080d0c0c0503070803061009150305130b0708160504080607030b030a05010903020706030e01020c121308010e03070302070b13090b0d 84
    0x4ca203483ea550f402c0280200b00008040a0382d2051550342800214500c0c0005846800c06210091040d400f40b44110080281070003080142d942000007003000441c9030768a54019070104580d18891501d5000186266000344011401c0d142c10070011030030042c1107a940c1004018509071b100900038014140000140700b00000c2044030310442403242c0740d007854014481c08540c40c03c1849d00380030701060240007041010300405404040d92501080c20f844002c07200b68104a0110064580304010040142964005400b94014002c1c006078961480d0340c80d00c12525406a030058040340e8100d900811042d51003600841e008041c0202902d50001d200e0343c855086031210785088025802541040020300d4040c0b1030540110f007241e000358a440c503c60041c070f884081500601c41d440c03001140c2c1c001080c868400c88000351094a0003080130000040c5100e64903042881d080f070040c401d00401080c0d00301002d06680461509104003038001d0704203103154010701490340403141c001203a60040300102c0d03180c15 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 741019694 1250 741018444 741018503
    0x3060d1e03030506120a030e1503040506010302010807181511030715050a09030f1d060424090302091b0706181a060604170316150b0a0e040b04 63
    0x14201054988070300d009029280b00505480c80b4480002400c01c0f01c40020504103402c5030315145c440706649409001503d0301250009015020001004110400038000fa01c6c0d4140c82c000d0b01c1c0c0600650301c0388021500807160420021042a401e2010003021400c040b0a80c0d1450b9181008102100201001da02c3c50b00300c904155044210b041c02d061796181248590b941000b10881c003070102040320b0318080d2040303a0300285002004242c0742210102800b1004070030540314001c00c541d6856940c1c2015280103601688681180c03c0e1000e000050745002e0f02c40c1034101e95014010f408940d0b50711005a8110000740f2544c1c0c40070404000107000600140b20f0110030880562658540f400d95042020305c0034006104008442e240f4014448a03a13604801c0d50b085550303c1490101640c03006150500b14080d8113140e1540700c100f49240c8042180041c000007042401c088108544502c00c8100300c0040068810905243d00307050114001c106d840380703050344c23090264403512000c00030700102421444610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 741020944 1250 741019694 741019733
    0xb060c0a0c08070b0f0306040e1905160f06080c0705060f25140d06030c0b0406080903030609160216240e03030a032013050a05011e0503060d 62
    0x10810601001001070345480940700e820010001c0606003d594981485000d00e00d0074812400310004c0c030700365220380249080c00316035001c1c0e41608840e41888501c1b41012042222140a80046c1d1580021021500c004840b140b900440503e840d1100944038040050500024038070b04000200c0881c0d01000950700900316115100c51526090b00e4082d0600300c1c2d201c2c1c03c115070ba0309852040350164084400034000300c2511140e55182d5001c0c641900402480c3c3c002068141d14207000140c2da659032020380100c581c00d4407446105e9645c010515182c4c2700031036103541c1c01740c50b00003c15170b1400d0740c0d610700c181f00c0414012950102041c00b105440c040b010b83c8210954080c1c8551140003204100c400f02c0c03054442d0a00c10580071109000036164010b10b4003040405076a0348040c801040394010303581c00b51241030011552035406d4050750b50000598080c590090301414000100c0d235110705a50311040402d5105000041802d036001c603000d500c054601035001e418000b0f1400462407440d03040840d88841e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 741022194 1250 741020944 741020953
    0x709180f1b08030315090f041e02150405190e01030b0a0239010c080103080a051b160e060108060d060b03010608030d14040201020304120303020d0f150b160f05010b060c 74
    0x2c404400c940c5c0f0413940b03101c1d0080740c0217070500c03000000c0b00880d40d41040e40074100b040882030002024802440001c80a580608415003c0284d280300d1402001591001c1d102117405059140c3d904010481604c070321a40c1c148a100100003003405c07002d660f81c003c1810a009858281030400240c464038906c4041980344d4103410300c80d00c07a440c120f2100340c1c481159034020310014902c84d901a040050500c0058a072842c001f0781510581d100742c0c201c69503100403417009950b4840100b003490f9180081c80c0741e43c3c9012503190340811a0010a013085210f014165980c000c10b6a800c0e00f80005d0307a150170720032911503481342c041048be5603081c05014080d008600046441d0b100300b0b0703220402d44803040d04225000c1c40001c248000350f640030040724291106260700940340d030b8003480c0440003446003040c1290302a00e080c28440c1029144c0d0450103004550480c10707a0090340780c45a480c500d00c1355212280d030451040c580c00000805010701014900d010384000501c0e0303e50030001c00e800350701c14104842a03402 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 741023444 1250 741022194 741022201
    0x306110a0327020105090315240910060e01030b030607121805061611010501060c1209060207090f0f05010905090d0f0c030305040f0f0803090709180f1b080303 70
    0x14144254100100116444a80c0034281220042e61524030324001c2d04104001405d468162010010110045c820f04070124091600c2084c0099440000d2040d08910840f000c00d0440d51411240d1a80034500e4a031118008910f00381060b0b6540300700300d071140d0506498480c2c0c00250744e002d100d07039031154007a034846003c00c1c650450010304444000c0000d0f110400700c1b03001203010441c0000c00f507501110085094031051140c0c04142c47d14900f040c07050b07121b582018000310300c583e03200028007042c0f8402c120101101590700001d4039648214003521005a215000c10040d00340c0710b4000c800c40c0341940b0400074030026200b01000c00d86609801100384d1980354024402c2c603850400140c004d4513064608004401c1180c0d40060025031900d0300501055210000b203402c0c04601c128000c0d41a45c003e00e0380e22900b500d0302d0090b00e00c0d001100c006250340960000011840c0e09401040c2102211501c1ca005824560381c4045480d018030b1010b60b6044038200384030149804040911006e4110540115143d14 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 741024694 1250 741023444 741023447
    0xc030c0b042d080412031211090f12060f10080303090109030e0a060207050915030d02060a1a060306060d0605090114040f111c0f0f02030915010b0d11040306110a 71
    0x80b04030b14403440300e0040c1503000403c1018080d075091321005400e40e00b81d14440d00b0111449171a1068030600e85160001598150030218000d2410001c00d4400c504c0001044003046014601c00c44060802d030014000aa003044a5610290b4001c0701d08540071030154640019500c2c54000711445038150f035403051f121090680090081d026510110303410855541401d200035101d10161140901440140d004121022074002d85114400400340449041c2118244029602c140c00d5412920207813405032030055003400030301240380c0414098600d80c51170729048140b0000790b0219200f105456039400001c1483e03642c1d01041ea0081501c079194031405000d03c0e041104441a400184850310301e40000b0040c0b102460080d20000752112003840c8591440d140001d02602c900c1160810303480c1341c680c3d041c0f0061040e038003641c0a40c00d18000c584207400000e82d00324900c0c80c06c0c0101d007001720b030600c040b4003000744e5500460b0300c40c010031800d6400c15603290748420941d11311118549038440081810321445 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 741025944 1250 741024694 741024743
    0x90201110a0c1815060305042904110402030702070b09180108240f01270609020d0f02091f0c080d050906070f0915090512060f07050f03070c030c0b04 66
    0x141c01108100305103080264100702600d400e05c00c000c10b0540716800501070110b051012034100908180d420020300918505001c3d545085608484020b000204550142018030a4a00c0b425840e00102000c174280703c0b11041d650030812a095001c92000b14400e41c03200b000313807203a000300f090200030b000c1d5907032804205415804440380c0d8002c50001c4802c2080000311030100d03504480c014104203444150f40342d80c2510340e060005d02d50644034140074000410b80b080354002d01310684a07440420a102628001d07500f45e110f64452158440c2c0c090b481c2c1d0803244848106013960240390704010340f00b43c0c41c41d50f880541e81c0008240e03650503643c0f00108541c010090220760b03803104031890714402400164402405140e810b006604200f45880101040d03a4000e86282d0080d10006124402541d030a06480d5036400c0100d643c81038000c0a180410449030050040d42c10021400340c440d4116940c2c0791088400c800114015010040c90280b080040754842424900450081c00d6a240e0564200d01aa690 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 741027194 1250 741025944 741025979
    0x114041506020a1509111314070905031203090307030806031606030207060c020c180c0405090a0f140709030609020409150f0617150c0c0f060702010c0504050d06090201110a0c 77
    0x90900c3c102c40000f81b14100c10f503201840c1199880b18445440030b0510003003042610204184c901d1405200034103030800c180d50200c5d1021001c48020b650030400c848043c0c002621040402e0b0310a2003040c0010b4060104240c0c07002010b000c54032004400704003020100400c1c0e0007000442d90009050090041602402e0000d070001d00007044015240004144040c804168183c3e0840d18800814450441c4804803030040c0302c0144062030504047c40c08074010304012018101a62402e11051240c1d000345c0040741c4601c900d503d9101d00240386496a00282a259808a0b40640d80788007950003c0c016200304501000241400105104c034a1031784001c43e0520b0300024440d100c44042500441d03030008031003215040d50b510040b00d0782c0740c1e000480340c00e004210490149000c0c55000072160500020700c03522407991940280400340c1c1c03040003514980314501407607400076152031032040883d05980188400c1841807400504502e0206201d90900700c00601c205c441d25a034110801c60ba400c1e00c1302c40000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 741028444 1250 741027194 741027233
    0xe010504050609070e040b030a051e060708070c050a0206030f06090f13150e0706020633010302070f14030d0b03010b010215040c050d0c090c0f080114041506020a 71
    0x9810040e000a0703d40340028501410403140030f403861038940340c603006109140c001808548441d41c140c904240c40d10b04190403912170002000f1050b0302200c001904601541c2d0944560000d611080c60031103d50070450303030503503281c4104902c2c880142c13036000003940300322003e115410203410706400700030802c0b002410410303192142c1030034490210b102c1501c504505074003400b802c0c80504841403d1024292850046010b40540200040c80755000b041180c0f088008071420303c86a1500c4008065a680c40406001440d1f0070f4000c4920b0fa500030390041481500900490009825503551820854861004141190004104c00c101815540191100904101d0080c1300a850440c0001d680700d2140c00920401d0b000200880c041c042030784110740140c030015101081d003078914100b44030f0400b114800d00001901c0c00141107801d9204410f070705240101a0340303c144991030411424101d590301d4412540c0942d032000341d80c090000781c06c580001005142c000d8220940c15003008010344000740c10056 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 741029694 1250 741028444 741028451
    0xe0f070303080a0b0d080a0f0801091418030904060b04060207060302120a0b01090801050907030b0723091306031a181f14070315081b040207020414010306060e010504 73
    0x100098002158079031100a01d580011340007051130000718400c421450103400103100040070b2681d154070090401d42041c2c582c4030f014031030b45e8030035480040b40e00c030380b0103155161021400b01d101c83d02d20401180c2e1001c040700c2268146004100024221141540841a10b010001d020011281c0501105009144d03606003103041c40380301c2c01ca00110394001051000c3d016580c90114501d40c0c014080500070301100300081007103140040e28281d840394240000c3c0d90000003c0d001070300c92803041d0b0302c159038201000e000000d64810039441074030680005a040354045c124501d240428400b6200b039100070341c020030140c01011128690107031032000c050120361f1130749030a4500003505a00040c00c2d140c1c200c01d9070622000d111000c0130400081c0715505000340d0399186281405030099264000005d2001305810b0710071040c1e5107280e801d54412a2912000407081c01c110328051070701c0c1586c080e03c02d203800600080303039034240001400c4024100f41c10454180303a58140502110804051660141200b9038080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 741030944 1250 741029694 741029699
    0x90c090d0206070302030705060c1201050a2d150804060b0402040b07031b0602030910051f0920070308010603051b030105040f0b0a140f0a060f050c030c100e0f07 71
    0x1510200c80400d0190081d1070002d000001c041c401c00c2145d0903540c005c4150341080c284229048131390351102c210380441d001254004a00d6250060040003216a01e0b00010a4282e56941d00c4000d01c0300004040102e003c04907000400c02031281001c2c1e118504d60792112078500d450714002e4211155072402e14080c2e44140420302409844400b00e80c60507416081c00d844500c040181d040d2a042c3d454001400c4034000300900c4009840040c240030428030380d88007405a40d40301031051001c150041712112400412030810844030446034401241e4444490841d0305000c0107030420301c50340d480903600710001581c041c010403e00f5803604c6502d03003100c402c803022400c101c808015840d00d40818056244600e5031010044024505036126003254003001d0401540e090307842101400181c1e80410a900800ba43c0701001d40c2864143c1ca07c0c000e07515a510360441c1c10441010480345600003288464161000f008628884402040710a030889450480481d050040c03003061030501c00081c030754410903403010806 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 741032194 1250 741030944 741030949
    0x6030c110d0f210906020712080402210f0609150f0903040b09010e1806040b0a0837110f03010e070e0709030b1e01120807030302161b05090c09 63
    0x112148000e240c075040044102155007114000f6020102c1d4030070601c0d00300e09008102c81a000307419118090340010001501c181415103046c0000c490080d4025041c820340c030a40b1491000210341d0030301d40400c641c00f003413074410400d1030304106032010030542d0301c40b21491003415130b82640d90390f00c2007800402001505014036202e40e40c1c069801035401c00c55011454500030b034410301d41019210340081c20b0600760701450000d44440c0300155076160140d82460303680a040e00b0480908001c4804032002404540b0f488802d410a44c688001d009140c0155650020840701c0b8600023224240d0040d1000300034038074140100042982e5541301030b230099041035100c1074034007030224044c4122454004407260036526064200d451303240d180c00003000303a42e02030141701c0c882c100c140302110001c903035100f1071a00c1d98032015402c0020810000041000c2400c00070100003034843c0c3c001c0d01240e6000139190750484406d5030b80c1140050001103c200200170201d04000d1454000c08454008a940405614003500071f0701 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 741033444 1250 741032194 741032207
    0x80f03071509061404060f0b01110712080f13060813020907030c02031c021e07150903050904050405060402030c09070c0b06060f03010b041403030418050603150106030c110d 76
    0x200c000260b0340e40c240e000901209400901c200d0850618105082c80d081c40c1420051804105a8108502e4003a1000d029401000c1c141c2c84840401d0003003468601c1c28880c240a070044443c1181c04400c1032108032002406e25002c0c2180c040a102100304150130440020242200103012031a0210302840c0361016868419003d50840c0d8545008607120800b120203902d5885098400d41000f0403029501300c50440560203050310905103140031a0218101d1140c0c80b090042c2400a0700302000442000319030b603410340c86502c42070310a003402402d1684100000d012110100c0c1c06035825003005081200718541807003201e02c07011040707800c8030403414150401840807290f03e2004144040e0b40010031082c1d6503074411b803460b840c030700d1082c80e59130742c2c40d02e820340320301d4020b032048040c1880c0c40c01c44903c07640b0f0084141c41c259500101c44240003900b1003441c3d0b02038440500000e4040c000d40e0b0390100d40541c43c07050035000c1c1100c1c2d180460b110700108401085024280d009809681049181d0b00c20301da0f1004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 741034694 1250 741033444 741033473
    0x1b010c06020901031103090a110303040528030501020d02180109140f0402070803040f0312020f0910052701140309060a050402121506010807030b010f0f0c02030610080f0307 76
    0x20320058880c02003000603002881640d603100591800401040303074000c80000c900c54003501c22100d84a0003115082856520300490054030b030701a9036007074034401c9545006440e011007140c011a0740c0181d50f50751107107400c80e40007804034440c0c0d5400041c0d5204080d00b0040d01341c01c0010030720340305800e64942020070104401081445210f080600c050300450764450301611a1190070041c466907038101440e004004083c04141200892100640726840301c1c0f00d4400e80700f011000b407104074a4080f0700300030000e41403446c0300c580c81444810302800d80d030f00e040141c4d60f21641010034582c40424019400150848000349030000c3c030b0b44400c0003000203080c0d000ca22180c01180b20712001c1540d484610001d88100c40d03410aa140b00d201e501c0e42507001d001c541c100d00c1d01501003a01e0741960340d10380c3e030401c80548000a1020b40458460f031802d100da548203158900058010b0314140403841c400750b0000381425819110804001c800d25021321a0340010300891600e8070070000114948116541c48014492002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 741035944 1250 741034694 741034703
    0x30822020f090907030b0a05060a080f1504021f030e19150b010918050a0c0c0308040b040212010e03071a0103050a06110702220b190e0a0608030415021b010c 69
    0x56001c6441c00c03c0401202002c1c50303000d5031102142c40c01901d010003d107c12a40a071050f118020000b0702180c0100e040700c101141100500800042d00d8600381d1480c0c0c020784126004a200442c0148890198080b281491810b03038012070450b0040078024505201000c0101400c01c9003850070002618220241c2c0c00c0312044076020980d1965000162034581c115880300e2410030020740c00c0405000158130240c4601c08250003040f12110301d00b421101003040342401008510300c0c0c40841d0204004002d59940244018980d4400d4008000380f58203450090b0421641c80d80041034800c200055074a41204030300856030280441c2d851901d50030b58840d01c0500140005a4034010700c02c0610404c0b0803a070700150090007100e05050125105d441440509c1600c08280b840c01d042222a07103040c08014404002c003035080e861090a05480300e0301048090300030f2840981c0c034400042d5511007400a00020070305240080d280c4080700501034207142ea209040c44080f10f2140b6026826078200d1401000315401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 741037194 1250 741035944 741035959
    0xf080105270c0922060b04050604030206070213061401020606060c06010b0307031404034b020304080a12170903270a0f150207231c030822020f 63
    0x10300b0b102e18440e20498000319003140116010007040f00104c494514160801c21003040f5083c0e80701050341d81030140b4081c850b40b1007001c000800c01751501c00301800130307240001c00b0010703040e404600b0102103034100d500c420411403112002a11079a018402250302040c00d44d0018a4041c8011160392a0384050040c0450800c004c4080740c1241c1c0f00740d11407000e403c808580303e90f01d030910b8140a010000c020141c0c400070a0034103940da030788202c0340c550000040306441d140350208182100a07140301c0080e0000307a0840c0b109000004184500300070007080d203402064110611524098003e00030020007682d0b90742034885609011200c500081107030107500f02c0c16654100e0170f034040400403c418007003da01c0c0d48480543c0d00490402c0200000e181203d410b0001d400820042002c140e854000318410107500300b5a150764035620702601c03661100c107800c0003003502900c54003200d0340c541ea038400600150005071034141040300c42651a1820140d0003030480c80070106041c503500041d04209891303840b901030b554 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 741038444 1250 741037194 741037201
    0x70905070c0605090303011809260c01050f01150801080a1502040b1309180c030b0406110a03020913050f0703240803070605062d01050f07030f08010527 67
    0x40349502514090744036000f4462402e2850f0043d940b60800e003ea102c10052280340300c11008a14499204038a80c032080040c0201d41c406445d4444d1a00b400c41c030700c1c0c0d01c2c000b0009180d401c4000c3c42002d100f1040082000595410503413515506180e000c481c1050120000060003c0c40300003a0040e009030303001e0ba0310811840c540140f0300190140b540041c3c00c03007102203440c02d0700842806250040d10142607003004000d242c81181d2180c1b00960801803e00e4002100c00c1c0b000c40c500340150f60b4001e000ea0008159013604105070452a4004007519002075400f18000d40c6500e40321035900c0c0c50403003400c401d122500b8050b2103c084581f0180c821001e150703407103c1e1000c1c078600c5001402c4414045a10080041c1e94540280d84c4070740c0207103000c84000b494907001071100e280000e4508021922480071380c03007400d0407400d031002c80400e0344100ca0510001303105110400c101e000081020034400c2e6601c000414080c14042e00114040c6c0000d0301c180d50b510b1007189165400c02640b0341d0125024143c1e0083d0700c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 741039694 1250 741038444 741038447
    0x60c12050f07140115171c1d27040c080607080105090a0b0405130b0a0c2a02130e010c0c02100507030c05060106020a140606030c0402090105160501060602010e0c0307090507 76
    0xa21103195a02e060040c1c07a002454030031240d100d81c00b026541c000c2d600030300321843c3e82c10202c07c20b80900002066600194401d2102c020640d1341d22400b0240c220a0743e00c111086d41520b070080ca82420078041100410030080100c18401500204000001050729090218010309421014040d0030300440e5403c0c001081811a900070109001c170150042115003840e204140090710a0320702a50034010010205400c0b0300c0500c91000d016101e541d80000a1610186500c4648101d042401e41601a11003090141e0303900c05503245c400317904240020340901111001d03070a441403690600140065402c0010150300c94074800c0030106468603116076112000d10303040d104020b141201030030318801e00001003a02c88e000a15510006c3c0101a100142030b84280401c0d034855044580c50f4058210030780151007428640c01900070510141089420310701d1944400f4845a80d424050320b40342e440300070030440143c0a10a513804c20a05002401c041c50110010070340e54511440350004203665240050100ca = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 741040944 1250 741039694 741039701
    0xc121104092d05090f0a1e0305071203020703030b01020c0a0501030b130501140306061f050d0b0d0f020103050c1812010e030703020a0204050708040b070f0203090a060c12050f071401 80
    0x1e40c2c040c4034031040a0755503078000740245002c5030341c0141d5100c0c2007140a19000700240c1c11081c103078014040803110004401c0385031031149519044050041c244121000115004104003541600b41d03401600d5400c41d040041c182d40a0300d01e210305541164100403226200d03684001d050360307404e080201c3e401d072141021445100410140340310507480d100c00410700c0881d07a14010444601182200c0f01c5c0d440740d0b400c2151540032120100300c0c414900c4960358400f80100007618906c20a40800100d5402540100c0d4000080300411242545619a10000c542c0c15226480d000084600040d0610803880d04286100444d40b4080e4811604842141c00682c001d40011010408003c141c0b91600041d240181d5144a00e40040340f2072400c1c4000a6086480350b4031891041c1c4d000001205180ca9408064030b041c403400010201710f000070844050141c40d8400654010710302e0b03980b41c9514446a08001c147e1034091500201000410400c00020100d9003090b11078460300300304d405410200380c0075581e004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 741042194 1250 741040944 741040991
    0x180b0a0b0a021608011122030f050c010807020105091e010e070b03150409020607262a06010f030312020d05100e390702060d0c12110409 60
    0x101000050030841d41e0b50100d414140c110040341100c2c0f55644804045090382c480d0f010040055409100240030142400c031110442040300159190041e140d495005c02000c07141e6040d1203680c0070440d101829644010005c1c2e2106031840200003078186180010703120707031410301801250b22480544005031802035100444030364040c02103407a04c81e41e40c61100416042140c041c041d07050034800325040f0381414000d40c2c601c1540188054a03140f45903980500b50000c01025256880104690200340b6400400038823840c44150080c0c4040c03142121402c60869004054040750f401c1000100600340b803254085090f66810b0402102c0c0000c1244a43c000740203400500a4040c104000c0c060030700d07003400c3ca103004d036080040005143c1d5171303142500a50076110703038240c0b41d90104801c0000b9052041a94600148000c02c50f1a00c1d000c0c081d00011560780000000c8412541e4480315400003a4006d10746980055080c0e40520a0b1400700302e440c101d038016440b17004049500d4030307291a4080003007c500900c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 741043444 1250 741042194 741042209
    0x10c140c070f09050613090b010e130b090105240a09050c1201032d0b01030210091805160801060f0f030b0d05010f2414010c12030c0810180b0a 63
    0x1400c0d6070340d401c1d4401340109441c0346014807444024061003040d0f6015900400c2d0300b10362101c8050b442c024180403485401001c401c5004410700710440002d44a000041c0502e80c0000045890708000100030203540fa45888080600c0c0141080c00700c5841c3c5034030303410854007800d10000f015628400a0942e17445000f03940c0d141030003d040044100274040c010201c1c2c1d4032480142c041c44034542552503c0610b4200005800ca1016400410040c81d10244410322031225107800d944159582c04101042103845007501740503500d41080160060f0f1480102594034910f242000041d4904400135207030145046000d410000e000d504aa08030313000b50018014100003400440114082d410514020412550364030010b90804050169a0f100c0b03a071501850700140d4815102140780940070700d80d200202030b106050082e54280d03a004160650300b001e02036112900d011034200c144810040180e0801818004440c0b8859018800601022003418842c45440070005484054100150b102c2200740e01444 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 741044694 1250 741043444 741043469
    0x20408071206060f0e0414070503150f0c160b04021f030f06080c0f22180c0e070e0d0f02060307030c14040509070c06090c0f030b09010c140c07 63
    0x60380c07110701c9030110425070080720308000031901d69410381a100110701c1070203600144280818080380103251200f2850315448215226141e035040030904191202c0b100040c010103013410404c400103c01c41c6145d0040035010110719024820410100040c1d500c40c0180040000b51300103021512003642c05014034005c0962001031107176100004028240000d554044103040c4000091646030024401c01e140e40004c1c0840040b600c0746003402440a00c80f0240a161540c1c82900c3c00c1242e2548900741080c6d051a0742d132240c1d9041e9041c20303e4400000c0d07002c00c96907045103081140060703012130070b02c4103110200c030f460b115102e00d03040c043d0400c1040400030307501010000070f200301d00740c1580c44942d42025503252034000341540444c18203507005a10507070350480c03440c0000420052151214800070780c0300318000501c0140c0d94540c079500c1680da03080546ca64590306024001c0c440400b5980d540070501800a209027081458020034260681002c00a0711300040381981d000034040c0017120290260300200c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 741045944 1250 741044694 741044699
    0x803040b071421190201050118020d18032729070209191103190e031e09041409070302040b1315060912031d0a120b0118061802070602040807 62
    0x80246a002c105460b10078484c0310224002c02e4010f015040c100c0c3d0b0310400901d07a10900000781c1c0d0180d405903040c0e226842d0340d03070040d08803e82c0706c3c0b2610140c24066a910300100c809100d240445001c00006d044000200600c100110241001045183c803824811031001c6214410110918040c1d07620095005141404000d000e9483d0302150090040051045c00404584461500a444151000f410600700800013606044003500116440e2003101c00b11b910340705181158003e003148500203500c00706800500c02d20149414012100050507a6a40d41a44e0400015455407000b051000901a540f03c40b00710013150b1f01c80b5007102c4000009a82803080d18540d58041d120f8900303a0207032801182d007004012544004035610781d0340d1164117898814440700d5500201d2441091000099440030380d0741c1011810306031a22070b0540c26480303a1103d24035075040044d81c1240c00c4242a40115041c54000200540e6042d5808003c0b03603200c1c1540181c0d80d4195084c148064440e5420081440c45050f100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 741047194 1250 741045944 741046003
    0x9020703081522021305030a2105030114090907050a0b0301030506010b1201210c06030507270501051303081617161506080d090f0803040b0714 63
    0x5261203420211007101e0080d500700100710041040c51201d2000040183d003034041030007030380d00500e50341281a1340c20810681c3d03a00060f162482c005421103600d54015003030309100d0049864a001d8490340d081940c00c641c10090801b40c1e00712902c0e02c0c0707407081803500081001000d040c0540409000041c000308406501d4015078000c85d8000e120840b990305c02d10000007000700c042c4082c0c40c002021904043d0a0341d181c00d03c04001c0d021600101440d00c1d003c503c01e41c3c00502290800001081c481e1408a45807070305150141404030703c050b8012000310310000041c411100030b01540203a81007400e00a44944203000c1400700402a9000100342d03043c0028072201c01c0c414910380c81c215174400c2c0914a812610217240003246c2c092282d0b5541900313109800c2d400040d10707148815203213494a1100141ca165a100301d20f1405d05000c0c1c444d008a0146101481f410490f480310b0f8028011110080d89010700d81f0324401104c0c4a0176801034039011074050460382c54a4248182c087c8400c001c500c0c42001541c0742c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 741048444 1250 741047194 741047207
    0xb01120914100212150f15090d030903060b0f061e09181b0c0c010813020307060e0f0409110103021c020a0201060f1d0c03060d1b09110f0f1309020703 66
    0x448000c100344c6500064982821055001400c0d40c06000d81411070b0b1614184a145588240f1008525509000d41c400e03940f21004440c4001c2d010399152035040e4078508084044032a510441d43c01102884843c8195448101c115075803441d506004075074808101c2586042030041407442caa216055600d10281c138021030741014050380504110300f11168130000b401030700d8820500c21101a070400d6286009660088446079841030392000b882d030035405540d0001e402c0c217600b5003210002c99440600b07021703c1d0803e11480748003c0b006460401c404601526890f034588000102c090425800060350b000500070310a0300030702101c8802c8290740f01d100d03a1740b0183c041c08203402400341480340c2400000300142a100f00303038808200007485a545440c0c6c1d01462409070300003000c050300110140ca0a0b00004c5000000b4074a200c503d40d842c041c0340f4200f81d5414281c80d0352120f221690101403200c520300006480489a42c2c031803a5640b50741d031b9a61003100c098444200d03800601507610104951051640001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 741049694 1250 741048444 741048457
    0xf15130503060c0c010c08040f0305070c050405040b040507080a0c03020d020a1a030a0f020901080604110f0403210e03250f09050a0b031606030b030309150703020f010b011209141002 80
    0x240804c40d60480102c03038042e012100270380043c01401403800820f000300000c180f00d9000c2e01d008003040d500c3d04041000e840f000c0d07404841980103001000103121040c00080d0141503844042c0c00046000e41b0b810790244c080340030280c0703e801051074610866954070322001c001c00205203103480102081d491840c460f002100ca84041c24148a00340c0024081c5108039114004d05844020b10ba032298400d010003041c5c00c442c00014010104001d07881d0404034006040214480c504120240c9410612008850340341c00510050243e004001b41c0540e034040780080c0203004500d21914a140a50340304281048280d100604400401c0d0700415001070a801c02840b030340f5404811310010032141c2c1819510010100c040300c2140002106110191094020512240340102141d0500400c6800110008150440500841c400051344410103806020740322031020504020480c000300d45002a08c00030800c4242c1ca486951829440100f14134080c5404880b10301c2400c43e5030a030401c0040c1d50080d031008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 741050944 1250 741049694 741049717
    0x207050d0c0b150121060f0807060e120304060c11091006020f06090705010c02040b09280207030804080c010e0a030e01180803040b0c0a06090803010f050f15130503060c 74
    0x4000106107004058100c1050881a9180d8a402521880004e8900d600c0174410300e40e192542000070308099900036080117000c00e240070301852483e00e00098240b12142c20312034003c0d0100120340a806e5030200c156412a44281800c10362070209290000f03007a1044960241e2044c1c0c95003d21000c103220452610664055400b01c07800d05914018a81d990b0008949a2406e640030444c00d01403035114250f01a00701d44054008525131180700c00040001070b0841d81e0303809452030034100d0a104003c0b1107003c15000030020f03003117180070800d8800030000f00c0c0041001d04144000281e0550b980400d41c0030300460000c0314240c0702c0f8504a4500105429183c005240c000303240c0c40240f1103041d0104074464115001c290045141603d4030590300410340010b44030700403900032440090041001030080030b4119115041c800d55a6050404411034030034980c0246014813810380742d0321403079102c1881d20112000010740c043c0c0c0f501030300c1c2c0c903034000030300c003908010f0b0140200814442d212500c0c0e0043c01ca001c064 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 741052194 1250 741050944 741050963
    0xf12060b010513051e060c030d2405040c0c0f05010c021209241c0608240f0907050a060804060b01030509070b07051e0c031209150306040207050d0c 65
    0x2440300441d81c500901810341d0f000c0010000411861400031510f206100700200c2c229090180c42c0e00140340780d04a000c004031690400196402c2003003040c42031b00030407156048408050b0485804030000000b260080701c1c01507540b900c1030541c05d4002c850841010350300101c1c80c0d80403001481c015029111484a01d409071041c1481e403003100d202c1000751440c0a00c041c114542440f9500c0e80c0ba8850b000005088000f0300003002500502c0381ca00c3d0241ca000d0f41c1e08040810040c3c60820454904002010300080e0b052030500c00d0380610408401464000d94080020060747d21038880d0700e402e05007554000e0384c0c01041d500c0000b5000b900000060701c82c0c3d0180004012040c0d20b02c00650588204840c0325220340c010b600d0901081d0943c40289c04068047c1d001c80700010700c40c900c0b00c0ca0030350401101040c554008a080c803428502000444c41a040c541421824a044c105c0852200a003020018107410000720016140e911164161030321150400100c0b205440490006001082c85400a4030061390 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 741053444 1250 741052194 741052211
    0x120506030c06460309080c010204030302060702060a140118110c100f050106020c1c050a30020616020a0506041a0a0606120c030e060c2a1b06040f1206 66
    0x14a620240d594003c2c142c11250b1110240703044008044e2490102d803102d005000d0850343c1602480904051031180d0020149420703c0d95019182031401028116068204aa06182201e5841c42281180d64405c001c24001c1502041c07200900702c801030000f0714550100340440c80c401c0010311045a8004004d08200a814101a01003a200240034042c0542d1110301b4114460138082ca404003003420a4160b503034010401d6840314240b524012050b0b414420f4a070781e00200e40b01e002400c01c40d06c40344c2c01c5150043d50f0101340180d1542c000601d8169400410104803050354001d20051071259400800d4038502d142c54a08821001990044110361901ca840011422013031842000150742e210703204c2000000782101c841014114041101c03081580711090b1030b140c1342003001520f0281800d01c0440ba102c50721410052200e0130b4242101d054161700c50400c28070407130086401c2800103400101d01001228000100300588200c1d40032000c03031003915100013021290411918045481110140140031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 741054694 1250 741053444 741053527
    0x230c120c1504061d0d0b0c0c0106060f110607091503091401150b04060512131202060f0604060b0d020d1503030201020c060c0a0e0f0a09020d0b180403120506030c06 72
    0xc04e010340b402d4220703110201c8403011400300990540d0107006804a14580b6840046090079140d982d40560049202e07401001c00d800c0c0c11a018220044450005116600d00340800a10030103a0f84621075501030b0a24601840300c3c882c1c1c204011a9822555079402c88000119440c002c2c0030800d049203c180f00301c0c0e0042041c1e01c0c0d10702100d0803900c450b5202c80c01d01c00c02c0744c401c00c00360b030700070305007208180307401d9500f0300050759242d6459540103098003c1c0c00c492a14002068440b54000d092620032482d0000c00d01c01c8000c0c103025150301d00d942140058a490741280d00380c0041014030070040e000c041e07992000042541c150020103680780d119041d2005500ca13650706150501403591410045003045180c46c0d03c90425000380c42e40d20710001d040d184180d6a41c0d071000100c0c0d10003144178031078584501c0a800981403e000039140380d10302c0c400c0716071207203895100102a8140080d44005850b25000841c6142d41d040204020301e10005280315a200101c0e20550001c0010440c52184000141a0407180710f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 741055944 1250 741054694 741054737
    0x10091a060306012d17160506040b0706090606030218040c140904020409050109020901060c2d0b04030c02090a0f0c1d19030c090504230c120c150406 65
    0x30b50380c4c4214103481c107034500281c1c0c6000f0802807a108402c01c0007140090b01c0d810702407202c070b584034040c8040c000c01003664650b80c0c881021504214001c87d81040100b10b04008501201c4900d6007040000461001601e018000350000354406544100c400c43d1042e01c4c079111240344c070701035441a9916415141d4425910f0100a40a020385501c000e81000080c05410030303402c00031a10348110000201d96120340e0002d1140b200c00e81060000803025540081000031100c1c1c95003100410740c0151190040007006a4068514520000c04400c13503c00070070b0406d0700407004081c00503402000840c051404840c030f4402000c55003140390301503040c441c003000080e010703503041380c3d8040c61400c00901260b18141409611281008050701800310584000085607442d211a001780100010128542c1018240080d244281c0348000000340b0102c01600701a200002c1d88240d0243c09440b842401c02c04001414288622480110381185441040c6c02c26600364500800907201141c5922604600d030300768404a5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 741057194 1250 741055944 741055949
    0xd0c170709030b0403110f1027260403050105060a140102060c0c15161413030605040c030812041704060206010e1302060418060b09090f040510091a06030601 69
    0x108822400c00d0000c03660f40052240c0c814002e0404242c103907406005286002e144502180312a001007405101310081401030640e0070b000a0312500c01d48003c2280300c0034588030200020301c0807401c5c811700b454030b020a03290041d040341440461903e07650b0301e09015002e0305c402c03545188a011f182901042020380b64030000c06144040e40104856610b092058405a1000d02041c1d4148900150300780c0c20850001c95038800c10403c002d0401c000e010b0800a4802c00da07001e600801c1043c280700024100a0641106080300d030803071804075054481d8144034a40105a0300040c0801c00001a076002014031000000d0245110b030703e4094500c2e40b1982d00b40c1075401140035034001a00142d00400020500c000b010b44c101240101c42c018a01c2a82d001414a038800d50100310669080081021103030494825840207000085005141840500003d901c1410041080e900c0e144010042070501208100c40000d00302d0304401001006101d04101c0701c862443c4841024454105000548600300810344504 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 741058444 1250 741057194 741057197
    0xc0e04061808070c3002030f0109080d05071e0e131404020a08010204060e19120302100e1603021225210507170a17031807050303030115050f0d0c1707 66
    0x2617003112a8154480340700300c40b0309907403610600c0b2026141c0345083c031030a160103105100d01681d0300c4190fa450001e9a43c01003981091010329190801c00040d00707901d0b800c0a250a14200c0401829000022514021b004c0510440b500e4a124210002450b040850166008886a10856aa4084c0d56080c0d1140c0e01079000019071250512806041116a58240e6103d0f0114280c44986031401e00030340d8001c8110a90050f840082c000000c0005403050f01c4020b8801d0021740080b0000341e4201901c02c10604c0000e0041c101a101103e100310140b00c02c200c40880384c3c0c00030400d10b032400b01c0b02e144032445009008071014800d6241c4104e120350281c0d411080d6000002c1c0c1005450600300c400289030001d155511400745078000000a5419488a280b65401c0d041403510b074100180c0141241e40e170078101a465602c202814840750b0340c0042501c0c11104980141c551080c07000f10212521b025a0001c600c0c0401e010481618141c8250450300d0603404a03507400c00d802d0311122411180c0d89080d1408030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 741059694 1250 741058444 741058499
    0xf07021903050c0616051221010501140c03090901080138090601020a060509060a11091e01120f0608151603050a14041a01120c0e04061808070c 63
    0x3e5540c144440a407140c40e185055420f12800a516641d04051120384600070f107d0000131a08108500c0e84030007420344c4d0002c24840915814540064035080c83e0016044021b440864115000300d01001111040d0380013414a03c42940e5900c0214040e010076903460710001039110708044040e51003104102d2191912030007411903446901400840074018103054114060451450701080d8240035040c080c40d17030000108034510340032045400304c6100858400c40c1840410288226540d8a0040740c107001c811120940c04800b0700c40140c1d25501580b289840d035900f400740902d03005a0b90740c000740407902e8080503281d0154550b1500705009404a43c009507640d00100719000c00389c8a0f80c40180d00065046000800798504040d46480c14400c0342c00b00d8000001d10307c0142d03051458140903004000e020211007240a03903a8940e00d1100d014050003000c1c0c4071110029040c0041d42e0071150046800e040d0b5031850a0150900c540306600907001a124441c5200380002d00c2d41c1c0c41100500c02441e200c003243e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 741060944 1250 741059694 741059713
    0x3081501021b0103180b190608370516060806010909050601031d1c020c100c021305070f0e010207061b020f0301020301060f0e0603040c0512120f0702190305 69
    0x20b080c80506a4100d0415541d100541981005d28503604501c3c2e0054000d4681c52070601a030591120440c000140030340d0400d4400c20070300c8000a6007502c003108240b40200c8040d0b09420f21f100305852005051707040c6031013982c01c40c00c1c014003007004080d50755030420b6107036510340f22002600c0014085d90b4440c00a0090342d0100841d4400c1d81c03010390070100500d40498040715480300d0080170300f02481078a19a80248072005001407400518805004260000d0599040b0300300c001140d442144000900b40040100d80b08219540c0882000b903203081100700300300c54201044010b1650400e4950b00c0041115070301c111896600000b00300701201c10540d00c20a0400c12030907044501c0d0327443c1c2006c07a04440c0c601c00a11440d9001e00265019160f19501c1001244c0340480c01451003000d2000f45000300c20070000d00c030208001c03500080a07900c0c280c4805510081d1050694540380e60b4109880003230340e010070740c4000c0d020307450002d1080c1402215450500c04240c400070a8245481c80300520603802107504c3d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 741062194 1250 741060944 741060973
    0xe130206071a0411010f02010603021c060b03030c010b12070f060e120706031a04020906030f070507120306032906100203040906331b0602070f0308040308150102 71
    0x10044a032040c588040c070001030361010702a10030b05a4040310215000400281c0650b801040d0701d9251b0020701c005d104281c619004205d2540e440e1501260113948403000390103000039500030001041001c1d048030713510104000300301e00a0071014030301c500c100006586000070440009407403060305d0030500010f8041c0d1070100706031004001d4400064100101c446103100700d80c400c2c843c0701c00401141d1004900140d0034504100024408202c0601c140c0c414020744103581c071088103407079000940400d18506500c0d00d072801e0b01c40f8090508001c003c110b4118840307070600c0e8182c02210171a84180c40000440052800e5002c0c00b6601d04070340c4407103107280d000064003840c0031824509483c0560050b245440d8403460300a069407002e80140c050605c3c6001281e00307902408918a0102207090030203452306400c5074004140030040d47d1450000b100c8080d11009000955044a89840d80f043d200b080340c01980c90b007d005118100d1f000d40c0460400e40c0014142200003501d5800070310168080c1c40c1030800703400c0c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 741063444 1250 741062194 741062197
    0x902091f0e01051810020709060801022b06030c0308180d050309041d1e0609030a17100b0703020d0f080127060305030a110115060f0509030a02280e130206 68
    0x8070442804e003041500c4c40b0f40c5951200300040400756025044070341c102100ba0060390215030101100368810004d48007100722031021901e103442c1e00041c080c482c15082045001810300c54001030205041450000104101200100112024014248210b100b0382d410000c440000602c042c00300d400030004441c1900c1c0540c0b208144482071030320550000c143c000d00380c1c9400316124806613540300f40f650a802480c3e007001916844800c0000840c9402e00a01c00102500c07070150450b4a08181d29001c120882407042802d005407610350001e03901d070501390500a5849285002c0d100214075240d000801052041050b181602c00c40044088440300b09266100d02d82c030030714000211581c0d1307000040001607040c402002040c0303890356980000000c0c3d040b10b41c01c4920b0129a10024040d180003003014a4109246d040d00c515242401034407203140c00d000c01c0c00e02d440768000a500c005005166a20840481c1c4103485652100065040441d1580207941c8140b4007501c04a07144607924110310300603d840340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 741064694 1250 741063444 741063457
    0x302120606030a1e090b0c1614071d0103021e1011010e0f01140a0c090e070e030d0f20060f0702190b0613050f0c0f04050306010902091f0e0105 63
    0x2800245889004012031341d0080c1294a0903000340c0c4803600c500134810222001908004280c589614000000f00505602e41402800818078102408044400384050001000030460a00115882003440c204c1181c1ca001c00d0004a2180d101c0c070203211600b040030f1611800c1c0c840d001e844d407040700f071400c40f050352111074400b42005599241d005011000c0340901c1102c00205030340d4004524000d100548001c0d400005042400041ca8121148505948040303840c0480e4100d41e024075003600d41c044203c130700400600030350780c2505c02c00c1c101c0c00c08594410404024010250344180440840c0400c444d07104505102004050344400f01080700d000c07150b0100713500220715004540f1501c584803070400e00030f001c00030240c41d032044030000c210a85c18410340d0414203000110081080789050303d481c0c00f002c0d0014050a24a0001141010408222400303c40c00b800006088075580c3da0764624081c065030210300000e00448540c49403042d040d00b00900c00100342055201d10306101e55031001114240c2094 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 741065944 1250 741064694 741064711
    0xc18021615110705010e0f0a030807030903090302061803010f06051f090e0705030109050606030702060415020f0c070906050d0b070804060207120503040b010f150309150615020607030212060603 85
    0x322a446150702142d0010002e641c854800816400a200701c11402c1c01204058168130b40c00c96014900000e611624a940c0050303181400640da01c101d0030103c5141c200782d0802034106000080340c0307002c01e0700e88d41c8020132410218000e011034100400c07010203440080c403c40303401817080d00c0f0409140348583c5450941400e0761616051041e91400c503030b081c2c9141601c10780e011502c00001031003080d08138040c0580c0158261660f83c99821310420095072408024009014442c41c88283c01001030250110b540f20000c00340d00b161116034041c40c041e1111000e215007010b4510b440070008940c01c00201c100180e80d00030326414001d0b42d90340019181c1e03010040c030407134801d58204035040000c0c15400100c0c1403002a6940d07561a46001d1800000b01c0c0c03811380010003042c010a404100c00d0b5185000103044503440d02c0d02040302045807800b1078040b0b41e240000940f960a24101040e0f41403c00000e40c0386c0749643c0c0c00c50b031458440c510203401324810700c1c54012a01654900044060411000468001c0c020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 741067194 1250 741065944 741065951
    0xb03030a021525110d030b0a0501081e07090e0a0917070302030d05040f062315010e0319030906050f0d1815020d1d0c01180f030c18021615 61
    0x22640351444000f0701240c140c0c00710f103048202c0f401d1400304104c200c40360a400d050410500c0e40c4800003640d0741183d841150304005d00c0f68000b03060b17003d60814000c402c0340d2200440020b81000180a894500790b405011700d81c02c01800080d80001c03c0b40640e1154076008001d1005200c0740c00d08070307034807030303100b8441a01580702c00c0003189a2125107214003845140902e48900c01a441c40c40c0c1041510050002e42031100101600041c010040000c1a03401040000c0c0c00b4121241310700c0140c440c510b070f020041740e25000300b0a18845600e0b400c480060103c0c4240d0750300344035540f5403905071401e010740040020310940070300c44000c08958541c004c003440983c105a4070421a0b0b07a58844528565100281c242141c02080c62040d0301d245000b60448115610ba40460380b47c40d603140981d0751540c0c00406410012a4500b241481c4d5403c080d0601030301c10b506041d09210348904103100040038920941d85c000544c0200740201407100e1003900c648225190800011380600d80341c02409410011041445558 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 741068444 1250 741067194 741067231
    0x41b110a0c0e0f060117071b060e0a120c11010f0c1e021905030a0602070c080604060b0a050103090206090d080405120f0d0305010b1209100c120b03030a0215 69
    0x80c1c00e00c0d02030007810411088002450941c03c00107516102402c040d041c040b080030700244514000704601d81c030042620304603c049010b06020b41191480380b1000d05030a16100d040003440b000800d10000c180c1c003c0c001c2c05030440040204403240720145801420f00311000c03104461541c81400190100110340c0f0746003880505da902e80701010440d00c2031052848640140e0302e000c6040091035401400061050b810050303160030080b9486a00080b8001c1249600040c51000c0103500c2c980d0700054100d0004a070340529291409200410b58408050310a2803150800120381d80b00780200104035902800e0300d41000010011701c0b43c03505082d40c04480040b414003000c50f840e01e5044c901ca4a42c00c81030000c05258140d00c0b070040c100303846c1c001c94008150500e0018403019909608460312400140c40702d049075500d42000c40c0c1000c110450100185041042c4003e8076503028848001d03030b81120104200007800d41c01090340d2441048218170158004501c034440c40c00420340e18940c03028a40c09500c01500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 741069694 1250 741068444 741068453
    0x130602090f21120406121107050a03020a030e100e040c09054209060a0302040902030c091c03020d030b0f031507140711040b03011e020c010b041b110a 66
    0x6003611856401505a420b100e410b80c8010050f4090460150350900d2410741088001054004c112400107101911520900080c1c0e010307100b1200c002d40c2200946039460542d01e8000c0d00c58080c05429070004521884030407652170000b2000c8200c0382c0b55102c20350141c0c2d001052202805d0040160024000720980015480d00c41c146886408000c3c000080c0c6003800070001c0318860740355111070801400f03d410021303d0800c2504115601110f04642140d220380507458218042d1003640c210004c2c2038004400d101c03900503058040d141400d405c5031000142c01c1d17900384000c00d00c001002d0241c01a805090320f000402c1c002e5000070f104000161040d651010382c1c0b00401c1c940f94072003241ca090300080804114083e60b00c080c00b026111000040c55262503619110350b00c4606400300a42e20590b03413490340400b01c1d5030075805080071071150300059182c2140c0541c9000290000a815560355003000c003800140d2a161140303032004e03451403108824640800c441181c0d0820341c0c020001c0280309150407000403d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 741070944 1250 741069694 741069709
    0x803160b0a0b0d051c020309090103020906271b0316050d0f060e0403020f0607080a020d0b030f07050f0d0b1812030c0301093206030309180f0f130602090f 68
    0x440c0190005e0240c84c00b0700000151351544000080115042403205400036500d50382450f04503034045a0349460390700c5d804001000000d140000c258408414031048c20380c1d004528095200c0d812080d5415800032141e0a00e1720702d8842200c0b011070301501c0c0304aa61000c3e003d8805440d1001c0e002a00043d03c001c5245c0d220101d82c3c282d04203000c00c0c88218100003c1550404c40c404032903220300050071081c105100b016000c04009444450915004110308070244c104e0b500000b1520401002c03034001d0001c0c00c040a0711418537000345405071410b00180d4041e41054140795007a16442569001143e42c1c0354401111800c1d0300801420038000d0840444407401e0b184041c500540341c024a842d030303a514043d00d40003110b1291101c1442c0541201075a400741e22150403d504e521201c81c0d104070150b0391040085e0851050303004031540044820940000105e4035000c26100f2140d100c00c01081da11171403914402618100c0e2400e80e0300389154204d0001600a802800246002504c40d1941d00c1465002501d41c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 741072194 1250 741070944 741070969
    0x11041203050403060509010908030a0905100606080612010606020a02060d0204030f0305040806100b0315010c0b0709381c060b03040b16051b0304031a100803160b0a0b 73
    0x280c1c0200d0180140442d0b44100c90b000008031000f044203500540ea091224040241150a402c0d5120301c0c460a0241c14449008d070030446507800c00489845600103814030000341e0340113014030340c024520548024140314800031b807111380d001014690740c15420468160710008060882540070300000002407050100c40403058845e0300c45a40340e81c18010070340d15141000304035071603280c0102001c109814503d000c030b03904480c152842180740804080117981d002d007041d800800e05c440794401c000c6402d0380111580195002100705841c880c1c40c00d00c001d88100c2c68201d0b50407081e070103480d02203820b0108800428a01e90042020f0440e42c07900541ca0088030038aa10481a001d000010081045403803207086500000200c1c52040603070020340000d21602400e05ca1040e0000f0550f5441d0200104209840045900c020414070089580c00c180c203194100f65400d80c0120310710000416000030100130b844038140a540c906070601c041d92100c04c08803501401c0b072944c465480f160011680c8034001c00900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 741073444 1250 741072194 741072197
    0x30215070c0515040209010504020c0f0a05010e0f06061522090f1410090203100803030a0603020406050a08031801110a0516061b082505010b0319080a0311041203 71
    0x164501e181c01c0c500c0c200502c0700e1406221210600810006940366070aa5040d0341c021346005850340c0d554910340b0b00e0300b02e11841c1070801d0b01c58408000100281500030703040703079641c0b0003e039040751400c1000740342d403028141c55207a4041040c69508110481810161010040020701c0b000c4407680d40d091344114501c5508130340021900c0781c28500b9a11b03d04e000c0c40e244220380924409131481c0a006200856000707000c1c24440c140c0004c040f40714510700308121405405d010042e81e5490502d07504901c01800d003840120f0207181040800075051070143c420008a0b5458005549000c40080350140c609402080342e030705000c05001da40c803003c5c00c01c21001c101c00340300d6030040104c895261081034030b00e400c40d40490104800840c8008081c00680324184c40e1030790015401e03450300440d0362520500d045600001d400f5414460010341848415000352040c001306401f83c0e00350f0404682c410300181c03404c00000c1e00f034100800110304868400d9000300c403802c240121507400c2a4440ca01078010b080480420340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 741074694 1250 741073444 741073457
    0x803010602070609120f050f07060305090c0f0102060c03040c180507022109040225080310050612241509120a0b06010c060624080f060a1203021507 65
    0x20205804205402c040e00c00b9082c075405640c5008494803403900703207141c010007640c10100c0071400c0000c00c0005502d411195020f84158648850000340148803c4032403001d144102c43c1701065904000e025203c1555043c1d0183c005507585012801299102520071111901c1518000032003543e4500980c4800a184802241c02e04000c44028a40000ba0024201140c004000c50707040038150002c580b07480c4001e44003d03031038420700b404841810503030080c10200d40400c0307428402000380802c0114818401c905a0780f640c10b840300706120b40c43c00745c00046003414604e400859425030440c220101e54040c1501e4400c42c20641c2c1000c940000d4103200d4407010800c001c07511071400c1c545a101c000e010711000d03005158241d22600c1c0c0b40b00b444009407006040c0410311810000f800043d0b001076028110034a0301805400b5800d01c408002c840c0909420009a0b0a80114002c07104450302e040c00760000406080c080ca08158940c0308a0304000021020f512603009840301c1d0780349041c0b10394442c0e08540c6885 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 741075944 1250 741074694 741074699
    0x210109150e0d1e020c031c0f17010b09030a120905101e0516120203090108011e060e120609060f060324060d06020c01050a150b0301092304080301 64
    0x40580d0151810740500c1d412400e00e020000354010425802d2048001540c103403164490003c0c0c1c240150000c4480e0580140d11f4194803444200c0c081b076804440b607075220042d00c01502c0c0110b84000300d0b100d4803448141007000410101e07003104082c0802e4074004080d184295044c0d03582065150310b0031074050204000960812941c50302964048a03004142002610b510240503d00d015a42d0740411009220001c1000002004070960844070294000d401c240960000c0001a590380c1002c02c543c0c1c000703607840001081d01081307550001c1c0045d031100a1440d41340e040000c180d40c44100000142c1d0001c0304d440107081c1d0400100100d900800e1510301500746410440740d074545901c0001d041a0107a031001c00b048c03040c40030b503a90b115188150581018003036154000003e480c0804040f003c0d01a81c004170301080c00303074010761040340078070203080003040f10501c9034041600200e0144500c600d1410280010010406190400750803042644282d05d01c0d22016268a4000030381a0b0381a10342c002c010005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 741077194 1250 741075944 741075983
    0x14010905010603020a2a080d05040b07051801080c0f0403140106090e03030a240e0603010605012a080c0304260105061c210203090301110703020a02210109 68
    0xa40740540024a425071801506039400b501c00f000c603480b40120841018825035403100ca0120500301c050b407100c10035580303a41d04c9207854040e000507103042c4d27040000c180100309124060030880707980c0d070112000c49030700b0a5403c0c010368003010014400300414108000c1d084074120741100900155100300a0601e03e078041c0074010b42182e985400680c1300c58980009150103000001c19250b00036240300c0c1c00b00f4891075080d026098202c511006050b0840d540102096020142203201d1007203c094008105041d075810044821016140441c08505001710050210b0401d0800410f002801092410305e0070707a0046440d0700c1c59006034051004400089080212204030f45145606400008020700a60606500040c00c0412100149103d49441821642044003080a440c51449010075041c604031a00e0310203526079014501440c07081d4680311000005d20034000542c0c2005030503500500c245801c0d942801110b00c00b0851080c0c0c40b03d08501c280b2100b4009004002c4501c2c0301e50f00d81c0f00060b002042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 741078444 1250 741077194 741077201
    0x5090408220b07051203010e0c16020303070308010e1e15041b08190225020118080c031204030b22060c0c0314030403020a110d050a05150c162301140109 67
    0x110740b444a17410001046115007a40c511600102ca8140b079550310105c10304031502c14640c0410094141c00701041130780500d900f082000e4101c601d03208490080e981c0c2c221041c0c14000201e1522020040c1c0300012a88100004e42c065400400c00b40000074000340300407442100f4800300c0c042000144d10041007001410154040780081c8010240950030806030f1039080c0301d40255501ca514451086086140541e881000d456a1842017072081442280d10340900b103854481180301382c1e00a200d010001507056000f0b1044408a903084070815103284c90310780e211800000c28140c10394040d841d20105c08003180c1c15106807036030810b032a140e000c1c0084441c5805443ca50200e4207481c04d183c0280108000b00f074000c43c090100c00d510001400912420400050241805802c007602070b10410a03000c0400900165044008186940600c1b581d40c2d042d444100c68400c80824404800002c6408000a009003401102054900b09140c150580040c2396608640e800020f50814160740e40040204011910 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 741079694 1250 741078444 741078463
    0x100c02011113060e09100603020715050f010609120f061503080414010806040614010f050d09060b090604053108030a0c0e040b06070b060a15200705090408220b0705 72
    0xd5520105180207006c038503400350700344240b00c1030580009641c0d00f004468005080c1c0c0301724020f420030039420522030f00d4500020900030840811013030355020411200788020fa40065a00c9003411300c201c9640e5a400021f0030540034068900045503902100040c070301d80c042c1024101c40c4001d0341e0320548441c001040c03820042d290500030b6142c21014840c000c41c8070f2564504500c2820f14940010305d09008544e03078402c40549400f15480c2c13031496810011250040000d07090119408845900d03543d00300402c5a000340d40515441407142d0929001070b240007000071405d200f103c0c613000c80644644582202d6802103a80e240c100d5a200e000200480e040103c15610050a441c2004104941c0b808605180304400c4090542c5490100149003503850704040c1d800381c01885280c1419030100d04000d8806410040071242e9256a2284c00c040040c0028140e012a000148881101d444079119800b0036400808c1042080240c441c21509491020048000806185010590f103107024108941484c403040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 741080944 1250 741079694 741079699
    0x2406060e130c090314011505060c150705070203010f05060102300904090f0812091203010608270c0109080102031302010f020a170306090711100c02011113060e 70
    0x611402800d034484181d5210190315a010000b19003040900c150f400c4141540000c060503c802d00d01354224106410031400440e1602d0f070a208940c98030304105c40d40c09441d00c551140d0780b204920000614a01d40c00c1038000c80d140c1003607031401c1e215401003800d4645c0b0041248051340c48e0414805079503410000f202910500125040709548242c1c40907001180009094441c0302c0003103031289496582d030380800ca800da440410500404030918000010b0307040384c0c1d00744d00c40141d030800040c40c2d2640810b0301c04030001e0b902c0710a0301d1a800e0032020340d80d0403005040c03000412344606070448610076401784041c141102400510031040d200e000100004001d0300404100d0340103106021040402c1d6000e000300c1c9509091402c004107000724100c1c81e10344c021801a004d41c920030400059410f03440001c5000348402d07103203582c030b40c0c0c0d03186010348261030702d40c045d4082c0703510664404147c40410b521441102c000b51001041010101d4040ba105801050905004111545007003003496003010580c0c190b250306 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 741082194 1250 741080944 741080957
    0x503251a04062a0201030b0112061e0b070506010b070c1e09050901060e06091b030711010c09061706131409071401020601060f050f0a050702030705041116020d240606 73
    0x4074070b244040d4940f10755009041c5a15010b03840160380c011110081d00d0404c01d03004002d481e585010001102007480120200d42c1c0440304007003501041c840840c0c0c611500407004086603443c0284030400c55012007415108001d40601c045028590030b140e215490031030315889100b26041080c20422218064610301e000da246c0703c000c1040141c1c52540e2030307100c0011958000d140e5a000f48140c41d101d1500c0f4000740a031000020400a240c0101042c940e01c1d15240003041000717884001561980002c1c064038010031380f40d0520b440e400b4008a282540101c1c0901581c40c41c028040c05202a56240114010740502d00d408014080d4010001d000c02820854007040140035600000307511010103015890402507045446001207020324110f038050155582026500c1c581a04000d10940103900304900c44c2c050200006076500d0540261408000310b06941d91a001c43c0c01090988009079580490304407620000c8070700440c002c0781d4000140d5880c813074000c52000c0854010001c985440c0c0048051008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 741083444 1250 741082194 741082247
    0x31505160815040915060e0106270512010f0f0b121b1009031a0108012d090212010603031106070507050c040f15061806090503251a0406 60
    0x9441d5000d001c0d41c4001e81e0700040d8810303141000500174011522548000d030030319000189106c070406c0c101d03049078101d0380c034026a10201d0806110a00e65801e0b06061010905418401031625124601e4140c04001c0006440011000c9600580301c1144004820a5485c849981603040850426907a48100006000d03a02c0c00d2042c20701190071010b115502840384201c1c49408240510280340265400c10704185c424680d0342d2048000301401d01541826500f001b19402d035003007809580e43e40e80900d9556160f01e01443d001032400030a16203d0580c4c0c00707002c40e500001402000c0c45158099030103551a420b048039182d5403546408806000c450400c0301c2005802c020610114690114550845010604229110b4101d01a200900f24942140383c08540040c02e42c0d0040b880a0125215800c0304009940d503400507039034490030b03120319505900206115160004603081040040900c88000c0740d83d03544556601d052414000c103540d028040009c0c003800919000311481ca0710940304861075401070f8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 741084694 1250 741083444 741083461
    0x2010b060d090c090612060b0607110637020708060702060621031809101202040903050c070303020d12062111030f0105041a06060a0f0201060315051608 67
    0x4544680150381c142d44000500070440000c41ca00700130000c210090205039114000b011104201400c1218003510b070100107402c3c1d0601c03105850520f43c104444c441c10202c6407043c810b15901a22541000d00ca00780e46c104000f1184020759840e4020700c0681d07e06204207040c0c064500314058200035041d81c405c0042081695000541c1c5a0085003911030300302240c0921910841551a0036001340c0310300001c1032544100561203d803068895040f10110302e2a1503014200e031040b0100d004c0c090701a0310304a0524058202a04101d0382d107842450810f1403c05080c24280c18208140c0040700181c000c044092051680326801e0716030304407410b8040041c0f034685981d8248041d1aa04901d120700222710030078060240001080304080c0000e001d80d5095440807041314000e203421034084170303601c40c0d980c0c1b40401100f003903142c10b10401300070700702c1c0b446d00107441d4041e50002c078105d040070210b40d00c0f1040031001840b0406424000c0603e003070b0100e41d034103040041200c0c8000d03050440040010910030000d000c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 741085944 1250 741084694 741084697
    0x1905030418021c0209010e0a05280306050403120f021c2409020c060a021e0d0b03070b03090f01150b090d06020304050304180c050307140c0714040c02010b06 69
    0x110801812148014078082103100a0700581d4410071031a25101801c4511500c16001030400c614240d8820310241140c108009082c2460300400d40c01924a0060401c1c0d03113030b003001454002844154100c043d035502d6481c2c2041e00c0b01102d007140040c610f000c1408444206001e800d001c1500301c0406d50801c1c0ea491b140c0700d1184103007a103022039903850b2428403030035207508016410200f24611038141c0031a217036005e003006076018408200c2588610b10015508251510907a11012445140841c0e005501014206540c206a100c4281146c0e5580b100d602c03607804000c07440c001c010b01900b07152a854117134012030900741c0d82c800c001c0180e4107005252a030310301d001c03480f003091341c208403074050b2584040b801041104182003401040307140700000744801d010303000010b881141c21032090600c2c10a00034059006a80c3d80c072068401041041c40820b4856010f01281c46100c03e00f250b0442c106941c020b0f015140107a80d911041d01d03280150008806410507011301d0369014490300007400450941800700d103ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 741087194 1250 741085944 741085949
    0x6030406062619080706060608011508060f060f04091406010e030615090718121b230114070308040302010b03070f0308180d03080105040f0501150806060d14040519050304 75
    0x251200c1604100703c02d070019200c5c8950401010490962a001d01402110742030141011400d080d083c6040d40c548103581e91882444050007036000500c2d06c005200d010707004145c0070248510140130205900d1064401c5281c20006404070380d2035820440000352200400944142c043d401c03003800c00000049050000d1841d040550700e03003805607140c0000f1200b005039000b000d224410213960000b000034103000807003404ea004a40700a0044e61085038142c0c52040d40c440c4130600c0d440284034510090160b00e0f41c09040406040082165500e805001e002d51300c111022408a46040140414142d0910446076010700a030018a034407418604030000c202440d01c0018000310b0005035254008000c20b070004914940075000c54064103151402601c14182400740703e0240d86080035001540406016590407910103e801c00e020401d884022545400018100c07038001d0020000d200342e4440328403414880c0b1203681030180b85821b1a281c40da051001101c0080402c12040f40000301040010048a04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 741088444 1250 741087194 741087223
    0x5060a080f071107030804030512033d0321080702100e0a02090f0f070c1505072a02121506120705101205182109060304060626 56
    0x202030b99580300454142c8120001c14106000d205800800c202c5000d0150040d2441041a100e4005003a000c0c45c100d8001164280c2682158003580868903c5400c26100e101c001e1419070041034208410800301422254400c031040d09030301c031540e00242c00056075a50340d031281d868883c0729414405402561140c5100c00c50005e140d441011900601041114583c0d480e4094a01f4580d45800c0c04020006202240d40c0050702d030326200010305c00380c0308001541000781c0c0f004400000054100c07140000b00f100034000014081d0f40210f006070044031014800b044c40bc1b03031107003180702d0300603106101a0321880d1303411508591140416040410004c032746203620800079a410341d8004e1400c0c5d402882d2544550145800c80310380c000030203400394440c40014209210000c18451600c2c0c0d901e101102c11000407034504540c0001c107804501c640c41c0350381140744118000c00b2a0601500000080f4503501c01e8070101d0702e041d42c614040104400340000044121b00c042c03d80c130200041e002c2c055480313007404071b840107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 741089694 1250 741088444 741088471
    0x20a050d050c0114041b120308070503270123150415090c0305060a0b07020a0603150f0f0e0708040804052403090a0c05060f09040911151305060a08 65
    0x700d201c0702580620004d070980c1560380980e0030241040541c002440010030202c030090a0007083c011001c507403a0000740e5060790307004890303940c0d500c0454881c0c002400c1c5800c81c04d4032156070744442e00b1019044504103d03032000015085500c0c8c18521100c0c4620380344075076000103c010081c02410b002817003800b110741602c001c03412041090019040c00020780219042c1480c0510103031751168194400c6218400540f9030000040e02c0d03804840c0203001d031000c029030107480d1003400e000d00c0e4804e80001b80340c46a4070510001894071444a80d90071038003900700c80011075130380a00700120a000b4400e1a0404018103007510700d81483d0b01c03400043d1050b400740030f0007901003da0404810385600601d040345401c0c50303000364032401c06481c0070382c65030003002c4140d0346102c42440101e280e1801d83e00b10343c180300340602c0c0c0a180c0580c40048c4000740041410540e6132048000741203109460343c0350300101d203029980080c1c4d070354820300d8102c21194141c0d410050003401e052000086c040d8010550a800844449614 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 741090944 1250 741089694 741089707
    0x1a0a1401020a1e0c032103050c0304060b03241b030903161a0112020406051f031a09042f010c0201050d0f06120b06120a0f03111c0e01020a050d05 64
    0x1114071014030070f8001d00c070b80f48030b00000051009000075032034440310324100007004018041048098890641c4c14444990040021500003045036000c01440c1c4c01c090242c07007c0031984294014258803007007052407201407103420403400c2c08800044101d0030200708503090450130b0207001141e6a00580e8030750791004840c1c48100e001c0c01010001440080042c5060301099a115405204074400300300040740503d0601201113100e203000c07010743d0410b800b00b10300e08603008850801200545089504100d150064004480040d19030103074551041c0d0040070780e29024080e0903070b008000c130741302d1108a195a414104501003030303a0160012020b01d4091070050f880c0e40034510003600810300410079101003850910001080340f22200c2a03a40705001d606241810b40d182000d02a200d0841c41c10352070f40c1d40262203e4000182001c4014103014006e1418005010742504594070741317900283c05070205808850300c590802c1d800140c85554600a20191103041100c0d66500c1da50562020200288440810503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 741092194 1250 741090944 741090983
    0xd0602040e0703271e0618030507121412071115191509020703021c020a0b0603010e06160c0b100e34030905011a0a1401020a 55
    0x68501900101000280905100c00d002d0000e29018000084801401c01d511225104180c50003440580008400c8600c0c05e5155130500c50f244490b03001ca600d155500000000b42406800c552403a40c46a1212956070b145805c2c0221b00241243c0307448204800405444050039028043d100250840d01000f001c2d03030ac1e910b00941e44408101d01c1128103200d92404880104101c0700034038040c3d1029640d43e0090311401d4026010f8038481c034040d00d000c1008400c00c10081019a00a01250780240b0607100760b0401c0840315441c84c60f80303a40c0340b40160301c80c1034203030144682c9041181d006007080780200710b40000298245d40760b4030000d10340c049a05040303801a032403d0080b404600c1c0746500a003034901501d0103440d00400000746002e01c00440c540310b80016544c401d01403075150768244078006000d82ea46041c44805400000303422420030503490380c0c0d090000403000d001e44400090b00f580820920300b00002401049051035010340400e00d10303c00104003598000c541c601600c0c0d04182e10f141c2c001601c198 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 741093444 1250 741092194 741092197
    0x17030f090f12150c0f070f0203010209060c0102090a1202031b0111150907140303030c09060403021305090105150a14030102041d0711010203010e010b0c1c0f08060d080304020d0602 79
    0x219400140c42c550480ba0000c000c108500840d44590305610140c40d510007540b10b90060069091609008015a002007101000703016a014801000589001591408104280c01880080040b40e4000c20094405d1400c102040702812030183c0079803609603a078000076590240128505448030744400040380d0343c0d2240500d006000c036043e084800c10700007171107030428041085580c0b00c400d00400c50007003614090031070701c0c80f440034008000b18290f803074001c40c01000d80d00000e40d441e07018004010020050b1608021010298515080000d05180c1180c0603800c2d81c500807c42c02015041080700c4080d0364903030228034103a82904c0380340170381d542d01200401e0081c46981c004940701015200c07034a86288900e504c3e10311540096441100500200d0070081c240e0100b801000240d80166005020451000c40902207042100e030481d00c20402c407003410461110100050000280380402e0001c515400c040d007c0d801401c01e0320491a6503045446601d003900010f04000e100b820540c5d820002d01c0300580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 741094694 1250 741093444 741093469
    0x10c02040216061410031b0503160303030b1503070507021210050402100f1e02030d05010e0a06211211070b0406110613110a030c03060501050301050117030f09 70
    0x2041150340b00101200c1c0070150040400c02c07203000d8202200707000b4032403980f80214050745203558140d440d98190790394001c8440010401c1c40041c002c1ca07000041381e940c104500c0c02e52000c51b005170400c0c9ca0841c01d008040c2d5101485150040a0000003d5100c003014001c0703c1c2e01589600e001c0361103128920008120480903854904580304001e440600340c0c415504c100c1c000c920856180850500f03960040e40d03220012880e20000c10051710317010001944030314000c500b11929205691800f98400d4209040702d0302a00b0a510381c01c0e03c08100002e040d254030951010b00729402500034011000b201c0d054030101503c030000d1121072258400c180640c054116040c100030306105907210a620f9652003800c1d9003152182c08001388806806101c0c50501152043c081c01801c400300d00f408103640c891041148408140c140c101c0160400000450b650034007841c040c44c450f50012036507500d00801c0600703503107042c3c200350156450810140f001c500b002040f40d2000708007485190301c0f112214000f545a11420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 741095944 1250 741094694 741094699
    0x4050c0907032a031d2512030306080f010204031106070602040302100206070215070f080403140408071706010e0103110607060f05090f0c010e04050919030c03021b0a090b010c02 78
    0x620408029070260989030311624159504010688540030b40007081c0c5000d503008503443d00081a104802a4008034101d07060041015a0b0340043d41d03801481321021041f01c080c6c0009546140521000b402800704556101c14038000b5400d15045031a5a200e85147c159050310440340010180d00304212a0155402107400928946c028911158080e440d998110358070310040c0503030701c840c00c290001d400b08c1c18015031b1a030f501c84094000c0044199149100034105400388803040d2680c04800054000400107001c1850260456a180c45070110481800c02042c48603034010600602c0980f890b02c12a0341101d0300148010b07040002d039808034101f44603024015251500b009464003d941803a0841c501614100e41120710940b41c41800d940c03150400c0301e0b410b0000d00c1000f010052490150404c68020703800d0820f86002c60340d8042c010032000e0000f001103010070130700702c0c51806054040c0119801960901d041301d2078800c01d0000181c1c01c10b018050107541380d030348002240301c5900c035081d0300c1c00c000e601 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 741097194 1250 741095944 741095981
    0x115031e02070312050703091502071b120314030c030705030a15030f02121222081518010506090601050a05090a0e100902040305060c0313050a0c0f0e04050c090703 72
    0x40d0b0400600102521140442e00e0303040001045031581f1038410409810340101580000180d02e145002c0039502100c4140d40808160064414408001d04e4a0300189204809400354501d9494060142206d0b40800141c24405000300400b014001089130762000c0a8030f001552a6109a24000200040341010482c042d000b0300220400030300f1111940351500855020180c8400203800369522440040b04144510090110250b5039400b840345008080060b40c0c58001d09458a2505140980c450f11500300c511607038007404000d00c2e030714041302100180c83c0700900580c500380020505195019151074108900000c2c0074a0140c801c5040d0350707003108014514400340c0d5644000c03031220581681c806070510711450002450940d14402c031750440740d0040140441e0780c0d8000c1004c400b9080105a03e40f1840c0e4402000e0024400b0302811049921038100c00c0b4406041c410031a000310010342014100611110070312000c10300016148001c60401c9400c40c509507a1000220064641800001c074003694 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 741098444 1250 741097194 741097207
    0x11070303030e102405041506030209130906020d11040807120309081b130b0d0b150a0b18010f171803070f110109180b030a1e02010e03060115031e02 65
    0x440310001c5804e4044514a1030105445404101c1210b400c240000d0b202e103a01001040050702035006072100c040024140071a10284034180429a0031f020b8040b10710a9002684400e001000d216400c1c010348000c00e42400c107400c204146a41c1c804500400070407420301048001007501c18500032020744042e006544805c030a03d052072008101c3d05141d5882500d5040c910200742c059032040140ca00b0f4001e100c001c80064580311503140760781c090054911001c5000c64151140c9411040c080182100c9504d41d9607804418a890201c1d581c80200038100b261240d00c1e468161341c40015450710400812801081c1e4407000a0080c0030000e00081905501011405000740001c046854580d98000ca4a100300c1005881c011503440009004124034044000695110030b0041c2d0700c034058146020b0120303107441a0345e440b000724010b00c0c3d401041c004501481810110b59000500340c01e0100107070020305c2d4550500d20b0b1a2014400011080300701a6111070b40e0314581c0ca10346d0341500f10034088104645c2c1d07a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 741099694 1250 741098444 741098471
    0x501021b0c090906100501080406090605010b030406140c03041e060c0504050a09060f0b1b011a040c080903181c121d010c02060903030d110a030c11070303030e10 71
    0x907900d00e0062180d004040002d001c2d41010808138415184030004d51074031400c180041d514880064001c0c1d8146a88075a080c0c000342561081a000c0e060000200c2d40b05e241030311300b0005035034103d003601c804182e15a003030000d101802420b982c0c20507400714031042d41080042001881e9042140302810740c42c241f08500b604160488010004d031181514030001c4540c0b81e00c441400d96a4601c030715480705da03400d1307802c201203165900a07010342c0410f100707201108103c001ca00303400d447c40500c600c18410346401d000300407850188994520003066051544403482c10703d00709500d0740102c2101035015440b5240c100100e66481c1d0301500d80f40550144102981d2060621080481002c00c0040108540e40700100c0d500400785003080321910142e4691038050107a07402e004581d048600f220750944014401518290801d0203030040d420b80d55a41035494000d501c10013400d6601c00c1210742c0074890168802079219402180c903034207030307905401c01180f58100700c040e00d403802040b00c0003d0f00d03d61400617044030b00c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 741100944 1250 741099694 741099703
    0x18060709091104030c0e10030501020d15060c120315240e09040c030f150f0e0c0d0803152107030b070e011d01050d0608150c070c0b03040501021b 64
    0xc5040d804100040468020000e0551183e800054105404508108841c034810003440d6801460a10400581ca41c0c90381c0d62402d9800801e114107285454100d2075090085e00002540142414500720318855201c0c0c941020707010418160608060300c8210080c0741950b8013543c0300051110700f0071286003110b480d00d000401080d10500c04000f90782c0304002449803900740b000d0b43c01340c0e412152010502d45503a0f6000340c10001c1ca10102d410740080700e01900f002a143c030450501c4602e1340004281c41b0f544a18060a2030406240603100c1c4040349401404141c81e1020340781c1c48003242403d0318500345501c00050200920000410714641d4400c13180e0b50809010030f1400890384a603441c0c5059407110101915046400c4010710f001601c1c540024145941081411802c4141070410074a85040c850011080d1891600315010f075601041e11000e010b03071030038003165129007a80109800c180c5a6980c94840d020070b4481d00848581c0400401c05210f02941110f1090f400322a0f0b5583c1035801c1c4048a884 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 741102194 1250 741100944 741100949
    0x31204060b0406051f021c0807030c021b060c0f03210106020304050d0807020a0503030d060806010806040c0e09070e0109050612011b0f05040f0b13081504060518060709 74
    0x400341070480340000ca003010700400341a03c000034401800c000780c0c031280b146003490101c0c2100c110301c00c000715620a80c440d8942515500307010760b01d0001500c3c064402a0540d00c041c5400c03811940f02d91581403000900c2c001c0030840e10012201e0f00d81d910701341d0f8501e40c6806009070a89141d808006a0407081903e0305140354802c04402c00403001c40c0ea0b03180e40603a200d010314810203801a502040318030014403118010401c0d20702c000e1501704004c3c0c0b11008a4034582100008812a65460764181b202403400c2100a0051403954002c0110b0b162a80c1d0310f040d201824031072220780c9154140031403440f9905004900140540e1601c5030303620341c1c0d111000f201a09041c0c0f8030f03600480600804420440341070007445161002c2240d5080024030384441110441c074000603580410074244400306d104224900400c0003030100070004ea4407100c0e003152100d004103490303220118560100388402081d003182c5207103603445070b040800082e580da10050790ba0204010001c0d1440706020340410002a03a40150780c0009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 741103444 1250 741102194 741102203
    0x16120609120507022103160f0605010314010f05040f0f050f030a02010f0b091e2d070e01021627090b01060e01050c100209060f0d05060f040524040b03031204 69
    0x80440017400c02da541c1c01580d03100420750303800c100060b0305000c3c00b11764120321091080c10307000e01001983d243c200440c0c81c01e0300110307110b44500348207901c500000d0080c2d1650425901e420041424a40e1303410940b00e0503004000e142003010388510007402000d0040243d01c00d00c0d07101740e035614400164001c1c001c08091014912052070034009d206107040110030203200c1c00e0444c05c041d00c485405a1046820b60b0700034101d107098804496203100c403c200199801d0312075001e1040e00c50070300b0305100113449000d40004043c11580000c80d40d0780004884120304007201e850005402c81c0c0381ca00680100c81040408003500c0741c0307081c926000c00708090006924121040d559405101c10500b400446049c415440c0d0205180d205180d0b03200e080786d0542c010080024014003a600d0f0401c00e50304100c1f950041413183c2c0490f65543c04201c80c40c1040ca1013051510790494003000b40c4d28109c102122140d221200d4180c0030300120042c092542c07200e41c008810014010f04030317500e40c03075980c04e4003030015401c442c02c4a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 741104694 1250 741103444 741103459
    0x90309091e1510141603170a11030411010318051606210e03300702030304020105041211040218040e01020c03071e15020306030d021612060912050702 66
    0x40c1c1001d940140301c180700740700600500b4903455909088441405844a8052400003003104c1c0c00c0176403504144c200f4040c880d0301c82c0d20705408280500941550010940760300c603070600110700ca22250701021aa4001c0c0d115010b5403031407160701f0040700109080050310030100b900c0001d54040c02400103807040e203600c0c60b940c6804041d84801d001c9440d680004610f86185135044503080d107550041d00030989000c11341048908245900d500103101c41c4400f210b40780046c0c00f2404056482580d0300c87e00e03500000b2800110f15506041d40000d00c1c034440c3c1d1042d90345000e01104c1e072074104280c03003120065850b4010000e5413210301541502107040c060081c401c1c85946001520701b08500f042c0240c60101458002450511903d521124140342c0401203000c0903031408850600040c104543c80381c1c0d15481da10b030068a9186c05810f051404a244030303070105640c004100300c0d5500ea000760341e1030140c0d00ba800118660814615050000d0420407400900d28480f4901012260790b2190107880028000c54820 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 741105944 1250 741104694 741104701
    0xe07020d1b031733040b040b0f10020c04110c0d0504030308010302090c09180108250b03061908030a030501090e07031401140405210c030f09010504090f090311010c17090309091e 78
    0x4803c0311818401603402c08000040c1c409d0a01c0c0c000580114000d0310300541d0300c000e01c0d2200240490340021803074000524041465090003400f00f1006034140190305000d85030608544000d8580001440003c0c4240080400910380210748820359841000162408800e2440d0409041e46c101c824050b40078644281008000c00c01c0d06040d24940400320004201c41d510704101101c20749a000030240741d040010080d5204201540c2c2070301d00c00601e003941c051500c9900c008001415a10180e0022030141e0400c40b80c0c1651280204071f6004503540080e154800403c415810350141009150f181c0c4254605020030091000201c0d0a906580510420310503050100484040c41d010300c0c150052142d0040c0410030700380c1055002800c213040141003c40c10a56106c41c82025541803042941199403143c0300b40d4100b58004011a00c0b031491706000340309050642c20002c1c90f449e60003818500e0442c1c00800b01e04c0c024018411143c942202810101c12450804101e03016000700010300308038440d854001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 741107194 1250 741105944 741105949
    0xb1e040b21070207060c0212152404050403051207030b0a090506120312070f090b03070f02011b020c04050c16050a05122a01060e07020d1b031733040b 66
    0x12006940717454860007810310064083c0314203d0002406000184180d50340d8031142ca42d00162075205602145000f10760059440d000e4a2048100214500840c100b00500001a400406482c2c00c602645030700c1c0311a03036400f4400c030017401c0301001c041c3d040428000d01140601c9941c001520401095640030a2680511038055880c405c400043c0441080d80011500c0c052058803410b1211a0034500340c0c0c17060f611028500050350003924004081104082c01c0250650203014469044040d0707240880c0d05040c00d14040d4648040d03000f40c0348165070301c100080360200c1c01d1007030b140202038407103c0c400500c4c2c1c5450503a40d5a4007981d02075641d17220b1105801585024103003100d0080384030608020581c01c00c3c41e0140103450703406034591195504d030344000c20503480c12001a0300c10382c1d5603401020102040c42e0040c105040215586c1c987c15542011341c004660881c441c100c01c3c3c201c400702d03400c1c141c1e124107483ca004804071100120b440f0124080b0120700f0000d603180403405d90100c408104c01d80d1610b04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 741108444 1250 741107194 741107203
    0xc01050603030304020a0e04030306150c050d0c020306071b05100204030c0f03020f010e040902040c09061206080d14070b04030804060f09050d030f060504060b1308070b1e040b210702 80
    0x4000f1b5010070742c14404e21035441010340841d0894070074200862410f8848540961210501c0c5038400007a40703540d84042800010040b441b5482d8103424109150710154003c2629000001c3c2200d0a11094550411295034101c0700c981605401c4000e4600303e09403404000003a40c45848141c80d551440000442d0741300000d107681d01181e03070050103003101c09040740c010360f2101c1d14601c036160b01550f600038202c0541c907540240344580c0041c1c1c3c0c0d000d402c00d06044000c0c000555100006807418580b85003400b6810700000c03424102442410700304004d80100c2e040d061184a4190010705420101080c0010150040002c070700441c801c0c1800c0c020004a8481c8508842d1030350b40c041c20680c002145100198000d600c2001c4211102c8800300c0e501e41c550000c0760680b1040c0d40228008000090784d800070b0415030101401901c80c4001415940e440d12000e84d000340901c01034122000c0c240c08126940100a1040720020304481d00510b0300c030700220221001c040305580d803405c6041c40301d00c00a01014400709 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 741109694 1250 741108444 741108451
    0x30b0603090c15091309021c031218050d03141308093a0b060603090d080c1209030a09060206220807020306091006080c0f27010b0c010506030303 64
    0x1004020070b0402c0740c10059850100c80302d400d2020010884138200b42c8a190214203032140f08840411403540501c18081c020540700202c81c0d05040b0400d07400d000030f07400310002c1100d04c40740c2008950752411416011715058801e03401005480b03600900d52049400d41c208854904d001c0384041e6150740c401c03036620b041503034100c0e00400c0b002c410000701345c05240908006241e0860040c1c12001860820440349040c0701041c508a6914014030301c4500304041c203032020794010820b541071411420100700c0c40d980c60f81c048101006020904001600a00b030aa0590f8841c03203880704100c203141004405652664003030b0b07141e0000078600c2c4c1c00126499000003200da0107502e00e404956040352451702d0000101480742c0c422283d0f00e41c104002005641c00700300190240e848080030740004031461040300206c40700e46d80500744d160400c428440d035542c2d07841c668420380c0c0401d03a100c04441460058644001c2460142006900070040000c1a01c0300c91101500c4109001e400070030070743e00c803e0101503607404100d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 741110944 1250 741109694 741109711
    0x1b09140d0c0608130804080c030c150304030804030201090b0f04211b0206090303070b06190501050304080c1005040803091e0303040f0c12031e081b031b0403050d030b0603 75
    0x4841081002d10a80889a1000d0600d0312003602e1402517031000c1c2d85600690144074982c5c0100d0105140d464107001507542110308850302018401b112405201ca03000041c400760030b000d8541d0024007418001e40005c143c0c1980840c10700014a841c20701025003c0041d2810382d01691904501801c18480d4601152822450b8584078030101032918403001149004008a810203810b2040c8002a14200060000948903169100342441d0250910407140120424074002d00c0c60340004010036600041120341140c0c204190300da40b0451182298940340801002442c500d1910041006022050b8040c2d80101701c2030040d0b80320119814518000a40715140301c0c00c0640003000401d0000b003200c000403051510501461406c942e4034402103240d0520900140c001c2100848005075401c0f00448030514203400c1d003444c40c218100301044031264a01001e82c4400640c001010903041444a1202c0f1103124001406561701c2c0c2c1c0b02d1030050344941e850303c0c2071000b003810400b203004545000c9040da4800c00a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 741112194 1250 741110944 741110963
    0x10e07020604021e060c16052b0609020f090f01140609030c060a0c1a01060905060708030f0402030c0604060339031a040e0c0f0a1a0c011b09140d 64
    0x1120f22002144c1c1040c2c641a61040302044000c010880500004000c40509031240c0102450081846a20070303031400c800342034a0070482c18485035484507420109803034218100194264143c40410500c00c604208517501074001c2003000328500307074140c11505071072524040041070001c54080c400d8074041c800705142d05801c00190030a150078000041c1000301d4aa26002131502c503991901c014101030443d0007d020070b0040014001da035080310035880140000d0b1343c040c2c07a01c44180c84207880c0307020103400c1e81d4002584002040a540e030820203078600e05001880b040da56580c81e40054014031074520482105041c0408402c1c4848648004503240e900300580c03000c261b01d0050b405c8009001d00c4101103004103180908801d00e4840344240081a5286001004002c105a0401c21110741044001c0d00c5001048400d0202c400e2181900030310a101d02035880d03c9a82e0845c02d203001d8500303d8180141c0c20703205024910b45941c00728a1404807414880482440340c0d60209000b40d134080c1c2840071302080c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 741113444 1250 741112194 741112219
    0x10305060612041a0906100f0312050c010b030616121104030f1401110408011407090504090618060504230c0d050c03060108100b032b09030812010e0702060402 70
    0x1e24145a40c1c000d01c5801d0141d241d08004c111a500000c068070f40f5620f981c405020450301800810401020b4491051049051746c5103035118600c184011540c01308000d000325400c107044000750000c90144c000201a42c0035071400c24450080180c14803099030020324842c1c104510710700d05120300010029048551803400382541c80d4608026220b007000c07203200384240540d0220240a02c50854240c442003080380d43c8918200c102c6081d0f4480c140c2d0310810781c02038002d00c144641c1002d0302d00103c41055501044d81c10444c14980f00170145000d01500020b00f00761940c0811902d039000503c2640328000112181c0003618961401004041151040b680030300c40d96003640c50482e02405c5220321401c1115903510410010904040e8284d00c4a00164400b500007400d038035050017001c0403000c06400520036040880103001c064869003480c0020551002e40800c10b0328440c403450006140c20a004998030b040c0c0042da07414070103092191088a500d48400310704c0740380c40881c101e40280c0d00104001021207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 741114694 1250 741113444 741113467
    0x1061502190f06091e060207062301052101060e0108210403020d060603240b040902090408030901021e120a09020108040b0a39020c01090e0606070c1202010207050103050606 76
    0x6444c0400da4131400b040d40d000e0f1300b08110b0410500c042d44100800368035030440d40f070004150362a2880c0a81800d08404410300326203007403114a811608101c428007441c01c000502c40502c58240c8624040300d5082020114200e40049a514100c5a805084580d200d12a00d4500d280e0700c0390480300410008100320030000b5203070040d11403801a00403a0005651540c07a0343d0050308980c2102c000c500e03401e0490f8a400900583c1c41402e81c501026a02400340011720341c001940710b18018001000d08101002050640d134003541034402c541120911040324014091140f11160001840040c00321800e00000d1a0420b4a009540d0442e6041c1c44030f8000707854550302d40108040060000340380c82c0ea51104825109100000c2c81a812900d12036100c2207440302100217a0040c905a9100c19940502001600d80c0d030f00004c458200d071418641d5021580710b44c00080c030a03100c3c1600281c60110104004250b201c0074042c9060301902c00d800b242d490599410040d41a1030b421112945d0154042c480d032041d44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 741115944 1250 741114694 741114701
    0x305042d112b0215190e060f09040e0a0209251803030e0f090109020702030f0a0201171509010902040e0a111c020d0e0a0b0f0c09010f020c0301061502190f06 69
    0x24030080c86900402c200030012400c5421a8680e00e0081c0008400c111101c2c3e0801b8040d0506a015100c0a2400c03104042c125102d10510b550f480c041c1d40e4404c0b46001c1508144410350000f9030042120355181024032213400b146c0d0201e00c058040e005414003240005000d90103d640400b0316811402150b80b56031401c2e2117202029607215006480e488003c0c0c103c0e0f452012a90280420210041c5c480c00d140c01072614066100c03180c8549540903403c0321300581c0c0c012850a41007140b9046141141e92048098000c0c210030b00b00c901d40100c07529002040c11a02da0700070b070051344e2645810310210b43e1001c1ca100140c42c21142400b0381ea400411000c00c00680204031000307034245441c401340c07400518034a0304003160808002c0e138680da008480f40c44204182d00305026001100610a0015030600b5102c40cbda052144400c5c6030f06028120140c00a4540207112100101800030000c00c002075540540c402551141180c3d00014090303031a04100f080d0020100d50074280e00004810303001d02d01650b405009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 741117194 1250 741115944 741116029
    0x30c0c13020c0d020106140108040c0b030c0f0a050a0f0c021003020a0509060705070e2406071a090a03030513030903120e03100b0a06050c0d0305042d11 67
    0x2619000c10002451200810540c503150038250300000c6c0305850f2540349204019044a0139040007420380501002c00c0d8004c400c8000c2d14091070b603455682c0ca5803a00050036205d06007991403005000315076941c1040d0050302501040302691114151241041411611800030440c004c0d480400d10460702e003503511943c05417a8903201070078a40e2418a211001501c103822240080360140d00104041c01010f0001100c3c03600710f41c002500c403072104500f950940508c4407241945014980220700582071083d00d00c07410b95100806100801d69050051107039868560700c00301038010a0424011600d01202e03101c083c013400d40c2542d20014403a0455440010214800220340200300d91800c8410896406002c0350100b1808610000f03040204601880180c40d15580540144181071020705604800890300003410085c07484d0004850b40c440c41c0401c102242080d0000c000100c9030140d5106400340342d40745000a000380c015003401c81c01c0c4001c014030390030700103000c1e96000c0b04640d04985902d1104d031a0781c4c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 741118444 1250 741117194 741117229
    0x10e0121170918060310020a0206070c02030a060c0c02031605060a080a0603050613030f211e111c27080705121b0c0604290a02030714030c0c 62
    0x1804070b5500005600c5401052064a6a00104140403891504000310b448600180b0402e50804000200203511401c004013071505101f0320261032821541c09000030302c2c0745030340500c04010900c44040001e01560038100c0490003886404541d007034a65040e0074240880380000c0c0340c54a40820161308030351041c5d000c0c0c030442c1d802e41c5610000c40010b4051042e030340f00710345c2d0300d00000403180f080c20000c2101a07081d4032501400071020382c84d1418061404101181c81e40180045403080c54110070803405c60411643d01160340c5030030030b1601c04034040801800e140740c2142c0300b00c0344091249400d00844040502d02909141c680b201c500340c9140c900204002d440c0942d4015050450544406003040703070007041c00b4200000001d2400781b05054928034240b410624004100d140101c00102d8058411f0740507016540c084140711000460b038104207024010314011904ea1681c5001d04003950300e130030041c81115844080c10170500480c600106440300c90751810028403c0000f400f042c4400e400c0034882411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 741119694 1250 741118444 741118447
    0x80d14070c0b0c0601060e0d12021e070906081b09070215040b010608130f03050913020708180105130306230403080f060a0320011b0506010e012117 65
    0x30100740d030004000001c00c4610611a6582c42d214505800c2080581207481800a0540c10506503281c2c06030114009a224840c20792000708001c06a252041656040580705900c041405051001007031400440c1c1518034144506a21101c40c0c9403120340600010f040c0710340184c0750b007041d89880b0070182d4101d0101d00548605840c508000302e814441260705541d954070703550040050a0b841080705038400007045030380c1d08a08842d6a80703454090245409170400401084440b000c1d521030220300c01d6103031111411540c2c2d00942c681a181a00580000c1c118112904030914140d4054800c8230201440d800e5000c0d00b483c1565520001080d0078011b010741c0f0b400d00704115607a00c0142a05500a9010341c69205c0e0070f14142e40c0b01103204c4401082e2500540c81464208000b9840380a02000140d12a002613000454600120b55807428581c503c241d0b03161400c02ca0090000101d01141a1210030301540151b030303200c401c1c082d142090115405101840d92031b2100124500705041ca4201a0080007903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 741120944 1250 741119694 741119707
    0x1f0b0c061618060314010603090201020c13060803040324020c12071b08150604020a0c060515030321060604030807020402090d0b01080f0c0301090203060f130515040201030b040501080d14 82
    0x10303984a4840e802c0080400da0340c04040d1700001da02c03075540740101030502c2c042c4001642030340002d4450001b040102d0040305040c03403000030100d1581204001e0040c3c8000c5a44555590030648490b42c0200c00d59580100c0d0a03100784c074a00441c0c001c6400c24003464008104000603c0c6d820307000350b842203c0c1a202c3e40c1d00360344203014441054407490004c0060000070321034440c4040b002262604050a114481c510402c107040c06035030400d4035804241c1e04283c00041e0307543c1c0c01050030809884480003651502000800d80c402481160640c00c0300c04840142c0c2c142130340c0c2c03841401500d00c01c0e404013030302d0701380203014400c010314068004110078140a0560f001400c0c0710368411700310943c00c1e007240305582c00c410340000e0140020420079a142c40100d000340309440050300440d03202c250144c8903a0081210400140115085c242443c0005520900311014084001065000448180c5040340001d040250150b01441c0900955042c1e9001034060001030380300e01420f8903111801c2004204212003032014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 741122194 1250 741120944 741120977
    0x14060114030709091e2d0207020604030b070f020f0f060a0209040b0d152a0807020a0506070305010501090905040b1f050a0e1b0301140f0f091f0b0c0616 67
    0x1080c100e5510103106071804104901d1003800d5075201c0c1a21b007030010040d610b004c035001c0503407070b55841c0740d07180000140d440d0003a0000c00c03c03500ca186c0024043d10440f806005620354048450a0314107280e509550072000752642484d1108104224215a540401c0c007003804800e01d540200350711380e0010b200045c00c10000d40400c021800c1d125060b600c500c013207803c10720800c000e80a289103203860602380309480fa40c0d0445c0f80545018100b80c8a0401c19400000b91030980204031504070280c001d000c0328070070314044100a010f00003d015550000e044100300045401d818055140a241d01400111142d600c60040d2540525070349a00386506400000000300d603103c000b054809095030f2994100146491401d840071120100d00d604244413007000100700046403017000203803019040320391403142641e100010f441c08a540814030750000ea81418020285d941c00c100240304045400702d055101e54884122036940034542c41016150084000110001c00c2850045000001030a2002824000c0c100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 741123444 1250 741122194 741122201
    0x150f0d0b13050712080d0b0117180106090221070207050a140a080f070902030a020f04060c05060a0501080a020603090106081c03111e092d01031406011403070909 71
    0x41e004024003030684690103100040c003c0f1405014000c594504d0341000b0742c0c2d400c0f014452011101d0111b6501c02c205030260b0301c1400010340052501440d00c400303003002500c06145c980ca0100c501950b628040c80059047c0700c600942d80c0a0024007110000c02c00002d0903e615108010850400c500501402046580e00c411303a001c0175003070b64042c40d11480180e2051241c00d5880d50800c00503030340404200e40000070005910b90503101d01c007030050303202c1d100e01d86108041d01452000d404222030200f4041403041d4041100c0307040070b000b8030484003580c0b104e24030b80b02107603400c0c0104582c680104895602504004c0b0007075400c540980000601c4682c6c540d0040c1c2000900e1150880f10405200c0d0700000b95450700959220315030702e203132140c9041e80101400404050040d0460070301c44020a040c0d2003543c4e030400c0b030391a00b6002c4a40c412019610341d0190200140065440d011900e0710440c40710203401c034006203200d4003060311140a40c407004c070550703e50758000400c0344040000c1e6907000700700c5605502 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 741124694 1250 741123444 741123451
    0x60f0f04060e190612080406272c22080706060f03380408070f030e040f050105031b06070611030403030e0f1e151e0c03150f0d0b 57
    0x280fa044404410806002c1e40e2181e0700c02e08102420a002d200851141012201107480a003030210b440300c40c0f40c9001100c41108015400103801d01000011801d800418002d003600c1030f000520441d0032010001e0025140a440350040380b21569a020705030380c420116060001d0082035142d081ca03a15555940030740702280c01240082021110410400c10080c480c0c14400c20141c00308020301d62000d83c0602c4199030ba49003050294440400f05040c820418100d9010b181c01c000c6500003a009410040e1080c803d02c2800b602451406100703003203552640c401c3e681624802809010041e882949075150a6030041180d80d000c20f0400c44080010403901c10f010b80b62201000b8241c44e0319141c1005000c9400400421115400000d5410814000410384508198010041c121328100d240415460907055420104140d04081c003803002d4019400307006c02d502c00b955142040240c0d284810a01c0c203000a42e070900d810606149040c0140c644400d4203ca10480a01040019001d980310b03c41c3e004400e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 741125944 1250 741124694 741124711
    0x8090a140127050601080d1b0206040b0c07140a0e0c0304240f110306091810020a0503011e0305030304082b0e07060f050703050d0e06090f010c08060f0f04060e 70
    0x10381c081d030b041020500030103005190b8580980708002d140f440c09410a41d0903081941030405070283c0004541d01d1100342c401500c1c0341e075a07281d2140b690030b1901d030795100c4034010f60310700300700265100d2070380c4c40c00714000390075203040040703010b55030710b5454151400390005041191a280480424215110318200c004003d580da80004540c501c64002c4080866900b4034142405000800030040345445854840703070000c0e4072035074003a0b0824810301120b040c103180c42064542e080c000640c0c180d120703034800061816641c41c2040d151560044020518072503115210090003032708103000040104007518040c0c8031843c54244c2c0b6015000502c201d076050b64090011540855507600e084407040301c410880d40c00a4050303070400c031141c1a1014000741c40d40c014030400400f00200010f0100e800306060300040c4011404c0c2d000ca0b0014100703100b0954540c4220704003000740e07600e06803883c2030700c0c3d21901103607000f0b01c40684034021045000c800d002229298103c2a034210751034802c00104100c060100030700c02c0825 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 741127194 1250 741125944 741126011
    0x1110a08070e010302190e031002030a0605090603030705120a020f07030c0e1614071a01030507032a1401300b060405030d03020307200102030a05060108090a1401 71
    0x922006800c14442c1465181010b105002c01c0c0319081c1901c1966001034941d0078200c46400504000138502012005140d100c1c2c1e00109c14880c1f5550ba540200e0242c407000c4aa0412641c0d0791010300da56800f900d00003400a0384040c00b028035a000840041c400e842ca5032041d61180368030b100f000303071504520b980211015401480e007000b07131411946295400102500380000c2d000d071641c2000b0041041c4100d108082c84000400b0030801100011002d41c80ca211160701b0705c0c0c1e43e5242041601c4803070354031040d10a680a61603810365642d0707201d02803800b02540c8841500396400d090650100d580180340703240c140500c88000c42c00c506000e11541d0340781007000d50100081d0502001c58815a4490300b9003038090710081c0b005004950300440d004060030302030301c0d0050700c0381e5030303054101c485107031007001d8100c8626090444c2001d1001900110b100b0f840000d0203120380e49540c0c00455501e40e045420004a03003020380e4440000d420103d1030001c8140d09030010a01a1002041807208804000d01000100c0c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 741128444 1250 741127194 741127201
    0x11040e040b060f01180501050a0c050105010b030108250b0d0623030d0f0203040e0c070209010305030d0c110d0309030201020c030a1805010219060908121509090c0d060e01110a08 78
    0x1050106080403070828a01085c81c55259880196034403814020f00b414000040380d00c061b0f941c400d06144442c42d070018000e100a5960340f2099003158401c0c00344010500072040d0849a01c600648580c03000d0b003d003008295140c1c075200300810aa04000024508c0036100e0360002000c04054188800c4400900d40106c18444900c0030140342071281d103160070910207034442300c5940d150003009071011641d440c52421442e6903008041040c3c1c0c410110000d6106d5814130010040c4440080982030308541d40c1003c009115080000381d070b1120008020411aa2003d5003817043c082c400d411886906209000140c204940108000d0450b00030801841c002001d841c0550082c19110b40301d03c1c014202030024292580100203c1d020450b0380a00c080d00d22625a46000c04208004003210b5013518114110500d50500700c1c0c040d20342d0110310760001d2040d0308090102c0c607400c1e0b000c1246056190700502c02d032616451a541c0070042c10380300d00c40c1c01c40c95598403114071840016900424903002603507900d000924 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 741129694 1250 741128444 741128449
    0x213110d11390f070509090c0613090e070f12020d0606080f0106090203090303070f0e0a0e0103050c030f0622020604080303071e02030d02030c1308160503010e0d0311040e040b06 78
    0x34900107801103a0f61000c482c540161601140550940340309903101ea02c240c3d00c000354180b4001a4102c540d800440004484007010418610f00c0107480c1b8116003480f0050340068070a5a0340100e00600300c56240d02e8404000120b0940c002486480c03026003450281c05880d1580f2080307910a40c0b083c415034000f2010448600d20a02ca01405007503035802c00c50450030704405d03442d6030b03000080840c0248051041b82140850181c07404011590300141050241e81d01e4034808000040c4c01c1c401140ea52144148845141c40c000c1242030102c013040c0010041aa9512140440000d15030322500e040c00a02c840200035844003001803014050030030040d6540d081440c001015809100c41000c1e05805080101c4503445d40441192014a0003080158a0740c6584510b0003481c8103203441c02c400301c000164001000031000c0740101481d040c3c040800c0e45241d135203080c5400d031a00803040d0305054202c490304144890095105850301c40095003641e05140c3c5840100402d5041500d0030b44040e81c00d4402c10084d403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 741130944 1250 741129694 741129787
    0x9010f0b01020313060516060e0718020703020a020112090b180624090705090904030f12060e180708060a0501080c060712030b0103020c0111070213110d11 68
    0x44030288011868000d01031800311074202d041c0104800c111300000c869600640c1000da002011341c1190081000f00c4c100380440c1c1d0385111911502c40d0b05980004914030a112074801e64449540540240145156503401103402001e01c9041c400c803181d5680180c00402c1490340494400c2000100002ca04d44e6004a224038104000f406508000194040d401e06451484280307407810500365040d00181d12050300590312400b896482903001500c00c0c041000707166025004021081054403841c000600715101c80055030161300442000344008400f2442c64410f050658641d0b6072901c00b81c840c007030340f240015070402c0d809032402c1c18025200c600604c42c4010074083c1c10048030301190101c0c034001c100e0340d440650302544500d0300140b5075504004103da0740030341c049903442400b2500070403003252400c640c4802c0750080b0100f81e0145500082030502518140300d100d140301600c00201d81403024400000c8050100030f40380310b0107071106202c00300c41800c8914001424001c52a0441d200d4541d10303040b0b2030030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 741132194 1250 741130944 741130961
    0x30b031e0102030f150612150904050a0b0718030f060902180f0a14040f0303141e1308040e041109010b030103202b020a06080907091b1b05010509010f 66
    0x42c00b81c2d0304081880d60b905e1b012107150081007001208156202c1c030b0040c0c4d942041700c1006400000010800c004c000c000300e00a0b491034403514dc0c2403840d4072958000c40e0446140c100040001003894014004510070b004145100c1c1e100c1c01021946000c40e030b000c14900705003160a40c000d42921000d003d030b42c81c0c0300e00203651b0181003441c040050641c0c6541701185030601070409001100012008070074580700e900040e1160500002c85074a40c108004420798004160285a01c4d5462a2000c03074100c180d040c0c421040241c101d06207600705824613001074003000300503100311130f071a1240c0c0380e0200c0c03901c900c18514001e25a540042e03480e589941044141817281c2c00940c0c2240d051203035425402d0352140c0750195048802a2542900110007618024030350170344034003942c48050804000f640581c0855035902c0380040f4401e6400f190b58944c2240141e913a100b0701104980075136a05d030b07461b0a1044800c065514908081c086001c4407580355142120000c0d05c010100340d464103a444112020fa0003080706 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 741133444 1250 741132194 741132211
    0xa0803040e06010f0f120203181c110604020f1210050901090627080d0b03100203040c060203030103050604030e060702120a061d100f0b130c02070909080901030b031e0102030f 77
    0x2601341011000070319500d06c0200902400350302002050a10004010790414015014216030741f411110302e601c1e9024004000100008600100700d144951000c103801e40660b41c00b400c94060541c505040080b0310031500a00b203400e115819406c9603280181c099503011300d6081c0700020f11401c0e14100340c004d070f07038907007141641c030f00c070045d12240086040040e4506600d8200013800e0700c07440c070b50041c440a0004c9107095075151107210003c0d05125096801907000364494003250b44116a03c890590700c1e808240700280175600203030002000300b80110071900303c10400409440c5010803640c00030304400030800b84951698080c0c0b90030001c11680380305450fa000c403d03403070910750404100003956076014038000e40a1002e40b20b04c40c11001480703681020603025001002e10f50744400c0044403100030b143d2400310b00010304c1812000690803427580b042c00c2400360031041492420300407400640281c00104006501440b41c0c09100400302c0550074124500c2c0443c000240c0c0e40c0c14410a40c943c0c0c2c84001e0200d01e03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 741134694 1250 741133444 741133457
    0x30a0e1509010c0f0203070609050c030709240b030c090d02090c07060b0a051e130926030c040905090f0601180f02210408040f0e070f0e090c090a0803040e06010f 71
    0x800c07080c5c0000503078100a902c148003088411035842c0c030b1403e10311022440d9416210701c0310701240c0300e801c540140809590329800015844180750802d030001502c2c0c850f0400d08201040401c0307043e60642e0040c031000e1800b40105a42c42900e0f07000c01e41490003200e0fa4042e201011403100c080102a0282c1042e10341c049030044403041c101400506160f03004092145407100403684007100e512510200352540740024000c11000206081142c404554102c88150040e245040f600f001a0340c0c40699001329441d00c3c43c1d0342458100500c0100512010f0440c4074a032240e09000300713000c041001094007038181e007d0740920004108800c501511500305440c03503441d0050010f500c03801002039a507421403081c21151141501d0300d05280784948125000310380c07001c0b103070030003c40c01d03021002c001c5008403a10b64034600c0c0f80e00400c5044410b5130b031445411341d01022246c04114140e80c100040c00540d4801800040b85039923a8500a00e5680554000851038130400300b000b0b41580c000e40e1007806408a401c118 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 741135944 1250 741134694 741134717
    0x80f0901081807090e011506021c02070308040e0405010207020310061a09030a1b0306021206090a0902150c1002030411030c06030417160807060605130b010212030a0e1509010c 77
    0x981e1992450700500c280c055841816050200c825040711f18500e4280d42c4015840381c980310000d4841a1840214070907045813001c0d8500030b03100082c0403003100e41000c4860308080c101200c4030111a400740c410f0350b41c1c1d07409000050142e507050140020400c04418001346041c030305500001d540e01407908440030a00c06100301c10090310080f8114900c25030210b111178040102126510062140d40c102900c498070110b03104400c2c26445011600540080f20641d0580c0e54500240c8280c03511480c0003034002c5108900744101001460207407510301c9071745040d9001848000c14240803a001181c0507101e9419200d0070342050306040c4460101c02c041505c0c070f41d14611301f0341c640300705c40b01d001480000907120010300d9002c4519600d0702c0600d00c07a07002200c95990362084c101980680110b0188504c58500c0d0b02c0c5110405441e4440d413500c40c00e068025007192096556031103517541000f0304100905031150b11601840e8024003e05a0401041d00400d12a00f0548140f44c00c5696864046040c0404807100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 741137194 1250 741135944 741135991
    0x52505040b30150103061404050c040f0f021201170a050601060e030a021206100506191202090307060f030e15060609030f010c020d11070f0b16080f090108 68
    0x484903200da0108a411050018103009000d000c00d0b4611600385000f8680303200e20480c400c166450480b4041c0509118080c0f034048100000d55003680c0c01001c0c0e40c030440248031181460f820240383c03046a0000068403165585c0d1301d400340d07802280103542d5a004600107100e02c860804280c98000840d000402e02e90440e80c0c0e03101d9039070030180102018000c541540511035501003000d0b400d82a800f900c4040c018419403007082d5500001e13500c0b0a00c0c1d8446803800300d000e05040e01500c0c90724801c50303407a080110401c501500d10b402100d0350180115000c0142200076101041028000c18160391406500074508000408440c0020100105500041d010b03910854400c0c2c140c54020404440c001d0761060303a140024a80180109a101c440d420011480c0b1260b8002c603198130108401d40320081d4003c40429a1511000310340104000100042010300c4508402e03405801c0c031a0807050008d4071403e11303440c0c03420280c200081d0320303568000020b030980c880c0d68020703030b0150072456841115030072002100c1d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 741138444 1250 741137194 741137209
    0x403170301030b27011103010501020c15030a0b030f0a1b06030603050304091806050115020d080f011502030d020f040906091e050a1503290f01030305090d052505040b 73
    0x2501480c0d20741135105101c54000501c0300c103d1207410000c0110501005811860b81c100344256405805078141030343e560305100403092552101c050b0014034654541513210001c4c801001c2d1141c05104840080c10124020002d00d0b030b0403802141e40021300d12840318103404224442e001304081508140302000050303000000d48042c1c520240000c2414440740102d041910318002d4083d0900742480000140a0806010041c0104040e401c0e500d440e40c0c1c00506943d85c44060300c1110070340b03501400421182a604110541301195881900c0c5002d5908102c00c05a8200c0201c07a9540400040c0400c032029042c8a00c01c010301042c00180514003200102d17100c4110001a850601c940b2600003604160040d448247c0005800008c102d00545a04190b100c0c050380740b0092a00e404580c250a180d400c10184062046070147c1c80e00d07610760301b19582252660030254546400c14003005208000542c10303c5241e02c1a0241c0780700c600c810850301c241103808646c03a806180500d103410142d01c40d5031520103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 741139694 1250 741138444 741138451
    0x11030a0c0302011b0b0a05010303030507020c03060f2503020a200d0c0206090a08030d050c13120302150f060a0b18011805060c0f102307031d030403170301030b 70
    0x1c000380580e0158004246001c4c09800051140078a00c00700041b03404036500042c1a06e0103560b041105550b8004140d0740c510619034010391607400000000c0041c2010020b00b0fa2100c4d2102c401180110300f201e8010445800340c403001c000c00c0d0041a405085940003030640c140e41d0049d403441c0001f412100c03030747d6201e141c8850b0201c10003448000030815902e81c0003c640205a0181100c0600d6543d818480d45070340100301e10504240c1003c02107000c04d2034810903035400201180c2d0188000d4501b10540c0001c0e8109102101503014085140b039032340c884080054851600c40501d01e4891500d041000075005403a044064210028000c520004050400b1030f490f543c2c003800c1904142c1c00381c00350301d8000245d540c84643d01881c0086d00c040c0000c0d000c100b5881a14200e802c482c2071140038248030007511810501d50100c030800e8104003c10b211a00c04580d0400000d040c0081c1010038a9065070010b100d00148100b143e00004040041000314004c107106074160300f04440c00c650555541c2c40c500b00018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 741140944 1250 741139694 741139697
    0x80c1c0e060f22053c0306010e180a0c05030d020a03020d050a050903120a0816080423011406031011041710021c0e0d0c030f1b06050411030a0c030201 66
    0x240c40e081c1000c4040140c600181000800c0450005d49840f828020352006484070078035482418a00c2140c07002c00b40440101401c0280946000d030708015502c180d03003400900d90241c5400c4405407030703040d000a00030002400c0c0603041e40042e0342e0401080c14070700440300b1642411980f100740c03101c000c2076010070030b01c044014501d0400d9030b540d0910802c0303c080c040d0500c11641405012090f140180c0000010003007580380f5201d0314029941e00102002c45821210dc1d00003243c140b000140006500070f00c2c049841150b000005144444098540e08490480c5160400701101d5002d00c55030f407500708008003500c00ca80c2020701800403014500c80f05c5d400780b0b104d0ba680e0720780c4021a1001151013070000340c1000680407821921002981144600d0080c2d10070b103180041d103001402a020b15002c5a02c0c403488030315440311907140c04180d03000c0b100035107080206130410412032924075411007903019040700076014180105250429050040112100ca00c40307c0c4280d0041d4800d10000c1c800301c2c1c2000c1180e809 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 741142194 1250 741140944 741140977
    0xf12060402190b0c0d020c0a0303020601270e1e030406021c0201091b0f050906010e010c060b060a0c050c100219050705060705100e0102040f030f080c1c0e060f 70
    0x805426807441c004035000070700c0d001801309460320304001c00603000701e10030710580c02c032105040810180306030340c138080c040900145c01610062244850748940d03010300c80d501100a020b0944c20300c40f808100c0d448481241b5054101e0f02410b40300141c194404600d800d20344000d10302e070030720b0554040c0d80c800c0311210719141c4c0c600014590201500039481048010b8004038a071010b000c080520f10b1000c81180902c501d000740d4a0380c00f0441d8104030341802d01c144010307120741802c1902c020054519400b4030a0846180b602d802d2411441d45400c409000106103a8950a402c1843e03460098103003031405207418040c0b140141600d42055001404044d0042c0140b0035031a5180c43d8240907003807078140e401c0701da00410001000010482c0c005030310014054407003820400034110070401c0d0f0903403049101d5026110b15000c818000310340440c06840015129080080c680680708131114140340f290030300840c481c240860210256600a0190480d030f40301260024545491000f494055000315448c40c5a00081c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 741143444 1250 741142194 741142219
    0x90203090c0409022704030f0f050a0305060a090c0903260406121401030b091509030d0c02030d150302031513061d06010b1306081003120216140f12060402 68
    0x40c2e80000c4a030f602080c01701c900400c000d20074521140e2500b035030100d0020b1801300e01482010f1080641540805080d590640b0741000c62104501815000e04000d500880c0318500242010340c80c0f0425500021586800b0070079807440c2840021104c0e40d03515801c01070041c082d2650002c0019049800b0b40e5420f003003905041d0540c800c0240180b0485850481c14850800044184810310320314601c1101c141c4104c41c4401503565030507205000c00c0d1840f42990780244101130703603c2c2c020b81240364480b4252040320f041001c031450a0003507440d85503604000520f541001c1c0298241800703000150411400e491101d42081e03940b0001c4071344039250141840d80d5401c8081c9104042a440c3d20401504908031807071561a41c2500310300d03038405200b9207000d0b0a132500009400380030b02071451089442c1841600c00c0e42c590345603004000705c01b91040d000c43c061001400100b120f07002480010b4915002c04110b01c0100100740144c420400c8c861511800e250483c9184000e00001c6240d441641990605650304 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 741144694 1250 741143444 741143449
    0xa02030403050c0a050a110118140402121501020d0804030e01050f07061a0108010f0303050403170405030303090a17030f041101140c0105040b010b070b01060302032a03060406090203090c040902 85
    0x841d10684024004c011410044c40030002e5035161490060301407254039410702c801901c3c402d19000d01c148444404002c20001a2411208104001c00240015290800302e40598188100c200d402000c13031800c180c040d000659040214414402d22818010700c01e08107500c0c0640301c19000d01c1d00030b0400400080b54004588203d041e110904d511041c1404208a6056800c003556840303c110b9000860020001480c80199401d0300b003200d405444030352030203056844842502d84240c2080b802c0141c07c100000d81510104001d40c46014250094000f406584c0f500411400851240603880b43c0e00b8410300282606203112503400540c00714200140114050041c1e5007808900c0c10041d03207100101e4000e0f03207850103400c280d10a42c840d01c550340503a80c075013081e80600e005e0540090804001c0d14014070019000340e000b160800009501d00311068002000005031007100070066039031850100034020107051601904003e484201000e50641c038102c0c010543e1841c50502040c0320359201d900000564 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 741145944 1250 741144694 741144697
    0x351602030a0b070203071406190504080705070308031f060e01030905010f0c0e0a0e0906070c0309030c0f03031101090809010c03121404030f020606010c12120e0606010f030605090a0203040305 84
    0x150b510071440c640510f0300750800394480d0002c0000f901d40d00840c02100c90303280030104e000b0b40700707240d000d0504400c6140d998000000b0b1200501c03c4400ea00101300b9440031440401885000314400c29145507240350140007181418170340d105e400313180c25034120103102050b008042501d203502c1c02c0c41c0000c0e40740018140103000d080c2802d80d00c0380c010324020b11400c0203a408521009012000e8807011040c030b9940714101c80c1b042c4c0031164000d16400c40d50200d80c2c9240301d9421004424020714180606507182d48a00c8084007090f805142c0d000c640d4030040042540101e4941001081d0340e000304075171011510350b0741e580e00c241501541005241d072500d1f410140501d14000384550703204410068980600144041c038071090760180e002c0b0f0341421404001900c0094040c1c171410060f520405d0440f001da0302c1d42c0c0c107000c10480c54014420320301944040014103110340c1c2106100600100032a062040024060140c4044007008140c1020360a02a68503038800440e0000d01d503020051392a0360303034202141d0b203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 741147194 1250 741145944 741145963
    0x7021501050904140319030f0c08090307020904050f07060503190c0c031103131d0603030403030c0204020901052809060c02010507080901090b040f150314070305071b35160203 77
    0x2100005805544059248c0c1c00038235001c0107140c0801c1100188030082d16034200485000d401640100142401414542d0103290854812001c4900d42010000090b00305107070f83c0c01c045c0014501108001e070348100c0c07803030111110401c50010020888410002009a9109840078091051111480405003070800865608440d0b030888c1d818000d0300c5001c1d03290b45100701c1e8032210908034170102103045482c01204460840c1e500d81c0762265541d98540c04c1c00b01a400c5901c025060150a100d4002040046d400c0360211941518190040c1d0102d440090310301c005980060040280803104180107076008012100b00642000495032507001c5803004a540c49a940c111140d01c0e400441c0c0010020400300072030040d5820500b0354802514607000460840300f00303410f070640160b060008902c40d82d01990159802c950940b90000c60740c454140941030520110404440500e040c800020070b03040041c07030460944200c59a81e940c0800c2c80310300d80c003a50040e03036581c503110000903c00c042150b03420000f0004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 741148444 1250 741147194 741147217
    0x203030d0914010c02060603010606020316030f03060302040906020c0f0607050f0c010b0d0c06030605010302070c060309051510030c080c0f090c0919083a170f070215010509041403 79
    0x400c60b000f9000031b440b00410740c3d07514021742c01c12401156242c0007000b6100e8810000d0010865034030b8030303141120310360b0901c1020400d02d9528a0040096100c60003920300543c007890700540d0b2503517031840746407a10ba104101152240c10000038400d10a9010045507017000e00050004d44401d03442d412107004080c2203150ba544a04803102480030841030071241422141191000c00c42c207070b80c0c3c0c00107500703034401d05000500c18100f000d1709110303e500a0380402e902c10b0280b4101c596482051019248031001a00c40c10741c1001e8810040080102d41c0c1c0d17945020b86815030240c11b1011120001c144004640b1215074881c0701140e00041688200409440c6000b0380145001482d64030407618400e28441c50003002040d00a100c07204c2c00c406507031203c400103d8203203101041c9001d00380e492003800340202000d4070b04008003108511540240d40b80742e540035951402203104142884c0d0006442c001c2c5040e130404070344080304d004110540da900d120550082c1c21003c45900856113074030650039440759000c143da = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 741149694 1250 741148444 741148451
    0x50a030b061305040201020d051b010f0e0d170a051801090c0f35030c030f0316081311060f031510020307050606040c020f121e070203030d091401 64
    0xc0c40300180c556809031030103403411055003500c0c1102e0800c0c0d6a0858010340941e2190009005440c0306100a014030b1002181221443c01801c0c1000d0a4424803900e20700a0341d21030120820031841803044940c00803541c01c080144081d14491600210170082541c003000350343d2030004d41d84040ca4608501c400f4421002008544c03600d26088170510003c3c00b0303500321900041c0e404a4808121703000241c0c466640c1c400048584095400c00c000d40e074508500020b035001c02d200480300b40c0c0e020406480b41e200740c01d01d420707181c1c9000710f46810748110420503a0108070750882441401d110302c8081c00001034125580d0345409004c20041103481c440c42e86006100c2600104010030900400102800000102c98070982100140c404980e02e010b034bd40060601d4100c40b010911510f859409966000f10b180142c0f5a5464880c102c241452181002442d0703914000400b01c4450000340c840c1a2400000701205040c002650003113941c07030054116070000301d5900c0d03000c032003840460491041c8503001e000090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 741150944 1250 741149694 741149699
    0xb090418030801091401030206090f0a08070e0a0b060a090b180d05010207050d050918040c0e0405070f061403011e1701091a0708070c2f030d0305040b0a0f0204050a 72
    0x1002102c00748030341c401403440c00368111503060000e41041d040b280c0050481d82082c0d201410841440401404954083c043d450700082550042c040d08004007203070b0402d040d980c503000c00140c051303400154031544906070402c1300e0714085400502000039145400c582c2c1e619040c490704003001751002c041101b98000300c503c600f01c0401005400030702055200c1c009448040b000b514041d5640d001711082540d0280301403400c01890300103400c980d0351041c01788451188040c2c0e100404040080181c03001e540315000350f10248070320000e03032903044028241c49c5003c0c01c084e000d0b44400c1034180810b0047c10300e880300464241c0400d05003900400045c00505c4900103c031b001c44020135000741030315081121009401341d0b8814140a905070185c0c800c6809490342c2065039104038080782d9410340d1100480304034050408050045854840c6641c2c0da045003003460003541d680b041010b281100800c0341c030040604001c100800541c00310100b44c2c0100104c41e02050312066184450040c1c0a150002030700700304050b000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 741152194 1250 741150944 741150947
    0xd060927030e030601121a010b041809080c030403020102074b060315091401090522030206010f0e0412110705041104050f0909031e040e040f02010201060b0408070b09041803 76
    0x3080b46e2601c52031800e007c41d84035a5002c90f44202c24815080280c1c070a000800690a111541e40c0e01e101c00140000b0390214076070b4404802c4c0c3c11140010740e1513440410280708558040180748060210040f80b01c000f02c0c1012000300f10050001c491440d0b010964840300e034100d5202654000c1341c418440d0503200c440d00c4020081c01090460009009034881000000d98845c00c2e1240301c3e00084210004600b0381e080442f010090480548032805070b200242d100c0c20604010025000410722a9000d44000d525104280c1d24151480d0031002800c51200140f000064042540101d4203105080c01e082c2c010301a181142002103c1d84a250018103000141640000ca10000c10503035804030350002c6248640b100b400002030040710039000c1c0364010403260030450089411102000d582e01021031070240c543c40082e100c910240d404582c90405620b25004540e020b01403000509080c607001350a0510b4010150380da04580d00c00c00368054800921202140c0b2030360442545194000360301500c42005180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 741153444 1250 741152194 741152219
    0x20a03021c0c060c08070f0302071a0310091109011d0a080c0901090207080409050c040302060a030c03110a0f0c0512040e010303030f0b010512090a0b0901020d060927030e030601 78
    0x11030785142e5041c0003099050103240003180c55504042c03803908152842d07841c4601c0c030740040c8055080d44a500000500700c26510404241130101380900d54403405c18241803400c1c0d03003d5800c0301c5481400c0c50003074400c106001c801d0f00c501e10401d10700f204400f8642c0449100044041b28025081017223541c022178517040000d807542c07500790f040c0e0b241074681e03176250301080490017505402030170400100001c000441807604126001001070199601d065a00c0d40000c54561100b418500400d84500c403c1007900c1d0140f20f0303c40101d140c420720529101c0ca02c8401000008032504000c1840b03a56012001444070401c03031481021184088155038a840300f4003402c65050074030080700080d003440a04030528006004070b000104044e100c20b820b00f6030231040407103c040c0060414000e4415403d244000c14240300c0303204c0c0950380000c00141d44007030320081c850544450307801160003241881940c171401d0000c200054809048000210689221441c1c11603402c001c2c982d03000d032300d0303c02c0c1c00010070b00c25041079 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 741154694 1250 741153444 741153499
    0x280e030d0b03120c060412030213030b071706090705070303091a091006080d0c020d150b0f060304020a050609061b07091d06060609010302070c0306060e010806160c020a0302 76
    0x40c120380610700e141c42c06165034071406644074019040300e00403030000341645100c03007d190a14100541406480c0d401000000019801034550030404410701c624250004c104010482c01c18000520610380400400d0f12080c001d0a81010440c0005004003071610a6008501c0c0c40c5c0d100b40780c608807595100401490080c00d40c0d048201d80601e0300802c0480265119010455450740c0140c5004a91400c06848403048001c0c2640c0006002514100044c40c08160101c0207900001c001070000b107000034480102080c883d032a0081508000740805641c0d048007083c11100103c44003540c50844038040307091806141d640d202d0035004410750b00c280f1718000c1044c40c117132081c820b01081450070000c80701c40744481c05a00b40348070350482404940c582c10800000c004014049c1400352501840f43c0d15440409101e80c03041d20960368404c02407040769482440d45006000385070080009080102d24840c5411351200031005003c0304031709200440d141e60054500654008048c041e03110030140340c01c143c415044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 741155944 1250 741154694 741154699
    0x30d060803070b3301110f010c0f030b0303090d140a0807030f0302090d020111011b1808060c1210030c12050f06090703081e04170d08280e030d0b 64
    0x200080c0400400075940550807444601c01800c3c40134412400d0340c5401e02c815040c2c1080000703c001c60031800200881403011080000018200040c42070041c03510585400306000c05080c448040401d03134000054450840c412500340b10141103a18004041e6101084004001d01643c480039052050690140c03a80f81d0280e00d8030303520b0b00180b130f804504074480c025005a1001038129402d015500c5002e490b60100e03141c02c000100000b24800c400a41c40c822100342000605100c0c020351514076200900d00104045001085141071100304800c160107201e2001c0c0003ca0ba0070001a82007040013144030066400042c85421182c035150300304000303080207400385d9891007102d8603d4038a24000480a11402e141c0e00030300324031415561110354070351281240c0300d03050404c01c40800000290100600080010b96402032024161240150400d01c04c48110014403d400c01000300600d0070f00b18050000d46c02046d2021141d014401040003460044403607a064030000c540c01280103095844078214901c03c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 741157194 1250 741155944 741155963
    0xa08040602280303020901030b030f0703020f04020f032a0703030c080906070e0f0d0c1d0c0405030606220501030813121e030207030f0b16080601140903030d06080307 73
    0x7540320840041140c2002c1d0201044031038610200c1c1c400e901401c5452070502d400700d816008500000e18100c82180007020326041003034100114a44000c50b502d04074000d41d015818900580301c450803501008012039401e08040c10604108a480161032000001c21440d40b900c0368120705004009089107104140818680c1000c210801400955944031703003030943d82c41c80d44456500602c6601d8100300c4500ea042456a402c40c400100c040b0700c00009003c0341d045030108809442081c100712100600490100201080140402e40300814403540c06101a106c2112190603000d100e410304041307003d048091407500d8004010005100010100d040b4100c540809464032041c9504c942d550000009002c95001c4502d441c05d0400c462843c002707c0c2c001e00503900c410707650352102c0d8040c01445e00c04898101318101041008200c15960003150036071854692046d14002d0001b0f4002e24052050402030040420300701e11035982081105e422000b10b05050100a030b480c45940d80e240c1201704100d030449003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 741158444 1250 741157194 741157213
    0x222408150d06150b03011203020c101403041a090d02010b15090411041a130f12140309040c030b030c03150114040f090b04171303081b0a08040602 64
    0x15504100804900c0080040c0d072440e8042d035902004010070001c1e002c0f1400d8003900041c221800304051030003131140000e00303264002c0b58a80281496240038000e03115040401c41110b410394440c4000e1f10401580d21300503581c0d2283e091000309000c6099980000f41642003c00c4090200401c0d9407441c42895002440a807140d031003005008000c0b91903400c84903034107001e011035501d420340214506c401c80d807100525050311031500042c003401e40000c040c03010200140010740e100b400c0204c5402400c0c0c1201144100e400c1c82800a0b0900d80c2d0705020b042d861100038244504581481100d030060801401040346c003c111402902804001c46011710900480c000e402c594107021518503207803903610300c5401a80e82032074122055201d07144032440d001680e030060140501158072441745450701500d00d006a40c135041c030701160364891081000da40000140200a520005050100140c0398004185901c500400451084c05140d009011040e82f14080c802410b0003039880c001e00c15510740d60300341d410031032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 741159694 1250 741158444 741158461
    0xf0304050a11100516081e220b0d09030905040c0c0c08010c0e101704080c0f120906160503030a020c0d021218030c1305150102060c222408 61
    0x40800794840072901c200b0110180903990501c0300d000910980f505030610060100c596040300c00010594558400043c0d52214400034641514080c2c8234115003201c0103040a00d002d10600070700b070260a07900e468490100800d0f01483c07104010700700c040c1082115000d200c0009102c1c12034142c0c151020742c071100b004614407c041c041c1440c001c81d0382d2614601042d104017070140c1d4184c241b115200300000244d032003a20030b0003c94540c0c025401040b40541300c80040d0035440c01c0c07080810300022503600c035405000346128030f102980d8008004903001c1da1103e0200400c1c01d00d15020b420002c0050100004101001c1810b50103000140d00600c21141c40c003807124000d81e96000940340204d28850240320300c81580b150368200c0014003a01400752038066018601056044801c4006600896158820040d900414101c43d03520754500344000d1105003412507003015984911003096035000031441c585d0340c03000c0c06031890100822140c0f42c00c064482110781c01540d036a540d00345031400941a0004140b00c0d2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 741160944 1250 741159694 741159709
    0x210d0207081c0b010e120a1113050c1b0c0901090e030d06090f1b050f0d2c01110f031603060308070605060307360605040e0a020a17031603050f0304050a11 68
    0x5500300b002021f007040c094aa0101440908220b56400101ca45a1b1b9224456a0084602030300036003c11588807041200c4212000c02c500e05260308580c01030b80c01103115501c08441038112841d0b004c000802981500c8150709522440e50410b00c1036042000004480f6150b502c4292060b00d00401040181314180e1001030b02d880109079900098003e01c6264600c000c24401404110801cac0c3d00050400500c5401101012081c41c5905c02150704040c0c40241240a0240c0203c010004620328030349800c0c0c007107061306404060b1001c903000300300440c0225003600075405a4061030304580d2143d02c2c1c180900e00a00505822a2042d005e4003c900b8005035150b0003192019404025650b05001700841908c409240c100b00d048404403146c8400001400f900c40344100040f500c10711003c1e040c002c41c5401405803aa2090340601210040d0501d001d021980100039a41d403068a56005103492020313040848041c050081501700100000041c001088400030b80602801c1c031501c1d140e800e903107502c000c00020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 741162194 1250 741160944 741160969
    0xf0305060103021f0c0615050405190f062105011113030614063304080708011811062b0606030b12030301060f020703050a060b03210d0207081c0b010e 66
    0x413514240c1700500152503a00a000004901d84408a015a840b0009803d580040d107105114030700d0102c018000f86018001e400d5000d008140030f0003a05d2500c40100c0981481800080000c1b401c00d1805003004000c1d005120155000c0d19855240e010039202400607400511040300e9203464104a00c1c640b1894100c4075108050003003904941b0030713484000d1405404002a4103410017882c1600400c0100d0303105c058000342c0400e0300180035007030a0034038940c04c403202000e00c003007052440a2359400090025082d008030510603251030b51119041000c410600307200120b02c84000d00814240c0204451a50143c0c049580d01e81d810300c802da1419042c0002c3d14886154904250410001800028081c070310f40d0462040d03e10403036940760b60b01e803030ba02d0618081d51800c582c0f050308e81c5800012032504204210804000c00c0028500c0e2603108000042e501c40c80940c8100150041030398018090180141c07101c0d040c6503200f07051000074158021005100c0c2d801d440c0d012580d054001c0fa114101481c61000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 741163444 1250 741162194 741162197
    0x1c05031b0f06041e0f1202030307020c0a0e0703021e0c160905101e081203040c06080118110706020a0305010501031802061b1c020a0b0c0307080711070f0305060103021f 74
    0x4000f5140d80d0342540806444d09482a00a03041c000c00056031035810100c000740541d01958813410000d1000b402d000300240064820304040f5818054201210605a00511030307040050365110260211407808a001401070303203120001c101034140000c0411210b400450800002c0c02c01034540d03141408039281a82e075100c9400e42c4050130b04c000e94005030f04070300c0d02c94008a180e5480d950b9042580c40c124011441c8100d0300404401d0104012040d400380b4054070260404180b00c1d0305008119108860140001034200d0719405805814841d620442c0c10180e00444290340d18002c1481c041c026043c01e20995001030301c0d12980458023000d02c2ca8008a041d4001c0405241c0050091a100300c49440400b50200f0b000c3ca0100e120001031409021209900300c1d00074000c01c2c00e01e414903031081c2038018000c20750088200100041a9400f1440552020041c01c024901e003046403c0d5500d003c0385a00f20380c0144030703c4900030080c844000f405c0c2d4101c0f13100311540c401c030054a184088003561b04484110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 741164694 1250 741163444 741163463
    0x30d0c0921150e0c0f1504140f0f130b01091a071209050d02010e030304050d1b051c061d06070e1302070209130f0203030409051e010302030c1c05031b0f0604 69
    0x4c001c5c0341880e49000e1501000346a85000920726410210070790041d4000a001d1074a12807161131801d06042d00e5030540c80c100c0c5c0155646c4200404142030301400000c0452076591446800380c168000c8a001740644481c2c0c04043d1400341d084103c040c1684040400d40705034002190510119101d0101e82c015074401130400122050740c0d50065900300e5410364140c4d1300d800144004140c03030700c0e800d00d0030042a0283d403035980c000788905072409150744a6000749004800501c40761004940c1100c007d81c225500c24000039040072212507000b40d100c0400d00381400c0d40920300a100049900050744d0003032007002c0710040c1c5041c49030a0007008a10443c0d0700290030080d1900050308120384c1100004041c0e015030200da1020b5419400241141d00c00c0c0c02410046948005201008503030036440801d9000010000d400b9504580000760354408400249108001d5031040003041040d416040c200f0540c040100c0e500e81c06000700d02400c140d45801482040d1040410310035014000080c540d004175003290004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 741165944 1250 741164694 741164713
    0x1020a0f02100519150b070c050109080a020f0d03020c190501021e0d0522060807260f07020c0423091b013501030303050a020c030d0c0921150e 63
    0x2d5010340400c8000c004240c000c4034000820486c42c80040c841c95100c0d6450704c1d02d00d4100b9001400d00000d07a0042d8004d940543c0e403510050b160070411400781403040744c200341e68403002e103800c81c82c020058a605401c00021a00f030b40250081840c52002e0300e109809850050017003d080014101c0340f0600c5440d6580b10f0448010414060002046402c844d642603100c2a0f45180c4480c4820780203074031000004029104001105070701c1080000d0b1003952020248070b0007014088015a0f0300007901001d0310702150310104014500802160003040c10180041c889400344110180c0c00681c08168200c1100d9090001400f28401003646c4812140d040c11002058041000440f285a1145e0101c0c45a500c800e40c1ca80300040c2c04116580c000c0c5440ca42080ba80d030540c40c0c01425220040d0035001040e006100c641c03202c210120a41d2400303280b0400002d02000007650880f10182540c0c41080da84401243d000040d10390b000a804e80715001355a2007406240701c4540c0d1040f030303001c001c185006030000c00d040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 741167194 1250 741165944 741165991
    0xc03050d0209040b06030f0103060c0c12142a0d0503060612092b1d03070902090f150d1406010f0c14060a0b01030b04060f180e01020a0f021005 63
    0x902940200a400001d0b0070380c07091302248241e40240c0b1100200c0c90a080104200a918040c0d05000402e034541001d00000075034031862101807003054681801138503510800300c0c002c1072051f25074543c0d81580000c0a400e00002d61070881103400001c001d240140c012412816004000b107070700070103000c1c0100e4a400500b0b02c541d44040c001030061141c03030085000f0720b038403440c40c5105c280c113a8154441441da2410b04400141841548118a0060000384080146160760108a0381e08480d080714015a4941e500800038003036200c080701c0700394084030903201111810304100192003821180c2908001c6007410841c40b250302d203021102940050124160305840d240f0074140c0418481c4280140c510b0b809a0340c0b0340605102c402c4899605203035030b604448402d580d1500030002d915030251010044a400c002000100b48100d0240e9203841d10000503108441641d98070184c0040c0b0b0b140700854035805c007050000d0400ca0000403020041c4a01540911408464030415010740480c107030788810181c03004030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 741168444 1250 741167194 741167197
    0xd0b130b01180b22030203101a090402130e01020d020408010b130905060a0b04021303141015060c080c0a0b0103020406090b010207090c0e03070b1224011d0324070c03050d02 76
    0x59130300340290200000001078800700302180040c07160210209400080624950710030712a9400144112520401d10026880c0c0c44400d240346078640034041380d03800d40821014003a2040d58803496040344001800039240b40103500c865108903044a40100040000541806440700701801400136085140030410b030790310030350103080e403900042c2c009414552020064540f10416034800d40701400701d030300c080c00541414403281d9407c450b0088104003a1190208522650303003140542001e001e58100f0000501100206a40802000e00129000070415181c80c1c001d00c002848100c0c041c40c20040081181055800303618042c000c1a8010b1622510308480c203806081c0074107404041c0a501d104a0b165074034184040d030040d165480c0c0850b51654000451052090001c0443c080505c041d101c003d4022022031688078082800d00e0728604543c0404203007440d0074210b0503025071520801c9003001c139400780090090000501160724960300e98078000d041d181c00d000c4420050020380100f1030311580720803550 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 741169694 1250 741168444 741168487
    0x5070c0b0a0c0f14060a151203090b03010f0602010501141c021201060e04110a030203070311061b0a05070b0c0a030302031b0313151e020d0b130b01180b 67
    0x1600c40d82c544a20340720111140b0b091107050304c42031119100709560032401c10803190051080d0710204040000c01d60030500f102c5180c011628000c045000c00014144626031103005003202a907025035a584d1207100c00b240310401d12601c2c01650800b000000e040c05406509045a140501144101e0000c42a0284808079071541241e10500481c4a134049403000d104003401390544a05040c0e40d4282410300c0d0191758000c02115105017642e00041c8016200495043d003140c0c2c0c00b0000e40c07150603500c40001d2485c022070100003410314102107035074540c0c0c0000880c50300c0c9a0140003a54000354446815041074404d104e510803c42e8400454440000c3c400c0c1d0042d9441050340545900100c0742c4440014030f0342c0140d4404d03009001d220020014081040e0124107443c1c1c00b40e20400c101a1844400800c1d02041400e2014559010600780906075440c1c214002c482001004090328841081c6084014a42c00300d03001c2c0091440320141c94801613445900080c0c403103110040341810b0307814084e2121544040e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 741170944 1250 741169694 741169697
    0x7080106050301063002070204050a0b0a05060d021926070503190605101713021804030c02030f0304181a0409030903080f070b060f0d02190803071b050105070c0b0a 72
    0x103022004070708052501d0f0340984190385c0541c2e582c00c203004110540e4009000c00220700e00d881c24492099960728041360440340160b83c09511008a103007180005d00460520f941c41d055041d151108259002ca140d800c40c52260500c86010b2580002c1d00d40c5d5039004036040008107900300302140c0041041c0940072020f100c00200030400707540381c80100e00d20301004005107000c00c90038444075074049540300042d94809503100e1101800b1300c2c9900041d0b1702d400300f4a04006051143c8000c207061512500c03440a941c0d40217002c52304400c446441080d07036075110340704a26403400c6441c206500304000d80640c08a0b900d510744036804070014181000b0040400c65011024450900d000000081000c0c016081c10030440c460741e0780390304250501e43c01c455002404180301e41d040b2600c00001d542e8004070366035045e0701038401c1e11103161401146400000c00d81c100160790310000c183c1000300300f0865100d0441112070141204001e6544005441d0303030249160061403007200f110b0a021142e00d5401900200f0400d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 741172194 1250 741170944 741170987
    0x90509180307081305010c030e060f0c011a1302070506041106120106020102071704180e010213080a1103010b03030706020d060b0301060203191d040b0f09090d080708010605030106 79
    0x110001e00e1039020703a10880d00700d60081600082c080150714140010a030030f080800400e08a0b42e0006c04c1c2c1054943c03040d1060a001c42c1101207403a85800b030b41d40789060403008002c4182542d1801c440d106004101a206100c0c0211a8200000900a4507280c541c441c0081003aa01c03265200701048041c0403940780c105805009038500000100002c41c001c189603000180e80d01c96500340404422108114401c0c0280104000c01c05014900b240c014580002e81d400508201e02c5180c02d4003911032041001d000c103170f25140c00f080042c00030a640403030034418402074505041510506080ea00ca4210b200e516070403c5c426400840c80da50000c1c111b421600100140c510b0320780e034004410f0f070000c0c0c00c02030040e480410400341c0310849181800e104d82c01130034961107902907085012043d007040748a00c3c0c041ca1700c070006030b041600c0b600b0242d6402c0400500035415840e09403800d581e01c880c03020290300092030710400300e00014001c201e2a4140c0d02d056407000e195a0801c4e5065419100494203a17000416 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 741173444 1250 741172194 741172231
    0x24050307090f141e07020a170a020c060409020d0b0a0b1b01180f03080a0b09150409050a03050310060f0c03082d18070810090206130b1e0901090509 65
    0x2003030819a2181500104c45420075541e2280d040d94140d0080040c0103550002034128045604500c441d9940107540060503501d1982c02d504a04003941a0314581e0800c9000c10041050946500906a2280100d130708101d054001e000300300a45443e4400e00d00c2614007040b800f0440707204420303000f040c051506c00105807000102c064041012000f00180d0f81103010781d5414040660004441da00715078405400d1040003082c0c40000d4000307a0151020580e03c44a490030305640e201d58015060664010040e50f11009607800c0c050003691048400c2c408804403a032020036154001d084031a0031441c690348a011003126542c00341d803001005400005940c40358508041c10180a074400204003100b0780030300045061003101c51410885020701840d840d044404240824000024000f82610801d00041003200307103800821218403031601c4c0007880c3c0403002404202c00c130b50f1100070451076030140c01004503920303074100104050155407031880c001b400c3d9990420030b5103048031200c2d0300451101c200030395050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 741174694 1250 741173444 741173471
    0xa03020d080f160b1806042a0b030c03150102060103030507080f1605011b02010b090604150806040c060212040302011b0312020c060f06030d0507150603140124050307090f 75
    0x61281402c80e1030500241c10005c1181c600300003001c8076a00b0200070803044c101507840102d10781c9014403a8a083c1c01460b60b2254040c00040c0c120b0050520208103035482c00c1c6442e03084255403003201e203800e0b500d482c0b0110315a039510001d200d6048940513641c0038108881603540e491641c1c003140c400c59043c0360074007400501500c00d1032448103a510130000080d907071148403000194841804444015a4075148000401d61035400c0040d901520481d000a550103190f0054078480000c3c0d0018403441c030814040004010740d5402e681c00f0b8401d80c5c1c00710340c00e419030b0351400031051242d80030085c00682002c0710311650003604201035a82d28440c0c18a00fa0340180e0200e0f0104a0b0480c03012464180e00620030300c188100b0564029070809802c0e03001d030085800b2603030054050f20810000500c106803803c3d16440b4120250701010241d44c1c420b0400c1001c0400008041c0a080401060106001950045456455020424001c446014019104c60383c68000ca450042c9512004001c416868607003005449 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 741175944 1250 741174694 741174727
    0x6050304080d240503010b0a17010e0a03050a09080607050406200d09050f0402031513060e070c0b0a0608211312140f070510051201230a03020d080f 65
    0x10f010071480340603da03219403903190f0940c244d12003402a4074010724081c068691400c04070540b6800b104601d810780384030721200e004000b11121050700703000e468010b1041540c014000d002800302550358141268456640030744820040d1100c4022070410001080080e000e140900f030900040c090300f102c16030b00c13003c0e0075080c604401c002c4400030f85d00b884148103038a03194002d8600b9020548013181545010b41036044481d50111183d071060b01101c1980314081c08a80024024003c0c0129002550601c85005000b01514030070480c0d02056042c00291013424034440c80d812292610300501c02031405401e07a0801d070410241d13140d6002e00800c69540640340c42c03150600102151fa2820403040b9141c10302c603a82d038035041d010615580005060301c07100c050003d104415a10b040720405425a2505001d8585100e858800a5a02501d100014103844444900b943e94680394100301680c0030f241e400c2140c40d4225020007940020101380003408621200081c01100303030080c909610740212401c2d5100407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 741177194 1250 741175944 741175961
    0xc120e0f04090812180714060d0e010e16030b0a1509110d0506092a040e011e0b030c030a0c050c190302120c10110405031b0f0108060d030e0301021c1b08040c06050304080d 75
    0x80703a443d41c2650cc07041070b0800051560b0003a0490041d240ca04507500d451400038080d00ba400305a03140c600003c0f2612007000150f00809050004000400c10b466041d4271a41154800c681c02515000c00540740e418260403c600c03d0b980300c0240303003880016507400003015120780e401c51194281804041810704441e6041800b13844105950308083c105c50659000c004400d400014941009200b4015950301d138206480c0c002c00046c0700481e03000c81c480c9044580d03004403440c1421511441100302c002845c1e101c001040c05000307a0a840803030401002e010864841c4441a030f04540c40007120340041103403070b480034242030f1042500515003070f65107000a28010015000001c1503901c081040c1c00c510302801c420407060001c0c00c040c0079a03c3c214000a920504850b006410b02407400640d40c2c1654003035040300c01d14800c00007441c0082c01507480041c010300070f81e031450030313904059454a16454010200ca82c030503603002079546d0019082c444101c40d1908080c20480e840b40702070004001c0c007103407401903800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 741178444 1250 741177194 741177221
    0xd0509010e070f1a09030607030e0a0807060e0106080d17060f180709140105040e07120608030a0207090504020622030c060e0108070c120e0f04090812180714060d 71
    0x2068180070041d01144c503000000700038800c0800c80c0c0031043d00c0208a0a51054103400c00144039070018400c0e07070500c581528014520200025800c0400c0041c2c0c0c80500c4000e00400200701040d1070705e00131030341c035541c2a045070040707070050b2000c49041c1605c10505910000c01340c80140540f0703920000c500c400104c05460914a5404020088100e1340b103007100e4001c0c04a861040e2283c280400040e146100790f01a4640081242c00001c2e1518007800100700c18445070a01000200eaa403000607849802c14080e0740c00502941100052920460140c1d5000b150005e24043c40c0a80c4030540c480515202282031100d103c0141000001c1000030110748000e020076110441d004113504001840e10400402c0c00d000c3c040c14030031041c00306004403460308058105043c01110070700380c2c000207111407203030340210b0b03603c82d00f421098400c0145003001f40488041c244400b0320f00380c030342841e0f4102e00c80c800e050a8500341e110550170400000d8046021a403c1d00140c500c900d1300c0354003100c010039285001e08084 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 741179694 1250 741178444 741178469
    0x1e0c040207030c0218040f0b09030c0a1103210d0b0d0611090a17061b09040f0209010206060a0b0a050304020f0415051009061d060c030a03091e080d0509010e07 70
    0x1042d428801715010f02d07484040e401016074a0300c0d81d10405810099000a8604c004400010750740700010001c9456109100c01125034036160f920300300d1034404261700420b0007801200000702460280210100b60415124005402c100001c060b840080800c8140c0c0c5138042401000d00380848d0503441001c59122200440c5665007031002c00380841a440c50744101c11240c81c0c3c3e41110380d02c01e00490390a410444020840c280510680300740201402180d49140d0300618080859448000e1075004107044007003a000d07101c041d0383c0d040810140307171168840c4a001c004100901d51441e84140700656210b0b10040c428030000101c200810301b1680c50980d140414055107506010500c1c20440c4944041607514101c082d9904041000300959001048402081d0505a20500650346c041c1510680b0000000701e0352901e01200d8020082c100d140800e40b405503101fa40c802214500758000f030340090f0854400c5140c03c00201c110313802050b00400c0c88206540e0341a48100c15003044c42610000d14240c080380 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 741180944 1250 741179694 741179717
    0xf0f090405060603060102033c040f0e0705070f03032306030c0f210a050a0516060216030305030a1506030c080609060307051c051623031e0c04020703 66
    0x44212003002c1c1201d4402e41003030040200320fa0b400402c54041180542412005804070b407007140710b000b0b410040d10b5642c00610414580488858080c100b200c048101c10b010255460481d8224040240c613403030000340c410410706000c21564800c204130248a0f02e00002c2c0d041c04090024824001140c2e8640202110b2041c014540b6003005441d400139001c035044d5412061180008002c03000340740740141ca402c07a0788450400644280000200681c000c0300b40d0b941d0b2881803500c40d865200800645440b8080c11602041452000400311102c3e0500e0040d00e20f19400d44e00c0994064200070041041152642000b00010340a00d04490041c111900d0110310703641c07002c001030001d003001040c1c2402000c071070080020039a00041c04c081240c2c410f942d10116248800c03a401040c0c01e030032201130417a20079040d502ea81d440c06094800d00321000c054150b0b1175214603950030440c1583c5409141d91540c00310110182c4040709103480c002a014101c1104d0402110b400844d041c0e8000d14015004119080b002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 741182194 1250 741180944 741180949
    0x19080a181203031e0501180e010905030c0304030b01060503090d03020c0a050f07180b0913050a0f0b0f0610021b0a0518010614030708012121120e0307080a0201020f0f09 74
    0x2c15101d81508018060356040402c5501c000c80841f0440b0b030f9241c1c0320390614a0b444000c0d0300100c4115005015640d4035014070350b629540354042d100c04c0700e28208100001801c80e1113603055a0144090201030040180c410704110081e400610805076035000b00181000040c00c1006070249001070703080644281480d04410702e908240d8840d0072080c01b07041c114141c585035283c081c01039000c1d0b181ca66442e83c014550511901c5c003d419040200309200321021081071015680c6001c1c03085014410003032543c0d5621701401204042d044141c2d0159000d4a0800820030a9050340c000001d009024030107156a1440040c3c541c0d10f00160903282c83d45254014807420303910032260640741d8450028249581000c3c50020400c100520407001c8040c070078205000c004511510700094117070019140c031408a03110b05800c1e240d01c0001d03801400304480c0d40e24075a02c0d00f000c0c0140d144011845001d1405c2180b0317a1124081d5a02c01290f980840d582045080c04112004002c3c200c0030940c002001c1d2121001c405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 741183444 1250 741182194 741182231
    0x6062b05040c0609141002031b07080c0d0f0204050603120703121107170310090c170901150e10030605090601080c0102031813150b07030219080a18120303 68
    0x44100101e613601809180c01c1c0c140d499050880545094060700c803154000c03030644c000c22550001000d43e14203401c8070b01800007404001c1d40d04130800c0d520708001e21020002c04101181000700f1039a04454074002503e8a98421644401c000d400d5134805485c039620b8072034030380c4039540480200701096003864104295101c0c1026103861045c50924180854440b419441e00c009400300030a04000001100480701940d40c2c0c4c018000b501d03052040d019580130150002c601d00b070760121010b21580005100400500032030b034900d410191050b604074280740c3c41d2410030700018584842c145014600000041080c40382510a0150034090442c55061601c150f041c11640340110b0f04550060050581400d03904008000070442240d4000740d1101000d0341402408156242030762402e07042100085201304100281256031180d03007aa80c000c0d08840d012203c0c1658400f0140522400b0300040c40c0031030003681441540c1c1100c0000600681d9903d030a0100540248021400692101c04445040540c0c28 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 741184694 1250 741183444 741183449
    0x2812150e09060615031306020430240b130c12050403050301090914010c09060e0406030b0601111504030903120503280b13091e030806062b05040c 64
    0x80140c542e6080280001c1c031021030700d000d081501003000010425540601141d0760185501038400d42d1030350350b13965448100384201c2880003403000d11000010b44280a20703600280721940310a41610b990200f01c80782407080d01d0280110032807580d5200100140d5981d100d030b09500d403d0004041008225940014400703071306200140300c60f9082009000c0001e401a054034190b90307901c01c00040301c1c0c07194101020b0428880c0c0c8005080d501e0070b804070030590307402000718040e42c030741d500d4480344030055400b4001182d0507440007070441002d400104540c4c0d889151121030085004044030001643c050805000410644084001c1005230a080040000d240c44d141e29800442c245181985007503030140001641c510308400c1d214001803001d0030300d40c681713900c2001042c9002d052204803156003c0014004c100c00348003038852082c080760b003504406140140c844903990540e1100c01c281c503046c06000b0303d900620508213200288a01462100c0e0100750003002c031403200b0f480403456040c41d040500303d448154 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 741185944 1250 741184694 741184711
    0x30402030d1103040905060a240908210f0f0a080610030203010e04032d0302030a151220040c031a0909030717131e09022812150e 57
    0x11a030082c040001000781c07011100303448004200340e515100084c0ba52402c54000041254200c0c07030035040c8903040030340180c14141c0e949601002e651102c0e140f955407204a243d020080d001a00300e25201c202c020068810003d4400c2c00360b06240804403e2103d035040603c4400020300302200b042040d150200c03c040c078a011030b050861542d414500c0800e1800ca000300007406002100307a00c0c0200241c03041e500c583e00e0380160f4044c0264500300d02c006029610a41c0c4500c807d030306112040c8104502c00200f130080b206118000304083c04203070b54888084814403900d00f01405c202071241e000d9240d1b4000c2c445010059900007511402c820882280e00d02c442c080c0500400761001002000e000020071202c02d81c0d00401021112000034150680c44d2103030001c445000c1c0e85109000031144804103604080c40c0707500e00c1e044400c50300c41c2c11032000c0303010741045040004100162040c40c1c0c0303008400140c410f0700c249000004488210021401d561845410602c7c51510020410a0f000d034002d10702e4021204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 741187050 1106 741185944 741185957
    0x316090603030806031b1207080105131b03030f03110c0a030c03021c0f030b0f0301090c080f2a19090207030e030c10080901060909050102030402030d 66
    0x103a22044000c101d0781400304100d880c0c08281509580041c61090304504503a4040000a00c1321a02520071405001004640503000b802901d21680084030508440019407030030300020150040c2040481c401c0c0c44050000941c043e920110400342442c000c00c406054038800ca0a41c400d445100c0f6072132007013084040c10917402c5450080000e000f0340907074201107603090a46035210301080c00c071800160305507445e0040a00951081040520203805810b400c01d411010a084418161080e80c0c0607411000800101e00e08003c050252000d03080a0b000c0c41e01c001250014819840f4a145000003680326911225112aa0700008141c542c400c8018507640d1440c4a5000358841131013540002c0890619443e2400c000400072901c0038060a00344420b440385500302d82c51103010b00300c0c00b41c0755203410001070f0300407072405003075062401a4001643c2e0b0800e841054a003032122011102880381 = true := by decide +kernel

theorem cover : BRFrame.Cov 741007194 741187050 := by
  have h0 := BRFrame.cov_init 741007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 741007194 ≤ n) (h2 : n < 741187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
