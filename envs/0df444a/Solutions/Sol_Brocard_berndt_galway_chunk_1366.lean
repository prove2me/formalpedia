-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1366
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:36:13.179867+00:00
-- url     : https://prove2.me/submissions/6a2f9295-206e-4964-ba68-cd8b03c608c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 245503597 ≤ n < 245683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 245504847 1250 245503597 245503669
    0x7120b0f060f060318100608011a030c0105070c030605040b24091303020f060c0415030204050a050f18240906090115020a060f1b05070f0210050d02070f02 68
    0x6050540039100101c017040f01d854000c01d4101d0100e0540045540628562160310003800d0103104000d5994600f1818062401660030850b84c920000741c0203000103142d12004440380d600c84881603d200c8090303c0080f000801a002c3c460103280640d40148441c2000c1d21102a4140f850f408c1003400107074001c003042d170760301d80d4800d45a0005580700201036642c9181006d0741000b0190106d41d8090140400300005095a000036000350750a008805c1440f00035176909a0407031140703001d8164404942a8200722620301000c142c50041006050403180214262030018018420340d41c020300c0954448903461701c0d66800071300404605040361046140d0403d80081074955006014280704400810a112403490080203c0005c0f20744c0800200400d14100c4014401000582d02e03100c000c50342140f00300305142c03154041e60041c0381c1103203400503c45c44c41c3d0700304041d900b0142607130400d001050001d4421312006101416601c0d01480034210317011b00c10700c1044000c640e00d00c0b0840c1c200305042c4281415900c41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 245506097 1250 245504847 245504869
    0x9080703090b070b16050c010c020a06050901020405030a062f040305010f110304060f1b0206041209081b18091b010302030c0a0e0609030703051513021503100807120b0f06 75
    0x303645100300b41010317450445244c0304460358000b2541c20040398004ca00c1d400550480414000c0c5010410b503103800922600f0b038451807080b142e143d44244c00304804a081380d849411068003000703071062410385201130950f401306844180e500056011604100340f00080c0103030610308040070b104000c027070301c02c40408207240070143c800703801143e80300700210318220380b0340c09400146010000e4426220801400941d183c00480301250b1000048040c1c0041c907000729401825691150064020808401c040703881d07035a001c0d00240e41c000c40d62114452201010703013045024410000c00307081606000200750001030340108103541010301c1041004085e10f0230000760760020409260101d410986000055200d0240c80f0010758540100c01c07000041210008240d03c80e1102c80d0002d502c1e40d500c0000c2000d0486101402035004070141412a031421036200056070700203002141d040c41c0a455008041c038102042c2c0040c00c0740b4040365003800500070340c614529440751031032101ca806443e01e68007191405001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 245507347 1250 245506097 245506111
    0x306050402071e050c03030309030901020c031c1409090a0902040c0c030e040f0605031006050907050406140921010f0b0d1505270a030905060a1d0409020409080703090b070b 76
    0xf050b025003040403d005c4003028442c020220b070344a0405c22440c41e100d074440b03c3e94a0151245040c0040d550030089011355441602110000c06110542000d0351318501c1311030f4010a11000f0898003a890396550443c602a80e421103000410b040b11384180400c8802e140d00c400140721039040c0c0240040d611400b6441e0440083c1c40c007203620001503c41e43c0203030941380c120a6040c01003100720207900c0300c0c0381d20220444504070354140e165100c2d14400c0c0da45220300d015200001e0b0210382001810441d450050480c100060604003241e820350004600a047d065003c0c0801d944502e20070005400314014180c2c04001120003a48018040d070342c00c2d04007410615603000c00c584070320000b40c00d51001170302c0d000760100130781d40b48a1a12900403425210800b100084010514106000c1040e090002c183d0b03454081c1e544410380d603403948103c02c11038440d14084440e48640c48030720b080016207841c051074a21600ca111800d803a032210703140140c13078085150408000c4040903c1403401292400200c00d0b00045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 245508597 1250 245507347 245507393
    0xe090609060c0c0f011e060f0e040b0403091503090c170312041a1003021005070b13110409150501091503080706091a090d02010506180c040e09070303030605040207 72
    0x403103000541407a010a13501003440d484c0180c202240c0703054460360890b054000d802000740ca0384948089115581da4055141e80700285000100001c070351810351504035000e803c082c2d60255503400309942c4141080707024400247c84032201c0c01041078a180580250032041c03c07070000080d405120307955900504007064030010001c0f0104090017407090b80b42c40414200155964145040010b00e043c810039848100c0c000c910f08441c00110602c900c0544100c107a00840d00a40c43e140c0e045c0c17000070341e0f11440e0280c8202585240707101003070362144541c6072442d228010a590a08040104104840c0c05a000c810b80300c0c01c00b211620503100c2c0e030707031074106607a844806262201190b0608500030140003400526880300740f40c030030104500c4551200e12a43c801d0342120000c80210300100d080e1081914496000510000903007030000c1c40526055201c001c000071282002e640e1002030304200301c00d44000c9030355001014140700b407580c98083d0202a01042e24154503211156031051400d4001024a9036a10303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 245509847 1250 245508597 245508607
    0x50702060310050a0807080606041811030f0607020c01020c0901031a090c04021803060a0603110f030109081201211511090a06030b1c0206070305090102030c160e090609060c 76
    0x107940c42076a040508400f1382041403542d00c40112641e24102806600114821500003400c00d00d840d010b502d042030140750000154900c1a51884d402c0c010750b400080c0e05000d109004441c4410400800f880b800780c583c0181260401c0301d001a0601a50f4400300b4025400c2c0c00c01813010030701c00341080c14080502d02d075080c00380d40d581500a00f080c400c0010b00381c2c041c1c00040d51404800c07850070b82c00c0040b44201c0c107842c1280c6428170500100d0744580b00080030344850300c4a0a080f072030032a5004240d604082d001150442103540e44003a00d82c080d400301803034041c2500040c00112009019021950908214941c071000c207911004110410100030400303054440c0f880c094040f5650040d6203400c41c01920003407005e0b440d81d1001d0050200c008000740107100b118501e0004020f0340384d60903441c540185c8403920b00155a00c00b00d4459000c01c1c402c3e13042d0700c02000b019003500420407820412840050b480500c0340d0134a01c01840d012030240541c40268844414054202c0020580d9a081079001d0040c42d552 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 245511097 1250 245509847 245509861
    0xc01081308031303030515030a031202040b0408010603030f0513091116141b0d150b030a03030605030d0306051c15060f15090e070809032808010e070507020603 70
    0x6000350200900c840ca000c010301440c40c3c1041c1c98202d5141c400d03201486a943c60480154000150800090381648603050050103e03016440d13088504008201c00b516040d1202c03a500392907071050f44062101da54070031040090552112854501a00c1407900501d02282094245403040c00c502800c40420b0b0349014164084a0725400c6524195580802ea90302c400c4e50b041104112410004d041500c1c0a098a50000107012101251444200806031b0000038030039202c3d25001c140c0b47c0d540d8a40742ea91100300e0002507404000f0168010301c00d0b0781c04a181070518007414140f000e00181c0906040c2400010700c510354600e005400a1502e104429000c4040b509260380b0100001c501e0b803078090b1412030007107505c20410400009881c1030741402c58180c0c4490204852501d046c0c0301e01900d00d034030100440c080500c240f15158024060b042142e04004a0141e00045038940000f1032040740640c0c8803030b101c1180c00c41522401805c004011641030315005e04040d101d0304c510350009129030170000000e40c0f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 245512347 1250 245511097 245511121
    0x1030b060f040c02030a081b040b09030f0102040305030c01110f03010e060d0804090c0e06120112210c030806040b090c070302070e01080604030810060e01030f0f050a05160c050c0108 80
    0x600325000b4814029030b400c10001135140e40c000c03041c00c40040c030020f0014031301031b01070328002042c1c4d002c1442d400e150a01d08070781e00b00300350094403e096150003074000310a0035010900160002d1030140004e15510203284201a00312588800280d010080c148441c05c1c211100c4825203044501505c802c1c005940d07048000360507800b0058000348403010100c0c0c0410206410750143c4000c011b03d0326000540ba25210800c0920700ac0c501d24029600d03000c600510a0071075101403504220312a609101d801c4541c0110044c05910b039100c41800200070064110515900130403035070b000241601c0030000c4c4404c000101c0c160000041c40c200c0140b00000b00842050301c2001390790000d20540190310283d503161290241c071104152001d0300001c1003040852821200f84800c00119040350715103072b142c102a00c4c01540680708100030355402c542d650130b1080400c00345014040c410010540006464a03100900800c0500c0c4841882c0820210b00d50b100c0019600080462030311070b00342001e42403a0344d601c02200c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 245513597 1250 245512347 245512369
    0x1b010305041506090203060f030622080f041508010504140f10081006080f07080703020118260f0a02090103080c07031a090601060c0b0402040c030e0109050a02040b06030105060301030b06 82
    0x10210f10300704000400c11100c0e40614028542103035000c0d512100a000c02d07503618802d86140b0140008140389a105007040315a0021441c4240c10003810704890b2041c4a41503001580485109110085007840d0390350700503240b9001d0403003241c0c20007480240d42c440707200007000240503805001004000c6084401400741c01002425004c08a800000d01a040e01016221520a665641c840c0c030700d60703290680d004101e174015030345182c000304104ca2030350300115609a40d0021950008034400c0010a0300030001d075018101c08560a10304626001c4242024a00341e000c00d041220307900405150401030b5104050541100d800401a545a030789582025092a910354002032440c1c4a51081500c1180104207480c0724000510586d803071a80e860380242c07940440e80c4802812100b80c0e100240061400b0313401a0301c2c0c001c044c40e0010705503031240b002e00d003101c00241d03090301c0c03a61040c0c002030114072b401d0040c4442c69030140c8145086515150200314580018080140022190340000d0142e80307544203111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 245514847 1250 245513597 245513633
    0x80307031a190e010501052b1b17092805010b03070618080102040608040f050a050601080a1502122403070b040e0a05152707020f0f1b01030504 63
    0x6864a03050b403548140040d02e51241a84071200034000041c0380d0300800130382c0c207503c21042201c02c8800480c01911800002905001105a07440e0f84003000584543c6504446104a854660301a130802402e85c48050004000c01002e034004082c0165445540c0100d00d00c440c2604050b120380300301c0b464110701400300004482c0d0984221a00003810540c0401c1d8410710001d488049944c994807040340314280d108900800001c01c9a110105001a10281183c00c1450140c01641c4480910340d641c24107048083e8406440c551041541e9801c2c4081d00c407000f454007070806811031405608040a601c1c0381070081005249840c07400f0508c801440380d900300492041c00500780c4029988603200560650020b010300740c0100c1b44c1c00c000a4600085200c0d031790080f6440000020140303030714030400009888600d4a881c4480d000510703448011810341685000d0b41c0950080d001c07901e0394105041c074040300300c1605000c0e6400b906180e0381d0005a02140e4810389401e1038085095030710350411140070480844a9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 245516097 1250 245514847 245514859
    0x110f1203070b0f010b0f09060a180801020306040c050c06060f0d0c09090309060203160b0c040b03090309012616171905090a15020711120601061407080307031a 70
    0x7070104002020203e02c594011011480940d80711122064140109017450746101800c0025410fa440c200d006042605550b241c640220808a84403900e0b0741c0c0581e202007901d81d004414010b40d4900303801010030542c000c2c0b070940c0c00d00440040355a070f14600508042d01030342e0607018052050711861340c6d806500350410521030b400b075a2120301000034812a1070503400200b440001150981c80841200e6034101c10300b44504ca000a0b540f20319941ca00c0c00740803034589039810440010307200f00304005035102c0d100d81005541c4949542c0700141820312460801036820803040303210314400c0350401680c0e4001c02c1c00503900b45c02041d03902c002d403500d4902e401c6c591400307110300c02046000c0c00708450307912031420380210501c010346851003100c3e516910040c006002c600c05111407003880fa240d5001d8a00e107401101c8003003041c01940c0124402c142420080c0d050f41d00003400622020750480425000b03003035008170992400f64640c88410f01d50101501034010181c5451010354803101200c284500d84000a00c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 245517347 1250 245516097 245516107
    0xa18062c07050315041a060316080309040e0304120b06061b0f010e070609090911090106050301090c020a0b0604020c0a020a0602010606030f0e0a0b0a060b070b06030c0d110f1203 78
    0x40c0341e5a0a001d100b128030a12445130000c0c0d090720040703007150150f07901c0081340d540300e44043c00c42c0c481c40303c0007010150540308805040d035080c0e03009040013008100c50009140c0d103a0b0381ca800d01007611b42110b6451040d900c00c03c0304100e070001c5094203c10407a085122900075880380030019916100d08100c040400c0d000320301041c11a5004144990b050400300000c102114010302001c1e2614094404c400214040c040700300311304481e079080045601e104854869203d501c0c2c10000342c42500a800c07030304c0000c6004c40103004040c202d105007034034802c1d5400280154081552042d15103c4001c007038070702898010071383d994003000c10091401032039030062014003083d1700c1d400c0003030007440323a4800d00c00040d080880ca0868141c0c548103500e134415055025041161258482e03554010000d0840312985540b880001159002ca070302034000b040c0f0404a444460904008244c64480c1c5045c2e8284101140c00d0031800003401c41191204210086e6504c1e40d404030960001a286845030f1001103180c080012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 245518597 1250 245517347 245517431
    0x30a0212040809040506010315050d0501021b0303190b060403031409040c031a0d050307060915090c0611160e0915040c09050f0c0a050d0902061801080a1806 69
    0x1010f4a90010b080d2010081d81d81c8075001101611070005403a202c0c000329110521990070310500515807030f4022000035103005401c1d0f02d82699000241940d00d802e40010043c0704201e00d50b15444070b10b01198500034450040340310300041207407045110040c1813212801d0350b0350745290b002054401e079140c018000c00000b20043e4014003d00401d00c001403134095102d000380403500d03299048814041c0c119001f18200941c81c0d96010023800d54503015224410140c3c4594116440c0d03004511001e84135500c03104c00c003450000b01900c049140039141125410240c40b42e8041d40e03102c603d600c01c4905440304c80c809038a400307404038140844c2540009011801100300001e0121822440b003c603184001d04200941d50702c0059510300e40d00b40c446543c4070804101d95000640308401914482c3e195000c0021602469400205664440480c25058480411286d045980c0089015501505091050100f0101e0304901010b034080b00704010036555481480c1d41c49501d003450710400c00030f040e064100005000c84 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 245519847 1250 245518597 245518613
    0x3060a15030b090117070b090a08060106050405030106170d210204060504050312160f0303181b0902130b0708040504050f010326030610021005100612060305060705030a021204 77
    0x2000c0e42e4003580b42c0c10000210488040c81001200100401801c94203081071017550096014402159103c240f0b170b000032403040d8003440494020440c94039459030340c81c070f81428142500c52a920013200075158411148560201048030305001a417031030900d07240c0307941008541c050802103000c1081c0e544042400704480d134100303008106882048003201d0106026000304029442851080c0c0007038000300800800156802c0c409a41e00ca2282c10003294001890034081b14090003000c0643c5c40111413035050245401201400c00030b04420941540760012403130807011414582d00c40c500401c0300001d02d0800f8020000155406003900500512850500001c2c0b01d8407180300380001d45403800581000c0002c5482200c031401540b10320030b04d150442d52180d04204150000704441029800750301d424051084440c4503481c0301d5024610341d061140c2c28480003c000505490303000e029185400001d10128100051050b400055072034955500d540f0b034001480a8000d40302c04208403141e41007803104000080f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 245521097 1250 245519847 245519861
    0x20904020a0f0f080f0102030105010e1302090d0b0403031d060705070311030a0302040305060f040209150d05010f0509070b030c0d0b0111010f060905130c0504020903031201121106040803030c03060a1503 89
    0x1842c1180c0c0c002d000c80720701030b01f03d110a104060100380c1d0410b858055051240e5000348000005900600f0074281601081da0100100004c4a440c058101000109500740c0300744480441349501d2405620510110740d6603820015150400b4032601007420420144a800c20310040d0f6800707420303251150321024000d4065013060004841d40e00030200000c0f400740308c48500b50b01c030b55001071034041181c40b401e482d101e05030780d6080d00e281c200b000d0440100c0411000d0058506102856200044c6454040061400c210b41034100180190f010001e000c02e020509055446541e500030700010240503460041c1d07414003400700d00c00c5842d400d10188484551459001008032814240c1c00d2203140da48805414075041c02043c000c0c605203008170107010314141a030182800744c1d400740859191180c43c40700340d01240303c00da100304d01c03601c0c1100662003040800b22045000d000256240d604160074100f0040c0c903404014103a00705502d000c000a030b20303952541c55040090568420a2031080b4501d24024040c0100c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 245522347 1250 245521097 245521109
    0xe220f02030d08070c0807020f030316140106060e0f0d15090c050418171e0306040608060c04061d0a06020d0807020c060d02070614010e0414030313020904020a0f0f 72
    0x300a40c00c4142409020103030301c00d04c11917441a4401c031843e5100701454001c401c040e07030402c10006c2d14403050f44042004040c840700011051406100c0781c40e04608a21a642c0a04804c2c1d0404004118554200d0070001d80000101c45c0100044020404100d01400f20600076119030b032030326a003614100b0f075903002592850041c94580a02c0341c8a00030701068500891894501c516588140c40c04210200201c1100c8050555010324049901e1800c200d068000c1e18101070802000090160303074505441110000d00340c0c00003600741403500c0d0b001c080090049120310740c11320000745220781c80c2544038641200200c0700244040403941c2c803180000d50301c0c0744084000001c140000e0202c0d080c01e0000994210b0703001e005003050300d400389001110707010b90480070040700d4030f0342c8541414418000d072041d145d010342a2a06d5043c940e14103414000302030b08540f400d04000d41c00030018001c500d5510200c4c1c0d0302440c2c041d80c2c107042a850f90310220f40c29504070340c00144800303180c80c030100c0c0703011b02118400d003100c1d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 245523597 1250 245522347 245522353
    0x307030b220c120501060e01020f060c0910030204150306141504060509040b130506030d05030906010b09030a05011a0f0105120a0903260712150e220f0203 68
    0x40300800d0000e040d129511200d800240360190051203001908220080303621850800b480c0030110340c280b002d54500381c101340007007445001d084c00e180d6810410f1406400e0341c1c40051207107042030700c0c03000001d200c0c5001881c015a107880210203c1e0740079070101e40040c6071030380c0e40c1440e030b840c10300300200100560300600801c01c43c3c1c1440c2400d14504402e520f00035070001d001c0c0500d0a460601c007900c81e980480a06500144c4508041c0324036581c042e041c07100110440c1c0c0118152404808041c101f007590030001c4144002402403000603400080c00700e06503140242071aa8510200b40040c0c903140c1502e000424940c20076010f440c1c003100300c954080a6000c01da8000004404c40c4005549074043c50030a825407500d060002190902240c00001050b4081d00380001a1421010b188000000700d45035089800401401d1042d626881a454402001c0301401082003083c54009042c4442c0c446c031804601c1c0b84044080b40e80c17094034402d008522488041c2168031705096141c4610440450b100c03e0384680 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 245524847 1250 245523597 245523611
    0x3050c03130303091401030b0907050322060c0809030f07030c080d0e1c050a020a02091305030d06080601270504080d060303081501020105070219080417100c09050112020d020717030703 81
    0x54068040c88e03030350181c004d05903800d50350b402e40b003100d40c0e401c0100361039a1203900d14400500d1007a00540c0c030300c0f824050803000ca00384440e0100a40206005003000c1071a80c82041501c4982050b00c06950040d070341403404101c0b40f4118200002c1c613000e0100c0407404140703041310317034580902d0004c0e21142850b801041c0d41300b40003500c1340a40f041d0161031841d03805600401000401458860fa0b02a4801c0046c40e2600803480c083d194289590020106400202d41e00e1800740300c41d00c8200002801000c08800c0704610382c4050101410198000c1705840c4202c0d00ca5002ca010040c20409543c1076941820041241036030302d017001070540744103840d000341c04120030515021551060184070701c2092960000c0c8100c1400c13006d007130180c08041c0d009075080d81c001d03c00800c280310007940c0003440b0109803000f0032080380e440c0d00400072603c40c80026400d22246040401459070418100407804250410040c3c07684c8140814801a200702d5400812244c0d4045c400300c3c141082c43c0c05140541c1c03107590100000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 245526097 1250 245524847 245524849
    0xa0305061e150f122805060a051507060509030a080115050d020d06050310090b010906030b012106020d1a010201050708060f0109051818070e04020603090c0a0314210703050c031303030914 82
    0x240c1b4160740c040c1d00407012650502440c1800415103071400e1004810304d00c0c00c801c4e61200d50884800b0303100d6031095080056904902d80c2d004100c40e001d071900010081c3d114001101c0640b40f446108220520036401048140d09c00d0350981c8000000c160140c150380907600c00c1e91000b0001d04405034203c52506200c000440c2d84001d5100381001c2da03500c2902c4035070301d90800c803500805004043e4124000c5e8001134600000842500107841245040980452100b001010024544031549813403130441e85844100b00b0025404450950065000c0c1c4010728000c0341c10700102c1d41901c151300420f40040e891052500300e5042201c2c0715206000016042c640e030031241c0f24054880d5040d10038181888020404503000d450b0001c02580c2000a0200f100d60030308643c0040f8810494592082c2c607100702c2c0501d80000400c052082400c200e43c482640e01d0020140c250103025070103030300d401804100022881c6030412208100322441e1080407605d02c805150740f0304d001046481c140c0034082042c11404216056 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 245527347 1250 245526097 245526101
    0x901050a0f020c120702060417010b100309050a12090b0408030405030f191e0204090b04050118200a08060108061609030b0f06150a0305061e150f1228 66
    0x28030410980503060007000511303a144180c101c07040999021b60200030009100c10311400144c00d040840c00045002c01ca0041000703a40a8000145014541003410f5100025400b050b8442090b5220307480540440401c4c030112a810000c0e00088401480003074046203e100c0003010b001220812000c40b400210b0036007085403510404200100681d00e07c1400d58000f84891030151b120000c00c0860391a1b810551b0001401d40364030f40c10940d48800321100344000c1c01800e014819446030070321070385e0310942c805a43d8031812b030002c000114000404244200400c5c1da595085100400b02c0904460840d61030f441069100c0300c0a0b14100011300120740c40c150b0207130103a05c0d6003040780e4110400100310380c1c440702e5400080e50020074035640103410035a00e80d031452903103010304204c40c01c50b5000681803511b0340c10b2044120103403004090200c2c0425049001760f60740351258468600f100178042d220800c95400c0311036405000c4100548003c5a03040101da03180d10b003041e2140c401601d49040040083c0292001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 245528597 1250 245527347 245527357
    0x6050a06120209040b061803074a1e060d080f0a090b0a020703140a0b04080a11121210141009030203070902040302030610060f0e0111060901050a0f02 66
    0xc04103101c0d100741d07035030292640d01501c103520024201240e01481c4000283c516804610750400041c4d50528003602400e0030400100034110f00510320843c02d400c0c4000c805020300710414018014000484400394036250743e0000120f0706a0b246104c00fa041c0030b14001c030f000260350120750b41009030b400003480600c0c04a560209181e0454540c52518008a0311883d032a4000049101481901000000c00107403200080402e031100381d001d000458110303e85a4910b40c9000e5403135096622240c0f034030300440c040542e941c1c0c0155000d040c071503482c00b6030441550320510310201201079010740000c0035040c202c1c0400409600064030b20041169881e640c0044400995002d4a00311886081d0000420b0a2151242c008120581030070324066503a0b80c0040e203000c0345904005107598022a041045050800180f85c111840c115283d1880d814000300401aa0851122100300200e4103d9408135034091021000d640d0804d400b80c83c10b51411428036800b030501034402818a5107440006d0120300d0051007624 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 245529847 1250 245528597 245528609
    0x7021014030105041109090106050d0e071503150305070f090e0d020604080a090314030a0e01020a08030c0f0705030a0206150307081c051c0903080f040b06040c0302041701090606050a 80
    0xd41103900b00720900c4028058207142c0c0034008002c00c50014aa13441d0070b961802800300da40d9881d41c0703510011300c050070b603001c0b040c02c401d051780039500c10300030000c4045032444001c20500e00098400540070320580344400661000e003d03070084060100d171100d820b021071416103c9140c414050f60402c190019036411125100000680100f8082000150100000c0071404602d1400396104ca8803078449250740714034904001481c1e40002000010190041052441001700b400070304035050060b1210706d41032000802c0c91007041d000084104850a40c0d00584203815004022641c0310f01000b54007a41d140780076564511401c0782408121190700c0c00280100071f468ae2040507004020b440030070003942081c000d50650a1007003e0140c80700c0291485000c040611a4010204a80085082c054030b884c50103400d40100012190400003c00d0306c40030ba49402c04030913580047c0c3301d040401d04030000d020701d800c5407a00310342c141c04000704400b054010701c0b0064000c0c0820090b065a60b42041702c032006d24840d43d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 245531097 1250 245529847 245529887
    0xd03060b0c151906060e0315040b0106030e011e140109021801030506060c010903080420061c0b030111040305070b090d0b1b0d06060201050f0402060415030f050408070210 75
    0x4010b5082080301e010360084001d10301880c0c0103521007646801d4500d03d0308480e0004a0341e409003909441d08201e50fa1b081d0b0340721903841e45d1508041d00d452035001414084d100502da110500d04044106c2584000010140640d0351400d0340d544070100c10141040c0060a1400e100d40d40020034441d6903482119a000948401d416030f41000e10019006410001c09503540960180300d8006001800c0c090300c1e00306442036640c000380e8501490070f0015000384a003556904604181d0080307680c0c0750203080300c00800c41c1603406c0c4080300c40480120301501d070f0903420582650a20b0081016844aa4054000e40303206000303850b204d507107d010b4480c3c02d01400c40c400e40c0c810800d14180c0040b0303240c002c80b2600301c0c0480300c01e481c01c0000e03d009a11564054210132080c1d55071070300204429035083c4601a08010425402000303801d00e600010075900490103880e200a100c41c2d0000c07241d5020746c1c08006405031815092110b0324050804001d55001440c0690292407030f22040003031a48524050701c110b10881080d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 245532347 1250 245531097 245531113
    0xf040b0609041802030a03090501170105150705010905150709050609091b04122306040309061110240f030b270307050604020406051008010b09041803020d03060b0c 72
    0x10800503103005410800f1140f00c1d03040c1e02e400341e1406c3c082c95441601989600417924901000108441c5c459034401c00c013801c11000501180e55150340000c04038110044880c0c5980c1e86081090040c0210f9000501c188602c41001d04c01c603480c590218412882626025009039550013806282c0c840e2a1003d5441409480040c1c00344c03003030480310300300b00812040b214241740d00e83c12003d4000714880016100501544012480780714500700a058030310b0310703801074900c070305180c2e07000b501202040c0140300621444000608945c40104401c4a10305d04a0100717102403200016110f01c0031741b00c042d015220544c00d0030f000c0388003154140c0401c112035004e10710b403000d0ba41c1e00303804075100c400e040d4400701204400c552130500c180e403c0000d405c9490141018040c2414070f0b104000c12102194449802074208041041119800a0b0b016044818051700d590752380100b540054002c059040750301a1040300c03804900c003416400140307503220300e01b55101004132645a420362015070040d5440543c65034007001c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 245533597 1250 245532347 245532349
    0xa06020102120c0c1e031312030c2d0f060e060903040b180d1506050406080c01030e0703050f1b1c0212010618140c07050a030f27050f040b0609 63
    0x4020941e40074840c00b0740c0c4825481c1784c6040454444c1e03500103c09580f0114801c4852101c145c0184010301d000e511401c5c0100300d80d9009000481d11003005040f4546200c0c607003e18010100c80315150200b40b13217206401034003034a000d11a09d041c695056801d6072038910b04c800003040000300a8041c02e5008021800c040c40c000e61040b565109030381088503400000c40d104015100c891852022500c10040c001c0d581803810107a00441700207a001034032a40c01c142042160307100106100114410030329011980105030050f682c98008180e01c024103a1103158203910801e0750120f42001d4400050380e20100050803c8100f020088845510a4001e24402d14803401464211400320480e17001e48000700b4035559420240c1d00d5105024440c0c2c0714030b502c80c0742084030440c0038400158480340040031582443d00d2619859039581d5222002018400031410015940d07000d1800c400c201d2003111520110703907034240c1101c4480303c0944030700d030301031254095510030300d00d014040d010313840c50040c200346e041c40c2d102c81c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 245534847 1250 245533597 245533621
    0x3051311061c11040302010f03140105010302090303070f210c08030a0f0b090a02040f120c03020603061c050102090a06020c0117221a010e041505040809031b0a0602010212 75
    0x2c1502c025030980b141d681c200e042c15078000c1c8824410381500c0551541d2840c00058000f813070455400040501d04001201c0300d519003130265044d00d2007071a00589843c03110000c40c0c5544502c801c090580d1209039085401c201c01002100c00804081002d440c0109800c00309644010030300d48020066070003880001d00c004241d500101c11440b4025001c1002244400842c40b8100d081e12449842600020140b1002c5c0102500b040101180c50002942d0200c0c1d032151004d200c640e01009220301c00c000089206551072200c90015280c1c011031909030b03981c29140030340c000d52003600990b0003501c400700001307616400400d81d8803200c14180c4420390343c040c400c4041109803100074050000d0300c9030402c8000040544018000300300f8030621804204458954081c0980c420581c40030403040100740800002865180b024544640c00950224040c0c41d24a0414194014941c6454240c0704c0e24880b004200746021ba00000b4000940310b8802640d10b68404a003031744507004040300c981007130802050303c280c250703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 245536097 1250 245534847 245534857
    0x50a141302071a0105120312040f03090510050c15061c03021c1106010905040804150e18040c05040e0d0c020f06121803070b060d030c050105070f0305131106 69
    0x160340018078000c901c0c0d541c00c52810704450f01c8188601102c0c010320072410010243e07017803000c90350020741c1850343e182072030441e43e08020320082144d25459100003c150242c148800540710060007100c00840403103005005420001403002548110202880e1089241c505c3c03a000c0d140180c035901082200e154403200942401c03500714110b206134024410207a00701030f000d040740c030300a903034a0b400c03003c00020042c5850410b81203034503003034074020070f010000d281b00c4215801c0f80c01c0800b0004a88800510550b117030b0081c54000c9410203134006503101044c1303400c0800e61040c0d01c14003003041ca444c1c49009105c2100c1081000d40c19951003a0384103880c4e14091100402101d00c000c00036080005050701140c844d8010100c41c8205402c60030030700010130403095101020201d604c0041d030501c5182d40f269541c05402410442c000c181d183d594500b41032007903010814a0750071100034803050500c84c50040401c0e000b41c4210b40000d19040201da00080d405400e01c00305500000d00c140310180c05010010325a00c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 245537347 1250 245536097 245536129
    0x907050a0b0a0503130b1e0a06151d0d0809090a0504020a1809080d051b0307021c050712050d0605060c0a02040b031e0a0309060503090615120102030c070c050a14 71
    0x5000505d0006002d0303d40d0382e441188a040304001d54201407141c0c1c414941c01400c80071440c0c0c00c0041c184180e0000c0d45185450704090b1915483d121480390013100600240380095410070790340c0c202c01040c040102c008240510013540ca0307440907038402110504070b51040e28004d510200c041e10401c00f0b8840350f08400200b1040d088002207440aa5a50203542d900007100f052915403940108500c1d8107804920081c2c441000d03030802d02d503142911000791100d148881c184510724600200740c0800c1e11840a40300d02541c4000b0705507451081c0440176007a0342007c400c0028007030070114045000e040a00540d01c1801c2804020b101100c1107a08120240a4100381e4a0f050300c54110f11038424000e40b00c0c501c12400800000e406082e040d0308000b40b04005907000700041c0101001804091900040d800d9404600034003011b11030501c09001034121182d103d80c2c41c84941c00031003841a80e058031401051018404c0103040192980d481c01c0c424040040c0c400e40503018021000c022180c1003119403521803402c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 245538597 1250 245537347 245537371
    0x90d090501050c010227040b150a0305270106080d0f0e040504050313090606030c03051302090c0906040303080604060909080f0a0c0f03020d08060f0d02010c02030f01050f0907050a0b0a0503 83
    0xf03030540c184080604059010084150890711a2400b0300f440d226101d80518140d9103271490a180803554a442c2c401d00aa540802d5511800502c1c0644004501464140c541e50b5220307040000350070380381c01b03881d050290040c00d01480780742140c1140074002c100c42e4044140c40d810b003000c040c2c0702003000030080240f0035a8a030000304550f00072682803aa111002c3c00340c035100000e01c0d41c1001ca00500b26040030300801c060500e004c0c1413207070000b0000c40f003028036a41142d003003440ba40c549560804038003e24501d02e030445c8011a0102c1099002480107104000c01e49041040fa0b03a2590814140d50f50264050301220040041991512090004243c84c0341c80e410b1075150650070340e5a00d090300043c0170058006170000d40301480207a40c46450a0f801240442d14003850300b520400152265445800003810b0150342d040e07900c11134905108003200f072040c0800820252400400703404007808205e0311000d940c0104c580c081654030301540c0100c140e801802c02d1904060320031100399030607800a010710301411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 245539847 1250 245538597 245538607
    0x15040e100213080c030c1e01090302041e0e061e150d030c0326070f031107030f020f060f0c18091f0f0302030c040b0a12080301030b090d090501050c0102 67
    0x103281800208a081003440319100e00710700d00060181008980e000c101c2c400d4229200c0f100c1c0a03030301c42001d20b400400c1034851892510340c100040c1d0740007140b0303070000750042d04001d0b803045280c044408844042c40c4441e0240f10041c0c40b07403480350300d804084601e10600854102410900c200d000c2007103600200c00c060540d901006400040c0020034045130880000d4182d030480b0b820540e118502c0c03070030035011140070b191201e41c0d10180700188100800580800021250720002c0e5407194020094032400e00e489a40d40312458140205441c40f0142d62201610507001070102900c0c1c002400392151038040015821525105502c20701030740700003000c903110240409020556501d1f6410a030090060000b4040b050100c6032800c04c00752101e80c00352101d600721520820246e140801c0b001c0c80c80000720b0b400180c503003480c4001600c110041c3c10298440100c42100c00400804100440c10390703000d0009400540d0701c2c41c420395540e00d0b8807404d990004609040410455000c0c00103042110850f0740054181 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 245541097 1250 245539847 245539873
    0x903030c070c0b0d1e090f08090d0b0a050609161706010903020909062d040605060d12020a03170124030e030a08150907021b0d08030103050a02040f0515040e 69
    0x2501311205940030b5a603035100441024140c0340f00c81e0000038800c4d1080c0105003850300ca0040011007564090015200003840010585c3c0320203600b80116402100203060341131502c0000020101280d0050040094102090240000c2d034000b0380d0b00c250a5450b03200b0001c00c0003000a4000300178048905006400c240400169a11901503105582c401c00070b02c4c480c1381102c444072501000e092000321040441b11214042a80000b209a009410410115240e241c0002040709a03c41d110041c1a040008003070010041d808110b021100b4029960b203641e8401c80c04010400714801c0c41004d0000e18843c03241c102c80c070b414208488242185003400a8854402035040c0d041d036210407070035000900c80d541041230700300c00f09199900001d4151402c0a49240000010b07640342a501e410b00d410b10030040485410340d6640c0f05c204d0080c0ea10103401034895a5a142c0141d817141c0c10031080384194180b070305420004480f4420280304400745080058510480020701008002294400714180503071311401c014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 245542347 1250 245541097 245541119
    0xf040504091214030108122a030a080a05160c141b01080c040609051203041509140909120f09120c0108010918020105090d0f140709050903030c070c 65
    0x81c1e6015640009000302040e400400c9100c1e6444055602801400180301b2444009588101080c209043c0e541c3d48000c401c14140c1c150618085580300390f1251031300b0030030b4640403000d480402c44540301c40344241c031404410340a40e4400c40f280408902a034500a6450380324005022107213001b100341000d601e21540800b4103000d4400400c00c003c08041e040c42080356400082c05901c0303c0c00000c55030409040c540014111780244c0701c0c9912a010700307080e0102c48481401250000d0044081360090b080e9050805842281907108440c0082d1807003440c4401c07814841560703486905040098088600b60800358011a0840880400c80140c1400744c1141502c13800028a00ba44c81c00d40100000286003000600458058001082c1d0a040c114001d6018840b00c103c804c2084d8242021901c03003865201061103108032150103414250020210028030240404521085040105440455880c0c41d04041a110191990b100035842000010f03a900c160f1070140100d18440c940c00e0312000d40c1e40c005150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 245543597 1250 245542347 245542361
    0x30209030d0e0d06111309020309030328050a050a0e010207111302160507031403130605030c07060f1b02070e01030b0916080c040605010c020303091207180b04060501051e0f040504 79
    0x11102170010b81c42c500480240441c1000340410b5000350b00c2c51800c031804c15203d02015154242c640c2088501c828500e0307001d03621182d5600c43c01420405464610009030103031800b607842c0203009180c80103c1c00c01200600031038850942069002814030800428410401d448150b1594030729401d00c4243c80301e04d45200c4141d02c40d40107500619080e8207504018050040008400f101944200724200031060a080d030103088581c20b04109849176030b10000540d0360300c11140018046d80c6044220620301042d07910515900305041c800b050080c1d4503513416130b52028203019245040700e100d401000001c00308445245e2240204080da070a041e62548800e8144240381c014198982000c1e0351012241490f1041600800342440c0c1a101c00f5a82e8010a80b20320503d030800703029182c600b02d948505102000281d0040030400705295120b4502c80045004080d8218101c0c840c90030400d0003e010342c40717041038440e030880b50072000302d051064081100309039125203a01920044280800946680d40344140c01c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 245544847 1250 245543597 245543621
    0x40906030303090506070309240906050916050109060e0906150a270e04030507021f11100c02120a0c05060f0105031c12182a06030209030d0e0d06 64
    0x85140f008501e0400c1c01c1040040c0104200342c5800701328004200d41500d0717841d030000a00c0c503031207400403071030b0b10b10014000c50400500740d6070a010a000004c400061440c198402d054001030b02d480d00c2c0c0004490469542c0314650006101034801d07a294542a8805500184005e04200e50781c2541c0c3c0400210b90890701150010030719400d2140c084010803051840071102a884281d21181019460310707440030054805020000d02043c3c6c00110340340c2210021010705525400c603035a0f21080070080019040c1c2416400314040da40c800d080380013942c010080c0b4002ca98010300704440005504264a8111840c180108101307071001202040c0107000c400d0080c4c03071642c1c070f2060310360612041c185030104900c982500c0100224000600f40d1340404404503440e403030200840c03486001700001d0030164917150301900308524004030220000164044103000c6800d001400941075450005508a0140a00356071701a00140e1403945201d2045444045050b4010801c032020310481d1100411100c06440701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 245546097 1250 245544847 245544851
    0x30c090703061503020702010507030f0512040c05010e062503020a0c08160b070b0408030903040b160c050901031101030c200d081f05061303080a09090b0a29040906030303 75
    0x500c40b6101c54406681101018201541b4105050740001c00a00c40e81c80c01070108001e00300612281c038440c4d41141ca82c1c00d0501c00494203400c1509040c11074015500c2141d010510161f41c0503040d04011041c0c0310b4580603503142c40b000328030802e5400701e1810303031030700c01c8046004026560300060310320910780c00600304040040a0003140d030007102070001310340c0c0c1103103540c00800e00855000401c1510080d5003e03500090300c51301d0340c64507100c40e85140120f8100c4c0d030038004d01003000e01d65080c4e40101c108c105401551542c00c0d0558540600010b200c2c28000a403041d212120b44456550080d0880d1303a0700521450002101040701c20175014034020101c0d50b110740d400a4054141155000034825000800232040c1c0c5030040e803268031107a00500314401d10303001d40d4001c08c076041c2d2440f003110340d0340045800030030b00d84d958941050300074185813040c0030304d0440c140740001c01c40e002d0400c003c4100560740d2000300010342d05c0c810a200919070051078020416504100404070b54025140107200056100f0303100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 245547347 1250 245546097 245546099
    0xe04020102190803061504090608061005040c0c0303090c03330204080a170409020f040801060b0f0d020304050f0706050a020f160b0a090e0f16020109020907030b030c09070306 77
    0x2410a000c0c0680001c15810b0400c2040101e003481080701d0304072004540503252043e40d44a2401580030302e42c4064191450030800140010021404501c68400400005140345e2a04108400c840c0c030703841c400000407080480a0000b07402580074005660041d00b19a8601d592039a442c9021484038610320440c680500a1091401c40450b100440d203041201c2542001c1c00c5c0883c9959414031240054120f411818000859424800850f400741102c11020355440b5920a60b11515a125202e002c08940ca090030004442001e10140c2e800e503c0110201440c165400c038219001e500094420f844501135041d182001c46001c0184100034811500c6060700e456240d50082e081001061282c0b105801214101468448035600304003641c00071000ca64840c0c0010004a808101d640c0000b000103444034103210610751001005880707403001c00f100c00c00880000204a0a072802401c3c000d402035109000301e00d00358065008490324003009000c0f550b4020184c07000a98400d01900e911000c02da83d850 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 245548597 1250 245547347 245547349
    0x70611041d100303020c15040801060e01050a23060c1e0f010b04050f16090f06020705090a0b0a0b03070201090f1202010c0c0c090213031515092f070506010e0402 71
    0x4140394019142c0501d8808140b80d500d001e91600c0c08404504d10842c55074641c10368075000c40b0152005401c0000003000556210385065244410070b004e15845007440820015017085555121107030000d014060210420806090250300c0d0082c9080b4041c0303020b207082005d1000b081031a0075000c0a0500020603403030912202050850703035190120303401181403000b0429041e00d03c0d0000d6410919070115400000b110385d20480310030006401004003150100e100188250340095410709807442103410f050701d922040c03c450708031280564069001445280d0401060350f15002442d07006d0642d0001003090a266541c080c28901100130851b0032041041050710380650911038440c94000d617040001c0b6070140c544990301143c1d814403420911540004001940401070040d4800943e4000c00c54a644103900b0f4a00700540040c0754542425030120790b00041051060041009400c0400c8014403034210011610101004490948011003030030040500091800c024080c0240341c00f9950a0090401d84 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 245549847 1250 245548597 245548649
    0x3140901270201090b0705010b0d0f1208090d030f020f21010e010819020d120305071101050c07081608071a0604050709060318021f032004030807061104 67
    0x24070205050014014460010b0341c1040131803090790300d409050340e2902c0303040c50060f01410460b2314064004004031340c1c800c20814000b1140c18140d101d00c00c08000c48641c2a002c0b141d010084840c5c0c071513540300c0c590414003240254040b070300c1441e81c410090303d85280401c403480e05a20070b51841e00c2a4020507000d603c0840c21180c0b10307026002c0c03400c0c80882540343c040f80c03d0342d5006c1010020300d00c140440c1040115a2145100809564440f907000079247c01c0e204080c00400044030924089180c402d0741500a207410302c103031032042e012500e646003001d81c0c68071008207030782281c0509034480030384c60710309404591810080d0003000c2c42102000f8581c4091070410700014000790080d401141400144441d03a6003162030601a01d00900c2e00244a00043c0d405201c46d414650010790440c5401c1109a0005400e000012042e07000e030700d00f405006c0700b1400507450083e43c0c0d40d0382c0c0c0000300280b0044c4001511000100340045c007520001c244c010b079200c040700956000c2d510104d031701b940360b00410340000565 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 245551097 1250 245549847 245549891
    0xa0b1306110c210c0607081807030b0612070303020607122405011e05031303030212070320040e0a0506030f0f03190e030a03030f020d18050c09190c03140901 69
    0x890603031414130001d0401c550707403040040d103281c041c86010310005c0d0700c1a80d540d90358004207030f18108032400d0030b9072424204501c0005403003050003150303100007001c401c400014600d0212a855401001c0720f59552500302c1c0c2144108908480c003d4981484508500c40d55041c5075031408140c82c80368000d03151600140450b090300b81d0406038070005840400c060f40d0400d050301d50190340755116006280a500d1304a00030310498007079800da14841000e0080b0164107078490342c485524600780100f42101c0540d060346074003c2c0e104500002c07060030001503100c00640c00c0281c203ca0050126040500003050150902c4218111000ea99002080718030342c040151030091078580c9a030405c0e4884113482004a9112211828050285070b2115a5500034958690407554034840b9101d08100040d81d0a03d0048080040c5509071071512401c901701e54945400c0c01290700900c210171207058090300110b440d401600c00c580d821018151340b110032502502440b45020721030729203a00006002c0700c0044581540b081c031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 245552347 1250 245551097 245551153
    0x100c0c05060f180d02192109030204230402040c170403170f060f09040201020c060705010605040507080f04030c020a09050c09040c030209030a110a08030406021e0a0b1306110c 77
    0x4c411542d492174000c906148038000030000b080e40162a0b081070320394a09400400000a80350149480c28180c2c0041c455040da84200c6042c0007003d4110f010600400c3d500c50a440d4020b442d0010400500c3c00d907019440c2042c003814486680702e2021511040d00e54110380942c00704615000c03034590342039070160303866200300c000038841c0c15800c046005c2030352002410b02c034a0040d907890300800d040d68004c1182410300c1c80010500c0c0d5480119103040380c064070a038400c96009074201030104058038001c0c10000c1c881c3d80b130780030782001d140d403552030443d181c2c0c40c076075401d0342c2042e00101c2c0400d9603006030089a00c101890740000d55540481420712088036103048520341010302c1444490915900400c6014516402c41807141386501240300058031302020f0f6110410301d21002600240030f907000329900c51000c080c0c503648030401417100c08841c2c948881d1f01e80180344102040000300c411806040c140c50340350190900003040c010b0340c1485c2c003d55004044615503548140004180da0b002c400d840f580d502c0e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 245553597 1250 245552347 245552353
    0x31d19060c180608041a1602060109090b13030e090c030403110d0f120f0f091b0f090c05120f060f240f0c0d0810080f100c0c05060f18 59
    0x4214045609095090f000b00d004204c1d03040c000c201400680400d000c9800341c04810f50165080910080c004c0c151038510040241c0940d000010301d6038028481c80d016141c014440d40e8165581a80c060102c0e82c1480e4101c0c203000541444040f1902c84203000d038030a00c80032402541d80d050605000e01140e4083d1507400b9240d20075203504410340d50040840072410784904049600d95503100500014001400a40c09514a08044168080c50030f800032040140280034106680311030569a0700070101c03034014400b100f81c00b014100468586640280c0c2c9114031131074100d0503d8511050b10955000a580c4103c20f030b6030410901000c2c0c9880c00ba05440c01404803000c005e10035500720109003000d180042e1204003032011a02040c036448000407a100036a42d0005d03505102c900703520240062500361000707840c5003074030f00d004112140d00080d07022121002c40300414150802c0d03000300d40609007186100c03082100ca04009400a10100000c1d0f00a11280080c4ca0b01c900c1e0003000c008440c00e42807000c600c254 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 245554847 1250 245553597 245553617
    0x6110703020a02060310170102040303030b031b0603040c050d0f030207140904021207030b040b1914060f0411040b040e0a02030103020a03030c031403070305040c050f060a031d19060c 80
    0x81d000900d28188075419218292690f032010048500d241242e807100d0341180c0300200a02e00d100040d0300a10650348242c07020000036035414149940c403012809000503001d1081d024284503e05500a154042d1003542d00140050f2102c01007230503c40300c044d04491800307082240f0010141c050285074050b2000c8151070074a80078a20010303a0740340700900003034022000f440c0380070100c81d000c1c03191038040d58224249407083e0a09242c00990300000300d620062088003901c11290b03015081c09444205261001c10107841e0f01c407241040f43c0d409038000ea0301e0f4003a91781c0078030160b0a28080041c000800407810b800b5280c1e450201700c07031030b80407008088980441c4100b0043c00103a07150600d000a580e05890142c0c002d0100345002d99201440c10f40441c4415004020404116072680055102c0c40c81031a8001c0c0071a910024001003450081c89140e00200c207021503a10b040c1301e948100c903112031000602141c035884081050606050184c0100400c18400b0782009000c01ca0264191101301450003404913 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 245556097 1250 245554847 245554853
    0x1e060a0c2d0312111e1204050d0212030c1c0902220609020910050f0f04030c15140414130207030306030b0c0306060d110d060e070f08060603040206070c030f0f061107 73
    0x13445042c0d1750039440e032546000503820307895100070b440d0507010300d03c0d00c2000c5041c01c0c2882c50366460304030341e524010301c58a6058038000340d0140c16640155169184141041d1a0340401f04031003403000b041d44109a500c0c500c00f40580c0d104022103823480d150307182514a5180103040c01d015198250000c20501e03004004105840d107992031071071140052443c1003516110b0040041d8024400c0e9a45110480d034081004414420340e0305003c0c04030358190341c80700300080403820151040d01901000000a1100f0f01040141c01b40d0b02030b55800c0110020204d4a1070b061b9180100126044181c06500007903a41c8024001c0000381200190082c2d000b0114900b545410f0b40087c2040c462038840000203906c0e82d032000359844502c010f440c0626900a4103111240d01c601c20304014040441d030a0000502c6c5845402c0500d001d000000d001e290041d0289145d0380e61502400a59413000b40101c0d041d144c180000400b103100028002c00c0709100c1d0800f11090051401d0040590750110020310f05800c041080d5400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 245557347 1250 245556097 245556131
    0x10c050c0f01090b040f06110f07060e060708180a120807080a0507060218030d0f1b1703090703051c0206060f03010e0106090b1e060a0c2d0312 63
    0x204200311081d080462146004036004441c55021a04102d80403d0104050003503140c110299619586e40025051000c501e199036880f20351010041c0d0740000380c09001c0385100d200c03000440a805002c15103021a2569800f03003541c8014660601d00c0c103c009100c6d01c0349008440320300285000160040700010a071a810201e114115000f4120180042d0340c80c13440c2d024a00343d404a94000030219107400c0710581111001c0000c00b1031b144240540b0b160346002500448107000d0400e050750391102d0802044c5800030809031055000c1c0c0c0d07824407182c1c110700501c0282004500c00c882c101c026040092461070450b04d82100307004d03080030f20202445c0448a0750b9001a01c960b000f00d007111a0b1800c40c00260109004088a0101c44115400c208001c41d11030303c2d540122882c100150380d040110108196000c82d40958489580d510030000c002d500c148500ca83c0d103450030700d4041c2c440007004802c644000e00e40c0d60f021088403035403140c3d40c103010002d142e0401d02280020385031003024040041604c2000f82 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 245558597 1250 245557347 245557363
    0x1213031706030a15050403120513080d150807060f030606080604150905071706030304030201080f04110301062c070e1302090a0617150306040b04021216080c010c05 72
    0x810300310341400140381c65030100301410704150800e05841e24200c044403450702501084606401241c2c150100b80c120583c1441818400e03003603d400324409120726034411995034081a2140c00701034680f910128059180c601041c02090a0740060600034a0588040d21810a03a400d190905103809401c1003080c0d0446030455100100302c1e000940c400c00b00c00040c00b050741c5500300100300c500d414100440036421012800c2018441c0407d0320f400c0d580c140800d642c074402c42c0802030000300200042010103221a03412504a40304e8150500200b80c060007003801c4800950201c98a180d9243d2500c108881028a100d091480ca5038541050318149001829200246940e50b0081e2204402229210a07a6055076660600145900851a9039050040c1810055121210440074a0011070030801c0c0014002d001060040e02070080e0b80c4e5961a4030503400802802170f6002001640f099080340818401c2c8006c0b000c1e580e402080c078900f0184081e00d00200f41031081c0c103000608041401140f0005000c103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 245559847 1250 245558597 245558627
    0xc0c210702040c021c03060501091e06050f0d0f09030e0d0c0b0c070b180109050d03020d050d0e06090a120c02030a0b0403090b03070504090c03060e040f020102010b1302121303 77
    0x2c02c203e0b510b1141246400a0788800399000182e540d4000d07800345c0e141c1c020104496003682d80701607541c2c40d415981a020303201c0f1409121014200740410400e03010780c1c080e00c0029030808900d4142140041c4c0002524082c80e14503000c03030b90303c5441004064016080c289040816103860f42035030301d184d84060a01c40c1c0390140c07481ca0301000c298014218020803495021b04840d602e01904e40111042041c800b9402c2c40d44680800d560280110711810500442c01245030954000e08021651001c2a01d003640600298512203443d1094002c5003c03041041b6409408250002c181e61001810035000074a80c204950f42081041c03220000980e4002810448803900300304900f04135101c070b2806031002c0100b40e005500100c008400c10906642040140c0100d60300e002c4107008038440c1b107104808490342405040071a03607050f00850003056124940d0712a140c41800009044106c11001901c40c1411000c503812481e0009209612844c000c0c0219402550354010910020003d5401070048501a040d107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 245561097 1250 245559847 245559851
    0x50a05010e07080c1932040621020a0c060f020a1706060c16030c0e0c04090f14130c050303211513060e16090504090201050706050c0c21070204 63
    0x49120304455100b05c134045201c04c03010080540c5040009022041406186543c0c4210012200101140796005010555058000e10300e004d081102c03e540760345100c080e0a907c1086400e030040d40ca0503510042600c00c00f1511074980c140700b1440c111007900c010b10302c1204d0207401400398602c06600607003a9103000c0441d40c42502142e4a0780041002d9000342c2c01d0f504034904c41c2042d01d030300c0d08190364200ba041d01e0050181c00500e1b0344404000241c51016213140902c1e001c1084204860080ca920480308807001c01d2001c07503075821190000145503015a00c030920720305081c4841003084440354404c40203010590246040c00715400394020000516400d944610070114006a04003a6007514210217183c001c114400c02000141c0350700080c40715000303007420b0040c600301055404541c008038580e150101e0340c500001c103003040c0500028180408049042c00820701c45c507000202180941441015001c445c1d03511410401155031500c0381081110007212008000812142c0354001120000e070380550340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 245562347 1250 245561097 245561101
    0x120d18170a0302070215091503040f030806032a04060503060f01031e0f060207020f031605042304110103140f0c07081210050f0a180f110a0206040303050a05010e0708 73
    0x30603400f03407203103110081d44052034004117480e0f8000d10b4050226140c2c01e4542c0c021070907a00c51034000c41e1100b41c2e0003400040c258050003002910030701d242d40c1d0080740130f02524400d11340b251144007542000710301c1100c013440034425180103041c244116001070500300e005010b1420841c1e41d06140d00e0040c080584044a1803110000180408408002c03055014004070f000141500b441e5009401c4132030200d1050319084507030340151400145240070409500e8006040700c0c070f49000c1200804c10080808441e000101c11205c0d9200e204825a00c11400795401011008074440010120f49510616508924060302400140c1e80c107004805d0b4411a41c1e02c00560704c0c00f1a042140c400e00076205002e002d9552001082106006095400101d0b07000b602e03d0001c0c84004810800154102d0103100c2d245000074108209500303c540124000d110751813030000d4081c801708500b061a502603168040968041c806100415600d031180a070721002082c41000b19504000b0102941c540103842a0208090100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 245563597 1250 245562347 245562367
    0x702150a050c13030803060f04090308070e011209031112040b030408130e011205120c10090c03080301080a0c0605090f01030509160f03020f030c0f10020a0203120d1817 74
    0x81101c0500c0800d20f402056640c0e00c1ca4602d80b142c1c1300b100e500e401081e90024003045414036000d000f1000303501d070302c0da0080c0340d8400108035000005480300f0390401845e40840c402c0040b092140f408414082d42d10703402c81c4119600c0080c609280514005564102040b0400c84402d00c0c8041e139400c0340d480704400d9941c0701c60003154103c2210f9600000e038140b001400000c1c04410241480002910170304c107442c038100b005040350109005200804180c5d40144280c4e00c0030080947c0080a0244070300c05500c05643c49448620380c41e04241c00c0b41c241c41d800008414140605651444000d01130707450900d10f03011800010541420b0024a018189501d03880840c8030750409000c4141b26503115080801c00c01ea40d46110301c5408010300c000e03401240640c002200c4e038140855070720450f1030090004094200d4000c188000490b8200c2003100318020580c0603401a6030a04c03d07150401884035049850303e2045290408a44440d00482400c8018a2640000502c210080c220740010030385c000c1d07140c3ca840c1c0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 245564847 1250 245563597 245563621
    0x8070e10060e01050d092f09010302010f0e0a080a0f03021e030702090406020c010e100e07230a0b13060806010509010f0818010908120f09030403170912070e0702150a05 74
    0x450010906c4008031161400030b810341b80e0030300e89947c484486440c805003036000c0c0a01c1d0142070002a0004a1728a00140c02c0d6005101c49052003001910010344c80313903580c080c14201411404200c035041c510460700c40c14180e04001e6800c900a00010300c21074201c0c107400c0f050b6240304402e4024007410180000805102290f41980c004c2240d0138024024200c1c144903079500c421003144c000c00c800e450804803030640d90000074610161181c0e0307610305488400908a094461050803217407a84500e002d07001003100001400030780190729100c51740e0100b250528402038001180107040130304015007800f1a02d850f13030344804042c2d003030b40c00c508210945848a02e404081c910060b010441c1641c200030840c020854800014445003040c001c0801060302d40d004e01c040c0700b0310300340c41d00140c03070380140401c0c030203c0c8001d410490b410240700308c0589060041030100c4c4600301900c400051641080504001500720a1501c079444586840034003981500c1c251003401c40b0300702600800d206503460001500d051080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 245566097 1250 245564847 245564861
    0x10903270e0414062e1202120a021909050a110901080901060506042c04080f0f0403060e010902040f050613090c0e18010e0106030b240a08070e10060e01050d 69
    0x10340d0310318030780b0382d524451505d5a0340b4075070f4005400394000380d0a40c8400d500c010030769200c107110043c0d200d00c3d0b408010702c0f20135820681c112801612698070042c1d49100d20035800c003d0b1000b42c161150702e403401040071244000c2580200d1030500c080c42e0440c500c0301c0b04581c003c04003420610701c0e5403580d41403140100036a41225402900004011032a000c034211143c04940d403141c1d448100040c0c1d814954041c0400351001050302205102d0034450701284c0000c0c0c04002c000c003420302c3c103041d40e980312030b401c3e01c0800e03071244950b03590307a90780d8002d504080c059103ca01900489c14400d82c1000c0001c24081080b450310980c405a4661100d010404a039220100905421940c0341c81400c0100404032040c03401d120300d405a61a01c1510b48640c0418080d91040300d42040080304182c0d03030295800381d020303440c01481640d03803c84a1030403019501c0d00007140c082c008010062000c0c0e03050400150065001815002d203800c1e030b200080101c03640c840c180343c0024100f86403107a115903070802400003812107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 245567347 1250 245566097 245566133
    0x613091d0f030d060f0305060c0703020309060304080a020606030111180a03020619020f150f06010507050a080a0318110402070219060201140c120703020a020a060509010903270e04 79
    0x700125403000040020140c00030540c0400200007007a603600100383c0d00f110500c40103242d9084000000d203c5400300026104890282c0156403408500d07070b00044040d13008843c100c560410101d6198002607040000b00d9100f1820380082010094261074080140a0314000d105440d902c1004070b0342ca91a80d60811004550142c0050341720041c090039031890304404401030f0014400c500318501d11640018503140c00808400d1580700b41d8a4100541000c1c880060469040c020108500800160208040780d0f107180034140c0207403240045280181664140c8001c03400b00392402c1c130780030007007105ca41e007100d180801142c005a41d803d081c40452240c80d8030055202d4902160140017a41503019001045007401c00e00841050340c4c3c4501d07020405000c0c41c604140b04074000000101440e000743d000300001501b80c0104e581c250f80a607240e8098403000c03a4800c1050b516100034808268022216101c0e810f42081e0f09c00240030108080380e0322128610850034072a0b440c0c00400e05010303100d1444590080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 245568597 1250 245567347 245567353
    0xd08151e0102010605130f050906040f021e03150103030e0a0602100906140c1306170601030c12020708090a0609080a06201207020c010201020a0c1104150e07020106050613091d 77
    0x14000810401010140c00c038907d05400c0c24005080014081803440c0301e60703808140301c840908540c00b440742d5180c4c103055482200300d42d480000e0042c1d40400484602c540f0000800e941c40d07056240040200f000081e445011f242c1010050180382c0d00801c101e90344c504000d50016441065043c05409071408403034041c101600c0e2400e0040000d240346c01441d074658410fa10440590792400d08a42c0214036034910014507500703102081041d032003500318201062280c640a40c0c1020075101c60400c03a0b1069104851659000038040d5690804032179000040010341005288246811120741c0c41301c0307248400030300725950351000d003402c18003050281c2508030140300499243c68002072086151070041e907252015105001c40b0f00019031050086032203041c066501d04200c0462035881c0049244d110900c00d500030303101e07443e400881c1820340020740103003441c8420701d03c01d0a02040190842e401600690f010708402c00a007100c200042014000300c0e10f80a90008607207444100c072040c24901c101d0701c10b140d40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 245569847 1250 245568597 245568619
    0x21027051612030504030206030a0b061314060306030304150c15142410140703030b0a06080405072d0b0417010608070b0307020a140d08151e0102010605 67
    0xc480000c140040c01ca01c44884445282c0b24481d451552080d0080100040e0040106200605000e0041c43c0c0120b030410002c120844604000385841c0c002481d6070342c44031010301d010405660094840c021020701901e4843c40d505007040801e0b00d0342700314090003402e40300354040004c503035101d0582c1c1e0500e580c00070040c9554407000450340d006800c1c06c00c11350b6114001d0070081601606809548204188440e000d400a59940c60900201100c0210040c05212005880440400b01d940091038404e210792707400a1603c0c01d5004100082e511070300000d041044200411000510004640080d58001e1000c1079443e510301c202c1c07100c01140c109090500700420180000e4501e9048003034029100c10240300400e20a0180c1141c0c201c1c3d6261040321602d52122100304032880408000359045159807058030703d125500e840700c000d14801020703001c00d41d62003100d080321090790200d0080d4220b200040656541d6400324001502900491200a01c8655030080c50410307a000350b22500041c0009003665005c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 245571097 1250 245569847 245569853
    0xb120a0b040b010905060a0e0a0b06040e070807021c080c0c100b0102010513020105030c070201030b0a1d070305010e041b080d020102091212031305070906090c020106060e01021027 79
    0x210415141119015008000032031345408a01490340f00d007102a00c1c00281e1031801c00e00c01700c4003401411503680c4540c1c501d00d103c0280c98100c000c02c0680003480e0100c04c030707040c0b509006101e030800612410841d008225030500034504041841d850700014030f4400030685812540c40014031407000c60941a104618000c910010700303401145944100340c00801155031045008001700c009600024001401040020300040c1380401900d80f0030f00614001548030084001329000d07c24a030040401d00380e490080010700b554100358294081003030303c4c0521640d450001b1080541d00050300080c0311110086218581001c50460600100719070760403034400f071210f1100a4001e40c00788201b1030040e02c1091149022180c0000d6140c401036070313812882c1c9035555110140c98070700846c0200302c40900072a00000368010301405208054103000c10700080c1c2c400000006821500e25030310030b40034000000c40e1032184da80c02251080041401c0c14010a110845542400580d002a00a4242808413480721414 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 245572347 1250 245571097 245571113
    0xc0506030f06030f2d0a06240f1a0a02250e090601080303190b13051905060f0105090616080702010210020c0a08072f03120304150b120a 60
    0x200d2050f400e486101c1092030604d502c0d00501552030040a01c1c00d40c81803020030010488825001d80340040c2d903207164030383c1e42e058285c0740310400070806281200070240000d2502442c080081c805031070300c0d8009a160146250900b1070000c0004414280487c0805072030f8000c0c001e07183c10038500e004200d280b014581c0044544013881c000c4060310710f10000010b1b0b4200002400506903022400114103542d01d81c141c1c018400c00b4002011249d648501301039030586c03a940d00085480070044000326075480e021a40b5012016140ca040030f6550a00c024800640c607201011500d00c802860300d20f41d140d180e0004580d080c0b09020b50940e8903943c1d0314a44043c00030540207050441c0c401d80c05d0350080d080d6203550030142d01604110341c00c00c1d0003160400b030006050500500c442441070b407801c0250707204c1c804c3c200d580c0e106a00d80441b16405042c00b204541ca824418501d40140012003c0c0c10341c00c2580324001940400c0303020407101039444031000c00780c1c1c0e1600c001204203803408045a024107001d20f40a45 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 245573597 1250 245572347 245572351
    0x415050c0c18013b0c0d050f0f06031506010e01090f030b09010c0507050718060905071e020d05090603060f130c030c030e0a1b150903050708030909130c0506030f 71
    0x3481c1c0b401048807013140c0c09070880c040c0f840b28011013851412110740080b258800000d80600024002040814051105030043c0303407140315410f40042c0e0600e030070100184480b0300240000c0c881d030411980e88400321b0003518440d410104c2032030302082d4071401d800103031112055074000350001030304608000704124024510718807964803200284a00c2240e000150b034540180d40009269803c420424010b408111504103480c1c158601e010488503a00d550740b070200d407000d6a071140054000e005030070140f41c0205000c2040303100c0d17100404d52540c50280c000c02c0c1d40101c0035800d1052074000041040c90384c07990349201054500424060039680ca034134620005240140f00d21020906001a00002d00e02034032071401450b291070040c0194441c42e0760741104400281078500034408080b80042462150200300b80315032801e9882d609002801c1d030416916100c20b607848a1801d902c20400320205464000c42039401c4120680000c140b003109140104d9031380f205030811030b045080030080200724110b040d4024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 245574847 1250 245573597 245573609
    0x60f0d0f050111090303030a051509011e0602030c12030a0f050c0703030e060f010303080402010c0c1d01080106060e010c060204030615151d010e01020c0306070306060f050415050c0c1801 82
    0x120100c62505102e29008149404c0d9154009000140040540c1d801c402d81c882c91100072640070307413130940c0041c1080600b03800001030b0001d00b28414407a40565603400c40900205d000450410800c254001c3e607c41d0514008201201c010022551500341900110742c450100d02061100b840d0220f4000e113142c014500903000a03040400c0503600c0b0b00040707030842c0610403150664405a00356201601e018002400881c100001021200081180c2034001c0b40901031448000e140843c44604140811506801809003a40760900c20001190005403400d5120009c1c2003221042c5000e00b01301c2c0080c01541c0c0090030441c1403000c41d40464500121304400d507518517407016041080c142d001c0703400d401082c030004a80790040290448640c043c3c10603109800c070510440340403074141c8001c281000300644095001c6a200d240a101903500a1030742c0d55054411b251041c01e180c908407105c0000c00c1c50350ba0680510000040c0310120460600841c2040d40340035003008000401e00c240d40282c948248120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 245576097 1250 245574847 245574851
    0x6030c3f011a010f050f03060907200c030c0306060d0210020307052e0905070b0c0f1903090806190908040e07020709050112381303020106060e011205060f0d0f0501 72
    0xc04403500030000d0b01c40e455034007031b0a14110f5440e4400d0049116000e403017070051001a0340640c5a20305900010648000800040c102c03190480317082c5494683d11000741d81c03207038102c0410000c2079200e4044100081d40c040b140e91006030f40849041e0f0841c4a0400701030814090142c0003a40808410080e08060782ea0070a03500c26210070001c141d04481204a00401d59004844100070200c0d0503005002180602030a036000940d6100300030340b42c08961281894040602c0c0060814150000348030b000600007440a0f00fa207107011154120050800030083d82d00954401700d01c418440c21134299000360000d0140c010243c2060000a5901c0c08240302d060400ca040c0307400421103464008525a5075540700da1003202c5043c5805c26078500d4110106d020002c0244d8088003181c000d1100080c070b002d21400303105c2b03880041540c00c1c028207440041d0010400d000344082d05072801e90340a2025100705280300303c00103480d121080054050000d9003080c3d5445131503c1c203103100b070001528840e404a803150b802 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 245577347 1250 245576097 245576117
    0x60106020c0d03080a0b060409020a090306050606070c03082d0304210905040216050303101d07140706060f0b0a020f0c10081e010e06030c3f011a01 65
    0x1c00001202d680d00c0200090004004262000b64a80201041c610700821550526490748031030002c98020200d42d1000641c5e684c0304100740582489440e4120034140d4405140c82e035039845410101182e441700406500d00001c8850520042c0d2150032003801c0d45100542140e1249920142160005d0b1001e0300c031902403140f5543c03d13146000e180225401d00c0d444080300315242c041004025000f510205412000316010000000d100348004c1d0b11030b038035200c4540340303960a08099418070300c880401f03140030615070410300003441c2d08440c60441030503001951a07aa204a0f00c1c028000e0b004541c400018550840c501140300e802000c094074064041c0c2d800c0381c1d01002401c803180e503110151801c40c0c3e003100710030041480310780c428200c10380d000b05010034181400f01c0003011414410804d80c480000180a501841078074075040c4401810300c982108c1e8141660b130326064500d14041407280008100385054000c03408403c02c0c441030b00640210340d000300091000100e00c103600a0300002103d0010349078003c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 245578597 1250 245577347 245577349
    0x213060e1002211b240709050418060507031d07120201030905071208070c05030a02090a0b041e09060510060906030f09020d120e010c050307020f1908060106020c 71
    0xc4500ca4441059005204844101e9203000380c02980140e83c1040702d40401059140403e1482c2040030094003038020700a04008220301c1405202001140c01100800c40c184601550700003002d009882080b1000506203812135060007804108410041800b41014104840316030190710281c03a42c0c440d036080340a04c180b240d0070140c40742d80b60b024110301004250480405948258002d0244a22403000c40b080315882d20505107041442d1001100c0310000010700e08108001d9681c40c41c010203003a001400382c080700e0340c00100c52480003000300d0002a41ca002c2000ca03a900c40d003201300106080e285c500000c81c02d004282d8045c00c416002625140c5c00c090108d40c540030122000760032210103030344001c159818504210080e00005040b011f6044c1c80d100c03018050782d66405051960f510503540000710b007440c8040903006240d400380c41c9061154000c0224080345d0003004852000e42d04544085509070020001280301c841c09040800c41915030304c010444240000b001416660b00e41c089500c2ea840003c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 245579847 1250 245578597 245578609
    0x7030b15030c0a180e060429010c05010f02070818030a0506040f0507050a08100e0706140f04090e070608060415091a0312040e1003050303010b1c0213060e 68
    0xa508480420000901805524000741c204001070749012050a402801803003980c0c4034a0700041402d03e4224140030301440c0c00d200340080d06200b4074500540d070100c4030540c88e00002c95070b9500e05209400444a080000c290311910340001c105204548a8969003049002500101045001d211545081d00e02d549400206000142c0c0e004006003040d5070340e40d980003811b41c6005402c803503600c41c0300004511555100f0500f005003412800800c0360280c01d400c280103842c02c100c0c41022075080032009009865101c1244040312028411043d81d503039035101441594800e907030084a583e4940410544500da02060a4085442d113640b94450740c1c550b02d0030001103850700d4550705000101100b08101c420000d401002d040000000c5042581c84c0c07040220741010400d01200900301000a0b00344004120350103c2e5030400c80c0c0c54000031403607045a861640d05d1006001c1c40300c0164000c541000204030310a9a032854401d451400d5440d40180110704000320314902030100400c01e881c11030011030400c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 245581097 1250 245579847 245579869
    0x110c07080303010806011a1204060207060f06060212180a0602011b0e1f051603020304080f0c0306041e080c0303150915100c0f1b0617070f0c060c0807030b 68
    0x141300030b40410b1340f03403a1009084404c03480e102102600d0502101e42d001c080f801e03030385106501901c80541d40300c0c44c52418804582c4022400c240c07651030701c1c00c1400305950000d1070702005054215110798034856100111a40120220890b0303210713803403400108540754107401403072160780c05140c4801003541c1400c0a0701c028510030310303054204210058891180381b0600140c0000c0c1142c2c2040d40c40d0020300c000200080c400d200040d805a40002030405c1039010412a0002d410031803400303030040481c06800281c51b10b00c05080540280d1106101982402100126501490340300510796902c41e0000c80c0e681c1c0b26001243c0c18458120314418000860034000406845080c0380444401c07050051020809264004060300c6c0800c4000c07248040060090100009414000c610000c10042650001500c54005401690410140b200c10710245101912031903004040307070038620800d1000c2141150100c0440b400603142d40d0400c5940d500c1c041d0840950307401020640e5040c49100010300178002c0500d14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 245582347 1250 245581097 245581109
    0x6071a1e1f0e160c0303020732010209060d05061203040609150507020102150912120402040509010c0203072901060f02012a030b04090c0b0d0b030d1d030a06110c0708030301 76
    0x190b040180f010b80300f01c06049840c0e100381801410409907444503000716030701702e052054001200e085e40748040c4803280e02525050b6004002c2d49084064030204006015803c4409810b0352501c0200d62155201070092081d08000c60441340c03103550b50031000b001d101091041c0d01d90f800f003a0040356500d520401c00c403a40309806800400d910b000801c404044c400c0c0c018500b100501400410030040418075006103030720804845084105e003010700400c811100050309840c0140e14024074500b810341c000c410fa610700758209801e41c0c08014204584110b011054180007860810440080b4074140c00c100004801a4954003c0101c412850101d00240d800e81c000e8031082600d40c24840029486a04a202c0f1500050310100d1213845030340c2c5084c0031a0031504401501c5c03202092840c0881106d10600c0c0e40c0100c00c80007050b5900291401800c4a5414200b0141d0400f0001400c416a1010000c600500c0d9100340d04001d49403218104c0c03442c0d500441d410009c00c0c000c1220018101e8000016203046e140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 245583597 1250 245582347 245582371
    0x4061a191b08130503010606050c1216171204030c061a0105041a0d11070b0705070807020603062101151212030207021519030b06071a1e1f0e 62
    0x261182c506070340150101c8050038002039030208442c0c07428042c2d0002007006071509921291380c0382c01036080440441a00c03214440c01e0203404041518480c40704142a08080c68401c14a12101812014811140c1400e1400e4041b01400105644a050625018044d0f80104140380d60824048a4030400301d0816001071000d000601c01441c20a0030440303030b1130083c0398140c580303500c8080034025122840c10f08010510046100c0061200e08007059502845515100e4a4410b1903504c080341070041c4a00680180f00102c001120364403242c4a03901600b000050500055809001050280000a0b002c610415019a0002c0c400d0305c2c01c0b003042c80c0d00d80c0c0100090050328210000320001c1d0090301c000c3c0c0c0e010203e83d42d80000c0540c2c1e10004d03c09140300c0388856019204000c805015110070134951801400300b00440070208440708a000c00c1006d1201c1207110780d485d46003e0205030183c0c00c0c4810490821101800042211110078079410040f4000102403561f861f00402c10b006822100c08080617 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 245584847 1250 245583597 245583647
    0x6080102090f060c160305060406110c07030b10030b0f090c06070f060e071805071d0105180a15020102031501090302010c0308040812010803090415140f04061a19 71
    0x110f860300c0034141501118040f6030704050401190a0191840d510a441c0358103d10284000d000c407a0090100a150304122203140015804005a952090340b0020b0691000c0c000072a61960401c0503510045030040c003001c580b400d0441802691034000c0c1c90202d03141c89100c0108445040031010303034000581220007544400104e8a07060060328034104446028010380c10040707a04001860f0381a00da42c04094005103924044001030025080090305041d07244034501c0e121017603071303100c02251f00c0303040b12034011800d005e8410701144807442580c100d291501d150426190030700d541513028512400e410031034580054003031801564000001d01020740020404050000424090b80105420500c80d040741440c1035851034207501061000e800628294000040c0388000d403806006e41980070040c40c1c0400800340c905081c04d4008c01004d10994029004907081c1e5001d0394640d07010740c00400d520303450140c002d00d1100c14100175600c0341d1180100440184449100c04d4801e02c0e2100883e030180002240c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 245586097 1250 245584847 245584849
    0x9060c0605040501060306020a0c03090515030403111e01150504020c0a082506050106022a010309140712140705060f03091e0601050406060206160c080c06150406080102090f 76
    0x261100820640b0290341711440000080c50742c1c402054041c4081c3c2c0c40703224403030007032030010546210340e1b100030710480c080d0449002c101c00c2c031411641c026526080614690b01051b03069800c10400c5139000e40203001701c0e0300910307000006412420181248001400050307450b901080102e0180c2d122400c1e8651010401c0000034801c007000303068030042d40010903455031880405888006070120200c40e6107803640010440d03035404000060151410801c0d1201e01000c440444480148900200781015120b900e00f00a02c40310880a59102ca180307801d951701d0503291480da50301e038054440110340c1100711143c005402e800c01b04420080d5038004054900c0d0006043c0d02c02c06c5600301401d54900c9001d109038030f5541e0061000e03240326103806040030380744035850030b41040102e902951080d020340d0804001c00c9440c081c0300300c5d80038000c0701d02e00b00500314564900704003180f4000d01003458661701c5a00240b045284000360300c000104021601030001d01d0301c4607802401d0740602031540e0780101d401d502440007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 245587347 1250 245586097 245586101
    0x5011d040203030f0c0106050109090902033f090906030a05030f03040606090c08040203120901080c0a140c0f100b060313052e1a01090303030f021902030a0f09060c06 73
    0x107000404980c01c011030b140800f41590b010b0f903500021a95604000c00080d6000040240104901c00302003200d0219900401c0d1290008968408070002d03001030102660f100080d4049a85050748000340031880d04028000607078000e401c0c036841501a040043c0083ca400100016800c0c0d202c0051414150b4000c40640c103608094400c80d52281c41e090081480035091140804070103803680d449015051600515043c02241410403024040401240d29030343d8001e010a83c00024001c15641d43d0410707260100c520004026200c2e4801000043c1d07440f01001c0001e280e00d0708404403080d5104c00200b13a4010049452160010340c00003810700010310b01c14000b03038001c20514091025502a030382c43c10b19400d8510b280c008520301d011032000071030040036250721a81082422071b244188a1542d1400060040300c01803100404058551155003520103030b07901a101800d1400e21141741002c140307a0041c0d12500419222800203000748801100d861040b103980c4129403c41d200e103d4049000c1c1c0344d03080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 245588597 1250 245587347 245587351
    0x6040b030c0109141c05060f0c090d02060702040e0f0706111f05071e0f03050c03040f021504091a010201051005010e04020d1104060e0a080f060c030702010902090406050108010b0405011d 82
    0x1c1c5c001c42841040301c0303032450b056210001354442c0020300f16628101c22514601c0300c0150080d01c1d01403003400f03d02c1382c0780c64040454141d82d4045440d1a150078080c400100070381800610034005008000400c01c403010700040c0101520b840b42c03142c1c1440904810760036500c64155081c511503194181c5210720b041e80703642c4800e40140c458035080802c05c00180180804d061400600307000141000304841103540e040c42031941014540d1021807450805441d151280d65a5240103485240540050200340d140e17082100e0041101c0744043c441c11802d40004003448403421080d5000d942801e000901c10320848841d80b043d600161510310ba540a508144002900700017492200c199960800da4a503048801c0038200900890b81c40e2810340d140d0200b40310045a003688444003e5000450218520038049031283c0e121180440d0740e916645e035044e040713000d440c1f11000650070115074020300080c8109500030340c1c103032003420b802405070071000350520045640c00d206032000d00340190981c0400040c0740041c16 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 245589847 1250 245588597 245588599
    0x40e160e010e0f0907200f061b04030b0703020a030f020c06041209030803180c10081f030807050f010605120618030408060703020c010f18020405180a030806040b030c010914 76
    0x951050303c0140841e004150590304140403c00d103048042d0040701d5200240300081c044406442c2e0001040c600aa440320701a00340c00042c000001d403c00241d21002c1554015500b140109120341801c04014000794000d800b1900020b007002c0502d51541d02078000c0313600074104c1e14003d00e425641d03501c81d13149007c0602c50140400c601c100001001c04d0000010314000c49240c1c04060001c81201c008038030301511600800e009031540010a056141c1000300d5550104000388461402070100389070428030201341c0c10060a509010502070140440042d0143c92521503000820034192100108080540c4486c02c110059005400042e0711002040401084804110880742419100d04c1c1d0582020012910600080d5012a9890140c070b030034052f4800700039088204000292526014201c503d4901d40080e0040c0d4482c0c0101301c04e600c00341010910440104141c6a10101700e140007040388106844152240381083c12003d07440ca80030425035010300d016102d000c0b01e586446900810043d40e04042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 245591097 1250 245589847 245589859
    0x40f1b06030608060117030f0d09121205010b0f0405010c0c05041806110f16111e182e0b0301121a0c0901120209060d02040e160e010e 59
    0x28058110280508216100412101d00b00305041d4039100050f4060460301094036110340009a000c01154000b15440d2283d641d1001c0c8000307020003034a40e8600c010003580700c0042c0202000d41c000440c808a02082c4424015642d84012491160282c0c102120440504001c02c105960050541d005124492240c0481e00341c0e1f281c2c000780c00c842e840c0200c05907028003124500200301c2140324441c80b0070528800d4074100700101480520740c0c05890141c54101d408132450304103002840003331021421008000c00c02a40300e40307480103003400f00380b505039000d420946404c08842100000240c4100c800e182d68180481c8181c0030a03102480e5010340c00c28040c5c083d100890304107003080c001d6028100580d12601c0107901841d101c220200e896521406030402441071004211900085403060a001d02e01003000b1005982843c0c020b2180c42c02080e4080380004034107a035200207802400448186420b4000c0b182d45d015100c81c42203003000d08810001e041d040c00e00030958040e5250404190001e060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 245592347 1250 245591097 245591123
    0x80d0506030a02030c302d0d050306030a0b070f0909090b04111f020309010f03090c0e10050307080f011b080406021c0915050606040501200a080a0908060f0609040f 72
    0x70106d04e00240340c0040e80c42d401c80084016600ca81951030301d04403101d080300d103501804442009458201c40e06580c070400400201041290380c0410161300c03050f420070a48000c2c0c0c14031100c0a8580a5060b40d09000301da5661790001e80380c4094130038400041c4d0424401c0695964a6586050f007001d81c4654503400400c940b0108484206c3c00700c1c1c0302100e0100e400441e030380e02200c40090141c50f07160500c2010503007000e802c0000103110044070000c548100500c001c050f110091081c86a1743c0ba034000540500c02e00c400040d0202001415107000d2600c000200040d1020a000240d0f045404184c0c03004103200c54042400214264014185e14030181080c10200e0fa01a034804265071458a00390b4510010000141403549140b02e0315400000403108546824038060010b480070349405004851543c070706109844102c024409444800c0c1e00201c025a901c8100d040a40792220034006c1034001d01c0790f5000900078101c18503606010f04801049140c01c1d581e50f41e24150180c0d980c0c04200c03003050750042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 245593597 1250 245592347 245592409
    0xa0503071a0a02070e010f0f0f030816060e1203100e07050319090602070f140120160f2108100905070903021e1516031d03030403080d0506030a02030c 66
    0x3e02076011f001008400c982c410318098004d001520160000b08020915640410019441340211105410640c0e09055491000e003008001071460034407807003490059011100221150340d0065110b104982040b04546031200b040c10300c2c1c1c960886022012030701c1000450046010000809413141d510f4801149100c0d0907514002aa0440b4000311000c07128071690408001c03c4a650303034441c0a201380200a0340c1c00e0116924035070840704011201c007000c00140722120320511030600c285590440314100b40301c111858a01d8031460f0310407000071f5501ca83d414100c1c0b120300c2200d146020780101109030184a00b8000c0030f00080202901440500040210000050b116000a650595070751540300325442d400400303010101c0602c0560800500041103006426100003003242e00c070f00d405241a04070f41c00c4800e403240c000c5920701000d0382d1501c0040750000c10001c02030014200700c07441a505100b00d0710360700281503440d02c552400a50640280d8a081202c0c2003c400800702c954200c2007154400c00072903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 245594847 1250 245593597 245593619
    0x150a09060c050403030f0f0207050f030304211515050103020309011517010f0203010e0411120312150907120f0204050d050706020705150901120b09150a0503071a0a0207 74
    0x1c4004001c42c001290402c180b64214200c12220320b20307810402a80440010000d485039002e010303e500c25030503088482800c1d01c1c1002a07502501c9410032403007040c0c50050740c01d005c4510701001190581300142031407400002900901100b65407603041d159100c0d003488011f4019400080c402c1c210396581d12003007045401e1052564000317012518005202101c82c000d10b600b035a001c80c1041c02d8444c01003004200c0e5110f0a11952341c090740015814408142410024449828011600c40d040c400496281040e001f020300c9070740982c039910b14604046000798140000e8000450741d1001151403104196690342154000c0d02142c544440d006240545860000e5280440c2040a65099024810034002e0b15010450b0401404080340d251403007410500700003c81c0c0c80740102030390402007542d0380301800359101d81003402c044800800061441c030f007402101d4002502118001d200d00d10b41c1800107002d050108400041d610121585480f60800c0c1401117801d6211040e01401c41c0708036400003422000301 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 245596097 1250 245594847 245594861
    0x10060503030a3c1e090f050d03090e100806060909100c031508030d1401150309031202040b13051215041a1006020c03010605010824041107170a02150a0906 68
    0xe030b29880a07645003400d02c0c401e050740614000381440417060f8140f08244c403540b18082100c20407149a0341188103031070229004030a50b4002081180000144003040920140000c203464092046070a0f595070700e420050b500d5015a0300c5e500c0394102c0100240171481c241c000203000c1501c0d042c007281c500780e0303486042000c5240d40e0000c60143c0001c94001c0c1c4000c00c5004580580003010501e100700c1d41003001700c00ca0080340c6440c660506940718484400c06000d0703484011190801d55046407580e07079542d60990207502503800304401820a48001c10246800e001180e5840c4108008141214a003a4008688800074009440a0301c010f00784507000111001c6062281103120054100c0c50700d8084040d14001385240081d100b6410504c0510460341e01ca05000d6211078000c1010071505003c240c414603005520440715040741c20200800c50a000100040074628841c0c0d00d01100f1403400d5080300490301800382d0580c0142c10807080c005020035014a05904400705000000351000f2a9594134111307507003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 245597347 1250 245596097 245596217
    0x1a09070e0c090108010e150d05101a09060a061b080c10090c0602030c030a0e0f0d06050105010e0a030503090906011b0c060915020d05030a140910060503030a 69
    0x19481c0b01540c4c41440c1500400b284101008a802c201040d4074403142d0358000940118810007010062000c00c01c1030308014202000c040006902c9036440184904281003103038080e000b940089411414607003600340c2200e4040c1d5402c6400e6011007010003101408140076242207106104c4010904411b10a801c01003000480c0002c40110364a044800c40700d0591141003590400d100b40e000d5200d02100711140d8012501c1c01001d0740c00c0c0240040c40d44100040751540003460740d0f00741001c04c6003e40c0854181c610980b501211076800004015054415000003001b0350001d02002105080a00800e03400c842d05041c401400c074200300503400318400b0b0000984047c032107a98104034940d00040c180f40900701800b5520102c0070310210103503982070041e42d0711003001070010000d40c2c1c0600301d5009c0c07460f094020740d0540c85c604210000c15640d070302c0d40400030640b500c1d1550015540c034000084806030507903600da0303100000c10040d0b00c040202c0045090303040d0600035014154040300b4000d90600d0840 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 245598597 1250 245597347 245597371
    0x15050105090601020d0503070807110f010507022107020d03020109080d0902100e0306180c040c05090a0f051c110402030103030309110a0501091a04261204031a09070e 73
    0x21400c0204448008090300320342c159040007507103181c020b42c440d0403030740e0110b020704086510fa102e80004503824102640304440318003c41465410000381904564011105582114003681e1404101035003c0344501d402c15151500304000d0005051254400302402d00038000001c0300881d03a101d0b089180e000c001030340c1005544590781000c41c60a4404001c5d81c034143e183c108040010700b07001c6035440c0c0c0003030840348020314540007020011074204481c0d2620207000d081031107400040000a40240c1060302c2461040c05211001709a102d001c4220804666004003125030103980180e4010a80c2070180040c2c0703030140401c1210180d0b443e9400114000e41c0300c3d641c005002c006034100b400c9003c5004001601c103401420301000780760f90000c218410b640c40c0041400d44031490200404441c440e50b84007c2e09401000c0c1500b0b407020a00c064240341550b50070644160300f80b00c2001c961035104a0200500c1104003404142004040d500d10a6102410320201c0e480381341c6850640b18889003c5900146441d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 245599847 1250 245598597 245598599
    0x601030f170a0503060909100f0e060105060304440703170103050622020904050d021009031b0201051308010f110c0d032f0702010815010c0816150501 66
    0x4078102246801062241d40202c0c1410b0701241c0c01040b41c4009005544100c0040000ca1043c070820b11040c2600406414200718604140c41d00da80500410040c40110740110400014642048011a40301d00d5006061a01c910300c007400043d0780826a5800107811580d15084034461201d01440c8640302c10344900740382c0c0300c54052500606940d00c1c2040d0342d200641c00f40c010030018400060721900071983d21b02c0482003d207008c074004901c03030f1030280103540300310302030280418444007080c4080703612115400d842242800c3c445902c1515002c6800400084036510000c035002022108901100c2c41450302520703061078a10405a505036a070003d0780c41da55203100c160128801885025034540c19800c4450800b240c0d901d03801c0c0c89800c0c21140c041815111031800f00144070400c030f4040000c018001c04c0000c1510030f09104080d801a0000300d01080409000c544507002201c5504c00702e41c0140d4500140005650303603a001c1c2e4000c400343e545540d40380d0078080c0002d811102c60101c29608100001115 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 245601097 1250 245599847 245599853
    0x803040309090f0e0d08070e040908090906030613110604031401060608100b0706020a090b0417010c09050d0f170c030705010f02031905060307030213092616060e0601030f 75
    0x9030000c0420310001c13883c05502c22000c600200310280e140807507041c07a00c1546e4440f0426642c1d40d803203100c036641c090300c0c064115082019030005004c15004c1620b00c1400c960703924091555440e0191042c01c10b81034160100030002e04100c00f0350302016800f501160a15030f5039540e04800008035010182142d4480002340701007640245190741c4010340400d1001c20328a0810a64402d200f420009003c10fa000610005130078012844a0005c1403800740082da2182d840809400d0003580c21031211495082659a1b03a0311445045a1ba060302c00090045641414030354440141d140a10011174030f01c04140c64000d80e143e250000780080b501000041c6a64070380030302c3d015007194080c0b0f0403002083c0c814014011102911300501c116040c1d106800503540c0c94010001b0718022556200942c001c000c05494440e185d0a900181405445103000d0088254602d810110550048580c888183c0d0f003807011076070542e421001c424466006003000030341c8000050019044c20001d810589203504030812007010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 245602347 1250 245601097 245601101
    0x109170a0614010f0e060f060406020a0507060302040308041404140a0b0a080105070e241818010e0712020c0703080406080a0506060720030d08160309020f0405070c080304030909 78
    0x2079500c202850400e0f50704042c5003a140490710b014142d6000c0e6a0710002d02182c0b1850500f80300c0200c010078513a165a42c481d0020b5a560000204036024052244001140c42c000d001f0399090302e501c046010309050904400c0403060b031b0f40480490f840f94445c1607685100c0b104000d044d000e071080a20128000c54041d09101031008254012883c582c903040801014a42c001c0c140508294221002000d810300c0c40c0e0510650074900a00b090448800610112415503001000c03007440b0003510011901800c40300c1c4050030300e2092042801541c281000200118414800c510800642c0c4000500740b1010f40d003014908000c0c1d400440740b44c131000809000c46500030b4106548043d880e0340621441c0f0b4002d0100d110380c05809001415144181e0b984542120300c0040703000e5403003014040302e0b11303220002e03001070042c50203503101030040800d03d030201c03042f07446802414011500a0098205055800c060000500c40149030101b000a410000000120030b00b0046004502076510454068180344000e41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 245603597 1250 245602347 245602361
    0xf1e0e030c06040f1b1806061b03081902030c0307031104140d02010306080d0905150a09050904141b012c010309081b031b07180504020109170a06 64
    0x40503510038454001080c10004545511070b500c1694180103490074a811840e690000c2e0a20340c100000034004144209035a43c04071403001c84c120188002036071003a059403114154900c00c0b40364101c000c164800300c3d01444140c2e401c41e90302000412280000400102246c00c1999424038944000040c0084998103005506008120030f4a0515061400c1c8028814201003900e59000d0080381061b6400c0d0781c082e034460380c000d005002c00c2e1025600703038070310041031800903026140c4607040111f40c20160b0023982041c0c1c1da240859840c1d401040741050f0801c030b070041004000700e904082862140100c01000e000072000c5070001e26070180c141d60702c0000076000324001216002034590042c50b0005255501d029103c3c245801c0c03c00064040c110b0406034081c0c03041e00d945c264004d15000001092100000c000d0814152001c034064000d642c40e1000d5460300564800c006c0f0116807420421003003845640807541041c414108104410750f0b843c841e640d40c420f11201400c0e035822503405031003485450b0017540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 245604847 1250 245603597 245603621
    0x2304080303040c0512030d18020405180f1f110702030d02030310051c03050702040603051f0e03040e01061206150309110409050d0309061409030a0f02060402060d0209040f1e 76
    0x42c5005c191406640d5a801081d2480441e02c0c1c0392040803820751316007c0c500300e211b50050000c0c007240c50000c0b0000c041a0059500300c01c03c5c41403c3c500c0c1c0c503100c400f046804c41019044158030560790051080000b40c14020132044c91100300704440001641c1c1000b0b00c2c00b960900f0340255450385040c0200002070201584503034054200404101010026a000a44491752500305541c81b05000c0c0040780c001d14090304001c0140c03003205034000b01c90155120303601c40023161003000c0c032681082c2e14140740c5900840c131803040c0c0203961038018001e050040345c8050140400100004d1680ea0b40d1001d2035200000d40d11100200360366000990a01540c000c021410b45d030151410710007441d440d40c4066070b4001412141003015540e070444010000d980d00055100380310900c222400d0304000000c140ca07984407070068404201c00c1780350215070034000306000d442103070010310b041c0c01c00001c150b010003c0c1d0300c01c50019502c5a034841031205141007903c11550840d50003003001c48034500048140b000c5400c1d06a0203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 245606097 1250 245604847 245604859
    0x14010b040b030601031805010f0b040e030705070608040f0b07091401020316080c07030b0a0e060708010f030803151201090209060103090206180a030f0515011a0a2304080303040c05 79
    0x5000e6140000101d9400c0f10b4280b13800076019a0000d840f581480074100020525402c1071320310740c00c99034a81c0100e500c50b001150304104190000360b0142e501e01c40c40c3c0c4d0082413a0010700c3d04226803400f400303c00b603005006080301400e1480c259900f48403540300300da050020481e1a0000d000d2701c0d640500c00390801c8020700085260a0750360020880501a101d0001c044080020b6106904102884150700540d80314010125504214070547c1c081d260452040009100d01800122014840c82290f8101c450704950140460304549613840a60f00041c400415904101c5940c1804d481c1e250251440081c58030001842e400640b040003140d00c00500094105401d007034441380541d446600700e602e1300030b9602000050b0401c1d60046081101254809030600441542030704c148207005c101c101c40c040110400f00c030700742c5c0c9407190700300c002070305610440c40c0034004e03c400c114040c011f0440c041900d6000f140700da000030006400702c80650040c1c2050b212a040031003880100613040400d40040c010444203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 245607347 1250 245606097 245606099
    0x3160305061e180f12120609070516111c022404060c060905030f04030b07091404090204110c01020403030809030a020d0c24020a020f060606041a04050d030314010b04 73
    0x1c45188030b480038010b00c1111100d1001c038001d14904000a16a5013041425280740505408080f0035540001000c039842e24030840000710185855010319100d05615100e80d4100302d000785a08031040718028048487d034600318080500340d56454120250020091404880d03154103106000d0148140c41c8000d11010040a00c507907034580803820346040c0d03800742c541100c280d011070038031102900350380f54082c000340000110710000c0111140107005480c0681c0b104003a030b840c1c0c200c044800140601c540241100550208001032406400150085000400200303a40144c1007030251140c0c000003000c65943e500142c10810940c02c21a815401105030f0051403c0c0220342c000a5100c10501c400c001c100a0402044000c0010b484011284500c3ca41c10f00d03441d525024002c00000c1d48003811040261181400707a01001d140001c41e0b0344101c90107851181000d03e4100c09200140f090249444500c205000126071612030030f90640c11240280e40214080d04580c205000135001a0060720140c4070403c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 245608597 1250 245607347 245607391
    0xa0f0908010213230108060112060f0b070c0806070903020603040f1203050711010605060405040509120f130905130204023406050601020708060103081e0c061f032f0316030506 77
    0x450b1740c000809c0c03c00605640350400c400300140940d030040c100c0102c2d0203001050043c000c1000c0c00c8080c0c402c06041005a444182055642204441c4040040d020140901c0141801d02c05036030000d11504034461401c0484d501d02980c0e01666440d0000a40d88030208503219501c003488000e224558002042481d0400010500034401c1c0c0c002e0501a40c1c4520224012900402203092400c4920302c1c3c080d00c85902e90050b17022503100b03001100c1c5e5017009a40102e010070851084601514215580c140104001d0b800d020294002c000c1c0c1100003000d504500184d110742e0240c0b10341d00c8001c00030344425484185001012110081d009504543c0b20101c1489280c4000070740301d0541e80c0000c01d40c1d480d0111289990125200c4e4800140d494802040306050036200042e407900071201290220700d1841200303054040e0501c58403020380001500e150300700e80401d100c11000505406106200500707040c001c04689050a07020718a01101800c403000c1052001c1400101d4000d080d841c00426100d031001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 245609847 1250 245608597 245608607
    0x1050a0f03060518071503200702100513090504021503010803070308150622050f06070212031308030307021015150207080106060e1c05030a0f09080102132301 70
    0x1000c0288510b540f4000304d0800e0303100c01040a1841d80250482d902e1580300c1d05403108500d0002160b07400300382010148902405003107809400801d95400c4182414983d4080014150000030481c0a128003040b01d20040c529440003003010380f01c40100880c00d41020b1051080d0b8981c203800450004138140010b11044402101310342d10560036240807441512071175000a540310045207a964081400210711003150b05240a111749181c105d011008480d07610400c1c09100d10400c4031a95000382c04020050041c5002d030714100786072071203004480c1003241110030700d0120085904080060f40c00031080014660f0304101c1c05000e095104814030100e142218086600c8a040c0140581c0e010402e00c000451442040010000c1103e800288035a039911000a8800d440d4802c40c1d41c0950702c4240e01074008450034000074540750b8480002d514120503450212081401884803a04012840100044962003400541061020012034040080c0340c03d10758611000021030750f151071030010180a500380e07080303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 245611097 1250 245609847 245609849
    0x2012040810020406020a030c060209130c030e0c090c0703090b0705150c09010c06020304030e0904060b030d02032809030c0312080609100312020c0607051e211e03070309020901050a0f 80
    0x107007003503231402400d49040300190192402080d0401e180c1c400070110140207800000d2552881d403010032210351000391682d180c12400102035088540c0a0100d82180308120052008500900d005400140c5a100c0c81202c0ea100803400d6910b0707031000400910400d82215100c0d0046811024646010038100028080d01c45000740548840c0d404000907003818010201e07802c01c950002d24800071480c16141c44001854100c1080e8084e21840b400115114000001c1701c0019080c07004100042031030f07000f000c0400a092801000f000742405001000540b0180c2c404090b5100d1100302e00080030781c03103006000c01001001e80340310f98128014032142152901110040c0e0b40c0058200d80f902040f103900340c1c03402103c1c041003a00040000b90303040c2840800f1070080010b00b41c0c0c003440e0640107019200c046e690142600100c841403012425a580d2480b83c070700034071600d8000c0b444580f011016003520221600111806c0c4046511141c060007140b40c400b020a001d003070300319141c00c059420720012000d42466 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 245612347 1250 245611097 245611103
    0x19050c0d0e0619093008030703180f0b0c04120f1b0b03090712150e1e03030a060602031908220807060b0307152012040810020406020a 59
    0xa008180040d00d590040f81c02070031000d2520103d200b038003180204a03084a2250700207140e9400303854441603910105c0918150094009039500c2d04843d2100c0c4110340c4081c0005050680d00d95000000000b039003501c03185180a100c0c01c4130100902d003000041c0400003403d031240385c20208403e100b04001c0309260491a03805c0809240c0a00c018504102803000300002000c403c00000000103211940d0301c0103522913403a000036500c1b516660322846590390800344004001a1084402c66580480750b401302e980003200a04907445804e05443c40503101451444110320b540000040103842d0030035000e19030040006100451a016001c0c90040c091078203c8541410844424045490304541a40100c4030240d07030006e1029100041c03500400d41e60107100122400e500340581244079103404940749040f00d00310181e50b0402180d8440032200484009403002d116030711081008641030042000202010900c20a190b44504185040b460711010800c500409401080203010b4540d0100e401029079074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 245613597 1250 245612347 245612357
    0x108040b04060504050c09131502031b0c010b10050706050609071409010504030611030f10080d0e041503030216050a0b040e06030f030c0601180b030d11012019050c0d 73
    0x140c605c0c0a41c2050403d2481e82d60145e144018060202140840c010b44503120300800c228250444100505a00088800f100500c4a1703818480361401d500008045460510000180300e1105000042292816020520003c1c0c004a005030420141c0d01c0307001d42009040f00c9940c0a49000071004001030030805008040f201c0100d602d20300c80c0d02540c02d41b400380d03030711100510020100d10f0301d81071140c004035800c0c2401ca4111011407446071040009105903201800a0b01054181c080c05444150340800102d4101e9030380e0103001d010307074401c0b8640d2024500c00c4c1c1c0030b0814103083c0303880d000c1001810b80040d03114800e0340b1003c00c4610496401c0320210b64503902002525610000041d0a084080c0c2352030946000000d44801ca01001241040c1a51078044407000b05280d0700c110701c0103e558910340710360107030301489000c52818095078000c000e0012080001c507800340b180740028510406450b4002a505d40410150343c0c0001c0d007000c0c50781e06c1d0454a41309080202c1d081c100795807113079103425003000c0c42 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 245614847 1250 245613597 245613601
    0x3040b0c2b0b09010b030406051b0d0b060423090a020c060105090c1207020d030501060504181d0f15090114011403010920040e0d0207030308180a120305060108040b040605 75
    0x80442d00070b140701403401080e014030341d0b030f55034010f001c1076000310307803c60b88246040005890408028100c88000d2900c4500380c1c01c200262030f81c04000e208140d1091341c8000103001c0010006010321103060608848540c2488020007242407002412016040e034a9280c0181720000c821000064003504440c1c084448100710b44802201519610a482a28004280c1703041001b0620f90001010b605650807030341d0400043e07a86003400c95441c01540545100710716004000c1c1441900758000210300c00d6585001d100c000e460402c5146081c8400000b0b0a180e0031000d000d0302602007004030951300220380c100900641400072210038566005000c0c160b11040c0c00d854900e00c03510b003588104004e07540000c14906a8110052220302403880e0042e00c0c0c8124113002c1440b010030804182d02e040320065400402020382555030544420f940100804039001c1000060311910303c01700071201304980224145410045083c8008003034400081402e8140001401400002444004401d0744260000c10000d10350b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 245616097 1250 245614847 245614927
    0x8030c13031b2c100b071a0105010e0d03050309010e0d0f0305180a020d03020a05070311031608060c1b07030605060a09110313031e02060603161211131103040b0c 71
    0x2a092a00540e01d65117021a082c420090b13162028000b4210040d1030080d20f07170741c4800456000b000c001750703150085150950600002e00660203103401c0035004002241c00e0500e006124600510f5084031400584443d491450b100c0d0988107050b040348048074080304552401205a0b035a081990b002809401d545c8044000e040c4241302c400011030303010050f81c28050362070420b5001c400101002c6071080c019450009000ca000310401d000f00c0c0d4132400034009503a04e030300f40805540c000c01c1509804840c907008000c458102444184d014610aa2000030707941011024400380381700c660090702c078161030001010a46c2d98907a05595100c1c0340103221514100c520f25040300c80c00c02400d1403480008058001c01ca41640100d00e082c881c903c1070b000c90f007060400c803c00c19003281d480e128081a108aa60f60b1202060340088541c0c2d101c54090f041060b0015135014150889107100956141408084103000400107256005a0440542000709042540e0124034140d52040310303800f40a101e005100510381 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 245617347 1250 245616097 245616121
    0x30609110711130e0102090108010e04020f1c020409050d26040807032c040c090f0b0a1e02060412030203060306070305040203010b04021605010e0a0c0308030c13031b2c 74
    0xf0300a14402c05110f101c3c2c08010316130203508034030304550200b461000080f0300c0f8118120380c070348266002041c00c080180a041401038400c07418a212034541d80c00007a0401680300c0e400b03640c69044c0721764010911180600d00043c107055180d20004110300c0500810300d800a040c400c455001a08400441e82c0c0e0001840d0644048000180780711f483d280d000542c4001130446c29059030000001d940c14031040d80036600481d0a18030a0080f10105004030400303000f000ba00b1070181610851501700a0744812400847d0912808024500c01c0164042030800040004208400d407407144182025825030030001d001a448000c014509030406039681b00103801e655094000202007200075008564918541c10504003811001c0c000f5151503003010041502410001150384103a178000e403102003c581560740c0c01d41c07035070300180c001703641010144503101c04140031150100c019840760303002510030003520031100c15800d015402441c8d090010404003206416100d8480220400e00d0404006036483e00340141c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 245618597 1250 245617347 245617369
    0x30703080a1a0d151505060d020f0903070e04030f1e0c0302010f0f060302011106130b0c0724050f0c0409091716020a08060c0901120b1f030609110711 66
    0x2500000328060002480b4940c013140900c0c064810090142e01c4103a5841001024103114040e0420310801111002410940c0130f0149103c1200119261210800001c1d1518107940c10804180488109101c201600708004504c002140e00344400100c00c9210603080e0002000b02d9a010b108481c10b511081601c06e43c001486082c08507801c000d21a15080304000410303040c00200d011034500444110700c2600002d91520844120403110341c40c440310303038a00c0c80307495025096841411062107810005503a0100b0304002c1c00300c0c0c507004400d41c5400303001c1c8070907503c000d8455132202e52200e06000140103408100e07810b440140300c002c0303006206031800070b5200b61180c59070f5038400f00108039415200410072840441c10300807a4184619625400710131740b2034606484040340c001c000c104c901e00c00d500603a42c1e00d005481c0400d0004022846a000c03805455200c00da041821801100003045640c0604c5100702410140804018241002e8010400ba100b1268090811800303554600244e07962816600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 245619847 1250 245618597 245618599
    0x6081905060f071106040804051e0f22092105090d0206031003050610080d090b0a081e070809071a0403150204050d0c05010e0906060d0c0e120618030703080a1a 70
    0x3485ca4501801c0c0004d058000d4060b244c03050000c0d40702c46004c6e0388410220f0f05000c900500356081400785008100f0300b0390301c2400141d5210000e28030a543d0402601c44d04010500403030003044004064a0203003501d207988214803040c0102400700800c00d8541d50744885460342d041c0d60013552910340300780354090360065900040c001d10400080000316900c3c8503c00e011031f00740808984007600040015200700c43c4900a40c12255000c0c810800e4980c45a11401d4001c0140c0201890003200f0a4440041e590102c590b01c0204032100f00f4000800810800b4400500d0141aa11100500030150454900c610300c4050409200000c00502c0b1090700d038111401440c0040c1a20111242483e0012006045200b0b031404211080003412060a00d1524144501d400400c05403078020f0b881d0500b8002c0600311383c0c1c2d0041048070f1040050319181d0180e081d140703070701c00001047c0625140a2400c281c50000308800240c0d08240494070000340c101d054990040b515403400b02d00b10046807080b9500f1300c0221081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 245621097 1250 245619847 245619853
    0x1a040506011b0c030b0907081903031512020a170705040e1501080604170f0304030c0f050304061101050c0403080a1d0a0e011401031104090225050106081905060f0711 73
    0x40c0c01c003c1040342d0842200d02c200c02c03192441d521740301c10704e44416180c49440e01a4100c0c1143c0004104110100200d440c401d050004034074084c0c039846940140b0603004409003c100300901000c0d0314000c6030110003852200301a180350980d41d42d40c9901e4220a01c1207034000c3d51520368100143c0c109118007282140101c86a078019a5505035081c0c0c0c60101343c07030aa4074034405044691440385038130102e89a48609903e21442c41d112603030101da07074083d07010060b100711103041400c10005406000a01c02405541e0f6600d441e1201039a09500311440a0000c0284007803c200c204006100710f003e44000401504122501645100740903d100c14101d2070390f903100308880300101706a0a041030f030a050f5600083c62160302d4030040015011500e00c07124050b00c2d004188000c01442c205500104443c42d0044651082d10180421390b6074442502c40c001c560503510f6039014480c02e8010030040c2400d008000c9004084003254440a40b9804041c0c26110030001081c0000d244602a2003080500d0130a0740032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 245622347 1250 245621097 245621147
    0x50607080423100203070b060105031810020301050f0102010603050a020607210c110102010c020c040507030e01020f09120303010f050d0c05060d0c0e0f03031209010905030c010606080106031a04050601 88
    0x1501c42e00458080d80396100384000305022421910000c1600c1103258044481c040a0711044019901c43d040180b560071034000c443c844120000c402d100c4406403141d0b50801580325414103040140310300d8900403490441e0714100003000801c0c000220300c24101c0d01950401d0f070762595400d002403000b441000b41200609860440c40c5079940c003d1044440754000e18415040320200401242a503142c51345903801607004c603200070024641039024035081041e038200022003007268258075080e41c2100300500d10700311011950710140e041c900b8940b41d1540803000a1413031581003081700b820a90301d0b4000c0f640552004d81e00340707042092000c200e80141c107000b040241c0710f429030355001010b098010b84170b50002c3c003464120401c0d81040d4252079400c1c0f9004015505000c1c5408003a504a000205425280d6403104020408280107000908034290010004070303040c1c0c00d020001d024260107a111030101460704803100354030301e1684804107040104035008a6a5211070b00100e40e020380b500e191205002890107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 245623597 1250 245622347 245622389
    0x6060f16081e0c0c040e1c05070209010608160e0604030215030402030c040c1b02190e07030509060c09012f030702030709050408040e100f1403011508070506070804 72
    0x20180c04507600d0488506514010300d203082d4040e0007550000b02c0340f90721615102c1d01c0c40c54160013200d1141003c90840b00401c40c2c400009070302c50b40f07054140703012030800a000410350500a01150140ca0756040c00d0360740d82003a60341d0301c0140f500d800c0c080f030401c1500491508a5034640e0201e50046400810200c0c0d0583e05c080440030300d9006850403840307849403100c0321002d400d1074040c103900440b050f10b44107400784000810418a120750a822a80810030403d07007821000e20003240b030f002d40701c520301c010702c0307850b101001608880000c0d040c940240d011404010209110340215480310030286044c03200700180070100c51181d2881da410007070010258080840a2400102920015000310100e9840e650744540315001c590080d030700a41071500401080c0441455103910b2034008083e032141c04490307503540f4010b641e8070159800a07d41c00501401103500b5103400d01a00c0201ca40914005610a292031401c035510500c900c02c0c1070043c040420b11200b8070003500d05660081100380d481d08000300d9a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 245624847 1250 245623597 245623613
    0x6030516090c0206071d13020a032301140402070816050d022a0405090f010c0203041409160e040905030c030309160e0a0b130c0206040b16050306060f16 67
    0x300444180602e80785624004030310009085000e4500c645558000c41500688018149007920907290400b1403c28040d003400d2540c030040c42402c10795500010003281e0b0700c2c10b100c1e12a508003844107200003248010b000b40f200c02800103071910030441d00180c1c0c83c44a4a042c0690b030261a01c0c00c1e2061658001103400e0143c0480d482c0b03000561a425500704001803d0300446a0716003070000b0b0038030115481c1000150401d40d2280d030f00000c0c0f071421212030601c00c1c002c40782540c43d400300c28801031f04046402c12264800c0d018480340d41700f048900c00d009140c4000c08804450030140444100000300d0340c080d507a91030f0366101070503144d00300e8180c1e541c40c4908000d0a680c0d034002d69103581244107009440c01160303c2c0c82d281105440b28102d07001c50688401c1241c07030103048101246036101013455841e01030010310344601d0707401803000e07009401d981c5042d0404001c4088010306040715411142c014031592540801101d5101c030b01203803035a44402e42080404501e00401c814241c06108400399141440160707 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 245626097 1250 245624847 245624849
    0x90204060914040c1719050c0d0818010e030c09150a0803120108010e0703030f020c06030a0f061403190f1b0810060b0306011d0a0b0c0f0304120b070306030516 70
    0x42e4030401c20003541c17240303c141c0000e4400507030001070304201030020181100007031004000340910210740840f5680000503c64003019102102c1402000540c944034041c2089450404902401d101141c113090002080d03e5028070101184244c001400040c076580b00c5c04103e0b40d85103405003407140c105440d00300803640c0350f200100d4213940324034a000000703001c0c40500072114a21035074000390800524595003600e90300380c01907041b029401414080c21954a400c4091842904202c8000c0b6061151952183c100d4050380c0052148060040201340c15440008070385105854511807608030071824204072000392403091006001c40001440d080e40c2003030b5814402e003598420300913142c20781c003041081703811600c0c0d610400c10b80400c2400068071943c000c00450903241400449180c2a0003031400003240b401e250307003001c140c1034000f0442c090317130007010800749440c508450000d610345400e19840041146c80e03d0001805070146400040d0035921a4020000455000044070702c0420f5521002c0b51103801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 245627347 1250 245626097 245626103
    0xe011202011d0a0608040c0b03070f11070b2b0207030903050607020a12120209032b03050f06150d021305011209110906030115090c08060316050409020406091404 71
    0x8040c080301d10405142c090b84821020003000241ea403454201d094030304050040c410b407190744480e0000a40a200c604c01148903280a0303413055610700c00c034000588401d0044c1100c807680c1c0d10000382404400c049034112a40e180301040140c0009030a0000e061002e480ea0f9250401c59002150175820113410510102c00c2c1da11450a40e29940d4440d44201d07581c00000ba00900050707052541703081558001e41c003540701e02d10128005071420100202013803600d000d00e1142d078800b2510700c07080102000d1650141c080c1c01103a15060280e030400c4081102c541d030018001c144511000d1480350030903a030501c211004454040740964480706400115813420300f140c494103000c90b50f298050040c810042c485c030301c0c046900c03403400c6000024210520078441401800d0750b4040d9607130310010300b86400300c000c0d01c0010800400c000c110400402e5004080c6280948028000d500c031440010500c88041e40c1581901c01c280c4002410600a00004014080a5004844081c50640c9a680490f841626a846540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 245628597 1250 245627347 245627357
    0x109060b0301050903282601030b06030a0809060d0216080306040f0e030a08060102070503030d0b03010c051905030c1209060411030723060708040e010f08030304030c02190e01120201 80
    0x640d42400540b46c0c032805a06c150b080c0000c02000c51b0840c1900d15444c10369071146000720f1000e0304040411256680c029100b0712208007000104208808908640d90198007900940740580301d9076282d031954001d03099541c0c85000049008a00e48009034140c0e180c03401c65400080e02d0404602f019403048d4019202c0c9402641000110303070030155039000f00420390312800c00651400000280c210380e000c1c0003400780d60441c05884c4000440f55000c00161683d21001d40e80042c8000481d01090f0031600e42c0385100080c40030a00000c511003505003181040c810040c00c100d0342e05c1c0d030b9101d41290144a009094641c0981d00000d003d0a10b20024050740708910908002c1c0c0050704000c2017543d03403501441103681a410718904000c0c80a642c20350940b904901400403801c2051550b03c811180d04103400c215035201010004020808050403c1c00c01001d2040245141d41016200200781d040d80d100702070301682e00b0000da4500c0c1e100d40042070340205100441e1401c203507159854010101118031050340016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 245629847 1250 245628597 245628601
    0x30201050a02030c030a0c170a06061e020618030405031603030818030a1b0b0109051012030503150f150a03060b13030f0507030f15060902031003080c010902030109060b030105 77
    0x40124800c8a0007a24113485031400c5a495102041c05045d8850256082114024020f90600c100441907401081071520202d00282005402070000100c1c00700d081c00405150f810500c0b481e00400c40e160070a01c01c8140c034444c60001e0480c01e24510903036100c59054450002525055014910200700f940d10070f64400e00d079a229060390840105840c640340401e60820030031100801d0141d5011494030912501c2003854460680340c40d00b00e130400742c0c800648036807100100702c20140a4205240540029030b0020f0002200c0e0314000e0050000034005040b40200c0d0284c1e040c99a030b803041d10155501c008060303200e218812004100035404c0f0b44101c0740801d0505e64046604110a400d481e192600240c2c100000c0c1d02d0758880d890203480b0740d1700a80c1c2501030803074084041640c0c40310808000d805105a10140000080844111820741e844034803401d03c1072007882061589010b0f9201142c1e00032074200e4448001c00003084c014288420000d6240d0b113011141800c01c40650000341754007100702c00802040e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 245631097 1250 245629847 245629861
    0x22712100603031b0309270f0902011106090303040f23010b0118050105030c0f040b0f18040614130608010608061b0f04060c0503040302040207230f03040501050c01151203020105 78
    0x1030190304c1000700407800290091120541e07106080072200040b0440c03002d001100d00d00b0500b11046510001445034503a50701c00155600041040314480c03070400100164508030024a840c0c1c0000341c40248511560000c01040c005c00341400000c0e100c003070b016280010717000310b92075000307140e014412170100b41540510b0340741c1c0c0d0094444004941c010384035149142c1d00c00d100304075154800b00c200d2884003414000458490440030203050180f03111104195240e80060081410303458000321071348140d0030b018050010507805201100f0b02d241c00d81d560072440003414854805000e00781c000076582c3d071900100050110300010024014600b01d0017405a080c0310700c1ea880078500c26400e100b40d60302002c0204010710340c818003101520380d01a5054030b060a441e0780c00601030f41d01407442542ca044686100354080c003000702115200504000c01000300707069a0441c10b459019612906d4144840860003001011080d04422101000c14a07694805500d0b1280c4150b4204050001c0e8015031803c0b00140318 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 245632347 1250 245631097 245631137
    0xa02030c010c0e0a1e0306060b0a02010f05011206050406110307090609050d11060a0516030c031206060212090102031603050c0d0503010e04020f03010b0415080c0402271210060303 79
    0x208010150850003e107091402c44d179032240007448968180141c10307100002003100ca20803131016140d0304140079078881221a00a00b5038218580c00c082e080c0c80c02004002001c002245003155950155020500e56540e08240e00140344001102d102c1038000020000c1580d031040f6a602600d58036102d15042c107071150180003132002406801400c0308074045034080503107054400361011820b40e1500c5460309001600b90300f0305044502c1d044001c25007011500d02010f801a06081405681076820081c0c40d1800c1c10095030307400506641c44d102d010014990900784d10901c00c0341c0c9a80300442d4000031194080ca8000d010364081741c0e010103503004503c40a04031901c208110390407100c0355282001e10b034440c2e400f00841000e1540380c05915650320400c00304282c1711030103156a500b80e462005008103282100035407c003000f19401c3c0d480347e80704204418048158075040441e50042c1d10240000c3c625680c089000c3c0424403045203090312a01503001b100001d1a0052801d9030300c203a40324030b0f420903c5400500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 245633597 1250 245632347 245632367
    0x30c06110c090402090405120a0f1409090402061308070b0a0f020a11060310230415120f060b0319060b0405062206180f150501080a05070507080a02030c010c 69
    0x54002c0c41c031408100589000008580c00c02d014200b80c440c15414145001919803002d81d00002155030b200c540319500d504041200c02e100310114540e0720b00700341d41d4000344803610020701c000d202d00c0c0301040302e041031004c65a110001e81341c030800711100e044e00c801e4900d2441d00f003140a04002216030000105441c80440c1c4406d050740d003c40380a0074124032000300500760f00018640002d000441d103001030082801c3d025401d0340406240c00a003840d410105010a0755445229901102d06241c010002251020411840b0613000082900302d400180703095400340220541c45549449143e0100c01051006c030402d10b01c40d40704100400080c081c510038401074a0b0b08039221503002d254020381c240c40b10100e0800503400101340720001002605e40c0f2400400c94005040e0811281e41d500d014035402e20a4891400c507030f01203080813600d1510307140000b45846001000407481c6900c80b00403880790780c003442c02c2d140304550203140075407100c45001000f03541c0d0b00420624106903080c0845d546005004d0b0080c12 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 245634847 1250 245633597 245633599
    0x9060f0b06040b0f0706021209120432041506030b0a0b0a1209020406080a0501231807090617100603022805060a17070503060d140307020901030c06110c 67
    0xa00b4140b505900988a07044070210740d1400380100038000c0014920300c010a1001c030001503603201d6007000e404c0107203409050b4140f05000c100411083c8480c98010103021805c98565200d05680c428000700c1030790460003181c9064015042c00d0300c058200d00b5101c0c5200c15520700351b800b006900c0741402000009002c43c030407404000130407c0200d05161140c252201400c01c071813800300318850380f940464119609980a90040d40190194400b004020300420003004000c04070712541c007141c420503d8a55502401c031610881203e0300e00446080248400d01c0100707691001001541e9030740416442e0360800c800b03a20103034041e4540c490441d4400303110f80402c1d00e80140c075000c0401020100159904a80c54000b050420301c0240001c03e559281c0c000d1416038415500c0e825600082038642c10400c4003d000d0500b848810f004100158585002c2500c14a411911100c18036490000f02d80c1144a0024080e400500a030000710038031003114034000442d203080c0d4421050702040002c0640f01c0c09010609 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 245636097 1250 245634847 245634859
    0xf01171501060c020f0907030501081e0d20070f062718020702030f010c02010501060c050a080307030f05040303090b090d120218030d030606170402030a03030e0f0d0309060f0b 77
    0x51101512803d1020380302480540a225110060707400584000822030354040000d490ba0018403858400b4001a04114101c440341180303503031408990f40c1c0360794140108408000d0303002240c0e9500048180c0d690600350f40107060b104942d80325008131070a00b1584c0281c001081c46024038526101072402800101e0040480704001242820f032110110740711035980c407000d95002d116080c0135940901003240e100400600000302e847c0480b0010b400e40381c050b4015010300c6400000300001c5400450a0b500969110024540e01ea440203429170080100c7c0791540c2c819444c2c08104010560554400000ca60090030440c6081e600c0d852404d50745e0016070402c0300090f81d0340040f990400b243e500900180d03030580012100d80c03880300f0b011a00d0900c80c03800d0349000944a46080020503086200c00718074410f141d0100c4064a080e8000c2a0f40d90588000101010b6480c096182c00e40810700442d0144800320003a0f0b458454a0705004020301020f1205462141c501791240100090a2148640c1100c0140513 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 245637347 1250 245636097 245636099
    0x90103050402010909110421030c0b07021504120215070504030807060b040203280605060909071812170301062c04020708040303110a030518030f060f01171501 70
    0x440150038040d200720706102842001041c42c012900545003036410304160161174601e080440101c8420648070120401341c0f0516500110740e000c03038401c011030342040c04003000c1d4686e960100e00d4112072201201c0c001c0c1c80340061101b0000d00c0c0700c0107544010030354212064500d2403513580320205002d5450b21f02041d0100002c100240d02c0201416100303008100014031902c410b000703d400e0307078006c0320179008044003401c0d10304c52120340d42102104c030200c0010821526003030030085495441442e8619108001c444001010b440c0301d1140300400078000d1019075400381d0b5445140c0b080d07040740401110514a1004840b41100d072400640b070407107806588045000c1d22035095202940d41e105940d440b8410076000120140d00c079400141009031040340300603610361035420b000780701c0c081101e410685504002c49200c00700b94084260340b0380f43c043d0720785c042e2610b9840340000c0c42c106020039962103030300904c0304020044950324003450481c0c0b040d50700440b203150440c0c211f54075004c41034040c141d40041440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 245638597 1250 245637347 245637349
    0x409080c1e1c05070506180712020a0909020409050703080c0c0102150708101a07020108070e090103020f03031227030403050304060e0103020d0f052d0c0f07120914010801080309 78
    0x20903840b0381060a080745402801d888150816000b00c42c0625460107600e8034005041e02040079000a0000350709101e80c900442c1d0004082d41e280d88102403805480d03600314000c0d5138813603000c0c40051382d01108584210740d036868004055081044824014081c12150041550011031940c0040450f141e650509a03200b80381641d0861000e8035a000c501501c6034046a03c0c0404032041c2c140040383c121654440c1014400104134910040c20b40301001581e10a180494841c1d00230350341925412103160075503401c1100803a145024a940d000c8180ca1000140001d491b192079510b40c000554102c503815400280100f560b49120740c1c0b10007172142e4401c1104200f00fa00c59a0034004c0a20f0501d005403500b05001843c80c00d03240980760908078180d441c3c2c1400030a030b072f0010318801d802c031100700c015403036412080d000700b13180750000d0031030184200004117049144041801c0316201c03540722112914034101c9400040c010012802040804110446500c946600404580c2d040714000c2008620f0708010070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 245639847 1250 245638597 245638633
    0x6180e040206070c2d0906290c01022701030e0a200907031a03010506011223100303030506031605010c02190b0a0e0f0114070c050409080c1e 62
    0xc2d0030340741c2e08480c0c00080780003294559401180001c003616030301049110581070140031700eaa80103069441c43e1000802c0205108103580e04405c02040c009210140024940d280610034100700403125440040c081d04aa03e015807210115144540e071802c04001c1900150111075a0000c0106141e10051740100014142030483d00c404c0c02d0142d0f2142a01d2524020640010083c4c1301c0502190300c5070100f00056441c0442c09030781d00000c50081c402c506001c0c00180c000303100445800f0059480c6c4109643c95a04c2c060303040c290070b40030441611076180c0a140c13114035000500040700000e060201046d81d6160014040710300381c2c960300814039054507110040d1b54031140401300700e0f000f5009031240380c0c0c5c0d01e0030038100c20004c066132130038956030b040000001051120200c885a100c2c00481441c210701c1c0c0d9203c4010301c138031620010b03400e82e0740085050a10150080380d00043d8454105400201040143c5015008030300c80e4400301c8034a0304804004030780c40c8520300389404195005114101d9410a02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 245641097 1250 245639847 245639857
    0x3030f0406020f0d020306030d090f12050309120106080d050301050f06030702010f0e01050901150305031e070501020403031e0c050d030f020705061807051e04090309180606180e040206 81
    0x40c100103141c404924482c030f2140d045803034507400c015408010002d540c02c0c188210b02480400b0314140b0a02406c1001250202d1503034040d0022904460403500e0070060304000b1201d030410010050021004908005400707003801e4083c1120310700680e2031201c0898064025a81a584024032004031b51142d20240300080e01300400f00c000710342d00d81e00d030031000340c49038400c0e6000040384200100309407901525260940e121441e01c0c040c40380140320200b02249010041d43c0c0e242e80800b40c02c0050360004c40385e50401c2d0081e100083c00d1944000380c00010560000c1500c400c1d4002050540b000203400a0701340e48084804074054082e8000c60303104a10703588240c0c0a11540503501f000141001d070140c4966242080844000d002000c00d8142c0000c050810000c280041c0000c0318403050103076040140d40d941040a444085c000e50b11481c0c100101409050104054012846994506800d0071001400742156203d003001013400740c07405c0d400e0a4820301c00402541c0104042c248951907a5003408925401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 245642347 1250 245641097 245641103
    0x3070b0c0d03023006040506100c1e0804080f06010b04061d1c060209090c070f0b07020a020907021b0105090105070f0609120c151503110a17031804050903030f04 71
    0x59968803810040a00090b191401343d501100491443d00c08140812688040d08180c412013100b016224001c0e40000c1a8408552180f0300ca240c1e00001c1125052031b40103044024180d04010a01003000800025200c030405c89450480e086640c1c0c80100101e203200f00d008510025515041c011031140d510200e083c5c01c070310060904108148600c960140c940a07540045441c1600010f150b10f01c4c0c034280361019000103d1210301c502d44040c80c0d5690901640f0079200070800100c030000101583d00030b1002060083d000b401034a958a81014000c2d21030002520240114190041141c410351160b002d85aa400b030684400c6d01d81106030700c524042480245003180c0094a0704110400a0000103581001101c3c54890400780a40c038034112680c1892204880040f1f0311700200000c0314502840c000c0300701d9801c490115541d0100c040806d4580c990f5400881803041c03020041c0182c1c180000040c5501c0344201c902c034605005200c100015914241c91f034080d190300600c0891401001e003407003240c02c544 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 245643597 1250 245642347 245642377
    0x3030c0803150604080102040509011e171002120717010303050307030e0709090b040c0905190902010e0a030302160501080c040b0a0c120801030201140307020607050c0106120804030203070b0c0d0302 87
    0x800c182c0000d2466000c0d400010450b500428200290704012055901620881c00b07149021135098200d1540000e4909c01d405034070400804054040005200c41320714031b411080c0540d518150307002d009659aa041e283c12000480044400600d00039900305030381a643c5c1a07640c0303461616400300483c041c00c3d0b007464490940c05507007400505601e841c131034041c81910510f2401200c3c0303403909115649014a62003c00c145081c00200880d28000b41c203070703000c00f4412004c001aa24818001281c3c2c402c81059955041280a0400702c14560005414041d403036914921440f400d446000440e0301d6541900c0c140c2641d113043c0b2041c000b02c0019006021031075800e00d4441040715660715401001200c802209000c16500f02c014410765138817444072111020417001d0f144c5107043c0001c0096607140300514003410020301044840480c3c50a4201030b004000810140032440c9150a100c1b5596010b403100303e200340300300301d030000d444480f00b4280c400d2034100801800340c0c1ca07200c2000782d01075444008211340301c031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 245644847 1250 245643597 245643631
    0xc0c010608160f050910090c050904021b060a02070807110f09010605130f03050d0e2d030c01083c0a020a09050a0f170a0602040b0d0f050103030c0803 66
    0x6201041960b03900e080c0d400c2a400e00d00c0c54031104000030072a070b401c040d000b1107480b420401840707440c2402400707c40045200040e80c484c90b500c04c407030324001c004115038030500010f50760388040c0a5181c980e4116100c802581c803151154001d04040384980381c00201050014082c2c10b002c1004404901c00d480e80142c817001014a081001030310001d001d802c117a000c1355000c1000310010202140d50341c003a10604120031402411174460039601c98009071420f04005942c0b4890005442d443c501c00b801d4242040600d14062801c1380c1c124140900c0c00301a0b00a02c41c000c44450b40d90312900e1814001e06291a142c617840d92a07103e280d00e0320100c1c80b900c1d10309050b0343c90707c0700b00f0400d4200c40300e1040c01c5502c0010303103c0310300c0d03000113091089a0344080e114250661041c4219445030140e0b8007120000e9805400c41d2148512050801800c4a03005e0070310361005c200000d2150300d110003041880136520040200c101031507100011900c081c00094001021098000c00144140c00110b030031202600c2d801e6194 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 245646097 1250 245644847 245644859
    0xa0308030a02040902071a011a0d0203060a050307062610030f031403010f0509100b04060f02070b0f0319020711060307020a050d120e1203040821010605091011060c0c0106 75
    0x1e644501c40803920740010803a000c0060104240da41d0141000c01d02702d0f2481c0700380075582e412038003501c0001e00291780d000000c55429907464240c4001000c001d03040d0717540742c0d03071f00c41015103664640404c0c42c0c00c419254054520403400100e0b000d2040302e100004519070341c00c588541203841c407601c00c11001e11001a181c606c2005c1e2a0015500828100f205250201d0810003070145640003d414a07030310103c0c00380148401d113100d0050fa003d5071068a0540680c0c00003100c124604041d07a880b8010385100051710310300508440e801140319501100101d011140f14100c582e04910880c0c2026150701c00408104d1580d2809800454100b01c0394411500b041d80180c0b15a170134448419036040c08104840c4404240f14907902890500311140705c0904012107803140c803035901d407000030700051200300000f844481c03050751403040200801d916044660a5031315001c0240807580129600d074400c0d2811001d0035503251083c040d8449103030300780010f0261519251045051031704415549000b6540700c800105107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 245647347 1250 245646097 245646101
    0x1f120603080306040f1404030e060405040f05060a0b0703050304020f060f030f01030b06041a0d060603080d0e0111090303070f4206081f1d010e0111090a0308030a020409 74
    0xe58003038002141e490600318108021615107030141e0090605003001c0000d00d800c1c00f10342540c02a0141040759240d0100800a072a502c143d41207250700601c0e080c0301d10294941030307102c00e02c2194207803041c441450300c40c0160117103070103261002000a44100002070043c2040c0c0000005100054200c0b4140b10b10328894180f990000c403208940541c420004005004104c144582c001c00203a808004144800f40c2c04d5645070001000c0c24003840c14107280c0c50801c00c055100200454000c081140c5614500074801c002d441043c803044025803c01011552141046003241e18000005000b1481d0401c27913a201d106002000c48242c640190041001d0f0585c030803c1d041d84454018100e4004045018901c54840a16801e50031500546000801e20410780e0000300c0c04216019003200c0405404000c880d040508044003455800d00458185003002c2c00c2c05420101e080c5841b54024000e050504d00c0c03600542c025180c141c0e034809884501000807071a10002150081c011003000352500b5110828041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 245648597 1250 245647347 245647349
    0x140a0b070b04120e030304061b06020c070f1509060c0201030e01050901151a0f03090a0f080d0c030c02030306060901030e0a03260403080a0f0b0a080102030703140103021f1206 77
    0x1d41c4034214800c2004220100342c0805829485040100020000b039000c07941e00e001e103005550912040014440241a04001c0140102d9018205640d10881c0301c7e49113485076007030312500c0410008414045040d03040b8002c03038a0000e015682e0342c0215860030004407506d6030360f22400e81c149540c030000d50a02030000c0c0501c9104054520002c500a1030100510044401d00c0d4065015801c40c000c2040111011b2402c4404240f05982907986986610785d04504144c42090000c000244841e0031504004400001e08100c0c003410358208400c4c4c00c20641034040d90a00408440103030803c000088841c0340c140c1c081c01480c50b0614001070b0880c1c4801c1c00c80d1800c0703aa07400c150045403846110071462410414014000609005e0b2a081800c01d40d401801d0480d010784104178a64807000d801428114aa02501d01c60b80d0003441c030a40c4554030007105d8001e60081d520180000e0a049501030300401c469201812660b020b0440100004148403c4142c940c408555008108910b9004201101140103106c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 245649847 1250 245648597 245648603
    0x3060f180715020c0d0503030609040314030103060615050306030a02091008060109060f0f0311010c02062a0118020d020907031503032a0f0f0c15020714060c0304140a0b07 75
    0x12664080d0000c007034901801011005d1003404550301c550001840030082d00c1d0006401c0d518a0f089445919043d60701803005030b6a01c1800310040700000030300038680c1010040b03030940610003042c1155800d00b240d0902c011035000c2d0301a84440302c918010704150720416803145443e80c092600a0300c8100960419401307900806119840d000d09120302a403040201c3c0080c808000c1c003001d0545540e650100c04900c030f010b05030500100d00200020744d1540002c640000c00c03141c4648810f00c5d050328010700320310b1074001201410b6182c50008264640f00001c21034401d6001440c1002c840400d5080010340000185060105920b035240c4941042100d2003900c0a54400e4948410380f02a00c0240b0214001d01ba010840c030150015105001c07a00d11b18852044d590054083c0400c216241001440d1422681c000d920540240c0d00f40c0c45041d0340441c140054503600091410110140f1302007140798042c0c41c42420154008110800040b009010b40303040c0b00502521039612655616441016508502416 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 245651097 1250 245649847 245649869
    0x18030519080c0703060519021c020d02040b0c0604060506270406020408060108030703110316081602030313090501050a050108070810080d050304060b0901150c1502030a060807060201020903060f1807 87
    0x101c1000304050600c2406a810380c1f00440c1042c0c1c1c400051814401d101e054054410307400030f10540005c00540444000e09088800389030780c0c02c0400503a5688107400c1b201612300034030b4640800c5003858030034100350a060f54400041e01c5002c021290b0280c2e0a405041111040e030708210004117190300f8418070b402894070b03602441c2c031070a013810003600010f0200801821a04100002c00c05054420501c10800b5001101d458a031401d10015010414113854044c0d03141c4404900c0104400c544d07860041a106030181c28001640c2ea6000d1120702141d5000e00d40c04148440300084450f80310312203050340140c100507070080035075455007143c0c100b01d424413101000900000402041c410540580024201c058440155030b40c98442c0c5400d90800f10400e04c02003088104040042c408407143d8043c5032020060210354a081412401e070090040744a80500d5002d0250700040300c0d4018800d840165038003601424440d59807501c009180c21000b425a050000041184800ba2508020002c06400e2007094 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 245652347 1250 245651097 245651101
    0x20a0c0c03031116050315040218240a080c0108100e0408120f0f01090e0f01050108030705070519050603040201030207081c2403080a030b030a03080718030519080c07030605 76
    0x280ba00703040d030180e07180a004c0c00c1c020042280c1d072400900001e41202c10881c0410300c0e125031000400501c5480188201201d400d003c3c0216180a152004980c1c0c1c0102e5608c180c511510042c0b000c80b031128801d2442d05e4108404500d1300d9409029036580c06442c0315603261002d52a80c60000300224151405d94030340c800820006141922010a43d07003100a5807846400c515042d80d080030014014010490001e0321a03906400d280b10801c41a180000a240244403560710303145615030742c0d0000c0c44161624896480000785908009440d1804180c0260081c07003298106428049598000386c4100d0406500b001500c0202d80071901030009a0308041e821b2003503200c2404444250703014a52000300003041903240d00040321002c500c038030403281d06c00341131510fa1000c07100541c01003400f000d070075400d8054510001d08242e40800c080e8441c0e0000c1d100c5c64400b102070b0070304070700c00c01aa001c000c00c1944403036a0000d08002400c526510240305800491404403100c81c2c0d103081044580c41100c0709a11401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 245653597 1250 245652347 245652377
    0xb150a0e0a09050105130c02032106041409060a020c030409050f10060306081005061c0c030b101a03041b080705030106080a02061911011a09061801050103020a0c0c0303 74
    0x1400620b248201402107506000018042000f03010660400d550f0b034101c1c0b80e950700e000f48265030020440c800d40c0500c2e000c0c400d610f000c031008101c80f060300c00d501d401d0000307508044098805020340c3c0c0c007a004010560b500c031010f400a5201c402d0280d120301c011700001516003e41d0141a120b018414906222401c0400b81c0300f904450503080700c8207041c188402403150500000d0245100003154102007035640350030002c41c020403005288101c40d0021848000180a6101f6100003140d03c94280d801e50303581e82c0070002e0791001c100d0107001000200340c0000b00410b85140051600a405400b54450150902034803028000d0250300900c0782c0d03040013a0030440e52400307105080007000814050942c580c041d030b000079074512803031402d50720b010003000510000c40e1046002444098000c402007011f941c841103403a00008008003014803c485903000200703d418907031040e0b660b150668400740c4050742088019000b94100c0c1110a00304034284101202080c41c0303050300401103010303442e80c1c900c4e460300745 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 245654847 1250 245653597 245653609
    0xf0a0f1b300209150d0501020403050a0507060206070f05030a02120108100e03070812101706061f0c030f02101d070b0c03070201031a1207060906021b040b150a0e 71
    0x10140d0103241c507007458030015885940546078403c0e004135498081822200c00511101d4024201504035840441c01100300200000d0070001c140c02141160459541d40704202d9030f900c0704584040008031903014600d0800e0044010f145c00c078441d5200981040c400710b21050301c2131000d90200d50307503601003141e0441240a0b4442c00c3c2c004409400507629064907a20788028500c106844034044810340000114030700380e20308080000e0300742c0025219102a0401c10217550f2041560694494182400f41210703200c4e00e4601a1503104040d2142404103040380c800340ca99120312240d0038194001d010603a41e05041c00d100d4070040e0a60559000801000400003600d0107080750002582214104842400c0c030344000156518140d0920b0082040b60b80d101544282080a1000039004030645102191b16480403d9903420380c1d10316a10721801d559111012641c0d010007a40e0030628081011951266080c25044208603003000752119040408400f00d400556010444110002e456400c500210f1300d015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 245656097 1250 245654847 245654909
    0xc1202061602030406020714030703021c020f090411010c0204060b0a020f0d030207020d1506090f1d060709090902060408121201150504060e180c04050102010e0f0a0f1b 74
    0x1d48000c0d41418200b080207940c0d0b10781401400011200048402810381e81006a2006140d029141c41c54202840400342501082004228403e045030402c00e1030900380000140c2c4116045a190002c0407049801540c00c0303002000700b640c2064039208040f6440c08000c0080010540e658000c05c2c4207010384d6501d50902c90000d152400b098010003034100940c3e28020b6803075201d07070010340d0101081c110440302c0c0010000b039401400c1c00740c100980804160301c0341c2d100981c44071001c020711994101032100f850b00c61f2012140d003404588140d03014010b140d007541c04040c040d84090171041c80c1c41d40350440c00e0701d08403a0b0301e02c101070880c000450304440016102c1d12401046142c0b07038100113501d811000380c43d0707010324020042041202c1c0300e0121244e603102c3e40b4148401c3c500d030200503141040c0c0c50380102c90b4401c0c0a0350303002d90b0030400c800c0d4001400151804181c0700f441c0181103843c0160341c8001d811400e161090701d8600500c0d101ca070b11070b00d031507116000130300c46595505004007807504000b08040b95 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 245657347 1250 245656097 245656141
    0x2060a020c0103200f0c0c1009031a0f0c0c03040b18011116060e010513231c0201050c030c01020c06040308180d0e0103090b103201030c0c120206 64
    0x400b10801400e01d0301c000c182c07000c03085c1c0c0c80096900c4441c0e45c2c1d0070700d1034821020109075010351352841c40c240d01604040b41009aa003c1c54076416925148140c60743c01a0080c1d13404c4800c41000d000160a62010f10041d044a20740802030300c1c0307881d684d841101c2c0036820000054110044402190b18a0760300000070f130290b07a02c00c901814680a0303004500f012120b80e4440d02003400038076074596882368814422a003520405401d445a0b0075160000718010315150700550103072f082e994001620030314100500d0454420110301030b0520600301c3d07004403095001310701501d030984000c1c404480b01d40820b0002d010b001c1c0021000346024a03050800030400c41015094501003100c4802e0343c00c1d0381c000400d0322100750304a0309001d02c100d00444e0040b0014500c1d220042c212010100c01e001185000c4201c0f0703800c55100d14400d030b210541030034190741d0558099410012440800c07010f60300f20b5000350080b0750b2003840c0c0e007002c1c079404005444482c01e0103011600c0b200182c01c12010032070681c07880d2080300c1035112 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 245658597 1250 245657347 245657381
    0xa061e06020606090a0e03070501050703050903091c030302070f05160b030f060907020f010908030916081906090c0b0d050703050105010912060207050706020307060b030102090109030212010902060a020c0103 91
    0xc034015010703460719009030040e400f41000c280016907920032500482807148446045071342e68840c078240207000b008155420400281010080380140c90700105450640400404000d080304100960301c20404a050003102459002e2202e8004074103054180d0380d18500074009030a043c00700b020664400c007001d80041c84051028801d010101d0118124664880000d5070fa4040700d44070700d04168981480485038031410b40c02c08000408101d1090091801000308a046412103030030796901c5800c0f0010390041c0718a135484a404100c0e003880881d211400c46c1d015030000100010f16842d040442c618a0700080d501c02c400003007000824005202c3c0b181d102d1800d240420a039410180000c20511182c41041c090a400604940070b010543e03045a0702e140e800303000c444100e591400c001e5160b4010f1308050303409900d440f2000c105030070706000311144408160342d02d0300c07030340c0c1117908100100a046910210301c0d961985803c006840b80c0000f01000080790f0011300384440705400050980b0502a642c40b2108 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 245659847 1250 245658597 245658599
    0x607060e010509070311062106040e0f07030506130302120f0c0d0509100305010e0112050c0907080106020706050a021e1015050f0a030f031412042103021206040c050c060a061e 77
    0x299081e840c80924003000712002110f440354000240a80074506110080d80115040b5090000c0300007370300d00840b4881c2081c0c84407a59202c40c2e08907490382041019000d038210703640c1ca58040d991000104030000b1010130a0381020307210a006447c100ca43e0441001041000994401524190310000040d040c6407500780b100b503041551075004160188600c5003038040c0c01c6059010003a080c0090b0001c88005440700c560f6190203040103041084c01c1c810a40503006910b00415914810b0702110301c142101c1e0010281c2e284099642000c0c1265903d480794030f40186600d003041c00c034560103426805004040001d0215041038100700d14180061102d51103155081c01c20800030f04201244204140c0505101d805107200c0540c0440c5481400d4607165015810800c01003000040c1a5000914401d5450a803805440d010150120b2003045030005510040d080050907921341074000c4003081e01c55160003402c040b4212041031a20300103803071440d000d0391141024840415800c5451a4910394400805251 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 245661097 1250 245659847 245659867
    0x8190c090504150c030f0f02120c030c03040b060d0204091103010e03090a0e071701061d120a0b0711030409021902030901090902090415030516230607060e01050907031106 75
    0x1042c0030400812009031666001351406000e43e00c00354480c1c0131614180007441c050000032000358800c001544c500b0400301c5c0460302c08496801070701d03c18284c8581442c030b1900d65458034105440b004040f10f52040700e040050b40142c84500400d52450301c110700d5481c0e042e0310700c0c04041c00e403030783c8070f8108046500034072400384641e81c0d00c0800400c4800301c01c120300b16a180e0b181c0840380781e1801d5100304841000800005119030340030750941520113a00d041d040b20384140c40d00308a0701c0b50890640b40680ea200d26030110100c2c2583c185250048141d04000c1c05004070020018150340199000031540360740480d401ca0000000c0102d840d0780c13001d40c80036500e00110701d000640208050300904e100300307a022032211003e4403254000c9440785a50b81d00c00040540d06e1910540d201062403482c1080041601c001170b008022042ca01c40901090003589442c0301d40c4400e10101e070300030603002e48042791a071003105620300c8203104490180e440c0c14041d010060440c1490404201030315540c030300518040000c2010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 245662347 1250 245661097 245661113
    0x40f0f1a0c0c0d110f120c010f05160f120e0109030e0411160c0506040902090f040b01021903120501080717030313030c030e090c09120102030603060402120708190c090504 75
    0xe07406003401c0140740008160040c0e840d007180d0440f4641703588140190004141c096101600355900c3c084000d10102c1d24104070300c41a90300680300b047d00d1103030810f000c901c007070b01030115800070342c803145040358050560b92050810748031104075008985e507581f01c1c5c0909140c1e110f00440ca081c441aa014008684412400c200320300c100c01c00d040713036602d01e00b00c0f610030040140c40e46002403034018076060b1115100c001c040020340c4402e111510440d0700481003401c2d81402d02070b1440942c416006031035440e414882c0c652644107038040c100e0070441d00d801c06001465207807180b60b0190000700004c1c0b0440c1c0c105200603e01100c5d08900c808507600a108000c0c00041c0d11881010090340351406034050050340c5002e607660040706048a03845071402e01000300d54002e009c040d00a5103400c5413180c9400c5d5400b00524200d2100341c0c0c541d0342580140000502604150440e00801503070360080b60804c941e6581e50a081171080400c100e08507001400405c280008508840c0103018044010040d030306050ba94404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 245663597 1250 245662347 245662363
    0x30e0103140408181c020d0206310909030c02040f230105040c02060f0c070c0e13020f0a0608061e09010303030203070306140d021915020312012705040f0f1a0c0c 71
    0x1207e10021a125011511020305940415050b41f410609a648008240d0150540200b8070580d5075145100081d202c0740601404401a4040d1a11188e406c1e440d004c2c003000e0142d0213174415090761244131080319154803200c1c20510404103100211554101010881690341c900300043c11548140309100c281144c151000760480c01715101140c0d5444140b521302800c40c080d62011a081d03ca003010070941d029a620182e154038030842c5d5090403159020100425a1707580d000e0840082d941d04c0c001850f034101085e402201c4a600d071425440b41d0494400103110750341c241c1007200069004014000a650140550000303001034454140800281101054503072407074001c042d21030740c40890603103d410704107001c100c00350000041c61032043c260400702a6407035004d02d405245110030030f0000281c8a01401c81d1040340001305080005c045940085540940310142041d1124400aa0320400050000c0c1756030790994480e940190451019804612440c50004c100c0000000c0c1008007451104011074034070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 245664847 1250 245663597 245663599
    0x18120f12080f011203020a0c06110d020601080309010806040b0d150b1c021309060e15010e10030311070e070804020f040519020717160b0703020903030403030e0103140408181c02 78
    0x804c61422509040740703490a5040c2c00b40600160000100b1190fa00050010203034000a046a00051914508a950721800d103d038220540081c00904488e620401c0d8860704440c00800c04520044d546000406010725400704491004d0220310744041e00f02140902c00f01c000044403510b010010b5034103000d0650080c82c10081c451480001181109001c550044052a4101e401088440404c00f0500d40e901e14011105000c410b180000182c401c5074403c002e4071900b560b0048903445c0c2d10f1030b40c013074035180b02e400102e41103030050340c0300030960f0a0004a201d114402d1582c503080c3d00d003400e0040c0400000d081590074025410401003090441403a0149100607500c0240160760350140c0c10700c020b007280001d9101000103000140022100c8502140000c890700544090600d5200c41006a04034481c220016400d038005000410110b40120589428800103050101c2c101c1d014140e0101c048104450441d8000e00209940207881c804400209120300d0650b0901e01c3d0082c210741c044101000c2580007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 245666097 1250 245664847 245664869
    0x50d02040c031b11101a060f0408010509010c0306080a0506071d04060902030703051f05060706021b07140301090b01090c0e03060f01051009060f18120f12080f01 71
    0xc03000781c1d2290340825511600401110390714014200000c1512141e100c50304440e00c660b10208204001902c01c6203454000e403084891405c180405005c074030341142c840e2015520003031200007000d40e42809080c0c490900c040000a50303400300704021741140e00301d401c80c400e07a621840b940c00002d0000103516812007000d003000d515414940d112038492181e0402915081410a80c00107100c0f103c40d0080c1d8003e440f11b442c244403a0ba0340c058641101600349078061a509111030040000341000070007048560b0043c0e40161910301c000590104940c40c00b45a0f14a5600c02181048042c0c10030b442201020300440091246000d140c552008040040c060092403d5031518040907050240322801c0b1400300240648406140a071100310b10300f1000d200d5107025402d4400c0b1414950301c900301d0442981d0351920342c1b81c83c07012421011244214091100c001c61000d0301e00115203005800c190807041d9104000f4064218018039160382401480d04100080c00305030000d1017206410040f010341500c184d4815 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 245667347 1250 245666097 245666111
    0x1806050105150a1227080d050603060702071403190807020312030601120b1c080309010b010f051210030c08010e010e0307032024010626150316090b010207080106050d0204 75
    0x9010044562003802e440340341d080d217101d130800c60b84c0741c00380c89031881100c000c002981d60b09081c592180022190320006070401c100500040f12030341e41034585604041d084507000b040d81d40c0042d8030a00d07c003006482084011441c8404c42c94100701519440304240541400d5040440c0081c02c8404e0580c2c3c000a031649600691000c2c0c1c03502014079954a002c020181d80d1401c035401c06804940c010f51303d88009d5400e00d80001620750244000b11484c01041d0744143c5005d607000c1495031020006010342a0345801c1620000209016100c3c0740c1c0540110000011042682d034007803421200103001c0221290010320000780802d07000f00c3ca005400d04103100c0e0880c00350f500940c81d401d054011426880c09034584c8540301c1003048108403a03050394055261641a8946090f2803901c5e80c584c100c4004014002000240c114261420040c121070f0b4081c0c11643c004042c1001500450100c2d046030078495078440d14181d09603410000d0900400204008200030b5083c070010071300c0c004a80e41701a02403511802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 245668597 1250 245667347 245667371
    0x1b050901030e010510050112050c0a0309020607050d05031e09030306011404120303090c050102060f06040b030a05060c0901021e03040e060105071e0507060e09010306050a1806050105150a12 83
    0x3110000415042c02000949080124403820081d03034040c40340060128001a110101c00e8440c5601804a10381002d041102c0e00c9811400383c20f0f2000c2c1260450014051030340010320410001080ca18035032610360722842c1c450b400280c6100c0703500d90380d0300360040d28060003500280842203e80048080ca0314118903004142590110320465221454410320175a5003024568142e00424403e80f15056011415507600d004a980715030036500d40401804079000b0961074502584002101c600c05016075940038910f8540c2410090225055049258001066003980d0303410b001b840024050349a2909041c1f60a0380140d41c0d0307018a00070717a400090103001203030b640d07809041aa44106c1e40806940d03816201566860305482404d0360884d403920407000045607d5009080f42e081c10040500050700a80c80c6d6100d0030080c00c1d000d04a805c2680c0d4414503c240f2062120320754020901a510109a5500d40420301440e48950030444075a200184103620a41d5446855110035081c6014080b81c9218022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 245669847 1250 245668597 245668601
    0x60617100806130201120506031c031e02040e010e010b03040305070c050909150a18030e040906020c03070c062c0a050603273403050105040b090607031b05090103 71
    0x1d08070a040d4882d002c1000018108850703881c50a5100781e980241e4042d1030014078050b100103440d00c5505801c03030340540c200b800480c01ea40e20598964540410305100e052000d040345035003e80c2e5070715030302c0d0002401e01c04184118440c500500140f09849240d6251214021403804064401820410300040c2082403040b0102c0000c040c04d002000c20045007068640d80395130300221a80551512000400a8900f034a00e00c20803a540f07032644001900c503411590204c901c20030050380641e00554449035500843c0c440e01c050840340302c10000a55854101d4200302c011000580d00c02400c01c010a419000390352800e0704407050000f6201c0c2800c9080c080240040c5540305281c201039001403000c810001d04003d55148030300041c06d880e401c1070300281c1061075a03844005441d00c0144030b4084810718900c184c0b001100c001d24030041c0d12120b08094881c1d0b950340c2915000d030303002d5440f000c2d40030a00446a0003442002c1e000050f50404006240a98074049155200c2c03406c3c107024868042180c103550b074025 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 245671097 1250 245669847 245669849
    0x71403040504180519020f04020705031306020706171b1c0e03130f030b1501020703050106080601050901052e020a020310091407031a0c04030803072106061710 70
    0x10700600807201c503111120b030301c3e0401c10300580740e0b44a0416011000a100c66881960740d03009048605000220030501000c1c2d4840b402c200c80070b00c0204040f0a6074408182014040c049980c003a003422403900c2402400c4141c0008007000c8042003106008512070f515000e000c4411b4070008a0b40c80d0740380c10ba80c0522081040001d151040d0a10140d9621100040300400785072140c5240c1d8945140c0f1a0081d0000e1090760000516558000303000c6022204160411081e800301441102e014503281d03680c8038255001036100c001258800300052042c2c1c5844010180903013403d03200004616601141d6110191040b0402111026001881000a031080c44600b03050ba8014046480003040c40c03581900918603440160340a0940a8500c00358074000700f411811a5000802c83e500c1e43e014041e64030b0711240103061260481e40c20000040080c00c803d0181d4812401c9490711a0002c282000440c0c80c00075104034160f1a519009040c00581c2c1c021004019540c0c2e8400700c0d2003140d4440f0340200c0081a6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 245672347 1250 245671097 245671099
    0x30c02040903230901050304141e0105370917160b01330215040b15010203040b0d02030406020d0908300c0304061103130c0e06060714030405 62
    0xc10315072406164121010301c3c07250000300c1d1041d6407074419500744403040c0651290b05000500c01c0004c01c0c00328440b5900d29050301c3c8004160766424455a8861503821b141501781d03085a5110000c02c200254030b240e6400e070607046120185024608003480f600c50504240030848160f5503800810244904103e10254008000131240c1d564040b4204144032000000421220500300f0300012030b030010500d03a004240b80300c100d0000042100c404440764030640c0580d0302000c511500440315100c400702050180101c1c0100d034002c44905088004042c01e44c2000c0c28541554002c110030012223030b500007103410088428500585035103c42c40e0880180c8a00126180304506009090003400819001000e901d0f01c00b8140c8862800303440e15400380e4509081c030100c1030301803120000d80d4804010b001154003d101d40f400040d080303004c900340c0c90180c005540719114040d68078048030130041c0c0c10b0324010261001031240481441d01600007070b62489400d400502c0c0c1c2201e250010090300b410000e45010f054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 245673597 1250 245672347 245672351
    0xc090108190e1005010f03080403380106020d0207030c21060c081909080904020706140f071404150513030f05150c0324010513121202060907060309030c0204 69
    0x8080d100b5559141e5801e800e060702840c1c00000101a5074403035a01040301c0d8007009250820346113403111f65030b000d01118402d4841000c01c001000c07202a03440505a00c0e801c11034680165410450000d1900000c134802109560040d01d06101103440016510700702c80b80c0e510034140b82e00c00c06075090307240f440b6120300914150500070884207036600701880d28840c03031946064031601d00c4408140019a0760009015040010030020f034160303424682c0003028650301941001c180e002c240c00502030520300c11160140001c036480b0074050f01d9980a00c0b9044112800c0c0c0c000c6044c9814440100e1051045440c0c4100380704000035a10001c1406260140041d0f030401c45220009607582400c9844204d410010b2010040c03c50009131403465030b8064900135400c0340b110b09000000074401704980c4103151503850600078180500b6546900002c0c2c1d89010b40103090380c01032111f545181041030007407003080460554202c0340c200325071804005901400c80e60300d4a00402c680d4802e05054820081210021750014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 245674847 1250 245673597 245673611
    0x1b030f060906091216080d06051906090b0901091e17010c0806011707030c1808030c0c030105130b0604150902030402030d0801060203070b0c130320090c09010819 71
    0x41c0011996a1144490302d00351200255410303072100a038440c2041e103403103503400140d040d40880c000002801d940c0703a055000080c00754852000400c4131141c10034104801910200a10805a01c0507525000301040d00000c1c2c1016403420010740355030f415000f10700b228580c4401654485020b80262070040c1000d800361410803104800700c6000e4000c03c01d2060108030420301050165200381c42224400c00c240112864544800c84210050070844048804025072400185080c07242d00300f8060003004158011550386221448403401c05011901e8140b181c0d140c2000c0100c02c41010a170741c0042c87d40200d8540c40355807084006001803003c00c44071059001d0026012508107103070750003180900d000b01e04030303001102d60700b20445128909010307170401600140058000070707000c0c03042c440e04500030003425414004080440001100540d04c20303154000c4100100c1074140e41000c1c3c0d801189804da92401061034046021003e62050302129410041c0f60400543c109580403c01d0110905002041c450f071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 245676097 1250 245674847 245674861
    0x60308030414120306060d0c090503010c0e21031c020d2912070b090d1406012c180f06040c061202030f0705091503072f1b030f06 57
    0x24010306090442c60b4401c14501c14040c0c0318034070a807031254600a0a047c902080000c03e03001800211585509020007220089410780d4280240908800076a5890260300da07503c041040942260710006081e207103442c20101c148001004503000405c1c02c0040702d000c1132450020f0030081c070481d052903c040d407900e84c010000c140d0600c6c1122100c040700b42c140d407410483c9020041c030034003500c8a030040d584c1308100411074980c0000281074a00c070024900310b01c00c0301030348620626a100c00440001d50b0081b81c010300c8a0141050510201516210000340b40c4401c1e500507080240042c041e41724005501d08000a5000b04020010b01210f41d002074980700d041510b003038406001c1c1c40c0104070100d8003242020380d41c07040d9031081e240b08590710300500011b038480110540d502c1c0e010344801900200d19140fa102c030860002d0085000d07550070360310540c240c0d0a9000024500100c1c03a4042c00315104000e040d4110b040c001182d00300306801d014083c62030000f2600180c03a03c1d00740d54045046000740c108020817 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 245677347 1250 245676097 245676113
    0x40812040f140a030f02011b08100f080c0a06110c060d110d0903020d030c0212030903040e0c03060307050a12062d0e1605010203041211150c010c080105011706040603080304 76
    0x340a100303440301706180001c8113080c2c0c01e131240305041031740c4d114056042000c25441042020f4200700c004407103045050700c8200d0300c6446030154005108a5002d241e00c54030509041781194000d1070b491416880440035042c000d03480c1c4045004240c400c0d4004102c40610001a03440303502e040141621066803890f1210300e00002d0050030358140e01601584c144032801d2400303030184003010011640a00315411801041d41601e0b0806000e0004030300c010b0001140c0d02c40c50300c0c0054010122040c03030540b24601002010b29080c842d80116000c1c90500c24100080e40002d0b800c080b0b419840b03c1d0200b00340b070101c01d178442145240c0020242c0d610140d06500c840c00200e50102a000c0d881909803482542071095010001c103040c460381d070041e80100420042c082c402244c45043c0ca110f44214800c0c0d032808400614808841ca1010783c40207800240b50501040034866504e2424840c100445690725020001e001000f04102e554006551900012400d40e01c5910000140d079004d12040e440e402c02d4217140390 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 245678597 1250 245677347 245677363
    0x3022212030f08060d15090524010617010902090339040204030807020607291e06010212090d08031e09010603080a0f02190303020a09050108040812040f14 68
    0x201140c907000c5401215485485481e2049030007900d0204022100e40d5021013901048503424106647d034942500060803d115064051a282c1c07000b00c1d140340009901008864181c1c000d10030300c0820a00150100980d009550441c1e00901005885080304404a0b05101e41a41500d03440a1140380c281ca60910703110000b00909040304840c0f00d0f0500940a220882c803c5000150017010288001da00519001008148152041040d05603401444420000780654802c0c411a00185141000140005441006000300c000540700b10103041030000070b0744980d180c405880150790000f17801c0d680d40d120b410506451a900068540c4d41c0d14204c4604403004001003155045a02044041401c88005006c0c203015240c005c0b01061920404820aa994500005860095000b0250001c008165a4101c509903600984001da541da900300e000512044007a000103050100720810b00c80070030441d2081d161a040383d119401c1240e16542007034032955074081002050011800c08410241d100451a22 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 245679847 1250 245678597 245678603
    0xa02040504050610271104030605010e010302040e0102030717090102041a030105041104060212031008010216020a06020703150c090b040609031704050d20150301080717060703022212 80
    0x14005488a642c50282401c4480b0030410b44c030310011108404105e82c1c007980c8040d05003140c96140994a035240d0040e40c030260b000384806044a40100b0035030900340506002d03030584400851651038a20070180c440c0e00443c400c0c004101a520025003400d13000d5044401400c2e041c0112615081d842c402610f00780e100340600e6000301d0400151280c001c241d0400c1e03900380c0388181c0140441d00840c401544081e00f000707141d40040c035000000054000020f200504000380303605842644030307a0a00500003007421640c03020b030440d8040c00c01080414009848541016070500c5c002c6155801c034101101d05a469411600354502d00140004049070001013070070460b4411a5500104000070544010901461007010303080020142d40e031300040c400318801500a00000485048200e0030004118041c84440000d18080000801840a10800c1141d9001810590b0540100010100c201c82d2100005049001819000b20340030315914070002000d06500c541c81080301e15070350f44594032000785005c0c4c1015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 245681097 1250 245679847 245679871
    0x3313020426010c02060a02210a0b011106240a0f1e0b090105070602090103150609081603030203070213060e0408190e10110a020a090507090801050601020d0f020a020405040506 77
    0x1c006800e041c01038400d070f0f0142d6009000030b5901c07014000040d60201c1030010344060400014040f00c00840a19409039a808000240c0d84d403922001510150491001320890351084080001d55030360b2000c5c58070301d1224520318a4071403183c200032070b81018140d0005114000c2080d00030840c1c0841d400b1300000c409010a8000c2042c0d943c2d1030f4844248120000c403400079000300f102d02c3c04601242c004260782401032400084c0348000c4610540e54011a401140000300055410421a40300b00a00d000d14100c0383c826100d064510b64019541e8401e1000003802003030b44011041c0005950760101d8014042c001c0403541a18082c54201c0d06980f005c0101c2904c1c4980c800341d0369403a031142d05000b83c01c0c8005402c40c0c460102921041d00c01601e910703800360a51062124050040e01c68400e100c0050005c64030100d42410043e0f0081e08550060304a004503a140c0020090145c4c5e000640c010400c0042c03e1020065007640c00407400c0011a284c040e4209003454103000800c13500040c0b0500c140042586 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 245682347 1250 245681097 245681159
    0x3030a2a0803041b030c05060c1e01020901020705010207260a050d031d1c18081204030c0e040309030b04020f100810060c0c030605090a050d030603030833130204 71
    0x11004c0311070240400740104401207014405400d00c400100400b01481c4200c4085100301c2e0b01d034141c4412480d280d40101d94002c1908442960100080c4010300024009407a40c6814840c400c5100c00650401144c05900401078005050060142108994014003601c1ca00144110098054410640c0f0701001d01c4400c55962814140400c0400740c0d20030b152841c0d112480704c07110480300031740040344100510004101c0003681101c1040201301d4030300007840300b98580b0300e50f00345240c2c0503070a64070180b10240d0036402c100000b54007007601d2342500c1d8050b19551040e1540e00100d9440c00761601200d0300445002c64624031140c003c2001c512940c089802401703036a8030f0b1070044402d22404c0e00d0040031003002d41820b1002910540000750701c00950809c58004450540310b40b403500552505100106c0e46c1c0b11814802c1c503500c09925035120101540d600c600700034665140d2500c14001c007941030342408144802d0b81c1036441c45e600c411300b12034814065454646407030b00454418038a051501640c18802c130 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 245683453 1106 245682347 245682383
    0x10020705040c11010c05120c130b070f05070501030605150c0a020d080a020105010806150607050c040e01020901110d0c020d0c0902131e0503030a2a080304 68
    0x1070b4105114081c0c00030b107421205805c081808005003008400d642c1e05802d080d19400444800712203949140900c1c99840303113040c3d908820740c8024009640c0c1c0c240445814002c8216008109503000d00342d03190015811606e03a80320302c0f80c00904803a003259250f42c81e800500b2680310f0200944441405981c0007503014405140e04958190000ca8030411003039091081030b024010080c000c00b82810403d8070100746200440c0204d21952000804000700300701032003011101d210203031061001c0d60407120782601039002250042c3c0040e4200100d4240d00c04001460b1904d140c042e03c5502c8051141d409000c500c843e00c2c030054407031115400d00086e0480301c62005000000d440300d4155106424004041d00c2002c681c0c480400c0014858001c0c03050340c1c0c020044907410111030070b101001084201c4180755100d08215031404811407001d100c0d090100b280c0007588101d110b02d03210407247c400030b5 = true := by decide +kernel

theorem cover : BRFrame.Cov 245503597 245683453 := by
  have h0 := BRFrame.cov_init 245503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 245503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 245503597 ≤ n) (h2 : n < 245683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
