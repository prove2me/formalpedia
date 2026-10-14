-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0661
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:59:32.431081+00:00
-- url     : https://prove2.me/submissions/d24d0e73-ce2d-40a8-b73b-dd41473f5cc0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 118705035 ≤ n < 118884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 118706285 1250 118705035 118705043
    0x7090902030d030b030601030605090f010e2103090304050f0a0306060b0a1205090604080c07030f14070e1b090a030501050708060f01141204050c0a030f11040507020c0409050313090207 81
    0x550b4180a803016010340da21443c40d1501580135400410204a4582099801000720360603990f04013001c1c907000e401c2d18222140074106500003800c1e0001c0115074026500342800b0010000e040d420618a140e407070344214443c0c07506ca140c01c18160b00144e950b12003c0401154444001c120141c1e0f11216004240c0044110307002040d10302c4810700b8030303112a02865200c0c4840f14090040e65546589410054000790314484040c0716011020002440c0e0a0010321403a02400e50144c050b80482101843c1054541000825034915400d010440440e200222401c0301102400e540383c041440100d0b030102580c0e80064207541c2000203105545422400a60040801b80e42e0442c107030040a0040d01c501e91152440c0c0031003c010054036480900c21180150410b03c42c80940744d000283c80c002800c80706c81d070741003a500965010306c181c041205e11800760102d984159002d0005203014103000e900c808007114a203000b03503142e000036000c005043c001c4806024000100c2008141c407200300c02c00941011000319 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 118707535 1250 118706285 118706293
    0x150103051003051c091502060f13030c0b090a20040605030304120f020a0305010903020f19030519120c09090b0402090906190e160e0a05060414060c0709090203 70
    0x200041c1005410106036600030340144076451305900e140864004c000b01d41001c2080f61280032801c014182d02204410450394010078503810701000e090840340000e8006243e070801d0b255040c0000e90018580710000c3e4218100c04919521110300c94185a404840200110b02074656107031503c25104070010300100a5908210290300da40c18941e6a128a020300c41e50307002c40d804c040001501d80038030f03010450710291442c0a8517960f0741e103a5081d03400b414021030140e041507184001c5140c040180c02800380c4040b98450b101292501d0240c03e0748144200c5045101400c1d51000303a80d07001341c80110f503500000c1d404020910640c034000b44080c2c4140900f00c000d6042c503000c110307280b40900940740144001450041107444143c04c01c8a400114410742e1442102d690001440100640c056482241d181c10f005519460412006100a0b40d4803140307482440801414071203511100151800c3e562018010f1030304010500001da01402403a20452891149000c0860308442c20741080c00000e00c01c1d0211 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 118708785 1250 118707535 118707541
    0x1080d020106060e04021318090215250302030705060f190203010b04090b010903060f0501050f01020a051b0f0307080706030b0616031d190f0501020109030203120c0c0615010305 78
    0x8034260b0749a0703c1004009602905200010700e80b0354003c1038104400301030300c05032a0740c1d10b40022a602a0b000031500e1559100700364003d41c02c003007030b0100c00c240c012021180b8003609941114449410f41d410307041c25802803286042018020402ca880050300b0204039030740c81c545110110f204035002c0ba20502d14510781c141c00c52801d4001d0080d6816181c40c102d641e8281410680410f00406001c0583c074104217040300b00001080040c40341d151070090101e804103086d030418090040074240d03210150f04651144543c00003041000c81d203001c03591074205039642446030070303c005030400302c0308005941d0501840b01c000940078070007e80b00c000c55109481c1480103080764000c0110b203014504018034541c41e5040720000080c420181c0e41c0816106103561f040405424012a511030f10303107810011a010150300600091800300c94140041c00244028041c030b25990f42d00075140c0c0200c0424210304290396012880884494050300d420016060881c0c8242c034002031288408408603c07400d001c81c0c505804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 118710035 1250 118708785 118708787
    0xf0c040b0f1002010908030106020706094b06031a04060e130302071223030906070f0f0206030c0a090e0103031d1201020c070603060504200a030b041401080d 69
    0x40060115004200700d80340700c460000d00000541d00d104a000715540c903101c407000030711078074003960180101d44c0c010410700341003800160000041d50001ca088205905030340340c450380f0300350342c004034041c660103100c500d00e0110104081c0e40c3c9035072100510200781c004000c102ca544c5507201c1418131002042828442101170140012284070303004103010483c001c4001002d2000080010188911920450b00380076a9108454413a032401c0c001210006103048911828210a6011640030312a460141d841d0041c1000007980318410302c2c0e001018202c1c11104a4103211203503902c6030009401804555032841c1c011040e01065000d00c11040100b500128041040400003c003641030326459118144035074841c7c043c914540003071140c90399001514800c00282e1070001c4c00900a14100c80300180b500b03600781a03010b003d40301c3d11703000107010f6460134454034a04908107070700c0d00700c0020105441d0358802070498100c014008180c0c0181d0003070701f84191807002401100e0054102d507101c8003075504400500c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 118711285 1250 118710035 118710041
    0x3032b05150108130c03081909150c0c0902030f040b070801060f121d010501060e1f0c020a09020c100e0d0c020f0307030f0c060f140a0c060605120f0c04 67
    0x103107005030301195a40c0108554014010385400c01007218030b40034008001da80c0c045e1020310640040b51603500c04070310030842d003008840e40d144d40c51080c01d00000c842c0c1498064075440c1244114030041003131801c0b400301402222100c2401401c41100199560718248107403a000764000d40d400c40d0890310800015841c4c501c035000c035506980c035550300c42800d5010050304660703425000501001d19541c032441d0420b551504050781a1481c03168002043c01e602d00f03000a0402d280190381c0502901650010380140d060041c0403d14910184c01c049002c20980d0000c208800c02541140e5161440068501e40000001442043c0300402210911004180403003140e104c015502214012800341c08115005140c0960720a4284130040e00301e4420710741d241c44a504151550405039049045500309208071940284e1030000066941048c0760000c4640d0a14001c0d4030980800d142048118001e800c10000d0030f40024000b440010040d0804511400e40c881d2100c1c01c64401c0003491240b411003d0b046c1c01c0c540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 118712535 1250 118711285 118711291
    0x4030e1008060d21020604030e180406020f0405120120040509130203030903120705150105010203040905280507030f05011401030905150117060901020f040603020a020c03032b05 78
    0x1544101098582000f440000410160304465507002a00001118603080c4034510000c0d5165004208500b0305050240c0312040101809002e0041040540701c101f00182d101c80d0050f521880040e81d82c5050414600940125008298411814900650004415006807620614000f43c5844070f5403030107c854018451072180300d80103201480042e1408010080c00000b5030300140039285000851000a8144589041c000d44040004581d40f424000704128800c0340e4031040b1407011465040c800040d64038003540c80f0342c1c103006440d1030006401922403840321804805000e402a40d25a0341803c1e44041d180423540240000d15200303042c2d55003506030103103904071102583c1c51203044411200440c0035000096040c0c400e44904440d58400d40c03a07180349103000f070626402d01c202c602e4801103d50304000000e0003280960b03005202c01c040c2c054103031044804840b010304006946a014010a0341070440303c3c0e503042e90602001c00d00790b0241c80d681c0a82d448100c04043c40400007001002904100d540079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 118713785 1250 118712535 118712537
    0x111201030807022404210209040b07180306020c060f04230705060f030405120315210d0e01030c14070308040218010306020a0f0e090606030a0e06090604030e10 70
    0x11100410100c1e404800919815001500c1e081e0b40320703e514418020780c100070307032120b0020000103800c0244070900b01600d600680050f81c3c0640c00300c100d800041c408140900b0203030600e4280c90104041c2d034056041400749100900d220f0904035900c1c14603600a412501652449000b01340018400d5980150388510a075440b921807101c45551a19100c0c519000c44880b002c40d22501d42d01280955810000d042110030140083c0c5e5240b409103095801c203080340d1041a40f001d024400d00c4038260759a00042c0741d5031402d9903809401c3c00745801c200740d003c500d45290441405040000418650701100800700120280c90034030407a500340404880804444007041d410030750500c03112000034410110180c00a000a045100840f1002c1d0b542100d068227070300450300603a002851258141e04181003d600c0c8405081800d0170340218030106482040092a1078850030000001030042c81c0316030720008001c1140c5040303c55900e80522000c1d51100700303840540108038481d0200c2024600311148288041c41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 118715035 1250 118713785 118713817
    0x303121b090b0c03040503030c010605100503103c09110a02120f041d0115110d030e01231503120a03022506090201080a020a050a0c050f0a031211 64
    0x30b40ba1004016030012031045070305010030040061070345c1c1c1c10009000f000a5240000824a190100f0071100390180024901484800c1c4208120011045203220071500e0001001820350748081c41840d000c2e58103988030080d032041806d007100303070008220b030b41058030100706d0104041c4800c02e004214500031009420700503401124440e10000c5c0c402c010705040e040704078801d820151030751300d0035240c2003d41000c0c5d0007040c82d100042084201581040c01060703001d003000d0100030181c21540e41c94081441d002c00c203150315115000441034003503005800d003041d0254201c55810030001c08412550007a03a0300f280500510011034124500400c800098000214006284c191040016006134009407031898060700040048866110544200404e4511854000420300b090740300140c20558060b180008442c0705015020515800004660207041035040c03804030a05135240c02d030f1818104503004a0103002d4001175004064001d5603600c20030300c03440f005000c2c00c0c0390001030b2074481c0500040c009404c12 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 118716285 1250 118715035 118715039
    0x24110c2e1d04022101030b040309050d080904021309020f04050a09050708071d030109081903090302031e04051005070b070c110d05010e060f0105040c0c02030604030503060a09060303121b09 83
    0x1c0c1c43d40c020291450450340e001d40c03900c84950300f008a104240e100750ba0701600710f0204810551300152400182034200d030040486507480c0c4a16956002d58800309010343c3c1c0c0000d229014441179144031000b403141c540d0540d5103104030450708c000d42d003003446024050131044802080d500024011503220b203010b1756070840e45030303107080e0b0441d020642c00c03040310301000d40c0010000a80d01d080c00f4050a442c0103407130040e0b031070b40007407024101010000c032139004061421280d44000303030b03000c4201c1b2100c1d2081c005414080800d411560325901c950344c03205601c0882d02c4072039945aa00b10020b001003601420710030101d0307601e018040c2c03440c5c460540000c0000d400b00740320000394940300c40001e800c01d0080d000003840c1100441c030149020020707150000b081100e100100726070315180c064940008136030300c2c121aa80040794003095030f904001d4401400d001d00440082da845d240e41c1d9440008113800d074414007400d0364a0a019140c01c1d5541034810f03c0d0703070401c94016204520000c00410340f02840c1d484094081c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 118717535 1250 118716285 118716289
    0x26011a0405071101150302101b03030e0c060c0703020103150b04091d0102070308010e090a050613020d0c060804021c02030303060112061d09060124110c2e1d 69
    0x14002c00c060180301e803401c24040310520901c9007000c640c42c1c20901d0405142140100080407a64020300c50421000b0303140003003210030407400450b216038582804544100712242d40e50811003411440350b044440401c207012840300000d0b80300b007107038000e0700d080008907a00074110250300441e02502100c0d840400c001c00c202c0060b60b01c000450340d0640e0b0000500e8007070500036403d907404000190009180c0d080140f1001e5008014075070041c0200004041d0340c1c180d40c2c4d50350b855070401482c0c0ca56050549041c0825501d42d540300082c800d602100ba403110030b8841201038040c80c030655099014207a481c81c4d0076140710024002c41101d85e0000c5c021400c0d43d407220011208881c0d501c841c0010240c617071900052010f00041d0401260340e280d0305008071480d0540c030710741ca4804141d0008685040758980c00d8901c55254a00000000d014500f11040f443d10b8100645400c0e03000d10b045030051f2101e1b9521000414011120317008001d40507002c851a10b040c01c1c00c640f4400c120340c54100e0038a020704060076034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 118718785 1250 118717535 118717541
    0xa0e010605030d12060308070f020102060c13061407080a120b1503060d0204110a0309051b0d02090403021c05030702011a0a0b07021504140102060901050106050304080a120626011a04 80
    0x22911101c2c1c0805d00545a031382c2e00b46540c0200d541121014000712442045680502c03a01d40c1c4280e504283d10700f800d800000c0c0e10020306a41c402e12080c800030710700340040000c01904998400c0c0c1c00498170342d5209402d44005200210611000d103603d450302d4411402464036890000005140340c5074142940c4801d010000325a021110403a8426501d40800c0b08800e1202c001c2c0c003d40902d07481c0080c0103002c501f00203003440c01c813004203610a2200c241c101000ea4a00183c030f07000396016070b03540086071740301c0c40c0592800b84940e041c044a5500304a42a40c8154000021885200f070351f4021301101508401d50051024a412801d5201d941d00070107000d40c80c080005031458600042c800342e4107e1640e0b004410a51054010070100340e859820b100d01541c040042941011450008010b81d625061000300135010151000703201c50400500e556400344035840781c08402000003020081e071541d54100d450300e8000a244c0c07104131b1503850101c801c03860062041e0a01d10003840c0300140244001c0c0104001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 118720035 1250 118718785 118718807
    0x1020601230406170c0d0206030a090f2f030105040b07050a020304050603040804090b0a0806040f0303230103021002010e062a120a050a06060507031d060c0102030a0e010605030d 78
    0x1c010301c49021010960b6450050400500301200e80710721110a4898050401d611104100c0c0130302d02440c038400060b114901102d9010b1022800002c00d4021403905080c80000028040c020054074a01c02140c1c81c0a20525818cc014048851004a103010189420ba40c0200d9010b031480480000040e2854015002008610b046106403841d1940341c10000f01550021b03201501c600c14081014001100c40b481229030b0124216080c3c582c082c0ba00c48081d0341c408005100600c0503103000114000c043c000e400507120982c0c4081500301121000d8000110b82c1c40074481030307100700c0c4050014110316006204054004940b08040c03e860303a9516010030120044e4400c4810051036001c4101c0c0740d080580c00742c00c140c1714116071050305003000048a403e943c1d016000c45001c9142c48001c1000c240c00c102104c08181d03060030018055910740c2541c1481d5240c98040c80d4003d0400a42802c260906500545c0304100b03816041020041e074100060803a00a8016650140c0c4408039030350344503025030500d0712 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 118721285 1250 118720035 118720079
    0x120b010e0a08010506030f0102070b011509050d0303050604050604020a0e1c060c11070b040609090f060f1e17030406080c041503020d051320060d0504080a0f02030901020601 76
    0x800c809820080751845040d940407107420b956803028024686402d201c40405028483e00070f504104180e100c1c40d844120600c00c1444840001000002080c00f5041e04c40040600804e00c511103191805c014018010480740c0b6072289190400250b2140307018801c1da070569042e0743e5450100a01c007000d1100800343d003010b64802e60340004103031b400030f0000d0103003428102099171265916803c3c03d10f4245400025003008500300e2051006126040d031000c800003c51341c00080105642da500e8010000510315900002e4881c41580404255901c880320000301c0c420a011800504a5580a016842c0a070301c00c2240e0003a041000104801442904a15041410fa1581c1c0f464640c2e40c0b414101e0303500710b460003180425004116680760707841c1481a594071130181448441030744015641c0f0b11100a611a0401548045c0c1c0d848100584550040d40d00481031050104124205820401150382010f00d41ca40000c4140c209492414404070542c2c0a07440306070020b0001d80d007404503004c01c621510640c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 118722535 1250 118721285 118721297
    0x140d1e030302160302150c0705030d0203060409020409050d0908010204050303030f06030f06070905092206020a0c0602040e01090506010c08120601030e0a121b0f110102030f1c0615120b01 82
    0xc03c941560203100303000d102e90000d100c0c044801c000601000c0740109070081003030302441071201113200030040b95000101c45800580e00c0d9a038a0024000305500000030790041e10f000700340010044001844c04c404500303602c0d50220305e5902c00d1780600380e201d540a6990150414008035081c0d20202d011150403150040641c2c0620050303140c2a46070034411540040024a918010011400d00515803500200914038540c5d203499a401c0c000700d003130107101d80200b8003070b0b0005109101510030b00d0501f40403540048159621940d0300c020088104003070051003852031038100441c40c20340c025940b0000c1c180d80003146c0d50400c50008000300c2d40501c01040c050605443e0000700703c1c2c80300c080c45403844961040144916050f0703c8180200b04030300090400c061419912080000f046400000d550500d5104608000715140700b40102e00714001c050303076541d21060216030302080c854480c4220740e8040000500f0840966610b0110304403030b803182070650101d0400449482811580d802002140c1f8041c1460 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 118723785 1250 118722535 118722547
    0x230405150c3408030c190f020a030c031e020109050f010501080a060f111219110912010f090c031101051806070309030b0903130e07050a1101150f140d1e030302 70
    0x70b144607a00c00c88039220301c682e00140f204c0c4c0b8030721908542c61b4402c41c24038111080b40c00310503010f5560740b6a0207000c0c1c00d000d0001c20840400d40709200c8500c03048500568111461008100640680b010344001c48140c080c4c0500c070000a07070144244c078100c2d4618401040d650340d091301d411000300000000022280c1c0c45100100014000e44000d10b070760080e440d030a0328640b418181d050003002030290b0f60300c14281401e98100e0619a91021380e981240100c5400b0303c003a0280282500401d60243c20b102c11070704010505060003102070b4001c007281d000741d5542c421000654011249481203130101340d0307103403d0141c2501860802401403c030840c42810600b0410391251a44400c0706400c0b5031407800d80e400081d1005807082c041c100c081c01840003028058031403c085e41c0c003800134040d079020001003040140001c013108809400154207000b43c5654031003866118507403c8400c10307050090f000c00100489908960703044c2000182d0031260401020000d4807030780076074100340700d800c0c0c4400c0d010103400b0b20035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 118725035 1250 118723785 118723793
    0xc0a0203090d08030105042405060d020c010e030403021008010b0a0c020d0203070b03090f0f03180a0e0406021201081903030203070903080d020403020a05090712230405150c34 77
    0x5444495400788910f552290300d001c007000241c44000e00c80c2405121501e6200c614861099005002c3d1002111003680f0b5085981c0d001009001c0e008219000350b0070501c0e00a0f07032890100091095134003d03544801c41160a40040d15050307801c2c0301d03950080204001d11205103124900340e000f81440103000f03042140d06c5400203441c01c4070b035401c100301d5048000140040070404004441140c09400003401c40c0c1c544200200e0344a0240f2403080f2511680400f08150a680d0b02c040c440150140d10a402204c1c1820306009000f90408010484900702940020982030320000e800e051060065440c0092272805079021030180d0800f5113840b0601400742000300000d100b05c00603000c03000c880c81c8016100c038034500400481021a90255015241480c20310040581c840c031025004000d5003c003152001e41d07040301464440340060803e00e21446203060004102000ca441c54200c0342c044400c11040e00e80036180d40d120302c03940301c518000d01300609400c010640c0100010f80e006e1211840242d81c44501e0f19 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 118726285 1250 118725035 118725049
    0x1b0b0105010c17130602010b1c0212010e0d0c0b060904050a061104170309040b09010f0b030c041212030c020309030a1e02041409070b03060d0f02030f07080106030b09150c0a020309 79
    0x141c02d6001e0328046130900c804c40e07091080c20000a401c032102e8004001c2082030a42d03036030901c080a4020f014002000402e030000750000a90303103d8400407207200486240f402480b6101109003110030501c2c48000c81d5040c036080098a00694101028102c01d064503940c040041502101059640030b050000081c1402d00b40307074010402d40100d000e15a03940c143d02c2000304603902c0a141d41c0c880c0c0c0600e40180201050107451038195105d91010765901e44600302a84030600556001400450844510030100a8040780c0300340e410405442c14440011110401c0e6168011200c20a82580c004540480441c12000c01d0511501c00400000602c000e5500410b0541c0d00d1034202045a500c5c030020700c540403000700401402032880d5600316045042c400d00040a00c3d54002d00903000720703038903910030007555014010040308407040800c452106545024541c0a0540392209442d558202c0000600d40c000215441f01412940e20480101d0342d14020382401c6a00201041021803106120210064603104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 118727535 1250 118726285 118726297
    0xb0f0d060e1b03060f0903071203022b0e060103020f0607030903080f0a1707050f22090509010b0306060a0509070c05070e0612150601140c070b0403031b0b0105010c17 73
    0x14086002c0c11031a1024185040c4001d40003980c2c0c038113280d003000341c0f614000c070075122081d030f00c010640d515501d089400c4019002e100c170008941034484280b052200c00030658410310040d50401030000c11000320105440b01070905c4003070341100304060101040d10b070140080c041c9c24403a0800c200207a80741d4844110a0300a01c22102d2204070014041d21410380019078403681c014440e65444047c949030070300030181d01921156240501003c2440b0820703a001009425a400390984840c00c813039541c0001d1405428152888090307546040c20328489400c020510900c00c0e50003408503a1a03614040500080d120010300b60001c010320508000e000900a014000c000c0080130060001070810a0400224103681040c000c84c0d540050500c000d186401070340968801c100b400d08a40030340341614042d48910070f06c0c1c04989a401002408100d10880e240984140d901a503104100507040b04030a00840c01c580d003010b40402c074181c004102540c85000c0c00020540b203801e156507440a24210b0030707000d410030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 118728785 1250 118727535 118727563
    0x103080306010801210f030e0301020c0706080a020906090904030c0f060903030b060a0f0815040f1b2c031903030902090901020415030b150304030206070908010b0f0d060e 75
    0x10a21105690103d0224058684554441525800c603621415081508130b8000c0884041410001c1811702650000e907010034003800070342d0340d49240004140c44d0601401120013068200c80420b81c00c96151003940d0000350701070413807490a82007004008050a0040044040200013044080000c1103584512180d40c4161808200c81165260203400e54903005a400d0140d5801d012016091313130b002c984041c106040d410031280c15151084030149100c8011450b40d0024180f90740000c49501540c01119032441880028407000c01c180411148404040d0a8003003060310003603001c06110f9a000fa00580600003412503500001002000c0f4a0700800f09040c2c02082d40c640e03102d000c1d41020102c00741d01010300e1000714502400c20701c0c814805ca0800d5882401c00d41d0f246c0303030040607454030315100c1242035551420540fa8581403400960b200741c01c982a00000302d18aa0010707192405000300c9424180c010244407103841c03a00140041c55444c1041030b200147c9903241a2000b0000307201000d584145 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 118730035 1250 118728785 118728787
    0x21b040608190b071707201e06062707030207020d0804080f010902240405030604061b140708030606090d03090812070203070b07020a090c030b0a060c020a0603020918010308 76
    0x410b0400f0740d440c00c00100580140300703c0103894140c0b00c014000042d446245030410200d0401c01c0b0041d184c00380444d09840d50180b1030011140d1000706d02c0a04c0540f510745807003c4400c281c0c2c40d0002d00c00d080100485c00c1d001102c0b8260100440701c00e1804140d4020614580103041c8015030b0000b0300d9070900400c0541e00c9180000f424480194103005400310903800c600240010740d070035400300d030383c40515800d10000080034001d00d16114044401f100d0003031500404581d030b1410309042800050051901311f01c10b484225200d40f0ba40760044952032000c80340960f84034100400c035102c2d10304960005129a5020500304070b90f2000da5610490405070754000e0b5101c042c0942010281c91420400250a01810300c082c069840103a40000c0c040085e154141c030300c10b490b54802c1c40810301c0c15840750080c0700180e0824100d140d906a05a101d00001001140c41d14901907450b0416102c2520b103d001079003041c40d10500b0f100a60090700281895500600184a0f55049090b103400c2084d083c2c00c21a80c07032074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 118731285 1250 118730035 118730083
    0x3060c140d15150e120a14011401050a0807061409040c11011a06190c080406170a02041d0711030403030323010605030106030c090e0f07120606021b040608 68
    0x140d1003410101624881046221034040d0b50b00190942d41c00042d00ba200e94061005d01c00c004c3c400f0300032072030200c1c0d0240d100d02040c40300d15512406081d000c8441c0300c40d4003e103800011035207405000801222440750160403403908190003140c0208400c068180061400c101481c81529184580415041a50745112208401580550a54a6102c0d0240300b102c0301d201e41801c0b90341d0f110110340f04605905442510290907000a664141c0040006400300b0008a0001200381d0440001e00d08216401b06080f0150365030600d92040740528010b8081601d104500c40d05076440311540c0390b80100d4982030040314180d40c0c50805186034420742041300080e86417400700340c00d4808000c0d44401c40c01034a418206d1981001401017048c0414844c9808268440c05c4109607a8000c00504026010800480d1024030f490a0301050240080e114100042c4000e03502203003d6045115141c00d83d9801d601074103108081208101c0d5015168850355801036031030a00041d2103208100192103803010900d20b41c11380c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 118732535 1250 118731285 118731311
    0x30b160201050c04060203090402031905090a0302060603160e06010c02120c010801050609010e150f0406110c03060708070f02030c0627010b1c0816031d030c060403060c140d 76
    0xb0000b51034655078400902042c04983c1c0c003c419246200c00c01d540060720b03a0b4900c003680c1c1d13803018102ca8941f8018504000e01818040129034094024025021a9a03d8540005260303448034400d0468071981ca56400505ca240c9030346110742e03000003052600b010048850f0300040d4010550050052556115070141c25507960400c0340b0900407c01140c890f801c00c54a200007a00300c4080d007004500ca04030304d0450b00050704140c0142c48042e045608450b40311521001d000e040086043c0200309144212031180f8210f250009025200382c0040d036030301240d80c8420303c0c1a50506500749088065000502c50410140002c020036031013014085104002410701038a600100c082b146c0119250f079041220f13501450b100d200d580c0045141002c107846d8143e509041c00840d038055417441d200c090080761010024140d01ca00b030400303c0e804800f5000603c10b6101c04040da6071002088035a00030310305200070030100c2c1c200e03070000b0140000790420116500c529100d13400c40368400c94003040c00f076554a400480c50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 118733785 1250 118732535 118732541
    0x614010f0b040308030f190e03030601121a10031e060312050c07061d04020a02010c0e060702090109090204060e07020724081506090607030306090c080c0711010207030b160201 77
    0x10074604020a02d0141141c40740001e40c40000c0c00e020380000444042150001d50a500122903680c500007000546904551142c503030344141c0318070f030010f8000d00310101c3c68820341c480c000c5c60030318041106100c002c0301d03814403640c032203542180300c1031641d503a40c4045102c02c000358a090401000400040761810740c60401004054050400c080000c03c2c002e010f00b204000450009651050600c82c0b035007144940e9215600d000304401c0c40e001400450590b4115030150080d1007000015143c012499400c2000c2c003003980983d5178060341c403448030300c010081d04445902802300140064008030340700d078941400b0008800151280710042e0700170741c410000b0510390803400d424903400802c4c540d180402001c1c02042003202030110700034103c1e0a5106076480d640c071011990302c1034000c0c20342c50b200d814a040190080195100340090715040068450926101c0d036881403080c02e41c141c4650500b105502c1d8603152032283c1c3c0b480340c198491039502001003450b008130701d84280e03294243c0c180ca2180c500402825 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 118735035 1250 118733785 118733789
    0x30507060f020d0e030a140102130602010b030d0302031b0406081f060c140106080d09060306081c080907030209040b190c020309060a12110703020d1d1203070614010f 73
    0x1000081c0364058640766000c59480c2e0b9682180c0b4190304802c2980c00060305003190303120000c1443c2e01081503903442c10b1043d0003511802c1c518289008951380d491400ba8261044002d82e40d605400c44207d900905000b070703024503000900e02e22081c0000d410f41004042d640d100d5000080800ca9007000c021641c00c01c450300408800100015251503481c0000c05064800301c0b00004080c0750b0203542540310b65070254000d600410000040790944002c4030805460441c07980510b000103401c000b40850800400911040e052182161103541d198118104030b540d0340c00541002400d0003805030010141c3e4030080340600543c010301c000b03240c508001e100e4200c416281081c62541c5414146c2d9481b69a4000c001e40d02a511305070303103080c0e99150b1440d08543e8050380410880410b85840c08070043e030041c01c0098110a40300c1e4003140c204081701e2209030f580c0810041010780c8038001d603240c01228102102c1d40c800b070801841c1124103080c0695101c106031048039020b00c0300134840d04010425141c03402ca02c280 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 118736285 1250 118735035 118735037
    0xc0a06050f0106170402060c030706050109060f050102120a050702120f011d06041211030c01110a17191d030a030f0b04110702040504020a03020306070908010c0306150806040b0d080403050706 84
    0x20b2404110b0224418880010310203840f40c2c01c00302d802c510303699051080398a01d07039012f01c08100540c1c4410f603050003420140208031a06c03a140350f01191075400000c0804040400580325410080543c10031940c0e0740c40008100c1e0008420005001110302c100610550301c1c00680011a88003101228200b02c0031071161010071540c4198280004500e881201071801c00c424a491681139100b03004281c510310456900200795843c040d01c03070a0b946501c1002c0d006141c11651030300041410610b00c00c0281d0380998600d21882d400c94200103448940f0790100521080e6401c03045003009002c00002d007103030066090400802d46810f03d0300b5003a00f061107031140c00c0e401100c00304402c1e041035202c140b280c068100024050350303031040400d041d50707501c4980b00001c5074014111440c0c0d28108800621070103051152140c40e43c00e080745005524000e014030b0003555101d0325100a8524046e0701118075100c0540620382007540c409a0f0f803075030b44640c90840e0f00c443c0a103030810343d220325600d03283c0c0c540f00181d44400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 118737535 1250 118736285 118736297
    0xd050a02120a0807140405061201170312070e0a0b0412020a0803030c04030f150c051b0604120c03090510020c0909030403020604051002070803031510090602030f0f0c0a06050f0106 79
    0x1440150003c15042d0001c0584c94001e80d8418802c004002a11403a0480c551000000c00c0200060300e4450510703058502001c5901c40a17051491101e035640503490110701860000303000600308611426800700b44c054014000c07044035903560100150350f841604003004500c6030111000079400c09500310001000403500452951410019459260156000080050304110345803030078070840314074034000f05003612020415682c50030009006ca9100143c0000e180c0d40d075510f42116000c010031036511858010903141061600d9003c1191605800c007811814408a8040451262114445d20318507800f260018403909007854100f103c1702000501d1801260f0040200780010386481c400c2e14125101500d0091a40080305d10680c00d160703e6401000c2d55100106c00c0041c180c84442c0341c19030403882510428100d0480303500469240a0364011240542d10400000b10070502207001040354841c0c0114290600c0e00c080a484c2c28049003d1007500c40c2500da4091000c4803600707804c0719004141d10f007014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 118738785 1250 118737535 118737547
    0x25030b0315010602070504110706020301060206061e010c060f021207051317190507030506071d010302030708070e18092d1c0309060e1006120807020d140d050a0212 72
    0x5d5481d03585008250150346c0b03440302c0c404045001c07019182c900d41d10020039500ea41e103504000b551101d0132925544100c01d07000c2c0b0503415040811100c41d400c001a0340c1c0898440f16502d5800103031030407000451b0003580c2008501c0160310081e404902503080d81d600c003a9990541400c40d0480440d87d04a5440c1032020310300c0100d880c41c0080c0c607070021480d814884e107001d81a81042402d054666102410304d002d500300b04500640d001c13030300c4c10a1a1390072a01032105180100114128001125200080f82e04c0c0c1c0049580c1c580501d42d80c2000d494020318416015a154500c05c0158800b5280c0002681c06040d0719910201a01500c1017005180710402c03034078026a03512117940d81100300340ca240b668100310980c00403c5c031a0f08218405a0007400034030800340c0445a207a5520381c540d003501c2c611440d141002c1200441103480560540c0c018982e5401c000c8150200000f000c1900c80894130061403d21010050030140211400060b440d00d409032104248030307001e0704140d20303407400e448205410002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 118740035 1250 118738785 118738787
    0x31101020f060411030a05030a0915030203070e0108090c0307030614070e0d030503220f0b0108071a03060301201b0a0b1501030b060d0902010e0a030b010e25030b03150106 75
    0x40b0ba58890341182e2103004800300340d00480d00b07000c0040006807079030100080d804142604001c1000031101030940d043c0e452a0075580031004c9001c00d84140c0000b5070003c01d02c035007943c8151040c0360440c0900050300d0760b0b80549070000f40740c80c00d90307030040f640241c07030700301c40030281001066243d4040f803641804031700301a0b44400911034a010200c000e091141c088089101192800e190340c901101c0d00d95070341c8e00b01e012401d00380c010190450b0211a0b0000c8800003140e5108042121411a1540b483ca056120844403542c4d110350001040c25130150750f00c140c0700f81e22408003100306207116000420242d981c10401241d16a001004d20445410380c00f0110003000a03030344101c1385030300c4640808504078413880e55004030050f080e050041a40002c4c0030840d4601030704280e002c1d81d0618804d80300c1d1112031042c0c03414001141c000b48806055000001b0040000d0581d10321344981c0102004070344200c6d04403010703010200110424400300081c0c2d030b81c000d004ac1401c04000306080020320109008da00d61401070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 118741285 1250 118740035 118740043
    0x20f1e090603010c080c0f0c06010e01180c02120a030f0c0504320d0f0b01150306090506060703050f07060204080a030e0102010207050c040c020703051e01151d0709120507031101020f 80
    0x840c251b041480000c40c0d030196025981035074640e4005809031000c2e56500d0380d400c800d042080c010000940d18601c04031155a40d584901c054003070194010f000d508402d40b0310b006154009040580526440340c191261180540c414030350700c0071440e140c10f43c40e2410302c2150b240304608110b000b00b80045918440500d16041c1c0000c2101500403220361605880c0c03441c00300d05490f10130074020116501200049104003040a004084004650f42089025a200e645100741e440c05e54403a070708042c080086071b0201e40715100500080c441e440c0c2d0300340361031240d84c0c2c0c1e030341260301c2640503030701e6608034007602000c155002e100482002e200344000c1d41044a10b48416441e0420202d50a02c220740e1401071030b002c68028029403000355000340aa90102d0502c400d03c62403881d0b40f40038031074076510b030032151480603100d1420841682d41c2054044800c10b134405117109044000360407c401c1c8107400100164403482c0340855540907114201a154003451450b0002083c0074000e0814155003101c900465030f50340000b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 118742535 1250 118741285 118741291
    0x60a0c0c05060109090c150309060506030a03050927090102040503010605041a0f01030e0318090f0103050703081c06080c100e060d05180f0607080c0406090b0304020f1e090603010c08 80
    0x132a0004103041145012400d081081c3e002100c03460b010700d42c18150607019845108a18010b0b2000d00455071b0b4801016194410b5040003404140140300003103403820007615140c11503944010108100d00340044450003010708440000c00c5030b40024040c4030600303003030140800a0400391070a0050580200d46c1070030f003010a400207809000f0b04011481c00c0c0c0e102e41c024080741c516800607030360707120307041c404202802545180003401840000c000c21466520107440604890b040009000c055045503140705480e848600c4150140d0a0b0541403403a1410078400c580041110400030100403400030148980c8800740307a144018071505c000300c070f41e0300e456123070440f51f22102c1d00b0070008041c1e4400444124602030042c100700244a980c00441c10b031900085e1050240b6680d496042c01c90f5910468080148214090b100000fa00c405040003d042c02201441e0054402860100b941482d60041240c031405d5030b50881c6200c0a2144098042c14400841508640241c000740300303810700030001400701c035409 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 118743785 1250 118742535 118742549
    0x708070f030f1502031f050a0b03070c0c1d0a0b01110c060f040e0a02130e130b070e100206071412060121020304030e0f0f010c120909020c060a0c0c050601 68
    0x30b940b0402048a403005035101011500411502c904000464040c0c90b2881c600030382d402d0b564034a01040a262503265081180c44640d41c4501d103a0b60070b2011a8209c200303080448201451034000b1558007c00c806020703025400b03041180851a005070140700f628841402c0070706000b800c0161140748140030505e81a0f0740320a441666a680c8441200909813150782e000843d00d4448009200e05c03081e50740c00804101d880c40081c0c2d0622a11030000081e24002030b1562032520070f01d030346d21000044e682d070b00c01ea510400d28140101980600004501c12040e0401c2c62001600308000304650385800054100b2904035000540c0c0c200b0048050441c0c1d0402c000d000b007410301554007240d01c008244464502d0828000001c00d645034281450701801205d0200390b041c0c0300b0008000c80c0d59003820b107148070202030b440507502d5100740c81c9a51121441e40310004510002c0004142001c40c2140c181c0c0001c00c105207000004003031518101c502c450883d109034100c4030400c0240e040071400f2030f8001035054150380751 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 118745035 1250 118743785 118743803
    0x23070801060b0d06122a090f0f0c1404030b0a060803030f07031503020105041703070f0c050109090b03100507030f060e100501051e130e09010207031716030b030109230708070f03 78
    0x8008061b10f4049099100d502d806d4240303100c2e80107802c1d107504509402c2c2030800c000d00043c00d05441c01c2d150b018900700c1820407054140820800b041da200001c540201361b41d40b0029442ea150f40c140790840e4003c40e401c0c954186450244050a6410300c5a1a25035510380070300e90203d81182d0000303199202ea84503ca41c2d10758854104a4400c00510849502c0366114440300b0806041d45880c60200c8098407480c4d000c598545000205107aa0703004955000c98018058140c02d0064901c1a00030600035280c1810960b480d800d030b0803101d0030342c03082c4d40c06401a8074400700e0038509004007000d901d03201c1c0c20403030402070213000da0300c8940c094441c641c41c02030b08800c00300c1e1242a4818108841d004a61040c0c03165955031041c005203010640c01041514000c0d9506940c7c180142c171500802882500e01e12014546004201c3e4100c0c4241c1c0710300c034207010003400862002c0b03a0b5122414440b0f001000a4001d801c08a8404a416010025800203200050286c400549005055803824038188030207451005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 118746285 1250 118745035 118745093
    0x4110913020603060a0506040303020f0c06040f0504092d0b060d11010c0510050c0307120603021302090406080706050a080f0103050a0b060d0c0e1509010323070801060b0d0612 77
    0x14807004920060b00c1b000d03000a8540b03030340e810000e5485011440d0318180b40500000c802040c14440104d8058404684080403201d15081c1800000e00503200152a807403010b517024107000e030b0088d4040580d6034040400811800c8617081c64482d0440c00380440e44684410402030001483e03c074100703113400809080c48031000c0023508056080c50400c2d11403451551401007004818544c84001c3d500070f002c260b0b03402095103050040700702141e1081c0400b0358407800b216800f0481c408641c00a01d080e00000d0800305d80c050ba5206141d00d0448aa00480042500031500c010559417092030180c1c07022032424481255407460312a2070300c1c0c903085080a006a100c0740c0001d02d0700e440f0301d2140b50380d241d8400b44d00079641d5521110100c1c80307142512814902c0e141000c140200d0324260984606a03500300810400c00544a08004011031021414607224010000005074244086c0308200003400d0ba0b49103503941d844c024007240221107139038218000c01040080540003241c0328148004041c040484002d005403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 118747535 1250 118746285 118746289
    0xe010b0f15070506040501061d100e0a0b1f0305250302070611070606031101050c0613021207060e0418030e10051b07030b090607080426030f0411091302060306 70
    0xb1040381000303006885018140010400c0c154446070481e00301134a000000404049400c4080c03205640c100d2000300300750340a00c108468000c1d015004580c2e0040011011440380128405055a02e04040051005a0349034005034140c001c040c0e22456011000003520212004d03100302021081d640c1081503400715140003040300f1988035a000c0010305019646581c2c0074a49140030b0030710b81c00b044803400f01201810100f94042c3e010b948204503404050310b501d03903c1140001c803403070080030140d83c07010100800002001040c020765000c0c058560702c54500c0483c0c0801d00c4140c603d50384041c1c414403400160040441d81c0094a4420000f088540c840041c0829208403860f004000b5401001d0100c00c3c40004092000142102100c1c81081c0c044810360303483c4441500c9140440328080401c0c201e40010f40080d401a20005c0703400701240d5003034480032400550b12646d07001100c1ea00c0c8901101014081032200d403008001c11100201c03884802c5240101c40a100f20103c580b009014400202c0810355903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 118748785 1250 118747535 118747537
    0x1c02040204030f0803070f0f0516020a03062a021b060327030702040b030102090108010509100b0f040302011701030314070816111002010605010801151707050d0e010b0f15 75
    0x10b6411034002d510b9060513041040c125030059130b404002c42e0310040c100d07402d00d004a28100c02642c01c2d03107031030381880071980030900d0300340a054040307a03c003048407c08000511540310f402c60680c04220742c40041c01948440401403500e682d4094250741c06451b0f5154800040061007842e10340c01d0ba1215101e46030b1600300d0200e951504405000520fa1034555400484000090440345000702c40a10045c0007801c1414201e2084041540c0000d00d02c00060089003850308407070f80c20244148020000c0b0341d075590f0040740742d003104c0c1c0182030069001408005560f800700750b1101e03070303460f0070703a40c81c0294510390b0040c0c1406003c80500414000102da100c0500803443c061b20490900b420584200400358034000c0c84507101c0c5003266216000041c078030005c243c0705100f58420b413070040e1150b0340140d080c2030007102c158010b402c000301080000380c18907c696229040c481d008043c0340c0c54103a121603007102050180c07210180782101d00d80c9460103031a1143c0d200662062490800d4607500c40001c4024058112 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 118750035 1250 118748785 118748789
    0xd030b040e010c0203090406210303091e050a021f08011e0f0906061107030c03030e040204030210080405010614030a080f0c06070e1c05030a0f090f06170106030b1c02040204 76
    0x340c2d480c0c00c220fa03488036000b000030035050004950030003030a84c56103401e66018036180740d120169040a0700100c000b9010703a00c11407850b0b0096080d03410a10303100c060080c0320b60166104960341e40082d1100030450510400401d02d4070500c0c50b076031400b030900c1e10004014450510441b030001c2110306106101521107640c0c1c00240150040700341c03629858502c403c0152169201e00e40c0010129118001542c41c04114041600d900c46248020399142d03450880b0f42d92656248039078000c0e030800000006a49012200350b1240d02170300c9451042c541420110b00b150210344c0311080c2c440c41440000540d980210f00c42000e154040c06007900c988526400b80e10724081d05c841c50255100d510240100eaa801ca42030054003001107800400e003200455204c507454940300c400610991081c42002c65483c01000e0100505c0c0c140c1c034149136040c0e41c40d00000c00302c0e0f116910880100d1320f0347c0c041684407401081c4c0a805003c042c2010300007898242e02080055681c0c0b00c550088640a0000004541d102d80407100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 118751285 1250 118750035 118750061
    0x80708040b0703150f06110d0f0c030f090b0a030902040c030e0c0d14070816090606051803010b1c03020f01110306010c05010b030703080406020610030201120c030b0402070b0105031209030d030b04 86
    0x5241c4415007d01017050204112503544660301d40303c42200d1244ca0014000d881594807850f034800e10756426181e040c80340f0707005410310600c080301141c1c85410f98068840100240d07008a1b4522013401071004840880700005c04150030050301242501340000c818180315401d03102c0310314140c000d081c828a001c0c082d1101020f140901030340000c001c0000a0006400d03900b80c204940c1c2c10b942c624640044624030321410011440500a051045501c4881411841c40190010a65030329640000b000d00480400d0b1450f0509119100018160304005803604410303000000c0210310358180b4125500c0c08010400ea041042c1c401d045d0007000008c1d0480300d444030010f800c0f1440e450700c1c0c1c5441c05a44d0014018180117216000008031401e001c0b49503030080b40c0d0103840d403115582050704840c0c060320415510b0400c0c507483c0c103030804158035680b00510701d00707000e4001d01145506004c201f41c200918031040c1c140c107103010300c0b2003055a80c0101c0c4096144039281800540340075188046405840c400c40b0000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 118752535 1250 118751285 118751309
    0x6010e01050f2b0207030f08060301090b070201150801090b0f04051606050304120e0a0b311a030106020606010309061107050a0c0602030a020a08031003080d0b01080708040b070315 79
    0x50320f1846410b54204100003082200c41c440d403a02c6800d02c04034000e56002800040640c18046021400b500040740c20400140020030b60804648640850003001d03603100005039540d401c1d00c101d103000441a080035000140007400301c00500c0c2c4502c058203d0142a650300584040082003c1002c1044120001403482e0152600d01d699103202808e80e42007204c0aa40258021511548180c41608a090b8500004186161640c1081d544100c40d03000501c1c42c81103200403810f07911729481c1580c02e0310700ca02d000c07142300b0000a0401c40c8083c0d1030f0880c2161134011a605000603c843c0350007203a1107238460400c0c03900040c03c4071030b82401405401110908618418001802018450041450100035020341068440300c0e542d80300403a46d03480b80c1e062010040e0808014040051f5400c0000d41c1c2111044608400da907441e82c8030301c20142e101c1c0658005440e907804001e0718558000203015805559418181e4942c036240c0c8490350b0400006210b0010944c0d220300c1075040000740305000007c1c04a070b601c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 118753785 1250 118752535 118752547
    0x15040e0405060114060301031a06060f0f031f0e01060809030403060606080901140c161104050c1e03010f0512070e0c0d05060d12050310080d05041e0503030306010e01050f 75
    0x2442d2076120a000f0032095a0300340c025000710742000d40450703040ba0790100105803c41080c0184490134440501600c2d0b000408020502e690018107000d0505081f88075082990b90420180c02c081c41e580004c2c01700d8050251035420001800000b406a0440700036080240700c6070740d92407000341584210703000100f1840c54007102181d802d5120600500c100c80c0d00000b001440b03004d81600700c00c880304403406901d0700c070104010340c8001c000e01d83c2e400e14180306041e0b034020303141444000f500741c48046801006014010031507401c01ca100000b54420002180c5d41c043c91941040c601e81e803110071500503140a00301c001001152041c1c10481c000c001c1000e9010b407116400d110300c84455917400321101103951810318010916528018158600f9944e11100f051642000b00400703648a4000510714010103c0e0385500183c0e004041c1300c404000c1c820317951420f0f600c90030114605400c402c1c040c1d40301d059841c0075106103d9518000102ea030000c1c003d007009618545143c0040350365102e03034041051456000720b60 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 118755035 1250 118753785 118753793
    0x501030b06090a090c050d02010c1202030c1002030610030e030903060403210b030309040b0d1b0905090f0d110304050a1203034205041415100207030215040e04 70
    0x2020707000d1a82196a2811611602808000e950002c50090305c10b0078181410011803405030002800d1610604000880c090f0740e45501400000850218026820002c4c4040e40d50000380154941d89800001c1103065040010101f40000400d902480034160344d229903000c0500100180c6418dd10020115141d900e09490001c1c0280400001070724041c4202c01c91003442c1086000b9040300480140080d41062403580801c0040e001c0d120741c4175000304502d4285030114a0003010080c84070750100100300349503e0200c400f0100e50000380380003005d0304200064a40b000c008118040c502c80c851401186015160890341d0851049901076a40080105000604d00c441450f4000342103029803401c200c1403201401500e584140020013440c00c07550800c400350031070101c0703d4081c0384064010f020f03001140c40d2404142200c03405c180c012110881d0380e007002404910003c0c51800a4000d035101940b980040c0c1000e551101d039800000c0c0304503810040c0550000d20141640d0027040113039004821814036042c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 118756285 1250 118755035 118755053
    0x5011b2d120324030308040f02180106051c05010b03060405040c09090c050411090603041e0f060b040501060e06040b0d09020a0303092d15021e150603010606050a0c03030f050103 78
    0x4100e44100f4a01140054810304a200001c0740d40546610800b0340e1551b0f1106400d00131040126400300c80007030301c072842040c54412680a071a80e0717100c0503550315120412a01445c5c400c0b08059403d42482d0050054103203007016a50454029200440d05858900c1d080c840301d20143c10101c1c04500d0700803d0021301c07680000b041d084440581c0c08009040c01c1c01c2c030040307152061070501500584200080380c0001d5400302011110714010075100c1c07640c034255441100800d00d5140555405441d00513044140ca403600c24503004112070b050400b00e08100c607000c210035000720b100d841d0660001007154005140b16820103c52141e00500c120440d44d00c03880c003c0c10981007801400040c104070448058014242c1002c58190130704212080c0f0014546101e190400c07204840000071402044c6144000095500000c044425070703001411030030080458082e0340410091042d8403d0b810070301e04100c1ca5801104480b1410f40a240143d20003400d1308040d0042e000e0b01c0c4800e001e8a06e414000814456000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 118757535 1250 118756285 118756301
    0x512040f080708070302061c0f020c190203100b150408070e090102040f0b0c011e0b030c06070f030e18011d07020d080703022101030c05011b2d1203 65
    0x804000094481da0919640c00e9240500080c6a001503414809807401030f0203880581c3d00c10844001811041d007c04c0243d413194400c0344c0e0391036004594500c41c4134003486113440c0800302041c001034070032994001994034030030000f001032290390310710102c0c1c100d0312030502c003800c1c810000392510b07612943c074a0425910b165a21440300c90200e603c0c08580c06003018000c0300c2c2292458120360010381d0510294010075801200b203803115650324014880d4400c0fa030005121260180c14000850850714030605003030148611915103d201d00300641d01c0098246218015059007615001c404c82c4000c1002c00d401840300305507881005101c00c00080c0744015401456040b210082142c400303500c400f035080e0ba031105060400c00104003110001100e85210b41d001c1c0c401c1402c0040c020340e411801da100c03003000c075600382c01c00d64943c2001c0e8020302c15541c010781c158400078822401d0844103a010b89840d40c0545800c040d40c020090550541710000e0782180e51000850340100d00051000c800803000760007010b541d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 118758785 1250 118757535 118757549
    0x3010e030c060108060c09040c21060905070203070f060908040e0c18011707030b01050412051c0504050a030602030a0921020706140f0c010e1501090e0d090302060c0a051204 76
    0x82002080d130b540081049401010343c6a011800d04107060704010140041c0302090702001820320841c254164507034902807051041c0b0b0000240c49040000c0d41017920700c01082c40302594000c00654001401c05080105400d0700b0034000954441d1502d40000c0030304c42c50b0b1202000381031400500c0040c0d000390004010084042d60081419401e24006407000544058500c2c04134900c8030005840314040d420910400505140c0b40703107841e484080220390841c502c00c003500c8941c003000e140f549005041184c09404801e40c00c1c01d50415142c400056241000b60100030846a000310110301410030365001142c0165100120b04a075680c020948100c800540380f59a00500c14200b0005d2424040d4030b550400c07800d030070702c10741c03070404030440b41c4080b9800044c0d030303c280b5903030350401c0f107560b81c418400d00211050341006050b00d9403420710044191907003018281002d41194010313055482c0c108005100712a0b0641d402074480040390080d1b800c064080e40c0103030a90085041d42102801c42c200140162111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 118760035 1250 118758785 118758793
    0x4091515030605060a030509070f2606010b07030c0f0204020d1a01030908030711120a020d0f0e102601080f10060e0f060a0b0f07031b0321060503010e030c 68
    0x40304000c5056038070521949420103020451881c09500c41d4014a91002050741101d034030070b580d050305140c0c0350303101c4d400718424402500c010081c9409105040d48800c540c0802070136694105094400184100940102800003400003141003202c0c08402c1e40b007064000f00210b407a0403410109201a0070850b9142440700107203102007200d9030083c0700e00181c0c0b0390421105415a0791b4902d00760344229010b20343c19114801c00c0c000300d414040390401040c030180306901a0a01c50300c0070700040e00c1d403141041d814086c00800b032910303100b5844041c00e44080401e64070b4518400c032020056010001031407c400c4251110b03c100118101000007200e404691406d0200d03000000f071001184112a034501901032900c45c01004540451443c420b055000100280038201e16039448504600136070040721802442c1401048120600d0703040414074000c0f141e80381c40d00260754019640180383d110851202030720008454014500000140d00a0002d004080c008004a86013002015a41e0300000700d2200c0d80d100b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 118761285 1250 118760035 118760069
    0x3030718120b010e0903091509010305090f030a050a030b06070f05190b010e0c12100f0b0f030f07090b04030809090a0e190201021009030c030f02070609030314040915 73
    0x8803085405803050700402c42c010141d00303101c0c101007600c1025000c40540e1105100c90103003030380c401801d40d070190151070340195900b40d00000502034a4005040000c5c0340c008450080a5031008000ca40240401d850041c0d0759400c160002d5000344003010006411070004520442004620508002d9a6024100325a591010380348880280c68510074000d202108039401045101c40a5500d19001510f07250040d0400c8070000d43d85000706411100c03240030702011703e010070070059200c5000011700240b01d1480c0c80e041c202116500355210207030100e144501541c000138001440307514003602614050781d9403591142c1d2401c1c1030311142c01182c012441000c0602c00300b100c8100d84d20800c4114081400540742a140e19801809a0b2188503000e0781580507075103042d5141071080c428016010301c20384480301050820f080040422041c1e0300c9a800b9944588014004d03542c01502500407a58189070402c2c0898898912058500550740021566410200c85645064800c100741c41a12031080100e24145 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 118762535 1250 118761285 118761299
    0xe040b0403030b030319050d020403080c06010905011401050712020c030111040906051002070501122019030504030e1014121803030f041401090f050f07060806130203041403030718 79
    0x22048000707141c210342d8442c1d5a00386c0140500042c01e01001c0241d001030400c0e9903a150554554400c50310106c00307401442c01804190a58455140034248030705000300302103040c4001070a20300c40e485000d88616147c081d8011074520030020480200703c060000e109480800401440e145c0060142d40c01c410f06003200032513941492441030702c07440c010303600800b8003501c1c01c40103407020328141c1d1307045200a03207442c081c030110107180340c0b03000550840d1a4804da4803043d6428448882e0045501e040c2014102014040841e0b4862075201c0c4040c011190301d588105203643c00c0d03030100c2c0e0315210b40750903200100c1c2184030341200d9450035100c0c64481c9030040001e5580f03440541c0705e01c42102d00b24440320382c0c00d01140c0071500ca240038515071402c91000103043d80098071642000c007410001105d003913000e030200320b805035814004400108024102101c96080510005007900511000902c620b54040006003c3c0940a88504204008a4244ca0362401c0408000740781040c010352a00d41c180c0303440c0c1c00244003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 118763785 1250 118762535 118762537
    0x10020706260414030f0a0905091806040204020307020a0f110f1212090d0204050f041509030519020a021002061e0f13020f040c0e0f030304030302030f130e040b0403030b0303 76
    0x8222809003034911665143d481900d44408401c1c40f10301807005101000300f81c1ca2410060400c0042511181c00f16880d000400280280040c00c000c0510f4110300c420408880001e032064101d80e0451300940c8075a01c03101c00302e20b07040c00620301070b050704a881001070a01c52212003610710034506407010541860300304c090021007040d010300001c40768402008071610341d400320094549044010540c8001642c0c135000102541c0c03050303441070000480c01c01808204041c0540c26441c01c1c0e4404c0050058240d51b8a000e001030040415441d000c5808040706011180700340800464558000e064071600c0d248054020343d01c01c2c1c2111f2a40c003041d00c0c0f040790001d00c98411025440b94061560701c040e10358400101b1038205404900c2280c100b1205040c0300507070381d80c034003643c10241c582d692101c205030114400c10200e000045403450003600100f0092001c6130b804001c441c1d01a0300800850381e00c1220080440381e003d81c903400040103c1801080c00704002100400a028501a0350f082c4100c0b485c001c10152a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 118765035 1250 118763785 118763837
    0xc060403121d2101050f0f3115060915090203060a08030304030c030f0507110d031103040915050604080601121506090209011d0105040504090312060305010b0909060c180f10020706 79
    0xc00070110002200c200e050300000840741c10103808239000103a0007a036416031480580044404954001440c1c06920b05c5100c1d0750000c04442d402884404000c3e4220003480559014684206800100140880d21080c000320000c0001d1400c0b0381e921f00e00390400400b5071142d40c904600082045900c28902c03440340040e12410307900300340a16003400980d01007081c0c0c100c1c02d210440030f010000c1000785540034144040c2c00100203007600803449a40f400307440d400582c6107030441c0d403103030200740310610415500140581c10740301503442c149507a90340342c1040c52646410b10360782184141000d8001c52050402d4014041d900801e1f281c0c450680f104e40d2400062414a00b0114001a000d100421031031503d40c00010ba00c500900b0704076016080e200d036240643e4510780050790284e4440d11104164141a628568031100100107000c2c5802d1040000d41248504140c00307500c0100001c94902d40d58a20700c40d41913180005019054055808402a4642119200d50700210344200c00c1034014010076031051035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 118766285 1250 118765035 118765051
    0x30702060f09070b030717042102060108030301051c1e0611070b040305210108160812030c090a0504020a03050a0507053c03040807050c060403121d2101050f 69
    0x220613401d1203449103203504018864801c000b4032a401c03891070110584094000e5000d500c130300311016403152000b81142700002d01c20b02150300c0203004005824003c81aa81075403003ca58800892242c01140c000da560007010152002032151250000c0100e001290315642d44103540a11807501e005a110800d8020a00060314404c8003000144c000ba21400051000200348180707900e60032207803003041503203000c00d810200e400c0e0300c0180c0a0135408071030540712008040742b0000b0610070440c058041414000a0a54081c1c00000724501e409540c5000b0345a003d4603000d0710454540e40700e058004c0142000340c4122101a140a0100c4d24482c07103142120406801304040150340d1790700001c0400c98210b1400e541d0200d203c1403c00e08941d040e40e00082d40078900030f00b0041c3d128101400c2060800101d5161144194400c1000700000b800f9a0030702c2420034528208402d41ca600c2607040240000c00341880340d4012007841d0441c8101e9918140c0c805d500320060020400e95803040342d40e072844030058907040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 118767535 1250 118766285 118766293
    0x3020a0227061c030822030201050604050f16080a0f0f0203060118080307110d0b071d030a030e060307090e010f0801060b090f060c010e100c030c080709150905030a08030702060f09 79
    0x3012131700402200390400c500d134010784032003c204401c0f6003109484080850041c0d4482052046a1606016481e0854408480701d042c50618404c0c28281d1003030111720754240092500003400ca44040d50020b01e400503006024882014003840308070007540200c035003501080040344160168403249045100b6103600308000c0d032424842c0c3e19031420108010320380552207140c1400e02c40c0007525003c03601b8002c03030080c3c640d40f2840354031200c20320800707900716800350003a4402c48604c400300c0c0d0b1050714111034071801c0c0c0e4010b59a0b1140e86080f0784503810b50700180d652455070f2000080600030300c1040401c4462250007044444d8403030590070074520820f09110740c452105600ca000c00d00e8500004c08da489000350000030144071101420b42040512104003283d259254403898600313805008081c5100c1e83c030b1509c110103180484004d000c801f42030140e0013500400e94031404400c0d00030952907001d040300804881c0c070900c051821000700e902c2251204e005010f40e00c0822a004a040e07000f41c001c1c18420007030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 118768785 1250 118767535 118767589
    0x606020d080c0301180219050703081602070b030703090209041b17071401020709051509060102011e0b030f0f030711060304050d1209060509070302031902060405090403020a022706 79
    0x43c01400b0105c6029058944c2003202d64001c0d0550030300410f05018503280d440e01d4500506000d80758407001440c0e070320070140980f98125480e50224201d0300f0303140c400d503ca0f904c135160000300b01c0003400c3d2158000d4028a15205200620507492a0a10068030f06200682d0300c58a5041314a03180350b448085600d550f0000c0c00600441c451440c2880340e0100610459214603070f50320304101900d4055604c1e050598183d500e410407814601011a40a8020300080c00307064034400d01944080d1003400c90004055541c000400c041d6000d1140000d0342041000300c4000a15100c8070907141e50014070125920011103940312040d08003002a03911841c0c0000c040d01c08400003002c15521581d003c3d000c581c406d9641e203d42e40001c1d40502c03a0714003030180325009007940760851050600c0c0001c0d84800b203410f110600c40d1140103940d00c2040724180d070000e45034511a80c4880c5402e0380307041c1c086540254032060020f80d185501c1c12031481d4010b03107248200100b082e91030328010700c41c4030f0540c8054443d03141c880e80b03a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 118770035 1250 118768785 118768799
    0xa06050a230105120f030d020703090b03010b030406092108060f03070335041409010807180207140303190b010903080304030e0a0b0a02010f050a0e2a04050a0606020d080c0301 77
    0x64602d500130454180ca00f500250380101c0d003141d00c030101c910302a50380802e4030820305074000c0f030100c090803401c801c4600d50f5040c40707101012404001d000900c15911462084100002001c030010181d07501c0c41c00310210b0000704c101a018110803a8004c3c0070b5080d1102010040ca03000170140100ea400c1451005184209100c00752108400e4041c134008200c5001a61a41910301c00100300511000c0ca04010341c051440c10405010300c1a840008998000c841c18080950100440d85034042890300040c0d51f6087d501e03140e2aa111040c00c01e5a01d400301201300055001c041076541c040740d4404108200c08100307a001910b611a00c0c0c080500700b4402800000c00103405003400b040d5180005100c04145a0f50704040301e110380c0801d90b0740c001070351203460018a1114500480ea0810030b0b9000502400d410b04004590703680700280d40d07202d020046898000e1030010500780d800700440c00342c401e124601d40600d012025003c4ca110707020042c49000108003480384078250060180e5035038442e042c6140d10300a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 118771285 1250 118770035 118770049
    0x40b0103080703031b0f0201050f010608070f2601150206040f0803091e010f15140418080d0b09060f010c0303150e040605100b0403080706020f0702030a06050a230105 73
    0x14120b0070b15660f045000300820741e42c2c085c41c0303031191242c0e2402c0c0e0034000c0340d50080c255a4090130703080c0d410802d6001030007025041080300360300c0b00c1c1c50f14126030305e181c07034203012220042e0401c4507a08681200d4582c0d8600d40c901d141c0c03e4141d0703202c113584080e204d443e0701080780e5801c402c803005441030328081417400005660500542e040b50503241204c4c0c2c00504103a800309211800c421460140e07656060702a0083c03114001c28000741020300c00e9070413040c40c01c500ca02e904591002014400d40d03407404207142742c008130240c000c24550840700352629002d0341c4d804ac10080034280340fa50701c078150041c0010303854900b40313500b250403e0040c1c0d101c408031300c101e550550151541345008040d907100d641d4040390507082c500c1840c2c031884c080e14000c40c0c14107205664a00c0804250046440450104800d20104900b501200c0149620140041c0c0d6502c84800c1022280100c0f00c00a60500030008544140030241c1c100341d0180020036800c010401e600041c00308511100103107c0079212302c4400402ca40d291500c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 118772535 1250 118771285 118771297
    0x7020c010e060c1e0f010e10150e040303150f0b0d050402010509060a020615090402010807120f0c120515030c0f03030c070f15051317330906040b010308 67
    0xd0180e50410441d034600038113084a500700800c83e02560400b80410138401c001120000c11032200800c100c10003c0c41c02602d40155414900319161a0100c00244406c0c3c1c0006000414035400c2c40090b03400c20785070007000b0313000c00516415001a01e94003c101c0035401628070082301e900300d043c285040074a2640c0300c0030f404010001d034103021041c00b400c1c540381c45540050001454580c090003451070034075112481d0260401e0b085004201e0b440070080148d0300044116017203115418010001500e8803031030000f800850342080d41e528204040034030340c55000000500d04091070001403080c1d5540c03030f400d0000b8091000b185a815071212035451010b040041c444421414003a0a8030300e000400c0741c0c102c0c60804298810520b4070414030080042c500d4412412001169a1402c54a030a07030f600e1b00d110140c102c0e4000c1d80e2442c039080c203281601040c00c224002c041d155802c42d0030000214402040d81e000690b883c0c0d442403140c0c00c40083d10565001c0f42c2c2c9480b0710b61181341001d2507421902ca065042e0084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 118773785 1250 118772535 118772539
    0x9091406012703082b050c03130c08070312110a171c02030f19020703020303010611030717030612121615060e01140303030907031203020d020c0303010305070e07020c010e 75
    0x200c04004145101c0081c0900c01d200800d10000341c4118680c10f1854045d07400101c041468001440303e180428021a60080880907440b4818507042c140a0248102c0e5441130a4a101d98800001003001c0340c100c000c901403054584105450304120240d49800b9041c0f0004c088070250708040d0700c0c600010010742500804c2c500c0042030301d0b01840a0008030380c0261464200c68600f41c0804c40001306088040b03103101c02980d002c3d4100061035801035685d0006009034070600003284812206400100141d6038220740000d5130745008900d01403c0640c40e4001d03698540241070080c400d103c4440c0c00109142c00345810003009160280a110000300031603680400c661380c0f911178201c10020703946400341d140503281e17980e1035000c59454900300d00c91400381c0201090190300140f040044480c404100101229081114138882100b0058101e0082c856064052011880403035041502c035800805113068038880c1e000c4854403070f1200c4070755510100c100d0300d10006034411140818194030034243c1031421140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 118775035 1250 118773785 118773857
    0x20103050a0f021605061b07020f0609100909180c03060510030c090609050f06100804320f152a0c0307020a050f150711030d0909140601 60
    0x2842c4814207aa000c403500c004680c0800c030032030051080c180041500141d00f098501140e416006000d0020f004044002c0e00c0b4a1b4419210f04864680c8011102c0200c001002144003858140014000703040d6800384490030761501d4262100340381507500100c212600b00c000248480d00c2d568038800540b00080c18042c5000200d1000800a45920411806810803590214840d030501c1044022102c000b0010610010800244403180e20760148844000d0034074a440c02c8103648604081ca0a00d1403031100c2e154608000704800420403071081207894607030250003500d040603106000703280e4818218101010075030090f03002c04c8180d5400c0c110743c002005102100f602c1d00c0b403c1e180300c1e11140c1218082030a29007000420808515040d070500340500011120706480e52208400314850010102620030f0b0040000364241c14800000d81d41c10f5071560060840f9400003607164018412410342c480d4804150400b88103141400300f40520b0391048006a40340d003070140801045a0503d03450042e10094000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 118776285 1250 118775035 118775051
    0xa1413060302090f160c02010906030b031213030507050d0209130c1a0a020f07081b120609011b020303280e0601270e0a0807080c01020301080c0f0108070804020103050a 74
    0x40f8102070b10302c51031848086142c64640403e04105048048507210100144851802c0050380c00c0b1400a056a1444c58000b86152035680847e18000b1604800e56540c640401d2040c0220401c00420007036910450661301c04603501c0003031107900e24107060000e50205000d00000c80c0103a80c3c0c00c0025000b070081ca005c203100c956448400e41030b04201000c45c00310103000581c0241c065010008042c030040c01d0002401201d10f092500f41d21041e0320709403800801000c01c1c904015541d41c50000e02c004820106440050419a140720300900742d8610940d100c5001006041c00b090020051340d124200140030340d100d4022514002c101410308010714105107a950b02c450429000800600317010b031001a02120f00c04803c403202510171000319290304541c50134642c000e0ba4041c00071400462096210b0440380d1140720504e4024100d0085c1404580c4961010000003008a0001185020940c4c19515030110031914001128444801c58030800030403a002c000c200194425402035500045802c00000c0c400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 118777535 1250 118776285 118776289
    0x213020a020c0907050901021c0507020301020f0c0105010f0e01030803040f0609050f07050406060212090103061518050609091306020904090807020a0902041214070306060e040c050a1413060302 85
    0x180200e144040164007400102c0c54904003899400d070030500500f4100e00306a45280003c5d0343c1c42c18601c14602644c03980c24808103071400b800c00d40e4400381d070080007992115410390401081e900300f50950542c0b50b00f81400050b103800304948440994030f02c051000d89581c01d40d150009650720151085034070381400100e85000c00d003248101410702e803003580a0052400506100c6140c11802d401c054803840c41d110b800c1005d1500080c0840c2e02c07140b03c288850700e07007031004016001031482c0e80c0030785407804500c411602c0e40c50340720001901c40142c2c1e000070a0501c0d120f00c24415a4000c41080d15000ba0304c1034041070305016413060200b0001d110391800740c03910303c580c00170609551115404a60306200861b8030421441e1001561000d0401032504600305072811041c4820004c6800c2d02800340443e01e84142889102400000065500080c0501199507107444da0042c0d00400ca600340c440c8c4a581c1004a000d24000150b601169401c0742c000c6600d40c10b1404003c2a1601c1c44103003d41035640d09000001a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 118778785 1250 118777535 118777537
    0x60548070807020f0f010f0e0d06090c09050a27060e030d02040303030b0d120f05120c04050f150a050d090b09010203040203060a06061e022d0c04050f13021302 70
    0x15485000c1d201c1d00c0c0c0d0000d1040c805008200c0b0f0056120707900c0e1084032400c0d640d01503490190028145042c1d07130204c108101160020841c0c0078003a103064280042c030000d20044196031021541120010004c0380d0b2182190f50440c0c0351002e0304007440500d80c00384221002d040ca1121403580c0240c5e030018062002d250010302d075502a00340c02200c5c5802041c10418160180702d142440389050f80c0c4500400200c3e034601812080c1480700038107010301c3c070020541c19071145064a600c0320f024034a000d09814410101900341e0081d101e040e114107800b01d03032188076081c806c54058001203204849130510202400c261407075044000e6580070580e9400360040861400480b09003d4450f240006a0b6410540145810301e40c00804800e4450305280707041164540c00040185009000d444020003940303a400100d00309044da80d404410405032007401c003051100f100005003160812000c48501c0d41c864020b00050714800c440c0940004ca080002800c41200a0b112084662008201d416030045c0600300e10b040b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 118780035 1250 118778785 118778797
    0x13020a03180b01061202033d0915050105070c0509090f0a0b0103030e030316060207030c05061f06090f0902070809060310050414060f01030b01021603030c060548 71
    0x20345241600400030b558200356541760880030030800754958a01034240c1400c080c1400b001c0b080c0800d103900c807141c890090081c030001800000414609250303840c01e68001034610780d80c1c00d02e426900c018000a8035800380d412504001d92141415401510708410048000001420100580a01d200942c503403803052020004652180160000c10350450400412100c0001c080b14000e503c20440d40907540440805100903650184001d0394a400358a0122940046040001c1c1540308100c107020b4484c071007041a00050b07029480910034280d64880031079400c4c466103d020300c850b4a000c4c0500800f42c2e180c000f070007031740d00038025185410080c0000c1201640b044621840017119840c0c18002440c1601801c40440c01c01450010241403440014280d0222041c04605040d81d403010100580d000344052455411000781590080e0b031790341805800d56108450031135071a4a0040000c144000312400308800148000c1074405c050300c0c1d907480011030803184600c078a442405103440308001e1181c2006001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 118781285 1250 118780035 118780043
    0x5030c0129191a040e0108010e1009170a030212060a061b0602040f0e010807120803012304050a0c02100e12072f0f1806040c03020903191208010513020a0318 69
    0x103515803510050502181341a00661112390404400d100155000280901c40c2d038034217400014000b10038a003510300b400406040c046415070224a46445941541c041c003034075411101c0303040340f603554070b070412600c14458050321020a44411801078503c0080c620400d007944141001131410340c0f104c0303100100400301d41c4600412556031005120a03030341484294001c204150522110b4000e80d5207045580c01705024410346609002c88034403d182c0d01d040314000c2464050003c01003810300c480000e000c0c0151010500161180e94103ea100b201d03144038610f403141000000d80207042d880240d00f00380e648440426115014185501402c421820625042d5045c0758401c844d103003214407061024420010741071511070180e50200400380c9000203841365002c2c004507400114010786d020190000c2c010b0031151605071040e485a800303801d0700103503040b171880c0c0162400d000d088140c03401103032002e009010340d9800094280003090b030b0204640261071408074a0402242d80d0703e103403000080d056101c41082d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 118782535 1250 118781285 118781287
    0x30c0303020d0903110105070204021b01051b03090d0509010216060503072615030a0f1103120a020a0f0c03050a03020a0b06030c06090f0d0c0305030c0129191a 70
    0x10540c04200306250070b1440c0c01d0001c0c505146484416504845280c6141030000003d4072100b1555554101c6901c841d0f45100d440c02420100403250082400300e4000c030360b00c0046812032000d142c4590035640700c1d48250008202c00360000208464907009014014194030422031680007140e49a501840940035550715103842c1e01e00810000c0144007220904841c021801201042240903203001a034804410b940100c404078200f00802d141041c030f2a80601091100c0f2440c104000c0610b514a0304014210304480300604455049403071442000614400b60b4800c92a2000040410f00f0b48040c030360240319591892540c86c4c50329801c00943e030700c04030010f070001280c820410201c6da0000350406000d4008081403480c00003c90b0241c1b24004078072b8812030960040302501d1b1303100c0640c0c0080d954070081c0c600b03546940380b6003075903650010b000100e100e5003010f031650080c15603405036140c5440808038060f030013007e5505101d0740700c1840c907007600c00f0880702c9004103080c0360604245c864515010941 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 118783785 1250 118782535 118782539
    0xb0702030d08150f01050d1122060903030c0602041502060901060e160c23031305010e090f06010201110a05120c1905030a0222030b070e031e120301030c 67
    0x1504040e10010307a542070100000901c0400422100c1144615009031070718000301103508010303129070065820300d0801c50704003280c01c0b0402c112003006d8124908a102d4400c0303041080144808680510301a500008420b004104082440780902170a0240124001071509480300403008161081d04a44409680a0018000400406d00c105c0e0010450341b80044420300308429020034403503550200c00200200c20700c0c240d00b03203c4e204402d030045401301e8124100c0c100c5220740454490300501c0e034a4810301c1450200044075405011003541c2080003d03c0451241e540c0502d50268000240c00b05045669a07181c03005181034980050101030a16107945440300a0100c40d40117400c40184902c245100070322415031001e18540701c5043c8082203045c19a203035514000544001d0007140ca142c81d6000c00261480100d554600c0061b080d0303070248030300800c555944c1800741d985000c1e000009800d58401c0c131003101205006540d000034090b8802c1907440191701c2c060036600c903800030303041039900c0b50503280c0c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 118785035 1250 118783785 118783789
    0x310803041407030302060109020a1e020609100e03070f03030e0a0c080d05090f04090f0f0b010608072c030c0a180506031603061802030303072003070c09090f0c0b0702 73
    0x3007210303440c95440040441a04603a0020344610301882045201030700400d01624042c0600c90800601e1100d20104508402080c2c0003990b5031420354162546004000c010a0760f10080c3c050700d014010503200561808400d5691080390b0355a01409804140d03559034044d4803040d041c01900e102c00d024116101c0b43e54100082d660400c4218a1a80d050200c20451641142c0322502d81080c00c00c003c80d0005a0b500b0107042c0002000094a0010301c008a4101420200a084101c2e03e060380c2c0180d5644a096441074816543c0c152390703040350381140040c4206081500a0020074044142001c1d003982e044c07540690200307180e020960030400c200c516840c0f20058480386032094640c401d00407801071028202f0081181c0503054940805851301c0c0c0c9031104005c08c50b05400302c81e8000c0394050116035603490311a100414004040542e0007071135078007001100400da0700105407107107550006031382280342e0315046440004250b424021590188010000d101042042032901c004050b440170265881d01c0070300c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 118786285 1250 118785035 118785053
    0xb0907031205181203070f2109050303070f150c0207050405070e0a0314031213020405010506090604090e010605030f0f07091b030c0e0a2d060831080304 67
    0x5a8001049018440c22405058210785103081450550790313805a540c0c00e210507821881080c1e00070b0003e1000c00406010804009810341180109408013040138450303d204480004252140c917138180e1052003070001154246c180d8255492080c40030064500d140b0071030b80107490030300f601c800150700000e90800c05421b16000c1d00d940021a0300c0c19020a404c0c0c0ea001400088460001400403110b18000c900011010012103046011074801d054540c988240c032140c4c04e400c0c60300c0481c00342d820600006030605000081d22034021004144074146070070304210500038080d500921403c0d6484002c006a2510140300300d12405200402800b0418400414a440d14460758000e949081c500240703110003e884103400d00c400c203550700c0d002c1580080d90300c084070b11009403c0e0940d40140d088000065040c0b01854100e103481e11600b00002e0700d0040000303840044110f104000124918500054400c0407a10041c66000c1f034004e000090035814107040144510800320494840b5030001c01d020500440c0e070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 118787535 1250 118786285 118786313
    0xe13060507051e0c070b130b0301180b0108010b0d0902030120070309060806010e0409050102070b010b0301090f020c030403030813060f0209120c03070306020a0e0301050a0c0f110a08090109030b090703 88
    0x290055203000440f13042e03280d580300d01d403181e08903043c0d01290b040b0001190380c901138011b052046451f03840f542c55550f40480000c10280c0010460f10b0101e485140e0350103100398504a41102d0422800d01c654014514043c03c0088001c9034555a01e24020600b8140c92814000d0500f2004034161201030624000e004009240c12210500c00c130582080b58680e403020703413140e2420050320049000d054900e0090301a029818000307100074640c41c00401d8006548000c0c504079101c4220501005041c06a220100e01c42c64120441c66041000140082170040061a4001c16442c6554003484a1a100c110442d00c000c8085c5c04083d80000b0080e0092500014907012540d01002902c03940305d215000a580c1c100e0707440018045600441c14020042c0031302c00380c01a4900107030090010746011036000f801040303e00d034041c0101c0d0303106020041032803041c0020b0545805901c0103020490154440740b10076000b59000c28104900020b01000150302c08403500c1c000c01140d002024044c0c19850101d00d078000003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 118788785 1250 118787535 118787587
    0x30606011103040909060204050616020102060a022d040b160201180602061b1e1e0306060a111c0e0306010911120a090c081b09010b040e1306050705 65
    0x700c210301401400402120100c03030002d0000078484007507107042000385c060780d40403d0b07110354040b071216800343c0b100700e00c80d039041e10076400e98280f0343d9207600340310032800b4945260640080780c4440100100b85e00c54a50140c104004a19081958403020505c46900240b01d0102c40480400340c50110b5803c54010700b802c09250079506045e6003030001c004c3d035400f001490402015401d0076a0400c0e06d003138100701c600c82001c40e00c000b61418840880b8007103d03070080309800d86517031000850f01401c507104400c0d2030007250000e01032407410f40d00002c202c450a000391020310907809408801d1004114940d658803a0840603140d286042e12460205818441d05034400355140341072900e5907a03850035003803c031540402c41d018040c1d01501e41c200d551009140741200284610704d0601c000c10080b10024082c800d460b0b480030040400d0200c41c0601c014107500788191054948140700620601c00f810070819806402107052851405084e00e0701d81c140c030030544040d00030075000114010402d00c5022840819880c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 118790035 1250 118788785 118788797
    0xd050c010c0807080c030402040e061f140607080f0f030f01080c0f0f0409030203090622120c03020f010c0605010b1b07030c1e0b040807060e032d1906050603060601 72
    0x1040024100304c10052040c403a41c6400000103086550355030022518001c1c00003221254640b50340d2000400c04240c0c90000401d4110000043c2c000310a18412403441c0042c004605002e85c650303c002460b000020040100c0c0300a10007090101d00510140d03100752904005002c495252070038907814541c9105403e4000c0c84850710b46800b546910290480e10740083d9000513541c50b140c1801ca0440c080c0b808650360001c0001815142c80411049544035422030164100155603141b0400d07546848503800200303e407100000400c003506d0030559681400906040c8014140529600c0d0821034800740c01104200d9800318480010343c44406103030b024800c0304e90003030180c1421500d074007503400e0940c420504140c02c0b084110745032010040b000e40c010b10360044007076102e903140e581345522090503010b0400082e82501c0d091b405440c0000c2d062203140303503058403c0c004003960b510082c148500180385044a00c5980724004000503441c1032100c2c0240100300020307550030040101418000050411810061 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 118791285 1250 118790035 118790041
    0xc08010608100311180a060f080a0b0a050705070f1b090608031204020103110c010b09130809010e040b121e0a020108070806030c0d0803070801061803030c0507080d050c010c08 77
    0x540181c50307415280c00c210321200580c56134001410350810100040031104007507007402510f16403030b0040000d03680f5060300b115280b5100c9110b107503030344420b84000d40906e41003401306006064a0744040e400800764980300d4500f100b0390302e84005007009803c0c200c8010070b00300c588a51108a44810002600c2041030500040c0d16051590755280500b0841c0742d42c1161244c00700e811a0300070390040c1c412036031a0a841d511407101d0b002d075600030301c0030b20484c07401080103c00240d115642c0c00040c201d91a408070f580c42c20f1400850046440401c40c400320b5401a40e58003e8184c0740d51600040200d1841c41c00043c001022606c080140d5203182403030907055a8007885040380141c2e00801134a40c82500ea280110f540e5861100081c038148100c080a074120811016a00c03c3c013040000844c401c5119032505141a6a50141120060100201c013240350a4050080c00003074440c0b00003072011802101116007694541c103c40c0d05002d2041030590100d80000742e00c2c1040c140030f020b44908801541045035582c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 118792535 1250 118791285 118791301
    0xf0609031602060306180906010602010f09032a020901080c04062c070302130e09060f1611030f040b07150c0206060f030109050601151b0c0b03091905010c08010608 72
    0x301400d40003e20a01d00400060025165013040d0441c0001d60550000e141c1040c00000781c0343c240a00a5500650921035413184441c0c1c0d40c01010083e65055940707071480c071a111105142c000b150740c800c0401119440f41f0358050b81c5d92241517406000254050b01c5007140b0603003044222850b80e407014181000c0f840b03000302c0d1080096804800b4410001d03150300e030707a50b0740715049000b442800e2203440351f03811080000c101c1c0c4125002c66807003102e09070101e0300d2075110f034a0600c0e00e803441200d11941062550980403081446209401710040481c01104d00b4145200010300790307a00950003100014401113a003606020980c0c4154440a50740d10040022000600c0025101d0348010600b9000d601a024000020744007580f10610403078110061b16070b10b5840752080d21581200e4001c04001078140c08645240e404d06900e03d13603060364440c40c1403c05d24548130007000c0c0e640004020110740e02450740000000154600c486074464803807800001d6a124001011b80380280c180c00040030000104200040c1c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 118793785 1250 118792535 118792567
    0x60922090c051011070303030e0f0708100f181101020c031507090605030f01060305060d050d0c06050a021c090c05030609071a04080c0d14011406090c03040206071b030c080f060903 79
    0x184c0d03014032380840d0b440401058030745001d025001e078550600c034041e00003820620204240000a4011405102044001016005a92000c120620000107400300c0d000080e0b00c1e141b5a0a4208043c01591090ba207003200003414048548024a5040b00070030800c07c1c0b00340c0c0032030000302914150a1290030340c1009810540700d44014080c00b018190740d480400c0c0c0b0366540c8044001e0a990240445450744e0b880e010050680c420080c0c11600309083c000804d201009034002c5c0e0b41e01c40317003142030b441c51780200150020242111520541da1568112004503c07901c0522480e40300700380030030003000e90303e103082c20004140302c0d07880008440003c10301c028004d041010440f4107404500310b40c100504c82c0241000e084803810094035400a40c6401e6841404049400469206a40443d00c003031695032050018401d03071104407402980000100844800030b040d03400010000450049114002c0b0746940d6561440080c0d500076040700e91010200040c1e10004014040e408a01070014504006010f0040081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 118795035 1250 118793785 118793789
    0xb04051212070f020316090b1333090212011703030103021809011418150f0f0910090f0b070e0303030109020703020f0724020309060922090c05101107 66
    0x1030124440d000c9042d0b550800034100c51b041072034406035000390303174000f800024603c181c6401d003e10190034449400c06440c0c85086541c802080203100d2642150100b0101c403000e81017841c0c4001415240460b2080140c0301504d06070390726810b07403030040d414040d0002030040703410503a4005610800c0140b0050700c1d01015500417502e00480e01c01240c5440c10514050408201c69108030544042041510710401d418522821500020340c0e0000980307030b01c000301100e01180e40c008005010404644861501c0790425482210b040560300303800340d002d06903000d89459207000d03115460310100c82c00600c00c40ca910281c014050742030050780b040800c0c0c0401e440e800f051188508060b804958141414005d0000301d1000b00900243c620341516180440341008545208a203401921070b1420202070002089401346031000304070605001c10303d0201700c0400002d641d42c03814000700d00300c003500359202402885900c2c0d120f401a2207510b0f0a11090024040c2c1c61002d060030444000d04a0a44d000d0106030881 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 118796285 1250 118795035 118795043
    0x21801080a020714011e05010b03060d080c0a0b04031b03020c0103180f050f0d021605040b120a200a181a0d0b0108120f0a0806010201060902040b0405121207 69
    0x1032565070310305005000f4041d01c2009400240031401d801c10498040d803002c064510304080d41c3c9450310900d40c42004442c001d000b4514454800c00226050703103003003200c1041551151821514020542c3c10b9141803901d410350480ea08446c210034002055003003a040800c02780f00c2003031858203081c561002540c0c0c0140028840c1815580c00030701c8180d106940c11706050300d4200e40310300d071440111f1610951711411030f441140385004408800c800a03202003640c407800e8030400000c2540c28141b03000c00c0001d01c00360007201da0260a00c086010500c405001943c0703094001c61110707052412261500c40e030791841e40e0207113100300003806040c0078500540c0c2c0907002010b00301c140052050103081d000180e81c03031582d0b116540401c1400e50002009030318160b02d4140d8582109540c10880d04400424036030250003000400006e0a01102001c54403c0d0301d040e0740010140b0000c5150381c0d03143c1c0c0c0c0000b241e10980003034034081070004d428001c600304410b0100d04100414000d0003490620b5030b040c0280d001d4590020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 118797535 1250 118796285 118796297
    0x110c07061701060f0507021306080a051b0102010603051e030403060c030903020c0603010501320c0a060608061006030c090f0b090916050415090e0a02030601170105010f03020d0905030706020a12021801 88
    0x102507415684c489c50140c1404004c982e5041294140540d4400b0784c0c40c40c1e43e06000300200000640d502c10f00030031040b2507001d0014003003003a00c160001e10b00003c1c084103034080e02c4240030001c00b04425000c1c010444182d0707200081c440101e8107000703090401600183d80541001c00c0104020390340700b180c040c40480191280ca00000b1800898841703c0900801070302d0044010500c001707004004100c0f1800548601002c0010664400800c0c0c1c5a43c03003106c0803100390075a00401c2082600070703000740104100928082102d540c8030005134030150459040b0a03003040c0c01141000781410011030b01600024500c0b4100069580f107103004140303100314007840d002110341007035449566000e015284080d04c20b021402d8031620303160391080000e40044400b540011450200004600070b4030014034182c40060b9203c883e8841d440c0c0c0107502075030112243d004440e649480d0f520104000780064105139120b554090ba58000c0b0762001403050b00200c20241d080b500c100140e5928074030000340c81c1e031481c0083c2010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 118798785 1250 118797535 118797559
    0x60e010614070206030c041806030804051017070e01020d0305010e0103060c09080d08040606050105090f060c0a02090103080304060b06030108030a08130204090b0a05070e03070306110c07061701060f050702 90
    0x1a0800b8051800b009400810200a000c641c0400002800c25900c60418001522900d0b050820941d01036100142541d00100018000f84c01c003603c03040d90040b280c0c00c14000c4d000300380b11006200c070012a120000600101000403039980d040c800001030885500d014411541081078110943c0c1041c80300401c0c0695801c0000f8000340100c42d1103000b05942015100781d4004040d01400e4400111001c60b035040c6049004074103507000741c003600c8050401400010484240c881401920303446070645442e20311402e507481c001a6165901d0a018522902c145a12130a151901e4030030344d0117034aa03080c40340c1402d000500503c5000016601c0352101c2d8a804070003521122540c030211104244065040340c03d20308003a051094002d0000c3c02005014001c10a1343d4550100716540c4080c001c12547c150400701081010403155000800d004002c20583e61407e840299990710740109944688003044004a100b00d540c5240541103006100700d0030f161038081d2048000901031310554000900c1510918a9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 118800035 1250 118798785 118798817
    0x201170403021c0807020c06040303080403030e0106090e010e01060806041e110901090b0112201809070c03030b0316031b0314010207050c040b0f150d05040b19060e0106 74
    0x15541505200c0300300380b0000f500214001d00d48481202e800d005071044020f11410350400c00126003c4a0f007680d60000f85444a940403030180c2003424072210a59203e01c00400c468000380310f4010342c4252140001a1060354000c0a800d60b1441e910000a5801113000c11020805980c13805074007100f654042a5944214544030030007e9540e0038240e04650480c00119010265500402d1006405d03210100c0700f0004243e41c0701a146440c1320711070a209880e1040f0410003078400a444c440380c0ca0b410700161505241d000c680c1d1130030129010700c0082c1d00403480c1014160144500240c000080d0060802d503460002d50000d0034066200c02030500001c54402444100304408040180d076003c20000040c04107018070314083c0d00f002c4810341d503600074440c0d8600030346001e1242206c5040050301c0b51580a0b0480c1c2001061184111034054140c810003c28010324042d12840e0311441c0309a61900300360034890400900c814800f03038030300c0c6a03915205081c002d1001c003189480c11260545001d030750081402c45 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 118801285 1250 118800035 118800043
    0x30201020d140c12070605090c03030d09030203040305190b0c090f010e19030302030c07060201051308071e1b09050405060a050c040b030c0c010507020a031e091508091603020117040302 81
    0xf4040700e01032081c2c10680c4080c03880c01004401e0003081c2c24000b54507880040c0ea124401c2540c81036055000b0440c0a00f014000d400c508003440c044c4c0192401c05960b62a06403c150318040d0002c00089445011000c02000202c010f0308858401061410030390001c010032002c507190404541400721040b0b1051495803103503281108150a09000401d890b070360304d07020b9540e40005003441e000340a000c5000c514140705120705440303506084512450300300940c80b04030460380306d40d80507200c5168a0000350b00d10001d42c407001e1291445660b0301170299107042080441c1240c0c5401480c0d0250411040c007010800008656401c02d000324400115515420440c0c5410302c21580441c2880c400402000949000c41d00038003045800a0002d0000d070303031018402ca0721070710607800007070208100c00b0f00e42d01040d00380100002220034506050688648030303009051a101002c10034800101450200112003005120b010f02c8a090720680701c9445045034006040441494107072580c11101000050a00d0320801c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 118802535 1250 118801285 118801297
    0x21080d06080a1518050c12030412050304060f1d0906010306090903022a010909150513020306030106090b10050d0f021303030e0a031104020c0c040f021c020301030201020d14 76
    0x250449a450b801c07494421034a021103944100304916200400d41d51030211030941c0d200c558000040c090f01d1803100108443c04c07010b0501604580310a010100b21145008400da484500440065440b20300c1c1c21402001d02c80d05034601020441600d00207201c0f40040da401040d1004101d038050038954031100101d006060540c40300186500b0302b03a01c0c1d41032580100b800039040d6650b040c400904281e0f00c499042d003c201d0240b0350300084040104200c20000d550103a55082044007800d10580e80c0c03640000c80030003ca2004c880d060350700209010641c6004d00c2060018131001d9814010b8422080000e4140740600318a42d0a01070001030b1140c00146980c0141114654041b0443d124031701482400280c10a6010460204000c107800e030300b103498164041d00071a80d01600720004c5035100c0040c0000381d000b5111044152103041d100903415940e038050b4440b521509500148c80b107443d002c00819000c489d903408203189104100500260344c3c04a000301d500c508074205a8180c06084190b5a502d00c240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 118803785 1250 118802535 118802549
    0x40b030c0406060e09090f190302010e0d031a030705010906050703050702180f09060c0702040924050a0c031103060402030c040e09010b010e0102030c15060406030506010909050721080d06 82
    0x2146011500f20b401c4541801404400d9404000e5642c0380c000c4160390b0390310210001c1c001d9001110611a21450030b80c40200c19102e403001107007440e400c0040c4da1070044924022004203840380d400b031410700345007007081341c08240880003403490320b25180018100303043e00d015600801038005541e4060600030022181c4441d40907208442c001010100351100c844203540700c1311660741d4a4003094248034000b481f20b0007000343e54891072920a150342003000400e18400c0c00c566504c0790300c841d400814521600c0710000940a40c0201ba01e00c0c285071000201c031800c0c441a800d03d0720b40350303694500203000800c0c1d0360b0005050303400503039a4449102d10348a83c020741d0f004140140c880c40400540d8501034002000c0c00c0820780702c419140080000598580c05281140c802e69031210110140e0350300042003407604003e0203080003d50640300d40702c950034132000f40c006100d810385541035101000003c103c1e0b08001c091345580d1400d42100070b910b804400440d40b03000b801d684808074500c0e01c3c0c60a558041001003001c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 118805035 1250 118803785 118803791
    0x40317040b240d060c030608071a1803010e060702071e0e07090302030d0918020304020907030b04111b0709020408070608040302010b10030515031606030207050a020418050d0e0f040b030c04 83
    0x30786403100240580705c0c0c1031000039091540000742d5001c0041d80b81e0544200b1034180c81461117407030844e5615007040300e148080011488103501c00361020b1007613040d840001c1d00a44510f16016030301030324101260b4010121410001e40c00c004044003945500255a15160010800c2d105e92104507981d418a800180d498010510f00a102e80d420080c1042250f00c035442e061072300c41102041c481280401c40740a034015040000003005035120b0b50002862840040c40016065140120312a071078011071104546180090280a100e20381000640024042c02c01d09501c0c0c50700f0540a181c90b0181031180320309000301d0a021404040c000c1d00000380c203600143c1405007a9a5400f001805801c041e2030a081e1030041501030543c0b410082050f0407060880b0801020b11031078413070110002e40c8084c030182d031f4a0164071102c1005070303114042e0b400032850001c0038064426641c10304a05000b494010101440251040002640c035440664011aa021203000800c401c1690221b8103002c00c2207005684985 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 118806285 1250 118805035 118805059
    0x203042d031b0807061803260c030d110c0304051c02030a03270308040b0d060801061203080a0902010801030b1f06050d0605010509030705060c0f060f040317040b24 72
    0x14030495000c049075103c004036407a4a64818055400c0c04ca82d0146140c13200c00302a05201142d0100c0d2115480908108a481c3d120500012880380350400141219030fa0400540d04000d040c1c40e0084071840b1203600c854910381a403244045a40e0300c034074491203000e000384403085042c0090751a01107c1c46030700a000d8940402051900a10103800c3c00480510784030000c0c600b003818596480d140c810380b40e014030300c1458141840d1105010f80c0201c0e5030a00020f0300e40901080c0c00c41c003801200003c000c0802c105841c18614030f40540b071a0402060880183d10b4251942d002d07030b81c04041d0a04483c1c00c0400f01905032500c800c40301c0d00010502ca80200070998440c00164aa0301000604044c0c00e15401000041d0319100111590311a94610550551008074148902d00d000002080300d0355004040b1620480d91520311410100111008039100b103804c801c0205064000d0b15268561a10020340c3c0c8803482c00d40c0e0355000d40080a0800c1075803001c200c803000390103594003981810001e40201340f104814 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 118807535 1250 118806285 118806323
    0x4060606090b0913020c160b0c070b0c120703030207050607020f16030b160507021005040f1505160203072105100209060d020f0904020301030b0f070203042d03 70
    0x2060520905000031803003a070020b010080e00040da507040d075004001919507904500754402a400411510940d405602c15903040700d10070703040001c010640313030703030300d40d031600c0d103030a45c0604001c11035200741c0c0d031600100002c440e07040c404101128448a07681c4d040d42c5441e031a040c120000d004500d402020340c8103c000b4859219000200103202c42142412110071003c0304225941c03414080c880208031994036030205d014040207451001401e40c5515015061880580010f0300b500040700f510310100d14001014040d21a0035034001025100d40c180d03d400000c01094010224443e00b201c10f0540b2004280b1081155001e000780c10080c4a41f0300c000d40c0011402c1d48151300040f004d4400c581c244500021110040f896000351610910b00030706032800c144800c8001c00c041d41c052280703d60079140030004484159158401380d0f01850040300070507024601020741402c0f07424041e00e1102954014442007020646581c024130241c91000140e4091265104003400c00307070100d80000300088503540d4200e801c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 118808785 1250 118807535 118807541
    0x1103010816140f0913020d080a180302010503040f1a09030a110c030616020f060a05040210030908090402090a0308070305130e010609060c050c100e0420040504051902030406 76
    0xd00e280d0194074515910b40341ca1154941d00c80459410000d1400c28461a14041c4500d03580164281d44c01482e501344e590001c1d64800c464a01184c2580f40410f803400c201c1e0740f146500401080c2c08800002150460700042c20f5800b00500c0106150132800c1c0b01010000001d4031603244002205914006082c0702038810385030b0b0046c0314500d0004400e1850f189182d440020005200140a0041c00d020303142c00c19030f190054000c1e1080310561040ca1141d82208c03034108480ca204202d00c071000540740c01c0600c100a0001c1c40d411249081500344103214002c644c0309012150003500440700140c0e01c040400100301d0920f07088d030002c1e1500030046580d1050503000002001443c1103108000990342d140e010328041d441c0d0030300072400001c280c501c00340320050017040074000840c00740003201c4002c1044000100c41d640b00441400000e90180c000c1e0070300e818140140e400d06808174520f0070100c03420408009a0340540d104503032185450b00d0114240d26200000d141c82c0035000b540641d80d80c0f605042c13260103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 118810035 1250 118808785 118808803
    0x30f0c0723250303111203040614060103090b06010f020709060b030109150e0a05040305091e01020d092102011e03050906070e010804120905130504060b090606040603090611030108 79
    0x80b40662001c00c6030b0307402c451010030807111484030b41100c101d04684003114240380004412070070380b05060751a040c1c882070601841c850b92050384040381035080e038040d0020444016080340d0605003088941800154240c0348164850828a084441542d80d088101d1802c5c1c1d90741e01403032105103024408a01c58546000650580d10000320500403205183d5040400b240f89108515030180e924000c82e01e6407915800041e0404c0c0245000c909081001c0c0008442e00e0510f01c5040d540107030f0240e21100da50b0144040c540880040c100101400d14003e1200240400d100081f6100590726840c0811680501000600c0103d228104526100c2400f0080c00420045d5200030051099100142c42584640d4004103440010703982c61800b52140da130b900e1030101801014a0922007081004120307500c95000d12400c081c6501c0b00815981401e0522030100d503120030600c0d0180946004209d0a9280c1000300d41c1203442c1450005003070713400d60a1940041881c855414042100003000051003131000907502c10f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 118811285 1250 118810035 118810103
    0x52106030d0c0804090c0311030a09050c10140906040b040e011e1a030a0b04020a050702240f0d0605040c03060302010e0103050f060d030e1008040b070504050303030f0c07 75
    0x4030300c034107406640c8a544208002c042502c1040180000201d82d0041e41005843e170078007042036040000101e84581040750180c01e41170f61a100d044c1840410041d1150340d0900395407108088522001c0100700001603100420340c840c0c00111041e00380c03201011140104030706051161540d49070300d501598504203101d086146000044060480705901241c03004841d56180c0c84420784c050540383c103485800c000d08218400d81c0e00d500c0520706171a140000c008a4210703644856480d000c42c030400640007401d0b40700031042c1c22552100d03500702d2083c0003180d41a401d40400c5a448500d40d01801000e86034076007060350003908020103075195076010b41240e002e8901c00d80f1540a4295282c0044003103e000300c0d944c0004413007540c0071544c107027805421080303540e00920300a1441010a030104c0c205544001c00d03600000c10840800061061031f8200680064980c07811038035052401e000681e0301d01000d046520541c283e0310200710b92010000071260050342c01443c075a840301031055550f03484442d2280c109 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 118812535 1250 118811285 118811293
    0x5070908010203072c03011a010306080f060c1c0608100c1d0103020903030906121803040305030706390f0203091e01051605030403020a0b030f1605210603 68
    0x440ca40c881030007a00e10a101c43d55400b1100c0f03222002410107580c4180c0c1071410061100c9085041da01d0a00070184242820100301c000500d19000050031250b041c1d00c81c001a402ca18039007003c0e2103003c281290041004a234403515120000c035844001c40d000105420040d10b01140010040e0021440e8039480701d4032401004031582d501c0041d07c0d44001e00b800e00314039070001c0203242490341c02507000d003c0b00140902180e0030068044041480351780a0310381920782e10200303020005076403910205500001c0ca40b401a5060510315564260340c1e00800c44000c0a81c3e40311940d52503441c11000f90401541703110662070303040b1f221090140400c03041182c03501c0001110b07200051602d5000004840c81a9009000d10300301200c1d0898010160102c1d5074568104601080000c0030110f1101d281c0c82d1841c0214003031076949145104104102d03209501c90a030205003841001414080010599846041c1c40840c000c03005507914100d03800c1c810307110348500c62000071a4220904020503a040e108410a40407a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 118813785 1250 118812535 118812539
    0xb2e030308060a0e0712060b0a0503010f1a070b06040219050306090f130609060605060301061e030b1309051507020102090102070e010e0c0c10020d1b0c021507080909010801050709 79
    0x4045003128501030580414024004101700c0c9100d80e030f0503069036800c0d2900040c41034407010b80610544c8000b1689000400120040c03200024180500b0000d03d0810140d440718801c1c106e07000901d0048500144c500342e4100c002440603140c540454003034985400d5101962103030104040c080340c000b40d03a4103000748010710000301c00400c040c18807401150b00704440d4285180c1980c44030080d080420742101c2054454000042c02e0312035601543c003170216911581ca10058000a40541c2d0141c00b1507030301094106494000729440b14030320820100c0c81c030381010460883c4d50400500d080e484901070340070b0020007020030204580c103501a28034148241e0039583e03080e6441e070b46070040b44001e01030340100c00c0051010440c400e40000082c914003402c2c8003525030070166900000100d0f00035030440c9154541f550f040c026240e003400d81e0000e964206003003519261202ea004505807410b000520b0220000018401c0d0a001c0b00e0000d903048030200418204072581c4602c280c9018060640380030001c9a852030740 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 118815035 1250 118813785 118813789
    0x81908091f090c150e0315100302010f020f060a0203010f0509160305061801060906080c19050a1b0807030305240114041205010b0a1508040b2e03030806 67
    0x860080085011064159115070400d8500404100b8000c40746182c03540380004a40106241c082d40c2e00d0100e44442c1001c0d1590002d05080c141c0c01c0c04103900511440d0100201c032108081060156a020310705546251404001640f4182c06240c0e491160b00c59601001511a0b0386d030001c505842c00c40c000c0442300e669503400e0200c506002c0e24000044400080341c8558203109901031340e800140103080d12480c400400c0311040d0344100780c000b072002841c980c4e03003400340a410403031264000140c080c02c5844c00450300400040040b1081c003881c02c0000c0000d86800b07070340c07103440800d0541c400317641c000540003020303d0610349a0b40016000c4010034100400254561820343c00c41c201503a40400700d007a0007440b0001140d028881d45401014604140030124100d09072000d0000700c94072038000000c030f000311001000a0483c40740d100c112018802001403042d00da00241c1c554111b03510054004041d10b44031714550090b0001c070580503a0b500742021000660103448002d41c1142c0c005e440d0a060340c3c030340da81 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 118816285 1250 118815035 118815043
    0xe0303040302090a15050904060b0a0e0f06010309030908010c0509190b03040b04020a0b0c0a030e060903030d0e0a050d05070c09051e04230703030206011e05010f030908190809 77
    0x10029500a0072a40001c0c40c2c0081070300000441d5070302214880885460351b0018001c2d5078152404d0b01e059a0740c0e826160f440c20101d80640c058541d1100d01d0b01a840c11100040e1780e103800514090425489110000426009100d404007070310441000b4440064074190040164008044452007900c1003600345190349600103415040d901d03128491403a44d543c0c0d03102c820040c1d80117070080382c00c5256001c00042562040d0007400d004c412038030152101d0900c0c3c0c200200500700c5026510310940c000c0020030310380c0e540003044420102c07280a0101c0d09100b01d100d058200311400710044c01794000c0f91a20000f01c0d5110004001e1103108011103522252110b9000b8100c541c1144e4100c8190859502444400d0a03030803030941c0315215151212240d0000010038400c884a4198a01300d40e100c00001d00030140c05000751405000091800c1440c0d00ea51601c8651165851090078103016400c500c0e262802c3c825080000880c1e0090b00566950300030281010380040815034400001e5140c1000c9014000046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 118817535 1250 118816285 118816289
    0xb0d0c12061d07050d0c03020a0605122503090f12110616020a080c0a0f0c080f01090203030307030b0a1208130902130315020705160602060c0a0f051e1204030e030304 73
    0x80000c2c2509810304060040b80c1d41c5d1000c043d0342001c21100c0002c01652554000d80c0581907680c0c0d0b10303854454444bd1024403074006080d40e407424501e180215642004032204403480c08075032401041c0150381d410034400c40b505880c0c0c054240d040c00d4124042654100d0369060600c2d012038100d503c0703135846410301803a0501c08840c08005130008070031800170a485c080903144c1c120b407840541d143d8500c0d0b65240111051040011039000911803410003040b08103200c0200040fa418000340408201c90340041d8403448001e00100c18541d641d00300701ca42ea11480202c101801c8034208902280d0000d080545c03003604003407064407030071a00c070b074000c43d528110b80241c605030b05002e004160648c1c11540d92010170103500c440c100d6450b90a00228001c55000c1045190041c0d2821030005070505011000b410040c0c010400700c440101000700600b01c075401000c1844502446c075141d610b80c0516100e1280306092200352071400d4001041810f04c003420502c000340101d102c0c0c1c07101c0e46e64540500034580c80b0701940c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 118818785 1250 118817535 118817591
    0x10e010e060105030709090c020f0f0706050f031008030a02011b110307030f02010b03030d02030405010b010e030703060f151e0806011d090f0d09060305011202090403030b0d0c1206 79
    0x2a20209480c0d50192020b19001001410504031154480d41f088007216410b031006001640303c844501800d000500c564481e624850002c0e0880d1400d11401500d20710801c280c1c0d20f100c520000025540612a181150142000d40c082c0c03952003c1d0204000c6c0039201000e4a2220700e00040340d05413900340075000440c007801b130401c00b45080080c161000e0345c8140310800180c00799500c4030301d0b0700d441c1c1c0e4043c001002e01d49000c4100503124105820309030300f1218008a25414030500703500c8031310503682c00210030301120762281c004680308241c203041f18084c01c1e485040e8240d0b454002c4000c1042804043d10b00d200e1100003a10740c45050380c444140d552601c0038071640a0440c0030740c10100c0002c4580781070542c40407581007181c00762500310700002d00d0954034030050000242c501c401486030710792602506005005440707030600c207141c0a8000542c0c594000d0001000c2c190303030700c0c6a1005900d81070300d0484440d41090203080c45680d11661000f599041800c11a56240b5144204580080c01003805452401c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 118820035 1250 118818785 118818809
    0x60902040515211602120705071a04050a0f03210f11120c0d18051f0c0f08091302070b0114011202030108012306090403030b0f09040b040209010e01 65
    0x55252048860750080c18203101d6025000180851082c2003e400341c0180300b880000a08404951402030601e4546c0003090000c100800c851408260f0028070302d81510092400181c02c1d2221404421031480703183d021507048031070200c00060b01058046840b0440303000700c18904040c82940000200790640e166284042160504050700c840d1250050383c8190584e1411914209645001004250010041441c40c2d51100713100801140c0e00aa02001007500060724a60721400c150008610f034005949841903604580d901031945882400c51207002c80d081485800d0103186410100c400741d00c01c0f403e860240801e181902010070052003160880d980016283c43c0503420801070020601d540d80c06941004143c03070002903091a5031001390700038124a0000180c80e04840a6034220b100c0d46c40b540c004824040d000c100303d40d2540140300741c2c0a60305107400504404c2d048000303480c2c0e50391001c4041c2c02c001000704010070004040341243c011802200d8000880eaa60312420304085002d010340070540381c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 118821285 1250 118820035 118820059
    0x801081501090c1b0602030103050d0207031728020d08060f060304020f031c0206011401050703020c01030b040e010f060509011203050f070606050409150c11190804090c11010609020405 81
    0x12660302c550202201c42c40c040d000e00c1c100100b00050380013a010306032800c1d40c4c004010402c03c4030401109076407400c0c40c00601142c518545401412020904120142c5800003a82001b44d2905450400c0406400f0110055580c8628402595000926034142c00f04441c1c030041500b500d0b010480140f01240100858030315a81c0f60309110004417802d81c031641520909450740a42244024100d90102c01a40142074540c03410b5021071101180180b0141440001c0199101003680403442c0c020815007801c0104041c0c02110108004008034441c1208651038100421100c0d185600310004490084031840c86590325203100c0c078005c034a540e1009002c60010002582e124a910002d84a0140980c10001d20b10381d40c0d8000c1000d4400d4800c00701e5003442036a1118040200720b00c1203031002c0403980341455407a410002080d6640c81c500c0c000104c0c4c02a8240440200325451046501500d03c0700c0d42488401d41800780540515062500c0e0119942884800301c0c2c94015842520700701c42c1c0050500032984 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 118822535 1250 118821285 118821299
    0x5010b0702120114040f03030c0e06030f150a0609060905030c0616080702060a0f030f0b0913020a03060f020705120304020102100b1309031e09030506280903030c0801081501 76
    0x5622002c1c201520754a42400b4018205400e00051040740116400c00f183e10703040c6801001c60b000881d2210502000712055052030300c542c815640d00444001d510704503602c804401840207007060025a90000d91420040360940e80154440126241500c80040740c6071180d0415803510340c910b1003aa003248080c01310b5030394280c5241c58510828080ca10083c40c0c04019004100c07280d000001582c04511081c405803006a41440b03014040009240c040002110766800514030100c041d000c1141100c034582c052040d5941c5020300002581e201504000100c11011f080000c1c0d0003800094459010703c0b000c000c1800341c900c080340e2250780c0c1640605030f03130700284250700001e10174480000d0b044203050071107004149040c880c0c041058005e4a88091022412441c0e0b02030f42c05103204d600400080e5101040010000591160024103940384110f20750224411101c5003100d481c60110000d0808100d0300a0581651111111038841e6072108656a2a00021982c3d0080243d1203418a032040300100200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 118823785 1250 118822535 118822549
    0x1115090a0303021e040b120c03090703030e031509010b1008070206160c050f0a1b0302060d090501090b07050c070f0501020303150307091509061203080c0a02070e0124020105010b0702 80
    0x6259420881399803003200c2c0f002d0f2105030b0800d404c0400d44000000b4280d05541804400f698040e00080b030300b030314600c0d01c0800705851b4642403000909104c040d445071240b42e83d003888000d00d29400454490300e90718100507070340d002e088400b44c214040c1050359201041140b0648109100c0e00300b5070020100c640300c03d504c030b29040c0350b51510703079007080446443c641c0092410303c1200d28045c150700041591840a043c4080da624043c400800c2000030150200016100c50042d9120010314250008140c00715007441c40c0940802d410050183e82d81d00100852150894050090210b040d02281c0300f240d2a00200c41114032503016103070259000303000082030a072844240d400c0c0c400c005016214600c1d510450309041d0b6017000c00841001c0d449010500264980344561030003001c400c80d84910380005620b000d440720300060154050a58001542c031403840c020415030009041c1081c0c5805150b9481c2503148400f0f252002c139040030090a000c06843e1841401418161800070254a180c1685603082050b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 118825035 1250 118823785 118823797
    0x180f0c13061b0c090e0f030414010c110301060b0301030501230c03040c03050f01020d0e06040c03140a08030c03090607020c0109060f18031a0115090e0703020d0c1115090a030302 78
    0x6801c10040c0d007400090905442d00004000c015000704900e04042c071100d04102501d95060300987c810311040040c000405104031101c4801c0c2441100140315085c1110807140410a0a40560a1080024042610b1402981240d000c1c0c802000000401c10a5802180c8842c030f0103800308440da400704031044e42c220001c603007162252004c0f01c02a6603998500d41400c3c00344690319402d03580450f900d0180748007402518007010100025000354136065641d204406802c0c0006000d415440810b0160000c04019080e096900030300d07981c6e140e00e003085a10031250b00449445015000b94004110b00500015544200c0c030b41c1611100d078101d0905004039400c070b03200d100c045e08005442c041042100c070100000c0000d980106102000021040214081c2201c103a001610450903a503400c150698090310010550310704030303240780e51500c680034200e001c1d026802001c14402d18043c0016010740d04030010b80e00781c0d030030784054951413030403c07030405d182c0d0408441816494002070002130000b0300c254000e1030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 118826285 1250 118825035 118825067
    0x30b0105120906072d0c050a06110a090e1905060d021908060f1306020906070516090c0e0105030a0203090a0507030308010801140402010e100e180f0c1306 68
    0x82041003032011441e410900340d076006a030380c12034014860150303449902d008040301003825482005210910b0205207003801c078000010440c0c600c445004000c002e1010315403d03a002001031110b040c0909200040740d002921640121700d00c000002202460000902d01c1154030500c00540b41110007224005132100074211a403041d801c0700d1050060351012407140b0075220501e02010a542032207911454a407002d02002c011402c0344041082e0000e4818a420f18994445401750301c640100000c05c0c0d450058440080c04c9000340d50300851410181ca507002c0458448840a0000c10b031102c0055540c10020022240003410800014076001c40940081d508a41d400c030071204819169101c1c01d0405025400450004600400411010000740207841110498282c00883c900301680061b104822031a215070140e050a004540e919008149001c2c00750006028501c94058041440349900e47c1103842c100b8070114a40031500c00c1c084035040e0342003a50901c405440042c2040d100f40c4905001c5c0300500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 118827535 1250 118826285 118826287
    0x40902040213030302060103020f061603050706021c02030601030c03020f07031d06040b0d0b040506011704061103010f051302071e05032505011b14090d020d0b071d0907030b0105 78
    0x30706003020880b00c440003140242c0c040c2072a94110b00c10840a00b031607401041c40b07600244401003c4591a0409039030155042c1412a901e003251329004029000300071004108003140401086800b2058005501c2040240e03410440f140d0ba00070260100c1c003c0c0000c1c01c0608406103e4000000e0042e0090030300490701502017441d0310410b84c0010041e9006070400c08440345c0c0800c070048003000c18001d50320800740c1243c003071046c1d242c6400020b0559a5815a503401c4c070001502041c140f080079030088007081c00c2082019665030311a824200040240c0c420140200e80165401101c50311038802d40b107119a10050091030a540748075000c4054a00c3c400c00c2d00d40740820801c105a405c524000a110b40c68800108086c200c014100f042c2180c2c01043e1000405440320b0003101c00c6a40600141c5a1085000f21940c59143c40c4010500d42499210000d4000d9410f00a881c140300411903c40e01c161a60703915004034280800d8104054640d01c0c603280d40001c032000101d801c0900030f40040300402c806141c61 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 118828785 1250 118827535 118827547
    0x3c03040e0103030f140c0d12090f030f121a060f0f0d09020a090c02060c16050a05010504050f0d090513020702060d0504020f040c0804141603030e10090308090409020402 74
    0x300003824280d0048011458100c044410250004144151040d81c40d0b10141001031000307505440d80701c1c0002e03407401c020550102d0b0351006c050364055180d1940100d50307401444007900d805058482007130582c80125194090041080d422805007120422000b10001000a08036080c07181c1e42e005200c2e9000c10b1134083c00000e100700300a6003d80740702c0750042d00101d1070702c0140c010310485025540106450314284660a54080e4000481c2030f08003034800e010755603400c0d141002c48518500c8140041041c01412664418060305401032405170f03014005441210a05080041c0e1724a003000c4011f0102d51034180c200710781d1078031550a02d8503101c484409450912540c6c006206640908900020f2a03651b02c140300a60400d05102120054203440c10440c0c50840840682500c60080c401400101d1709260000541014000310203d1002c41d10007600c0307a91213140180c02c0e50b40003020b86010709480d07038030000c41e944111501c0c01200d170860451440e007050030741400041c010980c0142c0e000384c1c0030003003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 118830035 1250 118828785 118828799
    0x51b0a08060c030106030c031a010c150c0302180108040506011205010f0509030c070603021c0906090206070320030a0c0308060a08071805010e1b030414030307030b033c0304 76
    0x150038402d4109100c1c0e280c1e01c0d8106000501102e4000e00c00500301441c3c80700303031220200c40001b034018121003403c220011031a40d241500807400c407070b050090002e0614641084450301500944001072070303010b01c91400c4441c1c1c001160480380441c0c003d0404d60245004118201083e4094100a8020320002c12000c51104a10003039034000d4600000c41c0d440043d081c82240000d2003070030302804642c941075250400000c0340328005550824401e901c507075600b50050030000d655104c0b4808550141402da142d9020342000380c00001c022a0b07103d1000c0355204c05500c00303040401111400306654441e594039100c40e0b1801c41d403c0400420a1313401c406250400710794184100000c41c003d11800804a15400da0301d0300060503154180d001400041d010424001c8440c04d48500b9100c0c00d003802c00c000d4032540c2ea820610f403a00b212010050142c0800414010b405034140c0007910310100960488071080207103654001c40d9811601795912002001509060f4014060003034829403003400103d80c201034903401c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 118831285 1250 118830035 118830043
    0x703120504030506040b041202011406010509030307020312030412030903120b2404090e12090f01021204031b050316091503020a0f06030c050c0309100504080102120906060d051b0a08 80
    0x3170680b01b800e1080d0400040080c0303a41d070491180500e100030300069440071104a105400035207190306120000c20b80090381e0f14102305072142075800408032840741044800a0485c0e82c01030340c0c01d0314240d511f0483e100000e4001d000c0e1960199241da9001028040d1b04035200051078480c0d14658002c00600c1e40d0044064010300d03404104181151440d9590b01e4082c24404503800480403002d60b4000c4445150008807680c00e4540c40030081d07403240c04028000c0c0040341031241c83d128031210968007082c04001e03c1070803510001d10504590f202c0c9032868803101050f940d0f403140540030a218400687c01c2c800e060098120301d400f4070b50a1008040325840350700103007104400d03030400c20080a1400007044a030b07902d4000c3d14501112418a54903250750207011035124802d02d1545070166461444011002e40305030100c0f4014008100210b486540700d0300c8250013000280c820324080e229410125901d441d00e01c0b924110941d2100041c401130780c007110703801c4d41c81081a08503030748140c030084c000078002002c3c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 118832535 1250 118831285 118831291
    0x31206130207030e01031a010c0620070503090901060c0209280c050702150310060e0102030412030f0206010f0f05010e0d0c0321020706050909090c04022208010b01020703120504030506 81
    0x4c2c442d0030b031300e400c104e00040c2110703464002e509400c1d8104105507011f90b08131101c6400340c1d800003030209203042100352501c02c60000c50a506188480000d81c90280700300440502901a421151642c0590340c0305001c03036003420300340000b9502c020710001007143c46042e411400c85224030110071540001e0844120b00c1262514074001c804241c00041d0303c411481d050500781110004d00c00ca040c11410722203061507852141e8041c020900c0900b903031103440340e1300800c2903400a1529081c6000900c02515005120000759003040001d441030000124143c1e0080c019801600e402d4045031850a107004011520010343c0034030320b6004100031803901c02149000342c41c2c8004c1d40c0030b000d015083c1000d50100107088003c8003401421504040010f0244a07440003c071060118201d0f460400381d02d480c0340e0315081c86c00d8509081e0307000344001010b4080e042181004603025015050720044a0385c4e401406090320342002c005401a082030000b880040c0b24014000820180d03803410506050712035455601d407540c16 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 118833785 1250 118832535 118832537
    0x7031101020a05090f0927161508090105190f090212010c0807020f0c09091c0315050103090f060c1701030c05040b03012c0f060115020c100203120613020703 69
    0x134a0030018145441c0d10200c0105c00d85002900c0d00c0d003030b007440380b2202c4500d002c00004d000322000c06540220801501481c22100700c4107540003643c074196080798280c038598450100310180c0004030b5880041c4203d5201d080300b480c0703c01e4408803030083c280003020505194060950740e10900300168440c401c040c1d280202030400010a0110f014000c0d004440051991085502004641d50311100103d500c0d2485041681d081d82562210610a404c1c042403a48201c9048580701411038410741c160000310161000720b90b40351007d51600011801c1e145824800340200c11507030320030400500e10354000c0010a680385440e4600030b81d45030701400084000c2e1b106807400d0a800209000c149010301c40c02c2e54250003100200014031801721034018464a01e0542420450522090810680d0034868440c1090380603058840ca507071914403030300c002c1903c91260b60041c450110211428200407840c4240b4240d46e80042d030400c92000c1088440046c0104044d4200d140134407001d842c0c10f400e0016000742482 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 118835035 1250 118833785 118833787
    0x61201110c0102180d0f0b07051c090c120c0308030703060b070b040204050105010305090d03110d020d050f0903032e0e010303050a0e0604060c0f1e0b07180e0c07031101020a05 77
    0x100c110621980c48024004510030048030007050001843e401101e01107642c8147da83c2042d56800c2000e961034000ca4449000c61901044078550600b0140c5c41100f50b14801c400c018681509d44c1a6192003440300d02000f0b21149122a0500100d03079010061640400035160118050740c5504445a40350401001182d40405c1c03801401f04524042c010700d0301404003842c0c104060b01c5c01c801d0b4680c0d20241175000205040d91012407513503140c8007400b10303406d6095a00042d5030710700546840307500030103003114120203150f0030001050412001104030380c041c0740d080700320810b1569040c204c2800120520020700804080040c001140c4040e038001c0340c002c601940324503440728581c13000030781a40140301390248030381001c020901c04290001602410250000590103286d0003d2600d154140410700c101542e030f0f0f0f1450180810440156201e610a02c199580c100d011544420841255211802441444040c0500140910030f04c44043c2a80321b00070f141000b01300e641c05921908a9008008802c000f8030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 118836285 1250 118835035 118835047
    0x60703030b043e0a050f0901171602010f111b0309040603060e1b09270f0102040810151202130e03180603011818050601060807170f061201110c0102 65
    0x6000103000c3e41d0701004604146130a000790341c0101148501614054540c9012031540c100e45d110383c40744444449800910307061402d000601d0780c00140f14070150f50040d802d0220142c5401c040d40290305906144014080c2030a55804140d0700e04002850744024611003400000c1d80380d030312806810001c40c050040010b035455541041c40c106100070340440242008a644000380741c0303400d0b810319840201a80001090034801034101104400da007050b1105204103c00c0c00c0b8a51019401482100c50701e10444800c0da80c019906010794610400201010303100780010000d46298010340300c071151000b40301b00010f00030014a60304171925108400c21540c030100e01c0d106203000082c204100310b5070882e0304909561401c85e00700b8840d62408400c000203516201c8803440800720106e040c40d6258044140c94640d0b84074000101004003c9411800150308500d02c03904900301d48100c0b500544005407a110a46da500c0117000c0702203184513884074599a03440c074006252000402030a005a0010000350780c0324 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 118837535 1250 118836285 118836371
    0x3031006090506120f0a0207020a03050615180c0f070b10030201090b0c060c07050c030607030c140301030506040f08040518040209010803130315060909031e050306060703030b04 78
    0x800282c00c00c9008020800c28081e0b020101d03100f459000c42c0586810381c00e90303140c642500103030007040c900039009800304002204000c80480c6052007200e6400b90f1800c414100303020400f003001f8102c55600c000743e500d00403030091140b00c0000d10741441085201c5d80381c24090340d50268411001ca85101202d28103d0043c02190b2b805008540141844010035040c441c160036596140e407405010300d2901030000525104100c03081c00301c0809850011b0548240f440c2008015010300402c580781c10014440ea100354119034034400590307041c0e07908003000b0300c859641c6550f1510140700001c1c040e2020001404000f880307640704001400c141e6a803202660280c24984144204a10107800942440d04140034100754000c7e220448811030750000c0456139141003c202480040c80250403a002d05800e040c916428545c020b4207070760000c8100001101c3c806c0400104a8450005a81ea44c0d48243d00300f0043c00401e220ba00320464038a0000c2002540c40c1400079020800e180021030100302c0340746000031543d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 118838785 1250 118837535 118837547
    0x1203080903130b030601200705120a0209041505090a1205090409050106060323060108060105030403090f12230c040b0307050405040506180c06030105060a0215150f011d0405130503031006 82
    0x304043c01f150318152008404090311501c40d40070b401d0040c1100745003200704100400c40d2100c080d030090030320760b1503040908185d40006152518680340f981440d001c43c050060000302851420f4002c0c0c4c0c28281800403801c11540d56004c55401c550194948481d04040351080c82401d0040030a5103000502d5111982507884502c2a4001c840c1540d0b140020407540e03980103070707040b94408002d180c0155650380301c0c90152460380300ca42142d000c6450380c903004140c0100031122a031100b0f00407503481c40c0503c81603544461182040c07840c1d41940c0c01c0002d00b00d6803410f080d084621031010081c103841c0f016480740003080032a074048030181d81a610400a0000c99010b0400c200007540010010301640181b80000c600e4611041c030513103000b03070000180742c04c400348240042803101c100403001e1b642d5400c00724000c0b13055080c0e440d00c0c0c0340304004040803a000d541c010b00c44081075980f04152b100e03220901074104001070100070311101c04031401c0c02d080d400244040c00114071861112085502483c2040c50081403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 118840035 1250 118838785 118838807
    0x2070605030c0301090b1206070e120105070e041d010207230609030702090c0903010c080a1505011b050a021c05060f06180a1508150703061203080903130b030601 71
    0xd000d4200706001041d00705030300302e80c1942d0b0400404152000f20201042c800d00c40c80c10081340754040c880602017410750204650080c050704640c900601980e40403200c4c01c80e9000d0b5440004540b10fa564102142400c0d04180503407500402305106400e000303100682a42e000b0881216400c4a5900001140804800d2085400300c0703100280101d207804050180e40b88521302000c2e10807545080001e00300100e907012101108009070007030005665144000c1c004240a907212030b10a8240940e020708460305540a6084030016510a10303414040b495042c0707445c4031598140c030f0745e005002904000d030710b4461a1180300e020508d00d68408060a08100d4107044028010760800713000001030004541d101111840c00828070b809200e80c0740c450340200700050004044040c0b00d82d1421500180941c7e0120b9035080b5103800303070b8548103255102e1745c0440840c0c0c1240100f0b145d141a55507002c0101c1d21803c00d03180c0c050040c03822249009a209480107800400da441800307000e50000c00c01045586c0441c2d1408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 118841285 1250 118840035 118840037
    0x603330c0403020d110f04110901030b010807020d05131706040c050604050f0f0310060b0a2d140904050a06150315050f01030609020c060402030729091f02010c020706 73
    0x2040c50706641c0010190061854091705420000c002c60680d41e03100311b44a120b40d04014002c100092403001c10019070b8210b0403805022901d800000c036460b50159024901c211290b40c0540154030070510140c900f904003640041038111f000401141e0001031703080440303122440c400144810f01d003901d0940701440c681d801140c003c605c05c0c0000c004a44030590400424601224103900c040540004a4942300940c1003440f44a4100100001c070040d09074010411289036a80708034051104041000301807520070282d5442004001e00300419a2059406000c0c001000b00140e00d4100f1100001d4140c8106940844100e5074540c010480005001511032030014242410b01c41944c4200302001c801c0810b1040c180204d0480c0c881000c540e210368041400351400005c215154090816141c0c0d40b000100d4040340288076901c400702d0611910074900680303407040e8620023a40e14003001124030541040e800c164000513140c0b8501991107400c00340c022008642da00000e02c55140443c024540501da90004d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 118842535 1250 118841285 118841287
    0x60f02011b230f0d0518060106080a141302010c050a0b0f070f020c03100c050c0307081308060c09040209010912030314010f06051905121801060e07080f0603330c 71
    0x500f0321290307030080c0e803445402c20318006403075600c3c030b802c440e405600b4605024050050400100e81d10f5005a410341c05407548110420151030440f1800d000d101e01038800794105040707110b5800041d8801d0709040700075440341060310243e030301039555104201c030305581040b04440e0032401c00242c140d0000400f882074040b031001b000590000b00210f52940d4600032244402505c0e85241032a80e4002c00c12580300d12407507000c44c3e41e200c0e4582000403154010014848904986e4480016659000108280100b8000c0c001d185000c0102003004025401000002c3c140041d00900280000688902c140a54001d032808280c50700350341c001e02628103050f0010341e040002000180b10482d84401a103542103591f50303c44006490840003540d0740e001d04881c2907242116001000820b80b160391110320001110070091210340c4c1c8070030369503159450407a00e105c0005d11440004e062165a005c929402200242c2034580c00494403030640b84d200114a0400341807410401181281154110310030791112007244a2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 118843785 1250 118842535 118842547
    0xb04110310091e0c0b0c010911040506100809120406020607080f10121403030115030c0507150504140d020f060f06031e0115090b030c0a0f060f02011b23 67
    0x20a03c83d60000c4806030119000408410400c14440220302c003820743e8241c86500d40161071003050103403165481c1103d800301c01e42181a06420503010b039034007c0d100140002859203c8000450701240001c142002c0ca00c01c1d126103d649401386e0b4010070180c0f030b042c1e005d007102c2d241c044409054208040c103001044615001088040c8500c005030740141e403c035050301c1110f00c18604003808005400403c2103900d0000000000b48030144180840441c02241c47c1400f0b40c0d44e0445041c1c031103004d11f02001d443c1d4038400c41c8075025002c03940c3c040c80d40140310f05251b00321000c009441d18070301260181c0035805a409100030b014050740400409034060a996414440c514200b00401d80300d5600340030741c0c5240000540710103001038080d0801003c2d400d800c1034444409548030040d4003d880002c81c060700a0040c03151035181814206030f01e0007614400d280200480f403628004468511245034041c1c01c5560740d205000559481c010803c00702401e41e65440d00d280c14203451005100301c190650a4039403070030001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 118845035 1250 118843785 118843793
    0x5010501080f0906012123060115020309062b0f0f091707030c0b0403020d080906090a140304050405010f05010905010f080a1107020907030f0b06040e01090b0a030b0411031009 77
    0x310074150f0340c944503070044181c005106e0398040c0008900007403203001071020884009980099011142c000c040440b415a603840d020300003000d81030881c041c01078004008400c203d0a01d5002486005503203002146550888442068405110101e40311040e844522110210700b10303002d04401c28010039800c000e046220345d5041414007a041819070f003a180030401c0014035000d02104055150000280001440c05150003510b6100e461810801b0514000c0131940c0903000250b40d0344500e210200500340d0421503241e02e5030340b2020442040340b901c0208008901500c3c0c6000b103034001e00e907030901c48140300d003000000f4290402c1600b05504002400c41c1c6940b43c50b83c41214140c002d002c50b0f00000e201c54005210001c20310a04902030340126002c030602801d10b40c950301040c550007102d0010003201a0500402042c0d00c10f1384950b003201a4240014130690004d0352000060500c0207001c40d60690350380c3d0b01c080f50101e046406035038010343d004001e8400d00741407103e4090003050510401c035082039991 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 118846285 1250 118845035 118845043
    0x9013606090f080a0503040c0e0405190813140f03010212010e040c030f03120b010f022e0e1f050103230f030c0f15091e010908040905010501080f09 65
    0x900500020388681d001018001e0741800c1c1d1203099000030050b0741e030382082c0034098542d0344103440454840d451400f0000300c04c69520401ca0007a40d014001d8203003107600340c040c4940115090800d0302d0400d000c2081302000344099401200401c90b417411504001410020085d000307100016113402a40104081048a0701c040684c03819100032045c0000079481e9401c01131911240c40d00003c100aa25100305820325410107140d1a0001d8811418005140e83c10011682840314800182c056070090381003101486456140d040014010742c106080b11640208403816a44003400150050b00070501a603003101400843c402c1024a11409000551450782c030f200d1008103051300020310704e4810b01304d9460b180d014840790000c3c03035141c01103035110f02503a101161102d10154410682d4460042036070502a40e0001d80c500c22450794002c0c041e414014034080704041108507040d900c40d56102c050000040344507010700007030074462400081c0c039814031001415469016103c20032441e4900204400d03c08001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 118847535 1250 118846285 118846391
    0x60501020303011503020705030f040e06181314060412020f0111070b0c09121c0e060702100c060203100509060303161203020c07031a060607030f050307170901 70
    0xf0703900c3c041051444c084009008030310000b8042c2c08009010300e84200c264020300141d07441070801e4001515000c08010803194014402c805c034082d00000030b001c5803264440c00e0360007402941507100b10225102c0d0141001002c0791300311520031f41c20081040c02941040401c400e41e040724001c00c800c410441540e105801071950040c040b90f0f007800000c8402c05424255001040042c1001c0d20f2201c11b141025164518078420110011540da0707043d22136840792030113403582c00001e0310240c40e16000341c00f404061010b056120303040c005038070185800580c080c070085100d00b0714460400704280c10a0100304c050b15001c0e01280c400c2e80180301c070001042c05401691611648012041d03803860304000c081c3e003e40070788120310700c0d07074042d0030400800d002c1c00703084001c4100031060100c2019a40e600030499580201640640051175124a55a402d4000c500454101499092402c01980141c281c0c3e9040c0074112220f40740f5035101c400445016090034800c1d505441152542c15100d500907002d6a4109505 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 118848785 1250 118847535 118847549
    0x3090105100608040206181f030c1b020609120d0302071208190b0f120303041101030608120a050909282904060905040804140301110301140a05091003060e0106050102030301 76
    0x42d03240c07c0011415501f014428002e04610b0100850f01e554001200c404100391011038200118090f0071b91181040c6442096804100012000681c0901805030441e00e40250014500341c020807000303004000217060382c2c4840c3d80160b600c42052034230705004e2800b10021310500000380207001040061520842c0751900f04680010150016800558400314943d19580c201c4405030040c0102b43d0080011031040b0700400200030b02503841e50045003242c8052003180c6040d0410403c0c00c0111103010004c210f0704c41c0a180c4281007aa50798002141c0070810303130305821003c2522800441c2c42414603501424481450b200f001309454440d90b0035000840c0d840b1041003d00703013030903014151b9981d40c01034001d0440000200301901d018500102d09600c140035030400cad03408070080008207107014003882c032000300002c1e02c49003542d103804c10080d01303142804100c0740c0c0711003080300103d120b489400d401072058513411442032000345581850390849900c0c03070203410346904204040c846070b41c000084904580340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 118850035 1250 118848785 118848787
    0x8070c05030c13020c1c0c03020106050a0b0a0f022103010509070c0b010909030203040905070806120c010c060b130e030307030e010b1e0a0b03010603060f08010b090f062403090105100608040206 85
    0x104602650071b2002043c040030010048032150440070380d00150752121188690001c208498949040001b07807107a52294000c402c5041002e00c00c864496004070540f414039004681041602c3c11020912410010b40840e4403500400100b04c1450403c007019080140c5042a041206079501c4180504c85d0500400e5143e40c4c554045404040c402c0007160010525050200482d00b0010b070b004020340b800b950414401d040f008901284048041110110000140c4401c01c4d1120745950304009020b07103075115079004540e25040b0050061a0003007c89041c0d508019540e68030b42a0740c09812600c043d955064a60b00d000c500c41c055172101400c42d0340e800303445c00c1000d134008102c00000d40700754002d0f00081c0785800040b00004045406400c41000d5801643d04119466250246e1a00300d581808032545d00441a00108040a84980084e6000007002d820900640b680d01007038200b00c0202414014141400410010040300c01c0c440c00e0f4100c808031805442d45850508020018100680b01030702c2404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 118851285 1250 118850035 118850047
    0x15140d080c0a021305010e0906010e0403030b0d1208090105130b0a0203130f050a03080f070518030c0a060e090a020a0210020306010210060e06090a0b13090804080102040308070c05030c1302 83
    0x2042a0790702039600500c0d2102e00f000c44c1c00903a01900c000c2c030444000c52142d03070106c0c41240b00411050b058807010050108642e44648044001e448510304160300007603048501e801141030b40009052000c1e85803150120b0341040c006180c01c42d08018004c421010406001000103284240c90315004002868056140d495104011000c0000c90b803004080c0c20300c050109040180201d15100c500f0b001e42c0740c0786040e99079440001e9110008031200301c0043d1042110183ea440f00105409040101408840e552662040880c494044640041001c503460440944503840d0400c43d503648a0481c1400b58142098084c0203036a52101300d00c001c05490300440084e495900c03c0080415400c080101440203079601c4503041b0342c1000944050b40181e84110024518012078001c225030000d0150078003000700450140007005148041c41100e070300004020000d5505400d0014001071360080b000355540e002140752500d4005d01c42c2d44010b000e034119208a0304103960361680408900d60301100035075204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 118852535 1250 118851285 118851307
    0x50402031009020417060c07110d0f02190806010803070201090b070317010b0309010c1715041b0206060102070e010e060d0602070f05100b0a031509150504050115140d08 74
    0x1c6029042440900c0c8041000100c40d04028030b86204a052581501c2e5251240d101d40a214402d00030082c100381021583d0f03c515041202180c01070324003c01c0c16003d6004503600080d01d20702c044511b981e03a00e80c01241400180710611103640149016001140342142690010346400c80b60700c0380031000701002c130f4044103240c0aa8001c80c61010b1445100070503685410311040103810958400001b90300c0c0c04030348030550b4003a50a504030503118040c034140958401c07048201c04030740141d8058005498080000800020070003200c01542d00b500a00030f9450b114000918200c19981302d150104510001000f810203800d44003a001320041d191510700e4066070400401900c0383c464020501c0c503142e0307908801d0190208d120241e00e200c000040c00004108420040540154003010348200303a51004d21150481d0b5a0000320206d11030381984881c200c04103000000c5800c2101d095601740d44400e42e0504a91744850500090010700034002e00c80e010a41c0425070481c03e541004200706d500007001c600d03c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 118853785 1250 118852535 118852561
    0x6050f150a1e020a03090519090209060706141e071409010c15050703060b0c1209030a02031605010f05030903032406040609030203070f05060d0c03060b040303110d020d0905040203 79
    0x84800a0101400241031050095030303030342034130800d0b030000c2c3c10317024046485d240c00211221180a01d44400c4503560400c0324800c002c1d84045461a4484410000800043e01030b00079403102450607d8162624039040b0b1060000000f2543e4444a040144041242c02a045446c804034804030f03014094841100000584000b0a000005032510802031902c043d034220a0700311034420300503a0350038002c8550318540c2c80614019481c03944034681025004060f4080c20074040c0c46920001400c5580c10306c00c07a004241001c4120b031200d440d600004c0c0050003256000200e4503e070702190314007140b4500e001e220b4030b0b4a03400003502403a080401840c40100b58404070b8000444144000d080d03580d43d503518480980849010300c801c0307002c0d0095010000304104002c00e4241202c00c0601018070b0101d007294200c00900c40415491305147d901c0070017142c08007010010744051446a160103030007002550125143c00c0015808908562003800d10040955014850500310780054034096100c0d12002501440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 118855035 1250 118853785 118853807
    0x3c1104020408010f0e0705030c0d1502160b06010503010f0608040201091a04080709090c06050c1c0c020f04050907090207050c1207170a02010801150203070f060e0106050f150a 77
    0x20240c00032902080314a41136014154000250034100802c1e0002c0e0002502d50400e8440d296058002409888003820a40305c6400d600b4821030301040d0220308140081d0403070700144081101ca0283c1e00f104810850845105a00300c142400d14505540c54020117500c440e90b10b000f560100030303591002c5421a40103059001c00707400c60300b055010320b55401c040c5000581191289040d1413280c0c00300015404400e2150481c243c0c5c10480e4410103900f800d900391144d80c000e06800086100d0854042c3d42174840040c03402c140d410941c0d80d510142e8079401040065510444040c2c429440c14080c4108000c0c00105a022200406d80250300c0300b205080c210b08050b04145043d410012404041c031074000c011900c2d000703980c0700600c412080c0074070000c40396031520709200007030200340301c440148812103c079003144641c4a9248122890860f1320390354105d815150a104440458448501000740c40c401e00440d8082d00050710110110390307030000007032a811001c402e940030070000010500a558400c41203041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 118856285 1250 118855035 118855039
    0x30e030d1d07050a0e07030b0102240406060b090f01030f020705061e010605030709060e040b2106010b070b040b060f060408100c2f07051c3c11 63
    0x400444851001190010411001c0d1074000e00390041264601020703039038203840016001c0e205507a51190b0030b4004108601c41039065128000c90f03100d515a071103100c0103480d10030310031200480c10181340020603900181c00a042d09681400070781501c1d00e400c514035010000c01d10740442c4110180510070028445c0180280c914014802041295150700043c50884c0440c8201c05040b03030b903035000482d29408142d445038002120804200203052040301d9240010000030000a85800b00304001880c2c0d00c02805a0203206d6140c0442c4030302100c00340800c0b8010016080154030f001815543c4180710781c00104020980302040010602c5070f03c50450740307440ca600140ca810750340c0780c90342d5001e40c1d244802e041808980d420002030503101441409551314440200f41e582054903203500c031960002202c02c1c041c0310381d80704548000406070b4a501e4043e040c4000c8411410403030182e03013841140da000098030000e443c0c0c4444000c0192400740c089079102c02c0094916500c91614614000d000000c070122019 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 118857535 1250 118856285 118856291
    0x1218010c05030105030d1b122d030606050301050310020c03070503040e0a06050f0a0902070311030a090305071a040b1308100501060305090c01090605160210080415020c060601030e030d 81
    0x600d290010001e50695504504903120b00411800454034034070505d00321286410030b084207a00060340d5101200c0c4910290801d9002080031075103c403099188441544c0000110045050305035400d4070a41d0054511441c0c1949150305000102e1350b0784504501d44500c03194009102c1110a10500030b41e16440e5000c400d0300d599503540c3d100e6a0b034501060b5040011145484000178852030a035020080105018003491686807815032020300a4012802c01d4051241403805001c1e00f030b109000070802062030341c0350f240d0f900c0d0440c01c6c00c529082c1c042d041500031200c3da25094080c440c541c4240d600304c4140b01c0c0c0c02995507003080c400c012003001a81c0700504520034252884c0090344141c0025060307540550b401c2020b640d40320b500340c0e070700d0b0707541280e160104070405002c0c41050310410040040b503088100c5a803e107070590f400304580b00745450010b030008a9210070310040103045851030181c6042081c055007016040c0c401079032078103006406581810790300d616922074070300280706a0701055043c110030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 118858785 1250 118857535 118857551
    0x9030b040506010e0a0204060e0d021903081309020f0d020f0f0a0801180902091611120307090e190506011b0f11011809410c0f121801 59
    0x1c582e5500c080c090040c4190f1820001050801503201780c03812981c0940d61080c40c8803155061200012445030140d030041056401d40e8920640d89607803c00451040c610700350b469215001d1107081000716000441c0581c01003048410354683c0105480c038001454900580e1114407031902500c911541c00750703600102000c00c0f81c151003500418800d04032951140303200c50515221281c1003ca501480c802507004114801040d901c840c015002040d401c00c505140d0f45250204626519060400b601851504c000108015955a01047c5003004060030300b0b0810fa5400e01c00d54245141928200396100907607518001101d0340e1148100c003102c0a45450036400201c81030400e0107600740303da0340a40715a05aa00d11509a510940312518225001101d0381c08050400304101c01134261b407500300c072110f14240314110310f412031400c45110907507000038103900c03c6900340d05e1950b80032001001c03640e101c3c90901c000c2d040e416007901159800103000c0c0d0410103540c0c50107030702d000142c141000b2003211741c40c1c0111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 118860035 1250 118858785 118858793
    0x607170d060906031212060803040306020c07140303030a020f0f040303031407050315040902040b12071508040c17390604050d0f030c0209070c02131a1009030b04 71
    0x50103006014601072041079240c04000d820360704544002000085440011421a0300c180c4904400352044440480c10940da11075140c0341d138015070825901c0d00d50019102d40403641c1000750b40014200c611011074107020795000280c99000c0100b80d01c0d01c17140c0018480081e002d50200b01c0d6196046040b8041d1115201c0c10000c0050846040401040300305c2000b151026009209592242d13003854503d41d6000c3d003800520001d001d102c08120380164562520042685da4038049044445244000780401c80c541071800703a0b0041500008428000400c00348030100381c071804200140c4e4615141402c140e041c01c0c681500d019082001401441c003841046640c1d054900380c11204080e04100020241c5110000c00c000d40c49688913095102e201e11510b2000103506d005000c8101d4040d003006004462160085030742030300203d50240020340015221421407074019241070020515010400c580030408242c4204480c00c591028416100012507415951081c0082d0028580c4000c441045061602d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 118861285 1250 118860035 118860037
    0x20408070e070f0806090105010c03030902060a2102030903120402031615020c030318010f02150c070209130c05040b12010e030406020607020d050906030c0d09050705030c03010903021b060717 84
    0x1d4a100180f0701c42000160244503000d00c070300645000305081c5550340303011300544021105100c2181415282c040c48005695840040c00c0075110761340f11492045402c41441500c5402c007007040500030b1040c42404004034000041da0b00b00448200c200032640c54600029190100c0a41d100301126075003c40480e6021040040c003111012940844000d08001410540c0701c2c043d41d803007425100200c9100d001e042d88924440e5803040180d0064600074006600c07652000d0300125020440b0000014082c0110308068290302c3d0702c039080c1030384150a941261b4644100c5030b6144a40d610071512642140e205a82d010500004104000c3c020020303200300701c1c8059140e410500c10300025000e070354009005140003040780342d4000c166a9845250181100801c20190000703480d40907049011b120040d81111144030703034400c0320302401c0108102d0346000304162800700f14140c154007030b90400400400081d000540911254200030360358111800001c0460300c240210a03000d88403441070b4400d446648840340c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 118862535 1250 118861285 118861291
    0x3020904140c0f010531061e030203010302010519020c030f01051f08030d0f06030c0605180a05060d0515041401030c090908040e060411040b0d0609061a030a020408070e 74
    0x1805a030500c2c0410b604208039581c2c100140fa020a20812490356601c074036143c001503031010f410301c4900700c030107600d4201424079054004001141000d241142c55050f411a03034025a030071352806520750f41c110390009217140581b200c400c29407601d035400b9144403030003030100209000c0060b003151204541c0800c054060802500c8844600384010300702401081d0a541ea8030584440c4c10055260119500000c4001c0081c103211181103540c518012000a062034040c20003030000d42c0d03c05848550b600d5207225081c0228517118450745100304100410b860b654265aa60460a04001615620385080031203031810760300d1041c0d00038a8904808020a6091000c6059034014034000620941340c0510300101c40111101030006d110500042149007040e03080380343c0c80079020b0f0011920340f41d122400c7e0361640003034000000c02c00c400305503604003003220310803040101144241809000c2c6010540e0002143c100800708006200000085803124260100d400034220704017114030580c1d0769031544039219425 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 118863785 1250 118862535 118862573
    0x11060a02120a0204030f02090a06050d0309060807090303020d110118050106170f030915120a02030a0f060b030106030506060f0301150318050c01210f020a02010e060405070e04080403020904 83
    0x102000c2800c0300118404c2d40e040da64096004055495941c08010030782c40010443c8200c030342c46120110f40c0d9150300450300381c4507101c2e4503a28585410403201900c060002080d56040000703800041004c00d5001900c1c0028620b1401d00c4501007640b010001d0242450000002c4200b4403012880e00f000310560140d030441b880c0e401440c42e01420310311499141c80706030140d150a03500520521000e40351240100c5025440084841d140c80e01c800071f00d0300c852404403088a40c041d808010000030300118020340c07a0b141c0003142c08010940c10070004003420b0006000d0201055a1000001e02035117a5070220384401d0340402e02c0586135170b941c6a442010b042e10b25410400a810241802c040d0b102049100c0603c6034010007500303c480ba66001120b158160084125412000120307040d0411050b1084050010014030301581e21144a02c01030309413108030382a660164402010000400c00108000c42554011180c3c02d03480c1e1560f0078451414015604065441786481040c84200f01984182003211008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 118865035 1250 118863785 118863817
    0x12040f03083d12060606030612020105040b0a090b040e040c122001140d0b090f040c140f0a09090b090d120207020d05010e030c0609071401050a11060a02 67
    0x40d4001c034104680d0140b0586244a07503044221108082000c04405070700702006280d46495460041d11001c0201d1070040e5003043d42e9100038040142e02d4041c101c050300911500c0d04c015411580000c050744298400c13015038490100360030280d00d114040520050216039602a1a035440d580c40d40b00c01070041e1811205168452800a4603403003192550f1340701600310f0003900c8100400802070a8210008a0007810022400d032640d00c42d1800a01405141a00c030800064104503a000d0128451000d0401a240580041007100085010910364142c0710341f10705010340b8032245004202c01c1d203481d510403940403034154400300701d207025503000c3d004042c007903040090b40d6224904882d07240c03014402c4a000040c60759600c1c0c2c01d140a2a0018586a4409001c600780f40d04a91a6242100c010700703c034110540000507142c42c0500101b00e0290400002c1c00904401c618068120200f07040d6008403505200c80821640303022406450710200c00c20a100c02e40b9007a1820f41804070003503000100b18103c54007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 118866285 1250 118865035 118865041
    0x6070f08070c0c0905070c060509011a0303090a050d030e0307060807020c12060a021608030f061306150e01050d0509070816081504080705010f05070806120706080c12040f0308 77
    0x445084145501030f040801c030101941451500005898005c11900c18400d07902e4801c00000c900b485030074803505058000041544680340014054004084001d01c240e000740a500b1059540004510403140b00f103501d602c2c4008030f407500340c4002c0c030140362075035041c0601440000d00a81210b0310701e105404507800e80c0c5400d1960030403c03800401d0340d45c02e40740741c1c3e10203030000304140c5c182d90003400c200101c0c40028440c007000396104141544211201d61461194138140074003414501c82d140421032083d5414880c45003456503400c41110f50025a40c02c0208a02a60310030341d005078110f40301e050603c442402245402020b0603510700720b91045250901c5170605500004041c1c481d1602a1010030303024120102d540304c618115000098400c0d9000c13403040000f540028400d216816007032110120200b028074000201509070440281900d01030701c080040e40d001e2040200741d40381074605a041c507000a03156405100654058001d440c80c15040e84420b210a018201c0304a003000391107991074080c159 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 118867535 1250 118866285 118866287
    0x1a090a090906020a0314130b071803060207110105040803033408010602070506070b0105060a140c0703020108130b062206030308090709020a02190609020a09021911030a12090506070f0807 82
    0x1030041f2488020751030980c5510f00000c0302040800e400807038031719100c061507440f04114070908149078001c0303542c258009151000c100700c45030310001d40c810074200075041c945030518468032880004c22242c100d4841e038040344070448903501261034030070b000c0740d24001c60b03d086140070b04161030a028180240c032032124005940c0ca004800c84d5010380d4070600b60b09031a443c010602120760810038803401031044101051445101407400b925940544070020803817940307140005002110080c01c24130540a0310407140e40401e0742020b06681000c001d40e142e072109102a05152404a5901030340110542041c01c000185940302580501490f40c050176a203500e903031b032401c01d0308a101c0c0d0080c02e000368000340c2d07500108101c080401c828090250402007040e032900e50004500c100b241e006454030f20790114450440c01407001c0e031075400181500341640414100c2100d15582d001c1e544a01007084040c03a008a0f00400c140c01036490b4960113000c641c0315061820001d4010301e06041000002604900011051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 118868785 1250 118867535 118867571
    0x70308090619090203030f0f040905010603020901080403050304060b1003140a0c08180703060609021c0603080d0213080a0f021008070806040518120c0c0306011a090a090906020a03 79
    0xb0300100d842807a501810201050107059110810380e454003083c03048444580ca5140200030b20300c403088c4040d030b131039003030507145012100c0c1030704010100340c4113110540150360008c20030380d0440e03007604109c2e4499580e031610f40050940103007141d400c640180700428909070545c01070340581a14145290f0f440d611000c0210485240700c00d000002004040818002d001c00c26139052081120010b94100031340707c0e200c10081d90b5041d44441103190380001c0e143c3c40a010058a02e00c10480e1510610426213103880e403410f01e00801100030003984d170004e00c80401c00000c120f1100240520010340c0c000c01254148100981131200c4e042c1d020311030f00502c50540074810440c0d40d12a81c1c031034461840030f845403002d10000707080c0207000e4080752118088007058040100034440c00c0306c1d5041e00540e44c0340140e1440e01d0030708181402030f80c0203074441c500610002e16180da8160140f548400c1094a82800c100080d80e02a03a9078484542d0078646152903040c800315400424100089884c1401030100340590384030a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 118870035 1250 118868785 118868791
    0x5160b0c0601050d15060303080601120c1218020301150504060e1905040c2403060602030909040602070204020f0f12060904050c040902031c0914010c02011e0203040b0c030703080906 80
    0x2090308598010f0250385007140612403079a00403191203c412240c950240c00f1584543c1007039000c511400b04205881d81d02900300184500310356000c1c044141108000340c4150380404101e50305540314800310807281c0328804030700407541c3c006009200103600d8004c800070018540c056180900d08062000c91544884040340340030300c0c880f12111580d40c084528010007401d000e00216240660040002400b21071240602c01b041078a4070030040320301d6516809001c0729590b6001c07000703640050003101c0c07096507502c504d143d12941107240540d450040f84001402071044808140c00c0c0c80000c01c014010504030b034007900b81c50340b44440e440c485480d000100300310184200e038001c085a005802c00d4040342095003082015900c081c00b05d450000b00710509404406107501e084001545684080040c00a03131841181107030000c3c20b25500302c100030b07000280400c060384980440f440445448201c90381c0700f0800c0320000d2a80c660301a484400140741503480740e0100d401540001c03c800c020420268002c510540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 118871285 1250 118870035 118870057
    0xe0105270a12030c1b0308070605070f023d0c1d0a0b0f0d06030804060c05010506190312050d0603030518010f12110c1005041707020a17010207050a05160b 68
    0x10362a0071562070402c01c1c517040c1650241796441c0940080041c407031002500c5290f02c41c1a0108251405c144001e1010700b0f01228202194004071240000c41c640d60b050700d400d2044048084402a0b68003050800915144088500d840c039044004106542c482000c4a032040090002000b440f130a80c1002540d840c24010301c80c90741c5041224440c040c00140040a110481c1c1c280462416502d466240590300958040c0c0c021404142c0c0b6401008420300c110781d880f4504403000508030030003510710340010900c0c2c000200201074055840800900800648810068100c0244006510f0780344c010302581046501c580ca1541c806484181980501d02010707220310507942e8072030003c5c2d010307070201c0c0502482401c0d14040c5204100d070341c002c81410700c0a1640340c1150344001c9804c0c02c1c2441c100c42505082e9007000c0c0d41d654207000100050b62044410b10440d1401608198860441010b0b00c0c02482140350080c524400e03c030742001001000310749009060b80c0d0b04a070150407552a80308498038490444102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 118872535 1250 118871285 118871297
    0x3020c0d020d050109061e14041403070b0c070b0114030607140408070e09070803030c030403030c210509060106030605011209050c09191a0d030e0105270a1203 70
    0x25064141010041401800148940d080c0101030300c40c02d0864103c0305090700c56075140d8020030702e17051004042031070140d43d01c00200b08000c038612004403403400c00b8200800011210800344846c940420a403002e0b5600805074118904020624401d0340d4040c441c115485540580009035481d28a40030602e9004040c015000c0c40d9100081104c08007800d810214503004240004600c07c0010064440900307070000a000700c50a001400515011a80c6e20600003903104000b0802000300744000e49400580c1400c4c04542d6039403580c0240c45c40403968030440400084c03480384d6000c0d400c16801c003070300451100307042c0c4440ba47c807600100d00703441c034500941d070104840c0070b54100c0f00b07a42c60344040b40f00b0b400b40c400e0fa08442c54100000d0729440c81074a40016841c8507107103419034070800d0b100c1c0b48181d12101036403048408100f00800e5283d07840e600007a092008101d401c40941e4001ca0488440207100300d55035200d2036614454110036825124001e000c1c070003840010801c4e034003400d540c1c007480350103484507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 118873785 1250 118872535 118872553
    0x509120315010e0420030a0f050601020a030c020a09021204060c09050f06030c04080703241401050d05010e01050c0c01060e060102151810060e0a060e06060903011509060609120302 79
    0x10344000500101c40f40d0441d6507250910344044446807400c0600e000c8042040d905e081a1005200399420700e403402200510308000c1c010941c3c0c0000392440c0013541400c0400c01894280005503082002d80d101c41d0b030241c000039030480014508424544240d10030b44c010031801c966894201c50b0326210b030158039080124885014203902e080c04c0039607800040105010311b4030f9280c11071942000020b80c030464000080c08522104589920051400b80412080402450100054550880300c06100d07c1c1d001e01e00820a50040c0902034004011031409a4001d20031820640040d000c00e078408400000c0c0d039403804101080600440307103d035004400580c000c2c00540181c0105040680c4041c1c01c1c410303241d954442140c0510301c141314088034000d8001000503403d10344030701031410344802000c103080039240640c00d1010009540c0c8941d0003d00076680103855076135420100340101014244443c0c015055500000c030303242d480d0080700548001c1d564050486640c1c0070390200d0008120001405038001d80c0d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 118875035 1250 118873785 118873787
    0x809160909060902040c020d021b130b010c0218090106050103050c0306011b05060c07060b010203030417130f030b011517040b0c121618030809040b0409020a0801050912031501 77
    0x7090300c65000e00030001d511409540080c04a40359004a403001d0b0700403c083d001d03940d07018403441701c40b001b030340e64250401c2c07010500003481440e6058014850307559982d014400c80c1d00c05c40340038003a590b029000b04d4041040c0c850700d41c00910100d41d80c959560031f2140201d0554441d000300741c02246644691030858950000542d40501c84c0130410024030191104034004c07410030041c2c40e0040c4544007a140d40c0c0c40190034958182d400002809055601c02c1040c0000192a000c200c0a0032684008180e114018070600503482450784c3d0010383e1444100390040140034a440015048880d50340003100006104202500c0c2070425040000c1401c0300000000c0201d0b4600d03046e81d82c401c0701c803a0780134a000307481140c48410790000d91b9a0f840c2201a41704412801c2d400c0085c07a101c0c185d480f80d501c107a0340d1440e0388410b03440c421030070a58084c54417040c0f02d05c0349843d242c1041c000103900602c4e40b40e0303003503c45810b14004c11044422103c54459a01b03d640c240360380034216400340709002c481c400d0758805100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 118876285 1250 118875035 118875041
    0x60803040609052403180c1005190318061b021f02030405070302040221011707140604030507031a0705121519060f0e030714150903030a0309020108091609 68
    0x11503c4d04080d031511488035074181a4000c40c4180440280c480d8003070080d50010f49082801020207004804501e01802c0c102c4c2c0040c181c60801c01400740040c00032040c0300048001e840d1446018082c900034140314010000f05800490908114000307840d4180310083d03080b41d0b0b03200c00c818452101031945031b25080c0081260005c541c050700034000c5562040d5640d000c10100e074455011501020b80c545000501a050074511500400d8003076060419096100c0500b03031149210712620458001002071800d0a0300c40d641a2001143c005003a503692035034030304041d400240c2547c0c420100d8007003200001c851034024030940e00054142c046540c2d8a40e1101c5042c1d482d07441d4141c12950000c90301d81c610391902a109240700140c9500d5a40d88412800d01d0005088501d500e41c1003031180c0c01840f03040c03041180f00d581d0340c1c075603040840750844102c084480284081c46507401c1190517010004804540941541001ea60107100381c1c1c1c0c0d18130075610100c885403906480074054846143c6004100b00c02d19040d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 118877535 1250 118876285 118876309
    0x5272101021314030105062b05070f0303050a110109053f090102010c020102030603031207090305010905011e09020907051b0303040b010e06010203030f070c0804180b0406080304060905 81
    0x400040c40d00302c90103401c0b00c0041d80b6520083c80e420301c290801c4001e0800703004035078020406490f050703000303480300c9550407030710400060202d006d0060240c602c0500900f0845040141500020192070a850382802041c40d8060201d80010038001c10000443c00814490f01000b03c4e001006400b207040120008002910744142e00910324581a5990b0380c0d002d1214480850441c0d620f074119610303a0b0740c0001a00f50703441880b180c41964070500c00c1168544022048454004456100400c25900d15900b83d1313509101e508060602d61030710100900300300b415803012400111240404030905022811102138603001140250043c88400208106030700540140c04c80c02002140300d0300000d1464980d52454200f207809985050440d4010041245c0861030160094020300c05140365107440c21002ba6003140c007030449410001201c0d007000900c404101a54041d11a0032903c011004017804010040c10030702c100d6501c51803402000054081e4004100d5007140c02d207440f12100280b404082001c604e22403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 118878785 1250 118877535 118877599
    0x30703030e13021909140612060d0602070503030709030b060d0f110f0409030c060b0603010308180d0605040f050c061903050c040308030f010f08010b010503060621070527 75
    0x203000100e410202405813910004042d03a92104d940c1c0f40007030396038000f9510008075000e04070400540c0e490f6444094440d43c010016980204210f5031444c1c510024414280050701d140008428010303003030381c00215441104d000e0451284203488080410a0801c01d1903c02001141c40e130310b540000844400341c1800e40c090017880e1030903800c6810042025113684550031000100d0895035042017104512510340b035990f069484a041d9811a52407548501c01d0a0b4000482680c3c40e0600066941d02c81025504562208080c031840c105460501740c941e243d035600b2a200d015180f18071034241403003816200000d100d000000a8030304d550380b00703400030303c400b8281c0c401c001c004010110100310180002c2d8082c01590ba50300400d0741c9050302c00190401182c11280460341800100d400d1681c0c4a010fa03500031404a81640d41d510403048592030865003203189a0035a44044100101550070030301410604030030f00d0f540c00d003000e105c407240000d02410050302c0e0707402040c200020b00c0403420204100042140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 118880035 1250 118878785 118878787
    0xb0a0e04090c0513091401050103080a14040911071a0c03060f03100c020c030d091d070e0a060201020405040c08090a0b340f02030304020d030305060301061a1305030703030e1302 78
    0x280d5004c01c501020b08a1002080f81d1180f100000700f2004004203807010715138500800c015415503031201800c0c8140c801100402c04c01e54040f22403038045500b01c8004180d468010042200009000c941c680c0103183c00341c5000c04804070490105607980b408078850640703454990302d50340c0c4140410684406000310305416103d2410340980d00300b40c40c4100301040c0a01d400421201c00300908040c6480c044a084004210b10402c04024040700743c5803a68084c0d1140d8000310482d035030000115401610034000303079071001ea040c000262403078040d8003d105440701a41d050050445000c010b030b0b206001a612807156078400c0000f080802c0c056028180c0001e05d0303070f50b041e0105140341d4403001c2005210300038002040d2400c000d41c452035000340d0f1400e1106010300180d421440c00e80c00041c882c03450618054241500c410010389513540a501c00c00240c2107000350b00e402901e517213561f1079242d00100c200780842000320303001160501e800101002140c0c0e03d07a4940850414260601120141a0b101c0700e0341107030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 118881285 1250 118880035 118880039
    0x901051207031502030906061c11010509031b030c06160b040201020a0503030708010f0f0e1611030d05150f060f0f09040c020619020a020c04270b040b010b0a0e04090c 73
    0x10820f40200036203015000050384906017a004541400703009400240705d04051001001b2030f8814000300c0c071040d504046e852003031605a80041e504c600c50001815030600501c1c2c110710b840d0180154000e0600010340444d501d981aa40903c01540b103042c1c06450548107103e14400020801c1541642c050f10610650b500a0615a64507146030010303112400407902490040c040d0b007480203501d0b001071a40701090302d0164034254507000645800b0b4410902008040504c0e00a1802407120320740110382041107a1340d42c00120740308801000141c070f0040701c40084684000c018544000c00a10810004000a150045e800e454000356403014008441d81c1900744891080c1c0e030f03074610030096101c44a4000d005107192521012601c3d001409a540b0114814409074044940c00615894000701c00e4134001008002e03404400410301440d107001c1c4880e08210031000410462074042401240700d441700703645a03620703081400c1044c041e0403640c00010380d0107034441c2c0e22032070503400400005000b0707500416081d1f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 118882535 1250 118881285 118881293
    0x7030f0c1d060403080708030117030f040e071107060e030606060c0c090403210501090b1f0c0305070501020415110d020c0108041a07052205060301030807170c0c0405090c090105120703 81
    0x508070f01e030300384d1f00c2103030100040001c5000100b4203889005140061440d0880450060348940101c1c000c1c0c1300c10a0140c40081d920034040d680d02c1251295100c116000e85030f441e00c00800c0d1908040302c160007070181101040980c1000c1007078440254061018100c180380030000d012486074001c10950400160540c0c2040c00992074200b2015403e40b0800483d00d58140380d0b011082d45d58108800d03008005284956103940001011049401418a041c019910490404440340d000307408000d001544009400030b040c000841e1160706101c050b4440024104180e410b454075000000710701c4c00941c00c1b00781d40c1220740d07110381045030348940310b400e00c4100c2506035101d08802c044101c652802044c0c00140c0d4401d00064001000c0664451454100c01300c0c1c1400081034150106100082141ca40420500d04120b04034001200881824000035100c004540080b60760750b84000d0703001d0040d031074003010038030191020902d40d0380c5803406001c81880f40d18150a00c0960b64910340060690300640b8008000030b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 118883785 1250 118882535 118882537
    0x302100f020703062f1207030209030307060227061213170309060f010b0403110d0302070510020703121e1805030304061d030106050114030901060b0304030807030f0c1d06040308 78
    0xc201074085c3c80e083e02000c0440d545900b40c8102010314a030b02e05108036120f034524100c049074410283c0c5405625100b48002007031841c01601c40040c0024008104012200011107450b001050201c0010184010341020321005114100e0800301415480e40051904026606480c07007a80c4100c01e0005c0410090b1210080b50308159500c0505402000500010941032951540508190304242c3d21f130a20310359071102040702c96160203011352082d031410070505d8000d201c450010040a040100e22141d0400025102d4246002c01c8030314181c4880f0f43d142940c45a0b09285030390405403440c0510450124042d1a0485824001290034290000108035902d0500c003900041c403160f16490848c15032070701d10f4080c0420b0482034a00a070303d003040400c07590b070340440c0c0d800740c40458100340d641e2a2501580b15002d05425040810a0000041440101076102c48100d2051a281d50104101286540c400055513102c100c3d500025060350b01075154404801d80e0148083d000070412450035a0341c1d034440f921 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 118884892 1107 118883785 118883801
    0x130c020a060b060c030301120506150d02120f010e01090515040b060603190504080a0305090a080301150320070b0a06030308010b070204021b0c01021203010302100f02070306 76
    0x6503880f007100302c0744003100f00d41c1038070b680e5a10381032030320050820040c04031b920380b0900c400030f21003102c503603220010a04000c0c200c01c40d5280c10b03002c10501c1d10788070362820350600a021070320007400001d2240c111004903460010458017000d003001c900b07104040c0c1404401228800812000420503030328264068001c0310019200e1305c42c440c43c1c10000303418040c0003202e645403000340424480f022000d418114516503091046590300c5425030784451105000904e0340d4010300050027544014402800c40c0c01e054640003925810008001603940702d51400000c0a4400280d00b001f07101c805801c0d5030740848020818800381c1c5c55650010b0008205116506003043d0100e4883e00715503c1c0c2d0111000ca51f04418040e901140788500c06445d04160b1504601500c641080403e150040f00c040da8103c0c0d400410a03c01c24280050980d00ea0101b600301e00c1c114000d034280400026200c0c451801 = true := by decide +kernel

theorem cover : BRFrame.Cov 118705035 118884892 := by
  have h0 := BRFrame.cov_init 118705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 118705035 ≤ n) (h2 : n < 118884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
