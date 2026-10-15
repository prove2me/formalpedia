-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4179
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:48:01.454744+00:00
-- url     : https://prove2.me/submissions/bd585657-cdbf-4c42-ac70-9395baad7a68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 751438848 ≤ n < 751618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 751440098 1250 751438848 751438871
    0x7030f1107230a0317040305040b13050103064a10090b040b0d0b1b070305030a2a050f1b1e01020307021b06040f0b030906010906030b010312030f 64
    0x82d00301d000002d40086001e090020304001000c100c0711030702c0c0c1c1c00d074803692148890280c4180101c2c0009204508200d010440460404012405002c06e03249a036070450040c0d04000c00035088680d960440c081780701704440d0039400c016122000820580801d0b280600d192945001c0c00b0803644540f43cbc0c02c544129540c1040152700807104508100c0d1100c034018800e02c00150248411500d04214180c0c00c170704070750f0004020404114800d80c000601c5190500030300310000340d2107139980016001314001040002407103084178982c001da50358619150381c0c0c16441c021030948502400b614465480c00e002c0b01241c6902c100c1d220702c065481c0200c42d98003243c2000c50303610742d83d07440c0c4d05074844c0113030203100070081c08549070414800c4d2480380b460394008198440510502d490407003e5080480c0e4451030402000c0b0380c082008203100000c1511449007600d03401c0c0030500d90304000058100f804414501359041004c0f9060751502c90449401030105440301200038000c402800400c009408201c4c140049542c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 751441348 1250 751440098 751440113
    0x60902070812010e01121407030203012409020f1c15120302060f01061209050a0203121201140a050904140610170601180b0a030f0f0605060d0b07030f1107 68
    0x42c03107003001c09034240c0c0e21906103410b005401e003d400714010108811a00140c1b0041d080e50b0f035a00c5041c2216141d9590f81d0000f42958110702251600e000041d1f40c41e88600d040d005c24a000c7e01801e4425820b01201e8405081e55006a08051a55000035880b100181c0055402840029036070700c0d03490310b40c5456101c10309107030100c40381c00c81c012711840000646031465000c03014142c82c0ba0342d0b00c1924601c20702032401c0183c0380025040c1d0301402061001801a5402c0010f10111240301c14010345811307030380f440c9074030402c0d05074425000c403030820784511141e42e05c020101d0f003502e4044603d042c1640b0fa900304002c615000c8650720201d0b11465090003400003100240e60100c8004108601c050080301e1700d10390712541c0a10681c21400c85480429084070b0719a0002007541c04041d1944129660300d459241c14050008015980d00c80c0c0c4008580500246000b000d0344544141e03079445001a60b036444102c0e0100042c180f8081541d5140100000c1400d900040039803105030b040c090312132629003420278 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 751442598 1250 751441348 751441357
    0x171c080618042003151807090f05160212041206020405091e070f091403031210091406010c020904060b181005190b1305100e13050c0d09060609020708 66
    0x42203424034039954042c5140000700c2c01100d00c80c8004100c00394039281d946e19501b650110100d80c6501071110040b5424401c0c0c820031009110294010a56003061510701000142c005180340071034004075003114020103c40102d50449c0e82d440d03845002480c0d0350030204000d0203a07030800c60b4000d5001d010301c03d4a14014943c6100011900d1060402d80c541c0d000c1546c0782001d14141402041c0e41c1c01c0100031828017295804005080502901d2a04910304825110b1200403291500d500000b1341042c40320107154032441d0401c51655000346102d040810010341554000380c8024841d8402d8000a0200601600b1180d032201c0042d05c242144003001001500c0ba05040715041100c0c010703554006810306c1c1014030030690a441c4c2820040881c1402100402030380800c0310780901070b20316900010540c4558103e11a21800c9a82c1c03544104200c1c4200200c00150340688007019040c0014042d00c40104004c035403914804020000d44050320349400c00c0504101d900040106201150113030a00101200070b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 751443848 1250 751442598 751442633
    0x22030b070e06130b070807020934120c020705040e010207060b1c031214040b0405061f1e03080f03010509010e13030813020a08010204171c08061804 65
    0x40c1c5042056081c070009010b4540050680803103040104001300c44940105103140c000d00707006282c0507007074010030350241043d658100099141501c82c0c04440fa1034800c81001000745c02d1a0469140c01c620040c03d2213400d0001100c2c40e42c1d900209014280200200c0c0000d20014005000c0500c42c149518002e4008030f00980d01e080c2818114045440c0100802c0305841d1041c64450030001c0d55181115102c0707443e400180f0391a9680364840c0f4654090f079a00e440313540f00b029001800d06d003a00d011420668090b2240180f518401c0300da5916080f0080c1020a8a40b01000700000719000705108025070125400a042c0719800105550004240001981079034002c2e0f59005e07250740e03100c040d840117801c11101035148014941b82c1900185c1b240149035088083c0c00f805840c0b01d0701c80d07000a14003456960200c0c4103070398001410810200f80382030304018001040041d2000c1c2107401100b401e000011031898007040107c00000d0190350700d0300c0c9102101e09100340849850301d4985080c0fa000c06d04801308 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 751445098 1250 751443848 751443857
    0x71707020f16050a09021b01020c0a030e03010917220b1801021209130609020307120c030b031005070207120602071104091a07030f090c03140f030f22030b07 69
    0x20300c0b42c4051048041126000f914160030f440c681001c1c00d0007501701106149078540c24501e100b004242c2400039104400b0003601401141c0072515019191102540c6010b00990519040c0c001043c00741200004024100c2c012903581c5007030001440d0750941111401d2144084840003040010350320000d080704280040c201d101c05448030b4016641d82c0841103440b1107900e0200140d02e074505107109200114a60004003080103034444600c1d00a0340c00c1210001c000403c0d84019200d400341030302401c0c0030300e4842c0c1400c01030741e90750ba03002ca074031080c90b60f0408005546500100c1c1c50144200203060003000380081d5001d003074905192481c060340c88004c090303c403015594100c3e03410b40b80c07910580b07a000394007a030380710103625240414802104d0010040b10605076035100c40020340703200c0d0003080b540398451410364120f24114a03200300c00340c2c114041903000e0b90200b640103000788e2002084580098080d00d00c292203400e950022500e804078041000641d5044107030000c104886101340718021419070304c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 751446348 1250 751445098 751445113
    0x180303020c1c0b13080906030a0c0e0406080a031115040b040c060f0e040f090b0106171b0901110703080d0e01050f330a0b0304020907050c0303040b071707020f 70
    0x11428220b141c1404094035220852010804510680302c1c0700c54414801e211050a0401c030000087c40e6410444521103c585c0ba165008100c5610030002200001c0441d0f00f080700c01c0c10082c81550311407501310024140701c82242078403090541002984e0110b100407000d5445071400d8a8a01c064a90541b8103c03640c00e40c065000c9441c07170154100103005003c0d3355804e16a450b12100300030280030207441041150780d5510300000440c03110307230b003ea001e031803652103c4040d0b102c000480014050020603000304101301c441d1590000b1140003c8074400e410918085e809001c4c1010840c2c28601c15610051101307200040486035034245400c6030000503c40070081099659080c2c1903591a041181d0381041c01c0c144264002c090b2101901c207405130151f42d041d0307c044000050100e4111901c1c1d80141c3e00780003011007000118a442c2c04825488040343c030301181440c02c0480c0311070b901d0001034002048103088000040c80540f240100f40030403003640145602508144001035100e80c201c42c14183d49003e0400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 751447598 1250 751446348 751446379
    0x150c0215030601020604080702220c140903030313140105010303122a050f040e010b070506010f06170a02070506100911120a0e0f100b010201060f030b16180303020c 72
    0x10107880c85000103030050440c0f550340c1e5441404070340c85070f41d041ba44010700781c00840c001c1a101c00003200e0b200036030000140325802c6071030280003e0300c00700950030180400c019400840e10048240c0790032031020001041d0300142071824140b00140b203000c040040d8607180000041c598050002103650f00701c004204441010389080054400d04007128039925883d00a030641501d1080340180751284030200005d0800707841d00c0660b05405401e86c00402070000206011081c00014080540144403d840c2035004c14a0920040e00e12590540e59185c070b04400d40000c0c0c0d145100d501180c806640c08000e4030010300e01000c03421401c00042c050072004c2843c3c4941e40107000080400c0b10520007102c0700c4071079075680f2120910302400382640c00412900803909100c002c103008002062092030038040200f00c442e0705400083c03c462603944041070440c650b01d0100085040c1d00201070700f042644148000c1e0011922007514021910364411030b603000d695400100741075021812500c4000104e9000e4010307070880 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 751448848 1250 751447598 751447639
    0xa1703070503160302040504060b13062d0311070b09010e010e0a060f09381504150f081e012a0e03030d0b0f0406030b01050d0c150c02 59
    0x440e0361002094040000c80c0b403071084803500032141074140c0340c058071b006c0d00c42011500b5107202e64404482d10300c020803040001c03500610310300e000d01810324240c10f40c002100c040300d500585061000e4010b10240b00d036803500900c2500300d0581c40d17004445155459660385030640c01884100c541d05913a51070920300c0210f0400600440310760039012401019110900c0c0c440c0d2000303181172400d121003503a481c2041c0c0005001c0601c2c510b4480b4542c000c40b41c2c243c0707540c4610000d2050344400d8588950007481002818089019914501e080940b00020035209500e1160b2003005142c10003e50181d4102c40011500000a0b0369801002000c03288555a028800d81c2801d0381c00c1c070344540221168031090074602580c1200300e0009900c59280404a00c580040420f0460f448001204001c61701c8054002540c02e04684030039004d40c05540400116207143c8586542660601499200303680030200102440741145210f000f400704504000e40c100446900900310f003410035070890103240706140a0340840f111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 751450098 1250 751448848 751448851
    0xb0301050106091a0c06070206061216060305041b1e05040902183d2106020a0309080409060503070b07110114071218120302071e080607020a1703 64
    0x2039116611100d040c11340048110700c100c00b4007a00d0500a0100098140f81005a907000340300d590007402043c04c1113014001e0140c0e1031078400490742e010380d1054150a03081180c02c41212054030700022152900d00d8a114142c07904144544541486000402d4002c0400c1c000303940380203a441070404866a85052005a406240b000396012a003803841d500103281d00c0301050352249088805502001591184c041c2100c00d1240c1c40c2c1103441c46100d20119261520f00c00300150901060360803d004d0b130720030b00240d42c0944c0388004004070340200315a20494001d402082c801d41d40442e0302074440ba1502940c2000b00420321500c0d03c01d2040c11400503200b1400d008552055420040400c910f194410041d03d60b00e4100b0b14480100400300590030119071901d81c407108444503a40d800800d0698500c4030004001d103a000400c000780004c0e940740000380c0000e107a004032514056509810016000c08026004540c2d10541e454052102002031180c0d0201d040d800c4e0354071803d04052010a10327501e54030607010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 751451348 1250 751450098 751450109
    0x50a080127020a0b0301061d0103110a0e0f03150a050c0903030d0902031018020a14060d05041b0305030c1209100c240204050310090320120a09050102010b03010501 72
    0x30721070144500544400345022040d001400c03650040307680355110820741d40240d100c103000500d98020004011041d212905020900740780c18401801c0045c0000c405103d65598a024000520301c801d10944a0102210b01c8407801000c4e6a0080690300380c3d07602150003124000c500a00e001e0002e00200360a0041d40c3d103801c0302030000c0d07091801e4034011800500000302d00780e90521908201e200815030b20301a1081c40b01c01c50320401e80e032110030310520034200d40781d400100202101c5450102d040d02c845d0107480c14510034400108098555090100300c5401c1446140e0700c0304043d08000c42845000001441103410400c01c035412085108200300c07150241205e802d601c15039540410384900d20484014030814007810040d10285410704c80d4162216070f0030740488801d900420104580e250074851308410021551062281405c0c41da00100040c111070140d0950081c8121280b844140c1000425400e52402030f144e85d071860414070280c4503000d030b440313080e00542c00c000715800c1034101801641e04890 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 751452598 1250 751451348 751451381
    0x803030403081906150e0306190b1215070f050c060f07031b0e03011a030c120a0602040e10061e0e13110409060b0432030a0c050a0801 59
    0x8460341d0381142c5010014080c0508000742c3c002a0b50780c84028400e0380018444203250503428120f408004d0009204040c1040c0b00390802020000031040e04003082c020006001c2c0009980301401e00003c1905111030070514032031083d401003600652204c5d034914010a956203c40d010240072140032503d03449680c3d100c1100790045400720728101c0200300c900e500300305641004540030548441c007880700c10001e010346000645c1c0c00f1040b4058102172007515000000454072844051802011a660f0445007021900a11221044607030030902480f4541d855a405003096682d0b580d6090100d00b40341c8207540d640614201180c000031054040c168031000038072181d020a00d9001683c4007a5030096404440a401a0349802e2601201c4503902c1200c040e0200040031a880703038105000482119181c2e0454094043c0c00c210a10254400c90f80076840034402c071120040c60aa03080911074114840c88984da0544641e01e6240200600601c00354140d0340103075a000c0d885a03540c2d6030302342030b41d4a031440f561415 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 751453848 1250 751452598 751452601
    0x1e08091003110c150a0204030c0302060703020a0b0a0b030c010f1d03071e090f0608070e0a02120108010b0f01021b0f04090b01081c080618041506060f0207080601080303 74
    0x50030a03034095200c020103401c1c0050030401405582440358081c450003012500049020045007408041007500109070420071070405081d03503600045841e2500010303126080214204041610030800310400369807060b200c0c5c1207400d181100801402040c0b200a100b070058007a0242194400c0007121121100f80e41c0b04d050015403580c1d50b8203500c7e0b285540715050700420401150440081d0a802d035403001c158422031b505850244400c0c100d55462811492042c1401d404120070100000d074138054420002000b8101e48031502000700078483c041c1311082007220710000150010f011f41c003200c00d60005807100c440b2188003800480e00d0380008050500040844c20220b075090610303d04a0080c0d2801820008500500b034450741d11002099116804e030394424401c001121055003000000c1c0380c96400d1450860400200140320741c0c4000241d50220600c500c001401c0c00303c01b800c1244a140c14560802945859090007403004203014508005803103030301e03000581010000703a00c50403100441d0185045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 751455098 1250 751453848 751453867
    0x60703051306050a060b0a09060306080a050a0b09010e1902040b010926012307094104050f060109050a0f050607140f0715080609040311101401031e08 66
    0x1850050900130500c1e503102e0010400302c43e024010940d0704881d803901003081d40b800c900101070303603c950030080c2503801055600b0000760000a501c24183d0b403024101226039140000c00d401091744081200c1c840c4645103810300e903000c08016658840f8000c1c0e80038044500c443c00150759401041c49248080c803015148100e030b03412840170302c1459035070600021031070070341c0206040d21000c5034041e0641004402c500307000380b4a400610290082010150406e04803209000e1044841c9800210700f0002100c05444100e020080c2400d405400c00240200050b04007066101401242104e84e1804101408004150b52600205950031550f00d0300501d2440790a01c802e010300c58005e904115921541e10415400307404091081351641e000500c003e22010b45482412845c1c0310700d0416644c1480928024000309856040082c2d40c402e8150030000d00c2c00c2c0251303421502c0d15643d00880c44500c2c1c50016404a40e90010190070704803401101000c2800746146207091a4184040d80101002d100f0032000c00d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 751456348 1250 751455098 751455101
    0x9070e01030b0f0402030c0901090e0405030a0e120d1d04020c0a020d0606030512190e0913080c011103090c01030b011d1306031b0918080706111308060703051306 71
    0x4a401003e44030304a600b40780e40c0410280d030000d4903044050000815215480d591206110b4010118015102070a0a0545501d03440740b044032444000c02c2a60926604c094499100b22545603800300122140442e80c20001003800d42c4800040540b00c44496249441c1e18040c001d40d041c0880323200140c007200e00c0a40c00c1141b030241e8194200d51041c0c6807840080481c40c24002200000381c88062030380e603488c5401c042c0400c46805560b001c1400101810b1203030382c0c3c4560080c0c1d940070300c15604840307e0910380d00b800103860003030103c10601d66003400b03280d030030241804002d140982c0320744088030300e010040c80041d8156040c07414158005a4414030388110f00464440305042244050042c025000c48103a941c0e0075611150019140c504100c03609d01c1d22200d0201c0004024001014204160240c94011304454685501c008d8103203000440c15405116080c0d015a80207000d410205640305800c01c035000301c491162050340316a0080c42d0000d50307154068000c0502c11031031005455503034540c6564160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 751457598 1250 751456348 751456361
    0xb0408150901151203032307390b0a0606230d181509152a0801230a090f0f141017030316112a09070e0103 47
    0x30319920395000f44000d20b082c0d070002c0003500d04201030b42e640c0c000c01e04000c0c099913503203000e00d00e00091122038400b00c802c007182e5130354010030b403480d0140d51032004c2020131490b00241c5140c078501c44007003000520101c0f204000f00c48030500c252224121aa5150121000c5808900c071310404a4400003001c0e48640030b4802000210070142d00003410505c10841503001c40340195008859004c00205c01e605101041030000940c00f250541401404842e50364554810446030010044503141e540e00c9012407103900152010844580b0680d00e0341075032840041050000384100d8040d81ea030740780503d011582107824155042405800303150758a2820794220001c02420300c10030349081d83c034840d0313042e1011107000342440b007041c0c06c080802c01e0610122010240c5d95a0380720040345503011021003c079860203c1a0790f41300c0c03009542802e81c1c4441a805a0349140710003011000c0b8003428003211101101d2581040d01c8810004058660b00e405c0428400400030a03100720010034039100c00207880398400e80015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 751458848 1250 751457598 751457611
    0x30711030a0b090d0e030a030e0f060409110904050606040e01060c14010f0c1202040602100209030307050a03110709180b070e03070609090b03012711150309070b040815 74
    0x86000300e8142d20340c0e01c0c40c80b0080d600c41580790008800e69401a900103101ca9400d00c04401520140c03100355009052920310881103030141c0341703284005907580c1c0d070001690000c0c40c03819030600192421002618003039120303030110b502c911310300404600c503401c100741910140c03011582907807203c2c1d00700802076800500079001119210510000c0b8240c0c08020b00500001c46078400003c01c00c50100070014100d42c10302482400b05034414801006000c4c3e000405019504440c600140d03180c81e00c2c00480d0540c0704403d40506035110340b848030f5042680c84449000c590031000141d4495540302d2049005031030070b108038a0590120f122181000c1105004502d4000d00a400c01450402c4c40380003090902c0b0465019001003045580100005c80890181101d9810114020000396880d00c1c0360030489202c80d654840203a500c0d2000008101500d0050046004020840f2038030956020741c0f40003c2c1d104880c56100e501880c134002a51592000655007070302c4000340908060361000c90840114000144172 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 751460098 1250 751458848 751458853
    0x80610051c1e0b1006050a1704020418031709010903080627074b0c080304080903010b0901080309120c060a051306051e030712050c041d0903071103 65
    0x140c2403094890840e002c101c9106644054492418106a40a58800394800000d100041107018519980804e020f4101040202c161015841c2c41c0003040080c451111103240954800301c2034001c0c95042180c502d118003140080841507a42c0100d1142640d01111004000c40c3e25900031500303d2800e00180031030764035000500118003c40d140400c0c0111011303a00300020507140c2d10000040701494414003001d805407022481c01d000d402464150340c0206400b2500007504041c00038450340d21807a800310020b500f02ca0401e0b140e0503d400d15801640c00000f510b44250300c1d00b40d070761486041642c0d040e0f040324030200145080c81403420510048001000a0b00f101d802460031415a030383c0c60a015041c00852940c51507210f03840c0342c0140c0800c0085400c032506210302401803480b1080c003142105010319954001c1c80d01c0fa120b9202c26550a50000b503a0300165081c0805c0042141c100b80c09002152042071424000c1508410620070702ca0080d560b500094008001c1b030400302c0c1d0030440a40c12400301404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 751461348 1250 751460098 751460123
    0x6270209040501060e040b0603040506041113020c010f0e0c181504021809060108090604171207031a0109030c050f031920060a120b011215080610051c 66
    0x6085500c00d0b0044e402050b040104400b041c1880d01c60702e505c407007040c1c4006156007803e0702c980c0d0751444010401000c01c00780c0c2000040d00d84a043c1c0340c1120100300e61056440d400c0820125010300480c0e07a42541040c5015021a03081c50005901342e442d02c400340a21081c90884031984090600081c444200ac3c1480e0009004035159840105540903002444402448040080201800700586418100038a0209115404001050880c3c00591010240000790700007800014240a0355840240340c1100c201045421901034001510f0f50030080300d80c680c500d10703241c015a420380346400080c121024108044c00b050814000c0d210382c926008007181e40d4145110524002203045034003c45031a00314001d0086440c00f1200700c5081502c0490f10386081c0403002d6070081c20b50300c0d40d08420b454103444800030701c0725900481c1882c1d01503904013010b01641e09007800b00c5c481e00d815442900958420200020303042a50848801c041d1a001841444200980f42083c1ea00b07090400b025681c0c281501e6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 751462598 1250 751461348 751461367
    0x7020c0109062001060512010b09060a06120905011527270606050306072003040e040b1b04060c11040c020d0f05160f0323032a040b190201062702 64
    0x10074468407c00e0480022581c500c4690a11540020180043e4050300d00403e05100180e00201b0304449442100000250700704030381040c1c0d0150480200d228940d031106a00070a9060740001404044e11004120a5003a130440641c2403c403140c140c0105805100c0c400c40c5502d010488804101142c020306002c1079560319140040d0610701c040d124500410a04c081c84452440c41110315a43c1e40b0f40728002d1030a00749842d807424009407005000504c040c0f40d0100107560924660f0f158840c4801c402c400c04e882d96102c580c00340c80410002020b1311a4240d0f0401c3d0342c81d9103058000c4031001d203001d41c05041d2004260360182d40303405000601e002889402d20004640b4600604000d0155014452203510074609003409425400c1c241c180c1880f4484c0142c8a42070380d219441121b400c000101c00f40d0140800c20305002078000080c144044c0740a90000e400900c181c42c801c05000380c0c28041ea1034002003507104c04141d08075801840303a280b1541e55007259840b0780c0e11552800c0c1302508501c0c0054034016012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 751463848 1250 751462598 751462609
    0x22b050d021801020f010b0d0201030f09060504080c150c0d020a0207080105040302010f0501091a0609010201062102090606120f101508040302160305152d07020c01090620010605 78
    0x1181014050250074681c00644e130410014514900980c000c12800d582e8a012406c80018140080d050503183c01d0210407211503544512a41130f0098410801402d1503d09110f450b0700000200d8554816004501c00c4020200300030390168503c9000d0700d181038000c2c0c88031006034100c0303400642540a84400000c50180030300501d8401c80c480e60000490000c05443c04085802c117800080c4000e1804060344050b041c0c4c03400220390000d0441e242c6d6103800340303c0c0040340075000304c1d000400c5c0c3c0e5a1a0061404105d85000c41514085c402c80c2e83c0000b981d41d113810300085003d4100c0d01c006003011040411040c201041c403503900711110900d200c03d0240c4680c0060040301e100c440580c00180d90404000916a052140032005d000d00303043c0820052a5486003940c5640d41c07260b4031118405c940200b011503000203150020541031916a6120f01e010404407014070004451820241c014800100c00c0c640c440c01403c425a030641e11148458541a81011a01400343c40110400d41d83c0301030208495407003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 751465098 1250 751463848 751463857
    0x50126222009070801050d170408010f200a140702360115090b0310090e06070207061713050a05010f0e0c0f01080c280905040c022b050d02 61
    0x500c000320341c40d212544244484814010b01d400200000c441c01030000340c0c1d940c50b0100390b00360040c0d03410900c8405626440d40c144a81d80c02171301190319144103040842c030640c010710321054a0349040d40c07214100c000c00713508500c1182e28034000a82981000f030469000345025112907800604242c6100ba0400070210580d040803412151807120f0004821b0058400c05110780501ba00000b01d82c00b141c00c244010305212003034007946407600d50100c00a054800c0c0c440c040303001004005401d0003048040b048035525128207441e41c10050084810120320329000b060480c130b55403603288140e051551100d00c1a071403c041003c0864443c022050b001e40824001d0041c0c42500c018400c0c00a546468040e00a00d004402c030301107070040d004500540040c0c0e0300600003d6111526415060344e071041742c114251000da00c1a148080100000c807142043e9a01481000075100d06883c1080300310303030940007a0f80d1110801c2083c41079089191454900c4070141340c80c0d0080560a044c000d00308482c480b0620240d030013 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 751466348 1250 751465098 751465133
    0x308040e041e0b2a1303021203070c120302010207050d03060f06080618220309030c050108040c2c011202090f0702030307030b06090907020705012622 66
    0x50303034240014415001004048010901000340742c1e05110740d01d26541c594010102441601000e00c40c1142204070742c15041d40002c400d44495613009071189142c2d0b00e03030303803404140e0180d0007004902451a00c000121144181c000d40343d15502c516005020f440041c0c02842141195003d1129000182c81000500310500740c2d9100840c216041c202010f54420180d481507040280e030b4020321940d48c072042c00c483c40c0f8690311410880540e546101140c080c14144560307000c8082501d05a809060740f11250506a0340718042031200c880d034070001100d00380010395000d000149403000402c150540519078007508440032880c40005240301d0703078003603075450300b40e2001c10400ba52800c41001c5140c00c0c0b2005902000005400b15a07051015000707507640030052007441415910800d009a03580d545054400402008005001d00d14181344020340703501e0144284c1d4082070344200504100d5a04d550302140c0045183e0450300169240e4020111300c9502c511142c80190f0109048030200303103001c03a034102100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 751467598 1250 751466348 751466369
    0x70303060302090a021e030711070e010e13021e0102120d1b03020c0a110a0f06030c0f050f07032006010806150102010b0121330b070803010605030907030804 69
    0x81c6140140034595000034032401c211803040084480146100281d0201c3c001071980c126141e599144041d03d4004440351220070074850003000144000003444864143d8000700c1c04030031030b40c441e9298109107091040000b580409030701460003c0e001481c000504884d414030450f00140030f8092010b250b54405525a804192250b5404081d0b826901c0b251140290307a00c2d003149000d191180c4541c840140311801080c1c43e0728011039514559400490f030780504544128540419a1204040c00400340c0840a0300030405510b0400c007800d018100391410b80ca082c070340c031528000c6266004c686007000824598031044250b0952801d68408011050203044904024202400c15200c02481d82001860303070f50440e07061030010203450741e20a10a5003d030814151141103000b11555560103003805256003401c40034040300d0083e000000c40081c81341101f0f8000301c1510701d40c8076400040e040c0700314200602440c20400040203954851801964846000e2040d69911a03c9545d14000c42c0d020341c0c418402e12 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 751468848 1250 751467598 751467611
    0x7020705030f0303130f0501061503020309160506180a0909030201050402032505091302030a0302070501171e09030d020c0304030204050f041502030601051605060702060c0c1b0a0b070303 82
    0x3800c081005602c0580c040c0002c40c1189080c0380e04040381c0801c60f1004000c02d091504120410100350040c80c094030010441c40304030b0b01031900090080d0800c4881c0742051094508502d011040e001402003074030405000c461400d485c80c0d08103130181c5800801e05412682ca42000038049143e0320506a0641c842e0b030000c036903800e1a00400d0f25020f070442c000c201c500c00500c0784803110032480d40720400f01c0b402695a41c020782c0e10085100d00701070501d40040c2d050b0081001e10320406034040b072900306844098840070220860354403081c1c0c5002e01110485028a00004040d00c03101e00b1140c401e07440f101c14000c8a24000030a451001660000040e00d18075600218040c81145442d01a050b40650344000342c15651030301e41c0302c4a40014108144d02c41203a400808070310180d22910031614188817010240503011040e1500954400341290020014080c0002180300c038002e040490340d00c200d41e14010f000340700b0001402004061103101d41580900d603044005084142c90b030181044078000d8400081c80c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 751470098 1250 751468848 751468859
    0x31e1003080403050a2a0522090c050a060e03060406150305030c03030703050a0b03030723120705010b0406121b1706070f030615110304030b0c0c10051015031103070207 74
    0x49444c42c0c40e5485501d49001810982c0d07801c6c980c0540100eaa04076144103801c2c0580d84061640c4104842c20040c0c1410201040d0500c40c0c0b240d40c40c001c81c1c2c030a4403100045a07427039104540039044411450307415001540031401103007044e046074096210003400304840c59966078031135281d94010116207005400100030001c4d072541502c03800d0340c05541c101b418810440c012000035140e10402100409150b0b0041d0b10145040c000710801c0d40b54402081160704070b40041989440b16044024210703410342c2058800322503424203015090880d0b05036011508010020340c0c038589000c10f05101800c0280440c000001e08844e2082c0d1603502002c2c1001610442c10010f40041102c1d4004114809140c18100100a039100c500b910864050140c50b100c403025101002c0941548281d5001500c5030b810001032011100d030b48402483c60355210b0088030907101301c00020b50141c51049903c03844642443c441006101000c12078204120300f686400540300103507003c030302c002e41c00544003200107910401e411b000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 751471348 1250 751470098 751470113
    0xf06040506090d0807050d1506230708042c040606030312060f05010509060c070803040f0909080d0c110f1c020106050f010c0c030f0303021c02031e1003080403050a 72
    0x401440a03400703803200c0d40b03d100002d8034421340581280c0402800050700c12111847c2c0c0e101d60a0b0385400c20303030310702100d40c0d40c0d00013819030404d440304c07442c407192422103038400340e20a50484c0d0001d035004440c0b50400b441c0a000c0c12445c41c603c034501601c111041900a404030329480380b14801c511642001910a04500780105006096840181d04134a8041d05001d40c2842d2402601215000d181290381c414140d4003103412801042490741c140c0c4a40f50001c00e004c040880580140c4000e00050420309680d1003a0300700352418a0000350409504104108840d0055001910f410703500342000d045041da8032515501c0d00e20541c080d00000c1e045402c801c03c003101e201126081000e10362009010150600000580040e07107014454103000061609008020b4441c001a00454200d80f6411489081703040c0034010354440d080740b0310b20b603110414200113501980b0030703039000e1000040107003507458142c034403440314401c05420507200030096000080066403a000800245100d90080c0800b039086190030705 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 751472598 1250 751471348 751471351
    0xe010903060524012c01050f07060c2303010506030430080709030c0e1807122f0d0212100e010b030c010804030f120606031a03121b0705030f06040506 66
    0x1410054100b5158070010380c03850750721401651645d2003c41307000321580180d50900c200341c8039a03003210b004542d0350207000d080d600c000d20f00702454540100b0f1070586035900e100c5403003110340088441400d10040c070090030054051507100f88100c0e242030302e030703507541d03842035900d01010303024450f40b091148940c0e10150748005503503089511401d03c4014581160b0300d0003045600c0b80618201e01603030400080c21907451071086c00201e0780032029641080c1c2c45801c041500c6140d000155011602148104941805401035030103400318015084400420308080114000d00c8003010381c0e000c003003003500c074400c0d042c24000640c0000b0a1000001d500803030412050070f4600801e0310340d1083e040f4000c102c007145d800c0001541e229034549400320b80c002c1c10071004d5500040f0803086006440ca814004078078140c040e0300400e5034021103800030f04004104010103035591203082c0181c1011005200c4442004401c01c0d03e01c1c0350152010a54003941e0b01e68020a01e803843c0c040c80440c3d50381c02103003032000b4400180f0425 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 751473848 1250 751472598 751472671
    0x1014150712120b060d020d180506090c030a0b070f0c02190302010e0a150c060f15090e0601061e03020c341410030902030d0f110a120e0109030605 64
    0xf0700040340003500040d440e0003034007a40004a41c00003001c009280041e0300c21000c010103220f04000a01d8030781052680c0b0031040720741b800c00c7d1244107040c168501e40083d441443c1d9500101103c0c0d29030303410004840c401c1001c0e0300c020500c01c210f01c89500595803e644d5114050303018500003009450750000408224003c81c0703040c05500064020700c00c908050000d0395201c0706030b0030584070005a03403030454000c143c002d000c0c0c1a968a401c3c003c52070b016243c61504111001d405044c07080e0071a4120441d200c94003840740201040c607001030b41c8945402c0c11802030700381c450360074010b041c45031020700d0b14184200e2881030f01501100303110300d00c2110142c20808200c0d0016140b0f04184034109100001c0d40c01c11020890301ca00092401030514038400d0304a1010103034050240c030f0001c00d6940020304186000115040402c440754180854140c000800b42d811a41101d40c5130785000155a044c3c50b0400d144030410704005090b000840030482c1030140c80d0180e034184d40707950072070f03c9019074054000389180b028 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 751475098 1250 751473848 751473851
    0x31e03151203030a050717010603020301031a0709030b0c12010806091608070501031107120c030e01030c0e121204030f0b0a051e100909050c03070e101415071212 71
    0x2500d0841ca0004152030f80710700000f000084507100c1c2107099502c5141800c10000003595980007017455649071300a541201d10641c0844040e442403054a520343c1e0007180c003400064504c000400c0414503100c03800307410100d40b81c4a05d15145081c100702c00c60446c2600b10020303030343c8a0310a01500044c20014884c81407207111540c05028204003515484d03610070700c6940c2c10103071280c4a40f100030f41000d044805441c2d010041450303444204a0140950f59020029800f04003448400b0307520b940240200c0ca80d4560700d40e00d0f01d4214a0030810440c22810203000d00549109115602c141c2600440042000d140545640c4c44100304030b00d0203038003681006060766a4142490140407920503140c02c1a80400801045490696038000c030803451680c0c5a400400d246051000030414024049240d1116000c26019600803944aa80354105414140c0781030320496404c1904004180c1c0707540e00307003518400042c420707a035060019a851407203800003c4141c3d545117a840c00f501c1541c0e00f1030344400713141c040c0240 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 751476348 1250 751475098 751475119
    0x2010e10080108070b1e1e07030f03050a0606021f020415080f0123121c110712050a030c031b030f020f1f02090f060d06030b0f100512031e0315 63
    0x24442d138110201b005c0b08150f0401213501d00c80009000716042c1c0040751346243e180c903140142001440d91102212001c042854030004c41e0350701c1564010382d010f4405130b40042c00c80708142819488007070075074540068500d030701740400319640c6c515003940c2c01c00c00c0303407642c5499042c1800c604210b804d8406a101c0e0303030300c56503071903400010340c8520303c1d4401d1801c0e08440c01c080c440d81d04c07820315007094030306031800c4141c2c1d0b11003481650f4540c1081c20b11060b01c807540c040300c0c0c0003900c03070311080b5603158100c06c06422036000401c118002482014040c1002c4c2c840d19056440004c0c201603001c0040740c1c10011004600d0340e2200450041d070410006002e00c407002d00034410200300280740d02c08051440359601000e50001031f6415142c17195400b0115420300139003210781e904600610705000b09500e000c101d5010070100b0100708190800c01c8481d01038980403a9003005a0f1411042144043c0c4a000421481c0003d000414004182a9031041f01c43c4801012039600e2070a4401480c0d000402c0c000030380710340c4114a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 751477598 1250 751476348 751476367
    0x705070f0305071b090e010f0506030c0f150d020d180b0c0c0f060108030705060903180418050610031b080a080d0921020d08040f02040902010e10080108070b 69
    0x40350105100d40609082daa2403030f40381042c00c1d041a0703001410540c0404200005150101d6600007640c000e442c2008100c000f681090290550303100342c4065505500060245526240814600049034030007440c030500b40c1c1c44002a184c160308020b01404103540d02291011001c0a14010280b2019030044414100c8540d40c2e500c88507a88058010641c1c03d0000c00c50019816003000400c40c040d500300102e5400c0c2da503440c800c070713620f03409a40304442d68020340c8003007441c00100006807419040102d001c10800895a0107000007000c01112040302d0b070091141c81004120144141801811040390003583c03907040d8103180c0a03400074018919400141000704102c85103011510400b0594031109007030303650b1111014a0081c1036000b002800325404582d8007403842c01c80311500c0724000d000c1d4080c0d03880140307640b0b025100641c00b00c4026251a00300301a000c01803516600c80403106105050080220440101080380356200c004109c0226541c3c5c001405090000c0013110001c15413191080d18100200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 751478848 1250 751477598 751477613
    0xa05010f060e070813030504050d051f020f03010b210103080702090714070209092b0206060d0c05120129010206160c02100c02150d05130506070c0c0b03010902040806070507 76
    0x10141c0328100820034a100c10184142c08581c000c9c08000c0045014a001d414602c0c0c69001c03103612401113280e5400a45540c010368002d48041040c90114542182c1c49c0c02c2040c44141d0000c4c400e1003214210500e205090504003038414082d50041c101262034000510510110f039030080d00404c103100e407405071702c0301c1908020112102d580e416603003581551612100741c5e140c4508c040384000100420700d041d54002c004a01492070036502c03035003180d802d501d803142803100d686014880039011008031482070029080c02e101c070106c0403082c00c0000030340c042081e031034035081c030030142e00d4074908a64007861000300d40e070402105402402c811a105140128035070040d18440d0324020080c000d44000c42000c6c2c8103400340381d5201d50300d5000307451040250103400941c0c4081c0c5c440320710340c2402450310300031604195002c55420305a943c0600200003980b12000c041e00d004e0880720084511400c0c1e164040350010881000e54001c11001d180540c81c0d90516001c0d5040c000024240820403500781f1042021a488 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 751480098 1250 751478848 751478851
    0xa0501030326060d1e0f12030509210d0609020408070e1003122c041b09140a080a06020403050105010506070c06050d0212040302061b0a022a030a05010f060e0708 71
    0x100c0d030f00302d00b04078030380f0300640103440380204010398041034443e0308240322003048018401b600c40c101200b003144042070300380e003285c1c0b083e84c401c0d09035805242400c518980f0460050001042c446030f01d82001000703207000055480542240c2c02d640d0300850304001207201000808081d014070709144a99140c45a4602100702c031912000e8080d8045d4101129002d001c0c0548d00b91020b00850b604050581400200c1c3d114860030342694040c91074514020355040801c00410403484c900d6540701d6260f460b10443e00c40942c5001c2c000e55025128207030005000108102d00901544105070140c0c842d0329504000d42180c0f0140e02150086104001036000202d030700300c52106441080c2802034842c0d10700f0403420024014400340e000740080f00c100340070500d900010210301c0741021b495170030710882c1d5003210100ca0b805580410f07005030b40a141290100c4611001d900c40301788440000000120000780082d161400b0382000740d80d5a5925021150704c520030780503280282c002488121082d042450004182490 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 751481348 1250 751480098 751480111
    0x10e0a0b180a080a051608040509010e010e060904021207091a010503100b1804020412060f0e0d0318051c030e0d080604020a0e090a020912010509280b0a0501030326 72
    0x40010384003481300d00640c2550340007005402c0008900101d880c00640981c058010f00344a032848000000e440341c400d444080c166070507a0720320103403030f00ea010138415800c6003d8022a4000d6101001c01c9a048040065000030705007020003007056070508158050b0044c1d0160003034108503082003040700c0040130354100c00454007030004081c0d490704202c40d80c40614601c0d0342203550203030001500280c0c44084c000c4400d443d034000e44081100000702e003e03c000315038000e080442e084d044801101c0e4a64000c0e80482d1844d514040c01c280000d81c0c568915040505a40301e4800c0310100c0c051265501d940b51040c3d25901d4110340041c4445001c20002a006040090000380304940000c0d000e017050388102d2071880c4048000d480300e2040d04000380840b000e174010388012030060460110707030461804140247d500402042c0040c00548017200240c101144111a2100514400c00e409400003240800040c0c03042c940711800040550440c600142a585600c542100c40480b0318031202603541c255070a9500001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 751482598 1250 751481348 751481363
    0x80d1e2a0813050c151b06040314070501060302041416090e0f06030a170a0f0302070f0b340e010201090b06100c0c120308010f0308070b06040e010e0a0b180a 69
    0x80d40b034645940380c5245000a56001400018100030076038002c8058654880d44541c245192141c070140c0c40d599210407903015000840300000e2090706251100103112140c068000820100c0c2c0b2900401c040eaa208152080382c421034100700045150000c0c600300c0110300902e40016142d140c0700c2c0399008600058490a80000a00e0125103195420020310b000e40368028030008140c802e40c594250706070408030390600441d00c2e10340d110305098400c1c401c40d069075a0103101e0b00501c501d5130715103008004001f0640a01c0014000351440b2071387c031546007490400c001c0800801d442c035403488000c3c410f0061808403815681801410340c005501c1105290744888107660902e0003a24540e4101e50340c0c02401720140003005143e602098048074080350000a43c000d80301d41410782d903500581d2203103210307503c03000d130111400380608130000741c208200c1600442c00920110788030200b05499403c55045101c0a102c90b4000803484003040b581204503039124603040300d125110082d8800507600c2e00c200c00130081410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 751483848 1250 751482598 751482631
    0x7030503090f211006080321040507031e05070506250305090a03031106090304050108072d1112031005060304060906020307050301030c0b0f07080d1e2a08 68
    0xb5140c914114080c0100f103003180d100c00100038001c60b00c4012100011806074200207000c0b4606400000301c0710340e0807100940d414152282605004880b0001c0e104482d80c0c019543c000010840340401c40701c215001116103440101c0a2070304903e88200c030351100380541000d04c201004107003000b0002c0740b101c0d481120000005005e14080700c2e28030030000c03001d40c81140c1d40808004e0642c0004201c0c1c00100c42e1048609a071a400380440c4c2c1e038029032054034002440c440001c2c40e000d1040e00003003003064284101600180300d0b80d60340c18000140a201000003800040c0c580d40c09042002185100c0850302501c030b143d0f003060300c4c2d195a0180c59000342400f408001000c50100400c0750701003081250812011522420030800007055544284410f84014207040030100d96020300108030755101050031210f500d010555a504005500198a4045243c0e941d200e04080e43d5501030130101d800c0302640000424041040103102030f04880e1000507503c90252400010b8945c00c0000d10383c00c600494103544c0c41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 751485098 1250 751483848 751483879
    0x61e0405010908180a050603062d0d1a0a060b0a0507030e1309030f020706021005180105011401030614090109020310030501090812240111100204140f030703050309 72
    0x5030800c901c2c020100800000c04520440074040e0a5580e018201d504108481e952030030002c0c039010a40e241a440a00ba011800c010460145071000d4840e0159000402c5845840000c862944051040d28424200ca0174141c48040c148007050f8400b0f03040784200070350742c01c00311030381c0d101d004a100a00c00d2140c0018540b05050055051502010009000c0500d0b0f01c030b503070b500d1805014100c0045010606c3c00c03640844250002c01c2103000e48245a000b091b09228504003480686806810800d03060300b81000c070703202840c0078048d0780e000c0d03c4d54200030001c140b40d0b200018101c907c3d99124048258080ca40303854a03940f2130385510b04480b030b100030150f00e0b07896121602c0341000031540700400941ca40300e0410b04000c00440174000c8040110045003155441c85104c43c0000c046150180000c2000600c118096008102541011840340e0880e20a54148418142203070f03c0364000206108000314070305060302d00000e5034080020240c2c0600011480d555500703549000f4242e0281c48dc90f1000500d901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 751486348 1250 751485098 751485101
    0x120e060904020304050102040608013f020405090115051c020d02040213090903031104210821090c010302072f060f0703030f061a030c0f0c0706020d02061e040501 71
    0xd459200800071542c07801c0918040307000303502c140300303080c04aa0311f80f0000800f1143c101e100001d070801c0440c8074617161004018858180700e1044c5100700000c1843c8141c0140c0c0b01e0b485802e01c02c03d0f4a400000c0c0801413816144511615903104600c200c151b08051818080c1d802c1d481c44055506844141d60500700d03200140c068043d0307520508050000c2400040d420366550050060580651410420705d03240300c68843e51407003180219110b2000807403e07180ca8108034801280400e01070007075103050240c4001d6910002c96500f407411500e400a205100070401e051041140000c02400d045292410903916010b100e82002501e907451941b0600b140e103207440c1c0012842450720010901640d43c104000142000e400c0804250002441c2c038a1080075207110340b08080c280d4111040b0108041e5515036071401903403000700302c00040038043c4080c0b5a03645c0014083c0c8454442e180152403043d082000c02403910000302c60140455011500303105503120403200ea03074490582c0301c0d1120403e6445044c4a070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 751487598 1250 751486348 751486357
    0x60406170a0f021201140105040b16210f020c042a1211040306050a1103130305090406030c03030815010c06110909040c090605010c02060f0304020d0507120308090a120e06 75
    0x15606400000c124005040203070009040c6c0c4d40d40c0311030405802c0c0300380045603203015900946244100400050081466120703007221854800c4044c000c82d03410200400607894245500e21010400380d030254140c3c143c041c070400140e0780c0107440c10400000e5107042031102c2900e0122540c60740560700342803040c45100d0010800c0c8000304960900c440b081e54919040c07aa0b0040c4019540103250001003000c3c14080d000d000042d010080f0042e0849c0c0340c80118107900c100c0b02c0c04c110180a000c01250303000b91500d0140c00d0066010300e90001455182d420080c100403c01484446000e6070850044020380e04030503481c021540002000516501c01f040e2040d0620600285c0c650020140c02000704010880200005451644d80207120966a520056594401d03c11009501450030b10131080d00100d024051980a8002040a41042031541352242840055000490040b0303000d0b41d58002d240d00482c0840d0001300000080c40c58480686403650045010456042080448016050503948400544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 751488848 1250 751487598 751487621
    0x3060e0703080c0c10030b010e15040302040e030426070e04080408030c0d02011a01020a200d08120708013c0b070213050402130f1b0806030c060406170a 67
    0x495a9002101140d80c0e102c1c21000300c4d070f01c2201035000c0081450700c2030154075920b207010f8451810005080d07080160000307100d2505904d0120910002000da40e60340200c0c600c0c2109200a03640d550f092023100b03201803042d000b06004920705031114104c4000c0005002084a0380e41412000300d031154648031800344907036031081040e4800861009011100403d0380c00e0304010940007003090401c07880c00320110724540194240940c0101d4091070210325109004803070414181280080b02c0a480c0000e1004900034005850000c00800d895540301da2581c0d2803a040700322400c040c55a98502071051860007800b043e41d030540c1500d5014803414120300181c03051440142000340c14900e031075800c003809a030000407090340724444011220130007103030034481c40c0d01558025115090003a840c590310703400b07459058400c000d1a41d4842c1c804d600700d0030120851031401e5031992803814500380315041510f0302d20520000c0b407203580104401c0101e9500304002c1c0d80580c0e0241c004c1240c6549098030712009001d20403d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 751490098 1250 751488848 751488863
    0x15090a060c11060f010b0405090a0f09030203042c0601110c09011e091b0c03020a050102160b0a060b1b0703120201090320120d0209040603060608070504090c03060e0703 74
    0x662042503003000c4a0b940075094a4100c41059640620080c00440701b031050102080c0100406e01031f900b00172900b02d900520054011440003880410316049819000c03080d00183c0010034180801040c05421194020340355044603807240021000d2041c0c0d880190209062041c46101000d504200744111070840400078a19011580d40344411940c102401801074112144480301098800b0700307100d00203101c0c50280f01c0d40030800d0444000d4a070a072200d00141d0951040c40704607800100709000800c011491010a54903150840ca803540003004082c0c071a035512401d041051120000ca0b10070f9409030310f5455509070517403411200076801c10415401c050300840c1400c0701d1003001901504061744543c881c3d659803287c40820643e2200c1142c500007007a47c180c200811030108034600381c001d0301600351007000041c40c00501200050840715540d2003180c5003074a0303840820820906010010041500742c07400c0c440441030707907a001440549070200900c025500d4840700551310041190001659000c0d18 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 751491348 1250 751490098 751490111
    0x51305060f150603130305091503151003050f0411060403050105090f0f0a0c12060e06040515010801090213022104080d0c090506030a05180a0f0215070515090a06 71
    0x4035002001000c940c9440c0c100803610310a00d26041940481c0c0c445c4400900c1c0788840712035582e04a070680d00a030041c4d070b84075030300c0f5074000d0088003890015402007865200c12121028290140030100011303010740300078107140100300112220308001c0c1e194020382c094115900301d008140054424042c94202a10a618140412500c288000b56030440d010b070340000c40355490181e0103005d0303440000d070a0042071074141c03040412108440700014200f0750b2041d000482c07010282c4450038a0400100d806072000c0c1d0108501c0311075401e84480183c05000b103c1d00904c08034949801195030400309050b442002c550018410601a401c0221408000b06009800540b41060305140c0d0b440d4005803c1442c0e9540740c0381c0040691802a4070307150440d04080e0480b0b0840c0d880003200e0001380001880d49241440c6892540702c800c10521150141c1e83c824803003007110342043d0050100801d40c041c623080c00c200080201c0700100d200041c10300644201003074943c0b8965504501d0074100348004000400460074500d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 751492598 1250 751491348 751491361
    0xf0a0f1508060a050c0c0a0303181205090a0801150b070c0509041412120408091504080d0809031e03040611190201051e061c0c03060606110a080d05130506 68
    0xa602c1e806080300314814041030700c0d548441a11481107801000155101804400002e8002d4000810b20b100d00030680b00040480d84800b0481c0720444000d900141001821030b51230315120f08498080d0107078070020080b001d941003840e5000c0000740120f14070020f02040040070000d10505500c05050003070104141d50419141000504d40380e2440c0251034015038941d0001003491800341c034020000e19891140c151215255411640d02032942a60450111780c40801c4109550009000915000d0300070000c5950750700d802003078160041c00c008204d13041008880c000200c5284004405802008a640d403900c071440d03c0402810300e0b1140f00641300780451b161300a5a684100800c206009400a0109a584e4020400120079940001a800f140003020405500382000c2030120f41480b840c00c48442c44480c3c8441ea0340d50003552046a03e1354541e5014082e099000e04a128403104160051059088030355174001280184811300d0155a9190b000440080c0c140003c1001e40e500074054032554100398 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 751493848 1250 751492598 751492603
    0x60102300d1b030902030a0311010b220e070f051203120a090c080c090406050601210605030c100507030503270109060b060c03070b070519090501020c0103050f0a0f1508 74
    0x10042840148100c2105902c54042e00444c10156401000b41201d81071a680c10348461005a644101540d80d030b445062007521540c4455010031001180b082c1d0103034100d1131580a942080882c0e0001360801c0c0380401080c61441c00b403c0c203550007110207654450580008525502801c41001a4100b030382091020800351035005030a41da024000760300cc6a511040c40541d1210311003401600050b9000012780441c0e0964490b80d00180c0506d08005101581d2a1701031018218031071308000c0e103036215810802440c041244400815041c0e03500d0b502500d1208000d0001d0241d00070203814408004001011540608003581200c100e1041c4007904986101c90503008044941088604a14010042c20180340c01d0b0142c0c1c0300c0c80032b100700451410110b5036481d035040e00003801c8031007030003401d0000c0800c00e00707003200c101d5840c0020f03038900005600d410002481d1014600307a240c181490041803102c076181e03140745143d01500d080804120000c51404040013410701d0441c2c0c20b5494005103000c1902c1c0c030f01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 751495098 1250 751493848 751493861
    0xb0315012607032a140405030d110105090105060d0f05070b030a0c0f02030910030b0a0e09060a110a0503060904031403160206090106050d1e020303031306050a05060102300d 76
    0x290381c100542c50001d0a000140c0c0300138440b80600e110820140c0410512410b400c440000f071185035942883e80e181c0100307240c0085480210089030350114400f91010f000d209159100f543e2400912090800b0000700c0c5449500c80341c042d0841000780301d80024403900b04212001480840040ca5a0b46000b0b00364000401e4451b45c1107000605e4a00728400c1d00344000161003010400504541c0380304901c110540041203441d5003160414032502c0c0c00625104c2c41d089c020300c2464404040c207254a042c04c0e00d001114070548007500310300001d000f508400383c1d1210a40380c2c0064280c2d94217403e0344460800744d644030300790070510465900010400076500d40599400012440c50380031103a42e9110090540d0036a1102d0094980140341380000d04003051030104000d1207905452810001c055490300400e043d0762003210040b098625038040b0404100f441d205c2c0e650f00c90341d00c80741000b40341440c900003500d9075140120043c07124401c9000140d220b907076440c0d002803248806280c0c0da0342c0028841d04800b4088 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 751496348 1250 751495098 751495111
    0x30717010b0901050108070c15020d020a0f05040b090402280207140307033311040f0603090218070e130e061605220510180f0b03150126 60
    0x70600070305000d0502d0300955041c0c8030140c454100e180d44080381180c1d002c2d5140402e460081c000304001b50403501e24030040400e0360f440d40b80903a0341c54105801800407030b1041125010468104000c00200c4859004d5440f015805c07100903a072030958080d41d048881001c042111403107040d01c0f212240c150000f40240898503010820461a02400308050701c84081c0d1001034000020501481e80c10200086803155083c403040c13a10b019134480400c0242140c40c41601c1e4a8012000141440310f00003d400400050040d440d06014002c41c81d808642e2000d2010098980f0703003034200120340354a0045070041e0f200e1001030807074134a04201c84604000b51625440c14040c0e805440045200e28880200040c1d0002040c0c84140c40d00a9100303034111070459103030500a075080c1085010070546e40308030b19031311801c07456558441660000740b0f0135006041e29602c9500007401c1810200400c40405091700d40c00902c00154000c8500904016291245880710445c19640111a841813100c0d080c0c0e402c5000f46c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 751497598 1250 751496348 751496351
    0xf0c020616060c23031b0309060103030206131e080d0911040b0d0c060804110a0815011e090b0f0307030c1a0a1b020411040603091406070e01080408040503071701 71
    0x100c03600303c00e5446240c405903c0070910030100301444e860f0a508021034000c40c02880e014410b200806054841d904169030500140c0c10880041040c543d040002540006255041c218005240da41c3c110020701e00d400390914100a00c446c0b001800728400c141c410301c01c1201c02c1071100084078034010700312010050005100d1441c041c004030003402e0020740c02c1090f81d440b1000041c43c90030308005a81000d0001c02c2120f04113200098440b96840e1241a0b00040a440004004000300700d05100c1c65030340d0503041078420a090608110b00101e000400710112090005e00080341742401021404c81c4041a0045070103102d41d000c008100300c15002140d0440f02400d071a4070600300070452030321040c4501c4117441c000507403041c0190000000b804180d0745880c0700810008a40c6000003020345550440d0384400c0100786c0ea0340c2d0316028888100410945036880c2c20103052a480c048202900c4400d2402d2201d0403c010f040c001030400581c84220f03006084e0060445026542e9080ca20f030803520307000403020955 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 751498848 1250 751497598 751497611
    0x61d100f110d0c080f0c10020a0f0c0b180c0307080d08010905010b0a0e06090d0b150922050307242306010e0d020d0c030614010806010302010f0c02061606 68
    0x2030201091a00030041e1640c2d40030340001c3c542d01da030b101a0700003c1149401550410a080d800242041014907034001d40c3d80150311a90b1400c0050b02a86004a51000303120350880d6103000580b401c070205501c006800c41c80005118a0505185000c100000c000c1c0c151017005808221001c0000398041076003403071340d030b0f00b101d0381e17241c10200c000d44000b0300c1201d0a6400c14010f02120340d0051a20215035800a80004d082141c41c200044a410642c00c01f40c0303985100c1c00c1413001c04200745000303a62401046e83e8211030fa0038000c55030b5140411070401c03c0c80c01211403c1c03e200700041032080301d210703036004002d40304150b07007401102104118200040f480b49181c0305501070301141d805201c1b4240785005081891940e180e10066502041090b030590f4422482c0c140500140d4820010000a60242000940840c00d510b803070412105400060707111400c5034001040071510014005054a5080c6043e0b80360410828003502c0c0c504210500a41c0241c001c41d0b0580d071503041c249000a824054103040c02368 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 751500098 1250 751498848 751498877
    0x140109140a0501110a0e0d1e0b060f1504030228031b05040b0d060b01180b0309060601032c03041703130e090d03021308011e0c0305060604061d100f 65
    0x14170914400f4000b051421000c007005e4030306404583e9503070340900c003055000703110340c464607070300402c41c0200301d607121030000034842c1c0340c2080a10035034043d00650342c440e00c4460600e204810307030007144002072003500d031040c82c2c40c40c1500404400318416052140c0010703164032440c0a03404040e10305484010088110700006051809003d55030301e805028002005407509510745202802c15030540d0380c1408440c100406000844810001c02846402c80481d20790a11140c00b504185000d80034504250a00c0450240840c40003c034051042d1141243c01008081c100180d00354001c560003020030548560001d51004400300041280d0f00c1c44007148407840e500d03156110700c983d40588151034258011079090800f0740c020385c000c011120490303100078030090380e0300c1c111800e4a18110340358245001c80085451880704501071101030f05060308080c0722034980580415618011840765800f0072018041c4010244c028408031005804003030302440e50740b00300b928003920b00d03a416a095070010b070f0742c050840310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 751501348 1250 751500098 751500131
    0xf041a03011b020c1c060216080412050c06040e010b071a100e06030a05070501031521140109020315071704030908121905070503130906031502090904140109140a0501 73
    0x40540c400690017005010f13841d02c00094212255060303140c1c0380500e00d1400304040d540600000c0030a100d072090004140c1c07030102d06048103604458043d910501042c00000b035116011411b46654194947d242c4405080115034807610194812000400b203080c0704164050b1404201990ba160380c4007101ea499050506580f00904000030307100d6000000180308562003504110541550400001d421989801240d4841d042c0042c13941c80c54803003c4162001c0040c00110500c003440341400800c82c107200da170042600d50200029908032004514001441036008881c3d0441813648040000028503045c83d018191000c2c0340502c100c03c0c0705082c0180301c0000c0390303000c80315061451080060188209001a1420341004030101c079240004d2121112074200c03070400d007005000c4007501141d0549103007450914a0f0200c0d0449140c6401002000328a44504ca2560f8215034400c10312412250342c95882c03401410305c0f61004040744803c4840361040040020001040740c0078500811024040f850388a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 751502598 1250 751501348 751501369
    0xf010e03160f0f06170105010e03210a030606020a2109090e06090f03040305071a120c0405040f060326090a12060b0a03030903030f1e02010e060705090f041a03011b020c 74
    0x202410701740184201d502c29400c1e01007041014041380c00c1c0800c0032100b400b10104441300f20103e40380102d0004101c983c98015900201060700141000c441f0b1502c2d82c034004480c401c21041181101121403824038496040b0744020310b1450410803080000c18001d985591080d5425a824440e1031010203000c1004001c440c00c482d8400300a2000b2440e00071710a036143b40e0b0507010340840740d0034060390f5035000c4031180076403207240d49080700740c2d4450808080204449000c200a16000c0c504032082c07002401c80d1018011024410010b00112001e182130355400b0700c507545c50982c00414206000940708401d103c101141889500240506481c2400740706001c10148400340c0014417114007000440d000700c80c0354041c41c15914201060b0003d2040c1103004003000043d020061395a49140320414806104c107940114442c60014036107049000040e4201c084441e1051045989032000d0621080449030140804c0c400741c0240311510312000740c507c400c1c80d551391100141c060b40a02003107529080380c425 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 751503848 1250 751502598 751502627
    0x90f0609061204080d0c1e0306030b06010503190c090314010b09130507030210110f01060e07030b0402041509240c0b041b032607020f010e03160f0f06 66
    0x1030514200c0002e0580c0c0042c003800c1600c400408100200582c0c2d070328016100c07091802d442d1011700040d6454402c00207009400c1120415251032010f10000d005103c4098000209280c215101c3d1101d5030b04522020000e0700c10044589001c030291032035600310401c001128007846907080c7d91603102c2e2000d826108240d585c16400108503000550300c4104207819007250b4003c0c011105101c4d00c9902040d15514031681c2c00c804110070392514040c00804202c10800c06610030000c7c05407a207044504040400d01500c0710b020b06854940e0b0480a0b00c580c0d040e0340c010312410201086140140c14090003422450041000f00c036030282c8603591001400c4407110700f01006949950b1501440d07260a2304200c40038100b1249030000c144c121b61407045018903070016500401103911800580012000c0c10365508013161041c040911021025944200510302444020700b06010320745030100001e8107040d44403840e8941c84196510119030184100403400580d0341d103451511a0036100c10040d56405002c0121 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 751505098 1250 751503848 751503859
    0x120c1e1e211503030c15290409020321073009080a06020904020705060718060f050904051e0c0403050c01030b0d1103120c030c06010e040201080106030c140f090f0609 73
    0x1000028461804550040e0081c01d84601d55041d0340b40ca003042d247d1807a140700d007840c0107400c3c0040e2450380103451902541d04a07802c00a103ea142e0109031580004082c1c03a010018080b00004511800c0017207910b41d942c08801403e076000c20301c0c21001c8030042d1210b00e00d1052400d0220041582c0a00c010700c0079148000020300081c92256210f03806503001d40d2074503030016000e1103a000020000c0143e240280b480d034445140c00301400103c186414503580c8070104110210841c01c0f48146c0000c11641d41c4070701a540414550b4030510717140ba0a840d03d00c280c0c03070068054400c00c06403224403009403050300d00c00c10540708090014801102561002c1490304d034813003400400800002c490030420f12600d00041c2c29600744110049451545410090101002d0b800008139481e00140034445540034000300071600c0954241178000070701068050213180f003490750b40c0c0c1c1c1d014040d6001c1c00841da003040c99400e059513200c5980300c022401c1d4004007a2180986031812120907640b03400400d583ca0080007808 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 751506348 1250 751505098 751505141
    0x31c1b0311030c030c120906060909010b060901050702120a0f051002090109050f040b04020a030b120601030b06010c0c0803041715190f060e010806010501120c1e1e21 73
    0x141d0303080991010b4050008002c2c00c200c8a028000806c005600c101d554001404241ca0082d050114a810080c0179400356450300c030a11035160b85002c252000114286000c1e6151019072001c1002e0300c1c910b070140c22807403040c4100c960400401d200c136400c040f4410300030ba400b4104d4110742e1070241d010310b4441074082000c6040900960400e803140d0642402c0c0240041070b00c9040c000810201e900401d04600001c4e05c50807039020030304110340d1201405002100074402903245440342403407c0d00c0139002c0350411801640c0c650600110070b82e0740c0041c003000c1d01030300c0d6160751754400c007000900c0e00105440039001d410f0000a00980e0410420b1044d010080480c0c62850b690240030001c142e2281c460802c50794620000c940490040396090103040444014811541000d0000d440c0b940c1d9240c44a0b4014100059907000e940d01c0034900110740136903400042252039801b82510004062103541d852804041d40c8000419030040e60104001340c1192200e0544035019050380c1500d00d1420603181c64000384a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 751507598 1250 751506348 751506361
    0x809100503070f211a030c060306060d0b0d1709041404030221040f030501061409190504080909100303030c11071404022106090a0e190302031c1b031103 67
    0x2c901115854010040c00c0d400400d42029411039002240401170142d0700038264500b401d017000b28810142c0e088440b2411464014000781c0039100f100200c6040301c0c2c6a0380d031a82d16440b08106121001c0d8480074000584203800c0104506070007000c4250b00ca14200b490701c0c00c240300402d040c0c41c000e5415070b000d040c2240744000c03200d12851110854514004040000254070012030b400303040690301c141300109000c0c2c17425070500d0a043c0c0c005000d40c81380183c3d00070710184030031040c02d500c071100c1c107140040342c40d07595420035907000c0c00f446461a8001134000100b003005074802c06d8000550f44252010070408260303803000c94500074541010341c0c96501041003800850030a40340b070421a08010405881d02e2000316050b40f94903074060122800c800b100c8207020701483c080e030001e5032240f102c0400304580310f034401856035181c10f0303034014210a041802d030f007409061003402190038404107160003009070346600e20400010118002008401c02140b489032203442c2c0700f40607181800c0d030400302240c21b644800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 751508848 1250 751507598 751507607
    0x20d0513110f1f0908010c0504180902040b06070f0c0f080c04090c080d02100c0f1b0303060e0907030606090c090e070519050c0607030c120903030e0a0809100503070f 73
    0x28010030350f100020030303418192000b03244050b84500c0101d6495481c11443d0044030303030a4405070766013442407180901c000c1c401c02454020200c03400e4009030340400d1007050f42c00807a001700440344031150010400101c102c24070904040f100c40032482143c80920442d620000d03a0303422941c0c1c3c01003000755001280b0740081c81c540354202c1ca250900641c10211201d03912100c00f072a0216000050015070011004011240194032442c883d18006042011149004100050100307104001203078000132080c92130424944a5803240e400780c502e41c401e000d00790500b100b15603a1004e0900c0200c403110b0500c1000b148440f030700e01543d80203139110340764841541e0500d4014992440010070610401c00f041c0201c240d900c010001e1020b039408640c42c0c040d65601c10302c2e0400c0c101480180101e00345400c00c0781e020b40d019070100c1c2c00e000d03910030110000740003502c40c0341c110050540c1d400240401d205008000701402040e00c001c1540c04002c5984028100c10500d00784c940707000c12540100804d40c500c40440046005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 751510098 1250 751508848 751508869
    0x60e010c0203030d0504210f12050a0f0e160605041a1b032134050903030f13051806040f02070605070f02160e062103030109020d051311 60
    0x40590b070400420b0032071351048410031a0309460910890300414419242011200360001c442d2420038900b891341807000d07061001051503074503240e0b61500011160101644010000100e01000740720b80c0d40b10558056031680c41039907400c20303c0b500c05000a0642d02031411941102c0103180d40d440304050080c00010288c00014100c003145070f004003c07040c0480c042c40100505a0105500c2c83c015101040075a4007402c0248416082283c4940d0560311040e48001300d944c10b80d01500144002150301e00c01c4a03607004d5400d0a0750188000300e80c110406a80b10050200f103410031440d01c07072107560780d0200034002d42c0381726500c4405640000482c07420308241d040294100e11803040917241450030b540710b0088400c00c9511781c0005291490322000d840e818009501381006600c0c10003115810407501c100030400203061075100d82c0704409550a44402c0c0380100380303501d40460603251250b80d5031a0040203580201510300e041440d0400252452800320000b20046420881e180d21b44072190081c404c0c8001c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 751511348 1250 751510098 751510103
    0xb01021e07120b0f060609030c10110d05030405010506100507060506011808060a0509030a020c091003050a08030a0b03010908030601051c1109012a17070b010608071701060e010c 78
    0x103400008a515a68000b000b0320091207184042c1c501c0c90404000c0314407410160989100340300401480045540c000f03449181c00c002222044e5403000e40e103605039514a840034038800c00d8019031904900b100d400c00051881240903800900241d6606c108104e071098208138481c01140041c00400301180c0303c0d60041c0d41c03109060401c2c0080182c0e2070000d141c0f200c02948810400e41c480410040703652124010300d43c01c0b118600040d41003090344e20002e521500a00709907801040c10030000b80f11108038075000070003580c0040c241c48809200e414407290591041f07401c40550760502c9200340103800e05104020101d608640b1003400d44e1503c20046030654401c602d44a032030321400c21688080002c5100e4800c03600c0c10320f41080d6407281484009080c1040b4072032026402c1c1e00002064010076059401c044c0301d1948244000300d01d462401c00b00203940a110030142002907210000301d580d0350860b00d20750044181c1c2c0c6480f900703240c1c3e40715240b034112824010741d800a29507100c0c0140d554000c00001041741c2c23 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 751512598 1250 751511348 751511353
    0x230a081b0412060b15040b131a03160206010f090507020c21010b0d02030601050103110c0616080108010e1027061505030a0f020f06160c0906090b01021e 67
    0x2080601400d1940058104442c24120a10000100070316032180b00c001490540d9000741d121700c0b280f2086643e01403881105036000780044c0e6072050018840408014244601e082e00481c012081101c0d01608100d942c548128001c9141d007013604c1c0000f406604072803407041c00d40311240c01e091480e070140201500c40000d500c201c000d4002641d80d0300081003603211202d40710400d50342a0b080c2081c00c1d100303010801c0303014174800944d0501584000c00e0380380c1510028280031031881196010410b40380302d03203d080d4405004240500a500185580201040700a81d4446a1f20b0b42c885000b6400c88600310102e10880e03000e03240000391200c41d0f411a5102805410001000e2100c04811003107950300030034110707002c2e6a034807910880070ba030031510100a41420b6004240806142c0d8690305c0700501c0c000068400c02c0d6000ca03900455075508220b4090170511001c11450801d2403400d00340f407141500454800c0d9080141c0480d581d4001e110307241035000140e008082c540c010566040040c400400c402d406030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 751513848 1250 751512598 751512631
    0x11d01170c1011030703020a0309050d0f0b0c070f05060402040c1103181210021c182a08010203090609030a1b0c0b0a181202060423040516230a08 64
    0x144090025058946c040d4014181c9a0315a240042441000781c001c80d11541625411901160024450302c80c02c0394010398020142d1a4a540c03591140590540106148075050200c010080c0205030300340242c2c4240d400b40240c440011050782c060848600c00030455005011000381c2682450302c03040700d400090400200c2609a000e01c078140f64150112039226900000c40181184003d0942915161041e030100400010790390494801c0e010940013038046180c1042a40c244264100104100c0c01c01c070f00e0309421280c1c3d40c2d890701d001c3e41046034900d155014100001300c11920120498121203000d51742c03106c005c0c034603544900d2046807402060b01c803051610808140a00030700010b100705c940c83d482e091540c00c01008403504059013904001c1c085138504080000507291030781904e0035100c00f1886034034107100010005500c4442d84440c1e03a8054240414420003100c0703035501603400c0e490f9a03a011600e07004100e110b2a190745200c6540703017207942044011255031250b10481d070071004594043d0082d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 751515098 1250 751513848 751513877
    0x16140303100342140c1b061315020405030d03060914160c0312060801140901021e07020f1f0908031606020705070801091a330612011d01170c10 63
    0x202c1307001c4905900360000026102c3c201000300801054a010a000500881c50184c2404001c8400711000408080c03050b244035107440c1e19501550007410000d0101da01484030200c0040c007606080c8109032a82c0d103816403035250481515002c51248010f812490b11051500300b0884406030075000507420449894050410441c50f0301554004100c0d80740042f420041c001074820341e0200c082d0841030f45030b00c100100c00d840b25140040185064004032020b071100c0e02030022404a14400b07060960003400a4510600110a0840240c0d0741d03c807591610140c1d611800c03400d990388070b0001c540003000341761081000000c4c2c06030000c10f02a1720a10035603c019503076010490a54803131503822110000b55041032401d1031031300d500340c075032055000b820014482422402c0c0702080d003803000009240034011280d11030940b00c140c1161103040240a800b4003e40e51010351011030b00441c2140042c0161074000010101c4241c00042080c03005400586181c3c210072081117807607002e00e06d500c010f0116200c05400e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 751516348 1250 751515098 751515131
    0xf08040c17010908070b180d08040f03090b0c070f0603020a0507060207141c0219030806100201110f091002010516030e070302060f091008010b16140303100342 70
    0x2814420300d1641b01e9402c02c048514030340c0111201c040902e5024400b40280e40d07922495081c0c00541100f0950000b03040d40c01c04443e80081030300700c0b804201e0005440100120001048006c0f2058981e484500a840d042c04400382c1c400c0001c500300003402070200c1c03404120541e0050480f144981003a50569580301621805c2001190381c5003090012401440c030943d405200f4441c2c01100782c694012482da203960086d20102c8060703d960b01961000d0903c00e8903034001d5014424030442c1c0c140094a814103801c2c010201c0d8046481603018014505061620380c2c014000d1600aa80d0f940136059000d030362480c214000d220035440c0d540244140782c000400758035403900400064003504a959941c901900c14016180045400b420400032840c004200140d001e00a864900414400e96140c2d80428101044030410b40b482a580d0307030100005000300442e0061507001203900c20310b08541880448024254002c22a82c0d114540304d044076801c50000d00d101c2600d10707514406c030400203a0100031420070344 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 751517598 1250 751516348 751516357
    0x1e0a021306050703021612031b0b0108010e1603080f030901090206030109091b03050607050705010b030f0705150c0a03052203061e0506280b0d020a0f08040c17010908 73
    0x40c04103400240351001c3c0340e411b020380025040c0c002840030400d450070308900d0741640300c4400541000102c208152020300c011100000143e040200d0600302c3d40c4810f6070310700825051007030b54010710407110f050071100800070049084a03000041d06003400c01d60200c0d4600c543c0014803582d001c2d5030b0382d000c0c800180d035500d02440c06001c00150001d07045010303180405404582d544ca01c00390004540080001480004045a00403420305d40507448007410725045024081901503990305014001900c00130706030000301c4004661080b9161600501d28002c041c15620861240002640280c01c20b140401c0c0900010504000c8890003001d05610304e0007018460000341d00100c0300c030381c0ca0310001c0e200401c0a41120b00d400c044058104500e0900c0c000140350b03020303028201c82c0c00707420b070310950301e04040c41070310710401001015a069038036062403090340002d5004c41c40b0f0300302084c04003070740c6911544240080d0f4410796000c040808113a080c02c2c2e03101c4a0446000361843c20750f4079100007800045840d4040d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 751518848 1250 751517598 751517609
    0x305060d30030b040e03070b0601050a12050103081801110705152511061312021504060f02190b070c060609020f04080708030304030503160c1e1a1e0a0213 68
    0xd2114100c1d0f0030041034410707080c00c038840c6a005011240c0822091201c0c02c0e04000300742030041d59904060300c1030b1a4001c0d00e64100303a005190200020622520380b00900484509000704108031035413200541d0703c0c4004044411031a882000207011904010b032214069003000103800e4180b061500b824000400c0c00301e09810003030442d000714810000c011030341540c0074408444a40c104000000e650f200f44805200d09528622146109402e54858075040340130344a4100350141e460b80c4608019010154110308070380103100d5940c681000d0b041004042c0041a40030a2007101503e030100b0456001003a06403d462031592070320700040120f050300c020480c1d034036080c000d15102d41c0b9140020b400d00c9820b41c000c0d041c64100704104800aa481011a58070003600c90300000400d1403114100d9000a004500401130300e041e19090f00702c0716440001c1031015200c4c40d05610351813400007d0030b103070240690b40668019000300c0e840d09200540b00111358090003911006003000391900d20701c4c2c5480c0c3d03290f011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 751520098 1250 751518848 751518851
    0x315060b0c0714131a0f010311090d06110f1323060d0e1b040f061a0a030917121006050a03230f0f010e04050a111c061b0305060d3003 59
    0x1780791941c1001c403038090070448242010010103480b55440a00e502c04c3c2c1881902c1a00d00c0b000307800030030441c0d91180d48980c1004100d2030b100c00400185034450391000100318040c154080000445041242522500444601c031001c4801000c40030300019401840384940d03000e444425842d03140f0b40400c01e03c021500245920b280c90041c41003031008643c5030b134002c02d100f00d00740607041c03003004125504412143c82102c2c6075561103082000c110010b04900c0e400070449040e0030011034864411a01519030003103802c3c0851034a480f0040782c144800550302c1020003007030091141d114458084d078004d000d42c40c0c1d001490700c10140d64094206400104607000074844201c44140544122004040c138090490103540300103608250b110542c1d203444403540102040700d880300c80d0044d601c54606110100000003220300c503800e51480d00c1c3d40038003078400c07140c0d500c052a80d012602c440d22074002d10b8003c0b40054840c10102c581c644070303000c04c0c034614117242100790072100040306202c2c95280c1480035141c0c0ea690 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 751521348 1250 751520098 751520141
    0x1107022e050307170f0403050c030f040b0a03060618050108100e180c030604170a0509040207050a0203121c020c0f060405070e0c032512060315060b0c071413 69
    0x600b10360400b4008001048954040245e8010f18502d1181c01035094100942c40f2401020100d28610076405543d061240101d0002110940d15019014142c0704d51014006151215000c0340e0f404070f825200c900d040000441044254016020b040e003040f806018200990303158406080c81803000e603105000500c41650310807003602c050194040701c510840240c009420140c0762401d0300031b01248140f400100c0064030250f060301a00403103104410151055496000c1030074030940350742a080041e4064012485c120300100103403c2154a402a9454201140c01c3e075007503003800941103038500c03184030721903400300c0d0140d01c10030044644141c2c4201c00402250f401c08c40300d400c0540001d0054041c01c0024020302c144041d440d401d1445104407442d501d0007800c0e148400303c807a0103031242c8806110f4074054012051041c0140b4910394840003c0050043c40e580d01c0f8074120502c03035a8110115604003c4080c1300e00010b501c0464901003000380f00c00c044011940582c002ca48414840c1031142c1a41d0350b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 751522598 1250 751521348 751521361
    0x30c05040f0b0108181507080402010201050c1606090203010204050a23100c020906041409030406030605090601020a02130908031905090111160c0f0b04080708011107022e0503 77
    0x151180400780150240300702624030001a01800c00a00751382000507000d0b0725183c241100700320103c10186440e0a80700c8905201130050558201075505034010b50070080041d240710002c1d021200b201d080c5200e01d42400c1700585680000b0500541d003240d00d95000c000c001034956608003c08080c0403080c03140c42c406542481400503031407500045038002d1240c3c1401d082e002e034005030419801501907400301c2c550387d9401b00280050410004000b0b443c001c0c0c006000480400101400c1070f542d041d00c040005039120b904000003910100c0d105401030303001040d69030040c1424103504040c981c0c45140451244ca99507200781c1c0d01d40048542c0c007005440761800300400b603414041c49070040105002000140e00311507010945d8884c6080e8030304181c52250800c010410441c0b01e000007030080201045090b07464200340c01315503005124000b01d5205440d00070403c0d00e018803500b5040c42c180810700d85001603a50130b0040d5030b00814401000070b9111944400b18045070300081280030f02c1c50752540c0e920314018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 751523848 1250 751522598 751522601
    0x50f15091611061f0e01060c1e051b030706090f1509080601120b0c0325090503010e010b09010806010e0106030b0609060d091e050601090b040219020105010302102d030213030c0504 79
    0xa0b07003c3d05e810985040100000d982104102090700c0d0040a03e42c0b0742d03e14000307080d03401801c00b40010824498000030345880e40000d021184858012001e41c6e0380c50395602c0c42110941c001c0c0c05205a00540e01c10100140225400d001d1035140140c00d0800c0055601c0309803c2c14040b090344200825501304001c08104020f2030402940084a100504d085050120401c0c00c0314011440d4440040c1d5600840d14595000d0590300c802850f00030700a02640008034981230181c0080801503000d0f0900a001203404140450f555051b80c100c032600141d5a80b038050304902402e0603445d45600920104102c50040d02e41100510011040f20702c0881c143c0d200346082145450b4660006480030324a1000c4000681c0204429045642c01400442c8a540c07620010b8001e00c00c66240710010000c01004014854064020034103e90080b5100d50190344840c206940c0b00b401e21046108101d805228001d81115150a402030190145401800c0c195100c040d9803a00117550401d80e540042c1600421191815 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 751525098 1250 751523848 751523911
    0x13020d0507051017040f1b030c0e0a06060f05130e01030303140603210c15040b0108061f0e151003021c060503120304030e0d0303050f1509161106 64
    0xf00c1c0b0f00340000328081d9101451400010308000c10f890a01c0c0d480b40d0501c041d94400c2e09140c10040d0141c3c500729aa451720301180e131017601c5041454000000080d540c000980b007101c0894126854401e66500c1c003010072200b552220072502400070071103101151180b08103003428085d5100c0d442c0040c3c11810040a00d0301c4581c020401c0b88641d000455140c140e440d1040e0302c0c0400070803000070b0354640d6075044100b828045152000d0f407140c50580108030500c045414681d048031284020b540c03c2d52100950985c0440446031004c181e07202a400400445140f40941684004150460312180061500280d40b2284020b00c40002075000309982840c6240300001d440c0388440c2060400c0810724000109485800041202414910206c00941418000c040d40640c0f8003008080ca04101142e02d00500209401d4600b545100d4490002482520082e200ea0388400c02c000c041d185c03140c0e641c998180781908481c042c0c40401c4401c182e01109820200a483d01400442c10007140701c3ca4040a4020709210 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 751526348 1250 751525098 751525129
    0x120f0a03080603210a110304081006061101020901140306030c0d030306091805060a0c02100c080a060603050415050a021b0604020f0303120106032c010614040606050f0313020d050705 80
    0x2088000684c500d41c40e4040320100c0c03c00c2d04100b01d51110a0142c03070700318000c0b0740c021805030040b078610141c83d008503408041916555250032290307001480c00d80d401c0f4010503a111b400300d500030f48a42d03560000e01001c1d55020400500311182d80072080d005c2442480903a108602203a21100d040c085038882c0d001e01040f2440c800e03103444035810103480d0107558503070241219189507900d030402c0e02180d100b4084001e40b942c0c40b1f0381c140300c44071600e00c0041c1010b070102c0c1d010001174500080030800a219000f0300340984e0708820710400382c0400242800080001804014000e5400c100004e400c030b1200e211102c01780305420140c5850724190040c02403180188880c01d00c00d800c104551302306160106107240c10b440140c900011880c040b1100d5030142e8a1400500740c180a400c4022991580150080420b84411405903100c1c440c1210034030050f0340c030b44e0240001140081c410700007503a500b40c001e5a40503009460801300780b011038010651903540a070043d115504401c00902007400c044945041c0c140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 751527598 1250 751526348 751526383
    0x510062c03010f0e1c080610021c18151e0e0d0b101401050d0905101409101b050306040624030507020c010c110103060e01080115120201020705120f0a03080603 70
    0x4007005c0018042d54009150603ca42c906082c520b50232442002030030003444100c0c0c0011314040c0e00ba5805001250101d03c1c0210346075903a0303c08120580311542c103808403402621342400e407081d03a6859811024041400000708840100021115540c3d074000b500300902408a07c0316030b09165842c124002074980081c00c1101e10680c080007540d9100e402c50300d00c0c03041c00d100024544c0c4246030aa0401d032041e01c00c0300205080c080c61542c2100340c3c2c0b449602032201801252058000801148107070f45c2101405041002d004c0342200d08240104019503003c8802000010702a40f0727281c08015020f42901c1081c0c4c601a0002480005a090f100725034101c9030b0760008009051070b240000346010541800202015040802e91119901a0300064050b002d95030381c10140f5a11400d040d8000c3c100c42d802c0808a15648070300007003498010040340d0056806a02030542c1c58108414003614a5480b003070b107415803060303003008084030906128031040948245d44890341418000101840d0085919100c4101e9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 751528848 1250 751527598 751527643
    0x11404030512070903080d0c0e03060903030114130908270d020f040b2806091401051c2405040c020703140307140609010510062c03010f0e 61
    0xc0e8020040d1003159090300c010360015950fa903403c4510b56501c5d44000c1c0040710220391704103610742580040d0ba0000131580c9158181c0980400c1540c0d4100585000303003150001c10052059540003512600c80c0040034141ca840000300707000260888012010981c0d050134081050740111a0b9400c0e0707046614601c080c6090440f19100000d4500c0030304c840e00030310601010128450540761600074100060008200d582c1d0b01c0040c1401d1001400c069403a002031f520b94a41c003144090090b014003040d10001a103616400c000c25005581c2907000e0b401c0140c104113800120300c20034010307001d041160310100c1003403181907017000c2c0003003130220380c0d604071522550610307411140803a4005030820889030082500d48030411248030b003034118030030101c000d840c280016250f061459800940c844c020940c0310020441c1d03982e01d820340d000305145400b0b000000703600b40d00d070408072000e0794004080004081e903000b0740b42c0160400213800c444c1c00e1003a140038282c407a44074a000040030b00c05c2040714000c03000d6070f4041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 751530098 1250 751528848 751528853
    0xd09140a03021005040c050424052205040519030203090108060f0d200d050109020909012a03020d0606030f060501020601050303091e0d053318121605011404 69
    0x218003845458103000f40e41c80000805000411700000001d1501030130800654141d4640001541c50021880881910024000074a400c020070110980c01003081c4406484141124040141c81c015000b80d45070302c140038003031408004181e040c41c140c07072080d001145d90341d94841c0094006140200764901c1040400400c4119845018000c5d208640c0030744004542c0402d40000403180002c0320a807a0030200780c403031407010484158040384110f4001c4039204865a00d040d4410b003600c40b900e880044500a20348109251280744810103464005810301508028583c01c00710b0440302d9982c043c40001e9103035160007810b28030038490b10f4040c0c80c0a00c040c100310742c10000800c0e500d01c24442e25500032061950444001c9540d51150506844010104264030711107081480e5600c414640f00c0c00c0000514044804032464966018030300880c940d50180c09903140400e01d0940c40c1a0314010303c1502444028500c5820600010804503c164800e046e82014a0030520300b1928500c5010710b0706001003050201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 751531348 1250 751530098 751530103
    0x4030503120a111c0c02070314011e0204050a030f03030e060a0c12050f0c0d061e031403030103050c01110120030a38010207081506040b06090f1309080d09140a0302 72
    0x140e504c4000c0780710b01002c0000c03494920158005414142001090072030a0019000f04c04074030b5038401000d0001001c01e0307000d0228461446960340c006100d04041000460b40502c3c402464021700b400079402d112188900c1c140b03001240c100b4002c40d50f40d11401c0314960000d160f088044050b0804000e603281c007034000e00c51104003503c0c5011a440106002c0c8030b041c1d89800100252540005540700c02d130311068200380c501c420307001c110381406811600340041a00001074a040b01e40000060a000d000c220040d15100042c28210341c0c95506c1d0060359640854180d248000b1134200c050695480c500007003000100e50711030300007400800f10030713105904e90320a20703520800392084448070a81807030002005071315000260748411944e010b0034007030600440718040464880c9505032021310031200e142040241c140f00304410303290700c600076652014560402e1082c043c01110f1031038002898881a480d6081640c01a0005041d42030715201001d041020011004c2912000400202541440c55130301a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 751532598 1250 751531348 751531387
    0xb0909190f0f050c12150303130b04090b030d0e0d06020405030312090c010f020c0f031f0b0319020607060b0321130602070b2b1a01090806060d061104030503120a11 72
    0x410700340034503d04d46c81030b0b40500031550040c81c0342002c50107295a840918800c0e8202c2c0c41849001c515040458469007004181c042d5051050740e160a041c1002100300305560045100a0390582e50a00c4041065182000201642c2c52480e080301b8013450494041850300400c01c40c5541001005c84445540e103400003115646050b040b10000302c6d462070b00f004245000a61910070705da45511001c641c0d44240c2960085040c103205805070b0f03040209582d0103d0301c50381d03100c1c0c0094008004201a102103809a03101144640e030003002d44a4446140034000d403000d028514001c203182000030441444120b43e60000c0041481d400540182481c1c490710300414012500c015602c41c40095540d082c40f9207075070306903580c060764400130844403860316158445d03405411030b5036010894840000c185c1d264005081031250b1070050079110341540603543c000c060480c0310b01c81000c02d04140000b200064080c00580b60f00c0e0320014055900c0e14010f00c0480c1500c1640c48501d08085041120300841191100c044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 751533848 1250 751532598 751532611
    0x70f02090a0e210d05070c0b0c030103120f090b0d02120a06030b0103030507080408010518010c080c0a030b03030909070810060c0f023102041404060b0909190f0f050c12 74
    0x103d41c00410b0b0102e0245485511480050140741c101008001c0e908038800821141c020000003038183e40700044064244030038040134056120002904107490b10a40701c08844035107502e040d02c0d41903aa00075180461304151204442c264010480c48010103000303003890391000c91044244001403071074680716138410060202408003c00010008184009407007150010074402d8000c000e10320342040c007010921140005c10600c0d509110280040c58800c0d01564000e0341c00c0300c2c4007490a05008000c1e0700420024140710b815000a0001d40c5203613a401054901c2001d03140c90f502d21b90f14001d011300d00c5d521015040103040c00043c2c0e00c00710110700710605400786982d0665039203000c0185892120b580242100c0e050540401e070114200000220790050021116421141030350355039801e0400040c1c890502030703c0c0f896081840402428545502c00c1d507080203004034800c51814185040030180d55803848104030850311804100e1641c1020300c00e2503030000d400010035081c400c0d0305a007241c02d60b0024101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 751535098 1250 751533848 751533883
    0x1081e010915090c0f03060212070e030c01050a140d0501050a120b04080904060b160605070c0b0a0207060204050d03020d020d0309020603130606120c031101020c03100e07030602070f02090a0e 84
    0x101410002541d241401400c0c01031703001d8006036a01d14016020754424030740c43c140a000da8001c1550305000c0c070045070380614000c024000c0c1c6440100112450b4001030b030400300304030702116400411001580100110380c2584404242c40d8100018030002c040315a00103a4561003d150b4000421101c600d1a50415440b80300b4607914407a410000f0040e104941241d100c0c0140003a8100050104944900720984200018003041c3d40700703081074404014a2902401260300720000804400ca50340c02071000030b114010050900e9240c8002c22109012a542240540c3c0030320880680a80c04120020402055180c24041180e480e0b01061980c0805000c0303040d5035034070300601010000306400c00c2c0007030103090b010f40c03815101604080344410254030050310350341c001828102c034135480402c0e502103007000503004191400407046200020700c1c000f000b03072500d80110303517000c03001411034001064101c0c0104080c6150141900400c101c411015040c142c04502d41020705150074004210380842e44440c080c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 751536348 1250 751535098 751535111
    0x3020f04050a090902010e030d0c030e1c03050301031a0105060d090f1e02130608060f180a140c010f020c0f04240807080a03050d0b010c0b01081e010915 67
    0x22140a801240c025a9102054100105800300194840003400e0300076030390700485041c40024152030f043c2d01c003600000180303650300b60380c007203070040c02505140100a4041d004001c0050781142482c074091008400184000004000748620307a8410761141c907940e96118210751604d4005030041c40342c6100e00219984400303a45050081244504ca0000d421101402071648214400607214800c0f8204030320a5117803030408071820220b4031401c01603400791b100504040d100e4001200150300b00170b00e02d00881101c0d8003800001e2409100e0144013a01c1105601000011244e2b0780d410001d54290042c1004038040f03414428035400200320400c20700503106141d032020b01030080780162960002041503a800d61031907a1000d084110744074100c528030402d5400b419181c01225881c0d000e03100b070243c00518240035500300e101c1154041d032500e02c0141002c03d2003580965800a054109074400b181a0304080c0c15610301000c100c1c25100c040e829000204103254199403560f49402c0c0070140d058034582e0b22078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 751537598 1250 751536348 751536367
    0x91008150a0213090c090909080a0e0d05030c0102070606140d03120f1a0a121a0c04090f061707050303072607060e1e0a030807020c2709030a050a0302 66
    0x2811600f4510007509510301241e2111100b0380544205609030000506400000641000031f2090100e001e0b030001403a464207401140c101c0e228400469a035611a42e5980c8003000644100010032501103103000240c1c80e5141400c041003204e080c0d6124511541ea03182d0000042da0b150922250000d0b418100b80c90429000c41502c40107080022192000c1d600d0003001a88441107500220b075200310840320100182d8651005081d03203814114010031804084d0744034040080c404003407540c080141d454007030a00742d8500715081520380150440c403a240e61417200784580135015041c611695000c81c000e0003d6882c01c40801d03901c0c0319200b4003400c4101c40483c841d0140d01800b0b8844200c1c02d0441e00300b80c44511504242c0000c165091402a0922908280d41c00e00d040e18144041c60707046400c0070b03183d404c0c1c940c0c80903142c0c43c00050034541103010b520181142a030b00c08108082c0c0141200d42c26409074000368030101c41c2d81024000440c06c3d030081c0407203030b000c1d5806800c4458207080e070314001d40c0b1a441030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 751538848 1250 751537598 751537601
    0x5060106031d100f0e0a05060906090f0703060c0c08041d062d1918050f0115050a030908040b0c15061c0c05101e09300501090c05091008150a 62
    0x45c54003030300741d00480d500401800700000780d0703d001d00c0400c02070b100140c079036401e21591075030f4240203c225034100600400205141d9880380600b6042c604044829010f540e1f15407440f54859000440e1500a4a5410768131400707412600b03a01103403d40c2da0401d400d0b460402c0c140f0649003181250107807100b50784218000c0c0c81c2d110f400346141d0001210300c2c0c900c1751284e11603018062442e022030401d40c038080009003c580008a814100c90005030315402c015940c1d80f00b204c641c0c1c01548001c0a2540b114012800102050010300c0100301989102d5240e502035210207080c1019207a0036429a0001c1e001e010441c0c1c0c40200c6039400c203d021500380c0034852940ba211030003030705540c0100c1e03000070315154212509400818010b403143c3e00c1898107041d12030b54001564039200d14040c50040e00d81080d00030702800d20b420300c4142c9003101c0c21112079200041e40d48060035500c88800403983d602c00b082d130030001c0d81414603c298101d00c41c001000081c505104410390340e0f244a00d078090440c0c00070004101742140c90b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 751540098 1250 751538848 751538861
    0x9071d0a0308030f06030d1d0904140d05190203120105090601110a030314160f0302090102121309140112030e01110a0f020918030d0e07050d05060106031d100f 70
    0x40b242c41902c92610b04901400c0300c0045510034000c5c0100c88245e444503121b07a800603044a010355012001020410521005480c020021556000e85c280309004104003085200c180700704a43d00c80e580c0d42555031400e403480d110200c82e902035500901c40940700d442c000d1001c81c1940c07010b80380c650a542d02d460049404442504000086d070041d601d8200500d64543c02c14160078031100c82031001030311591299288820904000c3c4006103060f09c0005526209400814070104144110340315038100307100782070f650344c03007440e203a540c1080d0f4890400c065103440c01000601200b0b211045d0f015031400340311070341d4925210382c02820000400b400350070b07603030090707801c0d0015080358011100035441c02c2c6001003100c050b211040e4420142d520018008442101c810911030b08148003543c1032240d51146500940301031030140001c1d008049011483d911202049190a8081d00c002c004c81d516041000e07084428000c90858030952500d1031500c814000945806000b9006100007000002c11075880f00401c0c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 751541348 1250 751540098 751540103
    0x8122205061c05060d110103360b010801020301030816020a17030c01050105060901050a0e030a2f011701050607030903060606090303031a01020607050f251109071d0a03 74
    0xc012602d1840c00700c41038110400c81408020401081d15030200f040030849403404010400303811011101c0e2294400c0d00110004030f036411282042d014004440300906110421002014100703d00010030300ca40d0380e8a0340d0041c48240002c500e1035065803140250391040e0a441c00821030f0f203411080841d110548102c005000120000901c1b0001405160b2690b2008101c205039609000c004502482c00d08116100d011050b100c0602d03207810f01c0c00c19203000c001001d140764107000c1d130400040444d074201710450040703080c1d1700d40c1c880204041105400310030713494100d14100111950400c000c2600c000b01541035610403a40941c5480366483d08031341c51565904010b01083c200307600007604540010000e0160703413080c1c5003401907081203022060411038000307000780181d02940206003000d0094000b40b0105440d01e07822460000d004580e40340d40c2c010468181402041420144248400c912421441900444e01a00c0780e05010b03400400b0700c00c4482040e00042c002c410700480590b1031030588401540e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 751542598 1250 751541348 751541359
    0x10e0603040c0b210702010b010801151b06020c0706080112030806060d060603020910030203130b06150a200f060f090a0204050f180d0c0b18061003060608122205 71
    0x81944c0184941e581c030fa010004440c8404070b01040400b40103000c3c4054194040e9a5014240e00e845551107007800318205071000c0c40300c42e12158180440900b02089454040c1d140503076503141c0041400d143c20304683c4204100071000b00103221106240342c0f00b01e40c0d150075140010940c0c4418002400c5441105110f10340b25190400024140381c16070050503441004503004092001d0081d815400d9120407107900344100d02d1264010001408a10017a400080c00380c41001030541e0010140c5e41603000c000c0040120328049038484506802d2018110051440c0028250f42007101c0222503641002030900c014032080311001800c00c00003000803450301c2c0e07001001480b850604c0041d0b01401c1206550000c0103e0b548072902480c0c2400080040341b2680507030354148144056100ea56a88001070059032a40301000b07441c06020004015860186140e101c4025070b0528501e8070808542d480c1c1c0c0a00c40d160002948402e0340d6400e801500c02d142410181c1d0812401181c1070407082c6c4070503800c850b9200 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 751543848 1250 751542598 751542607
    0x1d0c09010314070c0b0603010b0303160618060b033c0f0d0503061c20150c0c040b0405160c051002120a110712051b100b040f0605010e0603040c0b 64
    0x1e9070000024070b00c617000710b0505402e511000249404e0354828120a90564010045080c40302e404922090303400f4040c40300090009000c140c454046840a041a20711135100c1c40c84441900d014400d020902442240074400c221150b21081c40f61030580125072003200c0c0c00c0782d00041b00c1d0014400304800300e00c10001d8a02c49400d864015120f84c006580342030048a1104c00841000d00c401c202e0101c282c0c0008840f4041c050039540c0f0300344410180b81141d00001c5107aa0030481c224030741d01401400c00d44001400104502100340401c94074242142d0b44142d06060a10103031000c0544694000c50041c60b251480b01100c1c00d1651070001ca40042600351880001d5003000c01800d4048a40100c0ca5540c050040002c1e01c202001d05000c0d13031070b01400d4032040283c5030840c07500600090030150140c40b05090302c000d0301040706080034501d0701c40103a0381d030300d8405003451440c0600c1240c3c4c0c4480c0310350003001001d0415000912000030004014004d900010200e0207212101c0b04035030003011010009543c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 751545098 1250 751543848 751543861
    0xa03060302100f14071a1902040e0a0c0e130f0914010b13060605040b0702120d0f17040506010312120c181403060a020a17100305071d0c09010314 64
    0x42c0000c2030740d081c001404da4443c01801c0240da01281c407550340004001c80e65140541c145480340c6005082c5032042103410758030154822450000d407000785003400464803030380ba103401d01005650707060000400700203501884805907902c501000200b05000d90001071005001c8020000420b01e04001070940805003c050308441d405400880c100d200c103854103140d508440310b114058410501a0b00f010035000c0c4000e010080070980a4111140002e04010400c0b11541d83c990500301000400c0c80080d80d00c0b500c50000642000d464a00028807105602d1a0314058840325120fa0060000070030481d0400000d2116910403503941c1106070043c102085411072060300500400c201286915145511090008498151607a00346040001074054071300784da41c0e0350150b0b000b503024074109814004041c0d10a00030608900e542c1d4869500b44562016050a5007030251400c20954803010fa10011402030304c10030f148261400d42c00000034903504c0c3e01e030600140107902402180d40c041d8140340040040100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 751546348 1250 751545098 751545107
    0x70b0f1605062d07080c071406090c03030a02031c0e030a03060303180602060f0916060e0a1202150c01060308030901050a1401080a020d0c051f09140f060a0306030210 73
    0x1a210810011880c0d0000b03480c000e0780403450401800c0700f42059000074044500869000740c1c0444240d12062034030100b0b55841101042c10b0401c0c0c58a58040800c02041c10000c01c0b481508038001c0307008508012090b28000d58a01c1500700c1a88240c5200d0042c03000b07941c042d001040c01039503000903a80c59844200b0014028000d41c4002d0f00020740610814031103001d840c6e02401594042da010344160340d250008071480a4002c2d05035242446004840d807a520156444440a440c86903038014010714400104a14034500380c01000c41e8003042d10314000140e8840607485410783c5040110350300d036004614614010041d070350025040b000c0020400c00c07900c2041d4091403140c0740703100040000722200100c095010000740915240c66001255207000f40c6080010782041500c0b51030f540d0041134441c004110340201c0691a981d610300d5000e8010b0410742c00419140140c50045d6000d1583d6004500280142036210905406031000062820115200e60040300103550060031000c15219007100040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 751547598 1250 751546348 751546351
    0x10605040606120b0a12200a092a090e13050105161b230304050a17060718060c0312060605030a11090d020108101e1a0c070b0f160506 59
    0x80500b071030001110003a00d8801014400c1e42c00c12080c802003408540c2d10044050000c1100355252601f0410900041c0c0d26242001d000e0072600e48081b45000646602c240c421030180500306c3c1c00300426111172070003688400190129005040e081d0641d4031503401c1000c1c01e200400010780a075082c0030804c65000304551444040c1051741e580c1d080e29010303c0080c1080e032001c007c4028030203411801c4a080c1e81e800020310203a50300040b0241c030b15080c0e0342c50000c1e034448415842040480d80c0d203214904100418094140d01092134282482070105613401141c400309580160018031010510340002e03d407042050800c20160103c04111180d16200c01404981044854100441c01d0030015030f2000740440c01d0b07070300010b8081d02c0500c4008003603006580d03e201c004c054104000d603000c000030b0540101740c4100380d0076a10450074444141001c02040e032195254091089034601040f214104100c0010705800300c80d1040307445a211905032042d00014400d000c808004100004240820700c40702040c000e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 751548848 1250 751547598 751547627
    0x151f0b0a0305060f06070203120306061606051f140105030a020408162102090402040515090c0304110f0f0d0c080d03020c0d031401030f020d06020a050307020c0f21010605040606 78
    0x3078004584d002c02c106584c1300302e49000790544c00044036aa002d0184001654210300c0040c240b40c00c24040e40c855402401113400c007514210744134010320005015016100c2765518800c52000c040c0b6050041010b030704150b0740321560420000000151030003001d5419600036225040541c0c5141e1010201c11105601d14003c4614100ca5600801c60045010f030540e2205507001e400c80f4199502c68003000300070140181644c12102000710740840d56030f1442c5520b84900001070304079443e400e283c108615540300c2c100b9414020104a000f214460b80c0340b454210900d402200c5540302e151380ca01c0d2074042c00d0201d91280e1820f11842d42101040c540540140c03203440e08520403100340104104e801c50035505010b12001da0142400c006102003601003c0501d1680d0000d81500301c000020380d00e88041703911020408000a03808418061125814411600054400c440f0341903155088000110a6000c42505e00c1300010340845041e0304031020742080c3c1c010302004100b0022284d851401801c00800704041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 751550098 1250 751548848 751548859
    0x206010b0307020d03090804050301060b04090b0418420e07060915090b0f180301110a0c020102070302121507140f0a170a021902151f0b0a030506 64
    0xc00c1241900d020303a881600c82d640180202d141122058004203403405040d212440700b00004111524240549030040c07000c9110716a60b203182883c280c6c1180c00b46000a0f10072410308400c665141200704d1002d15541c0c000b4180c0504202c4141c40ca460008030300c1100301614000390298404041c102800701d100d0000a0b0140041c05e15481c03181d4031070b000c0b4000c0c5c0c0c010400b102c8050010701e9401180c03a04c2c041003802c03c50f4a032a00d40024035410781019524202c0560000f5100c480703032100410ba00c2c2040d00642c0240005485182806550702450200000304480f109098042d684200146001150090600b1612400c43d00e8842c1d21420842d10011141c500580801c103102c0c45250b05d0826552041d03a254101404140446a540d103c002924200441c081c8c84c4014880180c08041c0142603660006a940351384040094006140741c1c11201990041a070381ca203001c400d01a116405a50050502e0300c0800c0d500d103c21406415812103804088041354141145030103074003490241004844 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 751551348 1250 751550098 751550101
    0x50301050f030102030609220602040f054b06030a0902010905030a05060c03040303020d1805010606090303050d0b12060f10050a260f01230f010509010308030c07150c0206 75
    0x515084c0e01c000d84d200303074001800e00001780e0844400e5803d806a900c034180c441d407200c0d003607454440681c0c210790020000380003001000c100038600350b100c6c424400c0b0850b001201800611444d04038a0340b95070071004620114003624802280a2250300c16520402000e503512810321030402002800b0b6040105d010601740c0380c011806180c0010042c00a95020000f001c85944040f182c606940011304120140354092040c4070103200341d03006075a078802c000401d00300c500c0b4081c105282915030300e50105090000001e030520109600200300da4940c07821a001043d1101c002e030215a4400411752251210700495003884000300c24031042c2030007a5100c2c03050303100b002c0d242c4080004070005485288402070b4000c440c040442c000d030f0000701d10104a0401c0d80d00309804203003013500f5121801560400d108810f42c0c155030020100c2d0420b5081000e4611900003036040c180840c5101206001c09008404088006011281c0c80300c1101e012aa2000320314944800030041744d0082c2202c03101c0c1d440503004c1c020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 751552598 1250 751551348 751551379
    0x10092a0212121b04030c180b10020f0d0f0507080f07080a200d0806101e0906090b03010305370b01051206150d050c19152c0112050705030105 62
    0x8040d9019139400c006d126843d540341c40010001c001c2101d51b1078035881c0e00c0c0c42c140703002e07580c4000c50131001c40c4664001e01002c0d647c280f034090801c2c00410609090028602071861480d0b840b20585007199800b03905c40ea40d0f03402c241c16213821030240590041c89d4010000d89039558940c480d0190b12403503c0c0e00e980403150b820342d240c2680c40d0b100a011230000140108009116440c11081e0014081c030716003042e4078582e00a001d0003c400400d10a2407020410002c1e08010031688144020014a11500c1140c02c550455850075100ca401ca205003c070448252611058100d502c0c0001c20b1024240c548980181461728040c00c429100348034441c0b056001c0e104280c0d1401c0b01059076442148119400c407000d1103e401003090110480e030058500c1e12812102c0c09090325101800080c050040342a600e5540ca08641e11800380304e03000550301006407988290743d1524822141c000016448900300c1d242d00a0752004a801c1c0d4064074843c03154900b041d041c011440d8114009605031031041e50b8810000b0081d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 751553848 1250 751552598 751552651
    0x1180e0c280e132702040902030714010905041505062109010902010f05210a0906140f0105010f02152805010503061b0304021e09090610092a021212 65
    0x2c1c40034208502c10107003a1400c5520350350204c4880344000e0001442200c1900468034010703403a0006000c0101c1d07490a568103681024464006101c100c0e4103120030050440052442280f62051500801d8007003418804035420550305021861406101401c07480c1400c4118080c0000b039038103a0115a444c00d500301d43e03912a40441d1b2003035001002c110720302d03400745424980440000300440d050f00c0d40d64840200280c82d5020741c03050310f010600070040c0f50428006402c121141a4011414041d040f03d29000302500800d40c100c41c403080310034481099032654220340050721021804a0140c3d5800d960b204410000d6003c103040c2c841c20707011580d15980300d00030010298414100020385007028000500149850500d1107600c21001c0700030981607000201040f0010803d80b4000704a4000c1006c0002c6150f031074640e10001e2500c0041440041d10348044615842603c01312318808803182c1c0c28028500303008010461001f000d0b5082d041d0342d290204c5050420070400d643c6405541c40b500c014041e41c5401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 751555098 1250 751553848 751553861
    0x203030103060f0513030c060605062703010203160309020f21060109020405011b0f0206040e01090b031b01032d0f0b030c0a0b030a1b03060501180e0c280e13 69
    0x740126102405c0151019507800303041c1c3c2003c892003602c40001003825114803001d400000e080100d08040d0600707250100f04900c65001103e40283c0c410b10030040c011804d6030b0b460080b080702d0705002551140500200e54503840710a00f994101c3e8900c0d00c07568034516511001180908213a096600176600d0b001c415040c0d203e03900c40d050008120b2036a40c5c1c0c080501ca4514101503204800a1680003125804200c582d04036901c01c2c0112501000100700d400b802c1e00917120540c404030060304241e29050b080310041081c20880e40d040590380c44030320401000310f09330402100d40c88140401c0300210001400050503000c0119800c1078101514144070703040c00550890300e680c3c010035101000e03060216000c1d864000030902e50800341c071900c20300d40015072012541f0030036400360360110308a41080b00141841401c41c82c010b000d9000800104200c0040b00e50043c0c000380f212180d00d64400f18909489001c603c600841a0107000c0305070311654007034003e956a920010305441140034820740c0031404084804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 751556348 1250 751555098 751555111
    0x5100501050a0f050d0606020c10031401120f05060f1506040308041a0f27010c17030705090301022808070807050a03060e130c12050a141c0203030103060f05 69
    0x203041c42540310b11030140e207914915032210b03d0010300f441c80411490082d250164030500240c2c00c07041c00004142098090307000150018101403055180752800c84036001c40c14820013001919030100d010410142d07850b42010150000e08403001820101d02c48650390a085c1d035079005040e0b080300342c00c1703070340c10848184d4086a03001800c0500345031900d83d0b007540c10321ba000b86e00720a10b102000308040a15500014058050f00da11103035111008280598035034641a20400381800081e500220020383c519220803000352070040c8141d100d40398880161194000c0415061380355001180c087c0003c81c42d26a03041030040c1c1680d56030783c0d001002c00151040d0f8030958841d40046c400c1e60004507428050701c000c0c0048030303181c64006030030755030b43e5540b800000d4191100c401c0d0014130410001400252400c81c000f824000d02c582ca0404010ba50344d540d03d900c10f0380c006227034a0041d040500c0d80981803242e224484040307581458040320803100291258000d000469003517140c5480d000c1c10300707264412107100d80d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 751557598 1250 751556348 751556357
    0xc161103102a120f0e070803070c050901120311160b070203010f0c1704030e100210150f1e0b0a1224050f030a050d0e0f0312040e090c1c0605100501 65
    0x603404076590142844184c1491440e840307292618059108102c0740c0c0c000c0401d000030316150540d914004d0b2000d5500d601681c803d01c00c100041c80702408607114511001d6040c100301040105121025040880c2551110000440003400003981424240140b07841c0e0f02c01c9000b04a100010b9001c0411500e20340c008800180d0710050030a805007910482d01d801602034100911200c04c44400900b0b541c42d002d02c1030b00107800c48003020408812a000e510b039118101003e602500b41481e614035126082403042c0000d80090028881d510740c0411088005000b002c00819a41c154180000d48802003101060a4080c980100e41c500700490003030041961052910040c086440d0804022810b018410055850b028130041c0c1d40004a04100c031054108840c1c5031517110a00c03c03010480034414030289580245c000402c95450804100100c1e0240c44c0d280000c1000c0740c440c40d10282c640118a0400c41d08009060044441c01c030210405081c000d00c074213005d014035039a8143c0c04090740b04c07600c9040e0108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 751558848 1250 751557598 751557617
    0x30b0301020313021005040305120403031d0328060207050a1203060302060406030209131a150f0d090c0f030501060509150d031218080a020f03030c161103102a 70
    0x600c5e0401e0030f00042e40661500c64201070326038940504050404000203030381a80041c0030030406800c001d00400090b0501c24601034001e024000c40d03240d44002140b14101101418101c104001144000c40c070190003850864503480c8a2030324a5491642e50010348886106030001c6001324413901651040d2640641071a0405107010400d402035040074640941c850450162601b04c00d0700741c41003500104001c0303688104001510300f8000030144d81003950343c07415002c0028210360b10250b803c5548958a000000a1a0700c4c0c6041401c4070300c01941281c401c3c110030780000828040150421000d544086070700c900700da169945100002814044003039000541c1c80b11010110740600b45014486949100102d40d040d404082e01080c000040c504480c0d440002c9824241180d0401c01c1c0e0705012480300c001d62460503c1d0399410403d00078102c0e402d460328815103d0f4000c0150082d05e09030410300240881c0e03042810000b401000d80081a2442030320405000b10351141400c00354001080c80d40e40c1c4808111 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 751560098 1250 751558848 751558853
    0x30010f0806090d05090f0603240103090201020a020f0102030f030103050304081c021518030408011409030a091202130c0804020f04020a1209080403021f03050901111b10050903070201030b0301020313 87
    0x882d0041c2120031b901c9410500c450189489a400441c410200d403018094000e4841009007101a01c8020700e0727040614201c0c080300142d8002950b10340790342d0101e401540e00944400101d1441c803030b200c00000143c20110001040201c000003520948000c1c030240c0f50300c0c120441000c160012a510741400580c00388103411600c02503158807507042040305103c0e42c0f074501c2403003d15103503502c80e0788101e28a80d5900807400792507050f01002904103107040c020354540b0304100e00c001c3c0000307818094018140c1d02c0c2c104180856580301d540401981182d842480f1490b5024406400c145003110183c2c015411140415520310706132007100c280b40401d441d00700301c04007074428100003480b60700c008842d00c10f01040044050303a6143c1c1011140511040d00d486c0074200f02e0300080640d44054010052603040042a410f0b617041a0252842400c4a407a07140b4422940c0c50142e203421400060340314100c0c5000c00f4404e21441c0031004086050003a00c0c02d018100721142407501300d1000b1961080100800b5484400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 751561348 1250 751560098 751560107
    0x90e03091807032a08011202030606130f05180f0106060815040609020d091b0b0405011d04050103051c0503010b0703030b060409020a030225051230010f0806090d 71
    0xc221000340740c0000c003c0c081031080002c04a00722130881d0f4119144502241d110f07032084440740900038554200b80030080640c00b20b960f504000d03003d2442480f200d8043d084c10301b4140d010440300728050701c0a000740d0519152086a022405000c1822070150b40111701d20b01105000e00c0c0304440b90b40d920300c0e290b80c3c1c9840c6941c00e84020000344951040d00c420001070082d000d80007401c4400c0d808040010701c2240c07407030700a03088601c080c03900d4240c023070741c8104000d0061008244e5003224001e0808810480e10040d1114908185011069000349001c0020040c4440060380c4003410030341c0710503400140500c040030f0b64280000d00c111a4082002c00003080001d209401071110750b00c0143c03041b420244c540381741800340c0e046130500c2c10000764040b425040103101000c460644100102e5500216602a20f0751a194002184011300c10500081c0c01603085076802851560f940040d121107a0b400843d54a072008080b081c46044a103e100d844045284100480c0c2640240d45000080c801e888200b43c0c01d64 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 751562598 1250 751561348 751561351
    0x5010603052a0903100b0405010f030302030d0c030e060921090a210b090c1c050a0609050f0f030c0709140a0e030f030a0f140601140c1c0801090e030918 67
    0x112000302840403111139101003280b000d00d50101c40c80884d503010074030207110885805070700603a15000c41c01c204102280c0c0100440c0e403d036507800d4020403080881034040d07000d07080418403400c2c1482100e04010a4810204000910040074030103490070741440d055406480c0180100d013540240144804c01440720b03c0030b1841280c540510940302081c0706030322460f070088001c4800a1140c0c100c10030000240c40c00301d4408645018501c0a102c080f00c81e52030b035a60300d10704030340000d02c1955550b007680c01b404800c2200110710b001c243c3c1110200c50070050308507109e401c00034058440d031041d108081001e80150140d88821803030b102e000001d41c2d03680f6207404050b00052900221500040107100030190200b4001c51181c0350022001c1556440804110211100c41e219602d01c1d42c0d9038414090581c2c0c1c044000070391013004402031f41d00d52041074800e90820945401c03014642150000d40c0b1807294001d9417035412a145c001d13080100030a080c0c10240c0341c1c410310039501d6200a0344803c5041140d407607041d15 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 751563848 1250 751562598 751562671
    0x18011818020c1005040b040c0909030509040b04060b0a12060506040e0c0313050d110d02010b03120a110106030f2906100315030501050117120406030533040501060305 73
    0x3103141600b0f500c001001c5843c01e07901503804140d414100428061540000340041000171805c11006407180c03001045401032200442c412038948040156540c3c540d00240003810707003101102d984182d441f0000d001501c0c898080c02005060850005641c50007105450484131001d000c81060340d140c0e540410f45500060a03440c22310201d5400c080803c104002d001c1c030b01070964440000100c40350203a980b8002080c0100e00c216810040d16941c241c41c00b00348100145171304031100f07840703200c0b029064508030032401204005600e010310000c1800380c900c0c07070011558001d09240742c00c9180c0c6042e02c48019154480900858010404600e06007004030108039607034064600050140d02c40780501242030b12a500645560303444a0042c0428040a4000103c0900c1000140726103001c03210030f100315020303e111b00780901d82e40342c1c00030b0759554600c00600480c1c00b044103501c0c441c2240d400441c280d401c3c402d0006002d14985000400c00354000e1140c00c1c080c9070011512114007ca02c1092542e014503100503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 751565098 1250 751563848 751563853
    0x20105160c020603150604030b15280510112a0909070b090f100c1b050d020411190f0e0a0303121a1207080d08010e01060e031218011818020c 62
    0x1049c00c203243c29001e20110340a4181c1600007208204590458119061200031420411030002c54040000c000315041070b9900426080b84001c00e64159042012103090360150050103582e0b81810002e10110406007003089401210010510880d5082203400e10704a900c00d82e402d105a6001c131000c0c00414200a21121060b02824081205000041c0090000c070701540c8409080240d03803232038944c0e180482c3d090644924544400a0070380307604454040e00841d5520060561000030350111040e4401c614840d45001c0703400440100900c1b840c406100004808407001001441e00340a940c04690b010398480d4117500552648500a2100c2001c011005003891111045c81d1a14403100761540794043c0944403081c6440d990906005120020100300300803140180300c1030038691134603419103a05140110642c0b50070b20100b490404c2c403030030641c0b1507407000c940c004030301c12078450581900000f80c3e6508820a21403100008144050055010580f0002c01820f55000c055001d0203d83c00134604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 751566348 1250 751565098 751565107
    0x1e0106030c030503070201080a050c2a0a0503210c0403030302090a09061211030106052209050604060507030c021b04020d201902030906030a2406020105160c0206031506 74
    0x46840300e5103842c0d841201d50360004a080c00c00c1d0b40c1c102c11810b9000000fa4024415480c00c041800c1c0e880c89212400441080240740c03103800c400b01080c030400340c0b1784400f085400c02d64150500702d6403900700c158040c406030940a02c400c0c440701503900c2c0500504180c00e18038101411603405034081d40061070619088854090005540a402d00920005182860b02c2070030107015800c0000d040070440006c1c0d40aa0b050400807c4580c440110400000500b00c1c4c2400d04507856620725006890000e00141c0180b14000c10301050002039440103000380c403561400c01c010202418240d032601c9880b460450000c40e491030304013039401c0a400400c0001b130380c0c580008001d400781099181c0c0c0e0103414001d01030010b0104208001000421504860064a0008504000902c4005003c1d444000d02400e0403e8465540018106121800103400e151903c0b03047e40b400e4440344001d000300003c42d440900c4038030f69003a6848a030301a1001d5248aa000b91010f8515034914140f652500101402207800c16002c02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 751567598 1250 751566348 751566353
    0xb090408092206050a060e0328060203250215070f1701140306010f1a07020f031b1011030f090f0a080f01060b030c090d11061308120703021e010603 65
    0x2030302e80032880075240055894206410b104c0f003010740e40c020380700b805001103915100d80e9001410484c20400c071200690a81c0e010070b004d40c406e83c0c60210080c0940d002000340042c143e11038249000c04040c041484200800201b022680c0301522225115145074400119020a00c15620031101802d141080445d0301350101c00a10b4440007613211f9400c070303107100302010400e1030b080c031100d030060840d0803140501e1414144620100392030701c1170001100000040c040c045484801c0b4041c80d020009040c0c42030880800112846200c2e4509281e201e1200040300340c80c92406000c211541d104240000e500345022a070601e581035205c2103126500010304164107502d65114821000544003c00150415a020031002800e6907800d80000d104800140304000341e103041a070655188502c229862342090300c0a040c403461700900c82ca5881c2c3c03c400c0004003c49011103403c1d00b0400c40b0040700445034405103030f0b010b0341007501400a000700180c10450940704010b0307111200300001c0d56440c00000d0269640d6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 751568848 1250 751567598 751567639
    0x40f050304210204060b0a05041401140a0c1a0c0f070204060e01030f120903030f050703180b07021e1c051002070c0915060203030a0207210e1002010b09040809 70
    0x2a800559a0100a03440c030b08500f090300440008180d5184e00714140698400080c0060149014400c0c00a0300740071311070143da100d140c1d0a201420092025030395802d0700f060003480288590400d9071782d10b484e001d0340035006003c5821580b080f0180c900540c10104204076900701a8007030101039034400e40740c420100d00d543c006502c0c0c5000f03520490341c182c450101440e0125024a48110304024401518000c002103170300088001c045045924000e0f60f29805880e00340d40b003049059015403107001421000c81c04140410003092054004c40e8030303031a011420b80c5894800c1e034400000e50f8010000300481c504407540c6c1c40c408000d45105200399150b428240c5401c0301240c1024a054070ad1103080141004040320a101e0f00e119914a01d1100b031846046c02c502030344c1c80c4409807440362020784c0002e90505000c01200d1024219026001c0c540c104442404000c002000100b0f000e8032405030701401101460052082c04402c1401a1404c05c1c96075540e2030b034a11542103104500c1e040201a03c0011001c401c1c1e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 751570098 1250 751568848 751568879
    0x30a15090f0b01060e010f1809050a0e1623060904050403050c160e01080316031803020a0902070b060118060309230f0708120f0304051c03091514040f050304 69
    0x4a45e1a07000c220300c240c0c0010540740007c080ca01c01d000c0c03a143c440c24825540703c0c0707100540c0c44200b800724140d01c9660b0304030000c10495686e42d14a00a06041c070010410b071220100031107040c1a0310341c152a5083e11401040e000e5020095448481080f28500d18241070300714036030150103070521909190051480700d040c42c00c000c800140d81c10020034207003d17010075000c1141c0036000d804c00840c01c05c2d94002003c460025444805000d01083e0040c901012440721003100c0034680c040d1203103000542c0c40710888065000074108035070012150f40020b00c10b506ca04441c00120030302898009800340b42c07031416002005c0c1001c2c02e41e58410940e1a003075041e620136002c08080d2904070003e1400d1308908021030f0401650f504089125004400228070311034a58007550800c0b141c5280c0c4990700c2c3c56603d8503034039000c080700186903e0103944030310140194140e4410070459007e440a42040d81700b840000d82100d00251001e409026001d0100780030400071004040542d110b10212032130161116aa000c0c600d90 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 751571348 1250 751570098 751570109
    0x6190503060403080412110303070e03160303051b0a0c030809190308030601120507050403020405150a080312130c030303051003081309150e060111010609060e07020c030a15090f0b01 80
    0x302c18107000400203149146c1c45088058030f848401d07080541c500c3d684a21001d031041c4104802e03140524555a024010343e40102558001c5422080d940c0c44c01501903002150052420384040f034001d8042c502c003080c8503c1c01d81d440a030440202d400c594034a44140c011910554200f008041060480d0241c0d00c010006540917089951b182e180100004001840b007001d90420107040c40c09004201d6041410303101a01e5040750003080c00d989042410501a00d0002105d902003d89640000d44050200003814000010150b0558503551200e1110350342414140060110034444820400310303100342e200d00d4000d201400e5010f000f0360b49031581c85c5036410404540d44000513494040082c1b81007445482c44041e841209000c86034588100c0000740c4400070319841c140190401c000c10310400079070080000c0c0903240c0040000c1501c0752010446140c0440703249001d445002c404200c41c0c038000581e190401e9102d09030704007410500c44100b02a040406049401d04801c5810f217002030540d43c0d40340d01a00707 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 751572598 1250 751571348 751571357
    0x1b060906050a150b07030302160311071401020307150e150601030c0305010f0909030215041a1e070f0201140903030f10140415090c0806010f09080606190503060403 72
    0x864100340046440241006150910f0111085600d22071581c1c0c04003125052080c3d15101d00060509030060f21500c0c00030210300301d040c4ca01804164002d4070b44030501078204105c0d2507181c1c82c0c8402c0d11040003c0000c2d1170141c0e00500c0034400050f81c08441190101c0c04403008141e8510000881d8905007400c1c9010124035030030010003445517854821081200294503041c801d9501d0a240a0300901d001e0003500011511100c100c1c040c14001c104042030002100c1d215021071400e030a10005025108000b06800b0034920b000c903420034404940d003152001801d000703216a80714140701765a600e80c0c3c0d810150555480349120030100201002c07141c821940324003c1c42c0d03a032803d03a12a1510a40041106165081ea00802d0120301a41c1d00c00396100003003510002680104000e425031081ca042e80032561740d81c24880c1058a0540c440b008502481080e00c0795981c10309400e1302070f101c004550260842030303800600055541c0c82c0c1400480c1a4000d0030b000540c0003516000824208881140c0680118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 751573848 1250 751572598 751572611
    0x31605010e010213140609060d1a01050a08130c170c0f0a0e041514131101020c01023a050c21030f040501060503010203070c0c09050c12071b06 63
    0x80c02080c4508881e20021860a801004904901003050042c036000c2074204004c20304c9a100d2000302d441d016801403500791605000d03030211024000c0d9981c0e081008045506c00708613540a2415114150500e03203d0707a00315916403130703a110720307400c4030505070384072104840001044c038000000042c2004100018040380540d4a0500142d0302c103e01040b0f0142119100400102070310b07003005a08954803070a9140115200074104000e848000742c4044200c00b14424010f80150341d5211840d614880e4030703c0320035002c02e0001039890f546c040541d280540c0006c607141c01c000c2d9522043c0268081b0610312407000240b012540380c4468409400c0070042840010090303042c01c0100080c4014121084800d084022070785550000d600014041907402203c05020804001081d081100a4003020700219101c2c42c0000004041c240a10f50070b8540041d0048003291045460040c2031040c660201c601c0c5c600388542e006100c1c8208018031020801c59100c15402000d4101e400403c0f109000760303c0401c58 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 751575098 1250 751573848 751573853
    0x1e2503020c012a270b0306040f0509030d02090622030309270f0e010f1505040605060313021f051314010c030f0c020d0b090f0703030e0616050316 64
    0x315507000d09003a240080541c0f4030b8601c8035200c3c024605080b900e1401070101d080403080740e607410144031070200c60994120008600041074901851150074121001d0240c4143c00030010201ea0041c0d84600c56a08200800035034000e05400034001c040d40500007620b4812030080322080c0c004000a8180c14141007201042490b61100b100c0000e44412015072403082130807580e100501005481c04071186880344040690507134982c0c004500c42c6c4d034050003030054245640e007840051400f45140c810f60b110104c8046154101481a001501d001030400c07465074442400c2c100d540c1e0b84034007040340d004804400603104001700d40d0951140f00661340300c42d900c0300c00c0ba4410a00100c2c40c3c2c2c2010840c0804074140c0c2000340e070702c01020b0710655010f081c825194408820122010166500302139006020036520000700003e1910b914840c0a034001594920500000400d440c1d001502c4064009803002240d5540b502d001c10040c25042d81c1d07841c03200300c548019681c03a03013190000c40b005021441d50715200c406 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 751576348 1250 751575098 751575101
    0x1806010c1a01060212030c0304030f0504052e02120f1305030a14120c060f0405010e0106060e1201020a0203120c090a080d02010b0307060c03030509010e0703140c0303031e2503020c01 80
    0xa90124952042d04503c7e1856204003030b804000c02c007404101c1041e0905030490f000c0d404072400350001030210b00954000d08181c40420300c42074200c24803961583e03032815100784003107021860746002182107454000350050074400c50b00603001504e5080c0413041c002400e07507010407240150921a021083c5002101c1d601103040c00400020084855800c1001c0c8126200101da02680300803104114034064a55080407401004e41c040303c10006e618200c0003150740b0b40c00135485c2184500c01c4810035014403410360710500f40d024541034100980d01c00c0c0f181c0c1e29501901012a9030010004500030300304100140000d404111551104030700f600302c8038202c10040d40c280034a440590061b030007030041910b054002030201e075034900043c04140e590404110407440039001920309080c6d00040b03402041c0c507402c001d001404c03200300342c949901c50b620f5910003d04001c002d0304c0c400c4130318424040c501000910a00d0316004010b201c0c2414010410701c0d5801c1e110a080012519019580d00580362800c1c03000250 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 751577598 1250 751576348 751576363
    0x110706081906151b0c181e0b0a0812040b0d02130b07022d0105070503041205030a02150115050d09051002130501090b1b071503050406050a05061806010c1a010602 71
    0xb11900340d80b107480046000440c00c00300b2074060341c0018030000303581d05100d03008004001c0c1d545400c45c001c0c040d0307c081060f01e810030644020304803030364080d159030b0f4030f0750a40e11b21740001440c0c0d00c08810700003000401d460038068402a005010054a41007642c060044a618181c20120074404080b4410040d410042d6031840c8415040c007200e40a844982d040d0000e032000c40041904101000074030004102d4140f00381c070028202480014000d00d51450003d40300d80260030300100600c105405110801e582940c0b4504032107a42464400407901910119580d911200c0e002c5003160b141d25034607000440401c04214500da05250043e2141641c01245182c4032150380300c0382c100098450305100c81941001140d810078031854801d00e0f07010b48000300c0c9091100765402000749020401100c0e101e140c141d0403682c40389204000410090ba15000100e08071081554002e41190301512549100d61a11100741d03088941410449204403550307454131941c0e146071501c42e6580c102e01c0300401a0540401c07405 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 751578848 1250 751577598 751577627
    0x1603060503190627060501060f08010f05100c0b1513060e0a0203061f050d050703090819050c0118121403040b101203020a0b060111070608190615 64
    0x41003a4400300e81d80c0d80240c0200d03100902119600c2c13840310789080702060303c000d010034a403400c2e51800b4050f0812000410092141d08046202902000f0a00d231044904a06940d80200c83d9001e181c14441400208001d0ac0d03001c0051003009281d4002040001c0d00c4030788901c02444084002030182000e004080010b440782e640c5541c205141400b070400a111629800480c0c03440050722a503d8500048080480281020b0304d521078051045141c1d5200006110b8096030070810b0080e0340b51791604401f2541283d402401c0c0141c1802551060103403c0003081150f00c0c1840e00c54200440c010704642107400704000a440010344010b003c08028a014030441417607082e050008404413071040602c124400100020071048180c0001a01405519034030b0b009060f11100e40315000706285006951024859410754140b80c003100043c00b20341c410918440803c031100003a251151401e40d00b594000c1001c2c221066603c01c075071b21080101198800c402c0280301e0104d0010741008420740c040c042e00d058a5a030b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 751580098 1250 751578848 751578853
    0x121803040b0409180b040327031a040f1b0806010b131e23040b1f0c0f050a0c030b0a0e0a030e220b12030c1b060f031603060503 56
    0x8008070018034041d1000c0328203080f40401c0c11003040c0521907802e08881d000506141d0841e00744014075a0100c45a070131b503440d4543c03640801140049a00e01d8031082c0c4070080c1280d03038110160346c8040298a242ea08241704241c0e140000039955188042c04508060301c007109000110b0402001104000700b50040170a1144a4038000000440b010360352281c0c00380d001c8070014420740c4c0e82d02d41410744c4028001e00300c0401402420f002e65403420404020301c030101d4070a60801c00302d00c07107901e009100c09807d002d50040d4008841c01004094404401000c1d050307580348115800300010480030710507140017500ca000030668072401d5140c25040b11001501c404280f030f00c0c003816040c000c0400600e910703041d80c041c02e01d139202403200c070009401c501c500014840c5080d100040e18440020b65080007240d801f0440b1548051540c200c10305599005841310103c1e81d510001d1808260382c02944e00441d546005040603140080700e80c07100250368400d550016034581e9400700700d2445035040c07041c2c902507c1d00310003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 751581348 1250 751580098 751580107
    0xa170c0f090c07150203070203031602191401140108030705012412080906070609020a0503030f220509040b01050405070c03021c03021605150c0c0607030209040f02121803 75
    0x45151603800402d10074a0302000540701013403103112104402078184c114400d645d6481c1240d0000c0d01d80e00266100401226419140310b4500d00100d00c089181600142400005034030b80c5580240304001c48002516560720300d20300200010204905001c1c0c5207243c000d580d034640314500103084601800681c090142513410500046415201d504111240000c90045e0b42c602410580719510a908220b40c0c4082d0014681e4100310003908500c0d2160f00803264508029079a40900da04ea226181d0101088c2e54100141c0000321030721841e02d000c034481102c0d4800d0a98403907000c1100346c803050340c0c1a1817201031000108001d240c18007841e50300110a140001d05485559400395407000004400a1001e00090100c02c840703119a043c0c607501101148154044201402c1c01519241420082644d40350488005900b01c89240300b101c88200e1890014035440e591284100c00039004013201c1075015403910f8042c00320b4402c0d4005040501050b1040300480c0c1000b0009010395145220140d00c107804c140f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 751582598 1250 751581348 751581379
    0x30c0c120215030403020c180402090a0b01120905030c011103040c05030712110f21100504051e210a0f0c0209010504110c030c0d260105040903030b0a170c 68
    0x18400b90200010601d002c1e00c1c0d40311482d0a81c207040c0f502640a0300549100144510510030000c0d1074003403802960040c010f611400300102c2658449040741d4040b480541c03003910800515804620b1a80c02102a81d003000c82c202c1d130325802d45000345001d04103081c000c400d003c1801181603100c4014642100200103c515106001c002c1c001d5a540151031003c0d0f40340780d611251120301d00c1d500104002071070030510421038a522050a00c5d410741504207031040501e542c920045d039100b240c2c01550804020060380c2c6c001d40400c001d07103a450001c50a0303070041d00b941c0352840440c0031041810700302c070442c03490302e0f90b149007001081e68500310154804c00810500c22800358880540d03950640700143c0d00460036202049411001d0311915000310700303a1100255401000901080740310800140d40d550840c2c2c0045e43e5003001e2000196030051080e68450b4004001c949003c0c0d210174007440c0300e420041000d03822400011441321540d4010323022000d00c0345040c080000188400b011440048030b00200405d900d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 751583848 1250 751582598 751582609
    0x100302070b04081b011113080f071203020f0a06061d0f0613020c1209011e08010905060a081f050a02070c1502031c06031e11010e1c030c0c1202 63
    0xe04050450f0300c0024079141031159424411490303042800080c45800f080441a8503e07a2041030314801249904d14086030320350b0041806813024940720010b0100d1424092119003005648804030190312a800c103418065100384500c01e03a1038060703480007074a94030300500c050091044c1411268040c40d06030402090000c0c0190141d0071a400340c0b401c1c200040340700c000100910034035190a00030b214171a1210b00002c00c441c014155030b242030b80c85801140310400c04081d81d524415018002ca20b03014010b000310801c6a0100e40d01c944000c042e805881e03510001e80381040b80c0d091941c80f54400042140c050003026005864004881800451504105890b105a18916401070f94200e00b1a0f0200701481d62082081e0741ea000380c21500b02c0d020814200c01d0f01c009000d144821190140d460b081008400041503040c2da00603000350a022003203030031030011545007000030500c41e800b501113499059042c03103d21201304081e100c3d0701c0d200c1140007941402c880c66400c5601141c04142d0040d180c00c01030f15007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 751585098 1250 751583848 751583851
    0x7090b0d0b04150f0302040c0521090c15031b090105042108031603050601021605090402011403160311040503070605030a020c03121609060e0609220b100302070b 71
    0x1604800560104014000b50242c8038402c3c1c0311050506440300071803c0300d500b00304a000c89100321010000000380384010b0f6102d0082038070901503042c1000500100303100f03111040c1e610068500030398591511100000d10100c071920503003c000c40010081015080c4a2202594214107207080903040c104a200020072910130ba0084070641320317441c0b110001d00500d507180104001d50080d0040e03200d2034488600081d944038460b803070000a09002c00f150440d4004507007001d01c144000503650100b420141841000c04001d0812410814540002c1d07403c04110300246000348114207200c680d902540710010142c40b820300c5003040000f000c002c204155600006c0c0c1d0b408a03480b030705002d42c41e503480c045290000d0150103207040050100040d500c108410ac881800d103d60407524440341154002c5008990070302d028080c0303801040c001442460280b821101501c00260000c28100351015866100469441842180b840359500c9859003240383c07400040401e1549403c1c40e0450900b60f41c0e4550041c82d400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 751586348 1250 751585098 751585117
    0x12150f040e030a121407050a092304020702030a140129060703030e070b070f1505040506180a15140705070506010603180813170708030712020304030506010602030a0807090b 76
    0x40d505800c80c20503244c1e03040b002c136006540c2d2020740c03603240c0040080d080790321500a88001511155003c241c02d01407104504805500e840c00111241103081071100950081c201680d0512a00d2038410005021046a04a03070141d00000b0500e1542480d11001c1241850f803c881d0040782c2403120061030700c80d0b0095503003503030f0035150103e0b40c01d0100c07140700c0c14040c00f40c20251403001c0009030301007800120f01d000d00c1d003d44640c455440580d419510481100c900340e078010815008900424114001070040690301c081c01815100a483c0325070b41c060040e8034282c504981e0300e1b10749602c1c054031070f4102502e603480942170a0452410740f147d0780f010388426050060906040e0b0f0b034030001d05156550319a202d6100d50200e0401c1c0d070f5490b081d03180a0341c130f801842501002c01c0b4a8004080300040854010201c610b54401103003004082c0d96040c40c61101c0c0c01e030320011031105110020215000700b04140c001d08807a0095603440824503001450404010081d80501c50b081a0401000300180c040b140c21a6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 751587598 1250 751586348 751586357
    0x140609030c0303060f0a05030729030103050a020d2405150402070c0621110309060c0c0a08091305070c050f0613121106013309030f0812150f040e030a 66
    0x44e10f45c0d00044005040360442074141c440c1d11030200f040f100b07800b00301700e1000488990720404c48400019075441d105c02d000050164011401020041c2055040620014800c41c0315603a01c180a00c540348010540c800c50105054450091040320140d01c106080426002d90301545031500586444400c841e940c4140403c104050f25115070800190255403003c45007000240944141040301c2c20782508241c85206003802050080781402180f0700407540180440d0001d03190180c4291603010f0030742c100c902507580110480c0a040d5100d0014840e20340310700f2094861030420b1100f414400d04d050800013118100b58080410b00038910100002c4000d026801500301d502140841e008403443c0b40c805203d80074070f00c1180b00204036002e05446046480c0c01d4000ca42c0b40703882910f440c50420b0400d00b100702c070210386103820600114401c1c54440f1607803400b030074041c0c0c03511015205a0f400840103d42d9000501d08003015000c00d45403880101c1c0151004031000d20920044401254403842840e14580130301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 751588848 1250 751587598 751587619
    0xc05102a06090818030f250b13031a010e0a05090307060f06171b0603090a050a15060905060a05041a0d0c0312080114060a0516140609030c030306 64
    0x300d0038a020340503558440414401ca0b4820b10300386070240c20128503849a20301c19649681d4a0034005070244c4404005002040700c5c0003061a171109101d034000550362020f464040c08901c20101d030005009400790703503c85168103465420b0401c0c041d520b944118603030101120040000c424005241034001204120020f200d071111982c151444c07060020003859541085203124400031280d2004040b2151030101d00c001010302c0e2200c64440c0c86810750385802c8541c039404071440f414600c01440e440f070111411120096240d440e02440c0c8178160b0402c031452200702c441892801d4160040a008044041003400181410300000d0328405407806072078019039803102e10f064004018044200741440150040d164150340e42442c0b00010224001550b942c4040350f04804140c0c441d0240310f040b00d2a280f0407204480d181010485903602800f52182006401c2c040d41c140da013000c001c4184a00d1107011500407c03283d1070300f180c1c100003008010000300d400c2409041e50100011003100d0740701c040bc44540760716 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 751590098 1250 751588848 751588907
    0x150209040b09040605010f090e0703060b030304080618010c0e030d030506190303050d0b03060402010801150302041503020c010b0301020301150806060c01060608221e2307030c0510 79
    0x4000300c440190340400b85405000030311902c0d41c00541622810305050f00c0c100d8841c2d01c1c40c405d41e2400f04d120066948194405c02c0440d0346607004c2c904500c8000d040d00d1402d55980e030941e2801d0700c00d861042002e0000c1c1c8800300d1040c02441078184009160902d201075a420b100020388a602c105100014140c80b040010403581d6044400d086055241d82500310480d22418003c00c581c1014072a4504180340c406140c0e0986070016200b845282d050b50742c42582d030308003002c0812a12114010342c0505800740404110300081e1030600e9008180340d030b070043e1540c008074051800e403070a061645020342d10410043c01201c15586070341282104c14100b8401c1a00c0301c8000c140c0740e104d9521003d0f965440d105000c610550b010254038007032903aa0301c0c0f03000d159409228143d50311442120080c403950544500c1c0c01c4246045185210140c000c91030144c807009084840d804000b400d04c0c85032001e41000394144100840b0840010241c601598900d000070501c03040507040030418110302039890440100c0307108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 751591348 1250 751590098 751590101
    0x15060f0d0c23181011070f1a0c0f1005190903020706030c0905030321010e06060403020f060c01090b0612030315150d0603060218060901140c0c09091006080a15020904 73
    0x3d04020301503010030815076900414000a20003203e949004040c00010b0b040d203010000c3c001e070b5041800791203800442d404950b101d40d01c0130040c580a4020407404070701c07000013030000300d0950f001c00300c020610b413038103e14010050f419844120701c224540f40284004c241d000400900703413400760400180b0001c18510540b40d0048071340c0103e41c10310002030340c440344011404141501001161100301c1c0b42e622500c604108440c119801500864180401c00140c901035241c6524400040d042c00e1800104040803420f5891910040c2c0b10703500884244280c0b0304102c000b4140c40401c0c18041c604605046001030580c0301d0521032944540e0b03541c1040107001d142442264600706403403408000403640c914156000e034100700d01c90943e1480c1d0f000b80840a061640031134900079016980c140c452142c005021480341c02603131417501c06100392106d030500d5884040c1c40501415010300100801d41c0814108402d43c1c0c0c298214952a40002c0140740009810010a105c1284240c501580360b4008102080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 751592598 1250 751591348 751591387
    0x13021504030602040315050c190503060409080703022a0306040b0a240302040b06030105010210050a06091d07060c03080f190513030305010602010515060315060f0d0c23 74
    0x24442c074800a00002080004c507a8404221a49036040c04071b5500c0d245407404c0741c01607440010000220001c440305107440f6a00855104600802c005890340050b01d03030812a030040c0c0c0007103015a005e1010301d80769448070350700e1180354040302180c2481d006028020980f00c441c0604010043c000000106840301410781013041c030302d40110400c90500d20032200307800c1181000c1c40700382d014501d000016445403c007a01128162b0b50181c00500c08405c521401e10000c1000034010452295900c400bc10200480c0c01011104c4900d2180800c140d02000002c90415081c0e41c41401401803015500000a401c90b042a41c000002e030710110b11aa030f151080c48058024405480c8072900d04020043c10a80c8032580540042c0260fa04000c20383c0c0303d40b8240e0884406440b0f00e41440f1175080700c441c003458594003c2d0383c00f03a00001e0101e05c0e65102d1001c20029007015440b03140120340451301c2c217075003c0c0a2080080d150028034004140c0200c40000318428580340100508240002844040194401c2c8155 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 751593848 1250 751592598 751592603
    0x60403080c03190c11040c050405010e01030f0f020403030306080d020a021002070e0403081f1a0c01140c09120a0b04020103020306031e03130501090308120405281a1302150403 77
    0x2c20f140000a0004003803e400c40c82c100c560f4041194040c485060a00c280d9861000c0303030300c900e86001e00380310040d2544c001d10550b0b039042640307540303480544002c540652020040041c5015850798210301d000b80030340c0d00642203204564880d202c65080241c0c0000e02c028a290181c0d04a070070303c4004c000490030852190084238200d01c0e142c041c40100766110328018880c000c1984203030b0f194407490319001d4000010388209100050701c80329400c01500b00d100205607450b0650000070b82c285c00e414050940c8081101e21801900340402c0101e5036041c5540001500c07042400501280c1d040c903518684000f03400351001c0d0400da03003c4009160b50700c0c10884c0e02d4103074100e4959025400c1d0500e0002e662a40b04860f48030301548100b0b800030707139940100b80e09070070f40303070302c15562814450040820044034000400c00d1f50326118103d030311002404102c41502e840e110146191101d220302e418204003002c03d80d0742a142e0401002c040280e0302410b1070003174040301c2d812100c160250820600f4541d0700e010741e4201 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 751595098 1250 751593848 751593877
    0xd080a120204060c03030b040c021f020d1a04061d07030207020f040e011e0905060a09170408030403120e011e0905270c0906040b030603011b030902090f0105060403080c03 75
    0x20800a40041050030f00e05d00c02da405004444000381400141c07854000c1183c0036a003c801c203030024040c007481e5442d1681144100505000c0d004085606440c05100e0341c610001c0418801c0e205418071380244009000c4800e0081051200e00e82000b8841b80014650340c20540d001c0b43c0c0c803003107681e201108800041d00910500c00c9000c04908103000741201203071188841103a0544418400300d602904003100c0e0480041d051981e01c055507400a00403c03d0119501da50710f50008040240140140002e4013801c0c00031900c2e94114a0001c0c50320304c01025002c01d10091010400c03082e030b400000c5044480740c41013481c03070303c0580d0305054a800d10b054107c145c5c030901d403d080d14440e4a82e440d10740c3c441c0c0000d020903485138403400700c000c3c040d1246802d595004a0200002c0c030803a41d0000095400103009000042c8940c0c8210013050346078850703411940080c0c0c4505401d002d524040c81702507005804102c0000d01c5525100019105103c0c03403000810034038020680000c850402d209455640c55210b55 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 751596348 1250 751595098 751595107
    0x30504090507030533010c0615032f09061309081605060604050c0a08090f0d090305011a0303180f0406090e0d020307030801050d020d1703060307140d080a1202 70
    0x1016028240413a00030460311810303c00f0441140807412070401785480003282000c2600060300454801d44150829501d81742c4800305d0610441840403280300450040c1160305558003800c00010650800b44201c00c0700c001c101c80c10b6a6665104059182c000320100d800a00002003101150068145184007501110010030b032810704003042d1600305403071841002a201550703034000400c422150156100604884144542541907008444054110b4182c030b04031105400c40ca44550f2803ca03c0b10016000500c8818042080100c01d014101e90561a20781c040e0701d0b088000c01080d5207024802003854000c50000301c0416903100c0c0141c4039881c10000d03205100c4a6100c00c000e00142078211042606845010740c4c04a0715440401950780c2c2d254542d54240d440d9180000304100b88000e0070341a0703448542000d5880c001004130741d80b0038600031a02c07a140e84901e85a0304041c140080313a880109003041c10740090040f90f035442e00d8415a9030344114038a4640300b0803103040ba0b010450180d044d451620005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 751597598 1250 751596348 751596361
    0x9010b09160c061104140406080604030503100b2208010b1014091e010f0801031505060a270b0a081e0a0c120c090615031109030a1a09060403020d0302070305040905 72
    0x500410a03142e484d904018040146c1042c041110b207031b440792100c41d4004401080010344200011500400309110780105240c0780d07103d07640140e00c1000c41444c815101c1e0b0718000561142e094140c0100030b8000200002601100072405450701c481500003040580d01c0190a00107152058441b541e40290000c0d502d2091000d14414443c204000c0c50302003841144441d007010300c80c1e00001d060740e038012000e94040c08110000302c09040c0251126500086001c0c0100b5034200c21900400d003000c100003800a500354031158070007200c240c080a01e0145050b28024010710000040d20a21606402440412000c0c020552420203216120040107208080b000040b8010076200b108600d900603010030760050740c0c4a070207c0454190340b180e071060319550742080d8852030180d40081092582c07940f0355480c100e410400a41040d1400b0783c200c440005500a0265a01c01d0a14059010b02803034018001d504003918080d44e249803124130002095000901e440030144258241d0f4000c05041106011a05202 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 751598848 1250 751597598 751597631
    0x5092b0327080f070e06030a111c030810141503100b03040b070201060602032a1f0c0306080c06071214030f090f0a02060319021210030b09010b09160c06 67
    0xf001d42c5040303485507030030104907180c1c622510b074001d80005008003003840311036480a0840c400d2140c0c00350f0080d080b001d610900b401c1d9000503c0106e10a699104c0e091809442c08040789034541c00c1220f0043d002c01c1c1d10002c41d00d5407400d40c41d200c5400d1030219102da5480c00c8010014000381c00001040c500030050004100f1100000e5015401c07a4000b40403080e00c86c00c1c02c0b640da014043c0740d1341c003011907681c24451101c3c100c400204000b01714000d5911003070101d0125204450740c1211100d1040e9140c01c041803060b032600c1040040c1c40c880c40a0001c101d5040c000070002d003d925009001c0c04000102c6080c3d41c0e0154242c4030034441e5000034162a4a0121007440d0780c0c0e44100c5000c8142d0107202082c907200c2d0740104949607803d500a02c0207065840d40040c121101105000f8248826800c0124003072020f400003510b40b01c1d19102800c400d01d1070462410400041d406000c400c111380c10204c4951503941c501d80304542c800101c120350384250141201c1280c0781c11020320082c000c2031074001164800c00d0403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 751600098 1250 751598848 751598863
    0x60203041203140103031d0d20010311040b2d120610020703150e010f02090f1f0c1505250c03090e06031c05092b032708 53
    0x1c0c8040d60700780030081505400340c0b80c0e6094a4030003048100d0040c070011740603108402e00a01e5014940c0c00d41005100440d08043d0041002d44441352184400c0c140705ea9994106400b8060078a020f025482c88400000e9081c00740d0b00459100c00c00c0801c518180a071171255102110311400315103171070980700b10203c0303ca5130302c04203102010a60b4031000645a05042c070002c44400090b40c024490399242d0b031031f180c0400c680340c600e0400883d225009012984424081d065241e403482d8401607640c4405410407551503499291075010b0a80a044d01d050702c03486200300258076500e820b007c14100e649203070480d0188410403400e0401850300085c0304048450525040d41a26401038201240c1c000404c1540e074203c0c0c130000200007940c00d0700300744442140041074170341000d4003604441c181200381c00c1600400801c02d00d4100001c2d00440c20107800c4c034051500c2c4117800310001182036550040b22000612456a0758081c1c240111007140805110034454503080d40c1844400544515803a81c8202c0c0c1c507001e1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 751601348 1250 751600098 751600103
    0x10c0f0f0818030c1e04150f0b04140f030d0f090e0109050a0b120d0e03070302030109031106010501090501091e0906080c011e0c02090c210405210406030e0106080a06020304 76
    0xa85102d13900c01e0403d00e426051401d1031282030150525032004000280c00d102c3c482d02a45403a5500004001c2402400300000e00130180300d50f51260704210800015840c8904024854010780510130201d0b140440e078507640700c0141c541b034109001c18082c1620804a06e0384010203007101c40c2c000003500b40c1140c0c13026028100d60202440a04400c0c010000e800c514074104c50314581200600e1b40403540507030804101044050243c5800c60b540b40c002a00311141c0a8081d0081500c500c1903000c105801e004940c0900740900705000d0071390800d40001c1c03581c00240203181d013404000d0b000c5001890301c20f1130b5030002c00c550401400210b071a807902039290204804603d020500c5804002c001172031100c4090b180d40c90396903a0000c11880c5400304207840c03202409040c16031000704080d080d100201590303a05802c1840c10040400c5c100303440d0092621a030850401204440820103580002c080d0003214210ba581c4d10740424850f00188041d030040c0640c0d40200c1d0310380f00d000c110740d08000880d00554070031030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 751602598 1250 751601348 751601353
    0x60b071a0a0b0a1404090209041b0602070803030a05330411071a0c1306020c130c08151801120303180f060c030207140a1b05010c0f0f081803 62
    0x200c403441480d055034480c10b48940d1185298406000c688410762012200050040010400400b02d802003409044255002c1d9070442500c07094201480041d48200001c00d191b1004060780c5250103141d58681c000980385504140d260b20104482d4400c01c0541407400d9a0031840016215446c000c0301008500340c1b0007140aa41480740340c2daa0101501c0c02d8514103504003a100c013451403692610b84503090b0003407800700132401c00d1000081070b04090307400c14041d0500c1d8005200b110714103001c20120713024500004003401d04014040303000036449012240c00603083c03d207026010011a0010741007051409103402c1003200000005030500c0d040b10301c3c0c04402e0103234404200d081032010407000d259450b80320142007050310f0202c44001581c185c3c070008404600f4034006061550568401200740704c4440050205e5100d07403041818000301d0142080d40000c100d4600340120b1a01c0d00181c0750152802000d40302c0480303400060103021400650b0304815500c0107810791b46260740034542003036244c4030280394000e2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 751603848 1250 751602598 751602601
    0x80c09041e0e011a1503070525051e030d0e24160201200d06030803010e070e01050910200607090807050409110d230f060a0b010503010b070303060b071a 67
    0x2010395803c0c51355890805000b0401c1440c81e58085001980090300480c00c001c004c0160858600e609101c42c0020007910710318810b100c01c182041842c10102080b8000342e5410294030008215001003250200404810040744e8400e000302c110b070500e1507040c0f420b00107140c01043e01c01d4a420784803103184284501c8141e000100300c4402c00700c0c02c0b0b03038040207941d0102001020781e00001140d8000f41201e21840400841c116440e6652681c07036030000c2c1d101007a542c9030903040c414040d810082d100e1901400b0701c0c1240c20010f1100c00262800007400070704e4148070b510400b2002400502d000010060243c0b801c0390300340d062200000780a40344034410b906080c001c04d40d0214040c54540106100603402986800f4610b2625082085942c501c0c50f040341c0d001d00f074034a00c0c1c00d44e001040150038007508400c041c020080c1940411401c250f00207000c0c00e01f5504e080540c540b640e0b0002c0590b41503428004466864903210b28068004042c2600a02200c04022451108020980403000c500d441301d405004002e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 751605098 1250 751603848 751603871
    0x21e0a140a121b2103180507060f03140424020309030d11130806071d030d03020903071a0307201e010f09060501050a0b0a080c09041e0e01 61
    0x1d4208021000345100041c1290024242c441e103000040c0c1451890180e10300c0600f583c8529505440d1071885011300c42c0b240c880303140d59426101d25006642a054086800c00142d80d445e82c07500624000e040510540700d078021b040030710036404000080f08505d04c10401e804c1504108a80e401e035a001c80705026031080070101c0c60381250096034040c01410b00210304004078031003c100a44114111021244018044100607170300720a8554014078018024105234140305400074a0b1002c1d0010256003030304c2841e40300f180341e140010301040300c500b5850016241d1025400080c00e0040310742c0004020054000014900002d440045014410341d803a6122402d5400459201140d42e6a9403031420b80c202449084c400505101324054203080314000048003d84046011308036540842c058030b809036580014040760505124510107070221040442c140400c9402c000e02c202d02c01810323840d45207004200c2c1c42e00e640396608080802001d0411407654602d49811a0b4020188200105a19800c4c007212144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 751606348 1250 751605098 751605103
    0xf310b04050a120f0203040e0403050c0a1113020a0815040e030703031b0c0f020d02040615031d0601080303070c110402042705090c091005090c1c150510021e0a14 71
    0x813940c540350065800c003441c0c219116002003008000741c007403007030411600c080e682051106400c200e106191100c1c1d00200e46060204083c0c510b0700242c160f91041008407040b9410007041940001100d4242000d0501c0038041000340c80104041c860034840460784504142e0150800c8d080055030300c01d11480c600350402d0854628040220280400180044601c017508040214403070590010303001148181d42c810480b44840c0844011000013070b99402c4081301c14be03903a058802c02900007130042006504010001c0c1e140d22004d0300c90b0302402600b440c00d008009048400607069a0000e20441d119681d800e0030140780c01300851850034400d500702400303080f2841031261a014217551401008928030704800c3c4070603400301a0401c2d0340b140c1c002d440017a8694400903007070306c581c92840307440d07840c0d0b50300c2c405450509124000190b58107062840c0e2208203a1384000100480740100c0d404904040c02c0b42081e0b0801020349a580841c0c00154401755190600003814507a0741d11880143d1a4079074800c03991038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 751607598 1250 751606348 751606367
    0xb011b02040207111009081014372a020607030c09030c080f120405010c0609020402120f0105030706020a0807121704030906080f310b04050a12 63
    0x200109000261405824990b01502c185880784081d00e00488085001454403400003000d200018044202070100d100207124099003500030500a012642e9160340704032516600400f01d4020104540030409075600054901c080003403107041401c100400710702d080001d000003e01080042e030221102154841c0600091800c1228960190516031160103048000e807014200c14010400c10100101c081064034600400400c4900e008000c0a03288800d0700d801d000c3d02c030002c501c1c202000d003c10421a44c100d1212814680d02c41000201e10071948000780090107120a04d07824450440300300f1480c03160030051103050301e104404480c01540c1c0ca01c0201c3c0d44200d0b14074000d210000034013a803400204180350002a802e0907040c4140e101a20101d02000c1500c100c5051700003504c1040104040c43d08000c0c2c1603007143c000c00c0140c00c0d0b45800348070f40140120b04640e45080401903903288c9000400030ba041b40c0415400b40b0b4060b002c2c105410700307030b81c1c44151700380c2540c41820580c070403d40a40184a01c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 751608848 1250 751607598 751607627
    0x501020f070311040e06010b04080d020607020703030f1205070906110111070803090718020a170105060703080408040b1c0e0606011d01090513020a020601060f050f0c030c0a030c060b01 81
    0xa0007000c0c216070700d800c01d03040a240042d810549402e040d40203030304188052400307041d071007286c6074071a403405106621f0401c400300d58074199000f000a10048035800b144000c20b03a6058102004180c02169007154a19443d820040c5007520740001d02c0a8a5400f4820304c00300c4050f555000d243d5044820258201d400070b40071610305002c108003070400200c2c608080c540c07102411055070180c40eaa51564135040522a04400d407071b03540000d007084403d0b00a0524001c0c0503200640204940c102130104169102d0914060184012440007504200d0a64102d030040d15080c003c450710342c1d0802d21021005005141c00301d420504033076200052a000040c120301c2071310143d45210380e04240034610341e02990401120360402a1090700803075140c40e803052515000102d5500140d96480540c6c000f820090107812440030000e44000c0c1460940d80081901c0d94101c85422a40ea1405051286499885100b40022541c0910455802415001503007202d40d140650740c107100500e094001101d544d0543d5011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 751610098 1250 751608848 751608853
    0x6210c0e0f030624150a090e0a0213030201050c010e07080d1d010519020109050607051c140a0f1409070305120f16111504050109140330030c040f0501020f 68
    0x10503004a299440503060f0140588140026217228200d040254007669050012403603c50040020360f16040950303904c00720540c0c045061030618040f00031180307003600c8045d04001c0d0100300b69440c01c0b070a6120200e41c640040460b54040d60b1240d1584c3c584010742d85980102c0d29088079802140c0610740002c550b040c05030b580c18600030804503400e44681108029400315942ca000307250005904002050007176500344c59036070f00c9000750708103e036510850400b9548410700f4500401ca01d000c1b60f071903d60f0085031034400454054050884980202020300c190255000c0a606000d401400400c0c2c64090704d00070015103010951540410246100b07440c42100c00340d03410010503603d04800950035603041d00c034030a802016008400040e43c1a040180300501c140e000003400c00083da08810141c0041c20790300f107443d03072400109c03000035282ca26014420044000c1c1c1111041084486149000340480c44005240c581c100003408130055002030140085400204001192641c0001a80b40b000d810b030100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 751611348 1250 751610098 751610131
    0x1f1719020f0d050f032706270303090409080304050105090d0905040c11030703020c01030e010908030411060702130c0305180303042d110307090b0a06210c0e0f0306 72
    0x1c1c0042c40440b620291060301400c80029000304042c00184411411810f0001680000d10015003134400301406551180c141000807161041605944481100c000c10800401c1e0041d2004030382140f26825949900c50300c0c003400003042051400c0a0750286014000810269075100f880742e42d1246904000320228003561030400c50b40c500742c0c06c005184002840c01b201e484030701c280d005255170444007044025030050710b812034681d41d251003030034003c121100081c090f50030f42d0b0310740301c203180700c0a000900030442c08203100800744c5800f02201e56459015099278842e00c900fa6028008016034060306002a003881c0224294140e0600c2140d081c500c2d22024501c0c54884d030f41d960f60303070030610f03203d5040b030001ca1429400100b07107558003440d8040c0104040000d04407c84105410150207070444d2500754079002e8000c2d036545800050000f036130301d00d04255582c0c80840d00c0d20420340c580100c14a800304d0500c0c0c049188140d21100b9440e940205403482d02d41991218101034981e04103c90440c40d083c5400e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 751612598 1250 751611348 751611379
    0x4061d0607080f030903090a2c0c3f040605010b0a050a030b030c19062304030f030309021f034d1206030f030703090504051f171902 58
    0x1160002e54000441c0c0c40c007c008808a40640c41590050244003404024003100305115140140030061082040541e4030b131050121915005a02448080003031003400c044d603e0031480d04c0d0301440311000c43c2c040d10b5001c00c5100f000e2620710480e402c50320313a0f0421000044c02e4248a00752541400d041e02d907075041070b06500c000c500900c074003000f0542c5440385014492860f12103038a9400c8211131007041d00c20460501d00e0252102c00490200312280e000044240084403a04040e039044e03d40c030203418450880c00782001c40181400741000b80d400601c003941e0031005200260040300f07080003500c041c045069403079848801c900d80303030488480f0300ca608102c06110b2070403505681c188400603c4004091014a0051041ca4015981441d21018918107102d40c903e801c000c0a444160144001d515018490394020005d140c1c5200c0c0360301481e2280c022075000441d00111604010144040c0c208150351044482c24134001000e040c1101c0c0a0003048029450f072032030000010503005088503c4500650 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 751613848 1250 751612598 751612627
    0x12031602060d0213080d0f090807170f01020c07051807120e01020f070c0e010b040b18220b040506181b070206160309060c0515070e03010204061d060708 67
    0x2280034003a42a4200843c01c0041d460320b40c0600580300120040901c440101b1000c2c000001c01c56011090054004080000e01c20019011042e40c1c0c1410740c5058140c0d815803143e240020140680c06254004250f8a0220000080000490304101c818100c0c0c000440d0000640640988603400050960418041c1d9507071150072081d45106800001482c1001c10301d07080c00c064008100465401400c58020459650007002e2903000d01000d00b1090710749494880700b01e102c2d02c5404010034100715041050303241c036500c90200c02e81b006207130000384100705185000f9000914556a0482c071844c9840082603c50801d5120410040603aa25808050f00c6840d00300300c880031792900004090008104000068a4038000b0301803001031410800c8982d2100c0c54090400110f41d0010020030080840460105000146481d42e1001e500e42d101043c0d101c140c01101d8640903240401c0e003640c00000d00103003207644143c01c00f042c0d0080d0040d4a00e144038010801a051141820180c070b0280c00780700d11641819003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 751615098 1250 751613848 751613857
    0x912120a150909030e04050a020301051f1b0b04120203090a0302060706110f210c070b0403020c120c040b030d08280507030b04050f060a140303040b040b03061203160206 74
    0x10703a03041000e41d1200e4840c02e880c03980104500203000b5001062003420305000302074008110306403c1d4119030402c1c000c6640d04140c541c5e019840c0f45e0716203041480c47d0080c00d48802c4610203088a041503243c3d4100088118002d0310120b65540c001ca20740c6450500c040203950514000400305801e6a207160204621504000400e075081076803840100384172050b801c020000c1245004100e0345030181784113505040050782ea2140b0702d00c0c03011410001c140c6884401c80d550740d03600103007008194803581012880c1106000915410070381500240760700120000f0032000303003c004c5805000c2808440300b07040d2210303a51907800d0080340b079260120b081010514580d80c1101c609800c1000100c041d5244001a02c506a500b00d0200e991100c6145260810740540b560100c650350604800c0d041c00004240301c0080362148502e003070f0052050380070a50f824801c6500502180c0d100b141c40d0350305d450f046030301940141e0307200c1c1c407420b81c00e43c031088650400710554860442c8076800d41c118102e00e800784406d5520 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 751616348 1250 751615098 751615121
    0x8090409060209191e060c1707020904050601091109032d01020d09030e06180108090111120f062202030403030e0f0706030e070f1401020a020a0303080912120a 70
    0xb02440280042c0d281c01c1c1300c010b4101112030300d079841c151600150810124044440c0300c101034450500b1700a090f04070380520365095100c4240c407891340588200c1c02070350050100080d4040c0c0050b0510040c0800010514141e1701e50301c100300104000283c02c04458400c550b505074040c1c101001441740c10480c804604210f0034154007100c0742207440c98041d801c992100d440110525503405040d000e150303002c0031020b072582003501c01d5880d0070205001c030880c0c070304101d00540c100310180000450115082d00701100c440d01d4844125103c001c2015400a5840b0840300d04400291150000c1e5042c0703400c4060401d10a07100c0c0c0610700c1400c0030321000000e907000410a07400d1546460b6560040c0c10100144078120701c0b198080c00182e42403900060680b00070031064a1a07500c480307018410000080308680031164002ca0740103a0410f03540c010f07814452280320203907000d801c0c03284c0001490740000d0814420008101070b50510210341d20110500c1c018154101020941c040009000710740d10342c4803461111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 751617598 1250 751616348 751616351
    0xa02130b0901060201150605042402030f041d150d110105091206060a05041a0d0c0302040e0f0115031a0403111209031501052d0d121b0809040906 64
    0x400540801ca4401c001c0c0c0c00300005039500c42103202c51b03540c0c03041c003080039001c0e601d001894589410f4080306c0740741c0d1014a20300780080908501d08805d000b00100c0310701c100e605108603103071903480324610000703020400040120030001001070014401020507180d402c03001041e10704500c010751286c0510300b00c0c0348042e40c1808801c0001c6096a5690803240d00382d580c41c50001c0c0b01d146802c40034069424615440240154186802aa605140343d00102d0a840c0103039203c8103840810304014055481079440039400500e81414190480000304107021030096580090140c1401402150700c14691440040c02000c0c03030802811031403169240d0244c01900924060b003c0480742c801c000d003820090a8120b00d4101d000414541504051210304026414200700314255071404000c00c40580d549180c0c0300e040c084010340c4054070700040400f000f43e040301a101400b01000f41c42d00381c003c5542d81c0d00f9600819a285403192070880905061201d0700c2e03000c5240d508121400c0144000340c40c02c1c0c0c07012a0084d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 751618705 1107 751617598 751617611
    0x1230a03020a03090c0b0a02070b0c12030402060919080d05040f05010c021c030309020a0506070210030b2106040311030310140d0203010903030e060709080a0213 71
    0x201415040160361100102e604400614051070010b013005042d0300b0100709150001c004d014400079940841d418203445010103881c901980c1404080d5078440301c2102e4000000a000d1a0001d102401c0d140c01d1808160000300c50304014026062000304140c01009510400c1110500303840940c02c00030724280c02c1c1140c04002c00c109019450500c4048031280086441b0070a0700701d101411800b902000851320320300100a03000c0070b0f00581c829000c209000c6034910302202150300055004000d240513880390340054014040c4074503401d03400b0010802034442d40c10800668218140c0700e4026100d185810714001c0d00d04030038200c1d001c005900c00e104000c0d032820104504811740d00742907290034036600383c0b400040389410301440003501035080c9011101016056041090b10302c022000303440c0240d0720210200c0742e80020344285082c81e8441d507010000360503e408012800342c0c50b5040071030781 = true := by decide +kernel

theorem cover : BRFrame.Cov 751438848 751618705 := by
  have h0 := BRFrame.cov_init 751438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 751438848 ≤ n) (h2 : n < 751618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
