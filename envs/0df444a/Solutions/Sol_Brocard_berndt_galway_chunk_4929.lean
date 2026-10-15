-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4929
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:11:31.577946+00:00
-- url     : https://prove2.me/submissions/83d79acd-8760-47c8-98eb-88afb8f3f6f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 886330935 ≤ n < 886510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 886332185 1250 886330935 886330937
    0x5150f0f120a0f080403051519090314040801050402130e0303130c1206050f1008100209240304031b0b1f030c0602030403030e03150f100e07111c1e 65
    0x202e96900250081c6081080c00d80100315132521035042d40f42084c50040c0b40b1100e200d03400804020007d01c04511a04050a0b413403410001c6114041c514095544402d050001c1841050118010600710415803156100c7c0d8000c13a0100d0030465180a51030445140740e801780d4194004000150344000610fa24000f130b5445120300c1d0680c03a907600c0300c10760704000118048950390307200d8040c000110081420540c12088042c4109c8080b468046156503400e040010407080c1e079004903248940740d80e20f50f204026800500342101a2203034050082809074021101200401c20403050b100c80d10103007421007075006600529440e030326111503280309000700541d100041c440c0e00404001c4001190200038000074041d070380046845500b14900980080741118648d40254007101c02c20403003e190084184e0490702c6d010000c903280d00c2e0761008458400b11504600315010b034803010700102070741c484200b58003001220165049590304440001e0444c0c1a0250500090f25111450399880464101c00301c0d20855 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 886333435 1250 886332185 886332193
    0x4170a021c1b05031b0604080318150c060106081504090c3b330f04090b06010503070504030c0e06030706090f030303091502030a05150f0f12 62
    0x1203940010160610740410040240480c12030030204080d40200d4905810200c41000e00c46050001007a95004c0d44c00b030031403020b0191302070350126455040440340a00418000e4030707521030502404d00418030352114681d0044588060f0703c000429441c040e90042401c100240c440c613481c02d0401c85104c20040c001940c01c0d40d10800000c42c941c2c551017103003601d500c0344001004031494020186092032280c0580540208580c0441c0020b00f45191042400281e070034840c4056120501802e00e0fa40c0310038409984a80c04681000204e10781c04550f10030080304441d01c00c2500b544005100a4604c0d180b4001c01d0080640b010800315030145000d194046010702c0c0c0030341003503a291544080c06815074032040144151005100441c10309125000281940b800e100900c10f1074100400c224034140c2c8030203001c00d40e40b81c1e104020400c5481c000e426006207120150f480c1c0c145a400740c0300400d025120214203140040805034517041070008204446402000c07008451200f0307040c41064160701c00c02d0145401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 886334685 1250 886333435 886333453
    0x1080c0d090b04050c0607080403020d050c0909100609020f092b080d050703061a0d02070c180b0a1802034f020d03271d01050a0b0417 59
    0x310301d200d410400c40c01908402410b05003410154180704030103540c0780c05004c0410003440452840070849080b40c0c0d0550310f114000f1014140142030644800b8802e83c8440054140800400e0011b243c03201010130300010040e565031040c42c14124031520f034002000110911441c02c217031501100c2400c08540e00006c5115100c10f462010301c1c85289083d084800b90804104156024011f01c00d42d0b61000c8241010840c4031b0030301c0c03c45155940d06055015441c0400604a41c0ea18000d4054031a0242d010101d56030b02c40e11800310655032a08403c41320303101464854041c45a2802040c1181250540340500140c814110740540c0a940300404520880c0b440e230000100300d80000190208402c0358440740c6042030454103010980b038030500c00d0180522222028100565036a01011016030780c1410045146103154203800d000c211700000d880b02c01c0030800f000051103003010b60510340300c0c03104013280d41c110780e2034104002c2c500005004480d00e031601840705100b01803029100ca01c00e03072400360031200076503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 886335935 1250 886334685 886334707
    0x90c03110105042412061806051806120316110f04090c150c0c1e0801060e0f15091611030f031302030a080a0c0b06010e010e0402090411070b0114010c080901080c 71
    0x900c2c2c0354404104c40c01d171f4040841d44540b80c0e00c508000707043d0848034010815110440c9030f402100241680d44504500e858003802a03000b002140c0c481070a02408002e100c6050405298010300400d015009402e0408a02110325043c400c2c0002c8070340c0308071302010746418030031402c005000b6501408144204100490041083d141d2690014680404000296500b80280c18941085644503031910381c10b000090090812030040320340e010440081c40a03256aa448101011300f00301c00d480340c0c20096a40c1440b02201c0c0c1a04078a40c41e080b00e85504100c0040300d0b1440e0395034440c8100103051190180302042d004c99504249402c403900080864125414039154032409030f008580d101c01040340400c54804000c84ea00b09507a0082003404d00e44a20f21200e0000b03001c460444420a01c00c0c1d030f00043c00d00e429500d680c4240c0440d0a668001911803d1b40d1408090700382083c007541900001c00740d8841c0c0c0c15880f80d08101031896001d03c0650800c410200103444407180548070a454140600041d6000303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 886337185 1250 886335935 886335941
    0x1e060c03040b030a110f040b0d021b0f06070513030f021215090115140118080703082701050f03040303110304032001021e160501090c03110105042412 66
    0xb510108400710355a041c810703030f81c00440c0d0018201410034001449580b400c040144260f03012559900c90850361034040b08070450091280c00b0420003d44090864900750790b1002031814460300303400c81201c0309611864821b40307250050305003c0d481444c403808140300284c0a281c0300c0d102c861000c0c0003100c0c0c0a02e444501d0381045081c03001d41e00c908201108008a20400340907515030034020700001c603142c40c104a41e882d0120103d0010605101e5111140d000400400000c00000d29600e4251180c55450303181c2120f807580035040d090303101d88078900c01c0700810744561111510500c0c142c55052420780700280703120407900b00a00a030281580e40300850541ea407030b90300561003984203603986040c1c0301a003c550603420402285c000c035141e01c1440000ca001c02c0800207100a041c4190003207882c0c0262104610308800c4243c0010029401c201c02d000400c00302860380019607104488071212140b5060046070940154402c80e0881040e00090904032010011a004140c1161500d1180342c00d85410320300036 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 886338435 1250 886337185 886337189
    0x61403030a030b122505150d0b0a0e1e0a05010b04120503190504090f05010e061309020a0311030f03030402010c0206031e0c031e10150c0f0c06120b1e060c0304 70
    0x301c0300c5405c80c2d0744100021440f50000303860200d800440d0f51882c1e880e404882d00070314928900e03050395684145920b41e02c100104000344088141d021243c5071014062100540e4004e40d00c6081e400c90000c00e0034030303e941c010070703050724800702140b03082c41d24100d8440b004800c00355040e5081d0104014a10144481c002140c00c500c0607601c1d01d0380e0f602c1c40c24120034100c2c0c00807140208920301d02070050061840326440c00d9000217089031816150160044010000c00b0003407030007544a2400c20002007048070340e2603921030304c200403070035900011581c0d08a80d88903c0704440c0240040c40403018140103140500140d6040703e0b00d40c03008010800c2901c00810701c2c520684040b07111000110810a1000444c00105200352041400030b806003007007104811000c005000e00d41204040a580b426031500c80c0141c8540c0640100341c240d80405a400c0503502d044c06400750f0b46c00504541c411102c0c0500501402c240700d0005407071040c40183c0915001d05254083d1003881d8803950801200f40216820009000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 886339685 1250 886338435 886338463
    0x219180e010b09090f0615090127050102010605030d0c020103050a020f070f0209011e0b0304032a121b0b0c0d09060b2715130c0f0201061403030a030b12 67
    0xf0761102c500d000c00a02240041030f08440e00c05000411416881340c190000044141d20051920746c07400200680d00e600030703010a808190507c8407003940c400d06049040c4100d0b00d0a800800c180c1e03840b003082c10344075400180c030300c00030403c00c1032400015403103544a0f6a000006a00040c03c1002002000c4965800a82c00361814522402960103515100c1d520300d004200380056100038036103280e41c98050b840c2d24031460383d0480b07000c4001800d26000354000795080f42c1c0d121190001c080242491100c014541005491101e00315003c41c41003401850f50586241d04007030300d003448402c00c0ea201c10010000405c45641c0180034010411041300c5400b800300f0b06445a04046940c4d040c0e5824099254000d90468a183d18072030744454200d005500840d82120358080328007078030884500442c01c40141540110300031031030103040004150788a03080000a543d558001e0180d22358820400300003004004000350f1507001000f50288040c0603501c0201c030340030060103680c524441081070302d040c01c243d134100728 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 886340935 1250 886339685 886339687
    0xc031701031506140f01120e1501031202281103100218101b050a0f06140a0603080d02070224070201020d0f02060a05040311101a040219180e010b 64
    0x4100b20700800000c0e0800e0602c0d45a881030010000d038914140804035814000c18641d00301c3e580e2440e40000006a184504070798401070441c5692440c240c2c2480191001c00302850420480c0b880801d82c1c3c18503044490060450004580072559541401c1b0f00480c0c0740d8802502c2070314aa101805032210380142c00c01d0040e2191006850010001d8090380482d214250406d1440141900290440d4004240841e6007801030044d10300603241c00164940605500c085030420b0741000340641015a00f6400b251202840c0d84840c1c8a510030f881c1140401440f0081c148030b00e01d04005181d001d018441e0009002e00883d03200401c3c000e0402c01080783c0300c1c4104900082c802c056580401184420075554980901c803440c459200a48915025202d03482442d126000302d0309241c0b0071446098072644400a031040c0c5440403000200a18101210400b1100f500302081b4842c9024820313201c6400c40400f03032507000361124408888000c48000d0b00841c8090192022640081900100d8045c04084080e1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 886342185 1250 886340935 886340963
    0x1719110d0609110d0e03070512031006020109030806090a1e0605092208070303060801150e1b070b09120408010b010905090c190509060711150703020d0c03170103 71
    0x4001520810b40001c0c2c8103504050f10b03000554403000c110364600044480015003800880c15050540c498140c01411620410310100c02941141d401180500c060815440c1c1c465500d1b6800e07400da0f00002c8008e000305c5c1c10040052010300f0b000202c945d01148400c800503100407001001081911602e64102d4510794815042c0880c2c101445201e1b005482c8002005110322203180000f1815400c0000906801011030741d001010f001ea0001d03005015000c0c001c2c04050441c6d81e03200c907800c0041c41840b10103980794020a81110020010001c50f9901d48801d62a0030110b898403000743d100034103400c041d88986c41d49056002c000341c02400c090320319403002095804000340010000f80c102c0d00850310a807181750a20501402120071219660414841d03505840540c0c00259441d02a005c4002e40280f40014400104000e200d00008046011101c540c0490001010020180030707601e00100135a0144907000c480600800f0341141e41886860304400582c003c204141600302d00b81d00440707281207142c0d05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 886343435 1250 886342185 886342207
    0xa0605042f21120706020702090114040b09011401050711100210271101210b120d0e1203041203080108010b010c0503092106091f0c171911 61
    0xd00d04400c0c901c040380811441d1004091901d81c000e4030070a603003c1e000040c5000030040d00f9010b64544da50000c060003495a520a080741100b2814031880e80314524011403040c043c907004503201d040e07404d00000100c4000712100155001d9200c0d5000381c0e10600042d844030007641e03d816a070050810158050503083c40d0b200011030a413601461142010009245485e182c051a500c481c540c0c0c81d04560018052869a80161070302120042c12080882c0300c418114001c1626030441c0c49400d0090303540d950341007e80d4008585441811051000054040b00003081074540600851660780d003130000d0741d18103a650aa00c2c1507004e220801200070070703c1c290041003d00020712640c0b02044081c2004000b40009646054a034800c8000f0544104040812200c50801b40c021107a1190584c00c1100c445052a440d180c0e50341c655401280d80b4288081050408006940606007881c4559202c500c10000752240c03401c1c665400412600070810b100c41c1c0070344054039034043c0740400712131810016130720b0760950300e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 886344685 1250 886343435 886343449
    0xc050d1101020706030b0303090d1e08130807030b040b0c0418061a03040201021e01090507080109061508030901030f0b031b09060105041a03070311030406060e10080a0605042f 77
    0x112080c00d1616201b02d405103504c020044800e070030400c1303c081741048060310380829441d484a00804072040c88008010410966400601043c4035410a0f0200d1035a2400ca841d0b44031310602004054403142c401007000100c01680b142d8204040030403084c03c06840c1d07244010501c081c1c1e0030030420715884c3c1004101c0c0f01c0c20108169800b00756405500c1c5507207170540010359101d03c100100c88a50b400c1c4245050040c1085d440040d00a52100a55040300d0741c605030307140a0844050259041e40c90080c40c06111554920940116819070010b9410001a4001980180004611042030780d44031040905552ba0030300840d201490010031403800190202c0034031a0001d07008240e5418024100020f11208035150070318809040702c0c1c000240c0d81c0d81c40007001c0b000b819001c00710300306a44002c4103000400c000c0d0741240c001d50b174561018500a6403900b462400341c1046114002658115a842c0d01c041240360704800e0b4403070b006003001403c1c1e00c4506014022592616076003071003160342126104861400d10703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 886345935 1250 886344685 886344689
    0x322031a01180b0904140c060c01050a05010803040518340f0806130519090302060a0b04060b0703180f0906180506180a06090204060c1a01030314070c050d11010207 72
    0x40c60811040d031034180400d011340e1002c1c0c00a011a464903500700026001080343d60302c00040600480c0d212609098100e010702010349013030001c1ba05140000c103803480000700b0744003200c1000b405020351080591140d080c0c034070060484401e019180c5100e0701d64009040d068803040f50151000404e0642900c4010b08004180001004200c040c8c0c046c012159121654030082c81c5004d4030010381034070340e905901c0340d5003000e0040d00c0038a41000f0559003815008990b080c0310f000001010b2002c99002010441203405501564800d010144082000301303104411650b401d02d040b00031040c82a8607840e044440300165409103441a4849005101c8042c04440f040c0c500111a601880280cc0941c00203000e95006141055100e0b281c0000820345a0590400c10013004003000c210760326030300c54a00034480039444009586e000c0c040d003070f01c1215a0500107003504890b056651008000142142481964080c44003911a6102d28101082071b50f100181e0210407031042d8004004400c01c140060f0800c1c0e0f540d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 886347185 1250 886345935 886345979
    0x909061413050c2a0a0303140c1306030f023703020c030d05040305192f100203130501050901060f0806010e01090902040e1903030510080322031a01 65
    0x88010703c82d07003601c02070030380d0601000c005400c030018200f006101c19001d004c1d641c3c0310301403180f40201c00505030158001d400710900b50602904c07541c4c500a9040040c840c4c401e15407401e81614604101e03181c825032049401c208200f030b0151801081d000460044030b401d40005604485582c030368130041401010400001880d414254181800c201000f070f200e004130848140e031503480382c3c0000c08041c03180003150cd0141542d03a05001d1107010000007801003d102c1c008441007032503030f000c00c4a400503d2000442d2a0380640042059202e16603001000c0d4002038001c4101800f03860407540061005c0c003c042c45400701c0c000000d8064078000e81c4055104a560202c2c2d03d6400034001846298086100d00381501c0b0701800c0031640303070100c2c80803600400c08065200c4560250f080070f007074005581010708040034000d0b6424800ea03100e90038a0000a141d621901c0d0a540c81080344110315124410508a40303072103c40c8507a03449649440e604503001d03a260401e010b00740c1c0c0c40c0040c044207480183c9440c0c42028 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 886348435 1250 886347185 886347191
    0x30b1f030e1212060d0c0f08070605070203101a121b010306030201020d08070507080301031a060a060f12020708161406040b01030311010b060a020d03140c07120909061413 75
    0x40e50003548407070f01c2003a4070881c00060100001c0c01079280d0f4100900425403042415050a689104585a0900c18040e030403542c00341100005841d48150240e845154000300502482c100460031140102440d80014032052000300c4c0c20055a6039041c0508014900c89020301100800f001810380660500740010341450b240040c1400980d0307000888814541d01410500c0c0f0503225600184e815015440d4020314005000002104004140c0303a00040c1010380c204640d6180c40b05003c00901840e43d0003000d00090601900e101c000380b150101c10304030748080600518181c1e50b5103400c01a41d0010f404403d0f942c40b40d14a8000300601041c03104001400a80070f003072036007400e80d10302d40f4440042c40060104003070024a00940748003980030f003502d80e400030551a61102030201c080e44503081307441d44001091420759020618000c1400107449201c00d0f420303081c90b0520365520035500f98031704107100003040806900411451403500c9414041c05140c0c5028074200c01100c10018140c1481d444200200c0c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 886349685 1250 886348435 886348453
    0x106060e0a0e0403050a050408100218180a23040c0302120a03050f0c010e100b0f090c040b1312030203030609180c01140c03120a1d1c030b1f030e 64
    0x188030380c2c5903800c10707458900305603038070744091040301d0350300542d00004100c1c001c0200c1c00104240642c000c226000d41007501000f282c10050801600e00b030300c4d90340a80c038400d00d240060110849580004101d07100c1841c6241e007441d00300305100040104940407541c10126030300600641c5080c0d000e281f1002020300040440511640c2c004246c0d000d041181254400d02061040c414031003900030b03200d1a45020200c3c4c80050307000e507a0502a02c4007442160141140c0d48000d00079082c0100000d200e1041090034614062416810030790f6a80701c0d001e03010b1810102d910201da000b10700c8003e8519030b4020384c011034882c1001010090381c424007415600b41c99a000d84140549000440e411a0001003402c0c0100d20108024880c2034500c40c4d41340720145400000303003849000751801c4089000c0c05821508008031145000c4031007008080c510407008580c04003021090b8807a0005d05d07a03022484501c0e011500144c20804582c050401e00b40501407030600e104a6a030320381c1e140c80b03840750b1488101e0041112007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 886350935 1250 886349685 886349699
    0x5010b07050304050943030b0603010b0a140307091406180f031011030405010606050a050714100e030c151009020f120103080705010b15090f0d050f0106060e0a 70
    0x1100e148500e071700800c08031001640c81c0d901c2d8600f100c05403031859403010990002d4081c1d0680003a90610305c0c124442106440301c9140d10920403007141d0712010301528070f184d080c9003d40510b80c215401c403030100300e40f19010b061000304d61406907018500b503440302d100050070669824400a101948680214400e00100c1c0608001e80408c81c0103500a0302c90031540404040864101b000250400300c0f0281007185140c1d0511640006500c134602503c0200031058a60700c04407400d00c1504420000240140310010109429048006103c082c48c41241c4800100000b030400380c1301c0726000b40710f035900301260794209031409108591040200c0d00314142071303242008252240340c04d64005d8040d0031340c0c0818410369148001044449030001d9010341049903375285092143d50344222021101942812040401c600717080071b428624040d00083c49044c03404440501880600081d14507034000c544c120700001080b414040c521a04001c0d100100b0910300789070002e0030881600700480d0081070300380c5082140e8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 886352185 1250 886350935 886350937
    0x90d0c08040e13080307020c0f09010602150c1603030c110703020a0b18031501061805060906090103140f0a06050901050319030c0c0e04142409100e01090605010b070503 74
    0x41c2d076044a88016603120098004200358607641d0040144c00000b0a010007160001101d00c0c500b241103aa005460000009200280000b84101c10150344407400c41e1640300700700b6000507407294a40f03000d0b60524841041607045c90090001c150046640c0d0303a40700000c02d5112100c0044c1e02d03034200007041b80a01d5603000c41d104000c03610400d9450740c40407560101d0321a0f10041c1b101e02d48401001c03940b80d038801d40c0c0f000401d80c5080c4118004617a00c030381d8030110070030206405400c50310020985402e10380404103000c0c85910078911141019910104450003281c41c4d40014003813401032000d5034041c50f10180c00c000702d0741d0039001217208583e8034004103e10740e0005088210068070483c00d0b207240c0c17034514040d1030308520400c0c0206a4402c01d1804076941c0450030880b44598007a440c1225036034035281c16203403074007050aa802105034400c00b40701c0d1350320b1541840c6a0032100d102c08403024643c00b41c0d014012680061401e1003281d4454070f0a10600215019a074098461846c02c04c4c544102c550b1080c1e40d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 886353435 1250 886352185 886352189
    0x1401081e04030516020a090203061906020a23010509010f110c071206110307050c0118080901080702072c100621021b0a0606150c06020d0b0d0b090d0c0804 68
    0x4004000400404c0304080c0074000c0c18255014004041030381d240e07a00315003c0e410803a5414024030940c01c10f0f0b810403e0480c021030441715030f60040d14440c0042d842c1c0328000d00d102c2d940060241900451301c41603541c2442034130f20510364100000340c0001c00e05a40415121307024103480c2030003010301c40c952880e0804242034045548180c01d442c0441035031711f86100070701454544120741000c04410012030035000401083c00020342710081101d2884a5282a41d85031150780140c00c0c00001c0c001790407254020170b074040e04080740c2e00407101d2050b59212030645a0760070380304500c504000a882c1c800340b80e4840c08160b0304a4071301c502c40f1090340c3c01d10a0042000c5560081c1c03103003080c2078955600345a000c40d03048800c03200b10341c5045030140c2403140741c2a80e210210042150a80d00e4400c0018591500d00c030708044000040d40d44038003243c4907442e280069040b2074003900031507a6235045003170b46607140c00329411164864000040c1c82c2c5040580e00f0304040e8926100d0007802209000130001442103012241 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 886354685 1250 886353435 886353437
    0x703020a09210501050403180518041401060e130201090902030705031f051306260d0e1f110d0201050106090510050d15080d051201050405040201181401081e0403 71
    0x34191060600150103040510701030300c15407814091101f45648034950702607018000a100301c00c943d6400c1809580e11540850310a100c94450201d0000341024418940f80030210f400450840d031a040d000108000a907403071095904682c100ba030455810120072002017003428402c50461900c41e0300644148001880710034400e280300c001d104401200038200c0301405018265000240c031100402d0020083c034007400158071961284041c0c0350721044c940c04130405000024180000312050b042e01c4645501c0d59059201c0f51009a50420f01c4004040c1d980304111642c8000841c0302d04031042e0b0900c03c0c080307001011641841700601c88550807020381800c951082d520b00b00d00c60001e450484041c000c901c070fa001680d0805503501c1d96280801c42d880b00b5074001c0c00a8490304200c0844c20b4650744a1030801506100d070320401041203140650001d03500c0350040c12700080040102c0d0130f1500700c0301150406c4c1040145218100780d15644900072551186021010f109561200510340f50f0a0100a00040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 886355935 1250 886354685 886354709
    0x8060307120311060705030105011205060a0512011d010b040c020604080708030a0609020a0906020f010b0906131d0307120f0203180303090d0b15011e0e040914150703020a09 76
    0x410036115a0b42014280b40d51030548209080c2964006e00340d901c20700c204ca000400000c00f9100f100d00ca03110781d90140c0340040a40c80318514180600c400c80c0549400c0d1301481d540c0c3d807040841c64041c80144181030340100000a440c601c0e00080008440909580d0021980076004220001d02000c0c1203840158202080c95200c2d0703690b0b03074004003800301600001052030000c10011000d07500712004000350f43c0a0340a507440152803116031401c0352612420a6030000c881c4012920300d040182d40c0c5a440703048640c000c03540041e0002140314002507285068100c2d4000200d000c01c3c042a100300c1c08210a640c5002c080003a49088000d40e00e0080c449901d4140c160000542d4241c2c4d010403c0b00c01180019000c10110016414510701d032500494000b001700b51490b1890303486600c10501c8666011040303144070200c090b6504121210f90131410500e802c08d41e90494580410480c021401e642650b19000704650000c0d003031a84031000d0007401d8081814014000c821105801000c01015210840440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 886357185 1250 886355935 886355969
    0x31203020c1e06060103050a050601230705120d11040e06010e01230409050a0c09120f02312f04030c061806020d0503240406180c08060307 61
    0x1800d002c18070380300c1c0c125480036403840c008035103001c514503100300b400746c8082040e03565004512013540c2007124094005980301001c504022284021030070483e00b007109450500a1070b43e902c61410200140800b0a0440840c0084c60848240100303944428905040d80c14140b404010415000018081a06010800e8601e00c0141d1080c0c4000c1008420441294349034148804020282d43c005e00600242c1c904010001e407402c02540155403135201540e4070b1152191800708040d07002000d400d422607501e6100d0b10070801603030303504e05030000884400d1208201d045004002203440c0c64001c101010160a02821900c01e452440c3d0350f180d05030810351010106414846091580c0c8625003000304050a8141e0220b02168054001c8071006441140b91b920781e600c41c001640d0b03e0882085490000c3d00401c00102d00802041c0603275902c1c088008419050031604000905403421030300301e502c00c01005040d1002c402e41d03502079a6103a1146050095a03400c181c1c000c40c1d140c0e0301074060401020112100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 886358435 1250 886357185 886357207
    0x61302030f06010e0a150e0f1009020a1d04091a070306270b0a08030d020a030e0307030e01090504020915070206070503040906080c092a040b0d1d0703120302 69
    0x4034220039029050700e0166840780f00c400c4a0441c00d0310783c2c4d40e900d0716284252506c00d2000c2ca00740165040300d81c1802440c1e480b043d10240e401402042c8003203907030284d0b00001e10803440e400034003003250450320351101a0342c11410703a00070b035010440514806d600340600080403c02b00342d401c550202412801c22030f155035180080d0080c20306607003d580140300000c0c0241da1080010704601c00c6c0340000c0c0c810f210f01901e40003004003d450754047d181d8580c208001901540240360700800c0c503c003c508001c680803402c0407a543c00c54000081c2079010030006000c20030b8545c2c1c0b0005680103040f0407071f01141015191408141444d040b10060800740c2c400140707403020b40d607821040e1401c02d54028112030b902c0c0d1311541c106d006881c462081e8135075440307000305000807490100d001e18070408021040ca00200c00714100c1c002c83d101200580c52140f4030070040030034150080740081c00f40983c0403a010070f60008440b4006161202e083c0c10a484c0e4000300350500028404a180c0d45201400d46000f686034894814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 886359685 1250 886358435 886358443
    0xc14010e07030807110105030c0d021317030309060108070b1b0a0606120606080303070e09040f0b0106030e1e1f0b040c0c0b070c020306060d0303020f0f07200306130203 74
    0x8809080e8800c180000040000c0712000307000280c407030440c0c03001c1059200019246030009854985214405200c0160038042c250b015000481c07820080c18846075881d903049540d10f4405114007201c0e0400420090604010058030f401000c2d0100142043d5280214969443c000c01d402045001d85041413241404001c104403945a90010410420140c1d60000c207000b50000441c204c510504114001510420100540b4030035102170f142c100330a5000d2080084d2a400103004403008101050b142021520500c2e0340c0f4060011380c1c400095004c00c080e441c0746000d20112903d5020200c43c83d004005610118842c007440c0c460303040d0b04050040a10000010746000303401d041d0824540001003925641c0081220040e501a105401c11034503403010446540b80d11401c040d41503800903011900e5420805012281c0e90300034a001070804212210784691a8442034401c1c8140f0004103029044c88900f41245d03881d0061070300544082086800821f480d03400041c6003941590500507910203544080c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 886360935 1250 886359685 886359701
    0x9120809030d170f1315021b010c030e2a061e031e0f071d030a0b040b160f0c1a090d091d0105280e04210c1401 49
    0x2020740d0a0100340300310082000141120348069181070f070010410b44107003100140e0250003030325490142d00c812501c0c2c208940000714200c560081e401c2000002420507000480c40011f9104c1c004143c0100390341004087e200c40c01d0550072244c010a60001400170301080038841c11007400042d0a40100480000301c83d40501000d204105000301e00103100564003e000354420302c00c58803002c3c0c8428284080101003502113602c1c01403d00304ac2c1c040f901240c0035814415110011045000280889002227420b001512100724cc90741c4850041c0001c005c00d881d00c0f554020702e0040c000b0301c481401000200704500000300c040601c00c20040103404c0c8801450700251120b26041040ca66003041182560b65142071940400003501d009030100b500c09041804000881c0824a01d0320310380d08003001c02000440c00c2401145194001010032107000c0400d52007070041685c0740318042c5600d001c0c00c0110418131710b11402034501191800c0d120785241c1054891000503045941824012800384d2058010440d00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 886362185 1250 886360935 886360939
    0xb060903060f04030c171c020901230d0213170a0c031101021e03120105041b030536010b0108060109060f0207031e021212070f17040312030b030d09120809 68
    0xd1149003030600b40c48007c1c0041c02e81818084800440c00c140b100c02c901585480d180000d880c90380d00d01d01c0180c0340341050141c50110b080c00b4503018402c0c03196412a40300b0381500d00384204804040200160ba60080b1a00b01d1840020300004d051650329403148201354000100804c030045600f83c0710340d1080180c101d201c2201c4c04810641015103d403142da9400022081017008542c100120703940c1414018a0006070340490340980203907003043e09402412004080444045201c0451500c4076a5040c0c1007814049100b10300403072b0f941d107031086070a5415070040b00381070100440030b0010590340044a08200d071400e1030800609000c0041c04c905103502680003034010203444200c00d41c8486c0c2c003225040c07060300c219203413060061580211a116045410751103151a0140550401304486c0b140700e1500500c04c00b808410407002d240e2044550700550000d40341014121300d45821150144102c00f00d9607811002480b551080c49001409011140642080c0781022034483d402c0041280076a4010040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 886363435 1250 886362185 886362203
    0x120309060f020c0f2d0c10050301050312040b030711011503050c1c080f03060307030f12030b0906030a02040209190b0a02071e050d0f05011e0b060903060f04030c 71
    0x4103000c201c0194202281c1040d0500840f641819640c20002d4003041d0b500e0300d040921101c4200e4001c0f043d0a00050030f0104080c090794044400300d86e43d00700700ca50717080610b84078107449506090500d880c02407180031903500e10604000501c45905c201c0306881d8811004c2c906182c0d50590302c3c9480d8050103100141400c265100c01c000301c00c002004c1212040c0c0e05d13080d202c03207000c0900b00a807002c060001070005040b00710700708001d480c88181d10000b50b502240c0903088800403540c81c1d854202c1501a81c4c400e0b41d42d00d01003080e05c60915071602801075561400c4036054040e00b0300800180d03c3d2110110001c0c462940001c0c60b40c02500d594440030000581d00252a40f141e948001c103510a6100144803401405514404649030f250822546840741010b1064a551800c12042c810303509044142628015200f80b02c0f440010b609018541c450f0b504010810003071464190700c9030540f40c0408031b00b44607000c1030162003115100050117544c48801405a4580d03900c4500703050700ca806d40004050f00c00c0300303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 886364685 1250 886363435 886363451
    0x10050f03180c010c031205060a0e150f010e090a0b0f03030c0f16060903030c1704061808030f0a2d02060711060106122301060201090c091812030906 65
    0x381ca0910040304655203015189407803001c000443e62042c25210003000300b4036000050702200b4045e4040c0f03a01040282c2385000d817a48030306890b5101101141c0360f004900e0940d10484003405d182e4203030900b81c0420708151003000b10001c0014480c1d01c0084c90141c015075608001d0060340c0d10b400603203000c810090103403030340c4d9114201c889803240f007400d11601103486494001000b0f1403015171444211422551481046411690210340054504505903940d40313503241c26025564004004200401d4541c4807501d21014001d04110380c0d0225900c0780c00030303400a21544c040c0346c41a40407034425400c6803030003000c3c040040119840d0007160b9030030303462030051006056140d107800159040c040d081c55200c080e101000614560342d200b401f40208070000d5100f6a5030b40810501303812100e4001e103140f494501c400086d041d0310400c0c0409910100041c2e45501881e418444100801000b6010748501072002084006801b0340c41c00c0000d90041c504903d01089a40c1c0324401e501c10351080354040400c2c03240003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 886365935 1250 886364685 886364701
    0x509130c200f120c06130809030106090501050f09010303080105041d010f02040314010b0d141e030d1d0613140303010b04050901050418110a0b0c07061b1110050f03 72
    0x10280b9204000e0512600505080685400050700c080d071070382d80014010f56449801c4106a42e9000c901140c000500748054801ca03a001e0043c400238082824000406605d840100300205e0b606201a5004040100050001c280c0c842c024605480d0107941c0441e50008090105041c64007052184007554a042c1d41496403504540050044034025000d103044840e1000d440390032541401c0040e5808030004610790005048211075548804a1405440301c1c101d6018000ca94060030a000140c160800144080c042c4024841d110340320070104000c2d40c0364030300ea0050130f98842d0b000e41a1441c3e1000300400e0803c100d040c7e00d610340c41d42910740917241c8a50351054013492a400c9800b03000c2c403c1e15400000f103401e091078450310420702c6072950418000081078652218982e004031506402021a0307802081c8091040001c08221b58503070001d007003c501d000b000501080003030401c0c83e00c90071003c0101e404640200d4080106031401c8608803408004540195000e1280c07650300700301d0983c007000704003400c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 886367185 1250 886365935 886365943
    0x1302030105030609070608011e03120206060916090b030c1309050411010c0203030a18050621090c150309010b041b0f0201020a0926031201030c060509130c20 69
    0x940081c0e007103072415181d4115085d1034a816008101c001941c01004209820300507440101c460b000011110305241c59444416102d042841c1d124096803011060000b103040070030b035482e4014001658032000140d0614000e080800c00e210300c2c22042c0e400300104101c01c1c0907008440415a41094000d0701c01d96411228001d0700c1c044406a03141e84e4041d841c5a0107501520001000300d600801440c544003188009950880c28208043c01c804001480030030070340c0f100300c01040d41400107e07204101d814107030310404031020300402030031007504001c01d000e14075201c0d51307440038a9007004002242c4a94681d1803260040501071341890b8000e0814482040072103034084044000c410316559106e0304c607880001a800d0340301d8101c40000007180c0c43c0701001250701d50080203224403402c690500180e001d100203145190030100c040c08180f204d0340010000c0003601501c550040400781812030400c11480000382030a441a102894007940311618201124440c0c0711094500d0740ca0350300d40d240705224081e4640d0b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 886368435 1250 886367185 886367189
    0x50a020c0607081b0a0818010902040c0c140109050307030804110910030b090705030705100e030a03030209180408090405041415160801030c050607081308100f09021e03070513020301 80
    0x34240c0000c1c0f0403a84e52103030084540522041c0c0358042c041d00c1ea40f2900c0781030b00699510074036a560300c03c21b00d0b0051307072140543c0d0070750011540c803040480b50714280903842440040301004503a00d00000240000c10100c1a14145505410480c0c0c6903039076410031641c40c1d882401d000e90700000303040c2004500c2110781482025240101d4442c0f003690786062a07641e0f1217600340507159066110060801c080d16000401843e0810146003075081c031551000402c0c81d04925030700840c042500820391850758141808204c042280c160304200da00d003810340303070b40219100e9120200d02075501c1d900020103000600c0c400744154244c1d10220f0300042080c40d000c17062850150b0303050007040510780104044c0d61140e4556816660007000c042d22140c45c140402400d5031040340f0403203000c00140014450502c01651a000821217074001e0420f560f40000200c3c1126a40031200040600d0b1401502c0981c03a41407080c503160008401e40e0380e0349021500000e1134844998409503010140c4040403804810782d401640c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 886369685 1250 886368435 886368451
    0x40b060436020717030a061e08010b01082a0405030318090a1104091a0307060c0c1517070e03030a11010c0804051b0d1e0b0601050c030d050a020c060708 67
    0x41c4900408402100341e20803054080d10802c0207410b103425000c0042e00454010101c0207000685d04e980f4101685820381070f00a19801d1300038584201301c5030400b0700620007540310902e000001443c04401550a40c45003d00f50144181e250150001d40e10606d0101e4010345401401ca03510b40791702000491849005203426405100101c000c81c054400b14000d10800080350501c40742002d0822200ba40140032000d080301000360503150100320382d203060003400098140f580e05c2c04520400350404030b140344403540c002100500f8506280e550603501c1b9603002101541032600c0360540d224205c0807200540c100d041c55070325000015462020a0f0007000d244000c0c20000020300040e5001642513038500ca04590190507a0480042d17038089510852084501040c0140440e0300718907070740ca88210075050036402c0c0c4103400e0a102180c09200030040420791040091a0541c070344000e034411300b5141d0165aa01c04c101c0e42c0c0b110007007003048001b601900c51007500b9008072041860002c600034060b00e0142c0340d402c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 886370935 1250 886369685 886369769
    0x714220902150405030c010e030102070c031505090c0d02040c0207090501170714060f070309180501140405090304140409080705010b090a0b0303092101051510030e0606040b0604 78
    0x180c440e03500300c0c0c203640440c0c82c0240581b407400400d400550724981c0c80510940d06540c2000f905000810004885000e54041d14112601d14101020301007100c401800d100ca00e5402503131421955612400d8044466070306840201c2c1c6104429400e07460620503401c40a0000c0c20000003091444101d102400714100d40030447d4600c950311044403445200c5c100130590410000c201800440711564000e018287c424a481201c080c2c0c1d405940700d100030000c107410800e64403100100200c1d6543d0300030413403e0f101150b00304076500f08007081e65039030701c5684101018000d1840d18001c0d90350b20ba6200b0340890750002825551250a4a40940206070b040c2d0124402c1a420000c81c141740c06501c1680c030300260280045141029160412014024403104004c1000840c40c0080c0c15480a024050088c00301d50501d00010440c4030411050b084444075003001c0501e000c019954a0340001040307504158141c500103940714086011440600c030701c1e0050341c0740610111017551a80e40c0e0f4180b0f2080d280411180b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 886372185 1250 886370935 886370959
    0x12c01020715151e0b070804030c03060b040e011503230304030f02010305091603020d0c05030d08060907020a02090406020d0902030d0203030f0f160305060609100c05100606020714220902 82
    0x241c4c4032281003003040488101510081c0007038030461009100700c83c018104141442d035a42d440000d404415001111000d03198006456a410140509011030340d0381c000900c995036a10b442d00e4917103c4a8030001e80000940350018031500d4050001220000705130040d41d694a031a410114204c240c0040300f2030001c1c2c035000000712170f4078003c2021071400702c14180c40b00075541f03950204106100101e0064400d0b1110038400a40d60380e0401c80b11040c50600d484211080c58510200062120024000310035500000804001a9145005150701c2503201c0f100584484200c01a03030000c0c0018030009416204e111203004081e9000000f441c8a60b4280005812035581e0880121b0500304c15106c1014000d541904994954065004143d0140c4054803580c107140000002070f10100c01c0410b46004500750300411030a0010070300c0401803041041900b0710416140c103034001e40c0c0e400c2c2131103040e0440c9075100028156660b032031000c0c41d201494000a800503001201444c005007400f50302248560302d1603000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 886373435 1250 886372185 886372199
    0x5030d1e050a050d020a050d0204090506041a0f1207120807060c030c0f03050411061c0e1507110f01060e070206070921021c05010c020d02012c0102071515 68
    0x100c0c0c40d10b80d074650320385081c40310040031480650007442ca1a010b1120134060000b20441c148040c10050600b03110115407030a00d0030620044801c1c1c1c202d01e160404014a440c513042e1070380e030200f10010400b5140b540c601c2160210803800c0c41d65540104c9840d04140942d0700500002e14041c1a105016460822036141590300580884140320644804034218203076a07040701c1c0c001d0348420f5205004661101441540300f000580550000741194608074281201003c40100c0c4e1042c00a0109103000916508150400c03031232103d200188440100b284041c02a132041005001c1b1100041140e0020300c0b0a03620381100e018036030f030111204001489054009048036204d444030303000301d07000050303201000b40700d0200209280000d40300c2a038000d801982c00c0c1c010881d80c4030b1801c000700c1c00340e40002100001c4c558004c0c240381c2c0c01e0a5400440e814003140031003014030410303284c144c00b0100046000e030206c5017400d14060301403010040d01d15510300c05c0058502d02d0300c0d000020b007a9100e118601150341c5450b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 886374685 1250 886373435 886373437
    0x3200c06040303030509330c0c0a2303120612031204080d1a13020309010e0a0606030309050d1a180607080f07050a09050906030115060905011202071e0c05030d1e05 72
    0x21510140381070f10b0b100125403102c3c1c7d14500d0b4008811105681c540017100e001c030362400c92264021160210880100c0c1554400307100781c4006090003402462a00d5801682c03032a880c24083d24032442010f1440c040c03602d403c420011948200e0302040400703d245000d0400c180140c002005080209081c0f494115100c000b1404044074528020040e00d114140104884001d4000a00042d05990b0312100350040102c10170094403114880c8001255890552400405040d2240d03c403d008014090382c440006580603003035040c21082440620050390b59103610305040c041c031084240d0a000b040c06021400d580301026a10800e02d10192090070b864440c01140c0c18418001c5a2001070480d8900380924503010302d030b0350f8104c400180013081d42151408490500700e2158052408142410b20801540d60084894502c040c4080d0045042041d55105c04d0410b441101d01d001241c034580c40b00c174081108404440d005440060115510f00d074400c072004d480d00c40c041101400003d407000c0510351042c4144 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 886375935 1250 886374685 886374733
    0x1b032a01060e040803040f02010e0a121a220c170a0b010501020309030712050708060c190e0f0906041104080f0f1b1507052d01050403200c06040303030509 68
    0x41400c0c9186e50340c2e1214840601d83c07a034120704000c071521200009a651040520103040d1610141c4004145c510380003d00d5500c2280c40d00720324030540308200c24400c0d05e218050308060b0302d04800c8010b2040c0e141490411506030068a200f1542c2210300c125240300285c4504003610515503506182d896800580c2d59029020005078560700602c4140062001d0030000000188201d08480c203280d101c07001141059012120f40c080f03441e0100d1000700d80703114a2030004c810b02c0703142484411401c2d80e1001c0b440b60315640310450f000c0d82c181c202003070040c3c40325401692002c11051100391201d4840501d5a103c460105901c2d0702c0b4030424041c555031381c4001c154002001d052680d0001c45580c0d100c00d004003503001800d04003040d0310034070042001c118103006400410342840c40d800300517500002040b007200b0303d00400c034940c1d07032405d400c0000007a0421100c40c2223103c0b80440d82085030000d05800e14104002d116130b500008081400420590943c12172805030b11485c0580d10060028441b01143e00b50304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 886377185 1250 886375935 886375943
    0xe0937060e0f120414040f38060304060c0513030305041802030c091c1a0105120a05210c0f01090b1312120b03160f0b040b1b032a01060e04 61
    0x100010040134000c0000700820070005400844d20501c0a201d160231a061040f00f01c03000301e841d0820785402c050340d24000091482c4850074074054032002c00450f004d40002003005100f15911b2144c0202140103030241c1ccc82592103842c030300440e2612481c0041450f0018890500c40040c2081c0b0105048403500907688107421402c102400c100c4004104090385e40301140c900805040804210007181d60503014601c218408648100d0552600c030501140c610282c03c145c0c01c82e008000d00308005480401c1318640e600f602d03c840b450320710107940d5030791062140b24805d224604c84d40c4501c901e17145040d005011b655000d60180d801642d81e99001b8121708040b10802011140b0390421100ea0314040c01c101300c044289002c1c0001d144069001191500295020620004642c2d610070041155440b001d000a06402c005687c10a0314007406901c180c080d1028031004405810f0320000d0060040065401a9440502058100740e54405079031071440003c00060b665401c1100220b4550341c0f01d0711003402f030f0ba44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 886378435 1250 886377185 886377187
    0x1605060702040f02040f030f0c0605030705070f29010510032715020304030215060f150306060705070b0c0712030905041a0306010b090a0e0937060e0f12 67
    0xc01c0c0c0c00c020042011203804100715509000c04074a20407100c0003070f0055441501c084441280c0c50a02d00c003040c080d41d1040081003401c108020380b09911405464009503c00380301c0f03405843e1403414014907150040800c0003410300a00c0e61040c00444019a4101c030400c0c1c604103080241c0341000c40681e040308107100011814091200008910b41c04111312860154004c0e020500400c104441640d0050303034243c0040c1d0058000d030103c2050040f003d508140101c445124400c0c0781e401080012a10240c520116400440003800c5515144201c4407415440070a550009440d01a000e0050300103104507100d40c0b048440c00700b0003a2a00a0200241c0e81548441c901c461400c0e0030000501180040d80c1000d600540c01c0312880d840c10071080c2d01030315038292101e0b242c04942091212003001584004031274818081800302c0c80802042030300780c000c4a8415800800300c0345454072070b4040e100b540c2070401420a0300100c24440d0590003111141207000c11781e4a0248444a200d5451035020360202660380 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 886379685 1250 886378435 886378447
    0x10606031803050a0807020304050607060c080f09060705180301061706091531050c011407080307050708071704450b0604030b040203010b0904120507060b09040311160506 75
    0x200501704654800d10b1481200c0c54aa15900492034680000204403915601c2c0c240c040c00640e0404402548241950941c00340e62411440499642c0000340002c5c0a11000180c2d118010000442512540b84007078007c0c01f4032039a030040b2a20604104e10508458081c00740440c022030390203e20303030702d61250036103641030755444135040d944070040051f1580e481911044c00a400071a51103c00000990080f4058030900f62070340009807084022102140413000308016090001e40c58078180ca40142c0c6600c1d19a484040500d040c0c0490300c1350002c0503000c00709010071034056088120003841581d41504100c1c2c12504041c0201d075034003600829071801055002c251102812103803009001443c040c035070110b076207003c020200d50241d0141d0000d0b036007000b0000400003942824040c000d4065000e988030540c0c3e2500d51140c40d802040f5101c0b0404202d00002c0711814401c0766040f12004010040007585641021f140c0a0000c424810340e42d04503002d252090503003689454000401c42d10003911032840c0c40c3c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 886380935 1250 886379685 886379687
    0x60c0f03041128080609010204030b040f0c030f060b130b1807120c030b18010b0a05130f0b0307080604060605120c0f0309031201120312090f080309010606031803050a 73
    0x5100b0703201998211607062006010408248403243e01c034010108840e01e05400c04c807125040c54401401c802080e030040204000103088068001da00a030080160700a69803a4a00006548c61981c00a09425412901c4030107100b1190b20082140e54201c80303040802c0302804006013968101e01403954440201030a002c0c0c0c003412071003040d9000700b80b494108075200800410b0000c580d41903242c0c0000a036100c500030b1040c101005103c0c0c0b407800482074043e45601d004068940751007203910f1141046801b141c1c0340032600359031082001600d940f0001b80f406e20303102c0e00d80c0030300ba8200302e612030001490170021900c682040d1040d5000e8600e86c2d41c0d031525208600c00142c081001c09091001c03500010000c0660240359100030710701902d1010043d550310030001c1c010b00408c00040c0c10280381000c20340459400030303801400e2000840007034203011500c00003d060004000710704120240802d00000700704035174410194403034800d4038901e8a0401a52286444082d105c015144000740400c1040110341021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 886382185 1250 886380935 886380953
    0x80f0109020913020a030c021015150c2f0d05060c280e030d020c0f1309020a0e0105100504260f0a061e0b1005090105090612010503060c0f0304 63
    0x81c400252403128525102a02c003c102c0e4040586200042c2d590341d0040c0071a0703814403006400030743c040d1040c0080181030303c1903098171880388104040c80310010400e012050040354107200380c82c1c118080c020303500300f038115150130694604c603459024088007001e6481445d080400086d02a0850b005202c2a580d0741c1081c079007680264103c1b03500d0b030f400090040104290424002e00e03020719030764800c03031824200305051620041422401c01d64000380141c0016843c2d550174501e1131082295001190600320714200020321403520040c2d0030140265012604c041d5101001d41216000c1d11100075140e07488004507818000c0b40600c1c03c00900810f009034451030b5104241c9070301e40c03450b01514070303002901100d6031034400724402c110751660310742880b4642d6404198659950704003c22060000b0007184000501c03102c1a41142e2003440400318110b480b40e4403860039240d2804018040321b540b171340e0803600540c46580911425220b0312414002540c1d204456040e1440072000b01c8105040da1a55a0741c0244 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 886383435 1250 886382185 886382197
    0x50303130b0d02090a090230040f150e0714040204124e03050c07031103042304050a150e0406110a1101050f130b09010f0204030819080f010902 63
    0xb00c1e540901c0119150340d5040003078030081c00c0442006a0343c0250b6402e0450b0704110500400350020355841c0e0300d013060018903c0c1d41d881988a01403000d100c59915054501c06c1c070b40008440a145407039498181241c000420505075920f1101c00c65454114030200002c0e807107640100280c42c40903107154000036120340d150715006610602990903144404e44800d582d05c030768240703900030444445816101e068034560f2414401000385010300c640d00c1d100b407a0800b648540040241041002c2c015483c6058090050350301428854000c80e03408507103044c0000c10702202d059018452841c0c03a02042c4100101e00c43c0c020341142c503005003e0000d00d4600b0248102c900100140d0700682c5810307040600c04110070090801d4080f0b07449842c04e20101c01852801c50340020030200c0200c862500b402660054044044485075000c041e420306a6192031181d40500107242200b80c1040c000710340402013200e42d5028001d00088014000308544548004440301001500c01886011b044001405030210760303001012 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 886384685 1250 886383435 886383457
    0x5040b010806161b02150706060504060501051207030b0405010b0909160c02060a02070b071a15032508060403050a02191113090212030415020606060a08040309030c0b0a0801050303130b 81
    0x4c4442d01c940116031010b40091002c01001c50020b002c008200f210b1065034040c01c01540c08000c030034100750000e0001e106009207029201700300000251501d109030807801504002400074405541e4902c44425560000c0450300e104252010000784036807400e451000555284d941c42c10202c0407541c00b4883c0642c0400803078001c41c01005004500d045100c0001c1c03054520840004241c0c000022581d0306050300034111070201c04240c05000b9071030b07500092001104203441d0107095009100c3d1120345440034260711800a902035801001700740b42d001004bc0102551030380a854401c03041400e034820520003070b04020b00b10b100c8543e10382e215003007110500000c1203201ca00019050040d4000558907100c035a40301c0c2c00c2da48001390501c80307000c0302255080c503000340f40024031050070b051000071070501990890b80300704030640002509040c4900041c40085801000a100b026241c00781003085601101c090b40101d5003481c00001d07541000030844060350f44c0c0c4001041d01d00d00700342d01e00d0826404200c0c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 886385935 1250 886384685 886384727
    0x3150904140105010b190509090a0b0d200f030d081b0d09150e160e040525230904060b0a05130609051803030f0a0f020a0305040b01080616 61
    0x1140001c003481401e018010104510b0703200c4034160500d03201066a918881c0c10010240100922910b0300442c2c03680200d030340100403441440e04400300c2c40300321002002900c0c444401ca40c841e5500707440c0040c400d00090030b071002d40808214000381a0748181c000452000103075020000395002c410004014209105050103d107000044103500c400d0341d140640581d12044010403083c0040018841c12180e500c004018001103920300c113415950750712611800800545d02000201003003800e100424042645c94420040c0d4171049030301800650050055140c070f55042c40d4090b1010300b4520400340c25600040403008503545564599024011401c000d80d000512950041a16a5180007841000c04d404400045552800600205440780a01021200f9061340342000540b0710201c11640e01c55a0001c42c1c402a803620007071500240b00800e0b41024062000c10140261580742d040306010b01d010344a03d01e003590701d030b00d0079540307a00007960903400c1884050019408079000307210050380310200300465 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 886387185 1250 886385935 886385963
    0x1706180103120305220206070f05030310031101031a0f0d080c01090302010524090403120f060905151f0207180e07150806131e0c0e040203150904 64
    0x1820484000380c01c11100702111204440344103a240c45403e62224021240800840e8444c040401419000801038002c1400150136014130140c0098010040d07800340c100d076501d2a0000c0000c4840c48180011900072a8104446110b50310a0048414a05041c0e070705103025034512007006502c2540e442660b4000744640b480f50007049201014110100358240085205c20541c90002e0131503000034546201410a0f05000a11030b600c80700700700601800303441102c580c3d162420240c4164403003581d2030039030b507041c407444054105054001d00200d95042c1c0041c0541c2c2c03130701400d5008101c08038206076000584070043d40c107402101c1d01c07100c03225a25401035400b59030300c41070021505410300a0034082e142e29401240070750142000f02c0001009501c0001207110b58844d4018042d81014240394494003d400c00e900366056540d0000c005030010f2401568507403a02c41d4002d020749405903070340d00424202842000b0034205070081340c3c07140620900103000900c00504010098801600540341040c415100c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 886388435 1250 886387185 886387219
    0x9031205061f020f0d0801030b0408070804171b0103140a180503072901030f0b0a110c06160903050c04021e1204110604181a03010606050d1b1706 64
    0x2d04524280140d014001d54280c1d910600d1a0040040c4400d08001c0302038010808140078030b83d4144c015610040c140d42d600c600b400c008243d0b006a420210300c078203401e0881d00b07000c0b03000101c0c500310b080401c540411265140005508588080b41303410444a20040041d1000c0300c039500c001443c3c40c0d0765400c8001512076454991454110110031030b2202c400741003180c2510761042e0700101441000700402429070459558606201000c90010036820001000c119403000316004203144d0320149868507150144805151340d201c10a0311000c001c1c54041c4418000e0501c01c21140081e81e070480024110184c040c0103120081d8850282d114200c200402c2401c1c0404055004040083c1c60102144890800b42010240c080c61462514410401000104401c0400d940310884860807100006602d40350410b0a640c0008a07120880e41540b0b0480c2c04503000b60060050405c049100d0001c01c40500800c0300302c140d03511502101c402060088054203e44080c402c129584000054038640c00103d500d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 886389685 1250 886388435 886388479
    0xc1e0911160201030e250b03091905011407081f290d02030108060a05090a0b01060c110a1509051002060115050903150708100608011a04030b0c07030207090903120506 73
    0x560440c00e41214000100801c6c543c09800c060840126050310310304180c1200c41c0da51280c0040c6540001c50384042c1c105004c800e5010842184201c9182540c600d2302a400600401c3e0448010b03400340d000403541600842d040d5840d10a54092219048101006076941c00714000b01201000c0181d0080051a6405070303140003440c028104807006088038103109401c6400d8410081038586a9030000c15420045035012610a044401501b000c90f0131a10b9420b24002c009424400c03d9040350a600c030000b150b042d013400f261008a120758980c01c0381c0e900d0f4401c10032030500742c40c03040c00147e000100611080c1413150300908071b0022820454500715039036000c00c0c1842c08980910b007600030808104000780f07800a4400e0f82c0104880c80c8800c6041c00c0503130182c5a0038040c081c40d00140c1d00d0780b0010b448034004400300c8000e10307001000e40e00180340940e03001c00c0c2c55011507002c0313005000707285002800e404a80122241998035032990f10020a5045207440104001810340b03900c000b03803040900300003003010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 886390935 1250 886389685 886389703
    0x70b1c06081204030b0f04150522120e0306060604031e060e06040c2c09010f020c2401140f0406150905011d06070b04020402070c1e0911160201030e 65
    0x84a00c5480f00d285080c0011030820003006110100c800703074100000504040c44540c000001888009002d40f0f42c1e02c42444c400650aa640d82c0340da51565024083c0100004a900898002c0d070790700310800001d60078562038407400c0d200345400503803e000034800944060f00b000c01c403070018a200c0f505c10480303848010a13908941e0341012260071007014401800480c5400074050140c0c102c032617190380d401d903446a04090580c110078200a00c5800030409000080d002846240a80001036486003425150035849040048a4020140007800f00000d1807130b0b81103655040742c80d50b00a100081d1618000d00c5011440c1e80080c0d0f134010f645600104540320301900c8450401c040365507829110b800c3c1000500890400005450000c900700c03043e6500d03960705012145e40030381c820749412441c1c5441c8042400780c0607041c0014500d4016580100e10004840c007412080d210140715451800d0782c80d120502207805501c0790b1502d032941081200c28107100c50380b000c40420720600d400111800981811800d2000c84 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 886392185 1250 886390935 886390963
    0xb060d0b1e0106030603050d210207051c030e030a0311070803010b09100e03030d0f0b0a17100506100503070903060606050d1d0a17090a0b031602070b1c0608 69
    0x895030500d20450301e29400707405402c45007001c21009095440e81640c803240300440d1403c0007030101117120303030000005508040d000181419521058289400703a1540d000c1ca0070a00d13007080c624000c81d51a4800d0280581c400400c101441c1b81c41d180d40811030207007109149000c45014200007200010b5840001076008003080309005489000a40411030414260b13400c030310400c030800b201c280044d03502004039512400c10140000d151041c3c2c144803005070030000080c56004200f640e00144004540c00c260f0340c000d0300d08060350b00301209002103030102d4030191441d61300a48452240640c0c0f81c0a000207581040076400c1c486150390b86c84c0c0d681d0341038900c281c00c640002138020500900d22540340c000c010b000a5600300342481ca449041495940782c0c01204c0141540005540201a1001e40e104503010302c4000380500c0c11b480e0302c900d2051525030040c0ea00509042034103000550892000c1040000d4440400c911890220800e00d045859044190300300360007907640d000040c00318402c2040300c40a03881 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 886393435 1250 886392185 886392211
    0x4030503070f0201080610020d050c070b04060e010215090a02040e1504060e0d02031e22080706090806060907050307020118111207061b030c05011d0c030a08070b060d0b 74
    0x9510004001105c00380540b0f018800b1002e00100d102d8002c1569080c0045c203241c41a150180010755a10340041c035030103198611070019008c070700b050f031102020a000c0020707000c407145805404080a201e110413200d02c01c09401c4100060014074040e006548140c4403d13007210060941c2c6004280700200a0b2011034280307a8078104210409002d004e60021307013516002640c01d128511381d00900c001e1303c051040559400015400461070026107803514080b2865a403e0305050316031160035501c922a009003408205540c0b030004070408009601840340e4009050401c25072070ba001d05035070903000605803406554849440c440d09412651288030700038002e4800b000044042414407080c00d100070440c1c030060b000740c90284170090b00a00742030104401400308001c22034040c141211800005480109603500380040c52041c8080700d641e8402e440215020364030241e4600c000c25550312460036004100c043d06000c1403002c00c521803001ca6000030b0150445d044580c4503902c200e44c0101c01c941e007441c6909 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 886394685 1250 886393435 886393463
    0xa1101090e1320010503161b03080a270b06040b15090f0405101202031216050d030203060a0512010f1b03050123041d01060b040e0a0c140307050403050307 68
    0x8201030459424050750f400781c51141e000b9000a1440c0310060a4040f00e40105c0ea131015440e1080c0000f60b003500c4c6a2611201c00c52541c60b005003400805d44900c8456030800c0c00380d003401e10b01130100300755004001c002500560b90300e540d107100580000782410780c0240d44400c6a42c0c640c40b840044140b10440240c0e07682e650006d00b040040140d528410786010314076000070403581220710381c100c40c11740f01d04034001c030401c000b1440001d1801d004240c02003424107011520f0401080044020b04295200d0401e40d5071a08007144114100c2c001101c02e641c1c000c001740380401c440d00300912040c2c141c800d60000890308194408034030080e01c2c2d884c09602c400c021520818495164984211030141003090303200c05000f072400c0c1015500000101440e486190f60301e000340700014200c03080c0c0d01c3c60029071000f403140c540d803143c0607216600a4814130011410701000141c1d18400d51080c480c1c40a03071f9484100e40c03082c20301c1d03664215401c01070a0000b442400c100110104030101301400c07040e841581407000ca06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 886395935 1250 886394685 886394693
    0x602060c0309060609041e0b012103080106031d0d0503060901090905060c0a02030d05150a061e0311130f090e1902120705090a05090606060307020a1101090e13 70
    0x5054050850081c81030001e040000f00701942c000c6000c982c1d00c445500c0e68107100340740326004101c248600d549800390108000042940c0d604956041e4015003446420703140301e015000780481d0090010707075004014069030340640d020321400a20b07211a000903d011440741898890070941080101d0004410481030303242a40e50603001d00344541c0103102c5006144d44095541d6405008644000808070b41c0c219218400c00903641101e082500511040c10031b845408910031038040b1741da0182c0401040440d1035030282480b08544240e109804041c1c49042c04110001e04030a4041d2682c01c10400100d0703603108039080c18202030118001e030740107030f985048460003c680c0c0174408080c040d044000041074105038280324a03080c5405450050000365801d140342d0520161b40c00407075100c0e08502c103010340020340381d00ca188503690440848425407680000c000e080d01084440f40c00603803044800ea000503510420f2541d464806052500c445034540500c03440740c60040f2580008400b143d20704001740 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 886397185 1250 886395935 886395943
    0x30103061d1203011505120703050403030c0f08040206030c07080f090102070e01120b090708010f0911180106050d140414070e0c040302040e070801020703050c0601051c030e031c090602 81
    0x284038079801000e54082c0840025914081441004401c1500382c1c00c2c8800035003c2e004031101903140e1190400c261511040260040c0301c00c0e1425000a07240203466502c0c0c03402803480c59003045c025207800d00c00c2e84d1703035608100c3c0b03540c0001c01c940300c56030b000e105081c00a90a41c1c040d003114017907054502c0e12982910002490030045a10150100036003c004100805603820f2440000750402e41c548560b9845c184014070380001688140c00a41c609030513000040080d500002021b0b00c50941141f203600c0041c03c0211f10344800080c94441540c1000400c00280100002d2184600c10180411101852004907044035030881c0c0c10f541c41d2203a104222407130070003401481d01410400c41120000c0c10034014543c860300860100134005e9942e05883c180b800000c0112100038082d0b40c00170f6640e00704d10b02d4014102d4010314103c511502c030315000403415141907035400400104600c071008441103a6201202c000100450158241c01102401d07400c600b94203440c0d00c008100d43d100d642207240346c24402440c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 886398435 1250 886397185 886397231
    0xf0d1a1e100f09020306011110020735280903020301051b0306060c07090626010504020105190309050708031c0b030d03050c0f030412120216061505030303010306 71
    0x185104001401400c050002074003c2e624500001600c039590840180d0b441c2c1c0c0c5c8003171104814400d200c0258400402e44d0002c113040783c41445004d94000b030361040d01e624666244218090443c00e205408560f0842c1c2010b010b00741145480181d50505090089013846580192440099182c090070300c2542024082c4a80201340504203c49140808810800c28000500030510580e400030311707000c40d240204000d202405a03000c0800a9070390303551990003c4042000f0148851485401e090b98511040c4200c91081d9010703140c1500d4104940025843e44013108089418142d981e4410390100b402045418040c0080d03500540d5200c01820035240e02c0820f91403458036072070038503c040001d914007254140c03030100c40d030401241580322031862402c24081c3c210b41380c0030650040104001d00095524070801c40081c1d8540051041120f000070060313102e0fa03846031748003c3c044001c01000a400d0f600005c1b0388182c82c2c00c03001c9201d0f1210300090441d4420390066541c20380718203003800c55484000c60b04030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 886399685 1250 886398435 886398451
    0x7050a0b0609070f0809030c0f0c040c14070f29150a050f06030903190f1205041e0212030a0c120905030d050901030914100f02090f0d1a1e 61
    0x1c1840c20f400700404a06103041c407507007040b0790343d004184400c401304142e41340030400c10103403501180c54211442eaa1407401c80c45510071803d09030070342d00142c0203002c4110b40382e81e02000540381260030307101d0b090902d90390a011205115044040042c1002e80000f081390003031180c095841500b040c2044d0340c062503420051510820070840200500d0351821400501d041c400e40e07049407070380d540050240c11409900c8104c01702d1b5400014460415900100b00d0120300358070346030f400070081007450040403240c0403540181201100b0880905400311227500b4040300b07200608030280c81048a54441c110341011a0810100b10441c941104101000382018401e000d1407400303500441c80c00300000e0f038031f503203840b4480f00303009002554881507446900003901b659007001200d03541407940c000d0300d651003035400c44c0301e4139043ca000f0f54880100058021210860401003002c454490420104500b480b071021044901c2520b00b104001c0e11082e1180b1248079a8003a4502098a4008201c04281103001404c0b40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 886400935 1250 886399685 886399699
    0x2f0310050312160204020c0703050a0c0b041802090d05070906090b0301090201210e0a0b0915061302130e090717030310230405040516140d02012307050a0b06 69
    0x20306441e190605440c032031034801d2046814043c45001150080c400e002020030305006692010061041c0010310104c000d109280f0840615a54005151a4000e60140c1d1a0041541e0b5120182800f43e402900c209000200b440c040c202c0035586080c94980d05501003200a5120b0600b007000034030500c641c42900800f0b80081c00001007a0b400201a10030444569000310043c00000034404940c0c0d0140e100e511006044920340714241c04d000710340c840121840c814612850000f8403503100e02c40c4005001c0d080c00342240c00f0355410503000001035000268000c944a0080c01d0004051150f1024540101d6804001c4d0000504110310784900c00c4402a04003043e910130070a101e00300320450702241c115034003240b422401c910940c2500300c141c943c3d00821540f250618051000b40000031426080c42d060391040c8000b001c1e500c1d44a4003102c07040940940c3d20104102c0b200300554020021b0396501d880c4007890f510810a0106240c120b900240425a015804040d0a00421050b0200560418000c44840d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 886402185 1250 886400935 886400953
    0x102030903120907030f0318050d030215070311040b0a031503030512040f120e091e150a0b040e0a0506060408030703301505060f030a2f03100503 64
    0x16540d2080e0800b5000d500105800140d05140c10f0040c1005190b2003d45840d204c0320600f0300820340b04080301c4110a8032003908000030760746040112080308944c1900503202c07811001c04812201d800041040040c0b64a90704401d074111000c50040008e0020915030765203600e18140024200d40c4444200b4141c0011035006001184c1c01c0310a603110740c4070000300141196170ba85492002e100d640030008100c07900040310030340030b0703504020381c0003034480c00341c404014a030b442c03a0110344600910311403002200710050104d071224508240b103940081c009040803044d10340c0c0c0c50440a2652040c1d1040c21382008103c14004080c4883c0503168000404a4030f81e1b0905050900183e282d04c1085001800e1100900070041c4c24903d4003d01d0645c80c2e11007100f01004070041b4070990282041c0c1e0404085404000c030041020705d004d030b090f03640c0740b0009041c6030b00315030300c60616100410040d0b0090206d960b19401d80b0f035010701c0030480c6a11840005203101d40701d04195810072014240c80d00014440e0f0450401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 886403435 1250 886402185 886402201
    0x120c0b030c0304410c1c0201030b0a030b041406160e060310030b010b072604151205040c05010216290706050f0906100f03030c020301021306020601051002010203 71
    0x1c0d00e8100d40c21002c265044e1400740c05030300400301c2014400c1d4481604a803032100c280d03030310300c51a14482c20784419644281c000004001a0b5900c9403a02c01c83c0760101d50140b000755200f41d20520003c10040c004c415000e8481d2283e03070850300700b00ca04440000c101e084051030f1417024085ca941040c0f20005540c2402d00401d009044401ca01035050f004d040c1c0440001c2241c002010600015a0060224002c55855041010a941c8158025a10350800b620101083c4150f4010000000741c00321001b4105401c2004402650040f2401401000750a48070042c142c170003031142078021072150405401e150310f820000380c10b007121500400c005000b8034500b0014610714054040c00d440420049410303c5030220f1000f0254000e2003405000c5a02d0801004107021004030268004c0100b1012134980307580d50303860441039040f14003a003546000c001c1810030000c0e0150140244081c4024009404d0a800c1c403424003c041d01d66001c1001a030088004110300e0804180750180300784035200a51851420f000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 886404685 1250 886403435 886403437
    0xd090311070f0e070201020904110c1908042c090a0b22110301060b0c0601031109190b04020d09031e021b0f012003030601031b022a0a120c0b030c 64
    0xc1007103480380c0c1c40f40c0051403040c403e6048400300c242c014000c012044c0180c080700c10a400081d18155035119810f40080202c41c0c0c4081d1840c5a070b0302c080070914060414188040410641c6060854030301007142041605e201f8070078403840740c0c0c1110700074103141c0704c5810540c1c007821001d0101a80400c512550068800201c004a02c5c80354015007129041c01c01c13000030900400d21a401290707005d0020600c3c0703022490101d035160481e03009500d0502445003050801c042c030082a11901341c80111800003140034100340d0007007502c00710000d00041c03c0c100101406400c0d00c504100842c001038040e982c40b8030038001c508100c005040380303100402c00d0450400e503451284a20343d0b200d901c1071201a01c0d80002d68401c1c1c0381c03000d803281c03039042442c070140f001030425030380e80c0080e0340390703400700c2c0c10031100c5036200c024440c092111007030540c000c120102d003040304007a004200003e0b041e0f442c542454505115112441c09100500901121500e0440b01d801c000700766480a030000755125400b003040c012201f0b0044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 886405935 1250 886404685 886404689
    0xe0903070b07110f060a1b17060102070b040905070207060f020c1e100519030213090203040c030c060c060b04020a020606120709050c0307030b010305101e05060d090311070f 76
    0x100d0603042d454210066481a400c021891502d10494400c0c504220001c9862406090070040503c00c02c5a091040c1d0014241c60700b010001030444c51105404114400320140c0050301070060f504400d807079003241e6010381d00503041480f403181c42c1e800b0b000c64154100210802484c1629014145051982000b074640600c1850244101901c40307528160034074845030850f081c503000346942d1212146c0e85014180c0c1d08003914420300360000400c0f030403149009000300c80808120444e6810322508003c0003400031b4101401c1500e804464030004000680d0b0385c00100701814154031030b61415200da1034001d059980141070540207500511106140380d0b000210329410400c120b8044003031148100710140341c02e0140d4442a0b02e076003014107000d0030030b6201c40214040d60b50340c1e5052112862240055064072000e40e010007608101d000100f0503501441c10041070343c101c0032094100d49598900164580c0c2010840511082e9214180c1080580111441c144e5100c000d02070b180032460403904042516542c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 886407185 1250 886405935 886405943
    0x90204081903120f0f050703150b04030b0412030b0d0308060307210803130501230c03101404020f070506150a0b09010e040204080d110d030b0a0b070204060e04140105010e090307 78
    0x1500801074800402e4110200c5c0114041c02044980780002000740a0b0001e860503007620368101c0404580449140b04560a89400c0520103055480e541d58a480010205424004040e91511406065507928400c0b100e007074020703664810b007400e00108050424643e035000d0b5968040d20003404150452050760340d03001c540c000111035100e688802da15a82c0443c411b100500c154a0301c00c00405030204800409407110090450056030f90f648005044c1c03a210984002d004500080000c122071980141d40d0b030441c04000e0005410004841c44070529900072040440b001e0f08188108202d08610401e403089010003101c0c8801c80c10314002e0710446502c140e5003070f5410084001c49202803525550110b07001004107001301e41c28110103400043c8601100054519076000340a1800c0015100780161255200d00038200e04415160200b900f909a0001c8000ca801a4482e0340c001a0070184400d03c0303100d10300031000c099500c0c10316141ca50840348140c12410309a40181c00703002c507480000054503001544 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 886408435 1250 886407185 886407191
    0x3062907030509091602070509040b0412050c03131517131b08010e0f03040501090e0901090b011e060810030326070c051e2e0609020408190312 63
    0x1800e0440c0d50f03106503809590400326140c148000d03026081e11000c03243c1c0d25a400e9410071611007040042049040d42c015008800f003502003004514420343c0e240540f80726040c111320342111070300040e0441c1c001401090456a25840c20454441905000c01b034200303031450850841c00c03251036123541d0300b080074000e001c00040301c08000080080a101d1003840082c081e0300da0310200c0d60307a00d005010b030500004001c218041e150b9290482c1e11b0000a940644405840b4a0301d0302e8282242c2d00310845000b480480301390f403254040808611800841c5019007001542080c092005100c60310404001d036008500300400c1c8400c110003d00601c0d0702200f940d900d0300c0e00140c3c04180ba1400c220544400380c410040c0b40103030f0280808540c10000449100344070b1026281907035003c0c0c83d01421041c542d43c1c622b4850700282181d410300c0c0ca0f00d0100300710307940c0005c070000c0b03d0b02c41000d400d404489580d00084084c3d40c0c001020300885030100403414003070301c07190582070205500e90350040c50031840700d15100382d040e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 886409685 1250 886408435 886408447
    0x1c05071a07080f130c0b1c06030b0c16021906080c03011d1801050a020d140c07081b01110d0e0d020d0f03060801090b1e040803060f04110309010903030629 68
    0x100c4d082514003441e00101112449612003c1010300b540c86007140481d1000340c90052014007565000312421a41c0202d1651f04070307607541762110328560004488a10340b09074140054011307918030842c11b0034030b0512210024854104900a0040400985000c001d0103040c801045400e03000754062804042c0c40c48118125102c07244410078082c2020660b005a50800c020440f10003d6030740600908002e0400c20301101503c02c6481c012400d0903a0400c030400010001070b408280c00e800241125000c2c052041c2c24002d017a446c80342106c24450038108840c0c40054160840c405902529403460034200c050300d140c11443d400a540c0b254407e041d030b028000c0c50030b12114580c0c007960101e802495050001d114400881c90060424101100d010f5105c05071002c0201c0c80000301c54071b90740324541c4011094a161109000c0140f40e01c0014141a401038a07140c19000e584012800346001351005000410039070315a01d03001d81030f10004c2e001840e50221340f0b2103501040e40380e8100014900041d1040f603580300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 886410935 1250 886409685 886409701
    0x1202060c011a0f0a06090504111309060519050916140406080a0c02071d090a020a080109020f01030b0102031204051015080d03020a050d0b01021c05071a07080f 70
    0x40284501100c0035440c06060780300d007503458444444582411608060050b14507400c0190b9a6410b005550002c0c2c1c14001c280071504056005844881c010126507081900d58020300c40a0303001c513084405000d84801040166040000d070082403070210f07800d80301c2254288030108041d0b0000030051100c0d031322130f006c03003102c02805451042e010700c030b8866171141e80365102c11016200800a45041d070507189400452000544049a000142c3d654a0005e60079243e5141c0000e00841016092101d280564442000141e546a01c110002c021090010400310030a0040110500000c60064103143c1428200d4030039a81c080704442e4040d5510303051001944460400605d4104550610780241d49860b0781d4010710b0341d003c1907140464444800f2100c51560400301102030b40247c0c104040031603403d10880303542250fa134101030b15081061040700d800e20038400c29400c0c0d0446586080e03000c03800014413042800a040c40400282c2ca140d110310341e55040101d4010030b02000103021103002c0fa01c01000c503000e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 886412185 1250 886410935 886410937
    0x9060506090904110a1d09070e19020405040204180b031506012607020c1302090907030f1b110c0a0515031312080a0e0f0c090a0207060f05070f0513120206 68
    0x25010344500c2040c0d454a8030b140c3c980724a811518000c1b056800012610341000032880d064817004004103106854500d00024000340c4051403032440c0e502480080303400d4945201610060513a2011915100401d41d10303c0d08490030880154040d402c035070208400c0790601d40409800034420310b0001c1261040413000014032001d1211011065441c0c030511414590011f81c04c0c01d000400c5442d4411501c82c0c18030707401288103403114242c204c00c00100045025003c1e900c2198501e10400300490710f00c08104104445c0690120a00007240c208150303105400002c1101041d00d0340e065403009413280c1800002100d580210b0100c58020000000148034290303410741d2166616030144800f01d684c0d002c0d50300900040d404851103c2410324086003807407c4880064982d56001300100503001040c1040c0900254035802490b604455070200301040018081c0d10680341103001441c130001e524100000e004120880005500303080090034020142d402c07142084680131100c444c02c066110002e540301117941 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 886413435 1250 886412185 886412213
    0x9080a02010f1b052b0206040b01030b0c071e060b040204080703020f0a080604150f050c0a0c030917030912010b0109120c050607060b01181a0c07050a080f0709060506090904 76
    0x3c580205d5002c1503462030810090ba500d201101c9000703101d244803000403a603400c1e04480c09020403030803500400203d80003000441d008070000460518109d1141c8500001c5448010792220310300320040ca45e010301c10b1611454108810855095251034076003040641c1e240010300001c3d10804442184442c15076a10300740c02c0051440d41c0c10345050b0324080c2803096407522010b80d403070300d004d042c03a400c61401c01940c4501d40c0700700480100c00341401c0c00300c03208031062181440101c0038401180b50206a0340200d28141400d8280240295514440c0c1018444a01d513003400e12280d50f0f04061000350542e1304a034803d070684413514030070b003034a90050425010b4004140d001c1030304614009117542c00d01141c2c1e0008142c3c21404c0e201c04c082094030710784580100101d0f00c0b8030000d41e400191030007005218103001341100d5070301100301c41080f61610001200e4100641c0076501d103900c1800490b000d041f00707109603001044c9031310341000100c0c41e10011403111b02c86c47c1034030303442000010f0010381009070f4800302d020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 886414685 1250 886413435 886413443
    0x615040506030a0204080a15140403050706050717010b0c0f0c01090b1c021605010e0d081501110d0f021606021e1005090f0c03010513020d15020a020105060109080a02010f1b 76
    0x440c0c0c0011700380080c079886023002c50401e081c10203e00c08000000180614003403135059a6584c680f044a40b61103000f090003901070000c00442252051589503050162806003400003002a503d80c660302032545011101e210400d404d420640e03509100d030ba00f00d20034404a4030b201d050166648001da003216000d90213910000012840495401514070307030300d40c41c10180ca101300d008101c200c040ca8041580c400c0c000043c140007c000c0c00020b1000000c3d500644040e442c18141103800903e1002c2d12410200d020100400141e8414080642c807941040b403144501c483d045041c0759141000300080d01c80c0c040c450110b13200d070580c840d13500c1d141034100036249040e160000d003001702d41828112030752180400b4950408500c0355020700c200d03031f14040c45003501440703910125900c070040d81d030700740310051001b8101911030000e02001c02490101c0741c00103182c404e0241d8000612031038203a0000d84a03031001e402014a540c018401000140d80052170f60245480c0d6080c0220001d90604900c0404c40408400034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 886415935 1250 886414685 886414693
    0xe1806060c16080a02010908060f06041a06041d060108070906030914031315020304180c0e090a05040203191203050c0f040902040504050f240301020702120606090615040506030a020408 81
    0xda904020548003e810301c02d80c0c2c0c0045055232041419501c0d1400c0d1135840810f00d00d140800d10034501980428407460800900c41d0000c03c1b2000011502c0c1c025074404154044100300c22a070392080308540f658002c000b400d2101d028100940c0080c018120341c0070706d80505a49000c44001e00186005c10005445000102c9644118801d21a18604100e12070b520301c102d07000c078400d42094008015a401e03103c070380c1a0102c4103140701e012040504280b41e07d4070140010103206440984800d84440e21030b03e002040400c1d03504042c4145490314104042c0340003908041900303d40000c80311009a49122098613021401e916000707800a40c80c03103840320070b1243c200001000243c0d00c266402800880748125810032040da02d08000700304200084400c1b910901c0d0f5029540380901102d00c488a0301c00c0050001800e00300c488c1d0208000d01802462144107074080d40800c849032600c80c81c06503128000f0348003002c9401483c0ca02a0841c05180952881018084006845011142e0588009004807000c403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 886417185 1250 886415935 886415939
    0x90304031e0201030509070501270e0c040e06030c0609010503041b1806090501030f0b040305040e04060506040e0a0503033108120a0b010806060306010c02031005070e1806060c16 78
    0xc910407115904224040b0741842c0000d101c1d08030201e41c030b204036001a1150314090080c0703400c90f2100d80e058040e0540c80440003d02050b074a403c07402852290b01c41600d00b603600c904040000c5c403a0000180030511981c81032410320080d489a80582e010301d0000c3c2009900d03501c2c1c0d0302e4101e4030942072040d10041e082a040d0300240340e90b03201c5d5a200030349641d80c00800841e03441e0440c81c0b0035a402404003070181b50500601034001035003091a198414024a0150305064072200702542d21102039400f5924142c403441806100d01d0103200301d10b004000d01c0001c2c0ba00d01c42035580c5c19140d000041031048186109103140c2c10b0300080d001d41d0b442101101c4090329007250646824021f607005101082d0b03402c2000400a04558902c3c441e880d0111816120300b0040d0755148100503180e40000c1c501c5040122062030f01e07005803000c0145481001003140003080c1031501b2200101070100c0080071a114409008400c401ea0200b500b0590b007018064034407a60341d1580b800b486103485090304c1e101868031418240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 886418435 1250 886417185 886417223
    0x706021612091a040e041b03111e21010608101a0604030b15010318030f020c0d020d02061612030b0108010e0f06040b1906030504060b03120f0309030403 67
    0xa92544a00c90b01d51030002c03910b400c03002c048118081c1451002d410200418041c10190040043c1d10074402d44031903c01e03450302c400c59810500158011a60b00d0b102143d40e0000c0d01e050326407915001064403070642140e045e28000784c0070103040c4040405000d1038800d01d078140c04003900030310040c004072030843d650710044040900083c90040a030611002c00b01000050f1490300c002100c0440b43c0001154a007500d4000b0716810300c4501034004da0500da603400d84440801c0003004901e08c014041d80b280d10b03840c8141341c4040e00f08840b03060960706ca00b25011103600146d4480000100c25034043e0342c2e01d92191010443e01e40040100035026004210106602c250944e0540184620074001c0e60340251030b90b6101100060b0a4050b642011101090000104c1a0505c3e601c22050710780c0041c0a01241503c0c410113920021032904030700b00107901c4e00c0400051000c40d008918800da400e41c002d12001c0315801f210306140c041c10040d0f80c0603440020200300703025010401e4802654005916002c414000e1394 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 886419685 1250 886418435 886418453
    0x3011d030313022425050312090c0907020a11030c03100e010b0a151b03050904090c0b0301080304080c060c06040b040f080f040503010e01051b0a030e030d0c02100e070b07060216 78
    0x711742d1030740c04d80c120801040740440001e459151a07224000754103005440006c54840d40009008003e1881000100c200c141d40d0400040e0003640e08e600505a00c0f116404c10309020340e01d0708049130013607000e03142c070a02940380041e40b0f4819038a401c1d40041c050a114228501625699407004ea0041e20300d900814500c20700c10703404800218644900c81c451010038000c0e40d1725000501e01401280c014490b5a40504113a00415401403048008108031030f1900358015a03500283c01000d1968000300781403060001c10007030b80c06040402c80300b203405e243c6499000c99465400820040031020014081820030841c42041040c1d141d21007851074880e0610320b000003031a08248a8644a9820146840345919040c0700d103500540750301e90a50088040103028480c1a444204140c0415a440f50700f41602a01031020745020242810045080301d40c0a0000f03292200060103000035910b0031001e00090107000031020100d82d16010a544c0341e4407141890002806800d83c1400c20707020b1079107501c0c10807140c05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 886420935 1250 886419685 886419697
    0x109152d06080d0c0c03082b0522050607050a090801060b070b0601110c010809031308150606030106090e04150c03050f010f03020102030304020906030c030f03070203011d0303130224 80
    0x100f15407190180b840c00301c80c21030140a01900b00c00d1000002c1c8007245c0f1f07100040140a040100c1144412040c21101e001605150910444241d071103060041d000302e05403251034800f1401088c0403c1304880d840d00307600d0f03401c06044001070000000c0d081c11a240203510280c0140340e940f0080000036941d03500c440d1030b03900030354040b150202031400041456020706050281d03080008002e0000c09026070065a6145001d428001d0302d110520190541d030050183d41d0001d440c8102c0074014520104003580da180c000508564480c0d03800380011b0000c0c1e42d1200c0500121340c1d03c0840e0f6071941e2590b003024200c1c454070f8240346e100f05003441101442d049e01030304124018000c2d0780060383c00b60303601c00c41d000345024a404001e0050704100003042c0545400b803002c2d60081070080c02d88403011400d000184c6072000c04114001160800306092043d46402e218001a01600215a00024031200d40300c94680c031000784449240c8411016000946d07c075101c0c822903a45c2c180c0e204240000e25420301c00b031260002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 886422185 1250 886420935 886420949
    0xe0f1c02060304030c03020c0922230114010603050603060403030b0114030c180103060b090d020a08010c0f0f0804020d1509120e041a090705071707080d0e0109152d06 73
    0x1e041c0702c61581c01c00a40711031003000c0520807030051000700130b01200c0c0700f40202e000b62601d02c02000703084006018402020700c12422f0f40d00000c0e240e5008120034091000c16448402814580410401640c50108603e43d00641c0b40c03800140e034840c07020060380c4800030300100c43c0554a01108110405140d10010034000000484040c2c41c1c2d86403100440507610f0901070541000828445220581800c06101c1640382c13000342410716003078441d0390705821142010305020004003070b400c1a044130340d0480b081541e00021072a104909241c01d4020400310303403090000405003501c00d2070880b2441e1541e0f01520059510100030030203001001e5005040c03034104616184107034948100710103242048014074000e4071001c0d0403880315a807055001c0e140e54100150944400e04454200f404038902d040007048590310510b820742d11244400e07495004c8696800c605901c0340e1500c0707208004071360082c0c00c035407600842100100d0b0205424403516044490444505e4112282b080040900c581079045030f0256001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 886423435 1250 886422185 886422193
    0xe060f011217121f050a09110d0e0303010f06111e1006030c14010c1211030409060f0905090d091401050c06090a03080c120109150b031311010e0f1c02060304030c0302 73
    0xc1304520244001c1034440c0681c0f0594180080010112a130084a035140354100814105850b00c0c5410098440c2c190444803030760400801400701211500d41d407809401145000380c0d0b0141e540840036074400058584408060014000a1400c54200b100c100d014100c258180304060f41c070b1505a0342d11a0500581c2c06141020b910811070f0351013841e107000741039000060394071005071442003034405403030142d00c0710360f24001040045044001c600501c0004d0801d0074410100919020182c000c440e03000d40390038141e80000d90120304181c0d00080b04029918400c030100c0c00d04026070016581480389c500d55140d1341c01780e0010021040d034003291040410b80251a0100c45544124a039a0700307115500200c2811001340b0010b200407180c65000c078418210490000a105848001c00c0069070402c644603c06d2242c0289003104124016010340500d15003800c129007606860b00001d040011881c3d00280200c0c04054900c102c0e01d030502c210140c5580141c1070f075a0703e0400d424000c0400d00c85200c15400b42c41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 886424685 1250 886423435 886423471
    0x20d060506130302130c09150c020d0b1f03021806040204120f1712010e0901020403150507120605010e01030209040204030209010308070c21140f010c0906030e060f01121712 76
    0x40501490461081951f07502c9142800d040c903000a0a0003041880700f00b00500501d01d005072100d0b1240d10b40756000c1c0c0c410880620740307080c841b401d5907900040d008031058220010801612004034020f00304007180c10070360041c3d407041c0116009000d26803209042c1100322092009001c00180403001860260444041200700b6010380d001c40d20400b05180b500320032020040180c2d14003a8251034014080c00300262401e40e81e034903070049145802c6d49005180c0c2c1c1d904140318000350000a1200c0950419a050001a01d8140080c05000c940201c0034145a00000c1800407551154101d601031913000b030541c60256100c3c103143e1001c0d00400800c40705c100c0010320101c6c10440044036400d0702c098014101074400c0440d0b03a035428110030b03500c86004900c209000d0190000080c040c4d116203581c590f42e1849220301e401c03001410380300c03690806c8580c1e401441c2808250045482000d040da140301c900c84903020840c2c41d000c0301000704000c04051402c80824480da15041c00981d06008400424084271054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 886425935 1250 886424685 886424719
    0x1d190f0909050c090703020d06060e011e080c0c03073c0b0402010c0609020d0b0703110408030a031d0706090527160215090708120a12020d060506130302 67
    0xa2000354001c2d10b1544500d03081c51091400310700107540038049180140c10b084000520314203a0300a0313000000031070b0311004201c0e070b0755038040945028001d2400e0031706a41d103074801c0c0142010601800303100c4094000110011401010011199443d074801c103010540100c0e0140601e09696188018100911105c440d2129141c02e01e11003c4450300500e1003401506c55a0040d80e208250010896840c1d4407030f40c1000243e5900c500b4071030901d02803c035101027860a410010100c40103810019480c030800c0c03106000080d00002500d181c143e136818006510308000000c0b03600280b80c10009207440c8500d00010450344c2d400560070044890540d511452243c40c10203e2503501c200c0b011801c0307116a0030000800081200d542c0c06900b0f01140151001301000c950105284441103410003107991180703900300140d070310800c01440d02e50544400d050804074413040c0101052800f010342c00400c1d4010034901d13030f1015154402c000801004103041c3c0d40300e0075200d118004a9103848142c0c407441007034149260350 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 886427185 1250 886425935 886425941
    0x8030906090613120c06060b0a0815010f090e0a06030c0807050a060305060102030901140d020c0f100e0a080a09050d120306060504050f040f0b100c0c05150a1d190f09 73
    0x84d5220346040310344220010112562004800141d50180c4c8842000800e08802c0c0c1c001c01c0d081120b5030740c410461408000010035a27a11001070760410081920411201e81d01c00c501105a95030100240d01079150640184080d20311030300301511031422580000360080c40010f0850440d0010754050408a40d50502541162030803910a0b0241e0000c00215800c0d45c03003400290b41c400039a080c810b00308000c9696003400ca80090f096250300c1d0f4001c060304401080c2c10810301070550010941444070025003000c0780c0d15807010080060cc1c0400214401a0240c080c59a00000d050050f10300050741c1000d0800703003030045152a403000860310f8002c001c240c5a00c6441250140d4801600d501e182c01e02481c14000100081034580074013560f1038143c0c5d40e196845045c0071091603060b50b24001134410a0512918500c443e6200603c6400d5007824856000c9800040e01da00c21004d083c034005900070307415000340020f1000780386540580c01800d09031220641141d03020039102000549008240c45040c01070071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 886428435 1250 886427185 886427221
    0x60f12010806010902120a0509010e1207140102181e09070c1b05010905011202040308040308040305060c18100c05070b13170c0909031309140a1a01110a080309060906 73
    0x10041c0024005900f407147c3e60046500010b42200002c0e07120b240d1030305a401d221080c1840390382080000f41310001e0010041c42c0c520101c550a00031442c00314554040b5052034031207800c00b80a01d9800c44180150702c41140d0800d40307940d014149140515041a0041020401e01022503c4005069000c40800034442c0340c40246c42040e10303214030704c41c2818019607079406ca500d00300003625000c00c400300c00100103a0103032008501c40e010240e01c81d803d500e4451300b0503000030f00810416806200c5050f1295000c1041c0000324001c0d184291482d03041001200d903d4134010016001e8841c0000004001040304010410590b40c4200340b0461034031040c1c0b03440d103440320392106031655200c11a01d41340340c07402c40c176055003143e0361404a919280000d000c6401d0356002c1e9000341d0034075540344141d800b24402c0b0306051f940620301c014104000343c4a00403940041504606441c1004454540c407165642c00700690700600743c204e5600c0d40c817031903e03807162592000c0485109070035000306000300c2e040b030901903452a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 886429685 1250 886428435 886428457
    0x41a06090103410c0d05150a0227030115050d06110408060a140c0702010507170f0d020301080d0e060f03151005120c04080a02040b060f12010806010902 67
    0x1219074a903032100d0100a48000c1e8041c0c0160702c040c40d02a6443e400d03c00020000d01052650ba10742c81d61604070b03800c0280440540c0e000e101640300c0c101c0001c4002c00c07124002801e0041008098a96002c110000d02400b580d50000045640181600d680c62450302c45080d041140240310020040e032105070080003a2080540195401900d000000d06031b07040914400201220f19080a988051382d920f441c800355040100070380e0350304543c0c0000c50f4851209910034500510140ba02150358002040c81c416480054002c48601220301c1244105204442c400115054099215803400f41c200000303500c284540340283c808c50705041c00c5035000d00c610801c3c0000c020403542c285940c000e200c8000e40d000034031f0042d0120703800214000640d1051400311201040d642c03910740704c60784c903281c0381401c440c06440d9161401040c0010000000c000890312990b60341500c011070801d03e0000400d20a00a591440d00301800101d14100450580003030070341264081c60441d0030b03507640e603002d2030200d11450904031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 886430935 1250 886429685 886429699
    0x90203100b16020f03010b040510290f0c2a040513020306040b0a110d02071a0103080a0c0302010f0203090c0315060310050723030a0f0b0607030f110102030708041a06 73
    0x4003d46080e03031aa00e44000c010300003180c908682c400040c2110380c00c590b6111804041d00c4140710700554840080c015078001ca80015101c8081070415410340101a80038900c410001581c0c118001c061040401a2800300790054400a40c2e00c0405071105254552074004d500d44400a04400b41c22a23048070090b8024015080f203485c0d42e01c40c1c4038088002442e20310340c581c41d184581e40303130646c90006090300740c0c8004006032079510904d40300031041c40c9a04400c003022007440043c40460445401c40b2000d080d282040c0c3d29450b2a4034040e0701612410808444c1c540c0301008000001a003c207505221400480964200c00b201c03c040e070300112000c4d19141d4140d4840680704505290035070103c1d0308a141410611a2a210ba612160840c1c0f1b0340a1882c045030804400c3c0211070b0654040e1000c09101d0071028850355a442001c02d0142c01084000303000c2002c0c010007080c3c0c3e180503801c541d08485400e070081d9624588410081c200c241c003510102e070007600c040b20300d83ca4205040249805458028518 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 886432185 1250 886430935 886430977
    0xc0f01020a0f0605040807050f0102030612010c141c0204080a1e0c12020612100611070302030a1e0c03061a0103180303050601140c010e1507231201090203100b 70
    0x20f402024014021211040c2c10003103980450301c2080301c0302c10b0402c00c00016036246072240c05c2c4880ca1060100e160340584c140700a03101c04a812403454441030403041f00d01038440a81c40c0340c101400c44540c8140034903910004010603c0030010509000342d5001c0c0003680c1c1c11440081c6030310440d400e41600602801c03035924042c0180d10454000e4140070307000800c81030606a04c080b009a84110a41e60840c0d050840c4108201c0030340c201c140d1860701001d2034042c0607480e1841d000b01e83c58852141004004e2001c0303211200e002100000f00c200004c2e007051540603829140c3c40c210303000701218a400350f03850002c403460502d150320034098240e05200b80c075041a0300079002d55058001c0c1030083c8c0201d06100343d19210911100c241c01c0544116803100c400840c080180250007400c001b2000704640d11030000700c08002c0000d40200c00450f0314850491b600c10444211804511940101c2d04d0300741e982c000c00000000e0542c4660007550080702da006064a0a075a5005020000c1c41031840300e60356a2520494 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 886433435 1250 886432185 886432193
    0x141008090d0c030c150518010e03180d0f0c0f0e010510030f0609050a06051201050603070e040305040503031201091a130c0306030524131728020c0f01020a0f 69
    0x2100520503c02d09200c1c181036265641d112201c1e05121060305200c0d51502001465160a4031340c902d045e10980c0200003000100710000c0c6c592144044484000700c0d983d100a005840b6410550560360304042c200305082c42a2516141c1300d040c602c200003400c402400c01003540600f900c1da05048807001001c1040784a8001020381c0a030110340754128038a540c03510002103c88241c040d55109100e01040014203070308001c2084010f2514074400e0320241c0c500410403403651000a6518141c0c0e00b0740c5a0318886036164507040305c040c41103401054250101003100050035a0480f41c290603a00d06000a1001c040b03524400f044107032100a40c6980030302c04a603440d0700c2c190b4540c04030410800620780465601e07181d407115413600802d042003d01d00d030868401c9400700800d28040035000a000d0741b0326400c02d01191580444009828200c410b110400900c40013070829404c9400181f6581e01000b0075000312149019490f0b040c0c5c940403e00525614200008a610100e40c541d14a0b900145042400c030517915 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 886434685 1250 886433435 886433447
    0x120f041a130201141209011b080402060318030408030a090f0605070c1401020705030118230a0b1302190f061103030a020a02010603050303040503130b0724020d06141008090d 76
    0x588144d0480d0801c03580c01030010080030340b84207080c4c0e80300104000c64804060965038092107001020802d0b59011b02006a54030000c603134100101409020b146004000399034154816075201c0c44c0c4c0d901c40025503152554006141c8070032600101d00049400b9980d070020390743c501c50000000e02e0042001014005500301884034820f002041c41203c180075191000b0a0031100902c065900e44119142c07008200805d5500017960321082c280c9240c00b05001c403070000d640d0741007800d008054140940c0099043c03560706a081f05003035001000b03596040700c1410b0402c0c9144150050701c5032050760040114842e8081c030030380801070006100446c519641d4251140027074200284040440d5260103000020810070030156000703902aa001e1640c072500d40081004102c4a076014034008502440b19038081895044000c8480c0c5078408640103414403000d0010083c428130384003084041c0742000104200d020806d48601c000b000b0303269455000b40880c0242c1e00510104d072803c4003503020004c2604514070440d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 886435935 1250 886434685 886434707
    0x70f0302031f0e030408070e091c0e190b0a0e0f010c0b09030f0c070f05011803020103021305030f01020a0e03070312120f05150102010c0908060615120f041a130201 72
    0x2c0000032801411820603003540e0095002c0f4186502114061142c07a5109690308d1b00210329070300801c68140300501c44000d02e80058085001e0042d03e01c03903480a44c5400c00c40c0d10b074040b5098000e0401d80e841d440d01100c550070000308030001402140f4540041d081410481d03e03040416103c0156810182e82c400a444200070b1a0a4047c0802e000a81080c01041e01074443e40c40d4103070180c2141802d10740c0e0074100604551180d41003002e20729588802c0c841c031040c12000c2c4c94080c80d003d41d4600c9140d9903144111000e9101c190144201104640140410350190414140558400700d0f0000b95508042d1345280d14000980003d01000c03d0a010f5402100e007443c07003214201c0040b6560f042c201d003407002c035081100c1c001c640445420b440b104940e420b2041c0c030415611400c002c0d800c21700703048100d540c81074010701d05c1d8085c10003140091044001041a6005039950000c20b00c024980200e03036005081c42920115924400c00c0840c90b854401203560030311034201c404011540c80000e4004441401c112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 886437185 1250 886435935 886435993
    0x305190203070512090108130f03030b010201230703110702030c0108281d030c070b0c0102040f030c0302270705070804031a0709080c090a0e1903030b03070f030203 72
    0xc02c80000025020702402d10701c070000e40300390354030780c176024001410300c1800428030b1101c11441d1f01c4403400550703020b040c4007204d905445d000411054500c0180c1c01040400750001b090f084003000d4901d00014030388954880c400ea5a001e114009a8140848607401210f0000b0f6040e00210b6000500c3d500c5a140b669200c010007002164038400d0903150384001d040100f108070820b845036880c11400505000c605002c0050f50029480e00c0f4000d8070309170315020a4041c54141c844009403480d501070f801d40589011300644070403904429524501290031a50b1444224003605040f010314040c1c44403120600207001001c0d52161160351044e104a54991041c541142c003040c080c0004004249040728070b44015500c142c8428480c200b03000041e00c5407074581c2c404011603014102800003034640c40d8026400030018140402c80443c4440c1c0c2e40e04100d80000c111a4400540d241c803010305915030050b1150f03a03026020f461516031612003e120708136613800040d4040d480020301d10468800c0c2041851090a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 886438435 1250 886437185 886437187
    0x10f021c03060b03090312011a0904090c0807060509040b0a061202280203030702061807050f040f050702100b01091a07021f02030c0c030106051c060f050106090e060d0305190203 78
    0x42d030f8072030049030300192020a52580049040980543d520401034050020030084080203d074008681d14103104010700a0300070385d00c4030402002c120a10000c2c00c09004181c00b5580c205c1c0d00c0c0d440041c99074001d5505944180e0508845000904080310300f40b0a0310095500ea800c6c142e0740759079001c0a1361014411980803075210040002e0340500d0003030140e50310b66941c09542d8034144002c2c000c0c60204050400c04a55128101d8030200040000e0504200e0300192004541601c20100003001400603800c0700225038109010081900c1d4003040940050303258600030411000e030701c4011106401c01d0300a80a02c1202c0210a000f44420080a00384491006103445d0511b01d00792580041030482101070005640003141000d0310640c240080c010000094000300000c900d0980021541100030717510744500c0340054805001e004854000c6403003280701603010f1009503926400280100036510070003142d0507000c03000c2a403501c0c03c20641c1c11125015950305003403019003080c2c4100011030700c5201003941300c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 886439685 1250 886438435 886438439
    0xf14031608070219180e1e0106060809070806190b030106060302180906060306060306130911010305010803191103160f02191805060406050627010f021c0306 69
    0x22408428004207100355005a00c0386024410702030f00c140100a8080e8210314904141310120f00610451404c001021000c1162410516003504144071b1480340d0b0b43c501140030007200411415004401250b0b6580e850011a64030300e981c09413202c285000d4009a81c100300c0c0840e0300c0703d0800048000319050715000088480045c0c000a08460b055071200000c41d4002c6070340e090702851040d1003d4000800d507651000740c030f080d20001c1c00b1448011f159501c90b070404000b00f2074a03156044140c01840c40c4240401100c1d206042c01c020f000060031a4900081c00c04c00007048040d0044203943d40550800614058100c2805081d201903903001280380b11031000380031944803055103003c915180c501a0720440402006401444240485074015420912090500300310800042039001a40303185041c00003100d8990380e00040142c040f03507006030f500c400040750b14500c82102c0e21541454506000c01140018809001520301c1081c00c010100543c100038040c4d00c052000880c00c61140c0324610700023501903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 886440935 1250 886439685 886439707
    0x2e0c082101090506032e0b03120d050a0e1902121006090608010e07121509050105150a0f03020103051e070c030e06090904140109080a020d03180f1403 66
    0x2180604610090030390103004201e007600e580704083d0000010703030261010301080c0380f1005184221441c00001c0a0349950b000481980d182d004805034200107042d00c2001001100c0c001007900101e0500d0f001a1510f40414401903d500c647d0381035070304100281c81c01c81c82c81400c03480750040304041030382c00242880814908882c00e00c079211091548500c00101d440c140f400017011145550840d48503030385031900d10030f000840000e03c4021201c004861603001810791900681d445910321005c81028100090f481c20408103400c018800d000f5034800c80712001c0501d0030040703804081d11038940c248840c0003041c8007652180d041154020420680c000244c503850141140c8924200c4516002070031300c24001c82010342c000b800ea01000411212507052461000000f030715104003510090440c801100180c0c001e540c290000c001280d00001401d40340c200c4113001a40b904220340b11000000c1c03405625004104860401c45406600300d03900d551000e6239907949810810000784452030b40d103c2800060160 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 886442185 1250 886440935 886440967
    0x30207050a120c05120c071806090203040f0b1501051603180f030c060809031602040f092105040e0c09120a0305070317040510180219052e0c08 63
    0x2c0e9586641d0200c162149003804c0b410520703489181100700400b081003110680c4001006410341d1000700c140710100d03180200c080d000b080d0301c2e40481c50b254008400c000c244100f8814139001940a1340c0010303959941c460001507078194451015000c60f905109000400c0c10404026507036600c0fa04001d100480b080c030040390014070584c001e261000c2d19560038010040800d1404000f0700c62410301140c5400d101c2c070341d9504d0b8060708613003a562035400750201044d5510b50b04100800c1004070020400c0c00704605149034410f05116045030f5101440070446082403144080f6000c40d684c403040882140c603034403110b0303000341c0c080b181150348a0105a2041e441c00e200344462005c40b0300c01d488140e52114a0b1501600032a40152181c40c111012410440403690106040e08001030320040020b60541c00d0303c0d07210f4080c0103c0c1d4081e411a42c46400000d00e84000070b00c40c015560304440c60819500d034903940c40f0203400351413030724881c1429504903006078038000c038840c41702c00380703d03030031381820412190707960491 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 886443435 1250 886442185 886442213
    0x908030f0403030b09041a060a150305010602010b03070513200d0c0f0822051e1e0c010c1b1205100b030f0a030503100815090d0503010e07030207050a 66
    0x328a00003800304142c1c05100301210a2010341e02200107103410f8039081046030f010807040842800315800207140d540c0c2c0d00341c1d0300b0140c055000386918000994000038000c2100340a40e601540c0b91142e800f103145000144001110402420040009000ba40c0c10780640042e1400d080d8400c00805807200140135240604070720115188005442035020030700420144a121281090046000071b1003101e00c0c001e1046126506903240b2a13a001900d0b10b07015207048013204101d003d00c541d10b007480005003404100c41950502003400b554034422400700d03058039580300c042107074049010009040d0005286c004183c81201201d00d14980055807124520411400110200c8440d00806640300d5490303040d1155551b515001d0340100305a00440c0d104554440e8500006030901c480440010030a4601c0700700c40c1c0103088000155102d0440c40ca42c3c1e00343c0c1000c00d94400304e0a0090301c4040d0356036403107102585d04070380040340c0b82c004540718200240c000794031013042038800d40102c00400e0007103283c88043c504c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 886444685 1250 886443435 886443451
    0x303050a03110909011e0f1401140a1b080408060118150312030e0106051503100b190305090a02151b060f01060809031204111512010b030a090803 64
    0xa40d4040303804004007210341a08a003400d0b15018441c1e408591941c0307058a042d5510a440100074009001c51900c1e03c0803158815915001d0400d00460840c1e90440d01249042007078036245118124030b681e0240d140078001c40400090120a59141584086e980b0080701e42d0140480b507160580320014141007040c02d8001c50000d050104100315020202d104010f80003480c0f402e0b2001441c29666200c2000700904020020140c849180c00c0c440d05081d48030300010640141404119000c41d00c81c4038458000301c41c007801d0314140c0080054441c0c1c1c0071044400720f048443e020b1540f407422940960041402a0203200072b80f05000d501c0380180c680d15000c410b181c0062010320703218605801032041e006004111225650407220505c40c6035a542c3c0d001c1415281c060511040341c1c1c0d901c118480c0755001c3e0310501c03015a140700081c030092003075420b50406c0b8a130050b40e603800c60203544e1040d07078242e200303490348002c0940e5101c0040000002c1907000c0c603000b074150388000c03034402d40c1c1351140c90241c2c000396503a84d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 886445935 1250 886444685 886444687
    0xb090f0402012016031509020112110d29010219021003380d23011b03050f0c0403030804030e120a0c0801150302150a020c04050a0e0609010e070b07020402040f030305 73
    0x10081c0101b164191960144182c400d20130005581e000070400c20003407070400400d03600c07800c501c004114180140e6681c0790f80b034070080080c00f0740740380b444d0f4941da44840482c0c60030358840c2d410400c55102003000e02449d5001581c52082c68416824005440c0790104a44100341d542d040d100380014854800814040301038440e05a41c40c024103101003400c0001f040c0d03d210380e044540000025460b079894504640169040c0d810120b110300701c840c0508240b04a0080c19202c181c40c81030401d415600160084407030800382800d590724040c640320107101e6400080d0101348040c00140c00644140c60240b1000d0703000d0105540b441f4103100f2640b800e29900d40c1214200308800e0240810b41003481480d60640c501c0130141c40452442d00802d080c00e500409103018403000180c1101681d000304400140d05901400400c620f18002c40c0300c03c014041c081c40d110b0030340281000301d00c050380c0501618400d101400040c0407014506803aa400662040402302e03005902440f0002c1d524502d0802c0000841c02500c0785 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 886447185 1250 886445935 886445939
    0x3030c1b0109121808010c1d040603082145030f04090e030a140a0311160605090f0712320f0a030f030f020c1b01030b090f0402012016 59
    0x30030100d210303402c00c050682c5458506147c0a40c00300c40d03401c03181c4000c2c050416a4402c0004100078203625040a05160f40001d100c0103106507000e032040c15048500280c2d5100c0c0c90f0031200c60560312135107451019000700100c02006c10a800c65500b8407601c0350005005524616644841c04e541160b02c801e41d100c00301150412407072800d4064109040d5903600a14070b0102c2d0324202030112000318404200340d060100d445041383c0d02a82c40050107030303074080b44203881c2c9030360100040784403181030401c903101c90510000c1030400360002030701c512040046014040e440c0c10180324040e8881024020703100000400640002140c45800c001103c02d2020800f0020b2610f92040a1510717100650411040c0c0c0040c50380d4000c03c2e400300704c2d00000764980c40c010429000349021040680180d44070304016010344404580424550700c0c402264400a0700c040c0800030300f94040250500003200c0e001d41c0702e010a000100150701ca030300200300f0003070506c190640c0040119141d0340b4181d24501c40a21805400c41c003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 886448435 1250 886447185 886447217
    0x20306010909060b190908010509011a0102010218060c0109020402070f0215030c0a0e0f1e19080a2306090619230703021c050f0903030c1b010912 64
    0x100390180090324800d0010601d00380f404004d501c9484c1d00a8a04d81c210000a13040c1d40c81004c0a0004010b034800038409810a03148550080c81400307201c6542044446031442294018025a0502d007031040412000704550307024003049902000a105695596a41f218016034451024000132401002d4282141c04c844c8180003e11401008900704a2010b004010401c2c2c00001160085c000514140c0480c18610020a1120031040c007096072203a4540340c082034003031100c1c40070010a101165510300d0032000d81a070030b514403644d014040146d006810400f01280c0c034150303840360032200c0350210f902d90500000c030740b414180156416042e91304540c090040a0506000060581036a00401c03c42400360800d02c49099111028401c000b407807500000c1d00075030280d0b050790901c4040108810341d0704403544d01c2c03a00415040351310700c0c03003000b10303001040c2e421000005480c829408125480e00c2c0000f070348900c000345a41e80c0200d9010f03648a41c000000101e071611016600309564842d00b1090f40f030354078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 886449685 1250 886448435 886448447
    0x9090703060b270d08030702060c0a0f080405151f05100f0e030a0b090c030f28110a06030902130e060105010e010504030606150210050103020306010b160b01080102030601 75
    0x12801090300301401802480111002c442d6510000c1c1000c07807140e40c0210084120f0951003582c07075804111805510180005213004501c104150350a8482a03620403076118194003a01580000242000c2c001a160034003601c04a50407501480031210b10490380404400704a00c02c8510100007001c12298800400b0341c1d68060000d07007002c841d29070503c00510740c001c0045101425010400c05101e00c0d207aa1501d00340100c81d1a9900300c94032410350714010503925624204414054006d100300225244003010108900901d0b2540324200e54107969048001c803804242c071003040c0e8100c15000854a02582d0b03040c0c0c81002070a42e51400318540125004120302c907a920b0301701d84203031414064075810304078012841c0b0341562804d08212029100500040354030380140e030130040407140390010200782100c00798181c01c0a004541c2c221a4400030070000542a10006c0c07000941591001e801480401c0118003e800f1603003d002c0943c076144c1035500d800b02840c00a9015035407d07507000090251559000d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 886450935 1250 886449685 886449691
    0x190501110712080304020d0f05160611070605130f030501061401080f0604050711011515020f0c0105070204020903100b0f0303040e01050d0201030b100e040524040f0609110909 77
    0x10014041040c54000d2400d0700d15142c60004000e124004006011035035040216254583c100000318007202c00341c6001030741c4034907410b0031981c2c10007a1f00c80000c0c9203200708019441400544058180310380f40c050190380e02d40001c60a201c4802c581d25002c919041208a9040154000c07000420001c0c944442484040c121002603410096050208102d900d2803050507500700344141c800040720307680d1000c120360040031705440c1e0425508142e0061003c9886070000d80988404003000c07407008800082c181c0c2d9442c0101c8502007036030011041075a070f940c0070300c0150104a00144c0701500d8400403130006400d05460035146c00449903240b089404601380b45104040140060300118a0300b802c00d000b00e01c0028052082d13911400b0b04041903811a4400d402c0407074100000341440c001c00a104a018000c850600314140c05170b407525000038a0507618100500c0c00c60001c40301c03c101d0340210780a10000d81252040d80b0f00c003d4443d6030003c3c62199600c60f5412940f00010f8560f240e4011000700f150019010b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 886452185 1250 886450935 886450967
    0x3050d06061d0d0c050a1706060d020d0b06190305010c120605010e0405190e030406110304150f0c15061a0711010c1703180d08090606040e0309190501 66
    0x1464401e00041901d4941c41d840000c03c840c4000c000d0120300c0e114100e904030341c01031a08207100d24030006040e021403171032194039140041aa031580c0c1d40c010502c41d5403d07440c0301c0079500071030521140307010071134007900d41d90014400b5045658000340c50141303144a0710650300803582a99142840c4003481e80c4404034912401c205035042c44003a250800007451b00c061740032076034401d0b643ca0f030114060b035841044402d969441a8070078411000030069031071f01e9802034440d20380860751613035505101d4035001c0f0403142910841c0d803180040350a10b107412a1203412004050301444030501c140340100c1c10200414138090340c149808141a07081154501140100704c040407014003091101c14002240f040658061103002e2a1848007031006003441d880440844102c20000c0d08000300303105034402c01c1c0c2c501030580e03075009003140c0080d0101181260a400102d8541010780c1000303000c62103d24041d0448414080510126400e1000001c0090886910903c0304c10f50145601c20400c86940c10900b204034490308 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 886453435 1250 886452185 886452197
    0xc0e040b030606010f0f05070606061809090c030b0c091921050606011427010e0316180f140f160c081e130e0c0a1704061803050d0606 59
    0x411000a0704080101c2d00c05030a001c82c0c4d504646c4660310480964503da81c01c418180b00d91030755400054400340082031404107842c018040440e05400e180a1811020f921040040790140303151111a80c0c0040031b8030003440759104001d2420740baa078a981000101d18110a6442024a80f0b5040c0480100310116030004d2003055031210301054011034620760021003800d04505440e80000151128480d001c65030340c0404140b401c2c0c0c0801c4440c1c4d24501ca82c1c0034280c81304d002d514052010540d451072101c1a454610000c14004e004440d0600400d1700c40030200d90000c29401035251200f0241c454010081d545a51400e042008981d4003800340c0790809190701406024070660800148281d401100c081d100302e0002410b61003071010174005189084101c8a000c5e15108500d0255140c0c0d4400d03c1350017207080110000c1148100d40804980d111182e5450342106034415152007188048001c005032003940d510040711420814825408203224440d03a42d01c1d589601034001d440448190350001d508110b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 886454685 1250 886453435 886453441
    0x71e1e0f060219061515030e1b060304110418061b1e0503100b0316020d2606030f01090f0c060c0201171b0f04030501050f060a0312020109060c0e040b0306 68
    0x700000d8803d4074030380040001c10304001c14041c5104698031a0f00004800701d002c61018101580340d4491001010a10255001d82172148144082541050017440d40418100085800215016000c030880d08020f0301c08247ca1840007503d54441c0c25144094071480c5d2a0720f140d880c3d140a4210000c0341c042541480c0128082882d40c0c51240890801003100340309002000c2000c03400404102c80c0101402618241d0b00d10340000e018500b50001c18200c800351040d03f024070b6081d40100e10780103c0600c2240000e0001c100c0a40001c1140ca016100c2a054021003034012080380e420300841c03000a02500038199201100d10b41900d5126141d0301c000304203c035071070314240140c1e884008014090700d46551140c0c2c0c0c0c0c89501303480c0b081501c8491100042200018410404c64070130b0003600880f40210020001c582c1ca05401086d047c00848480d94007038405074040c00041c014040304150400103100000c2c0c1c5d109140e0700c030000c40f20720740020408501c6001d000e404c1c41c98036005500300600300f0b03405824a81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 886455935 1250 886454685 886454713
    0x80a11060c19080910061409161d040905030d0903390303021611031506060405220212060a1211060306180a090c0806040302071e1e0f0602 61
    0x1080e15000d4002c0001c02070200300081c10805c160044050001001c000c8950b0b2250204401c07007000f540383c1d02175541440080d0034042040d00040602c92a42c450002185006e00d0200c42e2400c9102c6541e80315569001400c00f00d04108040c0c0390b400c2007000c00144035521400d000e000c0701501280341c0710b14041402d003120f010354904144078250313600c8844094842001d00e0103a000c3e0164007054040040c4c0b500c600424400101850140241c041d029200310001d0340094070f01600040341d5681e0400c500300400c100c2c1e03003840356101140700e4000e10440d200a2810001005a1340003d40c180316110382c40c828420280b8207901034200a246403540c2c01d840b603626a80f01c151821107048800c2c496080480001e1311350f01d03842e02e11000035400d6201c0300d80e18a40326042c0b07401402c0e100401d8038400004903020503400b40000350036029503050f400170012a8034020402e40c1c1174071103180c0d5200102d010140042d0b06822016001c5181c84420404d410780c5081a03140e06c810503a60f481481151b001c010345551036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 886457185 1250 886455935 886455967
    0x7080307031d01120c0f08060414130309080d032c0a03030b1908030c011d0a150605131a04061a2802150106020d050a0e0d080a11060c 59
    0x14595a030801101d4042c0040144da400305004a1074071a1400c01c02800d02d410b074402e030300400d400d0650b01c0e81c0e0b0342900c819040c802110303d1401010a50680034000ca2040e182540c1c8510509210340752840303946840c0c480382030030000900a0400420f4031040c5000282e00c1280200f030110381c01c21058a80103620b41026680d403102c003e40a814951b640ca142d00441e107594000640282903181602c0351650b99445003581e0f903100e08a060f501e03520304030181d14a03000c072130851064079408400400d1815415124904d6490201c6580c0030030540e651400921a00c40903016540b81c4842140056802d4405480302c1a1003241840e40e48180d140c44418000c0820100107241d0015081c00540c2c2c450781103022210000180c000303a004c1ca0820311608104295000600340c1001c0c04072004d01d500743e681d640059aa5100d03d81120307001c00c0e42400703945c64140c4281c1044c2c40f03402c0001c01c0340c82030004503280c882d682e80c4050000b00014044410701403401008000b65600f00031030f00442403900b045013016220b2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 886458435 1250 886457185 886457207
    0x708040b01060c03020a0813061404260c0d0b010602011a1f020a080d0902100807020a0809032e060806091902031f0519090c0303080915040804080708030703 69
    0x103000f80e01c1421800c3c14802c10002c0585507021006d0303030341d48081800e0071349000c001d44200000504151421003c0480c50005d17a0126080302c10511504250035031311070700204041440007100d105055403c10940e8462088140143c0580380248495050070002404d51b201d0f46403c10344500709000322483c0e80c4946020700008554400880c180c0e60035010100d0510540502c05040c805020801421400c580e83c844801244212500201d000081e00e091303659110858040001d600290342c03107800300d075000b07000f0030301100700030103a03001c440b8400d13108001543d81d90800b081d0000c2c04500692409a188298405400614010b001e03501e400c2c1c4156540c3c0100c00d000362544440301c0700302130031924200660b00107210419130b0100e0344100101a0001800b040b252001003040e45000f8404003140f85c81214109604000300e501010305645040da107000001e4000b040520031007901016980606034940e00452080380b50b980e641d45030041d92072500382c40b0740040d105034204006040000380c0041d04986 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 886459685 1250 886458435 886458437
    0x313170711030f0d1b050114011d01060905042003040510051506090d24090210090506122206020c0d05040803031801110a0c061109100e03010b06040305150708040b0106 74
    0x900400030350001418098085d401099503003004010032403500355a00e90b50507a1442581600c80f40c80d107a0500a10708030a1042c140410b08100051115040c03a4011020380050f640200c040264494507160f41540219030035510780e007140c00745041d004001d015498210f20010342e00c407044005100014401e00c0303010806407244118107285000c000b41844011142150310341954001b00d18840203502600446000700c0c400c40e00060b0141201e40a80162000c0c1c40c8003501c1d45081c102090070724450200b000c0e003482c2140700c4c03200f1703001402940004c0100020744510760140c0c45010031603901d4a8035603242009000d00400303010501c0080e80000035240d2001520300700310700440e036110710540180311001c02e8102400000551204954104a0094140f8440d1200700114030080b14034160600804118035403201c110001e00d414940b0910204803100d0000300005002c3e50414000303121540b090b40115010340010041c0880c904100156075806441030400c94600c0c50560b41d402c61003401405010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 886460935 1250 886459685 886459697
    0x905060a14030709060b12070215041e2405100617040f0c030609032007050f1306090903230d0e0c0405010b0903070902070c0b0313170711030f0d 64
    0x740e0b03070100482c0c0020101c03075204010300c81e01c50803007565a501000307441e40102d00302c41c042440ca0307100007820380b1a52170000c01c006c02030301c49a847d10041c1c08041c03c5100e040e1102c80300100801c260041014901c2c065001085004001e00901703400d1fa00000d001010f4607410305c00c03c1200c1508100d8940000446030500d5089a07140e16109821420106020703282c0180c03c0c0c404010040b141d40035a550b18042d440e0045811640d42010072200508240004940c118007420010360511240041000400420200302b01468038803080454159601c81c4401944403410001815041a401021550680d5080e2250341c80c00d08082440c1c070480032010407079641c4080c03c00e00c1040a0240202000c0010300a0109581d286141a402d411800200340b0a01841c0340005840ba0b1038404c45251640c4031081543c0380746401c01486060704018012034412005405104c00a100181321600b444480c0c000c268860903076041070040f00000c662441c2c040c1c0d010714102c92180d2000039035000015034521b014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 886462185 1250 886460935 886460969
    0xf13050c0715020901030e1b0103020c0c120109060605010801120f150c0c0209100f03060e0c12030c0c0a051c0512130510020a120311070b0403180905060a 68
    0x1016091140c00000340c1402c291202082c04010103800030802c01400b6030b000e000d00c03000700ea0225211401040818400d400d907080b100c0d01c5500940152100d60890000d54200c6070f030560200e203007420307400e9a10103031b6590b071408001046014850070004c1c0c80e080c680244650b041c50301c8001c40c0001c400001d03100001001e044405c00c410303003c011100d00c6800c03000303000402c100c9d01d010305804444001281b0402046001031010641c00000c1d10440d40302c0302c04a41001d146440d1003005000c2048055030380e0103206540701058840301c00100c0342c1d04200c8020f664a0604600b858201200b0b014510710070240302e003080055980754000c521034020007000103442000c262801501c0e10141ca034903442002c0d800f161030030000012404c07841c101c40301640c996071080d140f25001ca84414100310000e00c9a480001c694030fa851190348003003e80c241e00100f45240031601d84820502d11800c903000c40004001140c000c0100c0c070303800380700d00040c014480d0620080c2401b1001400c040ca85016111051000d4038078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 886463435 1250 886462185 886462201
    0x50603180316110901060e030a0605040203010605210c100c021e0a14010210050c0301060c140102030a051501090b04140105040b0c06180d2f060906010602010b0f1305 73
    0x100c500304900020b00c8008410a0314002d1140e402074030030741d84180b0108000248140c000c04000c250a50010094810366120380c0d9210014100900281e03050b40d41c4401c041800c0e16a00307080c0c2031010300c03461240c0090210301810383c504918040c030390f8007440410340e0b0b10340200c0d04080030b001c42d1941100c40d105403500c41c4050584c0e001103182081d070b10503c480700001da664000d004c04004003400b0f80c00d840c540c007062500c1e40d0540700c0070ba6642034014020030042148901c1071560118103842200d104000b074403011005800d80c1c00c01d440d2815455500c009211561608001c0c04480e5102802d02110107403070450b044015000724400c0c0d0304000c2e00c280d0000c9071030b840b800c01c42d00078060041e411034541518054140d0b40d007400700c41c081c1a5824510604a0030394000845940390740d120ba46400d102044e003c0c13078800c6007410511502c00000c0068200360104410302a0501c16040c040003846c0e9589080c50090079206901440c0d40204003030000c4021680391030045c0300901c0d845d100042030541341c0100c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 886464685 1250 886463435 886463437
    0x101106190b03060705090a0602061003020904031b0827012309150a02070509041104020f072003070603020f16081b07061d01020d030b061b0a0b010f0506031803 70
    0x612550b040c000d48041050944e0444003a00510b81c042e43d05020a80e06d50209a03500d900070b0300c000d0815807943c00100f0043c034041d025540d0141c8680341400c1d180c1c440d9000e003070184992082c2100d60301c8001c20740044440100d03140d01c0c7c2c2c201c8000e0742c0e4401450b41c140060100302140c01c00c11154604210920128013500040f129840300c040c048140c0d401d280001042d0a8001107021401070042020006075880d01d40101ca025641144004644001c08000c020080d440f482e00101201d10030f100280200300c1c8046004940040303092035503c0102c6600801d42040d0301504002e09152050228208404c4180151065803070f03105000c0e0720340c51242c00c0002143c092550400201d04c502184500c0c0c1090100d118001c81e01248c8542004403074043c00032000c2400044205e00503072214030401d1402e4481d4110300c9503a1b038082c0031180f0b0286e001040342403c0105518010480d0710014a480c01c00c908403176194014051900c0c00d640140c00c2c0000540703180300142812895591880516034000d40501c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 886465935 1250 886464685 886464701
    0x218190b0703080109050c19050904090f052b23040305031b0d020a1110090803031626010314070902181201050108060c0c0c030a06050610110619 64
    0x4009407503a2080c038000b040340d2403d014014459061002084900c0541025a4010310a062030724680700010142100c42e5040448120b62094403200c1160100304079210343d242841c000c03400351040603801c0c0c01e490148418a1501180c1c4500070b00c0000c1c000e81e1003064064400815078200442e000849414917035406079801c00f8025020009260f405c1481d040c0001c0f03c8035464106030f07400a9050401682c0742c0c854403c014121040d880200d04082c98101002003050005081c03101505490702c3c00726282d504104c5401c0202c128200b40301d400d140c1c20a132181401030b81c41140d89941840c040d0300b215041c1d8184030041105400304012402e1850500c1104054071031240110346640c2c40e00d5100c400e0402e0317010f0050049900c164151505232040c041c540c1070b111000c0040842c0c0d1910035902c010f541c0229020010b9019074541c1c28007a81d01400b2030031160b4056103000c681410120204a81f4114001c0c03008280002e04132210390380318010501581c411100e2400d80aa403100021110280280d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 886467185 1250 886465935 886465949
    0x5010e2805032203051c080c2203080301050a0e041101140c030c211914070c18110408070605030a0603050604050f01050702210906162004021819 64
    0xd046224003442c40140c0f1801224029002c88083c40318405040003141d02c0e2000c004001400c00d40080d000b00b01100040406110a4501d50801c1c04c01003640d00880d0301c2d81e0011110300c0000801041030345071829500b809401800034016075030600346d0382d950507450040105418030980f2054a003101540b5400d548504812805481c3d94170680c02010f503c82c010800401c000c00d50700000001d41c1d04501d000e56000a180c40500b00e482e80302c20106440d4141c5000c4128502801044013400140e5071500c0c080062907090801c4001040c10b028030020707100207582c3d0307104141007400208484000007502104842481c00c0c00d035681d444241050f000340c90a500b000c0c140380305010502040000009040c0d900300910300080150307440fa9107040ba1605c0d40781602c0800c00c9140b000350b120004404004245091004090602e010341c050f44c0c0312504000744905803070100c2e00e5899034081c0d0004c18413010710030400311000c501c0e11010041d603a4102d4820580ea9014141c000441c125101041c1c40f14000340c600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 886468435 1250 886467185 886467217
    0x60f15080606030601090c0807081f0611120702060f09190305030a0f02163f03020f0a0320010902031c110105010b040501260a0905010e280503 63
    0xc440c2466030300c0c08207540300e6010b032040c040005603e4030780d41308003501c0c007105944146140d15416400c440d44100601035410004420365070010401009a10500604603034844020b081d1501e0b504904014044000b2110400100724a400599840b41211003800742214803030f456650180c04610854040d22980791910500720007c018810000058201c42c108c135690355918000751101282c40d1341c5041006240c8402c10a0309000c070418006601440a24022a00c0b64800b503050401c1c00380f00000d07040d102d0403040c81b0086010306505004040781d600703082c0000d000301d445903078005141e610161081071403246192400209403070203400140c6886d4000302103d041d405c081f4141391031619245201700208505c1c02c10018007074018000c8138101da060401140c10240703041c00569058042004e0502c521010f80042e080301d08440484c14040c501a40f00001c03501d0147c60081d007182c1c0e12407040c05096104c1c0c00502210082c507800742d10210440c1c003000350740f00403030f241c21451802074225008481c80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 886469685 1250 886468435 886468439
    0x1c09030c0605030415060522150e0f090307050d030507050d061e17030a0e01090f0620013b0604140727090201090506030702010f0c050c0307060f15 65
    0x42c0c02809540100d01810340c1c14010320b40080c0050440340a40704103508000310031405440c075202c0007241171071b07410304a8012402c0e90f40c030141c0b10719001d165084a91248155024411035020f02010b00d44c0c2300046100862601d9000d45a0544d52500d4588076810180c4580010b43c09a1140d000d51303450707250200051100944800520309800c10340241d03240407440140e00044e40308183c000d50160b0040e081e02441c81e1040a4404882107900a0491410710450000004101c0180c3c401040100a80e646001c0e002c2c16a11480c4500d04d030a00c1000c40c168140084441c5d260900000d15070908005502c081c2d0032601900c09100803641c107130054806008010800c414400b503000b103581c0b4800d8840586207e0303a00e4202c41303090b024034104090407580340311410b000060b1095015031505801414614441c50792040041c5807030780704440280c010303515a0481c1c4800c15090003101d07901920307420854103283c41046865a82d000d507400251040e901d130502284a01c40300c0e1700262800c103407280b4061800d5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 886470935 1250 886469685 886469687
    0x4090f0b04050f012007080708120405060105150403050d0f12021303210f08090a060e15070e060f1c020a050415020129130222050904051c09030c06 65
    0x42c09400c442e83c065420315142c049a1000c0300c11800c8064001c0740e200e8103042240c0c03120065074000721300864142c50f041048140e41c0942840540c0300da48150300501141d81081d06020580c02d000c048518152014070040c0300007503000c640320800d541e0a2410ba00600c4003e20304031040003070300c0c0b11201c1503440003901106000c0c1c0c101c00941070364000c014030410014001103070b000a401d0712001c80c00154060360320043d400c0c45039400c0703600800100b04451003003089460b2041120100c2c10540042d900c420030704a003450107108403550022080c00c141c46d25081c4600496164420600c0502c0b40080000b44030711120318190303850b00460b0300354104544500004c2c2d4007908035030260203141e4a02c4000f10324000000d03c1400344010352841d58911070b100007000029200c0f4800003080c080c0d07100d14803048010201c0854400340850220280c1c51200c04c4d031640d0b40c140d03031117851a000f481c0030390910700400010507030000da00400040e400d448224030000000d81120503c00780d4100510076280034200140c15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 886472185 1250 886470935 886470943
    0x9040b2b031112030f31150506240c06070c02090a02030601050702010e032e060f050904080714070801020301030611090a0e091608010f05070f0e04090f0b0405 70
    0x8144607032101c60041206060280d0740d407143d01c40e1a00c0601d8100009021000c40210305a001021a800c01c622454115244d82140f91460a56050009002c1e044000e003c042c501d00710f0b019482c1030040180c0d04048010880111105c0804d04800d8000b0800340030042c071803c100ca1404c4003510035510795040420009050300b4807204103a108100c1500407400b50180f620849001380816111b4901d44580c5130300640d00b41441ea02c400ccda050190041081c980c40381001419240032840c548100f84c841125002c10071140c1e1500107501544101a040c00b0b2612040d41d070503040b58000311950745400e41890800c00c950884200b6070b009000c0d0b0000000c07a940c0540140d8143ca100b10301c140402d4800130080e2080f4000c4d0b00200c1d83c05a03420302d08229460001107095086800c4c0425199074039170074040c40c080c283c880e03809080d03207a641c1e034a4020305000c50b01c40c4641000c80d5103485030300545818402407245002c1c580c01c501c210780d14030050041040032240f4100180d8401e0030030b415442c050420f544c91f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 886473435 1250 886472185 886472269
    0x1427010b0315060d052e0311010c0b070c05011a0a12080403080408060403091403030306040f020c031305090708071d1305071206060906021e030d020f04030302120f09040b 75
    0x20048030214100805428001b6070000707000c510601c0c03041720385592500c00c1396400503410f090500400204440c0450b072903200c5248107000c681c84000421089141c02404c451200d50303184000f0520344034144142c0d85041c40641103610b02003180740007c4541c1880b41a6100c0c4e84e10050241100080000d048c03000820300500c1240251944440b043d0340b51000c0110705046a50350390316420800026050380f03859417000303c1242003070b0401418080f042054603d03540c051148022000311400e002c101c10b1504222099000407540b6050310b581c2070641c030282c25004191401e1042d0040d1103442040d58940015240c110f00f40601c0c1030080781041c0c000505500003001c4a07034101d0741411404901180940c1d00d58003210000c1d03000308034211001c0003100060042c3c00525586000030032640f05030703175864000341004400f403d06283d034a0749946006031912090b80d6104500b0038050000105d404940b03000ea0703e010405403000314407140600c0000301074a4007080c0d4906440990054080120340001130350034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 886474685 1250 886473435 886473451
    0x2c0d0c0905010e070c08031510090e0a02090303070f11040203040602040e100b091306180e0706180e06130e0610050904051b030f0102041427010b0315060d05 69
    0x32050b43c03212200d00d000a011943c213008160800c0f2040c000445001c011030f4000c0c11102200c102100301790015031000083c1040b4000144007100602c20b000c00e00118130342098400c0b00441c645603600020a80f28050500f0191040750127a5042c0c081c40640c0481c81390509005108640c1c07440c0601d07202000303421a0080507024041c040c002085849143e01007810f541c4510b8034a428108004c007002a903020240711007410136141d410010300100e8458241c0b441001e400342c089184400b0b000154505001d6038029010040008626003001d001c14101d441a581940494034180c0e41e00c6011802c1840c0090140300001c1c600b0b1004070060388003064190140030341910f200303135281e520001c1041220007540d025059801c6a0200b0410241516083c00242000340940d10415a81207400d400c980080c0e01445101da0140b00300341561402c03d20580c0340c2514840c4501131020940340d2100c0ba01c405006070203207200f0020108600c002d520740c010b040c1c15401403009903030314811401900906800d5130200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 886475935 1250 886474685 886474691
    0x19030c110105090c12070b0316082d15090a09021314131103030a0e0f0a031203050601030e01020f04030c0509010e1315020a03090302120a2c0d0c09 65
    0x44030002040c0220750280c08031a000f40314280c01501080045079084030b640c8410311406000064422003080910b1190011400c0c04441c3c143c14003010742080c000428001e020031034a0519002d41a4103001e80c1d002402209842c04d459486204a001f00941c000d0040e81c000303030b64810001c0106003034021040e141d02c00c3e03400744d490440610528058440c0030850241c1d0b00110800110003880c0c1d40c2c0c00c5407007640524005d0400030190b2000c207007507a020005c0c0800050210040080a040501c05003c1608040c2c1d0500e541300d1554540300c0448400150320010180c9440c0841e18981c800d40015103414261030086640300510b00c040e085650291004903100d20900301c0000f018070381807840c10304860711806110380070740d110078180c3c0e04a4080ca00c100d5000e1203500e41c6041580707803407000d00700c078507055213000800702c01c24200030b4039040b1140001c01030070004200b940307819a03101031001c22449140b50404012010601c100000220b465001908900081000d1084c8100802240c0071070310795000070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 886477185 1250 886475935 886475957
    0x901030c09080d11070312050d05130807020409111f09080d020d1b0b28110a030902010c02040203040b0f090d0e01051621030b030106210819030c 64
    0x1d555148a612032410070f0f41050b0001661207000d03418441e0764011140507582d151b80c0303030354504d00750f94425402040001c40204042502c0c860512175150044807074034640d216080103a4071104140b1824400030b00640c0c1301c41ea1641089500c810b1903111100c0100741c1044c0c000c0c1a4113401b00e180030001c00b8000078040490001d00e0b000045460b400364081c540c081c21200d41f903080207540e150420342020110311100a60315002c00c0c4464040d5010300140740d4a100c81c021803000201c1012000044802250b00e008020103802e410070048a80700040ca0402003100f8200c0c5c001a10b0700d00c11500c2c003035001400001008108802c1d403180b00c0c03140283d00122101a22141e003040c0ea590b00c140745600208010582603070407903010300e005e0841c22111312a5048004c5444d42c0d40c04045540c4d940c00d0400b006560500f5034039907054055154610000d034000c0100e2803804420000040d00c9005520159004070952001e20010b90100c0d41071030300b218250580400d011000500a082d080c8240c4001039810502c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 886478435 1250 886477185 886477187
    0x705120705121b1509150402090105060c0708032206081003111206040c0302041410060e0a030f05061506180616050a0b0108060601030e0319050c0a0503040e130209040b060f0a0b0901030c 82
    0x806e5000320b4018042001c141c0c00d240034848a6441156140c1c1103200748000090300305420002003d00800810048400c0f031400e4a0500e001c0d500c40c0c000700c1c2489108000c1081015049240e5411650490b070018903c55010010908442c43c04004181e1070090104010521200b284440f04491090b0f800300810050800c88001e030550648081521101820040041d24072134600c40b00001c0005040c640380c596650395803c500002418203c4a03034001408100d982e500c5034a8071052424161b8425150080840d2101c400d070b50300000d903074070800c0e020038058500c0d61844003085c0000d81c0201140e81c4030405042c00e144003002403282c0300c2184180302c0059034030751080c000c0c00c0300d0020781c00096081001d40f10131840401c07201c0b44410200041440260003e407820054008a64058070145541d50704049451429800060441001107001021040180c0700c9c414401d42c05500300404610985480e0700044031824034402d40d50f804142110701244035040c3c0c000811404038241c03020000901c1e0610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 886479685 1250 886478435 886478473
    0xe06090a030203070b040614090d0311090a170a0822050415121703070906031802030c01140d090b060108090105091e031309020705120705121b1509 65
    0x6001030040c0c1081c843c5000003820807a070071b50803d10652020a1580510402c01c4d484007040303c0785d11303440d80070a03844190b940d00751041c49244044490864a054400300200d05045002c1c03194010a4009409110080d00140301c1c0722072496010ba140340d075581c25941c0c142014040100c0d462160100c0701d40005480c03800d44900b40240c4500940403415501c0c0032454000c07040c0c10182901c646181009a0f00820f0200000707500c180a640c480c8042d030390a041e001801ca582c011031529002050940e0000035070790001e0a494508402d1900451091006900e8403040c022030a00310005810400408104440c540003070744100700170390328008155504a4210b080c2c03181601c0c0c440b169004000f40000701030b149112840f00c441c0f20030481e40380282c142008508140b80b54003100240e580801c03c4020000140401010030101c100910704295580d120305460f011025100c440d180000200070780403099604484055402110940d030027680c0801000700c0700300c02250991881e000c0d00d54400107103503140e6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 886480935 1250 886479685 886479703
    0x3120301120204020c1e03030912030c04150c2117040b010308030a2c070501090e0703020706090b090615061e0a0512010b0901140c0607200d030e0609 66
    0x8441c809a0201076000d01000f5031107208010410702450b107403000654405c000c244642c011b81c0c0001c60f520310301849998103000700c03400c11040b899020410b00549940740c0c41505c055946010766010310300210842921503000240c0c1c0141000c840c81c3d5601710310600c950503109a00302d107440355001d01e4100c2c05d12014034481180c004000a12032401070022030071520103558060351074980000c0d04040064001012549410360080204018003d0150102c0901c0035100502080c04c10011841c1004401c6001250003040c9a04040e40461100c00b8031065800a402040c4c00480540305030400000445e00d0f18400c80780001d84450740310303104e41d007070600e1421a20020003007000000882140070b00300000f0380c400b10070501005818442c00c825000884c0d030860080c030b90540c10315a140d01400000d85520f14070514504100021310601ea8070400100f09258008c0c100d1808840043c0e074039400303c005014422051044e4460300354007000581d0154003040b80009504100c440f1665071003c0699103402103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 886482185 1250 886480935 886480949
    0xc0105010e13061e060e060a05032d070b070302010c0e01180b1b15040618030c020904170a02031308011a120106030f24090203030a05070c050d0c030203120301 70
    0x42c4011012502560101c07910700803042c00d64006003881e25011003038419607000210a5400001804031528002040000905040d40500410070f0400c80403840031840241c0109803600c2030900f115100c1c000d0001c1800391024a80054481943c2d0900900811241d400700700491340a1a0004041d07020300141c501c595a00340d00342c1007860809409887c1038106e00e6410b10f0642c0294068800000d0074003003910410400400c14043e840c1909005042d565049a1003c1000101c0e08503008a68403140321420680c050310b41c829503888904d00440071030310003081e1080d07120f000b04540421580c00f0004003521500083e4001130103031110a07036800ca840410300040918004444031405040034400c50203200250000090b0050b070320f44601282075003100f411964040c00b00c035500e00c0c4c981d1000014003070303c9040100b00401d00c5030740c0c0800d549104d0b102042d028883e0104a02c01044106903555004e048003400b105a034600e05d02d00b5421100703c07400300306d109005401c844807283c81031600b076038100c41c24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 886483435 1250 886482185 886482211
    0x6081810020c070f15092709050a060c35070c02010c0b040305070b010e0708040b06030a0c0810111314060705031c150605071103070503060c0c0105010e 67
    0x10500c400007980300321550000d600440c0c1d40090590061419200244540e0201409010380c0c01c4009000e001d258101c940c2c05181090b800400f600003403442c0d0642c90343c8442c0018030318080e080080c0780c41810400101080e040904842c600395000c50580c1c14204060120084130250203050351b48000381c082c200c1c0044016000083c0c0b914071a280c141c28042c0181000b03240c030140d03611458800f000c11941a80031400c00169182088454401140185044c6a04c43c3c0641020f0600a0028402400142801d8868004143d00784d809000180b51554440120310440c1d943c1c200e11501d843e40101200c541c140b070081303900788010325041155100807029000d00c84076030400014203221001c1c203841c5500900148008400142e017000107042d82007940104920703130803e400503c004d5511000040501d0740c4510810802d041d0040d05660b44554098207110320070200c04003203841d00850b68041d503494070811090003880300400c0000d101c0c0d040d03030300c0003805540c1e2502d40e038441034181030b64a1615060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 886484685 1250 886483435 886483453
    0xd090b011a0706230f060306010605090904110a0f2403020c060118140106081008012007080f03041217010506270306091608011802090403030207021306060818 70
    0x10490b401100c08500d4030700d55541c040c50034403044d1101c101c121030000c80c1e1100181841880d01d02004480d0040185142c441c0c900301c030b414082807020a02410080034000c01540d592029900e88c904100502506049a4000e9542c0c0f0300008601200d2030b0103918030583c0d0404c1c100294424002c44568030980002024030ba4685864400c15101c4000032800c03c80d66054190510040420854000c22042d501c1c00060304180013000c000b0829580005100c0c0c1c5071042071000003c80301161002c10307002105458503001641403140b0306203e0808003800c1e1f60000010407007000000d07011103040e0a210313550080809034141d0402c08040c000c1c00390b0303980b00c0310501c0011a9001651403440c070090509880c0c28841300700c0c20121745410707829211340c545500700d03c00300e00c4001c0c8855440703801025040000c1c03140d400610b0b0440d2045018450103401800754000141c1030500075011554640d5000e07200310104800388003039500905003030040f200064a0340002c5800703030410b041d1003060f150b070b00c001800e0b2a01b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 886485935 1250 886484685 886484693
    0x11041503080a0224010e1609090209060705160611010501030c0510020c0a06090503100501120f031e0e12060603060c0c16030609060608070f05040b0a0b0d090b011a07 73
    0x142002c0000811803162010b40341115481201102e92070b403460446545650406a4860040c20000c0c03000a100c0300145414000365800440794045581c0c0210050751050380c40040741003449060070140481c801d140c10045108500c5800354204c0c0c0c00342e542c44031958000c60469090361400c0c40044c042200782401401145001c00c02d0341c41800c1c141c0111076040031203a010402c08012680b11741c0200d0b810301c400b000107081c144a0021031003100401081150304001098002d469080e40151180b210b21540c1c00416010308400c1d01006041d58204c45400b5a16400a0082e184d1a040c50300845041d881480442c6e800150f080c086c5500402400d5240d4510300e90440507005040b1070451031140301d4000c41c01d840c4002d52030b80507502401002c00c00004505218064032243e03031080c040390b804204200a0280c8001a14064800071200801c031040b40d1000501402416003043d071080000107401207032007019031b208400307262080701c46021a80c0c1e21460501050141c42120003c10010881a0009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 886487185 1250 886485935 886485937
    0xa0e07081c11060a1a0321130b040e0103170f073c0b0f0c0a050f09060406020c010311090d06050a2409180807030f030906020f071104150308 62
    0x2841280340210b02d10880c0d85015240281c00d541c6108495901c5450402002950040040740d0000750000c10981b1a460760311509540b0401c0f10000d0640d0208141c8400d03460180c0e02c000801102c184103441d01e03200d0141c4d82300030000384000c540d040d10000030201800480d0f0250783d05011281c03002d0b400c08045441d401d11881480f04404200c04244051002c6034560300c0e0181d825095080c100d0703051500130b04d40107614850203004822051406000c105080f0300104c2111a5050a46041c0c0c0c0c85203110203c080381d5004071058143d1101021a01050890f800140020401000d82c2c2c00d0004514040d00c2c101140f040c3d04000e0303000380b40006090040b5206030043d07500441400400941016030b007a004081018121200e03502090f2480c040003009168043d14105054880054500c081c4d03540d9104100d2050940c0101070118203100e03500303030500030f0b403010399002d070048025590395010101201040d80000030071603400380c0c6011504040d080038030415100b0720003811809000d906646400c103d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 886488435 1250 886487185 886487233
    0x60108100c080609100905090714040902031c0e03010507120c08060f15040f0306150f050607150b090109020c0f07050a2d0305010504030e04020307080610091a030a0e0708 75
    0x1703085502000082c45100c6200d1244103185420140c6034490400000700c482c006c1e44250680b040307040411580169402041c00c005443c4111400405e84c0346221090320104a60002c0c680e043d480d00041154068009400c0200b450078440c0030044500104000d03a82c150b01682c8140d0045044084941d40f0704000c20340362a181006680741c0d04050b5584000702c0040c00642044402c0d6407208019440c8500d0449000094003110003041c020a0601d000f080d111b001c1d000011305640026100401000c020b580040b40b1000c020300305030302a60b1510f02e5030000c1d41c0710310300c40100c0d03120b4110119215000810b11106564000b031000002c24640740c80c2c000300013885203444549414207000a0302d8000c000308410700441c402c4001180c80e00c4c03d0700700a07110081c407400060041d4010420131040c2503002118030b6102c0000c81e8071040c0c030946068200d0314040150801080501c071400300b03812030140d80e0302441c071070f18250206000501900307090b103072103172490b10400d0343d2030341300300c409040880b000c10340200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 886489685 1250 886488435 886488451
    0xe0c0108060612010b04140d0807020f04021c050f070207030b0a05040318030c050108010b09060d0903110a080903060c130b28080402010806150a0e0607060509060108100c080609 78
    0x10034944040071403d0700e220281d1049a040c0030000d001c02039103c000c40303920620641101d802c11880025180c60790140310320500280301e802501f003102c0f040d80d510380c15a0004080c60008007544e5101590070801020141ca41e0200f00d6914030000e180395100090702e101fa00d40c44038801c6402d813a2011404040c002c058811418000c2800c0c005c008a11049034120065005031811114103240c400094a9180181c000c401100c03c10000702c1003540760300d001c1718240d0070420000982e800d00d41c00c0032540b03014403543d130b1505d0703000b101851402d000500000d014074035400c074140c891a0304c9102c0c0c071552a214604039006200000d00040001070f0340b020181c6000d12003400300f000040d069803081700c0204e401207110000301d4403100500083d96400000103500a000b41c07445542c0308008803c0c40310074041c00c504c02d42080000040c5401d5911803005644845078000c1c0e050005041c0846401c0e1149401d000f480d40a1003402002c400541060060b170448025648030200f494803075400784951017100400e146 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 886490935 1250 886489685 886489687
    0x30c15111f0213090c05070311210901020709050c18040b101b0203030d0501060e0102010905031803030f0f0a1403250c0b040302071404060f06081b0a0210050601030e0c01080606 78
    0x540040103010b240017418495413000da03190818940078040c1b20b4100b0080c2e841d680b080018000c2244100c0700314151445500317050b5214091400100c0c5888110340060341c50074280300502c50462116800342c55140600c1c15680164800c13007051000300d41c039101c5107a40c401c1011708a100e0560180d80f030301c00c80032103e01c6905e07031101e15600070030701e1607006410101666940714010011140e105280742c640b03400900c001e0040400c079488050380d0f400707812049100d03208414400011603400b0000c03540006580d4402c6601d800d4a44d034940c109420207070f20007001c20341d166030032281001407004032413151a41038045031078040e10041249201070034065050074480454a00d901050703080d14150f2243d446075008250140c20140c00d5401034a1850f070444c055810110240403404e000c804030b00580700380b890001556583d41465920744491a0140c90241c07a0004410112950209a48140d80d9001d2000e215a8079200d00441c1151211411000c494118805001042d803080c00900d8204900400f01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 886492185 1250 886490935 886490939
    0x90c030e0c06160f03050702120a020d12050c0106140f240f0705010203040606030c1401090e0919060c18420206041101051e0304030504030c15111f0213 67
    0x45407074260105000c0d0041b401c0807428070114540654014055a041c101800c0d444880b5030120b1008050140024688d03050245d801c01c42d10b1003113003a5500b05000c60000e00c0f605a90380d4001c0283c03800750200c0c5000b100320319a181c1c0103082c500003030791021841c42c2400c0b01d000c0450795004243d8001500d03410150a0421040300401c1090010350f01031402400001107130352070741c0350806112126030301500742c003405048034510b16a00100e00800322050008044100e030f0300d81c0c540c0380c20100b40c4401101c100c648070444106105881e400b104032094203803121041003842103881000006a40f080840035843e000e4951140031240307051b0000543d4044800e40e0951000070280c1d1100000c00c5030f000103a0090040100380111924440b000840a09109203007080300048450380c0381c00118158020000040030804251144040300e00850b01301c0272515015481c0c91405500c2c01c040c00c01180011901411082c50f08008121401c0c4500824180c0001c0ca079400200d2000e03401035011900d10300303000040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 886493435 1250 886492185 886492193
    0x40b0903120a030b0f04051b0c0a080301030b0406060e010b040b0a180b090319031b030e1f03051f090c030209060c0319030c08221704090c030e0c0616 66
    0x2a201416683d100840c00091480c28815000e441d801103500c03540c10002400800580303aa00c6131128510403c503590f030794106111031407a200744000000c0c14000004000020700148000c1240a20320604c2d0034803a8030703a0740f06140c5001d00300303004104414030100020804038003a81c005000500b412305042c0f8041180320850607200d8002c0c6d100c180300440014070742595281c280918071075010307900f81c3c0110b21441914010041154039204d07594958030707000804140b500030a00c480500c50004c05404c0d800d0070410101c0522010400d845011900b00750110b11180c20708001552461002070360b181000e45011b04101c0509440c10303642c2c05043c1e0030045481d454640e0001030186804a030015607072200d28100c980d07051502241890b04043c54081c4110300c40342c0c06540c1680140385d814802e800e500c1b807284085100e1840380740040c8100202c038651200180b8800c06001290f040e080c08001041900340241c06407400c40d03d0104c0300b90080000303420540382c14005000c0014003415160951140e590b6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 886494685 1250 886493435 886493437
    0xe0606180a0807080c03030711060a0207031209050f06030906070509011404030507210816020609040c2d05031609030b040606030b01120b041112121b010506010203040b090312 77
    0x107000e603001040140104c2d42c080054960030141940203501e13024a0780c41d1354020507000090140b0610000031203410140c42000082e0207590800844e00c0c1503005260060b205a0052040300c1c0511200c9a0032440e07450502c0540e0300c1500044040c0070079594a60f0202c41c0c0390700007401603040c0814403c04003584020100500040d52017040244421800e144101c040f844100a00c2080e5500107900a400034200000b81d03503024107a45441d4035680d60510002d00c1a0203102c0000f50803504e01084240c03120b034851ba2035209619003190011348030041c400d41080607030b480a1010003090081000c0f90540c03010140c128400c010702c0c9450300300d00340c8030340c0c6800c0e001200307940507102d441e00c4202c2441840640c1c05418010061f03c0000c403080b4055644003004007c0c01400502000c41504400b45d141c0ca4030240c0c0c55010180205a034440c0c013142207070100304d03041040108004040b0750114003003088144600340c09001c05800850034036142546082d02940031600700758150160307140206680300c0201c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 886495935 1250 886494685 886494689
    0x9051c0306080c030c03030403030507020607140a020a05041811130c08070f020d090e0411060a02010f1d0a080d0603060c0807030e0d0e0609191401090608010e0606180a 74
    0x40d40104070320b442c1400051802c81d2002c0098403d410811041c0302d1650000200c90442c4d0381420000d8903010940001142c50003081d1020b0a500d500c440182d80707c25010507405607141c400c541901580381c840080c8811205c42c0b42c10031292600400070000403e624200c00d104200c8024041800340504414520640d104102c0e0007021a8000007482400317500000c122009110910040c5080c40c0c91810051900300f40b8880c0c4c0c046101440d0205040c00400400c060120318040d0002e542c5504581c4002c0c020580d0008180c1010700e070045d400813160b0004100b009a00803480203002440007911556510340c0b02c0e019402c02d0075a100000400101d00740113200014103151110040c92410f0103001c2c4c203a5600550340f913031581207995003254954100e602d4082e110000c0d11059201d50f40c507808140d00d03182c50050741581c01d22600e80098460f1103d070b40c4800c00714080c0d03642d0300420b03507911042c2e0b0b1005c4c080c010348132515407035000102d40c0e041c090042c105c4549581d0041000c941a00007180c8181403503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 886497185 1250 886495935 886495937
    0x1c0626010b031b031c090e181f0b1c02010509012715180b0307050903030706091b08070b070204020d051504050115080c0c030c0d0c05012009010309051c 67
    0x3c00c4a8a52a1030f013480f2405082020390008612070031000d0b401821000640102d0310b40c6030b41d44000c680000c4811008503120409903088419141000c4507003055150054011803100c1e0400c0c44609a038104007140310b00c520800d014480d011042c650055615400c19141c0382c2c10004c0726540007824030345105c40b11419002d00403600f010103007051000103800d01c420910109014044040e0300c0d144041002000403a50100c0050744c407510382039030444a52148101d03941c2e25110114400003030041c564000c0c2c030402d10906c00c00d542845e20400c05218000244940341300c075006106e041181c16030a0f0300422031203200402c011b250020402811080381c409403030a03000201054504111030400b8030825002d030422402808441c054a080100307409001000e03c2148003012038504110b020410603078104090150030384521050070f640062010a48110541c0d41390301b00611140b9400715104c004018104403880d151410000708015006001c40e40710440703561144408001c01401c515614460009103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 886498435 1250 886497185 886497223
    0xe0d0b071715041d010608010509010b120304060f12050405030a1701081e010603051c090e06010c031b0507060c03031505090f0c0d0c03021c0626010b03 67
    0x140900504650030700101000340500d440601016a20200b0384100c030440403a000f09040c460040846544244844040e215600304440071034402419003000e845001000300030849042e00d0420426201d000e112032031800d800c100824000c46205603070100380640c0360308000c40104000280b05007242c104aa099916800215100501561040840144001108000f2520350601d41c899403648030307840400591b0424510104503030b220a410200007590001c054480d4182701041750001a4990340c031290000d40c01510100d659445890131502500d8181e4034486d200308a80d409a40c420409020080d20807280905440050f00400c28900175000e9075850604840360b500d0082c0990f509400d06401540c2d840c0810302960320790010955118001404014458480102c01d1500782329001300304145170b0170b150314444003d8241d0014942115888611051509128211400c8074110f0003005d0720400c1c00f88041c1d0606041004011035a04400d00001d000c0100c1e40019181100160401941400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 886499685 1250 886498435 886498441
    0x91005040e060103060b03010611100e0127050709020c19030e0f0d020303071b0f330804030e0105040b030a0b151602010c211812210e0d0b 61
    0x1141d01e140380c2002c070a0a062041c1801c1c0001255a80070501400d000c200401d5800070346c211042041038445943c110041000c5900ca0a0f030501809110300b8400026142d99000140207810741c00a0300c0300c81d0401e01801286007420b10000c040e5000d2081d4030810321400134094603641200c05a400460710a880b40001410410144603c140c3d1001d40584143d200110050141e2404412a50003e51016194582c0c910520707111009881d2a0000740c21544459008100c8640f0940040923344450000c4500501c407602900020001c2002460000e500b050104000034041c1c1f50020340c283d0141089400c094a843c80104140c1084440f039040944501081c0041d003411880480e041c0b0780f030902030380b50094041d50942e085c190b54400904010340724050f4001d1000d042c0c402401c20403120050b0f101c0e00041040180310361403071000328403404110800011003840d240d440da035000d94404100300050180115940340134280c1c414402c240940303040d806901e599030003284d84589100704174510b40381c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 886500935 1250 886499685 886499699
    0x7050319030515030a06020904150305010204080114392214030604030e03070b031e0106020d1b140a03051905030103020d110111060c09030f0d080c0f09100504 70
    0x102c0151200101030100c42c100c0c034843c4c0b00483c1804c00c150b004800035075a184c002c1c001c64000c000910301043d41d036524501c04000c101c41134000b00308403527280000740821848103400c145200d2090300c12950304e24507032195075130300c141c601a04580c001107030254020007070042444100c00c1e40114180c96920485080a0416858132811003003c0d0800d10610b42d00805181d006c80e80d18000034001800340a01000e091546503030812000020f02900301c0002c4d22030030158190b86400d49201d0803e0710103c1c080c000442c90234800031701b1280401050355004511001e6520301032400d484820300342c1d107001e60307070345240e105120030003100c1c01c1644aa683c9a0b07841004280d001500701090041c00d0411104200401c0940e441c0700048105a070009105800003c8040c01a5075800c500310580c0981e01070202040040e00003a40039140c001410f07401d90b43d44c07c00140b40f49842e104059186004a0190004140e01060160207032040d0105100c4e428a007210b403000080d03150340600850b030300003000042d00b80242 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 886502185 1250 886500935 886500941
    0x5072f0a15061706010311091506040605031509071d0a05120303040c090213061209050a0b0a0c03140c22080d030b0f1311040b0d020705010b0603040f060b060705031903 74
    0x403002a40280442d17504642c1e0b020303d28005010750314491281c51000c1542c0c841d003011442084e0380c0040540c3e90b00c0d995400060328a0b0012660350030a416500d50b05041410280012841403440341c1e541061460310041040000c46460300c040d0b0400100c900200300c507152100703036514049841004540b00d140c03515100681c1d0f8080e070803014400780113202d503c05a82c01a014641610140d00f05040107840d0503004400070109803c000d0954401d01c40c9220603c96070741401030181c0c2d0700e540107020b501c4100340d042d02512001882c42004000c2c0b60002003c4604000103001d40820b0f03034051380089601959140800401c503003000e483d40c0c01103144101c0c542c0e014481d0000403242540c1e040030b004040000140c000c21141c0005404a84039860100180400e104440c090300d00da0403500e80340d40044103110002e4001030310403109586040401169071a028090301d00c9251f0242c10b070810903200d0394999010744200400160000014842200050024009003c0180004400d6440c034000030fc402019 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 886503435 1250 886502185 886502219
    0x30f050a051803460c03030b030106032006040510030f1505010503060411040504020a0905030606032116082106091003110307030602160605072f0a1506 67
    0x62a402004084284002011146210740c40207a14403004c0078888107002c0e075401110440503c00c0940c2004090407604161040d5065009982c00c000c80390f006c4003850308071000c07030001400702100b00d0b0300d070402c0c40e440d00380d1162032400140080307051642c1c4a0210f9501070044000c40c0129440788000c5040b80c2e5980304004028003684410341c181407502d80081d0003071101a001ca03000300c0c3c46131440450280400102c0f0000c210140c0110340d5131502c40e4000b00310069070301805102c0c2c010040411610b1400142c90b8900908000050305084010512110300d0b6010701c8000060640c800d8100b004501c1c404040e20307130806c0942c0541800e9014006840161000903c45442001c1400602c610110858659010b4a600c101591a045543c90000f445e00c2071541c0018015400000c03a05000c0015000079507040c1e2203480280802d4a44050944040210882588a00ca41c441c414004000240c0c000181138603400142e8002102c140c0b981022240c180030b50040e10380d10751100b000414400402c05038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 886504685 1250 886503435 886503481
    0xf090f0b0306012921100e07090801060b03250e0301180605060a1505070f0b25050a050a05070303180b01060219020307030f150905010b040c0c11010f030f050a05 71
    0x46000b01c10010104081411014109495038240009281e071200021b010302429410492501070310706004024030a5403540201c0541d5424076000080003400e060036a805410070002c400380001404003000031000300455a00c0c1000741841d4803504c0368900b0b1003480c055421082001c524408035040030000e685016000601810826804100444081210965403455490000d580304140d00703140040b01c407110700142041c4004014404203004604d03d50610954602c003501d034030b1b25240340665240c01403002100200b84204412031219102d0303c000c212141c42400d00288075840710070610f0b003421704900d00300d507070303110080c01480300b2501003003911003003403408010140384025517020036100c2c0014400104a6082c032607010040003000c04540c4424000000c0403c14055541489406850500f9019005515103a0303000c1c491440f806160007000c0e00f01c444060300c41100001102c81c1104204090105903a80b42640c60f020418003074240a0b0303034400e1000c9010b0074070043d01e607411042c92541c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 886505935 1250 886504685 886504687
    0x203100e06100b0c120d0e060a0c0206130308040b07110a11030105060604030f06020d09140309041b1715030115030c0e130f080d0e0120040f090f0b03060129 69
    0xd40a80800210179510b0312100720703802d4a03003c2241c0900050009240c0c2c0e5541b50051104103c038881140d0701102410425034211406619005806d008010403268041d00240240b00000c01017084025000c0d00410b00c0c6c60940f0410402104250411100d50341c01c4a8542d40d2484200d2149024001d0940003c1d04654142c40c00d459940ca44040c403d41140c010103071500481c80403484101a4001c0100741d40010750308204040c07407880a82c0340d0b801150310500c1586080c0b00c40b0094500606403011103980c1d501c03070000c401c003030514038840594000c00c160300b040042100005580c9003030180160b0090100c20220b00f050452034140d02500f1140c205d4a05288050308204581400172140c0102c6a0099503c1c03900c4001414810300c6845030440c80b01c266401c14100e8018102e0540c44008114104510300c0c2c00006482a0a4514800c41c8116052080240c10134001e03012582d2002042003651a40024008800f03800700e810b001c03007640b2102160800080800204a07005108101103594010742 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 886507185 1250 886505935 886505947
    0x121a0705090315060d031115010605132c0907030c1d06030a050304050613120b0906060f030c0411270118120b06040905010f0e0c1e0d0203100e06100b 66
    0x12030000c0281141c00742c01c000e000300385c050541f40c050028100007020204001900d40e1203072406065507015070b50a180e400344803e000203485075585282c1414280c564030800e08091364101c150304484014000155a0060702c000000050001421600a02d8140c94440300740c601245204c14003100100300358020b42040d0782050008a02004540039524201c441540780c41c429892501181a680c20000070191004222401d000e183c2559910406240040f2549680d56400f4001c4000728000c0e490f0300341c0c1c842c603114800d40c60660448481d0011440c0f1080c24250003914841340c10420400c5440105010060014203580c00351142c040c8000d54081145864074110031841001e003002c502502507641c210108015541c0c83e00078864540e0000c000340701c0707403900c1c054140c010711001030030305220300c50200905c400d0706048078200500c4000400040c0c400d06400305000c09119140000c0b80d00d40110400c6c0c42c20040c542c402c00080c0f413400300013002d084c500201c0c950064213868004944881081c80a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 886508435 1250 886507185 886507189
    0x905061e091b0c0102361f030f110306011b08030406021b030705160914010311060c0303070e0a05010815010e030321060f0613121a070509031506 64
    0x10390b4000848035a202842e00e491040c204a501580316400319a500000f00e24900020f11148a441d40c081042044143c0a44010741141c03c80f6405981c0d4018500e540307150752565581c001003004907a05d04004ca502e048003c200c20441e0b07024010780000d04404410b01c451941d2028843c0599079441102416007041ca071624403183c00300a10040c000e503000a10880e140d0f00007002c00c6048241c01c000c9a0b00c564140c80c141e511140d00000318a45541500d8001480da40f85000b80c3d075907801c03448160b1480f6425600c440718020300034100550891420810711080080c1000114401c000c242c3c0e5010f0303000707903c004001140c0359561116040188602c00c1c0140c80405e09c00c0c100d50710409081c10166140114046070542c069129a92141544d1201c00c5080704c1c0e45061035885034030116619503c4901e200200708840c010848411243c180b100b00c01d00c0009011542c821000f40203005222428581e01589119000f0480d1420300251005c24a5003003400c082008455110a48580b200240b5000e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 886509685 1250 886508435 886508449
    0x50a081609180519050103201507080309010507140d11070c0b130e045111040f0e1f0303050406021605010e0120060708040309090b03030d0504080c0105010905061e 72
    0x202c9880b11010319004107000d0752703580d0701010494155407003d988800240c1842842c0d82c20403100100103508004c0010f0000d0310500500b48400418410315041180804c070700c0f002018030481585042004010341c1c3c000c83c2440301c2e490020310341c4075030865490344002c00150038501c1c00d0703003d03014158a2105020010715081c1c511050302c1070240200501d0562041450400035040f41060400c801c0c50084d020340040541e800f404c0c01e49072203001d102555450303000100310f1045100c2c07413640c81c40041d0144411768044290740e400400c40c0461100f15110188111841e116a0340110041400010100101501481074656400840c2059207a091402d40064070042c2072022950402441c1100c03048207010403a115012118080120faa0340e1606c900c001d44441c5050754290042140710f40700103088411801f0314042100098055070804084070341400c003505000c1c0088030824010310214140020920840e40203154440010542c0e042100c240710a0b5840b5005050b10400d01071401c03c0c00c1c0c0c403910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 886510791 1106 886509685 886509713
    0x6040b0d230601030c0b0c1f060504060e04020f0120100515060a17040f05100c1413030f0606050d0503040312050a081609180519050103 60
    0x8281d065a4450920005202e10fa02c004140700002d81ca0003d441c52045000031608244030388850b0f0b07108510600c03010400c1b556207031020080c62415004020061105190031011410710342c010440c0c2c11504010745050040c060600400003400504500c501e1042d442542d01c0f842d07059503642c01424013641c03c282a84224003001c0d00c1450700364102c444094042d2a00d2081c1600e40400b51640a0010001e4606032000c03182c0b100491010301c1000000f10740f007000003a60200702d01c0042d05100300300c85400301c005400d101ca202c0c07a0340c055071020b050b281c0001080765103402d6480d02c10003500c03041e08503603000746081e84900c0c2085030010281059910424144188864445040b03415015401c1c1c0c0e000050804c0c4003003144501d1000755000c028034140b400400c1e45403900e0304000c59035040c04004a40740c0e659010800d2009000200c0c00d1011046030051006500d90b45562040e55001 = true := by decide +kernel

theorem cover : BRFrame.Cov 886330935 886510791 := by
  have h0 := BRFrame.cov_init 886330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 886330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 886330935 ≤ n) (h2 : n < 886510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
