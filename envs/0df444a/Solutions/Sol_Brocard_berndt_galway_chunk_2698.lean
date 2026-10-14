-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2698
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:28:43.886813+00:00
-- url     : https://prove2.me/submissions/fc693c34-5139-49cb-8bb5-4cde376c27ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 485071942 ≤ n < 485251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 485073192 1250 485071942 485071969
    0x80604150603060e030d0e2e02090603040f0b060319020d0c09020c010f0e2e09021c21050324040207080304120e030304050f03030903010507020c100306080318 70
    0x50318050b04d0811001c070000040180a44100701405220030070710180f61504558004140e40c11100703002d4420032859909900544605440c0060420807050003082e0550030481d0104da416640704c8428050100b640759095009404a0040c01c40340d14060f454128000e01c814001d00601121142c41c080047c40c242c203601030600f1032011521800b6218000e80a00542d461040c0c00502e005992000c1d0b640103d1440c1424104482801d003d5031038103592801180c2d1003075540d50315a550036641e00180c1d10f4201520081401400c1c19010789003d0914180c0d1002e10f40312900c1c214118004902c010307400c80180c81c1d11405d6846545d00c02e4200c0d81400562070104901030741d0040c8005020700404c0510400b441c0594052031541154900d16001610b00c02140c0422503403560044c4400c1200c0d14201d024240241742c054162801c04145001082c02d4a00c103980910142c0c1100401900d90302b8500c0c18900201c501e8601482218070344404d00d81c6a200f14104803240050303210004240c1d844902c2015200c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 485074442 1250 485073192 485073203
    0x60b07060b0d1a1906230307030c06210903200a0b0a05011d010807050609060418092105091e090403030b0108070309080a080a1508011a060301080604150603 69
    0x82c03240c0f290342c0c3c40c14240854400300000407082e110051610148102c01c19a01100740d150a0701140b01d07400c00340c4150204046d40d0521803000084000b601c01c101403802480b094441d42c40c1c1d45c2c0080c400c01950407041c0020b2449500d81290040402c2e0701c0104100001b1040240300c4030541c001074500c0c105056004042c01d0b029900050100e800314651180d812105446030300907085034020094100c40d4802e10500316141d12482c028000c03460a5001802d10a80052040703213002e546642a5a280c603026015032105a500c100361001e200440600303103055442c01100203410811001e01400902900e08543d01615001554260382c00c030303000d000d56038254018210207580c5003a06d0001c01416450f006c07140080c0c41000172880d03903400703401910480d43c0c3c040c5da102d09100c101882182d604100504c0344d01680d403261300c06129a000b024849015099650000c11100c0d00c1d003c241040700042e0155a014200030401001003000c045002500658000f601080001d40303c510b45e809810b642d04080c08 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 485075692 1250 485074442 485074463
    0x5030c0106060e03010c0f0206041202010b130c020c030118060207080405030313060e100c110a180603021905030c1e0405010f03030806030d090603090602040306090302060402090a060b07060b0d 85
    0x8803542c00c11050f01c1e5920045000307000142c9030910855040007049400d4000d41d11910119002503c05110490548080e10000520401010010702024501c502d07140368296588030703000315582c0c18000030310760344000d4000744100c1c07940c0f045242408040010182050b40e003c160582040040400c480003814001d003180c5c0c680321800c401c1082002c070783c86800c0120307295035001035040c20440c43c44580a28030340c40300040d110b001c0e140d450b0780380c41d407002e90b6a000104804c041441040c482d00b003d0186042d01c00000c2c1d090640c030500c01030040d4034441120280030824200071550b03001804101540c8161440b600304406048000c0c131250b0070340d0718168002e00708030012400d1034640c0045022240a9512121a0386403d41850380315000035158800140c04108140b1820b0b000390400c180041c4a103200500d855a05d8448a00700c1e204110f00310010b07042082130109600c0d10030002c58024002c240200314503490060010000d01c00c28600034650b6071a040c40c651145c1d59070120300b804a4002103443c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 485076942 1250 485075692 485075699
    0xf0e04050414061006021506010e030d021e0601030503091018080d0e04050610081f15030b100c200909060103150b010207050d020a0305030c031e070b0f0405030c0106 73
    0x10700b1180b502d03590840e200e070f00c0c0069610700c0c0700e0005204a44507038014010b03600414891a1a2150080000e41484900c0054500546040000b86000d6800741d0140008612407480010340c40c000291300350895003b60b00600104001000300c80d510942150f10140354001441c06075941d84480c2420966580425000920803401007428510319240342c0c0d0301c41c801c40341c00e0104002c4030015100c80e604058040d511000140c05900c40d40e412281c084422809014040c61103d00c56805800c05071403601c081c040450815054010403403a028102d80c011021020f00f60000d182c92400400544000305820715400c01c402100c0d503c104821000d85000001d18114414070b551f080b00307200442c0c1006c5c48185d52101c1c00881d2044d04d500d21016400340800d545170030108400c40c500d0350402e0340e000108081c0000040c0007040280f050711001d00295480341030820180320490140e40501107504010800341c0c00190303442c40c0d9594071100d10800c01d000c0343c840d41447d9113540680b4074604543c1d840e041020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 485078192 1250 485076942 485076953
    0x315080c040b0a03150902062a060601050a12050c04050a06031a04020f0901081b04030b01061115070305090f1002040515071e0302010213060f030c1e0f0e040504 71
    0x1100d4100c000d490500030702800c403041c0103202c506803201400c0810a204559101107081e0011b03a03843d400140b01c90b04110b0300114191282c03440d50104a01072890741221034070044c0600415610010900b005802d00780d0070303030003c0c0c0041000f04503990619541d1000030317203109103041960040c081c041c1204000302d88503540500240690300102c02403400d201e68203601850300d402283da21044060300e0302c1c1008030341d000642d00d894004d030640c5554000200c6070003d018078507002c0c0004500401a40720b855140c900c0240201c90881c104a2440d085540d0b000900c242601d0b03420340081c02c2d07140008035541c0c2c19100608248a040c1c40003011b000380820319a941e035440e0043c10640740110b906502c10101108111041c1c803400d0401488910111281c19080150802c00310541d4002c3c000903103000c0c00c40e0000349610b80039802c9500071445503500c0e44030003036162048400507002070a044102c8241c3c160341c4e44884e43c1507144802040159413040711250b21038400b041e0a02400b03401030020b4140b03407808 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 485079442 1250 485078192 485078203
    0x40b2806060e0306101806030803150a08010b061602010509031e070902090d030e0a0b0a080a050903070c0e0c0c010203090303070f0801030b0a110f07050109060614010e10031508 78
    0x1264000b441c50500604903280104440f4010180c0c003041c1002145081104030401c040104203841c10f40c1d84880010109502c03000852003a42460801c240d030301c010004000e400755440c0c02c5160f090385800c035820701c15100e400c200d88140000000c5082d003c919840100c0d070a01c42c8001854050203420401e002c5690b11529020f0503240440548500b940c54401000c100d01852840719070007824030004001190003044002000040940150640c070b4492182600592002e03141c20f0000304000b0400002400d5803248681082c8c40d28051890b00c403141e12400341c0003e03c0d0080c01d940809100104203408221803c1303e00341b40010000350348074601022050b460b50001c940c8400401d6101020782d8205208064003070503a03501c040190b080ea114100042e00502801184a004140030401000c601e0410809000a07d110f00004185140035280001c1520819400105440805e40d00300c030b181d0703801480200074400140d50034079500c004034500300c000c2c0901904441c12501880d802041740c00e008244e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 485080692 1250 485079442 485079449
    0x21020f040605060a08061c02150a02070b0a0c05010b0f060909060112091b08121b100207081305090115050306130504050a03030c0822030909020a09080118020108040b2806 75
    0x6060311001e046101c8001f5280003040b000b036101710b040c82c41414404490001e890300b0a42c2d8811610075a46804035120640c0c442c980c50030208046070b810004000090052a01242d4155503244824440c1d1020516074024044018400c005200002e06280d00c54500e401c40803658540038450345110f800d02036400791144469940d0050020380110703418400140e490003003541d2103040b52800c1003044200300052a45101185103005130b00c0d040d4185030300c43c00500280c600804080b9511030a03000046003148041d0f0042c1c0c0502403500c010400241c0c40a040f07002e484031760404594a40e5030b40000303908402001d43d140001031801c0148014000006101400140b10342c804001d031384001d4000395400502256007010070301070b06141c1119480c0001038000100d20a007840040180c440d000741050341c2000d500d000c0058030040d001c1203000c2007402a070200320b6001c030340da0078084240d4000030010940203002600e02c07166000400e6600342005142407401c0e080e2800901180000b4004101030040c030310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 485081942 1250 485080692 485080699
    0xe130c0e0301090c030f0804030c06090503010e1204050d1e050102031b0301030b18011407030b010f0e031e1005090c010917060a052e080721020f040605060a0806 71
    0x42440d41014890301114580041c44441601d02e155034280d801000c40400b118140018040000020702444100018050944a8460b00c45c00c120034982181c1c000c00c1080300a50007490110080044602101c0039210192044401180c031345c1013056041603000310440344c4a0907001840d00b031000c1035000d14041c0210b100340c481c80e49030040c10700b4103902080c00047c0c200340780e00c00402c1c5107030140d02c00c020313584400c1d40000c0f40c2050358003400125420101c41d03140100362510554805981c2c0206960003080c5281070801341441d04c0f8000c650342e00442803a250000b2030390a2824500e130300400910b414401401803e0101d403400c40b920b647c4845000b4000ca000c107071032040c003140721081d4820900b00e0710008030080c8466542c101002d0050b100207492b0000c90501030703011100010644001c00d00804507200549403c07880c1044040c43c1c44440e03402450716500c802144000c410340514580000d54040700c0c10340140b1010340018000b0b00d010b43c0065440f03000010320300c0030b0319007046100b40b1030072046 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 485083192 1250 485081942 485081957
    0x3030201060e10151e02010c0206090307170f040b07030c11220b0609270a0b090a02071a011d15010e0402070606080717011505011b02010e130c 63
    0x241248560100181d07400d0000030300490302413000a03503031036201090703a4440c500f9000900f40300c0d02c22042c44044040000060f5101d00e0300c4803000741c040149a40152030301c8000d51501681b611550f03030061201c240e46880360800134070449080c01203010344014003180c1c007485580e1481454003a0203860801e1044892020401c201007480c68406246080c8010b4125088618070750145410020f04640c803e20b580b1031000d01420429840f01210f0441c2010340b001401080c810350700c130030404807130018040c01c007940c02c00c82c110b005501c500b00502c5d040300d2500c60140e11072085141c544180078004080501c054140d00000400c8803400b078000401c4100070f0150545a2100202e46504c55090302e04140810400300100c20141860340c02031843e5401104d0004003180c0b1014120b0600e521540000b1102a51801c000348403003081c0b29000c25281028850344c1202d29180c0060920f4401d00d00000580407051040815640240e90695041c0c000030711550b921481000303120014031407000d1017000a02344 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 485084442 1250 485083192 485083199
    0x2060307081603090b0613110a0306080f07120f0c030b0f1e010b03011e03080304060c1e1b0519080a02010608070e0f0612031c390e190303020106 64
    0x284c400c081419812040810680e910031045c015120041e41480c20301070707030b24212000d090301008040c0140380c0003075402040651401e05000d1a240c0384e500590015000400b0400011884501002e0f017150310616464807a0100d0400ba14105d00b15400604a11103440401c40450b09001c1c0703ea11a081d000c8150340060318041c1c1203481004240108540a0030400040c0b003840c481c000c28148102e5000101480301d43c59036a4800c40790003d5070f044034202e4440d904444c1c590f0700000c684504d0000401200c8010005c420005c14806021a10004020f03504683c90140601802860450b004205030070403040980d00c2c0000d003071b81c048d419a1006519080010850010116800044690409580d101030320380200c000311011000d42415401000700c50004000d81c01800904941c840d980319085901694400355025500c42d8104001c81c3c0080c0008101045903000c81c80341903000042c801c030795403007031190b00b40da282542c0880c40b0791048080c0718000070784100070035110070303240b00e0360082c06400d56 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 485085692 1250 485084442 485084447
    0x306031e0507090b2404050f03031c1a120a0201082a09121209030607140a110705060f041701021612090e090a0b06150405010813020603070816 63
    0x800c0c050003001500510b20800c00d00d41d0750380020040f240b0090008a0903005422030100c0d00254888050421030082000c02852911844032088250241c1c050745c40e02150070701d01310766000030f1740501590315500c0043c0d04a101d03144c100901282000741484011044414203150341e5000c0c010100d001803100f0002840d03030303400b40d0310080501c283c50b8010b01c81d115000c064520150011254036400c20b00210154155250400c50384034030b40c26060030181da5452a00c00d060608200074914003d11400c1c1000e50740303d94943c0101c440c4206145050050000d1002c103050400100c2d501607a8080000300e031204900d03030280001c02c11184040303409e04031808405070702401e07030085500c8203481c1c0702c49608000100300c515500500b00b400500c1c01041094440b0b00141034554161895a655401403480d4002c0180c480a0a0f030806412640d1601890b045d2003821443c0c415801614104207522000c04c9040301e0028907401d040703a00a28150726031401c40c50007400290229107040803000c03000d0b80b89020030b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 485086942 1250 485085692 485085743
    0xf13120807140d140702130501170c040c050904090c0504020a03020d0501090b1c0809030105010f06030f200f041502211216020c0d030801180b10110f0a03030603 71
    0x403d0340303400000d107a10b108002e80c0754010000c184d0300016040c0c541450015503114450203001c4c903504140702c0c019005ca885103818620307143d0601581c90310720a41d141903044800e58001e40b1003148c021417a01c015280c031003421601ca60050350442d001040202d4020b8164014006c46001c505040210ba0b0741d8205500c160760b40741c404240c0108140c00704900450803525180b800764020003100b4070b800105800f180c01c40300240c0c0b000351014101c0d2420f0082551600801500c01c0031444d080c000307903007130502050050882c0c242140d44804001240c04100078010242c40003004042240c501e00c0b071040b9006526011544605980340000d403241043c49007190090707509501c03010004911540d244081c0d210204c09101668081d4803800b607031126503a413500c180e002d0140c400e565078001c551505001800c44010102d2241c070590404241480d40d485554003e04240c0c504c2c9490018030029800c800d05083c000c1c0e00c4911075000da520010181070f0140c00490440384100b401038110302c88800c00b41501d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 485088192 1250 485086942 485086963
    0x4180c1704061a030c13020f1204030509150306090c09010c290708010e0c0313050d0c1b180504020a050604140a0e0708070f180e1506040b0f1312080714 67
    0x3906c0a1050ba440700b13a907001d0408a041400000e1a181502c84502031030f100484003100040c600080000080c1082d0300c040002088484c1d1040c19400c081001418400c00101544400e51003c44c50002e41c0c0c1c402c01402800079002401c444491942c2c1a50b52040348450074030003034565012000c600076600c00e200c0241294005a0f00380182d03151482620095030018200d03d144500002c8140085a800d00c040003150300d072900c440c190124940303012104035858920f040c81e1016618010800e032261541480820a4030500004056459200242c0f010340c46800030b503000400800c0c042000714100c9140383d404801103410081160342e40034000d190f803408441c210300140f45080410240d60040c08440000b81032801c0c01c9100b10300f1699030b0508040070b030f4082d1456291070303000d200c00c40070741d00d0907400d100d582500d0b23283c5490b0070000d10303c02d18402c1d01c1d200c160100c400510200e904010580e1440640051001380300642d4883c14807500715000f007031058400107032406030032045090000f41080032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 485089442 1250 485088192 485088199
    0xc11060301050a0905090c0627120c0111010e0d0203070c05090103020d02130603060218040e060903030403050a020a1a01031101090312110a020607050703140304180c1704061a030c 79
    0x80e418007130b40030094440038000950740d10a503c0483c0b505d03910320024040803c0d000840702100c0120003401c003521011511524024000110a030009070000310320f03824400310a00b003001001c01000f204500503d800410384405024509240340b00583c0030004041c264001c40b08501540d1300c581c2040200d140030b02c4006d47c000c0085002c0710040c2403025064030354401c002000200c42d603a9803240d100727980c0038001040501c2a44140c0103800e28191103030092007074102d401030495184c001307025543da1101401c090706011011078140d600318400c001d5447c4240d803184808204500100d0050707010042030104a580301c900746117540b03140d4810aa03101c01c80c1d030031001075031864229200a8864240d9424203248900401c2c0e91580541c9800c4000e000503446400240282480c50800803e004032518031090b981d00b0411082290000b01200e020070100c101400203140c442042e410ba449006c4100b1203240c095040007008184074590740018004031905407009012104282007584410451030507562 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 485090692 1250 485089442 485089459
    0xa0f050a0c020103091410060911070b0c1608041503050a09031e020703022227030806131a0f0a06090306050406020f0c0a051b0102150603030d0c0c1106030105 70
    0x550b03c65003140c5c20203401280d4601045d01c001c10624200030070ba00c0703041010703610b13104104014030769072040302c040092252540d0309124190341e42c072580740c101400300c0c9805070012503e10161403002880d00301d420781c04040550380d035680b4124104002c940c2080813011a103000d00180d450612800755200d040d9142e551000f68803448031031a12101301d51001141140301e80400800161200500050146484042000905103035406181500c200c1460300d81c4070701ca01c01c1201d0040021241030f0000e540c0c181800604ad544072004108205540d2054401546c1055900656020440c600c120221f0041d10306203258210f500c140441000c80748981c2c400500302c003804102050540d031225070407a100b00000b5140003040020182150001c0000f006a60010701c80d507c00c002d010403540d4070503010b050b03a03458007086450000c0e4842807940c0d95034040a18441c00074050707560501c2203880041c01d10700200140c119280000b03010758141d00307084500700500d0b41d08200f103150480c0dd0b02d0480b04014030f800c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 485091942 1250 485090692 485090717
    0x4050a080c01030f061202100306180603020906101202090d0b070503100515040e0a060306062c100509070201090c06200102030f1b0c0303040b04020f09011514130b0a0f050a 76
    0x40e48d030304807251001c055451a01241074a510000306218030360302a00030818038114010070004100241410b8032400c02d08450070380c0c281d00440c401c04403184584005884528400229105056002008280794003010420940350f4000000d103015a012050200c0d00c65200d00500000d003000c1ca140040e145401d00c41000b840340100d0300c0541c010f00340040815616943c0e45c0f60820303180107400c000b4161000305e00c00074903547c1001e00b500c1c0307051310908103917172500340803905800c641d01038081c1e10f015650300000100b542d8002d41100f00c1c0a60f010410451540c1e4071440102150380289108100442c6410180c444420500a0383d0285034660198615502d404007080b2060880c0e100e2003850341802e01c44420b25000c144055446240100d4021440349007d03c10002030941c4a0b01c0a40300d103030b1010050020b40b0442c801c54040e0329207820310008143d1071851005250282450322240700e0320010001c5007034a0640041c10840310700c4d40340d440e441500c0d0b0304141c0385409080c005500007585c00c440302 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 485093192 1250 485091942 485091949
    0x9060b150f0705010b0a09140f0402011b0302010b0d060b030f0f0c0f0d0b011d061e0114070f0609110102070e06060901090915230a0b0304020604050a080c01030f061202 74
    0x10400b40d8031500001030f4407403411010034000e80030f5612512450b5924105c5d00300c0d0043c1c4958140d886159800300d41e1075441c0643c006001c003070f000e984000b000e601007503201080600075800100548001030a06907414018074080d4003400051644900a016001e105540000005900341507e0650303c0a026408030700300500c1903072012040600d034807100c41d54192011a0025200c94017800c920422082ea01004141e103407003625000d440507020b440b480651150900414240d0348160109103441c130f101059460b00b01c00240075022018150031060200380b01045500d41c4074441c00c40c07080d45101c2500da00d51005907180c07601442406072010031040018818075003100142030000c4141000500b844d00e600000c000c94440e40d003017841500742030509201084047c07200c40e182c0c4800d50311101c0c8084803500403420000944c40349500d0804003201007070840d034510741507501034171000c3c0c2100c0e075103a924555140c1d01c81070410400e000c680351000000101c0440d0281d00245c5d1450060b000001c19203a007807 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 485094442 1250 485093192 485093197
    0x1510030207081b010212090d030515010f030b120f03130504060506040b0a051c0509060f09030912010908070c18060308070f1a070f031b0207151e0309060b150f 70
    0x24a1500c2d5420848170003480c00401b14540a030300c0d0080140210150158090200d40c070141000e0001c0b55092062600c0340c0c0d000c00011050101c0f40b8003c01c3c00d0b01140089400001c03484400007960292804000e03201d540040a0080c80103820070101115984100b4401110040c2c020340c0e400c060204014007a1700ca1017002000710300c480745001864041c0880d000201400c8180e560440103840c4c0d0180280e581c0204181307030300311844841801150401d00c01065807841402c0e4454041d12022040e08246142903000259480e00050115500c000501e07110b5a40055401010f0207808840c0c820094900c1d14800d03007007030741d506c10072031482c01c0030035102e00e034028810711000c07a548040f0181400034a55034500040c0a480303a500d4052900005500140c01e40b40c508a407072800035000410300844a50000702d0008a4800d0500f400c0080303d9500225419507810301406151a02d003c041011180d045d446100028050401040107450402c01c10050201d0300205d924400c070103216000e104c0448400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 485095692 1250 485094442 485094487
    0x115060212070c0e0f01080f010c02100c0909090803060102062a0313020a090e01180f0b040807060204083703110c090c030406060e0403140d0b0405151003020708 71
    0x5440c648613a00c2d61520700a210803186030f61242c0030000104826102004651556142200240060084213400a686a003c0ca0403c80c1c0c3c5a103035550f82203054060818a40903150910050002903c00e0500d854140d101b5111680180300300c10010300c3d8405030349a440d1408800c0f4105256810000c2c00740120b50300050300da44603801c20705e00d01000581c0c8044a030340c0244201100813403011450307011582180c9500c24a080318003010000080003803030503505104410380c4800b240300d50b900c49041c29113440c001e040004201601c00035012568410000d210302e54840500740e84461085841c08040e203e0482c80303440c00081a40010060010740581903e1400307513861022103103001940c2e00000c141440a0b1080c2c0c00f000e400100744024440075000c0c040151074001810f86c26800d069030000d041c072040381041641c0c1400401c8451040040e0b070080c041d102d10040042c4110300340045200b912560080010384078950b900181c0c01c2e054041c0c002d59000075040080c0c242007008180880302c0c847c14122 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 485096942 1250 485095692 485095703
    0x30129091348060c0b1602010905060106090806060619080a0b04180221060a0203060d120503100807050121060306020f071514132d05011506021207 65
    0x5101010a11014500e01000b01e00c0c2c0c1440542d031940e180d420341552840d50800d03020400d0780b107108804109030010854000c06000f08038254070010180c01c80c010103000c1c4004005000e0072000260040d8020400c4082c0c2e1680f2041d01d1641c3c039031404008461080d8035070300010701c00342039070050301c1030151019a070300c02c0a00b40003180300e600000c00581102e09003d1807200595920b41c801c0b00f5810304130802806049640b215441c000040c8035020b96510004103800043d2303030000300140058460f118464801c6030321550011a081072244080c0158004546400a00070403460001b210040000d2480032144180c5801c0000e16100524007482100c0c032682d60070b529211440007000400c00d10080c03c9a08406010603200c08580c94000080582d080b00c0c880040c1c20300032403a15012036065103a401494205990710300203031518006048042c03449180145c000d10035040e120b031f4500320050b180403031b00c240000c11140d0703242200658030107124080c0100503031150028044c1806018000c00c64035000c0c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 485098192 1250 485096942 485096993
    0xc0e0109050d2301020c0c0402040f0e13020d0b090f0151060f0e0f0d0609060f0c0f0207030c0e0405071802040e07030513200301290913 60
    0x8119140072540f81c45000000d60341c00038800e0f91000c0305002c42c1d10101c40c22941541b40901d0000d22000005680c080d0100d140700040101c2c02030441103000440c0981e005d0200c2e200c2c045503050410040504031000c2ea0140141c0b4a0f90440c10810b02c204606000b84818400300700d01400d19003130404c4021101d294a0380401c001c181c41c0c0340501008814211000c0031810521410120024205001440000c0500517a04d186c201c0765038580c0c1c080b5818180554004409043c0c50500c0005801082c1c0064925841d1180e09007024455811442e50b40d40c25880b01034030400710100482c1d45140c10311003e0320403081d8410502c6a90b01c2c1ca00041e030424000c0f81118410303625020054001408924003170070a56000400b00041140c100159501c80142d0408002518199032106507194544030014008140d03d05010000d0441c243d500581d9603000c0c00070041c0c01908250000982c1c2e007005081d000710541c2c4071519443c5001c40701d8501c100c540307a813150404142582d03161400041c2c0c288078202c0d04d011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 485099442 1250 485098192 485098223
    0x9050618031c1d0312060402071a07030603030806030a0308011505070c14032e0b04020409060f050307090b010c1101090312052106011704050703080309100c0e0109050d 74
    0x2d80402ca95601c03280b0000300c03040301d08440011601000400d98a5810034803850800b20034107043d450b07110800f03480140e82c580003860036000501107951085c45010008007404141581584050709492190300c030113035103031a0b142c02c01d50b13216030111000f0000b990000c018403d514500201001806042c00e086040160070703034480800d80d180c2d4019580c50441c030054009549810408108c0030302c001210701c1c403106120742141c000004180c51341448103880d1030081030b0a407034550441c0c0003005001030401442e611340c03000d0300442240d441518030034892920007045000141c4528440140c058407441660021644c1d840072500c034401030141400780c103a0000000c103038101e80400c40c8100035a10590b540082154000c203c808481038000580310f10400c01610742d03005071024038035110051480c541540c80d844c20915001c12604020402c043c08000d2000d1400c0002c4c0404038140200310500007002e01c1d0004031200990104040e00003070040380c081000c0e062074900101c855016841c03004d460083c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 485100692 1250 485099442 485099467
    0x6070204060b2113033606120e0307020108040609060203040605071b052a3606090109020307110a030f0e240306030304030615060807030905061803 65
    0x5040c1d000d2040480001820300ca049482403000c0e083c52403600390030f4460705082c580a03e07a0003100e1030003810f010b07141d0a540010803440e0100c03640c030b07100e04c960540131590b06010445003107518440d10002c00d090a00c1286510f043d0701640394100c990710011400c2099603001100d0030980900281d410a0350b0300c5082e404602503000861290740030345000301715814060001480498101e010491106601078842c3c005040464070f4450004800101c2428009160f0300c2801c882c41c0d05446540402d10080030025220f0103032900c4188001c40d81001c10208110821601e1201c4c1100c00c550f002c0500401407003003101c83e9026617081041858461035540d40da00c0610300d00700b01040b040d400b149248000c050340030361007102207403a81750a51343c079081602085030404118001d00860700d0f08100120000f4950785080064034010f6401903c01d1041503614540e107250200c0c2ea0161400045441d00021030310780c0640149102c1e00d5100001713203a10b0303450038032040c15401951040c07a8640420090781c80702c0d60303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 485101942 1250 485100692 485100701
    0xb03060d0309170d14070209060f18090c0307060801061e0507021008040b070f0503160c08040902180a080a0f0309051302190f020a0b04021305090d0906090807060e06070204 76
    0x32084010700d20644c00c110090820072400c2c186100d03d54040040000603100d0400d296013084003610002000c2529000080221001810000030542c1150070482700880000d09080801010741c283c07803d03251104c40031114541d0074000c001c0840e56100c0401260300240d001c0008488092400b90b040107501d41c0000c101c234910818200000380e030441400113211860020940104440c1404000080e00100140c954000100344030440ca040d442500d1101d80103015002070182d001090554070b41e147c0c68454000d4000301d0102108407144900c50686e41800540c980030b444144008040c440c0e01541c40c070410340c105080490402c42c01000020301915100c04486010040000146e1518040b8044070a40c803811510841040000240203800c02d4011a80d03110060b040800340c5440c3c1d07910300118100300d468581042c0024940750800441c3c1d40302160828004030f003580c400c81100d03500e080454102d800f03809100103e8021007410040c1a0003415054000c2c14040e10580c100082d940000d4101e8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 485103192 1250 485101942 485101979
    0xd0914061c05100b041503050c04050306090a0528021e04050901020403110f0a05100c0f030906020f060408030a020a020124050a1d060d0203030d0608250b03060d0309 73
    0x140d202d5080c050701c8603488030240c003d48800e0070a10b050500d00741c420745180300c0040c03400c000d06075100045841032041d84200c401514026040f030343d0310300b0103404040e44c076904070600b41c4850007080400c01c8103e58100b60398034244291500e810303042c646602080358020080c403107905191817001820104c1d48990080e00d200381042c400060303c4603d942009140e4141180d0007d00c1043d4200c2c0d1110580d44409128098580a44100c0d0420321101410f95040500e050003410700104c1c1c1500a04150744107070000c00780c5406500f43e030b0500140d0710b001c55407084256401400c7c00c03010300029081c10780f16805400c803651544008512080c0010010041c1000c0311000c00c910760214405214a04140c0c44140c000c0850814101082d0500c290700754031701c2806400240b01d00100112407013550b400304192004104c051104001c416074600005030381700028210b40f400c480350a0281e91701c120780303804058219251503810b0703441c40e40d41d0810000018017061048051140302d820204460f6540c400d4503040b0f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 485104442 1250 485103192 485103247
    0xa11010309050f060612030f030c09030f011107140606030a03050a02070b03090a0317190f111303021507050307111203030907050a0b04061704080f0706021b0d091406 73
    0x160605c1c2007403115424881c0d03d0865180c0c000c1200104442c0300b0011241c0c0101080d0900e0b481d2911500042e0520b6011a080e500641c20414141c5103869548014542c540c413400110280100c0c035880d0f55100d036011074102d03030702d90000000c440100f40108000d0230000d4491040ea0b102d1911000310360071941061380e84d8941e41d8480c9404c0c2003016001007210004182c80c150600c0b840c9403002d40241540d503218000e0204030f84890042040754159003000314100d0510001d03035110a280ca07031020040141d44400c4c0d101d081080046036085032198104c03401c40781c00c500914a06566a190a00700d40028204107803c0b2040ca5400b21030071105002035801480c00d80d01400c1d42c2840d00302006484c070b455412044c0c2c1240c04010422001e600489203582c8001074105083d0555a14244001039000d00800100c3d10040003e2940400c14258024034405500700440c880303003031950054555803200500c644010800c155010b10603910121005140324400510701031901e404803a1103e201d0190303c034079814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 485105692 1250 485104442 485104453
    0x405070510020114070305090337030b0108010e0c0904091a07050414060f1c150b27061617040312080a200a14040e10080a050a11010309050f 62
    0xb0307950244c900940c002c405480d00f485941001c403000c030380b42d104601e035000c4c0780c1100100b04071179102c60341c610000003802c610f186002c40e03400040c094058501c1d50041c038002071950001091504d84207a510303002e00c100348100c0b41050040c030305100082611201c20368170308c2c8150034000300c0c488001c0950b9106540d030b5138034035840300d1400c0c184990560443c022a44141c00a20600400382800c6007600d4544040303c0b410054403091881081c020b0600102c643c40c900a00c000204044c82031702c0c005c02c40c8003034810070021078481c10840c03c0c1d6031b08400644294041820414102d92424031448001813901509840c4040e46c864041c120b12680182d100b114400043c1030801202c0c0c0d0401c401e6540315490b00000d100a56190f541d80d00c0d10000e0f604200303800c0c28080b0710100b03014403c5088030600091409a1f035a52074032400200029042100e001c03003000c2d0f180303801189a000203d500c88410303601200a0246158a036a200400040111100d040654a5842e00081041042540300380c0c42c02d10040c22 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 485106942 1250 485105692 485105711
    0x1002071b290304120c02041b0306170a0c15120f050105090705070201020705091e0a1d03120106050313050a0b090d09030b01033908100603150504050705100201 70
    0x1d490114904031049080000d00800001ca00040741c0d08410303058900d05515078070118030000e8020b1000040da220342003084a01e120308a905503010100759482c1c000386d429100c8080d0a05950340e864503000a102c901d0b00c1071b00304402d52042403c112100c00e10301b48503529200c500101c0702120300100c1800d08103601c1d07000401c0b85050030b02e41c1036000308841c64401d1a00c6c805400203599a00d40c0c1c403402e8010440080001c41000d6941e2542d00981c12035100d89a5900304030070b4980142280d0403138502c00183c9c8201104e82c0724000822a40d80d001144100060707686032160030350303c58000400025080c0700c40c151b1031000801c240000403180f8402d1080340b03440d0500f041203e207050840c001304d10034044000e1050020412a510b0a811a54041c0040c1ca0011080182d01030540a003120040c1034000303001c013420801e0304810070105481c0c003e41250044001e802250b0240e0b0510311024005c80001121085804c0345a080207912038003a000b10341101c0d5882002c18110340b004c50503500140d54890340380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 485108192 1250 485106942 485106989
    0x62d0d0c1802070c3501020f070602031006020312010303030507021c021506090c040e060607080c0d110d0e0609010903051002090a170d120b04060605031f081002071b 73
    0x89014200d52850421808215103a817411106104589440716010400e0040c2d08102501107a042510111400f52520500d00c1e0000c065001038442e00c0300720040c4440070600038070000030313500c0b01c11591070880d80300e92a40c1c41c1a03000b03000280428045002d0101c502c014401040e1001d0341c5224607600510040030254641451401f003d4a1503110b03510150600544564050a0794190381890110154075200c500010303a00744185400189800008507507401d1007000420842d2039071342140c03120119000400e40f401d49a400d481c4a100c003007250011000070034102580038000418040c1407240c2429129100d251500303030080c450342102c035000548001d0320b0a1903c003c40040c49060b00302c81c001911848080c0d2501c5071500c3c00e40030400200e4600c12950f0b0160440800347c000a8010070003281c03200c0c4010429841119220b45000540c001c84c20a8241520700c0c00894040d880079061651109180001079400808181c41e603200c0c0c551404a058061a501e10080c49901c001c490403038a1804038 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 485109442 1250 485108192 485108213
    0xe0d080a0b010e010905010f0c0c09021306020606090112302003071b03150218011e0f0c05010e0303043005030a090b0a05062d0d0c180207 61
    0x41d18100000082c1c285160b90b048001c80f41912001d003070050f004820340d0001c84010038540c40c040c100040300c100000c5c0003100b65008189a42d40100e0902461742c03622026030390350000b900c040c2d0300013040c100100302c18100301e11449a1284a510a0720038510303c5101c2400005800707180408114038004a55075254000c241c0c003021480f211840c0c1000c04050144584a01a403c2c000d03240c01c000d5201c400146440300f1402d4037071540031444520103008480c2c2d0b072000303401c0103450315035a00e041d000500791903018072100c00c1c14186c1424513410514400004a4041d0290082103051140058840000800a010f02e01c00304603010021038480c942030070170301899040300f4400155100c4441442100202251007a50341046504190f60f4a44813107a00348010520000050844201d42040c0040b400e2160040d50184104a13641c800c2a44031800b4080101c20910012040300090035000119042001c0111103007405440d00b50f100640c2d4004a1440181d204580e00d90940d000a80c07400300401c6072031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 485110692 1250 485109442 485109461
    0x5090405041b05030d080c160507080105040203151302040b01050c0a1410061a0901170f0a05060901180e031e0a1d090403050c0a1e0b0603011a0904060e0d080a 70
    0x388000620314002a00009026047c146484030004151641c07810316940e00340d4682d400700c202c4003241e40c0c130041c0d50b00a0030261001ca20038094081074a14005c0891701342030091401c40d080710070240c150381c00c0100070406004001c0c180a81400240c01c03500083c00700c00f24180c0502d00c0c035140d2956507041c144c2000841c00074030b00842d141500a00103401e14110f02c11a40054107001542c805c104401650600c5005074880381100031801080200440001001e0240310181d030700380041e032604000c2061544003409400d854010b021554400c100f00d42d00560783c103483c0c100640b4502800ca22446150100400440d20a11000240740d035080e03500c408480001d05104040c20380c180070180014802c43d6016002404201c0b0100740d01c52600001d000341d442403984103000027140180a10420103a100214090f200440c501001425508043c021b1140300b40080400000100d68241088a44000a803045e0f03165555519116140e02c41000340d1a15201c1d1500c3d5032000d0b00d030092510701504c00000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 485111942 1250 485110692 485110699
    0x20a03060e0f07180b0d06090b0a0501050a0c0c170d0f0c05070e07020f100f0606080910020f070b01030b0a1a010c0b07020c06030c04080f031606090305090405041b05 73
    0x108003801070640e02c107580000d51840e00880c51540a003030302d80c865019800c080e0340782d24000759114070f4920070303070002080b51180c003000c0c4504034440f810080061030703910600e03020039000c01c851024603106507544a40c00307101c0d41c01d03082e54076200c109244002c0d00740b00d2841441d901ca8080d90003910f0f0001410340c0140d00c940f8042e8660b5a0700d684164031122280300c2d4100e0700f0241000300e040940207000209091000301c0444440802c0542034802925841c2c001c060301c541307019404034045200b0030a6070b108a202c0001010440c41014000009510155180b08610001e2060380000368242020f2802580281e086004c2401c1104881040b50115041608000712840c00104c2c940d80110025440035040440841b143d52890001ea0170001000c04542e03000388004200300c0a410804c029000f0340c2d0340202118120740c1142c05107952840360fc1d001d1400d400d0400401d4001400d25007110074028400c0c80d00508103105417020400313407441650120340c1d104103d82c581c00991461750722080100002c0303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 485113192 1250 485111942 485111969
    0x105030c12031e0702060a08010e0a14190212040302100f02070f02130b0406030305030406050a020906040b0d020d0c030b0f04020406140304061113150e150904140a020a0306 76
    0xd40c450750ba2160079201503210400781030034403902030014103440546070068903031a60b1b60540c200c000c0000308240240184241200049580b5003124400d880030f44031150031124040e1210040c0c0024019101c403440501a000c00c4031200d60419041103a003e140309800071310715202d45c91244419200c8500103502c6480c41806090045003404441d90899501075071404000c815034030000c0064004d5401d096081703402e012001081642c00740c0114812030295004011036111103070700308281c0c820840c02552200c0e00740000c0c0903043c3c00704010f10001603400001481d080c644044001520082c0301000e0100341e039407680311070714201030700311101110003210114136085c01c01c0800313020010452032050345081c010001070200206907200358001e560f4840b4182e1101081c82e100d102200076401940f0340721034900700c1c0382040d81c000e4110712480d040c001c0c80301e4034044804a14900c1038000d48609540151606405070300044000501e501a010208025a40381000d004c081c00342c42032544084030442c802e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 485114442 1250 485113192 485113219
    0x20d061409191e0c0e3c0c0d090b0a090318030b07050c1f05092407051c0e071a03010f0509040f06050a05040b01050315040b0901060305150105030c 65
    0x700042c0f642012009a0106a242ca40f410012500c449641140c2c41559841c0140300320042c9425203d16600c5252155960758440351004440c0402010b0a04e140032100d400810340d01401c5602800c50076410b40000507860b2460745070b00698100940381e4440880ea0303002c1e0581031542c451814110034411510201d0040d1969582e45031580008242c60104400462018031081090140c0400368181c1c480f822401001211200020901900c0e240c030103100b04000d125074504110380c909840e0040c0d600700034490390303903d4050b100c42d8081413407000004500089807106188512070050301e040d0703c81c003e020403410116105003a400f0046022043c0c1d50034401000310016600310542515015034001d002c5403030300c0c5800e00c280507188000409190070306003000690301c40380d44224412401203d4201031641c1c3d49041c103803102c1180c00455001d200800010700032400000005c2c0d0031443c40d00001480d1550703a00c5a600f05041b000f000e2503502034243c01004145800c1000c1d5440d0001110001c0a400d41e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 485115692 1250 485114442 485114453
    0xf0c0510020d030e070b04080d27150504051009260a020d020303090d03120c0306050d1412040b13080115031407050604080604030207150f0804020d06140919 69
    0xb0412a1002010b8541801400b00e44003400a00001c4c2004c07494680c990b91101c483c41e0301c1e0b00b600c1461900240859041d402d54a030792000307244108440200e10303c00c00742040700e002200060b0403011000e01c2410800000c442d114003881d1000307a503079940c4103500681860106a044041420040545003914002100d11036010500c005200e40c1140c0c400c00484035803012900718080d5192450340110b03d08000c1e818143c000c00e006540c1c20480c3c204100b0520551425000c640303140c09200c1e008109a512003000803052440300721004828001c40c0d4001100000110b40c59105030084810030300d01007031031400004504020009030425031700074040080c0c50070b00d02000920500c0060105001d804644100c4101800302d9006040043d00307090f5130b2602d0305403803540c40300e00f07075011401445581c1000883c1010300c031f07036810b1110284d91030b201c981d8000d58046414002c064410b0380e224040305c01c95000111f0620400251410b050582da50514181e00e10504000010200c6400c9001c0320900400041c2d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 485116942 1250 485115692 485115703
    0x601030606020d110a1a1f03080f0c0a05060c0c01150803070210031e0605120d14070302011e0e0d0c051216050a03020106090606030b091317070f0c051002 68
    0x10554038080c1000b00c8130050040c60700382c0c0d5010140582c1901e0042c0e03544000b00c821924840c00b5456440da809043d17640e0301560484c01c130b22010b44206010305c4580300a4844000400390350548104807030320390406885080c10a0b0041e600454040b10000c1c03104001c16081c0550500b0500c00030302a403000f85448030264403131181da040240300b02c02400d51440c1c1e01c0d000368001280011503086c59081c48041c203ca11005002038006c4901c550803030000b4580481c8009000001c01d6100e40e207002c1301c0070310f84806a0281d000204214155500c039071000c202501400b40b501e40c03155030b1640c045400d81d000c10078142818420041c041c2040400e9a6150204400060000e00680306030031503a51070707100104481003041041c000410700d003d0061860103059054010505403481018100400c640d40c07942074044504910086030081d20050003e1001081c440c0b11040d5503006801e41780200f421100c0d0080030354400b042c200e50241042d010b56050000c4000b62102900095071500d6824141c0072010355500c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 485118192 1250 485116942 485116963
    0x91b1f0f0c0f12030608010b010903140304090f0b1002030a020a0f11060c0106090b0f2b02120d03060b03090a02090c13090518070e07031107080408060f060103060602 73
    0x4a921003811561520540618a4654000e03601c5211144103140030070520741c03020350410009080c894040303130101c0c043c483e2000c9040d058640c2c45a1525564800903445120b150b518017600080c00300240c02d00640c0101c072402c94a10b1000500e401c100b104000001604401c3d000441d8001c0c8180308021b500000c442c403442e40c001d482034110b01d480b80703401d02c02d003e041d004081e0440c0d404684031080d50015040b9000340c1310040c005208a0300c101d400c0c41494211040c040360f0008204001305045550a03000300d40101d45921200c9481a40740c02241026464000119040d440703c10038115150307042c0300c1c60b8090132041c140d880c0b4505004940c0f030340d500a840c0010b4070603484132020503114661601112a8118480c2c0940c1c00b9681c0c51000c04024041216501c01c80d6000c02180c0c500c1d4030340400c40340e054581044045846441751a000c4009180444420842079410450140851000c101800c01041d88000034996450413840060940c2c030040c04840c181400c01909020040d008540d03070011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 485119442 1250 485118192 485118197
    0x6040b0a0225050f0c010206090a0b0c280311030106091403100c0203120609010509242115090d031802060703020d140f0d09030201090b091b1f 63
    0x1580c03100d000390248007804810600c0e502e406050b911040000104004540101c18016109080c40050069884170f008a600e2000754100248030f00000c1c10101d2500c1e003156040c890746051a60402c40400140300c200c1c030341c40340c480782015444ca89a03450300a4070301d01a0306600440c110b501d00800a801c3c0c050034001d1012400412040d55681d4900300032070802c10502c036106001c01c01c2c1402010b9141d030b0014036104803500d0004001502414096021812580c001d890f007145580c5410040400401c1c515240500c00039844c0500340c6580c1c0e00070100c01101d46003054003006141890072600d070000c1030032144092130b40142040031000010540320142c400b01d007800300e506c80c02080179001c40114020000d500203c003090301070505174001a4129141c0c100c0d1640071554881303008503502401160b0a0321242c410420019000020750381022044511900020420f03141503030307604020704001c454441b802e0b8402100110244e030070000d0510303641c00548103441c2980031544810310500c1020000f03403d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 485120692 1250 485119442 485119447
    0x7050702090a060e1302061c1d0106080a02010f18090c080f060f0609030115080106080105130b010311010509040905010e070b0405010806090709081e0c06090916032301150206040b0a02 81
    0x10b41d150401101c02d81c08c8d40501e010f46040076004960010138203400ca21307000000c011001307581345005100710401e5400ca5402015500d038181c7c011a24100c06094520401803404111110b49000b9288800a01940f040c0800d407801c17689801844180001d240b0351008010780300340700d12900c0d070380d119442815041c0c4550742c0d00d90b031900109014103003040301c18019101819001941070019031040081d5110710000388026100c5000318800e000060720060006503140004000051a1181e0345403194018103000b801d03d030140c070004040300c800760015034280e51241e48039114280300340034071005440084c0e0004d05081c2070a000034584000201400d000c1c1c07800b032003c10342c0640034101c4240200003001c2210b0440c0d403056070f0110000f20401680781140703e1104082803034035020080c0c0b60321640240549115659114180c0d41400300000781e0000d141c1c2ea03c110100903528900b511500910130740507103c803549032051510340701c2c00001c4000c04540080b0144000610366880c1d864012001740005138 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 485121942 1250 485120692 485120731
    0x3050c030711030f1305150f0d0b0f04050a0902101404030624081506090f04080706090b15030c090f01170f07060f230307050c07050907050702090a060e 67
    0xa10794484c40000300400f41001c504001c05850300c201a80580b201510706038805910080305070811300444481d0303043c001d4140030340907010440e6404500780036001005031f400802080003180840300113440d00700409803149038000550612100c00c004144203854005600c010010148409008500005004a4468210f614446000e0003404d003410300a182c84209103a4441d0701546c1c52045a0345214008680d5002900354585801311900c100c841001c3c038002a51269105c0c450390340710f2041219000d0361a2043e0020514403600d2511820310f1600e040100145001010300c0c100e0702c2895075125031507400c02c201100202a203203e04440e030301c01007080c1204030541030034104408160540c2e402c0c4609040090201ea102c0e0b05c1c01840c55940e02c3c0d07032031240080090b40800803580700c16008100020008901000c0c801d000826480c050f0400750348002d511040043d200201c00da401340700250003c1460400e500d8014a2940c1142e0700c280100207c61604d00981804070b4001c0540a41c440f00183c1c0a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 485123192 1250 485121942 485121977
    0x120a02131805060c0406020f0c0604061b0b100503010605120a0f03110f030a111902060d0213170607020d020a03180819050d020109170702060405091e060103050c0307 73
    0x1281c4039074030105980c120f107401120040150402c0c441c440c01446181e00c64000080c003c600c0c52040071018203036501c0c180c200721b8240c4600002840c0c400d410ba0300422107401060750b4407403450185682c0034000d0b0680b40350000b01400d407030351900224411403804136800c0e0852400200c2c82c9010b98400810070030107005007410b48078901d2000280c0c0b154040d620b400703400c203640403000307000921300e6885031105038494000c030b43d40c0ca5455003a0074001885807510400580f5101e00545903001c8040c90161600c2c101300500310b0707195071a0780840041044c21070800104c1009200c01e03030344401544002c22034a45889030080d84d401e80b21801030140082901d02904001d05050040054603049080314000703d180b0303018a900140001e400e0b200c43c01058200e20059106000b04038085400c000c0c407a42c075640924400c3c0b12548003401c100e80c4031030100b10010319a101da25440b03100340c66080c8001c0302e581c190010010f04510041c50581014640810800c00c41a0181540d0700011140b801811051001100303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 485124442 1250 485123192 485123231
    0x415031205040302030f01230105031e031e03220803010e06041103040b070f14040e091c21050103020603040f0312061514030609010312020c0a14120a0213 68
    0xa50140904070000b506c2010541010007880ca41810100201031000100e800030807081c000d26501d90080e07030900310700708204c00501c0c40320120001600d191094841c81110f20341c0c548100e41c03000d4500032007042411120187e145110309914200e440308201c443d6100e080c28881401002030b00101c12010075515201d66100030040c049a140b4182e481c04d00b42032500f80a0421074407800012007402c0315000c1588141e45890b61070413551501400c045c1840c0000b6800c11006000c980c5501c5684160071341c1000c1240c00000c40768190b20750043c465402d22580200da80c02080d005103140c10480100300580368082140d42c1315800c8070450140c0c900718901140e040c0d601031142c0d05290b04081000c1103040303010003058a0000750780c840c82034413804090a0394042c00300715882c0c0c1c2d01100070f600400115140114400d0720581910603140b200c0410400954028043e03002000239050384010042c6600700018140d010308074130002042e030342860754001050704040341c01d10342c511511860f4018004058141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 485125692 1250 485124442 485124449
    0xf03030c151109030c010e1e011403100f1203090317070b01150f0305040c0e0414030409090c060806150f120c0c190b040f0312150302030705041503120504 68
    0x20070b01002c0d052405000303140e00300001c554401c0c0201048a602580030360380034014030102420442c0c00700000c4e106044c0011029903510305100d1024650351810f030409006603c650b400040c500000c2d803c242d0b0120005600b90056011440c00090304c2c008643c21008080407250f100307400244950100c0c00c0780c00d4074059010010040d4000c00e00114aa5560442c4214802006d81d03800001c142140f03001c8043d07a030240c1d00030341880c101081c140108000400c0c06a4498014100c00c41c00003288806a0b01e95440390340310316441ca075a141c011b000c22520720f034680018481407810b0742007824900d0000b0305440315180800c00300d407000114982071074401c00940d01e40c080010090500c92411903a90640742d07009841610060140c400220346180d0440804600c05401484128455860782c0c3d400c9440b100701102902480000c402c0c0400031301560291051000303030150307140700803481c601c1030514040d29500020720450605040481994605a0240841f5084500e02112802e0001d058440d0b2007280c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 485126942 1250 485125692 485125733
    0x91f020d05040b07230318042007080d020c0709050709091e0519060303170115082d09030a0807020106181d120309070f050f010305100b0c0f0601050a0f03030c 70
    0x1c2e41015220410544500a040645051001c03802c810b0f0701d1190100c1b0688020b99406042c0400404180b00c8bc0140080c059000801860b00c60303211129840e100960b0b01040b00682c455081100155028129030001c2c0146d210501c01c5100e071107072040d100c04040000c5102e9030303605c0d8005103071841a1041e07900000045da10400c0515207a0030010056100d24801d078210b0599034000084000c0b0103031a100c1842c0155858104903101e0115001d6814442030510f059502e0b10100741944140e902071080c0034a924500556a95008402c050a40c440c01401402035904d0303d4000c00000501184060748100907000004491400d0b86040d4020b12485200301170f680305d03014418803c160710100450040c00800102c8581390341d40d41c03400d2516a12801003540000e410b29105c0c41c1da501941255800c4840aa28101002c1d15403002c108660000d105868190740015104c00c5080c005210480c0901026900100203d041000302c6818042d94440201080142401c08042c40f1a5203402032403102c054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 485128192 1250 485126942 485126947
    0x1516020a0c060215060604030f02011d220c0801050a061206090216020a140a06030b040e0109051f1a090903160804050f0108040201140a05091f020d05040b072303 71
    0x1440c000350795041652044412081c4c0001180c080e2070700030159001c4a90042c04100c202e1110f60044525a08400c1e0f56441b2a08444426005a80c1d4004822002c0000e0408400140d00461020300765000610740200b070040b2040140080d440b60070b110815107420f4149100d010001920744001400301340d019494051000c0740c420310491040031101c007064003c440303810280703884200408015440340d9a09610280c0c18004000081c0690440150354a005000044884904a445094030a40c44086170030390805030359954051000318101c0b0f58848486020041c858001a03000700088140b58154855248003000943c000001c10844a02c3c560350301001203400100c1c50002400d8010f40078052140302c0b5060101c0c40d0b9485050b00c2485240c0581d80c014a40b81c07052600d010943c40000b41408111042003501d0003900d4120382e891031001900603102003800fa000000342400c0248030703c0700402008000820069544c00180c03411701c0e401420462a480f480508040491480c080000213400003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 485129442 1250 485128192 485128199
    0x90c03190201111626030d0b0a0803160b0907031b0501030f0c08063606090606031e150d03080906281109090f0106111516020a0c 57
    0x12031601000c01d10070b8030381203000c203180c00712542c0310f030095441000d0142610a0410480c2d00781d24010414115000968031500c0c40b002c1700900715840300c940c0c41080380e11800710b0403c9061a1209100405a5602075428080003590a0703101d0304034003402401c4400140c0c0400c032110014401c14000319071140d150820000c8900d0702b0504025680302d5980842e03d03200c110001c11045010f06050410b807030b5102c25850342c0d417004201d44060400500300c040303039400485181303032070001180b44008000c55819121500d02401001248038000306a28042e1005000340720300f801c0308280050180e4040b0744040290303502c02c00071a01c945140c16456522481d1010084149504220b840d80510525810355226a0342c40c1100540210312080c400050b800303400805000700026800a41500e0042150300e00d070145940000d050702105039000c00880c2942001040015041b003e20942d111102018100c3d1401d4012030703010140703000340b20600c0e040b0302c00c070080036040c0309210140180f0b40c0101d40000303294a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 485130692 1250 485129442 485129473
    0x81b010c020f010513020a0303051605030c030c10090f0b040807050102030c1b070e011a1201150207080a030c0803071b050309120c030706050f07080c0d030c0c0b04020405090c03 78
    0x1d003000e280190f51070100400e4541c0d1055a1003001181c02800c003046d00d0b803031075600700c41030703031080d84200300f009001c80300040001c1c2c080c4010071010080400554a03840d1449410b400d042c00c00e050300f4507e510b0002c01e00c0000e800c1051101505411050103002d9590301d00f840c2c6094410b000004045510020410005950140c083c0141080c0c1d0008c0808006c07101d4803141e5601807074050801c2d045401001000740c0a590340c00390030341e00d074034228190408060000301c003014803003a00008212155070180a525690400591000301120801002c0c81541900c001e804042c0861000c0d10042c400400282594028000c0089202c0c4c00f82d012910b08100c0d003000e40d1240c1000e0302e114407540070744c00c5400c8031080006214040800060140c60b8481c503195091781e41ea400780110103503840b82404080d002c2034014002c1c00364441311a016000c541d56020000b41107881d501c03001810b12040000b08008541c10100c5d0ba9845907040c1c500260baa00c075051864a0844035940c0c8641c548a5280210419030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 485131942 1250 485130692 485130703
    0x151219030905030d08060613050411041d070801030305211005030f031c09020a03081308010c0c03020c041e1805060f0c180a1701141005010507081b010c02 68
    0x90107503403000352180d103500416448841d507000742c200084100000c00c201d840d100d0300070070a440c281000c03c100d003940c03140840d0661f10910542c01013141c010408011451803450344100020000c1d29040b403610b0007180150103c3c1041c0400f50070010b01081d001c0c00380b102c001401445016920f804802440c0032412510140c0c480d004403070107802049402109100c0002c142c0d036008804810514014202c2d00c26200109180705060b41d010b100d6201c00404a1002d0000307240c1c000b10785116010950600c0d8285081d1001000031008210300c4030342010200c2c0c3c2c0440c9901460400300c4d40498000c0c59040c030300054502512a414a4038a08004002c0c148041071101113003500c2041039820942d0703980022a01000c044072081d5994100700003121710750600d110b80540c4074100522101d6101d80f036111003442d0621060551210341c0d0750780d140c001c0b1101803068460b4042c038000301c040c5109050400092540c02005002494000041540d0b80c01030102e11740380c02c010501000800100e6402e41000359280c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 485133192 1250 485131942 485131993
    0x7230402090306071112040e10170a140304030b0c070c0503060f060d030e040204090b01020f01020a1b081204060515090c0d0c11010f05270309090603030c0a030315060c0b1512 77
    0x36009c1500001d11050101510010149214043d04039010b039501c1d40940080d2000d81c113926808100700200004075a152840d0007030894105003922004985002070308143c40c0e4028500c240d03c030f00200315461044151381580302c1010355000032820010314082c0c80d1424103081d422f078042d0000c01c0110b0310b401c1c5940101c240081c240e0884401c40000701c1031500700e1284940c0e4000240c0c20050341c07500d8517030107450224000d100303000e8203180c100100401050000283e504591082c0c4440600c64048406c0c11700041e1190110303000180c908249110401728411043e907248180d8840000002c2d9500444120708001041e034001d00a0501030341d240c3c401005c00b100ca83e40080c0362104070700381c01000c944601b1000f00c0c00100540c6005002010010011001000c150341440304000c807801407102808882d829505c01c0d2008580d04d41031304810221040c940d080141041a52407001020640501c01160000300c0302666a502e8249000400c040e080c0e514070900b802d110ba00c4050740c800524561a40302c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 485134442 1250 485133192 485133211
    0x3120904230109020f071a0615121f080a080309060f07140f0d09110307150e0d0f051b01121407080c090307230402090306071112040e 59
    0x4001c008061050884205000720303645003607910050100716078603802422510410800c131814000b00f03948030007000c1c1c140c046404441842109100c0d1604144002e00001d1844045003810700e1190914000f440d84014500e20000d0318407000c00001a15040c40700b4043e00601c03065590913155401d0000907640252110f407514890b10300011484c20340000316500610700c0d5540c202d0044106000294150084205072645134410080d6680a40d090311604540d1885800c40c0322041703104408150809505038842a0042082a1400c600b51382c8203030442c848030000c661a414550795401c045060200b1410000c0403841050502c01840780b00103035204684600340d803400c181e02c02822290f000ea402000d1100d00511342c0300c011400ca580691440daa00541400b9154101800c1c9800280f4114080e44100c000b01c4500c2c2450b0b28806003525031002124040e60150b242810f040007080ea2004001d04001c00c0286081c07440c0030398070040c824801d07100010080117445a4548148195646055594048 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 485135692 1250 485134442 485134451
    0x6040b093003090315040b010603020c03250c05030102090a0b030411030a030908010501082a120d09061701030f0b0405030d05040c142409060d06030c051305060607020f060903120904 80
    0x4c5d940d8540b09500d1144d5400542000d003640b800202360701030340120035203140e9400f0901c1102c004016190f800d0141a21144061105140905002005200d6604103038000e0340108404011900c0320081401265550640544d407075517107080100110070f0b0041455414010060741c8814141c3c01103a40042c2d50941008000c266650f2000691f100301809401000240c0c42c2e2070740e261170200314222103000710060702c00032401076000031039401e0009008803000410380030384c07060004603440207a5030054004600f0400095065490b103441c6980c00e50001001465032200080402c0300601c10744c1e040d00070a40d4240724504003031810f05001066801000070001418038481c10303619040f01c0c1d0b00062507402818400f0f44842c040c040c022540002c100340e4000e041006100400322152107450015802100c2c040c100d541000d04002c5081032000445100d10b0404d000c0c41020b80d51101190002ca1f411a500030803451540c0100c0c0d020b005030107003160305008100808000c07080e0000108541c00c1d04640420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 485136942 1250 485135692 485135713
    0x50109050402120a020d120e0a090507110a051c090e0405011a0603060d0b0919050c150406090612230708071805060307030618060f0506040b0930030903 67
    0x180c0d1388640030320103540304154004540c04038180004100c05915a4030f4030402c80001c480c04201d0414a6a202102560b500c000300101198803501c00407017170401001070500c90143e0303200c80e0359035800d0410b01080c6e10f5001015804c200e01800d01080141100850042d041c502400c0c461b0003451144e18060300d6032855900750103945000d41c2140d200d494000c100c80c042c00346946803107500c080010080e203418031070f4805c40c0d0004841c086201c6095417180d80188510070f2090305003d00203043c110640200001400140300035134111800348240e54482c0741805000129000c04809048003c0c01c03603d1000c480840b449200b03400100080c400c03100d64480041c941c455034001c40b20020140041c070305074000e014050047d4500b020080d0b40204041c0707800300f9815200c42d010140814503280042903565161001c0040780580c404410050401720741c05410249400e4070076841388203c0c5c0d10244506509c144c0340350140c8071040310301c81641f034039200040390a40350600e00c0d0341c80d88140c0c0281c0c424801e086000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 485138192 1250 485136942 485136979
    0xc0f0f0705040c05030a0b03010621020a0f0b0a05130b0a080f010f14090402040b0901121b0f0905060d150902010e0a0b1603020a1709040c0e09061c06050109050402 72
    0x40d041c6580c65a11306282d0b503103880e0300341d00616081c03041a47c15500c0d28070000f004100700410203071403803007200c6003294101984100100703266290321810242e0400c1c0000c01c030f03d54000f0141c0d241d04d0070604103140d5801c10b41c10082d6450143d03410080ca2840b0202e21076030b03111741c4609000d2050010718015a8182d895001c50484410f1358490b180e07004081da401645142020865030303801a10207400030030340b000791000050094000f40c014005030514052100148a014088101103542da8140c0c1113070203003482c00c100c2c1c0080d040d009405402d610350001c602152600c132901560b40750802003451105a060010201519000b1416070000307619420a07a09840c2c100d5480c01140d00c0c1810407807800c504454400d840729480c8d40d0540035801144250303400b082c1c145020103d0b2140400c0200da40e180200200f00849402401c88800c000c610402d02030f2649035a800b40d07030040000c66012203a481c40c80011704007620320000c003c0a20781031070300005012480303403c6540034620859030a40040101c0808 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 485139442 1250 485138192 485138201
    0x20606010804020307050d03030b0d0503300604180501090b1008031603082503090b09010203090d1404090f02181005030106050d060909050a021309020307051002030c0f0f070504 78
    0x380d450b410901040050f450b117207c03680a80c5120741401704180b214000003c14441001c40b041d10030303810008091640d84d101114450f9240b04000301410024034504240c0d4101c0401001daa0045075243c030310300d805000c0e40c0300486c45243c1c414024031401070f08d03240075044000c040c0c40088052141420100b8240c1c0080180c1d1244501a48003d11690f01070b101140c4002c40608801190441d0985102005a10304035130b10040a4548020401068500c4c0c090791480c0010401550380e441441407019000700460400d02c0d0040c00d2601c0c200c28808a5040781042c4580d90000140d14500741c400071141c2c2840d005092070341c0035143d16004525210742070103031861100b220140090380400040c8205400b590140c07801c4180440000380f500d85840c42c02c0c0417501e4040d02602c20341c0c00001c0580440c548000d01e04030580454405004200130790780426079500c018007502c1d21850340030766500402482041901d92054030042149c11120759002c80b141c5910a41d60352040a02640e080451746040c98001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 485140692 1250 485139442 485139451
    0x30b030703081801090b0f270d0311030f040f0e0721090f060f09141b090402040905061315020306010804080a030605030610050405012c1b0304080a0206060108 70
    0x481c03c1c6040303804024200340710004611541401a031100101c0c42e82c100d04003905401c841e00041642c1c1e011800e00c40b45401201580c807865089400441150316114142c00940e0301c1d038107042289020003510941402c1d802841d802c0c1c6c04841000c24001111a101aa0f0340f003124864156400f8645030190203d41001c001000296007420360414400c461030f40f90b1040c0e407640c7c0540654000003856907542001d8850710b07c00d140c8103d40703c440030014407aa44040410342400c0c00000c0c08000529031100585070900f0741441d00c142e0400000070195120768000040c002d5001050754035901d001c941d00455040500270a440c101e0b0002410b0450b40b0141c401c490007418140c41c0c00d40a556644d5940809610800041c02056101c0c8000180c03500c0400400d40141761910910000c1e03824a4148000c6a1050b84400780c11070313440424601105410624480700701d10000c00301c040396038503180015041082144103e129000100300414040801d0107825002c1c0c03e5404ea07881602da150044906040545 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 485141942 1250 485140692 485140703
    0x15120a14120406110a060207080316020a031209080702060309010e1e07150c061505010311120c03090a0b160e040506090105090709170c03070503210d02040e07020a0201030b030703 79
    0x344912070040000b141d101301050220784d9402d90f9a9924810380e0840441101c0340749020081c401201402174120084080c1403000b0185c00c2c580d900c00030103c00705072005034145580c0300d0b101303014440c5901c110380c1c007603401405081d40c81c1044038400d0300a20300b40340b032554036014021140203421760900b80089404800002400010304100070f0280a4025910304028015283c10110000b40c0500070108580440e00c403540e4000d15140025058488003480c400403c40c0400c0f01c4007100d80003a08094010445440341030b241d03910b294016180040345180501818100b008006400b074103004410805d00316236032514103044018042c0000d40300c1c1078650690102440740140040c0c10201c8899500280c40d00e0100d090661b10041e2200201142c24514459084a1510481410104060390003400150018a9684251441503001c090451422403540d0750000d0702241414507901a20060200288400f00c94200fa4178065590500b50390100e000c01c0c1880003601c2e542c640852501c088070f4110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 485143192 1250 485141942 485141947
    0x60310030206030c070506040f0c0506040612050403050915041406070201020d0e010210240815040f11130b030106090615031d0703050a03020c0f0a0501050315120a1412 74
    0x507400c21036683c00041064064080c20310000003c1038042000d18000c3c0e02900d80d951821f03c0e581412410300384140c01c1203029103030410041042e079030720210103020240da0010000c0d0355251407604954a03c640459039611190140441d1520110a0002c0c000c444948526032140300a003414840c3c0350040c031074080d0240e04041d0110032424001c114061809605205650a203124810039004440d042000c410814280a01c50150b20071100e840c100504402001890f040c4070444134101c82d40f1000780001e1010f00030003c11002c2000341c95200354100c1004124a201c0e03e0820b540714018007401103050b1080d803e143c00014120540d00c50320041d81c8681880c032441910304074007a00542880440c1c102e0021401c040320720898014060200070710b01c1440070f407844084908000f450010001c8500380314182ea50002c0b200741c1e6420301b10008441d82800c10b00d460f9078803070401800c5086003d841a410034203a605040a1000105800ca0094406c1c407801c44803004200909a13101e842c444002d501e00c408 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 485144442 1250 485143192 485143199
    0xb0904020a030f0203070e040506040630080f0a0e0109050a050f03120313140d09062001090533041103070b1c0e0f100b010c020307030c06030b060310 66
    0x29400810141e26182008030300030441107580381c00c0340c2c011070303000c0d00161000c040c150f0381b460f050003400e030000401c0350b052050341d003070032504d90005079181e00450809042c0c94048032072003010071040d54100d400264698449100400c110304c19402041c4003030005840200c80401c5600500c41e02066810190083d031065081030148941581c0084d00540d0504c1140228410404070100440c80b40c0c5c2c680398840030010781458a04825040d00d952141181c01142c03108a81d01c0c0d00c00c104e20b0031100c1c0f520700099072030380021200c0c8204485007440c0a06500b0312414100707000e8005660100080000c80000504905c00c0b40c6903081a42281401c090503000c1010501084504802010204004041c0c50030127a54031a00d100305d41c0052072551500494036048108400b0310b05c2410803100b41d907009003004000700642c450700c44080c0d00904050070758496217061541d12038115007120b942c4c00381c2210802c3c0e48038180000300058900c074107000641810040081d03400d1500c1501c0c084d0b41d0860b500d05020b400d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 485145692 1250 485144442 485144449
    0x2010e0705040f02040506030c04050901120302060f06011b0b27120f21041205030105060a0c0c05120303010e0a09030c0f020301291008151e040504080418060b09 71
    0xf032420380701550a809000110703a558a24005501039171010885070742c0c41e80b50106100c00711505034015000f03505410321490100390003143c0d0b141c4c01680110310286507900c500050343c800d80c4a01b049580c22010807041d204002c00e821009024025080e42c0c42ca048600c8003607190750041000c4059003a0b0001d82c0951180301081005c0c2207500d4000d4801d5041000d0b00c85d5000066030304400ba0740c2400da610301440306001c0e2880500e026001c1c01d261240c035545c100400300c0d050380b082d403802504010814401c40240034003221a400030742402040c0380c0381c8002240c007055aa42003802010190311404002c10f000c80158441c1010003580350302c4a004c0c9210a03240e0303585842c00880c0583c1c140d504c805c0c1607060520016030b080903088013510300c5100861184140000c4101d441c02c000207000c002c2007800071041e0307014045904d41c40c0844503803840d070030484a41c01808103109002500300f81060305110400542e003003d00181d0b4100304a80080070400c03260041910841d10510185542c00c0003500b13202d09 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 485146942 1250 485145692 485145701
    0x70203061005150304080c0d020615040c050f0c3d053315220608010b31060813030504090e010209120606010e04090c12050a3002010e070504 62
    0x40c0198001b07420010f40068850402400254450050b009281000000300444c5400d01c404c00c815a001c21800f041084090407500c034261200280301c1c004520308241e04010410f050100b9030b506c5e001e44042100064105e1084440c80303c0c6404c1d50300e0700e020145003902502c201441160107140c3c0300c040b40446102442c5640000c0311001020000001c81040c6865600100d00ba20040754001562100310716400e91550700c00a02d503403961070310b521041183d0341e80416203905494402200c503588505681451302494450700540000d02d07040c0b050702241007200c0e2400360481d8240c1e100c5940700d030343c2c24124286442104000402145040c0424464031281d68009000c0c0c250000005241c070b0520800520502908006024103901450030030805503800030410407045001d0701c0602004041360303900d02e44640c450040d03d0030180c1100305981404420414420391542041c1c40510b03001c01c10380c00703404c07585184403600007201c02c01c2d29081410344144142c2e443c0303908400180c4540e900b803008000151 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 485148192 1250 485146942 485146951
    0x3040c0522060303020a060e0f0d050c012c010e03030c0a0806010c24110408030d02091908031e0304020306060d02130c03060e0703021c27080702030610051503 70
    0xa8046641060510640d80720300b102440c002e4004000440c818542902920f40c0103603040c0590700a41c4d98060508000140c0d001c41510f40d003001034a600c58841803900400c1074030a100000c98035440c0d00340c050031014140d4403204014500034060512a141001c1d52440140c505004000041003c4917400d031181c01c01030303000023051400c045030b00459281e0441e0011a40c00072000b10172030740e900144048040c490181004a4a41c402341450320f003c040a0b1a801080880a82c0e20780000e620546941e46205109417100d1103590348144584504000d60703030303801401400310080d0029402c560441c000e801600d100700e0b8000c000308069600e1009000717201c50100c00482e0842c8807a82c80004a0311680a121402040f9940001d086440e149520340010005818030060620401502c0e0001c040d0741c0e40c0720b009285a950100e22440c1050007084072031516080303160124100600c0c07408024020004040550080381142c9070340d1106207546001c25843c0c454554012441b24000c2c2d4500d070b408001d903901 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 485149442 1250 485148192 485148229
    0x4090b01090522030201021c05060307060c08040e100905070504030c15091802070b1b12070216090204080607112109042a03020f091c0c090518010203040c05 69
    0x83c3e0a06008680f4400114411409070b500030a080003010402d00c09111001c03403070b07041802141003801c0440d0f21a020b41c0900810010740e414050144001c8004450083c4031640e030800151030001003240c2911440e024040500b414080441c2520740f040e826a4140c03500002c030159031602c0c00c3c50852445984041e01000d0140800c000141c0c0c080d5070310307031003a034085050015a030f62a080c07406031406d07600140240c0d00d0f0034403c5211200052a41c003a25003002c10f000c0ba8040a0b12844000d91a003808650b00d083c020107401c0d80419144c0132600600100c41c000f40460396243c450b08010364001d10006000b0745103500181c80040301000002f00e070070322403100145140c0f5100288010406903440740e82e40c480c0c926148258440c205044041d4402b010740103150440c01d04013030031340c401c0c42071081003013483c0f180704942c151740e28250060000d0272600d54800f492030f003c1f40c0c1e43c20f15400608002c540c00c07820b49407402100b11201c0d41c103000f202c2c1b080d540301d00b088a4081c1064208020050764a80d1040b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 485150692 1250 485149442 485149471
    0x3010e0a1103010b071103300c030a0c0c0807090f060e0403020c1c020607080406020d020d020d2006150102010e0706080103021e10020303060f100c02090612070f0305070504090b010905 81
    0x1b1135031400d1003010f00140088035007c2000d21041401c1900080106c40c9444600301000500130b819001310584542400c145420141c251542c1881c489204c02c0303400c003031400d010303100300040c2030013050340550791035401044280417a80d5211200e0b03c03250001c0303030041e0150300107400300c060506d0074401c00002c0001c000c0c000241c00043e600401d0481e040010121100304000034207200158040004107080c9843e84000c10810301d040100a4803098803102e03044c103100f19001104150080000024040d01c5043c040703e1107071803d5260f800401c04130400090155203041c055082801020943e20292001901c4190f4581d10759030a0040c2600d00780059602d100c0500d03101c1109a0325118500c07000c0505600441d11790800b035007080300348205942c14170301c1007242c070b10100e1050b901314191220301038044804600582d0b900c0040f400c0b181d0541c242003a00c3c054288045018403240c06101c0659004004403401c9540b41d401380012503d45c4200541007840ca000104120380c101c1d000319910840d041505503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 485151942 1250 485150692 485150723
    0xb06121e010b03071e0b090409120806011d15030c0409110a030b09130809040e072907110d08090604060f12050c0a0c21020303010e0a1103010b07 64
    0x4441142421800169442d000300102e185420031030200076040308109103488110700203030440313031022038030424080c070001003000c2c1c0841d95168448168181c01144e01c078804503400308020803d100c103d5000740812003080d10740102d1102c44000080c020805020306070b1345003850115950740e4100501c6500c00d110100004030f84500a4010300500b80a903102d6107803100491900941a00c1400c501940140100c5c41008441882549116004d5401020750355442c071908c0d02090280c4080d1560803440d20603540300140f2007400110004003030711828605203070001300f8060b40310035100d500c0e8040c10114070824003052034582052504480c038410a26140307810040400700d16030f6007255120101040710310320003c0c400e42d0400203110075140c61400400a03440c048451142d64040c0c080c02078104480065954100441620388100711495191244241241c20300c001750317603178824080c022603d8080c0001c04c03212481405082c10200100b84a40e05503802d0800550301500000800e8a2540c1f80c41c0700c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 485153192 1250 485151942 485151973
    0x1030308430f02030c03071202030909011410020105062110050c0d0b040e070308090d08040b091c050c090a09150917040602030d020c0f060901050a06060c0b0612 71
    0x1207180004401610040490201014080c00e002140d40c205640040001200c08140442100c2150fa0701103030480ea000a0304404a29500620004039044504100089802d0340300b101c10f660104030032100f200300c04090740800c9090354400d8600c103802c0f1502d4912042c103580801445e0411301154400c459a1006200c1a02c0540320151802008444002148418444240174124103d202520706100040b40c8901e495901d004030300c400b90900d000455090980c0d0b6403268002c60960b0000c0000c2c2d122a2500c85110095111902142c03156404480080c5410580e0320175844a580040c00b8040c42400c070b00074810544001498142069981d0381d418000408501c5c9140e05086040070004608200e8030300921404d80301e041c1643c4020302403200300300981e800811515400b1600c00302507250b2002148440c500108950880118003c4030b017040240c2605500c503034811500020b040c0121960342c0300c162202080e14502801951804001034014140014841442c00e0307480100c50320903141c42a072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 485154442 1250 485153192 485153281
    0x1b0d02010309020910030512030906070807020718020d050114090115030b090406050f010504050c09012003040e15040207120315050301050114011416021c020303181801030308 77
    0x14124541c400703040c01406020802d9504c882c8c82050090f1540c1000124150b554500130000010808003100007a40c0074400d00c40320780103000301c00701192124694070300440a0740018040d81c0445103071a00010f030445200b030b065820b00c0710141103e9a1a420404001043d01007451498180754070b8148000f030548400300388500c50b50244100190070b04025a14003440749060344224800d5083c0001d110f040f0709894100c0b600280300f405c2c401c8803080300100e85109404080000d000602001c9000a2500070001e8980d22544000130140100583d100c100310407401040e8000d00f8038034003c01100f801c140298032003801c0f0840b120a414181d03941300d00003401e440c8240c112417815185000044036958029082030b04c404118182f448c1018981e403907074001c000e0b0410010384100c0c200044040395025520f074000d0303600d40203001e6983c1d030341001e032954031984110300c070003802a1441d00c5c24207d060000c804da07034180d9a159a800e50380c1d0b00e580c90340b0f02000c0703103104080c2d0010816100450311412013825 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 485155692 1250 485154442 485154451
    0x15060315020c010518030a0f020f0703050c0a06020304060206010306020304060b120102041e05030c060a050f040e060a1202090403051b10150f030b0703230a0603050f1b0d020103090209 81
    0x5607807903030b41c8a0002c1c252640980b20002c0000c0700704c0c03c48500a004020780f46580903c1c6006400c0c04110715089251810300d405a0500e40030b264004000c0c02000b2070f4100a0030001e542040a1300d40ea40c034200c2c0c0c4d0b84a503201d0701d00147c1001c401070002034081e400550300607018400100b801c03060400001c5451107101c160b034040b694001420000d0040f507240079484030315000700c58000b00780703854040b903180d0815a00072841032200041140c115070040f82610b1202d100c410405465a4403002441c4200c20107490030342c45013400402c00101411000788003c1095030180603032045440c0daa506549903003000c40c103e400140c102c1024185000b0401510654425007000031840306c003403015000510030142c0045807100004a070500125070000c810303a03003201640c074001070711031030070001d8a07141303481c28600f0200c012481007031101c0d8030026000b40042ea40900c00f07132070301a1650f45503903a4841400380c000441d440c1d00341543d00145400383d895402c0500606010030800a16400260007840488 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 485156942 1250 485155692 485155733
    0x507060c020d02061515030901091e150606021c0e1009170a172808040b10060f120f051e0f01060c060b0409080a09092007150603 57
    0x415403055041040d40c5d0425040740034039001010361408100200315130710700c0c008543d400001040e02e205003503029604068211035800010710310001400b8510180c034200380c65050200b68080c041d02124854001195400d40081903a01101c5880491003041c0c10385410a00441c2840b00d880c544913101d864282141950b50f4159043c201480303c5a103030080e90965600703500c20170280e80020b03446011111113103400b2000e60303180c0041880c2c035190041001d900000e841c50440c140c0188903004000540940d02c211610451a6203180d080d05019400740701e07440010342a0340d42d903901c00c0d000b818105c2c00e5401d15000446c030f03411b001390818152101034031210a1080b200c1c0819050548400350b00b5005441e1410740039807940341580042850410700b501030286992503046544613030b45c0303a0003035031030b190f1011882e501c8903080c11018040c204184a0040c1880c20440c600c403d802c000d004160a030025050414180300f4a0346588181100c2090042c0c1d03e1580c8203000b201160004100008400014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 485158192 1250 485156942 485156953
    0x90515010920070201051c020d1a01111605060c12220603050613020f090a0303180509040206031611010203041b0602061308250503030402010306060507050a030e010507060c02 77
    0x1c02c4000001030030906040b461481400280010307a40002154200040014450340050f403e1112000a00c529240340403070030310700783d482c03050001c4d806031654810100340c80340d40220340b07500c600b10340710321079141c1d001c2071220400d0f018031091604502500d1034000843c00c6540260820740400f50b1544070304907a2005c1c440440708152120801d501e0f200240405103400c2c070040c2480400314842851410b21003180c107401040150301c1d00380a1060307604d1444010311105070b4039503e00300506110f420810a40854400300b1000c605810b11006007405140e014104a00d5070780c0d141c1030910074001802c0e201c820840b2140403e0610a07090024500550003404072620900d010624441c1c0040035034080c0c1d0547d04400208080e4810051401c09076640041034141d49100d07200b02035000c071640001414071592184071304020320900002441c820b5100303807802c0004a0315240140c0b02802048801041a03100618030301c0064494240084002410b04007141480c0d0560741d001c4c01d550100c2900801603200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 485159442 1250 485158192 485158211
    0x501120203120c030414150a090e011e0e0402030705090432190c05040212061e090a0e19080d0f0e0c0603040809090405060a0c02060705030601030905150109 69
    0x9006442c0780580ca96041c61601001c241c08540340e024034420340120061100034040300b5150088412660000c965030b0a0303450700c040c00e010f01105820f015020034101c140d0000304d82c04480300032454400c0050003103280d025142103040c1015410051040342c040c09032060000d80e41e11407850160040e48201e41c1228140d28041549007074000b109102c1c29405032120030124040c0b008601404c16000c050100b0040c00c034a410028038460035640700365081071001450565401c4103032a92400b91100311906400c9502d1911940c00b4040c000c1a400d90110304040803500f80611a441040c1c40400402901d050b00c44c4031425071101c040c2c20f401642e20010004d500700055003203200707210560802c50f80c10040b80f8a0428030b103598518201c0a81e0251b60008040b80522505038151340c0340d028001d000c501c051501d40342458072144150b4043d2041c9040c441c0e454100740c00800c569102c0c40480d0f461905554908004402408507a0403d0346d16006440c0710300f8121901d50078160180c5408180841c40c82031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 485160692 1250 485159442 485159449
    0x60f10020d1107030b01050d02010309080a030b181611070b1605240a0903051606020a0f050405010503281a100e090f09190b10090e0604032105011202 66
    0x440740b000d80580c00003081400003903c0941d440e41076504c241ca103581007405910042c0c0003030280d090040e20820010036800c09003541900540b1031808142c800c425901c0e00800040c08480080d503d940c450b2003034040c00540135107d0403c4804980704141120b02290f40c40003845816480211603501145070384007100c06104042020060080d0316410b40005181da0342000214820007800107c0d101d91141101401c1c18810029a4122410002030031079000441ca4141d000754030403038820b80810b2846010000c46030044c01940d08844060310f41600e990344007076070a51078224064080e00081d01017044020074003941d10070540b0080d81c821800d9883e06a4804003c00c8000d803410040800c03c41c848410002c6d110310120641140c0c5003040d00c1e1640d120001c9c59030500504903214030b02400d0035070140303040c040454440e034042c04009000c0141940c880c401c440617240071140e0605144d2107030020400092040d00d0b0300390740403090b580c001d0f42c50300141123940c1561001e922024500d00400c03004800e41c034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 485161942 1250 485160692 485160707
    0xb0310050603040b070e06071e03021606230d0f0b04060f080c370612020f2d0c01050915040c03060506060f030703020d06140d0209060f10020d 63
    0xc04964031415460076546640003c0c0c0e00408960801611601e410303800c2d00d919080e01e03a20350b881541c42e0031541d0400c3c04040030004107034054006100781031412012248108806083d129140eaa42560352030115080b107916000302039126080a04021205400b11107100b0260075070180180407130400309001c00c120a51300a5081b0200c0308452030401c10400b00e0000d8544543c24040e1031106620529901040004d9013017190340080030510800d940328415440200070660710070b80c82c1d0074030f9214100500000c034040c3e25030304610381e1403c01400700004910382c80560012540f000c01403240301004640702107034112440806890b9104c409003d034484044c0081c50043e1003042d510784083c40d00d903c030060544c40d01d11018150713039550008624582c0700c080807108104c2048001d10f6607810003000080080d4008408040b085180460124951041180114015a0050400710268600c1d0204407203c8000750550360f018031526400c529940750780c400c600350b03031545402400d0001841040130b003400c0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 485163192 1250 485161942 485161949
    0x50a0e0301060f05090a0213031a16050706052e170c061b0f03030403170702060408030c13090603030207260304090c020109051608160308030f0408130b0310 69
    0x90341044030038018080714090f902d085400c00c4a0360070203a102c24102c1002480307000340d1200c1c1140502030200c24000380c0b51400c1b201c00e0305885a61681c3d5241c0071444009050b02c0c918200045041041c0c1c80800c07400d070440c0e5000200c00d1070300c2807503003c2d089102d0300c0090065108200d8032080e120820180c04400020406640e00c0005404601413050014038540319003410340031400700c890100607001c48104032410300c0c01c003c501105d80c1ca0030310b818064080318000640e0004000144009029144041561401998896030141c15901c3d0284400d081c1d803c0340f131034111f1066a803500010022850b0041e9401940250007601c403071800e1080241c1d0403070521a2020f4030f00e43c07600d555174007010300000329012a2081c001c001910f40c40300720100e01410081c0405000d922504806002041c0894441004c0310001e508a44181300a000c043e040c480991002602c0b141e010b06c001041004002c0300c480d44580b007180c4807840d0106e00d94000d101812580c02c00c0c8004400403080014142c801076034040503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 485164442 1250 485163192 485163199
    0x1050406090516110f0105010f03060b010c03021c14120109051003030f0c06020f071401230103020d020d0b071707090506090f0402040909200d1a060619050a0e 70
    0x11440c0003d403d034051220403110804001c0c1203e03064108001c24082c0d1440100b845c8002d11440d60f480300b050410104500040e0707146890b007691700a00c0d6000b207140c80f40322640742d00030748810008404002040100031084c074041c030900e03030744070690000140024010601d000a140b03055504043c40d480490350300411400700703203100c852700307001103904003032101403540c4c051600c3c5880301c10b94900100079025504540f0710071017001c1100410001060485008404144000c2202414043e1a1529220621649150340a15400500250412912621115002401c081c0c02810035a03100c2c507000704110f8607840003d010b00340c0c01840c00403050407076800121600e0920720150401c000580c4600c03580741c81d644140b81a00b07402d8820388460301a03400806040f581003191007100c0c104184940300081040001c01c1c58040c60880510b08442d085c02c025402544003801441d400b290101c101101074200380d48490300b400100c80c0300d006211251800612a40c0b29600c80c3c0e025000941000c498080070ba12 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 485165692 1250 485164442 485164451
    0x803040506010e010602030d050c120408120615071104110c0a0605010509010f06300c02012004031709060307170702010e030f130506040303020c09010e0907030b19060e0105040609 79
    0x1750b400002d403207035012004400a0380d52901882d882e140d03c900202c802c0040c00c0742c2700300000d0102c0b0354041c02000391804141c2c000c40d515107007001070a119182041800003014040c18022030f0804032041c0841d5000303000020072092036501c0f006036030445013810344207070700c1f240e40002080600c0c0251401400f0556401240c0e50514031084040c0c056800313010100700c101d1006c2860603c002840f00440c2d103040c04d044840900f540d9501e07004e0960aa51030015600300f1147c0c5035011344848d140b002c1d000e600561942814155501d02c1d00c0c60b06042c04e51106004140700300d40b01c66071284000c5005526a8455210b8034805a0f15148810030060440c0c05591401e41d034001002c4d070101c201c80e1807010303003084d1a6644030300c030a125007500b0040d0021038000300d01117008070030140c0001d4a4294030004845c0010b2603aa1400b1404207000e0403500c9882ca5003040c1c0303040002640500c1920342288400d200080d02c0c1075455210800c03260240d01c04541b802c0101d00401550409100b0100940240340c0d0500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 485166942 1250 485165692 485165699
    0xa080304030f03030b0d0b0a0e0f120706020f0409020c2b090e060a0315020301050405090708030a0810030609060911010203070317040206040f0e0a0f02092d0301090803040506010e01 80
    0x7050052803400603091540324103034a0782543d150900d1900d0b075035011001020602340f81041c41e0091100911550891281c8441041180c0700095000c2400d400e44842e1440c1110030750362403003e900803c4000c4d154103030a105c0805d0245250020341a45024807008110050322048600120141591800084955180600d8640e40d0118440050f200003240600e6030b07440382c0000c01e1140085134400b81060142c4c01c18111003180c990000c5040703a00840e4140941c0d00d46910490310740101e882106100c1d0310030805e10741da660181088507444203281020311801c903540d40780c203401d0703981d42d1500300c4099030340301040300c1002280303e200d140d050710030301c0118241a1260707000380c04240c0c0c4074540c08180c014200010219604c490447d009011002400524290303180290010104281e03003912a190a180289410f040e00f4401d40b10703a56002041c40f000c070340c02c103800342e5104151103441c2c607002e0315540b0510f101034900740214004184603042040c1e0302d10f840e0900900b07040043c0c0280c130004500f5170040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 485168192 1250 485166942 485166953
    0x1b0509011b020312070c080606010203040f03060c0509040204090507021204081b03011d21071a100f0b07170c03030f07050423090f16120204030c03110a08030403 71
    0x64908009410140d0015164000603152044c8164030056080d4001400000c0101c0200c80300211962201124442c0d218100103a031a4052030040d8117140300c480301d041002c1403541c0c00c426066603640c18154508800e6001283c2a0707072240d0030095840352202c050220300c035410012548401c9500702114109410a95029103a603508a81c012403084a80084000b590b001c0d40b010074003400c9250441508002443c10b41d031520182c40c01340f450349030b00e00311002d111003900040b1400141e015890441881c1000d040c905400b4001d032034601c1100220b900407030680311132035518014041c07400d0071945505030f41c90610b0340d0600030621180300d01401d00c00902d07440000425a072300030310110914400d56a41c401d0440b400d000d541c0c044020f000340404207469005498076000007001c010f83d2072110b55500e0300f83c1708510b640140c404001c4aa403064002040318070803400030f80614081d617005840c095803034444d1403120700c1c01d4000344ca00d2032102d81d01c440e4a15240c04010000d0480f50301550625240d031310380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 485169442 1250 485168192 485168207
    0x305071203111c0209040510030201091205100e0f06090616020304031205090d1a070809060402091b04240e01020a080a1209051e0d02070b0f0c01060506030a1b050901 73
    0x10780280c0071003800c10503c0300e10b5010740f81440001340c02041503291800303074450102198170080e40813400031000071400020113940d41076215000320040c015000b50185070300090400f220380d031803940107074501000e00140901c00e5134014101200101340b00e092441303001002e15031405600707083d58001c2000b040003a0744464031090600141c104a9141d80302c403804600c103869080001007a442c0d07a80800031414a01d00b451500450640e41d40e82c24a94588900f107654110695020707501500c00000103486100300e0041100c84405095031608159441070014002900302c680035a192408c60715010580d540011510405503003440144550f902a445824882c895803131240100480411030f00700c00051900001c41c0140d010089400b500701600305030306444021025243c10303029614031040403a1002603d0010f4900800500380342c80c882c50280040303a41f1a0290584031354881c1c400050503520360018522074000100003145400070780c000c42071f04c0c4001c0402030701444402d0000410030b9912146 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 485170692 1250 485169442 485169457
    0x1b020604080904060b0f0c0c060705100c1b0303060e130803010b0d0b1203030f0109151719080307080703050c090112110313110405010308250f030507120311 69
    0x1982d40d2a0b0894000c03c01030885504080d400500006000311080e0100c0001c00310450034a0036903100403603140402102e8410f07400c0c098001e03400b181c070150504a030f0394094a5080e0050801c81a81d400c0030001004144101c41c0680200e50381c0c100070800d20141d0a481d44d84071100c2d000f03020309040741c0d64401070300740810b004030160b40c140030600c0f07900e40030301d0781c0590701c07000d4020f0403d00c0f041424078145030740380e0049500b01400c036504000015804002d004200d030380040d50180581c40c90510b4284481455050b03035503442440345188030000e0704003401803070341424020508580c1d2442c00c1000a0240e44016201c04105440d00c41004580d202c450b041d02c818641c00d19010004440b00d80400010b41440034152645620000c140601c855031060355603803640c820202c20701701c80d99020401c402c6a07424800902140410050b04480d21511000c4294265810000c106445c120352603440341d0303030419403046004c01c10004555081c4980c2441314441c502c241c0c0340501012902e4403910459008008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 485171942 1250 485170692 485170703
    0x801080c0a031e0507030b0601021b0109050f15030f04021509030a0f08121005040c02191e060c0206060405160c031d041b110a0f0f020604080a0c03061b020604 70
    0x200341e4040c204240d09408056a08130041724001030300c0307081000f2401c0042d0b40d6603001d0b02c0b13036070380c900b2040d0b0b8143c40c0c0082c03482050b11100040c528003402e001100340b2449203264014604004150300c04a1640510b01806080c8000b554030b00d03242c818015007406a586007899240244001001079038002018070f042c55000c0d504010500191422070898001e881c0315201c0c1d003009404000341d004070540c582c02264012a0103024902d0480d40603030312381c001002800008800341da034640102e034164044a005172650030300305508603100d459980032103140c0c640d8840140c10400c18410103144c1401030303c2d0817408080004040558188000d441c8420713004005084c00b949008000d40e4004406041041800141c41444090840400814400307070f40c078080d1001c0340065a00000c10800060204ca110344c1c08540701e0420034590b1103603074012521000880c0c1c003240c10840414450010b2004c008840d00c1a2a03035050381c2d04600e000c0b07003552040c4001004240000c03000f61900c0d82d000604c16001900302 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 485173192 1250 485171942 485171963
    0x19080a0227160309050d030b0f0117060d0311030f09041401050603070e1c24020307021218150304060b010305132006070f05100213031b0512030a0801080c0a03 70
    0xd282c00d4001d80b68944028045008100052074a5905904400c010100485d07803d00d010701d4600054400c2009035501c4000c885844000940c141402a03400f4034240c0a4100224224bc16600c2103103180d00c0003105a030a07540100b500480c41c1842e024401817040c0b08c1c0c03031030120b80d03041c0303004900f9900009020904004207071200840c103488444401c4940c4c0604a024200c8540d1424020040f000f2800a0184120f160650b61158070301e9100b0740b4010003440d4060f10b1450040c0c040201690000920660502140c0b1030350300b1a5950b00202c07103440b0080c03d072055142e240504201d03084450300b40b8031034145030806080140d10b840c0301c2a034030760055012000442d00c161020f00052030310a0070f03501903040100003504400384003528204592444c03060048440840d45000c40005074020749000740c11083c8002c6007030000880f4006400342ca80944216a4000c03a070780d000117031100030460241c80c1241c20004d030080e000b80d800302e03080f4090401c0030010202c06101c40c02045a14882d81300c0a0000c07510b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 485174442 1250 485173192 485173231
    0x11404120c0501060909050f0309211f06031407080601180f06060c0c060c020f01050703020f0604080c070504060308040302060f160302030a09061707080619080a0227 73
    0x1940800c1d2406800c00000c010b041d440350300304c00c010801c841081d1000c1c4260742000d86e130030f00300008a602049014014040b0030010780302000521318905400443c501444420708216407882d01403020f9222400404908189181862038103903250300390156464014076400e12115100084850442c0c858504406010800311220401003120b907003840301e0503003011400a40d080d4492001c141e124007032032075240c40581d07602090301c1024044d8802900161b80e010f00d80020741c000c9028040c1c082c02401514020b00310340b0000b60401e8403c40701140c50030000300b107214404c0c408100d00c01c042d20041e07504000481c25a200c1c64404e008501c00248210b00010f0582d442a009105036042c4440054030b101400086141c06034594120000d0000014010701300000d5003440f4401015191040406043e010b0315007100884100341c0003000c064000000c11400480c482030255010014500107018202ca01d0280c810809000c4845070b084614408205810b801190b0308464980c02c41c001d440031900f103601 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 485175692 1250 485174442 485174447
    0x108091f0b04090f0303060e0108060703090c33030c0e1002010209100921021c031413091b090605071704030602070201080a0510060e0a0909030f0206010801140412 72
    0x12003001d441d00700d0309295540c0c041060015440007010721070f40301404480e485904200405034248078900b155070203000071880300c500aa00550700079008000400034192100c10039240e01d02d0074081401c1100320851018500c19110007840c806151510701400300b151410b80040c08503056542c1039204040c800340c9140d215000350704841101e000a800d00428402c0301001130300c20f880611030410700801000000c1107606119601c410b2941d401803ea035030080403607100010000c50b201049090051401180c01e802c0c0041c0054444070800846000a15042021070b40030fa40d681454081e800184600da441c0107500a40104169603c500d0000d80f00d103118105000700c00c20342d5180d621040e400207000300500032280c0061a00500070f80322110503858554520085807030440700007801e408140f00a10413070348100003404c81d604000b80b103003940c02e454212550132140c41360006c801061002c04040801e41d014003200d801090110004c0003440c070f03031702c0d5461103c060040005180c030b20150f8203150b0150 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 485176942 1250 485175692 485175701
    0x306051012200316090b030a09060902040e0a05010e0f0606010c05030d05070e040b0d020618010507140106170307020a0b0c0a05011d070e090c10021f06060e0108091f 73
    0x40402e0b01c1004032040000c480d10351603106462000c041041c0148141035a4010216003040758121710001d03295a50f000391700d00c01080c01042c1256602e07140d654100150366180039500140c0b580270050080c001c0725103006400c48210042d040c110303030856003665041b050003040b4558400001c1c2401621650301d03150141c114801c444510400c80c0c9490203220400f94170040781c107201c001c1940e04204103c100c0040081440300554020b41c003000c100030303200345034142c12030f07070743c40d514041c18180d00744411035903020050b402050080e002d03a90340350000c00c0b00007594030316680e90ba40608007640c640b001c66000b040d290302c0580604109000700040000c06070754108040d014041d0000000c000e005000a030040ca01d00555429922a02c180c000201c0e034901c905403204d0050303200400401483d080d44c0140b0000c18400c0603500d0940c000c204440707406030030100c910441c0329021800021082e04102c405070a0901807594107041080240400c003400e4000a40b00f0403e40e16907011311349105074440c489001e070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 485178192 1250 485176942 485176961
    0x6300206070501110a030c020312070f020309030a0f11010903030c02360f0a020405010e0906031603111806010206060904050f0d030f0f2304030302190206070f0306051012 75
    0xa61130400c00b90402e100c05000b40c0b8400079165800d002240000004076680c1c0a4188202510410040402c43e0300c0c0c02503005064094183c0103507410565520700103400d00071850015290002c01504420402c008203440c84005442400d00114460031518010910315072840000d0003450b0614804101e0030200d103188094103044131080341c2c0b10103117825641e007003001038620f40950302029000c903141002e540251000e58506075210740040d424002040000c0308003820340e5425000e080440a58083c0382d10ba00e8000d11300580001c07c0300280306c0107004070700820351140c48a22680606002e82caa9010500320341255003242c20242c181c55038200741c0c0c01c204000f503640195110380e80c0060307009900342e0850f10000344200300401040c0d0351966064180d4a1001c0310201110b56070300c80341034041001034a25005402483d0041c01c2c2241c8500089030340281034428000b688c0040304000c40b030355008c1800c0080c64280d2506105c628940004203a0003422030410b0014005c0070030100182044652004445 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 485179442 1250 485178192 485178203
    0x30504021c030f081503150c1303080c070801020901080408030603070b0d09050f0c01020604080a020705100806030c040b0f151c06050a1e060804030c06060906090630020607 76
    0xe01c07403a80380160041d403040d062500410041c80028649181c9603801064440003c0c01400851403554511100c0c018005c0040700b00da003040c405100111407040082002d5407107145810303900d5030320750a001c1c5404c44585c410140c982c010450028580d910803000758202c7e03442030070b9944035119040081c2c00d106640d042503030b80d03680c003092a800c99403160700646a000c0c000c2c0144d56034054003009594403802d14014881c0980d1144011400181d84038005010300409481502c080315102e10000748808004009040000c4250040c80f80d68a02400721045031002201d08209444514010030a403e5002800c24480d003070f5003891088044c601421502c02c50010442408015110b0384a400180122f020b114040c02800740089800c0014041c5145d84a540d206c1491031280b07041c00480b04032400a10480800410281240000d105401040050700e422000442d0385820a040201210925484201048100c0c585000301250742024111007901d050440e9150140d94004a0052300c5000b400404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 485180692 1250 485179442 485179489
    0x1d071e06200309310203010e06090402120712060b10020705041e0501030506011403030f0d0c0e21010c0203040b120403030e0304090603060b0f011b150e0a051501030c0603050402 78
    0x4101603584d40201c4550503280d4100030312450380c44600481c0803d018401d0100d03094404a0128034042060650040c80100a0703011000407285041c1040102d074440007980713001e00c92201c20400c2d14010300030310007415034081c00300c0003007508001e645038601e1003000d000d80d42da00004ca02d0100120f143c00d040300c0d1006420300143d40d480c54100e0780e0342e00910a07000582d45518000c42280ba0102c2100c030889141c4050034244106a4844801030011080c0d00083c1719006c01c01d07030841d4450342640d441034102002800342004408400034207590400300d2039011904100300501480c05614142c0715513880300c0074002c15070364941c40c050380100901d4410041910000c50005540309841d008681034a11500050124011020078441c403101d44076641408940030b03000c04086c94690303015031080280200110070200c6410b50348202181c0d1500300300d001a0b0007211101303040c894104401c601d80070040140b10000d40c95501e4050212040f405500d00305038490000c20195a00c90382140078961086c003200c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 485181942 1250 485180692 485180719
    0x20c010606051e09060f0a02010f0c020312010b03090307140c0a030507150302070209010e1312032a0906050d02040f0e010e130b06131d071e06200309 66
    0x1d060742c000348043e60855418210252444007100103a961901000e800681007011441c4226055001950107200b103660fa6881060490000d0198507a400c2d03840d0060341d510002030240d0b48a0b104140c02c0201604401c0040c410b07540000070840301444d80001c0c6040a0344689500d0030b0070400d1080060380c4c8880e02100200a0220201c2d0040032503600e02d21070f958486404c60107809070f008180f4060741c80b513404401045000143c5908960100c00c25a40c282c07041400c0d9a65949131006140000000b030751001e407481d903080c41460304421007203661450742c400c201c4454010b02000c500c0c0640c03003c220000c160490000803540580b8058000051060003050b03c0e0b80b85000090000d106081c46d0204141c0852254411f40328017484580d000403000c0d400355035031801d000201c4800503d21034540c1c0d07502407100c0200f644490301544074080e00e0180500782d2920b2003100030900c2c001481c1400300b03880507040001d076400c20b26042483c0400c8113018140e010744140c2d541140111460346420180b1190171a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 485183192 1250 485181942 485181947
    0x201180605030702100b0109060c0204090b15010905030604230a0b0712050a1401150e030a050a02040e280611120613020406020a020402070219080d020d110c0904030201020c010606 79
    0x2940318000a508494040c04841c09505c00e0700c01c0c01003c0d601148180805000c014030a9004080e021300103070020603070100d82d039902c1042c0c000845041907206140355041807d580e00084400c01450211f00030582c40c181926107106d00c0f968042e424541c4000e030000d6400a010500940030140d400ca0b6402415140c0307148064280713a48000c8283c1100e00d0040060124540d504c81c1015100d2040c403003501c00c0e0300340701500c0142c0100d50100b0301440f80482210b00640c2d010044082c035180300d50054444d42c841d81c814801582c0510140000c290820117140c540b1170700075140c90001711401c50400520541030f08000004001021480e1a142c4001400e4003545501d0452a40113100a441c004034101056118104030700880c05500b0041c2c01643c00d50300945040d4000d40340b224002014000c21801c1100a801054025840300c1101e030000c8031580c41d81a014001c17440403402a060258a060790b4125594541c00c0407034140d4418138424001c1014903100750705489105c0d003400e00070081251110400b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 485184442 1250 485183192 485183197
    0x619120c0305060708070f03150b041404050a0e030304080a1e0201050f07090815060a1212030b04050705042601051911040b16050a0b040b0f090703020310090201180605 74
    0x10340d043d11480d40424881c912841d807007841080a44da031030602e92048003048018102c0c8070400c20300303003110000c046041c400d0080280010190240740c2c14008804001340815910000c10902803207150800d011400b01c03002c07084903800750307008800c241d441040071800d503401040b00c0342c00c00c101781c0328079210b10f86141c0540c00315000d607404501d40c0036190740b09081161a000700b401402e02d103400a003019500c06003000390140d0003450041c80700d50503035100e402c10800c03204120816070704240c102101007400d5802d0301c60441005000d49051295103000c80b00903102d032185110b90604604d1081c01d1082400a03000401c1c40f006498009020a00b004d20605410414800d071501003075140102d0991240100030444007141c812540c0141084030989460030055142d8070700340c1d11402150072880c001402e600555200f94070400680d689401c140440d02e0702950000c00c0c81c00716510014003480981d40010305140da1512400001c1082645440121000e804011840044d00c00c0c40802003076180c1c00001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 485185692 1250 485184442 485184449
    0xa0504080a1202040f1220030c0d020d060f1e0b090118020705010603150f050411060a0207030b0a0c12021e0c01060513090209060d080715060b0712260619120c 70
    0x1c8135108909140c4d14400c0303000c2240c0d07c49070305034442d08028200b8108001000700850004004a55000442c3c440b8410b5030120090704a419a03624500080b201d501d699014100d030481c1401c10003102480d0101e0305110040c0242c0b08200e880e02d00070118032899804854585078403800a1140d10ba03a4078100d20305c0d811807000300308854140020444240c083c0d10a403445030350403a580304102d801c01014080705502541062045015911011020a811044041c0a850002000140301085500080880c10f010600402260041215010041074180c00308030004000740940e03514480308181d02d00410407070b4060f41c0c001c0c0c050130020070750008660018012a000345c9500c5d80341d80d160003c0004022081500622020043c041100811502070581c100d2101e8804005059511121034000c0c0ea0801441100c0e000b1200105681c01035011500320810401c80d030f4080340c0b44c4207920b109296154024481c1c1d010b2607501c12905105241e00138206c0091540d840300c0f00000c5a9404c1085240c0c0843c007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 485186942 1250 485185692 485185703
    0xa0f09322206050d080301030f08070c0e1509150f031f1401080a0506160302040e01081c02070f090207020402040f1e080a080a0302030603151306050a0504080a1202040f12 75
    0x120b0001d16030900b100110741440d1700814180c034580c219903c0703003401c00d034140d01036031050b1060007400001000e81c140080909a0000160b0b081c2c03800e071822940103491080d815009034029400d11220303190011b140c0d4881034003251404240842480400c0c035242c900702452001040400840b1044403050303000300c80351601a141c40650742e80703600e1010b40e51801d04000500603070040c1c0008488105039607004c404a0f02501c1e0241c0f074155103440607803e000c005e0700060443d800104007100c05002018480ba42c090050024041091914603da500c2c0c141e03e1150244ca40e0700000d94808640d2964120b030b000e86034038844043e5658607500e50201c3e0b82e4084040484021068402081540780000c0c1120001e5104404a21305a403482c82100690800f521168252242648100d40702074407950703092066010003407071080070744103003807110946902801d000080d9290205007c04200282c088402c2c00c04103080c407400c081c50200c4264024811980450f0700c00c0e854a030301059900e107110f0440300c21800f81 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 485188192 1250 485186942 485186951
    0xe0a0c0f180603020604061b0f0605160c02011e020a14010209010906110c120c090f0601120b03072c070207060e042a09080f030a0f093222 61
    0x15040d07084078200c1c040079601032802d000400002e441264085010141030f40e0000000801313540d40008002504011a582600c407020802c3d0800c0c20885501c18840501c0d000ba1080459000605580c0c0c855004001c041d11469440d4400b2303000300011303804640c1c030204045401204243ca03a0003904080c0c0024001000301c00001049840340e0381d02c42152140300302400284403e80100046034401803070074010341c021075100f0007407a039034000490303c80c4441c0c11250015140500004012504100701124650702e070940c0345d00c0c1ca4138001144415102d01d8403107074580c00d810034240341101d00003c1c20038504401540030086404e07808540441260069199505254000810030056941d032138410401180b10003211400031030107141d03071501083e081c00c02c1102c2c00e032515101803c08034181c5060f0043da00000760305101c654040040c982030354003403801001042c100b400c07240100402c0000030010712200180c0d020301c2e1070248008042c0b0780340140301c0c2c030500c1c00f600c1042c4c01c42010b2103c24220300386070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 485189442 1250 485188192 485188229
    0x1181101080702030703050901031a041401050f0d0308061512010b12150904061e0c1d040e03190905090108100509030a0e0d050a020a120506280e0a0c0f 67
    0x3042d9641c10758182c5a448c10718100c1c1004400070070741c026400d80301300413140b2480b165448901c103035101494a06000c0f0301c00d40c140700522061507406510381c1e000300050310044000c261711805242c0c104a048a0150303c08496103c040d90031f005071084c00742d41200c079100004c7c1000e10540240010900214030810a42e80d50165640103d91170002980061004000400050045d0b0145005401c402e82d0040800403c818490480f4907950110303003c500c984c0c0c41e0407100401c211070140d125800329424401207610007040e640f03d000e582d6541210a0583ca0f85090042c0103180100c05010013030150000f070340c2d4407200e036540d07240101c400320361051408001c00c00310034000c0100d90428200d921615140903035101406143d80c0c030900151854040c000d07c0100507502c0c20340f81c1c0001c001d5010304405d4041903040c028105280505101010360403003100046845080900c8048c2d50000c50001130002d01c1590400d00701004020000c080008500300411140c051088c5241642c450441000301d1f201c0c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 485190692 1250 485189442 485189447
    0x304030302060c18010c15020d060302041b090b0f0f0a050d050a0c08011e091d0706051206040504140a14010605150d0b06070804030507050126040b09011811010807 72
    0x10488034070820065540744d80c4065020303404480141e032080314045102500d070700d001001c036000a0814025581c03264030030070546c41c250040b1303014409540c2d2241c600c01003020002d0041d80251090390031092004c07c210410f072140380181d4034190480300c4005e9880d1007645008003117504c011700c030001c0329181c00045002102180b18000c108002504c1d6002c5590808558040d154902012208110740d11540810710711030501071486003a9006004961201c19450104d003021940d402c0201000001e00944c075000500d8107200e42c001a003500d000443d5215400d0000410542e29030541c654420380c0500010050b807102100618400d4030000c004140d00e4104001e1081c00c4c02a40442418050000122144c0168080003000c4401440149000381c1c580d80c101290704103501c1529075400051080115507007004014170b40301112404203603012510f02802010140107030020300101007840010f41c01140c2507100c0d41c9203148880c0d54061454691a1980c0e141d003c0e02020340c0083c0f81003002c00c0c0c1c010b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 485191942 1250 485190692 485190697
    0x4081e0a1e0c060b0a03140c120d0e040234020306010504060602060c09010201060305071e0b0f19030f020708090a090b0334030b070e0a0f0b0f0d0e0304030302060c 72
    0x20307159600c2d8901c03a51615200081c090000c1a5a40107004220002c00154102c6284041d1803000c8003422108100303c0c1000104100d0100084540e0480300b1001c0740c1d55807080c0300d46680d031011200181c0b1a08418140a9002208100403a80d01c000147c0d102540c607502400400045c421411034486a88400074841034503503511940016034418404101404001c4001d00380f4640c2c188000207000b40d5030340315585040841d5000d6a0012a803841f510800c442425040010b851089d088600c2c0c424040c4c240c00482c801d41c00d42c081401f070200f034210b80d45440ba0f000323070140a00c061000c1d51107012504200c1c0c1c0c1391740260310030b0744502811100000c442d0310a0007031540070100103018210031081210380c4000e024044500c03c1c00203142080c500070224103540c80c600514000c00c2242e14030320b041c3c03401070b10700c00c54007520710301c24040d800c0e00300b00840d0411046000c2d244d5101c50340d1b490310040c107008102d5005195543c001c99040a0003880c045e4400030180003101d020b9400c4641589134a0a1000d042c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 485193192 1250 485191942 485191997
    0x909200a0b030a0b030604030503070215010308040b0a140a0207050315040f08030a140a0e010b0a0f17031c02030402030d03110711030a0204150611071d04081e0a 71
    0x648800c0c0204880d060311030103164044802c007004183d5202000c0040d080803c2160100c1c042503022060255040c3d041013070f803044000e04804001c2d00c0d411a111702d00103000750703c118142d030040060069001d038170480340240c00301200861203498a03e2944040e4807001a400b59900030321840d406140c0141529600a0060b1f4000068041000d1141c8880140c2d910080840d4829a01c40300040d54400c05006014414050300703000090311125134240703900b52043c1202103407151030b10320400c0c840b1400011540003110300c0500364402d9800e51215490642c000d00c2400e403c3e8003004ca00401219180d45c004500c600d200f2000d403902c3c2c4080c0f020540844160f0740000070000d03002d211382e10009043e1182e01d503444400034202d840c00103680e40011b05454001c0544041090700903400c010241d00321114100400440000d4840c81e8202100402052032010300424a0100a0046000c2c04a46011515a0800c100112410200602c20214aa40110300d0070000412091480242180c0342380081d011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 485194442 1250 485193192 485193199
    0xd0e0d12020909061011070f0513020a08070e010c0503030a090b0c1e0a0c06051303020601050f1f090305030a020f1b03060406091403070f050c0108010f1205010213090920 75
    0x664484c030042c040c01d018040052810310851020100380e105003000390800410422000c0004a420413080c8200001c0042024108600610480380402d42095240ea0712408518148400c41e8101c001250040c1506030040d056020010038000307a60615006500c6160090080403419115404040e03801e1040008600c3c6108101280319400c0a45d58002d00781b9980914149080000a8580d081261030641d5942003d294140c00341c01055010f0015a00401085503252410080b82002c94a85c50500400c3c4c0103134400d02104d0302ca018011b0703100c500590741050441b6103c6d00d4005e0013944da207112201d800d42a20808802c41c904500351b0710380048001d03024015142584542d541c100103003641010494041401d40300c0c0d416407801c104007900b0414007500310281c01a44600f0198140b14030b04014074100000b0500500c0307500342e030500c40412980383e00822200f459030fa0070f02d03600a006804e00351f0715079840584005000569a00308540c418001c803408110380c0300c0d0744030001000d031152814681 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 485195692 1250 485194442 485194459
    0xc090602060c130513020a1d0a0522020c0303040c1e0b0337230103020108130804060e090f0103120c0c0503010e01021b030703140f0d0e0d120209 64
    0xa04140200103480d1150043e200200c2c001d888100103210308401041540110740d011078460301503580400310070020008140c510116500c49000701d0f008280900500e4021030742e5000d000b01d9240c1c006004494802d94139000c64a4168000f071142e180d42c030655007511058540c51000c5030407601c00c2c0e4488032044400c4010900705240104010340f90300f00416001c8080040040d040c000c8100d821310a00102c1341d5213015221907604a42c2e0b5003159949038030b0f141d5041c64901119140c03031400390082c4c1580e809081440469581ca0010400c07040301d05801000a0000b1600048080c2c010300c440119001c100c55088917596108250303400940700f4440a000d1480122040818600841c9510f010074042c199200c1c0b82e54544010030300752141840c000150380e40c001386006044d03030010100c0340400c503818007551412040307840050907108000c54031440b1004c0000d0f484d0b0800819012203940400c941c100703100366900c0001958075603402a00041c04100311420426420f501071080781c591142c001c01504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 485196942 1250 485195692 485195701
    0x1b08030c0604120c210f021b01140d021309060618030308091002030f10270c0507020301091212020406080103170c1e07060503012303031905030a0c09060206 69
    0x184095010100e01050240d03e503103200200c0c10000039108101c1da6121700020322107841c03600400281c0c0074000401150459000205440e03030803030741000300e003100740790407442403401c12103111f6688035241d900f503032441c070000351481011401c7d00032000321603074107604002050340c4180903a2041d01030b108008400d1046001800028001e860705a080303101c1c04101e44401810842c17a0080b07910564004003603050760400c102040c0180c980020141c4006810100c030000b20034800c0d1540c0303141300c402c0440c841c0c03103030008800c0700e08c20710580f0342c0c00b900280244413000315401c0015246502d00c02c12000100500c0009010340c00c00e0003114200c07202540c0d0181c16a00e075445e040c214045550620001203010000c441d1860303020081d1700451000d221501c0d040d0507140350418030f480e045610a0042c00b1040c4010890b8041084071401020300f81354012030780d40c404100190030346c400c0d0048486c030041104017100f90f065102003e144104d068503010042454084400d5400c2c0c2d046110360001640700324000b8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 485198192 1250 485196942 485196953
    0x140c090105030406050714180a080a0b01090f0912050d060603020f0708070204090b10290a03090c050301020a210204141c061109010f09051c031403041b08030c0604 72
    0x2a8043c5e0700386800b4114920802c503000030b65000041700e23000700c0039541c03209a0074038003082000c00902864006029101c140e0307031540113010051042e01c0006580d10054040418540c20510266920100c000b5215800304409065500082c02804802c0d1900e0307404100107000f0b01c05c8aa0200d03040c003003942881e205640388002c542c0121012a0480d8881c0000d40c0003403481203069001d0f003155041c00403d5401c1c000400c0400c1d2041c0d002e1002c44044100c0da044105c1803e08036941c0140510b40454102d410341000d2403500b005074003894056200240880c1300c1e0341d01a40c030070030807a0b4810907a0700d04d034001c0b1644400d0b030245001c0c48085800d034590481480c5480301b0507084040307142c0003011032540d07641c4030a001c0b1b030507910603032888480016814041d50f03404500c9441c548403500388036aa450411004c184e10180c5c400d049050400d000c0c040c50103250044060503000034960207141da80345402d150101c2e101200000c040c07461800c001000c1241039010050756007003c851801405540ea654550303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 485199442 1250 485198192 485198201
    0x151e15050d0305041e0501080f040b0a09082107020f0120130b070303060302010e030105043302030c13120b060d15020a110609010c080103080d110d140c090105030406 73
    0x440030300c103081100084510404003000940d03040e84005c2d4080c00c1c64180090480718004000247c0f92510f441080001800c5100c103030340010a02c5d4002980107510324014615204001803c040341e54404030038445001c5480c8058468101d55082d90520203030030001509856030078045041c00880c00710740c9510300001d9000380072501043c2601820055855016401c0755000c0901075000907142c88061056507004045500301c00001d80080001d480c05455280d40c2003900092105440c048101384254010b00d070798420150681010115030f81e041c200a40c1950307500103406002000c10b48400011251682100325403410740142d01c4a0295940a08001c0c04d400d80d50303421902d10040001c2c14015000b184080d0001401a0722860300247d80514010314045000b00702d02540d03070405030180307081e41e8007481c214112648244620344a400c01c24980c005044450928070321202d0120b050052505160052950044c10090740e40903900c45024003d80380c410900c0e9a40828810804030f80098100e40c0f1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 485200692 1250 485199442 485199469
    0x61b07090e0c03120a140f0a0206010b0c0a1709191505070515100b04120311030c030d0506031018060606020c0906011115070e03011401050108060904030c151e1505 72
    0x2007003451401b450380404400d42240d0100c80c2890004030f40310485035010000c02d40502054080c150a0042c0700045698600d14000c0003003101c074030070311400601c2e86034900f40c40c40d100c0010011900d410062600700302c0d03081d071031143c441154644140520a10b024904581420f40c0140251104107040d05100b110200080c0520092000b410000685003207000003070809040703280120080034a0030b06000340300701e410000043c40360300108484560710f40c0000450340c6000d07510a0214650f039915001a0901d0000800358542c01d00b08159000c1c018560740280b040144124030800c09180c07140022682e404001007110b23005844400840c5040d070040c840300305c0781980e4800712120801cac24800c0640040080d41e040c00412414848600d40e0701d020b001d28019039098401110143d894680020003080c0040d001500652160011a0030300d4490840c1c1c0c070f2001e401c07032103107507120b105100d100e03000b884907061405008148002d0741c2580301260040c2000211007196881c6202e0902c0108a110b60f184103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 485201942 1250 485200692 485200697
    0x2210709030b07030c11070f1a04050301020301060806010f0201020703021e100e030a020c0414070e191e15200717030a030b03030f0d0506061b07090e0c03120a 70
    0x24000030028005102c42c51280402e0354012902c182e0140e805800000488201e401c42c0c0c0107448244030b112801040309040350b03031149900743e1051b815110b1035000d104030741010750035500010010a2107900400e84900070042a030310510b066552801c12800c0303003d034400040040c1c0003c020800e50600c0076002090380100941030354419014442c100c0700310b80c1005013103640d42c0c1021440312440e0307030180702d1721071800d000381c82c14441404007100040a25a0040005007070009440307012040342c89000310700c45031108814013505d945407107880e8030301402556050f01e1050801d4071800b147e08510200055640300d256107030300010740c988105411f18007030806103110041c800c2d00b0300010700c900c48081004214031443c0241d1b41e58046d07058010151007810035510b01a520401c40039010090003801c80d0880c41d20304d04006203c1d00c8860024409100e03440003400180341d44824070083c68404101c20003158a030160401c505400342c602241c846030a81d150940c5500200b070f030586030f00e9220004021646a52 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 485203192 1250 485201942 485201957
    0x1914030c1e0910080702060108030a0801051203070c0b030f0c04050d0f08190809010609060e01060f03020d050103030806030606041b1b080307090306110f0405060903070504110c01050109022107 85
    0x1040800c503d5901c0d201c4440028010206014840e601404803038090300c0c810740a10701d4129242e0014000240611449024203090021104a44800d0003615091640005039944e2140c0d1405440300c150010358840f504c3e43d00602c00300b81441708107400c4030308454000d840500c28100c10b03114070101060109003501c0c1e414040120400608900001d00c1d400702c21a1180412400c00da00150700b152001e40141e00c01c01d2400b00188540b0110700c491504540c03452400040115422070110041d0040030542c1c0d1b00141044000f004040c0c00522031071142100390200e44003691140700304001c2e201c000000d41d43d00808a541c1038100c520400140303044400030403056907000540d54814095620480304400046d188440034001c0110134015908100e031040d0805050034403c0d4490b030540d03c224801da9104500008002c4400d0314103100003001888024010012001c9004030180307070754407403891010603500c1c1a0002c10044418820b503518118020802e00782445961081d01c209500503002c1070601464 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 485204442 1250 485203192 485203207
    0x3011517070c14100204081005010503120f0d020a09030516050105041e0e0915011208030703050a0b0904120e0a0f030b041e060609051320010c06021914030c1e 70
    0x20001001413000b070160050751a841c00003e64107181d40c0d038410740d1b40325091400420450707600007401085841490003180e510000c5030140081c034815910540d60460010441215898019002404590040c004e9500c0078803100a40c0d02c0d0100c031405400d0118206200c280050344007142d40c50851014142c500c1b240c682c60b0003400001242c1102d410303881c3c1e0702900604c8400f260000790f07140100b4040e103031014280850741d0303088103d01000b0309103020566100c00117240706034540c00510300204003502209040c189401c1c4040c2002050420101107250007481001c54146040301104803445407042d0004541995511540c18001070026100038210380d5500102000c0105851403440c402e1000296180c5000300420558070010030240140d20f41d4a0b004020800f400200c8035035924802c400007201d0b6140c80140c800c440d900070040d2800380f0200d10071410352098106900300c01003944507001501c291001c00d4a844c40b04880000c0400300c1400074125140c0d2541d42c40d40c0319001040a030381071200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 485205692 1250 485204442 485204483
    0x1003050105090c0a0806010608010308250f0c080c0901090b011e0302180402040302010509010804062d0605040b0315040204060506030a09020f1507020f0607120503011517070c 77
    0x410b0324a00e6564021007048201490700340b0f0402c0c01850305901820841d85000005007144005203c041c042800c005201000040c4014058032800c0e8001d03900442c41040e810110001031451404031510800040049411500011400c6d2901c200420006103682050000c0010300b04800c6811305001c1000091142d00d990072005d035100052070f80d070050715000034007001003024881340740090203144108024000340c7da04c8000c960740c68000b8200b0343d00c0d544075481c001005002c0010170070400c20101000060340748803486540180300c40b00105014003602c80081008075443d102c0850313415401540011070800c0d0001070540d201c3d000a100150781030b07035100070958580c4221525004e00f0355503902c2404500e00000540501d0900342d503445860755102c103000501d44210302020784a03802100c9007100316655407085500c043d601c80482000f40c3c01d0303914040c001d43c1080c007400404001091314458002c0c41108110850b07101000d00c00e82c152240d0400341c845208544c0203480781600d00c594844c00c200c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 485206942 1250 485205692 485205701
    0x90a12140303180c0d030f050c0a141f14131104050412080f0c0315061902011d0d0903060e011805030c0c010e030303220c08010b0f0402070308010e10030501 69
    0x4030300c92441c0d83c0c1040040007907030802d070700c0c85100c0388110789409070309010aa03c010908043e210500308241d840c284502d00710316044003c0c0c801040002070011a020042000c00d802e50450b45034004422a51000c0303880d0350071ba804010201410205120010b8081d0b0380501c0a0b0500794020000a80c00e8105c0c4004201a103408840540342922181e19407116150b1180c1c2c0c00768030007100550740340d09081080b03440e8460320001e490f24050800fa508902040d0340e8000c21a00400703a011600a8015070042c0064040c181d440304020394041d5a10480740341c1000400c03a1409070350b180c0d5404e0325090550b40c03224000c0c181c2001c0c0003507940d40c1e081580583c031400000100082c0c043d00085883c3c640c00c1040e04d1808140700150b5040003001451050540c0340002500d4200e44016080100b000044004242560010401a0424640010008480c0019402000c078440c05585560b8081030305820f00c0180e21541d64010001075103400108081c10400c0c200c0e03900002038941440c0340325982d481d01070940303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 485208192 1250 485206942 485206951
    0x9022805070506010e010611031305040b130207140d0207080a0308041e0309091505010207030b15180906061c0b0714040609050a09150e0a06090e030a0311090a12140303 74
    0x1030617000010301c01550030070b50f96030510880c1401589414070721109001800c1e407d200700c6010700e8686a040100ea5180741e9664182d801a0004544544250508200048042407950454001c010860f5600c5101181d000c042c0c4052100810032444195000c5803030301d1004106640c06030300108038100340b002803100c5c0301e005402035039001000c0341000b0480b0200c1b03a044040c498003920340340081244d81d8004c02c00748116034000640041b2951200402c43c03e46004420090380034000741c060b03001488142c0ca1044c040c82031030741180d005541e01001e0003070328402181131654581c2c0d0218800d00142640c144181e1000142c5001d50050a200c103411050350010780003040414107042d001e10050902c2c000840041c404440c00b444000340401c94840f4400160042040c442e95103000500786203a950844001810800d0f010020440c00900954907500300b00c0031240081d04007807411500352600020794003880d100500c480103151034a401c810801d4084e0000b11200042d0132042c4103840320600285106 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 485209442 1250 485208192 485208209
    0xf020d080f1c0c0f080c09040203041b06020106050a032006030711120f070803070e0612090114060f131401030f050d0f0206150103140103080d060902280507050601 72
    0x1907414100040645580c0001c410800034070f0001c1020400368401181c160402c41e134100a034603070300d030701c12a03d4080c4209a02c45400c03500010600c01005145020441d4501d40008030320011500da41d402c90903210381c0c0c0b08036070303000081041c10300202c1e002400e081c1d42c06604001c600c00b080c80d8800860b070180c000302c0308034001c110100e0201c00c0d50081489020710054441c009a4034000302e00c0420700c9107005041e03001d8240750010001840e400d0088061860f1803400502d050f46501820115034214501215000559420303d404800b885000c4140c0f00e014040040070200d0402962041c40072121b4101040c044254881c2001c00104a0b5000428007950040c0031840100986050a40c5803800c02000c2c007040121200c45180c5069000c51441d400141700540f108900b8003000040b030241600c0603a45940041a000001c00c005544000f419002c6c1981c0d400d00c4034503580c2d51003e0072400f030400a90000c1d04a51811410880d112b40c0d12003280e10030781011418140c050311348a107844000d82046a8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 485210692 1250 485209442 485209447
    0xc10090b01090605090f07030c14041203171603020d020913091a040b01031205040e0a060515120c030a021306020a0308060d02301005060f030610030f020d080f 70
    0x801102e4040c0c44090001659419250705001c0054624404001c2003d420141d80b080c20f800907501c1401181c0c450100b02881c1078569842d00072b80c40c801070200303404401090100d1003240c10154800c803001c0c03260f1410400c1d5801040f0300318007503010754810700f43d1400942c1c1c2000014690394404000e841c4289400e0000100c501c0b107840e21550544403643c00307007028075540e410400010010a03000d4192540002c3e20326084400c10340075681402035070442e105070f040001c2000864240ca500c9002100c80440c1d00c0440c0007101c00c0d480d6500d03c80e80301b00c0800b43c03401c100040c92a4035010001e5403c14580d040040c80d162a0710010102c10071a83c120400682024a0302c90a15500080c2d143c0c0003401200c07004a0070080f640050090700180ba8003602001d000011032941d00c0900c40c1e0701e007020407080300b030b100360f41d0f203030700c0c81400505089800701e21425a41982c8032007030030000f500c50301c15102540300c1a01c003400d6844145140d03202460403644410441462400111608041c1102c200603403c2541c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 485211942 1250 485210692 485210699
    0x3070606031109040807060e10020c01090512042312010e030705060c041401030e120313050f0105072102210f060316060e0f1c0203060c0a020d050c10090b01 69
    0x500340b0034031810b400e104030480c10500003c68200c03c1242d10300e5520110005800507a5114241043d4042c018010031503c0031031105800c40c3c064101010042c808c0003961005418a04540c040c1d02680c000c406080b075103000e016446000442c42002c0c04400140300022103540307000b14074295105010521000c3c0c00110301d81c82008402c11210ba0003a4459080b0390800b03040021101d656511000e40604064aa2600da0800c640510408100d00600c0b404959280b80424001c0d500c0100c0030f40480b00c5105503003508480030010b00c201801202c0c030b940c03120380c40001c1d084085006c0707690207078502c0c0c0e440d420021700d440d440103000c0c0c498224800c0c0f01691054a008000c0703035007011004203160300030b400c400140c0702c140c41440110340a54803581009000c21203803001150780344102101c05900450400440e00213a030409881002c0c1034401c500301c03071495840680c440c07a54017490964034051392001c6142d22605000d040070704007030014a403c40c6d459000c003804520581d00c041328103403241e0520b00c0050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 485213192 1250 485211942 485211953
    0x1110406020d0914150d0b090c030907140a050d0201090905010e0105121504021009050a030803221a0406020705010c110d030626010b0a060809101107060507020f0307060603 76
    0x803001000c0700130040d40010410f901080501d404c0440b510303c40d03940011030f614140b0556218503007540d00a03007102c90b9441c007882030740d44a42c000d4070114094481d1500001d001e22101001c45007400d00a00420312045c500018065a460900030403410b00c00103003004a4004004d210702030003012400740c0060154541001d00c000041218040d5440c0d810100001540701040750b4415003065040c2d0310036122052102044235800c05540240340d00000c200700010a0194a1000d1409088030320918556140241700040301c4c680551001800c0004d120800c1038203020851016900034001e800251402e800342c0e0b5920b08444664100703c000c1880014984040d0600700040301650910b814200038145c10f2114208454200c0344000168981001a8983d8be04007908070010444000d0300e41e00e0290f4684001a10025044848407940d20512800764074011403405101101c0c03000321036107407030502c07030351244005000004c0025040d0b00c5202c07400c03e03400d00c0810040c0001e0b40542d600041c02411440c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 485214442 1250 485213192 485213207
    0x111070c030611310b120105030105010f05151c0203040b0906010503030a0e0910030215030403080a06060c03030506030f070b070318080706120605090403030204030605241201110406020d 82
    0x44034040c042409110300801820559154801641c10f01d1440038204103082d08030521141c000044030032010501e000780340c1b10300e924a410785600300c2c002c3c040f50f80ca4140d6510009503030310a95038031002234900c04004004003002030100f280e2035840d442c264625402050103a91041d981100e10290200c06c1001d856000e10516000d044120055841d0111400000741340c9000c842d8900c0c80f807822500030400b288441c0c0300d5440159400390885000b0455002d9840031600111410307404603004600086030310b215413080314140d50301c5440f07080c0c0c6011a61400c9000741001460544c16100c0c2401c00c0c4c0c0c91800401c07082c0c00030211462902d984650394a0018590010008000c403103c03901e0030140064400450300350306880302032900b01840d042d030b40c4200010704000c0e440690003501c42c0044c80f040c194143c0003401500d0240074180306a40b603090040701c02114500c0014003610b0050b08100851030000488200c1d2001e0000100700300d031840c041103005504c0341e48000c000d607001044031103035190000321 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 485215692 1250 485214442 485214461
    0x19090c05040c031118030c030604210309030c060b04230703150e0f07020307120503011d040209010e090a02150712020706050a0f11030c0a0312020a090306020c0111070c0306 76
    0x40c14403051005026103003603401020900190700b170710248900c003162010484c0d80c040400007000c0f100ca40c1041e040001304492800c0f510b002e964204040700d501d450090282001c04e56056403500e014a00079240c920003446040d000307940c02500d441e402e0119681407020303500548000891010301d030400510180031110704803070100a4910102c0c08110040c400d104450f03128440b00503914182d40c0d076203012402c5101da8603000f00182d15040b04113017a6540500a1070594808121104c111011500054440700040301c0c002c0d0310244040045c0010040080d00c5508031000c00c089036810302e400e50000e0301c0d420040081c016107100118000d400e00c28408941e4000e00d40c513002504415041101c02040c0380f0404442106200c0995a0348890a1040e43ca0954014203030060340d460302c0702e4003a144c0d101c41c641c0d202900020318010400645c0b0013148203c0b40254006c3d218107042c5443c5561703510294200751940d403507c0d56113040243d131086030000204945841100c5603001141580761100490340c07501e0303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 485216942 1250 485215692 485215697
    0x705010606270302210706170112080315060405040c180506070c12020f090118060801020f0a0e042706050c0304030804111203040f081c021519090c05040c 68
    0xc0c2d6491641155200e868140c0303030142c0b440810483d1142d51583e240d160f00f00700380464443e900740040c080380e0068140c00c1c82c40e00d0288100f004d0343d9881103174402d0f08440e030000d05510002c0001c134441040f4941413440140340507001ca400c3c50b07030300c01c001412104c0220032a404142e01c6104072058040210b18000985411110241071044d240c81d440c07040300d00f5020308003525031040c4c40d00342596651a01e403090319000503c4041c00d503855040310003e480048100c0003116092007808122035006000f601c82e0f980707002d0000d85c00c2004c007000490b00704140d804041e8200340e54905000310041c080c42c0c507480706040036800451642d22440c0020484400610804502c0c00c18010320001961098420f508a50070001c1034559030618000503001c11a140b40411041c400001c001914540781e00300709044449840076035540b065008600081e10855040e00001038104c01d14141d203564001144a030480c1082c0c14142d0441c03000c82044088507080712040d2100c11035560200014501030241c0d098001d841e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 485218192 1250 485216942 485216987
    0xd090902180607141006080c01032f1905070515010f1802090406080d0908070f0b1b0d03020d0501080d0c06180609061b02060702030706200705010606 66
    0x11031040c4801c480580910612000075060240310556020302428a078400a0b01c0c601410700f010700d80180414841d081c0310b4050084d4100c05036000b441009402003480075604081001a4149142d1984c80041c07040c04907000d0003007010740008480344140e0359800b80c66055613200c4a0600c1c1d842d03d1109200c5080041e40000103214008020f40b015080706c4400c4501507200d41c001c03d41c00040d00800044580040c5064070015107c040001d00301650b8003191541d01d05c01e500d504060344c6030b0395280240000c0c070036180410040081e040300204440c207000450000552000810300341003803620107400b00040e4000c5504250000281300305801010f8070307401400450f5034143d014102d0040c058000d000150383d20a01104d91940701d412460480e1f110320208a02c550600e01040205403101d44401400c0c1c165a902d44800d00002d80c9500422054000310300380740041c2da030302c0c0142403000501c160103547c0741420502c8000c040d019003817080c4503000205640d42450300c010102e070050701d445600c9410300b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 485219442 1250 485218192 485218207
    0x22b05040c290f220302090a0207020609090a02090312090114091c030e03010f020c06060a03020102060a050621060a0506060405060406050c2506030606020c0105030a0c09170d090902 80
    0x82c0304400a0181c5960049a155407801e01641007600540820a901c111448914400607003469030340b0007941d00c00ca52103052511003480c081c0c00ca028051009400407420000422145040d00c03403668404182d5401514201a800200c0d050a244841039940c0c62400305030380486682006100b041541e1042d41241000c000c07100182010803100402d2104654901e003880034980f141403400a100c0000e0020b000b805528a040f86c025402a003d21303d40340948000b158103858078110f08002c42e6016801003903070f40c460a2103800100303400b8191540c071400c1368000c85031600c62120000400590307000500000c1c944500010103840c0020040352280c14100300034003580e42e4100544007551101d02e0100c0d2103181c0d0501c0e01d4030300000030303043c483d200c00a4040c10400d520591061000d07a50240d40a1002555507070301070fa1750714501030525001c564144006640c0c40030b147d001c04142c100600e0040b010a41d01c0807050b000c60320038081410a0b42206642800054104a00c0c000900078404110300e400c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 485220692 1250 485219442 485219489
    0xc03180201050d06090515041503080928060305091b2202040e040f12031103190209040c081f152001020409020310061b06022b05040c 59
    0x81800090500001041000b61820240d0018000e041414001c0240c0d00304072a0400e80d0094100055100e070741001007400d1407008042200040729408507071541460010340400c81401400c4003040c4420104900d101707088540f19203454000e0031551000a62070400a902c542800b0014a101d03c564585541807101603d41c40c0141e6842c004020041d54081c500d08080380184c4203552200284c900070708180b0050014103205444158813900c4426544e08202800f58240d840c03c00324207130011024000508100384600e41030000850983c00180303400e00d104001001c07240041d1121000a540408104103031400c07000800d5404503044c1c2d00a201ea142c0001c5e0b40d6040402d4070581c042100507042c19004c140416440d8015004a000a540303e54440380403000030b402c01c542050001c00759010004000c1d00400f55181c031080e0071001010b006000c1e840742c01c007960254100c10303c800404c00705030071f2107560902c2181c881540600082040d0520b41010042c1c400c0300d811645404000403d200a0001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 485221942 1250 485220692 485220731
    0x801080102090a15020a230f1507030c0306050d060504050f0a050a110406121505010b0a020c0d1506080705040f05060603011509030206070302060906101404020306060405030111030a0c03 82
    0xc0407090941004001d0413402c80c100b020705080100042c500580009201c26134400300c3ca110350b80d140481c1c3e250108410b080fa074a007440c40c84500d2491100b000300d0304491203604419800c2582d82030104401c2c1c0d0380d1001c2030741b40032818030a8a2207170342c80e014042000010701465080b91550030046c24071090b55103a00340c80b20f1104800509420750103030180c2d42a152600030700014142c0450850750750400d800d0040700140123122203400f03185000c00100340c5c20b4010083d506070000c244d004014400b82403090103191074002c401a10f088154000c2c09600f0f1402d400341001502000e00600a960702d000288420303282141d000044050401c007c0000a45519054a0450700b1151080c0c1589002c0c000079145201c207074001030340000c40002d0035024560001110750103405a4012940c06070350b00f010440c1c1c040ca05000700800d848085444584901d03098000e90b0700188000d12031803030181d035030002900f11140340034004076420b004420800840080d11039025011002d05052101300d0301c120300e00a201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 485223192 1250 485221942 485221949
    0xa0e01030b27041e03110106050a030c050d050f190501060b071e030c0510090b060d0203030d0209010212160c140306011203120e061605040e0f0613050103120801080102090a 76
    0x1050b038005414461418041480400551035883c031300b0f859400c004089510040314140c9940c00c00c080041e2a080c2020750702c04803900f0110280c3d00e1400c0c0020406031516100c0d0a0b5481d201e151100301c0703164402d100d4400c0400440c41d01c00300404842c54140e00b5954aa481705204c62414017400300414000c000e00c04003044c160740c090915600e5843e064441142c441c80c00760581c0f02c0e42410341d10f08107040d0300c054240c80c05080d4617081681c609040041c000c0e080e0100a406410030300100309000740580140109203814015100c2010b403040e0141c0003904860104020084542e0340c5506004158540700e000c4c08444920801421204000ca40e40e01d02c103210341c03400c01112034445021705125a00000c0460084281401034281c206596641d60009580c0014400301c8502c0112266016404032411a03461003510003096940f84482000154020300c01c581002845440c0741c8984400d2280c0c030b020758420324000708540300041008106c201c0c141c0000c5030320381c4100003a07140c1d0358810103040b084 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 485224442 1250 485223192 485223259
    0x80d0302040e01054e0307030e010e03150406091b06090e0a06120b040308011e1401020309091801060923060a08030a0905150a1d03070b0a0e01030b 65
    0x80e0f201380078841d01040100b070305c0482004041c40100aa50000080c0100207524100014200145071108a8491040d420000d003c5011a240524654010080040d01c042e0007401d891b046240480c684060401c12a0f0807280345554401da142009190440f410075000c00001ca41183c5080c04000f804032401400b81d40b1b10055488005006c11342030390040005060480c40c2c08610072824074207100c41120585046020800d41400071402032802c00c400c80301ca0800440c24085645808078880520840400a80c1180030400c03060309283c50368440d050059007064401c54060156182e0b640c02c581072034009620385d5080400003201e050440c0e540042100348110060001e884403000243e0303036521580101658000070846c1103501d9080141041114419035004a0070400203400380e5007842081c1c240d10204510b0450118000807542000c0c1401e01c01604652029071101e2810326030342c001c50401e5000030b11100c0c0c102b08550f4140503075405e080b410380d60350044074040700036002d0409080c1400c508 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 485225692 1250 485224442 485224459
    0x2060c0d05100b0a02160506030c0d0b06091009030b011202060406080a0b0a0b1815040b0f0c06040c0312020f0c0d0201030f0e2811040504020102100606020304080d0302040e0105 78
    0x4a165410b0240401410910480780e5940d4410728007075200c036211103940100c100b480000007014104a01128464080f49008901d80342d6800c0b2b500300108441000319400032014005030f141902d51070104480e180300d586444044a1540c034010300c4440d416041056000d523006103003401625140159401d41d40c06080c079505a0b660b00308020010601102015806075011900050605050000b4190380b00d110044203500b400700400e10a0310006458662020041040100080410b61001d0104081c0f040502880c00c800c1952440c6010030550b000d4402d01d00620b003c10402908140088408020340054460b140c034081c03605448000c070001503406085104840340071a84a035102d2502c0740e541901c100302004a40418582e0b441e414180c4450540350075552004c404800d103241c20006600c00b40e20100c5070202c400340805418085c000301d0641c4105204003c9405245c090500035005075802503450f207191000151614811660313280c10305104100500c000000d40c403415041d290180d94554 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 485226942 1250 485225692 485225701
    0x50d020609042019030902032104180c0e030a020112150f0b030601020f0f03220306050415050c040e01050d080715292d030d0201091202060c0d05 64
    0x100540f09034105100c5010f000d403a0400180014406402003600e540d46078100201c0002d0250201d5426502c0a54141d0042d28080c010149030844000c0f5030313241e00026420599201c41c1d0f0201e03505e4107184506419119001c084183e40e11040c800c21030042200200619040740d0006452110550a07280c0301075120b54281c03401d818907218010090010203c48801c150365058010000e42054407120b0040c050442900d402d90303000903003003a040d0f40c0b10020b98070b000340c1d01d0f192071000f001405001050710603448000020407868420390744920300841802150540c00b021100803900c004140d1184441c040c0010f00100700d1100380141516000d0302c806e45080110301f800c4000d0301410b50014000b080300d4001981414903900b05200c4025116840101d15404440c05240f07054010f0340250007010005417801c0b20311741c400401b030300454503044189440c0170701d00120703040000c40000700300940e45442c8800100500c8131280440c42005c0e20241c0b0540c1403110f4812054800d04210030906501c83c004503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 485228192 1250 485226942 485226949
    0x60d0c1e0206041e0302060a0b0a0302040905010f051f140609040c021e070e0c1b0d030915050606030105121c0905030d091404092901050307060504050d020609 70
    0x1000642006800c0e4030403040c49000095039408112021181c00200c0c0c02490b00400d400c05001e0320301d85d80350f0081c000300c3d5290864100104200380005a001e0030b4400b0020240e06c60744a9051035502840004c0b41c2000d0010203903042c2d0b2006011000c1094101011000700f411a544800c2654000300c1d40c04040c01e10040094030034018840325a60091410840108450700044c0540340c41000411026603504001105900c1c0d070000c1c891014582c880200242502ca0444d0081c024190410000c031001400e100c0d40030314000200107181c0102c0d82c4ca90b0102d0034007002055030003001c0000701041c03005107071040c00700300c8038041031007400d008003816141c00130704000511802c42c144003d9811803a01d26000c00e0700900d445424801c060003800340c2c031800ca0480d84a00c4003c010f0343c04030750801140401c0202800010402002c0030750300440800348809000901c2c2005000f090b900d9076140030b140d41841b0805040c01c41582c0a10240141004100265140c4008040d5115011100c154450300c004021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 485229442 1250 485228192 485228207
    0xc020109051905040e210c030403030e0d050f030405012712140303040b0105120303040b070f090b040e06040605010206011401260a0f05060a0f031712010609180209060d0c 75
    0x1107501c41c4c100718409185c0c400000d02c00704145640e4a600011110340301d025040307840303444050422908100710903c0440d000d681c0e07902c0303420700c0030304041075041a03529040d00300003660307204901c2a080020200155a0b00150940094440366040d40f521802d600d10072640c15160b206c0c0c150503a90300c0e5198003e100581d481d16011404202c02c3e80c1d904c1c9080c2c9040c40c0c002d082400741d1403003510f20106008140e240001501d10455106101c200213803503400c41a10a000301620702c0d020040c0040001c600545c40c01c2c040c0c0000d000c0c180403205a03085c0b00c010003081e80c509401c11411540004010020030043d20f901a010910a0818036120030b000c090100e840c540c1102030b050305034908420701c101040a540280059010755401300a191a48403c00065203501d12691079104100b80c4107102043e0800c560110143c42c140303903079190441646805028020980c420b0010610f0001d0400c000444451660000419600b086140203003e5001522034003401800140440d078070040302006500a529 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 485230692 1250 485229442 485229449
    0xb0f091602030415260402220e010905160801020304050615010c0f050303041a090705090a06050301110a140a1218050601090f1107080306060706060b0313050d0c0201090519 76
    0x461113010075000d4007822400070041d01c1c05414458148842410141406881c015076009042d0031000d505014140d003034900c0d115109001d02c0c3d94004030110341c0b80034031462a82c0c1d4401c2000d000d14403c01c4d4045003007101268807071076180e40108100300c001640410300c2da5000c080d0360304a45c0e41000040040f203201000000c028050f0782a500100b0500c5000030146102e107208034106058040c900126101522040c0d034920030603400f5040a00c040c0c54908a050b40c4400c0e000000a1819654030000e03094076542c00c154102110001407503544607a00c130b0031062090031400c610510301202088010102442414481602c41d0b94070030b840400c0b03004411803450030703400c8411103196586403d078a20044c160170007e06519490652184204103c040035143c510360480074050542e680c2e14244841035000c40c0046417201d41d1600c01281405031000550b019204801d46c0c1c107010005403505030b150205050303107002032013109545500141c0c0e001d1b001c8010b4400035204007041d101c442c0c40001020b501c070b40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 485231942 1250 485230692 485230709
    0x90109051e03120d1b0915110d27260f010509010c0e01030608030d15090204030f060b1c020411040f1e050a0f03111201051503010b0f0916020304 64
    0xb44444240f000001c1d00d9400c0780703a00100202143c282c040690084203805010200d54800e5040040d1869500410030451040c242103103508281c2e0300150422036441c0c4410042049500c03006030210555040c0000d1404154089030900d09140d461b0720040b440b000c60481408810115400d11017050100b95000143c0200902640c101803002034060100d0380f005800060152184003141c0d8424091003085400000c040e51600d00c1c4110f20b24090510304020b20524220998006031624081c8010070080d40100b20420b003140c2107107400b034282c2c0d040256480c41015070580c403140388a0000030080704180c0c101c0e400100002c9008006543d4020f9078080410800c500000044c1103c00e0103e614002e01070000f4040750075141c600300080c3c40141c0c021031000c50b00c0c001e400d00005503403049007803d00c80c008015480300d000220819096030b000311408100c40306544454801410240680c070074030502110852030900514012030600140144a00300c0d0303503001303a4841c1d405802482202c010b80b0707503030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 485233192 1250 485231942 485231953
    0x204091401050a05040b060103060f051306150f091205190501061a040305010507170705070305040509182802060304021f051903180209061306080109050111090109051e03 75
    0x10344040f0001c0504407004d83e02c0c0840c5400081c1075610030304c1203005440340e0b260f2982c0c50a0422040c054054405031401c840143c0d20f01c000302d140701c6680c8152203502a01e81c1c45040e60a003100b0b0080a0460035070080c118a81422402c0b80095400700d0f95810b01c10360707001a941030900a0a00d103014081540c450502041c550700c0548902d69000014015a4012030090080d0b480d1000c0c22204442036884850310310318030304081380582d40b04030010311030340340a07152040c01c01d501c61000031501101603800b2040a40712810404000100744a8940104904511004500b0351403150318800c04241000034440d4100000042c21035980c0c0003864060304408100c92400a00070401078420742c842c03a6040b0781c170030000b810402064402d0142c03412041e0f01e954801002c3d4929400c0c02056100505103644c0b0500788407841064101c0b03849002c00800b1560700215000ea11410500e003103c2000c0000341c001d25007006030703040c10f9800c50340e408100e400580348101c0440740d050743e03d8101400300300c0340e0341c0c940601d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 485234442 1250 485233192 485233201
    0x60b04060b0d140f040b0c0720030114010503031c0e12030f0a060302030c061b0a030e010909020301141c05030315090f0603060403050309070b0715050c1303020409140105 75
    0x80304050030181141c04810000c1144800340f0004007003003164281c09042101d000280000c1000c40010f401610520204d41483c40940d16015035902c001c00c40f24441c0382c401400c500d02e140c24041d0f10381c04002c4108250865040402084c0c80b482003d1030095180f56803401c18480007840c2d030061414000440c00d451560303403512032148290f032050312440d225030041400b10340705003c14403603801126070080041c030803400841d0510202e0f8016400341d03482802c0118169065460502c02d65216601c2035032a1200040c500b0005484c0f001c0c9500102d40381c0d8414401070121100c0c0070411100f122044800c441d404a1802140410702d2410600500a0102000b44500421400c0e070131180b070182159004480d0343c0f80a111460a5001c40e1226856807250000c00c0109005100554200e01001c05940025494801005103a8803494046410040740900100d0f02c20451058541040740300f8401c03480c22443c3d65551401e02028007000c0c1c41240d503840d00a00b04250000d00d60401410b0780000d0049181 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 485235692 1250 485234442 485234459
    0x9080106080706030e03040e0601080601030e0a03020c0301230423120903060705031e071b0507080d0207030309031103010b15031b0c03040e19020c0708070f0e0a09060b0406 76
    0x41c4155030202c1d0805e501e116000602105413030a550584000420035603e103401100c1507500036148138141a43d5604081011074240800c4c80c08034040c0d0024451b007801c0e4810b041c219820540001c079107003601d60040300382c4030b8a504d080750490b40090308102d04130061410b010f203000f44002d8074181c51103454200c0303107021031200240c00d22071000c5098800e01d070750b4002e060700d25220072610351103500c890f9001004c007065495a2107801280518140c80e0a4044c129501c541a041402c01d403401da100e100e0130007a4110400c03100a40441c1480035000382450341d90080c1c40d41d075503400001c1420103480c4854580362001d41c1710f04114100285008109a440303a0003070055802552141e00f0991840f051824011940084440040c40c20f001185401d00e07080600d54410805054801041c90010b15040c1402e4580068204d2006403c05401e0907803a00c8092454a0702c2944000c400001c6201b0800c00e85492003691355011064a001043d8101c161418000805190b41c01e01d80c80391070190049408103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 485236942 1250 485235692 485235703
    0x312030a0e1504031d0904021210050c070605060f06031b0f0d0b030d03060b030c0d0615030b090f010f060f0e0d0b0714030c0702010507020112020301030f120c03020c040c0908010608 80
    0x90098440c00b54401702501111203500700c0e680380c2d607086510312011078014100308240b80080040c0e0300a803840280709014102c02c3d10000c1e00d06a604a8010480d682844644e01c181038010208070381c410343c1450b00d0002b003006408014512000300c2049e0440c134551096810482d184201c40ca60025591707100880040c0007400390555040c000e201d1040d91100701d5010384074103c150740c0c0340e6001a00f19070702c481440341542e0248070803000403031b1122400107098040500c0c034160050103440c00301e02051000c00344880a00300824580130f00b10b145c00100880c4840001040076184286004080701d1101d070425a406104840160740125646002c08180049850b109010300e400c1e03900c4010440e0882c5104189020650701c42c0e030803c0081141100560244006200540c410f05051b010043d049036040200d070000d90003a1495080580ca220801021030303424402e01c00181005500302145880081d5110019203803035000e607589803804102c460180010500614032000288022500d80c40e2039a1550b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 485238192 1250 485236942 485236951
    0x405070608091603080a020c030106032109150305070306080f010c0912110f180a02090108180c0904080d020406030204140d03020d03110702181807050312030a0e15 72
    0x18004004950000320229002070001500f0850711401401c58440f4517a9502102e5204103600c10368111004c142c5082c00340f10021b5009240410003101c8541744401300841c002c0b5903408010146400f40b1100003c440441000a80e0380360009030341c1e40303a900980c020031f16604558191702c50010100c0c8564015006070007000301070740d581041d86039504a802000c5408000042c005030782013612003141d00305580703800580540100324003403400038804000390421055800d032061680028000740c06503000ba0540e90440d2a4803a1405a9000110f00c0307501c40c800c1c00c0091f03100e072000310302090511004100340c5404966011003199541e0751018060f00135842072244e8007c40368943c5d18456a80f80004800d8821600740d0003030300c18480e4880d009c4004203000000709010f210b09205c04c40150310ba000000345103e00e00d0341c123440603080840f4020407101c407040c9888260303072091005101d00c1d02d003ca60354600702c4c41158240d80365226000d0030005002c03030349800d010b0784c4034811044171140e1000324040d015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 485239442 1250 485238192 485238197
    0x4030c110913032706180b0a0507030207080307020f041e0f0f060b071703070c0606090204090f3c050703050f09010603080405060c011e05060f040e0a0b06010504030b04050706 77
    0x8400607213640e01d1101085284600004042e0100f0881140220340b03008012040178000c0a100340c03a4600c4900e60303001741902d000003480100d00b590425404010540241401800541c10441190300040b0000c81a107080c502603a1603440c000c0c842d00b56130085010741c8041400611400c010100304a00030803000603130030281030030000c0010300b8011b440104c07481d06411074013021000c0251181c1207a00c1d4005000003081141e8200340b80701103042882144043c1c100107a02690321850f10f03002100303440c1d4242120002d07901d800c0307292480d600103549540c424880109849107030004981d1014481d00690741c0800e40f1800d0104000f42240e00d607205900c00d40c05413070150196180c1607026803ca60a5000013031111404200612041c1307000340260115450368800810018040388070b502c02c1a4040c18200c0401e0f80b60300034840b4918140314540c10504098074200100341003941c004d41d403000d080c10090414010301000c42d10301d0340b05801300c2e40515000b68680295007401c0c81c0056a64a0502c41ca100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 485240692 1250 485239442 485239457
    0x30714030c01210c2102120702030a021f0609020408030d0e030f040306050c07060f0f0f0e060109090f210e0f01021b0604080d030501050f011704030c11091303 70
    0x840d5800741c40c00c1c40c204400c6565800c00f800380a0f038840010214501d404061104205420203c0c007456584d03640e02c0104a01c0150721060100c01314980150060221410b40d00103101e054991540014001601281c014029003007507241390b0160010203483e041512264000a00800d00807000001441c10304002842040326081000755035860f80500c00075414034440c2000304001260460300056007041326802c0c071526000705030341d90404681d000c41c0781c400015214440003a103070303140c0c0c03140c05040d005551061000c0e403542038109403100414018082200e9543c0d40040900c42e2121602c2612030703100c1d1307500c0000a0410300702c191601c6030207000e01c00501310161100359800c14503101c6040e40010b80042a05806038100152034100c42c1d688030760001018000002d40d0a000c010b0540d9a54440c1c41c002902d50421042c0404440065039107414400700c0c01c40d55800d941205035040d44560907140c64035030380c5213925003808c51140c40344030150300200e401c0511586c0400048801d40309840317074441e1603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 485241942 1250 485240692 485240713
    0x303050715110f04171204090f1b0c02010f0906170c0f2205010302040515180a092f0a0807020118032105100b0f070b0f071403010b04060f0201090203071403 69
    0x2a03171100103100303101000c00181f2041215a46540001950f400c41a4012840d804500c0b4043c2c900d5031b03000100000501500ca032a01556000030a0443c02c41141c40c0c0301c5501810b0080251405807254030352019040a54006814481048195400181c0c41e6a8142e614100807510544250726190091018407030a0300000b030940c0a842210102c42010b0200074040c16425084c49e001d8010220b4401561620201004507640340d41000b0085d010900001500c4440b40e441c8a4615140c140e01d003007112070310408010b2900304102614050b108500d40000c603540d602104a0142920350701c1c0e5011a40101c0c0c26204040c1c200c001012548000f00c1c0c1e01d07891501c3ca2460206589007900c4021404910030014001c4a12003402000e014030108202c6141c0949651100b8842c0c400319401c200b080c40210600c950668410707a00b40e81305118dc03e0701401c4d035040018a580d140300d17910030313540cd00c4403205516524074000c0d08a010743d541c0081c166203215035960314040044081c0c40441d40b00340103441c20341 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 485243192 1250 485241942 485241989
    0x806090f0607111b0102191214072a080703030909050c09010815010c02060408061e04111909020c0705030705030a0503120c04080a0501090515010303050715110f04 72
    0x16000e10300c090005012035520b9004d852081c0e1402c21034941140503000e80e036600d0741412842000018031903154113440c00b41041e401000440c1c80d144035110f05904101c8800850b030400c0154100703c01c1864800b00c40c0c01c0e030b944041064800c650100307400d401203a400100389178000e51b2510403070b001d40c0000e00071940c2d492140820351250700c805c140403540341030100368000000c02d120404650181090301c6105042e4002490f590401c0e40325484e90f031700c100c08004d0100d041c6680740415003065030030381001d0300301035030382c180c181c81211071035406031812003008803031140000110340c002c0031071290440d6240f564202d06a2522018010107000b8410403e00040505002441b2140c1a070890051414400399159116007803001906800001d0030501000c56205c00a011408246202d10000601e5420b18540707241800090070040000000220040002c60b0300b1408440300310780e10030110f00290007211040c00c000d29040409041c0b021020840003500611302d00200162814100c040e800d80c007444260 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 485244442 1250 485243192 485243207
    0x100b0a060f0807030f09050f0c0108010503150901020d02070b061915030e07050316030303060f06050304060e010906150807080622030309050d090504050a050606031303090806090f0607 81
    0x12840003440d00941c00024510540d10190800345904d00814100c0903000d400c001d41c1c518a90079180b0744c00540132188401c100700002d840941080c2042207080d07240400094444a4240d11080752805090010709000c1d4294110740d00d5001104045440e4052030030501040c420440b000c2c0d0060b4002940c80040c840082da81d04122519503509003000e006014045000d007000b080c04011506c220500070074165028020034010915130038810709541e01e103080040035500a9840000d40a44001c4281320007a48201285da1242c0c10240c041036103210014100c2c0104121130018209916000700c100d1007144940e5410200c035089400c5801503901c480007141c84400c1074900c4402081d0307914042c2c0100115100a0400341d009050018030f8403116140c45081443d8586284001615041c06105c01e2526108650300603c00d000308000c0d620348140410300c10300c00980601d41654280b9510810580301c0c0c40e445002e0450f50054407a00e040180341c0e04e94950313800183c40c900e40907400001d1000d078400c441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 485245692 1250 485244442 485244449
    0xb160305090a02212406030d140906220f2303060115111009021c020a0303030e0c130b210307030804110619030608010606080c09061605100b0a 63
    0x1050780c02880360340c03200764044d144003a0942806104c07402c0640d410442800030482c0184d10044100c0c1c50703d4400c0504004400b40320b0f000703004084603824010701d04007059443d00751003540c40315982d43e0425004c051a0101c1d21080c031003200001800b00d1a0b4241780c0d50030341221400d090480070181d0104058000e445560081900340c0e2103500108542a014100141e5110503070803d010020f40c02805d075810826144150032a0b25243c0f00b0810460404400c443e0040a54030041ca80d905043d60000b02003510b184409001c040d00d03000d02d030741c004009100d0942090390040080306541540e03032101000e0400d00340e29901c00d445404001c0c010303e044070200360307484245001a40c0b503d502c0d0703501503c1e44d100140040c0d400c000c2d00c505040702912180018040071440410750015401110001000d440803071304595116410308400300040c0e0381010302180c2110103506019140d5088170302248090003250321402012005a014005010010491034106580d5076800e200c081850320901400030312921 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 485246942 1250 485245692 485245699
    0x60306020c010b040f02160f02040e0a03170a0e030d090c080a15060e1909080909090307060e030a120f09230105100e0705090102070b0f04181116030504030b160305090a02 75
    0x1f030800003131200b0701c1940b02c65100400002d032440e00004864603012000000700e000c1844001020040c50200b04225400240c400c400c0c40110704021000f5100d000300116818040d40741d459080401500078062000b07480028101c030b0412000b410041264500300f0000d45c041850514049000840c403240c052282013405071340c01c5003050000408004040c80842940d04800900000003103a890382c102c40d004050b410000d54854081d414050103c0b5500c840d250034990081200b900e9041c0c002c0003005905418440000c1c0032124031a0745e901600301d158000385250040501e0102c25042c820421101c1007c8070002c0100f40d4580440b0340032110540150008040720500144426128138020803e130803041c4140d410315031760b4200c0c10030950008a00103c40c0540406d041c40080c00380da884204030f80c03c0d00c1d01400426a107a401000d00e119040352980b0071441d0383e455500381070041c0c0840317008590120494246e868000440c88512000d400041d00007810500030944507580010260303101500203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 485248192 1250 485246942 485246977
    0xf0e07090302010e0d120e0a151e0c05030313060e0f0c0105070503132408010503060a0b060915030618060f041508030c030a140a0e21011401030615080a15060306020c010b040f02 78
    0x1300c096010012b403140c0070404011000510780c00107202840514060080020240c0c203002051400030305403810113071100710f10b9004006010030070303d000039521500a400c0c00d0496403400182040fa003184519181c0040d0307903d40c5040050365088010590103181c04000c908660440c40280440b0258020300c034080d4158408004980700c042143e03c440c101d440000c0949203815410701c0417840d8000d0000b13030017a00728004010002c0c2404c003000f550382540029000800d2a00d86800040e9a02c03400243e003c1c000c641d1169241031501c1540420406001403108884e1161031549400b5526417240b13104a001515000f41d040c8020710318030648031120100c1e100d111424a000040c40f8000140c0400702040c0302c0358801550b4034407803e102e4010880c141101c844c1c101d6045080060a544102a01c4915000205020400140082001d60200754428803d1686015204040e40542065000070388203501c002507881d02084154440960200300f61801d020310410300030700608900440542d20f0080415 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 485249442 1250 485248192 485248217
    0x3110904080d110405030d1215060c1104091b05041505030c011413031406060d080f0a090e090a0b07030612020105030606130f0f0e07090302010e0d120e0a15 69
    0x442e0000c595210040f00d60301d0800d0740e01c4c00000d1403c07626401d2103005ca4030849100041d161503000d0901645a40d500c50080d15150a000501031114010f020b480c84542e400070380e11039506c41c0c114201d0160804441c242360311520051000820061185502c00c41c0f82003103481e080a480c0d015a0302303c0d20001c0150030940720718001941e029003600c220800981c8200100003071407819401da80080d5000b1481c0300c49503041d0402d918030349100504442c2c4282d200b5500c042c00038281e90129141419801041c540780d06404100f9922100e4941024580e80000e42c1000104070000071981c0c10f8900525a40810340c490100030350032200c9900540c030020703903008040001355025800075500308002400082c0350600706c4040c004400d055400000382d40d50340c8502001070700302c45581000509902c00b8018003900703084001914164052000a0522410644c64102540e07400c043c0303240d00350043c0c1820079030544240c00500024990700501e00c5460011800300701103042c034503c41c000c0141512145c044140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 485250692 1250 485249442 485249467
    0x3191d15030619090617061303050c0c030a1101030b0d02010e061c020a0306030b09070b0d0b220507140403120e061c020a080c0310050103020f0c01150311090408 71
    0x61285800000407060480c3c000c500400560080c0b405103400a02c990409000001c0340400c860312544662295043c4540f280300660080803059140c20842d0f5641108000241018100c0810a51500500c948402400050400d440701c2c4842660f003000100200d00810040b00394030070010b400142ca0050700004c6083c03a80051034250700c9400e8482d0084a07203480402a40e12003500d1700c0003c0e4880c00204200440100e4158000d60080080e0a0b21414494100c0c40c500500d00340448180d101c0c00c0301101d41e100c0540c2c04040034404004a80e0f80451207035180701030881591450b0005a82c0d0040c0f9221040e03040030784061300e81c040444030b031501422408aa106d0310300f649441d4000020000d10582451460000300d204010100c0980c0302c4114000c09402c0000c02004a0f9080070304000304031800b51506c0c1e0f44005d490382428010384502034864103610700e0049144500c007941c079103103041c1d403030149042c0d441040b2403064280d0341404042c802440040d201c29500288014001c0c4580b991009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 485251798 1106 485250692 485250697
    0xa12090f0303051b0f0f0403120806190b0306090a14070c050111030c071506091e051f0909170a050a020f190611090303191d15 56
    0x28004104c50340601c910580070394400c5000400b1824251684181c0d0040c6400100c2c030b1110309140c40c406441c0e041e041d1041442462251010094010301070750a0003030f40c1f41002c3c910b00b5034641c90b042c0900884060001d07108180c9440701c00c010400b000701e40900c9140720f40d03150b139040c071141d04006007102c18008483d01c8240c420810020303150000c2c0116803841c0c3d0b120200c160040e0300381040c50000c1400c0d400114086082c001c0b14229803119171180110313521400c00411860b203e00450070181d40c1c01070048002134101100401850b40207601044001d170207544001100280c4401401c100c1c0e01c031070f0001c0089600440c0d04042241d04210380c080365450200100b9a81840e00c422040010011800412603071b168001103824004c00c0c1305840ca80600541241d8880030003540b026420108407685100080c82c103a54030b8540f4000c070b03000031200f03100074203800206280d01011604a6 = true := by decide +kernel

theorem cover : BRFrame.Cov 485071942 485251798 := by
  have h0 := BRFrame.cov_init 485071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 485071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 485071942 ≤ n) (h2 : n < 485251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
