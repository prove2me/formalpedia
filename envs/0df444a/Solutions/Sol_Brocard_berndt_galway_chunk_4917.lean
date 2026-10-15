-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4917
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:09:07.431042+00:00
-- url     : https://prove2.me/submissions/a6b5d17a-40db-404a-b5b5-fbe6f4aacea4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 884172661 ≤ n < 884352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 884173911 1250 884172661 884172671
    0x210e0a0f050d09060e01080a0e07050a0f0f0902031018150f03050f0604030206070f02010f0207060603021c020306060d2307050a060e03071707030515062106070503091609020d 77
    0xc00142c07800c0048014031741c00a4001800603403041c0300f9510510846605804032400c0503103407170104010404a4121a01c1d0140c6401d0400551841c05407032806004200780075411410032012994003001c80f401840b00d49040c000f8000310b01506540040c000000036500c0c803000543e00c00104510200318041903640f07001d5040d5001c121040040d0342c0e805981e040d80141880d55601c1c2c0201e85000300e44405008554803900100c0d00c0e01002e0014200c21401407800140982c034500c1003140c00c5c809000800202d018004941c4056a004564140c0c400000d40b1102c00d090710713a2902101b500f4800c102d09400403110440341844020000380c1030240c41083e104042c4250319081c06481482209040950590043c40f040c04031307171000880c54a20180c0b00d41140e440540383ea480505141040100c2400c071f81800c420000a450105405008140c4072100c548056890b100500d40364400181440c0c240100003000c944003c204110030b00b00140d0300a001a103050b103c514500195020310900e40c0028288 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 884175161 1250 884173911 884173919
    0x513140d33021c0c1202070b06030f0a03020303070e0a150908010b04090209060609060415080a060e0402100c021c0b040b2d0c09090a020d0606210e0a0f050d09 70
    0x10700c00c031480340c0301150403d03090400508504028108440d120341c01c10000d11a0b696141c1c50300d00180400303900c10150f02c42d9510b04541411314010103800e840c0302607402541c110b00401d40100c110384d0070203101c1c50040b0000708604d000c50040049640841a100c9041052000700e507880040a000d880070100280019100c0c41c00308820f50b0183c0101940c814000c45c00b08101e03291550003004171820241600d803c140d0707502c0495000880345105040490b028100700b201004181c411200035060038500140030b030805402040309040d090000b401130040740d205003c29551512408030b20642e0b0000c1101c1d00005501d41000b000307034190307130440d4071120f960302003286199032404185e4002105085101440300c80714040304c40c958003a020f00d05040c0108545451503d03000340180c46006240c0000d0303036814030640c142086035004c0d4030001c20402111003044141c4121410040b038001e16140206440700b04e4081e49040c6204014000e110300c0d0041048003c0010100e01941040c2c003d40b26115003a6407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 884176411 1250 884175161 884175263
    0xb120606101107302a061d2e0816020a02090411030114092b03150b0a0804051504050307121704080d0c0513140d 50
    0x49030190100d50300b169a09100b040a41304a40342c2c1032005403c4400100034090140c00005503070102980c54280412407039403002515254003d8010103a90320104481c03600b40000c0c68500c1ea8042c40014882034051180c2c11703a074041c8036007000804050312140c1e0440700164100000c040c0a211004245144009100c0c40c180e218020140c40e541d0b00505620b00b00382d802c0140382c0c18005c0040310445440c201d02c55190320248182d0024040c4c020100542d4102310319400d26201c940042003604418604442204641c0304401039100c944038100070a24070b1034520074000c910820f40164140d5100410340c060015031060b07080713004901880c25134426407058800e0182c42070b000c807070103411a8820000343c0d00046850034081c40c00d040901d44150140c058580320f000f119016142501c5034100421321001040c3c07681b2400e02c0d201da160030411303d0b007540340f20300c80c10b155080d10499102e1180103500c3c0c3c00303075101c282440d020a588441074010046d000d44110a681006030780c0342e821030020318403035116084 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 884177661 1250 884176411 884176427
    0xe01050307120c090203180109080a140a3f0902040605010f2c1f0306080f060f15120f01061d060f04060510030b03010e070e0c0a030b12060610 63
    0x83c021100c8440b043c00c014220010b580003500d002d0f03d00e0080b092108802c0828482c4540540c1f05002c01d030380d01c1c01c9030380004100300d401003100c842c1003204000d040510703600100d6404806030303a440412840040e00548100404011140c41304149d500c558400440d9100c0d480340035060b1007142c0c10010b140d26075004580d8501d001d84e2500108210700702507100c41401c041212082c40318042044001c161160110700400303030315050011400315a0b100d03048500e415004640141c01c000c00201407440000300c14990307407180a01459010140103001c6808902a1410718460100c007400700003000300d0005206607191074003000e91485500e400000304429080d85034003013405642003440f030300359108d4404105040030310741030466100b070341c038440011a52a00d50752504514015200003480605200c285402c1d030700c4511911700a504408020700a901d25025082c0d000148611203545441e03540c3e80c141c0082400c08006a4441407000c1c401c4000100090707054031520060f5040104440c1014050311221 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 884178911 1250 884177661 884177663
    0x120906140c1207050306190801020306040b03120d0b0a0801051008071a040308090111060a060f36090b010e07120e1209220b0a080a030503040605130c0e0105030712 72
    0x25540c2c1c004500e0441c801d4000d5034000c14010041c20710103501c2c86038102020b100780e2052000b43d4010042040d6032406d0301c544c0070f20200c164080e203413001c5d000c00c0008031b902c0b580c846e24a142c0e9a4440081640d207509400b00e01400013200200300b207042452a1104103c01c5105a507400c0c8140313480810a5011034074202071048802070382d64205030855941c50140e0f04407281190410170801d001200d54842000f69174010068800e00180c13a1741050000c804814082e048607141140f20b45540c041d1404201c2c4180300c42481800784420502d405120788050800c03900d01401e40d00320325001103001074072442c4403402820a40c40d680a045506c0f032058096a4444881d01c8980e04041a82041e54000600402ea8142c0060a40d6003030f01c599886861585034040110b071a403692040081703102d0401c000c000d0040c01100c80100420400ea5030000c1607403000400080c41e840d103800109500307442482400640035030200041d103003641c03152a08020400c092040b01c1c82803003001c1000480c1c1022240d402d07541 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 884180161 1250 884178911 884178937
    0x7020c19051503070c0c3b011a0d060605090f0f0d02040507020705061305040501210204020d0216050a0201020610051e12030408010c0206010501050c0604060903120906140c 76
    0x40900c6100054454000416003c05d0044c0d080010001502c81000580030b80f00c58140c065920a0030103905540c078800e11018040c03101c1e4a131160144056102007a4119112a0302c5000c0300450000b0481e50340c002c80740394040c0142082008580d40307410002807c2448015180204400c040d4030410031f529500d41807841d0049264401d0300050308142d044554840342c1c60040b074086561b1034010820395404408a0b045649081c0e03418070071403606009450040c05e440d21462028100400080c9044400000c000e2040740d0002d6260ba00544680540300c8070301030ba2419034528910b50030f04a1311040240c1049005026850004a00110008c854800e48001a108002c05810204001010380c2038001d410340c821f00a8910104400d001c0008101810580b400030800720041000030f07242c0201070300600d05006052122800c001c20015045500c103030003080210b408502400e00b030b40d01c2e81202c0c280610b100d041c03280b41420702c1440e40180c00f5036043c44082840c9a03440702c0359465580205824420380d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 884181411 1250 884180161 884180179
    0x1b030b1813171b0303061806010207060302161707050721030315031712090703020d031b080f040f0b030405030703210f06080d0c0203122107020c1905 66
    0x100c1c0c144407502c601d12491800b51840d00100407002c0340c01c43e079222403841c415072000040244c0c5080441403400450010b48a9a8081c2030020000c0c0d140d804500410080650108007944182e0030502241c0140c0d0b00720100d100004044001e50700540d102940c1695144036650f0002000c282c4900d44801d00d00420519110300340303036560100e02074554940000d62002c64644007002044100d0000c1410102c0d0030ba25a80d01d41c51030440003403504006201400d5504205400c00c09030b10b0740000d207210300d0340c14941400c0352203500e061040c40300c008030303405040740c2004107000b654440c07050018829244121030010320107a0320390889045200486008005400c184020347c0000d00501e29120300c07400d6101d41c0c54444500c0715001c8101d07502889200079054940700104020380d814480d52080110610740401910386940100343e469540317041002c2c008100281107100000c03408130f180035201b06080160032900f001400203648006a440c00c0d4460a41002d40c050304c0d0704c00da01080d0840d0006804000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 884182661 1250 884181411 884181413
    0x3250909020c031c02030601081b092806030608012004051210050408121e0c03060303041802030a11070c0b030c070803090f07061d12011b030b1813 65
    0x81c0d080200090b035284070501290a280410100c1011030640500c40180c81e4034201000602d0340e6400380c801c103a280f140007014a01040f2440807074070600700903140070b00032000340030007000c007803040744420004600038880104e003403a4076030401011a12400d0003817118003111024100e800c13014420002d0034074010003040001e070601143c640080302550302545c01d84000f9401600940703000300c40490302d0220000e2025040e43c03c805444e0380000600e85220090a40320090412015001d1b0003842d03544400300c0000c0c2d00703540400032140035050014061b818402c1800c082400b940042e00d0f444800360800301c05000507188001590074064110401100e035a1030241607200660001c2c0543c0c0100000300001804180c4010045000d070600f54003c2001041d01c402860074091190041d00c204500c0060503441d003c070b2140b40c480b4407681203a401c5225501540064014218890340c1c2811202101007410007030741507880032120b01b04c29101440082800c03581e004805d10304850080411480a11208c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 884183911 1250 884182661 884182679
    0x3070327031223130302030c06010321030e150a18050604110f03030f071505010e1602010221060f1513080313060c11090a06031b031713031502032509 66
    0x1341c90302a0050780d03d0b261203240d0341414207109030404c0c0d45507200c6400c040b0390021660155030604025150030030000203600c468644481112444140406200c00400c6010300b090380400c904900242c020385414072145003e9448a03400c580c1907aa100f21001c4800050404500d408100340006000d103103040c8294018aa444d00815003c1d10000c00750300e1858501586481641e020b000c9c2103d140300380d48cc0082d01d121301d002860f0004011039006004001c1150b5500b1406102032020750400715490f600c1a0200e9840800c0d00c0d2125031010b000300f00c8025200c5a0002003403d055010704580c1d841c0d460341c001990341d02c40c01d9035415030084031400402944e0b100d0401c007a21140724041c2208040540000101e09900c03d50f0700c444519615801041041100e021000030900f41207400700309280b868991910440700d4a9590541c11030000c2c80c03070b0310100c8449140000c3c0d640f000004030b101032000b0f0000c009402c2151a400001d40300380840413034450540400b800c0c80324540d46e460300305080451203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 884185161 1250 884183911 884183941
    0x3010b0a11030412110109031e02130c030509070e010e07050d090c060f171510181e080f0c061309050f0a110f03070327031223 56
    0x10200301d40d511030450804018801440105842c4500c00480c10701c5052a028854003100928141b2000c070101300001003543c507000c611600e040300140340c90324507800490107030898020440e410f0b07840c18040000980c0c01d580110b0081020300300b2030308440c6e00d80d0143c1d5921002800742004070162500098004c030310680082207200c80b500d4000c0f402c00b0890365050100b000076040030002ca01d941c1043c0d101701e6486a03650381e50390100f1585099a0030b1809800c1c1c00203c0304c0c8559030084000d00b140549031406045818801525100c154402903601c0420000c0d110070b040c4100da50b41304030f00707000615120000d041d01c40709036213801500405010604001c02c03640081c034120805142c401000491884034410148514030390740e42104213141119079503040303d00701d0100609a20b8140005080c00902406803640031045090014064070f6400e1044181c1c125030403016000044d0501d9403007015070000065440e905404020f004418628003102c543d00c0c64000c0302d840859841d40058560f070719160b00c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 884186411 1250 884185161 884185177
    0x9030613060b033c0d030c02010f020708071e02120601081b180907090f05222a0f0305010905101a0f0411030106091e0302131a1e01170c03010b 63
    0x80da4840302c004ca6240ea080c16819200790011035070318540c400c6041d8081c0181c19904074214002c6152060a40e03a40032103008103080904910160303102c4850480e003042c00070521503002000d002000b5440f0220b40d41d00d0409004100d018000c040c40d24292003801d04402d441c0941c024007481c00034400f41000000004010101d048038440e102c40043c0b00c0c03429210741010901001004a66403409002e4184011130744000d001070540c00c0d909000100d601c104011080320322845900040341401003490125007203a800002006030080000000c2220541c4184001c43c032034415551454010411135085420001202c2858011110408594a8200040c403581040200300059030107450b1200c165a8000740c12400106489840038840300a041000600d4049030303510001842d81154081600d0807071204030b2405041e211212076034414104c607810001120050907120100c43e000c010701c2404000f503001c060100340e60f40079001817011024000d0344182c3c8071010f03843c5140d103401400f40060b440206 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 884187661 1250 884186411 884186503
    0x60503010e1302190f0f053d0906020c042906280801170c15120c0307031a0307120c120302070303260601050a030209030613060b03 58
    0x72400e001692000081d080c4e038684002a034004a080a21803844404150400c03601940c0c0e13080208500d5688120f078010000b40d1107507804c030380280f13010304200b0001103915207010400240034240d030566000c228482158015401c45da00b000c266010b0104a690702c00d10004041c032641000002000510a0b2440b020009012903140c80f6a03880d0310a80790301c044500c5050f0014a6409100e01944a440e070b074050070003a01507000700c41210409696480030740e0b000c20b0107404101c000480015034078003610b4802c7c0320116584003d00d0016084151548201d51100200b0f1426043c0b5000420444032040c0742400500144000b40c01c082010210029a0008460540c2c40741004600d40450400402456203e81c004240c45411860041c00d080c10070400440801200ca0001035903100d0811000d070099002c1c20036a54036000003a04030041c0c81641d803110b425110b00c900340041248904100364516006074420032101c2101c004140d140c03034811102036800400315080e0341d82c40058031004506150802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 884188911 1250 884187661 884187691
    0x209090c12010b03010c021b010e1c0b16030204140d3318020117070306360b010507080d1e02031501090f0b1c18050c0406060503010e 59
    0x2000241d400744107811808040e51200703480c902d181404d015101c41582503001070141c1d180034840460394032011701d401c641000403002d8046516111140d85d80f00d03d001400410002c1c40035400c01c01150103098540032104981a002158264841c0c42600c2c107642d507550b01e5540c0050300104000c0c0f084a030803410340700c200c03044000d102d02010148611146040d80022001c00900b9844943c0884401501445c10341c5415018140141e0348520449031b03806588483c003485885400046000f454282c10102c0d603a485006010000550808140c3c400b070418100600b844040c0c01c440010348071000d200340d02003039042c4022000120110050101c002c901000090705038240004104082c200b01680f060066002082c0036002400350000d8035000001e007440c14055142040d003413143d01071445280980310010904003000000b03140c280110030320b502400c2c455800340210782c0c811508041402c1700c1c1c1d1712440c04200c1e46030825000f07060440e030003511028116868424100031071280100741c0039030b402c0c0038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 884190161 1250 884188911 884188933
    0x7020109211b381b1207021f021c02150105030106060e010c15110405190303020606010309020303090a060905100926100501060519080c030a092108160e0d020909 71
    0x40142ca04c54100080144042d028824000c0c20401100c1c2040324000e020040d5501580f568000d809441da550700c2200f020a050003001c0b4203001081700079180d0080a076464102d81980082c0c0c11060840d212041c0d01e2591703031081003500300c03411442400045442d81050307545940c029502c0388800c501550400040c1055101c0b048110b83d05252030940801000c201030100c0e00b048102d0198484111180610300b500310b45002e9600e0f44001c081504240e2180c103c03504540b000d2054444000c0007030500c004440c3c55040c0905004603500583d8061140b003440c4100302ca10441d180070403a42103e048009540407070322003004660812a0000542c416251481708039021882654000c0140c0d5640648803e40c0c0c100a02042e0040c0302d44400304050501400010082e05040365000b000d000000608000149810313000d00143c43e007550046542c41500128241c0c0011406104075000c542014861210401c01d40741121306090148d00402011520401810140f0b0010742110b1000e080711010070039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 884191411 1250 884190161 884190269
    0xc010e010221040e06010e130c120908090f010219151407030e070b270d08030f0717040305070609050c030109030c0209010503031e07020109211b 64
    0x102e4007101030100002a04201d410904980303c5e030044024680b4080d585100c500095031442c0e200825010340f07603240130914a0f103004846d42c4064181065040c001140581007038005500001c00d080e01918900200d00069813001c181d0304c8d00e40c1d56400c04c40d0303034146d240e84856048500304400c130900c1c1aa150044441d801d409400581300d0390303440da00403c0c514844a1000d0030840c107507000c040101014000c20300d100107400740303981c010321014448080110790180000c2041102c10005000500c000041c8000c0303a5811031100e1082c80305032901e20a800e240c50f40500380074000c0f180603000403014040c4038002521504100ca105028104840700c40c0183e400281c01c40e01c10410440110b003210941c0da04505001660700d0060600b10040c50030003106120301000c0c0b000010341d0990310030002540d0300c116802010f044018100c8117001602d01c0040511340201c02004c0030007501c0c9090420540c040c40f01c841c11610701503c00768410340c00c415039464581c019002c40100d284001c180c100e4040300c51054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 884192661 1250 884191411 884191453
    0xd090204020f0c061f0b0a05030910090b0f010e01060e2119020102010509030a0206040f03121104141e0409170708040f0b0a05120603010f0e030d14090c010e0102 71
    0x1219002a16040c1890042c003000b11710130a064030540e01c8204000c00c041100c4505880050030582019540d0355214484903003031030044400c011000b03182082c031506110000721024818401401c1c200c0040e601c0d44552402246e092140e4000a950800e610007079040042c610078400543c43c0d8555002c002d00c2d0340311410107084150181c8810192040b1b4015507a09008443d041044440903514101100d44025190200100047d08803c00c1d4240304007014822001011204a0b0100070009100e039200706401a5105100d00d60500b0b112101c00c0d201c503d80141e003011000e038040d40101c210340b806401e010180800c80010350324017004103200500c1e038035604010a0914891111136545504050101b06c00e0031454204941074030061080042c025081412122000c886d00100595a0b41b4840040e0141400b0508a14551304020f00038009150000c054170107080e9022080c407034000d80c0e0303400344042c40003101c1e0501190f101404849903540a500c0036a4446418415110882000d98200072314034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 884193911 1250 884192661 884192677
    0x2130801051f1409060114160311010b01090501030b03101e060609060e2e0f1b02130f02041205072606071404080d050c0c010809030d090204020f 64
    0x39468904112404145034080e1818020546140407058142855210b84695442103540115001800306030300747e004900411100700400c04090340c80e0301d0782c0907020140d10050002c4000c940200704000203d18180500380780380030182e413122082460100118058084400d00390703014001c1200303200a005250064031205004955044040e081d00d80001d411145940d00c103404010002c8414011140d1101018100740402c488801c8440fa00031000e8003103880388104c0506909011841c0e030919a0080c600c06041042910389160720011400240c000c8a180c8900035441341180300b11035034058555100490511400070014142901c1c0e030103444a401c07002d1800d0340c041d030000c8000c0000c0c1c280d00c1c10b0060320b8a100b61300103140580804100e03968807070240c02c0d4004c0c801a604403201c0c09003603105640041030b4010844008000c00080600b807503018910701c4030580681100c0c2c0c034055000d240300f50b0041c0d042000852a0601c020301040040c00000000c9901680070880030350b000c04410090010b103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 884195161 1250 884193911 884193913
    0xf300a1e0f240f1d01060c110a120303241e050d0f0501110f0a05180a0603060f050301230a060f03111305150f010e090f06090a020403020a1404021308 66
    0x50901040004562642c0c0c4076500c2050190f9040b032004e00300f40001c904459142c00d02d084840342600d400d2002c0010000340540041d040c1c031000030b01c000400c04e101129406500c08012103c0d10f543c21404070086038550703031520341c03502204002824481078000714104410002203141d5460b04009008825020807d407803100c40c030743c4410140502031007603801541074403003061b02c0c1080c55001c03586d480c02001e04da6403c2c400b011030308600c400182400f8000c1580c004100802103900d8100150091900d4000c0c1c0c50110141c11001c501b5040510441c580c400e46601041d8412104107464290304000810340c0800c1a102d03080084d4440c1c85035851409903119480000d0781403144800e100340650043c0c041a10242420144880d2009058403120041820307241441025000c60058498201c600191500b0045560030410304044507443c0e18040c00c5c00325a24a0b064580068883c183e0249000107503101c044401e040142041842c2c12501254026002500b07021001210008143c640d511140103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 884196411 1250 884195161 884195231
    0x1201050901090c060f020d080c070c06022a0d0f05071502012003040309030b070e0d060b0a051503150a0308070b040512040b040b0f300a1e0f 62
    0x10040e491540c180908501d11702011880c410700c40095440c081c1c0182c40041c0401d1030702041c2000f115008540116030070640095920341e44d02e4001f03644000340c0c084410914a400c001a00d545201014019a403c0040240000750a642c4903100000e0906608603110701c0f030304d02c0001c0e1285d007044414110840039000001c0c507851083c0382800c04694411084000700b820402c00000035005200b007016243c1000460455a40380c4000743c4200060030941988070840c1c115810411090b50442a000e0300d0548004500659071014040514004c1781c140c82d41000c1800096019100d107020680c003118005c2c10ba0b061142d0b81d407105d010341c0d0b000080950311261005d08100900600b080145040300c0303082d02251506103080402802801280030300c64400000007140c50b140c1c0405816500c1c640480c1480c8000009544c0030100040862100422450402d90001d07110000341d00c18040c04043c00110800c5801002d2480c01c001e101c04070115001c0d6540d402c801c18811000c848400c030700c412462500036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 884197661 1250 884196411 884196413
    0x201020709111803031c0f15120f02010309080a031d07050a030f050705062d0f18030a170904050a0e0c01050d0b04020313020f04060e15120105090109 66
    0x20030a0aa40c124200c054102100440c081d02e41008940303a00000046091801103103100082c158456405003000c4900002c400b0002a03000b94050050b01500d2041040804003140030790800160034818500d0042d8107030680e02c04121507664100c07869205141c0001c2e5412a6a14528150000030101b40082c1e543d9080c1510070a00900001c821207080005103200d42c0351500103400000c45001c01033111820110810030044100081070107002c00030111510749100301e411180c1d00140d4019076040708500444009900070481c2290103080306044004d18101e202200e0403084417290110302d4161080394400d03804503902e852040c18141040c61342c941c0d901e072824108411b541002c0c00c480500ca1030440030500243c0c0001d080c0300800000c0c00c02d1616425200146402010301c4c104507a0864000000c00003201941c0c0b866034145403088401090b41010039003840300701c410f80d0141011991024010694080c0800001044071500515121030346c002490060f013911800d91b01090b50342e441d500300300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 884198911 1250 884197661 884197663
    0x6020c070314150402090a0e0f060103060c18030f06020c0c03010c09090608030c030322051204090c17180a290105150301062a0b0604110f09120c0d030c020102 70
    0x1420318441c1c0c2030f00494146038000640c0c012001d400204000c0d5141c009103ca5807050150302c40025014050754015a5242400400340002c00194400103001c0488010350200c0c000002d8142c0340c100c0c40650310b00d0750b10b595201c025403003880c0705020717881032038805030f5959000d00460f18000b20039a12204054501000707a000c0d12816004080141c1003170241901e882c200006607179106044540c1e0001d000c408480c9910f002c484610b0242181c05020815060100d50a000703104a91030b826042125500301c002c115003008980c290140039080100100c0c50350401d218101d000100c200082d121022410340d41d0381041000810003020f8036018054040a0303100c6c40900134010041035400740507510201c007010b4150701c0140200c40078400031610100c0015500c2007811020101e0040344003000000341003408041000f100c1407446141401c01c030142d541d51440540700e03540003000340b0a0604015600b000707112540d41e00c00e94001e02c50048142d0407507691024022a0901907224003407030840c0c40c0002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 884200161 1250 884198911 884198923
    0xf092803111203120a0e1c0f0c03050702121e0a02040605090613180605040b2418060d05011404050114060904260c01020a170601080105090406020c070314 68
    0x45441005840c616003100640803040310b082c40c500108001300c503540d0601c100014080b8082d220740b01d01c520f40c8100d0b5200c6010019261105003610f4403030100c2450941280c40340a03210005000031024400103005081100c040384201e224041510141102201d0100350764202c0c1c842d04c20036500140d0042c00f0740c01c0038403c003401b400c029034414200d858450046080c07501001c100a070403d0340c4000100045840352403c00f00355506c00300501040c14907081c503e1850720291b8090b150f12491905805a00600302441e115008000d84890300d0b095504c009a0041d60004000c82d070003044402e0000c000400a02c00c00c0584065080411001e0030582031217801c40300185900045200c100e4180640d643c1d421205592050780000c01c003d0390040c0c0d00c218214140f0080b80035182290201e0210480741c019000b40039070781c0b1036503183c6103010f9491201208108081e550715000c078240d000103000d24102031b048107920502440c00585042e01c80c02c851843d1503000c1c1d1060700d100c141c1e007420064400b418400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 884201411 1250 884200161 884200193
    0x605182206050d1a04030e060a050405090619090f1506020a0506070c11060c1c0e0f041e09172b092012010608070e07140f092803 57
    0x8401289400380d990005010880c4d0380c034041d69200318000408052007900c95a507068006860251a0790f0a0391004e8120b07005406268841c646801c005081d0381407000904104079180e914028a03d031800110b5401000c0c081040c42469444c0c02503480c0c0360002e00004401021164001c0502601a06120341005005490102002014201200452411303c2c1a804045d001ca822541d1040c8030b0005a25003202002e030611031455074400c090b00e89400c941a13441c0b00f842958124460980030382088104c1d00005109a444a601203c004c20016940d100010300c038411490380d0824035682e80c400300107411680044050a02410301400c00d15400000545030008074281441800c0c52607645045a03203440e02081021030340070300ca00f50749030f8400490599619200000300601c60f140d51209894010034069103002107200c40110b03600510807509040f82d4500741009034100240707c00c003c20316a02280d41c0c00d910003d11031765a008d001d0454800d0070902140880c03e508a0b02d581340040c8a24600c1c52 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 884202661 1250 884201411 884201419
    0xf0302120a12020f31060c0201050d0504030e0306010308040513110712050d151707060215040804090c0e01030f020313020909030c0109032c0a060518220605 69
    0x380703290150460b654001030b048810300980c842c40c440034450303d94010480100004001a80541240c8285030802c50180707070211100207000e41c40b4a020b85203210344080c0240040c008120b180b0f0087c10350707402560058400e290442d04401804002890182d080e001600e0719100020104128949580a400c425030242350074400341740a504000d0a902030100c01400d4440c1500d0604800c5114004440c1c001d28444010003401640d0620f281d0150a10700032840d40340307446c81d003a0b0302c0c80380000784e948200c80c929030003000b07801c1914041000e00070014002320386210081c000801c03403231500d028600150341e2541c0e0706c0c02042c012000050030355517120300c42d01d00c1506c100140924214841082e085083d0141c0f1016821b445d4110943e20b035100740f50f015007d55103050b2000b010950311001420782c1000c01143c9121900002e1824008555143e443c10361149014000308100e070f004030301030030418480100039210204420041050b086c1300040702e8041e290319428013807800015100e06000340800361 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 884203911 1250 884202661 884202667
    0x22030f0b1608070f030b0301060906080309130b06030103080a2a1203050403050f0901021006030c1d070203030105040504030c02040e060603100e0d05091909050411040b0114090114070f030212 84
    0x40d2000e01900b00521500d13007010786030035030305510344c400b5000a4000e0502d40d03010030105560307101264403600101286841103a0f606e1048036004030741d024440c1106001091549180d280d03a1b2400301d107034044135000c800d1008812421008072113928481051030b0011218100048140c07401c5403511405100c42400d06141c4000e1001103984401035401c03030400340710030030ba0715510301d1700507450010011744100340c03941440804000c010f04024001c003100c4002e2a54640d400c030645140e0703201181150804e0042c2e0052004115078509a0801c0350020301908100c88048020b0300414103a0f2450749030f859550348a0801d2028604003080001030140d050003040020014120195071902101800201084008500007030790b90b0310b618400c00c0300003c0d000a231180c00d03520740110000e80380441d402d9487d80007008004080341810700904190b100141c5d2032555030076405800010542041c02050f040040c810400d0301440300943c028502c1e00d001d0441e2240d641021314001380f030080d007019440b50000c018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 884205161 1250 884203911 884203921
    0x30e010206090607261503012304110111060703090b101a030709170609070e090d11010f091103011505060403201c120f0522030f0b1608 60
    0x41000c40d0000485d2801528103402042140000388a00d10801c03e0650024180401e10801c403120200d0490142c0083c030002d9446c2500600121881c0c820803c01c4208000250015100c602c4461440405052411b22081281032081c42c14030210f0308080413a55a5900394140100901815031000c40400702c4141d50b030501c405441031410b170b40c201c020381c064040082201e4900601e5000e019008421043c8501a891259640c0d2204242c40003880c40c0550100400c0c1e0041c0c40b41c18610480e4003000400e03490303494440481d14216254459140c5550725110104410403a000f500c2805010310b201c9501d900215040508450800540c0c10100d210018100499140c0b1020740302225048101e0542601810b0086280780c0c800c02c40b49988400e6075a4030400c200c00640c00c4400c494000d1025503480c04500d0802c0c0c0d540007a105a203000b04030284900905c030a00c400091031448010101d000c0031a44e2075403402c0c840e902000c006c8484250b900e0401c00a1091480d07101d94030891403802ca4079500785 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 884206411 1250 884205161 884205163
    0x1503090501050c0f1c091e1202010203012d030803090705130902090c030c070c03150f05060906060c030904021b0d050304020105160f150c1103090a060c020d140a030e01020609 77
    0x5100c900c1d19040c030403440c1000320702007264443d900c11034020947c1081d401440012089010241104850407015050100003c610500c2628144c800c0390302c00100b45141c500c0003182120b46100c44901058103a10044002141e00000e1409205504c008000c0d0320700385030410800d42079080b40c1c03500c114644102080540e4501555640100004403042d40d680c4074031902c074070b480c41282e2018101c1034141c1c8001003081141071000c00303061250101040140c55140c849004e942c01a0751207540169840c000c50840d01c0d140000384070745559501228580301c4040080f4050b40c0154003580404c46c1c0e800e110302403180d0144000c00140c106464041d01d14541940003070043d0294a400141300600101c0490400c055015881c0506400110103035061544146440280c503d102d58000007801c1c2d40400541b01100100b5150b07204c000426441d4900d040400c03c0321450081d803002c1e64401c1007580b1000100d400440081c003c500360b40d0251044032034609018041e007004002644c11584960700b00481000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 884207661 1250 884206411 884206417
    0x10c050c0d0509130c020c1503091e0102040f140a0503071d0c0c0f0606100201092102120d0212010f03150915020a090504050c070314131503090501050c0f 68
    0x12241c2000b540b290950b00100300484a15407aa030401c42c40c2c0700c0f0440940e030300021400c690040464446145000d10545841c1e00e000c10382e1200c034281e000c1c000c00c4210700c00381c402c103030400f80030750000505207036540303032880181c00c174a50000c8002480d00f81d520f6060300704800701402a0000380c00030451145850460301c40a01c250b005101144000c07400314448646134011584251000c4049400030521000125121101569814411603034452407948080c010b025240b8225000f810b034500188281c40440c8100e0103c210002c2140280340841c0110348615001d418000810040140c507030b10410711609a084042e00901415017062000300000360814504c140b100c0c030b889002040c901c4207841c00815035880b081c150784030a030000c2003070051790340d00170703460000c0321403c84044c4140e49031030004001502c80d80740d01070009010301c40702d140c0020038903008094031401c020540c140300d5511040340b84c8a02c072040850002940301c074211418800240502d94011500701c0d05140307459207100ac1c01d0302c284 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 884208911 1250 884207661 884207683
    0xc031b0306010309060f0b0a14030d030908220f081c0e04060902033108070b1b0d1406090123040207350a05071e020a090e010c050c 58
    0xa000000542280d01ca40c01a41c1100c0e03000304184a104e41c1c407031010000d405100001d038062290440b0000359010b0500e2903504018020b0054080700818280490240520351801c2e01c03020410001d10750500c41040100038884044d80f204404582018003d52403280258000d40307036684213054500116601034620b0040b4101e0742440090a80014045805417407603510002c230491000c000c00c00507100700b0303000f02021402018442c82c01140f1060803500f644090401070b02030002409624009070b5400c241a07040342800c102000365030524075544c4c50581c48450801d1030140c8a102200002182c001c416400c00c008440e4180d0350340c1014440c00e22000e02c0094882c0903203800500d5a00b5450300da04440b81d07250469030003450340300000d12001182d42c4c038030303044140c1c98000402ca408485804003501e140461554405241001607202d02414032521290003240c81034079800d43e001aa00e800c0e03c40024040001c02103103034226000c42c42d00311038200d1840030900404003e950400b06002c60781246e84 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 884210161 1250 884208911 884208961
    0x915070e12010501090f0f020f03060f13050106030b0a2c0703020904091b0b030f040b0a0b09040c050406150801090c050702060c01050a050606040e042612010e0c03 72
    0x3800d489000603966080d552540c122651070800040340503001604a401e071522805002e200c055410800c4c5412407041c3c0e02409018001031000c12114a0114061152000d00501c0c01c0d000504151031001121020303032100340400d5440030180d00d40c0c140f403110140140303500c00280744800742c010182202c0d500041c4028600b41840350000e0021400b950680700c800f84040c0080103100c40500e020000d64000c3c55104a80d0517092000040300500740c0212072280110260741100c42e203a5648980340321402030000200c003030722001070080580718410094403039030040d4803111082c0c2c68902070108491075504a50b100c410381c00003140030b440d005042c0a0440e84010400600d58200110460740e0b030140d100001c2d0302c00030003d15403a2110341500424080d14001c401044a40c44d00300410103240320b644a42e505101000000401013285c1ca1883c0ea440c0d0f10907002004000d40038220a805035020811141c4080804001400407100c01607400380d200182186441c5107003001c03800c0140d07030121043c0744040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 884211411 1250 884210161 884210177
    0x801120807020d0813030503090315190207022715041b0e03010908040b0408010515010f1116090c020f010b031c020c06070b191e092102010203010608091507 69
    0x1300003050048130600343c980d000c44440240c6034506146c9990100f00000d21900c50041e80940703104011040c1406900e810754a200c0d904841130103400617401402d81a40e00601808200d01c4100110201c102181c10400c05000c543c6403608016140c10b844440207402203150516600748500c400041e8884240c0c0c40c14005050036008000038050095844028038074034001c1b43c0080d0340c3e4112405042501d00940082c8415030381c104d08a6103801283c1c1030680000c001c0901c100984d402a040c02900440400907200c040d040c000d016040c003441503010316a81950303244460307156641070110808420880c8028804002b07901c0c00207607601c4204211031b84407502c400f2420180780c02040f240106510141c225134555441d42819003e00300101e070307071881c0014466560b100c40550b5220f000c1c2802d032002400741884005136502c0008251001d0101e60ba404e0700b2001d1107019050b801c1603d0001404d600143e960b6052410081c0700c6407002e090542d1680c0b066501428120707046240d66407002641c42c107009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 884212661 1250 884211411 884211413
    0x110f0c04150b07051e2409010e0f3f030601020a0b07020d030b0d050703080a0c02060d0504030f0503010f06030207170d05010611071404051506190801120807020d 71
    0x2070340101c80d6000c0d44504800081c458200003000c6180352011800802a11204601c48031158694040c0f01d6111a0340b0221909801405130113420f5035001030f004130000900701c00b00704070986040c02c501600f030808e5000d6246400e04044c42d820451240503d9640100303000381d83c25011001e449050050b412010703011001503101e034403c00030f102039943c1001600e481400c05107006902e0b0408500074000203400c203039500205080c0400c4020800354400300402c0c5061440d210038955420020400e01000440806000585e075220702804854401040c0010303941058a4040c1003200403450326030138424144010411669040c889504a541500700940e9840040c6043c9016040307001804510325800b141d1408003500f00d03401241640d580d501c0c2c03016101040a0111b5885180f41710b00d41181ea800398600702c2e58246a00b00c207411858000303103481168002c0c800a02c09812403510385480d6011240544030465011485d28010907641d0703400c0d40031a0140d201c24103c0d200d1103001900541d00461854 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 884213911 1250 884212661 884212691
    0x402090102012c19081c15031b05040603050a0b150901030615050105030c0901030e0c1005030a050709030215130803030c120c1216050c03030705030106110f0c04 71
    0x2500c1c3d00152101050114185060082d0100950440103540302c0c3d02c0c40d130070612004038600b0b0900d60b04580010304100344040220f046401c5036480140c21034443c1c4045072080102c1400b140650b11650306500e00c01c89281540b07180702c8080d4030141c86a030800004001042000c03032504040c940003550103071182d90740004102c141700c0c021034058100c0c40000002080c004580d109540040d2034011003802c40342e59400440b001d01080d200080c20803001c006030306556000303900c942074441078102a10042035810300014124030120b811030340807500c00010001100550301c521680420203041c07140700b0908607000300d807003d104010340304a11040010003030840170007560135500030405102125600d10301202105019040340f01c0401103801280c000c00e111170070510549981c801c400c84682181d07039440b0304000e00c5607805206081806000c000c88402000e045c001103100d1003003510745640c0c07035140010040c49458415880348041d004031240004800d00412074492080f802c031004034165202034506 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 884215161 1250 884213911 884213921
    0x8070602190306050103152105010f2406080c0a03022d0c1513030e2e080603030705060a150801020705010606260604020d060801181203020a020705040209010201 71
    0x641440038098111070090303815004070742a941c007039800348603030113a030444901c1416203030061420f84150145250003030130014000c03080403070060001241c2031400b0760a6400300c0c0c0c4000c40c0c4014541099030928145a240800403004220f43d25120b010f0345841c0940d14050f0044030841c03010503400240c0e008082201c548402c0300c1d440101c010006054000007144403e0340095003520060007180d20a40301c02844a108078880c418081c01303000821107680e411500e03e12030107011a071020403020001c90342d40320b58071003484941c3d08030740c001c085500150025049800045c0b0080c40f0b40d01c10031010002440c003041a41d046548080045024141c1c0e100c042c1041840760041042076101003104006c1c80015004081129025201e280d568030040684480a000f0840343c0300000700031001003500d505103034bc001c1000220410001810a450340c1c2d01e50b0030350700b1820070490191b0600003c00c0a112011152801840c52410110315064a242000e07441d4421803040724841d950108180800ea4000e4000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 884216411 1250 884215161 884215177
    0x3090503030a0305040b060a18051b03090601060215040f02010309030e040221010803040e011211180613021e070f1703090c0f011202070510020c0c090f011208070602 73
    0x10749440d406140c4005008200841c0d050b00c07003180020104109050925404050ba0b080c8410120020301500504024281c0a0051044c84031484110882e04102d400510b0141090340003820345549085002886d00c0030203401421111a1401488001164106070485880d030a08021500b11014101514034000700d0040a802c5400019281c01500c2d4081d102004080c1550842c529640c0b101c400355907034010390040001c418058401400790602240040e01103d208014841345440710801140c100401c5a05850190410b5410300c621703032400c0e2403801c400e1006031310210300b0a0040502d00d000354101002c4640d601c40001000c000744240384c000300c42d01a17046484440b402c2148022640e550780100c0354001580203c18818100b850b120aa039421564140e440c038005001400d1080020b46c003c4800300c07000e01c12000d540d00180c4450025001c40d12a42e00500f040500c0701e0188400700400604400c2180451001841031a920509542c02550000302a50300c403200c0d440d00000034411114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 884217661 1250 884216411 884216413
    0x5061611090709031a090303011707050a03150c0c0b01170a0210020d1701080c2e08150405060a15090e010b0d1b140d0915020d051b0a0c03090503 64
    0x1000010b9030400a1402224410300c3c0030280e40190368a1261100d1060394040c3c0d464004000401000c1807601400c0304005512054901c41d03540d400000395010460340c411a4060001580301c002000380b0b04c5050341e40700290500401112403030340c401e540300c40705005250340f414a00d22915880e42c002c0005415456010304800c0c2c00c03483c44400690b54440c00e4599038000307a240500e82d80c900e40e0010096040380d41040080889490300030030880611243c0c00b080701d02c2003207241051180d045d00e2002030584000d40e2034901841c2464001c0c1c0100746c9031140c41c10301031030808041c003540361141c1080c03000701d03011040081c26000e1429000c542003c0180c1c004a042d4418500101b09450420018070100c404000100072407251640c4616140d400400745001007112151200700510603c4010404c0840b01c0743c000030324075116a10050802c01c0f10141c048010b60210303882250022134480d40350400301c1140c10b1403000840c403042c2c0340070348240f112603030402803240d90050402d0700800b691000307488014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 884218911 1250 884217661 884217679
    0x50409090b040203240417221e0509060d03110a05030c060f04110d0c080712021201060503060106030b0d08030c090a1703040512161e08010605061611 66
    0x1c00c2003003010344161000da20902170301c180d40714440e40a80d4a5180d15841c1c03110001c0395a140d80743c460b2000e070100c41d94201c2202c20011a1500300d2098011801d20305111070900941d424126000300030b612600c40d078540b18044110a01c6580d46071203a2590180f42101c82c00e171840c1032498207d4145c4480101c0803110301c14100d024041020105c080c001c5408210211000c50b0b650150403041f181091b1006490002c01c10141241818003800b181e50b80d40c0501645102035903243c0704140f0340943d80d40000c8025400c0030700181145000d08810001d42c585d01700031702c5800d042000281d00c4060620540081c160303a00c40c0c508840d110701400803c0d05410050f02d64a9182038001840d00d50b1141500c07078072031022000c0100b1420190040d8410140080004608040c140424841c0f00700d55000c21507040d1195610741503540b0518110a000341145c68103071901c046c20a03840f83c0c81201d554000c51a2641400010300c941c1d00c0710001d1b11000e0030b0307021311004810070074142012040f911000498009881c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 884220161 1250 884218911 884218913
    0xf030604021605071a0310030210111e07171e0c06120a2004051c050109050304082119112b02010b030a260403061a01030c0210020a05040909 62
    0x200d00202107803920200e91003110300c56030300c5420501c0b04850440000302807c0301840541811503100740214028101200d10094210625140400c12100c2015400004107090072a19041c0540d40041c0910000c107041e01095003003072511150718010100104406080048402c40c0401c54411421000380410b5034403a090750030520042c0301204e007444071a06042c241c0c0c00007400d500016000700d51100e002030505061070100841c81c11040d0252220035141108480450020310800403054030840041d9a65072070710a249040841c1180321041d58500d02e500ea41604540e80103ca40028060b0303100710250381412030566080040c070724049043e10612180808021845044e8090004000302d110204200d480c022030a0b109255802c6415420122401000841d0f12070622007240c0304580301c0401003440203c050507070300705900039581561582280b00100c0540502c0c1040c1c90000c0c41d040c44560380e00c44019503614902200801a1039002a81d4101540301d101918040c0205234014041592a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 884221411 1250 884220161 884220163
    0x1509031b06040f141c030e011d0405010825030308040b181b01110a02031203090a0b0a14070c03081f050406060c1e1a040804090207140c0a0b0f030604021605 69
    0x10f42d803611401002085081104007580305031170201e0aa040d0b40d94034400c41340100459000804010284c84e003000110b1902c07955490303000d001e0180c2804070083ca000e038031200c1d40c0c0100c03d003a111550040d501025083c0b010070740c052070865105401400041c101d803036100d000c40f0300c56220203c101d024020721420032040d5204001001d1505400d07614645c03000010740d4a540c882000b444000d5255000c03400024240b0700c000040d541c030043c00e034180c030402c0049403900068203400b02c42c0707826503030f90318244040c40900e000c800c5504082e40f440c040b440401c182e030b40a46881c9010b0013641c4030700094206298803044480320310000d82400f038014040e03d9078401000e007506000c1c50048580c403000c1521707408088881c48441c4c02040d0000d00540108255046e400c1c1c0102028106448459003000046080c20540c001060110310520035a858500240e490764104140d0301396040c0f0494010404100c0340407000182c41d211180100e1080e40d94640400203002441144009012680c40070354500500034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 884222661 1250 884221411 884221439
    0xf13030609051c021e010635031312021201240b09150d020f0424022109010c1502120c1306031e09050c1509031b06040f 53
    0xc441c82c1120340001c00720409203d2440a14103403001070b48448071040400140042441200100b00000903856407101226044544044241010022300342c80030355400301700c0803c3c900011140c81c05582450050308038000b070242c1c0b03071080700103200c2182402000d55a035100b103050078581c2c200c000c001039903844030512141409403985060390051902c000603451003540032202c0000c8004c00903003214083c22040c049541085903800002d031b5081c0030041d211000074004001074143c030030030209140440c0701c001d000e03440124440300454005091452a0220740d0558030380e42884000d05503200e0740c0010040b5002c02e6940b40140528040100d00788503a182a4014035008041e940c60f81140c0d030354018004240e100f0791400316400200300b8810414103129501c940310703110810740700300b03400f03040144440c040d00c0b803940040c1c43c640c1101000c0b115a1030a006000c8015541c1c40b110307814111544000707a100d2003120408006031410707141d401090b64426040310040d040c62400310340510b0301d13402420b602030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 884223911 1250 884222661 884222663
    0x1d0409200307140121110306040b1906120b1c0b0105010801060905131d0c100e06040311030f0a06062309180f030a080a0c03090f06020f13030609 64
    0x1403001044158a8140400e0318000d4a14240902c20826000c0004480b1a0900481c0f000301c004904c010101e2088203000d04140a1114540681c81c0e0518104020441e0b400e40c00b424440d0308881e0903140242c229040305400c5400c0d0b41012400e00001c3c818010241c8015080c003079224910f80207656200d14401e000c440d44c1070081041c031180f41e803108010340310343d40d0030b0203082d02051140380100b1031071804a0304041e000312404d01c085041c07103003950005100e801d010301118141d00001118035290030100421078081d10b80e80382200340101e0b03400114213603110b180400f07060801e882c0d03a1a40b85480410581d1541c2c150b02d021503e4150f000d0a02e04000d000c18003452a0485103040e8022103d24002012190440f00034941c0510380c4440344000311442c5004000702d124024514422007d41c1d050001c0c141030035242d00d07088017a02d040c48030b1804a070025419481418a0403c584002c2040c403401840041d070701403801642d440b12529800250b018903140064041010700000c410408950014890300d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 884225161 1250 884223911 884223953
    0x180501050109050c070b040b3301020f0c2112130e010542030109060602010516090b0a020a0b0406090203060609151009080f010c14070b071d0409 64
    0xb0f030300c884ea0340038814820020054086100c140125020a4a05001c0c0707400043c80b0303525081c040c840d01c0e420b4070201c074094030001612605006011040d601400855507040f070100103403140b82007103000623081d400380880c0700d1f0b182c40224103443c4151800708440000d1078142c403811602c4c0c0d0807400003403d40e40a10701480c1c41c2c50000b440001000d06001940d50fa001d0440d0007070120108480280b41e45250346040e454650083c070401003682961410021406440301240100d6444d0611202a0030b6400c060202088220482c05041070b196104810b20b007901e5080e03a08503034400f07103108220710301400044064460214103040c80b041004941c04601518400e409441080c2c0c0c4100c00c001402c201210b0b4041804c54075141c8800a00c2d124400c10b040201d14101a0078068480303034501e10b0300c00b0311030108005070340d120760445003150030595803204000c0f4508468500b041d80d5450038060b0394050015000d100c0c030021030410710803400b4101c07821800041c3c410400c030109400e01c0d5900d900c1c110b5440d229 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 884226411 1250 884225161 884225171
    0x1b0a2301140304050d080402040f1a040612170c1203011806060f0e09091f0507030b0d080a051c020a030c0801050d05060c090303190f0f030915050604180501050109 72
    0x112035002801d0b60300c1160880040d05200e1130000090781d5001c002801240d01c0b42d519510000a40381900c540514952514501d403000c2c4884020311007103800ba504002075008005248400140211010f44852003c40a00c3c540b903180070400725181c1030b9080c0c02c80c040c10ba0040f002098480281c02f2107100510580d030b040c440503645038419511100b0080c0440000342c1e40351618006418018109900314804e00211240d1038103500030404228030b04001d02c040e041d115024007201582c9030140b5501e4100440700c20b102c1201c01e47d0f0311106441007040c210140400403940c0d44100d0031000c0185814a450340c41903646e0581c19800070000d011210703040c40415085400030034142065021102640c0e44100100881c2d180c0b800d10404c541c005181456141c4800c000981008000e80c4000030040200d441d8130745010300141016100460700b102003801c1525144c001c2d000303c1e040100c071440540e40664001850303210b200115010789065141601c000c4001114003040100560000f41240c2c010001049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 884227661 1250 884226411 884226437
    0x4050303090706050306033f07050d030501080325080319060e07200c0604080f011410140307091d06090c0307031205090a0b070b0a05091b0a2301 64
    0x107845e02054901c00d4043d446044c031054001d250074680d22101c1c0346990300c404070181c0015544041000703107141000c501b80c040f07030410411104000b0300380b00000a0a00740300c90342c10443d14641d64000c00304800040c0c0d0034078200308021465842e00040c07060700107490a6403460070002144440c141001c500708094075082001850000d2464403078010041c90b0f4039090300c48404094084e4040c0304070706102d0140222243c241c66590342100a1008040b410007800c66608005992030071100b10789038081d0325984031000c008140481420001c1640e6994581035580740035100031a2901900f60070040100307140c50140c2e98030200080d95200e104414a04460061b510018016210b0501d42440d0780c250344103480a200041d0184c0f2194003450240c64030908150700d160006500445580c4005080040004e110007030010034045aa0f20031070700c2c7c83c01e01403030074602c1c1100e5403591598076040154030340b0481400150b8603d0040002400c07142104401c0c2c03444010305180d80481038102d603001c5005040211 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 884228911 1250 884227661 884227667
    0x70e011812120f08090c040e16090c0210113703060f061404062102071104142401030b030105040605160c03020d230a0206040605010f1a13080604050303090706 70
    0x1a104580503030240c900c1204186c01d1002625580c0d10900080c041c020b41401c8401032a202c142c018080014045404148004084c0c00c00c1d070442c00c288000b0742000d0010444007a034108481a4202c0340201030741e000e6640d01c036040c01d0214a00911461016110115074180c1d168010b0001d54407035030907404440c0d035108020b90710300b9820003650091100a00041240e030340a42d81c0030a010082003880034100005030a131310100c4e030004070115500300188654101a04103807044100700c6141a1000409080c030020001e0340940f4100b80480d900f403400d601160691081d00842d00d904070240017403010b801c161070a480070705801c41e400c42e80002007980171040503205103c005580e41d0190003404c116007103c10103d41840126403409505000d05000714526141540180101e050f140d0180003581031901d828170560703206074051901038100000610010b440117890320145c0355203c402e16550031820300c032090103005a60015415028140800c414400040003e41c4914400d02c2540c2d95039131a079100b0f07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 884230161 1250 884228911 884228927
    0xc0e0102060a0906150315060605090f12210706050f0c07060b03160602030c060903043602030c04090f091a0718120c05030105070e011812120f 63
    0x49005a100740d001c2012140c0d1a44200c0d055802220082904483c4031000800150340303900032a40642480c03620005600c0c40d101c0c40700078044518080346000d103410001100c031021007003814411340c0e50140c0c200001e281008609406c0101120454041440c0102007a00b5084144240c2d8814140400207001014801c20a0300c161208900c0c1801c0c90440e848040041c9140034140f609807241c82c00e2140480c01a00021004200560007982e6031210f150390b06003400d00c0546402c0039544140001e1100003170b82450b452600340c0d81180207008100c030000580440208205104a00344000f0034045080105030041080c0c4405c01e801b400b0100d03040c00300408841c203991018003400000d115031005400074411481d0011500e142000da001c080441d603245e82401030780442d540311041c0100d00300b0070000b280d0f0b41c40206000c0f0002c2041c0d2a000f41e01a05201c00030951504000a80198011201c12165900083d080f020003041100030f141c545007120311800d9030180702007403191101080c10ba10a00701 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 884231411 1250 884230161 884230187
    0x606050a0509010b0304030507050a0b063d0504030204140f10030b1302060706053c13020d0c0902040303080609040210030b03071a070311060c0306010e0f030a0309090c 74
    0x340300f603207003007981946034002900860400a00300100c1e00424400c12070708819034090181017103642031140800c1381c0e4041c01c0c192015440c1c00c07400702d103140f43c1d561008002a401d5440d00505600404501241d0a1103103400007035009151940004d904a0450906c62203422000c9026906486009440203502c4c0c41d8030005182090840c0001d0540200c44181600740d4400343c841402c2c0341003540e8400588070122440b4000241c003040100c000310080304408424500244840c82e00f15076881c554100441c0100030304101c18055091038111344030501501c010f2504400e00350f540603291420000030f0b500c2444280c001406400200e441c40ca001c0c09807501071039000309104051b00d003502c41500640001c44056a060241710380016022207003003841444a152420700c0d59641c2038516003e001580310802e1076600e9444402040100c00484007125080758003400d102504d0502c06002540d1924103c8040340c05010f10740d400c00415806c4003209050355600341060088000b0148116804840062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 884232661 1250 884231411 884231419
    0x30409060f08100c0c140606100f021908070f03030b041b0e040f0e0102070b0610030e15090703080a020318061303060f0b0d050d17010b040303110114130606050a05 72
    0x40e040c260b0584a40c000c042501e440c5c288074800310a1034540884119804d03c0090307203900700c10100880c51601e070644500f120b140c1d0901d18102d925280c0020f40d20300032600b203005200b00d061400003c1c003001b4000e4be1981c9038002111002c0503560b180007005442c4081d006030056040c0180c4007412070300e1075103251603d2807030350b283e4103040649020030018044080203401e03e00c1da43d01002c548241c0a00040c01e04a010b80907030806810f0020a0000e2500c400348050304040c68002440601400841c3e00d200001044407220083d0326610580d44c01d103285680010454603000403018005500400035100c519940300c0c20405010325042030101d0b501c111b161101c1c0281200c4401e000080ea168002c030800c0718a102d0002c0c0d4800b0b42c80204011070074403441581c503903000b603012424290340300400000058001910a2555140444c4134205009070b000007801c2c04580d074902c1010140c05d501400060300f075a500c0c1c02d0542031021001c4900707041c00c0c00c1952072509008020a0034284040180300710340000d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 884233911 1250 884232661 884232673
    0x30c010510230d020a121a10060804060e150f070201090309090213030803010902122203030504060e06101a090306041415070525150b01030b060c030409060f08 70
    0x200240b500d0488a40a40d0058401c402d4601684501d070303160010b003c1c4032015048140c0907040441013039a001d07250b0f07010441100e041058901414040c40e040310201d080c02c4107551200d1403c00d01801514442c00080d104525000e400041501601c60181d08a040103a8282e12105402c0742661002d5401030085060100b081049030026401010354200d14031129040c01c2d02c990303401040e80d000382d014210b02a0003082c058803d41204d843c2d56041181892115922240c00702c064044002d20f910140615581b040068103100c19500905840c007030100c16624103203008807205155204a014000014800f00140d950480e03a04040380c41b0310a0040007009160745960b918500c90607082e5081540f40100c10f2600b042030310f6601c3c0c45008030b1480d140c4a4941c0407520b000c18517004c0c2204100c0c4c1c4007404070a044041400810001a030001310369020401300c1e03090300140c1c060f15400c040c0a4010307030005651903101001001600503581405c405018407682c40072501c02c1100c2c036001d9003409030015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 884235161 1250 884233911 884233949
    0x5010b03132a03080310080703050c040903090503030d0c0f02012a0507050d020a050c060307050306010c020a1a030f0906040b0a1509020a02010e060f070e1e060c030c010510 76
    0x78420018440014421071082d001554840b400300d440d03104441d0002d010082c00074a20700c0411810280084900402c0400e141d900c0d0343d640d803c9420380141c0500e41c6d510280c4103040c821907279800681030282c00c4036a0b4600d188000001000d083c12464001584400c415007041e1060090300c6060850000e070314600c81040c01c0600039868603456400921004011440000d48140070520080c5a150041d20314040700e424450300b0b25450044142c81101c040041200780c0b50020180c0b07410101c02c1c82c11145100061000c03601710000b0784c0241401020001a04d001c80700d22030001c0d440781905480500480d1141010f03159604010345d4010101c59411001070840c05455001a00c01c988200d1800203007a691a181800c9a0100000c500141d449820881e4142400c00000d41c110780e0322522240d182c84c0c000d40040604003207040c0b00e841886001414004041c041b40f0403600340000500c850341d2a410103d50603070380d60009041001c1c07942400001441048850540d00031103366092a0600d600b013 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 884236411 1250 884235161 884235173
    0x3060f150912160e0f0f100b1303022d03010b18090304120c060807140a030e010204031a040c0e090d080403110a1b0b030907030305070302100207120305010b0313 71
    0x100b20341a0f00c0790103295000c030000d01280c80c0061114070031020003400c01c03c0c1454141400108030a400400100070b0012504c208086030044440043c40c0b280c03123094004404543d1686d80e40b029510418807005031500201c051240d0b03000d18011980c90840700ea040040c9803d0b500c0e4000034903440305680001c00020580a030466a002c41c6a8055a2a06e0340310300340410b03072a121413000d490300460a0000c0c80b40b541c0110009030086201c2c01c00a1040d1510040c0c0324072481080a20420161101000600c0200035015140616032000104014040d03000918080060449050300d1040801c0c100013802c250fa151003500501e200300c060b010842c82604250340f07009014104604000082c0780800d520f0300140200c86200340b00d41c611000c4004060050030003881590003000121208005002581e04001041c2c01160f525040550322010581003d909010446000c080d4550000403441c0800007005641c1104a1103914108456622804005410f0008a4880012841c0c0603605408030f18 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 884237661 1250 884236411 884236429
    0x2d050709050d02100c0305160305070b07020a050604110316080d0f18090b060909070309120e0609040e2d0714061206060c0f0102040302030c0d020d0b06130204080303060f1509 77
    0x4080e0401c20315002d030148101d0420040000700781e0012300003080701d0701000810503023703400100c07a1008191a82d40d64540070349a81d4003400007843c1d60001c1d1021000307518140942c049a030440c0b00f01d0b04d44103540d24907042c0c883c1c3c020401c41c2c000644402901e80082d00036540d8884e4525503a40b158041410540400c0c01001c50060700c030381c81304040c4000c0c6125917840541c544208902ea0300800c08690034900031042c1501488418144070b0880300c900341503241c0300c0c256828007100311000f180b022a0028101c2c20141e000a0007081c182c1031990004d04080c0e8006511552145103045a4400350b0315501d040c81d00381850b01c1c02c0d60180b070400080d000030b04203448540d00494018516454040f009d140301d4580607980340d11940f1079402250070015031405200040d45000305441c413009001440c1c0c000390f00340704003050051540b001f840c04101a910b4000440d04810f901301803c55803282c894030505c0d5070b41c100300c3d2034038814400c076814100c0a080200004407004e11035010942440003210400c04000d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 884238911 1250 884237661 884237663
    0x7060305010320040b130c031104060c0b190903210c0903020d0228080f030f0901080a0e06101707060e0607081c0203060901080f07092d050709050d02100c 68
    0x5505c070065117201d50340341c0d480e43d01c200e00c0d240c04c001005003403031070050140c034030352081042d83c91810b00c0104403a54010314420301e001d61000c0341401d644e5030031140c0c903884044e8101030340b50b40b882c080d950010503412045040740100f441204091500c00c180c4144141c40b10b01002c8400a0b00002080006081000400200920080c0030270500c141d6034010101d804501600c0d0058003107038040c204202d0a050240700c1c45010000c000c1e501e080400440c0308904c0c802c1c80051410080500001003411646621089a03a160082911500e0030600c082200d0440d40d402401503081004581e0b840e0310030700041610484845031140400c41c80380a0800c1415040410143e840d04020442601c41c0418811000306062070f884e00180c40342003000501103c132034142c000c20000d45c004240d031000c0e054002000c40444042c0c60010521070007440300a0b82c00312064543c0e90302841d40404100030100d2a402031441000070f9903031008800c0d40c0c1d03000c00c020144424000794029490100760301140c0d200c0ca1340c01c4615 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 884240161 1250 884238911 884238919
    0x1401050c16081b45011a031e130510020d0c0f020a0303050c0408010608030414030619051302180402040b06090a090f1506020c100c1a06120f070807060305010320 71
    0x50424503c0d49044c1400050401c0404060701c030040c0701c1c115040302581c01c140f61540010b800d40c54180c80b00c0400c0c009120020a6556181c4006080202e91800010305039601406440c0292062160240a90010701c41d42c0e003c036041603840d05149100382c40001c1c0d0121176500900c890740719900c0a0b00200f00c00b50068090f81000c110203e504082402000c00606900340250794445ca48040030b9070402c010820356200e41c0002c001c0c080078481124001c80e007044091070018213611001e200c0ca6903100c0107200250000c0b03029420031100304110010310301c52030090720240002c50319001000749a00c50107000640c0580480c00038404074405a000010311004c941c0001256580c100c100844542d595200d9401603102c0b5000160038140f80308240701100040c20030740c421104c290b07070307000e240380342002000e00d00415200010704aa4a0294441c21042c00300d00b0f603018950140380345038559a5900404856200b00200014018420721a4038101e903084500c1c4214a526094010040b8064501030741e40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 884241411 1250 884240161 884240239
    0x3090d020a1a0c0601090209090106030c050d050403081801111204060b060301080d351b0c0a0201020622031d0a0b0c061f1401050c16081b 61
    0x4460042c0c2c100c510500c2c41900d10948803a182c0c816140340500503040007101500510005807191201c44402c0c2c103450903400e011602920b952011240c500a048a250b03496051805001c245900301d8270070340c0600e516168041e64901400c0045090303800442c2003a070070140c20080b21049a0452011640051140e20f01103000c80b07204000848a800a81110300a50007184e0b460484940200c4404609000007042c10b840200c0d2541c244000440070b0081010901c230540040d07081900c2040c100c0196038001400b0307460f4034401c5507903640c0e54030201c3c00724094807800011405114901d404001c0d842c40b0304000030340d6007280756070880360210090200c1c6e05d1000c4a2109846070f95910704c09002406003c100036480d1480b018032a1b03e4084050910202c6405003c2d5007015a41a00c0c812026101802140340c013242078100120f500e8071680daa854820f015488681114120b1081000100c0e140c0d1000c8900070486044082d8481039225146580003c42e54030000c404207200740d22002c1219551002c4031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 884242661 1250 884241411 884241419
    0x1b010b060d09170c030310090b0a090c051303030201021c1107021c0b0c03071b05060a0216050a0602090a1a0a14070605040b0906280e0124060e040c0203090d020a 71
    0x881608040d6114844c1d800c04800c0041d000f40260511008008042044c808060303040d001c52482840c900841d021280c6a26003181107a008030116840782154071010401d180d90703420000d00070741250403598003004030b140342c120340510903000c0c001100b295910410715000380383e420080103840c007e020301c003a0800b1207040d4011400346551207128442c0400c8090350381c9800710005001003105d00c0c286c0c0b100d0510207880c60114500254081c1d02049640f0010ba0320108004105410f00880d14000d04600c1424051400c01c555a0081d02c00188255400c01c280317500c1d03601000d4070507460031804a04407020300016407003a100d404e040c03030005a1030302d0f00c0d85031a025844d48402e40d007084505030385c0184108144903080004102d41a80403902d12096184003040076410703108180744000610340261110b102c40451a000c0d401842d0341c1c960880410307020b0b1a40c182c252840a0a07100d1000450104c101c5007005003018003540e81000d0140d030103980f030624800100054020300810907a0010b2128001003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 884243911 1250 884242661 884242703
    0x203040807092f030907050d03020d0e030c0303040303020f011a1f0306050607060c0801060f0c0b04021206041203230a18080c010f0e190b0c0c01111b010b060d09 71
    0xb480c24142c00c58030361300d1070800e900b1131401c8455409a4061000d038140040843c4c0d010401001c00031a903c1c0080014500a0010b440c0031401c106055060000040000415030005090341d4250311200080c042000b182c0d00c01508081c2901186130030101c10f541c3c2c6d0100045420010204c490b89040005000e91100d001c1001608041812070703503d80e1310000d050515400807041070040840d8580010313100d4000900070320168000800400802d0004c0114045503903003001000c0440c40d40c3c0845c3c0040c5014180403058591282002000c00e01e8282c07110306542c980d20955030408440c1d4808007154891202040003009510810060b4080c0e800a00c0c0010700b6403401450117890101c0085400b1200d40c04410444850100b40103d9074002900e032800d0500b1025800110b0f83c2203081020300383d0f1001a961010710032000304180380e5203401184060301c000940902112106800848000b04500e00268201c410a18645070702ca9818810420070039200d400091415215240c1c0341f6140311480ca0749 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 884245161 1250 884243911 884243981
    0xf09040f0f06022b0b030d120207030504030210020703170c150c070213020d15140909031216120509120a0c15060509132414071707020304080709 64
    0x140c500d80c0e44c81c03e41e0124100030b0b02808441c910128040e102400c00c03010090030005825070b07440c5006801044410903d806901914011a0050305da800c280218880094581001d400b0454003000c84920340340c80703110300e9010745810018000007003005005150f080c2c40b01c0c0c48014081481e24500700004401078840c064080d0528035864009a11620320740f03512402c2d501002c00c005c2d9503075646007013002a0120800c03645141038054903007a1441d01c404078254114450044160080318004c0c0900c040c240501c04400354000b03080e170b500b08140300c80048160a4a00907a050f210541c811241e1035181e0307200c3c80007000714032454113101c580090243d0340c58a004a000340c52100080c2d035608100000c1c100740305400d5000d07041e01c070b050010003401c0d42c9888000c0703103051590000340b8044d0301c1254540e100350300182c1110b99030403528034076180801d0001e1a8503a80d500080384121501d000c0b4580600010540341075030040800b514a1508104400c0c00a102001c40369000582d04810301032803c036081c280c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 884246411 1250 884245161 884245207
    0x903180f0a170106170a050316060222030b15030307060b030c0d0602040906080706140702043905030730050f0405190c0509040f02090112020f09040f0f0602 69
    0x11138031903d03000341188508601c038020000c50300040c06020000f034000c0203e9190540d10107010024500b6414898028058402102c0c0041e00341851000c4805002c510b11040380e00c180e84d10302440e13a506110000e104c0caa4400e00360181d00030f005c0400001c8050300b018194140160441d50990390b01800615034070741c080c0083c0d42240c0e0015050000c03607a00e0180d07038040c1c00c103070004040281c135040000b45260924100e0051840c80400d4035400c5540e141c000c501811840c0440d402c00c0c14841c13030201c0303010b0350b001c9000500703401b0003601d80c841500400070b0328070800d5103032100c03291030b503245206a2466404804d01c04414000c802e091411482d117106031401002d42c5002c10110380381525126103000322a2005211002002d85a40e001980c071620a10030788505441c0a412616540707031481c000c15a40358001d511161001c00499101910302200e440c1c98021035070340344449215030502c10b5040c8141c8010740141d01c001051070101d00e078101080c4801d44103000c014500030000301284ac2100107440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 884247661 1250 884246411 884246413
    0x6090310110a0306050604050303071407080109120f0c240906060602070e010902042301051b060a06050d0b13020105070c030807030807080f01061d1e090903180f0a17 73
    0xe508502c0381d80b41c8540000352209550345c1e4034141c01c10000035528000d03148004e02e241010342d50344080340ca042c400000100b200360028414111249040b09002c2050b2441340006a18504a08007541c42030318808550750308911404050000c8404c101d5003480040f46101c00c0503202d200240008200d031041c440108079950207400658213204002c40f0b20315040e4000c0c40d805c0d006000501595100c100650300341c41c2006c2c07010340031100c280010383d940c1c0034a5111110f080440801103c0301034020900c544903440d2100100f0696840c3c004000591500700b0000d822441714000217011808410003a4002034014100141840c58a030b8400e5548100c07508112130030701020a10300c0030140c01005442c2c100240c0d080c59035091410045952034450140300d40000c10020b803102c0c030710030086205444c000d800003a01c924400881c00c0304030080f0801042e40980a04092400550340301008000c0c0c070360018155041042d00581b20301003100c400c50181c00581c2c00186584005121503540e00d90a9810034048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 884248911 1250 884247661 884247667
    0x7020d050a0303050714180121050a0b01020f0606060702150f120c0a021504020604080d0818060c0a080c040b0a0c0201020f1f241e0617060609031011 66
    0x407a00500340d81c4050300d400c0c06d110814071500300642d00351041d10f001c204000700ca00d502c0741800b801260f00009210a4180c4402900c825036004c0c1c2c0503800c0184100e50070b030700501c0070703c100034012682c3c6c441440d0140f0158012001043d582c0c944403000700440c80c001010305a240040498042c03075540140003015101c3c10028031400c01c010150f6166501c52440d0190a0030051412806510b40648046d41003040c00b0a400040441d86c5500c02d0710041c0112208a032104400020050202c040546a000b003000e80d0a1045440c17110000d4140d1045520b0040181400a14107003901c1c030320000740901491003c14800882e9001e0700a01624140c1c005959041c24246140006414804040c81c04282a0000d80041c2c003039660055081e0312510b4840313000078020301900d4144061078149400074801d400041000502d0201201115003048460b4040000e030380c0d551030f000d0b00c0740e4880d0f8002c50070f0740f849200000d6071450106c0160200c020058282d40160302e110a800089074455007550b14072007004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 884250161 1250 884248911 884248913
    0xa1403130816051908030106121103100509060a03120503131203020702041802010518030705100e030f0d090b160210110c0303030603062d010303022a0f01050a0507020d050a 76
    0x2007007600500091001c407103003650045d1311076907028441400303074206012802881080c40d02d1a40e0041f051903001c0d030070054aa0a14407404607002c03410b4451207104180c00d01c04540c091600c280280300b101d41c0a155844140c4003040140c0b4035030402000c06071001e400003200c82c0400c002d4512040c450115550069444085204201c1100d000318200000307910718812800c0180d800608941c880120340358840c4c440744810700001d01d03180722604003e0700816a00c00d44003d5540012002442007412000d44000c14185c15000e82d40d03120251403480080c8903940204884030401c1e00900c1d01007580c1d04003c80183c4690085021a14640002000151042441e4200280a025028901008401942c918104107001079030300d2002a0050302d07200340b82c08074074034010610880d000381019410611110740da03590070041d444691805482600c1400c1820701c20700760400640107100c00500500107001c104421004403083c0c3c100c900036000b03100042021801503640d50a91440c40c6201d00b0040491080c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 884251411 1250 884250161 884250163
    0x7060b040507030c020607120923120a020a170c0318011404030201120e01140a020c070905041e032304140402160807021815030606060a140313081605 66
    0x1c014410020140341201c000c061a6002c102540c100caa903150280e081c60240c16a000200884d44000744000003140103141d100746c0042401e00c2c1da89842058908547c00704126891510400a090700181c000141940001d0301044214105800d01c0c0021400d040304403c0b000d02c0c5a000800d605507010b141444200d09681c461400c102d80c8100e000c00b40e06061541e80060002891864220011a1540980d040408007540070120354405a81005014240000b2407402035201c00c45a0a040c0100300c0085080d03a42401803900542c1d000c4070000fa180045000c0b003c10744170044089040020190300c03007034008480c46183c4281e581e0341d0b54803030740c4600d05860540584401450703180954014400d4810340d030300350881071250b550428040c540d43c2e0081e00c0000ca15411355a8004141c20503041400410407000811034a010401d070100d0b45c19403600410403c1e103006d001200b40009441c1c0b1203030b00140d0111307c05140c226403152400c0300c4000711039560b0003141e0003508184440c0c282d2070300c0c840b00b4800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 884252661 1250 884251411 884251421
    0x1207140424110c01030905010212070c15061212020a0203240f060609010f020a06023408090d060605060f070c0e0903040504091a09100b120703060b031207060b04 71
    0x6003820102d0206084040030303030b2128809045941450780d14480c90060004c20740448444280b46003200740549810381014181e030041c42e1080c5c41c0c142c07035442c1074103804005e4411002a152404984c070845041591001d04056120b0300e60700450140742d00c40401604d00300040464610703c00c0e251184400a07100e15008004c004002c91284010102880703101d86400c02201c403c10428a058401940780070400d03854001c101000604280c40020000d03680540e0303804c038108140c0d2090445031001011428103004154240b40030300304140070031108166107407120540100511410010404640c0c50b0001440743d041500f074000301403030000341c0c0801c0007a4214104094100440320684c03504110303c09903507900840c010716014a03580c80d080700a07c0f0702454400d000c101801c2c40a4030614100450949070b8080148842031282030111006d00381c54411f10351034014146c00700410502d031035038075800d004c0c121100001d5003600620122450052001d030003050303207901032034001c0303440844002840304070f607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 884253911 1250 884252661 884252729
    0x105040e01060c0f0c060807270b030901140405030309070608011a0d06091d010c0c111c080f12010e01030206030412090b0c010e060f0c12071404 64
    0x404100414080c1615031044581074580c00d152540f005050b520700010044100c2d40c0150080602810004416134448100d03445003699580c0c410005a12442c18112090302c00081c00c0c80c1d40c0c404c1d0050008901c1f840241d80e206440a00110700300c0e000807484121202c00740c50a86094000100b004408407041041c0c1004191a1030700c120703158074183e942c3d0251070024299810861002416034510955900860040e100b2980d04101400307500e05c044907000600d641a409a5003420750b21405240a2492410101d8018804680711040308080016260a5103189235050f18100340d0000404c00600c080c110302244604426550840e41c004441260416400780881c802c441c8014001602c41c0800c1e00d4200341c0c04a5480c264000707090060320160040e42040d401e294000c80e2015051105400c04c104d00e12481b0152182510749003c510903404088400c0c1c44852410401c00401c80e00e2030b107000f98444490300d4080302d591110501100c061b07002d40c2c043c000d4580404800300c0c0d408180380d00705c8410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 884255161 1250 884253911 884253917
    0x3040f06090521060a0b04062303060c0903070501030b040207080f0d06050406050612101715060d050c012a080714060f01060f0509030d0504080706050a1d241801 71
    0x1038245298113599810010b0401668130b0b200c0308140115111504003801801505184070018540020658408110700c41c04178424441c040103c0c1040726100210380f41407101601034402c5904003401035010300200c071600398101d6400c02011022603070b442d020b0400411130194090342d81703da1842407010f0750656001548124540740040006a41d010101d442481d0490765041407035407000400480340c255603001e9000d100f06d01c3c62005903036030089807010510500550440c0f25855500c140403286481610040299220580f505925802254040e40d0780c0f070300d0b207900d890503001a07851020084071024103d51000c00421050b0030403107022441c40e159240000142210300e42201d2200303602070107100d14070500202c1d14401c41580c0c442d0089482c0e00c0c901404996240b003940c5001000c561241c400d500241c002c4035804181c0602c41c0d0110380301d00c07516030380e03c1180a81018103884084040310046038084410798000480d0348014000016460001004507201c079404d06502e007407150030104140c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 884256411 1250 884255161 884255209
    0x100f2a1a070206190906060b0d0f0501050a09150b0412020103050f13080c0309030f0d0305010812180a081f06091826030a0516030603051b010203040f060905 69
    0x481c6500240655210007580000700d20704e040a1441c2c80281003a8074081c2909040c221302041c40c0350b0640092100d40b100403170810032141e44a4901c030071200280242c50b405400302008000c0402c2c2c581002e0f00c0180841c80130b100c25660382502c038420380c2c02940200c0d0310182c0310380b00005540e014803070982c0c8000b05d0001344100b840c0459a60042c4889528020011840810800000d49082080c0d0342103040150446042c0440086e40d907a896041e0b14a6200282c2031000104030f03020301280c0d01102040000704181040c400f000c884007071030303003031042c094000301c808400040c602000c1049100280001020740c048660300f00d03d5500380c81c1c5e99000701c00041d082040492081c1a6403242600301c54100001403a44248034100462003145000310f803407004004030611050100a61280d03020340b404207c0101a1108540180d0a84640d4070025095400c0360541090b01201e0303030840110010144103403413805460b4100382d4a4200b060304414001030204a050056060071220300d0039800020403c1c4003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 884257661 1250 884256411 884256421
    0x1206190c0806011d1e0f040216080306031f0207030e03030c1020070c0f0828050703080a0201060f120c06050f0705060c0316080105100f2a1a 62
    0x1080000d07080d10304000b07a40d140b04201d4140c03004c81d41c1d20f403100207049501c0e00800c0c402c02c05843d000d10b642c40c1e2280d812514440700621b424800c0701e200c6042020f000224042549918506400040501da003501595040032850140507011100440300340800503141c00d9141001042803210440303140c0254020811040c1c03680d00054030402c0000614000700d108a581d03149007010150880703041e0b100c03840124060342000624040d20041c2c5040e003900d084200d030345011181d9210030030020103040491200720000d4064002e13030807140c258080c0c01159aa56900e5407103140c0ca6101a19450041c0d551392800d01110748010040002080e040b84041403450840e220340c0140042c9110301c0781807203400610340302c41e101210142e030040b5402509950746458207030100c601940c03080308c1442ca21141a003030404542e0240c8155810707200301030700310140342c1c244075002d40d0b003080380c40105000d108505a510160440114000c10000c04524440101c98000d01e00102080e01c64403156540d00fa80c03400b000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 884258911 1250 884257661 884257667
    0x120714060702011505040f0b270901060509150f130b3d120f020d0c1b0201030b010e060705010c0f050403030806010804060b130b0916080c030c091206190c 68
    0xe550307003290b00041c1400344900301c200404985000c15042040424030f0f600314200c400340030027100541e1200095a61b030f074032151422a05507000d401e92007030540c80030408000e0200b049503041000074040300405441207001460010a100f80c1d208600e84403014410141032288904c4003500301d9215a42c0140584100c01c4800c2c040c5106043c00102c840c118010700700d00c200c18420310701c41030080820081c001094120043d500040c082c400c0103080040b04401030348540020001d49010061074203400042d903004401811580101030704001410110361a01d41d600c078020080d1074401ea0001886080296001d400d140702c055540781404424003003000404e0300003202ca81e04c00c009203814142583c843c075014000b4180000c4580c0c00090900503a20b00d01861f51041c1260107040300e01310f071301799100100622580c1c00149a00001f07034041e0701150403d2405c0000c4c43d08201071210050800c4400c8001c50744147c2c2000b904d55403544180e0a00c2000c80b02008110200c40031032006201e0306050b41409 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 884260161 1250 884258911 884258951
    0x509030a0206090409230118151104090e03130614041707032102120412030e0a120b01150305010e07050901030f051006020c03070305070e0912071406070201 69
    0x64010400010350307a8884d5201d5100484440c0d0080c2c0c840e80300c159118030790300018004070311010a5868441000c010041d03140c041825264004006000d007003280e5550b602030407448182c0b17981d010051001040320000c80c000c52481c2120705005540307554903d124007580d1800d80d403202091084d508040c46100c0c804030200e5040c0c0f92818039101c000901d2101c240d01e001003551001d010b140c40003c3c5a02191600f082085d2a14069400c071185035034003840d804003521981c452820540c01030818a40000e02a028192180307000411041e440303607540801641420400700f007152681003d00040c007806260154140c21008140703002c1040358140103882008980c054800300c1884000f00720001280c0c03103500b0051305108052010302080c01c2c800525407007800715000780405406408030818042c02c0005900c411243c04c0001011031503d80350400b0004030f00540044594000c4600b0b0041c6840258000c00c501c40c480c5900c80f1408590345201403e11001410200071079052a803e0081070090003c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 884261411 1250 884260161 884260163
    0x2070b0c041a0c0f010c030c02010e0f060106110a0c09020403030807080405030405040e0c120c010905030a050303010603021e030915010905130312060918061508030a0c0c0e0a050105100509030a 85
    0x2110b58072850383c4600c500c0c00c410b96800b00c00540c280005ea0b103070b40d81c0c15003007144114240d4000b403165000f14940385481b03418030313113440e012540a50010002d03240700703a80c1213003602c0c0c080c010307280c070356100361220001d10282d500040ac030148c000608108140e48a45402d41c402c1032482d00340501d0800745d45450b103a100354401c40e80325079220410040c00b0b03c0140074810001c0c0c0000c0031b04c000080c2c00030002d40c035001080c074128045100301d04001114107000c150104525407010155185070300b0000158002d4021441380c01e15640450060750071581054021405106000010031860001c8a000085083e05802080403d8148014082e0410099040901d202e0f0302d0300b4a088030031803400c0d0342c80003450741e42e015188150404002c1e4940c22600c10000da403c0d0300803c2c003440b8042ca1701c0d0240b54a80700c14850070b40c1580c010002c0280c841d11510360101c00d42c5c454a019880c441c0e80707402145100d40c091726584540c0352380c0e000402c403501e40a10190b80030072039401c28a003802d42e4200041d84610308514 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 884262661 1250 884261411 884261459
    0xc05060c130618031709180f09031602120705060a0509040b042304060b0a061110020a0912151d0d090503070509060a090e0a03030c0206040b0420040c0302070b0c04 72
    0x1c54020686805d0084e41c0702c450001d071410089104607281030a20381026030340c034221008018080b5011610110840b400000d840e940070403580d9050b030a0050340c00340084220204e008248011802e82e686000030f0850103600e94a40f070725030001000b0041196020070100344101c2c80d00890351258039002000d045003480760000305985907910304021028010251519600015003503001c00d05540040344802c40c45101c80446421901c4542c1c010102d201b0b070b514203004140500020842170b40b8400a81c0f87d4240710380707c00501030442442010175100c81c101e00610f540c1162101c0e0604200400000000500c245400c10546103048082600d40320340e030107058050312069001444580b5002c030034400410280782c0400c031690000f8196600c0d40405c800840019003040b4000c00c3c80c51001504500071904001005103d890b1650f80301d04964030035140e0800e0040c1c44011030741540d10761150b5060704c01c440d2405640d4811502d440680140c00800c8110310b00014801400108011210341c800904000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 884263911 1250 884262661 884262683
    0x1030b0705090f060406030204060306350f0a06091104060b0414012001060303120203060108012d0f060908010501210206040f0f150509130c0c05060c13061803 70
    0x2140c0c0c41da83c03202d281ca41240002400180c4254507500400c101d40044d0740c10404d1036209d0200004200f01d0316008211200030313031003001c54004000d894543c6001400e0480313901d0704000308000e06000c80a0420317200d580e41d496511f0280035500081c481c04103030071502000641e083c9145140103005900130013054021070010a40c2e180d01403040d21600002d1000748072003031046c4809803030280210703000c02c400140081070b40004072406070084e02d008034416121101168205030310740d000c0011014410220300071303500c0d290b1603007040350076400083d00d044000701d503003141030017409002e030403880d444003000f80c4c9030400400805401001c407030050302800d580b14459a5050002401a0299030445620358844505c002031801c84421103400b160014504443c480b1421039099820b80905000c0320b0700112240c00a0304081640d6114541070111410701a14410707044d10342c0e500d45101143c0002c0c00c000c00261141d591004081c56000400052800140030070500507441d010131100e2000404990480e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 884265161 1250 884263911 884263927
    0xd020307030b1308030114120d08130305041206141e06061308061603150b03070e060d0e0a020f03010c02032b0507180f0f0302090c04050402030f09011401030b0705 72
    0x50308030f102e254895840300d10b4120300011501201d0321075407100880700200c8d0f80c0401c5540c03200c502c0752070700c444541d2160030080654007041800c8080007070400c070102d801140a140020f0075400707808000742d2a003920411071850780010b80400700e03441c1711058109452040081e89540108251811904c4071080030b1910b200517080d401c107a100b0f004a00130003049407000020f508420003103940a226401c1d903040420518041d80c003400d15940000c00c00500300a01543d0391140740c903000703020b042c50003d01400b40310031151054540361443e00980198815071400103281101300700b04800801644000d0107000c0c3d9240b00300d500658000315110b0748540d1640800c9107604200032041c0c02440b0300c0c9010b076002041028161000789070b0742c500400209201c03946819601c1904c440c0041c1a20b41410741c0c00700b0104001c000c08883e04040d0400022400e40c0f0799002841c0070b0f01000300c0812007818440001401e60310054141d160f0504251300400114903082c8100e60003201c0ca0034119070350300c1c007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 884266411 1250 884265161 884265181
    0x60f09060f01030b060d0219080f040803060103150504150302010314060306010312030e0105040c150f08011806050a030f05070801020a050702010f020a0f080a0e120a2a0b04090b0d020307030b 84
    0x11006955a503907c04600320301ca01023443c140a0380450343e40e443d01c8140d80c1d2810f218041c2d410946014041c00f10501c001820b9500940c44211041c441c11081000c4039501c500240c2a207100d204c008030501c804070700420440d6054002c444038500c0f040c0e6035029a25181d00481d58423201407001134404400e00c001d514034103000b54480c03410004844020702180c5820300306440e45c449180b081c2038120111400c00f00050344100074891007007110350349502540e40303405030105641080e016030005182d0355800c00911a942c04a000380194800c0d90840d20300c14150a2080c200984e550181150ba401000007001469000e404c54440d680c1c2400c2c242401140502c2c228900846980000c0080c0302d040c50350018090410007800032410655544070840003c0c00030310039500c031a21031002040e488607030700e04005200540344500c10406010256915041c60f1043c001c4860300c4e80c003003808210700203400c2c010070005004407207a603c802c0d583d40d40130304000d50104c0c0e5203805621010703011002c290301140082d12 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 884267661 1250 884266411 884266417
    0x40201050f0d1b0302090a030206031e09010b0301060b0307080c13090c081f050307050607031817010c032714120306090f060d0b0c040302060c06060f09060f01030b06 73
    0x441601a82d241c50451520900410040101410510076040b440030814880e00031148400c50191183d0140d51855083c40025040075014030500000100805400000324410768400d0a540c030000c80d5646d000340501d0708490540d04210b25038807040040141d51030300f04c0041600200403507485a9920f011594070202001e80350000d9501d0b07810124038034205070340700c01202d005140810aa49045400300c40a0b40e41c0660b03481070941541199504100502c3d1500c042c102082c02820b041c00d2440b03a040d24603088030010303006011161205144442c010300c1c00d2042c03503070050903030404115100800003840500b1809d07110040c1c2c0107080420190800880303d001081d14195581203038040b5101003101002504110f0364180160391000c0060080c400401056018800181c0b0196a000d0b81e900c410040c440d00818040810b1410440000144c90318130040c001c005c0402c0260446042034020002c6110100b050180700c3c4001900384600ca41d81c07110071740d0f010034090034000b41016000c0007080d4580 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 884268911 1250 884267661 884267677
    0x10209090c0702040e0606030a082a0718060e060609030c1302211302012a3002120903010603060e0105040b090118030e010210060f0f050d08030c0304020105 69
    0x559580107108a9003503400242060510071901880a641c0d10880d42d40d4507182203654030b62540c8050075070804503142d00000c0c80c0c9840321700c2c611001c0c036082d0400c03400f0341d00b00c07072180712515400004104280c1d404020913082e5071421150512003213103014000b00480001a149501c40c1c3c000048034a1555404c014034141c801d00035202e20001e5004d0a074040094020b42203480000d4070440c1c80090202864007054810a5160101301c207400e42600111072030700e0401003084011a01e11400d04006a0341442030004034840c030300700100c402a04c045172820081c036403288243d803017010741d180109640100d180c420280d8486021616441700800017805024183c0c8042d00d4140f0702801e00c3c40c00c00064000511890150740c1000441e02c554441131308071810503003003007103043d15038589200003072180c1280041004148110360a40e228004c5000480c1c0d00780d4480304e60400c1009d41080086a0610044020141201c2800c10a45c2c11345030b404c040d200040122a45150000019046a000d04240d403034032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 884270161 1250 884268911 884268919
    0x706080c0c2e05100f0902040f03030c080403051c030c21050705161506050121110d0f0603050c01050c1510030c141809031204150f200f040608040302010209 69
    0x90402070f090070407180290282d0345c500c407070016020030f0802503402110203c0c0c2800100c8000c19156880c22284101840c100301c5498004010000c00709004000c44c3c1d08940d002d1001c2407030301c03400000180c100e420000380da40130700c2280d040c00d40c100da00d80382c4a8020003806110200d0160707500b180c01c0303070140300303928254501d031900d0315480c018412501904900c1240b0b45004003d0141c40747d005484501a11800300810901d84508480c001d0352904031311410189002154103181d142c50313030501038545641d040d04040e56558000c02c00d205003001518100c140070300f002807501800607541a10f4074025210030340401084030100b00ba00560440301c00081d60846881480301e503c0c0c1c84a02c015200480301c0d2803207083d031440c407803401743e40340d401c80c43c016002100118540802903135540180f100082c802d88000c01ca507400c1d414103210368090000d111030100300c006454507210803050740c01d01c54408403601440341441103000400c651011a0251645402c4c14022030740c5601d0120301a101d8000050b1300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 884271411 1250 884270161 884270171
    0x6040b040f0c08010302090f06130b06190e030d14070f1416061404120b04051006140a090e03040e1b0f0a030b0301090819090e07020706080c0c2e 64
    0x82c5690050b0b1031816280300710388101103074a40c2c481400310a00c0036500d09500408480c130886200302d20f603000e021004030142049040a140000280110710000e200a0111f990b01c0100c2e01d00d840d0901510074240c585041c00c980518030042803131040d000e10038005246500908510f403e12581c3c42811317040c0d002010440d005200382d051961180000c503c1741c540495500003400c106039801304180d070705031120120f000d201c008998070b80c00c0b65131341d000c0c0c81668140518184900c100c1894020800500f01402c40c0c2804d041c143c005000008103164005d01d1241d01d0056490002d80c4d01108807400c980414000421503110100c1441c41d00d002004a4401d1840c0010031103460b003400b10103010b0017000c686040100e1464503043c50300703071220800010003c0c0d20401110401d01542e500900f080301c8185404074100340ca0341526015100709850410150340010020000650b0060340150b0140061111074105207400d540107507142c00c1a03196150101040d030029203011a41c03240b03c02e06c4440703142c060007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 884272661 1250 884271411 884271431
    0x309062714011a061c0c1d01020325020114160618240905031b01200403060902120d0804030216030c0b0c0a0b01030302071e0503030306040b040f 64
    0x601140c06602140c004040d0440ca524a503018400e540200c3c20984a690b0306040c03000400c195a80410501039450001e0052541c44544620030482000a1038840d010020760300d007038204441c03014114403811580200482c02d8010a116480680c5201c0202e40c03051041440c40181d400048200d0f501c00520004261a1040020b003004584490b000c0c240820803040040c126180403040010302900200444251804a80c0c05070032a0a2680420760300140c141425500c090550740a4070701c19000414813107650100180a01c0303038a802801640341c6502a1100480c0803110340654403000e05403e0356405884199283c13443d000000985030f0083d50040e01070600040c211b208241c0c1d003500148100440f5030704e1050080f01c0d88041da90002c18440b85c943c82c000d40d56519a00606204001d40650038010b070004601d2210540a144640c028009181c06d11001c400702105c49000d1a0000c0c045410070002905d0100c1100c1e005030f0141c80124100c8515400700b800b800d009091840c8003490000e40d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 884273911 1250 884272661 884272721
    0x21504030b0106031103060118080a15110a0c11010207090e150106021204030212030409020f0a030b01140a0c0f0c140f0405011a13082d0a0503030601030906 69
    0x2054074440c8624842036621040f044040310205280750304664000c0021132240c5d802002100d6000600040e0354003a2a220000d0b00c0c10032041d0700007116a91072458480388507442e07a0103042c460543c50140242044047d140041516040c3c08020307241e00085280c8440f43c0c0d00c2400400082c150302d80d024001d030794030002d41e41d81e2403000c40600d0100101394000071517080d1000c10320801e01115481042d0916003180c08201e00c080d59034040351064401084000344064850001c2c20412220100141e200d524109002d801d640122605504000d0900c40441060030000c2c255541a0340034501198031150915000d804004031040240034020384500000e0402c841c0003906000c1d81d8284c03080c0c44070b4410740e000c0c082511000c1c05281d0b442904410094070500c0402c02906094812021500344907640e100b00a003001b505043e0410989152003040f01507200c0c1c1c0080b031203030300303650b42c014815035525849084d00d030f00003d0052810103480b100201d007400a103400803100c56000d07043e001c540e03001041c101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 884275161 1250 884273911 884273917
    0xf081f1e0e0103110f0103090b0114030a060903020706090602070503060a0b040e100501080114010b070305280201200c0606011d04020f120603030705100b01030f09050c130b031f090215 81
    0x2c0c13031242c4c801c03a1700c8040b5940b19028241e002d035402000880181d0a0141c1100e40f02c8020300792603014031079000c0440206025000b0612001d004c0d40280444a04103400104180d0482e00140159400550100201d4400041c0d065004290240020b950420a00001c016041d00125580c1510808807a450015141c1d40914101c8141100800c50b01c0c0640b22840d041010134800d80c0d1207210248010004240507200074402403101d403110003180008265510200e4000380c10540042c0c0d5642502e9801c81d0000740c070840f03001c2940007041c0c10150243e035400c0d60345c40e00400c014100602840310480581200d4000752103410000c00942d11403a40080b5503459030882101c0044801c501400b0030900d08000c001c9a0845411001921443c650784001740017a019481d44c0c5410140c0d64604803c0300200f80c840d600c2100e01c9130001e070801007034440030170080411240c2d086109500d404400050340c0e0300080c1c0da1710082c1c80100e940d210005000100b200030070030340601030740044da0389200805007000750b001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 884276411 1250 884275161 884275193
    0x1b0302010c030b0d1e0606051306153e030a030b0f0f0901090209010c0b180c0303090f0112060305070b03041502040e0408070f02100f081f1e0e0103 65
    0x803c000c1c000c2c3d401c00304449a200000090621203020034000904007001c0380c01081d440c014030005c241e066492000c118100102503400301d0b2240d0320041448818030690003040d0a41c12450200d40c440c480c2c140030b100300344405800d403c101346106410074000f00b03440c1c3c0c101e004180032410340361076604040000c0e01030b003c03100565100e00d42600b603425403031800c2107000b0001e10024101c40386982c20000e8080080d8030074280141031107100441080020041c60364644205160300b00340c980c950100f00768601c1c05140707000c1d4500c80d410501485095844c1c1108074029040c09280031058607100f6092840201410380024082e8001c4100203d11042c143d40154002c0c1c0c440c0c043c02d1202d28205d403410089000c3c40c05600707201c038000c0d00800c01040615001e8100b0030700550350344644101c84da00050b00001c030391140401082c000d89481e90002c0d00284e86690116280b220150b941f0b1003025903e400d41054002c9003483d110000780c118002c0382440c0714002038104020305d4641035849050424400b15104a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 884277661 1250 884276411 884276417
    0x140a05370c020a0509041205180a0b04030213050105130906020c0303090c1c080306040e010212010905010f0b0f0a0f110f060609010803130b180a1205012304030f1b0302010c 76
    0x600080d071404e10705d40c3c02c0d200316003202019980e07000c1e00c0f4040f5441d9209145954580340064001c0c6d545a5440100e40e00030304c00e170a2281d41d16450b61041c050466a03024043c856a031800004110782c0d1690441c51000300307209030300001c40301d5007807805400074003a815120039648000710410241420000314601c607800122900381d01811519090154042a0580241041000d00100d001410113810480ca40b2141100240c03c04400d80035041b4603031002d0340a000820348580040000301d0445405001500303000e1840d84c41c080a501ea422101d10422500b042000702c0305403003101c4544501850b9904062203c1524050740d0000700c010f03039489040d1a900e200349401c40000552080020843e40103408181d503600d11075107400e1030005a41c20220b408200704a8844c0e0040c0b02d50b803000c08207400713044509240070107103085082090842d1400012031070a502d40908241503103441c0441729501075032601d006820040780441c00c0780c07607510070322140c82070140c410350820030180c06402c030000d5990315135 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 884278911 1250 884277661 884277679
    0x80d0e0909160305031b0a030e150d0203250e0109140d05060a0e370303110408030c0d0f02061504061703220f12061d0a03140a05370c02 60
    0xf0706c0b041d15013010200003400314120821341045d9082c0030014040c0302c00203c4650303040c000c0610043c810b9a000322000358400d0b501c030030544494844c0d01c950440f140c0c0c652070984002460303280040c050308000d01a00070074620300c251205c07041e516203000e880da0903030080c00d451943c00c0000007200580110000c0e0315142c05988031981c0010540c0c2103070f00e206091a2403603240f2140c04101603500d000750000950416880d61044d814030b2a40718002c00040425000560b61070b0007034581182000040b1038100d04009401e203088072400d5000a0142e000302c02690300700c00600c20000001c004106542c06a040c041c000e0007030f07034001e800100c042c10b00b801c03000422100482c060000854191824055144d2000c907150b403d11400e285c402d990203c45210300c40005401e0150218640f400104080c004000d82c04085d4810401da8000c07550f0000741543c034605410020480c10140c83c9000c0c801c4558402d000c4600d0b0b103203042c4002140614002100c040030300034189c40250040024400250a0307020745410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 884280161 1250 884278911 884278957
    0x17100c0302090d30021506041109061303050703060f18051c120501030b060a0e0f01030609020f1e0f0d0206070209270601060801080d0e090916030503 66
    0x40c1c021185501001040518080002c0d40d88550f00004ca50041c00e0624034143c0c2c2c00f408a40d45081050301c11000d03002441c043c65003580100d200b0000402e020b024505105620044800d400301742d5014641c11504952581c01001050307000a850368070241c09442420070000a01c800d035401011122000d500034458a01c002c002d0700d40603180d03400c0c0240f2503032000c1a01c161000fa120365409070ba170300c40d180c1200e9440344c50301d803c000d88101f03800c1503d2803c003100a00c404c500e490812000108000b44aa107207501d09412001101801407102400c000c1d11400b8510440d5104201d200782040c0040841000210308075210015641c0c40b4010b40c01000e8110035190145410b07581d0640259000f40b0807440d000c000c0e401d001e9017050243c07004101ca4424104043c82500300341800385c0c44441c2100030000c030361404100400701d00060340200c2e0107820003c1c072640069441601210907410584101c003041e2561001c00389455854154000110b001850100c10410040005c040005c40080c900c0004050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 884281411 1250 884280161 884280167
    0x150515011115010e0a0e070807060e09070f08040602071a04020f040e12130308120a0506040b0303031b0919030b070e06031305010605060307020a03020f06090714060417100c 76
    0x141680550384402c49800402040404454595014481d000040b4809050034802460503400e600550aa90450703078050102d40da1103150369000c18003c840c40403031410407980203403107c1e03c14044030007084060300004040c04002c1d01122010b5501c10000d92810183e4089209906402d650803482040e40c2211200c5a00c0c01d8000c01c504e08450b580640000000d01c80a10030700e50003105490442c4c100c0b1100040802e15031000703400c191180e03401a1070249002d00b41001181c0c40204890f00c03843c505040c181c80c1ea2000016a41e2103550b4402801003d0220b900810080c05941042c0364000905411900700b0451000b0b00b2045a1145800b00b003150cc0b000720548180d0299003001b5000706003407001801d80722110800c06005405030000095458880010510ba030b0300841310000940d116240707207010150704000c90540d10016202406160505403c42500c40c201c42c0300b4245240030f06441c05183d580c070f440c210f4005200085031150150044a000c40e00d4070800c0340c081c2c40341c4e4503240281e091140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 884282661 1250 884281411 884281423
    0x1c050709050603160305040203071208040311030a0b0103020423010f03211e0c12050304140a03200c12010e0d14121f0902190e1008041505150111 64
    0x1681e8000d0182103030113803040f002840002c0c000e0b80e0510540ca400075041e080040724107580740c043c584442e0380da41541880c42144400040c642e001c0e80c003180d012004900c490300c1c60790550354111804955440c00080e00030f02c4240c00c0c0b075624000c80c10340c0000074000001c40d0814041340d00c0382841044528601003544401c10b100281070000c034405085015624035003100403400c0746424244100c8440e00d90f1200642c80902d2250440403c600009000c03e10240c1c039a40c2d044004c0500081843c0b1429980c0245036002ca103110180300c1c2d00100004102d02002c1c85034044400c400b600690001030440c0c40a4060f08015202c25054011600f013070840a10952404e184172030790704030312854003c00c4121001042802011098204480c8030250304c80104882803c4c010180f0200250300c0d06580d602031000818814181c0003809892200050340ba11811141c05141c01282040e000b15500d9080c420414846030030902c6c03405140c40c0030044411501d01c00300b40c400800ba030b141710314007884030192680c4078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 884283911 1250 884282661 884282671
    0x151409031027120f090305160906052205090a15050a061d010303200607030e07060e0f06070302011d03030928060e030c15010503060a1401060e0103021c050709050603 73
    0x4040d00c014403c1d8070302610200d00401c5031403810003412681ea44505040c0600e141c0e210001059800e000c000c4034625000341030203804100c0c1ca00c40441410007016070441007045c0781010558650380002e840324000d1209003001504498541080450070140c03c00500707045400224251500d0008035059511501810742c03640341c40c1081c0950390942e1000c0e20306203c500720b14034602c90032070f40094103402c09020713880c0140b2498034003003440506c80301c00070304100498001100f00700400d450340101c1d0742e40010501c16984140d8005640700440c1c101280900b0b5500c5034a010f000081c4010f0300546000070045100710040340a40e4154540c06d010310ba42e6101403c442c5090540c907030042004240381d50303c00510003442c141102c2c03074004605c41c810300b0807480388010804035034008010402410240202c0360b10042030032040040480002c40c40b1004401030288000300041480c0782d00c10399000c2d60440f44407039007100c0c8516050300040c4015014100c2191103c00007014075400240c82d0804d5001e03a0300803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 884285161 1250 884283911 884283923
    0xc031b010c02030301181508030702090108010e0c06280c1a0408030601080a09021207030b13030221040911071e0c060e0609211204151409031027 64
    0x269281603011b5840740301a03424001596a29018100800d00d900296401030043c040690f40705c03180c030300422088401c1680515034690500d180da020054000c1402841d28400711126034a900480314581c0030030100c03d82070061085003424080c08141c000f442d000c0c00921881503501491054401c1d620f80000c02c0e14000d02c070040c00e0000c681c05602407a02c50350f1044114000085840745500000c10400c0700c4144072007190400007090060100b2010000d03071080c00d505401c06400c00c1503500a560f80e01ca1040ca505202404041c15440e6190a01725001442a100113010801c4007112000665004100072114039081c01c9180400b00e084c0305000401c3c9400080802859280c4202a41c0003141d44104c03991041c01003003071040e2503030351a06440c02c51014044112070705030002c030307038a10305041c503260f0080c005014881003125a0a42c1c5480c0d068111524100821004980c050841030240d0260715916014030f1107103103155401c0b540f014140d0702840b0f45034001c20b00d10311a920340001e0401c1c800361803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 884286411 1250 884285161 884285167
    0xb040f150905012a151d1510120303020a08160804020405090c1c020406052409120a12090f1d0606070c060815120d0e040f020c031b010c0203 62
    0x181e40c02400041380510541240c616010420003514400d030030740b0901120071a803944040304801003d441425403445442400110300d01c3d8201103a03a8951100404030102401035000480f10290034040100416154507100240710b031601d00a00071f904a95000c400046900c00024401c0205160151550000751206640e0352500d40a104c05130800034812109845000c0d885003403619080000c0e903c641080580800d4210070344100400e4525690045205000d000006550200e00c11a100f0402020250040d5507607040d0020551049060400003041c1c0180345031102404052544900344c2c840564408a071142c4a4010815000250203203100c490700e9546500440450030b41126040800148858100310895503801c0001880b074101e680046c0d070190902213000d4000002c1c0311180001c1314640c1c58084480b150a5a403440480390f0010030074403c00d00c20303141d12168030402e2a0001c1d450159510036900310700f5a6a903100d001c041c1a00d40018004140f1008188200360302d410b81e07980a14a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 884287661 1250 884286411 884286419
    0x30b012d0e0a0b120a080c0106050405011802070302070315150b030106020d03090f0f050a050d0f0804060506010c0813180c0c08070312050f010302010f1e050705030d060b040f1509 79
    0x3011416400c0c0d0f000304e01c0300c803800515a001c10003011031910030b01566565402d580c00480c2552007a83c030040c061400c0a0061105c800101c10031030308540300010060f21140715040480c42d2503890340c00034040c180e4a40e0450b5060b001500400c50300c4d1902d650394401c01d540c6a041c880644030034030401d80141c21603500d0010171740c4070340c0100b19110301602004102c0209629028001803491008541c00d80c801c0b0f1300c107000c110b4280035031040207a0b14106140c02405201d4050820310008000902da1941c0b14001011a800740d81c03c22125034001002a8407480708a51a04045800780507000c0442144041d400d87c40300c044c010140012132694038450801e005656004803a044000200c0034403028400070390001039a441000d2049240c01c031401c485500d03500001d071810701222007220400030030750f0700e015840403401d0700e20b1880800c600e0078079502c1000342807103806c50003100d40042c0b40c6800e05d2400241481940090025101f04007244505141e80d014801c9c0020303000070b60b03c40401c1c5600d0f0108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 884288911 1250 884287661 884287681
    0x305030d0903030b10051914031302010c240e0a1a0c0415020309182502030918010e0906070f030c1403040515160c0f0309030b012d0e 59
    0x78011034441c0c00c0214080c60400d0000c2c1d20030b0450006680005c00c086070290360846800c407000d40340b6a1034200248250b818002101c810301c402016880080085442b042c11a44a83c210b0070303134603400001c07031003040d44645107140300f030101080312000c0103062004541c640100440c031002c00030360000214240740c0b0b1150042480090040810442c0142071000156000d0101d6134224142d04503070185a0350300081c810000d0b030001120385001c80d4a04c00d41000100516408035104103d0f02040010b0307540140d2104901d1403140c1009140c126000d1200114010004c3c0c0155042e61012201c026481c0d49050500780c3c2c4070403c94154000031140100b105034180264044401c00240c0d2034852a503000072165034034a0760043c0c03000c44240e405484030b095450503d0a00c550403016000c03d0b0010a15503000050201d0640c2d03001406801c2c40d00340c0c04d17041500481d9124000e42d800342c10169151383d156051201604131003940018011030044005501180000700810340340020000d010580359640c41c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 884290161 1250 884288911 884288921
    0x11090f040c0e12030a170408070b0901020f130905010503010e06070f0e04050c09010e100e0103230103031106070201140114040905030c160f030804050d060216060b190305030d 77
    0x2030024000380502c10340841d120700404010b800e0a0000039175480c0321110000701041030094800e42d40941e10810701c40010310f01c5d011101082d13001007000459031507988220b40240b0582c844440c000000160040c0300300b015841c070408039480c1e81010046680d03250f0a05080e258080b0040c09182c02620000e01d19601030880002840c1103880e188518031950404203003101c2d800c2c4d582c029030350302c0031840b03401c070f580e224100e00c0c0260306c00d44442e020041030718406054502c00e261024140b586460342c20030004241c442c1c0c2e00701800c6040500c100c5586d203080107040c119000050042a002c1c1d5000030348400d00502503040c0e04a40241c0012107a07103414210002c2c0c2c1720111507140d019440f068980c0c0802c0c030400161400e184084050407140c85011150714100e840d41d8003018581403101c20820204401394180e81c201c86041d23410303807248034441c40c000300213115528003440d200d140d02030201c0c03d00003e58820011001c4c03d03503810385010380c109036007414000c03184802403966008020150410200e5080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 884291411 1250 884290161 884290181
    0x40f05060714030f04030b150307151e080f0109020405030c0427061b0207080d140712120b0909120f040305011107170301120f0311031206030111090f04 67
    0x4020801c4103030000b29070660b444403100c03101e1402c01240034818440d800010f030b9000300c5849a0000f81c116104003080e2250518480c003981c4407444001a06043d0040052803000300003055a005020000c85010301900410b44d0644010000341d0008243d40e242442100d0503180000c00030b000c440f1255003004045d001452031510010b48142c1e40222003542403010310403d034421000401d0070b508420029820648491201c821584143c50400003140c001c0381c8107010400f2441e05d144071480e09400c03480e0f580b041c044000c210000d4150020303142da50020182101c1c1c2030040c000c2c01100d891000300183c0030b03402d58103005160880c5100403480942a001011900028444c01e8109581d03500c4041c2160308040d140c0c0c20b5140e00049440400040368500c0d0400001d84c1002800d550416000d03010145c918a4003c02d2240d14070010014180101c1c0c403012000100300441c0d6460746100c40000b10240c050b201030f4080c4d800c103901038110baa960410340d2000d100c00b400848083c0c40b11400c0002130220303160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 884292661 1250 884291411 884291423
    0x1a10030209040c21120e0f100507080c160b1207120605062701020f0a1205070c121502090f0607061b050c0c01081501030509010e19060b06040f050607 66
    0x700006041d207050410028100f441c0c0b85200c029860350405c0c484414640750000308019044ca400300c1c407a99045034140c0510001c1d250302c103c05414280079250b504c41c0320009015820003040440c105080016440094641c0f800402400384c6e0380d078080314290017401c42c2e0582c180082000514014070a154240702009940c5010a10341d940b01d0116003c0d40c0200b90303000350b04141c860101c244484103800c0405918080c802082c0d082041c50032142c40b828007403002464250500c80a44075588070340d060350f003000d80040805020079506c05070041500540c4008940312010825002c480740050f00c02d4800340000074003041000d000520402c03940d9440520201d84a5503500c3c04030030900d280f0145c0495081107900c420303a0310401c2d20340c018504110300503172604120000c0201710100039112400341503100c080c00c001ca03998617031000403805080d0342c1c0e1803004a846410001c41d0403201d0140200e80a0780580310411074100c5042c24020503100b580207114110444090030001c90411800520241c0e000341 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 884293911 1250 884292661 884292683
    0xc060a080a06050a0f08160e0f070302120109091104060e01090e01090f0b06090c0a0e010c141b12030301152d0818010c2001061a071a1003020904 64
    0x1c000804d0050103410016400d500c045062100c000200031561001e900f00184844880c41c11000a1034120001d1103071070880191400300300c5950003a01074601c20015001009015a1a03c60007802040501e800ba6401c80c09071070b40a800307040500c159010398080b5500d00081ea820f015841c0301422180d401c00361307590340e155030b1200481c454640480006102318110701c0b00b404d043e001c10000d128094200b08902c0c4d410030034914002c0c4c1040101c138041500b82085d2422684501703110031000d8142b41250701030f0088180250103c003010050720700c030550442e1070850090740e59107100c0e40e0b40804d0003120070103440401c4050720036001e8103904e80200300d0350200d80b15820192555075a1000305088100103e5030180c1031241360020722200740d41000144000f0407103054a010010a8900d81a41c028586650806410950340082d00010082e1054130700c0650354041e00030a14506520605040d80d000c00400350340920130844152190013014a000078540c00c0341590204040e5142c090811102800c1038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 884295161 1250 884293911 884293919
    0x712020c0a06050919231204120807023c2b1a060f01050702090403030506060904112107210b1002011508030f0f160206070c03140c060a080a06 63
    0x603c0440701e90520440b484064901c000c203980301d074009443d006d56120f4202c2d83c0c504070b82681810981e81110010302e119140e100740c80c202901c0d87d20805101940141034840c2c44603040c0442800740b004c08200d0207800f035a00f507403480902d1620803050700540e8041c4c0d0680907200e00d0000c61191503818000d1100a41032181c0326500d05040f220181200104001c0075800c200d11442c0840300c43c04400400e00780149001c1c0554005290248010310081c20725a640010070110f855842c240c50255070050b00800201021072100d9140707410480b40140c1c1c009070007842c94408580220024003450060b202c4d4811075501c07074040c2d10300c00303141c510180c001c0d9031701e503000c2d0216035501030000440140c1d0f800020343c0e10302170090a1008111600110000c1d0b0041100c60055840d8404481040c01502442c41e101c070300c100e94400040511241c007960081c0040340c400d0030b2002840b0030b4400c90744907100c52003c5e0101031480603114448540305a911100030302500705a94081d101c215481000000f0000360349841d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 884296411 1250 884295161 884295193
    0x40e01022101030c1d07081302030f070306050a0603020d03110114070807120b010509060c1203042111100c030e07030b1006050910110a1a0712020c0a060509 69
    0xc84440507410050744801042880084803107007000d070854180780140c68121180c1142024400703000d080401511a000402c1e01c0c0031300c00c110004550050075100c0c00034041000399594042c502050710010328090105800300140d10030b900460b940500a0040303500c1035102035402e00c02c1009002039554aa07980d003540c080c5099a99442080b094a80d45040c1c10310501c014241008841c41b14901c5d03181c0702e50350445a8008040e1100b580d01141c00c6030380c031214400c0050804400e0310004460034404000c1c0410014610309100729046412a0b00c842e843d107010040700c5106a01c2807907022500b10001c50013403016150020b1101121030b0902240303040b69003600300d241107034076802581c009011109100403d0908503524008040a14105041c0b810541c000f441140c0000d044200388141c0e80304003030500c01c040c00b062085540011007a0070180403202d12861101040304e07110001682609551807000040c402d81c1c0845403254001c1440469640e1084000c08000d42482801d01ca070b141b01c80300d0006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 884297661 1250 884296411 884296447
    0x10509060a0e0c0a1202070c031211060109020301060f0c1104110f0a020a060b03070b04120501110a0504051f0509040e030c0d020705030d050306091b040302040f020910030e0c040e0102 81
    0x40680c03030a90340c031141d40d0001000b400d17040f586800054010401c61001c103002a00c00d0007980e800c5081c4582e825070310802603030400b0b040e50f40c80c2c0c00d90107484000202d40c1c8050b8040c6049840d5911610114031075030308101d64030415000020400c100e402007002c030904080d80108421010b0104040c9441014450106c503504400d03420001a8807110a80e4204503185c021490800307410740007450483c0c145603014626004d0f074002e0810110090710080180b04003500509034005078000d8103541c030500144001c04e19031050061501622204103800d138021440b0b041c1d01540d186e140da60a0030507401c03104000141038403c221103100e01c001d0140100302103041c0b0141402603800c1e00202800c910b042c00341424080701d140d541040c4130082c010000c564491254441e4055000c46801114004a24448040340039540000c0e4015180c081100044400ca900620000301c0864082241d4038050030100c1c19104483c803a0803164120011014840c2803d07000010149580400907050684400141d51018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 884298911 1250 884297661 884297671
    0x102070c03080d060b09131a0405010e0106080c130308090d05071d0c040303020d0f170408120603010510150905060d14070201052a0c1b0307060e09010509060a0e 71
    0x35400040081c4903d80c0351144400504039143c5041c140f03207541001940810035101d42c0d46000382c80d00342d0315026030a4001e05045184005001300401e5840e621040c079120000d0051101080060000ca4804a0603a0656402d5001c0c503c940722618219954584260860843d00781c02c61444a02131000603428000700018242c00c6807140d03414041c111035040c180d20f000d040380e000c2000400040c07012940c042406c808286203401c10f0366484514100c02c4035010020340020700420b89030340c10b0008110000004009400c2e80000b1256140c4881080600f01d680903204020118101e102c20403545d24219141880c220490400c424165550004600994031503500220780646c3d07a0550065200c4502e1303c1d903000b008601c020000c0e458042107001e80855104540817081402d1408050b492034a0070840d140040c000e0251441c510300300300304082c00d0403420011440781c020301c0d40c0465014410b0716a01071086006159010b17030f9181905015107c80050090783e0080c50009012031100002c100355030040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 884300161 1250 884298911 884298923
    0x3020127090b0a0f03150b030a05010606030c0e18041b050402030a060344190801090606050c030f090f120f0705010824060c1603050c09010303050415020102070c03 72
    0x1e2940e80c410001e41c1007003130300682200c5040321402e002041940d446461080666040080c26444682c0003a20300b40e258200140650f0800e20301080c4a581030b00000c0301d140480d01d42c1060202d80100300148021a042004040381011300082c010692540c0d0401044000507024150359480b60041030603a44201d0302d001c0300c075846d0001082000103102d40c032a9000e646908182d903200c0c00da022500b801c18010961110041d102540102c1000c0c120221070310b4011300f07100b079040701210080c054140c460901c102d1000f6403a210340099885e02450466124030301840186240450480700c00000390802c4007855001740300d00c18865590b48454484900c00f10018008000340c0007012503052900c4103d800141c1007100003810300403005a003d4442e0b0440c2d8081806040301d6030136a012407d180660500c04000303100700c445001c5001a12421b1505a034020400d031440c46649100344408045c0a100003070000c0c0003040100000c0b441c0c0c2c21354001c401000d10000d864801b5a03140e43d078243c9880d40050303981c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 884301411 1250 884300161 884300171
    0x1e011b060e0f0f0d050a0503010b07061b0c02100206060d020409140304030308040c1211100c0804090902040b091501081801060f05030f1203130213050907060212070506010302012709 80
    0x2d144001c200404019140781740403440d15882e860020018001807090218001c0d003c5000010003c0c1c5420001062040c1c004000310074584180003000e85aa889090f0b02803c030030155212140e00c0864114403c0034080c15000844000381e0030b00005190880042d90540d981000304803110106000402c000c50007541d58400318141070902c40b00c0e00046900108805030200c83d11800144400c0c00d00c2502c6504451424401509000c2903a5100d0034200041c04414001004100104a9404545030b0350080c0c0f002c0040031885d07018021504400da51008581a104008155a40c81145500c0d071100c0d01c29003c1c124a96015501420b560700c0350098200100d0114040c403007404e080192110085001000f841240f016029850f4540b0028100c0040305001e0f403080015510340a14000d4415031420081165144c403c80c0c0381d840d4bc91901955005000381080919024810001c0c3c0320015001009010264a9a8019582c8000002800c581d8801008030084028071080700031005004800010503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 884302661 1250 884301411 884301433
    0x206070605041e0209072001091401110405130b030f01050405011a090f04080a05090312070501050f01080c09060d1a04030e010c1e081905091e011b060e0f 68
    0x2d84580400041c1c4400d407010f94074031003d0fa5501c0c8503241c004003e0300b040c4907074603107404480c18080408012081150309090700c400412401c02d80c071141c40c125043c000c000c42c0715507110400451080707200380c0c2e80c40b1540f03000c220320191243c2e02c801445c031001821036244003828001c3c542500c1c8111010394603079546234822083c440401a0942111400701d52030003451524803411100414058400f0340f950001180b40c0141602620844080d07540040c220741c01d012003100120390315800260f00b184c8a5003000e0110300019600103005050b0360382d1102a018940b121401d0040400e0010440d5502055100011000c955881c0c0b8400041103050b5180100d890030b030034041c100790740342038526041085880599003c1421611140d02c4141101d1038526460f582d81001038440c000d5511103c20010810700040c0c0c9144c02070024a4180801d4423003440464200f0b40007040010950111804180600d203200d00c280c801a403503001440c414100014500702e0329108a10b02000c04000c0a00c075401981781c0c44c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 884303911 1250 884302661 884302673
    0x70210090e0709150306080d08090c21010b0a0f0e0a150e1510050a0c020d02090910050705040b0307080414010e0d110c010912050703080a0f030c03090302120d020403020607060504 79
    0x10a134007019040600a0302d00e01100c450303032100c407034950104100813500401c0741c901050103010014200100134000307822140d94040611501e81030070085540c60084443c0c03590401140e00401c84512840121140f85002d42006000c0002840f00200a56495032203904545c507480e203401070300300111100c43c1c0d860180450707886060080b1941307110f0040440000c0e40154004102d03803141c5011b1900380c0301c00710b6034400301e001c003841e50740001d50001c0300c1c0c2c00f0807024000004910104030b610b4141446513455405090700c1d1032055000d4002c04000400004403440c0c0554105600203214000e0130180e11042840b081c01c64068070040e0300c40e50420001c855095900c013251040d5804c451016004000313001e8006400c0d0708451081c0603039198008098414840d0602c018801960030500055440815110082114800303800e9940446d1400d100001424440e00c40e01002d20350640003446441310700d964980a58000c9401408a603030208004001a01c0d600c000d4088903101d9000410b050405141030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 884305161 1250 884303911 884303939
    0x40e010f17070e1605160614010e130b1305070f06020d11030a0804020312040801092114030a0216060209040b03030304030903110f030d0c0b011a070210090e0709 71
    0x1e103030160310500d41841503042032100e45400880081d2520000d080e0100d0640d00c600039000c56503a03041c04080c0400503c500340e0000d10910603060400c25140ea25440e4800000f031040d151042407480d05405100050712081c51950080010114242050700c1e682d900d629121080d006800f14946202003005070310740400c524118585141050042c40003246c0c0659528010b505560003040111340118096480c00d20004100c001e42100903503681d5220620180a894044000c031035410850354110344110348243d5503c500042580c2e194160215202030041c0d0b07800190040b034003594200002c0c15030344545052600c030303a4071942e030240c1c941d040001000102c4d184603000c80c2c041d40081040000096128040209407648812400003164510303002c038030030b040f003210010b070588500702542606541024030091068810300d58108680e0302d03400405851048150852a040e406002e10703001032410304505212044a450f006040c1561121414162baa003035800c04081641c0c2403045c0030751001e005203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 884306411 1250 884305161 884305199
    0x30e010608070b0904020f1e0702011b030e010305041b2409030f0b0c1c09062f0c03360904030504260d05180f0303030103080f040e010f 60
    0x640a4146084043c8032540318080d0b00d948140d9001031855040349800701a134014101881005a1035492000b2005140d4051402070f80031401c0480040d072480002402e4010403645a0f44042800301030b1070041d005040050800c440d100e42d541a9512440c00c0f2580c010002d14968402c4c0d2610ba4070904000500c050020640f010480e448609202240b11903020b09005540300002d44499660703a11041585d0144050f18980e020102c00c809504041c107070082900c00e070003503100f008201d0218681e00d68024440c2c0180c1410328001c46060304400c102e502404425140d03100f501d00e0314130582040e10a0352116846041441000e01c81502629007513049200d540500b62172645850070980c8001d8540c1c040c2e03201740742c3c40c1c0d007141986503c010400c075001030b070b00c0243c0011200401100d40b00541303990441481110451070700121035180d40f40507482110491b0018016620f96401c41c0c07039800d2103a01007a05010f100034100720020300203c0764401c0c5070003060001089240a814024401a24040244 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 884307661 1250 884306411 884306413
    0x50604061a210c03010614091c0317010503061911030403111c0e150c0d05031503060f0604050402030703050a030e040524061e2d043002060a030e010608 67
    0x1c00c20060f0b4220408036410342e070817801e100144400030390000d0128401c00849540008032952141c0208402591800300c13607110313444503540c408542040c9108072609102c5c0b5a807603884440400c0e1f240420a0b04034406200c001000f05072080e085150701c03400d40c025035044001400c20310840040310814440f150300c52080c90214038070381c0b03403e00c0010b10034010401c01070722a402d4501013200341e041400840c0e030400e0324201038540c110104800a03044c0d410071144c0d640c1c800440104002a440d0100c0c03210700c5000b00344420046a00d911017072200a003001001240c25200350314000c004034808220021005110b541c66615034101c12044c0400d446010740070a00702c440c521034603c0f003144c0001d50100900016034004d4ac80e20040e0750405245480000321002c51140000d1550a51004480f04491282d40c1416200c20a030925a215110703c034a02c580d1900c58a1700c84801d440c00400c01440c0114241c0b400d02c101100ba46d81c00240440d0701885201020a50f51180b0384078406003806500001d2203220 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 884308911 1250 884307661 884307727
    0x1305040f060617030d0c090e09010c0207050a0e0a05061206180c12060f09240a0e060903120604020d0606050c01050105090108100f0e010c110615060706050604061a 72
    0x3c0030a90340ea000718801380712190780740d18028910501c03a5412800030800c0500035003c1e41000aa11402007201c11418030040c02100380206090412105103421500c0103d14154a0740e6130a004100400010341400c1c2c3c05010b4000c0d03120030364401c114090264031820221070341e41c4281c0c0c0096150582c00b00c6214013503a81d140c1280a4440c02113401e50340006040c0c401d003071a64602c81c2240c240044039981c111004106080c0c0c1000d03038071410030588180d039400c1e03042140150240c400c0d903540000311050081da50003004640142440e00d40c569400080282c0003504003400c01d0900d00a5807000c0d085100080e00c08075241507003210900a03140140300a031403a40403075040c580b0076521110b0b0040400c40700d5882e08034001049080307030320484140c00428020445002045001800040c0c0d1a60076201032140d0400302c1c00c0044810400c01e01c62800070200c0e407900485036910000b07480010080c82c1d1042d2307076000000b180d03050100020410700e002800243e81e602207011800c4461031107281070b40403006e24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 884310161 1250 884308911 884308949
    0x6030c0309350a11122b020702150307230d0c0207051c051501060507200d0b10060c02130b0a24030612201305040f0606 53
    0x48641150310900c1d1506055a031004404000070400b085403603420b80a0000400c0c01c1d085038412031981c042810b940c141d81c80000444450041401076042c040e0800b800100c0200483c90341021b9900c081800f84000340c1030a1180d00000d44075805060700102c510800020480c6d40e5603c06c5502c003d401c4130650011210009080d03540f014040c409450f180203139140040003000d402001004024100180030308141c0c00c1480504000001180044130140b0940d8040407140014203840750594201b6a1510306006e031a4903070003c901030703060b005800201089010001350b00c44004c0030100c0c0c1d0041300c3c2c144550411070321013074110f12290300c500b080100500c079002c0140e58a4800000c51003c58001003511003c1c0d60018401c0310315688803100c950a042104000c4031400d421602407040f043d14100f0a40e82d45000c64010440c642000070908800c041c281c8030010a10210110300141c080c05801646100b00c0003001100d4003a2405d07075140f004490740f80100300b118010710001d4001013910500c50030076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 884311411 1250 884310161 884310173
    0x1e07030b1f0f0e040906090507030605060901080a0b040206190f0f0e030c28090b010357050903060108010c050d020a14030a0203040615050a0603020f0c011506030c0309 74
    0xd2901101c2c100f0080d0002080d0a0303440d0b4000c060841e8022104004681045c607046640c1c0a8520085592070f04ac200004c6041c030306802140d0491300070704c3c054200d151490341c544111040051003203a000c0c2040c03040090b5030304c07107003a14440e19641d601e410301611215407000e42a14000e2420108101d403c1030550b10329240402d0540f8203030002d0f03501c41c5441e10b41407078140301c405120b039000003540140b81000800b6995500b003070341640130a0701e04120600d0400d00000040c41c04203400311100e103001e002d0140c403440c80c80c00059044440741840d003140e907a45800e0340303100080140c0e00300000c00c042a0182c1e80e1900f07120381c500404644008010800b503041d0050100d02441e805002c03a654040ba14400e500e000b200104141000005035030307601d142a600040003508103807000e5410520f001e2140456601070701e40b010940388000c084201e120314220046000e036000540b040312010b814050340c01c42c80303424010034803030b9007a86050142c0d240c18050002c0440c1c0d04000c07038078100b42c2007107400c20116030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 884312661 1250 884311411 884311427
    0xc04020315010e030c0315072c0d1115130b03100b07030215011d090a0302031c06030206301009020702041409030d1a03060105091e07030b1f 62
    0x3070a00700040c00100d880000b0342000d148581094150086540081d42d40c140e0700190791140c50540c6980c0007034120b5207200c4aa8525600100078140810040b0300442e1800d001c0740305e0018460200c8901c600e00780404282c08100143c000d4521010115080c01d1220f00708540c0c0d000b90080c0060340f42586800010325145405070300c6040241100010318105052003030100e8111301c0d41050f04114956035038003030070310002c558071000c190030228a0003003040c3e0800030804845458141d4005d50400340c40c20080325040582d048400c0311650303a03070300020041c0c40d0040038251680c2c03110b6480c0007407078004c1517081030803582200754802c0326000410072107202c0400320303d202071710502c110058460701c40d840850003d050030f40d20000c40e440160200408410300200801014044507001d108161400c20300c1c0a200b1007035074400d41d154100704014041818045401a0300080c40c0703810003007082c0c00c8a00161000819180d00d400aa15511003101900746528640c801d0110090329540b144010320000b00000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 884313911 1250 884312661 884312701
    0x3010f0e151003140303181b0618040f0c09080706050f070317180f1b090c2203020a0506070305030403030b01021e03120c0304020307090f09230c040203 67
    0x10781c1003008640c01c480da121002000e19840721902407000d90f04100a0b03581c2d0001c990301ca0f003036880311681d43d1036414041112402401014882c40c20b900400080290a8020115a1289602000d1422190742da40c1c014015034008010b03000030b40d40c051007402020800c25400c4160a40e0090700204640f80d030100854500380c0d1b40700c01c1140c65503001d2408403010900c0c0c041c0c0c0c030202280b29080c03000074900b103803034600c00040c03603003c86840322a500c0303a01c0e441d010034004000400c071030044d641c012800d00100389036025000110051a04001f0149081c02080c082442401c003840804148210700704200740c1006014100d03901400c04070f4540d0000c2c014070005200800309515054142c0b0540d00030040c802c8010702d504070305d0b8068200e000c0c81c607942b904803042c2040e005c61414040707003041c0c4002044902507038001e80034010641c00d01c40e510024109003141c400d030150341c420183d0007003a008000451000307220020020f071669000701d8146800d0005408a1140d0302c1007050044500090a0034aa20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 884315161 1250 884313911 884313943
    0x10e04020a2d03083105060702130c09090c03060e070507140d121b090b0c030f190e0f06040611030d094d0609041a03010f0e 55
    0x4404110442820030000c082e101c603401c0da4541000c030820644101a02d40c020042448000c0314400b41000070060000b40c1e9907100f0064042e9040c4005c0c2420030013003001d1750028228000400e4120f55080449007004000400150507000a002c804814020728003c03c249207020301450307007040d100303085041001d8982c00a000340000c00d8410020f10100d0300f182c10340d07480c0c01c0e1005094040409494002510b0315400101d1905625207402d05642000700094059566090b8416052101a1140f640f01c50300c040d20a01c414001c820011442e5001802c401709000c0e1000840500e0413009002030030b10820607482200290046400d646503c025503040322100c1c945200030300c0200031214110b01c18280c911084905008121042c4040001d11080d4074000000300f60f800e03107c0c1d9410915a0000c03600103099502c0c1004200c42d001d20603c0c03041c29240d0001c04c0c061900e9103010000d0700300c807921104525134032941070103805c5a203820312503180c058201e40001d100b0002c0360956182c640d05801007074425 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 884316411 1250 884315161 884315189
    0xd050712120f0f05160b01170d03050f130c08010504080904050f190209120a1a060a1203050306060c0307030906030c0e0f0d03030207020303030709030c1502150411040f060e010e04020a 81
    0x100d40054072030924125005a841c03240c070752316a4482e003441034900e0070002048c80f444c80001c5541c0e100740314041c0b0510341c0100e504039540751008071480c14000c0300c40541d4050b103d00e40c04100d110f028401d683c0514816030005070b6a81c0d2110030300041e40d5008281601d082c4d000740c04c00002110b18910306044003100c600041e1360310780500018080c3d441001e036a040a11404201c1c00401214102440c0503401d0406180c44070395a00d000c0000d10300b40c1c2d004041031031452050000000b40030340c0146800600050840781804071040c4914615003100c10150b0004551910801413184c03d445800071000e443e207445c40111180c803000c944d0807980d448041d801031032080d480c041070511035416a05419801002c2e2562420445c0e00103140c5030282c00151041100d082000800002541101d82d001c5119006410700f0b14003c03030b1a45003542c3c0208213546400303011001c02010313500c0340700720601c1649607400055100d00f020448103a401050f009840c106044006002c096920394a6090803281d00f155000c00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 884317661 1250 884316411 884316427
    0x6090b0a211406032803110109150507110c060a1b02150a0906080618070e030102040906180e15070c020d21091a07020d050712120f0f05 60
    0x40340703580c0084034824051800c001c0050000a50240c5030088000b2421192406804c4142c003241804210300c1c00f11001c0d0100c0040000317401000100c40c030596200002401040c0c03510344d000103003035412003441484d955904100b00c05411011407464010f001c802420040d0142c03022482138403600c8600320600c00c4401030a01400450101000d941d54060b01090450b021f02c01e218102e50840b182442c0070586240c00840d015120320300c0288104401080ea0804c21101e915010212101030555001c020304170541c82c1454800340001c1005248031a80001c0d114a800c052020f0b110200030724848050030900400c542000005810b40192480d010301e20054445000a80307003c00854402074003c4c200000c400144948180d100248808807a1010092a45803500701c0f6101141e00440c07108041890807070199400010141070039610251100e5414009511441d207042520390140b0440c1144000c40030800c0103143e00210020750604000c904100f015001038811074102d040c4900f00500810005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 884318911 1250 884317661 884317697
    0x10b0f0c031e09090106050a080612010f140612060c0d0b0303190201200310031202031b010501031e03020c040209060409050403090314030f031605070507080c0a06090b0a 75
    0x80309240901c1c0c18000c14600592800042d4003c0340d051845141040000200c0c14014000c03164020469a5960050740c1d4400401c4440f00b442ca222178810340d652404001501c006204400415110b149114410318040d4104038401400f400c1d20f0742960040c40034062031070383c0b100944460281401022800d52480b0b0301291440c00b54031070b404135007c04e41c0b036050b8032660192300c0f020088822506c05a428454003040e00282c1c4025074051000468140080000c0b46080c400c04d040030141e407040e00c0c03070019400030b0540700b980820003603065079560f0710041007004221416a04281034041c4080400111600c000e91901050600a4003550f000288803000d590b403681150090020140700304103034101800c0041c040c040c00e002c220ba2490410600c1400b040001040c2c500301d1208080722461640c41c120341036000c00030b9201250074007506120900000d1024040701000d046030000400000030940b04000305103849910407014007048032410702050356400308a03403501e46c06041c49407132150340c1c1d034140e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 884320161 1250 884318911 884318917
    0xa0803060f010e03061e01090501050120010204050406330518010504090e150108071a09040f0204030302030c0c0402031015090312030b0a150801060c140d08070215010b0f0c03 77
    0x100c0ea050103440c003000341c108000240b6001920640030b04002507132304d4440d85002c0340c1c000c8c060507000c2004801502204403035048101400a95000003608069852001c902903c0b0650070080c200d1841d8a211240c0301e0052010046120703584096010351070700c0700400f40039031007010b0103051047c40c3c3c02260300d440d0740118211002000ba03000100080c1c5800342c5080c0d11954075450803d11040c2e01c10000500d020001018000d960103a0351940101400d041c1084580e444520050f03040354484e09060b0b042107107403014100a6009802941e030701c00d1000c0606d8242034903034503107070310a501c1030060200c180100803409094a407111440801002c01c030906440580c043e0b03100034009082d03070102c01a000d5154000103041e0030265602e22034a41c0f118100300604030303d6030900b0f0001d0483e400400c921485039001a01c11400742c5c00c80420300c00114841c0d4100384a008480e80801c050342e00b404203456040208808403200b80c3d907107440950405100010360720078009840d10550001c1424a0314020074012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 884321411 1250 884320161 884320187
    0xa080609101e140f01081503011509020c060a0e07061b0b09011d01090b0c071a04050c1e0a05280e04140706082a07150e0a0803060f01 59
    0x260460a10012103407950146003c2d89100b00e42810120b03425081012031440c12490507121544682e440a81810000b5450f148480d0326640392408201010660f01c03605015200e02400541e9030581002c0042c83d06070040e00c400000361402c0d882011000d000b08405058542074a0090f0501c40a40e42d0b0203840b4591440241006251806200741c86105500807800302210424418402d095203d407942207940c0140302400c0e50b0310000028044d038015100402d80c061103402c0b5000b4542030007412a40c500c000700c41c22501c4d41e000707013400c07240341c90040741c607656160262440006810084000c82c003204104e110740c030700440d0002010010081001c0300041e0101100c074a19420aa50741d042400400090341c0075140c100c0c00144160792000042820015646e00d1703268203505840d8100c0340501e2101c0c1c0101d0140b86e820708503003403040308404001403e10b1400707040c02181c0710300e071000315a0881d094844a40255407005103050001003940050702d5000c142100c5900388444c401c40165603135046841 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 884322661 1250 884321411 884321429
    0x12020708120402040e030a23040b030c0405011b020d2d06020306041b081303090f090504060e01062d0905090307051006140405040c0e010b1206060a08060910 69
    0x2440c01d003002045a2900c2c40759008a4003130001140c00d0080036241e2080f5814000003501c1c1141d0040031100500022400050010215107059602c20b00c05030190000d48010303058800000d400c00041d84d01c0341c4080b948401d50039041c14408619800610340b948034580c01030000d6840400e94101d464052070050301091040800f603100c44d030301e2800030000d50044402a20a514218102c844e18002e04400d0103c110213484086260704d80d00c80084050071700e0396080b4200008a1400309440000e070701c1000041010b004045150f052628114054919000715411140e1400300c04018145080941c24602128a4908843c02481c141d140e140416181c020b01c60311810041030003c0703040000000c2c00d586000e001030b62050801003c0300f81c1540e03040c0c03003408140310483d030b800c0b041482d02d82c3c42150400c0c85084100103c55840b81400b550036000d1b0722600280f074010850b2a500c04129247c0c95002e04110f4103245084a606000f41903148007034642400340301d40d080001c000c1102a100c12010341700c003032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 884323911 1250 884322661 884322667
    0xf0a030c111f050a05010510120e010f0c110607050414030102040308030106020a0c14102d09051005030c0403030f0909110403110306062101060f0305010c080c0c0a0312020708 77
    0x40040c0184040d1184840682e40c6070030005490b02c2e5440c0b1466058a400401d11081202c603c4400c5500c803840343c9203c0540c40c1d441802e500d0b0300c2c2c424401c6510700124000302141203215082e01414060f101010740302542c101c142004466a4000b003200c1c01c0d601854900c080c000078000c0403d0090149800003086140004000b003640d0360001020b100359441403000000003511240004150209481c102e034200c42480380c4000068011000ca00d0071041003c441c0e410306040b1044110782e0b22082c4440c401003861607001740711908221968034004161410b00910318100b0301d403c5142441144006400c219003684a0300c85644541c03811002007507020010b1081500b0f41100301c203503901c030b440100c45405a401001059080201d0442d00c510f1000308080c07580d24654001000001d50030542012555940d000031915080e003000050166003e40e000003030070034060402524081c03010b400d00c07403080c905220607015000300155510391980e0600d044101c038000d5480002c003038000d003a00146051404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 884325161 1250 884323911 884323933
    0x3040515360601080a0803041104180c210308060d0f0813180b0904020909011b120606020a052e091a070807050702090c0403050a23030f0a030c11 64
    0x1040c07480805201001541d0303581e680c03a0311041d030f80c6140ca04001c24000c2c0078800107010645203030010f40d4001c000303840403444400c20310421140d8050584200e90030080c010b4113000d039151542c1e0300500b40481d6101e210302100251805040715800402503407107010100012030400c11848111a0015072111101c2d4a43d569003204a2000902e07024000402241907501881070340c59018100344090080c001c510303141c89507001d010b1128401000d09485640303a25240b810280030b07109910113100b00344e503460681151004c0000640c0c12660101c0210760103c18048046030010500400140559900310200b48081c0320400c0c4610101e103102e0390040c5044030903014826071460322031100513949005007c81e6181c01d000c4d5111324082c0d815a00045c001e01c903a000605003000c0040d084611055000d0900f56280e8480b881c004518070f00700c0300210f0426522500d2201c0e0080c241510200314007a40c00d06901100d04100b50150002003400c05840f0003980100601440702182c0304c441e00001d8a034807801c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 884326411 1250 884325161 884325241
    0x110f090106020a260f071119050109080109210306080604080a270501030c02010e060a140901060302090a020703112e0218090c1312031403040515 64
    0x8180c0140c48000c125801074031200d1079044580d40c074080b00e008117070600c000c14a01c0300158000c4041101c20344240c0f20100000c2d40e400d881200034050158545064500f018001012000568489580c682c101210000062169410111071000140c41071030320189128044010f000b082e84440006d01683c400e0205100480d0000e050020712906c9454464030301031904c04812922103030213101440d50f07000520039584039401185080c21944000b107583d5500303403141c509003402a148030210b0742c0c0da00e4004e02c1c001110b0000d19840301e0174800800a41c0c0c40c6d50007007400840028282d0441540c0054001c0415000d90b007284c101c26504422151599944038100401c010b480b081c049401403c1c5101026901c6140200d07800101090790400403035044605021110b800500640c1e0340010034484c50000e2041d404100c00103010b82404102407001d6030402820724085920010190003041040101048002130300e4880c2d002e102c00e50000c166101039500100ca40304024441a900300e0195070845150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 884327661 1250 884326411 884326423
    0x11a0f011b0b04030314040521040b120402040e370b0937060e030408030a1215061b15090804330f020709020a27050d110f09010602 58
    0x1111783c8040000740c100150b00250081c044030014150784c007203d424401303034424030281c0d450280d10320034031810192600c100894a401010124110310000300c10001985024081c0300d0b100760303085000e80303c00358904e00c61100c9034041017401c0141d0080da094841c2c149180c100035102181d0405a42c0b4041d08201d482161070700c060714500e500541c5071728034548507480f88818070480b000030203205440e102c0f4150307210703030240c80c0c9070203558043e00042c0030005c2e0110080c002043c0060882c1d0b07841c00440d6110441100302c03243d07058110031202c625041031050b01e800c0641c14444002e41a04000c800120b86451100c400a0403161010f09041c5182c800c20811000060070640b88510103505880e24081d41c2209010017440f101c54185280b504420f01d01805000c2e030001c109414030580d00c5460300e0b800306005a9105107491000200e40003c40c040000f002150001c131030000d160800f5550b880c2030001009190135141c00b47c5501c1d803484800155503a88040950030f4003015007103004e0742d0303903c040103502c0381 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 884328911 1250 884327661 884327663
    0x712030212061c0f0503090904050607030606021c0e0a080106120510270609080304080c060a05090d2a06060e070806060403030f111005070e03011a0f011b0b04 70
    0x6001503000c140503140600780310f0140c0900f04012020402e01c1c2d00c0f584200c040c800400e4130a4007042113501c40d940c4500a81ca40700314000c6004080904000e1401011600340d5485501150003a403014080c0300365040e031605400351640350805858601c4400100301c3d281e2940268202c1d0b2030031200040440200611402490003001500c00203a01200307010705646c545605106500100714544141079075280c0d00b456280c0c025600040d449034560b566031015401a81d0603603c01002190741c2030321100030050309911401d4008240102e05106042c01c1d030710881c6803403490500031514817000c080b04010141c04034000014507003948101446c20b0890081c081c1b401202c924a856500242e5113901401c0c8190060304060f000d00e00d4076246442c21203442c030800c91440e00b0068191a629242e0034200909080c88400701070000316403d00f540301034007045015155034002d034102958021004281c113034800c40c402003074841c562241610001207801c2c04500d40381c6138902684004001c00d1115580c81d040c480c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 884330161 1250 884328911 884328937
    0xe010908030c071a0c060703140112020a0501050c151303090501020a2f040e1015030b15030111040905011e030f0f08090307030f0215120a0507020307120302 69
    0x210391620103058492003450500c158607408a54100058940b403018440c401c0014500241031145403c0c0c400c1c2003002c25039500d00000e8680e02c03690b64505180740154010031108107200b0340c81003aa4042242c05001e4802c0c207041c401c010419190740700040c480343e14208280e0803078201c140380c03c8070394081c0c1e44010301c01940010344039a0082800e500000798141140d41080c084100d01c504149012103540c001c500001503d6809521211a615640201c0710000c5142002c2d04502c0010131040b0308884c094100b8058000800070200003280300314000540003a603100454501c100804086409003d49000500198100140000300140d041d0702403416501a076400c0c410400c0036114075004100a4000900403080742c0254900049110f81d4503641c0c644601e4015080100b40e00c002800e1864a038001e48420084030301032003c500d441e41ca4160a20908800503052012808510300c00d00d5009041400e01991140884d030020700030000d039400d465110f4103034061880c1600b0020083e4102620f40080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 884331411 1250 884330161 884330177
    0x1005030106061e0513150e060703030e0d0509010f03050a0905120301080c030a030509040b0406030804140411030f070c050a050706030c020d020d0f1b0204090b1f0e011401030e010501060e01 83
    0xb40f244101d003103400d401c0f81050002c441d00e0400800b01038030072285500c102032041d400481d040760b4803104041c01e03229000741c8001803040300040443d4245034810401508200b800c126900c00e50b82c006084c803511040910b4002500d070740e0045a20010b045a000c00303000e0f071040d406008000c00742c074001076051f00e40b01070684060036101424160344a07560580100440ca0a000320500f500701075000488540340200b002c519581d0380c0c1c4480e4182e6205800486104070296154011341c203080c02905170a10070a0070261561428400b1829080f40150080c4104081e44490409101040003114107a5030440150742c103595940d000034005120255a000141c007450111907a81e50001c90200300d15081c4c5d460b881107803011203008603081648540d2282450505031310032809a200c6104400d05c0620500380100d60741000b8001c0218207070302030364040900c14040e100748a11407005d00400d046600344100d111a2031820b90059015140b000c0710f0341724a620b81000081c032594041c0c0082c0e40341000382c80f1040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 884332661 1250 884331411 884331467
    0x10c020706021506120c040c020705040b01080c031b0706020c0c040506010216060e130905062208040e1503060a09231b011e0302030f01150f08100503010606 69
    0x103103c0c0742c2403a540d100e0030300e140006141030400071600c0c03008030340c0071080d5030000076030100040c11a6840e043e4580164000c101c184810f007814468007485181c242420245460b00c4010b00d452880300801d1182c00d000c9411381c102c1801c2000003a180015807000c004e41d1910003180e2480d984140904125116038100804101154000b2440313070b018001034110b0800d03d82c14203e0990350800d110203d242c11840e080d80319651008148240001c0901c60382c0a06481d081140b40f65480c00301080185d640040008880800200d072002202e045810191442c69541c1e01d0100b848080005a000c1c65014003c51042190002c1d103580003c44c0b0303600c244221480000000d58405000c82c6000d4240101e40c0300d010000700030b64010080c031400c24414541011446100304503c98507030007a001031030100c2d4000c000e0101c2a20b0001c06180540550a55041c0b000c0c0355140080c100c594100a00c1c0520180d030000c0340c50403a440c0e11000240030042c0080c010240d84160003448c42805210070240e00c41c3c1c100d1000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 884333911 1250 884332661 884332663
    0x1291519111612030e01181e142404050901090c080108011a091302040603030908070501020a030507031d03030f0a0e0306010609060f0c0c062c1c0609020a08010c02070602 75
    0x842940d10088811803c541c090b83e080d2049101d007541c0c141030040d84640c1c07640c00c5003290b8070034000e02410618400710710219540740d492806e181d00000100c0d00519500382c440c0d11910016040026180042e0209003c09450034025224a4001075044140c0f07000206030549c40350011404101d8030780d01c0b44203581e40c0d804000d08807440d1a248501003a05d64103482d4032444c1c42d0b025550001f4185810f00e1000480d940040c080360840d41c02140401c00159040000325814003e5038000c0c01c00303001804401080e41d900401d148660702005050165102d001940d02c28031404072111050060101c961796000c0a81c00383d05900007034158400a41200c071000c2660801080751030495981e625502c050a013095820b80e404a00d0640c60410440c444a81c1030200f50310411090081000d5200c0809100c845e0000d809582d83c20310f030501080755894510946c544403905010b8130102601800c4190152918046004d400b1110b4080e50044c13498074080b6103201c043d0b0142010031001c4c0c00311003456555501c00e03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 884335161 1250 884333911 884333953
    0x1b08060c031005041a27011202040e031b070b040308030a02030c09030d020610090b0f04050c0f16030e030a2105040305160f0f08060415020909180129151911 69
    0x1910001c6c601c0d00100402c8096602c1081d065100a101151001d898096649543c0140700e02e03120303100c021301e41d4070841c03c004d100c10700c007400f20841414a01825a140d001140c0b001800031a41e15030b00000003441422800207032059000020240ca00c0c118403403e00070f40c2e81e5000d403080d220064005500007071011851091401100700513000ba140041d0b02c81c100001400014903130500795000f0441c4260340c00211000701a01c8041d400c0c025100030040c20010440c40b010020300340070f584000f1440c400310710b0301402c801201f95000007049024a0134941101c540c080c81e03000400521400b440180e1060b00b4a00b10300a50711101e10981c401039482c11801062403042c45030f206281c000700f001c18081003601200c94601d8032402000b6240100e60030101b5100c1004a0b0302e0f0f800500c0703002c05118920001e001c2d40b0340030b40b0755100f4080408101104a00302c2c0f4900d800480c4245100002c003014803a0007019500b51030300c40342d008429650782c078002801c0c000341c01100c031036103008841030301408800c94685 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 884336411 1250 884335161 884335219
    0x1f03050604090f0206070201141204050106090207050a0f03200106090b0303070201122003040303050a0b03010b01020d110f190c06020715050c01140109091b08060c031005041a 77
    0x1904050400e507001e11656a20400d010f07230400420081d000741d05e012450080c118040c120b10082094589401e040d0300b103480036013204441900420034000400c400040350f0b071819401904000c1e92500078903068400f00d000411a180c000d081c020740a151000650107441290358151003407080600c20070402d5164070503d4402800f14150700016900413800b5480b0200c0b070f02c06010a408640608417a207405504111405c800080d154420490102d019000702401c446054009000304000900041d407502d1003103041d00c01b0802e0343e410b640e4000501b000685007012004c010f40d417025481e501c001c0d844040284055402100f80c06d00041e02510004880084600d868031865280c5510f0600300e4080e40014090891592540c0407400b004040c0140a4028240068000317040d000720310f0401e5100c00260540c0488406500d420001c0407030101344240c4c0320400f488901c0d6030360348062620704100c0c503079045150030619012030769452841400c0050b0074070204880800701040c4001d00342c0000d043e1890 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 884337661 1250 884336411 884336423
    0xa0504060807032306040f0b0f0607021c03180e1e06030c09091b030127150618050a1803110102310602030403050604150b1f0305060409 60
    0x10080d1500c0350360519041490340c9800f085140c484100880e4041c004072501680b07000c014180100c1c4d00d05071044040c400c45a44050210b41051000035020152610301d15024810001e011011981c411041502d289a845070001225029080003000c030480741c54081440c0403450400309264401850044c8502120005002d410155080d43c106214016000707640500c40c04036140c005503500755010380304220303090040c0220b10904040346540c00c85580741c035010b03914103003400d44054040100a2010129160000d020038098503141407151908180e81441d1441c1080104908500d241d4a50305503005220500c099110303048110111441c00c0d0350702d0070640603103000d1b200280c040c43e00600ea88040000040c2031a00c0c11864031603400844802980c030301055901049440d42c40c07240e40c07001d028203200a50030541107669050703580300c0180c00030b05690406103018440c100310707810000311444060240520100a0400c2d401034110080e90300c400b0a0510300010a141403511035285881e800c50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 884338911 1250 884337661 884337667
    0x60614071113021209010f0c020703120e10030c140301210804080106060801030c171905011508030c1b0f060d1103010807090c0507021e03010b03061006080c0a05 71
    0x40d0301c50360a00c106449aa4000710b00c128210100c03085403000d021003000d040300c60900d901c1d14001072070845521070b00e8040342916080c2c00750112640000c2003000c5d00e91000a64100401500c801d032011181042190303072203d4214158461242c1c0368000444103081525500800003107a003042c1c080740400d00440244400c035824001d006a540742894401d0b0b0300800350582341c903445901d03407400e49441703400c00c502141c0200c004004000e81d00000d4801080c0f45000076041c01c0c1c50058140d01c0b110f000c61000500000c007e02e08044c45402e51100702803200200c0300300e10082d9104202c5072280c11421440d2440d0141c01d080780c09074004500c0b4420004070080042c5056090740080010b2a0000306011a02c5d650750804055014414401540a00002001442d110b840d180781c1c10180d40c070040d80c280801c44203011110050f180e09500c0040c1c3c607103600e196030040d20500c010a0041420707203045a858070505040c05114096110788500b95800d66aa07034065540384d019592451003410380480c0002c13420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 884340161 1250 884338911 884338913
    0x27030c010c1e051608031003020f04090305040618050a14040b0301050f0711030c0105090f060c2515060314010b041b1b120216050409020a060e010c060204140406061407 74
    0x1000107041c01110345003101c109038000d07203e41c403980c6c004844d0080000080102802503140a01c02000d0145088800340250300069070020300a000301c0c0718040502030029522103044080c0c500c4c18002c0e190162100362241c3d55070b1036406c0e00071180d0402c6030027945091091161401d060051501c103070f030784070345c0044507480c0c00c04115070040c1c00d1507542c03040c0e00007442445044c100a008082c011500306009007410400112540c0c01d10b90042c0c81086112030400c0122007001040b100310800640a80c100382c44c0740103609104020492010307800c8501d03460310002100300821803404c04c44161500b8000c10000c16880180005c65601c52442c1448410707215900d17202c1440348140f140c0200604565100c03081d6280d40c1c2c0c4c5001c020310000c0901680125000e0f170078440080502000410044400b8031510701150041285d06000b4021501040403131200111607034065040c5040103903003c07004658480d82c0710104402c81d2042103e4030b2207981091030004d5080e10481403a41000840701d074a500d01070309 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 884341411 1250 884340161 884340167
    0x17060112020c030301080303041703040507050f180a0f0b0607020a051c0c080c0f010e01200c03030414040509062403120f07030314070507030827030c010c1e 69
    0x448440103020380e02042281d44a41e000d0000d14020481c42c0300460b16403c2c03601d8507111050b011070800c00c040e40c0900c2040041800040c060040740c00540e1194039032010784002c0f4000048480001d1005c051140071f120700c0303150542c4540880c1e00303984000c00c0004418010803a2500c514040130391302040c10102800030b03107444417180d907001c035049000852103400c5c0c0c1d4411409a100381e001646603004110751070b0140c00c00c0322251400715000d10300828070041e101c00113019440800400d40b440e804514580100170700030498250550350007822a40c40c0c0340e40d5100d00501544420985020724104004902904400a1414060a0b05004030300f581481044035800c0003074032698072949481000e50000303884c0d114400500307107020b00303041050340e541032428081c007a00e00501d5004050001d40f010050700319485020f0f1303030400360700d031070310317071840d84480e407041040040502e400107c1081c11150241e0340300303001006090b04012031009104112908805485402501e045180c0b85845e011810390740d148 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 884342661 1250 884341411 884341427
    0x6010f0506031801151409060d030503040f020a0b0406110303012d0b071104050708060f10170708090f0102130909030c1b1a0f090907021509160501170601 68
    0x1124562048044010001e0306080d81c100c040009403171074004900740400c0c0044000d2400444083c0c55504190901c1030106007102800c807405003c002000c0081410804c001000c1148540c00502941085840ea1104c002503406481120003181015004000036200481603904a07041e40008402201003a21420091101a91109607a0003491004110303100024064292a40501c2c032009840e03900c0002e0100300e55000d0b14080c14400c4510400150b640e5844036101da0350f6040c0c071502e090840846042c0c0302c842c02100104082e00081c02001503113644408601d101da000041260003402900e61200d00700d02c503407002454a03094001040c03045200b19004510900d00c40c1c9081202080b0f03903140c813600b810113282458444034090f0404c0040442c0030540c580c0f400707000a0480d1038582d644048141c1c5110b44046207014541102c002031030035009211032100b42c80c901408014515080c0140d42d110b13480c9031030448120891480108895206407819071030708039103020900480c1c4408006603000300b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 884343911 1250 884342661 884342671
    0x1052e050f0d0c0207090c0804240b060408150f070e01030203070e06070501061401050a09150c0b041103010c050c0a0b0c04150504260a060b04020d290306010f050603 73
    0x84080080c202c4a409a1150041c205141d9025040c420b09211900c1d041e00d800c0340f04503040046110910001c61000f005288544a000d0501c07160b1045400c5d0070400b07052604102c551203040403074009650440800e01481c110038881008199903140740c1c1c0b00741020801d890b07000000381846c0c101182940a0b034000c6811042038204881d0071028a80095010340c007042080700d499456103400c2050b42c48006c488800c142c801d081c8281001c0100c54010070269592291a01c5007019a081040450241c6020300446801c04010300d406e02d000d04101c0741c14225007256500a610340340162504a21400580d0190525000a00a80b00c101d40b160b1080d1030003d00f000d10103140804c40050407920285890361a0400ba0b210503448900c0c26100b01094690300404003036200880b800400c00e9100480c000481c0d03640300000180c3d940200021078001e01400c01c00803101d51502070f00c103c00340e0f15142680d03031040c0d1503440261142120014141c5540c420320440070080806003050250386042c502a60703100b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 884345161 1250 884343911 884343937
    0x91008060a0b03190f0b071b150906180b150904030f090b1c0b04020405030a08070507030b0c071101020d0503070c0f0803042102030f0405010c1b0e01052e05 69
    0x130180a402e070340000001403001c40e480e03a203401c0d41e00108240c0b411034550100c164100071840f0241ca46050002d07101503480144043c2400400e610055a55441403180315080401004507207044ca8140300115050b010540e04031a40400140c0e01501c000210960240e02915920141d140e580d07003900c00d003400850420902c0300441000c90b580c1c0c1c85001511845800104044005051000107400c44504910403805540100000d100c0b0391000140c030300304c0c1d65014055544e80c94690030001c0c00d01000da04003c14620003107040c001e2000b518000b03000c8036401101600700e44000100160394601c50344000c0000f0500c140001100d450052845402a80c0505040b0044500c5035030303a2180c90b402201d089454040301c20403009202565107401d640a12540025494080e100190b032103980100c1c0b00717190420210441100400c82e4400e9220403020200b00140542c40d1900724118515074240501c9000b500b22110b071100d480584800507480d4541483d02d04501c0e890303a04100c0325035000154030208 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 884346411 1250 884345161 884345173
    0x5120f15090a050109120e0409080901050c0715030236060904020408030705031e072411071a060406050604050607020d02130c020c18061012021602091008060a0b03 72
    0x82403081c0079010317000d80b081220400b0004a244081d0508400f00c648a0281c0c1c44c2c03a008800040101c41110384c83c1209080c040d44460059404a117001a650024005210000c404c0e03074a094164025244681500d80c1c610440f1221401d00c0c014614092108200d40f007101d134003412641006001800c040d40050000351038140c6a184240c51a071084104803059440015510305421a4403141056480c00340f0a4501d0301c0200e8a6040b900f0038020086048101803641c004054049980520300d051100c2c456541c40351380d603050201845409100c0039807078101d43ca00240081c642441028141c074002000301e0705080c2400c080c80020b4000710300803a0054a0100303080b02680c0d5410300e0402d8115110070200b0340310074400300207041c40200f1441c18040c103091054103a001d0303003242680c3e90041c01995038852940b0004000c807032032703544004404906407001411003510000c3c210920f0340c050003034581c520940c84441d00e05801c01164415010b03076820a4000c160002e140350031019940070020700301c0301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 884347661 1250 884346411 884346413
    0x309050409080304050c0d1713050d21020c0a06080615070b0a1802060a03180606060f020705030f03370801060e0a030b151f0302030105120f15090a 65
    0x304450254000b0341d2004004010041003080800000c1d06501041d00c4044900f413a560301d50700140c0e0f52282d0034900200200d43d40003540800f114800041074014001c0c80303d11080d0400240440b204001c4030141030480c82c24030030306400010400400e00015001c001564030b4003d0459440704080e1805074844c814504414140d411a000b8146a03401a004a0114180041910100d4000d40c1d802c0400c37140170380c0c00c40050b07a6210140c0f000103206007008500001305c02c1c0d0070400c1900101004003014900304004c10401d500c2680e45007038440740d4084680c00380e11070b005c1554500d0300c04100b0361030f54010031800c45240140700d4100c1c06130500b101448501d14904919461400f2008050340010348100b00400101c3c0d800740340c829502c002581c4d0751950505540761101740801c000c1a5085182e541000000140c40b816107103120304c00072229001d543c40144038010040d41c803e105e03d030b11520381c1580b54224401c01107400201c49000b80c0c0203224803207100d851141144401440b000142c014018104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 884348911 1250 884347661 884347669
    0x42303010509030a090e04080702040e0f0a0804090e030c10150812070b010e190b010c060e06011a121306020c030313021207080709050916030f120e06090d030905 71
    0x2034002c0030140007640d282c542000009001c040310794001c010480c0c6070302c18403001c80d81c000102c0341b50300e4040e5000300c1c0c1e603159400d41d01d00d00401742d90320000c01d100700e14000050104042c0544141c40820030300380701c0b0b0003080104564a00440c030000c500c9401100c01021814030b40e5000030b16104c0a0f464002e0010b9070381c0d81441c20008112400c00b1801e6001480714200300715082114050002902c410600d070402101e50401c0400010b80b0b98040c0d035403100b02c1ca682e80c0c0126213021405510940501a03002144002c41d100c0d0001e1082181040e14454040200040c02041d21700d0398680e4032000c01707290354a400c0d442c18048c0d02102951719139401c01190345240814802140b00350f4502c1b07500a1306401600c14004805107891004046412548061000c440c008c90010111864074801113259140c080c8850300381741408a42c2d800c451503040d000002c00c1850340200c0c80c030b180600381311060070a0580f81510050240a8040d6001d82e041040442c05c1c039294004000c0180245071042d0078a07240e001013 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 884350161 1250 884348911 884348921
    0x90d120e01110d142202040507210b1e010f030c0e0d05010209100f090504051015020d180e06061308010f0e0f01060b030402130902130e011b0504230301 67
    0x3009000351101910f1042c4d25841c0d20254010b0450485524040c1040c1c811446107000c140e00203224503200da020030f07800c2e4415480b02c0042220b00102d6005980ca9590b200d00800e45030501602130050078070710f07020f11040c00070108030401042c3c40314002030798480c0b270890042c030015881c1c07000d004c80040e500341c65840e940c0300840b0540c404e0000607a540c1c00300c001c115209405003944020400a005040c40e1190321100c0c01c0220f440543d00480c0e9625407840345803120000303400c441a0000303a006403201c03041d40040d1072219010f0a072200c4c0d007800f985161003c054611805880024030002003c00e155045c003100420f03110b041445209400c544955483d4250b46e82800681c42d299110a59000510401d010051407140300c48001c1007028901059459540401007001e03200b1340301110054078240d1950440c5458541c001d290b40000404503405d940100881603d4110070740c64008480700b1405074080000b0381c040c1603218141400d1601c1030492080c0303503020f910002c41c005502a116651824094 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 884351411 1250 884350161 884350177
    0x603100b210708090114161b1704050a060306030f02060334020f060f06090c0c010603031205061e040b040e0a151103162a0c050306090d120e0111 64
    0x2e6099900300040c0322400d46c0c01103808440c12180c81c20510072400d0451500c110140d1103403c3c280114005240080440400010301400c0742d10007410007070b045c3d03075004000c0080d2041104c50412564070740174120304a5800d03000041407030308000c056401518008014603070080f03400548800894980c541ea900e41c0c072819074046030899540305e540c102d154050090744074503e4900002c0c001464030100189413044d004d8903060203401c1d1003021900c80d24803103040b00c004100780c100034000c00342e6901d0018a1b2800b100364440c145484e1001003003240c505039211203c20b201150307a440c62130811004000044c040410600d9000f1f9030340c1b44013019a20b0a100120f205401500c3c04071217210401d908000390f4603480720321300c8408410010070104e1224480e82c10100151441e0500342440054030401201070080314440c03a0b900c2a5a5071000c2001d40b141d82401d03644158182c40b2261541420682e03174071528814800440d051606294807002294801e156103d2480300206503030130024001e440350342c00051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 884352517 1106 884351411 884351417
    0xd27020a081b240f04050102010b0d030e100e123f13171c0201020a0c02041104052215030803010b0d0b0a060302180603100b2107 57
    0x500340300c8000121942030b5205009448a20344e50003504c00d440c0158202002846a414a1441800c036641c1c1500e540b1076201149003040002c0c0200c0c0c40e040204000b031007203c030301651a016600004000c61025243c00303084a25902e01150225441145d4003030884602d09048003070b40b801300c140e01040c0400c20744803000030030000c242502645c070184402100300c060111400005c580302d0510f07094201e1803210940c13808026800d0380584115400818101400074004d4100303600803400100d040c061441c030b8961120002250010183c8000040c180920349290781581e040c400c00103d0a00f0b5051b001005145907129000c900c81401250300401c000715103106004d034a83c100640b00c00300180748062240e12144000c0c000e4010754101c8240489c082404022810b0a408513401034001e4010140268182100f001442d0b0200d1408a00044107840c0c6d628542540380002d40140c17126a = true := by decide +kernel

theorem cover : BRFrame.Cov 884172661 884352517 := by
  have h0 := BRFrame.cov_init 884172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 884172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 884172661 ≤ n) (h2 : n < 884352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
