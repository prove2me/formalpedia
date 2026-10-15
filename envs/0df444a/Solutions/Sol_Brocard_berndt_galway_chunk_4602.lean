-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4602
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:08:54.608048+00:00
-- url     : https://prove2.me/submissions/309bf438-1b3b-4696-9b57-f9c30b695ca2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 827517985 ≤ n < 827697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 827519235 1250 827517985 827517997
    0x2106010f0f1b080d050f070801050f0108180303071101060504062105100501061206090e07290403061a0102012a11010f051b040807180e010c050a0f05 66
    0x400d500071040c003074a500c21150701201d00b44034051a841920680e82d102659080240c541d41603984030700c200002c07400c040c449154010203511780388501d54586008103074240a4080303940d0401c0040000543c103024440c901c4014245c101088070707903a2401c080300419000c40341c181c14005509020340000c83d032070280100c100380c45040c1414180318125403a111400201c4030811501401811000c2c441050540f0545000b42400e40701c00b1048002d201c510412212a9004019050f150100e0201e820200143d520180c9a402c9000813401c1c1109501884200c8241311b60030707801c1000203002c0101704081e0048000e0f2806407143d00c2c40c91620400590a07101d994090020300043c580350b05504c1522210040080f08481c01d01d04504c0c80d41203016801d43d203104a681c040a61200e092000c10b188038114802c030a5804030a1500703140c10280750301d840d12082d20540d4002c1411121100d0403001c04d502601c0140d0b0981d008000b00e00a054016195800c08100440803490400d1803d43d514095012500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 827520485 1250 827519235 827519237
    0x1a0a0525140303150402160203150106030e070b09012f031201171b18010b1e1c020711060723030a0c0609081e04090f0b09070809122106010f 62
    0x484d203140307034082c072009410140700f2880d00d218400c00b07440940c40521280744e041d003912045602541c140000901601c60a80c03a01c511070348000810092120b05600f40c541c0350f41e003441c05000400d400e0350b20215150644d0803000091104142d104c907007910000040003002c40c3d110000416030fa96440c440640078090400d51140d400c80c001d08103038080c480b0b4076404100c10041045501d041c01c4051969401c8090308401885c1031300242c0d40711181c0700310b924560303401c00101d041468a04175080e85911041c3d4880c1074418640c0100700e4000304107100c65841c84410000e0406130315088103081600255100c4100340c414626035050b06080d42001204403403182e082c0c0c0e00e40c29004000d41d03803098004d14110006550058050014030342c2c045e5140704000f104d8040402d8652164101031148040351072200b91184030a02e4052152099140c00900540c080c2031401c255026582d250f00690400f000080d400d4190407000459140110010403800c04050141800130040d5403814015206201d400329040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 827521735 1250 827520485 827520511
    0x3120801090b0604050f10031b090f0902041d0a060b0f0901091e03080c0309121e07061d0a0801020d0207050f0a170a050c030703030209191a0a0525140303 68
    0x14801741807200c01150311f07807014600000d90111480598140c0440c0c0d20448000034080403081154403034216010000c0c000c824400c5140c1032401c504c6d8200d40c4403082032400c04420000004440e4410387d0301039401800b1540794550340d4400114001d80702c1d80920401400f1413150030700031035081e00e50310010392802d030f41003130898105055407200070094100704a40041444100124039441d10750000842050a01000912102040017050590305183d0300e012990782c1e00a00c001c01490f9480460307004101184550840d01040c52400f1405000c26601324298a41c000694861601400e5000b2310080d03000e0300503901e1241d0700c14505070b25010b100710058040070360300540f02d007250003400c0100b0000302c50b810100d02d2700a20a0b2500d0440e0440d4030150007280c0d010900303940c07504164506118149100588404c09030528070308900252404910700092000400c003400007a00604c00c85032580800e4130072110b4101280c00b03480021100280031600005100e10000e0700306000400c0c0d034011002c0768504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 827522985 1250 827521735 827521759
    0x2115141308030105011103091207051e0904060f14280501230d0c03061b030b010f0e010e060c012f2506090b1f0f0e0c0403120801090b060405 62
    0x1140c850906500300c6c00c1d20701080282041c50313580d00e440d034104810702e6405031024501d81420499205414002c00e44e200c100c031504100b007a1744450469902a510140004200003100b07003c0000301040810105040c014800780243c508000400440c0c615605a0980001c0c1580c1c1590083c0c0f4401e01c1080003036151880b00121540c0104404502c203540501440c40306085500c90b403a20070b0956105856176540c40031070f0718510f01443d910407441d520030b05041c8200740520000030324078010301e03803a42c0402c0a52464042c40d82c5c8660780d20304600e240140019110713182241040c0c000c11410302c0c0000e802c1e4041c140c4d50072914043c1c0070481800103480f5a90f0803c0b11040003030a00141551102c00f01200c442003503800140720707218000d03050b8051b0b000f190440c5085070780041001041c9040060180d0107407410040905081e000b0800e82c0c121400f5208107465014038096940100d410003000298000b0500540a80c040b003210304075100b003201031088001039000c4c85914482c0e8011103410000034050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 827524235 1250 827522985 827522987
    0x15020c030f0c010b03060a0507120e1e011503030519020c01050f07031202030c030411010527030c0a08150a021201140f03070f050108100f211514130803010501 70
    0x141c5081c42c184000031075110f5007000040e050850884410703880d29070f00c034203019146500649000a61300449000c1201541400301c00e07a41c0c002c043c5404103022140c08a0740315141c8290403800d0b08602602401080980b00d00d0064196000018000750900340851060b080a01c0054071018a80040e103406180c40b0582c41d10408652200c07506505122442003285008101480110310942c40c8040c0340c2e03240d00323041c90540c04184200d80c408cc10488140020b20400c0100e140b600749010a0b02646492011500c0220307041100b10344280303134400040760000031030410100700c107810070011085207841e40e51503818000490013401c1c01101c9000c1048018000f06244801d01c041c00c0d030006102100d13454034200020314004640c2c004404103a0b49107400c000c1035070011030042d080488913480c0d0000031b0034501140365070021486440308034880c81c040001d0f03c8410200c140f0126802502c1c1c0c00b144001800482c0280c04404544424145014001049686a07000c0c00e21925071251001c3e01d140d11b0040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 827525485 1250 827524235 827524237
    0xc050a17060d0f0f0503130305150127090807081902030304120302030a0f0603120e1210150305030c16050d020904200301090b0403020606030a0c0315020408160315020c030f 76
    0x102c102c0f081404c00d0340c502c1c0800c208101824034094a4514448401d040d1703d004c07820302944103012144201c40c0b50040c42a41000784081509980d51030741024549426049040541000350000d0004c51000a803130b0709000740b45008040980c68005a90302d00341070407104a940e44401c43d0301400d031100700300c4406400d62080e002550170140e05180441c03070f0404005090200c5805a100310340541140c07902d644026000145130842c800100c800010007079030010455158031100a83c2c61845550b41d0079044001850074101d000f071504802100e48a0314071740185590f41e003070f43c04845003203996000e000405d890941c03080d00c05280e014000130340d991940c0d030743d61168002200c2c4e04141302440001848450300d092050b152502d00414100d40941000c2c00c0c040c0c1480c901500c00c6029802410481001c81c03d01022001100c0c1c2c08071801415000d040c1040d0001d0169400101c1c1c2c50244c0a0520308880040c0321500503a806800c161000c140130180101c05c0b489280729400090304140140c14444807124 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 827526735 1250 827525485 827525513
    0x12012301050a200a151a090a090f0b2502150a06120b1603050c030711010f021612092610020403150e031213020f03010c050a17060d 58
    0x3050007000760f5042120028120403105101040b40d1101490a00303012041d284121010041e103020010761501e186425070401811446502482d851340201d8052500b9a0141c0406034110700018001e40c65490420240c80040d500244452103010002c905078040c1c0c0003003a46981580c00501e2072241e0301540e82c1c5071600090190403a10f0381c6500010700d11002030742d5081d100d8840c1c540c1c4103081c902030010b169026040003888042514100401c1261110201182d400c06420308125904512040c03903607001d480a010890800c50010903803e000002054030302152a124981c22034081c42042d10845403a40d482c070a210700c142003480c01401c410342d00c2000d0b4400084000c15941070b0003030524050300340e92242d4400c58070341020038281c203d405843c0c0304034412100c580000d07601c0c0203044880200d0a540c041c00032804031101c1c410020442d5500d00121540107400f8009120342c80410320302520300d0b00f01d0071030600071546040001c0d2419000d0b01c540e40c86900024104040408d2688502d10b071190b0038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 827527985 1250 827526735 827526737
    0xc140105040b04110a2d0f091509051303110a08130302010f0e060d0905030d06031202060709030c091a0405070e010315050a0b0a02030c0601260105061311040b04080312012301050a 79
    0x708404140f200381705847e200607142030680401d500200da00f440c01a61501d0307000c0608603107000305005d01c0c040c1e224840085180c240c030382082ca2840700103595041200c1154014200c1000007440320380028074840520440e030007600c4d00c40d5040c18000080e10402100c05900e03911400400600b91060000e900881296009208503070400001c07400760012540f4036001a5116005034070301c242095810404283d1000d002c0c17501228151641c0d484d0004401e0070b01038010740940314606218400481e0040c4070241d14014018413103420810030190001004842550000c1d0500500843c000c00c01814101142e1018201e5a204c51401c184075105811400b522000c502003000f98404641003000054080c154030500b05000c1001194440000032404517141c0c9107904010030020309035208560483ca100f1348010204a60b407a21840022512a07904030280d030b0300f40070601043e2400d000018000c01121002403003a21398031180c2c1c200346413450510900381651800c01c92040c951003a0b020f402c408903e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 827529235 1250 827527985 827528069
    0x10b03030705010b0a12031202090429011d03030d02070f0219060206102306090a030803010e010e060604120602040914100b0301150c140105040b04110a 67
    0x10000000d045500103001070b00c8a80d12840509144e00d8850803000084c10304044c244801852550003800c10314140c03400c203c00c00e070b0124600c42c40340c8568200c0144050b03503210040c1c0e103070256016481d4101c09550024009201c101c180070080400b4014401004002001942801511024031020b0350044e0021504411110115001a210404500c0c03c021094100d00c0b20a401d00034024030345000107048031061812100c0c104405800209041c10788045800d511141c10344180c0403c40b58402c0c002c0c10758114506880000030b00c01c1c000b0246041e103003900d6007906166a9030390441190001541c00e190300c004200700820880280e000349611241c85048090300307041c2e0721440603040741c040e01c41e050f4601c00400100301c400f80b00400c1e100003030004e51515500350f50500d43c0d00b813819102420b8080520880203625414002000401c80c0d00389202d8000b4480751520b4681206040e50036030301200e2840005407505414681040c1a60a642140c503402c4007612030340920182c200c107822458111061 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 827530485 1250 827529235 827529251
    0x30a20040f27090c0305011103041a061819180206040618151205060d03020c0105090a09110705160602030d02180301111809090606091801020c0c040c0201020304030c0b070201 77
    0x1400c1e008030f800850142034400069455810003e003918007003500000303615010000c000c0007618080d44441946040400840c0503070790740c1e011a5403052040407660a81101604104040484400003203070018035003801e02212004190710b0840642c04000290b110405000c10300c1b081d1704c60384c07106000e4880c000d0780c061096074400c141940e4096144520001420350030302402002d2450248076003150050750811086005620000d403680741114680e8100b1000150700880d543c1c4c1c9010880107045100c1007080343e403254242d0404554000941140c00d40201120040c0d02ca4034092070008541d01a00603518203088030120b1002540942c00c4001d0001d0181c0c151760390340d00c09128040c010100700c14607035510a010090b01c0300c0700310b0502e20103100b00889030030007016a801007255034002409035900119030700d0320b4240020395014403920340303010b40c40400c160454100004050000c20000e460410818031580d1040b400d031300c802c0750054081580e108100b0000f0b10f10f0f504a9500050314800002e0000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 827531735 1250 827530485 827530559
    0xf040f0c021b090a0c0c0834020901050402090d0b15011412070e150c06040618030519110a0c050a061d0f121204051f0c061808030a20040f 61
    0x20700002106600c0c05035508c40b0401c843d140100c181c07003411001070000080c1c40c00b51300040c01c41505004841c0a0383d00400d100000d034540c10803140c882641305003424091700d0400011402c48440013105400500d034400c021880c000180308980103002e005000503a02e07600e903001074420324070b01c42c2c019400c880340a04c843c0115101038083c0c82d28804a10113050141011300307060041c2c41d81c18a01c40c5603d040702c21103c0c002a0007001300e40c58251569000b01d200e29402c48162440401e11080ea1080d01445ca621001c0110300c109000a03241c080310b03c0c0d1030803929801c0444003640500d005185442801c80070641c0b900e000034030b100840d2030003444004a00007207450541850700c03e003116942c1a50208040c0146d191140346603100816025201401c0c03106158002c2c143c07150054041c208035a1920384505808100a44144032900300100907500c3c28208041c1c00201180d40000d007403110804a61001400703544111740c1207034181c00c03c1c4003105040c100e42e0411040840c107075000d420240c80000f4014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 827532985 1250 827531735 827531737
    0xa030b1f0303052a0d0c020a03050a050619050103030c0f14030c070807150503010b130503061302040c030c050a030218030f01090b07050f0412020f040f0c021b090a0c0c08 75
    0x6144a580c40d651141c100301c40c204e4034280180e00103400c03203020300301e0300401030000240b000e00d000310707031070445020720f00f6001245403051150005400c0d409070010040c01e20100241040c0111011303400306005880340e004800c01c5441c20300004001445800c0b44070040760203031101040c420300512801118100400080f803070b651110000c485160000007080141e4003051103004001c03c11241d21f58060220700d0f40082081c40140a0445040800301d0414841049105008040c2c000501220070b80d045c120240c03469080130036022440756050110b40c0085038071900500c8945d1103c1d481d0f07a03080080c01c40054020790060740b85865103041c6205050701c6950100210112141690000a810746e480d041001040030000d20107020700904101140c00701201d0001c80d0300701c8018901380c45100c0702a200158842e140315200e158841d003004a00042c5186036440082100199021100401000c49100000c0008809400d9000e223600001401c076603600e8100821100030f5260031110440385503607509013 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 827534235 1250 827532985 827532989
    0x203130905090c0301051e070504090e01091442150102010c1119060902220c0c0201021c0903050604050d1d0607060b010e0a030b06090a0504020a030b1f 67
    0x3180c9400034800c1c000024032001d40700b0401540284030503d40350040b003070301248246101488540200000e41c91510503170503900036160500091000c1400e1a8000d4040e009003039055070042e0300a20805106c0d07500061045402d091481040c00d54840410400c1c05813103440000745d03845090407032040411000d10030b50780c030698803030040c51416030b02e030000282180c04a81c3e010003449184820100c48920016003c11045c80018590607542c1c4546400b0000d05140080250411103010981217040100d0800d16a002c0d0f5a41c0100100c0f14540e00c00c4405020f820800781c003603080078400d80228900310030041c1092001e0b0500507951603880e9601868084105c0301600d040d0044070902b00d545911050f032070400301d80040305640b580342050001c0c0091180100003000c0e1a0703924858030041c0d00420704880c174450003c00042c80e2a40e00d0904c400740c280212a46072140442c40300184035808148181c500482d009007841441c5800c561381d01d4558003001e05400013001d00350140c49182c0c01c00c0c03011080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 827535485 1250 827534235 827534249
    0x1f020c030a021e0703051507020a080d0209011103090f0108100515070b0901052509050303031f080604170f1216180b18011211190e150901020313 64
    0x4184512007141c06034054040c6200c803c507030010a0208081140080d11f416925140d01001c7e03170769110364100768500403002c1001825442d0100d040d1130b80c803650b50b014007a86a03081e01c5001c42032030842c484945a100301032650f40d00c04510280400d55520418120358440d00501e44601510344550000b0700117072804403200c4121000061403010013546960f81500021410001d2040b803c00045003801094200340701114400d0b0301070415038862007944280010180034080e26901d04100b0703030410326105140f528886818224400080604002600f01d2140b41c1000d000c200c00850408050240c0d1300039140d42504071003e005000e0308204c45c0c411107004003114440039046000a10b40500000482c07200c481d56021510000c014111040c421903c580c0c1080f03560035601c08050700183c03603161002c90b407540d40c10718110710280007080c039100824405611185030800000002c3c0110ba110342e000c10580d0300600c141010400301c2c4c48020142900c0c000500503a400d010300040032210800d800d84c4155 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 827536735 1250 827535485 827535493
    0x304031b0513090305030106052a07062304031101180605030f07020a050c09220c090b03070609090207030309020913020a300309120605061309051f020c030a02 70
    0x7259290406064100210001c0148508001620040c1080c001445807405204000407400e80030356203a409541c1c45142c0c0054007000388020300d45684d0b5170026000791404a8441301e0010640c0302c01008400c1540e00b0358421a240c2815a81c41e101e41d01004503106d41403201c403840720740108483c2c4441e0340141076207544058503841c01405254040d5006030844042d5080303e600d200c0803400c007145e0002003d07815201c0811a845511617071641183c41c07450202e5140c485141d550820480807900c0e0704a52150006200c11044202015140c0c1210f1050001045007018200400485030700640342142c001d090004000c485600422140c140c1110306801c0c4030b607001440b204502d043c29500026119400d03181c00203000200042e9815050040c012110300c01124174542018440d843c1c5034045c008441d001e201c00c0b41c40745021009004140c42051082440b0246541c00c1192407160304140d503040002016002c0c5040e001820708000c80035103150b850717001c01014440300705c00c00040a11500d164024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 827537985 1250 827536735 827536739
    0xc03030c210403080403210e01050604150f091a0423010b040b0412081e03070807080402010518040906060f140409021021051008101416020304031b 65
    0x901d00e811544140900418054107100119600200c901e80c05039041c10301d03510326802d20000008042c40d00e1140345055081c00f684801c3d01c40d06410160080206807028442c08012031710001c01e2607100d0081c000b00401c0e03804204101c5040d03400c54813201d1900c0d1000850414170301d01040550300e22200c3c0c01907a8014031100c02500c0d40c0c03031158034018034041041500b454100210f1044511031889070a00350f05620480c10144101370003103980000b0010701000c1207030481d40120350907400807204017021415800004c3c51143c02201d05a1041d9816034a40b40780c104410300001c04291000d035181e030410b030346102c628000361161082401403c9610700c0344150720300d000b804c0e60480242c0a6820b01987c10305500c0310050300e402c691818104030a080043e0311111034018640300784900151010a5801d1105104406841010302415100d07480c0a850104440702d1202c0240e510b4605c089440341780010018120000312030b140139920802e403041e09e19213687d0b5100c4d8400b40c203101109407414007a401c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 827539235 1250 827537985 827538007
    0x41e0e160c05120403120f0e12030408030a11070e090a0f210503161103070b06030a061e06050405070207061112030405010b0f100e011206150e010f030e071403030c03030c 75
    0x440340072400c580382040654051f4134004221859981032603011b1040241c05500810b414415100a00503020881c1e4803006521401011070700c00700d200c1185070144000100345440350744007141c41500d01c0c40080c01c400f40f10b0307070b1003940d459442c1d03006a034540c1204801d000c18140001c10000030083e0b590340c454980c20b00329001003c181c68074414a0078403400802d070004001d4040156481c1c036070041d44450307907a501d280c00300381407924100c40188075600c1c110300c100300021001c0d50f8a948010100c010031049850b4020310003152400d0714003c0160b44980c0d01084211700c6844552074510424055541050284242000c6a00240d40442d4103944a8400c000d007418a050482c010580884008141025003000500010703800751040c1d0402100f081c4000401981d5000b60000f412034029203218503079400d00003445043e0b600a000d0001d5000603101c0011481b074065004078110b50000303010072928111051000c00c2083c01582e425010030f010031700c518a41800910311407154900381c103503035880b0000c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 827540485 1250 827539235 827539253
    0xa060203030c0f191d01020d14030c0f0705010f061409060d020f0d061d030f0f0d06050a06020309010e1e041a0d0506100803040b030a0e0106030602030903041e0e160c05120403 77
    0x644c0d1b81107611422190240b03d50041072030804040448016a070ba07210700e450902c55108031296521310301c4001070b0f08010000c05600c40c445ca5143d02e00108002d94032907002d80d080749002900d140e803050a80d004a411850405d802c558007610007410074175885281e8020812050780b290091b2251031f41c03031942c4907005100c024001c0c070201010026600d41042036654020314002c0d4107940c1041c0fa4007096128100040d80c2c005005850000c11001c1e803d036070392000035607035440f886035980081c5800702c2c50102401c0042400d29080540c18103801e05c211000706001c001c2c58414003066152800080144103a01d510400050f100e01910150607140344c44080035030080161742c8000712a60040000700410013a401c256500100565400f00306003070b0710440c042c058440783e04040d100c18800000c0c0003003540c0010082003210039880741a02e40303d12952062200d10024419051428082000104048450b01c280d008c00400b5040038184420691030300b030703d07000742ca120f250f09940c070010f424018001180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 827541735 1250 827540485 827540537
    0x2090a0f0b04052820040603180c050d060908180307120f0609020d020a0602010c03110c07050405060a080a0602091c170c0703170d06050a060203030c0f19 68
    0x344043c070040c1001c0d1801d42400c4984d00c1c071161915450300d0780c0300f2922115000300c441007640d1814511501040f0403041e04aa0052203081c3c00310f85006540c0800781d1050035002100343c0c0180b80d5103869490902400a410003854041b80d60a0b034911820000521640180c000d001d506119610151222010704d40f41c26020341160f412007004100e004002107070020422001c43d4010800f240400c120b1002c40ca0803004c40e00c0080d0f00210030840840c2c81541540040c07405101c980c3e05110701e85c1c0d01c0c410700e001445424080ca03030541000c41c081c0103906064008540000c005000e41070482d40d1184240c1c03d011695100304d9000c0c2e00025121680e01e0552041c1c00b00d002d0103804401610203654075441210503e86085a0303100d000f14010000150a0000344029a04103110752006842d00d902c44000d03901c140b401e00c020381d1a1000200e0241000202282031300c40c160000c520f16160f01800c201d06400290300031a079504200030102a0134001d6280350401c0545458102001d80c0501002400b500300c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 827542985 1250 827541735 827541739
    0x80c0f0408070f090e0a0f060c0e130504030f090515181302191412281b08010312050d0902100c0209090d020a141e0a260a0e04060302090a0f0b 63
    0x41403060108150341051f040087c1c1c41070001030010302d81081170721002001c1031003940c01841e1040015a20b00a904168410b034801c0c3d4407041424150f2600b42c0c0c90360524050355401050a645802449280000400308911140f4071400166070850000703851704146030558a074150081003000907485551500401020309040688204c007240c85001220300404018850102d241404500c18491500c3d00c2c5040c04842c00010080c6481d503561017000e4011141e008900e00d10781e80e030010368148202c03605170581b94043d1030049030f40c245440c2101c541d04540900041550713074030b001c9001a501d07046100000c203102e40350f080084440e801008040c01d001448080c15820180d14017040c90380c0826a84001c0d030f40502c0c140c104a42c141401c9103046414641582494401c2d2691700c5801070015004036040d00c50142c0600108992240b4241840c0300070195516034000c0c042c0c071703103898041e60140000020207000041d0556a0350005440760760203592585013241d4640c6c00700d082c0d407100d01031042403801c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 827544235 1250 827542985 827542993
    0x31a0a020708180112060b07030801172a03100b0906040c0e04022a250e01030b06450405030304061d030a0e01030e0607080c0f0408070f090e 62
    0x42d45038860248105145118180e210180c02c079a00e0307003d01d400c4203c402c85035108001c51615100f20342e000358800001540400c9207000001822404132103c1846003140710007038044c0c0c520954031039030480c44010f6a184407507910440c001c0242c804010540140066141c04101c40e0315401c01d000f04400d02405160040d41805502240c1c03135001300c01220064425640181d940300001c2071042000c10b62111442c0c00c07085034401c030103040000510700c440640a8888034102180d041c58122040d003841c415969104074441c010070204240340d19007540440d0241c401010b0684140002000340b4140d045a031072040703403e2041820840617000d6498000b51503011035840d0801d5218943e481c00014002040c0d0754a841441d405140014030140030300c1c0d02030b41100d484020841c0b000d0301e850810a082030000b0300d4219460b258110003d1914001c10091b2156001d03505d03002a40552503020400740740410340308000000340110304204010050074481c444810710b40c100b40c0014203030b558a0a90300b0090380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 827545485 1250 827544235 827544247
    0xb030c060d18150c090b07020d120207080a080309070609030c03080304140307050616050c1c0c1703010501030f0b1e0303190e090f0c04150e090a0b090c0c030f03040204090c031a0a02 80
    0x596184040d8140c1cac01601d0030b1881c0c11140c80803440d1554a401444050064400c80c0c010080d020010318020209030040d00c59040e16082c080b140348000d84406030a07c0c0c5604010070201d00054003d641085c01021030350b1820a111880302e1469105c40300803501c607403110042028140c480b00c90f15031411501c0c904203141009192030381d03036150003a00208809814034128890034601440c443e61980c1d41c00520350500220080c1a940c51740c209102d602d02007030901074441000681c40c420078050b0079008010880e00d18140c02d9102c94400102d0780740d41c06100c100516403442654903002905500d541e41c41920300344008081c4049007034040c20b40b000141403201072001da030201c10251002d030340d0200b0808070b4031002004102c440d070031441001c0d60014040300501010108a400c401c010582c02d468016143c1c40d080b150b08407074030540815102c43d0300305208118019060400443c0c20074002440440c00403020744a00d402904158001c507030800c02c40c8200c500700d0940c040c04580c8268007007021400d100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 827546735 1250 827545485 827545489
    0xa05040e032203120504240507080304060e01290907140a02011e24080705150f1b0f07030510090318080c0102010b030c060d18150c090b0702 62
    0x4000c01c0310902900d20050900100c0703004456407040115000200320803030108500f0040c049501078041c011048a008000c8560241c9081f6410406130403a0703602894150143c45100700c642003c0c200700d07449515480180c0040009000707200e00d01925901c240003204400104100c40c1029007482401102240100284140c00502e040305c010070041d41582e5424000701d00300d004051003811480c840b80c60480c15030130041c80350b2000b49a1070780702143e11108454028240d90241443c0f01c0d900040c8c0c043d0900f07011a0804240382c03241c000b8450030450810742011041d0656402540829a4201c013000c0101c01110782004200c00981c039400150030014115101d2549030a07a000190b243d851f203820034107040600c02c0301c403011010400901c01c0700c140d8458121540302c0c9400b20401c0d00541c24074565400ca440c0114246030340e018000e141c0c6103041c0c100d41006014101c1004070350308035021014180007184182c0e4412040c200445000194000070180c0645400e105806c00b02511070140b00e05030041e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 827547985 1250 827546735 827546737
    0xf15010920030a09020d060906090b0106020a0b0a020913060b070b0f04050a02011d030f0a0b070921050123060a0611062a220506070f110f0405010b090a05040e03 71
    0x44083e54010807489a98004101c04c0d441c070200040041d441c0800c0041440301c00d502c0481e01c0d602c0f440582840ba40e941e80101c1c0d0f128052503000d4040c80400000c650360000560040c0792505001d007144000c05444c2e4030040c121140d030f503c42120010002800b4042201803d60280c0c07040c5250521201403c05803100750741c8901141c2e0090612845043c0700305003c18110b26811078a10041c01c0b08c00d440e0004c0d8107261140c3c0141030803a041909000400c0c104c0b0b014600d400d00b40e80d070014203100c808403d40d200008901c1011400c0d20715541e18569441600300e4100394051051613490038804a04003c010701c00440110385c418800c02036041143c00600001140c0039410903421710782a682c803e114013944011407100c413007402c00b5840005810307410203016170900d42c00c03650301410841103c0d03441050054030b02ca485402072440401040305000104070340d100c0b8035a01409840c3c0720102001d14081411500281c028100480d0045040003d40c0352801d4000e000d80026901400801c501c00309061340c0e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 827549235 1250 827547985 827547991
    0xb010210020f0d0b0337240b030f0a0209040602070812091203070f080405070506030928020a050607031707030603210504050f0d020d0f05070b0a050d0b01020f1501092003 75
    0x21061070170002c20f0041d04036006c41080641000c0d10280920364401c2405401000c40c1256070520b0030203203007030b000d8034000c02d070052624400c901400c582c0c5900d60130041c40ca14003d001b01d4503540d013400000007040c0900054504022203210800d5982002110036107400f50185007a40184810010011441e5001c0c200b003082c00e106040102c60341d250780c0350580c1400425040660003c501004101d10302c82d0000300380c030748000301865000b42260040b021104440341010083d40100c0e002c441003000e410000700414125000e4900315200c45818100340c0080441500c07000e0000e6202c140500a10141410340c034030051140c2c1c4841c01c41115400044c00c14081c7c0e1140344c2c802e00308041e82104ea601c85003201d860040c2e00900303a00300303c0c47d145030036400800c00c0001514a4030400d01c000ca481d0405200715455910141ca0b0603060940f014496005400c1e40c002c620b04500520010122031b280800041d03904200b41c0c20360700780560500b4880e10403521100b0045c0701c0c1039070307400c211134a0441035021260 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 827550485 1250 827549235 827549293
    0x30e1810050913171806030105030c0108070c0c031113200a030b0306010b2511040f06050303191e120e070509040b07090b0f0d0b010210020f0d0b03 65
    0xc0381e42c1c00c00c09642040f0b09000141c42c103400c188640542c0b05a40c030041100f00240600301c0e0880d40300c1001e020560000740100c0750194003685a18149601034440030340d1021140c58000003a0a080da110303c410b420b142e200b215805074100c418449443c2040001c2c4110921440822030b0815200014111105244402540010000d40307010710502c00c0e08810800c0d00003400310707001540d40b80c2d16044d06502218000e40d07040f01c00c001c402490629039101c0c0c60016000300350200704000110400000f4181d0880c441003c994820340000e10342c6061010300b041240b4440c0f44074050900740c801a0116400301d002c0001e0180d002c8080e42c05d1074220000000510448000041101540e01300f03516104d9903802113540100c21758100010420401070a511403001a0344d04100180d48001c1501c241c0561035110f00100383c2801f0511060310541c0c03191900507070501c11601c600141e24041000c0341e2060440c0031101000003040500312109028400e100d01080d401454580303007044541442d00481e1a90341 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 827551735 1250 827550485 827550499
    0x40821160c1208090708300309060c090604150509090603070506120a14011e080c0d02060307140d060302030c0a1a0c01291804020603070e150403030e181005 69
    0x11044001008410080c00c04442100d450040c0f00310403440c202400b543c0780c0200352049594801048605066274003c541400040107035485802c06455950003c0190f90381200c0103100007c0c000c0701c80e0005440b030b01070540300c00342d56441541c14064040c0c4002e00690080e44045000c0140362154801c0300c148402c042144481d549075a4100c00c05005150440141d04071850b0000c100205864403039a4240d894100c0103611070740e10710701ea64841d540a0304080e4418142c41142c0c000d41800320066501c0b4610349040d011144d494a0000029005000c2c00c1004507a142424800c41c20104020340b00e408080b00d80c140114034002e00c1585103408a560b019014602090400345218250000005000b08803814000d0031b1452010700f03004c4100c1c800c0607100d111084c1220030b03a88500c1103150301036038010b05260b1450356448000d55650041416007030b008620180130b50007100d00880904007035031180c0c2e200c080c10480300042261442000c0b601844049841c001d000e10f41e1801a01c0404640741540c3c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 827552985 1250 827551735 827551741
    0x3120c01090611090a080601050607290403090504060b070f03030c02071d040b010b09010c0201051e0304050c010f0203030907061d04020712090f05090a05040821160c1208 75
    0x95800750142420007400c890030034540e181c00d111100d01400101400341c1e071a00d07402d961010309541e40d010a02c1144d410010811819002c190b05982501030340c3d0100025049450a8541681e50950b00700d40c01d5001a85144040c000c80c986801036030000d0201c81030807820140240c0760f40420092000c0c009003490303500c0010306010b034002e00c400802015814001c0000c001484054000840111401c41d07100d0781c140004551181500c084d6a0b40e19410b94030280c561255a005544543c0850040e00e01001c48800d1068126141c900451045100390041c05290528034000340414016510321010742d0014000c0100c220400200401220000c0c90030701d0a540350000c4208030a00600002074002e40005480f0303052040c40755681c0084821039a680110641d02d03400f50a901001d8000d40303504c0540040410181d403802d0b04840d030801e0084543c0f5290a0039001211403054440054440d40603402d420800d605070100d1691091015a003800001c8a4003503403075200c035022505c00c0d01c1c10b0005407408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 827554235 1250 827552985 827553007
    0x150705070b0904090209010608041a0103050606213703081603110a050901020f0606060d0f2d06090603080d090311010e07170f1c0c05100b1903020312 66
    0x8030b452178000c0e00001a95848250041500c2400c840a4941c2c4441c203500303c0344d11050081c450f040341d402401410490f281d4004110145500c2584261040c0e41590207030a00c0c44140070384000f80182e0341f90202e00380403050b003500814100c5540da4660a280d00020404640c024450680c41445444110110b529903c41a001041c107031102124890700895040b20300390f0810014000030784260201ea041c50080c0e00c08995809080794583e410000078020003074400380320b40021080340c80603280031034034107081c2c0800c000c5c00703031088403100c41a15140150102240280710301000b80000b0030060041d1419519401035030702c030b004140144207540780562401e140c8510150781c01c28400c40003d0211030340c01d6001554a0202e400754000b40b40021140340a90040010b0030300c1c100110501a0a0481c11410003800503090700c3d540009000c00705000c04001b0b8001e1000c900d20013085040000d113840d8400512580c40b400f640315482c01c0300d04103c01d00159030f002621404940c0c03c910226070311500c5601d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 827555485 1250 827554235 827554241
    0xc040b0d020c0115030510060312200d02060f0901060f06141209010605030d03021201060f02030408060108030a1e17190504053313080f1206150705070b0904 69
    0x445610154a4043c110418a109613024000c81e4081d104403017905e00501146003c6034010b21005241c510b00108108101e0b000300301b601c50300d040820700441070039000b42c40c00f424421900c3c0440016000310781001038034090703610020307080810300000304031560038080398403201ca00500661041c48488400c036003028030240202c446440f0300c44402c1d161800c00c003c05a000e07040b103000d40d40c424000e6039011300f0076610034030a80c0c0040c14aa0300f00301060746400c1013600d1400e401c50361002140020003000c0b030902c008011a40c02401c0620003540c3e58010403000620440403c010350384012032851205c0340281c2d200c0a8680039501c0310718076510303649900d20054404151210040c0d201400c0c0703410402882000b28595041c40c043c80d802e090604980399000504100c0385c0d0304642000005030200d03e040d002e40481c1d23543d040c0316080662a010b40e41c030105070301e904070300114902c50100700204646401c0c04c440b9140c1520400003c40d0414075250f032140e03101c120034016103824040115500e800e81c0d603290 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 827556735 1250 827555485 827555497
    0xe0c0412170c011a060f07170415020a170a1e1b05210705030a050903030d0501170d03150b09060d110d0b060901091203020a0c0f0611060c040b0d02 65
    0x121642c0c0c82240a03000d50180c0342d0b880302c00010421400006645040a10172035400c02c03040d0006074940080e070794603650100d01038000f07030010002c00d20003c28002e10440c2200c0020740c2a4008003190052072400131052181a2034042030b40ba400e02080c0405900100424195030208682621405100004035005a0780391103d07401c044d008085a000d1200c045803543c91140010040c60070712450700d1044d8500d05c6000c4d80140581e008005002d00f440c802d0300503080610008081d203140031203030411901624800c0c0c126001060400d00048142c40c42006440d1100803a810180800c0303544a0300180c051501d4441c0c445040c80000715a40540c1c2e414080310150104854104002c800000b01d41880d50000003000c51801d2600d4100703c1e003490080c055581800301695200802d504101044c0e55525584c9000ca0951080b420a08002009402400d01404412411181d051b01c2c06000034040f082c1c1481113903241d00310b02c0038450400700c0101243c1c142e07440c100421703503102c0310149501c000384911 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 827557985 1250 827556735 827556773
    0x5090117040201140d02220501090b07110a03060b120d02030d09031704031e0e0916030e0106171006230a03060608030405011e020a1b030203010203010b0c070e0c0412 73
    0x554881d0f030041c55400703003e00c0d00005c0ca11f010002e861200e401d290384440d000310307400b00e281c030a03040020b0b00600009008030361040641414628419011900303d9a15420840700d4685848901d4424104a04041c1c9010309000c010700d07142c00300841c003035240d200c0c040240d031020381c403a041507003414083c600561608c04044412411b5183c141402012264110b030380f13008200c40307141801c40292003041c08034540d00c80107110401d252035928592485000310200d03441030645404403e0401305007817003604002c007640016032035502c00d100201424024200715240556240c20700a01101421a540d40040d20080300100c448643c0b600000d030954040d644002c0400b0304016000c1100200400940201c2d002070305c4150740800e0468940c035001419030304000050303010360444c0c0d01051240d4160007607040f480d0105040651250003003030a903070098015880d501c000284071306102908006190082020700e040b40e8560070f22224400d07061059200d641328034415107104070144281206221012000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 827559235 1250 827557985 827557987
    0x60103090f080a080609070f03020a0915170c0f03041e140708150910150b1812010212070f02070f0608042607080c01060801090b04120509011704020114 67
    0x940c548080d01c0e50002e800c0e030f00000e02c001301081c0141040940c81b8010790030f90701c40107183d03d503819048000b0b4000700300c1c1104110001d60002801c00031603d2214071241507a4400e11600d10705407100042840113011241e104a041080b4001c1244d407000f030300d0300240c1c05443c110350707000c542c4910507104258140240600c2515038110700c00b0000082c00800711640c80c4203807414030280051000114108507030b03030034041e0010809180d4142150340080583c0e04110300b0010065250200904940c2003200d480c204c10700c049902d42e80c82d10b4046004051811420029894102852501e5600001c094401c0007840301003210f64034014002e01904000c0e2642d6149e169240b540e07104000c004140c251030a943c0c2c2d800d848100002082c9840c03540a031910010b10780381c40d21000707544101c01039006810000c025540c0b2a400700f00440280104200030380203540030801c2e0704044c24032905844035022503406105003000528540e980110825210b44018203a4010503034540c00140c1c0d8244030310040e8004410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 827560485 1250 827559235 827559263
    0x306010f03020613091b0f0e0109090507200309120708070317040306180227130219080a0201021009020d03030f02070507090c110106031104051915030b0f061806010309 74
    0x1412a030f40703106410291f41d4001c1840b040c40d4261290f4070b4443ca500e00060301800103000411035030701710a82200441c0b50000100203805d0380c02112410142e0b0a00031600001010b0209260810201c00c02840700800b0b02400d51030030300c443e035441c0050f100040000306115003070314081d400042030b1001150810018805030445600d08480398005000481c4650341200f03a26603c03d41003031240461010000301100340d1340320282c2002d004c2c04521701c2203030f00c841585a0410410301500c9036170b00070300368100104029422840060704140740040c88036100c038075110000001d40d0381c08102100541c1c1604000560510005040000c1c2c440c0d248064614400e0100004424000388d0108440c850750382d44d0b031118185c07408126400d0301d15030b1002400700d1500b10050380c00ca00d0180c0c807240d008101529000c4041542504078416140740c1d8103070b50004001c3c0482007091001403440b443d400809658490014a400070003c3d800a90b03c00c2001442401000041c44a9009901440400d50003a0891071130130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 827561735 1250 827560485 827560511
    0x903030f28150b12071d180f160219030c0f03082508061516031e320904020412050111070b24090406090c050306010f0302061309 57
    0x22000a081504104a00400141414280d401e4030940030031030904070380c3c948070180200c0f0084c104e0090052040d48201d985c07941607450610100a10720301082d190301238600040584942000202100e8181c08036500070f030b00c03043c0d020942a2401c40105012140c0d500301e03040499649094031002041c07680440f203e2802d042d003014100e84030300f0203143e0718054580048408a1881e10402c0030a02280c5035201241035442d00c00e0381c0700190b040c600101400c001d00381c0322103070440181c2c1c141503002c111014110340740d801020010b02d1110803107041020000c00840c082c500503502c1800c0c0c802c135082a51841102c440382c0601202e08201c0020010740d00c2e19201c1c102c5022050030b51400711070541c60950850041590343c03090b101c03020342140d000c548039900c5100400680f45008000710402144d50941940c0c2d41c1c95040050049000d00000600b0746807502d4801103602a50300300078441d50204004200845040d0082010f90b903040c1e0705941c1ba041524000740c1400300750380040c04102d003800f08070b406007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 827562985 1250 827561735 827561741
    0xc020c0a031a090f1902060c03030c030f0604090b06131b020d12110306060309031c0e060f0408041712031608070504063509070f0e0903030f28 63
    0x1410300b40126000d070741ca51415250f40c070050007808075082c4e000035201d11005041560003449450026011601e02141c00d14224250380c0120750030360200c0d03004014480c0011076100d00c207038008000d403020400603081e40c650550f251402024148205075100355021158000d130881c2c410444240003080d04410700c00e0010392506c0c0300e9051078000601d201400300001c0e5160041403554000c10500d1851511040107000701a44001c0c8107068030300c42040031010070140c040c4540d940c010b080301d000422548009006003000e501400007c10460780c01c007480045031041003140d0445840f030070259082d00604001a051091004081582c0306001c0304000303940300184840e91591006035600300403940e0b0076200f030300c3d980078501580d000a601c5501f00601d885411104071000800486505c501100031942e00c07a08080440e0000c07515003045a0410601c1072a00d200c0c4050080310660030010b240038025150349001c01411440e403090ba4602054010741e481900507050901030041000340101a45480c0c0a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 827564235 1250 827562985 827563013
    0x6090f0501090c21120323090d0318020307090c1101142a0a0c0f05011505030c061c091410060e01060e030c0f01050d0f09020414090a060c020c0a03 65
    0x4a01303400f405201c4c00079207030341c14105544c4046151504098100e045000b0702040c60302030a90003411a1464140f115812150320480c0c002000b812180c030448401030075a251544202d00085070082c11100596002c2075442c29108034880002c0c00040e031050444610300b20001b0f40100c0c0d46844150303c0034a02d080e144500c1004940503280d032968100d09940e80d1041d50414204040c034003441808a1688240e40580c03007035024024440044c2c085032501c60854658800200902c502500204042e0506000140c03d024084524a08003400d24100d07031170ae00100d1814610556443d16940c0802404219418040038284c00301c0c2e9411010b07002c480000c00041c0226410003407040000a5070502c04c0e03040203ca403c000d005400407550300000d2000303050000d1040c07814007405000b5010b2000c1c0364411070b590303240540d00219440d4030900601040394032614054400d01450000c00280c540c00040404100ba0b00030000100c400d0013040490429114040d01079100c002840000103000c0d0407101120 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 827565485 1250 827564235 827564249
    0x230304050606090907030b070c060e0a1104020406050d0e07080109080c070801050402010e0d03140a051b1204121a0708010603180210050a0504090603030503090d081306090f0501090c 80
    0xd0700e4496804103d1100422911200e00f54001101030000512010999070400202e00b84445000c3c01c03540e803101500d001010050071a4003103c4040c0911035456480d00c104d0005490131403620b801c0c01c1d0010b0a91003030064a108039903c0c0e4030684480b0804018110003000e541000300300780f0141d413410031034540c04002c03480403d101d071a03008140c500c410f108442c003440d41612400074022804041c0005000c8040080c0d051104d206502c24103000315000510310b03401c0580c1c84035910702e80040090740300d445024903284d032903010381d50600020314000d048a0079030b00c83e40f01e03010341000ba520b07054188003001c21210713505000490600c094180c22031821810b981e03064074240301c0c0320000007046c0c10b0103041b4103020758415150419031080c240604000c0100000034035080c1e1a15480d108000d06481c0340f1b070b20440019000204001c450503041c0040403283c001813400e00c500c2e00780000e0b82d8004240310b0030017400b507542d15400c4404024102418082c2180c1c403000174040f281c881c6c2400d06031684c061040e14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 827566735 1250 827565485 827565493
    0x9030e0306150118061209060f0e030901030c0912140a050a030305010504060e060f01110c0319050129101709060103060e150f130b09030c010b0609010c1223030405 72
    0x4012141010210b01aa017aa40d101644010b101e078820002e011000400c2d19902d07520100b40c6940c0d50791740110156030001200942e950a001c40004040301da0082c000b20400c51440800c1c0020560340d1002c0ca074440e0880b0514050560513944141000001c85000b400ca00c40c410a400c02c05415401890482e041145c0400c00160f40303078818032044204458140e400080c21070610707010342c01540178038041035a0008690300c1c0092503011925090114001d20009030302114a4810004240104c8005600e800344050203207100380c4801c580158001910ba104070302170042c0c482403a10802d4445010920050030414a041424107a1380318082070005540c1142004201411840001404012740c120f00500c020542e483c40d0b6980c0510b030020705121b200200500140c03000c80c480d5003003e03020340741034409960b03100e140000d80b1b802c540c1c041d104240100024000d02d075480c0e801c903000c000055008031f0b442a244c204d00f1000ca55a1070200c4424002c000114000a0803c1c0711102852159101c0d00441d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 827567985 1250 827566735 827566757
    0x6020c06240f010e090901060909060207110a0501090b0c1f0c11030405060714030415050c06280e010b030f07060e040b150f090904060c0f0810060309030e03061501 72
    0xc4008016500c1d90740d0f0103d00e0f00d903a03010380c03800d000140591142d07414000280864461045034180c43e00e01d80700b030b41c245402040203014070004181c040030301c0c074048030f0701512285408000b900560071886a5144140d01107a60b4030802014030281d81d0030240000c85c0d0014000d030046a0005000c2c0c9c0d01c0c00307000158800002c0d082c8031000402c50b0144c400040516040080b179903074070300301d02a8140da03281075400240720001d1707041d601480340c2080c81201c4d2a200d1722062403907115460f140000b807421005000702a086020b00c13101d40341d450301c0f5110304480400c240846000e40e81c007501c0300300122030b0548180d90b035400650b14040b07190800d0310004d0380c0f0301034012b20b034401b0001503900802c1e000d0341c480c0d058400604041591002041e9043d460800e0398102a18440007070300541e42103c09542035034403031284000641d0b00c0000c00e0072264a5090066050a006003281c451080b05c0c000c071030925540f000d54405050107400e8200103000e0042c11540b0744e2400e0b14009000e204140c1e00c05003c100c0040da0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 827569235 1250 827567985 827567989
    0xf050f16020d120b010201020c030406200d080c0903013e0903120c0a080d1409060403082806090c030b182202030a05010c18051c06020c0624 62
    0x242e19081d180e0395240c40c1c400d04030030b10603c014181140258190340d0b0801c0200200c41060018000400054685840644200178040c400404103144198142c12550902042e00d0308150a980c101c501d000344c45803030382c15210100e80100402008040062034503120485890144103141268a00403400d81c2c2d60080081115040c2e80920702142d64190003400b02141c904c8c0058010303040c075203052001c4542c180b129886006160340800103e0070243e072159000040881241e00e03c54004d0b0350316000306110700d8075031001041554003030000c1008914108410266400f50544a544d8114400040014981d83d402a00090a0100c582c2020a0401445040b2480d01210f004c01e0102d010580d001141e55580c2c040400300c00c40510225003610040303500015850810540c42001d100700000501c00000017000380901e24100344002c5044c00000083c0096200c031b1441010b0214000a5000909500c5c075219010340158a041d4071144035403020440c1070010042c0c8140d031244062000c07000d40c2c80c4442 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 827570485 1250 827569235 827569243
    0xf02040b1212030a1401060c050105060a0308120a27061a01020709110d09050604050c1e0105030c160b0403110120090d0b07090501031505030703080c010f050f1602 72
    0x100380c40c2e4000c046642401000c0c40025948010b040b40000342462064004450b2031400381c1000c0006004450030008201c0240f08951f00003800b1140d1806491440d500c80f03103144a00c54060f40c00a00050104010b004540c00c8041d41c801c00600102455242d56409649040f8411007078500908201301885042c0d106805490380c1d40c410f03809020712a003040d51a801078501c07000c880d03400c5241000118140c03d0244601b00416210344007422190805041c424600f03080092103a20480c0000c0d031000000410721101c110340402800c045071295103140b4aa0150f004400e00c00108504000b03071082004560312025214501c02c2e220035a450001442007400c8030107040c0c014a80c021904003503070322640140064410580d0051086d02c64100c10b030b070b90684548003500d001001c200c106105011035030701806031800b80c522040c28004d0183c07138003000964414452002502c0d1401c0015540d190810a420804002c24035038424040c41c103000c02045540c1804603500e4680c1040d51011000c0548045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 827571735 1250 827570485 827570509
    0x301060f060f051b0d0914010306050f0d06060f0b0a23030a090807050d050d060504020909011505070b0702100b090f06011407051606020c1f0804020411070f02040b 72
    0x50740b0152201c00180c0c054034680d021807080300704040c1d0740301c180c110840200300110101e2140d0741c1d000c1c400c605d41407462180300381c80c06040d4107040c1822800d0007241c544141031414800225032455190030340b410300038001c105640025920291480002c9900010140208020b46080c0d036079075000100140321842d41003542e400680f0914042011078091034840d04030a5100d1700501c46075142c8522030341c0d1a0314005403011024041400856074458036141c5102d080c0040009640961410341c081c1c00041c05c9141c1406511084441c2d8550140128843d009507002c00350b224400303900e1410040b10281d9211142c100c0000441e040c010701d0600c50a00d2000c0038029403000210700343c0c0e40c94140054070021000e914810114100f48880c7c80030030010002001da190740a078000c0589410140002e081c54040d0304458000c9103800c1c0d40120100c61038181400100c05c902c0e000403079490390b2001034040d0100354802c260055000c42c00c082030101d5401c581000d207200719410000381c1800003c1c003100760f080c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 827572985 1250 827571735 827571737
    0x1209051e03250902070c090f0f06061103190507120903110a03020d0609020114040e0114060f0f0a0302040909061e06140105070501060306180c060509090c161e020301060f06 76
    0x581c2c2008145100d8000c1c2526902c0b50702030682254480f20400211140911030b1802a5107074444104d00004620808026041c01d1821581e0000c0d03144a2964a1040300c0501c41403844180f1601d04c95841041900c10090788807110062040f00c0902c014124440385c00709646440c840240d4003c01e142c60b8021408896000d030130380300b0b4042c498a85000421000388140d0520000420042c0d2000010000b44090110344148503c2541854180c0d00700e04062591035019110030002c469003003000d20249c820304000d081c1500d90b520740c0c0c1601100a400346501c80c045d032505012040c401c02040340c0206541c048080840c0c2e02c81d008043c9005c0c1991038500c500f185588403400300000d076500c106c004204681c060300011403155601d983d1f20301180d0300f8550482c40541c001c4004010014000b5001c0300508d464503009090042c5c1900003000c1c20030290403580032a200240141d548140c0521132101140c00000c45445405400c2c0e8000350710038071031812031095203090360104000070414004d00941c2d40d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 827574235 1250 827572985 827573053
    0x702030c0c0126060316120b15030c100c0c090501150f090b0918090606030f0312070503130b07020607090e0c032a160c05011b1209051e03 61
    0x79a111548843c003002c1d141076018000ca14804a0804090700400c0041c54203040d0701800703804504180d022982c000d00b044c8108a4803d00c2c20807690380c000760026600100300d0703800100030309100c400d582e24010110001c101c1807000800040345005580014101c840101c10a6900d001d000b400f102c0c0808884510404980b0182d018402d0a4200c000340c091640d014258413000144101c60701414101140c80e5141c1303620400400010b402e0602801406600c040c2c021403d010404802c074010040081c2203008001300440001e1000f002190f030608169001100741000d41040304009454010403120507010603038228000604041c030b690b0143c4242406000c0c242946c64088018461000c45003004422040c5d8071000080c108500d001000095110b4540b1007a050043c81c0101d0b040071158002810700082d8604103100c500b8811400030010b40c401084100031160090540740482a5004075400c240800106070510354900138900781e01c0b60880480d200b81c0c294114216450b0701030001120840c0f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 827575485 1250 827574235 827574287
    0x90e061b0c280501090503070320100504080d0c02070501080115020619140a060317030c0304020103090c1509171f09020d02090a0b1014091201060e0702030c0c01 71
    0x12002d5074038282441ca036840d01c120340c030707107031100d82c00d40300c45c08001d03506074200066041c205500294202c5182c0c004050380c01d190351090350200c0d112042656481c40254039403000a003009200e8085034826101c229082000c504030010080d5240a03071300806000c2080e00c8000304d03600541d330030220345c03140041e801480703a90b80700c0300760301c500f50000c0c2d140381c0d051502c425000090fa0403800c1010b115481c100c4002074035a207942462180b0f440d1024555152910410900c038060a00004491348241c0a0070040345503038061401d0b101c00280c40d03000b1402c0483c5545c0d402e91081d44030644a003200c10321880c0307075100c82c50a09a280c84a8086182440ca55090400405001025001241c0c0507000822610301c07000280c0209450b1302c000c5400d8a00700d951620100444d141c41c444080000c0414034200341ca0781c6409490700d0041c407421090f640b082e00300d69410754140740d094002001402503080343c0512800c0001010355640c101002e01c50007402030748003d140a500c286901480c04036040e120307880c424 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 827576735 1250 827575485 827575513
    0x30f0602460201020c280f0503030a180b04062f0d050a0c02071512020d0b10020109020105030a0b030a050714031c0210020703110106060e1201020928090e061b0c 71
    0x70f80d01809400c5035044103107006c04a114040e44d14441405440956035a1901500b0401202d0f046444c10040300500da203501d003c551215603281d809a405100051780c0301010210480308a01020540021a45c45074903086020000011707000318042c1d00001d101e41e40391801c41d4826640c124504100503408180e00b0090014a1a0141501c40c190b0420350b07407001c0204100001e9901ca8041c69010507168410118241001012160f0061191008024a0044d540000c1c05440050725105019803101c04080f05540e040c040400c502e5446070485d8202e55580101000e0554042203181c440e0040ca1101280c0744442120941900d4059002e4428919895240310003500b00c07041c16400c0101180d400c0714031034024032800b8040c16498503a55280c04001c0c0c01c00544422030344d0070b202564010700401090b40c8130418810002045071011005c044800702030448001c1c1e01c0c2d0b0000e0300e12400c2050301141501c01003030b1039000f99584810304c940000255100c2e00f25101c2c00c07a900c41154045009140303a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 827577985 1250 827576735 827576773
    0x10e060301120b0c1630020d03020f12090105040201030b100e0603100302030105040f020306010b04080715022109030c1002150411100207080c0307030f0602460201020c 74
    0x74880036443d60900e102c1504a404c82020382c182140c05402c5418490b081c0c1c081c06c00703401401100c440c01242201c507045002510745199120803018150003090680c0d510b402082580d85083c04007440c150b5078503003100442c0c0a007000b924180d02003443c0c0203110071542403001c2c0503003100190ba110141034003e210305020007540010009100e0441c24103000c001603500780100740c007440c014420400390a0b0507004241c14101d0603848150f43c200100f1041001110109401c1c0c201c0d0031000d00c179036025521010690601d15420031a24189619028509400d680e0704064090306405404070307543d03901c0803003e2003103050800d016440540e01c026040103943c01c0107190285d00a02c5081d64010141d500c0d0045142c5002440461000d60410801030000600401042c2c0310010118010140c1343d2854848510310148244068032113034000803148090f20030a0f0b131044c4135261440070404030107030080c1d064039800300c0039200c0006044030034988408244140281c1d20705000c0000a010854102d032255105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 827579235 1250 827577985 827577991
    0xa030f0f030902090a021e030105010e090421090f09140f04050f0f0307050c0f18070e06030a091a01032d05060a020304170703050a0e030307150b010e060301120b 71
    0x200340c0ca44032160300584a40d0f44d50307030051034854000350321080400c1c0c2d500c0c0f400d003903010500c00100d000d000401c52680d104240d03000f600801e640c40d400c170781c0b1103040030002e1400b5482c43c0c0e03004000503041c885050760322600c0f0710105c894070f040310340d942070f1603a07502d5081d5003101110503400305109000c501102003a00b40300d03800a200f41304a400f40003204000385d040515400400c2c406800214180c801d20405000c51b118521080b42c441403100d1080c40000d032840e0404c02c03900211100e240c00a010706028200a05148034000c00203a101d192040500000d00f000b43c400312400c42103200680c030172200081c00a41641d078031001c0320a02d800d4070050204412410889000e5035070100000c90003042080c42250f0003201004c0000d0798038500360801410011204030140a1040c040111601080c2d018040e02e105ca041c500e800f51136004910006460b40c02207601c080d1050800c0c40c0c0d81450082d0a90020143c140203890301c48464040504200807030200f481640c4007205481410030001c0c88203210070b94 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 827580485 1250 827579235 827579237
    0x105010e040b030d030221040f06020901090e040c1a180411070b0a1a030a0809010f11100504140c06120703060308040b040f0b2505070909030314090a030f0f 69
    0x180c0005090002884d01ea065507400020941c0040c190f054120700c119150116410480b8a6800e07060550f40d4003020051303031030090040e507030100d00350083d40e204621010041c00300740035198450070581000c030084c5580e40300326811003603e4284040811009001c1e01d42e5009158040c11a410040040c48060080709465038942038007000004000741c0940031050103012141c400080000140c0c203200b95880102554a1003680030206000001b09180d080354508803007803030482c48038010420252200c450080545006e4001d4009164080607154031441c4284d00515982c440b070703048908100e4488600e08102c68001604002c2030b48485003440704242c0005c2d003132038001426035072600c400455400c5034218692003640050100325130307440c4aa07042c0c050a140c00d50741d860311001183c4c4021025240844c8403001680e10350b22000d110052003400020709900c0004e2040c1c0c103040c94010b00038080d150704440b0b108005130100f262540b001034190300640d8140c907000b01c0070f40b481314242c8140501103842c2d8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 827581735 1250 827580485 827580491
    0x1020a0b06150d05060a0e10031e0602270109080d0302073003050105031b0d020f0316061d0117090c033c06010603090312051e010e0c030105010e04 65
    0xc80800840c0c2c020700300e5603002c0701c000403d800c0100c00c0090002c610fa0210b41440d1140041c0210854a400000200d0364840b90524460000b85c803814000841c0b410003602c00c500c04200162401c001c40200c2c110429030141084510180d1030042d1400d0b1070b1405984403580c407014038103c030315001e50300608242e40510300314141c0c040d401c0b403658010326520311040c90800d9056010003095403d80649070144c4004c50150142003500c92100b0b030306c030300080c0400d407151100c15940801c3d920788c1d510991215801900f603401c0000ca00d007a806281403c0c0c414030f4000340710315105071072006640c9203024030404140c3d118401c1102400000ca06598043c1990b4900d0140c11409200c13a0740030170044881007007800000e80e00c0c0326148a001f1054030504610000d200b000d60b100c1c0e030b02903030104e10113042d500715041c00206100503040880d00d050306005040c10301441c02e402c1c000b004851110000c0c51030070050308a81541c0e00d444070f503100e1980913a168a41c0c2241800107000320340c0240c01d14080640003038000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 827582985 1250 827581735 827581759
    0x180309050d0c1e080d09050f010c060f1a030c1c02042301030f060c020a170a030b040e061012050c040b0d0506040606180204081216020307090e010c0e01020a0b06 71
    0x204401c0c03059070414240c2c8140f00b6420403000605000240c508000390030848100d03483c2c640807400b140d041d9007030181044099041d2004101d0030f03502c101c84070004040100300844030510201280d015810545e4820f108070a603c4d01c2c0c1d40fa203400d2114a41c5c4030182c420000c07101c240d09000180041c00e04844d14200f5003040d1400441600000700d000318000c10503e0210049030a005088591416420301150001402c210214020382a1002050400481180d60300b12a070340072002080c5282e060741d840b50605000d9000888002499400b07100c58450010380d55a5500103921042c100044c0100345401c100c58081c120b14143d03104201450b80540800603d000b10b948040c1010345c1114115101d9a0724003051008040c440c00b00459200c00b03500441c07030f00e0b0a000d00c1950b0381b00c8440180c074130440300140d11400003110351021001d9542c0076007103400d05038455440780042d01c100800134550750310b0009014140f5101d20300a200030041a0082c00080000c1d841d044441038008041c0e40e044565030880d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 827584235 1250 827582985 827582999
    0xc0c27110702120d030f0506330c0c0405010524090a05043912020904060b070503030103031202070c06050904090b0721090507050d0611120a180309050d0c 68
    0x80e07440b10b00e41080203814a0404013102030121411040141c102d140b8040403c07a07551500c61013038104010702d180242000003a1040c0d081c20300400242c1422140010860700e10720840011011303043c0b6000c40c0d0a00c22681c81c0d209000c1140140c0c88503146100c101c00c140101248207400520400350040e046081e0552584081810780c0c0140700c104d0782114156200c044040407070042160481080b031200c80048000120040010240f140b0144100364001041c50613030381c50364440030062400c582c0446d280c003d0350074000e40380d030400d100c2540801e4800d10b100d08415454401c4400c4564001c01d07222515003800d078215803582105031456005545d4400c0d100100d040d80050500c80c0034240d5038610041e400001200c21941c0b103101541e84141008115800070b080842c051054960569a001e07034620300d41440340150021101c81c0381034910010300d64448801220145100b6000b0b21300610040b4891000e041e00396a513050050b000070040704041c40f01380b4014000b210400d018540207810b09840b080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 827585485 1250 827584235 827584249
    0x2613060f02160b060a060806010e0301061a0c120c030d020c01180804050f0108091009031e1e05072a0e100314060403020d0e041b0c0c27110702 63
    0x7224400324518402c00c002040042484564011026030744028030030718080003d002c280c4054405414031602c041500010748003540118024021010700c6009a10b811040f00e006a10150481c180c9008035824905003c13011011100040000c80082d031030009000035900080d0410307100654a55210007070f109180f0103110420300c02c1d0307000d034401c256103a2500c0108009070160640e1941445107010410080c0a000700c0c00a449041429000c28501c0042c5400c03140042c0304100c00304100c240d0226610300540c400c0b10751038000100454520784c100c003188261468000c0c0714005181c502c48107884080c2c02e80101c0d2600c0612540b211a203c00c0c1d0321640d0341d4034080c070100e901500c1624682e00400074001d5407028040e00c034801601500c114200b5403002134036000c83c503040300280003c9800a105039103640c0c2c480101251030040e801c128a0300c0c5071000f0003243d4190b0050700c1e045000c1502090718260002600784045000c0d003050707810110400c00700090003c05101c2c2c1d2601c03005205100140c0c030368007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 827586735 1250 827585485 827585497
    0x5040303240509221401020f0a0f021e061f090e0f070509040c03200405042603010b0405040e03040306050c071428020d06060f03032613060f02 63
    0x54a10081c1c02e0009101d01ea00300104000300c018100d00b4500c1404038145001d00120707403c0002c080d03244480c505490301a100700d092402c86031400080113900d403076008950b80f080c001554241e401c0b0b02505a031020200d10401459a80c2d900980c000c100c20f10a24080301e58081e500319082c40440d40d890803880102c520b034442a06207504502040114100288880400b0b40f004840c1c2d0a03090426445903581d001403808014800745004c201800d5441031812404c7d9a8000180180321524292810750b110b19503035040c0da9014811503e03460302041001068a040e100448100c9040074544020400507004000030542103000800000c1301107005401340501c07c0408012442ea5981280380507501942c0d0015015181c2d0002034401c1e030158151401c245031404c60074801d841c8100c460000806486114200515080c07402c100010010010140b003801c8034044c2e1180109041400c0d9440214021281d41140d550000800121030030b405900c0c0c14841400380310006036200f403510506007264402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 827587985 1250 827586735 827586791
    0xe060315060f0717041d131e03030b0306070e0d02060409020a21110702010e18010303020f0c04050609060909031b0a0611090f13090c1418090d0305040303 68
    0x64610180030040714a02140c0443c4c4040c00d18061410381d00c40b45640b50120741c9081c110310400071400340d50001002d06074190300031003107034150413500c44c480d0039641e40201f0440100307060007041c040d03515001c9200781c4901c0d6542c40300380b5455050010000107148001e022070703025200344008a280402480608203100140d213a0450705034051b604c0040301486941e60358070071030a01401c40400c040e884190352100c4c1d8203007080e8001e411110300140c03020918440780d01556440000020a1503400190b40c50340c0a03500003584d6079058240107100642d201103540380d0708400000c001c00c446060070321442d9030181c10001580d0604581e240c0c03480c0e0952401041c00ca695110581c03c04c10301c483c1d8030580395054010710616260000700d002041c0743c8260184200d104070041011102080c841ea044840d016030311544a111090b00d803148503c0f04010501001e001e0700e04481003699581003240101e01442c0300c0e030f0040c2100441201d044000d440c0c010011810103449185205e4442d105c40c0c0840034003205 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 827589235 1250 827587985 827587987
    0xc170c01020d0510050a0812071704050301020c060f01141e0312070c0e010f15030c05090d030c060614030307060c020102040f03120f141e040803040612050702060105010e060315060f 80
    0x40c185c100a8aa101d50f0020215070b002403c2d0440426900011114607550011801041c090300752030040c0c050240b58810754065000003120241454045401881607600b201c420f450f59884136501100405805c4056400203a20300e20640d0385400602810403190780202101c92000201a0701c41d03050b0003401007200c1101c2c070000280080c41084080501402682100c01f03110761910300465070302101c4c40889001d1507a146d000f110300912034002c80c0e10340c02d4094140700079050310346801031a01e01c0d0f0042c252021031500102041d40c0b5000a1400d48605000b0002c60410403261244801091050b5420055650030440051211074a49400d001075015038200310341011000d40c050640000c0400802c10400404000702d01d0a500c0400d0340c0303240340199030340b03c0c01c190000300c2d401c510701c5582c03c8424984800b01380012905c0d40203038448643c211121003840319403244070083e0b9492100307004e95400318030403841c4030001e8105007000d0369015920000c1411020442804200554040d800f20349a50304 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 827590485 1250 827589235 827589239
    0x30a0606170709180f0c05060c0313050d020d0209130f21090515090409050f0a1703010506040504020706090b01030506060a0f0b03070c030207240e010c170c01020d0510 74
    0x14050080c0b100a0640d1001404505040040f03405103400404004207141442e0040300280495950501c0c094980506401c0d0348070b25070a4060381e40c2d080404841200c1000e2807012400d401c003210f90036100c1d917010780420705000d49035007003209100b802003042840c400c291000c02c01140d884003010710710324065170034848200784041c40c0041180b2138011403014010292002c005584900344000714001280c1c40450b20350301c1010000d8058107264101501501c28504040d00f61030001c42e58089003440f841149062140720002d003440740c0004d04c1071591001c0140020807641c14141c00410040780305800010f504032050f0380702202e400d003c0e0001c0d10f1950164003003110760700384851410050892016803001080c5031155180c21444028000710822000c88000c4040600810004000c2c0c507182651035040034030740c50514030f010020100b910000312007044000055008031905901c140d0041c0d8104980c0c280d44104d6044c039480526440e08565003084184404016445aa80501044a01800098 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 827591735 1250 827590485 827590529
    0x606060e01120203100509070e04050a050906090601270b03060405010c1d0a0909032c13020f071709130e0f060c16020a03080a020a0506151509030a0606 67
    0x1007402030000c0c0d03001d1041061003d520b070310748040003c41346d003115420740c16074801c0c60440c1c80001d40c1082030340080c201001c3c0030640c102c40c1c0002d07105c0c0c1910011140741d90b9420541c556a91801c3c0310b80500c1c21144c6061480240640b40c03001c411064000c00400c807500c5040229242080865007680c59035504c0c144820320300d600080c051420303210412180c038210301707030b400051101c042c0344100500b240d07a8007030341000c05010317800f02014140030880c2c905d0182c3c1500611781c1451118403106106100c2c450b000388480203907200740c0301d40b007103144c0741030782049040d5a03031256401103580034442e01c001c10700145030282c2d2001000d0111082ca0500401d100e05282e04592500814040040309078104000b0003401511403425030f81d201c9840c41010140500c0c40c00400c4040507141c001400b0400000703a02280150001074145a4910560440e00b00355510b01091404002c2e00c0f1905611404040d020b80001c80700001415144c08001c05403500e40301c041d51200111013a42d80701c0d1010910b403400140341c0d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 827592985 1250 827591735 827591747
    0x2f0c0706110c090a0e12070b090d090b1315020a050705030601060e2407030816170a0f020c061305070f0506030c16020d060b04060b0f030714070606060e01 68
    0x20045401c041c05881c00098103a5160660700c070215004540340030014490744c4154010300c0c500301c19441070f00c0d040000d294001005c5d0703000e404180c480e00c0440c008a80c0c000f100241b407014044041d82c601c2e03a040d09000c080c0360590f100c1d002c0c0b0404c4c0c00d49042d000c100c891075003d49402c42da07500d80003002c100c001440c2003402c25400d58846446a0820401000324580080d490b003202c41c0200c5622034030b4114a60070101c102121044c050004001060450030180c002d04d02c1c60140110452180300f00c10b40e01e808960b9040c1a8400080040603d004903400170510f42081580700703010f910150409038200d501900c0c0042c101c481856152114001c0000d10005221480180002c0c03102d1041c030b10304203404211180b1000d080040151130010341e2002c40c6c510740ca65560070756030050080c0490310307050520030090212860712601c642d02d000000121070300003500701e40912500c0700307826007159078914041d51541c50042c082d00303540e02c0801403a000a4501d03c0b40ca009400240c0310700900c001940001040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 827594235 1250 827592985 827592989
    0x70c0807170a120305070909020703080106122003060402120f010e1008071e080607030e1b0f0f0301060b031e0f06010e0f01031d03030105041b0801092f0c07 69
    0x81ca411041400b030106042d03040300c1c0d6a0b40303003904002c01d4a44420360200c52030b07182980000c1e2541d10105286007095070091105040320103d43e6a0244510f55259400846080321000c0d07100c500e802d403180c0604103581001d50b5109400074001814900c1c3c1041c3c02241101c1103480344410388489006000752000c821083e50458582c404205546044c407620341d54502c1a805808030040101111a604d1401d4004038806031030b4400650700d550400f080007401403c0c81c0350500d40c041c016040780e2910f098045502c600d68000c000e10815214841d14103120141e000d140c00c3c80d8265403161808a00d544044001310300500102c0e101203911401c007031040c81080c0c00079250001010011050000c1c903a848159641003807000c50310940c444c0703000c0e80140d004201e002d0b0040050403c1c65081e158080002c0069030403298295002e000c4819200c01040041a10038100d9012540000c01408103000300e070b0102c2410800f00f450050201c0c8030255181c0c81407009003680410440000d10352000c42d4080c080b800c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 827595485 1250 827594235 827594279
    0x3110912060615030603120706022b0b010503060f04090501150e07080105010e0a06050c010b0a12140102070c0e101e050102160b0f160f060903020d11030a0c050102070c0807 76
    0x10845c1042030000c0c0c2c440c101c41951401d441004540ca405014a45c2d0441c0d149204200041c0b1544030211107075400401e007000a1b80300146003103911481075005d00220380c4524001060080d2480b070413004c0100800c5401020b80319596503459041d10103a00701030301d00c040c0450b59984200e40c03401100081000005801850402c680e0300c00c072200c161201054181903940300c1c141240c480740c0c0441858010400100c189a0212040400140d406201d2001e08025401401080c24210714002003901342e200d403c1000740801440c0004100606000810301d0704a885808005204c65070358101014541d880d90010308100320705d800421166804104030a95041010b100030851464400e50103102c2c02800070b00c20100100154105100c82000a0448003c6d84608410b03840e00311400c11038018680110103c001d480b4648104c402c035401080c9160035481d40d84001c500e40160248219a80078005908440390b64081c0700e03180c002086d240309980a40403200081110519103038441c03914a0090341140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 827596735 1250 827595485 827595487
    0x19030b0114120a02130911040507080a20090f15030a02090a05220b01140f0a11030f0409090804090f09050d0315210c08030d060b090108040303110912060615 69
    0x140c441c0c5c2807603180803121801c006142d5007582024001c204c1e88090040d40280340500700280150080a901d0103030000d6003017001396254040960f41007005c2071184403030745401803003c41c10500d80140303013100e00e03a00900320095031611b86140036001c0d04141d500f01c034001c1d008030303144da05400c0007064400123000c12600214520071118114251002d0143e1449546448018520841e40141700c6801206420380d445595040a4803007800785403c0ba00c440c00000b0080762052120503030010a8465410350403844030300c2d00f8a8511040002c000e050011154281c0900000a802d241c1d8803e44020945992000c035810030b82c1d2401c1420440902c4c0d2a90916150813440d0422003800ca0f9810140c442c910325280c08000c50001d540d000c005c0b2040020701403013000c00045814000440640521b400301a0240403054481140c4012409009203040c001545000041d020030320a4001304800c0211032055441c2c10400b8006c18002040b078020a030060f4401c07800e01000d03080000142508101d148034403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 827597985 1250 827596735 827596753
    0x402010f0c02060702040504020f06040803030a0606090305030a030c0909020307111501060914030f0a150510030330021305180108030702130b0618091602060619030b011412 76
    0x3043e42c0100385002e809159240006030031034036902100d09072030800601407511a07590300c00381c81e03603948200c5140322a9800d20740300013040d50050b84604240c4ea4014061410300c45082801c4005151030ba082c101000280780001900048510056000710450f0345d800211410b144c00b01c034174000012420542041c580350041021340e6100c507d142c01d8605940070061180c00000c0081d1406410030b26000d414003c801310201000041c1c81e51440180e4802414002d40d588c6040d00c801790003c510028000c580000e00107100e4100070302204148030040b00c2d5804904409550f0403080740c00412500c030907036003506014852482c2c9940f00c210788807504e0408002c42d6041900e09500c170300400000074020318000140424044243e0408405014041c00b85529450201e80c21440459903111712809040c41402040c4041c100260b00c00031041a0340040c03542d5100e013010300c80000c44000406015102c4100084001500038152500a10007050268034805501e0308025440802c001c1340f103010782c0301ca40c076 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 827599235 1250 827597985 827597989
    0xc03121707020c03101a030607030506100c030e010302210c0d1d120a09090e032502010c030e0d0f150b1c08090103060503012d0e07050603060d0b09060402010f0c02 72
    0x1442e6500445e401c40810441c01410601201c5008054900da15000c2c24081000c0142d259200f544900c0c0304840c1c4036201c42a03484290340d4142c8003d40500000e40b0f007500d2100a5009400400440021588400c9038480d00244c80c0031078507094a80c0700c040343d00042d000d0198045801001c0b40d154014103a20501600031074030300e9441c21344142d040307013000c402b00b0404249405880200300611520000b4041d03190701017400b985940c404a1420202c0c025032540014407540400b2480344240e040e1514400c0f02c849072420755905481c0001640d0000b0108000c02c0020554846408800d00c9901040190802511030345c0640720260401030180540702001c0d000d0140c00740c031081240b50050203c59450b080000100d002d80340710307001036800d0340c20304c880d2582c2c1108545a48640d4450800e1041312580d94401100c19a000c00c3c0032102180d01009091102c0d1030403800464000070000c09108001500390394002d020102103c60902603080b4000300015541c0004e0424111055813428103c98010780d40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 827600485 1250 827599235 827599243
    0x906050a1e0f1103010803040f0608150d1e0317070206061f12021903061a04090f0f141503030f121503030f07031106040f0f0c03121707020c03 63
    0x20401c034095225a07041a0981a5502080149010220055903580c4910039541d495100e40b2401505404c00c07030f00012840c6c820034005010307442d141d03a06500c00188000700501c081500c4c070140e800100d41d9046485a400061000c0c00175442512004101114002a200d450790010003080c01d540100e0100900741d0703280d01e0900d051080d0614800007402c4440d0048801c0c80300c0e00c0b40d0b41280c0c1e05c000784241c20440c00800003181c04071160f4090221681701c620a12060849400d601100c1005003c20300c00b010702034210803920701405100064103070685003800706680f0301041c903020740350300201881207a501d8503120010424080d00254175003010845420300351b22a000310710714424151404102503000510b4003d40b8072400a0440f6100c1c444056000c07150750000004901145140c08508041900401e00600c02c5802048109150701c0e1038949190511019000300c903140c481d0000400001c0c0c841c1101c0340d080c01c403541d030032003a1020b40280711a40c24010f0041c00540d4000502409141e400103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 827601735 1250 827600485 827600531
    0x50909030703080907050a0f090c0e0f06070f210f111c021504050606010e0a0834080102180f09041b030c1806150219020d0203100906050a 61
    0x103d082141c41c0da032458030030b050a0098114a42c012030101001844102d4052030100707079940200b040048144911040e0b0f010703030502c814103400c103002501c0e11029141c01805002460301419003404c280d02c103035448511801302c0c2c00c0c50085a110705009007403660352000790540301d0009800d0170441c5002000049a440005121b43e80301c10a40b490402c8100d4824000d08800001001d51040c950074645881c0b516444100d60030350004680380d5076015240b81800403003084400700c0d0b002c0e103c0b000304409207182004072480880d00d10303c1740c0314100c1d00c007101c480d0310000205081c2d000141c403000440411400701d0349070304138a44100200820768050b90340e54222a50410350101e66240119a90a140101c510540e400a08a0f2921a4000940980b21780429503080901c1008000140e294480d030109007407241c020300c005034414030509440001108000d00841c0c0028000f588403403565000902e0100300020414400b6142c1c0035180800c5424001c0b560003c0200e8010700c0b507600f075100907900c0c0103840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 827602985 1250 827601735 827601737
    0x9030f0301150c120215100e220c120204230708060102010b040c0309050c030a051c0201020d06062303070c0b0a0b04060314060912031501030608071e050909030703 72
    0x14114658050b0206022844c2d1100080d0003010503000065120039060b01c050755450300c40400280e0368480d80d1886820365040a40010321925003811011007c024008040340040e50b00c591007000c03501c0380f0326070401004800c00b08402581c0502c140001e981c1e40ca1038004841ca0800300009270003400344c0f001a801040703440d04171079560b12440100c1c05028040e00c804d400c90320306542608000d0340741d0041229a40078400b120003078a1900b090698540304600c010300290030a09148a000600e074041d88003d07034081c4005424584014542002c9901d141c1c0001d02080308022280d00b8005820501d050070500a42a0b07411032420b40c00290640c4c1011000030070503000d400c00111100d4459001c0f03d903540b40500200300d4141c8919010301c9820709d168980c842d500c18400060300400e00003500d91815200031340d995007140c45174540344141c203400d103404906064035508040381c0040200012030003030094003041605065118404015005541c2000d801030000c0d00400216600c000203e401c01c81d41 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 827604235 1250 827602985 827603009
    0x1e0b091207240b1309030201270b04080d2c011a1c05010c020606130b15032e050109080303010f0b1c110d05010e04030816120207050a0b09030f0301 65
    0x8000340400081259003d4564410f41c503000741000e5108940c08056a103219030000c00c9006411a4171a82249800c0d210301e002c00084010740d400200d91401440e0410b108081070f90804040081160946141d9040380c0c07541c9602c612034410b224842c41088502c20103c4008000312841d200c1e144080418036060300e40a115041d020740300c51500d020380c6401039a004802004040c00560300252201d20581e40240329551426402074600941d201d840150000201116000034181c40794000f90780005114404622000d800601c800403200d28240e03660041c1120100c1803420103001401540e9103810501c16644103000602600314003442c06025200b10389005502c510080071940b4030094200720940c06141028502800c4038130f0340340545110101c1c24402d00140c0e0321080d110415103411500580002c02000224101c1c0c82ea0881c5c2002c00f80f00d501c0c05948688240030300340d040ea40b044800f22a0369000ca4009014045103291654102ca440005140b404203441c0600707045000602030030080b441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 827605485 1250 827604235 827604293
    0x604030804020f2e1b080301050f0a0e011208071b051003020406080604270803060f040b0904150f060605032e060e0612011d0109060614071e0b091207 66
    0x5c0151a00f0562050500110642d414540391501c0701ea042031040c04c2c081d4201040020340c80c60880d00a50a8840303100c03405c02c03141c1c41c2c8180d04000140107202035504010410000004c510b103261002500b00e209156041402e1800e0180628485880d000c5020584140024001580d00c03800940d003082c011140461111840a68004000154034295a01381910844181000740c1e030406540b103880100c502000344081c0c0000e020036207142c020310740d42c801039410004000034048101e000700c9540000000501010420340c0004a50b0250481400b054010040009101050724403120000c01c1d001e80c00d00c84071a003070150b00c0c2000b1a00512092141e803000055940d10707048141c8611840c03800c4001c00c1545e561040079030000f004205162208520000858034450354040d450840341155500e1141c40000d2103a0b20f41e58010000480f0106000304448442405410402285500039407414a0509210b1507503444d21100540b00c1c01514000e00509001c1100203003078100340d0380c51103443c4034251 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 827606735 1250 827605485 827605487
    0xb090610140a0504140a0c020c130203040323070615080d0507030c1b05030c03010b03030f0c100606030c120b010504120809040c0302180d0f0f030c050604030804020f2e 74
    0x7202c98002640041c0780000c0703103504c5d20707481105500031000d02008010f800c0104e40100d8484144a101c04e400200740c000201d041c1c08550b00441c0e00038080e10b000421000a1390888a120704842c2c60b81e040c0070004160700060000d640b0030001c040580c42840248585031560254440f84101000340a206000c948002414000e0580c81c0c0e1080e48030655031940b155030441024086558007840b03011740b2950300c29525a040c1442100b4910000900450034401c49600400095001c80b04214240c01402c00044000354a4040d1001500036518003081c0c080401710001c0a0100b81d50051103400d013400a00b013013a981210448050350942100c0040308002c6082011a9202d032100e81c5400901c0e2100940210b513042e800340200b0b422007d03042d0b0712800d0400800c460414442006015807001071203100004480b082000d08261090400b40b04840980d100c060820038120303401e03000f15040704100401c61422000480600d48110b4480c80c0d81c80410600c000700c21985001e00d00101c134000074034044a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 827607985 1250 827606735 827606749
    0x90109090f0c09061701020705060f10090905012412120c02030a050604120e010801090e150403170c07031e0e0d050304091a031207060b090a090b09061014 68
    0x10740001c0d02c0080e883d41c2e4080d802c000c041c244504034101c039916903111031484040c006c940f5510342002c0100040e0702d84010000c030040025002270080368514000068691041c014400074a000364000100d0b20001124000c540c072407604100890403d040003484100301002c81d4215094010740345e407800f00c2280c3ea041d5008075a040c00654140f02c0c50300e85004201001498900c502d1060074844100f0500718020766481c503048100034046071407400140214210b44d444014490070440032550020030f011007054910900ba20b0540c00100340c200340d41d081e590740c1064a40c11030b0001c000d0358580092510010b201001a603141140c84038050316010550b44600319880300c00c0002041250012014500350780c1d03c0e845441149900c90520303c2482d03180324818121a40c4542c0074018040182440314040d2540d03101400c00c0b01c034603035a04c8d1038420079154080381078480c050f43c01001a004106003400102130b04010b00c0301621b5407080042100044960614000300d981d2008003403100f241200000d245 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 827609235 1250 827607985 827608013
    0x727051e07030b31240e090106170d0f050a0f2007270606080403082a0702030115141002011b03020405010912020307180e0f0601080d050909010909 65
    0x300c4071140310031900704c8410588100964680410401c1804030000307034800f80c17603641441c0318200201d0400800800e50710381388040d8010609070000030781c503858841d1840000d0291a1280d560340c0800c0140304d8003604440304060036409030070041d0620900c03160040c0404000e84400040001c080034400c54038080307030300400000d41070405035600540c59440030f1041811800d0100e040b0600d2004c1134165200e6881100306440b080d070366001c51036481e92015505004080e10402d507542d80e07040c1c40501d000c0f103c1e018078a01070364591410758520a9004150075201c400041328403014005500300105054400040d9048809807038941d218802002c050340100310000000503c10360070301181001541c035900070006d44030240c81d500ca82c01d0304e54900032640940203c00a40550044000b404410131401d052910b8010150000c44c042c02214646410100c000c841d0003003c0c2d100c1001032183c16414025a0890b503600d16084d1705100309480003541114061040259203940d039403080c000d00030380341030241c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 827610485 1250 827609235 827609269
    0x1233150d0312110d0605060301030b04021504080111090a0b0c0a02010e040204081009021503090d121e06060806031b041a0a03080309011b020a03030b030727051e07030b 74
    0xb0100070910b0740d400300f940c884502501c4651801402281c6403804800780d90607a03421641c03000c4150ba840e424403002e6600e1440d8440509c1091000144820b405d01840b54940719210083e03448030045010f002c0c00c1e82058100351210701007400b503041111400640c0d20080c540910740449014401c6011030000e200e50b402026031401900d04050b51015560452148039200303886030302880f0398050a8620901040c0c1e158403050700b00c260507100301841442d00301c4280a480c0700000720b50381c525030401c002082103d08035903c1d070344883d41006006e82042002d0342c4500141c029181e09100791a00c086050241e00a141c0308035038070300740c05130100c1c82c3c1d81042035500400340c003d207000360301c81c14000c0d82c6070070840e58440c81c1c0d130074086c88450b001d115042d428020b00705030700241002451941c0503070241003144030440c1c140c070981c0c000091a00600851a1030f12038019140b614029421b000b403070960314003c00040e29510403080c0320407162b1016605546c444150b25000030211601c4001440e0343c214410551 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 827611735 1250 827610485 827610491
    0x10302040f1e0e070804060515090109050f09010507090506070614010303021f060b030a0504020103091e1106070c0b0a0903022706090402031009021233150d0312 71
    0xc55611619002400b080480300d505200141d568814551803200458441000404840c00700e0300085075904813603080b48014150010480d8210045030041c44240c0c4110950f40c0c803202807000258520844036004000c1c00000d006070b1900c1c4070043c2c0002200c1c412a030003074400180b00403d100d1941d0045422080340714501c14036503524140203580b0b80138540121a03540c514960041ca5030b5441c42030104407403900581d24119a0350203018030080000034004d03030505031a02c80b001d00151500508000007034154042040ca00c02500380b01c07100ca880700c04402e016820401c900e001003001e80b803500c0106c800401c40d8030364800c050b1008070f45a0050358030094011444c1090800d039a601c003039800084807408000c03422070f81c0e10001000f5000d0410398000e501754001c0d950002c4e114020b1342203442041c0c000f4001442c84240c0719011071034081d010940200d50443c3c0007034210460018100c20b0b00814200c60300402500b0310640d004010301d142e20f034072072044201805500415005908848050b0a240010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 827612985 1250 827611735 827611739
    0x61a1c060b150c070815010b07060915021b0129010212070b0711010227010e0a1508070f080a0915020706050106030f060b18150304050f160501020d0c02010302040f 72
    0x1511960010621001035003d04036010420f174200240c50842c0802100e030000c6640d1030404600040d40c484070003030710320649644447e00810100c05103c204101d0411005a0b500c00d0b148100140c0307081402018910790502004007401000201385883e0034a01080d00801201280d0041c3d10f0003040c03140b0100c5051011501c20180085071984500c10441d60311102e84d000b405070145401c0384540c50354205e00700801581d42c4a2030300700e040585402036044c10104040f0303083c0c0c0c0028480200e81c3c2e0100e103410224040c0308429a620246054102010b0309107140507011522000c0c248020003007aa102e0b1340c3d1340f94410410711401d200140041c012480e002c55580030a403c00901070b1009018030800309003803130070000140c004d5200303002c12510110242400c00300a211b407411400d140b00003041c2d0002c0d0440001c11010500d00003540664844c000803c0f21340c50050100b4184060f2400d0201d40724a820010032241e40c0101d00e030f0400c40d1461600d0381d640f40c0c00d8401680280901d412100c442d110613440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 827614235 1250 827612985 827613019
    0x231206030c2d220c12060f03110406180f060506030a05090105090601120305030603010906020a21060e0a020a0201110313030905040903021e0304031a04061a1c060b 72
    0x101d1040d0948940414000720450400d0000c0600340381021420f07001c500d8000811140160b00c60180310415103072003600c42800101102c04d482d6190041e6441c2a80c40302c0400400101c010441c440e0082500d05120311441d00b880e00641400d103103040722901d80c803403079000c0c030304511580010301400000700a2500c070309000c1060300061400316184c232003d620740804902c3c1c1c1080007800c58103c4070301c00750606031010141d40448058101810b8942c142d9200c482080009007170703001414040320785030b0315405070045e00c0d181c0310010318806840c44812440d00c03a0a10850008258072b6902500b4018050380e1242d8403a4100d00411101c044040d14490100900c032007440d1044c0c80c07412081c001c1d17894021240e21602048101e40c2003040050242c1d010164a481c0c4c0c6160040902a843c07403070b4180c3c0c1c10541c0d47e0f22480715600d1030440000882c1150820002007104511414441e020300300c1c0040c015102c0320021070040340d07010306c2c000d0849887c4003038401042881c2d04440d642082c0a010030507030141c4c142c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 827615485 1250 827614235 827614279
    0x1416210212010e06101d0108031c0905030c03190503090706110a0b09031306050c0a0b10080604060b0907020109150b0f030129030d0e060a120c0207030201231206030c 73
    0x91901985400c0e00c00c580c11b80310745400e0505a40054000c1c600d4100d41a0410811031022554500f0280d203800e802d41c082401400940384580f0543d0245a0700c80a00801a03101c4c4002e807a032209109091007404101140055040240c4169080c00b510309482d170451140380a0040328014910415071080009124000c0041c00c18040f20341003100065458031025140e81c0200802e079102039010030a0f260105404c410700c0c1d50405d03510013541d0402e0f41c8900074982060402c41d400c2e82c042e51503a013403041e24100400003075403044031440200038512040c2e8400c1c00d2090380c105034000c4540c8a407003240d45942e8241d0300004402d8014020842056407014000f440c1d80e68441c075a10303102c6102d221090f40d090208040c4003d601a0382c44001101c11b1404215540d0000e081d40000c1001d010a6007011844900c20900c65280c15002059010300d0b42c03000526075601c0803180e128030b680d142100000c40301004141c8402c000421316802c1566942070100e403624030b0034007100d83d1003403080c6a403842c8000254 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 827616735 1250 827615485 827615489
    0x170304030e0301111e030417070804030b010506090d150b06210606070b0a0c0e0406030b09070b040602070603090218040c17010c0f1b1416210212010e0610 68
    0x1c1c2c02400150741c10340398044c460003503008299104084015214624031608002c5074014807038009503202c89102003940016401c080c07400c407450303000060184288203040c60071500419044941c1072405d0348020110340c0701c0785402c0c0c000340785032540081342050620a030404074140c0d00141c030290b01c450403001203020514400e4800c8003090040310100c0d80d141460400c1b0f98200d50010a01c038990f450f6402080000d02c01c071a01130301007218201044a040e60b6500906008600031039900e10a400c0a0440c0c60405019610000102c0000c01c0100a03068010030300c001160348038280042c4010042c00825002002d5071000d02205020f041003104108006100d4800d075800f5220f56031240380740c05030050880c1e407110b40100200c1d0081312440700f11031240d03080391054150140b0100345152140d4584144100d00110418581c0000314a90f941000d64200030f8018140b50049078220a95403102103200398040304068004d62a100076110801000d401020340941c40500b101c0480c9009400040c001c0098 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 827617985 1250 827616735 827616739
    0x7030203031603200a020904051504060903110604020a05010c0c0b032502010605131e0f0501090c08160f0c1202030403020a06050306150c07050d05010f0c020d08010b07170304030e 79
    0x803401ca400c8440c620b5000c00301c00c04084e00030300c04881903800700014118000c1c411200b902c204142c00d402c0c0b00b8643c44a501491180c0000316100d0b50301d00d0080c004108407100ca5025230301400801025a0720102000c040729402e083c080881c440c58201301c8001e05054004484100002061156403440300500422021a880385c940e030040f40b80008030b00ba00c42c64810a070b4031225001607158007514a81c0400f00d80c00420720366008500c1402e080c0d0b02540c14000b45200250f83e503800401002525004103c10100f1a19050322036160110085000007103c03e455000c00083c40f031030f141c1460282940d03088030f5400c050702c4407240b190031000a6695000340002c074007604c4507a000080b003a0282c1c060381e0241d10001e00c030321a030784409181090355410410500348188a003140008480d19854484440c0ca130180700003080740c04c0e206000c4025112210700c208110340c8500703890b4006a5212030024190341040d00d8680d600c45032820404019080f40c4ce000c4210740f000801d01081503000083c04036101b200b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 827619235 1250 827617985 827617997
    0x1215030105090a08030a27120f030908121b04080a02030c1f0e0f04063008030c090a030c0e040506090106080c0d0c030501090818102007030203031603 66
    0x290740003142c2c884065001c0142503d5003032010403038001d4141c0084801440c980904521410f4031f15854400e40541da05c02c0e074502c401c180c4541402135000880e004402c016040a001d15466507442e65031f01d20444101805003841040400c01c00c0440040024007164246142074843d516203110780d4507030442a50480c840c0c400c4443e144110301f08004a00303542a181c00d10001012000c1000381ca901e940c1e09a541d034001c1003812815160341d514840e14001e89178200100314402c041c02c40c185241300038107108588c0803e11100300800101400200d941c0301c060140789644821404c2e001c039000720141d4000800719001804041a0514a0008184601e007c1d2088608540304c108102c0d00301d0700d25008840c541d800881030345d000b9060400010800d00e124034070700c9007019583c3d240c0700e08480002808035080036000418031800c0c1100088140d140000b01d54a03503050a40f03041c060500110810a0b000c00c82d0000d21600c9291780070300c82c280c020b60700502565666a848860100184007100301240810300d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 827620485 1250 827619235 827619241
    0x20901170712030e040c11070605090307081c05070309150809190b07230c0633120a02030f01022d0403031413151710140301021215030105 61
    0x84034031241c0304182c3e010340741e110300481a00f00740400340c21451180028040385403840c21900000700100c60050040b5a00c0742d484442c04020982084800d601c00704440e40945046060840406001220700340b460400d556104240c0c6001e807650300300c139803000c0003806403103c20110250708035100b00e105600000641d10040901342e6000c5261a8441002e000e41c0820b4000543d010300500140b0190808100003102c03c41c0c00c050000041d611907403014845401040600800e0095180381030007001d070418040d9210340751000303034003c000c0311034141c01c0c807440c0907031544080000148005001300f034000d4280c5001c0110742101c103000c1d502040b00c4080c00307800003d030301c401c4404c0d9002c071140c544501407c19207881d25644080792950081c4071511a0000c2c104203245540002c0703000c05000f00039102604000dd98500c074040c0c41c409600f1040c6014801f031a00b00702c9181080c00c031076015508841c01920300103024a000c2070090048402001485243c6000c1c00020009104204c06c0250110024013841d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 827621735 1250 827620485 827620499
    0x9150c06160c0b0f150a080c0a0f060e1c02060c1605060c0a02060901090e070206160509010c0f060e1b03010e031c050403021204060f230d05130209011707 68
    0x7240048003d841d050311680480c1d012213000b9200ca404c41400000081c4445480f4002010146d6652042065610410601009003004900800103144440300140424600900a031001006000702403250030354103031980f0381d42d12001c0c407412504d402424241d110301440d0000c1e07544204003603c586840c0103540d40040d0502c0c0c104221040940c00c43c024004001741c80d4203200c89a0010352510b0306110b0b100d00d0108001e030014118500c0391420343d000700f040307003010754604800031000c65800c4200f0100b08112801641c00900358010f5552000c0c800440e1380702802d0202c0103201c9914003070164010091101c0d02900c0a090420000300228020010615054155580e902c503a20710b0024204a4080c06510b00307a4035808075030b0050007801515180300c0e508404041a50090304150b01007403032107200314402da9101a40501805041e030500c40031001004152420303006e07101550b10703003d49910000349070200b1140c1d4000c4081d4041e10076030301541c50b8490398048051180500c6510300c01d05000003290 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 827622985 1250 827621735 827621747
    0x126070609090908040b0307050706180b0705090102071701150905090a02090a1103040b1501090b0f0a031401030809030f0601060c12030912030507230f09150c0616 72
    0x6800c40e44902400a260030090000f502c804442511280414040068000000310065101d003185644180c2c0d25183c6d403400320111458401008445544508000001031840c02c2c450f82050103400c103142c80d011000300403031800103075401170400700200d0700e41941c0c401d4054201b229050701641e400d009017500e508000b01156030454000c001948001c1c091000b60a00119858000e8002c9001143c21550b5103064034259109407002c40302c4440400400602c43c0819000d640403440900c0c1c9900a50302d46250180a40074101000c40f211f040020183c00700c0c0d000e90306c07a040783c240702c10b020b039400e40e0b40c1d08140c030032504007044446c060302415202621708800458914160383c055114000c285109484e1000e01c0d14a0304056030070b060780e0754424000b0903550700b810402c10301c06507400310709407174005801031031504000f4403085d0005950007030b01c407505112015503011218140c02e01d8ac588070400c1c009055194400c08007901410001404811b004000c00d10b24172400c1c000c00c00e000c03103d1030355100301c3d18 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 827624235 1250 827622985 827622989
    0x40213090b120f12030408041508061503040c140a05030a080306010207061e0c02010302090315061f0e040509120a02030a0824010e150c070906052b030215012607 71
    0x180d5084a10704d00f520030082d101942e0080d00400c200c60425032152404103e01003540081c40100380d20304e042042500c2c00038106c403c030a85c0c800050b82941410350b190143c0c0c10f4a401914202c05051903603211545458000034002e21004040f1070301c109280c144040241e00590710b486c01030281c0b541c00b140c1d0780e0117844c1c490a0740d680001c50003d0032584201c111030159508400700d0405408100400c030664080140d005c1c0c8400301d1004520328140340041121a49880c4400040e0410b01641802c0d41030f0021111100fa000c1503401040c540e032140b10050a00d01d420301100c00c00032000c1205a101e42e40003000d420500000e46494289403120782a00800204040c95450308080418000b4829403082e234440050b8000a450f2808070381c002c01d4200c4840c3c001d80c4000d4090303800f401040000420f82c0c01200000c00e41900e9017106200829103410075134900c90015104242510140700c1010f208020366451400580500c2c881543c507180702d01140411741039030800e1060340d444410840c444c0440c070390342 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 827625485 1250 827624235 827624263
    0x4020909010b030402040f0f020d20040e09030d09030f02011a130911031b0406120201091203111c1e021c0c1506180b09010302040209040213090b12 65
    0x64030741e18000d410300303042d40018003c030b802c943c03501e407600c041d2a035500814102e201451005601c408200c0041d40c12504044480c02c01e100d048000e0392100c840d030008803003d560080641205541d190f070503061451080300750110900d031500315144c0c24142e00084542c000840d5a0080c0450680c00c212401c01c101e82200099202a002c205484407807501c0e803109a9091040f5100064413954100003403d092280609d646440c00400d010042c0385411301c80c1c100603000050b0106184015074000901c001c509001c1d5410052244000d20103041c040c00032140c490b1400b90881e02c1788001c90307034110341d0382a42c503c18401060400c070140142d40241c84499400d04c0c5254020100d07919030030503070f0310406001b9a40c003082c0161000034802003100c082955400a0350f8100100742d0b18901507040c103556660b100d80c0d400103450084007034001d82d01c8800881c1102d0701101e001d44c4070721894001400a03c1030074070f503071441511079600203520f1440c1c0e000340b9122101190202c09039019441100e41312002c0007c140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 827626735 1250 827625485 827625499
    0xf04031e110402092e111c03180b10050406080a12121e0207050c0a030c030305090a1806080d050a0806210604060f1506051206131a0f040209 62
    0x260740c80c1456400780c80340d1080145242151540c45842c1c249080300c1c0d0342c03034555035415084207410b002d42010000d200c0c4054880280b0800310b403981042c1c68589400c810800300741d140d01c45252142907030f580c00700c401d0f5044a0b0b0b212803800d208540b5404540c040c400c250180b41001400200b07800c0118070070f02402d801444811001100a01c125084003c0f101c000d01050740d41c98141030708902e084680800e0324441e200c01a5600201d0400e03600e4194203107a0a446440306d203909000040004103150203c940c5400c2403521a000540004c1c00ca00e09604488800580e01d5003034454100140c102000b22107102065821064424808444502c580c01d5604003084804011601c0f030b040805c40c402d221110203527001b000d00010b0311802d08090041c0c4090303a403e0b403540700d1242541024411408940c103100130208100b0f10300301c0040d0003130184d080e10803503490828000030b8250304d039074243e4031804808070350030001e0702803048921140340002049140030700715400f290800350600d1310807117031000e000078580 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 827627985 1250 827626735 827626763
    0x120f0909180228030501020706060f0f180b1c0b060102190b06030a06020f0301140307030210110708100f111623150f091606050c120f04031e 62
    0x102c41e20b408810700340c080425180414611443d60300c020307880a180301c1d80000d40d40c6e000e181007180596806820030035604c251810200030303000c0e00e10a954100c510b031001e170480400620484e14020a0071241281c1c001c1e43c6c44000ca00c500101158102003e407041d203c548064881d580126603070308808400c01c43c4841c3e5013094002058005140c154015802012290448400c1c2c2d20070341039810030643c842000f0740100046c03003085112030705000c104500707400030041c1c00d18680002e80b46001100b200c2c0280040c40d01e014903d55070030b1100300064001c4504480c040000300040b000200481c0c105c814145150280110203c030b0000c0865161a80c0082ca901060650351100401304280922600d424502201d98510003c020300025510f4580b0b6421210f8900c2e216032840d06034034004041640580150609190340160340c1030030301c15190b851620340d440f1801401d150b450103142080d078428801004c10107001d08050f01004206591041d2203000122650b0038001141c06007071003005280c01120b40701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 827629235 1250 827627985 827627989
    0x1719150903090810110a0e0a08010603211d060a0c0f240209100302130f0f0617060d0b0612070e0106032007030c0317071218030801030210030207120f09091802 70
    0x1181038407d0024050085940c8d01c0900908544559004079992101c03040c1002c0240380180c01c0080b004924102030620888aa08a02c21505511507452003204c01144654005200f907080c01d01480d404681e03115201c2203401c1c0144c5083d10b000c00a031104405052030f03607801e03440d0300a461203040040c10314000310400da4810340c080e401420f005064038000c4040041d14107001c020358001408441c00742071200c1d0410a00911450f096461000d801071108140101c2d911aa1201800745400184851160325010000b6506a110120503103e902c5000c0010500c110305032841d50486106072410400501d102c0000250b850100d10303481614541030000e180401d00031903400f1096031003441e182c0c1c82c1040b148400059040d0644204002505039150350b0301190003485505d0311480144036109203d141581e00412021050000070b00408142d1440c44166010b6015a072456600c0710b03810b8010108038000a228040b404410070000c2d541d0b010002d000e000e24450601800c00042817800c0651507074007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 827630485 1250 827629235 827629247
    0xf0a0c05030a022b06050a1a090f0f03010e03040e0f01080706050d06270b01111020070f290711070b0d0f061719150903090810110a 58
    0x201396a48034001c0c6540c140c40000c0c00d28490040d602c0754400203100f4141000e22a03001c0154001900d020107001d080d00803802d070b80c4281c0e0f01001c0116000401183c034000400d29040301117140c2601503080a15460f40b02c20040054820783d1000c003440600d654950242d80e8082d20284031340a03041d08100c4043c44102e2003000100300201e01c411000ca4503541d143c0c801c2c50000c40324501103400d202c103080c0881c950903041c003031080408401d11308a80302d5410181d1480e290107681c603c0c01c1107546d07511103000101c5104841009140c0622800d1a2a14214101840c221041d1041181c03400400c030b00c0c2c10701540b10790030b4849014007200381d941c41319600d200007520302c034500743c9102c813941c85000c50025012064a00034040840e440744041407124840c0602801d40e6100d8000e000c0e015204186e251300920006081c40d501e03810480044100300290828000301c0005e6403101801d90f0510b0f000009043d004104030040359003050440d50b0090301220980110760003590180303403000e030070400718403003501c210 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 827631735 1250 827630485 827630497
    0x10f020a05120411030a0b09010509160b0c0c06040305030903150c0304061805100b010306080f0c09061c062a0e060a020321040203010b0307030b060d15050f0f0a0c05030a02 76
    0x41d10f49442e03414813000607260040c240e104903000b41322081040805402801507913001441180200b0f0400040c400101d1200308034095502c4640c0d0104a043c486803080090009103000175080c00e55031600d03418141e440b50700c0451114000d02c5022129002c000700007160030303c40c40003000e80780d0441e2242d55640740582840e4401482c0c2d2001941c0744d0340480c2e4140040016105440c9001075210380728400501500c05da5440840c0700d421007a0b03201800b4030701003181020302030212050a12582c9003400140c48507912920b10b80c01c076540d40649002c200c102d81c05490038040c40c1a044c4840c00d840d001d2104500c400c2600d5030009280301c00c0185580c1040000b41030950741a0050b20301702400e031003100c01c240640210150903210003030280800e43c20203129a134618001038000d415140d0941e1610100c3d107101905544c0159042c80c0c00c1c0050100d03145209841104103078080c40541400b0785058105070042d140d5420068141e408184c0c030b04914402c06100030416124203085d60755070307514100250040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 827632985 1250 827631735 827631743
    0xf03150b1f0f08090a0b1602011b0309030e4c1d0a0b031b0d111c0209010f03090f05060f2a0702040e07090518010f020a051204 56
    0x41c4a48a0308400c50303a21090340c00116954189801000c00e801040c034400a4500030070358214018100c041042c505116a110b11100a100d20700340881c841280108082400c542d22200c842d13504144a40d4550000d908481c002e0360703003003540e000b04c03420400c050304101c0140146522070b4800300c0c20b20185d81840e0003114264405001c581440c4e00071680314050f51003c1000080700c0080e50310340c1e454088480c0441d14016210703040e40900b00650005544000741c0b00144400700c0d0074004481401c0c40d811501c2d01d00d01d40d04280940142d4110650440c5c00101c1d032a0030000d100e40224503010f80a10030f03940703c081c059407203602c40c40e03080d0002d80c020a1100c0040d0350030010162540f0104108001c0c090095141c100681454070308051603400440c01a854007482d62210014000740342e2140050f200d07401d40441c1c0008484011800c00340c40e14001d1341c04001c5c01820f181c00c11500c0960a00c0f200000c00c821802400001c01292050b4200d22078420020b000c14014425180a0024500140c1e0b100d1701c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 827634235 1250 827632985 827632999
    0x60121051015081203062103130e0601020d0f0801060309032304060f0504050d020111031c0606091d0c03060312030a02070201170403020a080a02191a010f03150b 71
    0x2500500c58251840441e401841e0350000c0803c102003d001c02c00d0392151304070131030b1807404c5060200005400c030703800c2c622205407511205454a1645003d104135024030031500b02c0708921507038901561801c890100c078420b0160080c00c0b0608829409000c2c0d021003080c2c07aa4a030b4509a0030031005800038440c520090b0104280c4940c1c3d0080340b0034006445803447c20b00020395032150310f0441e00500034030304c0c1c0012504005050104002c10b8880380b050b580e0702075090810681d441e825143c154a140a4014103146c1603c4038129031610903c158000000c0d580d0a58904504940351060300c8203140c4a0341c910034900f03000e140014403424690001c0c1d500f260b801001c0c0ca207009140882400a50425a10007111542c001545411903820500c1d003128130403000f2042000e854192801b0b51103504004002e4840c02e0009290200315100740600f8407400354100c001050301d10395003005d410212501d80b0b2207103488808000424451141071030001103a91001418050100c603000321405030039503940907900026 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 827635485 1250 827634235 827634253
    0x1f050c03070c09020c0601063e0a0f020a05030102041d09030702030307030203120a060b0703030c021c020f01050a02030610030f02040510080f0f060303070b1b0c100c0206012105 78
    0xa0403030b10300000384026900580c80758043e0540e1410000184d100d4018042e2484800c03c40d200744c6401d441a5040c418800494440603211400910014426030030b42401070a201c0c108004503030701c0c2c1c115a1b5000769214a6280d80b40e400341401c034411400740c0096980c02850f203408002d00c1801190384090b0f898182ca04007240d55000c82d180d5080b03140d0803000b6030004100c0c01b903140c402c0b55000703070700503000d00d8240300e02460f0140d0407405100d0303200d010b0101030300c0300d210542281c020800d600c203204bc0c503900da110b8207000d44402512000c4091a810302542004041206c00409000380d9020380d0004002c140048451038042e00201225005400425001c0c0000a6240c4e00c00080c05040607060320341217030520705414070000550740140603002030ac144106100060302e000041d90701407548071000821030f40f82c440e40032482c42c18030800d0411144000030455403510010800300411104e11f0300c00e02c0301200c030200a0303072925030034003d420307032405d0965203040c00707007080146502c0c1c03540110240c40c0440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 827636735 1250 827635485 827635493
    0x21203040302090c220506031501180b09031c1407050709180510090c1404140112050708010c02060a020d0b030610050a0501020c150c2a010e1f050c0307 67
    0x14402c4904c1c42d25104080344405104441901d41c2c00c00010000644d0304140c00c1c4800115a40000340901221883c80d0340b014000c0d90107628156a40c071080c00c00d4280d000d03515120f1001c90760200503007602034064410304080c503103c00955003030f0010701502e81c00145400c0a00409481c1c10404085e034080c8102100010150359622801a0141404221142000c3c80f401c250b171801404824035045107240500060102c2c0008441c6800d8540d041d8040c20003800940004015000440214035066101e8000045054080010035261803103402514141c583e584440c6007200c4401d010700b8056000710300001c400040e03681c000c01312408409000106401c00e040032a01e8120201c03061014106450710621440c03810102410050070300740700a0418455030004284204c15145001200c10000b060102400c0c605022132811010b400054540841100e40f61281308041e040c003c0f40401c05010340c403a0035003403101d20213000d840c8180405a1804020303100301c829a001041d900d01c1c90105010603c006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 827637985 1250 827636735 827636749
    0x30b13020307031a030a03091401052b0e030a08040b04080409150501090902040b0d0c090509040b040204051303052d04120506060a05030a080c07030606090510050f030a021203040302 80
    0x800c02e41c2d400003400d0804031081d09034042400c0e1000c1c8a1b40c4189007280000b94082481e01c1520381403114203210000c2400160342600529000c2c6440d01916136003110040f503d850f0000051601020074030504c0b001445a40e102c1c030501441e54001442c2d82c00040200340c140120359000341c03081901520b0315503210100700807101e048083c0c40c40424002420040c941e03111100e0006055040011450705103001d03848850b900c0b80ca40d44d041a2a104c00f050410140101d54010041c40080c05030103042c41d0030701d0900d02c00348084408038411803420020503404800000c480202507030549403945040c034059914540140c040c03d140f55101d450700b0003418884501e9000d88010075040501d16180a01494090700f4044018010340c0600312992040082c1c0d42c0002c1c2480445420815269480c109208183d041c000c0b540c002a241d5400d100c3c00188110481e400548109007d103441070403542c4800c1003100c540c14100010364150700ca6071981015181031480380e00a8807188080324981030313a9a02103040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 827639235 1250 827637985 827637991
    0x606040e0705070c0f0b49020705061f0806060a0302012d021e0c0307030215040503190b07020c01050f0a0c02100207060801080a080a08061201090c05040b01051306030b130203 77
    0x29084021404585283c11400001e502201c90003084c04143c0ba10251f10409260701070038a103400c85244640010040641d044903050354114003074501629243e0881d5100f0251465120034001c500d0740d000446550108800b801107a004200d40c000e139282d600111801c102c9007803c600d00c202915004000a801d43e0070301c90032946030343c011300848079884004640d005200c02d41044a030b0059503030041d0564001c103049056070344c122a0361369400402c295108076402075810840c0c15100323482c0075011201d101c00381c519501e40b040c40307000f03183e0380c9001c412600c61040720f0055000c07440900040c064990248080c00e100106032410318000c204980001e0012001c500102d40540c02c00c100900c48903510200640c003600c1c01000421195205a40320082c1c1e104070401c0204021409010959942e941c01b07494919007c0b54009000460190030101c040107454071549105500d0b2080c45007065010358140c621480112440503041407504c2c0c000d0b0040e018403a82030794020080305120010071164805540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 827640485 1250 827639235 827639249
    0x9013b010f0b01120b0a09110c0a0305130b0a0f1409150c01060b07050312041a0a0509060106020723060405130507140f0a1d180603060606040e0705070c0f 68
    0xa070164000c0001d001010204014081a4208605c801a0b0b03100c074072540301150890702001942580031044a43c240c02040d10100e001e024407810402410b0340407014011b41c8141d4002425120703601c1400001c1803003040001004120701300a20200309004105035081524000c01292802d405000001c130380021410559427488000300d1500c0b5506c90901c20300000c0c0c00d80010b0700740b400306185c841170350303900075001075822000701d101c0010104104003610200074003141800d90140e041005420024042c21100d4801d40d02c40e41000103100c91000800b07000700c60340c07600c01c440040182d441c1d041d030310301c41085200d4000307070104030000d81e5481d00707412880c08000c01c43c070005442c101048001c104d546c504041480240c000c1c84820383c4508048200d031000c0040341007805200d0314403003100c6580100ca0750025032102c3c2d640c10814000c283d050005100d10070072002d54a036039481d2403c2000e1801140251041402c0d2040000d000034003c400501640e4003900380e00c151940d40d03011440c3c40d55010f0304241 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 827641735 1250 827640485 827640491
    0x19060f020a1d01110304121109010b0a0f0e0d020402250f0c05100806060307020111160201091a0403080a110703030306090b01031b0509040212070f020609013b010f 72
    0x1040001120300071280d070040918005109a155204d4642d803800356001d400c04010881d081441048103d000359503000b4001f509581441d85d56410700700c2a134010b2940b1302c02040401000740081445103032403226241005264a81e2001d486c1c0a00c4000c0d00009400000e0000e0301c20340c400e00841c0c499000d00818492a0b00d41e071140c0e040d181070449603100d81d103e0390040042c2c134801c000c1e058010140a5001000303039261a120f540300a0224098480024040010780c0b00041020944445076114400eaa000b80c9035100c4a641c3d544000c1c443c2000408048800f050502003840020007000060400c90190b15005e48000301c00200141004943e038421004aa80e420042080b011903014155444009080401c54644050840b44d0005115040d5104100b0001403401642d035a9505852006e01c00e04440391080c42c1c405009421020f5440d5184054860307880061402e040500900500d4215015550031003011b030010100752150918014011911041800b0b400b20701c03d1040305462003860f4404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 827642985 1250 827641735 827641757
    0x11401090608010b03040f05150c0918040206090d020a0e0108030a030e061603050705041e171b21010203190506100504030b0a060305060106021c1119060f020a 70
    0xd0011080d0390320030814400341e02e004100c054040f07010340c1c0d80160400d45520490f1120320300503003410070380c90041d2000e100c1082801108a094009442d0054054801c1280d06083c0800d60380302074004c55001354804020040d203015418052800c48080f80f01401c019076060b02d0b40055456440c090300a018a544040707103621103281d050050101c0031130410301400b52810f1160010002d020000003100515481d60302050b01c9030301c02c2c0102c0c0c0090128000d0b062980b000c09103101d6900007144500020404061551041050041030222444d24020542207203401c00303400348200c00c0341e0300c841c4503541e02c2841500d040440080c0003c5101c0c42009091090984440800e6412503201425240c005e6041140285d401c1e80c100c811542030765041207940700c0036a0740d14030a47c05045181c10007405402001c00009074181c000a04628450790320282021455280300e046031076400c41041000c1c00d0340f00003200b6800c114000b0540e940c0078000e0300041203081c8400c2160050ba0b101c00d038644000b4068000c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 827644235 1250 827642985 827642987
    0xa020606010f0f08061009150519030c0503041b090203041b0f0501050417010b0a06020f0709140610020c040203070e13022d0910030902040b100906030c050c06011401 73
    0x4494000519040540c200300307000350f00600e04034005124501800c012101522a1340c09503034410018041d030a0486a000d00c042e40040140e00020504218085042c01000185000b8050001407210725981c20f82580da586c0c4400451400052080b000031403c070801107030aa4140c0000d5110700d000e140084000410b0080003400c0c038800f0760128880c2c0b40c080805000c1a03900030b04480c00c8078819500049107040310314900d40104803609003180d001e80c44400001e0b03a80d4000c9440d40413076042e84250341d2090350781c40000058440000c62000c40e014954005842c0e498020b02c451610310302841141d01c1e080e96900460101d9000303640620210340c03c8210301c107451400715814801c0ca445504190b051848c010980c2c128000c0d00da1813040c00e0042c1c1101403480200640554010600044c101000307a0208080600100f05001c0180d000c1c0f03050850f02501401c0c00011204c039100f9694a102801d407800004030b00820b0100300d10b404001c030030070403401d100008003d05400707002d2a120303c50620610b000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 827645485 1250 827644235 827644247
    0x10e0115140f090109150c0b0a02040609090c0215010e1021060506031204060e011218081b1002090907170103032d030501090b030a150209040605060a02060601 70
    0x11481003000140d0421001c116854000d0b58460030740e06640a88401540b40107842c2400d06030803e60700071b0420075011040c40d91251102c40c5941c0140300a00350b40d00c500c03030410240d1185d4040c80c0049a501c410401000c60181e0011700e00c01842e10544070114440e1950222525080e03116481d840000400c0c00f1041d12a050b89000400c40d0034424242030400d4070500b26509030710b09c0b000d00391564440009d603140d1018408a03082c01d42d40d001c160f0350b8079190f036406442c103100c04203480c1c0010074443c8001c820050510801e0b4459651102c01d011084250b6200307980e641c80b8204059000900e0717403007800c4480b42000140c450002482c00561640700c10342c00c0c8082610010668410800703218039465043e1b407030100c2c56054a4051500f40520848031041840c840b800346841000c402c010810300d20031590560056042c0c8000007002d00580c20b4400c1090f03030300d0b440303408081d0071450b0310882d031550003025600400d91400b021b400401d10781d0b5100c000070f21540040d40d040000d40c201a04005081d1781c042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 827646735 1250 827645485 827645519
    0xc03100b070302100f09020f090405030903060f04060605010f020604060f0b15090f0402070f1203150806090642102a08030601030f2705070803310e010e01 68
    0x140c07003041b0220b801c0d00010f5030306080c101024000e050120224040c00010b004aaa1002c009001c503100c0b4103098125100e1010200e500359541d52400d000890190b20800d40b0352103008266004191a03281da803100c0c0020900c0d0710341c071006269104802c8050783c8540500c091101d210075241c41c1c0b6000c0300300904c0f40c00c0c0442c1620a01c6140304102400000b040c200c100c00034142c021520921240c20490264005e0285003030362150a500c2d900d001528940005103684507500070415114561104801805c10032054400e03210303100340344c011526500c050380134465172480000a1940c00030801c2d001180c0000c0e2000508400200074000d00e40514013007840a0701d080034621001000d40fa0103071a60011400041c09a038105034445541e66104010754200c0002404d40b1582c030328010300c0c0e00f150184c0c50b080c071800445460080304030000e5100804000d65040b80341900c07000d4031300c482010030350494000e203000c0c26410451144021685014100303805028208031130503042103504000f84000c3c004414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 827647985 1250 827646735 827646761
    0x303110105040c031403090603010b0405031e06070e240306031c0e040902120f01051e01030b04031404030b012702030603070e1504020708070b0702060c030c03100b07030210 76
    0x2030180b00010f444508420220781e0000030b014501c0f17040c41c1e0502d045104100505a01c0740004c8008145800e01e0002813084400c2101260b0002000040d95040d051a602c5840840d0300040c00144030940148401c0761884070040c03da941045514034105a41c5032800c189008403000441084171504003081713a03c406009032803c0c0303890f1101622000b00040c0d2076201050096803115562000c54a940501121340c81c0c42c0000e40d402208000d02882c000d010480b1082d0444241d00c00111900015401d2241a6600034040030131075a01d913282601c45440300340549001400c1001f001001c41e0071100900d001e400703460811a1075412102c3c800000341001c80200c80c010b48100103101c0e65a8000624408079150281c142190f80e8034015003004114409a000d90841d000281d2403080200c000021304000d4484c4c0d503200403940f42e10608030b0780c98004494410340d0000c200040749505070040061580b0080e0701c1d29500071241c8403030007032403d60850103040307001d41d201c901c40041c07182d50360040c1e20481c250 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 827649235 1250 827647985 827647991
    0x309050a0b0304030f0c1a0a1d070e0c07020a031407051e04090602041802091e030d0302030910060b070605091623060f0c101b0305130507060903031101 67
    0x1411504452488080c1c0010244645d042000c0035035401110030140340c3d0307040324100d0580d031414150b201d010003045a6182509107464010091003030280400028420603400510500781803200b08050a82d002d0150202000300b80446001680d402c0342d030002035481482c81c46c0b260883e0521840c9800c00b103402c050310401040002040140c4410a88490780d0001c81e070201f00000b05060500003845a600281003021200748842403401c140d03002000290701c1030381c4e0b1007805c420400b00c601a40c194590b13050385c91313040034020203150f9200341c01070340d0001d1880080e1000e40b560122000e04a542950002c071143d80e02207a080c0c14003010344903090707100c80860003824038000d4402400c0c100060502a0100840310008080500c0d000009440d42099000d080300340c0e00c0302c1d02c0c1051900b6400903203403d03003103210b0890070b00700f009991302403000760402c043c85000c00907080c16416000740600500c10040e6960015440c0081001000b8141c0109001d8031a01d6040c1e0440c03c00411000c980103c111440c0c3c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 827650485 1250 827649235 827649239
    0xa0c080d08150a030605090c0a050301020c060112080d140103050c1e13271b030b010315021224030a0809010f05040801020315011710090209040b0405130309050a 71
    0x7801c00c1040d80d012002d0035081c80b0341010b9800140c841c0006410140c1200e14140400000400c00607500e100e080d000c55668100681d20341c100f500b80e104007a0707482c0c0903030000c0004001c41556044100d04480c420705186040800400c146000c035003405401807941d9606500400c00d002e000d0120008000d03090307070091b403150b000010b0107c00300b03400c610030740c0030b46540d9002d600c600200e944400c4080f14081c0d140325180440c2e800384c03450003020700e0042e1000507085882d1000040da04e003259040300d1340401c8408080e03103161294034900a442000f2441503400f0422080c1502c0c01044480c860501c003030703d01ca03000301e609020301071a07440c45509600960251181c0808140f5000a6915003a800d1034240070100740f151003140c00d4021a40440382541c0040144140c0d024040080d08004100383c2e85c0a00410000014011880c401d07160329404500e0310209000c54401e0760002c0030084409480803c0082d00380001c942100d03000c13281901c16804062401d0101540030500100400c2c2c101c8078841c040b4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 827651735 1250 827650485 827650487
    0x52e0e070521061c0b07020f0d081f090f090c080d090314070312053004060e0f0a0602070c1202010f1206031a0702070f0b0a0e04090605090a0c080d 65
    0x42042c00390782e03480401c000c0000d2840e540c0e51800c0c41c001e0b4600840b65610598601d410100c0440998162001d40241c0c090480e03503d01c001452100303e0000d40e034030740c10f0380c036820000e840c104414080c0780c480c03211201c80494003014500504042c1e620030040080e0b02c0c003490800584c080300c95040646c054126040824003207600c10750340002e0b070384c000c0724010800144a407140c0c5080c070700b03600c014103248490403040b05542e0402d0140c1105908031038113140c1094804440f10307403c00d4004042846440d010f0101d80441c40543c0900003001a080031185881c5a284125141400800c0200d4820b90000340300b0040010b8044c0c5e95000303040d640c000c40d622003802d0b80080c100c091010102c20030011003084500701c400c05a00201c0003150400d02e581e002c1151440c2d2202d00d002d003140c9190141c820709100103401074a40201c2c00c101c5116203801d60800a0020045a54204808459500944075460390010441030321403a4080c13000040102000002c900d4040824001c981c08030005401c2018005462 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 827652985 1250 827651735 827651767
    0xf081c0b1504050616120906020c040c1e020703051e0f0309030304061412040f0308100f120507180207030809061306050402011b0b06040e0718052e0e0705 68
    0x640c3d4100d90f425120240403544826010403440c2c007401c0c0c2242e41c0d02d030407841a0054000c070250f0301d041e425a88508070300e10500013030311807000d03d0303174000391403c958002911021a0540c0180c0c500d441079400203a41c81e02c41c140b03048c5002940041520380c0c43c060b034440600400183c03a6800c0d210014600303081d5440f001035101e0184d881840e003488650203009007401d1081c02202d1584d240f288520905007003034142860042d0400c5001c9002c03481d01800704609000107d825405c480754907040d54103440c00e0005c03c01d02400007010484840c0319070328012402c010b103107a076045100705001340140c550300e05040041400304080c0800809801c25002c4c03217410a909400406843c0c0c003d0f6012489403140d1004a0b140c00d000320842090540fa206440200f00a803081940920400c807414008965950411515003c03540300744414814a001c94040e80d400b0340d04807950040c58400f40ba80744124030b482c01c820701000b1102c030110455070304c0e80a10100014043c0a500b00a4070b00d495405c20200c28081c211f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 827654235 1250 827652985 827652989
    0x5090d050a09081b04050a0915020d0b040501030f02041104080d1d030105041a01140f040f0605030a2907020d0e0a1a030a0506060304120305040f081c0b1504 69
    0x4100000401d850040e006001e1800100100001c480e0582800910701c00c4400e41401403502c00c50078030700860a41c1445009000c14a60050088425061049110350096001c2d590318410540c80340d01c002195900d51044500075401140340d100403441602c100401ca034601c07122042741c49000c0c0f03c2881080c03400a071503411920f090500d644002903103101c0031440340080340703410b9156003031004200400030507040790300364103034400300039070f02a40c0762810711240d0341035646000e1304200a504001d48078603054000c55291034180074001545520398000c01e00b0701d005020160360300141c442e150403480a09508161040401c030090740d0640c00c080350000d49955450020f0300030043c070026181c91564416500340014a480d600380c1c14103e003603002c2171a1680003110b900d40c46520300380c002012800e2410460f0b10403039105213000d0003440d00f000190b00174540500240c1d201c1400f0b51b05a00000d00520040c1003080001105020201660210030700b5282d4005549000d1300c403230221100202400400c1c0d0382 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 827655485 1250 827654235 827654237
    0x91203012301140a18050616031413081b030115030231090209060303041a031e10141f1103090307060509101407060203040807060e06061305090d 64
    0x80c0710314400004940d09500d40707448821010f8005020801550020900c00a465001c0038408889075641c0800455000e02d0300510f100510115221000a203e241e10003118050744035003606000409002e0141d00016412404040d1f108400d007080ba69500703940c0e401500c41c12002880752a03406841940154014400280145810107400018410079500364207140c1035000792602e0f580c9007510f40c0015124018040c0d0103038201c02d002c100541000b100b15415070703011040c2804002601440c0c81c03d81d80c001000c00010607494100380002d03080d5000d82c03074080c0203812001d0103c10b046c0031000c008900702c5520341e407180e5107400020178049540c407114100d41c0e000741000c0d8200000341d001d06082d403052440043d458010901e010621a07085409814a80b40030f840c00c501101041901744c40c403601002d441d900504023403090394005252034000f5944148900d80e202c0c241100e99503644240c80300000d02050a42040041000d01c1c100044004038481107406e083c48281021034900f502c0300101500d8030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 827656735 1250 827655485 827655539
    0x1b06080f100e0c19080717060616140105101a0903060c1b0f060405011b020703020607020f0904150e30090a1403061e06010815040609020309120301 65
    0x2450f40342c9040654a0480c80150300c2c12031541000c000a044000884045011900d8690516010030a00c0c403010320469014241c54500800035445c80c0401d08070500886278100d40036013490b4150340038080c59006801c40b02c0c40700400d5040c00234580780180412107003e045c680900010050380c0e4005819038201d151080300d00d588a81e800c4080800b900d61000d58030035442055800c00d40c544001500300e108502070301c002c11100410030007401d4020b40300c00c42040180c0c0300340c00c02d0001d80350000c0104031080c8010840c0300b041110001240100c0011102900c0068450f00c000303c84807210b0142009441d450406070220310754600c0b41c044426170f0304203403031445c1c000c0c100d00c0442016030305c0860b01407900043c03005d000c05599550f20040d030290500c2c43e50107405880d0200c0c05440720081d00340c80494514102c034034980e541a0046982d40c0c00100700b6014500398130900754003900c4621882c000340080c6000960b0301d182c05003c0c0c034508200706541640b9510100010000e00202012544440180c03403289 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 827657985 1250 827656735 827656741
    0x60203131710050c0c0d11060a090f1506050a080d02070b090a090908070b040510200a050c1e03040303031107112205011d0702011a040b0103091b06080f100e 69
    0x241c0a0060351401c3c5d07040e103d000741c440c0e280c0ea040071403030000f01c0c458412070f40e895a0381d03581ca10a8807a2043c0007888400511501c1b030010303500d03c03030003803448046a6000174419944d1001650398046540a10f405800c2108889515641070085a000c0d040314450030345400740303840218000c0340141c42800816075541d40c0f00c108110685c400c41f034600360019801d904505043c2820740c0c49551562040718003610f1b00078008204425080700d00c00c1582c0c881e4009040510b001002c2d01c0503440482c1401d40d40c05200c016007141500c4203500d440d01c180c54001940c80790700f10f14010b82190310790065003409030400e00440c0d0024121403881220f100041d1840d80714201d100c041c0c0c071001c125982ea500d100394185000464100700c2c000001c0c13500c600301e0a4029068980c00c40c00ea00700c56801800f89203d44201803040101d003081c0e040028818010300d40043c0000c40c0b03849148448211580f584100c4990903030810004d90302000054004160507080c8030a400d08409044141c942e510031500f40e40c40c00400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 827659235 1250 827657985 827658001
    0x302090f060406050c0f150a050603190803100801050c090d0302160801020a0305060f0f1504260705030d170a02040909050a02100906082e06020313171005 68
    0xc248200d1901602250315641c03140c0c0d01034403a4001040241c803d01c640c008441510074000785c0300d0460800002d01c440e25455190501c0060715000746030340d802d840390100d8040c10a0b148400140d80d1303800740f000103440b4200018484415102580700d00f4490b81000103100e4000c03501001c488034140111783d44841814940390503410011020014103100d880b164002501d2141900181540111640c0400c0655500000c0040e150490b440080d040f13440c00102c2000c904091001c54404080106c0311420b20781d84030307540740c400103072000812816110080c4040c640041080751801030030080300a4009014104002840c030400000c1c160024046400030542c0342140b135044401814542006104042c0d860030300540d603801003e001c0b0b0040b40d1320f1080e02640c41c41611010300b6a502643d17031108540310000e003c803040f18103054603c60340d03d11084074034560b088542c042004203115005142c855000b00401100c01c10705610043c58000b01041c01ca22054010952000c0f01800d25030000d0321742c0310010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 827660485 1250 827659235 827659249
    0x24070e0a0909240906050604060b0304110102011d07030218060d03120b1f1409061c020f0c1b0102030708161103010f02070b090109030e12150106111501080607030209 73
    0x484a104030b5810301c5200040301d83d80c2100003110300a040a02558450300180003c48107540300d80070b0b003d0010f00114000801d22943c52074400c2052002084100135100302c055500c40c1d58070b045595601c1719504008608054004801700601c025050f02d20746840400701e01d40030b400080050410000c540702125010041d4000100500301414050015808a00111945052072520b82c081175207484200d01c1d1410407401c4620700078000d0711550602340064500511443c1ea1a0318100a9400340701e00514109050082c1a00754281d10051204030b1441c403070f10440d83c20000100381150800c01419000c900350004136101000b044420500d212050f0500462458801f655140c1c15405c24943c0d014030b00c00f50b0060121a8080e8403090400c0e11303214400c500300e8442c400000d000c00c00a21081001d89007560808000843d640280c60702012140080e03010702c00240c02803004156251340200081004200700c61000740341c5249001c15504240002ea41d4090040102003003580000d500200c40d00e40013 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 827661735 1250 827660485 827660513
    0x30a0809010e070f03050c12120a09030f112412040201120c020d0e010e090f0c07060c080a0b091e09010e302704020c24070e0a0909 58
    0x102c15510050703250100d04100300301e0b510055826203e1164007040e9072a20341300360701d5084134000082990001c1400f41d0030700c40e040004032405002e648280000426080e21241d4038161060419141c40d0100c4010450b40480800034400d003055642c503a410701c480e01c01c0c2194503801d03e0703075850308103a922440126205a4007900c44030b42e083c1050703002052940c0005000005120300c1c0c03116500c1c21450030045415404039004168000d00034008a41d40c06800740001747c110800c800c40f01e240043c1a02c8150130f40722001c0b440c030001044201040314019442c07180c0c4041c41c00490307181c9864100645050102c1e4501d48140324200c0714140030440b8218250301112503110701009480b541104185240203021071704918070074145104c85070100070340401044030401c08a14195000001c910750212200e45008000c0b1500aa807c001101300560f0811040400b202c41e4040c2603900740c00d514081c2e05001c400740000c0144540701e2444402665a4540d01c8165022000c001448010508090f408035440d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 827662985 1250 827661735 827661761
    0x130509061309150506060c120f07020d030806011b021e01050d150f05150d0203040206120901020a12020309070e04051c110d1e0f0c06151d0603030a080901 68
    0x342400800c0000d034484640c0c20500d80f4200401d658040c24000075104401000d1003035000304403400b0001380f05a000e0070f10726040303841c1e0908003425640804e8041291480c2a030125411508019040d0380c0718442130b814209510015104030b000d9400304115503131030704007611440101010000b0607446001540e01964044405108003407081000c00640c007142d0140c5076034000228408225070422510b191108c041014509185c0300c11016110025000540101c0c0d0001c41000328040c207200000c8002d000703054207000160707901202107002e080341c0d0300d01d005818944d006008005c0a03010100702d1034221000e031422945070342e0b540d142c150706240008030f09041c0749840c0310601e44c01540c0600c500030915003c004aa1140d07408010989846c040c135001109140c500741b421403405032190107400c5c020051801c0280d01c000b190f83c0e50307006492800132502501d0b20000410005d2101d03403c1c954055400c0300d081c070ba0301c0341807c0f0007291b00d0307228031039042061049903000700d4251042580709484881030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 827664235 1250 827662985 827662991
    0x7080711040f09030908150402100e04020d0509100908030105010e0f1e1203040302243106080c040303180f0909030917061801020d18020102121305090613 68
    0x814010100811100f00154001404810080340c6a500000c16882c480000a400c90342e5130f845608000001400100c407d040100b0100c903080c4507112400a42009841001c01045510b0b01c04401c5150140000704018101d040c084400007042d04201201c0c1566401e00e009c0065070111408180d944500b03400f80f6401a00b0f500045802d5012260001085007003100e0078822003039481d860031b660380218007000e544035105110007000714048104401c035040c07140d1196801c141507a07000c001c800a84801021984d43c4824591203d280c40c001650064031140c101140d4601303100220841c40c0c0034a01000b420301a4110484200122035035007000140848950216100d4880e000d800c0a400e00c5602140401c1c1c00c1d100105030f44440700200c4085d40074100080480750f46a021040102c0f809401070390040d50300700110219003095000d10012070144900034102002c2074800245821401c0303024800003e010b12010042d1440740040901b1200119409400c07601c8180004420440d02c0c1c2e01070300700c145 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 827665485 1250 827664235 827664251
    0x3121503050a1407050a2312030c06150a0803030a230c0a1b030203090f040b040c051b0303070c0f0201030f050106030b102105040c0506031807080a080708071104 71
    0x440500600101d1007590f05840300c0381c1d601d03014804001120301034001e90700004e22960300c0001c0303002040c3e46410700080c00b0207000e10b0920145400c0d0b40c4481301083d49500140c0811525080e00001182280c40a403179189180e40350851180d22800f000c2c2c108004e086c0c5802d4500f12402c4a03d40042d803000d41e0a129100c9801e15560031091540b02c03010200101c1d4144210185c0a506c21103030640950301a0081d5142000201c10001400484200d0591080d40d80a03020030039105d6106900c0c102099803a0260f46000000ca2400c0c0b5000706001e01c5200d60041080003007030307070b4411885000554412101d050410309403005901502c0f500c0403802c42d00e864070000007500c41d8580c1164071a490305550b00c4000111910b0103c94021250700e00b043d11000740489540415a16032010b60b00c2801100007a1400740c9440014501d9030040c0c0b000d09034062000003121603600140210401414980010816100140c0e512074550158490251120314042880420303c400544000c0c1c80107801041005820 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 827666735 1250 827665485 827665493
    0xc030c0c0506031006030b030102040f03080a030e101a0901140603040314030c0306011e141303050304140307090e1e0f06010609091a090127090309090e030703121503050a 75
    0x304c200d00c606000203042030403202041c1818821a01698661816076207800d065494150056111714440402c02d5524207454001036818890001c0084180b4404510b045182203c03024007040c22002611401190004109403c8136460002070401e090b10066102ea5860509807890248411070a120321000000c000c40300b40410000c5102e9102602c90003076049054440107407040c0c40180c0f40b004964003801c00208500c0103406031500b1401042d0490005403640e036540c0c20341d0001c1c6e00c80500640d003003031a1001d5160500c44036010303002a18007003048440c07074081d0710361b20107034000006420040114502c1c0c00e03250501c0340c03400d20305274202200c0036542d40301d200034441c121603c5103410b11441c0101030b940f001540010781e0380614008021000d680d007000e15070211910180b5501da614022142d1b03220808060b4050488400e0003511500d810b50310300b030029801e40e40c1c5c1070040c1080360070400c40d05001982042001c40340c82c042001c0022000060010072903035400e039810290044c803c2e402810100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 827667985 1250 827666735 827666761
    0x5090c070b01030f0b2a18030114041e030813030302070501380d11121005091209030a14120403061b02060702031905071a0f070509010c030c0c050603 66
    0x1039104e184102c6582c0d40710780c55290b0b0b940402140000000e020000b80c2c25441c1b40c0c601070007100212440c01d03454002400f002030702312007440c0700360303043c0880c01000c01050022018808ca1040018482022110015a0010503005005100d1800c194980c0003100c03e0611070b82c103a40026038441d008006030034004200c00c400c0950386203840203031140c2d03588034030310b070f505040d24401e2605004c0d0403164078881c150303680198044580c071210341100b003042c0261400d8004002c58409080c80320307000101802c0c010042400c04500100a25014108025403101c0f503c00103146991142c000c10204542c00702d0264450400080c6403501000c08000710b80442400002d030301c2000b903000101d5400800f00307041074050b80c031440d0803540b040250700180b08180c0700e43c0b1550300700700341d64000e0310388145007040310360f1441038a0f401000c030081131074504000c000111440405458101543c3d04003181407800c0240022320441c0542402410840044910810007038020b201c803000d428020b04480e103a1901040801c00303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 827669235 1250 827667985 827668013
    0x3021206010e0a0e061206070504060e01030501030c14210c030c0f0306041401181101080906040803130f12030902031209090a11090409050609070b0306030705090c070b0103 76
    0x61416000862240e40c014804070407410b10140c030300a0075501d80603e801c1d030498020700c19908400f049a2030103402c4000e010a900c101d40a03220300f5122410604020030301c0c4441d01400d81410714000040c404210000b52060840c0c3c0c1c0f41d50a04000942d200205000c04040c01d0b800c080e0261070150005201008200c07480000e401354110303682c039404942003044e8a12030f194426003540204c40420b021880010a01c1d290594160021984d44e4100d48100c40c011500b00040d02e4020402058000541e4055403198100400c03100420240c2815114407080d4400504040071045041201b5004c1004103009900c145030401c10340c140d800d0b0b102ea070240181001c540101e100b40a44940410280f2004094618254000d00a00b000c0c0d501c0101440007085032480100c800c002c01e03c00407800ba5558010343d1100341c03241c001360043e400c007218818505400741d08951071241040c010000b00303807000607111080300d5088441c0e541e20f03160b40d00303203503000d201300d08000e44242480710001c801e10045122042c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 827670485 1250 827669235 827669257
    0x27030a0c08100f05190e031e0307090b0a140a020f03040f0305060f01180b01030e0313031e170708040f0801091a0403020d080718290c030f0d1b0302 65
    0x1081031820340804444003110815000304200c1040784140c4046c2d40681c0018020400300c0e460464408244501040f1415600d2080c2d9400001c0121a6134030410240c0144007425680b400d100c04201c0c05488217000d15800d0100c60004101c50070320070320800444920800000a407681c85032916500b4602c2840341c0010340b554410600840c100118a0350042d0484800e210410b11903025403407040054454503440c00d0415032958400044001c0603c001c000700180840c4040040f85540b50406884003107000f00d481c81001d03011080d000c96400b100e22569552406140d03540c2d0402450071510a01540e001201c0341d10351a640400c0c100e00551000211130701407440051541c40c1002d8404160384c0440d001401a00021030040103503008401c0e03941c000013941000700e2880c4500d02103000b103103038591182140c0002d604c200b5600400b81035490202c035400041d035518003401a0703d5550749100e0300c0648495598000b41007107000c251503024690f12521880c0c211003150922000a000e90071101201c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 827671735 1250 827670485 827670491
    0xb13030501240605030c210601020615010e04050406320c040f1403070b0f0706050c19200d08010501120902030712060b062107030227030a0c0810 64
    0x541c0407200081070800111070350103040c0e030a08180044580350801b90402541c43d00a10103c44180119a10b100054405005500607450440002440c10501800083d001103448220349a140d80c0b007100344612440945011940e92940e19060001b401030b00c0004490b00110908081a0005007070302c0c031151245400026240c0e200c1565440d028851440b5903019a41e81c6071042100a0101da04e114202d50000c081d03a400c541da82c0c294500030391161140030718072400003901d2420050f00e441442d0300100b645000030706003500300701d006c1010240c40440d0303000c0c0310b44e2541201c110689140c2c003d55142c549001d5464051540780c002d08041420b008150100d145180c108401c102c41e44202464550020018215540350207078030030070000d0450043c0c13070258803142c0d80c944540350600102103180c3d20742d0081d543c54960100080c040c01d4007400880405004200cac141100001500141d081c0c8034034403927281c0c40c2c940c100c0080d207007450400f0300130040b0303a503050b00043c1a030f008a201100f4000010b024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 827672985 1250 827671735 827671751
    0xf0b09120106050a140301150905160e03100e0718051501020109053408031305122d251220040905390913020a0b13030501 54
    0x40c0d0070389800c1d0260941058508004001c0404c1c401c500c02c072801005000041c806040ea020003a80c4002c40d00481d00050b12201130140780071340300c542e0b95040c1280c1c0c03401c1d0140075201c0000039100c0100780c1487c5101a2240456003100c1310510048000f046d0310750410241964082d81c4101408048030001524004046204603035401070140c540c680b540b01c00980500381d0a00c645103080000d0b038910314010045160481e10403000c0d00c0004020b040004001c649603104030307181540c003031000c0d0011805160100c802102d00a40056913030f400003c030040c1e40300620100304000301d8950250440c03844900c207061540b24000746a01881c411400a400e02c891081d0710343d104000c04e07080740340b0010480c00b81000c7c00444c402851525280280004002044141480d1201c0c0d04e0f011205480e201d42070f0045003200b0b40699808031b00c4008401c121481c45090380031900042800e03000400f0383c83d40000e9400c02c00115940c0258140192456441c815220215055000400501c41c0002c403400e42ca02018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 827674235 1250 827672985 827673019
    0x4050a0501050106030c0f0804030201111813150b03150d0609050f07050303040e100b0f0307082d040201030b090907050a05090c190c080706050619030302060a0c02070f0b09 76
    0x20b219030801b154031210346000003040f0445145000500c150b045560310307038106030401c09140040c803074802040c84103012205800300700111026560066032800340382c450701c0c1003880c1114030280200d81c454640c40d030f2269120380c00003008644455140742c0c060b81c26101e04007041160f50003510f42c3d500071300031610140000c880450b0b4480207400341651661003400700b00300d091715895065a00070b10000038110b15a07510113011f03665030423290402000c0b03100032003040145c0354070500070307a0310500b800388a40e520318040d405400c04074440095480d06019400002b020b69009401042400801424a42040c43e001407481d869100c9802843d2280e0103000c0006114034001c004c0354064640c01c0703003951502e40303800c02c9520804030f03461454040c0030030900c1c001c0110300d6a5000e89002d9000e114040f42600d005802c0003130241065002c0340d444060000203001095001030310729480007510704005200040d010083e41762000c15405a9081440d0010200d00200c40070060121914107030754180d4103246100c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 827675485 1250 827674235 827674241
    0x60f021609141b1c18030207030318030809090901021611040f110a080403120207112107090c0908070807140307030f0b0601050f0309070f050312090d1a04050a050105010603 76
    0x58900c3c8520083c0201c00144540c5010103026903a25200003890400c142d001000100b980882030300560803959080041c140c1040e9104151a92000c0840d600c504541e1118410b000c0c05210318000c00400780010b0002e90254102c40c0000b11134014001c810340c00c3e01c1c0c050b81d04401c10003901e001d1820107203162400c195a005100303203810721140c00c50600c1241c260440e031210b00240300360300b040035506800b0030402040c80144015400b50752419080c807608400e1100b150703c0c0d41342405042c1e6000709035450904003c5140c10903103890010106071000031880444040d403441c1c000003000c0c0181e02c4000b91f860000600380c0220b0301d070b040c1d002d511a0615402c0548507000d511018204500e080308400c005484440c1055022005060003800c0041c0c9090b8102c058201315801d1007141d102440c24011020344040c0788004244c218002c0c0034920700c143c480c002600401c034240f07000d08041c803005010440c00c00f842c500d041004c074914040b00c1c030701410034a42e00c00d2001d03001d035229481c3c9000454030307030f110340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 827676735 1250 827675485 827675521
    0x9081b0106061b03140702010e130c0f080609041b1701020c01050c1204031110090302010c08090d050f07020406050402070f0605010f0b0405010c02010207030203011a030601091401060f02160914 85
    0x62030b030b0074a440406144000e0b1b41e021540032410012004201041c40e81c3d0b11141003101c040700320000070742ea1a500006040112060b200009109140c400c01410b541c82181c815403013603220401ea0840103820081620600854000442e45210000464030456055003d41542c0341c81c0300c000d006544828500200314070500e8100000010072100081c00b0030b015442c0b01084442c002c0c01c4648032015a018003086550b0007404074010f0f512002c00d2103202d640301e400540c0110280d00a050060030030440606a0320900c1c0c0401150503020440c0e00665507182d010300003c1c0000340c0159a100a07502c0c1200c143e2aa90f10121100c620b4100086003140004c0b2100c0161004072000c5c51800d0305080c0103680c900b0441800324110303c6190300c0840161400e000d1514201e0790f8442083e0030090f91400c05080c08016003120074814079125081d100c00c105800c02ca41103074020b040034610a070007414201d00f0701001e1030641c04091614000001e14000c070340d100208040115500c110241c444c0e08107041160014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 827677985 1250 827676735 827676737
    0xd050c190203071a040e0406090b160909150305030a0f0f05090901031502090a09020c0d02030306030d080907090507090f05060a0c0605191e0b03060103030c0609081b0106061b03 78
    0x11042032200c08450207410064071901c3c042c003070415607107001b010329034001103400311420b54850082900b0402540311090708044010708410790781321824002080323074000d031165818a17900c800c10b50400180d01326200001c0c0d9001010b49641c1c0da03082501500c0d800300c0782d1940002031003044406001c40d204405490a00000400703900071a46580c640103401c0074550342081d211a400c00241425a46130700140000301008600580c4405c80d01400038245000c2c84a8030041d5001002003040c3c56030082040c1003180b103541401115a204d00c903850307161090303580124140314603100a100803260880103040459808042350000c00e0740352801c2c800180680c642d41000f161440307400e00d000a44a80007140c1c0019840f19164914041e100f4284c2550412203143c000280c0e0a20620140801d5015070116140c0581c000c0c0915407569800804048003500c0180005588001c0301d8108000c510440799004540304555164242400010303000300030781d101d4036002c10400d60b2400701450791844140842901 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 827679235 1250 827677985 827677993
    0x1b070e010b03280f0e0106050a14210a050a300f11120403060f0603050d050c0a0c1509081c0e040902041e0c0305240f030d050c190203 59
    0x342e24030205103da0340703811030b0b440645901c00582d00a507481c421421034030b4550398081000b4000c450017508440340d0307030007160007100d4100080c00542040f401b03d540c50f0030103440c9071b03440a4104940c6c140b000c4420040040602403480f00390240b1000052180c179481c010402c404803007103041c44403600940d00400c80c4124500d151120383c41d2500030b0119a190107058102030303a210000303594540c00e10440c45641c038422403000c1014000d0142c0c51060100c03500302e02d88100505404c507169036940b200201087d004018000501c104c0011080c0184061281e01101c24613045480c0c02c03070310100d5184070840100041845900107015107001569580402c000201003070703c8405900102c807403000765090540c21039111030a00e0016100da2060884040200040801440c0c05007882c000352451049203200f01400c180c144101e45203a4014241c2c2c4203135042d0506440003550300480c070001c0303415030b5855260255454116025030840000d0814100c940144c074040d07001c0c1003e40701002c0d4101e00c0070307400d50702c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 827680485 1250 827679235 827679241
    0xf080a03171302030706181d160512040309030b07020a0222140a0b13090b0105010302030a0f0e0c2403060607051c0c060f050403080f0606070204021b070e010b03 71
    0x20859441d19000000181464814455500428030303250780c55029100180d1207811001c00f0482818030603010702000c20a4901ca10514601c201c0300c800b010b013030801140400c01c0300381b1003940520200d9942c1410b91400060614150601601c0792645210550700c040d080d030000b078200c91003c648403400a500400c0c540d0705140d02440000d00100240128160698440207130411400c40000c01d80f260780000c1020940070b207090240914800000030405a40342040c1030f09000072a40c03614981519828a40140c80c2ea86a5003104003410307a0250034000c00d40303002c02d901c20f50b130408580ca019920301038901203e03542d12100321001c5c00962804610f80c450f41170006c1041441d1840007021042d00036000c0350f41559a201d00a0000c4400301544008608468803900400030907014080341c101c100b50b8100030300c0c9080d46000d0150003001304071082500740500010310f9030384c5403010b450b038a6401030011500d820034400c9030301c2082d44a8000e901903100d0720000260411034082a141a1111201d040341562 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 827681735 1250 827680485 827680517
    0xe160f0e0f0412140705011401080d14030601030b010512100302011409010c0809010306210203010c03050c1e04080307030804061a01121a06120f090c10141e040f080a03 74
    0x1460108007138906203020440d860205009020710301d0014800d003605945545842d0b0020f141115108130b68080c081c0b40e0746540108a8900290f0744c2c440401c0c2008100f2404d9100101d52500c10542c000d0300b00b44400d0140501000d0110300d0000785c0340b007a202c6840c0121640c14040d19809a9140340340007a82c030000c1b04000915a40140c841540103060229116494890030041b00307100381b24400e0401161242c4c02d040d46824096002c9048850408000718100120905410f00c81e0400f4088140fa20043c0303007160810a50460b00240404000e694803144580303002098083d060318141c0e85c0342d00705180601c2d0718900c030040c10f8014005840e040e0380710000da460000504601d00941b243e000742ca1030024001e4031018000c000170800381030b40078814501080064200b4501400c0b070310440c2e2010140324090788a001e1840140d980342d040845c0b8048042100440d644500410b180f190000031005400d030907004001743c0150303001500440034140d15091055a0380c68101000360004104c400a80e9041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 827682985 1250 827681735 827681747
    0x1801030216230102070503280c021c170723030304151418010c030501080c15040b13170d080c070213050f0a150305100e160f0e0f0412 59
    0x41804440150b00c1030525803282280c04c90b070016a0305400000e0f2038441c000030030050080a0800e10b40e52881c1041c140d0005050088441300240500e40394400e2802c038003030408506e800203a0100c50003030100020401443c89420101d4202e82d0010b413600318124840264130440100160314006500303642d22500da03c02c205145c588101c10b0f06030b485855000780c01c402041ca0b031185d400d264100d0055503905000c1400c54408641e460201460000144500107000c82c04080550741111050701031a0640b1941c15a8411a4000c101510000500c540c0b881c1000c020501100d2a258854403064550030f49942c40b100061002c1c000907100c00005298007031040045c02000e4009017980d003840742601585003c40704140c0b40041420b41035002c01117010700b98010041c0148034025509001407850b0b5416942e0b1140e409521081501d90300e00004482e01040728901e20f0421141e0f0004680e0386d034000400c181c0305400b500220b4422032000030000d9032010340050041d036000e0754007007450360348503406c94070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 827684235 1250 827682985 827683013
    0x1020c030303012102011214040209010902160201050d02040519030201030509070806070f092102040c030c0e090402030c0a06050a0909091101032c0c0f030604050604110a0902070302031801030216 86
    0x40c40905105800031001500c1001c082c1056524101c8c0c45081c80c2c010000c2d0311005034000b08079640100102d9039001c501c0a00644000da0a0904546908030100814043c2c011600001d40090341e500091100d12149a84c28041b28002c2c1c0713040025403503c4010544515950040b840175611250201e0702070f0344a0a0074110305446440c20a01c074645504805080840b41030041001042c03250702c18055107040d12404003128607906040129a40d5040007800d403000c851504da1107036840d0b100140a645043c04400c0340850020b08901d005901c2e402d0191154000304c0741c0100060403650080307180d0b40c56201d090340d00c90f0082d1a0003105064000110068051580b01e246419820328000008031414590742d500c42c05040041c00114081c0b000b03002000310032540346c2c0d01c80d501c074005001c00b084010494581140e000708402c0400d004401c04502800d55135440340c030030f007440020410107055011014040c14040600000d03c4088407034011400c0e4000c00700d20b0301081078000107580c00190800039480c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 827685485 1250 827684235 827684237
    0x30c020105040e0a0c030e0c0109030212120c0609070617010510030e011b020f030a090b0a090b0a08070206072f011509091a01030507060507050313030303060501020c03030301210201 80
    0x11601e5120065403040b00000e550030b1340c081d512800c0007801d00382c140c094000a0000c0000602030300541e500000c2c10500c01c2c1c40041d0080c80d030041c10802c18141800f846000b00900d0301031513540c40c403015940e66030b00412202c4406074010558003003480d0b031085801400701c1c200c10b8a40d9495900302010440002d078010344150901d9910721142240f00020b000303c100090403894000749100740d805019062021f02d81030060140c1080011442c890342103a02507080d9898180d945464070040da20941d042007141e003155024040c04100303400c803aa44150481e1050550341e090b141c1646a80900781c40310700344d42c01c1012100b5024890850102902a0644982c0301c0400c00483c100c00e400492a014103d250000c2c014a42c40d1010141445542030442410004940514441c2c1d8076580b281c070b485107420700544040207400601d0030140034081090300c3d030303544941c01010802d940d07910b03014000704a81d10a00303025000d003161211980ca40031040c2c1f03040b00d0301c03506121058000800c00c8924440403200481c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 827686735 1250 827685485 827685487
    0x7060807050a0e030a0b0603100501080a0f050312010e0a06080c1e030a080301090e1501030c1e030818030c10090e070215010602060601020c06040803070f030318051c090e04030c020105 81
    0xf80c81c3d0b0750204454141d840c0a031544c10582c0c1032400070316081901c600c50b04001c15040100401030a80005110030080342c0051000e100011136141c0142103201c1c81029500003128a0300100b809440c2c4c3c45250f000310400502007000b0366454040c0f54590f00816201c42d441400f1404c4c001000910000086200000030300313036242144541e460651030340003a001900e103035545003400351009100300801c030b000c19100104a4084c2d0324659541040e518140114001c0c018005001100c1c40d82000c01100070f50f0780300400703d480d015411440c89040500c0b0000d64800c0c414481041018148011550009059a034950480d1401c06c18800d400c1d14020302254212700c1890042030b809040005542e000e804194040c01650501c80002440c010040e00345a1060341d04102c208500304000048a001c1640081c900c2e02c01c45660600b42c0007002400384113400300c216031441e00d0030002c0c041000003000b40031450690310910702000849903000d00d8082c116070f8030403940c0031402181c0659860311039503105151117 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 827687985 1250 827686735 827686757
    0x9020f0d03020a050d021501030305221205060a200313061e0501060216140a0306180519020306060d11060706060501020f12250f080a090807060807050a 67
    0xc03915644031210180c0068100019490400406200240300d19489200034040b461400110303ca002c001848014141301c0c00148105802f44044240e980d6030714440040750100b65103122100400345d290604489030300031140000e080744801d1003040d20110a1010546021000000b0100707207a02c05801703441d5000042d8410300016601d8010000c030345403003012524246650075040310642d00c06811600954100c0c0090036254203d101416003210044085650290405000b1810003811074102a00181c109451280070145004000804520550031101c9101030544e0721001c10040010095054000070701180f91403519403007032010300c0d000360010040209038000043d402e0344080821194a51284c1d0b08000b50361301480614441c51020024110440c10342034007504a120b115400032860f807421520001d00a108002a203030640d00c020f42426920543c01e000089070008042600092644100070620360408030311503003102e02e69120000c45490300d5000307a0340340e0007910608003008045184 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 827689235 1250 827687985 827687989
    0x30e01110f070b070519031d060f090f0307020a03020f01120e1005090f0a02041a040f020904060b0c0703260d0605011413030213150b0c0d08130609020f 67
    0x140030850822041564410700c503d0418040c3d48010091800d0001c14407000c101c00c5400d00904a09142501c1c00044c3c55075512600700100442080b00640d5100d1042000b60b800040d4400500500c103d0085a07c2c410f06100b03515504c0c4101301000b50000040f24042006051103a882e0021041c14107291710084240e8108008403400320100b800150701c24005034009010302e01c00c2d00e8001b8143c00241280249005441d940c42c02c110000074011a500d030038040d203401d000f184c04508800c00510901012201074200c0b03001c0c0d044100031074851854003000081a4120720112064003103624041c1c4042444c540380c001c0c03000f880580c042c60031914510030700e1034103503040c000303000c201d40000001411a0419000400010442c4d140e0f0b00014010803004440e044401640c03001c5a038100c038a40b0022403000d00c900050f0000c00d600e43c407079006400001ca0300840c0840904501b00e0904111068062001c20898680c801607446643c1c1c40072489511001c120701c0e4100c03500480c0090030140110600d200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 827690485 1250 827689235 827689237
    0xc0306020c1e0304060801050906091b19080a1107030f0e0105090607050f06010f050f1e1c1502180d060605060406021006050a08121303050109121206080607030e0111 73
    0xc480e14007500000703000c0c417807140c0001545d400b510080d2050b910f00d1a100010132119000a44403480b00c460714844503061016206c222542107440680e0a08001d40020014001c1c2d042a03800b04c5101e0700b80000b98004050f084180c0f03401039050b03680c005c080034040c00240c950110304103195040250810110346030b52181d40c02030580c64414401080500344051200341000c20681000c2d06a110700101000245c0d42c981e040b0b0580d9500f11100c826214501409042d021001402540c0060040c2e0581410550788034020071124040c0e10854046042d0000c1002284940140c03500c401c019418a5080c41c20540d0b05211254492a000241e40e501d4400107961608164424401a8003818110b0100803042c004c5600405041e140626203a042110b1107480740e0202e00349021511000c54403000349400c80b20301400031504180200a015814100059006080500100811000c3d1026405840710744502c5080311100e001410050b140c118003103014001d0012900d00325920360503d0115050300304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 827691735 1250 827690485 827690533
    0x4080c0a0b0f09010506010f050406050a0504120b040b0702061014011803060c09090209060f0906160807060b03061510021e0102040302100c0803130f0b0906220c0306020c 75
    0x30240d5542c0d490300d060000e0a458004140728100003100c0078240020360044140e4040d11002d0900036298010014111101d010380c0e80b100a03010304c0b28411000b40b0505070b0b00580110301410700080c4c9680c030340c1c009076912101541c091085c0400f104040201001610000300070190514000e0400341d0030351081e00b013000c1070f60000d543d103035620a4841071954002d000d0070000d0a10103070a500706000071000030018040c0300c3d0307251815400050720081c00e5480608444840d102e0320840d00702c000c22410f0400a0b82c0040104031446450289911003600d00002c1061007403030000310345500c646da0740c41400040c2e0603100018040d803141941c01c07055188041076980140103007400040c0c0712855401008000360100f491242804100280c800204606e0300441e40e010754a0120801910140e14058200c81c0901e8006011001203c090006683c004189103000744000420a4081340c034081c030079800f241030100003c01c0c00002c032404200040d01038003d401c1c40f050003026a02025a08015070303200341002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 827692985 1250 827691735 827691751
    0x3011a12041208092b022407030b0405090c0d0201030e102301081507050702151809010f030213020909090d030507020d091202150d1e0207030804080c0a0b 68
    0xb80070003000d003903000e00c3c2c50394012452001803040d00441c0d599041510300f002100511403048000e040c00090003044014101d801005801c40580031011aa51111006851841c0041e0409605032018545401080d000d0260f4038040c10203840c62074108090038188035000c07410715459143c0c00e03040500c240045218009064004254500140c02c900320b00050411030304d50000300b0784014030440c100001d0550014249050011941d103e80c40291107c0c01188070083d4001c400324140c401a044200c060304089030504c44440400c040502044103583c024000c0b00c0808095003c00c00140c03500422101d148800c02c0c00062801c84c1c0d03070000c5a0881c0c022140c86115500c03294450302c000d5418811a41d011132a440a0240e00e440b07860000d1094800e4403504100200001440703095603605800001c030358454140040da07030615540318802030081252010410b032903450100c08140e074580210348409515a84505d625500d81e603407020a40c01405145503948600c4a60000081150145d42d00420328 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 827694235 1250 827692985 827693003
    0x1104050c0a020c030a080a14070b0103200d0525030209070809060a06050306010501140d1d150103021507330c03140a0f11130614040b03011a1204 64
    0x1c510300a80380c04160030001e4001e9011890100c04a00c051043e5102c03170010f8901b0300d02c6406550307112080c81c00b85007000b0b400d41d0343c4c0c44000000c0101c1401d069036140b00e12500140822144c00c200526807a40c40c4c4081c0c055000462102850040c071030300350301c1c4590072019800680e910f0b600452203900341100c4c4403000c21442810300c03110880400c4441d40c408a030b407a0038001d6604201c046601c9000600c2000d05109071076a181c04469140419103c030882c40b94010424403d200c1201c0552044a0100c4a4540103000103003a00c0c0c824a802941079a4015128158088e06001c401109034481d820603500200e4418500440e9480c0e1043c1c0c0c00b0745440401000c4a812200550303004440144000c0000d15107480d545200c280e80e0344032a02e60010025600248040301d00c01c0c0e5001800210b00e041a074a180000c40b02e0301c0d90341d0350344220256100d42e0750f40d0b507258101d000507000743c0c4514050311000a201b03000420140c000310619180342d050449449044c05105440c0c951503041c01d072802c03102d09a07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 827695485 1250 827694235 827694247
    0x90507090f06051e060708070b07090f0b250204020c0604291e091e250e011211130207020310050c07030c02120f1b0108061305041104050c 61
    0x20480c0100b4024020403180340300058a4024002030380e00550038110b01403100440d003001800301c92400d5508841e0802201510f51504140042c2101c4507805017001c2a0003002d03002c10103000200c1a00c51003001844e0420310814100c1c280105148904002ca90140d002c00595181d45014451030b80a0307841070401181c1c003030a980a00e507108140c036260024042e4400100700e103820a540080d108031a10064046941e05c9142e189401d0038190780440900382c41004400c1005c80d800510b909548106410300559244480d13812882c0c003070b8510400c8410144480180071511803000300004081c13280e102c02500340c007440042130611840380d0503c1180d81d4045500000d5080c2400400c1041d03034400010803281c5090051010f140c050080c0c00741c20040070381c0142c3c007151100c0012444868001085a40c40840d10b0319072a5201480003041c40100195000120076500540c4138902410004042c0060b0030f291424640007000c008000382ea01014400312103210380c680788a0343d4040c0d8900241300d0303a152 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 827696735 1250 827695485 827695511
    0xc08030703121802010e0105031308031302040e0604051e160b1c0c0f03090206120906072a030305191d15040c0905040320010218030d02150a09050709 66
    0x9a1008860071120500303c3d0290040c2c0c2d006d006e00043e9002400c3c030a490752031724102c615610085c0c81008282e080c001050012105c0003100c0031070807030b208640910411100c0d06440303480d004180c1c0c0041049d40404200145407028921895002c01c4e00b400305c0b0340403041a03207007464140e030380c0d4000c054030a00040c82c1000301005903031896426a0308003013400b1038403841c07900600c00030012040008159681c00c0c0801199100001c45000141d90368201e403032802e140c84041c2d00c4482c11b071564000304203504c1d42002e0700e40698811681c80e81d6003248001c12a40f1035101034001d050000c1c0410100800190380c3c200e9050b0700d104100c0c0000714904120b40030b5000c601401e00d0070b050310b0b03500102e101d0311070100b000040c0410641425120b9400d408a2907483c1c618055401c14640018102c2441e14080d6040d44044e05501501c41d036441c4048084111a800003890703111150183e0560050f003091102c1a0f120468800e280e41051840e400010096017980700c2d642000c0f41600042c0b0a42e44030004e1038100c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 827697841 1106 827696735 827696741
    0x3c0a0e0c091518070e0a0f2105061e150d120c0b04030c05070902160b0414100219050a0c0b06040f020f0901090e09190c0803070312 58
    0x10700c042e081c3d0003d100c0b0080354600001400ca0031880142e14043d03044408540c1c1c005d900320fa0081c200702c0705104455036500741108811003c0a00030018100f0020036214580c1c00e4040c041c0080c840406a0145402a060201c240e1001407280820355035004c000058907403150072101c0c9140c00790010307100d0460444001d401700351008200002c0c542c0106034614003e00c940183c5100d00c1c0c407828641c089000c1e4507404c2c00b40e00c8840d400b03400012440c0c0316054006000d00c1c009002c04071350407481031034104c0100c8400300598003c107540380041400500b8070200580c40c00c0103030034041c0c6881d0042c460454240060034803181c0c1400308900d6100c1d544440d12885404100b95031359000511500c683c0e900ca07061450016100190004200c248032081034024034640c070203000c503603076481e1158a0b4400140c8040c0e52600401d240041e19901c104000d16119210b0340300c0c5000155515001700c01c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 827517985 827697841 := by
  have h0 := BRFrame.cov_init 827517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 827517985 ≤ n) (h2 : n < 827697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
