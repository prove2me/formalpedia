-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3944
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:50.14001+00:00
-- url     : https://prove2.me/submissions/2181027b-2cd1-4fe8-826e-335186628388

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 709172661 ≤ n < 709352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 709173911 1250 709172661 709172669
    0x503090405060604030807030f03050612061603150308070b1302010215191e1b020304060302071a0f10140a1818150c090b0415030e030c0307020f0d03020304 69
    0x15a4030740100b10140c0e1050291401140d010480c00c1d40e1720701d00c0c5001401101c01c000301ba00802d0811021400d41d00d0800311030011104040c005140070f5550909001d500c080200180c000d056403480c00341c1c2d6014080342d40502440c0507001071943e8030014a0002c1c622200101001d02c01d200c0c8a04100060f0b902298490340e04404002c019100c3c0ca60062812031151460411201c0f00e2808902100000b00e0f1b2229840000c151030b130030844201d0010741403440c2e0b0000041700005800401080c4042030095015002182c040d030168150050280325440c10b034042076a1240303c01d070441041100f8001e00481c01000b60006c2c2c0168001c400480740855401000ca0051030b40e80b0f00300030761102252000380d1007960600704050161985151780c1c00d00c2c1e5411002140b6110119040140e0b032003e0034000d00d1404100c45070360b0f10303035072070a03183c038100104402c10490500c0401d51505504a00c010040026010118000c0091076075211103204010b001001f4264160254031780200410129401009580c111 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 709175161 1250 709173911 709173919
    0xc0b0f16050c0a080c030708030a050405090901090b01090b040509010b060f0f1908040b070e03060a0b13090b0a0608190f050f030c031e180f01051e030a1404050309 72
    0xc58492409504041c0e5030410035410103a10b4900090040c2d0008500c1131409040c1d05603950651106032440d100d215080c1d2140101d04204020400b030300380034005a511400079000055508441e07510321002070002e034850321420b511031002c41c0c4c0381d18203031041c90b40000c00d60008105076904500855407034020700b80719140c4141d01040d4841301d01409811580032095151444841c1c41000002a10100341a03038280c80c0d00b482c610009007103502440c02d0792501d4400400802c000c1d0b50342103550028200000700d550700091005034089441426000300c400d4540300d030707000741042d143c022040004c89581307611440b1f86620030a810344442c2c07020480744c000d00e50050b0100131500741904199117040e03581e0050518522002510f900d090b14040040c01c0136001e407650a01840c4c4d41007042c00c82500504450175554100b100102e401440e160203410740004040c10708a04001e0f0307000100b8410043d80d041240304480020030007030300290f45c3c8224403442d2103610006009042988405940b0b010714440303140a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 709176411 1250 709175161 709175197
    0x2190c1109100918030215010303140304060f1a030f0309060702040f090c0e060f04050105011b0c0503160e060a0b0d0c09030210031415030d050313120504030c0b0f 72
    0x2000c281d104000341520f050103101c1032901521441001100110a40c0140103004400c00c034940c0d800f01c01412a43c0564070819840d42d80505002c040c1d0014204441003681c3d61894140140c02e80030761040d18442a00d101506511502494100403080014841302c2e001000003c400b55568010f4030055a01528001807842c1000003000043c0800760001c2d003140c0e141500003400690035030183d1302c50041a00d800c1d00e030301c20500074042035072800c0c01958082605900040e0541144840001565000b0321803100c00d80c0c2e07120082802c10000307030803a060301c820030381040c80aa410140090b4001d07c0c140c032108241864446001c069001d680d000036501078480100d400b5883c80780c4038010107107130018032541c081d20b8140d9015000306038100a0440d95454030001a071054101c505c1500fa2040203009040d180c035406400f181d50b50f0004004828244100c4480c8020500010705000c0000d01601ca15075500d096042c100422000341c1d11119903c13004210360325400c610320341920301c00f01c030b0241c80c408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 709177661 1250 709176411 709176421
    0xc08060102010c090e0907050a0308031b070210050c071703070516051f020709050f040b13111c0c1d100f0510031e0507030606110c0f010c0c0902190c1109 68
    0x108200c0103508c01940a02c40ca00c0c04420720200b0b500544c080c011010b01016154084042c54003a070049010203980b22050012121045002d4002007062156101c2036a4015031510052012401890004d0030907504c081904010003808014011134003052420381c0301d4051074100022405101068011201d8030748070f0b0443c404034001c02111000d001807010600140c80c10000c09202e9510845003915002040000301300190004481700450a400c800d8490300090403605001d44100081907450404640c00021004a241051000058030200760a80341c43c00d04501c1c14095250007901d094a0750342071b0b580c10000e10b0309080303001089901c1a5103201080324021030580080c0040724010000c0a6038040284c103c6065600481c811400c0d91010001641c49074011202a503010410310542d6001d60300c480781034900000c020310341c0c220501d4034440322038581d41c0300280c110b0103070700400811b81c0100d41c001e0003181007142ca185146543c5403d241196051f140d0309141d00b00c098140d40558070060101e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 709178911 1250 709177661 709177663
    0x160819110c0f060c100902010311031314070f090c200601050d060b061c11042111061207030c050a21110a080f0f060d060e1603060c08060102010c090e09 67
    0x141411892030a031005074030900b90417005800a01c1003240002e180c00310a014a0324a60240e1703004007620f076030080c00c40c090342d0344058403140074000c0e10300c01d481241c02c00502c0607480105100540112100404c1e1200403040191050014060070b8407001a585c0c0040c40078800040c000381118801c55021403802c0090500c1d50040070606c4100d0341000c0c00255180940d03c4040300c6142c01e0706642d20410000000d848050707100d01581c000c48800c3c1255030007550050b0498441030f06607502405002d8a400900340004509030300c80c00b28503045160500c2044121a010b100704040e90384503041c00c6181a8081500614a481889990325101b0b2203c000341d40c0b0980b50f0f400070100701c40f952240d5a80301a1403001414000c0100c80d010009801180094004d25003905510300541c400344c0711082d06101a60b503103010b48002c030307440f0f00f49102e05c400d46000c1740c00940220004600590000a0840782c0b0342000305402e400404041c156070420480351443d40d070084849040300c07100012400b59880340d12442e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 709180161 1250 709178911 709178917
    0x20a0803061306060e0a0609140409140304230303180915061b010b030a0f0206030a0212010932130c0e0906070906171308160819110c0f06 61
    0x60241034a08100410f00540010b44805c500f9422a908507000c6e0791420116004540c07030140310340c104110317044040c0360709043e040050041e10a4a8800c00058452822495500141c2c0b215800c0741074150703103800382110300c51a6170000e20240e01940c985061503034002302500086502e13900803007200c000107900d410703103103401503110030300030013041e80d03100c17031065401800040c101d080c809540b901c0f10b000707034900d000070300b400807254804841d84070315141d5000c0004036007004159074105602000609500c10082600f140600300c100400142400f810301c0903204d401d0900741d0b01d5006801520700c50051001d220b0110303480180c071211441040c01d145085030b5012200c2e40302c216840e15034028440c14407004600c09102d10601d0ba2940718907a1384440860340118081d0a1201d440014404a4103000c0e080d210000c489008240d50751801c1641c40082c05500d10120083d25010300c0401e900d540000c440155981181892074521184024100e060f6111075030305903901d2040041c09401c84040e101c02d026 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 709181411 1250 709180161 709180189
    0x8030c09130218030106120f03090f0f060f0c1a0604270506071701090c0507050307050105091605060f0703200109050601090207121809020711090f07020a080306 71
    0x2861549820148810041e400c8016000fa107a089901c885260f803c051003194103c5a561050541c80500d6441c0d007256a10021410f40802000c03100100d009911031250400130408060821151481e225008080240c3c100c4550200061505031902141c14500741184c5981c81c01c428078200e80710700b00091300400c581024940c1100c105900250344950070707809462203d01030340654009a8a0420840c0e80c6801c80030700071403011201e8010700015209500c428031034071080c10640d1400c03c16482d00351958002441c222182c1e9154403c1001a43c0c0500015081c00b80e80140c2e900b1090400300081c038a802014000c03c04480d012680c9800e141c810303d507524014003190828003c0c076a885800b00e0103454043c4050303500b44074980001941c40170501c2250340a42d00f0244400c6001e0340c0e00e030102c1c1c000404001403400c2003e404408100b81d00184010f0542c240304401c2010040000c0052049030100141500700c4c20101c4030810401c03d801041030403003154444905c550b80d030303210f1380020b407502d141c07500f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 709182661 1250 709181411 709181419
    0x8060703230411121e01061208030a05040302011103090a050d1107032019140f010504030b250905040506030d0512041e030e010e03070302030d0e031f150f060c08030c09 74
    0x2141081e500081c0c110301c1e10b040c4179400074030407681c0360508241140240c01c4000c00c045410000568107000315400950418840d01c00840d43c60406103a4000c61f82044d542040e0700c2d009480c01c682044010441d040c10030f001800d00003036220b102c48495490b03150512001d00410348a107191003000d0084036109a0208000b80010820350b024080201070707200e07078014800c41c0800702d40c1e034007000d1411500c640d000f07450507503456151508543c4c4412101e400501004182c83c80d8054402d5080301e40440c02d803084403030b90b840001c160700d0f000030030041d00d0307016014034040e4010302c0072400e940b0380c00811203101c48860045c5104548030341c60300c2c1c4074054500302a0396100014050381d004156000001602e540c0d402d985081702c48882204154844449100007545a4000c40810050a026000642807000001c0545000b001c840700c40c0c01c611124502000b003202c1d175036001a2503100d52084408090544101520a0a030800300040c0a0812401001e403004001000142d03030034146000303c0e59200000b030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 709183911 1250 709182661 709182673
    0xf0304030606050909032a0109050f0105071b020604030b190e060109320c0f040f03050d1e050d020f070b040b0c090609060a03150806070323041112 65
    0x1c204140102154016248516400c0f03020030502e20002055500000310094508500311145a0083c0c20103c0120400855505e0b8104d00003c00c0e41800f84622a200e0800049070918081070002e0800c80001652410f001c00f8070840703070250315000180c8090b40e92203402000b454440e050500d5a81201401e00711000d410240d54060011020070041d0407200d0301c407020300c102c0c490f98540740e00004554550103c0085040070340200000900079442c1c0100300c17603040905d000700d049030406c0300d68483d41141a03280a07200c1c0402c00c2000c00c000180c800006850004070765190305182c000186000000d4404100c800315190b41800083d504852040fa04000e01a81e00c01d00c52904a603107031021101030310241660030004096100940455030038480050400e460070303205404102c01c640181040008240d80c84031440f20303186107047d80d80090180c01005141c0b500c2c015400409403076607001d412407414070b6520001d46400605802c590011703805011b901c9074041000c04105894102d1040030f00390703c100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 709185161 1250 709183911 709183913
    0x60a02070306050c0702131a04020f0909180604030c081201080f06060604061209061b0815010f080c210c22030201090e0c07080d021903060803090d050f030403 70
    0x1440e001200d10a90060015945512042da03ea00032204c010750001c0100c526119a01c40b2540000300a448041c0c1c886011500003001c0f400702c0c3c100480326010498006400740c041d2410090413580303c0300500f024096188000d0700d268036050040d03c010300b80204103c500003040011400c0e00c4044040031356403203c661f074401c00c0d2543c1c2c5d44091040c420600400e80454540d080980c1200c1c2903400c0c83d150070541c3c2d420803040c0f0004080940c0c0c00d0303805650301e101d50000502841000c00f0018030359a15641c00382400030801d1a44160b07004424103110751a40340102c280e4000303a0081c0e11440c1c0d080c50546071440f03400215000500340550140c00c00c104c4040001c02014100030f02480e211030440c980050000d06079a490090907070201a010944500d800c0241141050003284d1081403a02c466040a146a5901c0391681004048002d515008204000607c80c0045503a0b00700f2603e03d803e000461408000c6500c07489100d15081c0125030030705c3c001c0180101000b0420203c45800116642c1c0d59036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 709186411 1250 709185161 709185163
    0x61b050703060510420207090c0905010906030b130902030f01151d010f0b0307110a1101080c130303030e03040806010e181f021b060403030b040e0304030f0818060a02 73
    0x41400b44c0285c00584425010194030103110105184075045104030401000915204082d01084840011480340d40b0010400c0710701030040000c0c000850f11070140850800c0c1c00501030103120340041c020180780403003001480d0349480340700402180b480000110044103001080c1441104400c03801950700307049a406c43c4135038140404003140d03c28080d00016941481c100807034880300303128100801800810a0040d02902402180c1005040c00c0c82c80c5c0d600d44140b0540d04140151006803101c5903a410612511b58107c3c2c4207a0b480384140e2021482c00f04a464a200ba41d5100d02024040698440710f0400e000010011038005c2c00b0040e0807607038690b0351132110a0702c03018203c603407264198100c11650081c6000107445080740e80c000804030b0080d417001809c0002500014407400180140020944502c4d400748130300c0340914007a0794040f9904002c042480141c81210f58030f0411503008000800c0400d032100301d041e0040758400316013552100a84103166041101e80c10b40307540301c4400542c0003529a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 709187661 1250 709186411 709186441
    0x1609020f160b0f0c070203030403020f030c1305061e01021c03060506280206091f1103010b03090705011e0315050a180c0801150804030908030c0102130b04061b0507030605 75
    0x44808403e0640303030f45602d1030070540d00600c04002c0d00b5600c284000e00040c03078040c04d030b8190803202804075858100c40000007100071040b214a000115a40c0c4d0511420f400d2040748080512000d0b10a0b00809241d440001d45d60441c418030405002040c0e104408158801d0300081c00410000b0003c41e11001c105100c0151805242c8040710441e28002c080010740b400419402d1095165101502c9400007074030100c9906518144104070385d95542d4400060b00303035410007840c060310059281549274980200b1581c60000705401c503034148041c810075600ca07849030300001c0c81c00704158540030805840c0005801003400203a003105502ca1011030002c281d1992016090011011000701844080c00000c1d0030381c4c008400303010340a490b8140d80e4a0b000380500a003043c6411611a152a8445694507840e1381c2c15034000e2140ea0030350341d40009400c0340e08c0d00c0c0c0c01d8552010700402842c5600d0540b9021028003103155088000c1c480c540131108440c00c0c0002406006c00039500004180301900e0b1098003070110071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 709188911 1250 709187661 709187671
    0x30a0305010f050306010308071e111306030c15050910180f0b0906071109010305031e03060f01030b0d120306050a06020334050a0b010f05031609020f160b 68
    0xd103464000210340082002d03607000c6070405005400c0c9a425900e43c00c841da071061b402035540030038000034a21407000034084891440e018002807a40d000781c4c681007214a5610040d8254545d08000e02840480c043c1c100e03d0301140c100d502a0085140511000c2e9800d02565414030b81c40010440301038859508441c0c1e07807801c0d400707400940349040e48444003881c1405440c050000c1001091140130314500b0a40000c00e2200d018040505070248900001185000300760400c444540011406070080c502e090400700402d482001c0490031403600d00c0200d0314111003604054101a00c400312103805440e03218900041d19007041c0c1811403629240e42c00380c00b50841d8412035000d49101500010b12520203c16551100d402044242031a03200c0c0d00403150300e0b00d00c01401a084004203c032540004d000300b0960744800c0c85956295695813410075210082c41e03950744110700035000350f41e8960741a900c4031004019180d09000040e00c0340c20440d0a101c1c03a000d00c4583d04060b0660700506402c1c00b044515240c810b07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 709190161 1250 709188911 709188917
    0x609100909051b0a0b18010314130308060a0303081501050c032221110f0307140901270203072c130c1b020f0301110307021b0a030b0601030f0608030a 66
    0x14481403c20720804c6181442800c040350b0741800411400c504004c48107550a80500d0041511498a5a284e4480c44103644c901c903c8181c9409400070107130030000d443c2e0b20000454107000b10502d90344000d840548010540d80424121400803a01d581c003c10544014103114021a5180c654000d00d145c128144480002030300301c078405002035428035a200b05500d01080c0300d03d041e14042c40b642c901d4559400d20b00c00941c4290040d40340d200079141005200000c00202080101d240118001c0c000202c0040c2c00220045161903200d0003440076584504c03c004100e06001681c90740d419030101c0d11000401c001e04070740328020b8030a00034010044108451003908070340e03810305c0c1c1c85031107403040c110303040464103002044800c0021481c900142c0742d00000103001074114044000810002400c4484580507815800804000d01914680c1000b144100b00128449102110361580c006001c14107203100050003d04100002007899119802000326400c03e03401c00d104140e1240e59640d100c1c0c000702c80340000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 709191411 1250 709190161 709190203
    0x6140d080d0e060112032c130615120501051504050907090f170f0f1c09050301020304210e0108042d0c0602011104051c03051b10060815060910090905 66
    0x240c040c40058101d0304040c0d011440c891f030075900c014803d0b64240750580c3c80b48582d5803140043d803440004005503004600399503c880c85000d0714050700844a06070810b60203600f144c1c034002881d031101405c03501518022030301c3c201d442e81c0b030800885540d0f0032604500c032000d60701d840000e0000140030503030000880345001e07940d01c83e0203500055a40d2000031103d40e5113034001c00c2d130080e90140905000300e40e0206807404680d200d0321800840c1c2039a0003078074101d66131684160301881c8400034000c401c03000f400b40e203424142242d1500c00285044005040030f42140b01544080c3d580080792400e50412a13098030501114607201d060544008400340306031000b550030281c400c2c006058078411a81598401403000500f150304020703040c540b9034512022010b1143c100039001300755040072143c80040140380700501c0c80c284500003200546102da440308c0100c1d1300900402c071070303001ca01480b02d80c460820340c0e11010665601d800c01c011200e41e640444a4140b90481b000d007400808203d40da20841c4141020310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 709192661 1250 709191411 709191437
    0x15030b010201021e210f041406040c03030305061c11091005060403152702030706090b09100203160f110a0302030703150902060406050c0106140d080d0e06011203 71
    0xc241e01c91204403031040703007640c1c43c40c10a1381c0c0004064000000c03681184401000c0c0f0245420a0700402e6564100982c002000c0000300401c082c48005010300708000341034182450f54641d600208180401024551100d0000c1e100b9150703613a0300804c0c00044070642040000750304007541d0210708410818090314051001500c4084030800c3e14013240c402410740d51825245444180c949440f6502d051a02d03902c41c42c0d603040500000480d12040c5803d2034807001c040f690f80c41010f2400d00c0c00d6021900744055000b04005003010003040e07950300038054501440e0464040012415403080003030668800c1105400041030201849038a14141d06c03580e106130400b080c4000b088001c000e40d100080d419070155005000180341c03120044002440600c0c0440d40441c664002103294010f5008540090400300704400262006d0040000504241e00e40c1c0030b8200c2d0502c0851302c02c1c800000040c0000d400007400003c0502d00f540085182100703101600e006585907140d0712503400e003402c01a00011201a60340d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 709193911 1250 709192661 709192663
    0x80f090304061b020a0503010e031201060912020409171b010609020301080d180b0a0f021b0a0611031204050d0f0305060603071b02031b01030f0e030906130f15030b0102 74
    0x941596400e031156803e01c4080d149845030f03480301c04000c0360004500d90303000925450034050b04030500c20076400703180c0340e072568401c80c8406030b4160b01480800c50b184804029011210980841054064070b000c41e9003951402c010000c520fa611b182c6810610024075846a450351050317030011550110001e00c040c6a503406428103034042030040c491140c000441511a050003440c4801d0703610008002e9406180e0703503c5400c019608a6005540400c1503261902149035040c00407080030100b000300c200403000e041010501da00c45900079901805210345808030300200810640d40c07410115070321082545414907000b07886000145c00080801c4600a100f07a149000b805580d12034040035004a00315a24a8000c540301c140300ca8510009503000004000582c4083c041c4041625021003a01c241094686c0010100c0d03581c1c04c0701440c81071400c001d200301e00340c0100c210351123903008980454944140040032005101203174824110001e07105400146000b940311014038001458804103e800e01200040e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 709195161 1250 709193911 709193917
    0x120305070207050301020f030c0318010f0218120c090907091d0c06031506070c03021f0216050603010e1807090b03010b0901120b15280902040e07080a1407080f0903 72
    0x451f0328901440040c4034070041c00051a8485041e5a1044800700c000120300c2c00c5482070040b24140030740000d0103068030300042d00e89030a88142a5036140c04c1c6482c1350280d9803204107441c0ea50f0701c07490104010401c0c0305010800361014215004080040711144100e005070076004010741501d5000b5500f515115107402400e5078400d100b890851000b4083d0714080020951103998101c2d840302c040c19021025888400e803203c9103401001c19a01445044000a840d106840106101d0036980d144103002a0312900306590448148900c95015501c1d07007058602850061408101d040c8101d030320000e0428180e4006c0001c2d000141e008000500c4091b05020403003009004181400e42400c2d06a000105180c004030362081000b8058220f00e050407000802d036003034151102025200055003d01e00b405007440e004c00600b01501300318038242c502006404890f0005004000b400032450009114100d250030000810120030403510321450042006854002c0c19144014007001490005d00074103000411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 709196411 1250 709195161 709195177
    0x1020c0a0e04053a3f0e0d05070203070e0712060509011409070c1b0302180f010302121f0c021009080d091103060a05060306072a060912030507020705030102 69
    0x4100301c4c80203020740c0c0301941c94248080d142044a1040100448210107140d4111451030b605c140c0b5544a940c0604c0b01509801d1030042c00162030407004100038007000900880e8480d0300e04145454032082d00004c1d0074903021b9032140c041c1022440400803185c0c1c0c020030804010400c0401088826102c2050051101c02400b070f075850b040c1e400360315070b55611b44040c1030382d40710100f868007466410955030795800903134008100c500c1c0c1c800f45160510851814481031200703441c203400c4d074105502c1c140001411180c810300c00640a00c460400000036408180700030020401a001101c201d0b5100c0c0700030b800281a03186045005010701411701014640e0750241064450704554000d04101e607070328107500200a00311045500001402c0400b100780c0f000d03c44644502802c0c0000101441d000c001d02d410904000d042c00c0c02c00440d03c04019219420891070340480d03031a400303d0a80e101c22894150020207040702d0207000140342c00110401c141d85a04141d10032640b81c0d0980706040d41d504189400c0c1d0084400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 709197661 1250 709196411 709196473
    0x2010510080d020606060315030a03050a030b0d02150313050f0606010e09070917070918030305061c031421060a06050418050915090a03140901080703090201020c0a0e0405 75
    0x13000c69200c0c60084059504045a8411600d501d2000e40c00030b4900500751004030017092010807c0d1000d180c00d40303d110f600d40010303907041d807151200e0307400660b986803a101e1500803403030040301080411103282008180141e01601b10345412008440d0070f60741c0d03c8200c86050004400c00034070705281c2840082745004002c0d03512507040700c0307082c9907620002040098003159940300702000016044120301501c0c1002c84548148400c0407268100142035a100502e680d020791850307030102c1e980c01001c02e84601c41c07942503d0301c1c208210501d4245246446601885040311606d402c207441c0d070a0207804c41c10b01980084452140d02030ba01c02c01a50b4500a501c14484000811015001500110b0304000d511030200c20035103008505040343d03655a04420703194100b90380d214065141c01c150304407803400022002700712014100081e2030002444410014601c1d000c064803101084110390003003002a05101004041034180341d00c940e4281042c9030111415038281c0320703040700403606a0a551000c20081d02d464 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 709198911 1250 709197661 709197673
    0x109060e04240611010e0102040b0a032c03120f0601020c011110050103080316050405130216050d11100612021014040e06040b010806010e040b0d02030d02010510080d02 74
    0x110410005044040d2150b880c0c140642060070504840740e00c040c0a0019500c6045003501c107503003c40d08503050f9894200d46a0304c108000e000b480b049600740c4055a4040c0703000f145003540b05140310000e401c1c010105e08001e8511040300a540400b0020702562107401030b16640c9561002840300e4008415900c1c02d0160300030306080c6505510480a241c120304401c2c08889500c54165110002ca0340243c0c0251100c9074040705000c04011800b6100081000500e042414241442c0c0010904900f0a03803a81500f0b90004456180c14140c034013484006411209a514031500c80b48060080c00d819209402c4900542d06403001982240c441c1c5001d6074160305c030200481d00d859081c8562680f500d210030041c860000c2c000385120002c03100170000751040036050211401c0450901094411b1011800d040c03060500811600340d81c84884150011811900429941400008941440f01598004e5058052490560b5000e030b015005240070b0b81a210795008415601c891481c0c941da580d80603030300181c1105e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 709200161 1250 709198911 709198937
    0x1b0c10090b060a051e0f030319230a082802031608040f021002031605013206060a0e1201060302011b0809010c03050d1805070b04120f0503040e0406050a0b010906 71
    0xb0018420100031b403490421000a0000034070315003140c0000c4c00c00540b0300480480465006040c8494150030032209103040d409105520801d0046029413000c01000710000307030071001c10030500c041c107000700064050095402113100c0065802101e030f206040b80f20f0000002100c2c480c0c0d0b041442183c115070311120882e100d034200008501c60301c40d0502148414060304500c4c02c007580603800703103600c220700010b50009103901d100c07598107042d000c81c40c8281103002450802154082150740c080ea00f25a09559014134200a50383d00c0440e0403803d030040840030340102ca00358154410f1055a000740c9a444076403c60410780c0c500215500e000600d0b030035051203000c0c2c955003d0303040300c140103200303090070741c1000c03000c1d075404080b20300f0750525050854207040d4403002c0c8401408202c0c06029a002c00e40e28290409003901e04c0c3e1005128010300181c0c0c03805105090080c1442a0f40141941c1e8a0040490800d0300b0224041c00c030a54002c0ca0040ca0302e0342c00c501c190f003c0d0b01d050b01110001d4a61194048031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 709201411 1250 709200161 709200199
    0x3050a0b220507180b04091103360703030203090a05060c030f0304030c080d1e0501140114071703190213051e03100c12090206031b0c10090b060a05 65
    0x3e0642414000500c01e0040740c4500c0c6442d4102502e0b60000711500c0d54130340000340c01924507040d0040e1510380c042083c890020901c40c071604040d0000d940580ba040d00c0c01c04d502c2c1c1c1ea40b182200c64038080c051076070007008056021005111101048418801d00da4a500400c26144038170500740502c0c0e84200200401105908051a4083c1c00381c1850710000c840d64560015170340c4451014090159203400b0b00388820a000c0aa520a030640c0408200c0d07581054411860340300440c060605025147c4822003c0f11074142c104c8401d0384e17000804980058000a20059541060780c80720040000d0b000e010981d01528402d50300390400209201144a19200500500e010b4803010150079803a991840021614100080000c1c88010000014024074004000b46050190038801502c581041071401c05a03a4401c1501c1d0010500b8a0703822400c0a8050140c08a118940001c1001c0c002c1d119000b4a0328919808050113500076030842c0d071070365a90001c011504000c2e00a140c0d018500141c0c4180400e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 709202661 1250 709201411 709201421
    0x50606040e16050c01140403170c030a020c0c100c050709140a0e010f14060f040509030a0813050f0601030c0b03060a090c050d02070b0612030a080705090a05090703050a0b22 76
    0x80c481c20f0151802c00c0703410800e825074441d50036041e03038126440c003070004250f40100e103034030303103d2a0810328a02402e14010700b003114400923000401254002c600201c0003a818807102c861104010483e08100c0c00b141d03406070659142c407405031890300540074009010b9005e4002c80e41500a440c281c05416603da620100c000d00c8c810907a0403443d9a83d160b41c40c2800b40512421450282c07240a80480d480c0100c204082d244400814500481c1000184036400c0400001c1e100002046d052507815540d5040c4e21090505180c60054810310400300268403480001c00d00e181a41c0c02515089003c030340b1400400240d11007951001d4012400d01c40030000d18901d80c0c82012500c1d02403501034640742100e00c1702c10690700084000d44c0c4001742c8105100701441d024900b00741c28180031000d14204210400041c10008000b081201400b100046008440d600d13083c00101a1030020408000c50500000080042034111815880d691a04921426a10780031410b001c19410803505003502d6200900e6202c0544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 709203911 1250 709202661 709202701
    0x60906090307200405100f0f0f0905041403030a0903140306030a020f190b0408160612051b0708074112030408070606050f130b01020a120f03050606040e 67
    0xf0168500201d069a01d5015940c06a8564040e001c20117041000b0700c210380c0c10aa006103049100c5110803c0038541c460840c501f1a007034000c0c0061a03503554141910210051101584180000401c21001c1000e6501c0380034854002c0d680d5000c5641e0f10003005110344030070364100340d0640c804500440140341100c540c15007a403029060151a1010801a202481d00c581160081e0070012400344000d24007009800c0b64281907114246880d031404038058080d0450100b0391510355115400200c1906016001b0b61000303d01d01d00c455600c0019003884001600070810031142041c00d08001400d890120041e48459000d03a24000d6000030419450310819104180040050094900003103601513085d01540c800d134003405950f982c6524902d00300c0c6c1142c106800c5a440303000f441004a070140c4400d40c502c84c1c03811451800141c2888001c005034a0320a60600041409095601c5006042e030300c40c1d280c09213122161010b212640301e52007013240130702890043c0c0ba007200d91040080c072202484000c0004c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 709205161 1250 709203911 709203953
    0x1b020423150d0f03030e010501091d010908041203110a230109030207170106080f0601030507060302120a09142b020a0209062e0206040b010501031b120b0607050a0203060906090307 79
    0x400c46d4110710750030b50754243c5c050040c5540d1420780e0300c00500324594260503250420f0003003100008582c1c2c2c40c881c40c0118021401000d02e840c50741070400d070040070351151514540003298401845840d00c214452a44280300c0c0d54080031a400040040050090f02c00c0300d86d0503005031001a041028101e541440c10250b90b00320741d00c0e06000901e0610178030100d210700d00154094400383d8150b09000c0c0c034211840d4840010144108905000b440110a0258219a4500740414108414106070801c0c42500d29a0219401094103842d485c00320745003404c00c0c2e1b80208450704024a00084143c2c2c881d0b1a49001a42103400c800c00900c0d9458011013402100300d20312032a6880020140442150700c41d200c4000b0096070001c000e01062002c062a0a40107100c2481c00740901c206005203035089a2070344211400384030382d00d0754002102c14290840e1140c0c001c0944025221180c60800d280c0d2640a04030a82c083e016a20100324141404074220703105000502c0218601102f40e5554030031881181e02581c0c007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 709206411 1250 709205161 709205171
    0x201120f09060203071707021203061f020c030c040603051f110406020d0801090b0f10140c1b0102061b090105120406050f0c0306101b020423150d0f0303 67
    0x8445a035200314031060380100b5006881c3d1426800107400c0341003403040001801c9240d410020400d03030029254a103c02e1543d10143c03130b41c1f14403000c924a920006003124100f01da80828200701540024a810350040442c00c40b0a0180c5d00410b0200700c942500014005411100c0240c031240758407a524240485103503400581d80401c0441480300d80c00079041680140c03c400b0078104042d43c0f0102c60390240a044108202844508002804458820781558080c403520021818040d01400003081c50081c583c40c15541c40d110100501d440f002c92500e8440c41c8000c25861044c6d07944005055440781028038222040c58443c20400300c0030380c002a44860400c070f410014840300d03040703a00b54103009030b00c99000402d036802c1035104c50301c0780390008041548687e414000c00105070388140d5440561406410550903801c1c0c0d0100c41d9133103112200007c1e4000d0b04210000455000780001c944940880003141810754440b5040041e82c4c0003080c000d65031000440a0410208096130744141200340700c1c0c140001c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 709207661 1250 709206411 709206431
    0x1709031608040b0310030b0a05010b0307030f0b04150302240304030507050c0604030b0f0f0417070203070305030f03041a1b0a02010f0f0c031a0319081b100b1c020112 73
    0x84294000c650300c0d0045c0444020410420100702d20498124282120501a82d0304003004140300307000040124042503184c00350128640759580c070007400f5110150007488003903c034034003410b14210710303102c200e018000c481841c1003a023804d00da031a070186c201216040e2079500c07552011aa1030b082a0420794160144403840c81c20340e44e8000080c0700035440740c0740c041030910b8188e01c40d500e0341304001c3c583d040300d001c80f038200320004d02000000c44085460410164990a943c00400e00d421110f070802007480c07100213268002000e2107070203180304034444c800c0f1b4111209240300004403003400307a0395054100190300d20041444203403000f80c04604828400000c044d803100c00302001f03543d203403000c5241c11a034945442082c8c2c2d42c140900c2982c104944030360000a9519400700c0d07510551692078104818000c601c0d00200f01d00c0c10304a9900c034a50081003840309244107601600c031803041c01000c250324500007068100b4144042000030041c501b084416450a07950015501d1101c0075550452007669086028 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 709208911 1250 709207661 709207679
    0x91305010807180506090106110a08030108011401050d050601050675010603170a0e0a03020904030809070503010608070e0718060c1a09010507170903160804 69
    0x60003000c0d004014540180740c000490820900344a5204101381800100302d0b1030f4941441c0300341110054540981006580e420040c10030b04042d10003421801d00100001e4005030540294081c00b0014003010a1079a8840030008075154507800141a0341142004020500e84800a000b1680c158000c0480e001c2e1a110340010765044140c42e00c0141100088070150001d5248040c40f45615003810300c43d01240384504280050b80c02c407002c03a0300d0341c2c0f20070140c45070340340070b4102900960f4411310001c5c480e181d440c280c85c06038107c05c880ca0f00041180115070003510346001c42100f16034014120100c6501e403078400f140c001d44001c00c003489901c101040010035850034801d6500512440004d0711141d070400c0d102144c1450043c0502c0200070b491040d00c044003407a00b980d101242c04c2801c1c9105454100e1a20200410030749030b03141002c0f03000794200002c1c10819000107221340c4c041c1d039640d6030b840c0d4103148001c6042d005a6041000794828000d03002d00060003070030011028001c0450303604080e965103942d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 709210161 1250 709208911 709208921
    0x90a03031d0d050d02010f05010f170118080409050901050714031f0801020d050604020a020c190b030f010501030e2d100516111c3005060315040c0b0913 67
    0xb124903134412070103400324030350a02c510700800d103d1400c14825545081c00c0c0c02841c5400d40038200000022040c9065151000d5100c03465000c0100c001c0c480c100f6450402c0610b5400920a19051505050005000060601c520b40c40703545541c03180896180c6000b00e401940d00300403e09081d203050284114000d40f40458044000c0c00c5142c000750f90b41c11404110f1080d6000542024001c500600c40a0051600424441c003580400e84684c184420f0001d0440c803500301d15442502d001c4000018003021071240d50441d41070314420380702880035001482d00541e8429060640c44070107660740b40c458841711000200901403056900456207003020341c0a01000f200c0c402c1d00c1ca0b0565141e81040c045c40141c0040782c002064982c0b50180c0407400404030000d0640c0c45484c079450410a11080402518103030707a8082c00e400c0300c0c0542e040d003040f0102c4a03010013403030162152440381c4182c04100e035a440d941014107204030f5001100c443c0e40e9141c07050a0030507401c083e10056200e0b1482c04c9001c2045118841d07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 709211411 1250 709210161 709210163
    0x30114090105070e030712021207091803170f01051504091802040e160303141909030b0a020f040308090d350304051f0f06060203130803090a03031d0d 66
    0x2540d0526042c05080d44c03e1107000c16010703810040003042540f18660b0078540254054900c0480d40541400d0f044c20309003160888100c10746017950446040c04d140c806001140d10a0321031006425801c03094040e06441190080300400204005102e50705110300350303208408c0710780c1e02623041ca6110208002031340d4242d081c4484043d0160b0b1854198501350050400e01c1c40010041c0003007004060400d81560349901014044c0141d0a11a00b08290085e04a07145000c281c8c180003130321041c1c0d03100208a040e0b144800d854408085001c01d1070601d03680300702e894a86040301d1251030189103584200298014036070084c4e0042ca00c0d5440e80204001a018909400e0360f404000c0351074842044982141d01c0c202c0300996555000d208220009000054020004840c2c10101a01c200b03050003a10140c2034502d45640e0700c9041030341c00120a9000005010382c04401a15004001d450300c2c0e0142d6240500b82240b903014000c141c0400100c1d014000400d400042000911081c60246012079109050000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 709212661 1250 709211411 709211413
    0x120302090301020403110f0109180b0d0c0305031902010b22090b01150809010504030c060b0a0305010e0f0f01020a2c1008240102330a05100b07021e03011409 69
    0x200302c11b01e2410503500b651000d0242001102103013480c80303042c1a107010703200340c40703402c2d0351404602003540c0c0703242c0e20007245a403040803002455124a0301b10303140d82081e000c1c4110820901e03103d071041801030181141c2100301400c00f01451007044044100a030001c0d95080d100d5a03104003400108407011390450190401c8030f0a20f207a5049603000400000380180014481c0e4903080c28080083c0e4400140c8043c250400404905114141e00003803d44606a01c010b005600e845280311840d0030200320701402958036402d40d480c01c2400c1000600740e1003890300d144009a9165294410500c402030103403246031000d903040b00746030407200104070b4280b0881c900310b01284020702000560350b95000a84030303401141211200b800701c1040040d540c0da1081803241c00440024051009182c003e184000660001340c030640c1c4203051a107483d0000340000c3d03440c40b1640b150040042510700099007150700c0c840e40a00404038070b002589c0038440000d085c0310041d40c15500e400c0203000c070070300080a45018000e400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 709213911 1250 709212661 709212683
    0x5070606120c170a02090f04020319030801050118032d05010908030f0a0e120c0a06090c030b13152304060b09011a0306040203060d120203040828120302090301020403 73
    0x2c01400d441e9112004a1429640413440c1000140c880894040e00020001c140034160744a910019041016001c05248001c003108007982c1819840160b0f030381295020303200c000c1c00b007a00581101d070043e2240000307050300f040180240d038190070000c41840d0700a1458152001920a0b40d2064251010583e0a85031440c0220a12860764625024582c000c8440794082105100c2034049985070760400f880040c0071400442c21000e40c0005101d018043c6901020410665200d40360801d034000d01404240d0b041800a0000341004c842580e210134070f280c002c1c0c03150790508914485900070f84800c42a040350385810303800b143d003115900f4400c11b010324424500895000078040c24002c4580050b03001100041c01000040642d030000b10889801c0707002070f1009a034075503501e40450200c41a4090040a415100e0b202001d21940440508280c444070002d44814190201c04583c408a0b000818941d0030307a015070074000100c0c200c0207903040c6240c82c10098101b84105d00000e007280c0042e40141c039108401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 709215161 1250 709213911 709213919
    0x501050412050307200313080604060f290f0402191814040b0f030303040c0305010b010215070e0a0e090f010e030307170406060305120702010e01081605070606120c 72
    0x11844207030704068900d000742c11450404402400410b0180e070f20400d0407400052070400f20024400c131140240e4080e100c41c82c4540d604580c65907524201c40640700ca51801c110421244a18002c043c0d0601703100102c801200381940c050310013010305c0e06607158803200418513208280c0300da00103800480d202602d1401d030941a0400501780321140441c047c1c0607108010140200b03024200303012540f110035100010142c411a010500d18400011800d50510021040008000c02c920301242a28070035402801804094001640e68503c400f000120510110000034000c2b84600310020091030010012100e082e03403500b10241d0440240d401c82410b4021603e02041300c6000d001d03a548811445000707620b540b80c4200c0003401c0d01e00f00c100094688030510041002d024454000c0400781d600101074440d5984d8806034061030f03520801e0304a012403100314010026600500d1220300c0703000010420500f82c2909070f0100d036140d011040071038500340d862801040f0f08001544c0d41070b43e944503c48511905042c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 709216411 1250 709215161 709215173
    0xc07030f020606010f11010b030109060e0d110705010e031e0106061107260a150c080c1c02030a09050a080406180f120c0e1f05010f05070809010e060705010504 70
    0x245418400e542c4000240205a60300100c202c50030100c1d850400d02103080c07002c902d0302504400c0d40d181d500d503080c4038101050240550280e40029008011621500f840a00c1654150741c411098409034000510400c0a540504001c1141810040c15141e4010b04461500e03400c00e04c8865000f110b0f2354528040c808a41c00039012584c2d03001c640b0040500300c1c9041e1000c0680d402c01401c07207448030b103c20040c500c03841c810852204100d5101700e0b0024186c0b0300d00c520340d000f01048410350f0001103400d00881c041442c80d0085510000c401c140c002d100580c115180d5002e584042c0450183c075580c0c12030400032460611080103440d00c00da448035901c038a4800000c1000040203c3ea0388014410081049042c50000d09941201c04c0c9054503414807105050401c0c0194507584120980321740c603810018080c51481d02100c0003041f01118480c0700e07807038078011112102840f0580d03000c51003c012003400b1400742c4000e003c0704001450800140c0d0701c8140031a030582c2001c5800c03505a9103c90905c010400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 709217661 1250 709216411 709216427
    0x1d0a09230c07020d12180e24032d0706030603020f030712151b0804050f2a0a03060903020d020f0c0d060203091216030206060628020a0b0c0703 63
    0x41e14800c928240302c000d03000035450302c8940100904140700300c4058580c0310b000e10103031a0381320f60140a01008590f500b10328200000120b40750080d4101c11020741c080072052941c442c0ca680c6019000340000c0c001c110713885180c204441007000f000713031140c2c000100180d010441c00303001d007444c0c1e507010075018658414400000115040a4801d801400c4280488421410404110b5030009241d0300166110f00028008214040c416841c042c041000c1600194201c4001030065110f1b06c01c48040c034040c6c403a0181c40340103820b08820581107201d011668554525544544c0c4034004203e204104c2d50b0b99503410450740000c03011000f5800c8080030010303554050200c0c8084c211000054541810010300190501000200007485c5c1940031021034080d24041101040144201403050ba9407099085203000f00105158100c0051140c030002403401d0a20707405482ea4402c078013104040d004a40d0502600c48858041014118481d650081001c52203213900c05000e0303803915044aa48007a9410000c041c0302c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 709218911 1250 709217661 709217671
    0x706050715200a030209090a1b08160f02010e010606090e010b07020d030c03030e0a05030d1109030604260d140105060a020d0302031e16090e071d0a0923 67
    0x146040303041d09210079855108076800d081c4480c0b50760b4401e0724403070a80c003d000700c00695800052180401a00103020343c40b40e4480a00c0b05c03006220316102c548216100c4c2c03401c4030700102200240540710701840c040c01c94a400b840b454000861092441c0c0801401c41c0d12540c021000036200341030070441c480046c07003075501501001d00040d160050030340100c0c52140c08014001c04000b661075011003890301c03e40c0810b5801c6088019a10188510308240341d50748c000c070746206003491600c41660410a181d800b26440c59002901402e25660b5a440d414000480310300c0d5201c11a108841c9400001b440c8402480c190218003000200003100c24000d001030141608407900449081040c0200f9540006540d00003405514025a0382d603110000c0400b120040308006908800b2003081c050200010242000070905556950740f4040d507442c0c5c1d418880d10261903500218461040c907418460030b14490022440020b0b141d20a999a156125400c1364071250064a031a100c85010392a8896030580c250307041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 709220161 1250 709218911 709218953
    0x2604050102040e130f0209060a0314010b090907080a0f050f0303071e03110d090c15020f010e01050103081606060506030108030c010507230d060902030408030a0c080709061107050307060507 83
    0x3001955070b601c00a110416001c3d2040060100048e0b01c0da0780d080c002c4010310b03480035001d94050105540a0302074014240900d118614034400128074810000d4000200e4a03264010014040503880e1400005040b1344207444501409250380140001040203501a00030f076a02c2d00e58421400c148020200c1c81c1e400300d5010541400541c10100281f41c0940300c1540314176130300040200480c682104981420f9205401c840ba440428840540d0040380c3d1011580014009005014890b001c0900300c4c1c0c82400028000681032006040701d40122960040061255800058854a680000f140342c0c1007680305284641c030000340d012014400f80a09900074041d4100061020400406581046628040803400b1030021035090b865680a402c41c00040801030702c111f64901301400c0ca0292507008844010304c4074108618070540c2849408414890082652160300160a06204560804049050791200e00c222100400d00d6601417240390010101c1d0b4490300d45d0b03480c580c5402c0c0c0304064141003503a60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 709221411 1250 709220161 709220191
    0x50c0903062503020304030f0f0903120c0213060302240c0106031401230c070f15050405071217030901090c0f0f06030614010c0c030f080703031802102604050102040e 73
    0x623800c03186604400009003042540c3d1812034a01703c0b607142c1a68805045131041d40b8408488079080b444e50300209009403000704492422210b000c041d2021440001d41003e0340f45e18001b0b00340d0301d130901500001c0115000e40d00d0500c03200c10b440c0c2901c50079041174911b00c08040b94010400e200348a4102031400d020803a2910f81d0528401c582035a80040030b400903160001a0b500030080c1913002c06050039070018080400440052115008040456040b5001d2180400110340d0641c403d1165690507401208241440311910a9031400c1c0c01c0581445102d640315101e010006081901030310240c140c1e0804006454540480310b14018a20340c485c0b403d0500d4684140b10222041c200020f020000b8204200b8000991400b504400c07420350015201c0c49817404036070200301900005042586c041c2e03a060041e2400821282401108490b00952110402c108560702500804110f20200c44c485803851075100a92910203e10000300d808560700d941c006001e1004007180044503800107091031280d030b9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 709222661 1250 709221411 709221413
    0x22050109180b010513091b0602010b123003090d0e01110309041508030d0204030b060a05010813081b06180c090f0901020f0a020c1e13050c0903062503020304 69
    0x110780305042c000c40340100f43c40b420750451205c45801801007070390b01000b400300c00361901401881c210120301400c0c0c0194204000a0f0b1103241100990091a001c6409030540088104c0c41c61200600003000c01403505160725101c00404c0c2c1503005d5842000110b01030441c0c2c0a503900c0081008142e24459810b11107060f00c0c82201150002c1511a03003035082e078001442c1052100c0031007190382d066011a0680c880041c0015040000e0b402401c00c49104030801100da46642e410008024000d0051500059603000014903610700c40700780e401514000c0c964949803081500039188290703070702340140d034090b441081400844101d000d4209245144040a081c4114400c0c00040580f00c0c0504131410310030407500443c0e003500080d81290820048000c50a5845410490181d2542c51012406120300d0000305008000c40c2c05501a9074118402405804c0c070b04640a0100c006040150500b80301c000f05100303400050718104a61401a90607402b61a121000c4a0911803800b007954009400c160044c810302c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 709223911 1250 709222661 709222673
    0xe120307061a04090c0612021608310302030f0a050319030b0604061101140402061e04170102360d0f120519030e070905062205010918 59
    0xd009a500000114840c80caa07166000480e0301c0468003a486490400800100214580101c0454a56440310515513980940e00c404034080c61940982e4201c6c107114000002d03411400a10b541310021113160a00500c4402c5600c030200c1b140748200c590840a2802e005519081041110355440d1800500300c12880f81c0c0e0300398581c09040d1036132040c1c030700c900c80c101c032800d009800c0f041c440c0d41c1c00b50805e600c0f113a031420020544116034001145039464104c8295800302e1142e0564804d5801820461034100b224500c50b99140540b100225030943c1880041248242034801008031131002c800582c48812440380b60200030011124006d5801409103400200075003c16003121400c0c0c02c40341c080820085d8107140b854555101030007013502d40481c28035000f907604400986126000f106118080d4200d0940036400c0300c001c8480120340c0da004000400032940307140c01c071640c0204060080e6900280d80b012070060f010040e402e0216240e101d00c01800f1001181c03041d0417504020380c0441840f28980c1c1c441d2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 709225161 1250 709223911 709223917
    0xf0e01140108070b0906040b030702103c0b030105040c06020d020307031d01030e060906240a0e150d1103010b040501180506030118140d0309030912020a12050d0e1203 73
    0x204500d130002c124170007181c2d541000d40d001403001201260303491500f14002503d50b1101c10584100c94600319036919901e0300c455035961440140c106180c0681c0c0501d40000d00301d80402c140104590b221020418140c90030301032103010341d208005080b40241049000fa0401001c42017240c21503000348581ca001c40d03800401c006500d00340411803006c618030680100c0150000d1000c54600380726450500c007c9100010302984141ca0b030551003641700305c9100c2d400703401c0e441e0310314040c0d40401183c90074014001c0403480d0b00d030040c030301d1010104413100030740c082100000700b070806a503600e2900d08003100300d0030700b801071000340d10f03088808220560622003036201c05100c50a010360056a2040002d00c151025808900f50400100000030b203c0030510b4804150f990010343d0005a01600b8031486019000b8011203c2c0e556060720354203e050b0414a050146aa0651003a0381c4030b002034200007240300e0810000d0340b1190003034024200c1e44403008005007a04003800b0400e030281c10b420040234020a004415 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 709226411 1250 709225161 709225169
    0x309060313020604030b040b1008030906090108151507120c0f080304020315010f180b091623040905330a03080a03060617100312050705010f0e0114010807 68
    0x440941c005030010511501035070f04001c080c1c0d01e8500c184014403441ca0160346c400c621011200c80441e4176410400d44074004d000c00b40d45c00080c2400042225800f441089134003400003500a1078820f0741c140000d1034032502e2b108880004600042040911055451402c001e52150a090305003a8469030f405402c080b0030000038003c46c0d0040041400c5503000d112a03465131104071044a00c0c0c1d611540141101c0c50540308034101c0061118103044110902c0c0580c0b144103900800081080e80c031041820351041245007220200170854921803d01508524524416810382d40344a40300c5041194000840300e0250020342c1c4150141122546c0b40e0305141001c0007c100c0c100842e0350294a14045982504c00d90402044a14080b071422035141d03043d80020201d030010755648101041d4910011308552068034242c100342501c04046c03001c5801d540b0040000d4100b460b1841c5000300c15200c0703600311150485201801e686694000c051100c0074001c41c800d01c050402d46000d55407402200642c0c0b00900e1003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 709227661 1250 709226411 709226431
    0x1303090902030405150405030a030b090c251401020a030e0a02030604030e19030813170715140307031410180c0203160b0105090c0c0c12010f0c08040501050903090603 73
    0xb0010b420440c003808002c00585034981a034555041c146040360b100c1d00529481ca0019150103545101440c0c03912156014001490b001403a0810064000405c004030003401c2016034800c50030b5200040d0300043c40325650342039800068640702102d10003015a441078a420180e0f41c8410f001d02e0145c0d4000c84d0b45604240d00d8200b801d4100946808507102c0c4001c0040c000d0b1210303141b03100005000803c0028282c40004581c05000300f0303220580c00006030300401e21045035030b110010610000800f09001c419540d800c1c105080e000b0f1485000804540c803c45030240001d480e00c0300c42c500066641e4100c0d820000100050980b2400e115000044200034001c00d8180360301c7e89150b0040900078000c6a100724840720303010080d5070309800c1140b6186400c0c4640e50180070b84400040c2014080c20039a50009011800741920a134074004000c44c600c1c40103454074842d581ea11498400400c02d108465a11525403030343c00c498900740c2480341c01c5034001065910305802c02c00000c03005ea943c15081f070744e00080f985 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 709228911 1250 709227661 709227667
    0x5030d05100b160525030602030c0412061506020d0e040b240324010905061b030c0f0f0a050d050c03070b010620010605100c08090a0b030402091303090902 68
    0x5010218480441d40c060820b5010000311003101e5a64141c2401019000b181261000d0441401c0071080c0da410381020f0100302c0c0320b03d10a00008007590011500180500c020300c0c102a1a0004c001c0104002c1c00102c03461907031808a0400114050f1100c00185828009841c2c440b203642000340440c0680b0300a0361095030341e0103c1c0d403c10380d9060398a43d54201d5032580c3d080c004c0a44595440300354803ea9072031a040c0b8500c00d426250418a003a41c1c5d01070081a0740d00324044e86094140042074000c6c0a52000c4403000e01c5480584603020005015013903020002411034004080c0d000e8181580c0c01d86080360390b0491034601010800005c2d10800100140c03421550b909084280d071411030142c0c100041224400c40000550283d0103002c50908104004c12141e00d03800b0040017500700c0340948035098000d980e54200002c01c0d4007441040c00c8082c01041007500d040000b0000a600026607080817040080101c01c0c041503040030b44030547e1200e0f21090300c01c1240c1c0240c4014264503554420b08008607000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 709230161 1250 709228911 709228921
    0x1e08060607170a030b0114090604030b0a090f051b060c060f1b07120e0405090d08090a0519171606020901090503061e100506030117070503061f06080405030d05 70
    0x210301810451484034220649500e0418801006480c0175104580090107903040084200441e10464a031504028481d41c989851a5140c41d910f05005061500c61a560034005021030030450706185810310601c09020b507a907000d4086080320b9196051140644000d0000c0003000b080059103c0d0440d440d00454881d80d40c1c0c0c8118600c6c059003801907190500701c041900c070100f041c018091255a005501c91006017501a8207100407a44205c4d0341240541c0201c0d51416172034091981c4a401000030015210904a280c403084d01d000310081e141e070703000e1503640c42d80414440e10b40c941c4c01085440c0c1c0d0040745421070f28641c00309643c01000c00a400319500045d0319000760300403410320004100143c1a562640381c0000c0f107095200c030b1042d980d00c060718001c0000f1000b119000001058989c003c08440c2580d080c14a08210000c489401507441e00c280c1402050580c2c042150602c183c20341d54070b11b00206d00800c48012404060344c0003409111058040c0b1000031404001c3d2500d800764804000b400e0703a22 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 709231411 1250 709230161 709230173
    0xc0302090a0b06120105090708220201121a030d05070305040b21150f0102010b0a0e2e17010c080c070c0b04181505010503010b0a0201020c1006061e08060607 69
    0x1c0c0d000102d43c00400003d0070300310f120100c0040c5048540440fa441c0700c1d0355401d00c060740c6481040b900c0c14945070300c074408004420010601c654804c3d0045c0740111401080b0001a000c541644100c1484050759801e01c0f00d05107070400000c20b088055240803818010b059401500c1c0d80030310300442404440c0031a078000c00e0881c103010354140811070700d45107846090451158034100c40071a645400395000c40364242d09540140a200701e4884d003d044c142845144c01000850705a000e0501072100c101c0d4400a49000e280030740f00d40c0c0c026569181411803900e09000d8515000e01c214100d1680c1c0d0400005d45a8160008031035035001244800d01f6a98040f9881d1080107540180c0028401c1d40c03002c10041140038039002d0613601159185404c01011601c1c07000a001c21516101305800101308000501000c1080005002100c02a000140c100321241c07a2031410014503210398840582e072074408100702584120f80c8041007521301c0034610080d200312401001c40900809040c0640c2e4005491010054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 709232661 1250 709231411 709231421
    0x60a0203070b1503210c1902010f18180e010501080d0207092a0203121f0b03060303030a15080706050703080708060307091a03030f03010518070c1e05060f09010e0a0c0302090a 77
    0x11842c00782c1e0038520745a40c0f03600441851f4001a40040c101901382070700070307010f20585440c10468030303600750b14286401c48420007000701e0505c2d400c5c955140c2603600b1218100b4081d050207007080c10080c11072004800c030300070300e0816107501003113445081030281d2000148250020340d001c000c1c031403040740b810500941645180f00d1b5035021140c10700e1610812601e80c08884180700c580e0034008907942d8142d694207e00e805804140c07040c650503001040840c100c80324a62080340d00c0c8515069029445603200f003d18100301e1a07a1003040810400a80c550801d5400b941090303114505040c00c680340c4c100000480d41d00d180c00d004081e40269600d0f8501c1070314090042584400400904072a9100c2014440d060150000c2c4600750007503010010154940011030748040c818101d937038420f44144219124001d943c80601c0c0702c240d00030300008100f008200c082c0466486041c46107070480c0541011807010b421100c1003490000f898000540708000100d00d108101d08aa0301200d00c0c1115031188241030008003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 709233911 1250 709232661 709232677
    0xe060d0c120c12030e0102010c030b091303030b0a03030201051e070206130c151110060501080a050c0405041415100509130f02040305070320090604020d0902060a0203070b150321 78
    0xc00d2001d0910030140e1120101c1c5c6055000e9009029010007900140e040e00e080d400d40e0342c1c1c84011040000c00800300c0b6405090854001d240100b107503100392011800820213074200b500143d444500700504020343d110608071752040884001c00b42d18003010000d44480000e4a401c1c0b103010180102c1c001c2c03040c04c061344005401007001c02041c1000030680075140111000c2245e01360301900c4c0c501d8041c21807a104001c01c407101a1202c1781035a81e0b10030712100800c1c0c01007070101c501c14140b1020449407075901c50284221f000a4559209060503180b6a8144034059140c0c2c0c89181641141d000ca00d40c44800e42d104c082003501c00140c990024020075000d000c3d0b0840115a076480403d002046c000001841030440380100380c2d4030043e110040c020305241c01d00c040110b410107800d4001c01c2c00360400398014445c01c0740e001e1000429023a10f80c0043c105a000e0140e460059001042c0b100078002c00e840426004559521444008251000440e07210804d003203c111030202122450034000b070011046440e05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 709235161 1250 709233911 709233929
    0x320a0e0613110406030e06060a0317031003050106030812060409030525050f0c10030204081f0906050f0a0b0616030f09030807200108131101020a15060e060d0c120c 72
    0x766485800c010700411b4150081039461141c0704c0424414103001001c4002d07203820442c0400034101030300110045520190100c03080f82000c11000011803000c2c401c450146200e0800280d0700c640c05070603181105800350400380b2036840d0415550009812404455450300c45c0c03212241c050040040341114000300c1400034046000742d01c1056070754031011a0320004448100d44125200761041011812401380d40501780381030340048801c1c140072411581541c840d040076600401c05005a941d18820b03117001380c03448204138119505101c84501daa004003811440141c0e00c1c1d5040c8034045900c42500422408041e0a01c445002000ca040c3e1042030f40b000503541010120b940d80805280501d14581caa050400070051000b00443d250361041b000c00b80942d80441100d000d1003115120599007400080c211030551180300c005c00c0000321207103407203c7c102c001c1c0d0f00e00240d0280341810300c4081140051449100707100d9954103000148804d00c2103819a400001c912020350700524080c803601c03007590024081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 709236411 1250 709235161 709235167
    0x130b3709020a080702070303090608041401020c1c030e0a080d18030f120606080711010b0a030c14030c0d06090503091807030e0304051e0307320a0e061311 68
    0x3414a640c0052144148030f83e1102040e6072204001c80c0c6454040c00001e001968151041000b9841068040e401c140a9203c0f081c00f0300b0720000349822a84040d900084a03048030310105500349a0031074141d0f1102040c1414080da41035031603d2034484070500001805090080340315100084a50700c500750240b511558605282c0e454100680300181e1000ba01c00000c001d10f805045088850080c5402c40c0c6543e15002115164a4002c1d1a120900b040300400c2e503680d002d4000300360303503444c0c80c0c6c3c0c00860240c5140a0385d1070030004603840510585072800d01070740c0500010080c0b915540403815030140c0040c4001140e078020300c0c0440c00d43c40384119003036020820b001110900079006a11038020689600c1c1000600e01501e050358580c002c1d441456840b03a000b101d82600120b500c40d0f1201044801400c1c0d49003984c83d0742203e00251042c1d4410302403140803038800802c0b001d500300d92040c1c510089444c1d200d2a8030305141d44207211b0006284a009201c101444d1ba80302000e07400520031040081007080e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 709237661 1250 709236411 709236419
    0xf06020c06010e01210f031e09090f0c05071e020405010b091c050c0f18090102041502010207051908070f050f1b0303071209030f05010605130b37 64
    0x190340d01e828020340e86100d225000000c2c1031801e42d14100345010520980d1003c0c4209034807a03030b41c945000c140135802d00c8910201d5481915061001c1e8022081e140c4a145a60341050f00700c0c4116102003008103442854201820860b1f60408250f851407070380080452100d06c5d16103183e40e055411024025000f6050000200f03248d50380c10b02034940c0700b2050b00d250251007078500103560410204240541550048405c40c441801c21401e02d104014018010b010045440b266004440d10215001340546e540400c041c00070389070444800e00d010401e407009600b0800301d5145c268030b4480e0240b80c17020b0f540c400b00489041003030001c140e07280c03e41c02514410004e11107051207034507001c1d407003030301c2c5140d010342c03048101d03080403203000300f80b22000c050015030604d403030b1b48c3d00c20b24592510000802402903405001000541c61100da200f82403140e00042806881e100034494200818264400403a046c6101c1070001d03150040c1d00c010400501e00200c10600c50f030015030324910403e01c40401c22401600000c0307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 709238911 1250 709237661 709237663
    0xe09070f080c1503070f0509030c0a03051e070e160306050d12020c010c11040903020c130b031608061f09020705030c06070905030a12050d0903080405060f0903040509040f06020c 78
    0x482c564010b80d100c0301c1d03011001c040c0703040502c0205d0322a00401d0800c42e1b0002ca41c2d01c01d40140c00824000340464004402072400207050021030f510455080e03002d00390300c0720854030480320406c15400720b0340103080c00c9007414040d002224000303001080c0c03c1c85240044003140e1094000358020700001c0d00d0340b218030304030b400e02d0603141020410900161050071900c4407694071489058044a402840101100300d00404100151103c19404e90071841030848140150780e81c08010503812805880020303603003408100b4141072001c50350350042040380d500c800304083c000105139107034010945000b8803141e20801201c4060798078250051803e41d480402c51004004000005000a808a00031501190307103e1340101d40203030b6035004958042d0483c1d41c420f0001040d1a01c201094841800c0c0181001d00c00c40da8801100d0b9070200076400610640c09100c140882806215004103040e010700c0344c0c600d0071030001e56481c490303480307080c0c041c411440002c0e06000d5032418141c89560300050a542d2246592840b0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 709240161 1250 709238911 709238923
    0x5060117041a01080d0e0f06041a0c070806060f010804022202070c0503010203040203030406050a02151009050a0b0901060e0609030f0606090a090b07030f02130b0c0d11070e09070f08 80
    0x10108185142c000b1541010010b01c0c56030049184c3e40310620348140005015003540d000c0c0aa5400640602c40820800c10302c1e000c1e112507400c2c6504503600da01102c8441460048240d01c4511a034020509104054403120103480d44c4031401c1c24090aa600c40744041182800c00400e4032001c110074000340809000340fa002040c00c07a000c0c0441820203900c0f0401c0608030301c016203000b0744c1540100400c01449000d4030281000d0313106d40c01650980c1200d82d0f800321030f24200b20b0b00c4460554a91509121095082c8103003500320441260410400101d8408946100c038180280014040110700404082d51040c013200c0c5c10f284054203840c15080304588403030341c6080580e0114403403200a00002d10f0b80103203105030051650001540d0720103032100d070b40c1500104100c10344070b0356594081086c0298442d008071050002d0040d520301750f6071400034410180c101045c0c3c00c084410480404804900500000f0340f10b000c2d01d0b4040000401038941340c1c0070030b01e081855840348402101c490300008420b9004105 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 709241411 1250 709240161 709240193
    0xe091504031e0216030f08130306020706060e0601080105150c01111308030c06040b06010c1e020307090b0f04020f0c06040501060519150c231006090504030804060506011704 76
    0x1c40c030841c02c1c07401c81680c503046000481415030103041000c0010804131801003071054050000c0718641804150925040f0449402c02c0d2030f51030300003590108000007441078034000c2103e103c10082c00d00f441c100081404c0410b1151521070032039000000d8803000e288040f1140359290030000c01c060b1003400642070294014400b502c400284282000420040100072901114080405440f01d96a1541d840c0c0b0550b101a06845c1004440644d100c00518848034040400304403038000c0826400b0341c8101403a01c82c01d50001c40040d41055503403682c9468603040000810f030200c801503200d20203e0440b010700e0051141510b01441000140001d1203410360000d801e944040e41c00110b6507401c04042d01600140d40300341680b54040820718001e15104a07120103402c1d1103800781034a030005d030505c0d0b41440d862454010013180c00c80c0780b0718200b603185c038400d0314010031340300c442405685400d45000e0b0410800520103030205803200d0010703203243c0c444d000c1c200a2401c000c0c82c00c810340c00c060402e01c00880b59804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 709242661 1250 709241411 709241447
    0x60302030c090103020d03030f1103010602010e0c01020c010905040b0d06140106030b030c01120506030715030b3d0912030504060e010c0b0117120d200705070e09150403 74
    0x1030740c5900d041148035503058031707000340800c410045265421001130220b03030040c81c2a030366144091001102e001c401075000340740301d03400410340e40c0c03020120300d0a00710700d2008541907600c41418031001d640c00c140e030401111021a4000f6000781c80c6408505542c000c800000c114926264518119108a40c115410f890f40340c0e404102d0400c07040281070b5620706101101b4003003803032111488803d140940166910180107402c0d10780c0560b95203043d500050130482c01c10701181e03c41c0c0b0450010705203100540b609003008441e1400034071400308028680140304000004020700740814545e034a01606146c2c000b81703401c010820744000350f030034010f240d43c020b07014078070005000c0380f00e0303200301d61291000450380e540250f44441e40da480c0046200c015100899a00204e0056040b01421103054070f0242004e528400c00c08138044a85036580c45944404000d0742001c0d030f405001d404042500002c06030203860010101505948038001014a84000038a0b09000317100844104800c16500c00000c00c0101c10b400b07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 709243911 1250 709242661 709242673
    0x50313060c02010507060c020a060e07051002070302090412050c150109050f04051e240103050f0f0303130609020402160209090f03120403030209030d080f07030516200a0606030203 79
    0x120841da60414000302900242044c03000070045004c07903001e6190108640111102c0da200c5560342801c0d00d181003849400390300034040801c0541014200341410405034030182c2031076030559001403440600070b0005840f40d110080c1241d40c450103a4202c88210b4100f100f2207180010b840e08000304500c0034010010868144804500004ea038112107030b0145503c58080c02c1103014400c6c109100d0448252140424840c0769030303800c0880e000706408034400307220031805003081d811824003900c0c1a441c40c1c006180e40d40513032101045031002000340d940000c600d0b80420508041c505210b005000495000396004d840061003002440030651107070740355442601c4140b12960780c480059110724100030000215007042100050044040300020350003442810014209064240481e10300740d40191003d02188040b0144007441107a41001c175400f02d41442c050001d407603c0c2030011440241c0e04503030028859100c1a0090303081a09602c0d4154162050071580000705c58140040039044038401030303000c0d000301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 709245161 1250 709243911 709243919
    0x4080318061911070909050106051008040f1118010806160f050a03050406090f140615310515120c2d0409060b120a020f040908090a03050313 62
    0x2030030b48a4407080700c0300403800111101015507000300d12060040140c01644000b0031102003c0c8a40c035501800384d40002542070030201401311041c1e103820a0780174800403804220000b02204031418220754404549502a400f800104d60101c4074403491050640d14000041000040062140c2c8100003803c000104481c01d10800d0300d10314a41480c03a400903604020345440c16000390005030700540306400002e8040420317103c0c2119184020001c0b00d8201001030003031b03102d200c2000b402d86c00000080c41c40242d070840100240008114a080308160203072030b6111a000d130351090340c101902d42962000d009602c2e0040c0d844402d0324514840d6449403501d1100050000710018400540c1c203400383c0b15141007000c202d01c6588902800c24440340704e0b5010440c4103066150b07405000c000622400c00480d034502250f0400c1100c040c01c030900d02042d402584100e001d0303503a06503070308040318003a503000a411005040203810351080710302d80da42005000000000f0004004001d00c0340e00408038040480c0c03a11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 709246411 1250 709245161 709245169
    0x711060f060604060509010219030819180b180d0906090b040f09113c090a05040f0204050d0b0703050c03090c01033308060601030b2107050604080318 66
    0x103075003980d0490414002401441d01560007040c5644c0705004035510319400d818034040b00f8040940440002d0006400c0c005a886d200c022500c260080080900c8000c1055042c4901010f4528010b421180c0303000c04104410010405050300303807000b1083d61100200c5200c0988a10304511518001851003030300060380d003040005a600365132071a440c0c111011700d4130714902d002e010b220048019120041000030324146169404c101c0d101c00742107010b02078031803400959001074036030384110340302500400000500c2da803003402e82c400341d5000301c400280140d0105007000080c000c40c0c00c4107030071203c601c10010601149800b0300307203d0030584e0303001e1140740e54405514402d4001518540f00c2940010040c0410f580aa00642031050041001c0134480e03421840302c0f040e0450b0744e18001ca240d07100c40c90610610300180480750b402075003820103100c0c50b11a0004100780c040e044401090310990540e1100c0022018400c0703600130080204030603121903c0701c240740e0b125404940390407125000d0614030521803c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 709247661 1250 709246411 709246441
    0x30414150d0513030f05120f041415060306010f050d0318170307020405070c02150901020a080d050403031407050405090c040305030a082a09060d060803040602010c030e030f16110603071106 83
    0x10421f4072512003150b512004d00000d84100c40b1030140400740c0342c513504100102001c0f8079000800f44200e0904400b071500701941078100d0244d100e00b18106200380d44501003d0310f0103660501d0500403410428614003041034058200301e2203420120012604244000f0140c5100da00071902004280c8540c4000e40301d10110403402504100041c0e6001c070039641170005004040340600585d580594103541c1c0d5101c0da8014004507249950f544284020b161703040c814201034050b2803c0c41c240900700742c3d5000c0c0160085118491003252400c0001c5e05800d41c110544004581c0542100e89921680001420a03481112058102d4050220360424a84504101040d009490814038a46503c0900348007007980040600b4191540342c102c00a10030a00300002d1004000d40d03400040c0c014104a0002c05840c081310145850307078001d00c2180014610b51045800401913503c46141e048103030f1070007040704c084455605034042400320401c2101600701c52803031804104c45041d680642e441d0145441400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 709248911 1250 709247661 709247677
    0x6080c0612060105180613080f01060303080117010204030f06061814060105030405030922061e050607050f0114100b0c06150301060302151803030414150d0513030f05 73
    0x2580d20740100303480754010030090480d0303940e118035103040a44540106180e540306c004d4078007404051507020000f0000134071030001c141d203c1a00030300c4258030b5614018500362044c040c0010f41082504040b0001c0002d504840c0115071000c031880c10390720642054030007842640b1403203040b48265129501002c499104003228121250101100c5803152801100d250700300400483d00c0d403208106039405035507521050001c000c007070a22041c04070481d170844010384841d42d11032008203404041059210f4507940803242610000d40340a51100b02038201145440c02c10000c00354103504e0310020100a184501d0a01d200d0255540180c19940d40e900a24485204054a0008a421800115210000840b0a425803030380c020004980c0907103d80000302c1421001040040d1518001400d5401980043d4100d000000403001740d4141850f0015a881c3c0e004044079031441b034040403000e5a809030940007503424040120100300f0246c9448801c150340042031150503008a0079688855030900d11442c1252001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 709250161 1250 709248911 709248937
    0x12150c0f08010308091c0501061401050a080c03100e0f09150105030307020906060903070b03090d110a0312021e0909060402031009020c0f0f0d080c030c07032d020106080c06 76
    0x26030320f107840724a002d801805d9410f92081c4890f001503004107540d80c08600080c0954000600340346440c0e09000802c8502c00384a042c40800e01500c5e2480b078120040c194000daa001034030b50780790794880d0140e400e000c45070841e01c00108aa4140600d000503941080e00c0740c0550000c565411040e1044070294507002d11078540e040e8010001d1070018105428031980050000d005141040c01d083c002900308815034205c100ba02c4004020050100000c1002020340311007801c1c001c0c48070446940c0c0680300c45131008050184542d480c100c01801100b03604445107000702142d4602c401c0c4c0007005140099101030790f600d1140d110400416014076240c401c481c080d01c00c142c4081c101c6844c02000c400603400402440e400c40c001c809030b03401550002c0c40034200c2000c5000c05230061280c01c06018241e1400034040d0140c40c0d1081c810044400c044070300b00c2782e019825080803d5955080305064292140d1031040c16114441000740b0540290150050300c00c0c1c0f15903901341d6180888440c18414a401044441400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 709251411 1250 709250161 709250177
    0x60406021c05070c090c030b0310020a03060509040503120c12070c0b0708010e13030c080f030402120a02010e0f0d1a160c0807032312160206060d0201081012150c0f 72
    0x4954991b002c0301c00c4001342d04000c42c00c040000c0000c1c2c00c100b511121829003940008405c1501039151003a0000b03094200c070a00c585040c607442c4c4075540d01035001c854030200d400102050480c1e00b00e105840491041e00850851440e0038000140700a1008c4800c980e040901c2010417642030083d008507040e01d8074450314040340d0383c40c0c22070418a8038152a0903011b1082c00c036405030104038504014600d0050f0520b107240e49062500c18042d208180d00c21500d003030340100700b007100141c1e44000440d500d25070841d14103a0030340c4030720000b410007071061200600c0004500b070301d40a0b02106408861040d201c900b24060b0703001004030241c0b60326859440051285200b04940c10001c0c1c003c500e400d4910540040e00d45502c80c02224508070303a404403203400c00d21155070040042901100308601a1003185201611190403d90007141503a40b0701000207041c41900300021b08401200c02a140040c5400c848078520722440707042c5064a02400008800311908000c16260158044c0880c40c001055a59400d14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 709252661 1250 709251411 709251419
    0xc0207051c03020c0f190806060316030302070b07060216060f0510050603010302150c06100305100920030f0109080c0705010c0b180102190f090f15050c0c060406021c05070c 76
    0x5e5800039070140c00d6000d40034403c0b600d0320041c016090000f5040c140001c12407405c0000815140c58200d1a1a040a5460200520019a02140740000c403096094041c2d100c2c465494217801074054002460755402c500c036200400e201e0a50051801c52072000c908100c1500c40ba01c841c0c003013424601419402550030001000141803c071001c408803910070000a0400c0340803d00f0300d0405805807144020400007607010303c00e200080c031030840350341104202000069001e664800e001c0503c1d425100b01e81c02440f01c0700b0384985050000c50400c4070304000070405014030340b4181c07049411207000300e009486511008540d07540100f44070392942d030f00f00f29aa13210b41d0b120030350308065400e0b03007000094a540a1001150b08603000500b204409c4072a1902b80440702c4545000b001091f41e984142d50745110050100400861a4402803010120b0300e4603a949044454400785403182c0703072480715006000043c0c0094000d038040340b090100d442c1c2c1200542c45020a040445140c0204030025205094040c401c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 709253911 1250 709252661 709252669
    0xa050105153103062301030816020a06120e010902012c0901030320120a050c071211030f161214100204050111030f0d05060a090c0207051c03020c 64
    0x40c80e10320719039003485000800c16088900003580407454035810b8000c090080291901a524015108100d00c50800b40c0030320380d61030458018030024095060005220102e44d04c619507014500d900541020301942c1e403044000d01c04504d081c2c042052900e4114034181448041c0901100302e0f805a5684004040080640b5071540d502e0102c0754081c1884000203104c0d4460500c8180214066100c11041040c1e11041d81300400d044541d89040d90082024001d03510001c1d0241c40c00c074400b0b0b24000c0d03211404103607a10300e8420a5041603640c0840f0759541402c02071401c0c1c2d407083e0b5100c1a02580d108481001e02655107070001c0d40b00a0b0100c90640c018030042d0640c0c1c0075286410701403401600c91041403060107081c005c01551900555400003414400c0396040f0803c41c00030001d52008502d000d40800749a00d55000e0828010003c5880303c010841e141d5446140c0c6025001120741002800d520044c00381d030b02c0b034807403113094010800100e581d810940c240f02d207800e40e1a05034000e481e41d221007000300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 709255161 1250 709253911 709253917
    0x2010e120c1c050a030e0105250504050312130b04030c18061203110c1002030d050a06051f030605010c0b04030c1b0e180303072709110702090a05010515 67
    0x81e140314403440038405855080e48007015040c510760380350184c0da901107110003004d4981d9005038a0050b03051000b40600b001c04584425549020321400304d0100c8130007581141c8510695002c82e03070600c682d03a050100182e03250f008000b500f40010340001f001e40d42c0c1c980182c1d180504e00c4060124149100100807800e1042a030103140701c040380002400a840f80084100006440001ea000511140f600541c0420800048000010884101280d480c0d0320303e00954a2082030032a01d2850384030004502c040310f66800c280044d0000525030b0701900030104190903032241418050000a05020700002d01d54068103811207001e0f0402c0c00c1e104030359901d03107080c0d403183d47c0b094003220340b6030030000c10071850304001c01d11070041c0038188048402400c021078840000c0001d001c00e400703a900b0400c107101c12a6005030590098080301c2c14002202c0d2056000310900b4102c5600200c04282024480050005800d00a245103072007200c2001c1c05448011000c02151824041c160300903482a0902c0700b03c1e0071035809 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 709256411 1250 709255161 709255177
    0x40b070204061203080906061c030c05160e090d050a050405040917030c0a1103120105090c120109140a06031e060b0613150305060a030206091f090504060602010e12 72
    0x40461090382d51400c0d0f83c164034501c41c050700004d800806002044c0800d214103500f081003102c50300a02c50044646985406000600030140890341080a0800c9400d100c0f800a200a900349460642e590300c0080c100d00360225840b4041d4011000f079880210700520550b22201d0403a03455504290800040c080200100e40b000da03522134181c4500c00d04289558010f600c1071b071082e030f185500c8000c020170107400e10290008035001c58000b80080c0801d40f40c0130701e03403d04441080369128141d80f01e01044e0034292082044012552860384000710390b049240c0c010b00c0e295a058050600740b80d40e400c41000c21100c113808010701c60803405000d03541000c020002800c0b0b09004100003c0c0c000c050a00240240e404031035510004455001c0030454203004000c600c06400090406002d1481d100001178403010060200a10400010440d4180c90302c5034000140047c60203130b00d100301d43d0292040540188120f2050600c00c82c14214003080803072042c0941c200780031130300c8014101114a01d10710f410681100c81 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 709257661 1250 709256411 709256419
    0xd020109030207092c16060801030f111807091511060f0903132322020f0d0c0309050705010c03090e0615030a1512030813060b1203031911040b0702 65
    0x140c020114003048940b1924200010010480f11b41200c1000354040001d60142060204220040010501c2107603908800b0b40d1010281406000c243c00003480051007002d0100491901010441800d820011903c1584c0b01803c648031007030f4003580111020004d41038171200b40d0700080c000c01e505c841860300031034104960780140c80c181140f808980e0710f8a0708507841034495840c001c500021000c1000c41c05201c1c01401e9903000103030601c203d00a08903a4020300403100003503001031020740454014080d20702140c001e18043c085541c0700c100050240c5407010094800d03000740200002d8560161180c0500640d00d43c90380d4026a01d0001c060740c188600420300703600000075030b40030112007048030000c40c860003141900140064406c441c1c10715071070490b04601c041c4e02031808084003007034000c04626840070f1400150010070701c4524128000e01410b100c000d4125500c03100d281022040031004c1e621500300c40d038000f07070b441c10268003940c02c1d687ca008181c0f03007058040006100c50700e01100101034480c000341c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 709258911 1250 709257661 709257701
    0x102011407271410142d04030203070b180402040320040509071a0403050d0f090b040501050306090a060305031b0f061605030a2703030c180b0c0106150c050d02010903020709 76
    0x3410044090380f00c240d2455a48502e00810049440041b0000e81e004030210309550400e030a50340072036a0b80b90302c1e002c0d60750508808210a90201c0c190b40b04c6110b2500003500035503d9965902c0d02d80080c1d52070b81128840e03030b5100703020f0424a041500c6528442c00303022000380790b0a40f03000c0c840024941c40c1c580c204801c5004000210200300104120440c8031100e90790303000d0a080c1070000810058040c4c00c204a01c00e4108420071803680e1010940c0d03003101040301d0b240f0254694600f0f0304020303e80790f48010700a000100706054880e2500800060100280e81658078203920b0444083d00e9880450b40f18a48007000c0122001c020722810185a020203403050004008903103001340d01a020594428401d5080761080700300425070316014075502ca13185800c0450011a5000c6050035100142c00741c00804600800c00003207403002500314a00410740d00c20005c4c1031260b6510001d010960302c1c1030550782d61068004482081e4414450a0f0342d107a0160702404146041a2801c1c000c0e06c000c54230901180e00d05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 709260161 1250 709258911 709258937
    0xa020f12030d0905060f010e010509010b2d09030c1c0b0403120501080d0e03160e0a0902120604020924040203060105070b1303020f070e0a0b0102011407271410 70
    0x380b240e0070801e40240002c1c403072490240000c0d41b81c000160845119142c408004204603100d5100b014151900b421485031034078064007a0f44003108941c202e001d9007005400681c05555085401005121002e0b020340b81031010f100140700307128801102081c3c401903003010103008a0034823110190010f1091410146440144144005440085c1c004208680020001d4201c59802060404014906902034901d10340860308148000c407591080c40d0545000c840001c201c40446e5200211050380141025074030001180c845a5840045900324003e10541c008a1340888030b003200f903500400e44000e0340100c4ca44e2030b403c2c4000394002070b0005040c88410b010301d500184c040c90000f8821002c10304413503072034080e03802c0c020302d0407441d4200c00303e80380c010650511107070071044002540050b20304004161740c4d0860740104d004085680c541f100900d084014401807983c0001011400d540d40704050303d1510742c501c0c1c250302c1e4400ca44681c1d40740e01160800c114a50521102c418160411030070000f03840000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 709261411 1250 709260161 709260187
    0x301090804090e0c040e0a030f0e1306080106080c030a11061e120c0309070e040c0f0e1006030b1305090c0411090a152106150c030f020a020f1203 64
    0x4070750000d1103a241c584030604400d000030012038219140898080c01180c42c40101a5120202e50070003804104018800342000b9000321450070030401e002c1c05000304c210156401134018546400ba40c2c00035401c000001a00403400510140804802000303400e240b201a55000442d030300203d04590061810300400580001c8128902c0094258071011356640c40086041c04101d1001480712044100510600004010018407002903503419a1803050580b50740c24000c61862083e4000707840c4001c240f030b01141d50401909898001e16800f41c4c03500c4101d8449000340d090b180c540300d6072500182c15030745a080421003900070541240940e4191412180d5010100d03050303075507020f0400c070138840001d00e10f002c506010f1009001400c420340c2c00c041565030414010443c1d0207100d07040451100301e01600c3c01b04a4160701000081000010440d00000101d02c05030201c48008400c0c0c01060604901d0300e030290000c40c50100007a4010b04824025031010204440b08101140159040c40207120a034902c02c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 709262661 1250 709261411 709261417
    0x12190909090b040b0f041e050c040905010e0d0807020607050a0309020a090c0e03010509030927070206060a1401091a0d021c0b0109030809040b0f0613090b030a051b03010908 76
    0xc09404003010318541820850000c0c0c0c00078182d040c0b41c02d802000c000103c2c3d00c07d00700c400103000f000c480411074040c1d418401d103082c496001c0c03d9840b516000c2c2030000c00c901540b0051900c001002601c2d05a281101b003a201c0c3d410840380c0c080581c002e2400202c52610580c01016518a1400c000031182d4590f00481c0740c0107819002510b1255440041c103e59582012104c040003100300c000744403030314002d16055140c0c0156410a4040e00088051078043c0260030101500002e10108600b036525007044000e584407000c1d20854002d0840e102c0115200d01c80303848884422310181c41d00003075903103401c0c200240120500c1302407085950a1010440460050009114104c800c42c03a00c0600d071740d440c1078001211105040c0382d041c40030780316007040000c0002d4151b032545202200d0005812445002045a0040b11004150722060002d4080a030740480042c1600303680c88118104101507c4000f03050f616503824401170314547c4030007081d0302c5109214038140c6030854041d0001c0741c10300955485c040103030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 709263911 1250 709262661 709262663
    0x201031e0c091a18040902060c0d05090112090f030804230303010311040501081506210105071205070507020d1e050a0b0604090c170a050d09080601081219090909 71
    0xe04500d80030854480011000c180c0c00c01108900d80c50510092034613a0300c4000c1c40c807010701550f100c10100b41507688520503100c0da0521030b4103076102030b480c1c41001421a8030004c08140400c0b902c0034410400300f160721805503102d511020301403080c00261410345560000900c201e034540e0b076146012402e07110002018405104407002141c43e54118a0315400b007045400d5164000c1d1b281c00f00400450700c0c0020503215501e0f8209100459031620000300784148030003603801079207070203d090b030180d07240c415070102d80b05d03e507155542604141d04c040b000d42038480640e600c070006002441440054680485a0360880d4842d461120f41050380c80082c01d81d00b4610503040e903854010078034240500c6440a82c5941c08042190b0800840c400c07a40c0d0b40c19406a80c0c0145402c0e81c00c102d07001220003004002031101542c114003200c00f561048840100103c01600035403405000364000010961701c002055105240c0e400c071114105070b80d00048a584210020b00501040456000000e03140042e03c40c0003541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 709265161 1250 709263911 709263917
    0x91002040f0e0901050702190602040905010b0d0b09060a060e011e02070e09060603060121020904060623060d05060a0e2403031908070c060f06050901051c0201031e0c 73
    0x7035103481c030a007110841c020003083e07040c0d05000c1042800e5a001c640c0200410050031001c10030542c0b0f080000081c0159001503480070b140c41c0c000324040d9880005000d903084e10381400d02840030324200340f00544030284c51240e084001c281d02403240354060b6040b264103190601d41800803204000c208103290548201540160300595028440c1c0440d03180290ba00c106401e0041070642042c001207660b40205105000160b20031000c0210390312b41d4100c5c0203000d035030010100c882c1d50070300f42460300c0185410310480c1e03100d41d4013078801044400c0780c3d0516101c4141c01440582009000303903150000d40401041c3e10740c0441c100a0210f914011940c2241c0a904819414418500700c031614564200c2d800e01c00b240300e0b50003809048980090081540700300721180c90001e1040d240c80c0c2d800d6440005150000309024100294064081039a62184044603012184110540d03078420600c41c0450b1410000700c03180c0c0800c170340a030165000b074015112140d000c002c2100c3e0780c80c90f100101c044502c615924400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 709266411 1250 709265161 709265189
    0x501030f020d1d0d080103030c0f0f120816090e0105060d1409060603070e090a0f051e0a0b0604060302060301090218041407030c111015080115060f080c0f0309100204 73
    0x60104105010801d00e050502240700c6d4119200a4800002100014440d44403103a8000420118a0440310101c0c2c1c04005142401c21003a00680340e108100d070041c450551307141840c2d840314485c14070181205d0089010000507402d02040c80348aa00c014a5945d540351a242200014a002c0d03015501c9280c1440140505040482c1018100051940000d403401d5618040c440c100f400443c02000d4503612864500d80e104031031034101e04040c0c04040c1429090f00707510804104a0020600300d54003441740c1490038282e950101007104440d0385001c042d40060341031006000400d0369078001d0100c4040d1843c0c1041c0701c5090f1000400750f03021116041e042081d6401884041909401464401840d604040200d48002a18580e8482c81210682402d0751111203040000b0002482030018001e42e03402481401047c3e10348207600030240c820700000900010095200903c80c0075098080c0c1c400c401030303901d802d880c41d0345031041e40c0000d400d800c0d65025180700d8415910144c4020002001c0c000c03001c4c82 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 709267661 1250 709266411 709266461
    0x30510180e0303190b063603060c0717030f07120b0405240409120c020a0314011401091112150d0c080c041e11071b210c0501030f020d 59
    0x1130b645e15155142c0030300c20501034040d00310345140745016900540d6400700c6103000c0d455a40d020002c00ea98006805004d4071003072085600d8502c0c01051068007904a0b5140c00c2d0030784606144034070040310390510342075404021500080c403d850b0034110210459000c00e104107100c0014044032016951450078030f21108151190400b4000c01d66250b900840c4d041000e08000d8842482c610f580340400410008610615401c5503500c29050000c0c5400c080e001c281030200c82d80c004d000705101d040064800d80041d000080c20000b03400340070b0742c500e000c2d85098280703a10321600101803080035003a00701c0385507592424003050702c903078003407161040c0a00d1034059850b150019107410246c4900c902d071b000d9070400013900001c0c10b41100c04140c1c014130707a2002070340040c0355507424114040e107000200b181075080720502d802e803008100d403c00d65100c0c1d6140000c2581000d550704041216036002001c0d141070700c808012070741c000d912105802528100140c94440c81c2e0240c3c0c1c003140c2850103e07145070160020900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 709268911 1250 709267661 709267711
    0x180f07060801060f051903020313050f0109020901080a0c06031d0610060e0136080a0609020a050a030f060b01090b0f070b0f0615070f02100c050d030510180e0303 71
    0x149810285040907450100d0b10130070991142800c511ba9030a158000012405007e0030308084040383c0e030418181c0d00d0030500c02d4030703807806450301c0c82c020b91042e0320000020403001e0002c51130380d89441d0300425550510740b500009401030903c5038422071190803021509420a03000b800000c0c815104030741d100c2c6030b8070b040c00c1000d040c54001c0c0803190f0411000c1110b46050f244083e4000c0004d00c070b90321002e28a2202d2011035100342405400144c0c00b030051010480410034242c001000040c421900707020100d807504148082c103c4680700c05812281810603450214400da841400800390624190f0f01140e21100c070000c03145d000142030255828005000014803243c03000b102d40140d11605869030908048002921020784049042c0388040300084040802c51030819500303071785034003820031a800b07500900050004511208147c602e8010b208194a0091084c45400d119040b1140c4203000d0b903041600c2d0310b81b40c141c130899541060b03503180209080d010b0208003552292114282e10311032803140c41025 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 709270161 1250 709268911 709268927
    0x204030f0b060406150f05090d060903083102060c0109290a06030c0b032a2a1b1302121b0403030203030a1a45180f0706080106 56
    0x80308174840c20983c4202c00725440b008602064800d443c103552150f0315100055510f041492005100070302c0c1c0800d00c0e0805400c201e00178071514640508a040d043d82a049a01034107160004101e0700d0f40ca880c00300014580746014101c8600d150000042180c01642c0781c114145455100042100e0b83c00a10070005000c400c450f03901500394141440b45916603980c07910701880034001c0d103603500300c0480021054000147e40048082c9000310000c507413821180408001d504c0545401e0181500d480008208110078910741c0307007485040d006284420040e504001070314038000310035900c00c148178510302614020b0b0020301010000c1d5901d5610f10304083c80707204003041e0b00d4486d000c0000750510040022a4020041c4d07a800740301d041000c540c031201848900e103c42e004540c0c095011140741c180c00e54482d85008200381c202180754008144008491800b0704209690140820410303981d400500910100700401044860320070845944500100c1c001d802d0550642120340020302440040051aa1003421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 709271411 1250 709270161 709270169
    0x601060e040606030e0606120f011505010329121203090706020105060910030b0c1c05040c091806020d020c03120610030903050306010309080d181109010e01090e010204030f0b060406 80
    0x2c0280c80011180c2a1b120a0010002da10036401c406900900b84428802e000b4003c2d0090000c00032144188107030804103d10f0b0013007600081c9050724079503249110041005003901c80045081c540c5d2599820015128034041910000e40034450303580e140300017440c0186015403980c00c040c10340303103080013002030131950018001807040300e002d42441244003944846c201545d810400408643ea01d0b0303150780c683e62040a0080c511900c4004051200c000c00c4c0d800301e070042c1d22034085e035003804d540e4203290000d580d2a04854070041082c0121000010030903402010320394400c01c0c0140c103100700c58928500b141c11410b1803052200902d01000300a251141029003000c660303003810425091a510010207900000f081a4141980c0c1c1c00403105019050043c0d51602e0300002c018010b1602c035000801130303141ca40c00c04999072007070310400451915000f0b002c1da05984072104484080e070700e005000d6000c1c04000c154000c095508004c080041103106120b0720145010380d60001c0e00d81805410300c0201c5500c1d42c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 709272661 1250 709271411 709271417
    0x60209030d030525020114040f0b01050a140609041503050604031710050d030e0a06050414181306020408060a09030f1815031b020c0109080f0d08180601060e040606 72
    0xc1200050082524800720f65069254100284e003421099006003a103030881900c0102441c10041040080c0760307400102440780581d902543d0340c4005000a210050045e030b060528801c95600e0142001c0c005848956401403020810303504212848440e5040740d002600d0941014003008141a00000040c03400c2404d100b07400c2c05840d0440d40840b40708000e010301407149078030798000814180b090040820403800201031036a1191323100800b51442e8054401d9001c8100c0c0804280b406182402c107084482010b10713103070041662401c0240c20b00c1900c5410071100f0070b509004c0412400401c0050510840038000001341e0141030b810040c227900d8044601c3c50410000c000c040d05d462401e41400011500035880050001003082c07019000341404016460040c13070400080c803810b5a00250101d0a03900030b8a424901c581c40b01e102a89450308500f290f542a401611300e448c1551040c0781043c1d1100a0040100708000070080c00e6081460a90000340060303100c5c3c0310a0315500e041e105800040020341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 709273911 1250 709272661 709272671
    0x2060604231321080109090510290d08030411060d06090c2a0803070507020d0b06091015050918040302010c031503200109050307240f05030412030e0109060209030d03 73
    0x4500100703144c8050240130320b03d6440c0c801440070402d08000b20034010b0600402400184880003040c0c0b03804004c6803850b04511108080c0410a081c01d406035400d217038000f1825072465480f03440f483c600041507001103400c02d40c10031401c2c440c10035078030800000d04030344a00818100901603008144200c04503001003030075074044119071450700c0035404400e840d501080054480d82c945070280da45004010002e0340180c030240d5110b04000741021213030301c16082240c40301f440b40c56042c120018100d440c040c02110320302001c41144d507d07009101410400400500210200c50105160500b90b42d00b61003c40c003603034580d2208100c42d50140a1070240699103103020110a00e942c84c2c07814110403518a001004511000014441c2d00c1080c806001e05006401c440000d69110714139075000300104902141d14020501c5820407600c00d402ca65044503040d0703100c03400c5440d95160811246260384451041c180e68105600c2e03000e6081c0070f50ba0650b4025000107072641516010325083c64100d2001e042010302d40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 709275161 1250 709273911 709273973
    0xb070b15060d270c15020303040f030c020f0402040902032502100b060d1401060809070e0708190609060609050307030206030705160218070e10020606042313 69
    0x12003070302e03100402240041090450360419094840c141400c0780d20b0305112200c0705080c4003080d10944122045400801d210b43c0c400103041b0785a0106a800410280d4100036100c00310f03203e044040d180600042440c040b61841d0f50024049034410390090040c02c1d004410440a0b800040e0280d05030391f46040340311110001c10354002d44583d02d90070b41318107141e600c00c0e04c1d040a440760002d40b4084074208500f080680d2a4100b01180b84000348503040c0007414000006544844c04181c0e20221101170711900e040343c580c41400d80d100c403030041c04500d034840c165080c000c6450460180c0c4008208203030000620038100713203009002400c0c580010740603500c0014100010785811b07003241d81c01145482c017140c40d1800000d142c00744040c6a5800380d441140c1010415864131600e01060042600780c0319407803811041341c00d2002c100c1402102d00096001030001890a003401d4025214a514080c002d102c0e80380340d0482d54012040036140c141e9007106d000c000404005582d0411041c64410b01c80c000348950308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 709276411 1250 709275161 709275169
    0x180613020424152604350c0c04150501090906230d0804080c210607030b0d0203150109150e070327060e0c0406030f080310030c0b070b15 60
    0x4070f2040f000500003188900c00400d02c00c1140251800081380341100700e1040086100290348195419607500c140d4500c030101c2d40740c1c20030060b4030f89460109004540502c91000c540c540c0c000c0d138002140d13405000040d258503940c3d4407400c010030100c550451041801c01c00010940941900140c20f81807400c0400d00c070010168000c10440f11111015688160301e03100030500c2e2009060000702200c501107008102014081000c121880068031140c0c400e60311109070034a0600914050f803460741002c008600d50903c0b0b90400120701c000034240c1c11080c409a40400d00c1c010001030140300318141f2400500c241c40c1103000d4140d09064180881403260b0030080c00000399031015001c5000c0c181d4580a0301a444100c5600655a040500404c8041c101501703099000c1c0204034082c4a1500400545034101d02c1c1501c2204281c4c0c0d08250f101c41c2c0d11040356110807255001030502e5182c1076850710000f0000d10740b20083c6020308403001e04192540c80e903140103000b020014108040c0000360450441c02900d07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 709277661 1250 709276411 709276481
    0x18050609121321051605130b0904060b062101090b06090306010b03091c260106020c0409080d11071109073c1809020a0c0206031806130204 61
    0x12500415483c1103103400100d55000714648002d0041c01809455001d04050100d03c604a62094503a0f41100020b01d40e07484c1101c6e140e20026911541100115002c1541070380102499000030740480e00c1d001200314003214084004c5486601d1340c02600041c03010f501a0300504802e2502074510506041540d0002516a401401201c09001000c0001400108208451341c203803010544007000a54000c0c00040421100d40c1d00044c00311001c0c00441e440074211003885040301c3e000e5018002074500141000040d141304041aa0061000d01c00390194800620408038403107200c005080d900c1815141c10b001081c074504000b44a04000340422040b66000034582c0d600319078130032030784515000e52200b1120506c051031900c03008002243c069412540c014021070100f04900682d8903103183d0329147c007803d91007115101d9002415290000006040580243d07400c0410040030a20004101281a01e015411540810001c050f41c40c454154203113840cd01c052448400c55400d1081c800c101041001c003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 709278911 1250 709277661 709277669
    0x1030b06010f03290f010207062a0203060a200304020105041203020a12080106110609190503040902030a020910050309060c0d090f0605090106050a060c0308060103180506091213 78
    0x4056400020304092107039211610035010302054204020125444c0d5024051403000c00c0d01481050140f8809980000340500403500c0b40e03605c5a222000100403405401d04584074480f80c000600c0c1142c00503541031100500ca0318200b2000100626807244a5101c4104510074108241040040c4005030341e2100446056074410340c0140d46038051490100d10303141100074040d00d010404031040e48065403080e9418100c0b6050b5a0310440744080341c0a4544a1800b030f03418130f4090b40a202a018007052240f002605c1902440c1035905041d0b94243c901c042e40e00448070554410b9000034608500d107005201003030f8440c1689019411490206002a91840d000d401c50f8603201000c01c5505517013a0075000201215130000c0600d240016038904407000c1c05094440070602e5007030080109560815044080c11a11035641c2c01c8541442c43d01c0980c0c6900000d050a4101911809171502804801003120043c600c1030340109034518281ea4020f05090b080c14501c88415000c00c4100900c80b01321034004291 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 709280161 1250 709278911 709278917
    0x5160903030c0c2303060709061b0804031209030204110f030f1512103608040e0c1b0c0d02062d1206100f080703060512030a090e01030b0601 62
    0x8001400c3c103003100d42c0306034420421102074404030341528034100003004d01108140d08031481381e1100d0394251440c2c2c0460003400000750071051460b603c006110701202401e07018010517460280c0326221880c0c801c1055000d4070120700b48840030011402c1c030380320302d6044081d600c0c541400c0122840d4541080d00c03010300108850031815005c14070641404482c40c9040c40c00a01444400e0320301c13800a51a1203450058020080c6804804c00c07800060030030503c4000350305841d04650b030500c02d42c1013400300007004080d64404400c0c0804201855018690745c010f62080d01c1c001d440f80c2c29a118180c80e10f4404240e0b090303540001c5038140349074541ea41d0040321158101c1d1629110001100f03800d4088100000c1e049080483e034902001000c4c0020040100e018000e5200c080c1f542e81c0c50034050303110224012040000c0ca02e5800403151849955000d421021038600803505239a00c0c40098000400d080144034980c20005001400b113800504100c020300701802c5c2c2010310f6245458241134254014102414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 709281411 1250 709280161 709280177
    0x60e0d0303110a0306030209010f0605030403080c040806010b0702031b060f180402040b031008030c0a06050618010603021308060c09040522060f05060f0f1908120d0516090303 77
    0xc250281c0c1040c20484150403009031074480e64a8024098691444182d00590a500002c03804003140c020a0f4291242a15410314648941d5002c03100698010075244a0140a000103d105081031020130300816107d003003144c0b00c50389401014105004034400002184421304c0c110101e480d40030998507022a60000d10751140d01c0c1091008821070343c2ea644030390052001802141101c20b56001c0d502803501034041c0c0c202035888040d1b00350380c0d2180417900c489a0f44034900c414000f50107504003c0d888800030740314400314666840220b1004c0000e80028022a4004c0b41921009400e080380d40014111080107001c641070008001ca0144151103001d400740f6250800180310031080700310b0406007000002019004403540c1071020041c841c0702080a1710030300f440c2c00700d0040d240c000c00f03820380c40764010a1642da250000080040c403140c50603a1011500001000094540051149a8054689170006030b0781d03007c00908a0200e503c0100301d1500b10b215158845601c0e03a0003003422060f0790303050400341e003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 709282661 1250 709281411 709281413
    0x150501031202010218130f18061103010803030a0506060405040f090501050718090e01020405030d1e030209010e10030b03150a110a050f0d020d060305030a020723150927060a060e0d 79
    0x3e00b020125241c4164240448c800001060b110310101c46405a1810403071128a841c1d498090701c000e100308403d035802400411071b00c00362030303000d560810801485107103882d90b298049030980342544a0040001d80c2c0c3c1e0a1101400002c4c0140340d446201031030b12840b45140305010302c001241074003440b2011680c0e0900710144060950440b0040c040040c1100e6502c000300c03000604a50756205104048214000e404081a0090080c2c51200c4c40585130344400d008c0b201e0030300400b83d0044141c0d1041644580c5000d1550f282840a540e01c20b05154200c485031402a1b440b0b819581c0c611341c0c01014500410802c08100e500c0010740710f1410780c2c0181c655484504a5510010f401040d00c03001100b1318042002080000002c01000e1082051b02582d001c03aa0361035041c202c0346036000c1110602206410124094a42154100c41d84444032644078200041320001ca601040c14215003d4503010341105441411281100c5590088003118a072402c1428076800800c41c81001851900a10700642c00300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 709283911 1250 709282661 709282699
    0xe330705030c16081005070941091308030c070c080d09031a2a04030614041a0702030910200106062c0f0607150501031202010218 57
    0xd4581d40441040380d03d8800d40c0006900a100244984c01361489201014907100825001e0b40d4441c0d0842e84451649034601903041010104c030f41386d0b0162117100002190400703008502c00081040b038082c901c40d902c070300460500c0682080605078034030582c04644c2c0e110001d101c0c40c045a900001c40c0144a4503020705103131030390801c403858001d18010b008041d040070040d680704003540f00301ca000d9808040441c00242c80840c8180f0b040e1b8002e000c14692008291144546010460111a851000c103203043c1d942e4071101c00b16054000840e0b140840b0105100c24003507007107050b01c021886e801c0d89952904000d84040c2d681e100f039110203070180c07802c0b0861a01d1280501c0c040c1407240060311119000e26000d00900c0d000308640d01819011900d01200c0c01c0c0b407001d030304609210700000850b681c40c2c80c50300d03c410040351000140b00aa48600d080000000141c8030500051880e1b4000d840801e50354110301d006264900c13a107802c081160300c14400c030007043c007284400403c003c500381c3e010b0742e104018001203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 709285161 1250 709283911 709283917
    0x7052409030a140d030506090f0a2c07060923090601111603060e0a03200c0a0e0603060a0b03030a140c0a050a0b07020d080a0b01050702100e33070503 66
    0x3e00000d00250603050600c034007050500d801c0c1c135942e40400c007965885080040145042d500c0b4400b08201c14005120401154000785485000300d181c41c08415a908031150b079602d0701c1005114503007000c2020000c1c1900710296170003816843c1c040210302110800c02c0030450445081031403090420401044580e4024946030000c044185d058a003112240c2407000c00650b600d100440f186450030b0540030340844040b44505071168140e440a0410401c6030111000030704140c207070703031203401441900d10b010b46d01c1840c04401004070401c008001d1812104050034060010049003400f82800b4118a2a1798044222086880f0070308018031000420105480785000e14820250240300b2192404280200050340b41d400c0b500c190740f0030403d80c0d00e80104a8588031031201d00c07400714001501107480003405400c000388442e8113240c041e0030100c8640014a180c03402ea6030200100340320f081c40b000300b070810451445840c2c0100c0d50701c04405d418003800141122112480c104446004101c61040000510403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 709286411 1250 709285161 709285163
    0x906310c0207060210090204151d0c0f0d0b030c282103050703030617010207171908041707140c030f07151b06020c1b100f21050907052409030a 63
    0x1880e4412b03071541c1004000300130200d16110810000d000213a0711020031012209101d41c103a21050038071071407840d940090810b000641b03605009007007905001e80c0b544050841a800d0010030400c06d840f11010320300b00805260002901412500e414040407580542c0c90703050032b40d00d0f00d8043d42e10340903802e048004094030741108600710440104001c00c0c01054001d040c2c3c1030b0040040c141904884000c07082c2901c59040c0502c1d4000f4020b41c078141d03040c003580d003c5038010701910130004110600304914610b9405a40100c03007401401d00b980305002004c01540456a106030002d0003044204003025a0380c218502c0390100c4c000307a940440ac0c0051240c50741c4e94585000f858104c403003a1861030420082d401c03e03a268103252240480d54401c100400b1000a80040c01410702201d50900c8a01240d110711080000703014040c00070555900c201b12912061018120050700165504204541c10704000c001d9004501c60005201605d003181159440b0060b843e851200c415500e0901e04040303428a581100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 709287661 1250 709286411 709286441
    0x10809010219030609060f050f09090708030c0601061407020307031410110a2a0b0604180b07110706020c060a1404080303062d0906310c0207060210090204 68
    0x2c0c868201030305034000c041960030030142803110310345600b100f01c0035104911a040c0e101d030102002801d64107004060036001401441600c0006444035111031a5900005102d0402d41c406001002200d03848440d62100035514014145070007403d0700003a80e16000d0307001c043e151010080388101080800c01801e40812101201400b51103070341050840f564200541d4400030070181d0441c10804010007480015603100c607002150202c1036504c0b01e412500d0000c2081d0f4019540301603204104020240070030243e40b00342c8192440345004200108000d00302000031030303554000304051104540201c4c4c5032102c0300e400c0e03401540f0b9940c108800c8503c10b84440760040e0343c2100103008644a00c010009500c2160195a6103090001583d1036180f010740c840c41c0320000302d0040104c0225440d00840c800c1e00040000c0c055807840000c8880c002c02c84550a0003072040c800c6e000000882c101c558020506203c1c42800076200d16441c0001c0a5210107410400b01c0900e81c1c0d813185117046503255400801c114511007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 709288911 1250 709287661 709287697
    0x90b09010b0a030f151d01050609011b0204020904110702040e0610060c05070506120f01060203070b13110301050a091506030c0612060b0f03150a0326040b0708190e0f0108090102 78
    0x41684c0b1b00316a18566010180e224901c004103903800d2040031151102d006070748046541800f452242c148016000040781e201b90204411f00c002d40d00ca000700d000104002c491b541c1c2d11005441004101c51171440230030000d030010010002c00740c0c0104c140c10110f8101e401c2c6125a20920301e0712504101841d04001d90054022a07001c1c48986454042842810131685210141c0d0302d0307803000d0340d5902854500800c1c031940c0c0301c000358603001050303205100940705521444011301540300207420b444080710b11001c9035a030f644501052000000d00680c81c0071a451003003003d9030450f1541000c00c0036070300a000c18844810000c8845000c41e510003402442e5400145494022021410051703500030390794944503520a800d01711b02032520200060807a42d000700d402a14070802190504c2480c0b80c00105500500c090000007101d02c043c80042c03040301c0c802c401040c2e072a40285040400c10442d10541c9040103440e026424964076010f502c05001c1509081160702580c444007402c1c060b1003881081a001c143d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 709290161 1250 709288911 709288919
    0x80d0b01030e0102161b0b0d0f091202031903060509040b0705160b0403093314070809010305010806011d0c070f1505090c010c11011403070504090b09010b0a030f15 72
    0x11115100c0348249400707a800c1c6421101c401841d4064007c1c1a408403081103185190030042c0d01003c02c51344005004529a1500e03259a41030448031849940035800020720120028210710401501c45218103041150342e091101041120100a00040000e0140008140c2840c000c000b030340e1101d22047c1807080000190701c0c00c13020100307050390101c0205040003000710307001c0021403424054640000c541400c0b8162107132030042800310346116005000d803040403400c2c0c20001c3c2c4010304141d401030400070b5071041594001030480e401640419401d42003a0b00500120303054100740380b000d86c20b9201c10f0741d40c1c2c0c4038240e03003042505c18038500038555003181c0107820401450410070140c0f250449810003c0359100c9100d20b884000c0380100c1d40c00a18605100780006460b0a542010000107252000d03089695184041c880c2c0d20903207803c00810b0002c44e04200c158840d00a0340312000050301c00411700c0d45400c2c1441032501031050f400c0c0a160719076503030600c2d610362a4011040c103000500c0071000c036903803 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 709291411 1250 709290161 709290187
    0x10021e0318060a0b100804031808070806062403101701330e090f0d020a060f0902060f030604090804060c05010e16050d11060f0a020d0c080d0b01030e0102 68
    0x500550700041e0041d6400101c000210348078a0ba442500940240d54440721000b00702c44941b0014011010300a00001d085610340d9441107020180c00707190000d01c2407500742410300385040e000070403440c4240010702ea1059450a00c81207404140d540200b403d480351a040182100e0040c2038004500d240e0140c00704e080b003224150407010388010003401c402c05140c0446003080100d5080381103040000540c80b0b00700304004c202920998400c00341416a058031040410580c10005031010040060740641c10321018010644079030440c1c0ea64400b4100070000307081d40410018041c03190042d681c1c400100000c0d541d034585400001e507207a402102ea42d552031700d07840e01400800964005403041d40c41c040b8940c801e8103002640300944450102c5d10401945800704001c00104c15980403101b03241c01980840c600c0d140d0b000075200c5e41c44280242500c51a002c98000d140000c450128420088003078940030100c1c00f45012202d2006c407424011452000700710040c1c0240008014580726503100040800e0407500e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 709292661 1250 709291411 709291441
    0x15020301030b1003111e0306160f111203190f23130b0408130b09011e0e06252001090e07030b28150203070510021e03 52
    0x220600d400b100b5911540440404081c1ca40030043c441030240d45507900b030b450300c44c0e20008800c8103494140009280c46012a050070340968640d400d1101030400780c0e40854029003540c080582915000141c4030060040c20ba03568002c41444170941400004a4038100030300d241030b03900e00785140701840441c98000b5868000c00101403080c610001d4502407022000c030610445020300500720a19a092010391101d02075418064022a02c0020410103140802040100500207280c40c81006032107840240000d010720140000081103040c81025003014503820030b0240c201c00e00d041c2c4031207071201000100c01210b10504807188070300040c9042c61a041161601031504a07000b911401c00c0107200350001580d440c00036004082c9010842c1000401d403503c42e52007001c01903801810701130081c82c95408403045044500c6c0500050b45072074414481e900d5000ca046a00f121284010340c0350000948500e9140c103060341c4080e418580004000008075101c130700c240e50250000119603940d080c0920f40c00c450513 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 709293911 1250 709292661 709292663
    0x1080741040e0406020d090c030c0302040c050306091603150b0c0c030d020a0f050a060906020a020d09260705032d060105060304060b01031b0908010e0a12080c04031502030103 77
    0x11414090024061000a058404403142e281102c41d0903103d0f503407080c000e90040510311a210b95508005808203114849a00c010744c0501403451456041d4018030050f1294441140b09006d4104103000c83c5032900590b0642c03044002d040f24a00100042d001c5029007070704a080031582605e10800f08540c130740c0800034004215010100c2d11950b18034418145c403105426600005a000008103001142009088120581c4180140c80c101802e40c9d82c0d840855a48500a4407141d501140141400d901001a406000078505248001e1884d1040008100b60a00041c101460564074603240c101c1c820818400034050050a545523101d80703040d80c0700c600c44142c1c0d452070341001111036000c09280c0410703c40d0599a001c1d010780c0c59940c07580c5544000d4458a0345150415543e04032883c000c010010b003a0380d100c00c5a684620100f49001d4034142580c0b84d510200365280c000e02405000101e0303402607914000321909006c0c0c000d0741c50034000c9a060045600240004071011180000b410490340154162 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 709295161 1250 709293911 709294007
    0x10b0406061d04110f0d02220608130b1306020403020411090a06030c141b0a0b09010c050c0c0d0c08150f01080313090f0917030709060f080105010807 66
    0x200c1c06000304010360f054071940c4003004200b00305d00a18030941c2c400602ca10f1603501c101528000314011000040001d404210005124081c800e00c0b40c1c81d4403103034850b0011071016154540310400d4a9a280740a00504121029100403020908010741a01500d0003903400030810000204040720680741940001004da204400c1401c02040444c024810598446040e5540008070003800c2c95200584e48003805441881c581c4501250300c14408100c500d000340c4c454881d8140364200080381e10b00f034656184801c4140101440410030b03a0710001800c2c400a1001c480350440796242d401c103103501020700e80000f0510b000701c0f0150103003080300c020302c0740c00384000e01c22007101d030b0380d071451a00d0300c4c1d0003042f09078005254050020004c002d910707005800c41d080c0d50980007038601d0340380d03590000341c4120341035020003540040100040d058100440358002d00c00e50030f10b4100d140f6101401070454005010b00c6041c441c203d800300e41c1a80c4070f0200d0250f92079502c05403241000f4440c0c120700c9060f849600300e10b41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 709296411 1250 709295161 709295207
    0xd0f030e190b131a0a060918020406060212090906040e030a0e0f1e0405150303040303090807090506010507060c05071406060a1a12130c0e010305060c0403080406050705010b040606 79
    0x1201d903c00301c001c0c0d40c980c100684802800340d0b5030244240210140c003a9891030b494420205190000703104e2003a210b403021102142e5149144140026200c445c0e0000055400c910145031845048600700c030080c10b003c407501c0e049941d5040000d001400424444002840041081e16080c1e8108010304054941124208034147c40c544c10884200c1c807443d10340c04081c10561211166080940240d50800d5000c9135a14200100c1c1002c00d25540180d4401d5000a038869010040e100b0140003803c050041200d00b81701ca45884400680f070752048580003051240c0d203d804100c444d1140f401c0e29a0950320204509500044541c583e0365400151180c80c440c0c1c0440c0d13400504009040d5001403164a10b4000c1741c2000d204c0000312100ea01c00502020070b56240042d03600c00246040441c5015100b4070100441075411401c28905d0078a0040400300081c03010007003030011540100c2600c007212504e00d44075985607180d280c46409411030520b081c3d007060801d080800c0141d00480d940d2000300c81010004c0c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 709297661 1250 709296411 709296421
    0x40806161403040c05040510090c050a120516051602040501090203061305040302120a020a1203090c080c2101022101050f0609180403090e09070e070e030d0f030e190b 73
    0x1d51000b560000c0c01300301e49503030811180c00d0a4220a0340419107241017500243d0300c82d43c002c02c1d03c410081d52400204009400d103c01d503082403280031180d050100410141c17418101c086450b9070351880c82d00600901040f1480c0860100c5c103030880b07296000d04103002d50b5a407440c1400c003070f401c1a16614407620610208003090482c5100380351155030580c4c0105148000307040b585412768418100d0b00114020f56800c1030200e0b00d407180007421901e80d40d030000f4a02d0090f08007484025030036042901c158100508000e42699841e580c00065507991600c0031300a841003038806c0c020310846405004400c0c1001c00400c9800c203150381903048480c2607503a0320805182030104107880c0f003003038000350344060b0080c00c9082010280514a90042c0301c0c2c01c00052042e00c600717554245480c111200c01c4903070700c0550f0178041c58004d040700f1a088410750810400700101c420009071121801c810000400103030751110580b035886504810205c0c19540152111006148442e950341d00f6881000d40b484055072011072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 709298911 1250 709297661 709297697
    0x1003090f081602060c0a05010b03120703201603020f031908030c090d080711010801060c061e06060203041a040e073e06060105181504080616 62
    0x408065403111881002100d1507560701003940181c80a0145001c0101c0b41c0c00050711003400074101a0180e9008125884051501d5030a503580d1401250081d0081ea648240d401c41010076180e4060f4981003604442c140d02800c0d240303082801039440618030802e0100e011907080346200d01d0036a802500c0b40c0c07203c104407006040d501c1d80749003e41400c020031401c013000440e008402658010700d1541c422460101c896000500786101c05805a401c9000000d100c810440c1d04003030040110001e0034200231319071402d00041d20f40c468032a4060081d81c1c640d0321421944c10f000046440b00c80d4500e80030030056440d40c40c0290380350018050200001803210314400b880a00400351030841b61800d0590707101c0d66600c0b4044403404c0d500810122403500c841e82801c0c44d850144012203040d038031464640140c07a407001c4d0440c41c208019108905014080150b01c0350240710104810354a00161503d2001d9060307007240c08005c1c07103550b000101d240030700000e2000d480e410f103840c11204480c2e580e48400001c6886045 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 709300161 1250 709298911 709298921
    0x1011070b16110402040503070e090606030606061b0c03070902070309091a1005271e030d1409060307020c01020709061409040221070602010e0106030512090a090c03050103021003 78
    0x10080c6a8900701882000030044002d00034100005040542840d41c0c820101c3c0c03030581039800c0000c9030110308082080c0c480081240c982c2c010012001014241000300c0894441d1050704040ba10101c1002000716040b001080701c00040703000a400caa4000d581c480041000b500452000c0300090300014001507848078030300500a0b50b0050300d586842c880c0e8034038108020b048000c100e20051040500c040d10081c400c2e400c400c0300684d4098019905c2080080030041c0c5514070280303400101143d42d402840985000070807107445821b604240220322141000c0b9100da000e05c008440c1e01040000c00c2200d02c1d82c2c08641500700b05401e0302100c409503103c0103030070305480340f500074200002c00f00c0b20300810301c0ca840750850360418005011450080310398003250460015048070040e50380c0c88140e08020459092003204448442c0b20000c10107142181c0c2c03901e40b20b040b9170311440c10741c4a005c1072103020313662181800070040c08050310410010481d044064080c1c5400d01c0207902c81c000880b1200b10041c000e0041c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 709301411 1250 709300161 709300177
    0x90f030a02031c11060a020d0e0a031403090703021e010323240409050106030b0c13090903051b1507030504050616052101030b061912020f1011070b 65
    0x50043c1c003030640b074581c0711480004074900812241890800041c801803041a0244001030310169403030f01442c103090143c458220121241c0d40c0041c0380c142c08664410340014080400101c0907580340c40305051117185c18021b8002a61002c14a80c5403002c3c648080d05850103a142a01c01f8000c401032007e0340704481001a81000c0d17200700d110002865580c2c1e0039680c20a0758100541c15a1103a81c10010804660103064100c5150795200b100740280100344000e80d522400007103001d0329001102070300c40701c004480c0c824a40e1603900c600c0040d0070903001e241038400408008051380c0c240c8100528203551015040c030390b08a00150000496600f038401c0c00f600d441190014004e000f280c5030f125150b010381103108905400c0040601811254034040040c1d18a11031060140c6a169411810f248069150140c0300314400c0484c00e00c683c118410040d09901141d100c0c0e13030f1101241c0c0705400481d22140b01c020540c0d51080c001c1220702d01c182d07005043c590030400300c0e0040f00c10180d182c2c00310440350f1086d10300c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 709302661 1250 709301411 709301413
    0xd06092007030305091603030206091c0c1b0902030f04200f0f01090f06090611070602120a0c080706060e1303090b0703020102042616060507151d0102090f030a0203 72
    0x501010038020b40040d40c01c41d81c98821a075600042d1000501e080d00c6c0c541040f8010782102080c4a41a40100901ca0b5044900c5e078402c4001c00700050081d001550400d0014103070780b1035040040403e02002480c800a211045040d580c0b49040e0203141641c4c0d808032400c40e404003c81d50003d02000684500d00868080513204c0042c2c07031a041c04001c040341004c6803090410060fa600031a0700315070040000014005911010700c1d850a0030707805029540e64000c0100d603a80504000c000f5a940050301038810000320700710598890040b8011680141c01e010041e0084400040344002c01c4410362140040780c1c1c88074803401860f16088031600e5650150400540014030980080c0710800c0c4c60401811024440c0c0001450030749d40750000c1e03401052860050826204003c80000725410074800c149125549940c41c0b94050f0a1100180590043c5100a0400c3c0ea200e5406403a003201390340184020701d5641e181001e03d160300351801e0301035441744052a0003058440207044107414001101c94403164010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 709303911 1250 709302661 709302667
    0x1005090405010b130c03061d22080c07091103040b0f07020c090109051602070f0e040206120907091a030c0f1c0c0302010216060e010c05030405060d060920 68
    0x508220048001820680e2655a20903500d0580e0b0741e20403804c440c0840c0e5480200300c0b00706014002d0100c6601e644140900c14800442c400d180203007240c0240d0105441018003500c81d041c05520001d841d810308010003110340041c1c104803103c1c001032888100c800000c8140100d0780c554000b03200d617020583e0028a04008600414074400d40c4000300313640a415841103a21003480c20000801d208001e80c0b010314420f07541c0d028011100e1a078281415011103600080030401d20300454800409010310070f0342c0c0c0703492141000c101150348280c2120001d445540007002e603810301c000c0b1903440d1049842181561031a0030a0103040741c0400c1c0c140c504084004000d4010909901c041c0300d002101144110b5000f228921080c2114004c0b6203110300c480d0040020704003c608500c006894641c10103092030056080c40c0382000850b030700c0704442409810a1030505c0300c0d032010f480d1451441c040c0b40c02c01a481007010a44c92681d1419500c03234412200c40280074850184819514080170701d40d500f0042d0158410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 709305161 1250 709303911 709303919
    0x10203070b041104020f030a060b1620060d05191e0504170403050601060f020316020105070c03200a0914010501050711030105010605120603150a0e1207060902030607050310 76
    0xa0030007264014000c254140300d820600c030019080743e001c400c02d04405140031082c050a80e0440c4600f00107800690340c0b16141c020540010002c81d814800000d10001028140908038045240000001000a0b00d40382d07c40c0083c00d25000a03010889070b80341c1034220040034420100290041a150600c0314980600c46051680040040c040c014010740f00a480154083c245400b41c0004000075405003000e03151650400d2001000c2141c1e000912045520902c05015011802d50f9a00c0358185d0900f0013655031582482e010100d50160f90018000c81c111808103482410500d080003200c0c50100d40c2110b00946810300c3e141260028584849100c540b10010702680d40942d00800d0718501640100380032140070ba00090a441003600081c1c0060408210300e01300f01c0344120f041c1d40001c012000780c040718100c07841c42c220300c000040400386540d0301c1e20268413041109200c3c0e0100ba4080d001800d6940904e82407840242c880e107a412030091040400217038140e8803030b00540b03002d2504003465030f0041d868 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 709306411 1250 709305161 709305173
    0xb031507050a0c05030a02061b070c09020711090f15010206240307120303060f290a092301080f10030f03120c03201608030907050a0e010f0b040501020307 68
    0x301600b24820320410940c4074001c00c0c0c042002d0250601640c0c0100310503c0c02c141e1309aa519204101300b80d03100828080708001401c051010380a40d902c03400c00503141d020b20306010b101c0301e0000c1030003504555500306101c41c921132010011300ca00c40300b80b00340c008280360500499032004100c4d40d11900f0306105510b60342615030b24103000c00500f801012105250380710880781d90702e6150803508a000c41c0d80d404040bc489201070b62210000c0500d0050f00d54a260120400c816980c3c0f42c1c50342c1c2e08066000610903980ca070042414102130302c001001c0c8100310602003620384103e04a42c80140c04100d03200001201c0b5500c4810151041c280d100b0720080c2d641c6945c1c2c2c1d40a8101052504130140f220050f4003a6144240d031103640c02e503468a80d07003c5200c0402e26070850424000003601515500100001d100308810000321584840e8841d02541d640c0e03444880d46814000241c220f561701814080b8002005d06030140d07800d040e10302140d00c07038070183c0d964000400d042c441d074401d950143e00103100340f0001c140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 709307661 1250 709306411 709306417
    0x303140a020c090402030a05060a06050411090f0108070504080f100e0c0d1103030f0a200607170604020409180303050106180e070e1017060907090302060a121e0b03150705 75
    0xb20280483d8042c003008e5072110300701034084820000013560f50380c04008a2426001d450040030b0030203c0d00e40b614011202107542d034144030035681c1c10720024101145c400b9104100315002001094180c0f0f8080558003842038561489940c0e07070b504503041c803941c85440c090100c3d895180a10042c840c805001099440380422114490000d90600003405036910342078003100204040000c41d5151208400c9208a10401e0f4075006000f40d0b140d4426030400803281d8005000e006480f0442d80d06055540e1030b200003401911603604502180c50403c2135400780b0141201b9882035082c03290310306004c1c9030f0f20b6240460315030224180702450550794800402c0158030454600d500407445207050341c02c0c039a90401083c1e800c1081011000000c3c0014031010015108101c050341028044940300c2440c1011500140404004c2c0006445240c00150100c410b90003400c011300341140c50041440320400055407519101045180c810010341442c08242080c40c010170301042c80501412000300e81d440380e0000300c032990 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 709308911 1250 709307661 709307663
    0x2131404020c072c04030e0132070609140d080a0902030604020904030c0b150102010c0908060601050c07080703030503041e0f08090d050604060203011406070503040306020d020418060303140a020c0904 88
    0x84c83c044400e09140d03900300403407145000313403a08040040d1074400108a51240360520400c088016061080941121190f900c100a212021600d5203141d0600000418031000020f05e00c800c0460441907510300070038010f540c1841d40e200c1074500c2c0d81d030300f52580c2a03c200100003589034010000007401460845071698005000f4605588105600d96400d054000d09640080c000049440481030359a0309002d0440328240c1460b110303242603e4038244540d1040702400040c10301001162611000c00c041100e800203011880480b40b40a959003400303012684281c07401d030f0360080d4072400c0f140d150110200c040244e40e8410002c4c0000c5501c0d840c0e181d9140c0000f48038591001050042c9400300c0c0701042400e0045000701c0300180d417549800c80c580490b05031400481c0c050901805518049603001c0141c0b801c5039000140582d650500001c100300030702c02e9030054120b26113102c0501c201c1340d0442e407244c0e040d240700e5280c2c48458540c0064940310781c0144c185c00001a4030080c0c00c801181080c145c03a82d080703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 709310161 1250 709308911 709308959
    0xa0606020f2b1710050f040c0801050d24060302011403070c030c080c150906130c0e1009020c0c010905031f0b0402040801020f03160e010f200102131404020c07 70
    0x20021503494058070000580c0d1901c01c207801d411080c0800c1c64500f001c6c3c005007000f00e4003002556008800600701e03600501c20280300b4a0440003107001d01c4004544c2c0702c407582040108482d00134082035040c00600d5a4002603001690201020901c8804002164082c03030b895102c2c015100d009550845014032001012100210705021200508100300f01818600c0441c100c40c00143c6404610f01d403804000404202c00308030300d101840f01060300d02000e4010380b01614a0007026540d64680010204215072040c074005200140242066002040520128030241ea0b1381a500d65184205a0350f5881084c0e02c10340c43d10400303035003000004e150307000c0c9820a002400150909640b03d0742c040c00ca070851280040c5014002003003011444540c2151010540740d41010b20350449107038002440348031038410800038020315840c000401010640c900d100548070718020340d079614610840c052145800e01c590300500d000480380003075600c1c05000b6900c0040c030302401003c03060f1400e000c03200310740500090a146 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 709311411 1250 709310161 709310177
    0x8060d1113060506040803070b0a060f05101710050306070207050f0f01092d090516050703030e0d2307080a0e06040e0130050a0209061203030a0606020f2b 68
    0x90380384e0308003500c01499010007458807014103041c460001500103080e43d605030714180c4c0a0181e80b90060b40303c03060314000c0c0d4011641c580e0f981000e4035098142101c6c54500000142000b045420041101003903c50650075165140c8954030140c1e07403a05907000d22640100c56145140c81400c3c6600c101c0c0c0551414504020300c0e55403546000c22680714107020b8445201d80e48014003407111160312800003080d0b4104200040d00c0e243d440a100c82205500711410008002440030502d803003a00f21204107540402503a00300c0101540c05024002e212604080c81803070400541010400b41d42500c41c80d81e0008038061621480c04412031343c030b4900c100d03413a078001001e0101203284081449100d0103170120030401c0c19101078034071500d5007412501c01005418803500c200b4400084012581020081d41078039104032039150b4800050070500000903c24051102204000c0d070342105030044c0d0b0031283c06400340c40350080344d0b00b001900d0340c40c01944014440000348041070070500c01c84501080200a14107104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 709312661 1250 709311411 709311419
    0x30315030f0a020f13020c0106090c17010603090218160f0306030c26060108011410060c021509120309190501050307120213180501050f0f090405010908070c0608060d111306 76
    0x6c981000c0001c071481c1e0340d100300c14840720b0307650320a1f1120303030010b41464011070145c40030f4100080414003c01080640712131803c1d046460725541c500d420b81400c0300101151030090300d058400e00c1815140700000b038846000d154520700900c607450541c0e4102c17120006450810442c008150f403400e4083d41242c13400100e8100700d0380244147c501a01d00c142c00850090718801012402030300182a1009005c0921801c00029401c0b0140030152a41500c420201003c003819800b0340e4043c400c0d036180c00c884024031542c1450300100040955820072150741c20340da8282114a10451554040c10340490b0081010542280c0640c5a02d025034880110161600c28810810480120700d0b034030008412140c4240d089014101d802403502600c1c4c240e441030307025507490001442e48520580d9040c01f914a00300850244030081d08641c1449800c4000b00f541c90b0381030320b009001501588105800a448040420040e107402c00001340500e07007003e80381215200700420040c0b804034451002c0711440d6241c10000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 709313911 1250 709312661 709312699
    0xf0d0b1c14101805010c050423040f110d0f0209151e0a08180a051c02330c03090307030305060607060c020706021e030d0b060d0e030315030f0a020f 65
    0x38070003d00c0d6606021200f2503403802d142519109440c1c181446400d2009022400b07000c03c6855944a8140a58038a00003010100d002080d201c0800301000d4140b1055049550214008081d00540310034108030b1044001c41182c00c0303025a00c0496405000005204079942c3e44102501c03044d030300c00e642020306022501c000301d02548444101c40c0450748000c2045030a14506142c4051020350138041c044441e46952496201d00e454008602020091002c142e10f00b032003000102c0a80402c82640700040c1c0d505001300d950b264030b1352449040f0129281c0000c2c000b02c800c909503400b410303040b4021800c22141e83d400b81d000e00700040c0301540241d414000100411414091944010800d4000c1c0415604142e4024205128590101c0c015804c099541525041c00070464025a100c001c00048a007124000102188a0440b8905040d420300f0078402040501000440c024107860303140b9400c031000d0380c0c1410703100e400100c02100d00c2e4100021900260902c28a44190b0f544010b0aa00e100c40440b8058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 709315161 1250 709313911 709313921
    0x708090a080f010c0305060906010f180506030910150f0e0a090206070311120c070e06060405120c040506010e09042a1212022a010e060f0d0b1c1410 65
    0x30000340c0d1201a04c80c501c0e41c05100711038104d00d081d1445101c1d440c200c00060040f1649521080800030b09100b590450545d505114024140c0141501e42d00e0900e80031031603a0300b0002c0c1001c854a0b28040c1000d00545000d1100310444c2e446031401943c091408006c6040458010b0400c038106e61581200d80050b0365030b03002000303414460380742d540c041c1c02c00e402c0042c60884600c0c0303d6031010381e0401105032030400005004080b1038002c820074071503960f0300b40070920500a940c040c64000c5c2100484448444000c03c0079003040009450401280d0343c3c00b001140d003002c0c028010342e0400c10120115001c20f4005072410b080c1041e405c1c1d000d10760000e413140c0c54280001c680c40008038090101181c0304128040d01c85c182c0042c9140300500d031a9802c10b50340300d00a818046200110014000c20b01181e034003030750720b5402e107503c02014039132104040e11040c20181d022a0300d40303110501d40b0501c0050352800707500700381c25003103804403d0a45484654810400c15580516031100c2e05c2540c0e0551401d44960241c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 709316411 1250 709315161 709315183
    0x40602130f0b13090b060906090d0b011205010f150b0304380901020c0601050915060703030f0f0e03040927120f020729190e03070909080708090a08 65
    0x6203641d4200f809100c19150269402c0340358418202110101c069031b03460306070781c0380e00c2080f580c0300d07a80c1944c140041c14020700b100c0014402c55030540009100c1490340003040d80301c0e0044d0024000c441103482c504003229a10410a80440c40e801e40070301030910210040c661183c440e820407140e6030f1030750300080d903001004c0303200349418680701c801c151009080c03021250300008064025030400000d48903460b00c81d0340501403140218001700024a00c070600150f15880c0302c0c0043c00241d039071002810010003030040904150b0803541041c08224400b149446451188039400010354146410251003001410302c540c81c03400030b400502c2c56510744544c1e070042a132255100f041012030944030360001130070f100e804031101c0b82550040c6608100e82c0f141c0f00c0c06030100060303013030b2406c40124a52050612a024800c5202404442161038100441e000450b070703411000304500b2109115a102c02c01800d40300e41c9000200f240c901404080002116040a0143c030304004103a014026160740409142ca214410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 709317661 1250 709316411 709316429
    0x1611060114030d020a110d0302120f04060f050703080103030e01020c060d0603020f06190309020d080c06010e0c0c0c19051203210402090609040c0906170105010b0a0206040602130f 79
    0x1d010790a00d03007048020b0b00900c0c079002600d1881d40e5900c5040d0001c943c3d1411600075441044003c04240c800d100e030030545001e01c04410340b039031611100c90401c0c2e0400d0107218003041c10b40d03c02c821018042c1d01039600d1141c0c5a0f031139140766825950110b030400135400f201b038107521850245500c00d6a4a1307028100c281001d040005569146004120000e038843c044580a040d0400130041045058043c088502101d418045004011440424144026840090030125020548906810b004600306049940010130f004081d101e171903031418a8868904c0c10401d0742e1046210003074a04141e003451121841800c4848600786e5501d01240b80c0c00b201419040058000080100f1164403c10b407403220554401a091458031b07180d4045030714004054081d52061040390001410000481e007444050001d0080c288010341d568062403508109000240303c0c0c035404c00001142110024054840d42d017500c0e4001c0001c1e0702e90703480b5400258000c0b8017805000c070a1350070114809a551400d0340040c44c400c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 709318911 1250 709317661 709317689
    0x1b01060f0602160b032202060706060803071a07090614040e09070602190f1b08190302010509160e0c0f3714160f06092001020616110601 60
    0x2031021410f43c40c42d00300004c00c0c4000c1c028070950140320070008018500700d0a01454500c103c1c00090411700031035100510082c00d01c000030a0000000c40500300d164401c0c40078880110306441d00440c1c1c520f0071a10724001881e200c0703003001150f10035101c1d04032049441890510f041e44940f000190b09904803040c4050b540110340030402d00740c3c10061888860320138864500c941400d0365510007500d90204000d400c020400000d40030b00390110088000a003841012a030800700c00640140440d0b520403026009540380000107443e842e03010400b12081a02c00b0600e01c85207080804044035140d0280500282e103005010a0701d00c030092038000d00b0b020003582141075009003440c800440c0380205001006400180c1108958000d0304071040c280da100c14000e44c40e4582c10140030080c501e40762400e001e0720040700f072000101400650350024004c0d40c010400100c180c61980c0580001c080170004080c01070b0b010000260b0010110310780e00a81403410b1504003c0780d17510341411450000282c0188191000031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 709320161 1250 709318911 709318933
    0x70f0f080316050403031707120606030e0c01030e030a050313060207030c0b060d1101110a20010912030203070209040c052215050f130b06030a0203041a06061b01060f0602 75
    0x1502c41100100303200d20f805880c0c00e08598000b482550002907180a0261540108080d5802550700c4e58940d501c50804003c0c05560317030f100402070020306401405c42d000c0c00404d004154407900940c490102194019817030600002000c0300c0039400145960501502401d1010010f0768034001044985d0080d0341c3d0242081c02d50a20301501c400182c2000c6c071038224500c552000413608450f07604070349400d00302004403501e01e1120741d00f01507a0710001000c02140e20003282302007410b04009400c80c042a40c0d04410b417030f1150200b4904050071a8040c015a1003440200d0040c98040b040a0744a80314000b0409a0f070b540700040b41c081030060101602d207403201d0b8204100b006c02d500c18010040303580340000d03031801c0c0382c1004070740d803000d43c0300d00b01d800b40c05511070b5049000380c0c1e0380010441d4075014124030742d2442d102002400940059a0845850090b20303456086a0801250b050060740018580c5140c04280210700803103101c0c054800840b5521003500140b400015201c5000030101c41c0c0142c000d240071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 709321411 1250 709320161 709320181
    0x20a0315061404090f240603060e0f0c01020316020604091b18140112140906010303030b090f070318080406030b03190507030210090801060314010c170c070f0f0803 72
    0x410108180201c1c0b901c0c0c400d0012607008004014900d422a41040301c0c001d03280120b1015103446c07040000101e041c1400001082401d5014001d050443c0003a2402d5814064903951910312050b01c0c513006078024401d000c4440e2941b010031341c0013403008050900c0c05036114010b10548800e0301d642110703036807141007070054a50481101c0790300f401003078001e0341040c0c2044180e5602078070a030362407030410105c5816034122580c103622600040c542c40010303241e0b52400101145d640c910900080380068107048042d0704600f400d0816030b00461100011441940c1e03400c3d0100d0042010f40720098038079004c4401c05001c6000721009002038046a07801191840c804003d162038000d502e280009030b02010700d181000300d030011420307406907076049443c1482400c5000e02141c0c0c92005070000625035207480800402c00500b00040115180081c0c024070002c00114415030b0344484480c141808640c0d0100024032101c010070080101030700c034440a1b000725043c1e80f11801c507105102c8080340e03860400400e00c448080703 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 709322661 1250 709321411 709321439
    0x106030f02031501030c26070807180501030302030307030b0301140a061d010510030b010c060c0c230a032604111507211106280209031207020a031506 66
    0x258903c1d0204055146580f10301d4080300e02e105078089a214548a901540e10300c40c3e10254006112040318503158880c41c80c142c540102e031007244070041e80178603d00f01c001c4640c0a614100c0c0e81540244d400d41e84c07881402e8000d440c14044c2203034035550302c800303220311603111007141d0f0b02445d000302d400110f043c2803504c1d6078091540704448004400c003400040001e50359186113682c10322050310f40810b4900200300141c0f40240c40c29801000745042c0851810303860f600c2810700c85040d01610040c00720382909a81186080c0000c403601916400a04046020134001c0a44030648142600c14002c160301148500e84003101c1610100c5030b12003000c000b10b480349000c2d416031910306c84070440d16140054560720080060201071400c0c0b0f50300000800c0c03c2e6684d020b9a16041d0401c1a1401c1d40c1d0345190082e6580c1c0741144a001500000802046291900340507100f5100c404a0107801013001042e040d0111409800c00b4408983c0035801450220000d100001040440030810034086683c078106004075034404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 709323911 1250 709322661 709322683
    0x80411061c05070f0e0307120c0b0705010c02061e07082815060f090e040813080a02090a18170c0f0f060703051302120c040509150603060124030603050106030f0203 72
    0x443c160007148221b582c00300e00c40c002c490031090801d08507500da01d04070b1140c103082d900c0812144404104a024000c041d040203281b60f02c0c81d400d8420b40c0c1d0b10301034a59649205525400c0a58030240e0000f00450702540034140c001c1040d0700d0410b6100945040d00741401d22045540c1100e0743c617101024030b420480c00490f40a007019082004030f20489000c010b1242c90a441150440a02c400106090100d81002c49220703145030021a0121525a48040d5556110441c102d010f888103800003245603034948a140f03000400c035079a519140c00c0d1070b03c0d84111051700d02c240000d07004003040518034104040003c0307070107000083c02500c0c030b180b000f0b0031303250505900800c080c050509043c100122a6540419094100c0c0e040301c600d25aa403004031140c0c0307804210002990414503080c188240c0540000b00da08a0f100c070a900c1c61030a0f44c44800380368480c0020701c01c449200c060f4845080c500d000d0b50501c040d02003080e00e0005003440e52900d825095410f01d0f402602d8030301202e1240300030350030103010700010710b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 709325161 1250 709323911 709323917
    0x60603060702060c03040305090910061b0b060f0102010b0a030b040309090510050402070602090301050403050c12040503100c02191a01080309130b010c020409050309030705010c03080411061c05070f 87
    0x2038070381075802075168074006090914880000000804060044041c0e8507a100050582252442e00f0700c43c020319500907010b80b0010921548035003078280300c10380c2c80d2032841d5407008001036103890b69024002008560010681036540700c496201c0640c5421505000640c05069502840d003414107026211512325000950748074100f404204810f203001007520111241941c005035551f0031400c100700280200d1039429415420201804241607002000c0c10303012001c101070312102e40103001409007a01c02d6208d40e941580182c00d01101310355003a03200000460150041c0c03050003240e074890752203280c2c0d241c4044400c00b11980e00155689143d0b0041f41c05455482c0040d0f1400a00000040079096039056a003034883d1240c2803100183d12410351402030f0760380134000703124042c2d0b50729150741c8a42013403601900a100b0100d000901c0d610900e070750100345825032039000041c2c4482d102e00960600d00e107000d0380c111008000190002042440b0303420400d5008200003500d05151200600307d4550026400070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 709326411 1250 709325161 709325173
    0x50a1a070804051b01140a0f0e0d030905040e031306080429040f0512181309080f0d0917030a05181b031207150f0510030308061801090e060603 63
    0x304005102c2041e031186441e1240c81d00c2c0c2d010f00484481404080c2a1304a81b008900a0344541d041200c03101e8000c07441d15903c8900a00c08288258102301320009800034a25290401090030a503010300710b035400c3c90040e80d1800c5a501d0058285654a40c8900c2c00207606e44104000d00c1014030391b600207100c42c0304411521000a00d905001110082c201605102d03403e880742d0100501000040c1d0ba0a0304125865260300516040140c9100c1d01036400317000d40e040c1082c0002c1031119208020007141c0c095038090604400c4800f0070340c2c40c0c2000e050f900c01990b58804280103da0100c403034881810041c15865a2450102100c0007502c1c07000d03103030301a103041c00780c1c62000100d4040b4900300c86054000c41800d0700004500068a031608940544801040005d210003e010001c00700698484c4030600c10303c0032601a40c1050b0407928106c0d03922085942d0540d050001074450818140c0214004041c1c09450402d03810303500301c4c1d160a80c4030f52900d0743d81c0d801c2c03030070888d00601039298031400840c05004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 709327661 1250 709326411 709326413
    0xe3301060c060507020f06070905190f1a2104020f010212030c160c0b1207080105130c02030918090d1403010501080903040e041b092a0c050a1a070804 66
    0x12003807002200060510380c0300e0000818180c82003001c00e036813800303010444801d41003120014014400301e0181900407270003503c42180d1340383d014000004880c0040d0080a10a16201140d0b031040000106c85124040402000c0100d0440403d84641010030043c0340b042c80c18913104221080c8032600c091410f642040400d40410000344055981c864684d51413140e075014080d00108081002c40300040030004105d901040102e034142c0900103107070340000d03030010030303190028151401002482120b500400401e901c90855080307405c03540021983c2d0049901300715541c0006154455452241c680041a24007002a1070804101010710300080c3d040912480803401c00121140c130050040c00c5c1413000401c0030401d030f00c00c10400c0310300501a84088560a092604e440e4120300480e000070f03000c906203002c01107600c0002d4400d40151892010850311400240d1001c244d07078102c140301060a000b802c6050310003082c002d11030034601501c03030011181d501c04414a690001071300a040003042182441c2044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 709328911 1250 709327661 709327667
    0x10060e15010e030f030309030d0b03391210180f02040218130219050a0221041805040614160e04020f04080105041103061603050402040e330106 63
    0x90220300c286018020305220b400400d24181555000c46980d110020400c180c42c1400700c054150021400000c0c08848220000c242e550210f41c0b8107511007030072061014413140ca01d00d240a82d003803100040700b802031648900203084038a005192000300e4010f101c21004200d0140700e00d100900c0040b4030a10822555101c00107041d182e144001d021f641d001071044550030011004800345103006080764100c4842c0105103001e50840621040c0480d5080c0780100d132603010740b080c3c400d5040e44d5030040403c4481d0b20410426429419503404d5104010000491155078000300c0d9150912081030114007404d0a02e40030040314500740115880c0150310050000210354600300800c1012145000480000390000090003803042c0710380d00b18900310004000500c00419003109100c1c5d03014980034070707008600c2c00030705894110869102038070303110140340c0d503910601a9100302d81160028000007007481c0565071a600e4800c64002180c042d44a82107070081c410003218070010000e8908070305040c0c035454003c0c05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 709330161 1250 709328911 709328941
    0x6040609050412080c0a0c110406050402042309060f241314061e070305130f06080f0601080a0905030c100506090c0901020a0305070305130f081608072106020a0210060e 74
    0xc0082340a11480156a03880343c0200014000c000d00840d03035140e9500d0000000d21680484100d00c1c41031070000c0400c0c1c904035480c944201005020b4060768600b00e000c03c40d0046c40f850300c0c9410580300c159032640110140014094040800d02070f8001181000f10f94000801d0301003100c0d115003c00c0008080c0d408024000701d20a042c26800f40d0340351100f624041e912405022140c180e101e075407400008051440d1110102200e102d52141d0301d02c1d8a42d018402c400ea041222a580820792900120304a441c0650116031401d00580a036403d00540800321703803d001e00164080c260b10744403000d010040c40c1c00c11103660407038801c16001d46000403020003c1d4403060b140f10050309012005c03030418103050054044981c140c0348800340701501d50325000c4c01800c7c0e135240d000703009040c4500c80b24200400d170444200e10076038a0100041c0044e40c40e20700704159103980d050380d100001040113040700001c4e1140c0050f000c60102c0743c0103030040001780e440103000c94002d035004030740d940301050520481c040d083e001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 709331411 1250 709330161 709330163
    0x70f03030203191a0910080d021b031b1207030b092409061902040513090308010b0c150703090506040b01150c1101030b030705060a03061d0702070b0306040609050412080c0a0c 77
    0x503075055a403041100c1c0c0c6c00f540c40341c0c421062401a003c40303060380da03404605034104203280c01c1d4003413016070b4950034113507035501c40e50924030700d5a907a0310070703242030f143c0b29952150100e400300072a40e4203900e07a41c2c0c106140070161052007003607001c2e0f030108455001038038480c0c94402d000381c1840074500c0c052007078603656880070388005054030b1142c14030a20702c400ca03011603010781006400040740200302d08080c402411214001d80005a1400012550070420812220407199200c01030050b10381c1d2419142401c44050b084000f41513989280800240c0c00344070ba0340c072031401200c40100c698984469100b9981e80703410b100c410044841c07074040000348020402c090042082c07a0015048140001007450305000d5040540c0c0071002107072501900c0e40c141c1102003079992011742c900b00760400043e401110341081d10002e0140c1c00481041c00140c060b04050b5600540c0203001091103640c4000c40c004841090b03c003601c0807240c40d0b51820a480d040415507400090340c60b00a480c040d0480c6000303001010000c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 709332661 1250 709331411 709331419
    0x6020a020d120903021512010b0c030f030c0d09080703080106050f03010905040c0f1401021c0503010e04031205010311030c010207060e010c15020301121a01030302070501030e0102070f03030203191a 87
    0x42c1c0d40c90039a1146001d07001459014040300780c00703005501e500d1a03a410922030f61000080c8140045010070008060320207100c401d40c011400c1101e83d402c0c2103d103800c01010400280c009001e0403544040038082c40c14100c1c01050030341c1d910020f83c20000e00a08050704084240f150410010280f8283d0104503070455940c0e500019003600c1c0da2511495420b2035a00041a0b141d1044002c030f075007440001501c00001c400d0302103c40c0c0e10580c00752102450617007100c400c04660140010066103c116820b40d074890712038545020010002d1907007600b262020781003600c0c81c20361040010f0850404000071200d101c0d00340010310500340f50100003484102403040070f170704200c0103e504c80100800c6104402e040d080424007991a0b6031074854004502c0c603c3c0400365020451801d500d825a120380091034140d9400d5400b9010950800d401507021784100110003a4640d0700300801d00208500c1203072030408074401d070343c0560b8030706240c0c02c1d80301c1c4115500c0304034010b24a0280710300d8540001200000410310161 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 709333911 1250 709332661 709332683
    0x204060507140c120303071d03070e180d0f03060e040521071505090d1706010f05280e03011e051f08031c180314040801020d0e0706020a020d 62
    0x12510b5030030100b0460b08260403c080002102c074201c2d000c00654407504030340d075410f0034007100e40e03141d07111505d120b09405415400216051203074068003111070342d000d15102c21208000082141003461701e035134520f04200040690740706a4641d43c0c0341c01410020504007919600904207a00e0300c0c4d480d110048080070081c0000f44421489180c0e0009482c1c5158111061811080050000f14007410044408039580d00580c6d0340e107101e05008241c1100c40074001000321020381c0d00e000c01510203061503042e420a02100388804210803d170b140d0b5400030100e02544050007145100c1c00904070303400400e009032180c1d06145a40e9651200c081401301101200d070004034103500e40909800c0c0042c0d100200600201d00010003150007800000142100a40102280745250080259004071084440a00d1305100140d1b000004244912001304941281800407071500741e64145446c00c90380862100d691a80e110700c80c130f0103104028803001c002082c1d0750020746a4801d84d81c0c0000d070170b10920180100222480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 709335161 1250 709333911 709333943
    0x1060608190b13140f090d120e0705041d0105100803070f0c0302100518060304121214010f03030e040902030304050603102c090c092e090608100204060507 68
    0x1502c89415600e40f50040040e01c048122800504d103045440b071000001c1080443e400c082c00280c581d00d428410f944d105c56080303402d00f244c03002d0b282c50f64040741309100e10040442c641c0d8440c400c9514058172256592007000c0c004882c1401d6510060401d41100c0b00030340100140000803045480941c0e208201405545441c6040c03002c40b800d980000e07400100581210480e581c01800503c26188280e00c0c1c4190a0b4138441005464441110010b00241c00300544410503806009000040300845c04027007102c090102d0580d0882c10240d1003c100040c003c1004c00c14550002141c00c1c4504007981c0603c0a002e1540100c0e40e01d105074403915000d03000010010760041011010b03003002c1c08508040100300c180010400c0250307500543ca91500c09030403808a522804001100190400040c20142090340d8020010f0b43c182c004101240504144007031070b00940c41901c0140e0068404000c001601e80d060100c0a854450b00c1d03624820031500c100800e102e1642c100c0c0c00e070346540d43d025a05000c2c000070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 709336411 1250 709335161 709335169
    0xb090102030c1e12040302030d0e010309020d230111031b0708030123040b010c1118101d090c0d060e19060b0d080d0c02010b060f040801060608190b 65
    0x441da564442070050030b0340c0180c851428072840362802c400001311502c2d484000841c0d0414440c0744002945036200303118064a40e0b0150000900d00001410002500d01c02500800c1a86a403804119400e680f200c04c9801901036a0414000c08881c1074000c01c41c50702004d50f8400d80f0312010f0003404880c801541c06200342244402181ca245510242d0941c40b943c6d0780a00c0c203444e0001610303150824200c070401c040c1d1400c203171042c0100c8040581d0356454045440d00c8466030034580c41c80054100c4a00b5800f1449a5030900e01d40c0e000b0031021310385000551800d903800c01b401d81e4004110104c03070350340b00c00d0014550002030038211070441281d08020403401807030218028a00700c00e50442c18011f8118494a81424001d00c1d217141d030082c08180080c9901104000d040858150014800b180c03e12400b60804100d6011440d45c042c54000000d141c40783c2c20001d041034004403000d5943c4240042d080c03004800c2030080c180100024103100f04c050a02c0181d040080c4112020780c1c58807640c44031480c004e581c0e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 709337661 1250 709336411 709336417
    0xb100305030708040509010b0c03030a052a251a07021f050402040b19030609021c0b0a0605030a170c070506040609080106150c02090a02040b13090c0e0303040b09010203 74
    0x16000c0c08032a50b0b07642c1031400040d181c129228140c81061000d0001401c9400300b0219480c03c100000a14030f51b40d80c0500c91001000007503d51b10150480e080380d5614904c160f00048050441d50507495246e00712500d4018010710000580c080b1801009112000510ba807000b813410309580c03070100785c0c0c1c1d40d071100012842c0001e44022079003401e51400a02441c550350754803642c080c6000365818040026034100b400080c50000c01544101c88640a041001c24000ea22603080d852000b84210a082100000c3c0301c1c1d002090001940e2885c000710500940060074031800740140019805001050380540315030614990650b009c802c0804000741c0304000c80c400f88400409444002e000390740349c54641100600c0e5070720721b00902280f5860040e02107106100e01e850040c8000302039035005c040003241e5080c07000ca03827400b604100f441c1d5020f000c0403444201e01c801415501da40c52000300a828030b80079078003060703800b94500c81e028081031243c49a00e584000c0b04a5041c0d0704021b04090b41d929a1100403880c500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 709338911 1250 709337661 709337663
    0xa08030f0f0d14040506060a0e180f07060323010605040605030c160b0712050f060402160b071d0909060604020306030a0c090903020d020706021c03060308031302010801140d0b1003 79
    0x601e8440d0302c40a90b212043c9581c02180141c0440383c02c0d58a003810311880f08414041e01c004181c0220004101c00070320f0504910052020301a03401070488100c2080c070b8140d094000c40e011a880d844400146044000725080c0342d20b90702000d508551429101414510960280008100c000000200c21402e43c0c41155203072442542600520a03550616100300d0400ba1100c10014504035002c45145410f03020f00c5014171100500407205880d0342040000039808880c580e818590381100c0000840c10b0100c00358845d1100d9140d81d0702c480c240c0110742c6043e01d1084420740c405e458502c00d2048114000030015407181d800c1e1001a070341c4d102c50001a142c1a01c4c0f220091140705030340307408103000e00260081e2b400740f8842c3d002c54881c488445400d980f59600da014a9006900c42174460703034011180c1800110300101c609001420740e0b100e0300c90402560003299580588101c0381080703000c550384480102e004020201c50415080540d20018013054000030001d0b0082c100c0c40082485072480c40f460300001c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 709340161 1250 709338911 709338937
    0x51b0f0a031811040b19122a0609060c0305220b180f0a0302030607030f0f0509011b0302032208090607121d09010b180a230a08030f0f 59
    0x9108070707141261100a801d0340f80f03030245050031580002c6050407814650074004820108500d6801e240503103e20000034039040c0c59008004441440112821884618005900450420f007504250b00642600d00c0c40d07100783c04003d1a80c01000c0440c0c1d1100035201e20003210000070303c1802150881c00701035407030703a007001c80c00c448001400c102c24011480f1806d6904410f88642c03030302c10072140400041e00410306c0080d41540042d000175006a21a5011010561840c02d001400c450b2038038080301180c0044503a035030240e40da07064400c08212200e5900c408540980350641c5545040084e2111083c00c20000940d41252802c040b030802021405444404030094215600c402040c24400da805403003880e1a030100305c050400d03000d000054091818034580c040c018104503440d02c00f40003041d9104030849030000c043d5440d2202e1582d07500035050001d00303c0800305420340c0200c01c0ca603c025504982d44520440c030388501000015804810b460b460700550700013907201e5000c1c4160303004501c144044030580b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 709341411 1250 709340161 709340201
    0x5040213090c03020a091d010312020114010e01030209150a06031a03030d05011a03070503060111010e070e070201180c12030512160f03090c1a090405010b0d051b0f0a03 74
    0x11050b40350f4007800005c41d0b9580d461098941c3c400f80107045480ea005540414403001c0014404100a0f8980c220303403407030034400050074814400d410400701c0c0080c1c000118140801004000f5071815130321554100908030403041050402000250103030300f00d0300c40d031824035440b0300ca12082c0314031010100d4508403014007501e40e1007055403038080080c0824040c840c0da8481800340254885590400d070392003840d00d42c032460301e55203071000103450654640c10382241964844002d04201030703003030040c1d20043c59031144071151403d1003c00a0f003507407404041c2058290344650503070049000000000b04907044e1080040a403565400c1c103d91134070903003408481549045090105407480812900c520002594810345100d11150040302620905940984a2480800240445510820825030030319101d0743e03540c6000c01010104094440c241c8c084010f80402248188039401203004495205003585090320b20514450784500e1306014203d010b035030326100410311102d000d00961000110000d02d44400c85 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 709342661 1250 709341411 709341431
    0xc0108090f191202030c0a0305030a060902120a0b01020a0201120c020f19051207030e090c0408250b0412200d05031c050c090405040204020d060f080d05040b040504021309 75
    0x81d1080e0200445440e85544061002c3e184040305503562880c81c240905903818a54034101c2c1e5540015001c140016a80d070400146152140300074094980c095101203d00d2a00842000855a00140d4141550060020000142e80c014004a0800c1c1038110025a8103420342040f890f1030f40c0044105458403c0e0441c400b0b600e50490083c1240c24820011107510101c0107145d440f050041c02c00c024082010130003c41550f1426a07a1507500c003014074000c0381016901c4d440c25207418443e42a107a10030790795485402c601900c51460202070503015600a15152a08501106407035500e03901500c920110b04130084d09043e080061007650f071000b000f81500103071504003030b6161f5002070018a40302c504001032642ca003000c1d00409108141081401c0e003480040c60a10016241c020412030380a9401c01030260001c6051040780b000e407000c81803880b4a541820106441c18444d58444014440f050004011890f1890100c3d0140c0e103055601680725000e0728a182c28419050300040e006030305221050f5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 709343911 1250 709342661 709342693
    0x10504061b0c03241e090204090b010b0d05090106030201020a03320a170910090519050703031101090c090e1507030b0f1804030c020d0c030c0311060c0c0108090f 71
    0x10f862400d21300d0004e004041c1c0803001c542107916419451816001c0a5804100d00c54250f00002101d4005000450010b017141c3d155032100900760416021554085418150700c4403901c1020307030190505d03000300804c0c0e05640001c1d40d51121030301c004080000190440380d0f04120704015401001922960480c1680d440c400148240c200441510009100111079011051040010740c000e5001c103010700102080ca1030039601510500c9001c5d901c1d8404c04120500c160051200070f40dc2c107001c2c1024004442c1180b4006051101c2007802e80d1543c5e04100b0464080b440c030300c1c100801c903016280300040791000081c007207042c8024400c000c2142040402000a1990150020300944104540ca141c44101c0c17502003014000c3c210480c401610f0078000000c1c0002e00440c1e2840809000829008800c01c0c690f4403444040102e800443d02241c1310a020405c0118060441d540060121201f82c14040812441590742016821079030401c110b01c0c0100314a01000e124248560300c4800c16564030051034140c1d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 709345161 1250 709343911 709343933
    0x1e0c03060819260315010e090403110f0a0614060d032c0405040605010f050114040e071107060509180112021014120603070b0c060a0b04020412030f030f0209010504061b0c03 76
    0x7985e100e05021100c0072456200d18913a6046c04001400c0071096122501d00b203500c06c030411481001c1d4824260220fa44007020808075202e503100d280042102d2074070300c50017042000d02400c03050017031076006030384000641c00c14076a040e8000c00e011020042549111036050321002c106603550000c0c906028071050254a80046042c0e42c06100c488024680e61401100c3c94008500041c0998105100500c51010200d400742d4104940c0d19200b00c031070184544c0c1a08200e4994404000b0030f600060101a604242c50022507020002c1d50410309980360000790036034494807401c002e104110105002202034003624800f242d0ba80001900c98860490541a81180c001921014403c0c450108000b5070a40503000700c8601140c0708001e0b00040d00d075418840054828204900d51141d003c0c0000315841c00d0110070901c1041c025a03840c0740c0281c00910160888050045103008035004014215940c0d030803c00300c0d01210260324002011604681b55814085c000d518010981a007080b4008140008a007107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 709346411 1250 709345161 709345171
    0x1090504060c0e010507110a03020901230d021302030901060f15030b1219050a06020d02220303080606090d0c0627060e06030601121e0c030608192603 66
    0x1c200300400d4500401c1e540390014400d030342e000038001c201e41c0b0300140d5458441903014034082c02c1c400481c3d860364001500c5800980080307a1850305509142085251707055403620203581a200c0001408a540200c0c4900d002d600c0d04a01042d0004017041080c282580040020296504000445a11041324801407554558800002401c00c058802c00e450501c0040303080c6506071005014a030400d4114072241c0400c3c3d803042e1290b000f00850b05000c20400c1c001401e42420a04005a0322800c0341200141094200307030f501c00c40c0700074003000c0c0300094020315642c0d000f8004030380c1941c03104000c00000c0c0351604103101c0207100024589000501a412120113900112103441d4401e142900910710b0b00003136114843c2c40c00049010082401c1c600b0181c00854021406140890400d01c209109109841161401c000c030380200800c09440707000d4070b11565240102510381030021504e810340071580c0d940000d19000141d40420f2039031041019044a0b221614007500003c0203038049415100003941044072 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 709347661 1250 709346411 709346423
    0x1a0901150b040f0e04150e0a0c0e0601020d030203090c130501150c080403020d031412091911120102041e050109050612070804020616230105062206030b01090504 71
    0x10401e40d5034403055800343c40f402680306040d00c0c81c003844000121070140c8103848444038542241420034942c040c3c225212041c2d0000c0c03030003d005140581d070120682c2d00c20503003440100b081c06400d80e4040784a00164240b46030141e01ca848915255043c00c200204448d4042c3c030f0000c032040d0403d465000302d8101c80c41c4c024410094041004240d80d100c1c08284002c04140c001c1000b4001032400c0b29042000c43c0c0680750507910709001c403459107800e9000e41e200310700c10701c40035040040348070302000448070720142c40c0442e00000d8000d41d5020500c2c412000350134400c5544815003d040002581601e000b824810030318800c0400001d404a42810306c0c0c01010b00250003440013088a00f48407088800c020006001c1c1802c9030340311803040301e1000d0080c0003268007040401c49201900f81c28180014042d0150b20017600100c0d00030f83e21086400e202030401d14690400c1e04010241e611480841d80c010849803c0c04002c64099021800501040c0c0000344507242ea10004100e281c001e40c400c0c1d100341e106078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 709348911 1250 709347661 709347701
    0xc200d050f100b0d0807080d09051501140a03031b0c0608070206090a08160201030f020c07050f041a01110307050105010b0a110703020603061c020405090a03020607080f04020d1a0901 80
    0x140c000c0c0c03c0c2c030400904950048410043c2200265246000384039041c010300146040009900502065030341042c000d131400d50101c10364200400f1000c1640340140b1114188a00d83d90a030400b10349002910b100250900c000e05213002c2c06101c2000d20000800d2340000102015904c500c80945000303425a120ba00500c40c000c00100c0171800050341588107a0013640720f0381004441c8030520001003800c1c1d0220304041e15202c2c0d022003103040d03001500030000c0303010107041014100002d01081c5460211120710483c14a06074550f40e10200c111040b401e0020f10741354204201400c405851740c451490001c21a6182074000500401400d02500f50070050b5a12186e80222032218541c0d151107501000e94401820008a01176207000c10b0317000d19100c8103c840d68100d5007036400003403c0b1a000c40300c8031016001242a8020160305011143d0300c516541000c0e42507041c0715111044040c0c005100031300443c00814610140403034103101135081c6100d050548040c0c0f81c801d50890103007002810200d441d207422 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 709350161 1250 709348911 709348933
    0x305030a170903040f031103031606060501030f1401090b0102240402090a05100509060a0f0305060109050619051309140c0109140d0f0f02032e0207030c200d050f 71
    0x11013160101e17180282000e01660640d201c5646422002c0381440d40b40c4003c0000454103100398100211250250600151b158940342c00541a10a0307403104403801d0b0f25102426a180b4264848a410340700d2003170000a54883c80e000503441d25206214401c10541f24103003c010a8900c51100b9100301c1c825a08000b4544801807124203486058400c2415400d41d141c050003182232200c110790344090002e0140c5442650741d182d52403030030210342042c1c0e4160804001407100105074001e0f290070000c1174a404a606500000181c180501801200c2c071842c12a0305501001c1c40e103400c00f946040d00321031a01600d880c0300071890742e56050601035070301240c0369800014801d0300114900084800280c549030032051305998440e0001d9400c0401c0301e9130241ea00501c00941c404005c52515202c0f5030403030240f05030440440255800308080804507140c0104104000a688078407001c5c45654030040c12440868081c00d240c0c2e511202c0141e80d904a030baa02c41c0d44c3d092010014603103020444000c19240e200c0b0075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 709351411 1250 709350161 709350163
    0x2040b09150d1b170717070603050a060e0106120e0f0d050c01141603110a0e1e030d050d0605090720070b0d06320d0501060305030a1709 60
    0x411202032618103200100d422440c2041c0041c0350025229003002100f00702050400c071a00c0200e030700000c1a002c40222040e608607400c015000207800029a50301348500e420540699698050148a0406407a00b0116002c4852038021501401003140f074084550f846510040114801601035030b1080c1c142031540c203403210086018130092288602800301020311040565042d480449031b030020390340e18180250341c60f0400500340d01036003500c0d0703074107107040040000141654018442c1c0c450703420b1f04225507580345070001d0201c00c8070502030790b5105010803000b4040040c43c080307405c95601401003020440b8020750010040030840b0504804000c0c1903222014840105001c0300c0ba000410840b540c204d00c0e4120008071907002047c01012110074a40340d01e07068507145c00580c001e45101b9120396050040903013400c1c441c0a09640702e800344040402400b0b802c041c441916060900840390304000d0028880290010b0010f160810200e07941c400c3c9240c0d004010660ba90f04400c61940254042442d180b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 709352517 1106 709351411 709351429
    0x2030a0f0302060901060b180f04090c170307082b1103060a0e070f030b0411030f040215210a0b030d1107140612060102011401090902040b 61
    0x1600c0c1c041e10b41640a800118941d041900074041c0264000503600540c9000c0da0f0310904402c1e06012440c044031085203241c006042c42814414030603002d40c280201c40c0121200c81c0c0e510100c148040c1c403402400b00081c01d0071300030800c0030469410550180f09160608884201140c41401c10004071080000f034540741500100800c0342903d4080481c800400e220454a0143d180c5988010311480034040d1110900d40e480e140010a40c485a2040d480d00d07440ca8a56a900d080c0100f00c0c04081034100d80c128801c4c00c1803141c440740c426070241501c030704204071121280720020714840c4210200c2d0003001c07035aa0a0b07468a0000041e42c0800140550f40c0c42d94503102d18044191255071f00b4000c0540003094003011b80311442c1c246d0703101c40c1d040700c00500310026124940d840d500d00407405885a0312014034140340030000850303010310b96440041c1d20b03071089900b0403a43d4000b90034062003038 = true := by decide +kernel

theorem cover : BRFrame.Cov 709172661 709352517 := by
  have h0 := BRFrame.cov_init 709172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 709172661 ≤ n) (h2 : n < 709352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
