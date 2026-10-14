-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:43:40.155988+00:00
-- url     : https://prove2.me/submissions/767378d7-d017-43a8-b00f-e37eeb0fc46c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 14028783 ≤ n < 14208639 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 14030033 1250 14028783 14028823
    0x901060e030709200a020607030c08010815091c020618010903050f0d060306020d0203041106040602151015020a0501050c0301060e0112060902161106030702030316020f2d 75
    0x91640c1e00107151844621004500c4100a43e0b01030260740010b09511703095030010704403450f00c094020709580000301407404000b404c5004020720000016032030800da4075016036000d00d550b02e43c645890103141c001506652503507100000c14098010170003500480261900d02401c50002c0006800e880d00003400a0000c0c500300b180c40e0b0f43c0c41c1e0700c902504040b540c030386020030010707a43e81341d000030307a08081010f0704515400400d100030844000d000302c50700c8030705845107800c00380f821034040d490350310481d407081a8030f0b500c1002440503400c2003449409001209201405074521020096503048541400c5401c0c0d0b19040100348200c1d80c20f01aa81210001e42e5899600e070880320045448405103800c645980c0e49446002c0303001582c0d4005001c0504c0d110031003181502a0781094005d00a203007244034010103081003404421580802120707841013500c000070040b14514142240b401101004a81c0c43d402002411940140107078142c0b80c0c184204900781c4c4c0d181740122003c4e0344170720490540440300404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 14031283 1250 14030033 14030039
    0x105030309010929030109020903010e010603020109050f0d0503040308071202012a0c0b01080309040f02030105060a080405070306020703020c0f040c0c0201030e0102130b04030c08060106050426031204020901060e0307 95
    0x2400d984d040d494503110301d92110301e0b80791512041050300282c1201c680c00e9004148a00c207420244100c0d04a13640f110024040340d031039500081d1480d40c0c680101409245080507036400341e1203403400d002c2810b2341f09003100d03070380d50f602d0808a2154000c014225110200f00d248031204510500a052a07000d108030040003400291080d0076109110703034030020034800002c0c0202c0110b1043d00b8658000c2944c54041c2d65280c00c14010030086070001450081d00c0e5205000600c600c1e11060300340c620011650820300c10645650514030714021744c543c0001e08031400040d00c4000c05501080c3c2d8018903509540c2c0d580606154001c1209442e085c3d00a403000842900c80000036611a4004c0710017089000e00040c50f001607011950918400d9400c2002220400035041040000307100143c8020500034015001d15410000024203502c66442407a100c17500e60800c007400c103808075038240b650b140c0d500122580c0d8910701e00c00408072002164281d01c40c0340e0040000840e280585501d1070203000003409085d0040c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 14032533 1250 14031283 14031299
    0x60911090c1602010e0402030f070207051909090201020a080304030507020a170c0f01030b0d03110f0303071407050c0d06050a05010602010b030a030309050f03040b0408010510030f03030b010216091401050303090109 94
    0x2039800c001d07410131030301015980c241c6d00c0358030007180607240c5070340c0b0402240f43c283c00103460429aa44001d005d503080c20162641810202c110340203403401c202001ca42900c0c5400100d00d0280d003810054510706001040c8801c054201c0020702c26a03100b40c2c0c440c0081039844020f6080207102c0b00e9600030b0398012780412115854000c1d0200c2c0c1410050400003500450741021070705081c0719510460202c1c80045694400e040d08002c0031801c07502d450015840c500c2c0c54000140100750b201c0c10040310400200c2c2d90010400140a50b900c05403000e401320880460701c0c1040e0028010a4030030f44101890100080352092040c02042c50000024008020f1840c140d034049000b0300d03204405440e10301802c0c0c2010198101400140700408034010340039120383c185440d0340c0c01c6131006840c80303018103000201080012192400e0380340305601801c0c00243c42c3c3c24000140c0c1000e044003a442080b4841510124030700c105a8805142c04580e00c0000b2007903a02c580501d035680c4100a0401c1c0801e0801004000510b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 14033783 1250 14032533 14032567
    0xb0604030f060f0204060921120804060609020a030203010512071401180302060c010b090a0606020a0b07031e06061205040b18030c0f060403080903070201080a020310080307060911090c 81
    0x284201e40001e000d440800003c02240c02540140c0006040310b0820080b0140700748084100a4450f0a010885e04440c0d449952503200194082e05001480000800f0722010f54041c0e4028242c101c5c0643d902d908950f4018000e6109001b0640f003a07107141c0b40020100c0d0000344000c00c0d21415019030010302d200d203006545140c03403604401c0b103c1d4111640480140c442001510601d42d40b00001f2480658020070401c0c03290000341a001c01c0c0b440d100d420002e43ea4005816600a50054446540c54840041c100c01521643c8101118885005140c251307502c1da42d401070040b1030440e1303120314407410206010000e940050310098a0400120041422410b003018070000050b400b0307003100e01c1c12000000e01414401201185200c980110040106042c2c11002e02030303000c001c12000d14540103031980041d0420b2070281010f2a00340d40480003071615001884014050101e4000301d0f501c462040ca404006003d100200300c07005a019180d01086e402c0c0010518000d807100ca41e0b5a0400400c516410050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 14035033 1250 14033783 14033813
    0x708121006031a060d0b1206040b090a12030507030b0301051503160506040510180306060806010905010b070b2205100c0201092003010209060301080309040605060a020309190b0a080108100b060403 86
    0x980d50314550340103561f450300511284e91a0b4040605010325050a10703200000c030060840075103400c9904040001203482540b8401c5124034100041c0d00d031100031007240101145440c0030341642c07800302846030b50218060741c903201120440454240569500d0000f0081119208450f0008800e00c410b001a25102d034402041c501213161412221007400605962851150b00135100c59903141002d01680351b0500c00f00c0d0151041003020310095251111341c42003441801d2020700400c2d0703e90040703000c8903681042c0b105c180c042081000040d82c110300300340d03072903c105010840c051460606a40206030040c090144240c0e0000c02460300188100c1d004400c01200385800e55140d5400c200c10f00a541e5110080d5020b0030441c070007507454000c600c080c0822100560042c51040406101c90a001c1364000202d421490040d22400c0340d0701200000354160a903583c0040c0340701403002c281e94000301e9004d03100030b040320041011101e600e4540c48a50044520496a031760700001c08020a0000c5445405407810b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 14036283 1250 14035033 14035057
    0x6041a01050c0f06010f06030c02150a0209030c100201150909050d0c0303110f0d1a09011e0b03070507030206010e0709090209011107030b010501020c0105090307050906060708121006031a06 83
    0x21028020f504a81804404d0304122200c904800050116650501c100001c4080701c0c00103115240e40ca85600350121002800c090716a90001034205054600f40701e03c60600303802606d500710503120340c68081c2c0640100809802c81012a6400107124170a80c00340d03054407a0080003800404590920841f048511840144c040c5616000c0c1200341c40700d41c2d03006142203205288400c0d2a41c502c0c0c0b1500d416603601c003402181c0c0d89451013030b8105c0c981c0e48038061811100e00491109015080481b05011807220784d00c241c80d0220048200018150440d0003820301c00e10990a54601e60389a0b960060f59400913101400012200741007032000e00016402800340443c14100721b81c1002d114011b06103803042075042102ca034080da81c0100003c1d42c0401140a500100342002400d140501010030381e125401d01c109449440004003003101038460804584919400c0800c007540c40c419103040250181e0195250010022100c40009031584240719101e26000519600754144004400f0031030207802008404174 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 14037533 1250 14036283 14036293
    0x30305131403070c1d0718030506010b0301030501050606160308060a030b1e0a020705030f070303060b0316020601060e0607060914010c030608010b03031912180807050606041a01050c 80
    0xc10103440807690405810002540d5416807031500d403211465503803001044013034580012503001000b40314141c0c0600c0d24940b02030136a20145032503603075416075400904980540c500129120841031f008605a90250000b402700d5102c5406224151080920741c1d03200c000c01035004030000c1c0c4601e5095402c42401404201c0316901d986440c54202c1090314458911508180d90300000d804120340e1030751001c04000210700305082030b1140c1d6201d1203000780202d03840e20001400340802d80030358005005040c580c4c0b170f070684034604032903101720b810050081c0d80050701c00c078000020084e128074110a444003014010600305502591408003800681504950301d00071140e25003440351091141c4030385000030383c0c1c020414034034181c0d040d400c4440c90086035001b80c208001d40044500c4030200417840304402e1500b1124000305d010100014001011201c4503038000e8070019050103601ca016080c3c10303010300306a41c000d440c0c000400007141c0b0290300c819101a60000c02c0401c96010748081e1210150100c00d40c0c6c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 14038783 1250 14037533 14037571
    0x140a120206091305040c050f01051b070e010305070e0f061c060902090703020a1106010501080f090309060a0306060e0108040506010b0708120f0106080c040f09021c050a0b040f18030305 81
    0x83d01801c1c042c60300e02c40165076004000c20721645070020b41c010b10003500c4880b101c003500c00000b0b00c0761040d005403a003030310001940d0030720081013040560010148040c0020b201c0d40c4070f181258442c0034511a1412400c032900100c1d03c42d402801c0502c0c0952001403034000900503007a0020f02500d46000180c4415580c0c0300400d0250b26015401440780095a40040c0c2e10072607482c020f040ca101d145888030709940102d0051145076040681c80380c114001240d607607c1a0f071103a4800d40380d8450704072400c0c0c0241e00407854104403034041d000305050715050349034500c0810340000110383c0f0080886000d0000d50040b0010000480810000c100c00340c00b4401c924640300410b0031520408200762804201d02c100d6400420010780d0043c2c11030b410002004800d4a81440c0200c4059031035018002c0c0b0140380d034009046004a200c050646da9140340c841802d1105240841151307000f4002e4140c40303401070b400c0040b44240300d410340c46441005c000c2c66289800e001400c0e2821002004004d154030f030075041d0500c90b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 14040033 1250 14038783 14038789
    0x30c0106030b180102030103050c040e0a05070b040f05060a0c080a090b0c03121312030c050405190501030501090b15090103110c010c14191103041d040606140a12020609 74
    0x250010354000c1400328010b0802480c402d0f001102c0e14100d4146910500040c00020400314454948a00c106d0340401c0d50000070303081c94104960b2100080dc2d41c132031840b0006210f00c8602c054800c440e5a460003d00e01d540e1a001d222040c411030140000180070b400b03088000885090150072080d2003032508400c5c01c1d03154608100c480e445003040001d5a880824800c0300310076104a4143e2001c0880100c10b4070b2030b495a40c20140c0750044402800381906c03020182542803240040d100202801000440c2801c0300f03480d0481c0c2030095001d41400207040c54000306550000340280c00f917501000e0621070703460803050b00c003211503005100c50504142d1109480e941030300e5441c018210746c45808000084011030007001900440c222040802d01180c01d006c89020f507840c0450480d60013055052000d026507610901d24158880c60700288103441c800f1000c00115800b90048030301c038034440c010800c551074440d10480701c184004900c00e60303c08400041400010f0608100f88030941c8003a0181c3d05005c000000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 14041283 1250 14040033 14040041
    0x50a11070909050a0b0601051c0b06070803040303050405060601020606010507030305090111070b0901050121060e010f0609150b03010e0106110a020d0b040b0a05060310020a05160804030203120408030405040905030c01 95
    0x10a0f03450ba840442540144502e03144d59941004c002d081040c0703085d41a88011110250710704a2071b0120f56600c50705034443c2c48000c100e8041e2507011800b40d0b564a0a460040d008002c107130703415030341c6104aa001590390750000070030304d001e42016140c1d81e0802881e0f90b001c070b000d03000040c0820780302c2d5210740112201039203c501800409104806642e020f00d40f1507051400c5910507841502c40340307000380c00903110151020602c0039180d0440408640110f458000a0140405142c20505149008400100075503143d1201d6101c941c0b00c01d910034503035900e10b038a04d0107000038019032405c068a640108003030345c02034105054080000c000d40b8030b80006a0001014030300e0501058484022a00070042000200e00000358800b181200804c03440c20301d0004240d8501c1da0000340502d15600041300a500380c0603005841900c3c41d0362007001c844460511b040c0c01580c01c1480b00305c1c06841080c80072070200d45294162000e65540900035414603103000708110141840000a4509000401681300c01c00c0c001c1c05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 14042533 1250 14041283 14041301
    0x9040e03040611060a050c04030201080402180109020d06050105070507090905120a0302040e07020a1220060901020406030b03060f1929030d1106040f110a080f010c0305010303050a110709 82
    0x41d0f0310340100300c10350001d003400c000a0115107054609400c2110354090341d4291416280c080c03034009803a65651001c152120300800d260744c40c1d24542c00c000507021555030018581c00e42c45c0841440398650301c40c0151007900810000401c0c5030000d000c1405880e68075404075034254090422202044826502ca882c00c0d40f000340c0f0070380041e80002c0c2c01d0184036001d401d0315800140901c01029101d070030361540c43c0008122010002000594907a100701410740d607060100400c41d240503942d039401c006800354000d41c0a4410036001c2810081100f03250300d4041a0070388120300110719881150303906030116203080300302400a4181d968804101d03d0110b505039800c2c60200847c48036000d200c80100405103410f0b1080f90120410914000280c4441d90220f01103030002d40c40101021450154540a581850050f403c9600040021000141900300094103054004080020022002c0d50340040f0141c0e00c00740409030201c1e0081244185d010312400e00480310801c1003013540c040a89030440c01c0142c60f1124 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 14043783 1250 14042533 14042537
    0x60b03070c02010306050604060206072001140609060a0b07030509061216141321080a09061103040b0301050d05150c0a1202040e071d030607170a0501180209040e030406 74
    0x10704840865826102e24000b5010803580c03181094034004009603514001000f15040254603c490f1081c1d040e40d00024500c40300c1103000b4018058500080050342070211030030791103602c1c400e003c22501d082c840a5002030341e92171390f403803440c143e141d450568960340020790054025804000b15080d00a9019406026004400812a98080c150001854040c10a2510410480820a48260090980c41c15045030080c56903420f512002d0407000c40c080c40c0c03c2c180509007480000f40c10f0070203a40f05001809650403a00ca4800070b00c000b100040c6d8a005e0381c0500c000c1b06504000501091a11080f003516086c0710340200c5503070240c0e4568011202030103460300c40c62100042440404150002c002410105240c3c400310305061806143c0344009501410080c140001c1550641c0720480224104402d03c00c050b00310362050401ca607004044c0e11101d90944012101c0d440840c01000e85401900d048030110715a01c0909211400703481c009601041041d6405552607047e8240e03182d050010f400100300603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 14045033 1250 14043783 14043797
    0x4030c0e01030201020c040b0f010e060904050103050609060c0f070b0c0c0f0705102303060109080312160804030801050108100306051509010608090a0b0a1d010c0210090209040204020d060b0307 85
    0x510001e031400308003100ca10f200e0f80c10201da40d0023584541ca03800e0034041d42480d01c0c0b00d03208840c00108010340300e010042c46c5c0140c10f00002106206c0002840c0d0700807200c43d07048681540e02c90301c1d40b0840c1c1c040c540c02102c40300020030200001c120140109038001ca00544500d140046510f986450884152507103207403500500d6080000340343c03160980c200002182010509242045590003071003500d42c4203c0d02965011000c40c0f100c0e440750703004201078100759044968a248108101c0c000c50310441d40e50524019000c1c051019070f00c600c9500d401154580c585100f030b030b400d01d4015a40c4060082100e4030046140300000042282406190700810090141004c5010034109114440300160000f80601c0550020f00c52031440c0000c0c1035210980001c4145003540380e02c15082c0140640210400980b04002c4da02050b264040d4042030400750361383c00f00c8030b48099095581c0f00f9a414154007a6002ca0148001005810a40c005140e0420303c510001040c6485194914080c1c005580b014002880 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 14046283 1250 14045033 14045039
    0x1308011503050c0f06120703020c0d0c11010c112103040b0409051803040e040203011b081e0121020d0602030c03040b0c030103110607060905070909050111030c07030503090304030c0e01 81
    0x414803d0280c444019640002403072030b00c901042c1a03103c0c20154810410b00800005c048902c260b050b600140200d0301620782c0340504000c01000040c404a0a43d0a400c54150809040d8040d512034044141e004d5426040303000b10104100c04426a103500464a0405c3c1d86ca28200c040c1c103000801c007500100c1610394540d41000e0141e021603a000300011447c150710805030018a4000040d070702203440da0262801d03266a42c0c408680034081d0708100301c0241e034a004100301c849402001151044840784070301018661035803020700c208031082c0b007003a01d40074044d1001c514a5911500002d181d42c0064510703074101003180e44285c100e81c4115182c1c025428084184000c0200c01207007107030070204540c0c40310300390f50441d1200641822401d883c039100314030000d00c5208102541c2c215004150f0000181d68406907151800d102502c60600100c03565480e001c541c0d86254101c0084e6801038040027586030400e00c05503825115030f4009001c03544148000d000c000300003903810350300e00090a42401e1206c02545 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 14047533 1250 14046283 14046293
    0xc110d0507081b0a05030705061b010203070503090d020d090b0a05040305160f09060b0f09040f0e06060a050a03080301050d03020f010f020a0e0f0f040506060705010e01020306030f03030115051308011503 89
    0x3c81c1210b02e071041c0410401007046940000300c040c01e81d84216841507442e1811355002c1c44140c8500c0107406c0650000c001c00840503005000780d417083c54050709558401032048002c0340c43d61015080034003c00c860740720501944409101034030b407000480c02d010307192035201c1e200c1d54942201c0c001c00c07450400216405000c4454540d8100c0d00901e402e410522445080c22405071203402810200e440c80403012540440c0c66503240c01c1000c4907510b40c14200076a600c1d03840010f407100d4081b1802401809000000146400c1000b403240440b41c0041901707045900b040c040000c2045a058103400314440e04d14940c1c2124030a216880120f48600c600607695050607101a02a203c00900d1510604590742d00d44e10310f444100454143c0300c1c1c11500020709a90b4080021079038003801001814035841c10328024181501540250b01415080f4202ea2103440c401c40a142d4a00c403d000d0007442d4030326080a440c809001700090001d05100c400d000f0030701502d8600c21801c545060442214101c9280e80800901c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 14048783 1250 14047533 14047573
    0x307081303170408071203210903110d020604061802100504050103051602030d0f0f090f0b0a0e030d050a06120302060a0501060305070e0d1e0b010f060305070c110d050708 75
    0x480c601080600f400d280c2019203480722444d10805071080a0300301c2c6601058030031160401c1c5e241182a2041040541c1ea40c044014407450300101d001c240c0581c14030780002c000007060350201400364014036140c6c6e1160754510142040120340c1c40c40c1840e02550782c2c01640c2d21042d10380201344030381da440c0d1510320f007200042c1034400c09044104240300c0054640541d40d40403003140c01001c450740300882c002c0007041d8020010030f0100b22600c0d400340f0b4403094004003d1851044130b802406040601d18603146d0010801c1114103841d88020168420049896100c0c441d81040703a0025911000141140d515a0382544040452074100d0058220104004c2e203d140e0344140790240405117410402c61030804006000f442103000c041c0d110b801c0f441c291804000e1030707a81c01c0440444401000380c40d191685800c0f90313410020701032a0040759580e000494410b00c42c0c8640c500c40c042c160b81d44a0400b0064a4003e504140d240901d42c10460b029805c20110b00104400300c000d0040d28000c0c961412080ca204a0b13807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 14050033 1250 14048783 14048813
    0x303050a02070c03140a08030709140901080304060c0f08120601030c020d020d050c030d090303021e0a05070f02030c1504141903060b030a060603050a0b0a02090904030e030307081303 80
    0x1240c07051003602d011800d0f03280301409990348132140d9280e20700d481c00b4040c9007030481900101481400020014400c0d0310420b8001103901801502030003a107580100113410100b40a40b0134658410b00042004911038580f00c1d02c40340c01403090307000c2c48610f0384030407819500840f4a42e8024800c0000e209503035a0500c11190102018070151a500110384002510780310640b00301c404104001c220b075540e104d01031007218507250b041d480c1041004024903002d0040d410500300d100c0300b080f0b203032000d000207a100411107001c400d0a54402d46072a4560343c503d40d00d8000500160f805119111007842140c6402c070710144070303011500c006601c0300e190450203614840c2e401c1c1002e0144c401c140a01c00d0f00501c800484091326400903010802c1e10b08030001c00d01e844e0324041c0140089091503000002d0050105200341643e014042c030f41c0066460805e41c2007a44030b10408250003180c1e4900140c0400c1c03095808103a00080203059921300706090311200306d55007100c06030034100c3c800d4000800c100b10014400c09a9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 14051283 1250 14050033 14050051
    0x803070b0103030509011205011404050106050a0804080a0c0213050405070b040303050d020c1c050309011401030f021504050d0501051602010b030618070512010e0f010b03070501140f16030305 84
    0x5009015554800038060620004042c80400b143d120401d84c021210552040d4000c08100a02c0d070b529011500405455803000380a40d103000c1c00800c2151203807003101c0c1d0b01c5040d600d412540351602d81c0c1d0800039a00c0442c15200f080f41350320780b440069032285400560741c802040089941d08040c181941004010ba100c1004040e04110410001750408203580800b07240300c1c0c0050311514000d409030704003400302c52803c4080a00d21014031109400c800554001c21048000304500c00d0a402c50a06d050f1080c0005802403180209000052511080c0c83c0869111740001d117082c01d54541c041145c1c407007182c2d81102c040c1d46460411601c000c0300d6000d104052820b200070b0101a04180200e6155400508014400f444202080c40c80103820814100107007005007008844031603444809008080914443e032550081804200480005005841d0a043c00401070215980703400010f66850741c605c1118a00c500044c80000c08000b04e880c0036103000030045000b0b0465074151301d4001c040300c50040206c07007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 14052533 1250 14051283 14051287
    0x201060b0301181e090305070308060a03030503060d030210060f0303030e0a02060306120c0607230a0c060e030106080106030803010f0e09030f030403020c03010528050f07230408010c090803 83
    0x1980804002040c3d42640229001810596112080e502c4440404403412154100100c201c1010b5004008001030b40c001da441d0075054580c0e408002d04940140b00140c0011420b0010480d18504007d946100e5482070044606c20004090f220054400c1a40640d01c3c40004107410814150540524084030b0304240c040e104444a5600085541c0805400b81d40200300002c03c401c080b01040100c0340d031006000f412107403035039503d28022815030300707a5814141183c1011110a48000001703043c600e5140c0c032042041495007032850403903886029241d001d0b410342d00c1d118009412002846414059800b40d4207480c0d5a40c1803480f00f403154102036110345080e00b440070400074401c0d40801501c62980f00d192105c0e549440c0e03070804a01c1d142ca1ba1420070f030f0552804060001c032818444078811160120f1a1400030004401c0100c011602d00301c42e80020760380c94000040409225400440ca10456100c2a11061456041c5ea9005811030307001030780d0982d034500340704007544d40000301c0d2001001341c100158 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 14053783 1250 14052533 14052539
    0x50d0c02031303060c05040306020f0d060905090a0809030106270b010212190302091e100507080912030408100b09181c05040801020c0106031101080103020d030809031308010b010201060b0301 84
    0x802d882803444003508580d03856581e4200c1c1c0d8810400c6a0003503801420035526440c801c0c000900070760010404441040c6484800120383d0018064a44074100400c054000c00d011030f180c0100381d500c0400706079410756075000040b440306c0c4054040b20a840080384038028070340032600c010302283c9000c1c0c40d003411340d0720496240303005100c6441156420300d02c0d007101da0b40c2104c0e007107400ea019016600b05182d119044030710701c00c0780109003200c030706030160112000e4005405901c0d00f992148070710380700034007007031002c000994140c14001c00b0901d800006c24110303860b0903929940d09042c05070310b031040b084054640314400f40ba80b400201258105c44025140321180265000380f1745c3e00c0d009207403407400524611400102c0a03018a0035070700140312040084d9500c6040460301402450a40822226201c110700100d80c00c1d486480c1581c1a03079030160081e40d4002d80c1c1c2d1019100341100400380f00c007611003023168181040e02403025000402c000d000203c0d00000070303800a0f0a49406401c808403200c0c4c184010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 14055033 1250 14053783 14053807
    0x90905010c14040902070305120103110102010c090609050f0d0501050f0a060e0f01030b100b0c03040f091104061d040204030309031505071e050705010e0d140304050601090c020c030706050d0c0203 86
    0x48040710504c2c0c0c80181e0b18601860151214090401405402c150010000007400803054040c54210000d0313000b082201d003119001c0d2002c1e00c0e1b07070048000151400708203002d642020000e503010a50020030340d47c500c6000f6a9500d00707580c02140e0f9160018002024000b41d900340c0d0041a000c0c00c0b41e485401101c1c5130005036152030060500c0090300070315000011a8494100340d4604001d4895042e00950f9010420310302944da51003032103800e983c43c000c24400240b0720090702c03038440c00540001f00e4918262501034122401c484c10401b07440600d0000315010107559031342c80100020341c4079403200151941f9506108041da121803d40122407824a000c0220069214540c0e03100c400d1180201014031a1901c030032138540c040d0303841c014940d41c0b034103e602d100160300007800311180050b0741c0d8150155094003138141d102d00080c2c070000c109034420703001404101501e401442418140d8411030320100c08400000345080e415030700c501d0100d00d0000d683c2c131003070310b85004030004040c4a000a40c40c12080c1248 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 14056283 1250 14055033 14055037
    0x5030a0308070314010b0a090504020f0412050304091514040c0801091508060c1801020a0302030a030b060706020304030f0315031106092e020c010813150e07090905010c14 75
    0x408000c8041c0c00149000d0081d40000e00c0e103100a001c0002640c0c48000d18100c5500c004002008550b0070362001450749058002c070344010284454450800d403420701104617069080c1401c960900040c80081954001c5200d0410360109100c02480c00c14985070100146141d040c0742c2c540070724102008800c82c141c201440b01e04455007220002248041c9039410200c80b1034507080741c3e20324000c00040c88807100c2014003070074141c4404c0e250394265040e10740040e40e4880c3c07000401009a007040c004030301e50a00a034081103441c400689510300d0908030390385640c103d038001c81d401c4011421191890641c0380d40f5200301004200352080805041e81903417180c030612118242c80c0c44c411500081c189281c0d031a0300e001400f40c8403070941d008841d00755500038900b040308000640740051280310402c2040d036208481c0f96008040156201491200c0b50701c1d0382d4244d0074561003000440b81c07901e005005043c010881a8002c1c6092000040c003c2d40901d442400e4541041c4000100000c00e43c110106601c400e003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 14057533 1250 14056283 14056303
    0x801030209150103110d020705010c1e08070509120102030f07300f020712020c041b0e030705090a1406060c03030c0c07050904080417070b1803011107030c0c0f0503 72
    0x1a1912080d82c032400100d026010b91840e052200501207449603006865402a09640b88244024040501902000c031800c00f07800401c43c0701840070710f00c1143c94500600c0f82ea03070070103414600145410340c40c6001c5400c9203403a41d150100f03a0b50010030030444036811b441c1507030802c1356844c1400c503151581141401d9903480403040200345012180001d49070082d079100510008010340d041d074881d411401c004140402003046240540213a0306403003018502842040700107401d00c2c0c01002d50503003101e02181c10803000100c0c5a00352151440101c0c09036200070015110b0310801c4c102003184214407808000b1083c0c060222402894240420004014084140c0c0e5014401001140e120b0869503c06c514290440d400180c01203000010301007400001070080098401180c018040a8001a40305603908610b10641501000038003250301d844000c1c40b404c001c610300003000410740403040003240d1065800010b00720f000c00e840d04095410002161856001403001c41d4210b101c1c1460800071a0b100c070007a207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 14058783 1250 14057533 14057551
    0x50a0509060412050109020907030b01080f0c0c070306060612020c070509060d17070b090c030705090a1d060106030b01021f05040602070b070206040c050409170309120d1b0801030209 80
    0x1242032540e40d15603400b0749000304107048998001d41d5050501c41d00030001848180d008060940020f038403140039004000c0d1482045c2d40300b4136103903141e092141c0d0b02500607010008000c0c00b0015804410001c0004401441c0110400070780e1515201010708440d120210320302d030341801409141c0ca940c0000ca0100e0417940e00b41c68156195540400280d20300c000701d4001805040342e6158000e444610801800441d8855000003080e0f44401c01b81e07503500d501d10800c4641c1640110b409101a05111100a0300100c54a4010a81c65040c14020400454404030459507a0100c801044560740c14011a4030a1800780081c103401d000c000399400008030300d27600d0512141d80f110003050401042c3e504403508503401c640308142c18100104000d448900580d02500c4400d860332003c01e20b0700e458429040c8141d80441901c021480d1103002c055584c20080050205029249505081c50071050082c402d5200c94000001d120489245204c216044800e5580402000d0710043c030060b15a00c09a940003107a031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 14060033 1250 14058783 14058787
    0x61a04090b0102011104060e032407030b010201020c07063204090507090b040305060a060b0a0509150405040905030307080a050601080a0f0b0a1205060a090201020a020108070201090516060206070e01050a05 90
    0x1100140d003d00b05c0e8050310031541d00f0006000500c21b500100f90b4a0850044080d5103150405140d03180741d20782c82401100c010306060780032488460203507100c0c0728541010300005d824041f02d0007025051541c6030744030b0310114400d014001c41640140102221600100c141c0e50b0203028002c001344440d00031800b40300c1e03a0a50700c40110754028080e940d01c50050198140041d5278030345900e095529a80150360000c11641040300220b81d04800c41c0544a07011180e035030385070902e44031804100c1858003202c03400d00d06d03a0081001140e01d44850162007849030068004607036a04200600500303400c40203140841c003030f14003030501055030707031014100760018012207020032542d401c01361210007008240e400b1584807555a400261603d0104480d81c4c0300c038054400d131803041d40c80a0300e8800707a40321140b000f40182c1250300824015030189502c541c01941e50b01c00000c0c8503441d642e0701454052030b800482902e20000b402084855410040305520031107034038007191800444400038110780102000e02080c4100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 14061283 1250 14060033 14060051
    0x806040f14030c03040f150201060602030a050f1201060206091009050d080403110d0206010801060f0302030307080309030f0a020102091002010b0307030605090f06040c030302071208040b090a081501050103061a0409 94
    0x8000f6940103000070b1090304d580f00d03655034000082840d24412440e40d01403880c5c0c000480390043c4a00c0781111800c0d0080d600e17000b0000c40440e0070f58014075500782c200c0d9090002c1205550036003401c0d40a080b50b5002082c140c00c02c40d101a03e028440c3c440c001d03c075810003840200080020600c4504031135141460192610749241c290707070441016142111a1180350b170040c804175400034406040b0347c080d40080000c0c0783c58004d140c0c0004940c0c000030390541d004101500c00105640010341d4450650010303030342024003018031545503910a60813900107070b4002c1680c00152400265566205084e40000c01034004090086070311602c2c40d22024100c03a42c0daa0000e00c2818041c0800d9849905a100f43d521514040c508810382c21890302054005226002000c01c00e80d00b110f6140d00d20710340002d91142854a0034107000510f51207003100c981c04c0743d4100700000300d000d0100a10040c200101c0b003c2d00566041c8000102190296840300804c4c81e07000c801c16660514441c112400d03580c80c8070010803c881 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 14062533 1250 14061283 14061323
    0x804090c0c0807051609060303021203041704030303090611070b0402090405010209030a0c091406030a0f1106030403030516030605061210030206030c04030c06030c050a080403020c0405010b0406090806040f 90
    0x300d079800c040d14120001410400b08100451001410f01c51401a075005a4960441c54100c03103181c0001009640040f6080f481c0300380d02c1c0061640580308800040d0802c13a10503070b00d8007641040d4812800700b5140c1404c141089000c2c080c0454041480c9481c506040341030301c0e410825031025101900414801c0c001c01d06001003074044a1400700301508442c8154024905139000e001248900800c0e98609055113055060643c207143c0a084001c004091540c42916103954021803801c04480007200c81c5001110ba4651401075845103000b0b4400144034074000044980c00000000310404151902c40203000580c2c0340e505448030703e9288540c40c0c00c1592001303542c0725542c80c50b400c023a6000304003008010464000c07130014402c2e240324507411000c190341c480301a802c0d500c4954407030000c1070041c8000c100b5288100314407a40140644111038292030744201007401c0b0ba4081c1c1003c03142c0100020248042604658000014007040008180310b20b015161042500380c1e242004040c204d8407a030215002c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 14063783 1250 14062533 14062547
    0x1404021603030207020a08061009050906070f050c100609020c1605031b03010b0a03051e060c09091512010b010912080d0207080403150501170c01020d11010f0f02030718030804090c 79
    0x1080b81c1040390001d0a0550311400100000cac801c084d9000c0c01e01c80040c403103009c0411050300682d60343c0c581808400062105443c5030300251100e4109106503545070200b954940030f04030080090312030050391007100c4889142002c00801c44601201c1d46090108940e440000d481782d84036011445407040d021080c0b0029014140d00c0c000c040c3c0c4282054400b000703000c80410654800000b440349107000c0d0321100b150710303210701e811074507000d4840c818080315116003445200d01d640800312070344070101150034100040400419240d44000d60303564040f001295604124628054820711003c20030100f144e84d10100300d44194103c0f1004a60041500d1040140000c25200a554040036070509a444409000003c000c01d2080300210340c451541508000d10104a8403c546410790244c59414848903080e81c45031121480c005866607284100078140010b4070416001e9605244d01594034209404001d100403010210540b40c041d04003402c10000713100300200d50071100d04810200e020702c50740006440c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 14065033 1250 14063783 14063789
    0x51510030f050405060f0618060d0201030f05041505010602070b04030f05010b031203040c06080606030402010c0c05131b1b140a061b17060105120405070f0303091404021603030207020a 81
    0x5035007014140300c01c04c031000c11001d01c0350ba425451400c0c00d640b500304214900c0b1000d00c0c13441807440301e031000c101c0710300300521504901401810003107080794065100b0b50844000305c9040ea0f41109680a202103c04179000311401400584010000f450801c4900403980c402c0f0310000b0310504600326030804010013900000c10107007008007070ba6440040442800c03040e900c03c81d0100c07141c825030880811294041c1c20b03107a029210140103e81983c0d0366600550700030001c5401075880c0c003455500002c00b0341e5102103081d9040d003607400204915600ca52400c3e214140b9032035100c1844134506000200c0049652100f401c580c00201000b114040400c1042c10705090480103016a070619140f404c600d0b10a4015542e0b00c0d199658182c05240f1050350000c42085c1a206c180c0001e204100c00405c030030160900d650014014008e840e103059640f0b000007501c20740e0354001c5000c140713240d0082014400310526480d10300020f072000d61411020703c3c2200c0da10024400018285540840c10a081d926551194030103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 14066283 1250 14065033 14065061
    0x2030715050a02010b060a05030402040b13020415170603060403140405151c0501031104020702010e0306070215010f06020a080a031b110111040e06100c0b0f010f060305151003 77
    0x101003000800418039840245400c0140d0b0814000d01010305104003114450155541e0319030568541d41c0c2000060000511040d40c468500100400404007078401000100242c0b0301c45d40c803498860801070400080ba82502c00301c606420100511610089101c43d4803590618003000d0075000e030f580c030346224015500166040885880121140300c1c07084010186010000b8405005280b82c4401e20140c52003400004d2260440084003001030034282c000d440d880d07105051107601d0442e01d030701081ca030a60848200e070043e40101d401800806e02c1e0b82c0d526000d05818071014240340e0800d81d01035960003a1700d600401d072000c0010300b00c80309482070348282d500c943ca4501022a1082d0b180d4000c04c18040501c2c10710300c551074402c2d1900300075500005c4800b12045c901610341b4079503031001000640d12002c1840414402110b2459000a1603500c4035440f4299241c030071002d5504000c800c118800842d007049051501e4030092021022600c03201e404001004c0318050108003c1c880f0480c083c1c00c20304000e0f05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 14067533 1250 14066283 14066309
    0x20a03050604110109090209030a120201020412080d0b060a0c03050a1403040302060406150807051201021605030408011a091303180306050a050703060605030a02030408040e04030201090b090304050a12020307 91
    0x40000f0072a4446180000f43c1c0d403a000746840311000d600705c0c8224500507074590700c22005440040d2413001c460680c01181d000060410799101c022040c01c44500d8003c440d00f42300003545070011006441100c003c0003003500e055060940c07800e8050100210000007400f8010007042101a4034440c80c0045100c4428055890b01c9091078980a543d17000165800c9946c03500b0081895040210b0081c4c80e01102c3d0303e070000f400c40c0351a050030b20540500015000845540130000c16420403112601405910310075402140c0d100c0c03401c280c040c211141550000c0b541c0740d010310352108641c0d0b00503c1c0d581016030302105912441551074280c07400f0866000c0341138540d01c5a00d00006004650780114401c03800f1042c03d0045564082c8111300316481f03400350f28007051081c0040340810403558046d55009128068131072030103444240e41c494160045404500603915070780d4403000c00c9007010803950000e50741d20003542806d003840000b409a4013a4002e44000401e8440300e14150b40d0100b1003800189547c0500107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 14068783 1250 14067533 14067541
    0x120209040204150807030e28060609021b011401230a030b0c0904050c030906011e03051c020c0919110702040903021c02030c0705060309010213091505060c070e04020a030506 76
    0x10b000340c0130440300b484c0401e00c2c0190845940c0b80203c0e9003810b0b02c0d0000c0c45041132416124610743c107000701641c2601c12543e03680f4007103100c5009100170a942e0303060304804010145110401402d68501a40355040181c003207004109801c10b0140030071707103051030131200814640c410010840100c0182e1024010303541c040d09101e103908602c0c004007841c020654050140d659000b0101c2d8082c80243d40c9580681e2108004018950308102020b4861640c3d05419010715500e8580a04c0c00d407401e01c1e10700845110070400d8041030380420000c4c40d900026209030025180504611030000c00040d0f43d07203070041c0c5800145181c000c1c030030201e41c3c200f80c2c010801c101e11103583c28025075900c02c41c020100c0290144070f601948500002c183c800b00c041c072400404940d070800707060001d1a007001d0008181907400340401c0c4504800c072178032071000e44400800011801420000280503210701d0340b1042c010b400c1040f4600c540c1c000411130205480000041000300e49a91001c03800c844100c1e03101400d01d01404042c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 14070033 1250 14068783 14068787
    0x40e0307020409060506120102120726010609060822030509040f020409060503060f09030706150302101106060423070c0c06050903060a0e0a030e01020708031c0c030603020112020904020415 83
    0x52400f8003029110103240151447c2c40f58200d208492100c3c0c03a0710790a01c0090162845000d0454140e0040810606000014401b40a01203030a030450004600603090502442d944500c1d071551180034400302c4051b80c2030150142a01940045029040290000d00f1420a44554102051140461208560320713660f9460060003007006000e2a0f00c607000d443c000c030380c030411381841c0c0902610311440a50700d440c1190b600c0304020071144055902004040c00c001025a44450200707102c9110342d100d036510b4682c501c0c415402c002005120610861401e8141030704080022030908900c030450170089016120094140c802c050003080041070107200d8270010681d1075001d0b000c0e140107202038048620589520008000741d501e40f10849810b903201302130380350100b403003445444404501801a41c0106440f100c43e141558815003070b000c0c405140c00300348000c0c980c1e18492000342006c549801c00c4900d040d41d00083c030b070320a41142c6840d01d40c0c020600c160701d0368565049074024900965170f403010030300b803601c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 14071283 1250 14070033 14070041
    0x40803040612060e070504090903031d06060114161509060603080705071202060f030414060901150e040b0106050304030e04020706061d040809041503140307020306090d0203030105040e030702040906 87
    0x200401050400700000740720b070103089009009a41e15180c3c90309188c1461064001410710703010650800d5219014048000c0b4441c11086030504000050807061422034005000d0340107a00c041c00c1504010010009050080414000c94940c01000500300ca17511030141009850b40420113030080c1d1404100108002010001703000140c4100141d5001650300c0c01c4e0301403000380381d101c0650407180c00c10a06036104942401160700500c01d0030466084080c0c01e80361440d049044840c000a030303540b00f5000d44c060603200f144170003d111071112065580361a6480080c010030602c168000d02c0004008281010301604181d003400c14058021900c0b41c030141041c0019019a21403103450700881444010310040400e040342c41941c009090a02d4046000c0600004100c048104c1c0710040c144100403000075108044c10320106201b500540c2c80b00a01d0042605010028258031483e40c0300c0c08804030b00d42d401100741c1c0c4c1120402c85000400008101c01d00342103120b488002544146820703000c10820a190380 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 14072533 1250 14071283 14071307
    0x1110f030409020a090e090c0607030c14010b01120203060303040501110a0b04031d010e03060c0306010c060608030919030c0b0901030603081207030b01050403050709050c120f0411040b0d020103090303020408030406 94
    0x2e541c41703106950b40040c50a0b2003050b5803c0d2074a402c01c200c000d1050526000410185101e0300d020100e0b031006488020b0318034000660b240080c2d4484e60028455a84240600e0000d42051021851070070b22900207643c0788264071070076061000d03d554540e400f500c14040c00e0081030b04402c91505903d007600c2c00070480070b068188860b4000e0020b2006416500c121950864114090b00401c16900c81d404d40280603000245118100900d10744082d0002da03842c0980d9000340001c000441d1950a114208501c0c02c41780103884202e60308202c4d0030004034558008034000c82e40c0d80c4442c030b543c0b56140310040b0040c4c07820750009420b107040010a8650720141c909890702c1940603903000c10407002110011a8544200e11018107244d018104c18002c500741548040d40042c030010025240c2102c03140700c0780600c80115424610040007070200000d101d40300051900001c403c950410090b116807000800f59030810201a0405503206080d070700301802641280d0242490b1422a6200c4c0e5403490700030550708402d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 14073783 1250 14072533 14072537
    0xe030c0706020d080112030e0f04060e06040506010809060406022a060402090702030c070e0c0c0a0308010e0a0501030201051902010b040501080705130e0304030212010204030c0923010605030601110f030409020a 92
    0x760107001141314a40e1981601c45c6115005000c00301510103d400241045109070311031250160303d441e0b6541c0d8402c403401460440c05010795460000301f00002c881009040d6810b2050820801c0f54164000c10010781c401e501040058907500d580010140844440c0708a442c0070320b141d03000300404240013542c18440c0c1d03c03c8500c850641d82c2d28100300c0e1203009048803c0483d40c0400b82c00d002a00e41a4007150388520612400c0d800c0c0314a0382041840e00103502000d40c00305850400501140d0b00c0c111440d580704104920030300040d455640028040e100c1c403103009442c080200300a45046100390848616100000c0090040303584038029552140d006204461150b0b0030300e2200e10406c4081d001c0c455201d2041c0740614209807964003030010400010b00c00c0202075508000120000e01100c0b40d0401a140c400f00000d681881c0c061006001300800f14200c00140c082d4004100c3d0380da004d07045a030b0100003840c00a02e0520051015490464403401c050300a000105010403034044541c05040241125 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 14075033 1250 14073783 14073793
    0xa061a040e0a09020319030e0d1b0801020405030304090209041508010b01020c04091208040503071a06010e0108090a0201030e0102040e040501020903010c090303080403032003090d03060f0b03130302010e030c070602 94
    0x24004000c50300050f9000703400d5080100d60b8030300255540119011139019080031400c442c00000051010742866070704460f5090369010054201200e840228040c1071904000c40c582402c107000a5600d029600c00c01c44400e4000840b0a030a4880760418000c0c0586200c40c150740c5520350843c0c501a254000d0068010300c15610404194902402001c24a03038000400c0880030078605011a4108401401030360a407204000c14030010309030728907861320040180c80302c03031250a104000601116050440e2410448203a0038404d4401c40400c3c42c04400e542420002503d42c0012003840c064050303544076644a00142042100307003d0190002c2180032000c9000304184080600d043c4d8801c0900e0001600041041c000a00020f00071b45c8400501c0d41d8054a0f41c84251803100111890380c0215004441504000d18001010ba01401751001903e0302e0800b50f04407904100740310115001c020038296042ca00309a5500905000790300c4040c4040e41035007034179615414541b0240e541c10541c03181000501c18 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 14076283 1250 14075033 14075041
    0xd031112090a030f03020f03070b0603060f0c0909060406050a0605030114090403120207060906111b0309010c030e0d1e0c080d080a0b010e090109090b01050603100e0a061a040e 77
    0x32210841d40c403640028034041c081c90958403103480800b02601d0480551284101d11074244800304040c180e41446859902100d10b0240141414114081d2290003261505000d00000300e4030001501c2d80b00e5030030b80b80b24109984190014000c2e00360b541c0015000403d00710045036096128008505842d07052501c0c40d06078005a09100c4248022940500061459559403450f58210380003011514000da43c003060205207611140122120b4070070640e00d20a000404034142c00340c100f21082c510740c42c00003650400c903490700042c06111000000801b0080e10009204961341c0b0304d008100d11940016204e80240462075510418441c0400141e5461280f075000003a202000182420070301300b2035803825455191205151f014110078003016040c031411602c0700040c2c4c1c60704150300307000b041000c5e07001c100b0a1040c1400b01d4929010b810582c0601404c100b006050312100d2081700c00c50303403454501c51a030303a240400322008000a800640400c1845940740945203d80300c0608144c40724041c244c030607034403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 14077533 1250 14076283 14076313
    0xf0601050d0305070803040303020403230607020d0813050304150c1401020f0a1b0209090606040c0e060a321305010c03090506030703020c03120a110307080a02090f0d0311 75
    0x2822681c01070000790104109000103161201a6410921900b000350801e6141c0d90b42c840c0440d08081c030000301c08610700c0201c01d51182044071030740203030083c0042c00c056070391400014403003c1d0061117107614111079480a170070480e0800454000b0103040354185213440c200d2000900c5480c00d030700c056545a03031a40a52101070018030846140561005249280203400c200549021005c801c03510b24a982003842d003030240e00d50410540c861013144000e041d99251407030400c0308480b980350440c0104242284810420b40703c8108071130040c82503041c981c40c064520728a6100040218841010749500300700c1e8070a552240c2c101400c1ca040850201d4804a0307101e400440d13101c40c80e4540a00060340c00082081503040500040d07030020007a14002d444c0c55050303c0200d295034440b00894020409440411000401610a420402900d07a900074a58140314a005103481c101804044185500088642d011307070b030f0200c0c44110034901520308202607940d41005030401002400d0b14000707004201c02144500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 14078783 1250 14077533 14077549
    0x4030e01051801030b041404030807120603170c070f0605040f061e03090c08070609050405090a1a0a090b0f040303060504060b04170309190303020c0603040209040209090a02040e0f060105 82
    0x804809085607090601e900114040d205c201141904165900311030142c59040d10001441203000c0e440701c100303600b060324008104410300741102c02c005151000501c00a43d0f44610070001000d50f6010325103424800c0c0ca1380c0d00b058150f5000c03454034000e410340040c40c00c0d040000360081b100803144422406903100c0342036504180610201c40c0c000141640b181c2014025400744440c280039003226096991105011841d05000d600045c001c1140c10f00104100c0ca0719019590340f10100388042e00d008043c5a80e0f0206190391061414034102e20240040c40c019a581e101110268001c5881507840c1405004010110ba00b90b030203500082c02e203040230590f81854020b0b103007140c19040300c01d46010f240003415103038001090942c1e07003030307010800c646a01c540d40c9203040001c024922000f0130b0028614a4003030301e0b01c480801e045019600078020080540c2d902c03480d19910030303016602241142d484180f07650070701d20300140095015162294545c44400c00151001c0c803805408219090750362a002041580 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 14080033 1250 14078783 14078797
    0x607020a030b0901200c010e0705010206040b090c03070b0307030509010603170703120c02071701060501091a09100807020f03030603030d0b06040909060221060f040e03090901080604030e0105 84
    0x10001003080000544a4405030791141c109000080d004100c903c2c140d03100c14210017503103407a01c800b05a18188080a10804000446000c01403603ca441d042c0041d40320307000244050480008640043c0504070148018201140000c090b40c0c0c0c030035201d000171090ba8100f0756252380040d2900002038113a840500c540d20a4980003002c044e8010115188401550f100447c218200b0054581019480c10320340030704000505150003800c0304900300b41840c0a50070b00c140c9080f07400e0b03040c40400c03c20359030130a0940c3c00f60f03540c000f840b0a913003543d0403200072681318506029800009102282c1c1049074440c640c240640856801d0702c1425068810080d560702050f202154590001c1003080011010b651001e00c058101400c460b040030baa41100c0021908a0740c0251030082d00008c442003114200000e9135040240120003401c1c5007006c60102d80420305151406014660380d841e04140000200165200f1b10b00081002e005583c4600910780c5907030054a003140410382e8030240040540c0100c040d1119 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 14081283 1250 14080033 14080039
    0x30405070e06010507020d14010e03030c040b0904020705100501170a03080a02090a030c0f03060b01050403080a21020403050304080c040216030305070903080c0105090c0111100504140102030403020f0c060702 91
    0x650341070095524400d00054402414450100705c00001612900100383c420ba00904445250b0380c1c501802c07500750782c4944101422070300208100a241c26200f01a181034441c0d1591140c0c1780e60300400810003c0c8200c0c040a80248a9004200e10390055a048541a2001a03074a031803030114400440d0759138100c40c000100410243c400040c014402d030381c054401c0d010b0041641580a80d2515404400034540e08961003003882d43d68213005205850058441e060807c1c43c20300e10b0280342d5224048140114811941040040382c4c01240640d05000504845238103140c0445d0383e9135880c03a14565941c0140b040d41114000e1034030964082c60b00e48251201d003031002908256408095400710700034a8020000d0051183c50140403000c05c13040703800f40107440480400041d20341890148140303400421440581000702401c0d207201c000601084000f1921604e01000c94203444c0c03072804000c101c00510211185604c00300030002815400180301001403240340540d0302030a803003c02d0080354440c141e00690 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 14082533 1250 14081283 14081293
    0x303060504050c041e0e09030a0e0a060503041407080102030c041806031e0501020705010f021b070807180b030307110109060810030305090402090405010e010807050a080d0c0305040e0705031b030405 87
    0x88400100e60b8140c14200c10303101c61700c0350700c0d03100c08692508800507205411a80d01c0840c80804040e0000d040044914080b04c003181d005181200043c4640f000034802409010700c0000490355400401c0050060a0850000e40d00c81c80c0800102d100d9400c14030170740e119a60a0a070144003850701e0321070300d4107407600400805580b1952100c41901d1400030720f001c56407990300b04048030124100780f0804040380ca601002680d5500c10900c4030984d04800740c45401603070002c0034200080e200008001046441008150744501158241040102062908541c060100050050030410354004290301c40600341c03103283c80103440744000c880905048800003407050040c0002e0020078050170107041a000000d1000d49469941d40c0840c003a6182a8001c806e5060039400621202c0f400780064009440d080d11280340841c80c5c032010320b50702c403171070000034080c020740410340c005141c13042003102c024154424241c080c604065000030b00390b5000300d5003c04112006032400403100509803c0b68011078004d00101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 14083783 1250 14082533 14082539
    0x21006050306040809030f060112110907020a0605060111030309010507021c0f1d0409120207060c030503010509040804051e1509100f030e0a0803040b060301020c1209010201060906120303060504050c04 88
    0x550b0302a0205c150b15204648032040001810005135000e04426038502030784886500d0030b501d40140c820700042c41480040100410390f0b80c0010b4001782d032030b004500820141c032124010388003c002c0304940c980d40c1c0400400c1183c10481504110b0081140c0e0b401c4030040d031390006810380c403000c80c1c150340c4001800e0b0050705000385208018882003100700c60f030300541d844050b40c0050f08640e075000c1d00700c40054100d134503031301d20b15014040300d40100505e0906041c3d001860390000c066100501485214030f4207480828280034190302a01d001d4030019105200e0400e404544125000061580521460309102c0506d00c10340c04400740d86582d000a490203019000d40007055075150022800e81e400c0660700c545600780c400e800c10a190070980501c41081e500d003404c2c10040032110000780254003c0c1c1c0100f00301510050700040c035507890380e1914001e83c1c45600b040f0040b8050b103d140d001c060001e0502c1000704102c10107a400c1a90720b846502c080009a56840c00d00080d12800c5640542517030b4140010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 14085033 1250 14083783 14083793
    0x151006030509120403050c01030507050a090315090b070203040806010b070b01090506010c0c1806050402120103020105072108070f080103030207050f0a0e010807030c140303040902090103020c010c020d02100605030604 95
    0x41c42d00001c2203001d480c0c458840344050101500198016540e9521204141945580610405030040b003185001c5240083e000000303000c0c0d042d0f500c0020610385031719036400c40c81417440c6d100c1014141d000c000148a804e20301c400030f42d03035045401003e4240c02107030300008280070304a044964440d400144107a07141e02c1c0610320401450001c10490500c014082d070340e40007450415906001d8038182460300042000440b1040031501c440d00a83e000d54410044244c5000b04c00b0101c9044030b6092914560314201454840c000200302840f00100341e01400040409581100d41144910543e0391014001040380c0700488002c8800c0c0700240158002d01400e00850501e408203582408015145e2405030b5070b660b1400c0c0c080c0c0d90981c010100d5401c005070170f10400000050000040220818050b1a10076400010b0780324401c51041d0f04859500094030017059000e03805031007400da0070500810801c405150040c1d1290400c00c05200140030b07001103000304004510800c000e480c400360040c61903a9580d038030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 14086283 1250 14085033 14085041
    0x1407030f290406021309060308040510020a0803090d171302010305070912110f010c0b060402090a080f011407031404080a0c0b0a0c030f09050c010804060b0a06030504020315100603 79
    0x10000708119000d2501c0c50401d0940c00c5039005a01c545801a500c00740c1c0c07801c0100c03004141c1c21540030582045c5040000c6442d0b030f81550140d81c011901030036000c80580082e450010120402000c00c00044100101d50070f0100c2c0061000010340c4880700c4881c1c50403407605e0380403400c864802d80312000080700300243d4402d90016a1010203418076600481d15010654101c6d203410f603084500f070b0140070769100e0a08060200d09070844c001e00f400381c01c0651559070980382c2c60004101a01503940407a116280ea501d80007140010044078042c0c440102000c43e407140078000c503045074070885441001203211640b1900c5041a240850b50065803035417255511b0a54562052a507282000544650500401c4002c45054014048080300103245000914058151510042100c02241c0750080c880301040d40801c152444031801d1a04c03a1160340c1e0f51610f000201b008082e516000f803c84003000c9813076600b40d4020703030103a0b0084040320310105100c280c60703c641ca000c481d0f5031803100c50382c0340800c022402900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 14087533 1250 14086283 14086313
    0x201020c0d021305071412011e060207150545060711040207080a0807020d0302042304060b0301090b12070803190c060504030807030e071401110703050106121407030f 73
    0x1d4120602c03078111043c0344640e0025003001e07d0b20020b0030010800c864000007081c2d0654101034610588524100001c2e450f401548600c201952407189800051841501280c00400c01450b02c196600101603d075040c481d40e0002c3c2010113805070014400340d5090920500d0b10000040036035240519981e650041c0e0080042400d8105809000c0c200000d0510300c041d10b00118181e0b600e114030b24108074028a4084030070340500074948104014050201c240100302182400c61300007941c2222000d021074001d12a9911a001921001c000420328441c00e40144500c0c5c10201e2369400c1c1d1b90010a0020f450706990301c507405456000700101c4078192032943d2012400b441d0744c2001c44c21030321180c4402081d41c10449007100001c148030100907066402d440b0301c0c42c01444420090000d6800c11784001c816900070301045050011311440040344203010030114010350740c000000c1c00102d41da08100d00b01d1008250007215602a8098482d1031804000388600850b600008800103881040d100c810705404050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 14088783 1250 14087533 14087537
    0xe0c01020a080405060711060d090506010608040804060c1a180d020304050a05040915050907030204050a02070b011403010906060806101502030301030803040206090d032703110909010b100306030201020c0d02130507 94
    0x24014401623840030301510306812202004a130407502440c0182c10303c00160091340c140301141e000e0002050710700c03040da000d40e000d83c1002c251104017800c02d034000f1640c00022010000030a4108240100c0108594441013495411035a44807401c80b4144d03284c2c0070324041c0c1e6400c10401c840800040c94940c2020f60341e180101d10000220380e80440101c00c1d12001c4408407460f5000035000c10840c2424468558080c02101e8118104011039441d01141d04040c4140301c01070340410b070005619a400e5100f038013201c1e800401000141c0da9081465220002218480094686d0b8a03002800d601d5076400f443e0a5002940514a56030a43d0790300c51860300090810780e001039080c40f1060054980d82c0c102c1340f10a0082d03d41900d486100340750204200c1c1103100d211050000c104080001400e0348103088048501120f1401c060340e2840b000e5801030000d41c611540c4145410440103841d505030340403600760b034000e0f800d40d10481901c405001d24044011402034001006050680b13007140340703030300880d08000d80d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 14090033 1250 14088783 14088803
    0x19050c030403050703150605060a030509030903070e01051207030503220e070513080d0203070204091a04030801030c0602010212071101110f04050405090105090319020705130e0c01020a0804050607 86
    0x8105000e240d5040790700101c40c15031150b542401440a012011001c01e9481c20080c40300030b0512010030403a0040464401c00d00d6255400300710003040c01d00695030341c400060100c035142d03039a0b4650001001001c3c0720b81400f803016488112103241020800c0e0040c0c0e50000300451a00d881d4020f902c0c01031070307601000b60000d0400c14002c502c01c1004c5d10520301400f00c0c2e130740c3c03141c0310414062050078500350742c1d100042075030102085039449600407003030311030640d011a80004c40c5042410b101c0900c02800d41d908900300c103da030411041542041b070311416240141c001c401d51076102e4205908030b100d540608400200c2a100044100d40b0500703040b880704c96071900200b000c1c0300d0341c040655143c0001118029684c4041424040d5042c06d108075030f44101240001d02c060304091200c2e948030f1041e1800304541d20211400c0b84801c5000300200c05c000c000c040c003110000c0101403000001007151008608050040d200700c130190358030001d606809150444030300c6150510380420440254000c5004882107240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 14091283 1250 14090033 14090047
    0x3062406110c13020307020c010c0c05011202040305030a03021b0a0b040f0501021201090e0c0f0a060309140609030a03050901090b0c0d0e010504060902030c01080f1b090306150f06040503031905 85
    0x404000e00302d42119883d000d61207062800001c2d0615080c42d518a042002e070700c03080404104880b20034401c548003070070036500c2402c40d400c81c600648280d80010f8107038030002440c0c202056040d40104500641d001040303c4c4c6445000b49262661103412020384201440b0300030078003245803001805000c51052000514140750980798545604090b8010603459070303240565a40d0300020b100b0040d01170700c115107001c005103c00002a00c1e0800901a0b0300401d513032028140100950303a49541440c56000c0110340c003c0c50000c0d0030580c0c950080e402000001c0c2010b000c0380c1001070500030b11036205d07032040d2026025a1018034010a40e00701090049000c0c0d103544080a050701c0c20320030180540e0103040d020442c029540181458102c140c1c55040c104006d020411681c154400300e0f4541003906450100000700345081181c1c40741c018200c80c2c5525020345400d2281c6003070000c50021141c0b800340c0c0c0c00040f5076606010450140100e21842d90036820420104407040c141820411f11a129814041d0400c04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 14092533 1250 14091283 14091289
    0x9090a060f021207030605030d1701090504020321090f040c0203070201140d0c02031209060112080c03070206040b0309060606030118090501090503040605030f0901150603020a020a0212030403062406110c 89
    0xf003a604400426901d440502c16410244034842c1040d84506206140d000407034819a182e0b0740503c42d0210007035640c0c000c501196024048110813004c000041480710b001d00c140e51285a00c00e00400348901c41d0745070000344608080c0511112a0390780e802542c2483c0c0d01f03400560304081c14820000103a0000c003e5000c03003050382c0c0704403618103502d07a00440d2590b180c001c800380c0150014000c2d01d0141c1c4a00e004000c1c030b42c4054061303010643d1005e2610344907148848010b186000700480203510a47c0440c002c0f8144d01928080c41c85850101c1c103e03112034507803805210107440300303000d145003030305a68165084851103608201100b503c03031000010025229115541150081d030132100002e0b100009001c05824101081070304a851080200300021000c0c03c6403c04d84a40d205000030702d5004944001450700034031241c0083e507000780ca1600000c040c03c06c460749035449400100d07686864448100700070181c55803d40d4298400105000c021410110180c42040d22446d100c90301d84100c1c148000d16031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 14093783 1250 14092533 14092567
    0xb031008120403060f090209010501050d06150e0102010b090105010f1103070b010e060901150c0f0602190915021b0f0a03061401150c0b040b0702190804060e09090a060f02 75
    0x46500e41d0a103464500b10300d0000d09a683c410b521a0f2100e040072182e9000d81c5c1c41c903020030704440c4d00b402c0c0555195a1020390001800c6150b01c2580307100300c000f10496200c0d4100c9110744800c2802d90080004844010420003c3d550a025890002e07043c02800d9100e61300a03060b014030602c101003101e0074040244d4440900d814240c11440c0c00b00490030900c01c4509108d01241d0140010f00d10040c4c09001542c1c009166481d20756019000040f881e0a0b8401e01c49254100c0745404106001ea0b1101c0c6403103a40680018003512030b110070807204e210300da40014404101100752003040149200d01602403000c0010a007400c00400d94406800000040010b50a11170046d1201000096401030f625212180220140c49400142440600c00141000a02210390320b50f00c503900003074000c4503854a0300c080346012007800215084034807943d00a0280030b0410082c2017290385c42c2da660020340c0481001d01200400079a03c20300309034441d41301d50f0005034141c1c01480c1c00041c0050010701b809511140280d00c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 14095033 1250 14093783 14093803
    0x807031e0504050102092e05030402040b0d050703020111030c031c0e0d08040b100308160314040306060f0603090f0305030603010b040f0b03010e030c070e06030a020303030106050a180509010b031008 87
    0x507030741c00142440340c0d01f031007007080c82e00c0480641c524042d404aa00c000e40c10100c00e1000c2410000008001011590750307a00c00c04082d000a04409003130500c0e450312035a00d081d0780c04117901084e0000291032b02140c0000c101c500e0b402c4404050342c101219014450001e003000c0c5210f4101ca88c907043c2001d4450000c01000034102d00c43c1c0e8039540d06082504207147c12001c040c1188049204210b010b201140001c0220307641803090102c12000ca02031424121501000015009481e40d8001000010310071590044c0b0240c52500308290029961134005030100c8000c280000c040320007850403600401d00920183da80000080c0c0041010365140340040c084900c003110061015996172140c02007401e00340320709600164004002c51038102604103141da00c00180c03041e400140d50405c0000d180703440c00d0040c0f1601642c09001c89440e56150040949541c1041641d500090428441c801383c4104608028007110f1018050039040d900b40030100140e5072008100d0f15101130900c50008440b4010000e18000b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 14096283 1250 14095033 14095043
    0x1003080921100b0109050904030503090a080c0d030b033409020403061d01061a0901110604030503010503060c03010303080a0c0c021306050112022503200601030209010801020304030807031e0504 85
    0x950035109540c0d0303040f101800021030400140c100d050000382c5510031401e03002901820250784a0399413008281c0790203517410303005007200c40100c0d00091142000a81c00780144080d10180503c2034200241a917800300c074010203010308403500e071441076030003014044007040b03031125072641d456600ca0074070034160388c425803007210f1607503940c04554a482e040601074441d0000c0340d0000c0c0070781460302d11140c0d0213090002496103600000201e048482e0f000c1c209025001e1500001d0791111700d07041c20050f003290400d119480c001d0182c0c100060412510008481c1600d80c107454a80658890b40303001802020072000010900044040e40d4001d680c61076500100300d0307000e550206540d41080001801c4e00d0f00140130312541401444152032550010050b03885400d0320704200000c5500c142004c070f5055000110046443e000c06101412a10300450600e060741d00a482480003640d84807415403c03880205c0d0041c0005400501064140c0c1c42031300003000050700901d10a01d5444819014011030310103036000c5074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 14097533 1250 14096283 14096293
    0x20a080f0a12021b060906070204090f1101080c12070306030209101a0408120c0118050105060411070503030604090302030405120615010e03030301060c030504090507020a15051003080921 82
    0x2040203482c05224000070070302c2c405060103098451140c07240020194031548101004220300c8495200c02082d600026002482884901d0f07030f030300b40402d080307008260650b0344a0703046075900d2040d405076400a005d080c440a1507031400825101c02e00108801600900c01c140c3c030f9510000240e80d0b5030b0081c81c01400d0f0001d8040c140c41c074003140f00740c80301003202c89401c0d01c20090100b04000d0002041101007050303030003031450f03a035142d004149004007182044c00f4010040e40b42d150091000540c002ca202d02002d0301c00b0008103990001000392400b07046402051a48108005a02410140c100b4805944240101c904040d103c500148011074040c0c1a00314551000701000886c800712074280f69004000c0c00c014091403020004a502c91005000710b00074411084040f5040620840848009041c5c07800204107a05142c00001e4450a1522040c0c0d0034034094108441e020b6882d204081c00380015a4103401c0b42490f41e540c0340405d0f0001a505903010410a02e01500d510f01440045000c0e065403010701 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 14098783 1250 14097533 14097553
    0x20d0507020609010e0d05030408040e01081b090f01030615170a050705060702030607050c03040f0303050a02150609010501030b0f0301020703030501030b010b040b1e1b060709090e0304060c020a080f 87
    0x910303100c2c0060100c00c0d01d0b03040c100205842c40b80820020000119494001c0d40c0e60317a2820a4001d600c40d5600050165203450000582404040352118010560880001d8142c00103010030105070800d13100ca14140300f01c05c1c01080040d11307580c0290000b155000941075026680c00c100140c6240c040c0071071a41d5008030307210004104042c42128060103048035014140b44558010035503507800140444140603000420300d8141300c041065400419602070407000154a034a40140340750042200c20b4094070420156040143d100300605100300d001800181071a8a04001103003c1c0074201000c1e50401045034006c11240c5080c0018203440d40291070125142d4510f00d040c50902405901c03010b100c0001b400144085025038088600103400d19030380741004502a000d14602d031040d8a03901c8103800c244605020031000c0401c409112380382d41c0c0c5880078001e039a001d120064400d41d803580443d5400410042c0051406400f610800301c2c00600440440c90b1201c15907450b01124284004440e40000100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 14100033 1250 14098783 14098787
    0x30c060510080118050604060902120a03050a030e031617090a0e010305060609040506010311011101020a0314090f03040302041a030a0b160e03060609060622210206180310020d0507 79
    0x607403110004030303101000c600c513580711140c072002c0184c0001c4c4001e44540301f000c00c0d5a580d2415050072000303201660746902e52440c000c0d059034811210709012031f080186513500360070040103540d00003078002240d0318143c1030360362111559a090700a004042c081444100000e0312289140c202400018a0310a40c0354118180700d46081c4004004038070520782401001700085001c140302e4110b1340e1005521890404400050700e0b5882035640d680055072000c920001c00c581c0c540c018070302c6881b000b02c001045480710b0301095107610030526107420550003000100010300309075100c2800300300501080b5041ca500440003e041c0182e258060f50313a0088001486004a50341c4c000b500029a0f900b400141000071401080d00c03040010500e41c410031040000612075203d600440b803881004948004030001840200c10b11680b050052144d02242041d10f81034202111044034240380e00189030b00c1c03e105880300d084010369900c100807901030081c00c403510b01ca101c46001130900e10150301c1c00031a080c81c0440c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 14101283 1250 14100033 14100041
    0x30602041d0106090b03040203070b0309010b0f010906090e150d14010f05061f0e030102040611060108030a021f06030b0408031509010605090111010e0d0503040c060e0109060309030c0605100801 85
    0x8050301c0744041400420900e90054810800c44101d01c4400c2d80701c0d6100e000090a041859004101c0103a0000400c900720390107512940079504100d81d080c042c04201d000440d0900741c1409640042504144244880c01c942daaa06511800c040c00049401c0c0004000c503060040c10317141100c50005e450032204402d1801c1c001c860502d01c1402c0200300500d041d2001030620380c5100c186951450030325000e002468800c1941c2c00161401900a5540e0303543e0f61303801040c0784001c20382d00e0602d00405c000410503100c00700c1191b040300c00343d500611034100850003c1c02c2c060031440c408100340d9912840040002d9085550701c0c4994002d120700d540b00e00e001841d103030028035007248180c425210440184103054111041da2030615003071030310036001c1c0b0300041c1540c014001643c182d142d51003408a035242d00759111005510541c403450b107507215641e945c0025941c8054030300c101804540b503a00b017803012038482d0f400100c01500034a0201c40181032515028221801134618800d078031b0404005103c00002405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 14102533 1250 14101283 14101319
    0x3060903090905061302090607020414151c0605190501030303060603050901020901080a2c0604031b03020604021314090c0307060e0d06090501020f0c030c0c0103050105061e0d020403060204 83
    0x282c14050b518098000800700d1265281c1546220707804070300809540ca031002079031641c6038003400400072581942e41081b0036040846001540361900107540442d820001030407080036042e02d9a1440c01c0c102603840b4000750100400b4002142c4008d80541c28030002409494001c50080c1c07030000d80c440c10914001e0903140300810700504c1c3d0707004120880550342d01481e40c2e40d000180c1140050b954030390320348986088216250b0b4400c078100040082034520408604c0305c0c055486501e812103a217030440ca40014042d941140500940c002800040160401d10202070792100c00d039a00003000340c64884d00102c0d1010580b2042c2403503010402c103500508040200314003611075400c0c00c828100c00d4034001154000201002001103407510b0003d410020250166410044da0400890b112410a120300703a80e6041659202c1640c850000003c41030b50080c07150324141d503800362440c2d107060315032200ba001e00c11244c81019180c007010043c0b000308213042c1c40a80065840f9040c090b0b9102d19080004820b00100c41c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 14103783 1250 14102533 14102549
    0x3021903020c0601140d11010905130219030605031002090102030702100c030206060405011a070204150e19020a05040e1003051b010305090105010f05150c03040f03060513050c120a05070306090309 86
    0x10000322083e43d00c11506d03000441d0b100c45a4501c2e4000314004a400c03442e41e0784016040390042d0048444106103030090000d47c02c00e840081c100c0f0402d01c8040f000c1d01c0481c0b18445d010381048140da4170301d100e03076001006504011b004503498134007184d0106030320b155038841c50300c001046500002c0401d60305000d11600600f00b01d40600055040292140f24100301d852261000b80e0005543c0003152502e41061041031940c1020a0b0341c1640c071100b19160744000c840310744901000c0792400d801702e1a07510aa03034010130640d660a08082c100000d00130b1001e400341249030070070755a0308004001042080b0106540c129541501c5e0000103580016081d914084c0c00f50300c4590618005000442844c503498080340c2e0101c07028502841c00c078020b0002072080f100c010000740000503000c503400c00c2c002151380c01c50b03220340e100f00603036951024800c0c41d1164609009200fa08046641820741c5001080001c1d550050010380b0f29000040d030b2880d1800025500403900551101c01c060113050300130712030740d0040c4146 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 14105033 1250 14103783 14103809
    0x318010b01030c050a0f020c0a0e0106020f0a0f20090405010219050301030b04021504080304080606130b01020601060302030a0b09130b0709150309170715050c0708031603021903020c0601 82
    0x70340000c1c102c0d0207070100217000c0090420210818034801c02980e40e81000240c40040706907201c4d81c03681d42c250802d00844d8058421820100d400d07690000310109141c4e0860384101042c401c50765005a00840b500c221500c8200c0150729240d81c0c2d86002845001e944964001a582c44030b1501240010140314602400c2c06401c0c4010808505801d0009500c40c0c1e0440300d545c3c140702c440c0c180398501e000f103402c21144c1d88008140403401c0f20000900500448003224040080b03907445c001d810039510803100300c50060300011b004216050081e0061900520917002c0030400400e281c01140a420b000c944a00803000d105415a051214840d02d164200c0c1c2c99207801c414281c10403002d000c2c100980c1c030002d020150303503006000034814840c10f250b00082078040802d03561001c5c0d040030003c1c040320300a00e07441c9034075000c04031746512600341c122603407154010b4000c0d095030b48400c004c48841003200c01d0001415001c210b14000005c0803a0081e6a060141d100142c0b0b41e14051801890450160480c1c1e4400c400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 14106283 1250 14105033 14105051
    0x901060905030a02090606070b010f030b01090207030e01121b0302030a0609020307140708040f032307120305070f080a0908010c090b0304060b0103060b0c03220b0f030c0f0318010b0103 81
    0x4505010304039011754190342d886c0c50300400710ba483c1c403d9401c003800141010002041c100080b0b900103080f2070081d0013140450340c0711040002203105003000200400c3c0d03810f440700c0da29402a122841214644000055040841e204010031030241d400c1803400a035001080120403055441480043e00201c1801c50440c074212202600c0382003146180c000c2a000410034000f0800d154040302c01510b411080c1c20750382d5a036441c120400140c000149200f81c2c454045d00000c0e00c1000402e8022207903030800d00903011481d42c038241c509600c1b8170021385d14085201c0003c0003190401005010074109980c81c081c10601d0120105d0849031000b0100c0e040094500c0100100d40c403140503603412603080303800051b000300f100005a005107880e6200324000b007030124034580c81040220150145010601910f0394004d9071402800014081e4010050313910030a104000f100c0d100c00e8040d50b0300c0380901c104c180c506969802c450b80c403600100d540c40d0180441d000207030b031550028024035040282c01e003028002a08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 14107533 1250 14106283 14106289
    0x18030305040308071b090e0f010902100e0112050c0703020f01050f040b2211100305090303010303080702070807090b0a060203070b010506030703020904110d0b010206160f0e03030a030603020901060905 88
    0x8507911010386140000302c1d0741824807051202103039982c10040f8044201076a50081034014005c0410030030524000e0780c0b0ba80e5074488040c065440601d600500d4000c0904803140180c03000c00f41200c1050400c0038103040c0c030030410003503c40c00c3d0043c0b0750034415980703074a913500c3c00034a03242e8003c4140459905003410b1140580c20306a020390040e900c404074180c0c0b130f61034580344030680340103001c1d25100381907200d03214051014032034142c4030245007079400c91209401c0c200281c1c01d0311002c0d1504011544200010070200303114602080e000301491050b621000c1c2d446078903d1400c00d01e9081511855603508a260651514811050040620340051414800c841e102d00c0440c01c01442054010b102c000005815240701e80c1c11100c40c11402001081288400000240150030203044071b140d03e0728201000140e036000068052040c01e846001c465414080e403011038240030323500c0380a4103100040c030038a0302135a828009014044419580018020320b140100b003502c04040e4010410b0015002081c4802e40f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 14108783 1250 14107533 14107537
    0x6121b01050706020c010203040f061107020307030609020303090a03030509030d031103070c020406080307030809010f090b04110411030f0403090603050601021510050402040b0409050105100c02010c0c05031b0118030305 96
    0x20809081c0161a445282050303c041d21030500c00305001c0d40b001003004204000390f55000d1200b80102c0d4100900d00c590354100c0b003188901c0c40c002e54540d020110030000501d1740e030445010780d440602902d080c400310f030b0082210246580c004802081c0e0124000380d030350400304011742072f140c070600d810f11072031340c01a00d401c07000e101c080d010008208860211505640381c50704610010f1015208072551880c650900074400071055421030301c207500b0441e02444900103405400c3d151031700010100026241c50b0340e080140c40e0840308481d002520b4202d00002006214003462144199115044040c83c061038020050f03111900804107040c58001840b8169900140900308031a0040d45113403e92030388190340014003040d40c03001e0752041c00018007084291001024100700c82d041c04050115036220005c10651002103283d0a001441a0100c0005584100d100c0200d04d4011a00310880c2512100420b0030060100d500381000003444844c15080c1d644002014040301081e8580b0b003a00d811960014802c3c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 14110033 1250 14108783 14108833
    0x315050f090601140301080a020f0303031509040f080406110c04151203020309030706030902090708010b0d05041a04050102031e0c0406080c041706010510030b030c040c02031308060612 81
    0x241d1010070000768981d0299004001e80c450a0b41c10640343c1d80e5440c4125a11354440e42d049000b540d12540c203901500f00003003581d018642001440c0340f40080c2005000b207420004105664a8001c00602c2010501c81c0d030043c80030781115921306140303246040f0368034901410801214003942c0341450101031040b842000c60151880d03804c003045000000d0a0480c603500504450a60602a4100000d00141c16501500c0e0350752094414000d0366807052801d4514000911034080b900c00c0030486030040055680c03000e68010320906a0700d02100780d1078600c04543d50216000c403860382d8000f062003c1d1803034501c401c0904c80008010801d032450164900d0748580140d109032414001000040b6400b0380061040e035000d04096480c10f40c0030086000c0340742e80e50b9003c0c030485000d103400c903400740032842c030a010b40c0c0d10012025005007200c01030801448000c241411880f011400184400290055204804001051000002c011a080030802c11a1206841c51600e0782540321066200e02e244400010103a4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 14111283 1250 14110033 14110039
    0x6030606040e0c0a080a0308070206090d120906020a03050a0f0612060f0902060d0606080604022106010203160503070506010602010b0d0303050408130306051008030a0903060203060d0203010603080a0315050f 91
    0x30030414150201d2500714443e03c4141c1c041c80c0450082410000001c0c01e00b1500d00035030b2500015100e661003a6107034141901c0f040c1e040c1c0c01c5041080080c2d4000c000030f43c80e0b5480d2002c0002c0b24100390300d40d04200e80110081000080e00d6105001c0032056a02420700380329884c0d00700304030161a1415840143d500044020034180c0c03210400581d4a480e03600a03100190090880c1d503541d150074044030010324403401031700041203c2070045401070078144240c4d2180400e01504088040100c1d80034503921000910320303411844200724101c903030700f43d442840e03071414442c070003d640394491494a10b0908605030040021a80762098101040e03880410034070f101d07601414000b403192202d017041c06140c4144c82504d22020302c1060000100300c0d03144c1c092440341e036009420082c0d20391034a19580d01c903c554120b000c0041c1001c18284040381e42640216003100001b41912404580340e40030038250f8000c1d038000c3d40c0345080440d92443c1a0340601031031485010703191600100500749000550800401c19100340 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 14112533 1250 14111283 14111291
    0x319020906060408010c0c03090806060a05090a0e1b040b041505150408010507090501030c08010602060c09010908011109031002030f0109020706020d06031101020705030601150503070903060905060604060b030603060604 96
    0x145030b440703840454000d440c8aa00a00400303c9200c0c024100950f890720840c0000d150540000d080d00000c5500e60044400405440d200b614000400410010280590712084d503141c2c0500d000e640c040003880300b4001000b0184101180660411088801074090f80703001cbd6003085481c4050f802194141400d5407802c44010304044c130b80c080c00c1000790145400507100c56180c4002d02c10382c02c0e08061144201e0301c090341e0920210321980c0d011513107841c1c28031803c07000d68000b4000c80c3782950990302400c2080010300d0084a80307036070b844034030b400e644510402e14a008130001e110010346c2000d01074580c056a031000d0541c40d504080c403038048180c405100342407440d9400b103110b00803c0703219012201c00241e0010240302054a03400e0820002c510858a6400361060107000606810081080c40c12503030280588038818400390815601c0b5400200120108040010b001c40042c003280b04201242d07000340c005080c80c0c500002071000b1200c094000c404910741c10710802440b513400050880c0d0000c410f5501103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 14113783 1250 14112533 14112541
    0x30607110304030c032303180108090120030709080601031101080417030906090705190e10030c030c05090106030207151505041d01050708040c0605070f06020307021b03190209 77
    0x1d04600850304001d00000d0300388800000d00403a84c50710918000d030305848010944186108903035034411401050407410b0001c03d5020340d50b000300e80e0303e030303210540c20000308915504d407611701d4260041d1035030079820396404030a20128651143e0004040c1000000078901075066448000c54200b0100003076041010340400601009a1101d40100d58050001a9900c038249482e007251640c0088440c209244a81000000c07a45050403800f040b0610b4030140d10f1789036003807095038101084003d01000404002500020028403403581c44030055004034405c02420341080d0800900030ba041c0e00c01800c150050148601084040208007810f80721080000344901600004a60611850748100d030300c903207000d00c480600e02c04288141c0411032114003c200580d030300302c0195806071050318041c04400c45180144030b0036004200070034440d40a40f403100c3c82c02ca896034440302a030f0b208584460058100038031882000041001d20218010110003400360464444480d244e007034480d10303010b841101081302207 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 14115033 1250 14113783 14113817
    0x20a03020d050c07020306071409040911091003062307030c090305120c01051e0f0903090907031413080f0f040803040b0a08010902040e04030804061803090612020306030607 76
    0x85141d45a28101484189400c0400b258160080745040c0c0c0240580c8001465192041000040700c00c0880900c50030517182c1000d210040284175811223040003541c003952708a541d2980c0980c869010800035440407400c524181381175030b0a41c2e455a004a00003042c0705450003608040d154481c1480c03034001540300c84200c01311000c802660025003903028040e8495070844c9104001c140c010b00400c02800035803203c0048803030b610f452591100701c0d03500d148040350304e1031080b079009a002911391040700e051180050004021403401d80301c4101103569104c4120107040a091529803000600100b0a003940507902d44910301d124203442c1c496420b40010755400c7c540c40304019200034081000c1200d0b11a84c1f181e1141c1c61036800f941c4a1808141460300000c4c01c940d10b4004c450546902c01404200380c1c445a4098400c4240688200c404c1900c07012030100c0c03200302c0f91889200c14022780d288210a0f02d0480c01803c140813031310311090b5039401002040031039100060050b4000120307240040c8070412340303508 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 14116283 1250 14115033 14115037
    0x30901031a091609061103040317040f08071502010510140a03050f060906060a030507090207020418030f18030302060411010c050709020901030b10020a02040b0a12140c0409030210020a0302 83
    0x2800d922941e18003d00a11400c44600c0b40111201c94441d560026120314081c0e900c80c2c0700540d4074206500402c41400012500b540c8038014403003c94029080903103a444013a41c0922175000113101c5c1d80000400c124402004100541e0450135000821007810100c048031a40c0c105409000801100030150701e14945552501c00001e5400c14143c0e03181d5000c01c1d140701d80b41c280c1503c21034149d1103180701181c5030380f40c0b50103010122603005004100f680c0c90180e4070400780d000350b40c00b80d920590b204122041c502c03420072001d400e42e10a81e1090000c541290014008030807807035606036041c00e96001440001d800040080d00690014024400c80c5e88200c0100c0e801c207041d800040c01801100000a0b040e2440d0b00a0a0307500026241071000200d000b0a00168808052040d0010780c00b40041d440941815880078442c202d001c0d18070740f4810b841d2001d40307145090000301261203108607244042002c0e801d00143c000b80c94101c074103100a19294500079a100c01c4800c4008401d40d0001d00b0b494400d00940c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 14117533 1250 14116283 14116331
    0x51305040507180f0b10120b0609040212091002040f05010c02060d0903020f0708240702100c0c061104300c0b0304031e05030a0b0f090f160806010203090103 69
    0x94440c003000c40401044000d0040d081c264805a82011080c1e000c2d480c19907146c001202c216a949040315100102010141c002c4024041d04040204210101034072240018036408003071a2651941e81401d030400e43c900a00100d85003942441408180003803441c490700d001c11030b07500346001e400c110018000160307075101d40c440c1a152903203400c040d00708240c0c010450401030900031050394007040e540e95055499000c0060039002c012020190117101403040840700343c000c40f240c41211040d105c18500ea804458190301c0b030318041014105260100a82c3c0e000381782031010b0382c0700403508062802c40031910034510100c0d50030000c006508041c40030500110907510040d08414034003940da40d668450040341c1d100f07582c1500041d4401c17403008000d03180c0c9844896030101c203540b024034659540411100418002c4a1180c2c007081100d0b0190f0142d40e5003008902950200c00004c105080414499100c0c0010400a40a02286c182000341c242e03004800ea03001e038202801c0119214294038550f1001d00f00c5a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 14118783 1250 14117533 14117549
    0x100512010305010b130207030203091507050706080a0608070b03060103020901050d020d140c0a080114040e01050109060f06020f030306011d04020c0109030306050301060305030f07030207050604180605060301051305040507 97
    0x800042401415001801e19110986020483c58908134129040e4030900c500070300076a0003000b4400c40e604002d01c1c0d40c401500d4440406091400990302d0900b040b15640c01100000d00e19030034424246135a1045100a0820300000c00c4943c1c500812154540030003003c1da8149a404252048564001e404450b000240280215590880c04015030010200d04d034103840c1d07541800000440b038845580c11074680c0f030115250a5141da29042011f20034106141d80e0680003a2944000c01d1402024042c4501825808102003002400c0100b034518416042d030100c01154888051298030003c040212500b0400a181440080d01c4406400341c5407500884029003151001641d185880819402204058465a014003c544d40c1d80e040500303035411800041c009400c10001b0882d10200e071030080540c1c031302c02d005882c84540e50f90002002074105500801e100c0c2000210005103208611420015040071034450b411541000d001c80c02030202c80e143c207650156110046000e000c0d040008200800e898 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 14120033 1250 14118783 14118817
    0xa11030a12020604120503040503030f0919030206010e07050a2102040f0b091e0105040e1005040c0804060f0501120201030c03110409021201080a020d0206030703060506030f07020d02060103020a051005 88
    0x754034002c0d500c000c21142070b0794005400c00d1203280076103c0c0040344c0c0540d400500450454450b002030017100c2d140038000600a101705070f002c0903240b04280c0c08403503181c000c1d00a000250b161041000e05c08170010000b000b0040104410710201d50800d4041c2845101104a03400c05200600245c00900c6190440c0c13000341031030900062042030b100002e028500f02510891040346141500152090520b848a400306501348018040b4060b100181d50b4020501c0d128480c0300d56507800414120744580013000c0010301440e00f0441800107a004052061050b0342d020804e561600351880034002c07070340c44002e04040c0c9075040d41070322500c0b03a001003030312480381d010890f6207580d03d1781d04800950100c5002c009840181000203001340011400070700164001e00000d02c001001d030b00b002a030b54001003101d000e2580d26040410981c69000c0030354450740504090000908140c200a41707002c10042e401c0085612440062005072a8002884c049800c01e9508004965024a003941c10b8041c040c2810390401503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 14121283 1250 14120033 14120063
    0x8030f130206030103061a03011b0e0105210f180a03050901051207030b03010b0102030712030504050709020c0d0e0d030f110102121f0b13050f04060503010e011b0f020a11030a 77
    0x1f40e01c009a002241d00019074041c00c1c02c800c0c10700380e070121210340c0010500c03403a0160282d03000c0c0101e425107100c14908146421901400030209100b5030b001307402140c1500c0100710007600b25080e11030700402110401c40c5094000ca908a50300c00b00f402d0024104070307012600d540c0d142d018606688504d0013030781d42c11b03a07145055080100140700d240038681c4030f5801c000c110b11444d400442151a010707002900d685429003000d4081d000380c000500202c0b443d200c0c1c01710010701100c0500c0a0400040300300c0182c4207550481400030700c903890181380345110351820315603100080d804c1b10b138080da080c4031810124804540c0072a41c41c028001c000400c00e495a40000704080c0c50300e5803820003250348000d2220105507458260f0f894140c003030261078010b01d04099005001618200c4050000040000c0000c5005501c2e000441c1c01c1d06e10b0100d140c02242c2d141e00406454560300885502c03007d90740e00c0c020b0231840010078002d54070000f401020b40903c40c58080d106882d05d081c86041c2100b074020610040300c0384 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 14122533 1250 14121283 14121293
    0xc060b090a0902090105010903110d0804031b030c050a080309040e03040f06050c010c030203160e0d060609020d0e010515060c0708031306090807031505090a0212010b0a08060408030f130206030103 86
    0x402100e040340f054213180008101517000306040b03003e51342c012117030030740d59654401801800250030900f0b442005c4240030000014060302c001c00c910b401c17800c4280c500c1d00d10f580707004940740c25250001c62050414800c1841046000400c3d5081341d00c04690104140c041650043c1c110710a0303401c2907120801e100c00205480d50848010310169004034001c1080313048100044081380802da50039820801a1001000b08611910b054070303030b0b040f000304112880c03c3c0c250f031203404944560b48404280d07500440c42095841c0103125103012403103503900a10481c40e00344004001c0166403090759200d10400b00d070100c981c0307604022003000703010181c1c2201e99400f0120001d5014030040d1190130002440d422020409100100350001229030195104019540845250700600f5004080b480c0e503101c0c9140d4000543d4504518a695411a00000564907586005d1219040e8280c01c00780c0319a002c2400d00c00001e1811003166445071403100c0702691a22034031201c1c00e00094402c07001e0340c40072000c400441444 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 14123783 1250 14122533 14122541
    0x204020414010e0306070e0909030c1005070e0f06040603110d021b1605030a03121401030818040504020d020907090306020a0302030618040b01061b050f0d020106060c05030301060c060b090a 83
    0xc6090b20f40c031031440362540425a40b903900f150100001a000600e00b4101c2c180310440c1a00a001a01600d0404040588507860406c18070b000c44000742d100e2080c09101b5030400740701400034606031160341039030300c216000c542d2a00c00e030f00c100130406a6544081c1d00d080c200d0815281c5000200105640e6114101c841c802040140146000385000318205075840c40354110003002101e601502070320480e06662010345070002c004c1d0511000d00e0712000302407040800b054010307020b1803160704403988419100408188810700c02040714001d070b10340f0b410302001d0ba1b60210880040c9a0485070720b116070369108411110300303581d588028905400860509015901a00030b90f05ca140150380440e0300b0304568540340c00000041d1805020f40c162800180442480342c494901d1002c0b8101c82e4000c001c240d0b944291504411403000116600038810500013580c1c28001d50000f8156031615a140c0b4000d0788410391640300601c00c060902480c071159104005440d0844c80c1c000b00002c001c0c001910300710154201038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 14125033 1250 14123783 14123819
    0x2031314010c2004050903130b0a03020405040e0a120207061d0a05031501150503070c020409030e19090f050613020d1e141f050906060c03030108070f0f1d040f02040204 74
    0x14500b40740004000d42000402c0d1003232541d11220f000d070401d240c000c1e02885640802000700805808000101302d0b40c4490141520400c01c900080900041c00e04000341c40c0c0a4406000381150490a070400540c1d610600e00440c410040e140401500e09950002c1c1c1c15900036889550103004820010480c8907440b05514104c0301404000040c010010b4004c172854402212400041004205070750050304180c0d000d5090315200f405c01201441c83d20001850f0b584010000d01e20070000500144001d0745180100c0f0964041c035002071040c0d0070304000041842c01518440c1034156400704a44d800d40d6040c0c0c11400011203904201e004101040c04000c0251203810200d020107103d600c003182e600b420704401c3d62040101c1c4130281000030f0400d020080a01009405280e105505210061529804ac8001c6008018003001020242d1178440001c03180c0d011903221520031200c0c44401c0141d04907600070040c0070103000601b00115611458500850b42034185c002c0e40042c40801c0115460790008100411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 14126283 1250 14125033 14125039
    0x70816081002030f130606050603010b07060e06011409070e060301030309060e03120405040207060e060906010509010e010e0a02030601030e0708010501090614030309060f0706020d050403090602031314010c20 91
    0x42220038107520242d100540310040b00007a510700190344d03d080c10501c5001541704500c01b0403142d54645c00510a034100fa000b44910b42000910101080b5051040c0c642c00a058000b620081d803404e403148000031585160640100302c0c2400152000d407003001450b41c01100100701d2900e07541c582c14014005c00301c42c00350300082884841c0300c1c489032078001a0142e02c900f120744118942410141480080d4101d403008503a102d445010b031f012100301c180700c150300c94101d50009145540c507207810808000700c1a4441082150b24600601a544106072150f43c06921303884090f039661546401200209070206100d03090380108078001c1144181904058100c80600c80d080c06513549a003c1c18a0303d880c2c54045139450b0f0b1040166031070b103040000190100fa640300780b8050400d050303030701c0741c03001c0c2c0c2d111001000d92155503000300b05c101034001901c0d802401c558401582800c0d4140030129229506008180305c20a0490b4500c03900d0b803148400340301c00ca52124240d000d0624181a9620303c1340a440107603c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 14127533 1250 14126283 14126293
    0x7090303080903030609010303051b03040e09010b0904030807031a030d030f050a1802130908040305010606020607110a060e0f030f04050f01030e060106030203040309050a0b03041209141207081608 86
    0x41c2c0ca00000050301d0240700700804000d8180d1842c2d40507034041e480309605121010040100407040142031020f880102800301500c400c80c5002105142103c01404d44c00c1d124a03262000d210101c1c5d880189190301c040d050a000444c00e020302c0c080030b0800542c1c2061503241c420040581c2c60a54160407a10b88504c002c1014427590301e4440b2450300741c0c2c4c5044010280b210040110f003002d85440007544600315941c0700c00141c0c120454441e07002682c000d4009132402da44551080103c9a0304020031984251180f600014580110300070300e072103800040026007843c0d19100600528a42803000c103a0364a40841100d80d1410b81001a8016070032600c20b2a00c14519217403510101d50003405a281e0b081b5080c40944000da00740001980290400f400c00c1c1c0070031900440100e961303124480b40c5400307081090001500c1c0c0c40c1038074240050079401c03c84007041040701c1c0c00800c801c094079401403c071101c1c1100c482c0c000703203a121a110318109103030340800224814144071202c90b29110b0410000ea40644003511 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 14128783 1250 14127533 14127541
    0x50a12030210060605070b04060e06090d020c01020c060306040b0a08010c090f081501290a030902040b0f090114030312010e0601080901020301030302070506070201020c030a122607030207080705060709030308 91
    0xd002c40f0058403c100c0071030030800c42d440000c0c0d60a604541d01038400d010016403021a40204c1d46084004c650a1116074040e805d00c01d4920340402c0401d140440c2480244503d0811802090b5036000140a0354004d50300d540b0103801c655214503141000d00541c3c0000c110b803c8402400406078021445289030102c9070744004203d454011501203070032504030410342a164640362060300764841c0f801d15141d200000c1188211280048001412103184940d000300750a40ca90041008031000a00142c0c861611480c580300b8a4903070300080b03030444110328a040b0006100340f02080c1540302e80c5051400c4001024000301d1410a4205d0480c000d500030f9031b0b250929a01c102c182400c0303210a001c0600981e204040400c05480c113400180381407072040c0b06841d20204100c01013403600c1c3d0010b1080303c23800300d52078503803000550120181b440c5d03015a030600d05503003840c074003628204003003d0400c100300b42e00043c030041441104021118080d41c00030455000b482c04085c0107016901b24001140065035005c082 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 14130033 1250 14128783 14128813
    0x305180a0b070b070c0b01030305041d090a030809010b0904050f010b030f030403020f01090302040c0f020d0c081606020403020a0807080c010503160c150e0304030c060203040b0403031107050a120302 87
    0x15016503030700c6030306a072400e01d072a10b03214842d21008020000300040712986a00040790007880034025442502c2e59621281015041d1000c00e0003424100c440060344010000843d40000c2e02d00d01064050404140c0750721070844480c0540348000c800c13500255440e00340402c00130002490038030f91003c2e030000c1000440c0701041540341d98001016a0042e8400d20045c400b500e449000c500700b800c0c050402c03c48099895020400f03980994001c0000300c0c41c414030b04030940e0b405100120078005246016038080d1425600c114050195905900407000a0f481c01c3c000c10452781e04440280d6002807203421100e68030b14100c1d903101b00c1805001d080340502050480070b075000710309407802482d02e40030081307150030344600441d040164903800343d528622902d082c030b030b0680c1c141c4030720030128000304055980e982c1036003400414022640d01000843d40108010410000c5107010344c1c0a40b80e0620b0170712114903250b840c891403c40d06801040d03000c10502c1001840800c0003440410a600c03036000c2c3e0b08840c44000c02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 14131283 1250 14130033 14130049
    0x3040b090324010b2d0309070e13080d091e060606050f0d020c1608071e030c12060906060b09010e030106060519020f0610030302060108060105010909180f030518 71
    0x1905080610394001889132400d26005070280358001e4501ca2260604080801c109000310b40c0c1050141c2c50000c140b00d011402800410082c00e2282209052402c04180848a40d00c1501c40606105c0000c40c0f80c001000954000900d450340200450429515150702003000150f10b00c1c00719030341440e082000491500990933115040c1101c400c4904200c0300c040f403c40654000502d85085005d01e80041d203481e43c0010417100035041d00c000400d241414455035074540103d014000502c03203a02c88042001540050000701590046081c0321501e5100d89070160251140d45002484141031400104414450001404d42a4030980e070700c07d03858004405150032504240150000500c00b000b030110000106443d26030564100d1044403000f8010440f018103000040e2013248401c510590100705159040281902610b0031306d01401c81e030f501d05400a095600d241c070035500f2241d12603040a4030216070071070f600f0440343c014084100c10100c81c90010030303550006111407200321700b000003406142805c0e14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 14132533 1250 14131283 14131333
    0x6100806070207031502090405010e070306050102010203090a0f031103070605190218150705061005090c040f21080d0f110909040807050f0703030305040303050f070f0c030e0303040b0903 82
    0x9004858213580b50307041020000c2e41d05031784140d001c2001202c0c0b034070780e88549030003070041c910081141d040210004090704e07110f902080c1160300600a0080003140440c940444541c0628420101e210300d00c0d090301c0035070400b90306803990700020480b082441140d0300b040344541480c80c403070303000a04d84904c49803c0f8022624546050f103c003000b80982810b104020f600e680c2d0464080c24102041966002d190501c02c0f03a00d44640c08883c07400304001d061011070b280d000702d25202464205801e110b0802038030320fa503204448500440c3c014641d0a5408411248245900655002d540c1d05500000f1400f0b8a00c01030b480c44150f203041d8143c0e04000c40031054592030310000f0818880c03034503251290320507608101c0040d2080c0c0607024a60b012400104095002540700b40c4011995242034203025085070303001010700e5443d9038207104010690b036209070309088012403421700c03000000c0c0c0345c01c1c2110304a200b2034070300341c16100004002c60150007100160a16080440444030305c00c410070155004040061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 14133783 1250 14132533 14132537
    0x30f060f010c081c020906040303030b1009050913060908030a0b01080106110309011107090203010303021005010b250303060503071707090b010e060a0201020f0304030903021e0102060703091403030103050610080607 94
    0x80055041d114584c01e100081300d64804015041003010000a8442c0c1c0c4698001c9020030341e290488038190819032408483c031728070b0782010300c2458074001c08640f0002c40141410003110458070b40d0010084168085460180c00c140c0c0507490f4a886205000140352400311716010500800000075045d02c900c00000c640102c4a02540c02c1051800040d2071810715491303400000e014004021400100d075201441c000d500990040c140404030f820110100c170010380248031a0070f002c000d807091200500e03c0440340e20b59103091100a1001e90705046000b0310303054008a9050113826000034545c0b081400000200500d881a5840c4c039603501c02401c201d0f401000d00c54041500300d4442d03540c0e450018050030700350320300340009450120203650301e00c000e0744112000c4011960103d01401541452404205103850b940504003101c3e0844001030351310180140346d03004142c0c07919012810007503290f042200d19540030701103d842c1d585919195454490840382d04901a40703040000840301000540e040c041c00a40d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 14135033 1250 14133783 14133787
    0x303141510050409020304060b101107051003090507080d0e0406030b0c0304020a090f1a0105070f020f030703060e01020306010f1b080f090d0609020306090c0105040e061203030f060f010c08 83
    0x90000d1049a144881060042c8107080c8030000d80301d21280015031049101c1c240010302c00f1198401c0005140309a0805020014029004038080c480004d40f481607032800c54075085880010384040340905200c401c0108240107404000880c281c000582890905503a02c3e1191032065420520003101c18511002d17000d818800003068a00803260300035500240042c0c94014659228021102a1005400003460603503a40c90109890034000c4500743d4907220920340f180c1327044800c0c0c07180b140d02d50052030041d101c4d8a0156410300319540410003403008643c40681440500509060503000350002c8030a14041042025075101d4148517010403058036081c00005040e180f2180c89440494000542c41c81e00c140d400c100460b03050340c0d40ca000191003489200d0105a4030320503c10704d410220b014022281b540d000d0000142d1a0ba0844142c1c1c09440314031641403200e5541c10005845060031080030b081c540400001d100c2081c4449a00f14401c180995031009450800c02c011030300c052420402902070501 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 14136283 1250 14135033 14135071
    0x1208090706170606031509040c0513020721050c070b0d0b04060303020601030f0201050417060604060905010f140a051c0b090309011409010212030901060801060504050402030a02010c03091a0403030314 88
    0x41303080610f402144112440701d40304c0039030000c00c541c4034042e6004d455580c2074030000c100b6480c1114640c075038842c6040c3d0540c00e003291a070300d05000040301c1514442e1400c14001140300140300d00d0a0740d5120143d4001c07220025541d94036103e45a00041c80a40310310300301180c071162070600380111011240e00d54001e240e5a840c6031240004501184003c0341044810040020054941b0b912005656409001b80c0305500309201003104032421903110316115401d141c0100300d0100103503100c80c2110190020703090701c3e15281c00000c403903c03103640010341d0010080d12048030044024030860b00c074500c6140d0f0302da0103403600d034603866482c0201c100840c009803007140791184ca42d6030742e4054010004180111017009450300581145c40e0030880c0c540003560765036003040159150074081c4c2001481c09a0b003c102c0750406401103500c075190700704046c0c1400094500841010303c242c0703982000b0440d0303180009110007082d140b40f049500c64402a40000d080500b04c03555100e509a4250003180541e1614806000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 14137533 1250 14136283 14136289
    0x180705060a030204091d0f06060906010509030a08030907030c0e10030f14100b1c0c050603071404080114070f090509130b0c040801060b040308040902030a060312080907061706 77
    0xc0700040389010075400b4440000c1c0b02c40d860090f10800f0320100e0414040c90401c3c000c2c00c2c0f4146c81508114002e502400c2071051903107031121059000403080c646160b48002c0308003c030303261240c4104000d018110010811405150200703112007500d225041059082c1d65690107545003207402c2c2da000c10003000c0d1100420004580070101011107102d007405400007044240c03038a04040f103416000c0e00c60340e00d45520058070700d0b1091030510305420720312843e0141c101ca51a000c11080103801198090f01d0000701290b00103000710180c4074203122402041303030380d19211150b0a01030301007008c4540c0100c090b180450002c50054982c820545100c0c0d50396071002c1e152500300710b4906d4000d08040c0c46003009460340c0d000724050300d103071030710800a0100c299590b51900c00c5050844078a64803c20425805100074000100c00c44110f1f4100d5450280c0541c03203498480414004200950000300428501800c4040483d08402074511418003403090361010fa6403143e094a01200000c2111039191200c00050038900e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 14138783 1250 14137533 14137537
    0xa0c12051b010c0501020706090c080304030317060a05030604050c031b010806040902040e0d0302040e0108070e070e030c101805010f0507060509100e06010312020307020603061e060310090518070506 87
    0x40c014500600240282d899a80c221fa0010740d050710200e4071861a0000d01044004000044c509000154a01071940d10002d021444005540002d00c0800c00030a0050b80c0f15844500030b0000142619094185840e28559540b590005103000340500c5ca003135044c5680103800c0040000701a100c00d09203646600400008001e8000d04a9006aa814031030f81e409004025100007107c0319100180d903207082c100c00301c50400059000e0b200c1640f0681060008000c0b601385103420109608041000708502c500103410051032200c419002030103d0311002090381c1c409000040e54050000d20740c11b041d162001110840f1003d274401c40070500070440540051070b250301941d44941e0400c180ca8009002c003071090140c403c54450350340180e00c040014020700108400455070000603000440c9000407581c04100b107400002c0405d4419080184195a048007280c0701005245c1c1c0101265034a180002e08008402480e00803016030328030304000504190020000502003400360070044c280d5500d010100a166 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 14140033 1250 14138783 14138833
    0x15050117040f0615031401090206090603090118080d0b010201090201090506070602040905010909050f0102030402010909050403051207020304080c0306060303030a0b0109091107060b0603060a030312020c030403050a0c1205 97
    0x141c106800d4103011898038450180009000303401000c0340743c034500703140007a500301c0b81e404810303a45810030348c3d40144e5030380040ba06550000e88000d501ca51310202c17080d0041c080004079403000d0f41020000c2041020040003005220140c6c4010040440401d004900729501e0741002808648000e0041c0303e00e21f42500a80416031160720098940f540310000c0109444e020382c8026a0181c0710190042003240c1401050001c0c500200218114602600000e045001c0752080b51001c070740d10404281854812001c50b1400000154540c6160a00801c001d590f070b442032081117854003800c0c42000282c90013180c464092038008004605544441c10103000800300012202d05000304003000240b01800360182c02e49104000200c551200e0007410140155240055400c0c0310385010070400140380e6410589209503078040c503006000e101c18448400080c4103c08552000748030106c0d00104000d80003804c135910311b100315040422960356003035003054120000001402500b090740954461000400a0002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 14141283 1250 14140033 14140043
    0x30509030d0603050c01030608030f04030201140708031e0703060b0d05060d020a0303030f0f0207080d0b010e0414180d0c1101090e09030309010b15121003060c05030108011505011704 80
    0x900702503801d003102111003070307441201d15404c400200850740da0507106600042580748080c600e0501058480310b280e110302d000003414405099040d80840c605002600d5045074450001684c074141103800780600da90540404200e980042c000034412882030080300101c0304130b0f22109051009220b951005080003e0a65400c4401c802c3c2c11000350352418101c500540c06174400140c5c40c80400c82c42030541d08103204131038640d801003050f10001454030080b2903c1e003402c80030005000040c030004842684510034960b0744241000350181190f00a210310600541c01107910100345000b4184c81c5880701c840255650118600b007400101154584205600400c2c05160a6458036200d1204001c036440581d144400307a44080100002d030403091183e42d41c0120300319200d000311611001000400d10900c0b070212240c031100310100b030310f0b40c41100c1d0410103954003400030b10140c4016a0014117640007445850b0b059803d0100044000c10640452405e131041a518012a0380b4010a000c08903c009401180c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 14142533 1250 14141283 14141287
    0x301090210080906060409020105030106030f0605040213140301050402010507080f040509070906080601020606130b010e1201151a0403030302030405030c151b040b1e07061503060509010506030c0103050903 90
    0x1005030340d030003030a0201850302e0b02c80405070b0404910583c50b0220040c0b01d40e004518107c1000e0160382c0260599045900502c2c000c18448500000640500300b10390281d038200b4000b140380031030414005803030b405840d02543c9244061450340700b01400d944094034041e0204804001c0ba00108003a035005001100c031400b003251a1503030321000b14042c45412100d2000141400304240041d03a881003005030003041c00d100801180c104100080e07207450743c00200c0ca00060f81e0702152880c3e80d0065408415441c0010302c8608441c080b15040d038060052181e80c05c00810f0000c4000c521188044c3d20360561480e19040d0324205803c7d55000d5000f584058400d4a05110031302c81c04143c18000c200540e04140c42080110705820142808042c05001c540c801144010501c414804415003800340c1d4108842e03d00b4a03030040d4486a40031025201c0c14102900041c1402c01b006022540c0c024684c003142e20848041029a031a403a89600b200d00036581554542c01007000e200d090340c0b10360401508142e890080c0c0f4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 14143783 1250 14142533 14142551
    0xc0403080901110322050603060f04020d0b0a0b040e07050703020d1d1c06060b091f090b030703060e0604090809010e040f0213030b0907081e0114011205010b030d020316020301 77
    0x280c9507401c503805c0844000214248080d060f501d4030405002841c0549003103003141032802c001000b03444055000b074003496010828518401c030303640146281500c09000d01c8921501c0d8940316905a1144c017451000c070030504080766800b8070850444580a426502401981059038030860b40d00010920702c001140d0302c22880c00302d558800c43c001220a9041d2000d40160b51b19103080c20545820f503001026400007800803114a4851031024010001c0d101d609540d1080703030f184240e039182465000511052404000c20210b079815074481000d070f6590031903592003595410200b000f030360313003100004180d40c070280081c80ea02d502a585140c5400402000810103100e02c03000c0000f01c0e0030920030402808803042d41001800647c1c110319401c031088901519115003030260190350750406851584074100c03140d10080d44000294881c107250080d08406009559460460100302040d604042c5d40715441e110f140040782c81c00094046040726290003542c1401c890702d2030881c0381c241c62a010790301552204605 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 14145033 1250 14143783 14143817
    0xc062d0709051c0501050f070507060f06030f0c1707060f05032707061715011b02030a0606080d0f08070c060902030f061906030201090506030901090501060b0a11060c0403080901 78
    0x1c030900c2d8850341c0210620300e100d414005c0c2912400307011101d91410080c140700000da0b22404403420280c01c44400f0540c4e00c042070304007004010507032000c1e00030000031b01c8203c10801441c00700002c0702c0070040ea4201d50003480c1700c0c15803140d51030b00c603d0020035403040780d8400c4103005402a5501c001101030701c00041c400c42010401600c480800c4001982106009003c056000303e411400c84150103000105850000910070314041018003013814000d03440760048107049a51007641070107a0290907184288920710b0802d018100ca401852054002e8041c2d0300d0032548281604095489903503642c852540390130703074240c0303020340e01c580243c2c1c030241c80b00c03c0748015032002c2241040c5510341c08001c103050306d0080c115503802e450f0740d24411069800c10108002603a80071244005a60080300c4107540ca440c2d40d000980100300e000c500914a50070325400181c60001803002c0c2c0f1401c02161102c590744c0d10b444081c0ca864200c102d80150b140d48052005101260100007d4140d05906051605007a44640d0038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 14146283 1250 14145033 14145049
    0x40e06010b1b0102160b0c070c0f090b03010e0c0405090a0b0408030610020d020a02060d06081c03050606070507140102120d0e07090c12110d0207080c062d070905 71
    0x1814054000050503450010510103207507071100b0a100031402c040001d03003900251026514080c105418103400700c1c10070300340d0364110340c0b000d54005e0b10419002d40e10300003007052104a00c034051020f86415256840740c1810b0003410305100b034040213091041a02000c100080401400c00f9520740711361032241002898940c0540d01542c02f540140380ca07171800c041000703c02822242ca9004540100b5858500c240c2c000502c0d106041d070464012340c690b040980c140004242c29845481184580107408906444510340820380b031a071035909000550b107220521610f880340c90740c010b1203a401141c0400425210484400c0403800504c146d03100503030180418082c50304001e085400f900d40c2d0300c40c0e41403018001c01030000101031f07100b01800701c4906601c000d00101c21b101400c6070700c40d440d42a030410b52a408402c4940042d0050011502d81343c240c14800c206403c902a100c810b1711031103012481403084c046108158244e042d405a07074080300c2494a2818020141c102018800030450203d130a580c1c030341c1c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 14147533 1250 14146283 14146289
    0x20121180b060907110709021e0708030604060b0405060a140c030712090602010c080609040312051303080a020708030402011404030512220e130c03050109030302070507060206010506030601030902040e0601 90
    0x7501900c0c1c0c10120704101d07580c0c034041c21000501400202880440c0000b0075a4011140079002c0140c42c4c0c086c102040b01c440260000300d400c80d420008004040001303840145002c2d00c001d0b94108007590301d603117000e04584501d005499000c40b06101c8450300310f1182030300019184016200c1410000d00d01d00082c074540010104449454030f0f013a03001e4050740e02500351001400c261009020030b040320070015006100203017845020b50305120000782414084c01c5c10140310700841d002042146810700f8a440090090941240041c101001048080019000340c4041d542c1002c0c2c0c0510b0350b1102da0041d10066100c00d01a8a00c20052000102250050002d0000b1500d5120031a683d601102d4a6444c0d40240074a1a80c2c40400e200081c02281c2d03c3c0c0b141c0c10380c42101c0c110f45484a510906110400b0840da90004225608221801c0101603240e0094030300180304000f02c42144dc0c03540f40507625140240a6240c010b01c041c80082c3e86507100e6048101e52038000b4000080d101d50b40044e480c2445001d0b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 14148783 1250 14147533 14147543
    0x309130605090903070b160216060201020406021b0609091b0d0203010314011b12060b0c0705030c1008040201030f0204080a0506100f06050702060304030203090a0305070603110702012118 82
    0x903204104500b056584154071070450b0300a589480c005a43d90400d0341400341402e601e8400c980001c1621500070080352240c1c2115102103d021a52810028040d510601a600050203481518504a03c20110076800084d005011606008406050020150005000703080c135000c0d81255040400254000b013000b800944c501695035811410907601f500510101a80d06071724020110f1030f024085081240250614a0f161485001d81c05121000e0030103074024101c0080e0008840c00e8841c8005851000c8800c2036040d11070240c8a003040061102c035400c4003030046080c00b40068015842507010043c4c10091207001405d041e01c46030280e00d02540c8001c100d64903407103001402807440c02d280c0300c4402000340d251041d00d9641041001403045c0502c540003800f411011002c41e0406000b40700383d850004014201890f6196030382862640c80c48030740300d0300000c2480e083c4403403020102d0000322a6856010b84512047c00c2500500c0340300100b0075840b555545946080400390a10b4088138620700d50b001d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 14150033 1250 14148783 14148791
    0xb090a29010f050303070f02010203130906141207060f020a0807061505040e0a0609050120070b0106020705060a0507150606090e060a0e0f0403020f070e0a050a0605060409020a02030913 81
    0x100c0c01121919040c1c000d2584944010002c00a80c0d074000111100300340d00030201f0808400501c01030b403a500403040130000a0080b44000304d05250700b54070243c00c8420b410340e640c10100304c0320140704c006030054a4054071908a0341003442003901503c034044803070380340d4030407961040ea8a44030840301e50031032881100c1240e2612200b201050761021a80040c200c03c032010007035540c00740d00882d0b0314030300f021004043d07a480746200414800b0a510180c04a60075030340e807551060030800c0ba91003e80c002001100d5504401c0008038500c0d20000c2d000342642c1000e84070a1a100c06400306440c990001c1030100c5503403203414043d14420321039002c2c050040c070b0107881b0010403c2c1811101900c0e03000c01480c06001d51381c440313010403000c96000f0070540c00c054059400325080d11282070072801d00b12440c0048145103d080740015028200d0420188502e0364281c04006640f00c054514081e10124803503183c1c08074084c002441034100a41c0140004038050040364600312224020960301082c0400030151203a071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 14151283 1250 14150033 14150093
    0x301050103290f0103060b0301030f0b0a0203060d1e1202011b020a050607030e0712050606010809010b130e01020903060a0c030e0316060b01030603021906020c0607020d0b090a 77
    0x5405081d0b0010b600c2c508158060480d4107025281e641e054501a20440e80c1c4545801c141c1d00075440300010301411260039941c1e44c0c40b400c0c14298058515030071900c50305101c0002e800d03000c842c800d69009080041c01c17481c003034030541c440c0a0001203200150398108050401c070b41c00288070a051040d011850340020a4112007070401901c800b005a12440542d0449080500002d1010840c07a61000c90b86c140041c1080c00c480070703245402c525420007098290314103000000e0160005015206400907611600c2550f9414130a84c02d0318410304000350032422031580d0780605103580d0024460301807184001820607c00000080c0b03401003d41e013041403a555082070b014842e074103021303038020003241c800207500d09011400b1142a95403244400b502996a801d41030509030f100340c201f000251f070001c0000094541c94203070b15010180d24400c65000d40b00c1d80a5070659418010300b40c610803600105858101100342d1a06108048000c100316114040c001c0402d0015000d050070003180381080382c1016081c15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 14152533 1250 14151283 14151287
    0x405070510170c040b0403030201020315040e03070b04110409240c02030301120602040b030103080d060906120b091207140d08100501030b010311030a020d0f09021f0203040902070803010501 83
    0x8581005020356103100000640c00d40100202040c44a192006049a90344060560050207030741c110411441002600006040e41500510b00a68241c08590884552102003008540c900318198592742c0050210201181480c41c046510600a4030159103c081e02000503045aa07403a404490011a01541030094890140b02a0b4406011141005044829000a5624081481454921840400c6410401c2550f4055400900c81c0001700354581d6103a2910492507048450401e50b561700d40900021007068500501d8222400030b40c0396000c9030700306c0c0ca650050b010000c1030400644146145c610701050700b40000d01d803c50043c062810081b001c80b100c0c0e41040b81d84503905e8208145441404030540305a1021030884009080000f10140c1c0c03200160060010512202daa02101204128500e07080d90018204030001c26410442142d10035101c1c1c00f1031300181c80194010304107040462201801c55085820409540100c03410700390b845507060241c0e0312000e0b0444816502200421441d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 14153783 1250 14152533 14152543
    0x9030305090c09040f1a0f09010c02060c030a09050c03030301080c01020d0906050307050c150a0c1b0f12020a0503031311011e03020f0d06120b07050304050a06050a0e03120405 77
    0x1c801800036021a034010000504041c001030405418256050710714020404402050314100d07036050900200c61500384a10010000f00f00c03004a265400c0c10356248201c2e1004c40c240303104040d0b00d1581c609541350320005000412100700e04480301d2140c0080800c103680e08002641c02031450f0340c0208542d151a00009041c818415203070000d0015500c01405815040b01c2030b02d60200007880c11a454805041e10b042c07420350480008125200c5980c02d024031118a5003222380030079810b850308c00301140c08888008040c800081d0140400120803451000600c0014020703400d10000d1040301d4075120b094a400e07096a209030b5210095035480d550303060801031200c08a01c0d9440c03003401e020008180001e00e0041e10720265480740c080642c0010200ea40d150a1700c00e554001c9a2030364200041521801d400c4a00080f1050070b58400c8941800508054480c0084901c19603001c00039140d40c60496071004082c00c03019061010040d11501125044c140c02c1002d050304a681d54030b0200d044c1406d00303003c0e0800e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 14155033 1250 14153783 14153791
    0x904020c071d07050d0209130507020c01020601150207140301090b190b010507030203090d0201031b081905071b0c05090c0901090b090f01080402030c0411130501020106050904020f0d0606080109030305 88
    0x10711241c0b080010b016080030555424584034580540d80d0340c2c2c47c1c00001d0711002e0031800b1a0b55286401d044c0803403558002102803241c082038080b64520703600c80004007200103030003100500603445180140f054a12000210f5804034001e80049000d0400340e907407400381d0b141100d0340030340c1000810a100b414a0340f401194000312003801d1607858900c554500075100d10440031800e004141d882c0116086901ca580404400c5140610030184413501c010010060002600c91407415541044101400d018500c03416010301d0301c13030310782c28020941035144444140d1645019241c003216500d0004040e2144003840d4400c00380341c0880b550340d1140000141651625800800080905100c800c02507210900a040349400c00d0822510750350b11480000e1030f0019103c82581c115040c08910080c2007908405010070200000d04c809402c0e880300c00481c2200e5051281c00d500007a2600810702508040134040c43d100d07009004030141e005c10741c60b18019146594400e81c43c0c3d84d903034100361090650610a003604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 14156283 1250 14155033 14155079
    0x20c01050a09050904050c030f030705060a15030f0311031902060906010b09060f07120806010807020606010c0305090d0c0311010306050a0e040602090102100f06050f03010507120e01020904020c07 86
    0x3041c0748540002c102da4858040c06005520500110307040c04810420745d05010001003c442e1b4086403007040980325001000200d070984181c9010441d135601d54010380b0b0060004e0810840e02c03510b140c48010040300703002002d6090144102c000103c0701018001030000303580340e015205821000e42c9009207085001440c0041d540c00c13400042c0100a041c0c5c0850b03010500c11108242c5564581484201034821034a0042c42d01020106541c0f0503034000444c4c40c82500242c0b100c41450f5580c81c070598440c00116a0a40003600099914001034011405828000c101031300070050211150b40360041c40196420945030502882d01100d01c540e414019034000c1c00c002d48540e03100900c0c085c94aa94804082d01c0246a241c0224104802703034800c0141d42d999144200c400e00034044072024010050030a4003426009800c100c450034900c1c2814003030076010b03004940e40c7c7e0590425050340311000b0041499403a030300703540800030300c9201d036151300160900001d00c80207010514900954045006044c40500755 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 14157533 1250 14156283 14156287
    0x30b0708060307030206090f0315010305011b0f0c030903020603040b1603020708040302060a17010306060807050103050702100b010e060c010605040b0d0515040c05040c050703201b03030408030316020c0105 90
    0x7107031004034000d012242d054075010f8640c464076000612520021a210750944109070000d4200e081c0c24001504983c05000200100340d51f1016460a0017134803010880455846100e003154035114250800101d8001d10b003046801e5140d40c001040f0f030b4002d43d01a982400cc039410300600c0b00041d40b10300ca1135007141c1000c5141584d25900ca034414003680c8000392280101140744d41c8601d0060040f80020002c542c00b03802c41d0341e10b07840d0160051015001d658000e01c01e280700400d41d07500074030600340165806d030000d200b00c486859100b07018088504205d03042151303220848181d80c65040203000000c003400d0012640030300f8a0140802c0340c0c54500d910f4490386804a20901090380800e00482c0d10441d41d03082e211070b55503820052075032049940000e030090705e081819140140d001018090f030f0381c82590f030380f255031042061200310081c80001c00001504400714011180356000c24050541d20040c0a50307003407503610882d02d8210381040307031901c50001250a01000b01a07051201e11b440c01c0782420140c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 14158783 1250 14157533 14157541
    0x20c06010915030204050c0409020c030c0601150e04090203150c1b070b19110304060305061009030203060c0d09050a03020c101416060b09090d0e0a0305060604020a051210030b0708 79
    0x942c91042c1d031001034000c940d2407006c00c016000b04800c44000d0035003581c0c2990384003503603184680d80740e100f05500c0001d07003c0c01d0004500580d4001141c2c40c0b20035070f070780c0725010801e08004110082400c020200da15110700201c18000c0185607c80d07034410b942d1282003035251100001908195991444094142d400c070a5061055025080594091070111083d0034080c20902409480f2040484d040e0816480003042c006205039160b08003170300c640800d46508681000c60f480c1520441560b000082d45074000800123140458602c024050b049040d038004079a40c81c090b00c8407401d000c1026015030051704081d000800074107141d00710303482102c0d183c0740000c581070090306581300303034020030030040220303c0c001c100702d0103001c641c1d040089080d10040001c03003035090141c052691040103c1e8140c0c040b9079451030b069030514004c040c080403260420058506940c0f8803040200035801110a80140107041c00309496000c80c0340e02c0c9174410801100051030789400c50038071408105008104030b0401519000700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 14160033 1250 14158783 14158811
    0x3020304050d050309070b12040c060c050a080c030d11040503010501300807080a0305070809010e06010b03040f050f030c01053303010609020d0501090605060f1e04030f0303020c060109 81
    0x103680d041c250b40f4103240c984d10307071151540c108a100d0703201004100010841d41d52451001000d00d0265105205840c41255600002e5034030381c0a0410142c0a500400a07850109075802c0007484000d140205882c9400c0302c419840c0c084130035118540b001050003040130f00080c00d0900c18a800340500842202c03480c200c0c8031260b00034020044403500d060886150b002d00308442c07101514540703580032110781d840d07402141000340240070844080c000104040041004250184904024200b100c0041c0c00160f0a00d468500280d00c013410494443c188403e00760045007040c4440018200800302865070707101592003003400d44002608020351012007440070390f13510007030308000588401203400341c40a251814000a004200c1e03944050500d900004524000244650106041c0e1f000301070208403031a112010300c0524091000181d9420804000b441d01c0201c1d1009001440300055142502e0715072680d0b50205608110102100441c1d00800c05c18081201441014050b111120040000b000c0840daa = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 14161283 1250 14160033 14160043
    0xf050906180c0702010507020603090c041409030a140706020a3209041a03010f09170301030b0705070809040f091406060a0b09010306050901030c05120d02070612140711010b010302030405 82
    0x80b9201c42d42001404030708590084090343d007001d03002024161240760130002c854441480086141c8210719242d613629440e07041c54440750080110100544c2840e000e06419134901e600b4444440c8050405e001030340c0042c10500041c00d4060041c0c3da0090110320343c0c00b854202120350700c000d054046005000640e030a071543d05130703048000708a4011030084d04400c101c40c0d403440c0014025815500785041105412119003050500b14400d44a0b2070aa11598a44c03035640d010a0000038444c0e91941c0125100503c2800034160240c0a80300e03071483c0087c28000103013115241c00e40c88204a440301c0c1c2e404280003040800700c250b1000800508464900b40c000107400c81514011500c82e004040740c180030a91080d8402c8010384000380c0614040e503120300700f030300e5406040c1c4a03441c1b0954040d40300c120850004120400d41200c01c1c0c000b444280d017000415a54007900b0007080140e940e40e29482340080010501071400b42d5140e8850103203080c0ca26080e10b00b03440390006075505042c010414072002840c0012 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 14162533 1250 14161283 14161291
    0x7030207051506130516090501020604080306010f11070e061318081305030703060b090903130e13050d03091707020105070b04060608030d02090a050a0509070c05070801060f05090618 80
    0x158007401c0c3e603038600043c184000049280220902c1d080030000428030f036840410552209403280081075540b0b01c012039071b660b000c545c0200050400c2c00070078519401801022842e071b249007482103003140188030451a00750070358018500c2c2c03901d5000344803980c1000099960f92040e40b1405000c50a02040c00100280d4002c3c001058604001121a203042c8221070b500060030000f403e0740e07400340d40d9041000c0901002c0c1c0d07129101d000f83c0400704034911000012503484024004183c69120302d401d02140704004020f0102c000790070310240d2400013030710030b0114008460791a10300140485150a00d850801504920314103007100c20030500001d41c0e0010151a045c85c0d2005050700b03c1d80d90b0f450044050403084d03105010354800480c102d040c0410540190a02580645003000b185545004110f0400352502c0f55035082103031100402c0d4424451200224058041c40032101c2c1250344028081c00c44076650b01412540c240400c06200600e40178400c00d80081084402040c001044a5000c0c24018050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 14163783 1250 14162533 14162563
    0x2090c070201020312090102040504090309090501170a0311030d0501031a011e12050a020307080307030e06040f030204020702190602070305100e03040b160506010b0705060a0501030305031302040b0a030503040305060703020705 99
    0x4000510b01b05401d4040381c02601e0054018040ca100d00e1038003a2543c1d880d0b010765000181002c0020840504082c050148804001c00415072280c5980b002e5507210b4400e084d0f11b081d40810880e03101a8851802aa40218030890314408401804078800c010b01e84d040c2c10200510388100c000a216203145c004200c151248103000c1518142145006880c3c80d41d5004001c3d010b0086290000381c840000c006000014081c2d198403040007004400c100040c4a280180780c111000c182041c005410154050103515102402a0140c0c0341111014280d650302c9601c07981c01a07000d030105108002c802c0c414411240a15101806212205c2203181e80380d005c1d60145810750203000c100041289996915520200d80042c05c0e100556141c918a0520341d205030400d80d1a803103420040b400744981031060780d04907609680c0f0700b802d50310744211f0780a40c41c0c800c0307038181e9000c0e40394141c102d01a0340d882130071001941729000542d95079203145042c03070500700d000704010181441031140790040b070700214017408072030118 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 14165033 1250 14163783 14163817
    0x1504030503060111160b030f010909080711011b0507140901050901140604030b0a06150e130513060f050604062418080d0201060519120803060319030c02090c0702010203 74
    0x2480c1143e261001000780c05c84100311144c000514280740c4c00040d801006001d181e00d5040c1c1e00d8185ea181511540740e402407520b08200301840126a2566400511030414904141014980e6280143c00701c0d5505098070540c0108008202ca5001d005840c1c61090b001e941880ca41e40c50140000d2000f0814401d0007103ca01000140545a6560040354050f561202c04500f503814a900901c0050200340140703006a1150107490481601684100341c6440006042500d80c0300c8800518010b404040c10404561500c0400c507000511a0b0191140901415800082030700c0d041007040160b071010781c4541e402d80c0740c42d0318504110400211503114628141032064200b001d0a0042442003e56031151806010301c0c030030000d9255040d08480c00311201100c0c00584e80d002c0e0441c103004c0c030b1500d01c5111046000c4056a000003005480a154440d0300141030b1210301510303840b9800c03141e803405400c40006812201c45421403400d03e0343c9580005d1500b200b942007811640c000303541c2e0b10074088600c0c800120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 14166283 1250 14165033 14165057
    0x304020d0f0b040f0203070f0e07180f03032c0303030103120c0204060305031911070512010207083001030807020f0a0b0408011e0902030a020d06060b0f070515040305030601 76
    0x805401c9400441c0d00c03284041c00c0b8a0507041c03802c403491800070228401d0042860009040101001c4401507500b10212513555480b00130302030b1a00781005807403a0149d000b0141c0001c0080100c0418001140291148044800e0b114400f04a00c54049034150800d1501000102d03036460000c2507a040d280c0c081e140e0341101e1903030f010a03100d04480c844029072082c10814003008020300840500030070302e400c0c1c074089019240000b00b9682c84650241003d9660b10041b01003104e49010388190850000030400186049100e07151098194410903c113004072001501032000310140102e00c03071003c005000c2d401c100c0e5045030b80d400a079120b1000080e01c0340304500d85041d0310b60307140340f03000c401004504c2d5100d54981d41da0f1202c038081d202040c0d40701c007680b041100304211284540901110766900401407d1b90506507402c20584403030004043c4e45060b942c1300c010826000d90300052444030038107014180c5a281c1031920b5403a2841c6219040c0080314507505000c0020780040c00d80b6002102400e01c10f40c0c01074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 14167533 1250 14166283 14166293
    0x10b1f021203180303011202090a0c02060c07140706050301080709021804020c03130305010b10020f07090c110a03030b040509010c0905040209010e030a08030103050f0304060206070f0519080601030506010309080304020d 96
    0xc00c80300520f100c3c040040001401d000382d1000c2d9110510945582c07401d81d4443c2c000500329085d03042003a02680091000683c0040035a00800180380315203100c2000f0710000b0141c1c0d203040916040000441c00000c0140007121381001820b0007004460400d520b44481046c2c0191040010040a8010f580104071049100f02c2071003640c105251580381022019502d051080c041c0c00980e1810f4042c2000c068000c8400d031021a995440c43c2c1070344003e00820380f074000710b10024a00300061804100c451820000c00308403e01842c3d071081c2c060740d004900d8055240c00c120442e01c0203000b05045078505403d090702240c01c1802482101c00840c2d00581b034a9482006a402c00c0c00040c0132030b414002d428034007003000f041d20007450580340038504440318440d0040c107903980e0344154099140940d00210024800310b11880b45a5900705036480c003039092061182442c43c10358184500400442e00307000401034196418400c00d907002d4800d2078140900c0005031920f555900c4040e2001c0e00410030b5900c40c6050103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 14168783 1250 14167533 14167561
    0x61d01050c0109030c0227010e040303020405030d0c0c06080f13020307050604090504170903060430080403030c050301210206040314030301031109040218070c08040602010b1f021203 80
    0x2075100d0000c0c8080122454010400c80c46100200d208841e00c0040c8151401c1d9040d104064101810b0b02040507400c00c180c8a0109800a2085080503020000455182c0f024403c00195056a84910301c401c00d1078a00310080c04c80d280c0207a1308210041c000c111006543c110400e812158401009420740070310b0010a0611303000340c0040b074004c4030010340026821520f41c00148128000c2504d001c14200410042d20903200301107005508d90700242c08580131840300d02440f58980d451070070300c003860403491410003203104004800d0710102f4014000c100915800d4043e2001d40314051405500c0c66040007251808080e10102c001c28095000e114813045442d60011100a0f5400c040403a81448620000d235540c2c0e4002d000072101d464050000700700310f007459440d8501032503004094601d540340c0491410403400001340100100100c820070580880d418070003c1014080d2130f03001040180e042c0040c04440d144e0303603031042a42c164601ca00100302d940072038036802d04c540d00c0002e641c0c0c1e40c4130201e80350403003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 14170033 1250 14168783 14168797
    0x11060f0f13050f07051201020301030506011a1306050a030c02010c12020a1107090204031b1a0702010c120504050301060e040206030a05060a1502030d050106051206101103041409060901061d0105 85
    0x144105100e0090180000810f241101c101b211490303120190b411949080c0d0000380b1000b071090303010500500001c0310080511080b0751111400c0da00781815404552400c2101d540030324003049002a40304181603160188011041603400244084448241d0040c046030360707821a680300700c1d40480d091964034401c4800c001201c101500300c45041f601d0700e85a400a502078031088070990807605440100b0044040217000311018843e041820803240500300c2160340c04140200d04001e054408200010003000660b0ba50681d50348d0b4840c1c4590802c4180b5003151100c0e0040c3ca510111f1004010060f0341d48001c583d4440e0fa90140070469882da400030032031454841d0081c0c0c0c0c1005850081400480d40040902004500160103016a903a81c0300c040c1c0340c0e48501550314480741218000601c1505100b0900c0142080518000302200c05c0c0321440c50460f005600418800c4070313084da5100707591520601480d007045089a03c07104651606002030b140c1003420710f0145044c0c040101c0078101e680108161008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 14171283 1250 14170033 14170043
    0x601050714070e0f07020604061d06040606050306010602030f0d0207030c05030409020307030609021809060112021204020f031606030504031e03020306041a10031113080d11060f0f13 80
    0x810a542809840b40c0303050080c003907040003000c0041d030455128142103009040b03640281c4019251038807444007508182e5070221400900c01d40c000460b2904200343c030b10942c01600c000950b2800d10040500f868410390200c0300f158004d20840114010900c121180c4200c4842d0050344e41c1018a425140d0b0700c0b81d50400380c0240800324001903485a6900154400d80045e1ba04001c1141c4990a604c221f000b04c06045607548046e070181c1507075003000c0c0c3d410f9820002c141400204481928421400d031780c001e8071504808804032050004500300b210ba0300c0e40b0b0b01400c90103005042400301c1504a031120701e1068008040d10340c1c010406050158450001c581b400c3c0c02c07104110300c00008094003961056801070302035850901c10820044002ca10b10b190b880005024030080ca103150320880107440e010411018140782000060401028401d14000914200b0090310314660286c00251440540c024000b0154110b030b01000303c0000c0c80c0c404168040c041d580c902807551662153f0f42d140c1407002e01e00800c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 14172533 1250 14171283 14171303
    0x90c030a03110705030610050d060b03010c050a0909020901050306130f090b07081b1b010609060806010f090501050a0302040207140706020f2505040504050a080304030314010503160603020306010507 87
    0x3050540c02a40e500803011502c0c00c0750006a40c0304189a0b4911048900790a41d2015202c280450329041030040d06242c0940e101051811000c0f00107400c441e4040c147c00b0100703100203008200c0359080f4100000030b1a40c032070214104029840003034070754070000f092148605034012611401000c1036015840403981d202081004405a00e402c54520388140e8908003c01c1181e00014080c11003452443e444080101d1182c0c18003800c0d580c0030700142702c0c82c050340d91f00c0e5403181c81c00301d003512240c411b010040004200030000c5524041314072010750495000044c1d01c50074600103119544403c21841e04032075040c0c60059940c00d0504154030400074581010149000e1644001000755000900242c0b0900005c1074500168140e010500708020943d41500c41c4c2030144802c00c540c2c40c0a80c00750341d0240c000d02c281d030981ca82c141d03900c1c041380c0c2c0121400c4003ca43d0310300d0300c90f80b400303040a43c85024010940041100c038007031500448403401980300707403010160001300003401640f0620945113829030040d5145 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 14173783 1250 14172533 14172553
    0x13150c0903020f120a020108071709061b03040512030402040618050411010e010804060b030a08030c040608060a08030712090801060605090301180f03081e0108060a11030603070608090c03 82
    0x1400a06107120aa106031144014a1483e03c1c11045000c20754041c140207082d0513400e40d00554003924020128000d100080034500c00305504a000140b19051420207070415152500806c8030b0301c0d4980f503c40746402020700420000680001e40e588610300c0c0c1d03254a41d01c075500e510010700030f010140c10040300d4041c0d02c040c0380e4040c011500305c23502503403190a0800d00e051201c40116035120701300032050f0020703100c40045808180316a0014102c008003505540038070109880c1e072000c03503000344c80072015191f00040c200002d90740000300c00c0d00186c00310303941085a440c2072203660f66405825800f400849080c0348141d100b0340206501d02c000d0401d84002d2007069510480a002030300030011a50103542050120131680700d00e01030b41601309a00175005820b001039034030110f0f403038440245101421000032981282010452034014028120340c1d0052001e403905480c1401030f2081400b800c078958000b4001c0c4a4140d17000303e507410a682161034000041d96602e100c0526148082400c2030b01805400004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 14175033 1250 14173783 14173787
    0xe030423010305010602011107020613080111070b010803030601090603050a06050a0f050901050f060a14131202030d02070303090b0c01021b030a1716030218031e120f0313150c 77
    0x101a030038003601c0410407607036204016420b0f1038110403401914001007211000518015000c0d004034003140100e06a02515111078070708450000500c2c15141c000494400100071140603690f0240586201030b40c25400c01d07a0018000081601980060686810000310300748580d0744190003c200080451150640d1014040009900d0b0301500d80982d80d400004a40f0b4281240d0000f0303a20710103884d0b40e01d0040030b80c00032145d10342c503520040d44400d420040490072900b03120400c40179000e1342d545c04140c0f1038280304041c43c00200e07040d02d030159007048404202094003e8903e8085400e0b0414981c0e42e541e1107081d2500900c00c40ca80500208068113440c20042c000001a003d40b01954a031110320b14040f031035484801350101c50140880205002c1407204510030380207032070340c22901840604904447c00010741040116480302c3c030344040035000183c591008020348100340400300100707880d2807548803804480e071000030041c401030381110440c8810000e9034070410301103030a0301e0b40800c4404905140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 14176283 1250 14175033 14175089
    0x30309030201140a02190201200c0a1703150d0510050c040801050103051c05130504090609060e15060109030f0f1a011202040605010504120f0203030c07120506090703030804060e0304 80
    0x1c4000349505030a050011b46005110f0311035181081c0040d100343c116503110050b01980450780c6410a8081c0102080014400c10240106c464000300d14a07241e2a001c0001000440c3c1d07107601c035100d400c400201e03002040300824040302e95101910041043c0e505c3d4002c0450a221300c2d40700304007541c87c00b0000400e101d0041480ca1030014492004507000413029821105d0340164008154410401e04003084030f807401c2da1060007918825440070950040c030307032903d00440310a80f085c107036140c00640c203141c240e41c0c102d014158012401d0904842490031030301d500942d0f0b0f1000e50000c040620014898050001c403858650007404a01603029441da10703030310306608490b40340c00201d00071400d058000c00e5940c010b4081d00d00b81c84580c41582100080d64998507020b03140d4500c00c0c0d030140401c1003070b908400c0060000501400020360304114030040c41c5040351420500824401035070b00040c1080c40040d60201d11740b500301d500b2860110b0b252541d0048941540300b16031090124101c00008204041c0361111 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 14177533 1250 14176283 14176297
    0x1d01050901060b04030b0a0c030b040204120b01050406080d110313030f0308070201060308030c072604030212010b0105040b030a020c060103030e090708060a0501030c02010b1525050604030309030201140a02 90
    0xb03000c92030703803003003d6601d0380a2800014694905900011200e00440c2e0207000030180500e00401d000c0038060216080340d0264001d8078070b024588031800103024120b482d0302d0041200b56420081c80d89010040c546548041080d03404200702c0e8096803503d5a000c0040e03403c2d20341c0103810240f001d943da2812010001f0f24240403804601d0030700000d00d11500600c0b510040780d0b0820002e42c6159610000300e090b942c0b203448110340142c88083d42860210048007482a02070100081b541c1c0c50b030a6004011241107040c0020000d44c0c102414090300da6848802c3c0c1c2c040315a000320103a2261148800400640580c8030802b04074455403000000341540040d15900000f425500c500031078841e40300442c2c0c01441114615002040070008002c0395100e03900c00b02401505200009035260a94006144440040c210300014100800c0b40c4416900c1a10503070810446003040481015031a40d41e16114040180080c041c51b42d101c60340070074035000390000b50900c07a19403503103022403511100001c02504070003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 14178783 1250 14177533 14177551
    0x20a09020f0406110105070f030e0307050a0c09060503030702060405040b060d05090c040e010c0801150507081603020706050a0e0f0f090a09050105100b120705120408070215030601120c031d0105 85
    0x505034213200d040c0310340d81c05400d056650300e60840320300300168081e0220100c91101e03480304000030001329070300780080b00306580b00d40c81c3d44000d640b5010b0242d0983d03c041d00624880d800812107800180d848104503411510140d60101d1024800b10006000e030082850320840e0500780000c000300b40300e02040d15007006c80112410403011001483d81d030700b202c000c9015100840c80c08401400121880c40c41ca008502c0d1602d0124500b055a691b03850b244c1e00480303032200c60340910b1540305c81095014043d040242000c0c1c039015042c2103400100400000403400d0040c0290031400010f6000e4403043d180b491080009008074800741800c030b8114000303107044c100580c0da40d403a1401080d1017008506d010303001c0310031201985041044018004100150103060308040c420304100c111030625035401c2c09032080d8043c0101549456160040c8410f10448910b003074850351081040140a07a008540310f8620704003008000b0360030302003080540060907000c4084140c0007c00340c0701c800c1e101054012030720802201c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 14180033 1250 14178783 14178797
    0x3080708070507060c0519051e060609010608040305031311040c020610050301020a0c0b060a15080a0c0512010603090f020415050406050405040206070219180204030618050309010c020a09020f0406 86
    0x7608101c5422150010080c10747e0031441c0034603040b0404c1a0801d40146c0150150f4849a44890501041001c13a80d00200150417060400a56147c41d04a071801002d8030b040054043c07070107a5008145200040641952201620100081c05079001c5800c0c1d0300040604104005144018040d60310700d02116001d40d03140c10f00c0340100c0d032401d0600941c2d59001c00e40d250140350005c141e580b101e48503030050030103800058114000400c040b842000041c1441e1720784a41040e42442c0800f0b10584144500100c24844c04000381c029814290b543c0c541100c040d0b1034001894078561800e0381c4003400c000d0010358881d00b480007820f0305441010f04081160402c035020081e80743e9840a02055410441340a58401014001c1c1005410000300d0341320041c0710404040481600e444546109805050900b4210340d400300b4140100526880360814600d800c4072203040d1070411355189980c3c1d20403400d465042010390030100b8210349484000070060b0403410070564503408104644080d0350050f200f41c50004040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 14181283 1250 14180033 14180039
    0x90106110615031002160b0106050c1204060c0b060d14010501090b01030e0705041805010606020606010e180601140d06080d14040b07060b1804030207050a080c06040e1003080708070507 81
    0x70030034000303560316005005006206080b54004c0f0080d080391201d2601c60414141140009444010850207801c084e00c03540e480c3e1a081c030070300f4038040d401e0060b6024800300b00402c1c0a056041a140d104040d0310000005055880c20b0105201000351440141581250042101c00e18010b4214505960b9121010001148044011800e80e101609507030769581100d8005d104038100342c0c00a022481340028989810081940c0c0d6a08448a80d0300000c01031f04a2024405c3c0c0d503900801d071440013802100d42c001d4002182c0e60750201c0f550003030311003070500c1051701100d0410700c081010360705090808003040160b03664401d40d180d210350780418044000f81c103101292640507074007010782d82a0703110000300c1c1341419115582c80f0000d00044c080c260340400e2008020150070b8880244601c0b45110358040c1a4803407174039041c0318840d14550010060381c0c110006012207030b15004d0aa8040301c501000800d06030f102c400300307640c4807100c6400190949400285050501c450320000f0001240f00d001141c040c40c3d9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 14182533 1250 14181283 14181301
    0x1031202011416030212010602061902190e0406080a05030301182705070506070f11010203030c0a030f09020901080d08010b0703090608042d0c050603161d0901061106 73
    0x46420850101c0b42e071007002289425000c282c48043c105540d00700113240101c2c603440f141060400368042d4005078005420000c1d242c03582001c0200b84175103c503043d4142524a00c0f410b050360000f1a61200300100d010342c030075656407160807000003800540e05590b00740c141e5080842d16030340f00340a20404500740a0350700000911900c990038a07070410982050075403510722644120300710749840540703441c40744034000310743d9555030b100405107288075800c0244562014500b22494484c041d06841c155003040c03080006030150030041701c162822a150004039070f14045840801009002c40207500100e03000000b2500480c00228049801c6507034460540e280e136103120303c0782c0500c5078000013000109060020001240074120494000c2d206801c0401810b02c140103181102d0003d0b2132300c0c030040d030841041000340001c00c00360f003001e444141c074500e255140a000c05030600b0440c000080030040020947c411440302e64130369419208000380b94101e00e59498000400c0050383e081d41810601810021640d545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 14183783 1250 14182533 14182541
    0x204060203041d01030b06060a111e0d030c0e0609030a060903030e060a050403020304121401110d0b06040302062d070602040312020d020d1206050604030503040e0f0112020402090f040e01050103120201 88
    0x1d510600001c46d03075646006102c0c81c3e4021104400500685c80030050506106000f01d116100c0c4513803800400d0b00040a80914107500d4004500615150410a14410768800340b204242682680c40503522240131021910301644000082d241620349880032041561541018104030724417011035031181c0307c8140c0300c000c4034016100200543d100b000104040c41d050741050b40e03818003a81c52800c1e61221001071710300751a0b200c050094144400101d65000d40c6062042950742401074a5503420a420f41c1d01181e020312956422901491120280101d118140b40700b010a840460102c540c440b5500c1c6000000781d007081c08120f840c07150076002d8001c3d4500c001aa041140c01e650700624540300c41c142c0035120f1005c0f2074050010740f5120b05000c50b40b901c43d10002c000a41c841c800a550700c501d07201c2d01080080010f0540c1c598010a040100420740050b40c0b000c0c4469011a8016a615503a2000a10341d002c0b05403056005424144c00c83c0d500c52040d440389040301e0041c41d100e0041000218200d08031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 14185033 1250 14183783 14183789
    0x6090108030a0e01030204080f07091a0112020912070303120506090408090103091415041202060112030f1205010311030d0e0a030b09210a0201060902040f03020402030a0f0204060203041d01 83
    0x140c1d206024880c1d9552040401070001e0606060042c84d103901c0d10025410600b4420340070b20f10b0360005a00b00f0400a1034400c514903045c1403004c012400e1030b0b03040003c00104028061000140d0041844200c40d501d105045801c046044102d61100c2d980c0e180107003804451020404016151600042d00c034244480e10b6446254821070f0315180c01900001540207000c00790044d241c079444030b01c42d407454410811240c00410784d448100d282500d07151a01e80700c440f5800d8900c004540054004200041c0203c003805140c03607050800d511541c1119100b10340000d10394201b0000b041c00d000000040c00300c00d00105211038425002e0301c441010b04001541d140759641c218a40007e1986401c20104d0300d428012230b04441c50700141c0701c03c0c0c82807280c105e90b454500c1c003178500c80398400903582055980910130100100320280095050074030346061400360710010721000e03019640010000325004416445a84000702c183c0e0219140d07501c640f002540d0390000d004102e0880c504542c0c405a050307180c100e540c12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 14186283 1250 14185033 14185049
    0x150b0714011407171b0d1e15050d02060403150e01020301060306090b03060103080306040b040b04050703021207090f060f020109050708030a0f08090706050f0c030c010b0f0103050f070e0109030213060509060901 92
    0x340c030503012945c0410303910151108814540d01c6003e425442c5020f040043e81c5c000100700441c60071005403481c0003040f45a27210340c4c81500302050501c010303210f44082d41c044035000300020220507018400c00b401782c00500f81c0403560794030003c00031816580591044090301d140500801081c0c4c2001d043c966110310030b000190580009000040052070140c004440d5200080c00124107400240c1c0030501b9540d084e00d00b0300100c0d030045a20004800480c6445500911524007002090710340581c400b07018100d8095042002a50300011030514000d4110a01075644030f81122a1300c1d80d070b0004a078503500310100140c0000c001d4800441882c0c45801458001e03400c03540900f4609182040c2500c45501c00d03036500ca000300d42841500288501030014006048504001044071302d007940c00c011400c8148c080260506142105003c103d03a50100c250b0b40c004103e084c400c00816954005075101e00080e80300030f50026034a44002e04c0401e0b00e80041007210016542c03070030310b603c8000400c0600c55090285200c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 14187533 1250 14186283 14186311
    0x90904060b0102030409090804080c0a0b1207090b030415060b0702060f07030306180501090501090c02030a1805030307052a06071e02060313030f03150b071401140717 73
    0x404140907a01400c400e0310140122480c00390740d502c000080d1000190f040d0b4150501040401003001d09021040b00c2c06003c40d1505840d505000b040400c0b8001e02c0c42207490107201d040022a00f900544000d0050000513404c143c4a190600d481c0394a1141501c08011035401e280c800101c0711240419907002c00d5000f1701c0c83d4100090810a04600d8101c1b01c0c0079010161203200026520400c2c100c1c1852070559804003007139075810b01800100745d40040e400007101610704010740034003690110503524030078064030b80b05034410072a0a1103002900e85404c5940c2c14000018031030100080007845590480b4141e02c400c450000d0f04403000300d84420342e40e019800410401c100d00004015489003c201d03980c02907012241041c94001ca843c1d078008990b0700042e29082030484007450381050240c1c04c415031030301d802d108481803010b03850034051361442405031011002c00d20f071080000074a000e10f070101e80000200070203a03114201249201040e19100d0120340c864070058030360b19056160038030890400164031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 14188783 1250 14187533 14187541
    0x4050a0212010509120d06050604120515060f0409020a05060f07030908060402010804080309030d060b07061a0f010f0212070f0b0106080903160201021005100501030f02040e1305160609060f03020909 87
    0x20fa5404106c010502658822012406a587d00090300107007204c0b2280e81b1a5100c9440c1441ca00944802c40c540414040020040c081e81c580d41c0d0003c06580c00d40d0302260080703480c8046040d03540380d5006943d10800c045040514802c0c840b01826006009035981c02491303544150b02500c40c40c0946029000650101c006004540210025a0019071a2049038a421500c07600c100403582680c0080700d0a1100148200501803103010784120f034130403201c00595080249001500850000d42800e040c080c1590645103403a00034030003620060340c420b50140e650003907440e02c0000d81c1c040440480c1c10320312520011800f107100b041c145100d12010740c015483c03c0c07110382c08041c10040b40c0c04100d04503c1080088c00403010b4a000d840e000c0c81d07854840d02040c504010000d015214100c1d200f0f02c0391031060000304140703e0004115600180d0b905014121200e440c10041e0400c40e0b054034130806200d84a0b00001c4240d440a0000c00321356041e9101001018030032070440c282c3c0310340d281c41a44100700e50042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 14190033 1250 14188783 14188813
    0x100b04030512070507080f0d0e0402091e030c0d1a091203130807020613140102010902030703060c090305060c0301030213060e060f03010f0624020304080d0c0602090904050a0212010509 81
    0x5108044c05041211001d40e5a180e6491038248051542000703500003210901c455500441c0903d6110001c4500358240464075005c200c2004040c1c0424044218003440303c583e60b01c081c44010301c01c142c0076020301905c400074204649000382e903103000e045500c1c101c800a5064a00801c07040b045400c2002022b240d5201c40303c18202600e02960700b5222200c00b0449040140e0b55000180007120301c0071020b000d298070706410400c025200008060559040415110040c1e8011412800f80c07540075100180c41c190b070307190440740c4e94201d400050083c8900018001a51a4480958100c034800c82e400c6401d1072030b00c02e034003060b55024070405000e5501000414018034180b03040404110005e0000a90300701044000c0064071070581c0080003010101e4003110b400c1021203038801c1c3c120700500065140a00e00600b02d542d50788088000001c00c124100401d01b00101e40d01115001d0703a00078503020789802d06042041d124481d26400f2840b40d096011031a4031508103008040c0b00c1c19a030405840b060b528912a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 14191283 1250 14190033 14190037
    0xc171e07051903090506060105130b090f090f040203010614241303080310050d0c030807020d05060a06080616020d12060308121801060f0b09010e03150402010f03060e0103020f040b040501030b100b04030512 90
    0x8cd00e5200004800d41075140d11802041d921404050654080301d090070300605003100d025400903005180315541c40da9050300e03023540701102c4074078a40c0000e01592400c0802241070203000600ca8029946500000500c66480301030342c083c2c1003901e28000140c1d40c500c20000a14440c107001824102847c0b000c20224102001904090380060441041450141d80e02810140211181d4209a503903140510004a0400000754041c4d400c05203960021482c100c00396031034213103921803800c10040959049168005030800c00045600524060311820802c0310b48186480c01c903401c20482c2101c6004400030300050013100115010001c070b2859140c2000210034480d404551514103020303441c0d802d10159142000034400c1c180c140010780105080c984001480510a241c09d0070815060002c00d1100400c00c021041c1125070448040104500340b101241c081d0000c907509660080c60038000105001465070103610404d406240c69005039190300c018030440c052408064440e5104c00d1000b01c0c05092000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 14192533 1250 14191283 14191297
    0xa0b030a021324110601031424060f060a17101206020705120315010507030c06020307020a0204060b120c0f0910030c171e07051903090506060105130b 66
    0x102600e40b000071600d54440364030940c800e802c50782142c01c880680c0c0141c03031600c4190305203600d410401c058520f1411030356680103000c041c0480384103103c412071240040002c110b104030506a001070101080c0b28044072244100d440c0c074000e90040011480a162000841d25035002c2a01c03001103502d6804804540010700a20869403611010800710700b5940500601010074132a07100981d40343c04c24500182481c14112061039229014000c0c0585480c07841031050b0394820a10f0020b40b81d41490030304443c02c0c51a250041d00c01403001081c04400e6501007040315040f402580c0078006180d84480000940c0304641d00c1e00d040c1141c03103001c1014160301800a08071012903500d0981070408d0740e0700040c8648185120207000c01d40d01e4540405d6580c008a02da40c0e2048941140e041e0342c074080d10004014840301fa0000c0f8440b580000045100c2d00980640e003181400700c2c41c42c002074070b59035001340050030401d50a50344c610030040020540c2d84900304841542c810a0700b591801442c01280d11401e403c051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 14193783 1250 14192533 14192551
    0xb0a0507050c0a050a060c090b0a080403020a141b0108010b090f030304030203070e07090801090b0601050901030f061509080303071b0501140a1d06040809120a0f06060303021203060a0b03 82
    0x301c0b400c0e005400700801034801d40108080c00c000c3c8042d03c0c00c841200c04170015882800b0004000b00302c00b03450b807030985401300800e080c010740640e51407074200d081198900001308100b440040002ca80900000c2d803494a800c000c402c3c00303105111100544408070244a41c000c02c550030490040343d810013800701d01502c03d0107070403a8106610b80c1e00190a1600940160702d4139101d00c810880310700c2d484201c540050041c24020042040c0545030754400c1c10000b00309906000d000100c800d46a44654020490621b940c07070100b001d66101c04010b6003010003040a00c0000d10f5260012a00d136002104803070140103d61107900300c644100e4103030b55440b03204040541c0d041d5a205402d102c1c3d2010031100e6441b803c00010000768981010340742d840c0100a64040c0b00582d8882c00401c0001140c0c5411540003090880c2c1d035210ba045001c0b161840c08494800c01070001c0003a1400d00304200c1c02c1c1d0081410b40380700f602a00c0310228100e8002f0303098003080b1a003a034405d400c01e5082080e11010301c000c5401510794 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 14195033 1250 14193783 14193787
    0x1a090316150501140913030210020702130903080106020f0f06010302240c0619090c0603020f07020307090e01051303090e04060b0316050901060509010905060c070509070203070201030c0c0b0a050705 87
    0x200c08041120801da000c4c1c030f00841080352406503460049a40b40d401215920100920034094070007d564940c0241c1f100c0445500040c44419943e5101c0503245900c1401d02c01e100f810918a002442d0b4a8203100302c030702511444866010041c0c01165004040e1800303401011668070f1502001000c41c1940208041d00e0f841c0ca21010b451410390f130013801c416544000030109070600d41d0a0b0300407203503894403000e004c0e071030a00350a00140b104404e1b03200f200d22614002d40c0740c140710210001030780b190740c00080d410300c030342c420004850203da0040082034920710002c20540e5250b4103400019004c0d4140140002c100e0306040c016540030500c21034001d4051000000e43e441c2d2400400d2401c0d211100b45c010307080104c1020082e919007146011f014107a1803500908210307143c030002e468205c107401350a1007120049400c0d800b4180400c041402172030020401006070508247c003a40320792110340e042c0c0c000390500c0409040f40b80a558400d19059115070285565941c2c1c02600d4000c0c440508084d0030000c003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 14196283 1250 14195033 14195063
    0x306010c020d05010605030c041103070807030b030a060501030209060906090a0207030504030c06080612010b0d06020c01110a0503090105011202090402060702031204060f11010605061b030f0d05041a090316 90
    0x244a00022003d100340c000080250610703013094900200d88021a2041e41030240550107844c03c017096a41140701814951203640351003e05802400ba504003164141c410250200140951904400d041364002c0d10110000d4075401d050090340f9108481803a0448500004580035403c02d07030041801e5406443d141c0e0030540c80780d80d801084107003507002070300088107402440020302e44090341c24224036000d8020008019114042102000f0112025007011b0b400b14401800740002c0d0446d1070440300311425540d4491827403038050500c0d00250342800c040d628140020519011a0714a40080b0390014501031640d40c0b50741c2001480da00985040b41c1500800807140c4600030800041d20140110342c03208000800c0d0424005c0030a50007851415540c4e0510200700101c1e00d4803421201951068840401182905803e0910314400d4014445240307000280f4422034022503402031703014038440c01d8040c0c5000407007a080340c0000001d40b50040e960f08200b00d0494442400c0b1003281c2d00c20711420940744a032203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 14197533 1250 14196283 14196289
    0x11d030604030e010206090610180906060801020301061d010e060d021605030c010e070b1605120705011a01051305040c020f060a0606020d02030c030d1a1207030303200f0306010c02 79
    0xd020740d012404640d80b40030203110381d81c050101c10340c880708900040c401c0d460101002c0e0702c00040e6202e43c16110384a0500a40007581c0c5801104070503030040c0e400d00049507140f81310742c000e500034032507000001c00f00c003407401282480319007400d80b51005a403840e40c07082c4101c040190b1a4012501e01560b1907080024949240098400d80d00351800750002d5034543c10385040403400d58180600c40078490300440700078000684444199400c1e41034900c4207191b01a80307883c2440c07078065500c44c200d400300008541e540410105402c52150544801210421107101500640325801a5902e400d100c1c50001c0781400541004e0b03001001182c2688111954001210441c60a024080d220a1032084d111a01405565010003041c9007843c003500c0158038040288040725224040c91800300c510300e880e082c000041040100744a10420401481980c180c103c4211140c0d841c0d0340c600c0102c0c04242130a05111038444400320240c00860038840c814908620342c1c1141d500c036400240a11306102481402c400583c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 14198783 1250 14197533 14197543
    0x603060402160501050f100305030324180105040f02040b180307050a03060905060903120403050c120301080102070c0e010510030209041401031a06040207030527060f040e011703030402011d03 84
    0x600881c00002c4500380300014a595100091507c9403c000d01c46082000610003c03c0340d0b40009801c0c040301307046020352000d4900300c500a4074280c1c0000b44c400d0444c0130100600e0245c1c1210000c075020480c1c4000d240c0b03454144d0140307106210f0450f009115101c1443c002c00148041080000c0548464a442d080059004040c5800550b541c6554000740c00c10080200541c5030404c403204001c600b004085c1d00340e00310490006000904001010946401e01107080001d0880d003060801200d440c0c0d07868140040c002e4205c3c0105941d521000c03040010340c000381c8813045050300c40c09049040051810340c41603012b5409005065005591111000d48562500414078040c505c01c4e0720560348402a40d111a02062024000d40d120f2072040150700b0001e0341100031a40c0c400400c50f03030540c0d100800ca50410807102c20007800e0703410410002c0e2500d4400c407901c0080098801415100c0c540fa40c1b124a45007220300304415007140d640c01040420050f6000b4054102d1100d80c00142000413035401002c0781c281 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 14200033 1250 14198783 14198827
    0x70b0a030b0301060b0415050c03040807030f030201140606030a0c021207030306080f060622090b04060e010e03040302060d0b1f0804030e09040c17010e0610081203040c050603060402 80
    0x755101e024010390700c1c080c0100401041998906070402c0c2c100454040301a01c0c8401440c24071100098806014000b8000c1d58020300e2450140d918169030307030415011080c140e80048006500c2c01144000321840259040e003d07907000b416803800c1d03070744414104008000103640e840035840b07442c543c0381580c95144001c2c00b800d482a513010450394503040e8682c5c03500050b00c2c11109250400380400c08030b5102c1c014406d00c01480d10503003030b0107a01441d200c3e038001c001d0b81c9009071030711014808200c14420301da0002d51190380c07070300020480048907485041d1640160b010003540400100070720801d4041c640c0002d04100001010000c0c02ca10b200107a9005020364029000072810050400041c150029200c003941c0b0310a9480d06c19515042c2c0e5000785808460140c00744500048103d401ca8601c01d50141ea4640e96410442d070715400e184188d40841c010340d00c1a0503041c8a10142e00101c07401d80c1e01924061944500d41c580301e00d050004005c0716070001003016400039401e1000075848440c04d03c0c09100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 14201283 1250 14200033 14200037
    0x20109170405030f06010b07030e1314041202030a02030f03041a0703150501030605060a1d060412140d050d0e10020403060c110d09050105160507060233070c020102070b0a 75
    0xe00d52410b01494182211020740310010381080004001c015400c600310703005268546001840c2c9540b801c005009641c01c2d0307240b1074400b85408000241d0107588840c25010b940143c0301d0140800414200301e0786d038414800e514005070018031900084001180c06075410a00c00c44102e144a21110460413114800b10380c040e000070307291043c1c1903c030b0300d071b5028140180100b07203004e000316810080414114481c98240d041000364030b10384020f54100c1e108150301607030b07401850b441d135403580d5100c01101e0007040d00f170580f0400d800c12119003445200083c0b0f040d42e604a6190241800d8008031140010200f10f02d1040c2c40e070040c2c20190450704103901c0104040c620920001030030107089a002408509180c414111a500c070780051425280c10641c41c104460702403811958442542411028841480100400c1c5100c5d510010400c40c5c2c000c15034818003050784d000301d02e640c580c0c0362845d880b081803820002d04841e0100085940c1c00d00c80c1c20a20f500ca4018011180c2107961864031234459400110b0005c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 14202533 1250 14201283 14201287
    0x501140415060503010902010503180106150c050105010504050f010509070c0b040c14030a150b03010906020d0902011b020f011101021201030c060f0311030a02072105070b06060309100c02010917 85
    0x10269400e40300390b1000e088194002c0250200300c2d400a4035a1001034003010716084200e0745040c900c942500400041c050300348002c000700407100d00140440d41d10080c100c416509000c00880c1c54100361062a00c281380d072112442090b46407005104880d0005440201084140c020440102c4c4001c4015405540700d10103000f5414039159010100c014030340c4445209810126840c00403500258607c801c3c0450300c24001800340032000001e0040c09007110080200d8004500500e4400d02580a441214000e80700c1ea00e8109200c1c82007000d0940e11040203600169032040348005501c01c401200f9410b80e01000145020b1200411030185842680210f030260b44032002031048550003148900ad10f10281810710803048003800610b12400010510219154040b549409000c407104034128070008250485402c040c0b9904020050b40c44100c00340d6a5401c60404160181841804c40b480383c00060040c10a024005810802520903c551a42107648408000000c12800d1940465260079125015 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 14203783 1250 14202533 14202563
    0x5060f040605010501050307080a0b0d140d0207060219080a090519050a0510050301090b060702060a0305101d150f03030d0f0b01020610031203110a02030306010201060b0c100905011404 81
    0x3001e440d416080181000420300a01201c0389e0001d841035000845080c02040c0b444a44e4040b50201085210280c0701d14140c3c5000303400700b040410400e00c0001c6940c261403640340c440d034099075140340b28622041603142d40c4a4440106501c407001c1c000200803840c145030440c0c0d581c2c3c00104003040150720741c800c03c4501a0304014034076040c50300400412090b60304840045032030740d0183c42c501052188002d20b50300c400d14040c0c5661820102c81070680d00801682d141e1103001d030024001c01c021201085810b03100b601c003048034104480620b210000b02c1840310219514410302c12a0b16031003c1c065a00700c0c003040303040c1070240d4051010f0003041410900020f4421724510111090b10b80d0200030b94159004401809408100c00d40004152a0040c0c03604890116401c801c50007040e14103010300d2031610204401da201e6a004c0011070280a09034000d0001c641c40728070744003082c411750400744015484101701081c04440751704884400b6020314000a251059102c1c44030f1000c070302320340464864810040d66 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 14205033 1250 14203783 14203793
    0x30d020301090212060907050403080c03040e10170303061e01030e01020a02010b040506040203010e041e120903140f0729070309050111030909040b060d020424091b03090201050705060f04 82
    0x402e17071062007100c2c0040b40d03050034080a0003d07c280e0202401200e030004030071500d20400c00071500100b543c080ca1070035506d81074004100217442e030300400d03440d404402d55854814000000ba40d00610f001440300d0701c428071030008520655100d91240381496111039000c408031800384040c01d00c0405a40000c100e21000d0307000c210880308000d240703504c1903105000502600c00c10548590f48036500800e89103030780002c034154007140120004002c107003175003a034050200350b070303000e0395840440b885a03100d000c11001300d91610361103007145408852554828a4204144891070307515600980034126403d202c1682450107040d1580440ca0a8005c100b04d0001001256841500d81c898203540b28040e504006036140002d140042c05403000c3c00b041202400300e02e032565003122644545500400c1000407011000e50200ca2481e80e01496019101c421000942d0b240c8e580039a416200e052400740120029480040d40244080c1e0000d074100401804240c00040040020902514846a07041d071989841e281c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 14206283 1250 14205033 14205067
    0x20c0d0303020309010623120a0b0103050102040501080f04030e0405060a050607080405030601171009030509030d0c03030b0109030c03020910170303010807050d05030a0e040e030d0b09010906080d0f02030d0203010902 95
    0x120f0070310141c801107021f0180f8000c1e940e0081c04003121a4214039010030381c901c0c0340c0144030401400642c40c131030000042010543c01403080f40c100b85c9520959603108441c002a8101c00c80740a00401c02042460041c2c1c81d0035030040c0e03404000100301600d4681c46802240ea15041102c0440d0702c214000703014422450204506030060100040d10300002c2c550501c5a03032038410107807661304101c0d03d0f0f549500c101400f6a0541c1d4003030002504803211008281d10040419046200650220340343c442d00e00d070b19500c581c0c1d004098039000101c88210750319503424007510040082001606514408000c104507094079110541c0340b021000441d229410520300505107015544958814206244803100040380031055800c14046410720548a002d03030b00c041170241c000b5440c00070b094000060b12070150700250b0301551810b0000e59003604d01daa00c500710030003110054004c050ba0740d84005454107032144288078201c109102c91042c2c1e410000d62402030016608280c02c40704c501900400c2c526640b14503410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 14207533 1250 14206283 14206289
    0x6050303030601020a08130306021c050c0c0307030e0607020d03020f060a051005011d030111070b0109050606040b0706060503070f1d0c031f0302090f090d05180103020703020c0d03030203090106 85
    0x2010318a94103200b00040d6642c1d41c01c560040046d00046207040c42c0200042c0203900658200c68150b581c1d08000050a00035003025001c0c41c442450500852140100d14080d10305005104000703611307040e915141035890681c200c08099003c60100b2101d001030b10f8000d442c44805d8420707001004114000c080c01800e0000c014040040076140400b0001c2a42101c688001294000e0070810342900c0c00001664200081841007500b42d800c00e2000502580780360300412034940905807100440e601e85000e0026540160f4010f64070800a020511071b000c4d8030740040805510031240000c007150b403031010a0901c200c5900c801e81d0011070020070005807100750150b412510b0907103031282007840c080881040c0d9010150203440c1c154981030340d030b1f04010700c2708150380d02031f41d00100344040078a000c1c1001654141c0480341810a401f41d0303602c00810742d009500b50303008040284014400c0781e0080004400940144506a04602c00d107845444039031521300310380441078001e543c0036a80e803170040c0500b425115994 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 14208639 1106 14207533 14207539
    0x4050c07020405180c0d0203070b0a050403060504051e0328110708031306090b0304020405041a0a05040302070f0501080604091a070203040302010e010c0209130c09140a0605 76
    0x7080c8901031303e596001c48401c42c0414080c0070186402060094040e44003000901c5100c02c82405885207003224a08a42000c2c0d40340ca509041d40c40950301911141c00281810280340740404210b1802e944020085203400c6a420704d038000b4038401e0b0304440740404100c1100000600c905405c0d448811280e0031908115100c00c84140c507580003600320448856030600008045000e148850304441650b07040c9405c40e40d0b281c003800090400104220f4000030501003182c102400718104038040d00040100140a290901e4040e02e80320032a042084120140202001103aa01103c03032944150141d80209842101d4a0801c2c003014803100780d003e5100c240420013690703e40c0040a44101c074000d0765049080100031300107490044881c180690005110303000520055010001240100d2007052106e0500e6603982c013003001c03620340792400e0280308503030014001500110f01810300074080807 = true := by decide +kernel

theorem cover : BRFrame.Cov 14028783 14208639 := by
  have h0 := BRFrame.cov_init 14028783
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14028783 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 14028783 ≤ n) (h2 : n < 14208639) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
