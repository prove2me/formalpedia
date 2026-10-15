-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4168
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:58.253386+00:00
-- url     : https://prove2.me/submissions/2d2106b0-34ca-485a-9618-315ace877415

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 749460431 ≤ n < 749640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 749461681 1250 749460431 749460463
    0x1401080c0f040f060908031806030403020a02030610060e0301060f06081e1503102d06080a0b0f150310050414070b0d0f0203100e04031202070c09060801052412 70
    0x11810a0401041660681c010040940c4200300034012070189991403d003044042750b02c0740e42e82d901c3d0300e07041b4180802d071400250544504801c0c00800031403400c8450603915103554003003402202d5070405090b126144100d007440316200d10140203003442107a071a40d1128440d11146203000b4296105250104100c4400c00b600071032040400140c03030240074440084c0790880081c0720051484441868000d80ca1300d080c2004400c4c0b49100150709155041030b0001c11f0808160b425a00c114142000b01c07000841c0d1440d0161448000074045102d442c4001111010290042c105002d07038502140003030001030401e50f802000d0301400110200300b0840c840142c41e003000d41d26180c3d6901c80d41d0405450408103612010307801402000842a4584a10f800301c0701d0380b0850140d6501c40741070586460202408e5458a9070001a04200784a40c012909048641140041086d01d981d22081b07400c8139400e60310384141000c41e044160340d941500c60300700c01c0d289004241030481425001d4103454800e14000170f5203c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 749462931 1250 749461681 749461709
    0x103020d170d0902091f0b0a1106100501141603142701030c03270303060515070b0f04030c02130e0f010b090112030915020a08070605041b1401080c0f04 67
    0x110700702141913581104001011081464001c00c004600800c640075902c0c3c0703240b010800408c500d104140ca29003a080201c2614a14103203040c80700c0039501d4038090706000c14020364508074401e14610031580d48100400c50840000341ea9030b42207454151540c180710307003004140203001c0d0300786a0079100c04205100c1040d25100301510b00c00581a140183c1401d000c1c1842d114000c070b0000e50000d00f819600d00c9094100610812070314082d0300410003504a190040362a400b80015030943e500101285c40c021400082c5036074a08031240c0c0800b1342214000d00003001c490300000103042c03400144610b40340c1a880410311112103200c491519034110076000042c2c1d10b03030410b20340342d0070311901440c09400000714048880c0c0300c40c1c8018111520f28811804058203203038003c000207100744042580c507644040c0302e91b603510301400c000029120540302035400004030340c0108903200c41038aa80c003c5130008c020480201c2e05c443e0056400303100040001d4102501001690b140d0000c10000340080e0100d5100046 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 749464181 1250 749462931 749462933
    0xf030a060b090f0f040f06030506041a01051507032a061a090c3702160312120f05010b070b070f05090d0206090a170d0203120103020d170d09 62
    0x9541107503001d500780c00000c106030601d9445402681c0b107012400d90f03d0342d0b81c0c10302044c00314005040b504040220036182100c040100500030074014083da0180c807007111044952158540c17010001c1c441e17681c1c48240310300303076a000789444001303041114001c1c1000c0c507001c1020400e1202c0e80380ea038082c0d10640e03850301104100304031051290241541000c02040c00d10b60f110001f080f8903000190541c0c08400700030031074201d80c216a4406151107001100e0b515406840c180010441941b1908400e0240c002d011450300600761000d42c44048a404c08051042422030880640d140c0c0c030704a0b000c0e07500759203c0c110300c108803407507001d92402460b01c2c84826039540300a080035805d07100060005010040c909a00b11041d07a400010786460003002c40c0c000c60421010300c005540d84c0b044030a5641c01c80b10310840018070001124000c0c2404042c40e003a00e8801d8502d00c0200c0e203c1c4981000d80701c03400030340001440542414401c00420b10b2091008440000c0c0e00f200c0100da603080480341e110016140c010401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 749465431 1250 749464181 749464201
    0x607030203090f061b03090708010e01020306130c080f0903041a04051f0504030803100302180906010807030c03080a03020c16210209071d180f0f040c061805060f03 72
    0x102c8000c12034400b400b100c0c1805e154580c0e1204400d10814126040030000c68000312041c00890001c1ca8004002c2100b00031070201c05000c2e401c110b542c41d1041e4008466080c0684c824060000c0a0585e40e8035140e150741d074080b45c2c4810100c05041102c161000b4040810404211080d141d410021044031640b40c5280201308200f01420a8561f1072050b5120145400e058000c4c05031400e59034041d80c520344030750301c0d410392000968a60384065800510502c1c04e074034002000074158003035800402510042d80c0c03100d4075166141c1481c44014001c01854400304040380e03a440103840f0300c0f42d8030f103400341c6012031301c3e50480d190080761983c3c0321202c2130340c5501f04101003000c80b0400c1c91007441c58400412070503507000210038000c0104035600344201050404d40404105000b0145c1c1c000050540e80c0644580000b030781050b600301c0ea4001140040ca0100d600000c09800d040d1003198010007000ca403c1c101002103038500c3c0c0c89915491380300320340c400100d065601d0b00013901c00c68038807840054030303440c10550f55 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 749466681 1250 749465431 749465443
    0x111040503032b050711010b010207080309010507111f020105060a1d04111c0213051312090b18030c0409020a05060f041208190503240111060703020309 67
    0x5445110104810040398402005440e500c0d00866000181030b0b40500600340703c4420f000d5980c0f6010314090411060540003000540340315140c0c002003012218a1005aa0b10411402403480070391040c4039844180d8030502c01004400d1107030f041210b48542240124403021800c031800c0c05548181682a54540d60901c1401c0e0b0141003100c00c80b801d580340800042d50002c8180d6038080b07801d0003500041c248600e0600d40c0d0701281c0054400300680f842c000c1201090040000d00303d210380c0e5483e8010104842d28069280604003040300c44034082190390300c00c0194040050041c2c24007480840028919900308040d003890150408a0001c000c100f204140c202451405114480c0d031819003c08090f031106036680c000c2c2d0b0313420b03100a81c0d00c48050000c2c0d189070141da4403d4038a0003c50200004010702c0c00301030002c00c00100c8174101000f1084509880a0004903001000040303030b008020103a2000811008000d403041c140003030039a0340400e010b03040c408101e40c2d62020075000000d02116070000c00807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 749467931 1250 749466681 749466701
    0xf1f0e1e070807050406030c051b100608010603021809151f06170f060607140f19050d03020d020d05040f0b131e03110709140105060711010c0305041e030501 69
    0x1501852500f0600500f417400356000351000c0650b039205c1c407801309000e07000b140d6a2091140001d10003103401c410f200d40d203039442c000002109040400c0044e04110501442c010341c2d6004000c01c102d9180000031600782c10303004000320f51510480300c0c8420008400900c00c6e004150301203202d061920000081800040d09600580c03c1141c0c200c5813100504c16040ca0a0b00101c003001e2494540e00d070340c4c00007102405003840c040c003000c4c184c1e96041804500080d1080100b085041610000c410050410405031002d0101600d0360b000f20240d9400c50b03100340d0040044030503800005040400024480044440c120f800301d07021030100762400240007000405951213070040310880c0d0038480d40c2d51041210102850f042d40301520000e542c504040c000c0c4401404820480c00b19521b2075690508580903104510000c00c10010103800440c15040c070a04a80425802c900352400c1c0e034500e540115005910f5803000d4040180c18440401d201c3d0001600c58a0441768807034008080342541096030031a401a54 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 749469181 1250 749467931 749467937
    0x1612080108150603010e0d0908070b090a090e07030602070503280c17120f0a110412030c0c051c05011107050a080a09260c090f1f0e1e07 60
    0x4010300701c1c001030140b621485080d040c41d0103440c2d03100401d000d080c02800c002424004c0786210780c125940260b1601c00c03954a01f04640c0102e40c0da1110034030920944040e560413200f11841844882c0450304005002c1701d441e03048450850743c81d1150000c030381220904030384503000000c03c10384606a06821a00800361540041d1402d041040054150b00310700c103006110318131403070255514551580076102da0031603c6501c43e4940c0340202c007901a144c01164290846881d021850f03042040142c241d40c152109941c030300c00c01d05070b47d4406030b40c81501c0364012143d030001c0b000040f80c40d4035501c940c20160750120324181c405580d1841c000d800e40c0d040c0701019013504820310006001c04c0340020000c03100c5400c00e07403580d0354400b243e00450324018643c10200d08003813a5820310602070b0703501010303103000c000e0b00c025100e81050f0801001800d52041d20310701d1130210500d020406d4079851003483c60503202810100080c0c590b030350307285900380c0000b107600300441c0a41c56500680c2d1505070842035801070300c030700e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 749470431 1250 749469181 749469197
    0xf0b09070215160302070b090d090e0c0711060702120f010f0213060302090d060903020a0209060108240103020403050a0c030b01080a0f1101050c15061f0c021e061612 73
    0xd0742499240000900c24041e008450000403c0c0d80d01a90440e038203035420039030303c40203860030100e81d0396503031184401c03400051441c2130005581d00f14220818080c80584041c64509141611201c0200b00480740d0658000b0342000550016030301c17500480301001404024281c00b141c101000c6007107401040e21000c80c01e0041298501c001e5044491f001606e005080050f140c20440c00032414503c13004d0320080941c1d187c2404c41d41410f80005a55005620031511515141e96000045803821412b4403c05211051411801480500c4c40c49070310b203944040c54014282580c4e900c44900d4403040702c0c425038210480a070140103000000e45100d025006500050052012a503a052400002c41c41c010707295100320101291203a110b10202c50110b000801141c01c008191603002c2280e14003079030a02c1c407804540c81c42c0620518441001c8003c500750b0307207a4239803d100300c2e020302428260101600745d00c555660500d0000381d981e08090100902c03140788a80b080300b181e10f1b0803502c8410700c3d42c12505200e1a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 749471681 1250 749470431 749470453
    0xb011b0f0b09072103020a0c03060e06070e010804060903021f020909090102040510120f02070302010e0d0201180b0a0222030606050301060e0c160b0106020c01080105091512030405040f0b090702 85
    0x212000001007135a1001e6030000780c01c541000c9041c0500840010203001121030008240701203600045d120000600036520a0313100c102e416220480d00444041c0414001800900440d2450340807400b954041d0040c0c1d00114041590500003001c6c1041560b0400d40c04100c4078810704003080960b9005112070006c614260804c0f0001e024100031a461404120a444850040c1215500301da00e0240e01c014040d900d40c0800e00d00a8080d00300c41507001018407803480d00c9100d03507205024040f885507400503003011a454917240e84000080060084814903001c100c030303481c28020880307e14692031032450340f0000ea504501c2c02009580c00c540c0014030a80c1018000d03c42d55030a8025143c00c030040700e0b045a920807131080c100d07085941850300a00070041d10000045c3d0a03401103007440d44481c09070386200c19680c0380c00070446810b030151800081901c4448512031903091039034072100d4003414a000c49040540e280000703401c2c1e503810f2541800c025100e41340c683c440d007002c208440c0c2050351030000d0700000c590 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 749472931 1250 749471681 749471699
    0x316030e0304080319230408010b0109050915120607080915010605042114030310091b03020c030c070807060f0f0e010315030803150924040b011b0f0b0907 68
    0x46013981071500c040000ca0611190090740e006403a4540c10f503880524541c4011452980d030445c8c03140d052954248120589035602c100040c1c1d0036030b54010036142d10341d26a51003140502c0c9a840030325800010744242c283e0240000c000480c03250300c0540c1c4802c40d40c5840c0c20024105800400009821407848005000d41908542610262035400c038000c03200f425244420f000008200c82c026003819070745041e0010420b40403005610900b2000c503000b80d0a03545100300300440b010300290b040c40c00004c2036140011807290300201a507909500459080402c41d101440c208516507100c1c01c481c0d0300c403400802000d42c000140340d040d24640c5c01c3c8050680c00d0010040d20040704001d60720704150b0364002c0400c811035000c0e40c1034095a040b800c0e80d074072440d101d104407a4262021800d1031040d96140c0000d1413a014254900042d5500c44819200e885014002e000240400003101d0f03041c000d5400c41284a0381d00c01c9405600035004040301020b498582c03d000c000c107200640b401c1402d812014061100c0c0711 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 749474181 1250 749472931 749472937
    0x5060103051522020a09021c060f0605040b090a030221100212070c02030127200307061107030b270d020304062d0c060f020a1407020102010e01020316030e03040803 72
    0xb03041643d03403d0f5141480010010700554025207201840420700f85008501c011080c0105000520100f08044c0c40f054a8001100c00b482241c000850030841480300400340c002800d144500601940c0c4076a0f140da00040c2c812041700900841c1841c01c40303010100740d504000c480040c09488408500c0c01110110043d4001c0005120b0010b10031880d0640c0300f10744007540110b8800d600c80a8800f40c0000b910400c0b12596065007050b10040d070705c541a005c00303441180b2101a4800000e0041003941c0c5000015210786007030720038080c024041c1030300c00000300790800f00b072512850714258400358010302c0000108584c40b203c190a481580407101030b012440d000021501130701c0da00d046c20141042c0e0301b9803001d100b1001194000c58403004c00780e00f80b00103401400110140d4890f0340c09109006d030104940c0124040c480208000505140400e6980040503000340881c50042c400420181c1a8202072402c0e80c1c402d0350204802143c2aa140d80043e605216040109181a01071494a440d0a804542c0c80c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 749475431 1250 749474181 749474221
    0x20d1b020d060e0f0106060903150606090608100e102301050406030b032506120c02070513150303051b070305030d4208010e0d03020a030902090103050601030515 71
    0x250b0f580c441e0641161003040202c00c41ca03041c4000340720407030310f942c00100f032201680303c201c0f050b103218032440601c08800c1c000c0100366052950350a501d64030b460403c6500490144c44e190601e0703035028001c20500e10a01c6ca0501c12500420b00a1040340703414003200c00b58581e45020404001c401000d000e0716a0f110701114201d40700751502003501d90219001034103114400903600c04003070b150869943d44070107140e407039030031106991a0b004100310154010025100007040040060300414003e012514001000e14031b520a5041d0000b000c000310a521084a9165041540450707008140080074582200d0354041c04002c01c005404d41914640c0d4255480c01040c0005002585030286108201d0503c3c02d5140421301d9040c540d1100015034981c00d16586100303034680c00d0058044000305940e101401403410444001c0c0081184601c000c0c4110025001081e011040545900c0c055026075140110140a10700640243c14036501d10318145242c824411860030541c41400c0070841034402d5449010824 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 749476681 1250 749475431 749475443
    0x3051308010b0a090c12230a05010302010225060f11060f04060e0a2018130b0a09110427030e100c080f03150904050609060c0915090a030f03020d1b020d 67
    0x2c7c81820300d039180b500054030607803000e6100c81804c000760907009400c030b03a04981c000e800741c4100d9004c41544065202844480d8119442005010404c540c459034400f61041c00e141391641200c4240c514003401c20070284d4100440110810610081c000740e84582514145041d000700040c42c060380e00c1c00420f075500d80752001c2e0805000800109500c0b203d02ca08071014030032056801c10b1812144103081c07811440d0301504c500b2150360000b0441c540031321960414036000569152448000300030480a004000d101c88101c9210241140d6404c441c0c40340b002c48580f0030b407100e502403242882440014114142510108000039800c8030200e61380c5022107070140f0100014980d00c3e80c4002d00c0054004d801d03001503820000f05001c0005114020070b83ea4020b4102000755240c94580210000340350060381103841e4095003c0190114046402c401080c4c50100540440905a500d4460040307281e00d2110550140c1c205150f01a122907000c0c2c55a200555409014107044506401060207030f00d4803d001044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 749477931 1250 749476681 749476691
    0xa110c01031a09090c03060f0403080906010320030c041104061e0905060f0408060703050a0b10270312020105011d010b070209130b01030c090e0c0d0f03051308010b0a090c12 76
    0xc0130380c05101c0a01050000780451b045410544000100d001040f1000c1e0006501d01011456240300440c05d1412a0340003034050302d5090300b10a80400c100396400002c3d5042c451240c20140340d0311540181800001c0124190b5141d526080028204e81d42041a4a2200c084903040020a5030050921000d581041d12001d80f0f8044103501101c140c4160341201c1107038800d0340104074032107034140c005521170741807104144090000c04c8140642034480194080201e4180c01202c0a44c1034405c090100605400000c16545941d0b40c83e00030303107042040441d03c0180d44a60061040300400740108211a61951003030030740390300d0251450309901401000a10500b20540410310045400c0107070701c001a0803580d04822565030345042c50501d0b80512508030700341d081c00207001d998103000c00c029092003c040c00b80c0403101c2e41c40d80e9142140c03010200480c2070003018018941c0000400319504098501034000042c101d07059420060313100da49a000c2c865503400c0140700348403298009940e03443d4825804012078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 749479181 1250 749477931 749477941
    0xa0806150301142206020f0405010306050d030903020108130b16090501081608040606080f2a0618010c0b0c030601090e1e100b0a02150604091a1504020a110c01031a09 73
    0x1a107480413000d000140040b0f030366001644000e0040c0f04880c000d0703c2c20041d40d95075806008000c2942a0058003007030b0400010000f40d4010801d956010000881400e01b4545682d204c100990b41600e0082401ca41e4082c15084150045c081c0005018242007245591401c5151001200402400d02d810400200003007010011729420003030140c0041d034191040340010b0041103681e0200e481c0303084130b206a00200c041410350803030f6462040384c00140140d4501103080c08101420307403450621a0400411043e03072408504800b0500f0b006d1b0300031083d09941c904007140010000c242c907401c40f0b5420040751040c05503981c07107041c44038200c0c5107165100d07200d551004441c40e0a54120381c04244060000100340030000d6001c603030042d11140f8048445040c4e01c82c1c030b081c0811192458001403445640d0706403554982078800301c0d40d07032000303070000fa6925032444000441c0a980100100350040b849c6083d0b9461a4030007800380e03009075071080c80c08000b441b0791240c0012090201182c43c6c1e018510820201d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 749480431 1250 749479181 749479231
    0x30f020a030209072309031905070801050c0c01060801020313020d1704170f0325060b040f02090108060f0603061504080715020708010c08060402180a080615030114 72
    0x50055400502c40783c4146000d0750050100d20800305401c9503800102040e03040d420010080d07401a80000c2c006210312618020a001d40e009030b0b9605031040e201e5004c0010f014a001d00491f0b1040c192040800c0d110090100400c0c01c0d92030300c1c0c21042c056401842045150092210b0b80e1110070f4040300c483c0742c06c50042c20074604004c1d4040f4040c0c0400b07800200855840c4403611170004036103003038003240c80714500b40038441c2d2240143c400105c83d180125941d401c06003998500040440d004034000900246130400040c1194003011140c042c054005c50007001660b0000c850543c895812b0380d84081280b80301c40040c0c241e110041000388079858060000020081d904140c80117080000101c4060319194500181c4441444054400600c1941f1006c21034113018001e030443c81c012500c0c5c0b05130700c0d16010101b0000e50091028061000d00004000c2010707565010300c900201194000782c4918140107042a00400100c80201d00030382c14921000580e800702c12503d6886040a8a00c100c0104043e00300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 749481681 1250 749480431 749480449
    0x30f02010c170c0c010632031504080c0714010f0203120a180203030d05060f010504030b04170c0316030f0306050a090902030f0a120801090504050c040c02030c030403030309020901090204050a030f02 87
    0x207013690300e40320b070108048050807110b00a002415002820515800d020000c130308132045442a010713003000d201200e108000c22032080d00144504000c50170020a00601403a0090907845951652081e104110790780d604001d011880900070700c0510b01c0d00075025100c281c01030024069042403592a40003e20300c01800182d1640d40794018141c0f40e0302c0240140b101c0c0070700015603156218041d0410406aa580038004450449910175800b4126581e20384480c00c80000400404210800c108415440724100340018005211600680b041c00340503405e005006038558032540f028107141100074012a95192866411103038144000b045907101480443e051404122144116124585aaa003085600d10040800104550b107441d442d80c4d80309400400e40c0c000350740150207078103c00c2e00d490003401e050700084404862401240c1c641005445402e1540c2d01640c41540000c0d038400481085145c0401a2401000e17040c005604041c03e180004501039001d200003003420802c030320003000715224260f81c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 749482931 1250 749481681 749481697
    0x90501120215193c0503040c1a070312020f041403010f02210601142d0a0207091812081005030304060504050415030302120904110a0c030f02010c170c 66
    0x10f0aa90005500507100782e1041500586039400400030403007a540b010826806440340a401420514800c10243e800b5440076205076a407110035000810f4038201030809002004071034003d2680c0f2803050070014a001d480d0b102c5100c407540104900d03a0302440110580b408e0b10f00100e13180300500340c40ba00081c0100800c807000007076a80041031808101807020030105030102111940c10495461400461b4030f000321007882d078207002040c480540a003501d14103043c00781c00040803407041d080451080200179080081d444006a20080040c80082000d015900461007d000b00a6121040b44c0c1c0c0e100c40e0b0240341d500c4e50104080a4001003503094002c40850007820064241d907612502c0300c00007816a4014020640940e082112070314041c0c111803100b03012280c1550180c54180c14a0304065255130100b03400550050322040c403524162030800050002032b00303d07107441018a5140c074004d131000440d02060029a45414500b4030b0254204050b01a580c0c00c500d103c0120307a9070342120110078025101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 749484181 1250 749482931 749482957
    0x80616030b090c0c0f01140411040216051c020307170f0f0f090406120c0e0a1e1b05130b09060c030315090c070c090e030c16060306090501120215 64
    0xb0500154281000043c50350100e81e40070f5036281008500054262403454800102d03044150002501041140da40700555450041001d8605103004185001d04519920241d8081d00301c40000441c0344283d400080303036420103002850519119481d000c807401c0d01035050359030b1800005104059880070310200c4100b100f4040c006515140400f200f00b02070340000b0078140c00340d45451001f040b0340c40c800402c0d50750b865002580e00f690343c1c101004071507200c4e00500300003000b0b074403800341314071483c46040d42c0360540341091000030f42000c0d00c901c41400002600f0821041c84020801910104a000310781c0040d03c00c00e010300ca9880303041d800070070018810b094881c055408040184489051509800300b0410011a404801511400c024890364442c60000030900031241c1d00410100405400810018064000b0350303081c0402600101c0c2001411b807041e4003440d4089900740541505441084050080440d0030409581010070003013840445d100d020b0300c550904446c003030300380480000700c0d8021040c044c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 749485431 1250 749484181 749484199
    0x309030c03030807020c0f032517010b130e0303070f051209030a030c0e0618041d060106031b0903020d050a1b0303020c03030306060304030819050708180601080616030b 74
    0x109009009030700503901040180103840340d00c0c6e05481e00c03040280c54488001d002d0071000072044000c03a5003285400c40000b0104103107800003062207442011842001c9007000100d419682c40003000f07071001c20000740700030840c138080c03030081c0e04580003068a52005141c10000c00c214018542a0b03028040c1404e008030061040c001c105030340c0804400b400c240401c94400340500309080c601602e01040c103040d4141c120005121707400741068038110078509406c000e0000501c03103000200301d42d1461a00350081f011170380200c0040100c2a450310508402141240e803401c0840001d2500400c2c0340624400a842250030210358014000c0030b21141c1d601d9503200301948820f928480c034074140010345200690141c014811180030030f090200c1180d200d00313401887d80e0f25540d1207540907901a5406000d0304c0048402050010321041140f003804d02032043c607103402e1100d2812481240009132092104c0d00310750007210040000b85400516990400b00c89542c1d684010300c51701e4224000d0100000f0740381e00404034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 749486681 1250 749485431 749485433
    0xb030705041a0f1c0b0901080d3c0f11060c070822080712080405091312030b0a080a0210120e0601180c0f020304150302040801140f1003080906070309030c03 69
    0x4001000e841d400c0d2800113011760f9045004200d680c0c0300901c58000320350001401c2c015054443c0c19425003066050b01071202c80c1650f05145c80546009003805013204102050410300703103420001d00404404c492400c80130451029288980f42c2c00c018000c0786020001180413400c000e8260140c1d81c60141070400700c502040f03002150444e0b101c0340c2c411600140110032021540c050800b5070340c0842030f0854101d610389450f100911507015401050041405a04c400318000556144002141c404c2d40f907801007220f90000c810003c0300142540034103e203901c045502001611440401c4482c02402d091645420050f250b444020b064445c80781600b50048000204098200e15902d4040031200c082c03c00080d82c20f44001d65600360724030064070140c1c0c424841088910100740e00c200320010140b81c05402d01e1b0340d03040f0090079950320301492040808110b041180c4604202c00e420b61000c500380054602030b24544403074400344a40c0d5541c03800782400080c0042894016481c010003594008511920b01e179132 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 749487931 1250 749486681 749486707
    0xc061104030f062909062b050f0106060f080a1a030708060a0f0527010603120c050f06060f01050c0316050a120f091716090204030201090b030705041a0f 67
    0x18684e4805100000f2a00d00d44004840582c514a840c0043d0030b905030703a00d0709030401c4038080740542004480d01c400e42a420781c1d03464a10343d24081d00c3c401d01c02030106c2941840300c1803d40303900d60844c80810880c03001801449a100741450f41003802c5560000346100c4844807002041d146101580c4c051040d000e0001b110040011000d10800c1c0d1610100070030755000d207034007042c1c50040c0c40c0c0440350741c199180c032120000745580710078601e18160000100c1e00d60720fa4455008590103086c0c0008160006812814400c080c42801541e04030100507040500e030071000500240031740160300b410441c1c0440c0750b500c0010100304039013008030b10101c807602c3c080892810740d42d600d10f2003c04541c11520640d1401143c0d01654540d09400c0b40b41d00d401103c5800c0c08a034403076140d41e070510740e4401d01c2034554280c0340c0d00001c9811000360581d04405a52903045000151500c0b00c50b50101d03990b00401c00030040030580c820f0690b82a1088030f8000080f4884904000a8900071161164900000001d0408030714417 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 749489181 1250 749487931 749487941
    0x60503131205090301050a1505091f06081807030c120f05030c06100b0a0210020a0318030839160b0a0902090603010b010c110102070e1603050f070c061104030f06 71
    0x40c200d009103c247d50b242c200c5001d85042c1e002046440801350350910107464105402c41c0d20004429401050003000d551442940b034003540920081010a0f06001c413135030141160311072030b01d040700c010201b1920b140c5e14000854094481c0c8222149036a01d01801c00283d406000750040e0000c04a986030a04031000503110340f019100145c040000c17503000101200d0400c25107800860382e40240036007496145401c0042c0d40085950420555180c5c51741512807417000140759114007959499015103004403c1d60700c4e0041e0458800d00000c0e0050b00e200e400c007140c286a10f12080b50034489500c5441e6402000607056200500a0440d905102085802d840d9644107091960007280c08075604c0d00c0f00c01c141401c0321440881540020040c0903da00030480700302c0803003625035042c81140c1400e903603400900c802040c117a8803d02d614001e08541c1801c4c0d54540681500141808861440350600d0788001c0e0912401c4000200070b6902c444c5503040b131032501c03000d0707c0c000d5402c03a6103117104498a14141e40108 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 749490431 1250 749489181 749489197
    0x7020c13020c190b2a16030216210c0e0f0a0b09060f01140405040c0c150c09090f021902010e06101a090a0305030720060a0504060503131205 62
    0x8881c800080c40e1052080b40c1c1c6150094010483e0301481d19614026141d0040d1204040d003010384070140c15450106190007044a0380384d91b51800310607515454024240809503055900d004c9182c8801c4c41918120f1a814000103c10900b2964810b19854001c01024555128041e107500400420000c0c0c16583c07070192003103512a404104440082c0c04222110405541c65034002400c0c0c3c0001003a54080c006084408fc07010030707864101a0340d81d00040070395040f4011000024001806882000f8003140a0443c60301c6e21130050140180407a0001c15480c0320340300b104102d60300e030b01c1c0c81803011100358106c84003410400400800c1800d1940040e0203001003404441551168400045405a40880d00010b40e050b040740306610400801000240342c005100007503101d1030900c0000700142c0f0070401003c030140b003001031905100f1598425550b000c204000580a01030030003d8804156004044a094681c0b9040c1986c0b246c0300e40c005000c40c15007500000380304041e15442054015040306c040c101c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 749491681 1250 749490431 749490433
    0x11a0a0c052d0706020d08190f110901080c0f071e0b041a0f012102060f070318060804030503070309050a0b040b0a0b0f10390b0f0402030a030807020c13020c 69
    0x1544e50381d0040ba0b5400c0d1324511030700090041408201c0724032a5a0340000b8000e1014030101e820382c0c50740e0f080c0701260b602c003aa00420b0000044e1011407941c20081166201c541001c03242d08120442c03140000e0744c403c0080040040412650040c100c207004112440010380260720400c0c14030301840d000025000308490800c880f002c1000050b4020100b0304000d041e641e10790120341284d1503140c0404051608000c0890b40070300d040c416800ca59021b840a007214900035901c0c0700102022100c10240c84125410400801c20300b4010080441d402c04100c9800c040d991900082c2e61503182003035030524600034030040c12410710100340810700800c614401d02072184000c00308240b0060b40208500300c006c192129802071114400d0320308183c0100d10000c58214403140321101c043c02032200741c1400d1610907005058810040b001c4050001c901c04a5500c903191103205840c60030203800281d5103e60300035004040200d0840003607c2c2600c03e101500800801828807a11000511500806174000388800511 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 749492931 1250 749491681 749491693
    0x11e080106181b0c080306010903050f010605040c0503070f0507020409060f0506040b0a1a0318030408030705010f0c080a0c090503030f0403120507020105030f063105011a0a0c052d 79
    0xc0c2142c079410443c4940803d840700041c0000d00d58034142c1503040101458144a0308000000100c1c000748031007402c401040300001415030900c402c11044071745001001c0c0802500b40100303c00d4680080d89001c200c441d80c00c02649031000c0e8030018010b0040024020246e42c100304540101c0d00382604080d000340802c84080c03150703400001c00d0211000716803141c2001c0c01c85440841c0f81c4440d0460085800004442c850107409c20340311004d40c95a4441e43c07100d241e0354400210f8206101080c0303d80622001000e4080c424a01d08540082c139040f00034141c20040c558a14003107c234607000f10f0b071070002072001030141c0e919200c1c0c041140709107070864403050b5240c2c074444038803010301c0d4864021150071030341c16107505003151185060300828440040c81103030840281640d0000b8040d0310b1000411494502a2854101250440c40e805036081a030004100a4168043d24075610841065520803400c4bc030700740e00c03042298100280380102c09aa801c08401c00d4826850051490f1200d8100c040c0f0080b0031500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 749494181 1250 749492931 749492951
    0x327060601090b0a0f05032a030901050903030601050a030b010306050a0f05040b04060e04120207050312030106180303021908090a090605100e010807080721270b011e08010618 77
    0xe011302c1800d2071240001c0701d443c4500044da020794040d68102c1c00324802031020071310040c0d450044240c14140c01c070f1031a00220800c04501b000340102540415608051411810311000180850003444914000c1c5a2602c01c88406644660b11400040c44010401c62a40c0d55408003158201c0c800d0243d68000c030705006800b1454181405070070b085641d190450449942c40d601c0e00c0000c48610010744045001d500d000081e5954100184120008103455540e42d03545000300c040e150542410044081c000b40300010004241c0215101a003010402da07c144140d592785481c04080c40b8404401e40c0c403c038503010102c5e101c2c0550380848261001541c241007150880042a14000c0807444014006090103000400f824410500d0f0781d0060160b06008200854005230403841c0020406c1b03100001c4e64540c00300c0b00100b0301710301e42e150a400c0c41c0d1680b04034032004c0d11030200780348050080700a0b01c200744099124600d60035914400400c4500c1c0208451a21100d0980c0440c64801d110700c801428111122 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 749495431 1250 749494181 749494199
    0x110102030408070321020d1401060806221d161d0103020d08070204052406120109051003050d020a0605012301030b0102010b030d03090b0709081002032706060109 71
    0x1e008540202001e401c0011aa038101c6510703900c80d41242c18400040001d07000c3d11000d00242820403100c03a00480c1c0706010403074524114034168443c01c20000b03294184103140d2184e803660fa1001d003c000c821340c40700b494840e01e5809050000740c915084150b0085021505001091080c800c0f03d0014050050315960482213000c81d00c4580440316003071420b0010001442c01c8000071000900c11040c04c0c1c00c00c0102e0b0005811a6012030b600b0003280f8a030b007c3d00012407074012004c41180811900c003800c11003c1d0401c0480034505000e007610300c1e5030352800b003004102000304507002540d000044815001c0c0b01507000752940c815400c1252420b0403e00041000507045500e039501c5c403050380c0f07183e000f0024840110060000b0b00c840606556840e8021000f41d02e0900038686003004680b804070300342840c3d1070300c011030b048006c0030300080290500713090041000110b00740030f00d40c04d03e0f94056100c2d1035000140c2072480301e8624074140c180b400c0d0a02c407030309030700450443d1003a03e090300c84030451903560b5411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 749496681 1250 749495431 749495437
    0x1b0c0907111e0c0603041b060503070c030503100506030403120f1107020609042901120509070326030703051f0b1606020c0106080a02033708070b0a0c110102 69
    0xc291a004080405a900100d03810b51003441e52000031507225039009800708145034010744007911402c0320061040c40341d030320685210009201600c1c000b880c516003120000c01c0700f804c0c10b4005080220010114641d0302411080c0405480700620643c1d480c01c00349409864030f0600540300c41e003582402400c5020310300034426440301c441280300c3d01e0700c0c1c901298200010355100c0e00b4002c0d44076907104505012108000170501040000740b22616807184154009404052803e01d0000300a00700001c00401d4180407030482c086980c0401100707030199641c0038005182038060118810b40e04044200859954541c00040c000c180000c50720035580488a0110140c0d031380f50140001d1140100800904440f20030030402031280628801420224884030460965425a1240020f5407040d11503000b5440c00b80000a100d0420300043c16085101589015100d01150089030302c070507408203a54140b01c2d064080310b00d076582c0301c07000030145d20f0403c104400510348140800009459030b01a111718403814030031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 749497931 1250 749496681 749496707
    0x3040b12180a0204020a1206080106061b0f0b250201021308030a0f0f030b0402070b07090501110d1d090f070e0103090c090506030124050f0d0305180301021b0c0907 72
    0x140c50100b0003502400060740c09030325144200148043c400214801c00d01c901000351a42c0d0002244840c5481c000800760503a451000d03c50b0300c104c029090001e00000e041000140e07000070490300e41d69454000c0e030001411080d041d070103a01c1607403144056507819070060109200c0641c20040710740d100c1417080d17501c1c01000704002c0030030b200c030040408490003221402410b0585190110398245036030041740507a04911801c031981c59074542032081c3c65800c6120400540000e00c0d1030000640c8681000d592046d0f005440018449005030b5240b0a07041a00312021003c00940000990300b0640b030104c880c0c0c1400c0f0742181c0060070b00c00e07174a401c2d50f01c24003d40030702035004940700c0803250912280304001e00c0090000ba9141d941c5030304134108484200c03007001c0c80c85507d0940c01c102e2460324050200c40141c0510007440b4203a5181c1c0030b00040d40110694401c1c2d6603445400c50307818540c90200e40244111008060500e20315111501d41050020b49446000c07411344003150782e13807a2040c05850042c803540d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 749499181 1250 749497931 749497933
    0x4030b010b190e0105221815080118060c020a0c080604030e01020c060703081015050d0509030909070302090a0302030f030702030c18040f03140d0506100c08031803090303040b1218 79
    0x10340708000c40300d506d450020704016904030f503445a460401c5038051148400800550b81c86003101c1c1d0715200b0550f240801000160000e00c4003403914601c5408070034140000030003c60381e900190010a01c00c001c1036405c954480e400d01051516800003d513580c000300c6044000411040b4002425440450440c80401000e40f0081c248000c0d950181c80d1010010001c48008240400019041d54000b43e0702c1400480c60702d40c242c0c0d800d15030480340d05881009101211a6108100c508ac0c581c0351400f2555010031035260051711007103990006141c0e01003c2c0d2000c0d500d4400e59081002600000c4024500c4501c02c80841300d000817910184646005559002400b01c0500e00018012841442100020521034a480c100000026030403d07150780000119a0a9030766134400c0003064100b21101c0115041da50030980c142100300d903620b5001d80b20091020012680700d40040c401e80f0303010410341e03841c03e00003026a51610b84170a403800b400d03080780a01150104101c00418000c41e06150749800d07050b4104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 749500431 1250 749499181 749499187
    0xe011416020a17030f010e060d38010906060e03060403030513151b031a0f030703060e06040b060a0f09090f061b090803040e0a0c0504030b010b190e0105 67
    0x14000040805030000100542c0100c0c1e80020010740080d441c00c2c030300c2e9403420380d00c0c2c0c407800c10602c8074419400c140c210128046400c414880555110300c81030a01035440f403003494030440c424401ca02d04122140030040c0d11504040a616809103044d841810f880300240200a00d55170341204945a00c4800d1040e901504070300c01040129210741c2000b648441004050325180206945d040c411790544404022107550300e80c4002c405030500340558400340c01d64502800704803280c40f00540300802003802144582c484803074600070754405001c45802907800c20020425050030006950706c4000c01c40e41141c400c03102200241540c034150f07001e20f003a1200c0d120b10322079050402112400901d00050300b80d6012030690052800030f440ca001e19115281c00207130034407600c50014001b07072914403640c01000c850f400c180b20a100c0c41010010865001200140103d4917075203a800a44540c45190009860070a91000201c0d0301200c0038000c0020720700c0c01e44465080c1615140855015a004050500141c010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 749501681 1250 749500431 749500441
    0x30c050d050c0906030a062105190318081e190b0703180609150524060415052101060e0910050a06020d03050a0b0d080c0304210203010e0114 62
    0x40e40301d958041800100c82d850003120b40c0c005a402d030070460b0b515070942d444c0c0c00706100348443c20b500048212020103040012210315565071b03440302d00c1100718840803202d51161505046c443d001c0300c00d00181030298082d01584500301d1580320341c070344d150080041c0071000c200400840f00250750341418103000e401003014407860f40e85080640001d802002050340b500c0642ca500022001c1c0110721511130400000e08000c2803800b401400d0714600f06d460190f141404019402c00d05410011420181081166281c00d4401c002102c50107150403d540c0c40c038821001080007030f00280144411b115060074582000d280214001c01c0714003d004010014442c00d00411050a0507050346410002c40d400c0301c0d046644490114103020015071007000141e000c191890680c0760907106242c0c011100103c14800000c0070004180d840d00582801008144e0001b5441c610080900a8501a0012070154001000c1c44906044040c10b0480f080e80310b940380030282212560144509a66070f036001481e05445c0d50b034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 749502931 1250 749501681 749501707
    0x7050a06080c093c03030f0703020109080403050703144b1f0b0d020904021309080301091118100c05011d070b0a020319030e061015030c05 61
    0x1010b09804402003090080b0461a80c900c2c984844040b0010341c2074486800004c00e20590300ea131103002c84911190140c442c900c03920040102c4490280302180107958000a00d003c074010003000718084d18030900401e01000f0400b0107d000b000312030284038000880b44101000584800d040d1110700112481c940301400100280c1c0e4107080d1902c11380f2210142d02c2d0300810241a00c2d00c507410a40c02e150000f0601200003c1348490482d5015000102006070031342c4000800e196018ac100080c4c41805424001411507444880c51141122081014481c1031614504455103800a01900d4811800c19a015080c43c00440903101c003480760f0700d1540c0384030f03100105000b1800c00c0011000304102c240f0319424046102401400030721089038180c041c07800d080001203810300304c047e00140c0070b900041010448090b400015114946060307502e1440640c00781d8401c4d00103004400c941ea0320341c0160303c1080007a1241100041c00c1300d0142030241030b0072a454100710100d88900000c3c074040b41017482400380b00e0030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 749504181 1250 749502931 749502947
    0xa0b28061a0a0f0e18041202071403030708030a060815091506031902131e110705030d020906091807080a060b1204050127050d0302130302090a09060c020c01020f07050a06 75
    0x8044c100d00c444601ca00c5c00801c18040495041d40c6400036407080407200380d0304014a200410140d883c0b040c6021030b58001980b68854100c015048100c04400f140c40c1e03081c44d500000c010b00100c07049130180900b10076800310041007140e60784890700600500c10310010b45962018801c1d10300070086c0c100c1d8038000b8200b0040e0a907200d003d9811001038101c000403001ca510035115201e01914108100f000d514031224251640103048000c864004c0c454800040c90000c16a030000016038400768071541c10b000815403500600d41d1700d90b880301c014400084a501c10702c001901801c2c0d607035075000c1c00340d030303000780364410750343d080c410f20500300c500300300486050100c8844603420920070030002c50780c4403c540900c003001c00d100400404d480c4083d8030200402004014440c0d00c2c003c582003c1d818400c21155002d40034030b203440040d0280355450001481c140450380107480301d640c082401c02c40c5502603a070003903881001c1000d1901510500070200500400080d01d0302c01c0b19001441509054108541250800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 749505431 1250 749504181 749504207
    0xa050c0a05030409150b130608071b0303060603140c0405210109050d02070e010f03150f110301091a0d0305091504090213170a0b28061a0a0f 62
    0x4000c0c00005000201c092008000800d1010340202d41004181799840200390340380d0010004c0ca070104081251035020540c070100b02d800e14200042d80c0da80318541a0313482140303020320304807020b03080340721404064056120405840a9035010080204520012620148180c812460200f41803108100500d484020101c90b4920384a0840c6448001d482813400d440c01c0386422107290b0460360889203804d9040142000401c0c3c00740360006103501d0031440380d000749100e01000d80414800300c14038552400079003001d8110303190035000f08801407000c0d518244d142c000b03014000d040f074148856074456401e107a82d81c0400d0500244404405400c95406640513408038900580004a21a16064005028010300004c0403000c10269485500200100090302160881c6810329061040a86031440003d50507108541c0681004840d841e0103010301880180000c02c104003400760901142c40b1109500311004076181c2c0100c0c0040c20214640080d0903018401c42040000c1c4481d80001078203209081a200708 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 749506681 1250 749505431 749505433
    0x1b040305060406020a14070b01050603040f0516090b0a080c040905160e0406050601110d301505010509060d0b010c06050403030c020d080603030406030510050a03030f0e150a050c 78
    0x106550369200350400d04201c80c203603212903020034002c400d03070b410982d0100d0344082d8170b80462a054155a0318491040c041c00340b240581e41c0440040c04001a00302c0c41e101840c2c204003211003d5801580748a0124040e008041c03d060a05404030b540c1d040c25001d5806990310072010f4145a000c40080c803008003800707035058450b4810a9980d00c1c40420303030074003880508049100d640d075514207400c07d0800d03128090721041c100712604a03050703c40d03000813501402d416400c1c0384c012650340140e0310042620160b800408400385405040040003402940041c2100038401c80c00302d0650398030001034459026808401d0740101d010801ca81c0d070221140d00c0301d004058141003854020556454001c1100d004030b8003100829a241e41034010681c0402c414044460a860088454a40480032030b480f0702881c0f140d035050680341c070f000ca244401040024000703000080d100c404c1030760340c034200109403541046903200864410502d441c6c0600301045040290482095203030300d0148140012666640010041001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 749507931 1250 749506681 749506687
    0x1a040207020a12082205090106050702031626030a0e120715030e0c0409030f0c03020a02030604081215032814030c07060201140f0612120d0606050c061b 67
    0x20a20500324603505450250908580b04c90340c40c01d107251010b00066030705c0300f10414040d003003100360303100320707500f81920300a150180e2150f0492001c2840d10b01d0700012403440001800c00821000c2483e2401e44041801c10098040002504001601d80c424184003c000946c1d030003401400d810001c1b98058060070910845103403690764901c0c14465028000c1001c00a5250494401c5842c0f04108a40c1000d030112400c000522980d9405030029092044000034060401e405009040c0240410070075103801070b040c1d0341c40b4075080c502001b4990044140306072041194000c00e880d001407600481031144c01800400807041402c0000c010070b50681d0440071f000501b804400c0000359000302080c5120841070055869907030303149e009420000c1942021045a02d0103500101c601c211026880d005102200105c990391254008140c40c54204081c182952080c5904810210491802846404070481040050743e4441c4012510352043c6088140c26034080c13070218150580c68141100c00520305000589 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 749509181 1250 749507931 749507939
    0x18041a0607031218030906082a070c0e09010c02060405032a031c050601210534020c2d011b110306010504050c070305091306030f0302070602011a040207020a 69
    0x6591050758482102180d1805403c201500a40124050700c81c0d41003140c0c2c89e2500d100c036000c02c0d001c0c0b1003000c05a21003002501250045d0380d0201c0b8003c43d080f04044036215210442151124800d0710802199840e108100b01e80c5807010510398000e40d40034028500d04041d0304082a080c0b408622210ba0403c6410b01c070a00c0000c1c104020000040582c250f0202451501e100c40c0c115100201114103104a200300e114041c1640007140e20110f460303d8000469440724480e40c16034407910010301641c004924040400303940f0340300410004081503800c460080d0303907070350522a80c4005022840941030102d11010301c0d010000c00034424903a01850445c051002401072080038000d402001d80d400b00c940c2c6803403402030a05010240c0500780070745040c0401d08040c503a0207a0f41c4684003010301048000326061030705aa80c501c1840c0802c5003120180035842c1c50b0304004402c007c0c90a002c4001d8440c071a4000381481c010300a10079194652044016140d2490081c80065032141200b280c0c004a0740c00c02007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 749510431 1250 749509181 749509217
    0x1a0c0a110a150e01021e030d09080702040908070606080102071a04031707110f0303012d09050a0c081503030a181701020a081012110f0907030218041a060703 69
    0x10038421007540c1d03911406503c420003e405c02086400b503056115a02100b0410100c0c0007089551100e0150b000040b1007803581000c86650044210096106081904c95000d00110301c014290003030290b6000c0010b559298005030807441a030340d0080401290107122072002e8041d10307543da0f01070b0003414601100a44a108040000e004a4610021400328005010907030810003000d1540f40440009515550404580d10705c0705201403040541a00c9404210f10004010218070004010f0018140483c0c1049138800380a4030b02d6517680e100190003003000644d400568052826581000303001345140c807003400011102c8010b1503d813812101000303000061030420444d5266050410000016240c254840c401090400040c3c141c4102d044601c10502c0f1510544090f0b020550340111400311446403900401c940000420340c0e0355001d181a4108225150513400400c0d8240080500304551040390003000200c8254840501c01611150000c1c882400c100005009140c000d04141440e40c002c19011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 749511681 1250 749510431 749510459
    0x1305060112110c121801020a0c0e07050c1903110114061e06071101180303020d030f0f09060c0f030e1902030114070306240f0f20071a0c0a110a 63
    0x618900740d0005a04102c0e40300005c4a00001e0000744094404420750703840e000511444c2c0e0091040b62100000401c01d8a0f008204030f803611141c04c0c00f038408000000d8141c0e401c00241c400d0a0b0f01003903c43d028644068411b1007450781103e201d080c220019142c00c42400003096200701c02c40c000090200c89280141d031000007810034140301c0c81c07035440003800c107400042100709084e03030b060100160034071b0500c0060b8010130300603640f144901c2c00088030079a401e400c60142c81c1a081103540c49203400e09240c140021900000307038a000a4880f60300c1c128035100c0031411a441d1010204c4240c100500d803024100000d004040c145d40000d0010954105c104001898540c041e0f0718000420340d07600c41005044182d41107122101010600d184040382c0d4550007070506c660307e001103c1003011240808203400d0044d404099914204040f540c0f0050480034200d9680a550091401c4046c0001900400c98001d03811070700030300a0f01026169840065a80d0000b24044082d4260700410003440411181010700c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 749512931 1250 749511681 749511703
    0xc12060103170a0f3203090f01050c03150102160306020c070b0c0a0f060b0a1707060f0807080612160e0105040216032001050a020304020f0f010219150501080c1305060112110c 77
    0x5da80d6682014030403185804154003c41d50540d0400d410014580114010f403644000130302e054034401c210000040b401d0040f440e04d4810344400c400c00100c144411a409041004124406c0300d44a40e140c05581c0c8160094114844895100107500e50000c0c12079410a940284100e401150a020040000780c1d007072590f4110000c02e1203141c00e914a513038003c11200d0300070213050520002c00d450100005040c200010405030510841d000404d0700303a10740c214648029900881a20070764001c040017001e01764014414200c5003a2031800200316440c061089031411034010341202081401d41da407d440c43d003000c04100111034400035250a240d00280070fa00e01c00d211311003006a481c60144100f0030000c40c02c5210754001c4000c000200880d9030002000400340f81c0c0d090120f40c4000c05446c4ca681c018102008540c2581e04103030000450540c00140c191585070211010400454029400340031103208070380076400a1481003070400741800d0f80d4401c120021501a06501d446000003040c0e280801d00c0301 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 749514181 1250 749512931 749513027
    0xb0d0903121d1005010f0e0601110f01020c12030c070b0709080115261f090204020c07080c030a05030306090402210601060e040b0a050f030c12060103170a0f 69
    0x3000a0840d601807040b4002d5014041040040b541401b82c19070480d00a4051010741d88001c2000c502c85278091107081184022440444101c10340c00d0544501175000342c80c400e0f96130302c00c000c42d00442c500030710b081c3d910442c4050b03451410241d55031243c03c0c101d033000c0c0614080c0690380501103180c29081c00b030580c5000c18000d50a40c46413416050014220804054a01580b402c03060030b8040c0704040703800583c0c005c4880c85101c202d400b414200004262815000394400e200007030900c6078400c0414020115100003040d9400d404507041071603180e080180009145410400000301146000e00d043d5411500251002ca00018128814090078454103003501103544403a00401c191a480110180407100c15141440f010004202044540070380380110f0f803041b41e8800619125440030072201421100040218021070300601d11aa1240001e000907203180626001800260030303c0e00c200c69544041d9524007030101d0804404940d12854a120310004901c01640c0d030202030100c0050408010b100310b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 749515431 1250 749514181 749514221
    0x6040303092d031d0a1e09150608040f1202102a030f021224030703020d1407080d02030921060112080403080406120f060b0d090312 58
    0x410a510001010500c80c2c40710a80c2034004201c08204807180400641d0609265805000c04600001c40c2c2c00109212070b0001080d09000030a8080758600e861055401648180125210b600c0c42040e01c808506501081c003550780100190347c0300c1c104096005024401c0d14640f03124035603510603100c01d1850000010390007080c45000d0040305208042801c82c1c450500d00403103010303c2e1a22100e10000810a092669582c0b22103001c030741d01d404840d41194900185d110615000307400c00003c20510040310b203a44000c2e081000e0341c0c100040c402042e0b0781c00401100a804a0390354000c1106c00c22560f148903409a22030020780107408101613181001913401071901c6a0407113060103c450b0707440c8504c62800000310b04c494042c2101150090560b0000350010801203828205440b480c442e030340c0000e0080c0000280000d50030345c045010045081c240c0c2d014446010790649600699903c0d0003081c5105204219480c880314241d840300450601c80d0504540d0940c0c4810000c04517482c1c0e581c8850380e41881 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 749516681 1250 749515431 749515433
    0x20301140a18030914060c15040b01060809061b0d0905010c021203011a07030203190e011715040f09060908131703041a0904091505010b09010206160c050604030309 72
    0x500880e02c181a042410204041d51034400401c94000ca108400b041e18040320f02d180652a864101c0399280310600440f0704002d480c0c40d50666448080360103aa02000d00000481d11920541e00c45d40200c054900034003690f110110700f0b00304221450089044c04804100320302d41da81ca0350007250400f50041c0000520000485000303400e204900140c420500000c00052044204480e00c030102505c941200030f8403921a49420307440c5100f0b030003186070300071090103c02140503880210040c813413a080c0d0300c0c4201409065080c01d03504a05a039100911900c01003184428205039124103000030100700c022841c00116250708003180c0700e00d0801e0b00d100c80d00080c0750101d81641603180005140020b0304c1d01c1e440e0400440107032280640c1c01000c642c1c006081a6041008400041d0343d03100400400410251446291441200706039145d015015400e180c000292105501c041d11540783c0180c0107480ac596940c7ca10303440078031460b0510002d100120900e130000c81d404001c400d03c2248a62000140070503a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 749517931 1250 749516681 749516701
    0xc0609050c03190f172101060f030204150e01032309060906060d08030c040b0c0303090c03031309090501181208060406180504060e01021602041a0a120f02030114 71
    0xb0360782040c0460310030b0034060f400504010604840c2c00d41240d410b45440c0d454000111061043c0000088000f42c1c1510031890601c810941a040b112035403140403240051003000d4090380220b220340703404085040550b01c0b52038003440881d84285e01c140360004a9900c00100c448402c00003030743d8810381d03400340c004122101404001d000d41003006180200102d01e8410300082c01d900d0301000040a055000c4086449050030100355006081c6001d5640e88480c0014446507507508120381c0c21060744600784540069013004021691007012445560000038100a0030001800d80806c04550542d40ea104c00148880583c4022941320b00c00c0c00a10000031024000600704a00070b071400d44100d180040030070008084003a24441580d01d40070229955546d42803400061090345801c4007036500004104010480d44450f045c2598030845017000030b102c01c0c051040072011060b0503180c10140c1c0c0308007030000e20001d003c203507034a03482640003034850902580072a00b950030580e21350210403e00c806011001d42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 749519181 1250 749517931 749517943
    0x50a030b0f0a38130e090c1e0405011403060610052704060b090a0b1213110a0b210f04020d0f0c09090c150c0b06030a1407081c0509060a0c0609050c03 66
    0x90003601000e03400c01b440707140c1d114a00000d61601c9200d1011408141104128007511b0b00038005004000540e0755039800300c11020303141241403081c00f580000074580c0c50702c0d00604142a0242d0f84a0781858100b5800901c8a0503646040c0ca07041c2c0404401c900302da40d1409a84041c3c13030040d0701c55403140c2c00302050020b01d103602d801102d9003b42c180030b1442d030904440780c0c80e41d000c405100003203000c85050038840140040d04034482d8110410710404100c0f00d20740c134010050121402c030450386807080e4003010111802c3c10340b0703055aa8440d00700450051718008102c00c10305402500e0241c0740f200a41d55408200003143d00c1958001d482c3d001c88400d0104812402008284580744404011440003000b000000c441c07200808900c2d04070b010550329182081a0280366a000280c0c1d100d01c0c11480c1e079583d40701380512030240e9603c40d40003c8001141107000c1903c1003c41a11741901f04007000c1c0401075180c1000300a4000c200708400180082032403802107a0810780908050160240c5103c00d06080071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 749520431 1250 749519181 749519189
    0x4030c1d070f0f050f0f030f010602060c04050f1201060803190e01111908040b0a020a150c0c031214040f020a080c0a140402040e0403050a030b0f0a3813 67
    0x458211042c0240e4111a005100b44900c2c5801c0755101c8080310004224010021062100203011003041010881d03102894107881481d0202d408541d107405502e13205204034002d40350003c40140c05100d42d4100320501041c21207202e0004070392076803150000e034038641001c0305a9542c0c0c80f41c541562941c540010422110810038a014408040003a0301a6983d441c80d01211840700050310740d40c0e0074000b01d402a50f01410ba00b08007640c0e11041510003d58030030110038103907000c400c490201d50340ca243c03c0c41141c0b1010010340b00c00c5101401901c059400128685404007000c1d00c0e0102480440000704445115a11a08086841275000c0c0107111380040d00e608006511f41c0040d060b80001d40e00c1d03039442000c0703401e505070010101448902207800380c0101c0d84210000081d06050208050704200030b40b0310b84900307980800640c41c80d807007004440d03440d03003250680148020009220307020340003002190380c0c40c1e2210040502d56106000c4002c2162004248401c17200c041085040544408400350041c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 749521681 1250 749520431 749520437
    0x6090607110d08070804050709020331021c03020a0f0c17071a09150307031b0302030118050a142e0b0d020c07032108090109050c10020304030c1d07 65
    0x21115069001e880f0810103481d040c280402c00c0d0008040250402048001d403842001c15522810440150200ca1b0b80721000302035030b41003c0030030360300107030401c840403090320b80003854400e00a2a8074000c80c4a540081d900f6011401400c1007540803030420083c003203040f4880c0d01020620303403030071011001800004882900541013003074100200c81d4100e92100c2000c100306130217584c030b10031a40022070040144403100300601010042102076a050b511946400303207031a00400501011301001c900705d00c02401658000101c420140c0300040b00c13907002690080015030001442c0c0e40203944142c1480c0b04880d09180210f4208480c0c0801d90705050109a0041100e074081c8e0f0a41040d6106003031b4085e80400c281c05e0341d40854001c8100804128880003540c20017607400c888402d194002003074500c103802c4000820040e502213400d01c40141301c0e840301c1d141c000e00074180c2242d80c8010045406c00c0c10320240110300c010320003c0045040b078001d5400500c4c182c03204102804401d44400c0260030020070748818 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 749522931 1250 749521681 749521693
    0x20d0c0906064a120f06060a0509010e072f010504020406050d0f0803090313080106050f0d031704210503090d0807020303040305090409060606030209151611060c0609060711 76
    0x2c0301e982c2c0f8039110342c10503000d420752004020740e0085000c8440e10143e49086214011500c8941c08001c10100d00402081d03580801d482e84070410312451032800c3c8210281c0e0031340c8500241d2224860440100440760a820810403130128180d054414240d05070f4007043d695541c7e00b03100442c40d10f481650010b142c1524100c1032840c0544400e081207c41c00c0d00a070410a0000020fa4800d1052040f2803d0580c4100c3d411502c58407001c0e590300901e01800345500504140854414034a071a200e102c110303d6042d03032000d1000ca03414103402282c50010b441100e00e40b228100e5010001c4040c0c980303d643c1d03031300c0340e442a85030700c0c081f030640e071800000303000c90010f0080c0d120900502075404000c40c0c0d801030301030400ba66100c03120f0300400d00406200c14043d240c14174040000c80c41e164150003d280d030003c100c8983c030300e0b40030221038641e0328031404581c054404099010b11002030b4540d41000d900e10300003030007281484945444142010000c07034042c01190014010400e90769044002254100591001800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 749524181 1250 749522931 749523017
    0xf030f06180108101d060412030c05030f0105240a030e100b0d0f2604030506240d110405160f050a080a18050a030801140301021303020d0c090606 64
    0x248138095440b040854070748440750400c4400d08080c48140c0c03081a070301180d1191900c5e040004c82103030340d2a400b5001a0401c1d500c1400319102e042520b02815803c04c81a103141d18280c1041001130101d26030b000442e841c1c2901d00c03400d2914170003074016001c03140c4020a058145143d02d81c00c3c0a10041c008148074070708107844486441e40c110f050007082e840740c4001d035040f04500700711641c002d2442507040504240a940801040c0352005402120310500803103141c0c0d00e40481a120a403071610895141100091001c1110716100d1405032810f13001d076135101c58290112000c074060307900c115010f001c0000f40c41c1c9c0810a003a4001080c0c0065082442c105040c1164050000c144a002408146107144c40b40240040580306903230032401181d008045034100319451070041c08100c0f0900c01c410102050848502072070a06008440720114160356161520f0309503401c100941e880d0500585016415031004500720702c40f403042c00040c2004da1100f20900c0b00d411a491005031403c2d442d0004d00c216000e00c44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 749525431 1250 749524181 749524183
    0x60b04030525230f090f07050a110a1a0f040803060402130b03100608100617150a230a050904020d020613240825050f030f06180108 58
    0x1010b180308407000001c01080030282c1c41c84100705608043c101c4825103071069408080d1030307140310900c5000d0303409903100c00581c800c201c04900100d40c024424017050000900c90340c0710784000c10900c215410948540c012210095142444d0110200da503594480790300025010020b8910b6441040c2000040080c81c282d070b0307160f000e804050295030041e074000c50a42400745041d00d640c0702419200840e41e032070385080840414400024070075000810b40c10340124905400c413003c6a416520583c07200c0b1410f040380f1911002d82c06005140e0182c1c12081051000c007651000d1080d0014180100a5840c455041200a003212050610075200e03401c940410442d41d1038101c07803580d109404545185084103903001040692049803520f801090f841440441c0090f4074910321610100514045006000c01d02001d50305103405a41d104003100003500049032850f0644d100a585030190b140060500c0b551000c00d8080390001e03550303943c40c40d0754001046554100101d00418401d5000012000d95150070308003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 749526681 1250 749525431 749525443
    0x260d0c03050a0203120c07020a0b03060607080903120a09090501060207030312020702130626011517100906050a0c0f050904241d090a0506010e04050a0c09060603060b040305 76
    0xd003448004541015020300034800d80700742c02c4000f402000f071494004142125548803240403445444000e01c08120b030301265003030701c0c03140101034005d07803401c035181e1104403039500305800b032a915118881013014040e201f9000303855201602c0d2542d02c0307414145217640c400c0d100140c102c0421503101d04000c00110342c1c0075006c004c1a054403030340181c0d11810b60020521a4611800ba000000d0910000041c034803000c1015405a148140342580303c0c09401c80100e090b00e040002880c02c6410100c411b00010728060700f039040d040c13000300031140f071041c0c200c40a400f40c1e810070806846503a612003c00440f20310500a807042e8070310341c0c64100500c05c07001c1405455405454801c078042c03640c4505407041c40e010280308081402e40380c1900c95201c0d40e9640130201782c56078481020070105c4104c001c201420f2000a01118890f807100161000744e00b810f20018800400610030b403103920a48035008007080d440021980606150540032444502300304000cae0a0700c50325800050805002c01042021913004905 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 749527931 1250 749526681 749526683
    0x302071703042601060305030913061239240207090c051b0d03150e060907031407020d09060207030515090a140309090a0c120b19260d0c 60
    0x10420b19003000c102c240710fa81d020118240d403250700e848000b1052090001c0a01000308044a00035031800c42080e228081d02c4a61090310315150361a845200050040c110f060303141c0210159800d14600750b0321902101070303000440c14104004401c000d011582c000031840d110b039040d105840c0590520010001e5985003039110306440360703907109004a9034901c980200c990316400c481c400030004405404241e10384c03070619030769800310b854602c14200c400c0d20b0042040407280b410306102d00320340d10b0f40140b01e03c04e84001c0007003003096a926a2000c0b0a000c2c1d01e0483c0c012695130b40100824030018070068151900f0b90410230170365201c8081040050000601d8034511968000c40603442e450b5418844e1505c0450b00004001c00030440c4200080c910001c094400c0401c1107640c808a0b8540309042002c4880803084280014007241d40440e10000d2a00720f09441c3e07030085d2102c04588002800c00e4400003003900701150355000c1c6100f0900c80d00100051203903202964024000c07050901c1c0019041c440c1200e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 749529181 1250 749527931 749527949
    0x15030402041b0f120b10020106080105070903020307030323030103140c09101a0408070b0d0507180909020d06020406111e060f1008011b170601081302040204090608010504030207170304 81
    0x4c2e006454002c00e400624004c8400703070040e070f520109190040c0c00f038a0380d4020a01690b1810001511480c800e0840354200d9401801425032642161001c460303610003490300e01400364442d100e55084c82c034540021070080d805405030803500492201c0071360815082103001e40c46100c200d410f20180e034068000e1401140d08e62084042d9000700d85400e081c45024540c4940c030070340078074080000c446000d400181170321031440310200103d9a440d04140c4030098110b01418100d02a11f10038000d54404d923100a07601030000700400b8081d1001d50307920041e80d100c0e41000c40080c10300702243c80c60b1a010407048520142402107880984094a100b61b59400c00404c40c0c10100101c0c000325409107500500f000260841c480280000510b055528040c0f602d89610480012140a09002d01d9400d0100c882d014180507910041140c9511604056100052400b070342d0181c0d0801000442421512810b0010720701500042120b00d45404c01a043c100194010180428070f40c40d12154803501000b1a82902e0141d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 749530431 1250 749529181 749529197
    0xf070305040608153d080709081207121206031103100221180a0506062d010e01020c04140601080907030305190509030a03020f060c0f0403080f0915030402041b0f 71
    0x5c500760280000440306a081d481911003590820f948403030310030b110724981d40390081c1e4150740d0b8190741d40d5401c01e0078100540030005e010440008450700418002001b040c40c044d545192540c019808603400d07940200c071911040c88440d003445c02c09210b4400f14158800d021070400403118000c001540e0403800d00141d06e00500006404140c002d0814003111140307500301c82e0303545114644541e6500e001d4030790a1169640250a4210b4030117600002c56400010711055115800c80c001034440d021324605540c103500540d61056070546171449400000809005500305604080e00003600b0388074060030207030715074018080a0011940210458201d00c0c1c51710b42e0850424400da070225000d000312402d155040c061182c041043c1640080c480460990510071303035045440b1900e074101d441c031450100c082400340074041040030402d810041d10782c00d91001c50301854041d4590000d035803d404003043e80c1d00004044148000d60509114446401c81d01940800503401d40040207006085924002003c0003854 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 749531681 1250 749530431 749530489
    0x31505100906080a02300105040606051e4c0c1212020403290609060109060c02030708030406120b031515040e0d0c1b0311060a050f07030504060815 65
    0x4003100301b20300c40e070600700007000b90404100780703000c0d01c4140d07020f846280c11f01001140e01d1600c2135542841c001e04d401c1d070600b50140b8105002c55100f445030002c2d0900c10407252242124502e440b0744041805604c001803240f00d070301c0105842c03000d0300d0b01103008200011500e0000a51403003141d40c01034545041184511106425040281c41141c00040400000541a06d5a8140b901c01c1c3c0480b91110181c40348565146824407509280488001c3d00264150304d0400c40540100c030341184090014041d01c10840e19441c40c28695030117548507900066640b40c40c100354a000c1d115403080e241044000e05800f84074044040c50601d000341c21464000c86007089004280c0c1c5980c05200c07070070145070994000544e405130150840c0300254080e5030f45982001103a014082608401d41665440504118040f15031014410140c11103a48401481803c01186c02055000d034007031302c807152107a0b41d4580e40e5401c0c00d600801891003c1d20038403e0341440603418a0703581d6107005203000440110082c40342080d030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 749532931 1250 749531681 749531719
    0x70504032a1701051e010b09030307020a080d090906030b18150103030810171506010909050f0a11030603060a02090315010b120708240a031505100906080a02 69
    0x189010007221401007800003500c00d04240050044000e0303000200f0150b0350f030000680c1c034885d07541e00514480c41282d005002841340c04024100c000030290499042c11403542c08988240b411f41c02c01c110a80c040c1031407207651988010f800000d4014440c0500c112071955031f4146010368090600c502e104840000030720a0744040008041501c0b0104101072079594905014219031010784a007030075100304803004103109040d0314405120411020044c0501024010620440340700036007007904111f06290006801059402820301444d2006041d42c2036050020200045400c18282030007903a030306000300300ca150740220700d0b183c0c058101d103000b503521091680024100a109407010010b20410000400da01e8039010241c6459240025070002503100c100701900e4071a402c41e4410100c6081c019086034180a20b0710924000030042c240400075034482e074540c00303011044207260b03030703841c2c2c0d982c00f0040b148002c1410003000b009651000c000c202c1c00d02c9a04c0341c4800010001a0040c0c42540000400030b503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 749534181 1250 749532931 749532983
    0x5031e1b010c1b0501030f060605120a0603020a06021b040902011e02031903050a0e0613060e010f0e01050406050609070c0f080904020a091a210702010905030d09021807050403 77
    0x42d0000040c42848404408254042c00c1801a14000b070300d00601c03003501040134408d200582c1d000d629218144000c001d10022840e20043c00da00d0700c26103403c40000142c96107482c1c03d0280000d50040c04403040c1c4c0c09001c80c186403142c4640c51150b420444020003507600b002d041c0c81803090b1084008014043c007031081c0c0c0740d4415502401c640c0e4024014040e42558558001e41c081c0003411070078002416034110440d82d0b1002550016100a42d8044880000c1d03c661b101e40300207086500081252503410340d400781110a000ca24030700a035100c0d8104410440c69115160b403007502103c0c80c2c0820701301300130014619118102c008025161800917201440490030076503041500061040d5669480303504018210700051050b00006c40342c01820b885000e4035581034806250700b03c880d41481c40c0c00c414803100b2032840030b004a0255585d1755052400710700c0a000810b0710410010020a8071031040c81881562485074240c48008006030080c03004042c0d104084800b00c03031f04213606000c0410403964000c6000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 749535431 1250 749534181 749534183
    0x40e101511160611060108010c1b03030b060708181e060c01020c0d05040509010605040e0a1e05150a0803030402030a02012f0a060b03010203100302040c031e0605031e1b010c 76
    0x1c0d90744000000c9055201ca0072402c0fa00411094175603690781c40032124243e07001001c11402141241212210030700042c0b031a1030f0890b02900e404180505000003244072039001d02425112024001a4800010b1840403084500302d41a540d100840d40c0d21241104154000a442d91084100040080314858250160360300d141015083c0c526196182d07001812951061064a01440841e03000042c041d001d03800b035400f01c07580c4250342d44e0b4559510040c64000c050f0600650b510081003c07001d0b8190b042d6200c4c0d0b03032203810308283ca6003200e0303409010420303c030a00b94050100d55200b00100b05c01a20049070b04003025078282071882c0b0b48550180d450810040c2280c42c106a05070501c030719004100001026010306008480402003101d11009042c04d030310040f0380304240a04154000c00043c181984070a1003400680303400a095100b8240601100c030009003040056a2121401d0080b440c0034040c0e10215000c503001110056081c1030303419240c980034a0425040c0d0726080d043c69099014580f560642 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 749536681 1250 749535431 749535463
    0x922170d02040803031501181e032f06041802130e0c070b0a110a120608030a020307050613200d0609080d2012060307080111040e101511 60
    0x100d44540d80240d03650000c41b03c00504171000c541030426540250041900c004800701429038140c03d007a0094500502e1403140e0040302c003c40400808612550000260484200c0d55206034014120108000202c10340407030b440340f0001c200030400e5074500b80310324940e60f012120150f10380030406096400380200341d000b60b280310410010880030020f164010700d840c5101e040c01e007900340c48600e81842211840511a4602d860800c41c3c512824000d002100f41c4880007107011801903215011581150860f009400250340082540b008005003401030301d601465102c0d10002402c80f903103130703121010644800da07115a00306909903030007602d8648210b10398039007000050020090b1850034210300d0313104040b0300441502e0003c10008003102c0100360075400c01000b0f1070f82c1c100380d164812642c940d4000380005a040c85030707606c0014036501c01c1c012160070380040907100c0c0c2c0721445c1c2082c4011034040200080a02d2840310703414405803030050418038000c1d9580c40d0080c0a040c5424500e86841c0100c0c040c401ca07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 749537931 1250 749536681 749536687
    0x2040e0a1e0807060b121b12060601090314190f050c03060402030c01110f0d030c0f11030f1c240b030f010501030b031606020c0922170d02 61
    0x444005190400184038802210900e98800c21414034501e010300e00030007021040100b1404545980c1042d0700d044401009480e08041c03680109107808000c1c2513030b0010641d1518145054a030020f404171608034800041e007012b16203400000e0030b100d41404007c00f03c00f884000c10044503410480c0e10704499030300c4a6010303125404d0424148444544034112003d200b014030300c46090a011540c80c0c010b5070302500425464013100c006407010040e104840344540303e00c070319180640c4020010042d141c9881d0300c000230b5800d112500103041c200120040300a0041140e034081116074008102c801604618400e940c540211032443c41540c2d0202402c56825814040300030304892110000ca1070070840040c101b40855514004508203000c100c030b843c260b1218000c01007202c1c1d4021741082031350b40002001c0c0e40d0a000381103c00714004d41150840001a808030358104018103140507850b030051601c2c00340e0b904904ea540c01009911240c00340003041c12400b418441c2203504440113a030050440d01a040d51 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 749539181 1250 749537931 749537951
    0x429060c0a120206061c0f150e01020301150315030c09050a0b0316090b030a0b0f0403020f0615040b060c0a060c1812200607081e04091a0301150e0604090204 69
    0x140c0e070311301503408512030704c80508643c0c4064074041e41c440e1416800584650303d5105500c2c2d02100902c04207290f881c1d15200e100c4180382c808284021806400d5102c1940946001000d004046549124568104120108042c0007042054074040d00b01c1d03100c48000300329030369200585400760041584460b007504c83d003a8000342201411091000350f52001c00300f044420b011004159403000340d244003500303e0400d08007044842c048080e404e50710500900480b50208200351045142c40d9040300e00c441006511810000b452404e070281030902d410132100c150070308a0103500d00380c480d1250301004000310b5660510504080c0a01c4009820f1810b122003400c00e50b80e5007082d000a0000e40d08200c0d44840120010840a170000507101542600603242605000c03440d655031030142d0203c0034410303031500d580d014080c0c01d8401400800191280e9280440d0340c0c401071b0360007003004088014192181c0d040c103103001110105000c00e84100c842c07d00c2c51030402e0f20b030040801d0040c4003140c2c0294120b42003420800d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 749540431 1250 749539181 749539183
    0x1401030b04020111120706020906040f06090305161a0a09080d0201020c060c0304030906080a06030204050c04090e0f06072007030c1806060504050603070e09150429060c0a1202 77
    0x2407046000703894030044544010034242d100d1209411040220700184259004619140d01034020000301500310391425849400700c00100903282d10180c0040d4828038244108881403060511188100100c25101410100d00c0600881601481100c0c114042501002c003032240a004000304060070555601c02d0280b01d00034080e5210a0038421035204580106404034109811240324581681c1c0710025242820400c541c40352028011586c2680c80c5c1c08040050f90b52882468082e4480ca202d50360745030718040c0c206050b03070661203044009410006014016110100710307140c1c005081c0c0351600840e030800010601a4003810440a42441003120220420405d408190242e41c0074010000607544140c050300c00750350130340c09800009103060004101f6030802e10007035a040f41090400e101d441400101003103d4040c11140d07000780c0d040b26001c1c0429410103201e00c00d800c2155101d1091540c4140b8111030180180ca000f181c024900040c1c08200c0320020300c0a00c0019078045800c800059a02c0c4000b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 749541681 1250 749540431 749540453
    0x110d05011502250317040b1c0b19051012020f1305030331121a01061115040206070b07090302030606040507020c0f01140d021b0c1c030201140103 64
    0x2680c050300c0381d0f03c800c0c2040c1c602140031084201038038030800c002900350780d10b40582800c0108210446001408081100030700c01010304a0034010088201c46da0040c0c104032025517200a4116000d1148408008503d515580d26001a100251000500048101c4013142c0c05940c0c07000101403148042001174208109100501c002145a05c6e208229a140c0c8101600e9124180c80140d40700e50307000030302c0c4491003020750481003849c04500c1c0b1030086030344510104500300b1400c001c40e40b084540a18010104209440030302401c01c030701d05104a00b80c210300c220b03a645280c03941d141c40d030140c1c000081c08642d505802c4640c161ba000e241a2124285200007070606006808124407030702490002500b03c0c1803520400b48181d4141d4001c0110201a82c240582c0c0021020781604005081481d480240143c000410308640b80110041c0c1d910b00752011503100c2a03918850a20719041160340344440d07a41d00b41c041d000c04144c43c1c5640340b03810381840c0c00da006104405031a00c981c0d0000000100340441c503810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 749542931 1250 749541681 749541719
    0x41b05030304060c0c0b030c2d1911030301080a20060c03030f061e0409140618011a06121306060308071406071409400b13110d0501 58
    0x1c40030399135100c01186419000880f088c406e000030502010004030360010235521042107025003a140e0980c2400903903080d500c9600c03c06504008070140c07080c15988082e0070400d0001403409941154180304440751140b0b00501c2c0581150004111404d40c0f280883e4a08110a4008c2c24541d698141c003400302d403250821140d00d00056104000640c40c1d0400e24002042d034800008451142036151042000600c0902810b60300d1146916842042c3c0e00104500c5001d44025580c642c40c0400508000303003503d004841150f80543c141c00520683d40341c01d03040e02c1c246c0c0c201c240003440c2a91540c0511309000c2c3c034084040e00315400d00000005000c6480b00400c01c541c010329a50444009074014243d03110402d079015030006d00704000350603021120300013406803200d005210000b08524115103da000880700c54a4600c41c061843c2c0060300b04080e041d1190380c0e100c003401800514040b00000e07020703140d403080c480541c0d40c5401c4901c080c012140200c41c0c980c000c1200c1001556104c1c0d282c8140ca00305060 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 749544181 1250 749542931 749542943
    0x405011809050c21300f1204051b030a1205090d0c0b13060302070f0201030b27011509060203030106051305040c030b2403040219030c06050a0210050906041b05030304060c 75
    0xc50320188890145e10a00d102000102c07400341070610101122076500c00d44000400500c1402608008002d5040142c000c900131401018103800301d590f84140100301c2c0e08418426403125900c200040d007240e24502c10398007103042940d2038418410224100501c0008001c0c10000369403800f182007980e000207456407542d00000124603507242c40040d4201d208061018181100e044e160b1001503102e5003001e410fa00001c0c0c024100828001e400703d90342c856100b01c0155a8401c2401032081d0701801b01d00740c4450a01d0b01d0703c1080c462034107001940f24801801003404201000038600c501030b540b9540300700288400b91082100e1100600001c0007402c035804454441c0b1140460f41c0c00d009415094044944c8011340ca182c17941c3c88590810002100c04068540d10104208001000c02c20b880b150800410781c0b0340f0744c1a42ca40034200001e042050384900c400d00c1c2841d06092004c98503000030700c2980301c1c2d07114000d0402d401d07a528060707401c10400d6000d168588000034003c141c2c0da92002a20b000300303104030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 749545431 1250 749544181 749544193
    0x5060103030806090c160503251104020f0a030e21030702010c09050604050f0d050610060f17010b030916150e030303041e0c030b01090207110405011809050c21 70
    0x3c8100051204160b89101d0145000d0190146a20466444034000340c810700c2100d10380040c00c4d40c551510020310340e090100004014100040c808680404000c4080440d800c51070555882404102130240e1a2080100340c0d90340d40b00408080104022101409615004210300940f880200b0540d03000b191600d0042d4204402d500c0313035a0040c0d403050246c4070300904c0760f4200790400d01840040d15540241d954024182c200220101c1d50a06c2140e014500300c00c50800c3c40303404c02201070a182c50899003074081003d000b820800c50700a00c1d41803819607003001303036041d40e0341c81d2a01d242c1c0c0303890302000400c1301106484c0310014081a46903654030600704e49032102c041041c06502056264003084802610314680307a00c00401464001d2001c00250344030300c105003004c44d00c07a21900d0030a078003608101001a400a0300d0000d114400c480d41512480c101c4091085604001c104919001c21500c120801900c56032807108010042c407001038107070405042c803076441c0c417980300c0c00480781008006585035000700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 749546681 1250 749545431 749545441
    0x50a0204352b020616110319030207120c0f02090a021b060915011a2203150608030a0221090d05100c09080706050f04030f0b010315060518070318050601030308 70
    0x4c10068800c211140d0030710312660911606580752942d000c81841140410000e084000402010707511495419940050f103800c040d1404806149107509400c0600055900b1040022031aa400206c803030760590701d044060b19540b407404041d014564480b00da035141d1409090f0713407c2000440900c01c018034404c41e050482c02503080400e00c042170103045103800c3c00304200c00340d13045190003e283c7c1451044d50324104680c4803200710700c0b111654008848004c003180385100016124010300b07020304000405940740005a540182d031340c03201d0f21036800d124a0b01101d0502c002280f641030303841d00f04002d00700e00000b0302d540c0340c01600c400c201402e072042d891908003030504192080c091700c1c060b160107100501e006402c01c1019290f0790080302d01d1000c45642004044000b07120328080c0903440f4420307240390480717506501d401c0b04c403c5402d004c45040039241480420403a942c00d40104d1614600c4c00a41c9840c1c2c03200e07201107024022142c64000754541c1440d035102005000a010382c121b038060380d1030880603110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 749547931 1250 749546681 749546683
    0x103060e1f0911072010020708011a010e090703020d150819020a06111f0b01030c0206070c0b060303070f030c050f0106030804050909010f0519050a0204352b02 70
    0x1240300f0300e0008080604c018000650313001c180c2850031807085000c3c20a646018002400324190180e224016084180d0410100303800340100030710581e1042060280041c0e820000344011010146c0070720403d004404078030308a0003a03040300c00e2007048540034007411120150410803003604c1d201e2018544a03603110260001030350300241085c3ca40c000c1000f6030103890040211002d404000300707001903000e501e01d072907608800003444070020303900303580045400501300002400f01c4081c0303980d00d0300790342000381003181c9503070b0109110300d20035441000d8801e05c0e150040864510701603004010311408004d80041c0c18075812400400b002c0744903804849000201c00c600170309813140380c880105581010f00013484580751001441e46d1100c6a0340c00022400001a11002034a1068840d601d460213a00320040f0200818081d041e03008001c00d1087d0b241078949074030002010708a2556603198034112242000c80300c20110b5400030481322008880d840c0c0c070300019011000c0e480c0c070407640000361a8110136400d240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 749549181 1250 749547931 749547941
    0x3140c010e1e060706182004060602060703020708070b012d0302060301050906010302091f180e070e0d05160e0132030f06040c0317070f110103060e1f09 67
    0x10020b0712200c0701c051070320b0600c4003541054908403011902c1d090322140c401c0c00c04251074400350103256500402192201c9407810101d4814070355000c1c6080c100180145a00050444e41240942ca00142e071414113052442c034500407000000c00780e1047d03900002d080350b0340100d44000d46041070105100c620140625100040191000a4101c1e1050004000510740032058507030014060501600c1c100c5004d000815500c11441246a005c010007070b0012901c2d0300c240c48110f607504030b0444207281d904203641c080a40c207008084108000103d0444900c9407035001964080307503440f4007110050490f2001c1407100503403601031002035180f10400021041481003c0c56228000b8001072801055900440c400000b001d19126805100700d130004111600100f0625204501410b05024400e0035032409408084100c541510504418022540455054485001a280d00610b042d03454585840164064515079011007800b4440f0410030100035003401490043c020f04000405003c0d40311240070b02151 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 749550431 1250 749549181 749549209
    0x20307030e070e010311062503020f210d091e051612021201020c07060201050a05090d020d2703060c020f0303010b0418180c080c06120c1303140c010e 66
    0x20460328010800300303c00200100030001c01510030b80c50122200d0f040c00d210040003041c0401e80408234000024180d040c0078118204040e140074143c08940ca0700c842d4007031a0400b446480c500400030b03c01c50000c00681c000459103034061303d04d14021940e90400d0414109906040e1894014031f20180c800d044a44d00c0c000980741d1001e5541c0858071185c09020509146250407030841d0b500f000b019160400401c0041c00800c40c0c1e60010031305282c0b00c40140241c1c1e001810940c4281d010b480402d290303d40100b0058104c000d146041c4418480e90900c007421560b0640001106a034041804014445960402000e0040a8084036201a4580d100c42e0340d0344024461915110010701046c460710301c2c00c152a203000030318201b0211b81340031034100c420103103d1403a5080702e80b00d15500c4200416601400382002c2014111096814940d8441e441c412103000100500c2c00e00100040e64440c1607018a42e840281d500082d14007082d1110914542ea40c0405094550100c2c0094030809903d00e01170410381028 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 749551681 1250 749550431 749550449
    0xf0c0f040605030604110f0405040b060414011202040f030b0610020c0a09021b01060e040b0112080f03042103060603060905011d060102190b04030e01030b01091a040e0a020307030e07 80
    0xd032030031508456a8101401503940251a244400314021003c409440060780101d0b201e41e4840c0340c40700300310407980c11040c818000e50080c04204007d004400fa030141150b42800c001c000c00c04044002c00081c0701c2d940104000c46038000010092000c0c0b059524460003040e00c1c04035000c2c2440a017645e41e0240c102c40701d0360115608074103201c142074070b4000c1c01601002e0ac2e411041e0000b4080101e0035100340303030807180074a0314060411050002c2020f40ca4010304840c00c41e104840b216460303003512441240d81d007840606000010608100c004421748100d51040301101c51500c011084c0180541800d10400300040d00340300300840c040b83c1c0d0380f0603030341200c600030004101a451400740b21b00c8040020422815030184c05000b032003000740c070041c408545115000440d410701c5d1918015028004202a140c10180341810001c05660042c1030201500c44802c943c42c400e40c0c0ca45a00031380341c481c81d040349500104103001d02241d07814540165018490750f48050047d8003020304455078401e400c1c4100052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 749552931 1250 749551681 749551687
    0x1e0302181b0a050c010e210304050604020910080a1a090d0206010302040c0e060307050a08150d0609080915030a110705210f0703020307030906030e030f090d1202060f0c0f 75
    0x4401c608002082d520006007030007820710140c00300260031210003000000e510f8020400ca103a800c4910110580700100c0a142181542400d49a013591108024030080c018601c0101103070b03807032851405600007048020b0440305480c2452030800300c0c00c010900014080701c1150042519000040b42114224881d68001c0c0000d030301c3c43d001c20000c0c04c100d600c03100034050900142803850721060003d5201d00260b0315010b41d00d50181e0710003041903030010316034107004290701c80d0741c0001e80d0342c0304960040d1508440003085181031030808405500ca00f10f0065801004640c0d1626801c00500281d44101c8451340d042000c41c3c3c201c00351081c148181403000b841a080b9003000301c40c040340000403520700414040040c0c100f070303604010b00c80151f00c2084240c015a001080c510304050b8050038034400b8091900d0203000e441590340c4c8032980e0740116640700c505440c1c00306568085e500c690301c281c503c0719017100c84116a14054cd101a4640c2c3d01595448003400b2030800050080580c0d0080369500e100380d055440c0707 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 749554181 1250 749552931 749552971
    0x191413110d090606050a0806250f0f020f060112020a0906060f27120b1305100b010c02090c03011502030f04300311010b03070e010306020703091e030218 67
    0x200030030784204103c600076a98040400c2945400758484090842c1100901041c105a82c41e8005070b50265500d84c4480400d0a10074042036000d40380402507001030400e0440f101084600f13078100744029003405128405d4900024031035800000e0b000d081c6000742c44815070152122203000c151029402000c1c0881e5481061045003845801d4445001c81000c0400c1c3d440828420683c070321040c0c40e4042d555442c907105810042c0300e02100035a0700300d2030224440400c2c2105554180e20340d5004410060003030382d6110961000d074001c12203081005e5000740f991400d490301c007660b6400c50708280a5803503400081130740c80c00c4940c000800c0322614490749030880d081c64503101d8554000c00e1694444608040d0a04420307000050314400c5045c02c501c00c9d1074031030406e40380c1324045085409810f11a4400d0780030788030410042c1c049a44690649411940150b0307124843c3c1020341d4019520380c03001101e40c0b50a1004031803d01c02c0c0001000b942c1c82262850103522400400721560304081d02d660b6000100700114034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 749555431 1250 749554181 749554207
    0x1030c020f06070c050f0d02060f0604050714130503190b0105011803020d0c0506070302010905061f150e0607031218081209011b0e0a08030304080301090b19141311 72
    0xa03140301e11a6044400c030306d01c0d02d10082d05000d02c068805000d40c3c0040e0074003080040040c0c045522003420b41b8100318034501154010b000c01d06d82d03401c1d540321010009010700341e00e4100b50b10b03038080e00b40038088681209a5003000110310520712019602c088050001181640c0705001218950203134001d0b840410b41150200f10403584100c0f802c90303603c1c1c8420300000c2d90340c444001801e607490003500000303141203032410107900380b00c0002e1808600c0b54292501c1c401c2d08101013128001c0e14080c0010385000500e10f1026907954030b5102078194000c030041800000c00d5840002400c40c2d07040042d0a20903483c011080c0c00c0034510114004111503014400301c1c2c00e021b01d4240341030b8041482d41c0041180140e40c1d03248074564000328482c50010300003c901010a04003005a08001c20401004600e1450551591229400180602c03001035448440241c0fa565462001284801203036801290940da9060700d0b55040c05404d0b5558000c401010281c3c840e1411071280d48102903d0090851505515040103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 749556681 1250 749555431 749555447
    0xf05061e0109260f0c03100e07080319030e060c0f1c02030a09020f030a0203030412110a2601090803060d0f05010203070206040203102c011e0b01030c020f0607 70
    0x40c904100d0290320025181540c1c4031040d108400001512440103821407002d802d181c0e000a080e0041d60000003844819100041c0d6111455140b00700056014210ba0259040c40b455900800d454440403d2034040c20040d110b035880441d01e0741d10200060a84500040e0729400e049500079203c110901c130750088406c6120044c4407071452400184148100b03400c0d04c02c100d030000e4410f407038201c1c1c0d41c031111011414240d21130028030f0000c40c02030845000540c0000d0ba01c0c400d602803200c142c170343c003d103000800c50124464125003030002c00744510039860b551811540c5004802c00f04403c8100d0440600c1c0040602c070700c04002d50886c0c04c152840d5100710a100307801c511503c00300c1d4071454000304003012840a101440c020129940581040d040c20300425190400d0190020800d9141c5241c6401c4041c0c80f20343c100d114a5080d241c50721b03509040c1c042d9801088a0549000c03d41c1d5002294150203210307034004c0039004400d8a0802c40d00358444802c0b65941d40900b02c61605d54040008964000e0182400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 749557931 1250 749556681 749556739
    0x30405010c1103010f0b03010c0504121403040b030a050403030c050c0d0f020703050106080f06010f0e010e130204020703080610170c090a05130f1803020303070e010210090f060f0506 80
    0x2e00c1000492100824215101d9a07081303940e15564425140f07446c1340a00072a144d844951410900701030621844625070000611f0090191035404084a00090240140c500900484800075142d142c000020b002410044604400017481e0601c503a090074090402d543c01d1000c401c0041c182a0441758041c1c4042005000c050198422840b0010018000340a03010240450320050808203d1101c48603140c0721040c0c000d8070200f540700c281848111001140f1504407841c10720301c0d01e400d442e000a8001d22020a01000e50040c2c000501030040c10f4000110038025603066984e620403081d035580031036001c10400092040c280c29000032039a1400e00c10040c0807410b0006040c105030654450005d0403180011081c41200c5845022000e000d620314800d6a07095580740380c03512007032111a03600a40340e2000030080801c0c866000c580c0440e5034801c02850a0310346c0e51010801550486c0d003001b0b155440c0802084490300d080541580d441c170f81030b00525015440280c00c420703501900e007c03150394907400804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 749559181 1250 749557931 749557943
    0xf03082205030f0a0b0603010209011b0204111801090e1e060f0a03030f09051905060a031401081e1507050304050a05030a0521280603081b071205030405010c 69
    0x8000304103540c05100c20040f41100c003000f0403184900c4c0c5000208840000e0116100e0b0f4418002d072009660010b541c002407280c400741500040916100060003080210241035808901182c0300116842c0300100c01d84c54142600c40d0880c0d00e9079102d482540c0c0b00204d4064456200f6080300440901d494040395401ca0001080d103035100c0b90200c081681d070040c40d40107500042da00c280214009420a09a10242c0301c260340205080c583c240b100050300000344603042c050240000c40780000b502c42e501071840f0300c801118440d100d507902d900c5a50307103041c10064030140c10642e070032501c2d40140015840300c9000a0045904c00e13030703a40030410790f040c2d0801031040e030f07160140c1c140780030010f90248020089800240c849980b00e40358440d1440540f18a036901d0703440307441001c0c03c0c44a042d2140101c0304520314030310101084200107a140c50301809031980000c00044001c1581c28002e010581e202c180c41c101c278002c5500c041e41d0799074252807060807013101404c260810041488035510841c0010141c40c0a14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 749560431 1250 749559181 749559247
    0x20a1803110d060f050f16050a0507080a1206090b0307090e0606061e040609030c0b0c0c150f13050910060503190b1c03020f07140f01020c0904060e070f0308 69
    0x2a40100540d80f04841c1c007020b0a14000c1041f08902c000725950000103c0ca25005082405240002d880351003002c00140004030040313090072600307100d2950031007180e000c0c51050003a5540c1d802100081c000140f1014860b008180020034440a0780c480c1e509402d811900a103e1602c4210a1010a40c05655100e5184104080130401034400c80000d000a0030a9510898664610b0070151700d040400d4009031000301041102c0310100c00300250745050300d40100e507a5102c4542c000d8142c00940f0440c1010140c0c901c000c540600c0c10140d661003c4d08884065450080c290744d2090004a080e00341d0240d10301091301480483c540c81023445c0c0c841c0c035003005004c000070401038400000e003180c0e030080d80c4441d8501640e0480d0003096414860549c085004a004110a50400038500e040d401c0c503403a107900406a03040c540340c0c0341e031081050102c4107030701400201030350400f800c141c0060b00c540a03400460303208001c0001070384034220b0280d00c100d9800c90800d50600f490303c00e07400c1d8403030450b08029034014024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 749561681 1250 749560431 749560451
    0x20702060705152202101b081b0d020d12020702040614040c0f020d0809012004032009010308031003050f0a02040f0c080f040302011b03020a1803110d06 67
    0x304024581c40340100002c00120f60200c0918401c0440203080440040f512814800c1c1d590203120b40710030701c90f81101e203007240c0003080703401f2900384c00c8403c500c00780603041a030488244001a4000d00d80b035400d1046629179015071460050b580d01c4000c814034010703441074461100300ca01c904041c41601701c0b1150013516203100d5800182c01e907001078003d10046404410803928a20301881042e048001d2414115040b104440000e9240c030b01c1c0c4210030041c0310351500081d00344002940058194000d240300303541c00f00060f550355616034100d80400c5078080b401c2c9a03018540c0044c06c000f810240401800074045a007165501a21a00060107102e00402c1003a400310003d002070080e030156001e00c000411103004940104016038440c10400c468403440c019440f01a180d100301100c3c0d2000004850303019a8540340390890042101da2400211710079800703130650100d07034143c00500302d0324882e9965000055200d145500020060300c00140300301c00a42075a0080c0c244441d8001d403030fa000e8140000e103c694 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 749562931 1250 749561681 749561689
    0x1d010e0907030f0309050910050616031206060207030c0b041503020703031b23070804030201050a0504091404030807030e0a03260c03011e08150604090203030c01050f3304020702 78
    0x4100f01240400c03815003050081c5e0070108030441d405003420441c00e01c0345240c400450010700c9040405188120804900c0c82414042d01d0030300180c0c1061581041403998408000f0344842460101b2981c01e072207080d0000780000c03001e05032000da6a0b0f100818102840c01c440650007036110003022810305844000c0c1c3d0030340110322110301485181c2600d8a11841320403454191405499000403070712503105100100100d41404141c506495089c284240d461203c0d401c192640c2c0501e62104a0303450074240480401e40070f0280850041d072080d21a00c48a07240c5031410381c29100218400c503200d50100c042c03a004030380300b604207200d103c400d076944c602040364a0069400660044a40e90103a400000c0100803a0f0780000031859011900701c02d0750010b50030144441d46a1803800281c41c1118901404100c3d15031b02c0f0703441041295030090450b03030344518130428580a014212814101c036684000052030030980c120705070040d1080314090440d6141200e0035040540c68105100b90003540c280905001070322 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 749564181 1250 749562931 749562953
    0x1020d051008070e06130e030301150215040302190305040b04090b0a06020a080f0c03040905150a080c03030d110d0e03071e02090406020a0c0210181d010e090703 71
    0x200001010a15240815510030024200c0e405800c01c1e078801802000030020b41e10030603800800c115005e02400080000c40340c05404140500134250100100000364207140a224841c001015000c0d11032101003c01103030740a4400b1a03008c0c1c0560404000d1002da0300384e0305071a5210074800e00700982490788400254550784c0141d0842c0e0b441d2a51100b5480c07141c90040c3c4a64001e00041c4000c00d0b403105160340d4100f0074000c040014544140c00710b807a0750020410300c141d1700a054111030030840b521b801c08a02150f0741107031030501d025082140d408a503480020442c0340354418054010362030721140003000030090142e881d2100143d0018031085015005a00848080e585505c008549480c000e0030050303140c140036000c001a65085540c28001612503030b0b4920f9100f500400016110b204484042c0c450602148000703501c8084021016003441d0060f140e80d12604140791020320342502c401c54040100c400b0301c13a000341c0c0c0801f58010041d02811410b000d0744007074100203079644581d99036200c0300009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 749565431 1250 749564181 749564197
    0x31231f032307020106031416060807020a05101d0111041401120c091505030601020705010309150c110c0604030506040206090d0c151b120305060420030603060717070e01110102 77
    0x1035150401002800915481547c0c03141d103d00142c0102e040c42e01d042c03a40a000ea10544050107005000150114024002d230700c0c41542002c15581030b100c0c6007d214000f400036200885282c101c0858540350881c0500c2040300f514105000785290a040c2682c02031455601e9a071141082181801e200480440c2e0240716030b8000b403070b113031a0880d40c1000c008406040d41e10f0514001c1160610030024140e0340005c105044513000c0c01e0010361000c040c206246030002103078083c001d09080c400c1d405c0426501c085030000741c2c40c01c0700640b1003012080f41082103512407884090495841a0f000c1005460a1001404580c00083c4840666462591500115109613010407080e004442041d0121a04040501d203408081107000400c45081c1c0d907110302d2185011510400c040d9284000f0380141c0b140c1c1d00410900001e00040e0014842010074030440354003c07100300e40a4000c90000c540d204d4015141050304a0102000c5400d0fa641c0c4a401c960030400594502c1c108401c0e40d10304541c80000307200404a003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 749566681 1250 749565431 749565433
    0x31207032d0f0c0c0b0609040f0803090a0210020c0f0f040b1e01120c0206070f1418030f03030c03010e060402040504020a0806040b09070531231f03230702 68
    0x9602e001100022210160245020f2240300041c0c0c00c0062010f5803010352200381110801d100f0b13180d50130714060059500c0002000120000b007803045c2c0150004010304001c2c42200e6654586054400407600c3d800180015a040391201e204c1c01030503d4280c10040c80120041c00c001000581d0000151042e0740a00301224030103901030614405580c04080c50014401101c070030701407084c0f40e1a0080d03407040c0c014003880801940320141011144100b810184164840b998980ca412039035011420303d41c040045030f8400d208080407500c1c00d003404010b13280319040c00c0c1c20b4a070030350f0319140300a0801c4500404540d44140c0c20403010801740c0c1e80780f001c0c08200300c0642d01c1854078603181092004503610003d810740304564510401c000c440d40642221014000c130581c462600b1407081c034200302c2042c1039034080000100752601003190418600c070a04240c80d5045c00003404e10024040c4050200c0c040a00c44401c00c042d4091a45140650803408403070f203903650b8010b10b908191500f5150f145082d2406801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 749567931 1250 749566681 749566691
    0x90911041806060506031501050a171006021507080415060e0f040204050622020d140108030c07060806061207200f070b0316030518061611031207032d 66
    0x1c2c014240b0500010384026118245513090110142c400c44280c0c0424904101e0005204da000728441d1032968081c0d900012405881e05210700d406c0d00b0300031940611030051051007115010850b8000d111402030120303449140141e1034685030101c8000c0301d00b240c44542c03511007a0000b03485101c09061403181014401111042c1007910404c800c0c1c0300c02504540c4500c0e82c0c542c3c1c0c4601e10b00c183e482c062052078403040040e0394603041d038410f2000d080051940015035050000026203004080000d2002c1301c0340d441a034a205484200a65085106540313903500000c09005c018408881501c010340c110b211400e1001c1c0e032192100600f141c1540c41b000c0300740190805841c48001e10310404c401e2020b800c5131001a41545020880200442000c020b0141010b840f18041000540f02489a21024500303500356200c3d49804412509420105e5015100054407295242c00c0240c2c00300075038150b003081d007803121640d032a500c0048006c0d244405810182030440007040510001514101c204280c1060300440d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 749569181 1250 749567931 749567933
    0xa180b01090803030f0705090f030604080c010b090408030103120909091b050a06050906030408160303020a0e0619031e09150c0e03120a171e01090e070909110418 71
    0x484012140e00030942c0381d0042c010303c803511304042d0300503a011038240f800c41d03161266030001a0381c1010f01c0f03000b1501030013240d05001c1800506401070600710044070003070082915160038825100000c441c050105034051005100184009110032410810380c585000d1498031682154211040703140100c0d203240c403040300c005080b010204840001c0c00d048851090301440c040f00907206104801101d031283d140080020100300480040d60034010b4ae81c13070060050380c854a8003038000e510084203100031411004100800345850310403101c44000542040480400c407120580c0605500b40d00140142581c1c10b03881e5640351144079946000d805441d004002d0003419485074116080d401c40002002404048181d4945000074215080511103000c555038880981040311559803201442c00389290030780c24016981c8100c0b0440c071b000c00d00080c1600c0d299a96034900000c5030b829806581d050340043c0010841c0300029401000c025010384240c84807031841000040807a105800b00210104441300084 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 749570431 1250 749569181 749569187
    0x5180a050f24060d0231051809070302101d030a170307030207080304060902040b1f0f0c12110f0c0901030605071803080307020f0721020a180b01 64
    0x258000740d400c030041040b418541802c140140d40040e4168000781c600d00200344544458045400c040340d401c00440d11514403228512001043c0d9078401002174000c1080050220105030410407224010310550b81c8009039045a485100002d00040b041c1c015403e0000c00350300d6040c4000e10048055413611107441c1c10002d0381c6d40103d03162800074065408814060002200c00068010b40700340301c0c1d0420348a50300d40c1811000f9100b0103000503c10b05011043c04100101c903080b0403039443c800c4800b07100054002d0280103909517802009140c420a01c6010440d80d13005c1c046c0c46607801c18500d400c0c01e1030821920741c40d200c14060280900020144444c810103c041406034090301e080440c0a4002074103120001802444180030240190741d0711004203002e14020341407184100d4100050f602c03a6a03403411b0100b0345070021903842016004141c0650048d54020406009840002c405a6130400c031041041a0440216800300e8200b001620089441400d000c2480c402864000f00840c007107490f14001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 749571681 1250 749570431 749570441
    0x7050a09080c03060402040207052812051c02030604020408150a0608030f07080a0e1f14040e0109050a0207022806030c080604050705131d060907080c031005180a 71
    0x203401e1030b0010810800c0c966400b00d0110b81094045401588500075030418a0500e10002c0040200201891040300c0408195501da00410300030030405240b001480b1040d01c2d903100381c05902025002c000c2c3e01c02c140748003560245800c00e1025200506103520391140d00d01e80a00e144071811140441001c102e0a1941c0707020781c1029201040c00b43d810003009800d55400d0340142d1400030f08490f00444c2e860308042c8660748000c1100030082100c01410380e002d040c10a03d515107a400b50002d648050917a00da84074000840d411030302d003000700c0440c903843d206000004100c0500085d890f55000c001036000b59480d801052100919501c040c1203441e43c0e007894101a40c1540c1c005c03000e15003000340c2c101840381c0050f070203580706500395404503265840c94403c5803284204407686c1880d0419942c0403c00b4008490810301c2d2040884c0002d040d91240020441721482c101c074503000007408440001d42500441c0095904007404010042c9040d441d400019046180d0401140b000c4240604020450b01c4600034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 749572931 1250 749571681 749571689
    0x151d061003020a0f030903140a17060613030f05030706020708030906091504030e03161d1803030705130f0b0304051c0e010c020a180902010f020f10180b07050a09 71
    0xc51030881000d101406560100700144140740d55000ca000615028841c00d01e248e8205d0b48a10b503075035060f6040a099280026030142410600070001045401d2480131281c004001449142c203617881c40e924000c03000e1641d0003c403004d000c1884807000003002800a410300e548158040c035200d1920081c07c6181840040206613143e010380360094903080b0600a954100d5054034010f10320000350f6001c40c0c5032240c051912054401e03810800150f003401c402d00c291840264000010817915481038525603c48100400c0740103400c10004200001e020b2001805116880100c2180060395424416a40031280c1c1c40008082400010481000030511503404000c100c9100c003c0c002c048031400a110300740b100c40050601c000905088150354540d0301d01d8008103204018001e604c07281d4100280503018420007240428860882e180f200c900110b55a0084010440240007110041c445c400142180342c040f841480d40e03464141002c03a040c1100c2600c1403409840301c41d59041c3d40b9600a00040250340 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 749574181 1250 749572931 749572937
    0x9100c02100305060f120312040506061002030c1b1f02030d24090c03020919060e0618040b01030207022d120a2d1b06080910151d0610 59
    0x100304c050f94400d000348400560a81c0d1000304140c400b4000c0d4910302c00c0102c8001d501d8146010070040000c005a0107110303c90a81d1850350620844000345d0b0340303002d19003105419401c801490200752504581d03244101d40010245d0a012002d404481c2c4007a10381040c079001030700001084e00c0e030004540211342c0214007010300004101c4060020b0040300015002e4150401d4a07092003201452003074040c6d1340b8070700005080c039500449800071035020005070720860700401c80302c03440020b0501e0686c0a0780e20101046510b20542090305041000030700c90942c260741855070a11841c170158458000f0201090000c030b000c601d080c1200c0307000c0c64040c68400c80240c8a1110309402d17250165000c0394172000c1940c000102800030131541c00c040340100b10f20038a51901c0300310b480c841e028482844900c01d207640d0000d520840540d221002103a030f10381304076201c221307540c0009202001c0e28401d0348881d1007160340f0284000c030561904032650103c800c44082800440c452070030b11404e03240c514009000807115007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 749575431 1250 749574181 749574191
    0x1207020705120c040c091805060306060f06040e0601090f0e0f0604021806130b030702070e070801050a050f12060a0903030f0b220209060307050705010e060405120a030209100c021003 80
    0x800b5440e0f032600d000300c50b00c1c021a01c1c1d1204a031024001d10007040034140042031040903201c0c00194100404084401d82d11a02c210b030081249810540181e0320005406400d00d0315040c2010035491380380c2d0f8040c140d40c0c100194004006944c3c480865001c010300f424414501342803d0002c54105200c0020700464401c1e481009018070480d002800351440c0307001555940d440d19804000c14569054580c0807118004001042000e2983c0c041000d0065134010b0440c0655512048011101c2a0b0240211600b04140c0c803014442454804443e080c030480040900401951090030103091150aa44074031640340c8800c4440b0130075800d805601404442940d0030494030316942d0000300c0c000304402c0151403811251003884100400c40c1c04807402c00d10007070701e03071036a82c00e00765001040c5500040c01036134154a4040005051320780894680e00458010340104010000340640c080d040c0e000c550074005060f42040903030469168580c540380717400026140c60f0103c00d031a005100d0000c26801608080502c1c1c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 749576681 1250 749575431 749575459
    0xc0f4706010915050c070f0609090510061103090d110f06031e0402011103030403080406061401080424060b040801050f0f04080f04050d21050c0c0d020a0b1207020705 73
    0x201802c1c04881c4848003407102c400414006503540d01c81c0340107003142405880c00119002c0d121005440440311999140c296442d134400449088a0080d550510009011341003007240e42d01c41c01440c0400005d420551707180218000c000f030540545218129030303882d040344805c451448e002e40084000407040c1c43d000c3c40d62038062032809000741c3c00040140b0300d12903103000ca015a4032840903000131440c004200c0c3d03902c0c01d1608000c0c1c003450301150101d810a00707100001c21050101d280b0521484010307140c240003038640c2d03903d500040321000c0c0191503046025040e4480410580980f0700100039140103199070740d04003001103082d248020010350107000c903001400000356030000e6040d4810b400c40c200e20740b03170301e441c134030b55655441603a21450384034011751204d50603c109400e980da403440c01c135071240300250340710041a0303070a0043d181c1c074000e80d4202c120441c07104c4c20030760450407402d44010010039080e912803010450710b4000b1149456404214401c204540b40c042141c0406080110b840302c1038a032034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 749577931 1250 749576681 749576687
    0x8010c05091905180a0c0509180612010609090204050601050c071517070203031501080621120705030a090e0606070204090c0e09010e070b09010c0f470601 68
    0x181c0081c42d000d00c2804a101c0a0384030041c0802d00a040020246101600e111120031103010040d59824006403a00c0039050015016004840031914003424080526408506210782480700800554120300790007401d0b00706510030312811000c0c201d0840d0024030b40f002401031000715040148094140b29081004e042a05800a680003c541d08114100c8110034a5642154030701506102641d0070001002400700c41c85c2c011014511818810002070f00d0101507800440e449602500c02c5a0040481c00384d50100740c0200c00e1404288840303108603011a90b0190f00b01d0042d9201410036a502e0300040340c200406540000c4003401820344800d14916410302c03d0014489128080e402441659078044940800580200c1a0028002c1000311449840c24000c1113000c0c281110715100c85000700c1102051007258082038800c040010780d0f80040c0c51800c0c0e558242007804080301510401040044450701103016074a05841446440d010b0140307101003c22030003040601c503100759843c03504c8810403000e0b0f64 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 749579181 1250 749577931 749577937
    0x20a120e0d0e04051e09010b061612211d0a06021308010c0503070c050a020301061418010b1e1e19020a02030d0503180708030c07081216030509190f08010c05 69
    0x100c12003905d0b050380f0b51781c0b801401005040e0305282c0180011030154441c0c2041c4082c03c0e403213401440c818043d445240402c41c0e031042f841e501e8014100b0300c010500c8024000d42e1040b00b1941c01c0607102c0014102c043c032203e14003581c01e50211016600000c2025410342c2e0041d0070401000d000c4001c4c800e070200c200014002d4003004102000b0026146c0e080401e0110070440b016080e90050000c20215071565030304d000702d04c9a034a40038000d031a01c081100505408000b01d82c1200c10340d02c580e60134004190a00c03070004503a0f04000c10388a01c144034200c901c05178040d440c00c041ea50500c907181e9a00035941044009001550100c056401101096016032404520044800304510789a9902c0ea21f00000e80c5809412040f640d03060301c54484042a48880000100347c00380e08a02201d100300e90b21040c05544100d030305081d41500006120884022421010300325a003442400c20074180038403200469200c9420140612200c14506e00411240324050304000c06004080300a0000b14413450780549948 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 749580431 1250 749579181 749579221
    0x10f02060f040809060703080601031d07031103071505130e09190204020c010c03050402040528022802160803040f12060905010e03031b120a020a120e0d0e0405 70
    0x700751a00020304005a0038210b61880c2001094a9151481402e00074140c02c0c0860303041d8080303807810560f1080b558084045070583c10902e0020008903007190780f50502a40094006a05403140450105002c250b0b4480c80307040424550700e41d41c80d4503008c404048410460362008224051100a00a4100d8042903c82c09114100d6146051550500c04a030003803141001d400015480c001400c020194150001030065008070f805100710784884050260800003055104803018000023940e11000071030b0050003501c034440d52002c00030307400c00d040b03140a11801d080c07900060300040c001c0d541d075200c0c21040c00060200d43d401103003454144181584569801c1c019080c0200c040e484503010480a40c03c60ba1415074408028040e9548001c8025175940085c0d90075180103403c0005010301e0450002078031805940e05140e0002038a80b41d101c0d20007944201c851604204d1141342c0150300c400c050083d111001075410051180803404440106100302103412176105034280020701c00c1040030104500100b03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 749581681 1250 749580431 749580451
    0x121006050f220b03011202130e0303070804050c0301050705120f07080c0c0f01020d0501051002060601081303200304060f1107171e0c0f0621071b0804050f010f0206 72
    0x210004807108016480c96848000d030000f002001082001000914040c0103209541d503441081c0301000c1c00c000c5c0c902c01c403080101c030341c814030000d0710080c1b14590040e0001d01980075122948140c0c800f080c207403101140c3d41c80219200142100d5680b420788009036022000c6d03403442e0181e003013005006203803902c040c110114405c1c022904200c000001d1100600c81c40749000219a14042440d04102034082482060310604000030700c1c04c541800802c09500c40c200503903401d281030785e40d00002c2c030500d805128142e08000c0b01040c194140641801d2100c1d150301c4040085844074502940104100f0346d0310092020421004002e030801003001a03282c05a690183c100d0f540c80d00e107004480c0c5804030040c4a102041101080b0408014020400811880c1c065070b04402900201060013601c0c41000f10810082d8543c01210380303481003514450741c22007620329103000000f48200b5401079844119034151840e000001c5c0030001c2c0d290503071181d86507280a0805004c0807002e148003a403140f5004010b0803103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 749582931 1250 749581681 749581717
    0x10030504030e01050912010f0603140307030c1e0602030a051006030b011707110d030b010e0d08090d020406182c1203060102011503030e0a2301120b06121006050f 71
    0x1586d01c24a042c2842901301008025410580490030b0151a45100503100003400c101b08221000b0701000302e03103503035400d178403010f10303030307406640d403035030840031001c4c200100d00003007014240014003c0c0021030040359401c00220fa9801c261038000c041c05025804842030501e8004001001d9070000c4040c807204841004010180d40c402509542140810f40c00c0f60540c050502800490f90300359000c0d00f0551801e0b43c0d8051002c100c031041c41200740c0182ca000c0c242802c1840047c07007501e042c00003a406184050300200d0102e0fa2101100340460340b0610009038580c0781d100f48510105039007120440c140c003034010b8050380b1400344041602ca0001c8403410008400000001e601c0382d0003504103410011089401000c07503035490030000c1c00c00b0701e498600c511a48440c60b00140c0d00003000c1c1c003064044014118a8400c09a5100546400c0c01c201c0c5144a443d0300d415074422035513075642c0078004160030070350941e10318034100007011800c074016001a0140f05051010580c41d41040041d180e580c6981c0d00306140c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 749584181 1250 749582931 749582947
    0x50a0e0402030313180e03030f1501020708060a0b040b100f2304030b0f0702060709140109051507030f0c2f10051e1801270e010510030504030e0105 65
    0x8154410700010072040310708100c00003614076110014031004290002c08104003e030007004a9224230056a40d68182c802010128040e9040c180e440c4c9400c0c0e105004607071450340d90f44003442c1041070840704000d426a07030303a0280c401801c1900410500d4442151140343c1d040c0000d01c003500349c24100200c03108010040c051401011001d50210304591000300c038103070700ea95036481e124010035412594808642444d001148181b0700014101e8050710341502d411780a64140b01d101182070001d4100b8504101030110002015160110b1200310030782c442802d199a07010750b0502901c0c001007200800100720080100b040800c2d000603c0501d20b000003c0c03401c4054500c03204041100300c0c0c400015500c58110700d0760306405500710005100c510001c215140c1103400c001c6203100103002d8000c03004801111891030003080c1d0302c200740d25258540c010300740c0202001c40f0301918803055007d80089290800403c014400752501498040c02c103543da2070b080c405884e02d55801040303d511001290f05209010072100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 749585431 1250 749584181 749584183
    0x2d02070c140d08040b03220f1713090207050705010215270f07050108160c120513080a03121a040b0402095a04020409020d09030e0307050a0e040203 65
    0x102c20740c000902c1d40c3c5842d100c16517098554000d0304d42c0d070381c420316008128440400c090402c02001e074205405203034800141c0c0310800b8900d03201068103d11802085075480443c4206447c0d000f40c800c4203001070b2211801c0c0741152500c40c00e50001819588054090803061000b00005036000e0302c00303615040c450f180c0ca1110986110b409844c2440ca001e880041a040c140004030b1008881d000d036034200070383d11800c00c0100300903010003200001503041c90b192404100481c84445e10301c0410f10744140b4003090358900e4000140d480e041119190094072940d03042c140d101803902030303d003620201000511a102402402508812082070103162607203054462655260b060358030490020b800f40c6081680c0c480000480c0101b83c428a6006008020008008156521104020342c4048007140c10450400c0c030807081491100b2a04e50043d02000045a0380c5900d0002d809005043c00e0302107010482490007401452100034610b000c0e600c000420081652030003814421541c0020b188201d41d19140082 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 749586681 1250 749585431 749585449
    0x182c0f39040209040614131b0305150d0302060a0c0306051008060301060b213616030b01150201111c090f030801151e050c010f2d02070c14 61
    0x2483d0704c5460501d00103410480440f4000c441d205c2150154694000a25050119900c5490b841c0e1191007105046070b030235000f90721080e00f20385180a201040141100043d6406c1580b0b041240142c1085080c0040303c4294000c40c5004011401c09004841c1031601040000c1c10700c280006c10804c54030007082681d1820b51110b400f60050840c00348e9113180483d05c0014000e401340000500302a400005481a02800d800154401c0c0c48100f1a040740d0310240c82a01a00001c04010000d0154030458840c04508843382c2000f54803843c2403401540c58520400c640d4056166603809590500f03141c01c0c601d641031812039500e207400c180700311140c1d07400a02d88801810032035030081c900c5c031007103c0245c02c0c0741d0003051113812130340111540c0c56032038850303101107495081021500140c0840d540c040c111460042d0054403100c0215000060020344450001003551b810200e0134540160201034508070180b88140c0d024540300494040d80b804c4007644d55146107090314030944918184640c985c2540e56518818 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 749587931 1250 749586681 749586697
    0xb06041a040c020c150f0301152010060b0a0c06180c030f380606120f0403080601140405040c020114040c050910182c0f390402 56
    0x8100c0c000a2082c060754644152100b948140001e890112001401c04211307403100941d51078041c11030340f078003c1291001805400203401d0000340c00e4401500422440c100c000f050302d49005200d0b141c59000001c04854076030700841c80e6450104003140803103400000b4250500d5215500041424a00c019001d001e011014000c044041350200002402a244443e0b140d440c060005880d60a080d21145089601b1560404c840842481846c16101800100d01680100041c00251601c03084ad0044006070380d080b01e03546455405d24050105040d400300480b41d00072820f09184c1c808605e1a844e5034a54003440c41040c1c030071519498000a454030039000100c0980a216503d103903820213107840c12000c846405124000c1200c0c1c1d0010f10004410101d1600716054008501600d501c0b14a1041c0503205050000880d6a8a1f50074081d0380090368100c0f45e00d03052000302074500a4200c1004074100006c0e80b0016900d404161724031640011aa4031030802520350b103450641071500030010030b01070b00607101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 749589181 1250 749587931 749587939
    0x30a1a0a1202012a080301080d08011a070f140105040303060905070903171e041e03410705030c03030703080c0a09081b1903120c080409050108150f040b06041a 70
    0x9040405c001a07880514140e82e000c0301555080403121104440e40603003486410010751042c02000401c00c3c41000406440c0d00a01c0c211900e040d903512074202208843c90003404c2c6039952010041807550512800d0040c00c8007103001d1242d4140b00300c00520703422480c040600812140e40400034190003150450f0030349004002d2041588800010045440c1c00a00c42c1400c0c40c1480c28900000d5000d0a0b001d109903a4013442441c1e00f80758220b40510143ca240e15060303509a15148855814003219540c00d24110718500100103ca0a200605082035504d011b01740c0281c4c018850040001d420885d081c0e4000e410b00380391505c80d0080d00040700c080f00c2990114038a13010f0640c40400c9100994003200000c081582e000b4072103d0036884004c241e41d402e01c001342045208448420035184222089101c0300d00a0300950304083d102c110300b804940d02a40420001d60040c0501d02c1051542c0220313540c0400c1707100c03003103545203801d46410060007001408544591381d29540c46640908000845c0415203004e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 749590431 1250 749589181 749589257
    0x51605030301030203071d0a05070302130e0601121a040504150c031b020307031d0301150f090b0a060e0906060c060f0402130c090302040b0d08030a1a0a120201 70
    0x10816a44950003804261301a01607079a011401300e05d0350300030000442000706040b0070350b40c404011000410010742450101502089403800030b100500040c4082d041c510f58041607410040700251030300e044095142c40250800006004008003a95085a982002d40780400c1980e0780b0b20344003001c0085010003d0005150008040600d44d05500001d690312940b00041c003090404201640d80b070281c14002000241d500400624165200d03c030a0102000600007140701e01c10701c0c6815100e41c00300e400c2545040c03c00300c1c5c2000f8420050180d40e828440a5496040260070182d00410b01c0c02c00358010760042206e90040f0310b598450310304484c84000d0351026130ba407505200b21440d424000c162410383c0b1500c0c3c1c2500e14181031a581c404d03054000d0864860004903440c66003848082d0900e032482a51100c007441c2e82030081821507000b1449030151b00300007d10a194840a00f0302d12280100c1280191221201400880d04140d103021107176409003010340b0000d5966500c66904005084a004215164 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 749591681 1250 749590431 749590433
    0xd15090803091c08090318120307060f050c07170f040302100f030c03062106111204150b09130501060302150a08090109020a051e060403080d14010311060a0516 70
    0x8644141100b02852448080c4a00b66400700c0e8a003005a0317131004543c00070824281400c0f0401d00c0c40742004800340c00d40c0c1d044040b0021190a40d00310000503184240c6441e140380ca01c0c006031143c5944142e41c401040c1c1051040c0d12048580d09141c400e02250140c00a8007450046135602920000e550081818807140403000d4010800c040c0c05500b10086401c1c09640200c0314043d01603c001d8800804d06010758048540c04800c0b40000040141d4420343e544888901c405403002c014601840b1080300550b090800780360500003103400c403a0300c1d94024644000b031f11046e07440d000c8490300503c03030200b1440d814410341007003401001603502c000c0d4001d004243c200d204180003c0a004000c40c00d4850940c2c507994190f4850070303100c1602c4001e6021111041c10f10a83c540048540125071802024450140d68800070803940d0f0b0181d08207492100010400f45240321070741c00b404084400c260220501545566517529007101d01282091041d0008908507840c14402d4041d01d10a00000c3c120406070459 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 749592931 1250 749591681 749591683
    0x1511010c030605130b061911010207030206010e0f010605030c09010e0d111509031011071a0406110c070b1e070804081c0f031a1206160e0d1509080309 66
    0x280c070074140070300c19a00c1560b81d0401c4c0d82c80390035412400508400d250440074a50307518044200e4070f000c418819a1171036855034030400d03c040c000e55031190b0020032141d411300d060200b110340014007902880a14000501c50307154000140c981154072144110744441c2242d0040e100380c0e555441040c3c001c0c5618284000313011610800e01d844003825a0910200315210310801003d00c031b0a4411a01a8030900c4004081a8140d00c8551141c070008080e600700a1070b0355502c140700f1000707101c00c400c0341c04000511083c090548104648904144200c0e403401172a01800c5403601150b1081341c12640300881e0002c4690300710181c40e04120300c1504015600c1c50325280c8070b481d075081402003c40e02e108010404040001d913140a8030b01c810300d030702c031095400501c0d4022005000310022074403a26440144420240e11240140081c0c101c0e04006000e00d4a440c0d800383c00484042070b00f410403c0100d8005021a444140c00d070491036402c86219080030421802c400702502d06106c004001080c00000c0180c2464 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 749594181 1250 749592931 749592941
    0x14150c0a021504090203250c02090c032a0406080c1204030f0207090608061005040c1202160b04050f160501050d090c0e0103030504060807180e09010609150302030f060c041511010c03 80
    0x182001f42c80d601806034400c6641c0740c01c1c000000c0d0403903c0f19001c0754110f40030b41d000d1948080c07580902c280d607051001446100700000c0c107445043c41e2010a0078016241c00c00c54640d8013825141000b130428404410914100c2c03070241001d820302078403100c103601d4644280020006030010b06001d00103241d9995070681da031081102c034509407008400010845103030600a10300b1441d0299540c0c4030745640158910300a6110642242c44141138100180c002030700209200c1c4914021b0019102c0302c00200000c038140400c00314104100d102640c03060103e6030701703c070903107400c1030050340c0000384c03402c086c81c202e048400b19410071400d0380711210000080660020007402968002d035038504442d1914007044c2da42d20003841d05c1000c21059094103221844104c11065405007004001060f91580c030143c20080794154805a0241d000800e01441581003c1042e150380d040d0907402050f0504c0c0c0300484001d28000c500444a0440844021b014034030703c20805007690504890080003c3c0d040344202500620f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 749595431 1250 749594181 749594221
    0x304062013031e0b010506221d0603070b04061d09040809010909110a1b0f03090f060e03030304060504031e0c030f0c030905040e01021314150c0a021504090203 70
    0xc03003c60101038a120302c100c458254080c69604150342071000300f040a42004150308042c03e2004d1841a1811400100c24001c0900200000c05550300301c00705100c140f0000c00850080e402450300308034818050040b6800c917009403401c500d1102412051201c01c9114040c6190701044680078042440381c103900803ea501f00980342d4015007a070718070480e41643d007001c079454100c04003031000d411242d02450410200311403407e0398005154080c1d5030506080c1e446141a0001010883c050140c10000395050001c0d2405090503c1000503103c000390f501d01c03008100501d02c03625400170600709805002c402103504100c4048140c400c04030203004006101c0604c050340010030394100007030400e009144868085801d947e03030302540c5080006010150188580d0600b09644c204800f186c0c078040001360b600035181c81615024181d01500c02c0080480c1085580d684200b4200445070501030300003510002c0b9981500c204101d4401807100d04968041e66105c8092240000300304410f140c80b0708a07c2000c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 749596681 1250 749595431 749595443
    0x1c06021b0f06070206040b07031b020f16050307031103010e030a0f0801060804121805030a0f0507050901060c0f2906041d1f0902040c0210140c030406201303 69
    0x9003200c20035460b910042a00c1000c0560490004500890006600140c0c030080d1400d0101b242c00305841e03201b01c042c006601c1c00005800500001884007418020519158544002c0e800d070706007080700103502c82c00144070080401140072504211a102908025407521001c0e06480c0c94080c0f081c4041c0c0054406414500003803241400401d00c1c0e4041c50030f0714000c54001c1c940400000c1c16000550316660314800702503035141104000680303641c1c10080c020700f40b80302d1074012041c0c0032039241c114174004080e0083c2d4421030b00b482c014090350b60301c60031201e1601e4000d900120303010040d041c000000d07070240340300141d81d40040f102c840f061800035000e03501501058504010354803141c102c400d002051411500c610341c0100075a0180d100c003100403404101c02850000520000c550300040845010b4901c0d000560484080100580018400d03000c0503600d1840000b11450500c004014070f200c0103100070300d81e95941000d8081d06101c82e035490310603841d84c0c07034440d602e02510150905034003132448200c0d41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 749597931 1250 749596681 749596693
    0x5060a0c0b060303070309050607050f120903070f12080d020c0307140c0a050907050a0e0d061508030f0a05210f0105120c090a0504051009060209010905010e0f1c06021b 74
    0x150341000001c40d17400030b405640c1d03582004d09040030400f40b40d0108138203403010701c501200c40d8078013034091003070500080490038081d560790f80300c5084c1800c181c040d40c050410580002c908110a820519101600c150300c200c3c3d003980c848003140300f01d0080c003645c01c1c011040d03c00410f00004201c0300c0d205022001041c2000c40310281c03d400c04100941540e40540d9030020500c0c0045141e0b02c1c01100908069449400c240114000311000f00340122200c603000d442c6c207903d0780d00340c0449105c881d00c080040c212203406145480d4081d60342d5030013031141241260800070000340c1d070880d4224104540a89071300c07400d106e100320305003442c5000004d074080c00f460b88205040d901001c8100d400080c89441610050020070f601c0d51441d00c40c400428000b002500d241c061800e040803010302d24810520114447c5000517218101e51300010301c502c1c00c90300158107101d81c1c120302c091180c2d00c0c8001180c01000450300480800c102c00b46801d00d071102c500c401840c0030b0000c28112107103458400c9042c1401240300446030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 749599181 1250 749597931 749597941
    0x3906070804200d06200f1902190305280c0b13020d021c051f050c0708030a0e1f0212060f0603160e0a08060402130c050904020d0605060a0c0b 62
    0x41c0350100300c0380c1507402820503240c0800200030317400860300601d400c81c5000410807030203d1000c0c240e00c0f9421101e11003100081c5007850000d8103580401104603403000300b0341c058400e00d698451035202c0c0c00c05024020082034049000000c0c2015040a01d01c4079001007107100c451002401c00d071001c002c1240d10020030760010300c180107503a5a800007650010160301d1884065001e200304051011120054942002c2c4014003184041000c0c1c039010b08004010020603490458801c105c0e60054612000c907207082200c2c0c0c0200711100280d0360004498480014448a125507041c42c1800d560a200305c0300e03411420303051400e101940a083c410103400148d0b81c90b6600c0d041086929a0503180643c1c5c00807062010030810284068030032003110300ea06100c02c00300c24038000900c01d04130b0350380000714503803018003000f007181407010074680000d50465080c0400845441c000d8698001e4803061402683d0100b802400c40f84035030440e10040001506040d59a074407900c0081000c46901e0041d100c2c01c00f000d01141e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 749600431 1250 749599181 749599223
    0x702010e070302011404030b0705180103060339180b0a0602120d020d06032117011401091505030f090a0201051206010c1703070f02033906070804 64
    0x148100301038030160032400c2c19540192034114001d040b01e4050071090101000043c9040180341c002c0c02d1a0f2a8251900340184800d04803440d01d94100d4100b45c108a03040001407501c0302d0f4507034030300e09402d211410403a002c044166922418021901605401c4230000fa28076540c0e00701815120b140791b018042400c0201c14804c600c10f540c0304410040e40410003820181c03411002070080d051503010094584202030041d141903e6550300190355144149140305459940c000030055030340414240800e07244600309802006003014850130b0800c075400c2480404507849151104040e0485a0004111b007003803400080c01038004640c4400d81550076000300303042040020343c202c5a107a050f501c0d10f14000c041c00c00f160542102a11040c14001c43c2c40003c0c001400221302110500158021542c50749002c41d8018031b0441e044150a0170354000304444400c02904650aa0708c01c1000260742d8240250312900315200040014007031541e000d00d00c1442101e03548000030b180140c1c00b4050101d0100c004031181 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 749601681 1250 749600431 749600441
    0x170307121d0d32060a230423150c030106030c08040c06030b04021b060910020f04030f0f08070506090610080d210e071703030402150f04050406140108070201 69
    0x25007004011400c030f6000510591038148014208403c1e40c40c41854000d24501d420302c181c0c4c20101c52600c501c07a00f40e45c0f60030582103d0000604801464150500d42c603160301e0200300c0340c00002000144040c44103014010040032482455440b0500341c00e03d4192002c6a05800078004c48002034280701c0e040703061794814104d00c2e000f2500000da21844910340001680141413500400703401c55028401013207903a01160004e0b050425580103405289414410742e0300b0549400c8260a44034418412450400581c10a44050f41e40c0550030141e5007055041c0382403900305e0200700038401400010700c03000700800840c0c243e003d00c04410844546858011401c0c403040c200d03020b60310342c0c0da03c20f040c24600d403485449000300b800220030043c1c2c40d80e030129000c030301a1000c5020203c008d0748034035400c01104d042c800d008551254140c9c040c5055040c25030000d1182d04420080501a45021410450040704041160300400703008004000341665110013015141003904442d011805c41400542510b0041c090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 749602931 1250 749601681 749601683
    0xa090b0a050609090c030405010b06070f0312020a0509010c170418180b060d0c05120f070503011107021e13050105030d1d010f12020c010e0f011401170307121d0d 71
    0x80c0360b100e17a5040d1860b92a5000140191810b41d21682c02c040551036072070040680f20f0103007141540c030220909010b01150303100400300c1c144500c1000000103056000050f69184035003480d001c1030364130650604444200300403644000c088000580002d0004030600007a040e64905c070300510441d4510130000c4000d4254100107080010010002120307458541302c8940c010f482007107044091500ca030045401c0201a05803001240c1c000501c2d0b07c0e42d0001001101c0041400310001c1c042d803005034180c604c1501408000034060369200c841c1070740d100d01c40321020300b00c04d034082d103202c0000e821218480c01038031082c440d05000780202054000c185202c2d01c40042c01032680f0700d801540d5001c160046451aa80701c0d0003004000e8215100820312207140001e00b00360f24103d00214401c0d69182e1000e04009040d107407161240c0c584400301c0c06070400d043c012411183c9915005080d120701100d0351381944500305c00107220021900c2c010040c240c000303000b1707801d40a450124bc802e01ca0080c091000e04c40c90400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 749604181 1250 749602931 749602939
    0x100e1e031902011b050a0b090304060212040f062a030c030e180103081e0409091b06140d020705010e0d110a0b15010e0a120b0703020a0e0f0406050a090b0a050609 71
    0x8041068401c220300384d9908503210b001202c9503071080391075804842000307a070702040d10b0304002000c001403603040124040d85403031441e11900d841d02d07100806143c2c50440c8a420706010f0314194025480068a10000e0226a40480060121030360f141c018018421800110041000030054918030700f03206100280481040d00500c0299017140c603843c44682280030061550307100c00c011307440070242083c094001042c109001041c11030891408a414200c40d080303e142455805408012031a40a408810303504001d501c10341e03403044601c1d90440030b4030070144007078907540c01c0c15944801144009180d24540c400340d034a10244100c00d01e50b260316012404400791016a00c20b0200f005071401d1845a034040c90141000718000030520045045424584d1108080428005101e01408050b40d0810f0b0321004601e4214a0300503511005807407840240c10803030103500c1d1026034a0b020303200c503030120014140007410381c08803590700d4048101501d420509a4062095030800040d1400c14805481507e10028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 749605431 1250 749604181 749604197
    0x60711030f1933090c17060a060b0c1509070504020a050c0c040e0a060203060a081c0215161b08030903040306060e0c0304080c0a0215030601080f15100e1e03190201 72
    0x100840c060242035801740c4a80002100c0043c45001a182081d00d41610f503014000714640f0609460480348141d001c400340c0ba00c1000480613104001c1b84880e160840c401c0d4401e115214448807070b00c3c040f407035000250030500c002011075905400030b02414000b201c120455805980c3c7d041070000350788004090b0141548544007030400240325401030342d4040e4002e00441d2015640b404480d140c91001c140c040d8149001c0078004032481c1d410300c041200c5209500c26201c0c00d08210619000a0143c200e200e41000101e0714480044404508244101900510301548a0a1201e8010703140c1d40b1a00c800c95102e4a4240c0000c1c07103c0d0345a9030148548480400d00d030075603503107803a60040c5511009902d40540034101402c2c00507961802d0583c61005905034640d140e02c0c000b00094113045010b005001c1e140b0a0360100311504d03904120b4100c444a080e2807141210089030405d5400c1100042c2d240e5002c0f9a44086140e04041240710300221314080b022160784c520001c8100318001028003029000136082 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 749606681 1250 749605431 749605523
    0xa0905012d110d0204030b2202100c030c020d050c0102150103210203070b0c0304030806030a020d12020c0405011d0c0a020a030e01140307030b1002010209060711030f19 74
    0x781c0e200c4840c4004110030b16181004600196040344d00603007085031021020020b00c400d0901601d94203140d80c0c1056040310503200075070000f803c2016003032621420485410401420144200000b41800380d000d00a81402c215a140007500c480c0804d251038010300c0303880d25103034080858100c01780c1201d8100200300050f826100b89282d120150384000c0741580300401c024170008680905652080f0710040c0001e44a00f81850020000c40c0003034101440380e4452400100540e94840e00d111038243d220084a602200c42c0701d05a044c040340d5000075074010b29103030002032164000364011481910140f4a9689681d40c00d000c00701e05d0042ca0700e40030040c0e00907102d44000038041c0c40c7c4040406414100a18905c1908500048650044910800091701c0720020941030078803500d041d00810490000f542401c0300b0302c010410328080c9100280100318020340751074076900c09000b0340c211040068242d030703818a41c03814591800554081c0444245102060109004d151040b00c01d4a403492441150600c07040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 749607931 1250 749606681 749606771
    0xb03190f020609090a0b040513080a0e13060902072904080c0a0b160f0905100503130209010608040506012408090f01051008150601090506130b030a090501 68
    0xc410100e030420000c0001d0303102541d8980c580c0d40f14491817000410641c1003070050009490014217400128020440024001451081501c100c039606251681254044c003000070304d500300e100141c54405241010106420b03607a81c0041550a02506030030420541040f14266403a070340a160381d440f02001e0010500040c207000080202050400480b40114139940300c03801c00800680e1980c0c000d040e030010380200540c22211042e50340700036060504180389002c0104250a54808000e01000000800103c0019004006100584c0c0141800303001703684440d0058022541501d0544407446602c1c0005800c06000118581a11840d0280e0790740369030040c0700303071150240a810105103000390340c0051141c0000348101889841e1004503402d8a510b407205103800c0010100380300ba43d916408003086440d0b40c10000729411600c058840325600c1c0361010b003490240e411604203400d0144000b00303010300d6640c1c680060b031245020700000c0000f581c1c0030400f0528031781d03200c20025510851040048803940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 749609181 1250 749607931 749607953
    0x60915030f0f150204090608160f170f0a062304030c030809100507080106030e0106143303060f0904020d0b061c20100512150d05100b0319 61
    0x11282d0070101d414981c6110f504140e0b0026041030101550b02d500821071044100000c1201e03840140b14144581e01f01281c0500c502c0c45401018002c542202202868540800401d01c8190446040c0c035840a0240b81000180540c01d107000b0305801e6140003c22801178201d107041c081da40c541c075091000540c81ea0151040032004007640c00034007442c05180c10250460090741d1007000d00307684501540d810010098129890410f4480d0390b03a160071401d0110500861020b500800100c8421b2500e20324070449104402090580011310291400b8030b50015001c040594007800c0100e5848000074060350901007031581c2114007039403100784940740310301040002c40b403190051006030036801001c3d203803c902e2044403d018411030303004144600c4201140302009907080d01c0c80c42101c0c94080c89000c003600800601400368650741441000d0086034031200c4510108003d4079001e4801c6030441d906007003980c1c1320000c050144180c6411301403501403514001c103e11240c200b003845051255100c41d16000b03903101d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 749610431 1250 749609181 749609183
    0x51f060f0e0d050109060c020f2d160305010b091905040c050a06020616080708040b070302040f091505042903032802150610080601120c0201060915030f0f 68
    0x246126681e81035450b00820600c0c902d00810000c10b00710b64503d002012079842d2190310046400540450010107000b24546401d110130f1030140002d40041000c11003060b120050075056807050903040110550803030150700c11a4040e02c0200862000300003403000e00d82007200d110020362024442c081004070b05034800781e04a4080c034800107034941c403070002c56406281600518090f9000e00304200c06000030800111600070a890301c142ca84c180020013400058024000814074848640000c1485100354141c40091480c44941e5070103989d154500d00c01415083d01c41c5100c0000f10b140840c4a0411340902c003991914801034880c00885040c42029904005109c50b50500040000c040c030800884401c1a03005480c850300f21040840d904003914101c208450078a000303071000304029581c1c0c0e071075820502c0c0302c1c054102080702c0d80d00e2400403114000e440030344016481c500511022150f034154001d000352004400204940c0c40e1647e04103400c00480d00c170040440384019088000201150312002c029 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 749611681 1250 749610431 749610437
    0x902031306020a0504030b090a050312130609150509071505070c03150209190b0904020d150b0c0c01091401050f0f0409090b0604020c21070501020304050102040504051f060f 76
    0x52010355448005030380c040084100050000704061040c40280b04800f07401120300002041980d895685550320fa00601c090070f144c6645410004240c41c1d105041482d68031fa020070100218442d502c0c144d800d4110541c10345115070701c0c1100103860440d0004464050307a40c10408010100c10410048415a110301d0086a031742c865103c0020008000c03100184585450381000760716030310440d080c040142e00443d02c105040303151901c2001030440540849075030f10810b5a01680d11030341341580da00a0515076541e5030101000032400038040e64007002901040c000c0e402071340c00c101349603001180c05070201c0c021711941c41c45444100c00a9030140e4010324881c0c0210940320b00b0141510034801d00780e0006d83c40003400a450710031540c2080400700c1595070001d4101d60450909100d29006551a208902078002d00403402c451044829181c0c000c0d20f01803540100203542c0d0380742038a4014081d4000b84190303406a401d120120300001c0545030444112608048103900039440d020f0110313550701890104a041c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 749612931 1250 749611681 749611711
    0x4020a0206360705040b0a0e150d0803070c030207060207050117070e060703090e010506030421020102090d080705070f06020a060c0905040606020606150c0c0f1f08190504080301090203 81
    0x24950010000301e40700ba0000c0042c0604a14200512054403101d0f104941307e504a1070040c01501c1107040030300c0d0403000f001c40c002c207030140074030118081c4545180b01402456000c02000780b015031161000c60b0301d40c0b095080e6280d1a5558074141d03501c4081d03000c0d290108401003010b100b01d8000c0d07050703158071072240d00d4902060464080070444651150710254002194101c0a0051100d40e50090340100b031f0aa402c030303155103415200c10100904d0341c0070030814000381c90452848180300350141e50341c82000400c00c0d451241d035071600c002d80d68040003007100c450181c080d0000b01d4682c8070400e9030451342e042e0090200d070f642c2a91a0001000c44a508030300b4440168000310326915148121400340456030021320f160308105041000107101542030028811b41007180030310800020803407600390801514040a2540742000240544501d00303200300d03989da00c0c046842d2a403944a0300c06801890705100e0b0025a000c8210903c0a49104a40151014004000421040e021a8000d5a00c0300044850580d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 749614181 1250 749612931 749613001
    0x11010204090e16080d0806061602061c0f02340c09061e0807230d05070512010b0102030703081e09280f030e0109030b0702100b04020a0206 61
    0x100711591007281c1a50b552203042c1d1003042026202c004809000d0900080c075503100e0b0024000c040243c02405c240c000d50000c03c11108500e100c14406a031251300414954407140d02403100700d220760622000352441402e00c0b0080c443d0030060300c00c84101e6400d401e007001002001e541140d81002d807a060010000c414814424041a10401502d001d424a00d102003409813402082510b8000e4801c008201d004081d1410481c2c60300018800c4111803000e071035103107210603011040070000b12605a042e008616260100d08101c00811044165442192407480c26003000320450708840c00550140d0140e4801c00020011a008240070759201d00d502846a1040504104590250b401602e07186600e6010002c078807041404038640c2c0c03201d10008020203001500b182c4421040603400b0310050180842c14408402c01d0b4410051030010310b400c00c407030589500304031800030b5640d071810500352003242c5065070000d00340c680b600841301404500d50007045151224002c0c20707000d00038451208284103107464190 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 749615431 1250 749614181 749614199
    0xc2404030e0d061802040f0c0806011206120515010614040b160203010f060501081b0f030903090d0804050102060604020f0d0507030f0e0c090601030e060a02070c0b07320a0311010204 80
    0x4041207202113008a6003848078414001a601031b040c4008005003014092a0301030f50005d0313015032191091070008114184000314100601040c0c0189000c00540c02c003417003d2200c0040c558105000552054460703a03640c2400301c42c070026450a210894204101c104101e086150103031180b0f109030498003d00795000c2e8000b0b421510840210152562956420040340da08095a1940035540000d01ca501e0544004c00c5101442059058060120080302107031000303400300260f95000002420350300c080b440c82d0600103001c2d0803511a050040c8100390000f596410b0030300136240c0762401d1040c05070030032000307032008005418001c041d0303800c06541e4141c000d01072455020304910a62881d025080b020240f90500c01d002c2030040c4040c0c1814100841c00441e960009103031540701801c3c901c016102c80741c600d0b0100621007254801003e804e00410864103020656030a06229040c1d610b100c01c1c030180095084410448643e4001810307007154802d040481d0080f51340c2000e004c071701c500040c90320303884034810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 749616681 1250 749615431 749615441
    0x7140715062c01050609130513020312030a050a15060f02010902060f07020a1d01030327330f1d031903020f010b10050f0c01110c2404030e0d06 63
    0xb9101e802c05207041d400081c035882103041d000d040c0598100785400c4044005c01c0700e802c4c401c1e400c0c0d158180d031100081c18130078104c0c4005100f25401800d03250305a50100e1400519041644e03031401e191720380404102c80458511820101c04004101c0200c42c4d807424001b40c440b40300b031484020955494240c0007005946070710050000f004403051040e120300e100d0041c030610380c4e0640c00081c00c0c40c400c800708074007081c4000c07540c6044960500c7c0c000b05401501d6001100c00c00503200c10611006c00810106042d2441590200412035084d1004010744a04000c1c0881007811420880031410101282c0080d5104102c019949104411502c080600800200c4d2510b49030030200200180314840c61020164148541c02805c64081b0080c00300106400028206603d20240c0505000c0300060305240e144101080c1c0d4040c001d442c000f0041d0720701d8039400300039513889030102002600480ca0101421098161101041c0c1c80ca4402c108541d5600c2d941a103a0001e6030171301d40c0d48201c00004400c001a154021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 749617931 1250 749616681 749616719
    0x5180c0f1302130303090f0b03151203040902030a020405090f13110307080708010c02011401081209010e04090b150a030812040309030f0503040f050405010b031501030e0f03070b0714071506 83
    0x280c0c80111f840d1611102002046400400d402d040400900510313141001c417180c54100c08850300114121041d050754074510607a80b1940003d4008010010807440300c0e80500f048402c1610048466590307078041c140300000850b82e6050300c0c4480070b2003c0220380710b18070740e581400000c1d045559107512042c0d1280b91600a41c01804203a4460350903182d031030b45c28005c1401d503100005040a0750350500300c0c09911200e6101009605210215401c1507a030700c1520031f0890400050020403078001300b418605048081107400d00070310010080c011240b402c0c02600d0314210303030300042d185042c09845201e900a00d030001d40290208441a10003002088040f001c100a1902c280015070b40c9515040d00008615041c2d401984198500b1004010443c108030407640d00c00350010102000d01141c0006a00418110702c0c0c83c1d2862050303207030020f24100c0000041c4000b0b80590f81c1c0f02070a544004007200c0d01d030140d9002c405000424000e0000041401035440501d00b20700c04003080fa1600c40450408001402c88 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 749619181 1250 749617931 749617937
    0x1804180803150a05011d0103090204090b090c06131a0405041b032315010c150903110105011217040b0a030603060b01090b0a181805180c0f1302130303 66
    0x510910390080b0a8141c141e1405503888001e83c0e00d0400040c14607074074003d0906825851110f0f07104544e2203580240c20302c1d680240104564040e50405140d4804100d42e2010644200a4000060b1030040b064a006403001d458850b00141801c0d1507044820012280700440b840600002c50199100e0180f9411610550380300d0301d1599032010010203039082c2c51a40740700c0d0401100c90140380d4456001ca140d00810604007004a0300b9101c6c01290401c0140c400500300111900c00c542c1c40210720b4002c0c140c00c074000e956240b403403500c0c43c006070308a880170300c15880001c2c106540000051048421107044014203441141041c2d550b24040300554011400303000026900d000c140100402403040b0f010b03401007840c0010201d401c0c0400b11060b881145108410b01c1249c0902c04d602c08480b805100250592079400c1c0520035044e01c0d6103019013400d950b044441d06802d0f412000c0c04200240841c8041c00003020825860300c4802400041d8031189a08003105400f0440c00744c40302907042e5207800840c401c0e9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 749620431 1250 749619181 749619187
    0x902120f0114010b03040309060e01020f011401082503030e030a05100b1305040c0b0c12070f0209160f030522030908060106030209090115030204030b10050910080318041808 76
    0xb485000a0b50580003200814428030600010179400b0149000b950b07414140f0203c11240b10006074580b83c41e41000280303541c00d0041050704881ca80c0034460484a00c001111544d9892121416041000c0744141040c1c2c01c1c054810070109211303005100103400054182c070144c3e250b0b0b84607a82402a1101d48005194449254944c0c80c10f10718030481000c1c001c3c000030045814641d540c1c0c000e018035442480c426400228000e0116102441038890300c0f540d005080343d895000b032401208408500310141d109125140002d8012150743c8040d0451240c19528144030204084c1d0540c0103040140c010400400c5003c1d550240e00001c1c03203200e003441d01a4440d280740502c1e02d2404c07440d010701600000700b05030050180d03030720540368900e801e4155a00c0038080c000e246811a403c030000d026035800505048002828400020014255502516003e4940710241d50307880e030001070007100c0b620460181350720400010b01d2080021444000b5014028030100d1254580c400c04503200111403421303901d800c000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 749621681 1250 749620431 749620451
    0x30603070e131205130609210803010608040606030b010308190504052b0c0b070c0b030f06060711101206050901030b060d03110109030f02010f09150902120f01 70
    0x104103000c02011408800c000e107160050002019403590003005041048102c600d48645005100b594500c0c500c10408900256440c1c00c01851021940304480e1f4110060784000b0441002c804842c13a40d5400c621214510791030000121502c4200a200352500c40d640c20000c000141078405a42c001c502a103a2191500050b40003003032185003c50181c028000304100c10055501d60f140c11320029208136105901071f110156040048200f2050000d20b90300071403c0214440441c0303406008406d00440750100300301e803500c850400e1341c80281c0c0c2e448805400f840000e00700e89080030040a41c0c500c00c0c4848500785101401141c19110b00e41d60000105000b400d15550904681c420300004043c129004d0341300c0d501d1a1142c41c2c0302c441c003a145c1c81c05541d001441c4002e00d03000320741318030b6900300d1900200700e0510103080040001500d2010400194202000d4400c1d240441c0509112281c01140c00d105c200c61442d040c1700103008110741244c12604240d03004007500e03400d00560000e800950004511100e032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 749622931 1250 749621681 749621683
    0x90e0a0612030c0b0609150d08090a06030c14070507090e0307061a01030f0203360f0a1202031c0e0a054804050421090303090f23061b03030603 63
    0xc0996001ea100a01000b0680e0b00c00070840c90782d20b605a1301400c4000e235900342300416218031920b507504904a400700241c56030f8164080b056411150f940ca402c00b0408010130700c2c4501c5418400341c001c1e445100148018621903000c10040c0d50b0740812203141c84003a5642c01b040d240d002080e00380480c1d659281c00e000356003501030f16500c0c0f18003480c00c510b540380110b080041c00c50706801000210504803122010344081c00d83e008101d010190444040c01d144054581d901c0c81d856200302d4030440c000001c201d855000006985a0410400c8220b0311448800041c42c000c2000c0c20301c852552090742460004603400780301c80c80b4281401608003541103c034044405800351304421003001040c00c02159005030044041c110201c140071507000c166074486084c0003240324081d0040340500b0f010703020b8000d031094000e9810000c5900caa21213001c8103176588940c0c0c519415500c00c1244a0220b1704c10307030200c040f81c032161045008008001c181000f444102d01c0018400c41682401d450b800003061000500d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 749624181 1250 749622931 749622953
    0x50f0a050a0209300303090102032d040f0510140417091c23060708010f050a0603020c030c07081f150b07050a0b070e040501120201090e0a0612030c 65
    0x1004a4041d0f240100300310114104480b0803900c9000085004840c2c4c103603d4079041d4020744402100c003100d4803800c2004480307000394415203071180c0c0c10420010500808008010200c0c40d81561a00e10019641e40e0f00e030401241c0d030412080710240141161100c0d014007510450f41c002010240b00144e0f45040e28003000b100d5500e04520910450a00080742c440d982c40c4560704481d80442d203030660f428981d01d080500f011021021403200118055542c240840009029106142035501d521469980b08802c44240c0d0a40c05080c1d00051068403d200c502e000e0b17001088446605c404980c0b91805041d00d040c10040f103904500016009175680042003119120100d82011203180704112154201c952040300d801680301e440720341030000c0303038102c1400024003d02c2c00c030a0300b09080040700e18018400800c8261030441d00d034445c3d80f0301000400c00c151240d070401c00356941a1107841100741019080010614010000d0820940381c05c4042840341042016109491207038032a1055001c0618150907424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 749625431 1250 749624181 749624191
    0x3020102101b050c120703081e0403091707030f050705150301080a020d0f020306040303050a060b0403020f0603131202060a0506030303060321040b070809030f0a050d03110d050f0a05 80
    0x90920700520344210005150404001031400c1c0f1070381e603603800d440e910b0a2a8000e40d10341c60116020a40304180b5800a50442c070981d44407418140740c0c03a00289880e00e6800c103403405800100342082c04c3c00301b00d02d41070158880e0b00030b4008a449481d5070741e450300c8032090800c1d0200c49a070809031003084541000510700400c02444102e05096606085400341c0d01d0092034000383c420801e558142c018046222400c1c240c0c16005816104c0340e15003810054040c01c001d45864002e10f00c0c0a03000201d1280f00010f99080c0d940c002c16102405014104124294001401c0a003000d45101a0700340000d0ba40140701341100480c0d00a801c440c03a1041d000300484900401607070080e002001003000356a0089080010700d20811194803800e5201c41001c0710310f00983d00315407030071800003446c4c50901c0100ca000d0401908210129044022074505094031b0700407041004009a204800c000b00840c000e405c00e414110075000d48504020302d1000203010366409070350506d40755208000f0320103240d00305d0040c15402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 749626681 1250 749625431 749625463
    0x1f0305090d0c030c02043b0309010e060f1308060f07091d04080d060f03021e220f0c1808030a020a140a0c0f090b010e0d08161b03020102 60
    0x80d10001c035002d0649412288001c00300040b0456800440d51030381d01005580001e86080f0411034008003207841d000c803102110815600d034103240c4100c074105c000304890040c0d206a4034650142c14003018419190421040b80049403828000c004454109030980001040007400034400c03820500701c04a40031501800400400103220400d00010098200b411100d811152031320040e540c0b907060000c124000d180f148004103081c0800006c0039134103d5911802d481c006c4445100d07410725188510041900b40300d18030740113800384403550050264041c81c07102070704031500081030300300409004204440c081421140400c0d000e200380c2c04d540b030203045c0602c094054200118a8014420f9002e5960450242c004200381d49910424284200601245c0b403036540c008441c0103419114150750180310300b580100f206c81460125840f40540c450900500c01800180c4650a04000e50303c4191841d4007006a20025501a2000c1c10006000a030016003600a50f0301c00300702d540c1584002418508070914003451 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 749627931 1250 749626681 749626693
    0x628031a0f07120b0a080304030201120e0a080d060504020d090b0f0103050c0f150f1e041d061c06051e10090e100e030a0f1e050f091f030509 62
    0x70714400c494005503a03050070480c910380c800403030703025120b54518960000d800c54400210100004040c20a681c0300362135040100103540d84030000c681190030001103591000300e894000c10340703110040403040300755a40403a1441c1c85e20301040980c0d0104054043c1655280103040500c007420f040c05400c0802c003c40c0704030340c1d4555203c0981d500324114021f803042c1050300e07014400c1d44c0e580800b001380912040d000344c0c441100d5000042c2c0c6411114480150740c1d05c0700c0c060304541201700200c4094841c00c08009252813924014952007140c000c14440d08030034001c1381450800020750075040340b68030440d800700d49407520440c01d2055111000b1102e03015943d5206218140402e18031880c01e442e1102000074058401a11181c584042c0f44c0b40e0840d8a445e040070500071260100041102d94520788410940b0844e41c1c00444401411101d102945094007003d002d000344500014031040080c1c402007418011048001002802d0746804603244d100c0b14002c0c0c01c100ca030907005580e4000b40b00c4c805000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 749629181 1250 749627931 749627941
    0x515041d1608040309060809071d150102070b0d0f0608100905070501180504090512070f0519021e030f0f0601050301060f0302180403032306090c040b040e0628031a 72
    0x8917001c4513000e03400a21881000050444a04014000051404008900c2840022001e00c2803240d03090300d00703481300082412036004a500009200b02100c810b040c03928a0081203041c6400141103a108040e6002e460703000010b8400000c010002c801d00d41d5a10015090301545030440c505070076688503d050059000c281041c80440c58802800c444054070003045030161880c02c581007600402070400f4100e0042102401c2c1710198484521aa104204840c205800c0850715554512040da00035031040640c0c01d81640100116100f901011019044403160400ea54580c0d00b40311081000c85006d0b407103100100681e00e400d0088030001e00801c83e07004052811174001c1550026000000c101111968002c41c04042c07207a4014215000e085480c281d0041d050a5040019501610340c9440b0b0041d550204284660f031800b2142182c0307101c185140b40500e81040c1d80b0444500a01d101d40c092031a0f04200305106100101400a000030b0045412560852401d007010300c200104030b03450041c0d40c80c1001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 749630431 1250 749629181 749629187
    0x507180612050711100f020403021c060e0102070b070f180b0a0201050105090603030a1115100e06030f1c020f070605091f050a080c090301090b011805100515041d16080403 75
    0x171302c4211101140e00180b501050020744680e510003174000f11603000e8142e0203403440c48800a49403040340c062240c1d081c883c01050a03406400000b41c4940c1c85100401c903198006c00303407000500e000d81043c1c6458842002c4c00420720005622142c09000002541c010060b8284030710b50240008903072644880c01c0610100ba034074010510315505204184403551550241000300000392401075100120b01d242c003810543e922800c1c0d21401030f080c500400071403100c4c0f0f000703d004a60010746000801d1203070b1079180c4094103030100004e25425070250001501e4550b00c04d02ca9803005d0702e050345541c1e41d14890b0302d00f4003550000a480468001404c0d04211500980c054115401003800c1e1412040365100e0408190040c410b01c1a1140e241d860110b080c41000981c00c0c605048445c1d8548110310140422844c42c182e9404540140c02500740344000c0c401352818455010401e580c100085d4245616030a01c081940d111521020004c800c910400c142186c03588000c2020011070720348641c3c0c505140c0c0e005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 749631681 1250 749630431 749630443
    0x105040b0c0f0c162102090a0245030a0510050c090d0620160f064d0a1220040302090a02030115030507180612050711 52
    0x4400400700051040c0464016010340310110341050a07111030100510102c1d100403802d00c82c454000341c0e0034016a100c0706008410300e0906801500c0307002d03165a034600502c02544410036602c41c01e400f0001d030002080c0c5200d08005004455118444000203983c2415440c04480050768800d03480b8414540004070042110018240e880f6800706468030b4040680710940254003286401100545e400c105100380c9804c80200c0380c004100d0f0050340a441d01c42c42c95140300345035030300301d0304000c40c600c000010b44030060782da401501990700065440c3c10b9440b440203410801c400302c01608201d0f44414000350300c100e45107c03d90f24810104000440c140c83c002003070f010702908001032000c031001007029101c00d500203909841c6003041e06460480203410f002019009404142c0c0294408800203000c0170301482100d0689142c020200c0306454280d03401c4000d004024845804c1154003403c0710541815540083d01800c0540c40302039806001c400354500310360004110b801040600903603402c01c0c100101e80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 749632931 1250 749631681 749631691
    0x10031107110f220b0f0d08210c070209042a090506010c0c05240a090f0819020d080408010c0e1008070f050c031903020a1205070e1221090102010606020105040b 70
    0x404a00c0c9130305100043c040c2000d804500342c1284501050404004115004145110b0300c80d041064181c07440100907042101241c00b981d074080c0c01c000610252500ea014070b907010340325841e0180429800100d0b01d0001c43d00985c24200d03800891024003807443c04d4099150b00550a03c0d002d01c070b4681d6a04c4031400f002c400d1280324000e00d0b040980940200c2240d8060322a03403d0501400d5888486002c01802c038880391064000e01d1170800404100c800d4003107411041001389021910078a8295000c01038000c001680850350400200800145201c00380110300013455982ca410318a0a00002404200042000c8400800210004010205402484032880080585042a1220355070441d4501c0c0d842a103408002410400e41404201a0b15800501203d01e0303c1d81c5403000c400269010401f42c0c0c80c01d445500c04101d0114005505041c2181c0c000868141441124000624001d80b04002040074050b403040c1800010001d0113540c0900501c0001c1c0700e1403000f00560318180c0c45071200644003901d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 749634181 1250 749632931 749632999
    0x803010504021605060711010e06090607030b0604031401140c0c0a080d0b090109061a0c15060a09020a0206011e050a0b0d020c0609070603110a05030610031107110f 72
    0x38901140f803190300040840658040100e42d40343c200b08101404c09031032002d0204140d03007031420280b09a000415824000c8980c04014502d81c0c4801809502400002c5811034000743e05010000220b41c040b040c009901d200203000003072542c244940b280c111100101094080c81c810032100407451000103000404d160040001d54861070060407100107404a1490150b01404060011807030309019448103080300d2183d000ac1817841581503000c0a0b6000b40c0d4400341c107507044010440030542c2618040b81e481100180903464058690740ca4404a811500d00030005900c284014042e641801d04419410040301124106c1c0c3e83c54400002d20008481c05112009030000c2a1b51754922400d406580381c1c02c4011041e04c40c0c1e40707090045660f48090601c15040000c1c03c040000f122820b5103070450741141134564826145554010a00001d0700d1004001010150b48100402049000d000540841c0e4410503c00700341c41848410060781c00e0420301d03401d1084510381040f00c204a1200c90240d1000c1e0892 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 749635431 1250 749634181 749634187
    0x7050306031c03060506070602131d13020d0b0a1b1e031104030203060c031506040311090402180a061d0601020a02120a02030304260714012a0f02011704080301050402 73
    0x10400c40103020590b101c00e4101101081003800c10115401038112011446400b840d13180c2d13186c504501200c10700506101040107880801c4cc02c100c0140140d000070f002030701c5041500c400c2c0d0783d81d19071a5000c0b81d8000415650786000e0036085011114007003070200902e02600b200d0071908501c029515a4082030060540e95210002180009015500216002000e403001c51401d482c88101d503500880b404002c0700c840f506164800c2c6081d07002c0e1400c0d280c0002a15220381154400c0c0184031101800c240c0c3e004601c0031a845800c030314591100e124800508010409030f203401c00410450407070702e4100342010503047c200811a40c3c005540300380b007901100d485080c2040760119a051207000c11000c0e4050000040115440e01100080d6003c000a04200d540440c0724410399a15940c01e8040c001c50070441000c1c840c5198410b2580524154520b0348000011a0180c8640c0c0d05030f28252086135400398980c0090150742c0c2000340ea0b410407074402c54031440751400d0340e501d48241c40f0500400340302d03603408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 749636681 1250 749635431 749635483
    0x90e0a05030c0a030206070305090c0d050a020a080d1421061c0b10051008010b0a181e1707030206130b0d0e060a02090306060d020f09010b0c060705030603 68
    0x1041648601900001601d540740480301d42c0503101c0d150000c00b940544140d801040446200e0f10a5a100d40d47d402d018194010130441005002c0250900c00c3d100c1f4854000d4000c0503075910980350b0011301c1008024200c0001010000c0c20390704c2e12540300c0140031014040031105860314943c2d101204c1d805254000280c1d24200000c2c42d808001c0741030603d030303452004991700f08143c8217015030048041282c00310310702e81e480d000c00050840034902080050385410041141040b00806003031064414100750741c00e41038628a0070b40c0142660f000b0b8626103001117500900081001000022f4843c000416403950a6000c00c1544d0701d010303220003030040301d0000f6407010141c10700c6007482c050035030081d50a580b8204080700300080c01240c00b00c400f05028100c00304143c42c0340ea20844110b000301801404099a07108208001c45154440c02da802c013070f0050501305941d40e5888010302070302c414050f09807624801d0300365030300c0e102e4001c0015042c80410001e01009540000c0ca844000c07000703036a000101c1000e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 749637931 1250 749636681 749636683
    0xd05070e07030e0606150a08040303060504020a41030603120a020f0c010206070906030203040f02280e0408040b0d0605090711161a07050a08120103021c020a090e 71
    0x540c0d4400c60240611000388412541d160b00000200c5884078202d903101c1d1150803c02c00c40148000212200f80001c00609407418001c0c4002c0d50701c40e020b4200010903036030380c0c4046000da030b10820510b4005003000e841a4600090f08155401800142607080aa8008400351568113114400301c045580c00200010710700344c0d000c06c5100e1442d01e001d8a0a6100c44142c070005c1d50b15100c01e07114982d18002e460004010794030005025103d6200b07685d0341c41e096413800300150001c0d400a0b10940c0c10703000150f00d80016848602e042e0f800030030340350300c584031458607429001c8a40340d5640042c05110b10707020500020501d014203880548030781c003002c50342d1069140e131081e00070501c0c0c2d40301c1500080003500700504150031008002001c0021801e0390b0b03000814421150400880e800740d4031112090555001840b0319204c050300d60144210b04075640c01070661200c1201c1d4105680080844001400501c00c600f000548010650101c1050442503036a0741c0c001800c000841c0100c0e0b485a40d14828040030f190 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 749639181 1250 749637931 749637943
    0x80307200a05152a06091513030c02040c0507140c0a0e0613110c011104080d11030c01060308030402040c0f20070f0e0130080703030f050a0c030c0c05030304020d05 72
    0x9140e0b554a01135102c0040304800c40304034044050264001c01d0006070b1a442c001c0344403c10b283c84010b81c0c0c1503645c3d8003020388000b00110001a0304006800f200d03a40161034a205c1c940c2102e4250f194203494213140d103044104000c521031144d807607400140345805243c403114895016294210030000e0282d9480c1c0204d50744501c00343c51a0350700d0341005a4201f90169210052400c4a101402031282d00d086801040c698440c2c1d1051203040d5014020050150b0300c01d20344400c0040202056a203011160381a003400c4d241a0b41007a20301040000038401145031a101d42001c0b101e940c240155025501400501450340d01d1951074010410405100c0c207245040c01240082c0c10410307040104a505e030440800440400d0181c0030620a41d04884290100160401c4809141e040b95000054100b9a40e40d1415000707204102d0a01d038a9110210b5020400e002c0c00e0710481008000003611940840b00500792156a0b510000340074101d18100045071004c003c40e039100c0e406a41011484420745811454a2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 749640287 1106 749639181 749639197
    0x1202100c08040809153123060408010608061e0103050303040305070c050a031401051b04140d0b09032d030a0b19080307200a0515 57
    0x407980b00007400c1d2458080c00e8061410304070119400146c01120008402d5252480b461540c20484c42c9400d9201c0c110883c4440454170305070606801490880007001580c41020141105890314401c6400070112036008102c0325075500484c580307803c0d0580e9150381540303086182c9080c044a19540138180c0e500310010310b18503183c41d0b07400c4d50150300400d000c07901c0d041d1518001507983d90340b5801c01c0082d400303650550b948814080045d400c4400050018420200c0807034050040d00e081025241540d562401c103041002000300040c2d161040604000d001c1818001002146200400034042c44040a9480d5081c0100e03504d15482d1000c0e01c0c54000340d400410301c00101020000e80103040b800c10060148040d1900801d8220b24141143d04500607a502c006904401c0102680b02c1525142c102024118070700c10903070002e2401881e40c07090071301c0f5590380a902035440035a030048402031 = true := by decide +kernel

theorem cover : BRFrame.Cov 749460431 749640287 := by
  have h0 := BRFrame.cov_init 749460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 749460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 749460431 ≤ n) (h2 : n < 749640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
