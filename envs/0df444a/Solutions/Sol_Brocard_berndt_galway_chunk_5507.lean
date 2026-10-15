-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5507
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:05:44.489981+00:00
-- url     : https://prove2.me/submissions/0567e777-dd0e-4be6-9d31-1f6701b45a21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 990287769 ≤ n < 990467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 990289019 1250 990287769 990287783
    0x3150507020d050f2205030d05070c0b070b013506060906120d0e06120f180c0906041e05090a0c081b01142a060f0c0a11010e03030c07 59
    0x144000300d80070300115800c03103850000b0a032429145d4052401351700180715001c0d003166030b000d802180340d03102003040030310b9011070b81c40f0a61030303007001e1a200011022a0700004070500040c4036a800080d071901016041d503240c038080382c65940c0103080519450384441003a0816082d2001524a503042c040b602d2406076800356200800d40c1d035404180802c0e03800c01c0a102030b0590001c0000d100c1a449490080030704036000b00160f14003414580f041c50030f80010350380742645403403610a21402c054460030b500c0b80f520b00200a091080c0003000082c000c198014480ca0259841e80da00311152a03003c04075003c900fa0150041100741010307298a0b64902c00c80f402180c030070030b102801140510001403c0034000c0620003410b001d103404007004648540300c502c1c80c00e280d00c00c10b10000d10703000d10300c0d98906502c0f5a408209081440106001d514050020300801052250f140c18407131403400010403035001c04075909140b008595003ea0480c010007441001c1080c0380408803d000c0350441c0d4900500115010f149 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 990290269 1250 990289019 990289033
    0x90e0c07030f08092d01050f0c0412140a06061707030803040803061c030f020d0504050312091201020c010902010905040c080417040e01030f0c050109120f240b01020709021602060c070315050702 85
    0x262302a030600259050744404030140010080782000d00d00620b05248281c40d114078404c4c1091041c0c2c602401506c0c102c66168545030700380300c1c140702c01c3d8408a41e40e03103078802420542d185444580052102810162081d1800000510a07032602c0c11022020b1840601c00b40c4a17442c076040040c203d4001c12851170050144496050180e03103e0390543d000c0d11801000780c6403243c0c02e070b05a418203522034a281a000308801802c1601d40e4400e101801c280c0c15135a00100b145000d030300c0014564042c80c0c020074031072807501051036411588400740039171281d40f002d0034100349070100c29a03584500841d4081081c80750040008010080c522041c031710014444c00b41000e50b40e844200544020001e800b40d9030f2842e1f02c0c0290000803485070101c1c0701c45280a821019403184498503001c80580780c0c070f004c002e10692030b08180c400ca543d04000481c0100143c1204600b485512040802000b02780500031788500000300301680d40c0c41c41400305400030b41c0e012031004560315401c1c82030f00250000711741c2c10026001d040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 990291519 1250 990290269 990290281
    0x27090b041107031d1905090403030e030414090105010807021c03271403030c070f030c0b0106050304150c0e010c082505010608032803090210090e0c07030f08092d0105 73
    0x303400350701d24613000a45e0b038182c00e040612252480c01401a401c06840d05070a2190b881c0c00d100920281000c29a80c42c0300061810a01800c2001a88001c2c10032241c18104440c180d40440d1103042200120203a001c51807036054110080c1c5542c11482c4084000c0502000100b0300c050000149207202b21140f03e03e166891008a860340000c4400810003141048214002540e509030707814007d1190910040990b03858480e0942c44500360080c0001c580004207210500003061031280e501d03015200244000e2003080c80c010000100201100e06003c440d075103131020080d140d01a503160302c1b52040c9008450900c3d42090102d003001001c1512154078003a0301240f070300c0c008006c4982c0c0140451440098015042811a400c010020500105950380f2a86001a500c40200b0811074542d5605c10b109903041840a501007040503085980d0243c0412400c0c000981181c24100314200a0501000c0740d51500c4940741040d004011250601e200c40c0751041c00c02c404641121414141c0c0e50080125036108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 990292769 1250 990291519 990291529
    0x90806150904080a120c0503070318020f060d09050609010203180601030b0c0d090f080307020c12100c020313081b040c09051302040b03100627090b041107031d 70
    0x4184407504030194400090104550000510012040d403800481e01403912a100701182c468900359030000d2000002e20220315418042c65104140000400caa4181c1c2d0f60300050128060107841c90240b42d0204402d0540361542c3e11000d89a80c002003650701d503190420802c0c0c000c4d4006c07225120101c4861b40110000d00d0b001403814183c9a0010910506445544040480746c115150482d10306450f0210300b400501082840c1044d20301c40c1201507168105002e001e420704405900541c01056071850f00b4407032100015205809041982001441c0001d8100c12400c510503140300e0900c02c1c2068000080c01c3d140056807000390403181d55040072140c0d84108000035220050014000a054450140041d01c2c04225010304a0200c5000514140e40e0f0080a0706a03001110281c40700c421840003000048d030407580710889112484a0120100040007040e08900e5050041c0b0324510b82e11400110706883c0ca5010a00e81c80b09041565115441031900914120030812022a01a600301c2c0b00d403518100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 990294019 1250 990292769 990292801
    0xe0702060906070522050d050a03030b04110904051512070302040c030e0a06113a0c1e091d1501030b010f05090f0901120c05010c1505090c030d090806 66
    0x640ea110305e0305640307a80d4855070130b501000b44032802030000c200048955844400c0303c50203102c0c9005e441c0b10500342c20080c0440d0200030b101030050781040300c034409001103001280c071080d504170f03030000e03070354a4031042003013001e455110194100d487d4191811a41100003886022284225070038403041c17414801c210306030780d89415000c5050340311003002400070725603800c600e141d030600d02c12040c1400c60342c62503500450b895500015041c03641d001c034000342d004122040680050042024000303182d0650004040d0030101012001d032000b125083c0078075910030040100104804c8440080030b03d440c2e00070344800c04065a90701140c003909401300c00294000d0245110b007900503161800000e060321000d0301c85903c003d0b04298003054401000c1714582c2c0e03110002d0b002c1d0418101032500c141c0c85141220856034250800c50600c0181c00c2c01c4000039180c0341d030709208200742d0341012030951600a00140f4080f00311064541c10300400c1c41200c2c2c031685c4007100600f10703243c40c8221101c0d034440c44440c010780d01e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 990295269 1250 990294019 990294031
    0x92903070503220c180e031303030909020c0c01080411040501060f02010b01090605400503060901050c04030f0302030705060a0e071e090c020709090b04020405150306010317070b010e0702060906 85
    0x280c11042080641c000c458070170b0300c0d100e0b0b4004a6507500d800341c058210b03484400200f40c800140781013481850707880009000034180030402145001c2c040524580e4500031401018104811000010104101c07a011194134030400380050000396101c83c0c01400c4001c0300d103400b41c010340c80e20700a12401d6100342c003440110303401c03601c4140c0340620503011000d821404003403114400880b00c410030008414410028015200017032620203c2c1d09140400d801e0450143c2481100d03814001404a4100130f00102e40459511487e010a004424602030341580221180580180203010070044036070801c0d0451003080000d8000c2d030700d2041e143e0011620b004895007005c454071412804c00d001ea04015404138103004018011964010364440d211020b40300d050000301c031501288001d010460915000d000e80083c19140343c00002d20702c40b400300f42c2c2c40405100141002d00016400042c005550301103070700c81500502c90228940e11040082001e4805950700001071040e41d00081c4280d20100d1a0381c0281c07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 990296519 1250 990295269 990295283
    0x705010902040f09120e01030e0a0c05090106080106081302010e09190f0606080a02030a062d0b0319151d0402030f1c0311090618091609290307050322 66
    0x1c414034100c0f10091ba100c01c00303060564445902410000c10040c7c803000c031b4803e00c1e41c014094200b0041c44001a03060f488002400044030051284580140c5619841421042c510072840c0741400100d030a40f8040c422940c0040d20881404988045041202c3c0340c1d80b0384260500c0000b1061540104940c85842944d00203030403a404a4241c003815002103810816071580892020303110071203481c44100c0e6141c09699000b00000321011700704c045810800800d9442c03030751400c5182400c507469000040c890a04e0207660b4031943c0c541d01d4500485030a0147c512207400720540c9081c800100a48403055605038800e00c983c042000c408840099240c0c00d03e80c030403504141882009605401030080e2070442802881c052004040b030307880c0c0a01400200300718507102c0e01400e2418082c841c44042c0030306035640703040c040005e00580b6504148844e0460711089503130f00c00300c00702c901c22103c03040000d00190922100042480301c1603904c0b00203140070f07100320303042d82000403e06240906a400c010703000400b09 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 990297769 1250 990296519 990296543
    0x11061302010503180607020a030207051f210e160806010614030414120901081006140d0f0f0603150204030b0a0e16090e070504051015050c030705010902040f09 70
    0x1548540b014541000b150100c0c20b18038a074800304141454400c60303003140168010842c2d0424154100302140c000c100c152030b80b946000c07118001e00002c40145030b40505002c0042c41303440b01041440240c800c00180c0a00411001030f4100c00f0341d440314001c1c2100c02d031f001040d0710041241c58006c60260b0407180140c4461003000d118600c0c000c1d064000034820340d441c00c405452a907034402c0601880751501d0000540c0c070354500e52040007401c0144040d28103440b1401c0114180510b50b0000502451502c0840e0400d41b601d649111000c0904254109100514140610701d0007051040d007268050342d201e9000c0d0004840440003042c101d000b181700c09400706100d0008100d483d00075502903070403000e001d002d41d2102d514800c542c03080e0840a91000340c2159481d00d00c080e244206101c00b80240400311418007983c1000b2000e1042c10f4a40e000e02240141c1452203000202d000d00300721462002c8a030b050f26100c58075428058000c1070603a50690007181443c10600020380300f4403510020304c0c0e01c18455404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 990299019 1250 990297769 990297773
    0xb030a02010c03020a0813031a0411120c1305040606240e010309020d0c03020a0b0c0a110a03050d03060603180b0f06010302040f0b07050f0a120507080d02030a050403110613 76
    0x200110101c1e0540560196040403030110300518002c105442881100480652840c0b0304214110024103400e0b14000f01001440300054bc03241181580c03401c225003501d100c9010440640c00c0007134054815a00a60b0041050031501d1540c000902c5140550800c0046030b540340c440e800300545007640305031102c001d0140032460034001c05d07494403009418900040c0340807130b65020403501740d100c150036100c1082c200020400c600e0940315640140541500b41e83c00d110480385225952410388074002c0c400c80d0075000002c515141d80c404070006580240860306107004181024004012500904002070f00340107440040e2482c8803001c030884c544c00024103100c5e81e1141403003500041d0241682c0d0400d80c08020009001d40c9200042024200072003415035107082038a03015203040d50703110400c0c0b4260410f00ba1392022640f0704500782d204094600700303190361301d40504c1d016840748100640b1150781480801840801401d603800148034600c01e03154181c1c00750b402c04200c1d40d2102c045403440108004c41d810440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 990300269 1250 990299019 990299027
    0x4050601080607090e1e01080307060f02090114030915040b0f0106020a03080118290127030b0c091c030f2a080d142403030a050c031605060a0f0b030a0201 68
    0x79001c1c0444120700741b4034101c000c044c2c52840082c1e001803065800400d103102030080c1c61140d94031500b14010114035000d1a200080c04001b440c0202400e07105020000450200084c0006402075a40c1c9440400724586898038903c4100140c0380283d801c90201c00205e6024000a481c0c10415016295400c95a10349200642c15000c40841e08001603102e000c070b4180b00b8000703c9420070b101000c14258080310b215400041c0b860920440c1416481c40701c100d40c001d50683c40603000c3c1a6034210154600a5643e209140c000348035103a441500040181c0f00c0c00420002d880305803218078401d5540030000300c42034034202e0300d140025607249080d858150942522074000161126810310819082d070400403400c2e00c190454407100c1c0c0e1024030129030020006041c003515039184131100907840031800d0f6010038000c0b030b94a0203080304441c00e02000050301c4e410b1400070003e07640243c40e640000c20280e00c6605c0c1081e2940c6003903860074085070404c2e040d8200b00c1d10501609012460140080c000540c0d01d0300115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 990301519 1250 990300269 990300271
    0x103050a121704031d0303091c032106060809060402100e010e0303120601030b030d080403180e1005190303081b040e100f0501030209060913022104050601080607090e 73
    0x8082c40480b0000e1410082e8200324540300314000d840300048495059491076a6070030070500c0038441e170810080c00e9079035610300f503c00201d020000da24804174822882c05460b65803240385a1103a07007450100f655000c01464100c00140d0301395076640d070295200c41d40301e2691120243c800a61009000c0c0c060307110544101055441da103414034010414680e010b001c603043d544528010038510070044104146035815018a001c0300340154014003486081c00360080000d200a03100a00304485241142c1c0541c1698000c0005049002d6043c40c180c03c1519801045800a100303c41c022076140540d081c80a078148000c2e41101d41507180e0706015661820b402c03080c3c101050f885104c500062101040c1482c5029031507100700c0e03051100e00b02450910305d85559080840e80040d0415004202c1d042e80d0351a1074080d900444800c1e6005a200e11440b041240607004982110481052403c200c01c0382a16802c450340c01540074000342ca19690b256018103844802c2100c01c0300114a069504000380c03028060f0003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 990302769 1250 990301519 990301553
    0x806010e12030d0e01061a0406020307080f071403071109010506040306050604090b100806060a030c1509091b090806270721061d06060f030c0303130e010e0103050a 72
    0x42c0c1d24045500c4540401c03201400008003c2c3d030342d50076081c40303204d550384242c951016140440768205440d1050003943d91103403440c010424000031801c0c581c1c48218030180c42d03d19a2019907011b4011a00d0bc1c41c43d070720380065070704ac0d400581c5c500301c40c2806d080054a050507070f04040c1c43c40340b03080e0a40d105c030009404060f100540003a85c89c2d060501060031500128003074189140000c07038641c64003603050b190210180445108a955034400c10000e040c1da4000c204907001501c0f810035400700b0b540140c50030415540400c2525003018400b8004d0a00002c5a542843e00c54540d010310b01c0c2c8450306a035607000c08070b074403000e072041000c1c10b01c1c00380e41c24002002c910803126084071159603c4100b0152041074040c2c070946c0b00a540b01d21502000003500556080ca0520016080351030300d83c405141da500d8000e04410f018465120030b000d500d40f8240319500411a01a049941d24841140e10896414403841111704416440001081041c4107016040c126030700140146194050b540795401c0000142a039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 990304019 1250 990302769 990302773
    0x180d0305090114130311091b0301090504081903021c0608030301091517030d0e0d090e07141207030b0a0803040306051315051801063c080a02100806010e12 68
    0x80000c15041a12444d01940c480c0e000c070001c0c4d003448400c0c4650403402a0071892807501c11034503006903007202000e49046900041c00840d4544507403d042c096031148071081c11800b0390000006000c06e4054005056070100012002c201c440301043c590120b800e41d010701c0d80c640e0030810042000724110380000400c030781040318842c0c8542d601c0f651601300d01c8090004401a070400720f441038880c1d266200d1003c1320b401c501d0107400130001c40d98009184107110f00407075500c001c071130020442c0c091140c440403040381c0e060385045a459610034054981402e04841c03900002c0c3c10310741d002c0603c1c10807c10810440705010001c44c1040d0440e5240c0c00940741c003c00400a043e401035502d07001c100e204c2ca01141540c0c480000152174100302946a00c80b07031000702c8a0704e0b0f50f030510400b0800d408000039007104001c540301225603101c001d42940c0307610301c104420501404080756408284d922001c175800c030400d0b00c00c852003500c040c00e6180c01d46070041d00700d410501107480c11101c02d520741488040361456a0706401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 990305269 1250 990304019 990304027
    0x30302060c0a02030316140a2604050d1d0423161b02010c080301090f0b0307050604050f0a080a03050301080120030a0b180a091707050d0c05071a180d0305090114 71
    0x120307050168004a601c4230000742c0000c00480c0c426807881d541901d607107408009007014036050710f85641e207682000005041112114030500c1c0042114075a90343d4940081c02841703504200000543c115401103031b440c3d21004c810001c92241b1120b07514001c450211a2620071450a10303c3d4010208400002c2c2071341401440702d100302c0003480e4600114007074104040c000482c000345c081800121040f201c0395034001c1d404000700f408155504015501254011984038690100310b0b40818001880c40c2d202184910404000328101600400a10305940014008104040c2240c000070654400382001302c2a5001c1040402c0c0203c4ea680c02544070803002516101108051a1007100320010480b001c0311542d5441d2400c00401c40400d0400b0b01c10300310541c440d410a2080d0300c98548500c1e0741c20300d90050190041e800c0f010410188600340052102c01001104003040c44a20022540112070410000c20040310500040c50180d410700709494041e07441c2400d200740c480054895001c014220700d801c80c030606c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 990306519 1250 990305269 990305297
    0x201110a080f19110316020705060d0c090b1809070507020109150203130e0106030b01020c0303030114120f01020d0c110a0b0907090e030c010516170c0403050610030302060c0a02030316 81
    0x302920082001421030720385c1c4ea24000350341c00081c401010f01c0c041150016101000303160344843c142c54405510000014038420301c684155034500d4203a0000c01c4030300c0c3c007084030295084020400f29a000065075174000d9651400c00486261081150080c04203407910003d00c501c00070203200811401907030044038549400303061031101c00e540350b41c08016040032200060107442d502d8020040b003440c00b07000030304507009035400180e100d01050213031401110300011050307002e030b89002c4094000314000d8186c40e280ea4075680f0083c082e500804521030440e003070158408410f0301c44c61001d5500c4440e0340180c080d0a44076500d4880c2c929000d00820054850351001144401707040c440d00034040c6001c002180c0d144003201c003c60039264006d040200000c40b0302c4d031402c50b440e0001c410405150100c81c29103401d98841e10301c030406004c2d0390406407207440b034030080001c02c00307c003901481681c1c042c2e001c42e2005d50b5100d03145500f0780300344014035005070014000700309414594500320941284500b40040d0b110300003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 990307769 1250 990306519 990306521
    0x6031107060911030706020d05220f0603060609120510050a1508030304021503070c1e0b040b06030601080c030c0910030503031f0f0b181306090b010201110a080f19 72
    0x1a81500c0c601120428043c0600e010480140103080c1c90020740100082014007404a01555002d418108445084561040342c000842000340200510b030300807480d15810024001d04407401040003260840c00e0205009045248640350164804014010185580d415402805010740000f040d141c40f1250b00c4c40803030030205210040c1420f54011500d0746801e004000d1020703480803e40c21104420414414042c0d40703c00e21441c90f80d080401054660440145010200003408001c1c0c500750440007448100103060b0b20a038024001241254140c3c3d0321402415120301c0c010f5261941544191203006803070801040507607019000040d01000c0b1581c0c1d40f61141154021580c0c0c8040d06d45074000f6002c2140e041040034080d000040c40c2000b03c40c200000c0400501c40d20302c0401801a0741603420b140769684c124925909042c41c042031008a98a1038600050526080c803307001d94282000243e050180d40c0940c0c03202c0e0101c1d9640d0201d91214820031802e00005092600f0006295a40580314066 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 990309019 1250 990307769 990307781
    0xa090b030703140c07350307050d0b0f01020304260a030201090c14030d050304140106060f110a0c090209060f070b070912120810091b1b08040603110706 67
    0x55a2030204401ca000510f09628090051841d20039010910606020503503044054490205928040c6c44a180058210003054407501048221001c004108440710340d00402170400b20042d440d00380800c02c3c0329810007600b020030b0782200340113078800d0104000f02124001c500d0207044c404800c0300c0b614805444218244003200d141500540c5d12800900204808560358030018500181f0080003611510002515020309000c0c2a0030010b012020a06000d8485401450521018000c00103140e685a01504a00d03802581c040071808800c489100303d1400305c1c07051109680314a51610b80c40c2000358250003500400313091500008140300640300588128010003155001c2c240c2e103c2e1518084100802003d000d400011007001180603401c002450b454812040780c580d800e0041d25603680c006d90250740b01d9160311046465003082c092000c02440041c2d14040140c840e40c0d0f098903126141c000000100c01140300400750300c0c0401081018a01c00d40c04415070501025250f4a04841a2105010307900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 990310269 1250 990309019 990309031
    0x41a10030209181b04030804150e0409050f0609030406050304080c03090a090b1f0c060f0b031002071a0603030d05091203040b0612060c3c0d061e03080a090b03 70
    0x80e0003050000d01d01c0d086011030100c4c4c400e50145441d01c1d0955440f01381da070056104100044035a8001059180e008120106c204940900104405112802e0055440b5911412845c860055002040c20345502008039026640071b5120a860350322145e844260070340c0042507800450000384010400d50751542e5806c0c0086c12041800b0842450000c00c00030034520a00302051200007020402000035007010390510203582010001808002599054001d80b081803c0d25505000311291100600c160354060140c85010309080002884040003806c0b010780241c5840d9859441400000782920040c0c0040303a0002c1d4810582d08d0701200307241c07140300c55041903400f112119144010042076003002288000c0902414009258070704002150307403498403856220b900d0340710805a015212400c8400700c045003182c120101820002c3c8201d014045400c07052000422504080340012035012460007000a004c5860034a414503242d41c1d940076190740701042c07480071304c200c1d40310001d610401c075400b55210f44 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 990311519 1250 990310269 990310309
    0x30421020307061802130e010f0203090d120603030e0907051201061d090f060d03090815101401080f09100606030506010909050906060913080a020a11041a10030209 72
    0x242c40e15159064603207028131032034500030340b000000c0903985105090704c00303481c405000a080810501124050300f81c1440250540b4000024001100700000b261900140d103940c0b145040f60070300c032a400540d405440080c000405a0500781c29078900000041d4211003541000c0e80760180d100e1300301c030007002e0980c482c0010842102440c0c582c0c41d0f82e20041c0c041c501c0121a83c42d000c3c80c04c4c02c416504800040c005a006d215519003a40170140983c4144001d46001c43c200d4110241c00d81022030400d404850710b08406c0f13640c500c0090211007514050541900584803130301036980d0001e0301d00e101c03500101900c6240c40b8880380080611401c0c4103103006407085907000720701880c140d0009800c000e145c0c0d010440242c40c080170084208070204525401c42000c0301d080745981c42e030094801e40014410700103451101c1c002440240303583c0010340c07507440a2040300707030a01040f1404104000c4488641950310404c1e40c0003400c889038904032843c44901281410010704103860000402c410b2103050301c96885070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 990312769 1250 990311519 990311527
    0x912010c050715020a08010311280510050a0807120b0d0b0403030e0a0804090506040b090a29130c051b1f0c0c0b0c16060b09070201021306050304210203 67
    0xc003144420f0004600f2504900b50705d0f003a02c0c108000e00440c4140300c06040c01c0d0003c103980129690740c0078805814111064810b0111101d1040c0d0301104802c5d1045274440c40034a661181901e0040040d11401c0c0501d0701c600388a503031940001c0d2400d1052080e80d0030643d550b00701000203a40c482141c41c15040c0582c107081e55a1920f480d0103030440c2c0101c0c0100c1d10591041c844000003456500403641910b00480c0046000e072200c6003c0b07805406084038007548042000d040050580c1140d0045002c1461071910324045070300d11a03034648188440d000680c014200c3c829071100c106241c4c022080200503031401900e0011030749001d03400c40703420044442c0250030885800100704030032400c010400f038540701c0400014110300000352005a09040042603c60a80d0004240780e01c10b07030a69000c81d00c00e1410220302029803920720f005204666041c0c0c030404034140032602451051007611142452038222144250034040c2c2030300c198000030f00807500c0b0030f414840c0c3d01a4120158a0040e01030940e0001c2d900d07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 990314019 1250 990312769 990312773
    0xa0212010c1121071a071d04201e0c0f011d03030f070212070b0106030c11070b0706090c0e071b1110020a06050403091805010e0c0912010c0507 63
    0xa2001240c03070b141c060740500e400c0c3c0e10441000c01142d184405110071540d0b00e10741841e0140074170590710440c1c0c82691400c800c0040c61038002c210303005540c130240d4105819040000402c8100c9054074090316000c44000d0500042051040051803c142c10404011800103c1200d225059202420100180d08400b1200d07000d81824003501403543c19a000c1d0b5081075070034101c41d0f641c0c1d0000500000f446500c0c0404a8090750003401010f000c18040d48046685000d2400d10a100c44001e00c108800285441e46003188bd41c1310303c5558176a5034041003d0110f141c60001e500110790480c03241904e40366510403502001138510030441c00204000422818545400070001d000d001d041c6c0030b61a0b140003030000c4e0000040c0f442c180120b460700c08643c5c898200c10900d0040740780006129008000728988000c3c0030074107401c41c00d58001c0ba0a01014807100c490a400100e080e52002e01c10840e0784003841c008209004050400340101010203014072201d840641c40b040d007500c690212400100c0c80002e03440341 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 990315269 1250 990314019 990314027
    0x1209030e0312131706061c140304030b090f0c0609061c0b2110050c04030b09070806061c0b0c1204030e150a1710080706030b0418170c0a0212010c 64
    0x4c000c0c104015500860400380c3c40e40b0303080c0003040284107108a9025001312503548003041d6046800081c1c412226504800b5290360f98041d000a81c0d02001d03080001d008000001203428440d102d40003c0c14400c9030305c030103200345604520103a07a40035009005404440d8402480940120010000400c00c0c1300001c1c2408185d800300c00c0c001c1c00341108101c1039099980700056454192101c040c00080781e80ea0b100c0c91283c2d41c0100d4000420010201c0d00380205528002404d00c1616140c038103460054441c1001c0010b211400740086842000c20003000b000700340d0800d60542e000da880e240c224035080c3d05030203005a00380103c6017100420f4485c00b4204c13080c28121450303846a26400e094a207085c0c060640901141c60044c5c06002c03104600000400b09840c190110b0010304500c0211000710340c8901c0c01501030021403c10b14045c61821018103c002802d150034400580c10100300ea0b4107a0030754049001550001482c450709105000081005888056040d00c00c1e03c1c411000050b031880584000f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 990316519 1250 990315269 990315307
    0x3020c010c02010f0f0b092202040207050115080610030b13081902071202130507030e0d2d050a050f04120f1103061b070615060207030309080601061209030e0312 71
    0x45d25841c1c02140ca10b0343c0c5500303001e46c7d04240301038601241100d05e010204c10080c5820f10003900030b40041140c00c100300c41504054500024010858000e5459620f11a44c4606c11150540c900d0b9802508101103904040982e41080712440e507001c5409175621040c0d000d13440f8218485841c4008004500340a50600c041c0016104000140d81c2e544d032950009003c1c0c80d61901e6a100751070740c030404030300d5207402540010b0381c40510034191a8501e43e200e40141c50314260381428110400040f401e40c4040004851010070003040307486990400d60080c2048450b0340101c988021056020840443c91103425004403010034407036403007568040d400741707801e40c00b008012005900030341c40803090140401c05074864040716400070070b1241d100c80c003c1c10040e011305111405051540c171100f4000c030344103501041c0501942c0c000d8481c440c10715503031809242e48240903c0307014009543d01d500401030702041d401c011401d81c06480c20740d84030509100001d04050340c280d9901c2007028002403a00308494401225 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 990317769 1250 990316519 990316541
    0xd0209182523030c06091c1506050906030a0609081e0405010906020f060109020d020d0e0606100f141606050f10050627030a0b010b030702160b0a03090303020c010c02010f 75
    0xc00121400b150100307942c1d2140390360040c440c4e0400302e101c2c206502c1e0b0031491840104002030415485105040824038908510200100301c0c0c104440464141011704040f402408080c0040206044907242c4500800c0110021a50b9071000c00000f00f020f01801c0b180e004054181c50307603d5035145007800141c41c0342001d51110b01590066410034035000d40204280741111010740d00541e0341c01071100d40000a104410040207105c0c03600000366505540010081c0c4203802c103450411401d46d44900c140c0380b2640c04000d040000f01e200342210b000e00900c20241441e01c0b000100d0800038040b41c0d80701803d46c1c3c001c68441070b18074a0b5204115000d00301c400c019004090640e510f07071501640380c40c80c00c24481c2c3c0144400c1030480508510343c1c0e5881c201700280109410030030400c815610b4501401d0710354402d41d0500c00601c90145040a1440300d03503046011140d08a00f2140f80070b03c201070035006440b41440c2941815802c4c00303c0d00b0480c5081c000d0946a0005900001d0029000b4561800719004c000e50 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 990319019 1250 990317769 990317819
    0x3120703140115030c02070b0f120a11070602091305040605060906010807050901110a0804120b160504050909010920011107120f0825110d02091825 65
    0x10810059280f0101d22030040c98500415090340e00d101c26841c03d02164000503140800103805031090a07000080d100840b007011901c41c0c640c079055042003c0c0d50f0310302481c0c042d1000c05c00001300064202d6004203883c2d540641441241d56100d0646400c0300c0e821074003a145546c07030748204803403850858141548803509081210071800c03c0b150040050040c07141483c1030002503090303000200810015840301c181d01250695a40f0f403240d00803050024000400c8a10151102c0030a079039015203409000c0901c1107680e41c5007442e01c4d0000f0070003818405404400760755a9110064082040088080481204030205840007034014000405d031039400204080290800e08007400302c000048055002c55810049241080c11541010b0035144a061105000100300c89504600181391664010f001c038000d41398040d20070700704002e020a4081d002c00007035001d950304c40040c0c4d04c280701d59128105480f11400b08c0b20342c101c03c01541c2803002058500c2c8400766002c8070040040d4444180080055146a10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 990320269 1250 990319019 990319021
    0x2209140f070f120b0a030204110c0d020f101a030601090e0c03160b090619031a030609060106030f090803191d0304030b0403030f09060f1a010c140c030312070314 71
    0x700080080074a48406401180c881200c04e100c0c0d0741d03500c09a0069900200100440a0108014102a4004903c0311084d000d000741118034179001150a40e488840c410103002079440b2280004001d240c03409025044040002e04203250752020072815020304400100020040c83d8042c07107a1030824641402c6200707910031203101e0380503100e501112088417203900d103042e02c2d200440c1c0012103c0c0035599a90001142a580290700c003035068001800c00a100e031020224482050107050b02c80304216400415070b88400c004101c014482e40c412028034400950010b240c4100c0c1c1d80d020b50b035a005440407140300c010440c010400d402c503407103003405141c00c0140341d0850031070025066032207000310301c000b4184040e4100010145406504001e982c486192170030000ca240d18945200101a030445c0030003038920740001d000000421405040142205031100107103902d103a0780d8003d05074070503100b0200500070580c1609080c0c400f0000303460742507824414540d0500d8040d10050440348038606035400c05a07984 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 990321519 1250 990320269 990320297
    0x816170906040e06010302310e0c09131e02030f010909020306040b151f0f030e031e040504050705120606090603072007092007082209140f07 62
    0x10450b402c0f2031200103100001c2d070b03801c00182c0003401141222244040e2850b000d004121102c2141d0b640481e908060007211610340b0098001c1c11000c40301d601d00204204254100c0d80750000707810b8003110070000c0104460980368101e051200442e000c10100c03540100900c0801c1c0a420344460152690146c100a0915141c00003a9203100c0a44058181c0c0103d60204510441d110440084040090200303040030b00c03c65030180352021001c40400000391071502055915203c2c0c02886002d00904004504204812036200c000c8074400000507200c0a0401002446444070f0054620541164803020b40300d145c040c8201e501840c00a00d01d41c4114002c1100c04115516a020b60b070300302c01185820060088030240c00c8003210f214440b01d42c0b452040a0000540200c03e400000342c0303503007000042d0f420381900080134080e8040d14900a200f10002c1c0701d95030010340d00c502120180010440c80c45411585d8819003401c031220303003000d0b81d10070090070200829100301140f2103030403031782c0e42ca82031907014489 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 990322769 1250 990321519 990321529
    0x60b13050d0f080a0c08040308090f03010606080610110d030b151e2215030f0e15040c1a040e010602030a0c02090a0e03130302010e010807020307081608161709 70
    0x240038002c0940f9400f080034450f01d40700e041244441544048901d6030f030313602ca05215031140c0010708100d1095090250144103818103001e03c0c400c0783d540b03480311041c1c3d40f940801c0140c040c0101c3c08401c101b184518907174001c144100700400405043e40c400248014080c1d050104103c9428495a403024007085451100758441070f91081d01480c0a04103511150b036920a001c40703440f0390300b0040301c11141c040c0103d00c0d1445c0b41c210860301c40c241c0d1000c20440341c0c40c46000054408103a880c00c0d1a4110366203c8a40c8510500e00c0c580c841c1c0715110081140b5113410005d10040d00c0c1c01e4001c1054a401300d4244444018481564054401c40c0019030400807400b0009094441e141c0d40280500088800301c0c00e01c59082c2c000c21121060242902d441e405483ca0230f101e000100d10090740016900c48110ad8154040d850050040e80b00d9030180d4508201c640310303d51141e0180c0d050402081c0558035110201c1d61240c094003450440b0041f4842c1000c032800c080101c3d0014450901c1102401c000c04207440e41c070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 990324019 1250 990322769 990322793
    0x40905181515133305060301420f082403191b091b08091e1516050d050a150f0303030e01182004060b13050d 48
    0x2c011000d4022050002c0415403848114180d8107805040499007036401c044000010102e074046104601a00700c0400c1113204450300744103039500000104010701081c1048491800315001c40051680180f98109240304050180c841801c16146d40d4445400000d0740030041c0c2c00c52a18501e0803160600f80141b41c00c0b0300442c50310018808a90b26001d008050700c00340009032440800360740e6001480b0040c02d00c206540302c222074a40c800c903105100400d4400d0301c0d21840d1001e2800c023940d40e81180f025001a25041c0002c1c012980701e205200141c0304203030340c403c5400e98010006014101294030405c1201240c03002a10740014144101c40c45c0800c1c66200f425503600501150011626807201820b1600400001c82461075050403c140410001d80d034507542e6084a220744c0e001c1000300b0841c140d6601b211010702c501c03090041800d00f45000326282202582901c4484101043c1030851803001604442499022480e081000308455081040e03060003c00181420b0301c2403000c0c03001d0399486440b8045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 990325269 1250 990324019 990324031
    0x1a07081f0e07090305011e06150905090405030d0203010b091908060c25050a03110c0d06020d021b01050108210f03100b070f0c06170a0209010c05030409051815 70
    0x580d10000a000070f02c642c50000003103412400821110044004c154420522981490811800c1000000e098024881c03000c1068503242c0d540d4080b14104020003588541c044c2c01501c0a2005100c0d550640340b01d40300440c004d18032107010954600c4610103010a076060000314988541d0f4001c0100400300b0003203206980140301e011000e41c0c511992403980c92030190000c41c0210100d2000070031003085030004601000c40e01030340311a028001401205983c40c1001e480301d9403c000e16464041c005101b0b0740180000d0b1071030407800360038000c1c104071350040003100c418012503680d1144010400c1030800e100400d1142404030038485840c150341042c84240c0f2400995080d0b000c0300000050503a07600d41d00c02006842c0c1d01152696803041414000610b80e1012015581c0003981c00000400034090440c9003002084403204032619640d200c440b100030341140e1002418010704000100020b442071004101418040c98006001d0501105180101442c090b84100380e511040c5070041c500f04985040340e11075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 990326519 1250 990325269 990325289
    0x9131b0f0e043206090606150c0c1003020f12040213060e0c0c120a11161d0403050438030c0403290a0507020c0a0f03020112091a07081f 60
    0x240c0c600500d03c2c242414690496458050b45083c0000d141000c60090300030f210031981144032401d16800321659110300c07003100c00564801c0d034222600b428040c05d001941c40480c10f00504060155200c030525500080400c50800e1512040104520b00031081155102900804100f8241040703a00303a440d002c003410203c01c6510200d40314850800c104039040100e0200d5490766111095040d0103484040801e69260950069001200742c058080220313070100d50700b0929944240307654900c1a210440041e00941c00c20004200114568038014a13080142200e5060f00100406800000844801e5140e6040814400b0814080d000f441c41c0c003560103698001314031600d034044500c00c1504c106807a1140034007503000c24081000032620f03035200c02d1052a1035020b03601021215810016454480d004072090f40c24942c078180003552103605014194003552400013145c8045032a42448014020084d81c0240c1400040000740d60f0311428440d0411b0500c01c3c10244012980035800b07040c2014050340c5664 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 990327769 1250 990326519 990326573
    0x1a010f26090106030602040e55050c0c060606071a09010b100c1e05031e1b010902031510030809030114091c08090c09131b0f0e04 57
    0x201c07000307502c407600459200d6411999a07503501068040058115504d291021401061a61400802018549550588032800d0340e0300d0542c85091402856052190036241110101c0d003001907907840303560f0240e036200b022140c444603180c525900d030960040a10740200c5041c0b02c41400180341b40341c0d125128600c9110070035581e076078440250041c0f445100e2642d1240840300d006c1900b6030001140300307042c0d02034240c00c543d51444103102800700858201c0105254000c0141e191741c480e012003c5070709034000a25851422040b0301d0825220700700b4030380042d0f559555400c003408500c0c00b0092020f0740101c038817061b8680d00c0e00101403007000301e951101910600c4000b81c2034400d03540c00c2d0b10507200c90468110b040d006050a00081c1e0703490000c4405803201c0c80425034038004490243d040305200313121130401805141c094000380100050040c09118501d0303001c0c1007000001e03004420091a11203055600700c2118a0f180e10b00c11308803c1c651010b83da0207080c0080c4004902499030b40e0003080d4954a0b00818 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 990329019 1250 990327769 990327781
    0x20106050904021507050601031a06040b091f03020a09061e2417040c0e07020c0927030f0307020105130b0423010e0a0210110607080907091a010f26 65
    0x31341d1107054002041ca010f004004000c0241c100b012035001e401c03101079004c01d9992202800304907603403415a1540b1100403030008002401407800d80080082c2c00690302c81150340ca5002c00d550f41c409401011810380c54100a00400c082103203180319524031208070f038010780e141c1050750a40c000c1c2889019203a20310509105611030181450410707000da024041031141c82e240c104070308820300900032035054220302004201d81d5440010b401c402c1030401007000c0b03030b03513154030103000c034030100c0c01d03540c1c1008601e1151050207480052000c2c7c0100d440c4102c50755130341e280c0950024211440180f40442c0d100c55a1026004034415800740c5034410f40c46180c240712081444082d010f0004040681002076003481407a9504082c080b519901491003034802440c0500788038002d46101c462440144504d9002100040c00c00780310310300f800c0d00b20340a241580d450907100d661240070b4805503081c0d5064524915042010765910203140400760b41c09250a04800c1010b41034103401e5034800780f00d928911802d4012030b071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 990330269 1250 990329019 990329059
    0x1008070e090103030c1208070516230a05070501180b0c100f0b0103060b0306222a020d2f030c010614130506090109020d090210050d0c02010605090402 66
    0x14014009003607211569480c50001c007100300c880d10441d000394601d68200140da0103642c1441c0501791685505080c0802c071400181074800f041c009503507400040000f4090181c1000c1c400080c050301d8405803800d9135281c1046071a058040c1d0096040064541c8401501e24007008918250340801417415900c449129605107040c40200b802d0844500c1d00004500b81d0301e596211490400e000c0c0c03020710001d40c0d140e2000c80c060104684180d00b10058072844815044009410705000d03a24910002d55000519840d0202c500c80c0407002c185007504240303203150541c040000d006035802a03c3c000a101003100062078040981d45101000401420320b403800f0780f01c0034400d0741c910300b080300700030031040c0c0d980c007028096280540521030164a80d98007444100b403003030043c03074800c40003d0f2542c98aa442c2250510007540032462441000340d95030300400050b51011400040750010340d40345a141c82d400d0341c42c0d030200e40e80300c0300642c203581c5000c0b0100300310345481c4461944140c04443d602054455050207032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 990331519 1250 990330269 990330287
    0x3050a0b03070b0d0b030102070203030901141c02040501030f02280905280501020f0705130221070e0315150102011407050a020c06160b060f06070605041a06100807 72
    0x280c1c0c1801985804104a8000750280180440001d4144290f0a004051500301e2103207040180d09030b0000c100320003840d40507102071040d44411b080b0051a1411210041d002c0401e0059004070203600098100a1503030f00d40501102d010241004510b0700d1125107188190750114a02c07101555005050014554000c59110780100000341045041c1c130b490a440c1c070940440380143c010402071140000c0342c0b652001030951111100c4500078541e242c10a0200f00d081c0520081d010b800d035400700034200012100807134000240e00b00710044509030030b00c2078000e00443c900c10640c500030741c08451180c08100340844402e070000c1c9500f405142121040380102d0140095134100000008a5001c0c003110a40c01402082c01080907401d0f120088850000c00c00c3d0351203401001145482101025000b0440c440b0255401c140020400c44400106401186464004c00c00c2600e50755607440070442405824520380c824a4a004c2c105c49280c40c14200103a5a1407520744068204000341e80015070a5004128a03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 990332769 1250 990331519 990331541
    0x213020901051615090b010e1005010c1104062d061404030807020d06090c21030503060108071106012d0b040b0309010605041107140114060415030204020403060605030d080103030f03050a 82
    0x180314103c010708241203541b0081c80b5400d040520f400008403011412200c0005441c01607490110804041c0c40322048203c40c2e924950744070307a0300e01c400290010041d049614482c210001150120085408000c540c2d1696101c5002d00c2010081c0e01803485102e42120b003900e07403044145031a41d08a0003c00c401400200006200314603011042044c088510042011507020320840b1002182010070301802d0005424001c020520178404076800f0360044200f29880f0265251000c400f00d418041c8a1400d0f5080c3d0298006200f15050782400c40d104030b0026400c002c044084030140c038030f0f004040d071980c8140d11400d0458400840460f00340340e400c0d005103004020080c418000c124a100b030b42e801d15403228030b040b55003c0a554200310b84150600451004810b83d080b0301040c0d80d150f900340070281140e40244201802806404801652184080d00c0a580118000206103083c003091600d040c1000704800c0034010000010000641d12244284902c01a46008111501e6001d0b01c100030b1300d1d402200c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 990334019 1250 990332769 990332771
    0x12030c0804080a0c080c0d0b061f050903010c02030f07020603180109150b090403080115021005010b13050604030b041502071410051021081201120213020901051615 72
    0x42d40e08000030000b8146004070f088030203c0d43e42d0301c40d0070741d100607242c2a2900706a05038024004298010000c0341d22200c05000e0080d05100c0070031000c0925801c4141c040410804983e09180d0b080910814210b035201d400114a02003005c2c00d03405090284240003032180700b0010024100c09556032842c00050040c00080c0b004403100d2130a01c4095203014072526201c0d1500c410984945071503000360f40216010303107400d03d6507420a1384001c00d5110f00509070095102c0d4840403071aa101c548180e41c0246542400b0680700c0d00003581510803150264000d0748540010b010a10200b0000c8588580050340030170449000700c0307802d43c848068002e1502c007034000303007441c920010381a6020902407810030107481e080100c4c1d40c1d00380c0481c8840c4c3c00c41c09000000c2900103460040c894030040034030402401020341c141404401c1c0350480440d00260009401e1800e00041441182007901d500e05480c0d128400541c2040794a600080c120300442242d102020b1044585034144020202c0c0d1883c00031500d14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 990335269 1250 990334019 990334027
    0x60a1d01030209061201320907030b0d140c060c0d0c0501200d0608010e190501020d0e1c050412020d06060b160b0903030424060503030316030b04051012030c08 70
    0x6004201840241f0521141c6500c803804a481003074100a51804049000d043c0d44003404148207102500e480188404180750341e03075180300d8850b80c54116681c00e15104c1c0320b2019a01e010280010306150401020b80d000b0b41c4240070082e00d103080441e0a4100c2d04051800d07480406030f03828100e000d020042c400030b81040e00003480480c0204c104005002c8a5030200050140e03039035401c030103400c071050460300b0001a04512061146806044070150b06980600005818442d421040030100c6680003c0712009030300c02061480000c4603018207101e5040c40c1d00f001400c0c10314060342010f020140f00002403160b01c010b4284805c1041e02d038070941c0035048003d0080d8039030007035003154050410380d10703003d4131042600740000355003810010840740700311351018130320501c0ca5401c8112440041407140304148580c0311f131001708480e10708202851042c501c01080c80d039001900d80380582140c14149180340128140410403a1102c02035134003c0444400d4000884ca8000750b08045500c548050b500814100c0001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 990336519 1250 990335269 990335287
    0x201110c1806030105150109050f0402190807140703020a15020c0f010203090705041a01030504080c0f0c0406060c0b0402060f09090103050c031606140904062d05060a1d0103020906 79
    0x5000c1c0348039031025002041162955900e07019060100703041180018400d110502c1541400c0086280741a4041c1c800f50a09000c000e24003081503002d408000060f24010400c0526a40040051000d03134414510314035082158030000c0d02e03070145503c0948441e02d01d6003013001682d00c03541203038045c2d040c0c075041d60001404440aa8040c0d801070311300781e0051240800c041168075152140802c601801c200124541034908010b40c0035050091050703c4000c000d0024591110007403050440c60681c140203040f81c1d52070301c0b08020464020f034100500300080704081c40001001d00032804e4002c1d80480c2c14a844500d002c01140d80ca1060290154100700544d0002040100029a24000c50300c224250b030341036002d0307800030509080d040c03281c0c50005017034044001141c0a85001040041401b900100b4003d1b201e41711581c504164030b80c00911090400c1089030400e91004604c0c018102c2221160315116003680c0040ca40758603031006942606284840300a9603000fa411140c0412024204507114100341c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 990337769 1250 990336519 990336559
    0x30c08120a1d03040602060a05180a0f03140a12090c080a0809030f03090a1203050906040303050d0b0319060b1f050a09270b030721060b120a0201110c 66
    0x220711014103061129542c035441c0d07021054030180c402c1e681c02080c09903140140784020780401b504090300d500c070072007040404000611030004018010458102c2c0c440040c5802080154000034940d20b92606000c06102158403040034480e03003507405c501080b01c4000b824040b0800b103040d030003103510b4401c2032005800c0102c480b010300703110181101580c01001d0115030352600d030b00c60318100ca07520040c1200203000840d584880c075441c642c000d00e4401e0800107804046030302544180c00543c08554085041e54042d24203001d1a4890070301130700682520203020f410407005030903d0f0001865540c6032001d50005072a1071580c0c49100c0f87c0251040c00b030004800000c1e0155208188210008124007404a642c515070800079400c0703003540d4020b400c1d17040c0c1144503a00400710821055498001d84500184040401c6200301900d414000c8032a00d6051071303c1d041046072030620b01140a003202d400c0c2039003070541c04140340c040c268080c2006400340b40c40d000081d003031180594040e0340c000e040100f00c920340e28071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 990339019 1250 990337769 990337781
    0x50910092c090c03122101061d040903080a090807120f0206070f0206060909010222090e06060a03080f040b0a080a0c02060f16020106050409050a060c05040b07030c08120a 75
    0x50429126182e4507001c00494440303c1210605030507900028441e562407400c40c00401d91407441e41d178079201911840c3c0c04289404401c1c0e100344006414403100f4580a0072801c0c24a62641c411501084900059540507113081d400800200010340d880d00400d082c40104002c4561496002041410340c540219010b808042800450001841120f000400c018002d014032650009503400808041e6600700800100d80e03402402c1162a5409200d044015071640701144034a0020800c1e46d00044d051500b080e0464103100b40e4072185e6444002070000c5034442c071100c0402d99800038030b070503034519001020400a12481d07001c68260880010228100c582c80100d8038080c0700c02e0740080c4231880781103804aa44030426200e0101000e6010046545842002078820314609580008507200303540d000010220b421710300058926400c0200304004000451080441d0742078582001c5007028100003000101e405071500c0141480094140070040c08146001d070340d40d148200715810080d1070810320304405000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 990340269 1250 990339019 990339089
    0x30209120a03090e0403020303061c05010e06040209070f0e2806030902190e0a0f061725030807030c1a010b0d0b09150d02061b030a080703020a05091009 67
    0x8010140400d030707070383c284d07441d6070041d40c040c1d00550075a00c80d81d00308844c1414065421601354013901c1f1500014034203005a0b0318208d011350290034945001d006008200c4c10081070142000010921550311a03089106060b41610603914119400f1886084c80011030302e42000f89501100e0040000b60294913400007509035100b554805000125060503100310140ca0054180c520742c401d0000d0b20450490703002840840c51480d01103211969500141541c540c040034100310b940180450001040e0b40745051841d041510642c08070403859078940400c07034010a600202006000d8403507809000105810054650070312546400703a5135520584036580d0300850102003c503007030001d0031115140039801c1074410380d8040c030f00c08043d5102000304121501203100481c1c1c4018142714001004084140311a500845c85005541da1010480060039a2000601d12000c25004100b00f110465006041c1c030030701f100a40e0782c19805d044100c01a01d0204080c1c010071181d00179000880e0030144615140c543c4d2032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 990341519 1250 990340269 990340277
    0x1b040f052a0f0403080715020415020105090f0604080a0e21010f050411060904060e0a0b03210403030e0f0d03020105012c070e03161d160f05030601030209120a03 71
    0x289003030040340340e8002c18100840b03455061104001040c5800000d11040340f060710384c80140c0101182120032a005078100120244491500c10700083d0248251a00030017070f01d0042000745900003115540e040011300040940c00c2c04209030006901801d81d0260945006114291003460358804101e03540724414915215800c00038408003071403d512442d409260402040c0c2c071807100600034009642c3c88030ba003160b000fa54800d4000b4200014041040c091031f421240400d03e07405100816282090700142d40110300300380110f80035000c002070304030740c202c1c1d526042074018101d070383e00001c50040d904903078250081d01e40c0810004256066102d40e050b500c83d01c05450040083c81c07442d60003a01004a94203a00d880c4401203141c4500805810150600c02000c858092021811202d6013000341c0d8082c00d9154414190012440e206802095210340c00d001d01d2600c06640f80d1000700b041807507501030b400717104c0000040b51b8180d20035011618450800381c465031410680445035503507024403140c00c3d070020f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 990342769 1250 990341519 990341581
    0x1030201201203270a120c020d0819080c180f120721050c06031012050703170306030c22060305100c0e0a09020a0504033509031b040f05 60
    0x1c1d10b41300303003601d2060654802004848440c1d694041c055000d05804c80910101d0011080142d072084841c841282c86140100c2d1242c201d82400c0d030b00c00f103001e00f5003810f0240c10410080d110201c1c5041d5004108040e00c81207521902501041039031007804482d45d003203410306032425920040012280212821410080307107c55001810360740070355140c400141903822007802e00c0440d1500701c0107142c01c483c80094041000d0ba541116021004206200722103c0e04405404c00c140728a481e0414070f20192031490519600e400d0002a0b00c07142c4d1440394604c10307007102032145c014040302203001500d94941203003000750a449040960b41c0f6120305e024080c1550078001078144c40c5c4d1003004d01e80c11440028008140090502d2900c2c0080d4000c104510200f000c28000000410750306d0a840911602c0001268036140d400e92803410f0f58503c805001d032610404111004494400003201c1d92110082550303e483d03110b150000501410540300440d01c8103081100780144030030041c120211b0310020591040b44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 990344019 1250 990342769 990342811
    0x60f0a080a1512051c02150a1e051504050c18190b160221061e01060e010216091d011e02030a1b08062701030201201203 53
    0x944290300403401180b07032a10000c201d0440c0c400002840300b0301c1a01607a43c0103650001d88000701c49844401c20042c1c2c84034540c80a0420340c0805036400c9016403000b4000c4500802c984110b17000807502c1c200c0600d540c1d100240c01c419a030303128020318250040003404281000a04046941c20400000e0380320805041c601c0414908001d00d613100038500c00350340c642c145c6086070b51461a088000ca0054030f0400003240c4005036204d0703208520f5000403840d10b103030f80c2038107281306807900100030900c9401d01d4039000300c030110321448200c0c40c0c1110024a04041c0c40c00c0e15000403400c26201c481c1c0e1100d101282040450106607d030066000b5504d00002c0d01038210300c81c1c41c96800d070ba1031a04e03803070007110010701d6400b0286e04540040d980403104883c042010388041c100001c50050355001030002500d031905000c4a417401300c803900509100f040d400500241d16408000c51100b0610000313043c0218043c14554500d0115100c0402510501c1030300c00c850500c401440a46d40200c4480210641c604e5550039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 990345269 1250 990344019 990344021
    0x1116090f090519050f1c080705130504050c0702060d0b04050906101a0403080a020c2701121a04080d0b01050313020d061d010b0a080f2a060f0a080a 65
    0xe1010342010042808075485120f008000b10007410540b01c9014444044404001c10072012501d010740d1041d029034095030050050040354080c00c50401c1000c02c00035840c903c02d5a2001d0000e54100715000111900c5441c15241d6921035141c00940181000c101070000e1400780d400a0200c120035503007482941e03194620b42d078070b603142104d015030ba075502c040b014409240c11003240ca00f1441100a002d00e025100e031111031007038100c0030326400140d2041c4c2e404e40035400d03c10360701d50300913964032008039400201481561844005002c1c10100388a6010a10240004401c094201007900004c0a03d10309081c100300400d9407168081002c01814402d05404d2548101d0860f441000300300c0c907000306500c05a08119000b07034032403030595040d0348400f01d05002c500c60900201440b60308000000307401c0382c4881880301401007070f4400061500410300c84991f05102141014814001004440041da40d601994403a03880c1040141c1e08540046040c0035124003d00040c10b644810380c40d206000e6540c5038007a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 990346519 1250 990345269 990345281
    0x308040317032e0939360305060703051b0405040906140a0c091e0e040501090507030c32060c0f011104030c0902090a14011116090f 58
    0xc02800380c580b540100c10310541a0a80403002034280c01c043d540e07074140c40310030740c1c00d40000c8020313500c0761440031492500a14200c1040c8403020f81c1102000c851480b02902e1068030f90503041c0c04014803100c02e29004e0004000001c0c1245101d00144241d840c3d040c12651450100c42d1440801d2a14002c1003d2100794411034001000000019107070034200000e000c0a08944901115159124980c0b103011050b0750305490302c0b0b1400c0c0500040c0e41c468210717004205090b070f41d11080d078010020716080b003201c00408521082d91212a0300c205241c503545400c3c3c0c010a454540580706005518011040101c070100030400c96008440101070500781c4a16a403104580540c4141340d42106106035000b400c04401800c100f03020304050342c00380e01c0c4141c040c80c02c0da0320360161044005800201441004004d82c0103201411288400b142000d022102060102449005601c00c4000203410304500c1da20601a016805600d0b0094503680224135400d402224a9406000d0540b030611000340c41740c800c148900 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 990347769 1250 990346519 990346531
    0x50610050a060e01203a032406050406080c0c0d0806061c0204030318030b36070302030c010c0503090f040213080a0218070c0605090102040f030804031703 68
    0x407107460104161100c1c0010408541032154481025107000019070040e0f00c900c00d9080030b040d40d901d100001007691010036171118a00c410700c41c401421000c010b450a0f1410f103080c203000902c900c503418440408040030340301c24150302c204080400d80c6613001d4050030403141c440d120b03081251286200381003640181548503600d035002d8000e07a410148129030054110602411b190300d02090407001d116050300c2c1030340508001d500058100201a805070703070840d40c0e41e030f501c0a01c9495425a44c802c00c15980c06050303500d0369125211240d9241030f5452054400714070034220101001c4a10704040c1c2c9942e610322003030340300e0b000e001c81c4098154094244103a440740c2c0070015524018650342000502207230b0100154106a09101d85201030710400014405851705400a145c494802e10400401600030048101b24410100520214942255944500c036a02120205503651018122070080c06550b1190180881c114800014882890000c0054034000c51180f0003100e0002c0ba8100244403c0d120 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 990349019 1250 990347769 990347779
    0x305240f01061d13060605120a0b030a11031005040b0711060c1b150108100e12040b160507060c0b0a05060f0607030c0f0b01080d02210a11060103060905061005 70
    0x4410f000724502848035114081c001d200050002d0080501d00464440b5049100071403000035080c5000f02038850550390080310080b0601c03410306200042900c40440c500028808100051013810390756082c0b010300844100300030f04022500d018200240c0c419415121031000c180410701d00b40c220303000843c250344a50366443d185032411040c0741200c10420800140c41899004c0c82000b40500412520158001c0215030020000404003040f040c0840e00d40300700394001980300080484d41401e205040d10308865400400030703150300514806821300022088000c00034040c400e000700d0060b40164031080040e004510340c140076507406845104403401580c196a1100ca01912102c640c034100700205541d901c01d1400b1000402c0903500d6180305c01f44e10504890007464fc43c01440742c1001004a012016038500c020001081c000070301070700305907012141010800d00014051035140c0540050350080c0100402c841540da524204072000b403200f460200ca460144030041680d481d440210042980c0000340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 990350269 1250 990349019 990349037
    0xa1b0f0509150d0e010e16030c0509070507020301090b1f03020d02060a11010608030d0f1a04020d06030803040503090a1703030106030203100b030711102706060305240f0106 76
    0x1040068100348042c0401c5103400c100600303014040203020b1300c40c2e81c039007910020824804401d2510308012003d500100c035000c120034108007207803c82c6445011100255555162074941001c01c07161403240c250080e40660038028a00304124186003524410b981c9000d07031101301880c44685210000b15403101a6100e46a04500c10141c608140200010442c1d0f09182050000c102009402d4412030b03070051280380c10200d9030341d00b96017840c000c1c000c0d0310410030001c020403001c4040300705143c1d0340130442070b010301c2c2d0101da161070241c1c42c1c1e40040f01550300500c189840c2e18007450426070301c0e03021111150280da85428000f4084a600c401403c0c04e07030002001d94116030802400b03c0080d040101a2a040031010390001602e20400b00110300404007580c81300510302c0c00e0784242d4504441c4138003101c42c0d20302d485407041203a0360518201c0148112411a020207000758100070b805003102e0341000c2d080340504140098264080d544c00041403000302944802030741c408810101d4070109208601c040395140c9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 990351519 1250 990350269 990350287
    0x912070c0e091f09030e220504080c100f060e1009050408131502070f1a0903211206010306050d030336060b0a0312080901060902030a1b0f05 62
    0x1220307802956141100c9083c00d0a102c90b8001029800d00300d42c2d500e644140c00424958000303a54011010300b52800a001c404000a107801910f0300100040d5a43d44c0c0d001041c200711484080b65040c0306070000700c03622082003d0303e850041041202252429250a40010f0034170015219580301d48007070b40b01690f145160468210207424020800c0701e80400400451004114825651001d00021070741c094500b2149440030740341215540010910401040c010007803400d58144400316142811042621500c1e00e9010900c1c0c080501203070f111180e07101845082408105010740843c0c0e0b0708403040103850300c440b8019400c482c0f1038000c16070442c031002070740303804280a9085403460b032100001615041070000d114410340740c111161680781c684000083d0003480050300440491440445c1c032a41d4091940d41e40d220000c10101051090004020014000440031340c07103107009024401c800d650b42e1501d002d4080080c0744002c041d000900e2161030b02c0601c83d20a40356209000300729114517142c40101d0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 990352769 1250 990351519 990351539
    0x12070b100806010e180a02030c010c02011e02160e040f030e130e06072003070201030e070e0a020a030e031309020306040b12060f01060206100b1c0c080912070c 70
    0x41503058040440c03034001845000821030305000702120a8050301c50700b8414035142e0155648124410f03964445c49190000da6004a08100d200b0401d0a0000c0c0d20740071403005803071181c55006c410000c0300c0031480d0b401e1095000304a8441e49150502c040c00350320f4440500b0341c540700b802e0301e01810303440a000142e400a8002d883d00440148001d11103400002c030420304c0d406641031480e104016822a00a000c0c410b600f04141c0201683c9104e10380244034502c4280c5aa80c1c06542c0004c0c0c1056225020000c25a0307044c09840043c02c004900c142c024600b10324000082d5100201080c0060715103070010022110200079190040003061002c4030741450042c4400180d00054151580141e03221a49076003561500b108040300d0b05a0405440b461070301c09640180c12005a12480a6402c6101004411203000d9481705c152101000e0482e114a040500d403003030f0680e101c5120500e10301c1d000840d58070030340004c0114410034001044030003681c513940e8220494050400003d29051561605111090781 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 990354019 1250 990352769 990352771
    0x703050a140c0321060a08060f0c040e0c0c070b0405013009060501080106060302040b0f0a0c0b07110d110c040f0f060f0f120b342012070b 61
    0x381c140aa400d14100103040341c15035000d200705204180381c12040040f5202819500b40c2d00200403038800404624000c265521504000c14281840010400003450306803030000792030140100221114951404182041c595400802103d805210b00c0400140c600c154801703e5041d103006940714a07c00e403069101941c61100d4001c40b152050f0b0451044101220074401d250540d80200c00200e065403610206a08680b030300e030882c00406004002c18000c0144200482c0d000210946040340ea507101c3d15402c940b030000180e801040f0320903210a00002e03503030040b4106100c003544810f41d0b164640d05c41064a80405900103043c3c90303003001400000703915059111542d45140ca043c00720300c8829030030300d4100f01e40480c0c2000132030031404903082c0b01c00c040380d0115802034104c0380002c4400b4915a282c42190000003410013000c6400380ca00500200b0a0322100000000b4001d44960410316255001d400d11820745c0c10254480000242182d60000006080c50085607911a90703251601a480303d41070824 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 990355269 1250 990354019 990354047
    0xc0a032016141f0c03030f020f0a1409030304060f0810211b060c0b09012702030a020d0b070e010c0b01030b10032906040203091018150608060601050703050a 69
    0x120740e1004100c10341002e0300a01c0c1602055941c400304c2d6885180107403c0310805542030648520602901c0264050ba0088505408160410b45d00005d001c1c1c8407010503101e06846141c041c0408503000400617080341c0ca003240d80c10140c456085a64070728010840c44e0380544950b0220020101c070207a00d22920682514446000d0703441c111291501d448510200d81e4550700000015039100600d00c1800316a8000c190070603c0c500c0284030b00304c10307421425443c0e040001c010b01080205c010306400c40d0350803c04140c060f60301500070708040400d4246142007100491303003000420640400391100f50303ca0071501030825404160150140d080d078648104c03001d8001c0084990001594020011990303001c450101e81e5403039101e1401058000600040002e0041d21040c02a40103106001944402007085e052146c000c1d000000d00208414074900700c00320380407000d800d5007152540c5101d800c2e00340c0c2080065902d448115000c0b9101c4100440c0d180c07203018405000a00140084c1a240d841000c0c01c0d0380c240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 990356519 1250 990355269 990355279
    0x115180b030610080601060503090303281802120f0a140c060c0d0f0504050102100507120f020705010c0e0d11060910030e0d02070b0a080c0c0a03201614 67
    0x1980010a2074003405507100025414010b20130080c10301c041000c03d0240800c1d1402908600780490482c2c0c0d41c0c000039000381e007280c00c290b03140207014011500c5040c00548542e014455002520542c00245204440580c0540c40224080040c88800203080064443c960010410103040d40c4400ca44050707103000c0341c04d140c026000e010040d552420003401c900300781131000d00450741c0c4410b00a0002c1207140300030750a01609102c1049039a8000c2142d07940100324142c0401c141c0e5a132880ac0740c0136010411400b00d243e141c000a10f07180451980a4030007284200000c100c5c40510100640705a4041d02a20742e0117000529a800000d10911100e401d00d0f801500c414148250300b000901240c1c05000c0320b0000036079500781c1c00540c074020000c0744800070351400035020742818070902c5881480b4030810304051003540340100c0c3c4886520030440d403030703841c094050340c2c0302283c103107802000106810071010f94102c000045d800e2580001c184104040001d105600c4075a1401d03600f0090100d180313030320075488 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 990357769 1250 990356519 990356531
    0x6130521180306010630020301080d09060207060c03080a110f0a08010509010311130204081515090105130b060f0706020c10140112030c05010f0e070b0309071202060403120206041103011518 83
    0x5048240023441c00381c04010041c1119080225004000454552040046510048040191542148410035501e806180552480d51184080b4001c0c0030050809000c0b00000200302003800d000d480a071203820421b03039030641d06036603071010010480310a0102520280300201c150000380303131040b0402505440c105001d41801d946100741d07410400d001d0305030801d448040d800c01964244854040440d5041140d00d00b02310750408020960110156041c82070250f40ca0700541c14540d9001c0a0341e0780302e1110145180d9a5030700b4074000d00030390001450309c45103200350b1038a07110b140224025003c0350703d0190003843c11a071920a07104529007030f0000c181c00740010142000c020540038001c0306480ca40c240720215607070780c03051099803800c40587d0001c0c0a2000c05c3c000d0040000c1c0110f40e260869940c2c2c48c1900c030003203190002400c03d114940c0300400c4800416140045150040390704d9128901503400e44403100b4600040c5030980302c0f1000701d0034130500030ba0001d0000d070740b00440308124204041c00021718 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 990359019 1250 990357769 990357857
    0xe061b0a050307030e18040f0305030717010b0c0d08071d010e090a05060108090d0801121b230409020d2303070507170a05061305211803060106 63
    0x250f52101d1002e4000640ca2840910b02c1d08020400e5010096200f203044038030f10f030507150403c240c00003c0c0300600708500000402e0380c03140300e5840d030221611420014201940d481e05094481c0c1c0c8680c2025100b030040c4207031400c502c2d0040038039a03c50000c0b5180c40e006400008846400404030040950500001105501858540c400c0d000d00c501465000000e8034140000090545680203148131100e600000d0641c02c0346605c0b5101c06e0440b0305440c03258084801c070703103007541205003118900441d0500c02c500001c1e841c818100d803103042c20030680c100b030003550b40b00d0103010070384020040c041d4002540354075090020346d800c4122801071403251031b1150b070040c60b02c5407a41168030a450aa80a0b8000d140a11200c25038849903d141c107503c5000342144903043d910b0f61340742d500003056989214003034680030003440018040ea00c1140c0d119503000c120418181c42454158001d03d101040f50710340c1401001ca50b00f0005003050580300c09495965404107821a00901000140e01c43c141e5003d13211034450b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 990360269 1250 990359019 990359023
    0x909033203280b2107031b030605010b0403030807110109140a03140711060f0d0213030302060a06140f06070609050703021318060b01030b1207150e061b0a05 69
    0x100681000b01101c1d410300075001d0b941010010342e226100c026140544110441d41c0d040b4040040280b1a00e00504141c804c001c480c0c244a90707540050035800c40442c2c425120f0b15104810400d8074402d85080007079076210705440245d401503000060106903800f01044100b0300809180303400012200001c62001541d9980700c1100300000440a403c0d408a039941c2d08041e0003a24140d040c580b103040440c101100c03030300c88503200172800c04190b0048a0004205900810a40c21564503010721901503507102c0000610301b100c9245480190700601903000801d1281e18280911070444c2c1902403e0a00303201d90740c003007084801640707041c7c9038462401c001a07000210385000344125140940d02800801e4658018040c84002c18243c5900061510b6507401c085035a916109403500d8111800040440b10700005170300400c1e5a10030241d1120b8038003040310004200046d444180c41c22440c401000c1980d80c0416180030f090444600d9010740103000c0410310200040e851840d13010b8a5040340c0713050b006600e80e54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 990361519 1250 990360269 990360271
    0x1d062506020c010c03150302040209030307080715050a0b010c240e01020a080907060c12030608060a050123010c08090105040b030f010f1a031f0503030d050a060909033203 75
    0x214003035004a12080c00303200070322803084101010704041c4180d00006160010b80f0401d404000e1040ea0b01107620203c40d10104140c2c0c0044c0e500003c4160b440c0039909040101481d44403050760300c28102000144458454018016888010f840e5214012984c0da40c1d03887c0f44059018460b40c9e40b088100d44000385650b805000040002c4800040e0345001c1a040288885401418012140d01429041001c158080e008040054106101c00121400038900302e0280900d03511004551242c50140a89041903501940c125280043c048004203950920309050710720700e80c035140c0072038801c0003024081015074000f0490300c08140b605500d400c2d1601d221050580082c2c50321524040113000502c5a09148202c042c00780800345070101c0500c00d65404451030f403000404c0700c1c4a00007001c0300310001c1c107003400c203410240c00001c0c00d80ba1582c0c8002d0303000d402400f084400c203c066081600000340c0a0891158403440d64056664440780039072040400c1c1c0146028000c6810056280c03801d00b82c41e24004095 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 990362769 1250 990361519 990361523
    0x507021f06030c0e0115051e0703080907170705010804050109062d05010312111641010f0e04140f15090a0906020d15050a061d0625 58
    0x5125400d43c14242154034083d04401c1e140c1d070a02e801484514440d01c00910580940d06d03206030303600c0441d134140120b81d07141120707103844400c0401c0f00030400d60006030691040514008a03102c0542e22100c00000d001401104241c54107c40c40c140300303e511605580e98401d005000119160a4907903c800841d8400041c22014482c40140e51030078000c40c2d9a100120701e2240e1043c026541141c48004e05010072040314011b00c102c10094003001e11007800985038850809040250159070f40d41c035484941d00708843e02c3c2540c00e0081c83c0c04860b80050100000c818041c440f00080391000400542d0004582080e2130300b444031490810900c0d0341c490280c9100c00302d0001d001d0a5508021042400d0000d018200010100070306520b90441e403a41a0365562082c00d0240c0880c0742c12180c10b004000740b00b1101b41d44d10550404042143c185c075822100e104566040e507003182e00d903589210840342808061344181002100b090301d14840d25104000d440c8000c070102e0014101c0c18500000c0c20380d4841c140702 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 990364019 1250 990362769 990362771
    0x605070507120602070b0c0a02070e04210206102301030203040314040609140409050615060c070803280207090f0e2505030705030304031205040e0a060929040507021f 73
    0x300c1c03002c1101c1c00c00002c1d0440d034081101f03803c0214111010391074003101d000300f5002c481d843c0001001d000c03000302d0300520341401120f1620281c031031030b0000b5294207086070710311000ca460030b00c000388111403191400c520f40b058401c13041146101c200110065800a0802e808010140e0540c0144003088401840240380d1078403200441481d00c203004496090044030903100c3c44c505490071001c42c2c400314a1591200715810b0b0003089000c02800904103004201058100e44203040000c00c08140010050840c1d80983d050684000c54000184c0303a00304001c8034610040c0c0114401b0495502550040d180c1c0c403d0b02d0a002c1405403105104a26002c00302c48840080f007c20000c954280069100000203410183d014290150030140401d40d603105600c00281180d40c024140e9100c81c0c45803080e140944011140c4207a24104540710750080c0190340100d00c60b50b440c08501800d14042240c09503400b41c0140411521012640100802040002c041c0c1c4254020701520400b50708490101d8810700142040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 990365269 1250 990364019 990364027
    0x711032a0a050108090c280e180607140c01060308030c0318030a0c082206090e09010b0a091d010204090f050604020708090d0c080709050117060106090605070507120602 74
    0x800c1100e01c2045500040c1400725a07018030400403004101d440342203805560b100f03400c03c0c20304915400e500d4580100d1004c0d03188800046016000003550900903000d0b120504507095480d01c0290b105e440030b0318001e022450300e2b917201006032561406000c1480030000006805c50340c0c0c0c1c403a880f150788112440940b000c03000081201c1108503a9580c800e00c0c54010096003401503004010340011069180038095110118070916410001012490241081c02c04060072503901c1c90050b20741102802160720300703030800d030020b000340030144200c40c4d0741c41000303042c80c100070f00c1c181c40b6a0042c14140e10512064110040d20380c0c0d0101c00340001c2000380086a030025088a803990300780300710703040508100d04c0350740104212400308485806448440070201c42407003130080c01c3c0c81c104082c1c403803035884603039103000b40c42d00090042c0c0a6400310307040721580c1c080c2c030780070b201c02109564841c0c0d8240136800215404600038031400c3d101e2006440b805116104551820361503201e40080322f103070624201d8405170001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 990366519 1250 990365269 990365353
    0x402091009020d020909090a0b011206020d0c0309020909030910120905060709171506120a050a1b15020703030f1202030c07140304060e0418020d0302010c0305010b07020105071103 79
    0x7006c03984d002c8029405095000280d958403606403c0600c6902c00400b19141c660341413200e0303641203131a0550300c14010040d10080810160250502c140141c1c4201200d1000569414001c01110a0504003c0120540e40e00f007082c15101c0da420a41c942034400d80d54030102c00080d008201b01d80c010346440e00c1e030038041c40c03070240c024114246108543c0301d82e80083d031310040350001e0600640d80211007115420f0248400c20300702c51828003030301d5024010b0321501a9480c01e0100c0041030229410b59402040c1410b5104c1c1143c02c5c5d00c00c2d2003100080107920100c400c0000c0780c440c103618a00011f0317a28208808880b980c074600140c2c0c100b6105210341e07803400075060041000c100354415400b02480c010b103007041c0c0380c40d40c041c005d00d02c145001c41c003131a10360020a80c2c1c1c0340442030f03e20305140d009001c86410303080341c00d009009108035581c0f1004646010008039081e8800002d48543c01d0381692800c0c5401000d60300c101b08a082204003540600c02c4404c4080101d4295114030f0b109203000c9084181c5036401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 990367769 1250 990366519 990366529
    0x10903080f100f12030c0804060f0806090705030a05102d090605030601061103070206161505280605151c1811030a14031810080402091009020d0209 65
    0x1409100b5a1210b0380d80810494070610344030f004850b04480a102caa6501d41400d44100b84050f40c000d1a03000006008144a03401061940503456982d84c0d04481756105010f00c00400c105a038410301198040c40040e05980740303a00070f0342c0d0040c5803070440d0080654840c2ca1890144070344402d285809501583c494942048010b1030004000c989000e2002c00d01e0200429180c3c0e8041c000d110401809411500b0402400c0084442072540540055980c160814403028155400c0c0c0080f90f214110303680c03481c0c0100450080d14083d0400754120341d6407515007807200440443e43d0010340306079611558009815900e0341b020640004000f200700359a008a17040255100c00c07076892060446141c0150b8407840d18646013111703119640245000510303025040043e20340560204000c081c5070142c042c3e088480008000303000110080461440207010410402408510301030320300000440c03140000d0058a06240d01e00e0304610b40260014201351100b8803541603a200d944070042142d00000e001d001401d003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 990369019 1250 990367769 990367771
    0x8030d0b04051608070201060b0f0405180103051e0a020a0303080702100612080c030d061401020f0a02091b0f031302120a1203050a1d01090209180304060302030a0e010903080f 77
    0x200722410401440c0402c400310741801d41c89190b004009100d4005403505000f5030090001c0e05020164603150815901001c001c6c1d071050250034042c011400040f00c03500c41d083d9200741641c0d4440e01030f0041480c054501d80f60762800c04440345117440381404400150302c60b0386000c8040c50080d03560100c10314281002038070349000003104043c010300d090002c00060020458482d8583d80c0008416500c3d440f10b2900e031305c2c40c0540d101211a65191410000e40d8083c48524000e002c00c0a8080e0380081c00b4120f02180c840003c0d120181d08007468100058403010030101c0483c015058404103070410720483c060611a070000c5440a42c640120440002903281002c0e2012040310580000c080055041e80d41c46802d0648111000a043e281c0012442069494100965460300030028502101c01200c84078082c290f0031606030b02440380031011815170b491410181c098000181c2c0258901403800f807084000b07501c020580a10766075180404100d00c0003e000344502c1f81d001c0c1d40d030035042d0f0900f61454952800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 990370269 1250 990369019 990369041
    0x32103180601060c172b110c060c0a03060e0a0609110f0a0807020f0d020703060c0206240d060908030906010605090a05041e06080d090b07021806010c020a08030d 71
    0x80504010441164442181c54105134401c065404a00045d60601070078040e250306c0c0356808001310304024885c031144218000c5841d0740c04007804240c10746403880c98284a81c055042c078a070003210014621141c0000203100704001858009501c0e07a565507014800501074841c4920261155403c00120003d40940403051841805030b9103000e410b18059281d500c40d054a07582880f0310000010703201802400740740583d10b459010782d00c10b46400c0704000e446a0650004941d1180707003da00c0012140300003071651141e82120104c14003c40d0011070250484400e902c050351000c15040450009036840c007920030800d202e140c030070340c0300d091130840c07107061010503003110003048002d000b01013659441c034403198112442550000303449040e60a4603485034080205544029042c894001240500095595108041c43c0e903004d000c030b500c4100c40703900c91052041c065401382600700300303505c400107003050b554020304141012144403c183c0c1c00700307442c0856544160fa06400108941e95090114010103024907 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 990371519 1250 990370269 990370273
    0xe180c0708131e0605030f06030705060f130f06200c030a1101080708040305040b0a0e4507030e0f0d08011d130f080d0e0a03142703210318 61
    0x15041c008014101c0c040106007407c1b41a00402140d0152000c0c0000760240c00060b0000f50350700e5644021005552000d40441800031b4507040c00614400d85401010582c1c8072537032508400c101d1680e07820419400100300f0005801084c050312950b07602000010340d01c6220303059440a64010400140c4001002030080d01840313506020040002d40c04001c40e0103460200118035280e4074440d404940c0c0b59548c2e0f0b00c15411401d4a1001000c030102d51505a5611480010300400b240020044641d20b00e8180030000744440c41b0f02c0416102c0c7e00a070041300029641d64111003810802c422007914001c034524050001c11038180041c015500300900103072600014949113201824140c0c0700300d044d012a21000380c8105241d007649400c02030030300c0413a05180c40e041800e006058660b49510b4890200c5501200402d09107002c200c4043c0c010703002c0e241c0c41c0ba2030113415180041c05800000600a04020f07a6a150140b2900703c00b03001982e042480880d41401e501c20344034504213070501c0b40b000c030140442c2815 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 990372769 1250 990371519 990371579
    0x31f060f260103060e0c090f01030b1e0a0c1e1d150910170c0c0607030b0306070c050304050a0315060915090f15061e0e180c070813 58
    0x2940c250000707411260f204400003020003002e030701642001403c02e2010381c800050800d00c0704100c20000142c1c140c9029400740c0d11a5100d919008001c5604403102d19208841e5400007546180c469124500000c01c5040c00c02c0d201000d0705460040d032400350b10039008620042c100309245034141e60450460007050b02c50440d1100c065201d140c05008000000744200200c0003406c042070711500c0c0582c20540811445180c5041459221805030820184082213220b500001034105209005000d04070001502034400e41d12047c2e41100c0c1e486840000f41c5151004010001d400d84810110100a50080c6010f0112100311500a8261180e55214544103401c10380e007a1f407080c90f201180c0c0100c81441c06c1c000f4010102d08005405080e42c1103500503590543e21002411079000510703100d040d002042e482c543d142c81800c082d0f03501c140125401e504208403411004850000b03003a101e070801141da40081c107010042c2d440690580c0115104c0003003000318402000010700c1040581c1c0c204007114848020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 990374019 1250 990372769 990372827
    0x1c030b030a0219050603070c030e03060112021002070b0d020901030b12121c0f0e060604150909050f0a260c1504022409011b0f0206031f060f 62
    0x560380c49201c01910450341840c001c40104842800600100009010389440385003942024000790122982a00071075100b020507103240c540402c0311410b0726403000d1541196511074007445001c0c000b000101c01540300b01c0101150b156190000781c00c1d004d11280e400b5a4803c0b02c42c0006043e150800603450090005c0d0703005507405240410b0020681e0014040d540d251403070359210501c0003000107400858103180030200540749000c1c1d08444801c600c180100d645a440303090500c803c840d1850384001001d03004e80000c2c04455070f9a00310251290146088400f1b0404070b500c802e0804003010001c0300c0d65042005c2c5590b00c40c060001040740d1000350615a03081500442c005a26042400106610740c419100060301315555902001d500494030038034545403890001c256541a4001200b80b404162491420b030540860030002c800e959034000015011903030f45500f4403100b500007412489490480038404085060280f4050004200696035400b121100100c060016030050105071842140e40d121090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 990375269 1250 990374019 990374023
    0xc0a08030a03050402030a150203011d0615131d07020712080304030e0109030b090c010e0409020d0b040602041205060412080f0601120e03040f0311030718110d0603051c030b03 77
    0x40e00e0941d8100481c40741c0d81e5100103030612500c05401007005580b02c04800d0b03410300c560701850580d40401e02628040b80d400741e070201f4000c1e08807800c1d41d225103103000316020b0100e03041c007610044480c0c1c014100e05940700d420031500300c04001c02503ea102044d008021409904116040040440c44020407100044d61101039661200600140510001d56400e40c03d80c0d00c40d51202e00215000061580107050000e122602d565203444140e00041240311030f0a8580303420b11030400c5a40d402041040410301a80da50b00312000002c0c13040d04d00d5a400c0c400010101c52005168080030300c500301420382460189000000c481010096404000881c070400285018a000c09034001c035003400c082140503101d4054001600c1140403c0e1680d00002c80d00089035680c0703003c01c1d01502e100f540300700d05807405442410358032101881184050241002200284099076010100350500035804618107080903101da015206180c0c411a1907902c007c062501c4808200300e2150302d11064a424080a030b20480026 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 990376519 1250 990375269 990375277
    0x90c050d02130b0f1806090c0c21130f0e0c03010f061112040914010503120301121a1e060a0f06050f0909090a1b06050d1806110c0c0a0803 61
    0x291401c0d41c0c0f812801e03e682e80d074424848081030000d0012101d0161505064065070301070b103415001301018030108103142000c0040d100ba07812001d0052005000c03401c1e80c040b0710040823900d00a00c1c0d5040021244030002c80004201602e542e50007480040e00c1c00007101000c040041410042a00500c014041c1000b80f00c402c0044401380d1404010a42c01503003010706124121b070440001c088001400907808141e07402c405001000c00d4604256603a0351030505403281064404001504000c00051204543e8404e0180d01c05010302070203041c0c0050100c200405503815900c1c450101c1480404250000c09400c905070b22010a9801c540e8480c0340084c03c20050103140901c005015010406601d005035071002d03a0b070101c4000b000e9105500b400050251120344102040c1c1d118202035421604034400c061030764044811a40c2c48a00e490180c0701110014441016928805c0d848030402d032010520500840c040601c90541596585002144041c03030808a051100d00500080b18100144035000c0196 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 990377769 1250 990376519 990376549
    0x60504060815030a1203020d060f050f010302030c03040f03020f0f01060e0a0b03100b0409080f0c060f1005090403140d1d0c0a0b13050a06080f07361206090c050d02 72
    0xa604074001c805c1064019001d4001c06a00740b501d81030740010b034801c218003030300d0445100b80d82151070040280c0c011020380c8400c41e14014956800c20100d00022a46001c45160500030b20507581804131490400341444225094616036a456500900140c00c2c040d088542107001c034030080003005034a00219403601d05255921042650729017070f084240e140c0b03130807031001c550740301580980d500a665200d500d290000c01a110103482403c002840c0d89005405480c0500480c0090380c80340e92400c010014104c900a004408000925903941e240c2d103247c2c030182c6900004103002090405010303252800701c0e05402000f12056229194001a58403502c007010f00742e0b5020b1103925a500c1d84407000f81842074590340f107141c00c00b103880d400050141e8070031140360190071a2110611243ca030b40f102216a54800180c42c100e20081d0200c901c440d03586282c420b80c0741007402e003000c0015552180031390701400c14401d090f20150384840c0c003c0208a050328060000d884126840d0344210703190740128218100c0d040b52 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 990379019 1250 990377769 990377783
    0x506010e0d21091a03100f0803030426030f190c1205150613060306150e10120c0e092a0f0903070f180b01021c09050901060504060815030a 61
    0x10b0741d403009114107402000360540381440046840d0905080700b4a0703004031110f424059030f1000c085444650312600d8011240040d00030340c10b545941d01c54007201700041000c491485915070b180d0364400b140d440a180700d80b0038004064164603040890f452808440b040d000f0b0040c0c60800280f0020f5040b005540c5252505070002800e95240390074407a4040795a98070607404403000c900c0e041240c10480005041d41c0f1580e6051043c03035603444061580103030b0340e5405000704081104d9030006d8100040341082225461824000c9000c1e59207290701110402c01640b000528811895a00c9090001003290800202d070500c64228440344e00d114500c6c0e01e140448884003c000600d175090388804003da421070039004003505c11166070303026841e1901c2143c0c49081200d0b00d01480801513a00d0f14030824a0701881a00034041010311034504078034001464a00700240218004046420b458180c0054040c11310351f10b469603102c0c1051400741c04074070300410f040c115035140841a00c880d1000724006039032a0348584 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 990380269 1250 990379019 990379073
    0x120a050c011806091137050312220612090813080706020c01090806131406130303060b09010c0b0c0d090b040201111b012109030f11010207030e13110705010506010e0d 73
    0x2101801c003440d1f0015a061180c4041c80e000b4072800c200030541c44210700040381c00695945c91034007500c0010f201d680046110307296040640056504040c10491003440560700e0001031081021400072580c0010350246e000305804d1100316010001048903200908043c2c007014035101d46179a030703401c00420341ca441001d5142440b007080740d0707680c001d0b00e240c0c0d1030400d4800707038070b420500d1000420303403a4401d44c0001c0c201000010407448030401c584441c1e00695564942481d00d4640280f13040c000b0b440107039802d01c1000a406000c0140c0720780c00005100310150542410a400018020301401c140b60b81340781c1044007110300100382401c15180040d0203080c41c081c4180400078200001000181c80742d2041d0415010004041d44220300041d802070303c0d22420211504401c8441c05c07400350580050218207549100652860240100041415602030115400204000c5120550455003086405a4503482440203640c0c2068007802c00c00c60554007014054200d44800c00c50084802c18035000c0c2001c2a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 990381519 1250 990380269 990380359
    0x12010504021905131802120a021305041509021c08030105041b211d030c0d0305010501120b0d050d170a05040b130c051002070e09120a050c0118060911 66
    0x1110003814940c001f0310038511000c3c242d11a648481280303504034858030310100440040183c42c811640a02d42010743c1c001c003241b051000b03c0003400c10600076a4080d0044641100707040c00b41104180d401d124102142e1294900010301098404160000250170881d511a503405a03004804140c8000340e40000700302c041c0314020000007000102e4451800e5000b402004003e00c10000c000d00391141408125400814a54000c070704942003802204d0018141c14004608010b00d0340214007100c400500d00708078051315a8036070349810000403482d07010601c132810281002e280c9042150384104100018845450550348e40521460010400f05051700c400680c00d0074031447c4a200350280c00040c10a010615030900040c0d41c8140c01c0c400d1042074024000000c0da99040841c18a41483c810b4031785506100440d00259040e4000e130324440d140e5980c550301d81080780883c01582056038020000003c000410303041c400f041e0080c03030401a00032600c140c4521400d050150b4143c2c03002600f1040c1948019002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 990382769 1250 990381519 990381551
    0x2100518060f04060807030e0c12010f0203070801050102160602030906030406020c0f030904150312081f18390e091603060f0e0c030c07021201050402190513 69
    0x84940a410501c0414180301d60396041c0b0081050307139035544442c01d241d9100c09088054440000c8a401030750010f0800c0002ca003403019038029680c000714000b15100c0304940350101203030402c40b904070000740440010041c2e5601030000d6030448103241e0442004900f01000690f0360300c05c03003400a009180000c00581400b40c4c99041d24068184002a41d0090740c101d04000d980f500008105840341d8908a5888225400880b1000440b6400b2200d54640c10851f03509854555005204590005400b00c0d20a440d503140085000503102a06a5400c0c0901b00e0400c00111507074060910580e5038030b10715000044508044d215101c04a48038502c1c1c21004406084038031203105680507810100c8201403040b00c20200710039084015035a581009500d56603500401028828821200160707113603400304000c051281c004560100f00b031100c49141c100b030341d03011030b001d004c00021001c0300f80d540d202480300b107180082540c001070b0b07e000d42c05584203080c0000a15480d00780d5440a082d15a030f10103403081c4034a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 990384019 1250 990382769 990382807
    0xd3203060a0506161e0302070e07110d050a09061b060f060909080903240403031808042607050f0111160305100501080102122d090d0806060403021005 66
    0x201920060700d41282001c43d043c44078003400d086848014030210b00714450b85c0d0f6110412529016802400c1052a2184880e202440909400100051500b912800e44006c0128000c00d181c2a0f441550f41c03c030f00a0000c01c94003030780c0c01000410106040c0e400c0c0032640c50104046568120724002006140c5411410090600b03134003580d562400d10760f200042c04000406405650010307415200819200034006201410300802c40240350006404178001c00d100b98440601d55491030340c080648050ba13207030451203800690015038054070030070b80c0b0240d00f41c44a4154a042044800030600307181040d00040030741100700c200604108289140001c02d030b80c1003101c145810000c0840c0c241440d180d080c0070b9110805020017099241c01c05000041309041482201c01c200a2400c2c0c1d071460f61140191145220580d17031032010800f0032003090f04820700340340480354003895101004003204910282c014003a801c005107030300c1c410b000520041015840d080f0024080c0703115490001d60f1806820340506107915 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 990385269 1250 990384019 990384029
    0xe010e09100905070e030f0d02070e180a2d050d1d060f130b07020105041a0706050c130e060307090e030d090c0302010801121203110c010e0d3203060a 66
    0x41424240704001d500f0000340100030031700f41c007942d100c1262041d203160344403107070803407400140d1140004000e40308040301841e400c412802c2c1014842c051a042e06850441c114905039015141203058540141411544a17221a95482055025800b41c0c45540c0c4401b01c05950304180b14940000103c00b0301d4440e22080b4504c0e0050009880e450014071404094100b881840d07410310500c1e4000c80c02c05203403030940b080590305a40d06840c2c5400c1401220b41c0800d54040c0310a060000d00c00ca00004000e4003a0a124450b222080d5850350103000122100c4076140c1e00011141014400b0b110f69600c0100c3c02d01c007903481e01240401d10345500d00b2018654420415046660391901c8000b50800420804480449000340e035003c0003662180350114480b40a04070003001240c4110b1000302c0c1034080d40009498078840110141801c114210042c295002142408041d42145815002140e000344444081c508841042610003140000d00c0042c2452885200c24011020000900903039580441101401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 990386519 1250 990385269 990385271
    0x10090911041a0415030201200309010e04020409050a0905010c09080a12110d1710150309030e0a03060207052104120503190302190e03120d0603080c060a0c0e010e091009 74
    0xb0034080d0708503c8804e110b00003280000c0021900c24140042000f000c8944040d1a0140d454010100e0040d15503000b0351030705541094090000182d001001e110340e920492241c000403030750240915260342125900714a070814046105c4040c4480c00001801d081041d0b40000c4000c800c0c0d0001c50103807000101000044014490f02880210003a44445445820412050300c82e0440e244c164041c03d6070303500e600411031071040075210031112600c25040a40c0850280c180124840a2400850101241c3d42c20580c0d016400147c00030800c41c0800c015552410120001c0100301030404142003240324a2042e1000c1d448580c4c20342003485010300848203203008410704149149100400540a034118002100010350364400a1410500400101c070203580c0c0203002e0032051108158030032241d08140d4104e04c0b8141e42d04008400520f4050003818020143c5005002d45d00d05a5860000c1d0b9807800c034140204211641d200500c3d0747c00212540d00b1034400c480035541743d5503d8a1220881100354840a555 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 990387769 1250 990386519 990386531
    0xf03020d030c0306050619090b031611010c0c0b0c04080616020114040c06030c021e06010515070210050c0f1e0c0301090803011215021210090911041a04 67
    0x190001800d0114a1403900c080c450800728400680881d40540f1600f81c20002c1000350b480303000c2602c0341c400c00b1082c80d420444056910303901c032018039401c03c89180380303c02d404424080145070003903c0d907990b00c0030440c0240804510000000c01130840c01c1401848660600042041424409e060314040c2c02031700c084541d0352405000c8008004000c1e50040c015528246103800d5601c0c0e40d1094520681d000416000e00c81d20b424000c400806600c1039000441c018580c0344901032110004880c00040d07003000812a5505207000c000744812000591000c0003002c2200b1030040c1c81d11001141c0c9100345091242d15604403041c05800d1141700b0b08100e0050040f4041851101e8004c0440300303240002408803031208040300c050500725003003410007502d070040034401088403907640240348050f80d10400c0c04040c01c01041401d01c1c02d80e0000c043d442000d0041c50204407203d4100755020700100f0300c5030170512440c085501c070301445901c08204c2034001c42d01d441c5401c1c029405c0564610424502400c20084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 990389019 1250 990387769 990387773
    0x1401021011190f0c0213090f0b070e010903050d080709050405090d08060d08070f030e060301090515061c0c031e1410051c050a060e010902040e0f0c040b04090f 70
    0x11a8041e003050611002107a2070000018450070499140c51495140d0300c00e0130420703400300000c4003100b2480e8552151034a02020001d03005e10f50740f110b1140b00d4000301c9440d08100d9000341c4040130701c000150400100c0c0310f04001040002803100d01044450a05d02410707114020211030007806500800d80241c10a403c4c403a07d5000001d8500c1205040e07907400c18603460707510807c1641c0c0043c4c0c2c005480e1200500000022440c42c0f82c1e261125807085c04d00003648000007000c41e541e50030903030007108156614000c00469143e00c1c00750b403201d180111074103840c2c41c0c14100000820600c0c000c803401410394900c008044580643d1006480b980210308003440f80c0c514003188006000e04038a8040312102d0000410014001c02d044401a0f91000304201c1c01c90981b180d1402c00069141d105482500c1039000d04808101c02d80310b03c40c80108030100204486125005000c1540c20700f4001c3c80c5944c0c40300559540070000810030303c008240440300403408220302400540500340086002d068659070182070f0782 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 990390269 1250 990389019 990389051
    0x150302040b04080c0a05041a150d0e0f010e0303160e03070308040b07030216080c121006030c0302240301090c1e082d01170f0f060702100b060414010210 67
    0x44c48408a91420b481600e450900c01a00c920050211010360307190548405807909000360980e01c48084103140c105901515103806603494211003031520741104194200c00704080c01149402d032000802180382d410441002c450b8400d24101c48800c01040068092095030280010002141c00902c070b207441e9034450031340400a510510341100035221b4100c02e4060003512102c031508580c0c0c110003502d98001201c09114200141130000c40103030161b0100820108500e10810000c1e5000f6500c11128608bd4810f1002503410500150519a0a400c11210100801045905403042044081411140540e01385d485403040d8111204907484d03c80500c91269120320703114414404030081d8120010980c1038a0710310068180e01010100700080180b203005250542800ba1442e441c1c22240449490079115080069158102e921750b0002c00070710849aa041001039401602001d00700041d40480c0001425849140300d082c5001002c1c25001b5050b0f8000d010f0506110f141c50010710920703c7c4010398030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 990391519 1250 990390269 990390283
    0xc2a0c03120c0c01020c06090906190b0711040b130b0f060408061006051c0203040f0f0b0103060b0f0a1229040c0e06010206070e031009050f061f150302040b0408 71
    0x80d001e485076441d07103541ca620001b48030801c000054a110319251001007032041504c0000c00e074980126002c901e2000c40580915039800030010801c683e0348907103040ca84003c04d03840451180d84268103010b80c040e040e07520040b40032090b1809120020706108003e0103d0080b0108407440d50b4011008540080e1070040840c0c468490784051307200ba00c001d42c03a044150380b14050040c5009150410741c01100b20440c0982c0155046401420b21043c1e51101390747d4134948210640d0100d0740e40b070500e401002005058001c4200c1c1c0040bc0764003080610340311010403420140c0c1d1140b803307902288020001444001d1409002c050011107a280490201c6440d811100d007054408403031400130235a0004243c10460302c42c074010401603001e020307140c499410407200000d480100e141d1601540b400580b075400307240708088000e4800c40c0500228034442d00341030f08181c0024141210000c02559842018000b000280d003960390801984801011482c011002801a5001028168800500031500500c001400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 990392769 1250 990391519 990391537
    0x5063115050c0d05030f01060f0e061809060a180902040f1d0c150d02070c0b130306060f1409040305121e0901060819061418060c2a0c0312 61
    0x10f4845404070541100e00d072004a81c41c1e112044000014001c0510902c00c0b103207111403d03d8016072001c5d24000040b801c0c0e000d01c8015420f11200d00d00c1d001c1781e0411754486980514201c0d01074420070300e010401243c501d80025124542940c90080c281159a1540105629018450b041100f40d0f011900352a01c15080081c2d44001c0c4640e07420358800b4903014015600d080c0c1f4011600d404c08614992000182d044002d048035410003641e80031504003298405400000c1c07541c1e9804c41d40c05e11b1814104100c2e08280c01c418a141042c52003403295210204540c2c2a80707400f6a0b4000040d6140d080481d030b1401031070b40d0341e05d0f000d031950103012107100c42402060001e401400000300303a45a440040e404c0310024403c2c4a200c0e00034580002512030789d0444030318600d001e01c001150f915294205040030704030861780701a0040c1d070780384c441880c16010459560f008840d111114903056060162981c04010402c07110601c03c40c4a01c50780d907100c018400300001e208045e0481d4001c20079444400701c40d400455407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 990394019 1250 990392769 990392773
    0xe180a0b09150d020f1f030f0e03120c0a120e0105270d110703170c011b120b041b0e100201110403140f0f100605063115050c 55
    0x226451510880380c0e02002c9030014410001840c90780d00344101c000c03101c400b550348403a03211910912086510306050b90035180383c0d0001039202401c00000c040b41c2c0000c01c03840c4181d01c240808904003d040840942050b40c0800711900c5800303580341151000300b5101404420b41c106101002c228005401c001d00480340711101c624100080d0000840010840009200c80e600c0b0041f20b5140070b018200c0c5071000b041a2302a20f002070345136224003403201c46007040002d0800700080c41070b90801c004c1c03042c0d5a100504544000184101c1c032030040c40421102c03202e2654503526100d083c02c5076200c0d0305c8a1141b9200303005030300e1452140315025141050302640035010700c05105141c141c0b0381c410312a198525200c205000e0400f811034503044d42050306900090100c1c810401450072440c0c0c00c001441c107100c0c001009080c3d98201c0380043c1c09890b81540440d011350414040449481e40340c0c10f9480254111009048407030040d565845001551584030b685500784c2c6510000c11035601000034140c414820702 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 990395269 1250 990394019 990394021
    0x6060906030513020d020114181801080303070f0c0c06020c090105030303090a06020d140f04031e0c0813211419020123040603020d0e1b010e180a0b09 66
    0x3015000c0da00700325891204040f11490300001464a403415141d001e0040c54410b00700e4109811080c4654002d000c038041294120040c0041e5160913613601540010b026003581309545000b83c0369603240005455001440420b24043c0c942a20404a1940786a0860380400f940c60f540c20010703403582c4511598070300613007020001060600b07001044a00404400000f00110b1009480707000007500b04035109425070341c0750171491802d00f605044580c000e4040c2d0081c4041c5041c5460041c0c5602020080030082d20a401c585800050700f002410300300d0303504030030000d41da01d0704c841034080d20848542041c0c204100100b851034041840242c8080c15922502a40c4944d00e500f00c0f615944480500400a40700d20380c101150055101e800e29107800f0b0b010a10402181c3c00a806003026070704160482d01c0043e42c023052040000107280501c0000382981e101804180006614100228030350071038103810700c0307030440700c0d0740c401e8540403122440790b0a040400d9400d0b041001e020710241c8010701c0d4161141d00140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 990396519 1250 990395269 990395279
    0x320d020a151809020319061a0d0b0316060f1b1101170a050907080a0507031b0308030a020a1b030e01030c02161514120609040c050306130b070f0507060b0406050310060609 75
    0x480360034291a800b0401c3d80c01041460300100707089c2e0052440c0040b45841e0fa59104042d217042040360740b0420b1214900d80c101e070610300018036550060110304100100c12501154152081d6554050143c00c100001501c130b48010040c0c804c406d900c2c7c181640140920304000b1501c41684c0024040c0740004252030140760f48203000c580c1d41149036030191180d0404403080000a0802c0303003210b08a5039180130342500e2580d0381c48021071a0000c4400070f070010b030000b03200b40082da88200c00300500e003428007070340d00c102116890081032902d000a583c0c0c185580c48400c000294000c21012980313030720702810141480c6d21401c1c201040d090702c0d2440004a00b02800742c2172603614038415107140c20508440000f49a40b5081040050407014005442034145942c020807203403030600101d0b00c2420300460b0358840280d5072520008044005019a082008200107541c07082c0d8003c080314201900f03e440491110003031400640146230070381c400340c4e043c4240752034100c80c80340c07540003030023110301549400e101280c6e91 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 990397769 1250 990396519 990396521
    0x130212070801061e020c0f0301140703050103151a04151e05040c03060b0304110109211407080a0206031005180906060a1a0a0207320d020a151809020319 67
    0x1004e5040c3c00350300204c1c103502c02410010042504080010008584005580c202c6442d034001652600002a1103c00502c107208815101c001e151041c088100030410100c20b0b2301480f07411801c8414031031516528480302d02c0c8615074001001d041c00e144171001c01d042220700204810001d100d0a4000c608012160313401c18041c0c4030388403c40e2507244070149180d8540d40c60b640f44140c010403880c10300c481c00c030700411a80c040d007a080030411100140c150300900d55017080c0d000d0900e1010b8101956101c1d103000d00c42608003249800400703a040c0d541c1c90312503e88508082001c0d20300d0f0401c6420016120b07581c0c1ea01d11241c41c00a004801000c10b540c42a220b040030f12000d403c40d8000d400144a40c4203d01800c0e00c04003004100c41c0041d8030560b5040360310303600340c1d007140d004007541c040e601c0e50303248130b503000d0200100790000200404580c12200c03514154045040d1041901c1404ac12582803032038040d0050180c0415000915609050440281c0302c0c90a00c009410542c0c40400d011030580c04c15220f0115 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 990399019 1250 990397769 990397817
    0x180212030405030712080708042c041203090c050306090c01090e06030c1020030d150e010b090a03140a110d032307080d05070206100f0513021207080106 67
    0x2c003501400d6140d041024900c40c0c1602c01e4002c07102090104020307400706580c440a0800341844e6503040400c089042c40c0da028101c101ca0b1080c00301d924100500c00002c4a0000e92400840c15040200e44242075041c80d401e24040c645c80260580501c8d020000d1081000c00c44441c6101c090300d400381c0103512261401e4403050129041c5401d68440c1c0043c07601031038080c400300b2004286103840d000e0b00d80c038013802d010803a2580b051004250f201240c07034030700300346503000b82c12201210790003010041d45441d4440408180c1845072000448001801034060b4892680301c00c051508511840d0304005050015aaa140d0a901c00c0d0f03200d004000b003800041c584000864503040d01035070350581411801c1d040c18400100300f600700403440c43c1001035800052002010303080008031040c0000c0c9a1800d2a0080d0814400408400c001d0710604010720030094100010710a031201510301103a12201041030800030f1080c0114800828144820840400d511009050586600c3d513107a0003420410150354064442c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 990400269 1250 990399019 990399029
    0x11091e1626041e1709060904180b150d060e162409150f031b1205010f0303090909020609040e061506030933100f060e0904150902041802120304 63
    0x700c14401d144c1d2001d0780702800039144000c011610b0402c80b800040c0031111141c0c8040e1140384040810000c1c0f004101240b90710410402c104025007490070b001419021007414001c00055548441c602100d608001e1454000100f41400c9141e41c0c03900b0000440030801114011150703004c100304c2280c10301c1846040c040f68034001c800c01c0d02022001c01510441e01d2200c4a808069664082c0d52030314803119100104469191191450040b400c0c0311082030b5a0160040101074400d0202000040da1000042013103409407180059000b420b480024101d01c03940000d2941f203410080c25102d41200803030130038051070310b000d0f00c0c40384440c0e00024800d2502084a0442e41608034040341c200303140342c4242d61003a00210445403605940000c40b219210302e0b0a88404030000311120007800032440d442c503202d01511080c01c05c6d81141c0b242c5000100070000c0107000403e030f03201c01c401064000099800031880036600810505c40b000c0300040c000c5111102c41d800f03a11030301d01214060309000c2c011007250241d175 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 990401519 1250 990400269 990400283
    0x309010912020f04180302010617150705120c0406031802090c0c07050301020f03010e0f01030b0103060c020a0c06052a0a061e0911091e1626041e 64
    0x80d01d45103032001c0441d010401030740c00003001c0720140080da0f1944154620300c1514000b4031148040340c14028215a000d0700074501c81944444c03000d0400d40d000401555182c47c00d100040b5503a40d0100845180c003851808843d440f07001e1741800324509800c4080c4c002d5905580d8100032030034600c40000c171001d08240c030203500031008101040000918100800c0030080e2601117070003599554010a0882e4040d400c01c800307070a804001400078070b124101ca150003110301c01c250031185d41107444107407200c5810302c8002e140942d6a07402840c594024007040b071540c5d03004145002015615800035205034000d5000308075860308911500101414480b40b035a03000c0004d001000950380c15a590b0006001d07058604440b1001e00100c5207410003030703014040c1581c0c480c025060860508030244172107180c3c05089064016500302d000201d12448180d0b0b1139021142024030340742c0d00c9004400781e52028032400406440e5044155000c400500c241c60360780203030303c1004080b60185c0c803d054060314110b4800d005001c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 990402769 1250 990401519 990401537
    0xb0903030f15010507021c11100e01050d0b06031807060306080c0d060b060f070605011a0a03110c01020403030e12150a0c0e090702060702010c050309071208040b0412050c03030901 79
    0x1030000b000203031001500605080789000711540000706460b26003100f00e0200d00241120340208015100030004600080e5241d610300440344d03001405c800c000d03041050401038082882c209604498000c4541c26001034041175413428500b15407aa03080072007140022a00c01c0060019115110b48140c908980c5201d02408403003910004201c132001081c036064071215103c40c402c8005540e0b2a000340b40340806182e040b0390706c2e406441e20406450b41644800c01502c0c995880641c02d07084c1c0780c100e424500d92440c0000300c1102400c0c140e902e03402141e90a007519803000c6030210425130050700740a81d8003002c45903010b400d01120034640c0d0303800034444020480f01000d40400c0490140e600208040300c607608020400d469003401080b4501c40031590440180d100d8070500464540a10511881c1c0c0754500d05607141d403030307c42501070b9100d41600c600d0b945544040840300601c601c41c01620080e05a807180950f443e559540d1050170003080d5082946c3d140070b1500001c94514001084031030318030741a1a20841 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 990404019 1250 990402769 990402781
    0x92a04090b240f1504080708030417070609050f0a270b09100e090a060207030503010e0a0b0a05060c1614090f010f090f1523040218042a08040b0903030f 67
    0x16450204c01c89010b61100f48000f180b42c000501076407028110220066860300e1420500016030a10303400141c940e034200c110300b48009940a80710a0984070251043c1025003410f8003c50204a043d50107840c43d200c01c410300d619a400a002d18111951103140c0030701007800c0d04010004502c105680c400ca00714103800d42080640450120035500040c500141c60fa400c1c0f4545542050707a01108044001400000c014080e040d10b01c0c903019001740022204000103a11240410031184079802400d2050b500461240882d1508003c0713101820900346a401190355100410000c02030841c25951007a0754800010f4003081c0500d00c00ca040710394100b9903500a0740b402e90300500130071080500703003000340e02c912440d8107880f44135040744001c184800001c2110141c254581c1303072a410841009101d035004000600303201c0b100c0d41002010000460b400541c1d5140701040c444a000300f903079000c40b4140d001501e09441500500f6182c4620300071a60300d41d01e03a9501d1800358580c0b10884040001081801c04907038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 990405269 1250 990404019 990404029
    0xb040606081e040302070f1508011527120501020405030105070c0b0105041a030d080703050108070b07170403020d08121303020a23070807090b0405092a04090b240f 72
    0x81c0050085c0162000d03503440d806440409515500141c40c16a10b649558000651003403070380f801450303c114002100164504010510900e06d40020608440082d000013030000e1840c56400070f009913844000300903c2c07490124043d400501c601c0e80300707510340300002d02e0481c003c08400801ca5807208044a040c1e0802c02004014402d090030040d4054500500c01302c0e68404004086441c0d00b0f6446111562501d00303c004d050f9801600141543c0d003180b242001700440c1c01c0c05a0b0310980c4d00981170710700d000e144143c3d02c0803805150f20280d030229009a40c50280036084d8010003920000c0024822166200030002c40d80b01c100c2c410003001030303108e41c0d90600481c0840c4003e20f4400040000c2d030904203040f5040619203901c6802207401500a44401c200c0b00040b031181d400420030070358051040c0c0c5000d502c4640c40e500f01d13451040b9803030440002196403d800c8000c2d07510080c0d00410800c0500840d0a02081403030701114048030b21400c4000182c4941c2081020382249070000304501846c2404100b404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 990406519 1250 990405269 990405271
    0x7030b130c090507050306030111040803271522030f120e190e1006080f040c0803132306031909020307080d0f2316050a03030b040606081e 61
    0x2035100c18488402107800740c0b0502515024001565075203071642009030805003110120300d1071840c0741e0740c00c00040020480220503500c1d4103207401132840c10712076807501c2202c9584126540c2c99100c0500d48140f1701d41c4803910050440c2d0407502c118002e44076510100d81d690104c15010203841c0410000500c00043d0078900c1220000b5001c0c41d0064229101c1e02c0401c2501c0c40c1031403680303c00c22070484c090200e1074129001c0b541c04080b07034540c00c0a20740b5014014000c0200075149440380d8035000002410721404102e514000e0440b1030840b0b9440b00c1400e4030031b641c8011130155481c510001c09948034000c1c820321805075912001400649162221b204448201010f44074903c038180d01c900c10040980d42c2805035800421340c02e00039146852100100600380a00000300d0005d211481c200002c100c0382c0d0240d070204841c116034841da5500d007111241c0101480958004040d841402e0244080513032503004505c0715401518140700094503814156161001202c42d980703030749103007261840484008000340e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 990407769 1250 990406519 990406523
    0x1505070302330c0a0f0507020f1005210711010c210e03040b07020312121306110d0f1a030a0f0f0b0411010e0a0308030a050712151707030b13 62
    0x202c600070800710400307400142280d0140c06000003050350b008880e002003000860115910b000e034500016940015601681041c0341030140c1c0c4401c00c011861800381084401d08040f1214110303884001c8d14402807481011181d06002801c8a901403120b10b4050154600d0414151141c000c102d40888020500c0c0d0350743c41e8459006601e8205803100e5040234001070000d807000502c0c0e20b83d505550b00525150884800454159000c10050a05400c09141c0c0140d0401c0024645032001c2e0310070709000001c2c04580c02200d0107a1790008900c0c1c0300540031340c0403d00545ca806810720081b0025080411403400780500b054054021082e44000039030045e01d80c000d110300c030302c4640d5100c010940b078111440e02d08031400c40f03000601200581d8590380196013214881400c86004000314115a210700c0780d408042d005000207610b03000441c4090740a809201144240b11500300400e81558000d110104a107120b11604010340018a03000c80c100482c046080d00d4128210076180d44601d038259203000250902 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 990409019 1250 990407769 990407833
    0x50a020f0f01390302070518090d0e030312070f020d08100e0603070b030f070315060c02010302070201031b050d11181009080703080d05090105150d050a0213061505070302 75
    0x10500040c0c0d00030782c81d1990f00d000c0d9009048090801c41404140704618400b0315010b1200030402c041103000042c40c2410607038518151403200410f2020a10310f004000c514240324140c001006015a4040b1050300402e829a0032214a41803103442643c0c0546c0c1a5031500179601c83c0e1344144401e0001010b425013101001d012a00b034580e03a03441e01401034000b0b403144142c560442c0c0074003804030b5040c00307284681405000900721451a0070000303004603582100007030605070041452400c1d68020340c880110311180b0350b55185084002e0344010b0070b6600003c01500341500d00b155401030000c0860554111158034841d907000c411001e000c000b55281d400e040380c0108030f00760307101080d41941404018000d5200b8055a5160018080c001043d554001d081c800c43ea85400100215801400c0c00d0b07030f0010905469440079016503042a6040000070300c0040e40040780241e48140c0a07003151b01c101c0c112003441081131010181150111600d00ca150030280060340900381342460081080e8010b400305490f441 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 990410269 1250 990409019 990409097
    0x40801060609050a06031e05072007061403090c0d05120d06140d030f11010e060c0315030601060203030103030f091205070603060518010308091804050a020f0f01 71
    0x642521541e400040001d03501c0701c0c0402c180c0c24011440340252115080c1404411091748004940c1d1114610010020751900045800c00c0d01845400c0d814241a16a041c101242141016980c940600c65540054506920f00d03984c2038034038066a0150000801801c0c0600039001040194119580103661500a800b05ea4a0026058000304103c1038100000300b04503207012152904002030680d800e014444100701c0500003548158001c11000799030605002014280d00454010f1a1103e140380d41c4c1d104010610002c04000340c00303107200d0b040018080e115104400103042d2108000e200302000350344184010700c0060301680b156070720301c901c40c50900030059440b5038080454101e188280c0359500002810300006505000e41d0010f000c1c01e842901c001c1e0203051070402034074814480540145004031b4210308a1b81c0b00c0c80603025203103106040391035505260030266220740c004102284104680b1802c11020305003d109000c0c0e414050b161520102d40101c07220f610100c00251104503118070070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 990411519 1250 990410269 990410279
    0xb030405190c2405090114090a060c1e0804140102031201060e12010b220209030607080f01051509040e010902060c030a11012d060306062c04050303060d0804 69
    0x39914440035002d580840d00c0503141c240c030845034204206210f40f1030001c8402409005400c0421180111005e2a05494060006241d422580a0350403115404a4034070800a80c1940c00340d00201e4007070003092a480780132a205018501e400001e80010000b0009200802800d0305c0000b05041190301801a01e1400007907200c5141c18038002d0f00f101c00824249410080070f810490701012068215030001c00941c14140001005444002e09812084160608404115030107805032207000801400315101c50500040c05410050700310b0b181c038440d038030307c00c0005031510304414003450381c2c5202c03c25107146c03070b080d001484094100030b0b502080c2036488020010050316a03200405210b039100c4055515103101c250000c2c26680340403520381d407507030510f82410825055003001100c0365a40281c5100c1010084015001034031281d40080d200d40d06d48200011031107044000b40c2100141409841520710000c8044481008282d0700500103030306c1440045c9241c01e05400d4080740b603018150b05030038070742c1d20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 990412769 1250 990411519 990411553
    0x2011409090c04090506040c02070b090315070e030f0a0c05011d13020901090e040c06050a090e0403030b0405010b0313080a03090501050412031b0f0806010c022d0612010b030405 78
    0x26900060b00e450001010000c40050340b0800d5009038040380d003070001c042d08450003580c400705801460001c003000103020806990170440034030034010f003451a03c81860203050151150307d550030094083e02909000e54012403021800f41d0349954401c0c00d0201040c10a401110791090303900e00c81e0300750b02c0c2818403c0f4041d0f131690045c0c0040c00a1240260b0b03105180c00006000880a03408030003161060800e02c0009455403540b00140d540503c0e05035100c0c14125070450f55508194070500d140103034041030100f8140d15803c00b101c83c0b081070b01d0510441e680c91901e03041521040701d0b28040d41d400041c900c400108524000d20400959281c00308140b0341c40c1d1a0b2500b1a04113031030883e081001d5078030142d44280c050107880d070704071000e10200c2c0641008980c041e100c0c01c0c20503085001c11801c0c90004040d6800798031084136142d009012148201d501440f02054000013078220364030042e0854486140c0d2500340300303e0762041214001c003039150f4a0f026140c452a00054411a02406103044400c411022 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 990414019 1250 990412769 990412771
    0x71704060c0e040c08010e0c12010303020f070b03070f0c1712040c060302090d03081b0705031201150e0609040204091103070908060f0f062116050f0307030201140909 73
    0x50440007404801d40c4101070150b4888008060040d401c0c016403104040d008003a140c110b600c03180140c0460b564004a100c0e885c0310b41917213045242c04c071b0000030081c95400500c441038500c40c6411100025190700c401030803400308484210010b180d040c09505498810002024023910900c0611002ca00c1500c4e29440380e000b540041c09941901130404c01800070b0219001c004092a0408515103201306001c00c0034440786c66809024000c41001085000c0254034210742c0c07030308101d60b8594840109103040e98895000c001d00070300b214000000400c1c20444907040c1c142c0040c0c103489004041d0542010701c8010780000c1c03920340c0d00c16401e101c0043d000c40b050140003030603840200d4840d517a2903c0000a024100660022140c43e44414200400c2d50309941003e03402081c405665400d580d00c00d00010320310000e450300c41c051070b85a1400003000c0c3c0740015400d00c3d15a84450440182900e500c00e0013608801e4642440d4950304c0500c041001d940030f045c070030b84121150205c80745403503910000300b60a250 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 990415269 1250 990414019 990414023
    0x6090a0314030703120203150d080d060320010e01050901110304180c0801060c0c0e13051b0307051818160e04110607230102070203060906221208071704 67
    0x20003d8010101640200c204100c1c52811030f0031411400d101c014045101090015140038050740020310301031210f004240c500d004000081030000948a107001901e10141d58120112030900c001e9000040d8080c103150070b0600810381d50380382002c0c1408011190010310b40b03001340c842e0204000110f40003001c0440c007290040344c0c0700301054030b0700003500050200c00141e0100d01005103000140700025410180c201c00c80b422201032020540382c0b00c08038480d80d035900f20020124482c03204000d00d020740c07001003000715034821000d0b920b246a498050150b2125413441d0500400e00080009208003025000003807100074030b40895921251421511a5101407500301d068148100000c00c0100804900a003c0c42003058590a0030a000359403140310090ba18000510445201003002026403000d45c1a01c5c00e068006040703581380d0404074040d580350321007510304c441d00000b018119001d00c901a0342d40301d00f4070380c011800001208a1401201c1184001e0310303d03010424003805606203a40b03041000cd0143e4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 990416519 1250 990415269 990415273
    0x1c080621060429060f0f04020a03060807150203031909050307050703060507030e03070b0406021c020904111c0c020c0a14040e1612060905070608070e04060f0506090a0314 75
    0xc01c280c100083c2000c40d110800311824896038460003980600c0f018076030441c509852986807100c0b0200007404417005900b400d9040751010611907001645600080c0c201da01c00c0082d40c5250351103102e0420000802c01043c0096441000842c000300c0e081d20f0008102600c5030300010f1000c945035102400c65000001c140c44550005c0001d000307000d428441c091300000b0a080803c0f0201c10020300c281c4030b002c0c1c000b001d04184200000141841500c1d0110381c6c90321102c101001c4c403142d400320311000940065110502803440c2808100da004804030480c0c9020303204d24040c47d590040c1c514120007030103030304d1032200450080002219031174031500190006000ca108149010798429400d001c125100c01020749101d50000010315250f403408075108040d0740310112042c5043c40c2e5030415a02810b0040c0c0c0082103441041000101c45510000c91030142c002030381c80c8030102400804020036a5424000d1140201041104108603e4034100502886201800e41c0c21034580e01d40f24035440349440c60b0210095 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 990417769 1250 990416519 990416521
    0x108120306061207181d040b09010615051815040e0a0e030d0e010b010c03051905130305030a020613020f060a111c0e010302131a0c0303190e1c08062106 67
    0x6060000404000d01b000e01012120210380e0f000c0849901c801810240c41c400861000c141714100c20341181000c1c0c0000c20000c620350780b00000046c495407010304048840c07880c500d11409246411202d600d400c0d054026641c5c1450b0400f814501141ca026151500707840c0d5030803084094040a00180c05042e01c0c1c404009402002c000c015400d4541030200c4e43d0421681c2c40d00c1c803002075004000c7c1c4011406901d8280310090282c04180c9042c07142007131070714241002a0b0000b041190010003400000055402d507145525042540741c800c2117a840002d50080f010b0050013602e0800001800d4034800c940751102000d0561003005007003170801030344103124142c1801691802c135000b001b00d442e10746003031800710300c0c207480b009400e0f01919850050f890200c0503c507410100c582c101d4161680301070240c00f503c0d41c07418840010162079050461f10100642401ca00c214004800706040c1c500303021165a450403507890700c108071501500144525403040403203000e101c1c41404c1819503a0410f044600400103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 990419019 1250 990417769 990417797
    0x109240b030f010b120703020d0905030408071a0f04050904031710050102010c020c06070609020321040609050411070b060604080d050403020f0d05120a0302071202100b090108120306061207 83
    0x40c400b016040110102c208000080081e0b0110502c2540300c050b0b40740050322101807050f44009080c51900152041c44085008200d410020a4000450700741c00c80031314101100324043e00341806000a20410250103100030031035400e04c1501c03950301500c42e01e40b90308800e0800c89105484071040c0c89900e4a9012400280a9540c09110303140c02c1c400c1c1c0b8002455580314403000940341c0d100b2600000c1415803103052050843d01c08002d090801451403001c14202100b44a020480c1e82161058600040240c100041e03642818885d10601c3d100860586140071484e03140d003c244172010300000c0c0c000320300f0800050780020500400381450802c5c4c0d02c082d5030314130310700410950100407003d15118070b00e411200d40004600044480598481004850f1079844494080e03009000701e01b8064998080240c0c52244e003075020510341200f481800700bc00400c80d078401403210b00a024002c01c002640b0254000307968090140156a10260080085140003038921044000703040c01d0351400b0100e4006113000503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 990420269 1250 990419019 990419041
    0x20a03020a030b0f0f0d1a0405060405070b0306370801060f0f0b03220f0614090114190e03070b06150310050607111905010f11060109240b03 62
    0x14001c3c0045500d0b402d510025030020369031480c2482c0c0944900342115070304c020060b0412201082650703002a400b91403815080032521141c045408403424041c80101049003054042924090100980b8003404040c029035001050701c842900c0315001c1e009440006448105045081d018210800c0003140052031300707034501c0440c10344d0341101c410341d07070740203414010400c0c0340c01903a0b80100e075540c0d140a00c00c000550f030325106405003400b0b055059040079040503c006500009600000440c002d58143e440307c41c12801c0b00c91696610761441f005402155110600b481c0c89880c005003401c00207110002525220711b16401180126826548039003002111720b00380024140d0050118561843c52030308290031803002c50207010740392003000c1c00b0481e2424000101400144c4440191000d081040c0a14090064881c1e81c400ca03800100800365801426102d101000c01c07d4943d040203000036400d02540502500d000c1210285482c0080300c03c0c68400100d180040003000e40c024415501d00301242049 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 990421519 1250 990420269 990420281
    0x303020d1a1005070213090c050109090c0f11070e19050601020d0212070f05030a020c0f0303040f0b0d1413050c04050c0a03270501051e011512020409020a03020a03 72
    0x11a40100240c0d9015580e1502c514011681e60249402035031000d044c800036060000d0407807030443c0d8910b4500c00104000c04c600311901620408d03292400e07815500c40820089c2c0f41c820400c00c0016200d0005c142c20580070350840c5155180740400c1d154066110f043c507848802c02103036184126035880202070700c940f5030351141d150000000e1000c1c05001041e120003a65505141d468190403e0000441a0a1100956a0045580e448004e80b50303555140c0e90b00079507070032444803043c0c42003504c086001c01034a40041280e08694001c07648441c95440c1445421840c1c220001c601c0100c0c1c0c494004200285400d0500c500c40e201103d800080f80e07205042003803034115018070050085142c0010302040c0c480102c1625501c07286d510b000315a1101c40304901000c4000c06000c14035441c000c141810400c28103402070ba208070350304040854480c04c01c2d00400d4a2a40a104648220000405200744c0b213101d4240d00f4001803074008054035143d500c0c171041c800c9910002800c1c1c0042c0d800705200083d994140201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 990422769 1250 990421519 990421541
    0x12060a06050403120503090a150209012c06090f0a03030f080c250302161d0603010b0d1b0509010303080f0702010615051606090b040c12050a0209041a040303020d 71
    0x440c2003904684d00c1d00e4070380038551044418000c010000a0b50402d0400c42001c095512150b542412914201001c002e0740010314060702240b0301d24220700e016081640310000002c1216040c484900181092001a52104000c2504805440f40400c2a501c1c0c0c4204c0500551180d503884101031a5440d0042070041d01400a408000c0204180f0900741408880782c45410b25035921541c8050203440c2c140e15015450750f1044896000c1400081c840326018a10503461903d83c0480041d40d440c402014220740d09001c10f11741c002c01a1024801040c40f001d00b4040607007042259420080d258000920085c01c260700850005020300e0400c071603d50001c04a5400c219980020300010b41441c151000c07078000a00b12404010000c243e1130407901110b0b0b42c20300402d800c040f08001d544001e080407648140226001c1d110421101cbd400648400d03240ea02d03c075660380081c00340290700050307809c0001070f1101510540e0b5082c610540076103a501c25015450003540b107600c00680c3c4806034181c0d20151280a10700d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 990424019 1250 990422769 990422777
    0x1a10080604031e05120f07110c06030708060a080609010b100315140406091a0a17120304240c0f0c020303040e04030219060c1806050910020106080312060a06 69
    0x51000003074000040071403000442c3c24424841d2080401150503003d243c0c503480c00e013000402800b2002d0a02108640121000d5030b8a1300c003040c10360407407595240b02ea1215600560100005080c031845007003459007001c4020000b107070a95803000c2961500c0740648003e801a55100808101440c00700414034061100381828080303011082e0080030040c2c07542c80b400d1074041c0445445400c40d42d8991184002d40a41c000070410241c3c140f1001400d6000c003010140900c944c1c51010840120003940201560900001800b20b5001203180078801d40001e0422a401048261110401e010380e04080400c8584414001003a02c5800c100500f11002c0000c02c505011414204901503100401240d054458010700d042140d100d91070100d01d010324100302082c1d902100442b050812a00b50441d02c28540305a4030418001d500c01114030140e1200c0c801d0001040041200c40d07091300304032518803401e004600000600503130320018a4190703442001d141124100d00c90802c1058a8100d800c0c2c0098591345c03030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 990425269 1250 990424019 990424021
    0x30209030714090412021006060801030209010e091c09051e131a0d0f020a120c0608191d191a040201080720150906070305090d0e01030204031a100806 66
    0x2c041241c00001030300242c03000302804041841c89000308011141c010310031004010813070380e801c1f005041120a000c201d120b00207100c0006084054141e4140c0582c5011010703010000b0307000048100381786400f2000042c80085603002403290b9900742580024100d14010907061341c01c20b410880150083c06144488034034000102c02041034050401000280070313241c900556815080c4060f1000c494030000350301c1903107601d0100c3c410f50003041064000d071060704040c0c84a5150001030362558800c50300b0a00b20014802c0f5142418040d80102605241c0402440f4044e102650001d05000255820080c000c102c2c1c88450100002800404c0c0e04c0498121148100c4c1043c0e40002d2020402800c1038007040b48806800c0f85501c40c40192000504442c8104d4050f02003015501da80841c1c01ca9111545000c3c0f8800134890501030300605100303041d032201508000913400704c1940c10026046007641056400e1101200082c03568580c103640c0740002004080b00d241034012030501c42a190403058203904100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 990426519 1250 990425269 990425309
    0x80f0301142211040b04092c0c090a0917090a0906120615090e010c0e041a060f0435070e1306020d150501021c0804060b0a03120302090307 61
    0x141035408920403a10012881c0f021030142d0341e6103801240c10424002d01c0014000a0811440d4003800c020300c60300840907031140041d01301410204010355000340300e03080b803003821070249040485158864000c1c10001840480e03038644007034403690740604410b4041c1c0000c41e24a5494640284801802100800c0c08281d08025240a00e211503841c004c1155803a80007900161070046e817450003500310074004226502001e01164068030000a131000401d400ba5154265820035000352580d4840c404150312903071120a05004640c0d008100150000100f031002085d4003020b0140c0101610000d00c00da000b103610407400d801560340340d0301005c100c1ea108490401000500e80446130307001052250000d8664018104440a8824498114080c07480d20010303150103c4200c070010140c038000c1e401c40d584010112600d03081d15401215080100e894000010000380c540d41140f200444054030025440c1d0707681e580c44c641c0c401c207c2c450501003900400c2088490a00304a4500180444059140b00701681c0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 990427769 1250 990426519 990426559
    0x80109030e0402030a09020d080a14070209060d0c091508070902090a092307030213050301112719030b151011010b120708100207020603071b080f030114 67
    0x102481c1801541c004c03002030f0311003442d6402030100c40c1d0060084034030394000d4500100258004100580820b040e1120495000c2da04400e13120300c654013030300e066030319141c880410400c501d105a0440304200d1a45003c103065401e4001d103880d81e121003520103000c604014446041c228160000c40d66984107101d024007a56610800408651009400091509010b00e0a50a1269500c8074415090b002824030040710340c9035000f800007010400070304d1075a940b960105404d1f40c580690680d07541c0000d210500645180c10600703002c00808114100700340c6128404107005143c1100554542010300700300b0824440c1c0500c034940c0c00002a2580c40650780e189002500d0b088203100c40390100041d000289030042800d50050f501110020583d20358001c0c0100320503551039903801a03003894065102140d019030454001c2d01e40066000340301c80d086a031241c5044500c82d86c0c107085e0b0700c1c1c210790484400020501000091010030b02d1000b07000d0783d03581084040200d2094290409000321040c0403110181e60700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 990429019 1250 990427769 990427787
    0x3061302090c0c030c1b010e030a0b06040218031212070f0206071409090a020a122903122205180a0b060c010f0509010c090812160b0f06090108010903 66
    0x18030039034a500d50340e121803942e00e940104441e05c100c51241490301140b041c065076042800c00b000b607030ba540c0040c0307401c020f143e100c88520320010209021840401c03810b03d00380e00541403ea0b001d50f41440700b040707080700082c603001c451703103120081681c00511100002444508030744d1003080d60404c503540f00c9420300b000790344240040c002c0c000c203d4400c01c82e020308501c1c03104450b440329005041c10f00741c0c200120f1490081d4000c4e420b020201f103400019201c2c8080b139018034800d500050034250942001980000501100003a100c1e07410f001e0703590300814140c521800b42002d00c01481d200c24605401800c4e0075010021074000503c0342500c2072071080402c800345002c543c82144002d0110311052b000002c140b09006040b800d0400354200510444449141d0303101900c070720f0402c00240411443d000f0280c0703884100b80142d84150b007003054401d9a460b0a24000c0c410f8641e0140703500440d100589601e4903c0406551803140121500180921480c00e074590501502c1500000c205000040c2d4014001c206 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 990430269 1250 990429019 990429031
    0x7020a02090a0b184c09050a110f0a1b1a10080a060c031b0324050a0905090307240e010c020d080402030a0609080a022802010305040f140c0306130209 66
    0x4985506030700d40320043c0540382401034544500c5d0380b07100038001d441c0d03251745081d0045030851460040050070000b801d0041002c9129000d8a01d403034520148640602c82e40411040400d105040e640080020031244070b00c00e80e02d0150343c3c9801101c0c3e80c10900a4101340240200d44042c4c0745860a0041620205003001c50550100001030300d0010a2000c0d4060030810442e407075044002c1e0314001c1c2241d01a008820064020000301e51810b800703c0c041e4000708907600800703800000e0404203100203160341c1d000e9500b041c00072040f2410142c1c1541c8030841c0d0b00300502d16018a281c101082c100c03100c42030054480c02c9032820024044582030b80d600030360710b10310040010204002000480e040d0340301840101c2542760820014082000319007004032066005080f044018851104060a5140d486003040c480c00050070000060f208141c00440c080d10001d0070a5403a1582950380000142d00e40e52000c070103401100c06090b102da41a0201800c102c002010281440c050200800040e44d5104509034050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 990431519 1250 990430269 990430321
    0x606022118032a090c120910050c090f01020a0b19091202061617070f260703111603140705070906030b06120d050307020a02090a0b18 59
    0x6410320151240003640400450b805002d485419281d0b01048409004007091100000c08640070b20b01c148000440d0885084010107001c4c01030448240800c6081a0000511390441c0c1880803803803144c908840060b500c00021080c00118100b1070b003411013040f111500b0900281201d0075060b00c444200c02c0008041c0d954054564191a80100c91648401986500a040c25104030b0f9a1078010796121019900340c3c200f04081580003c001c1d100c1d80c000440840c20b1604c00300c180c0c6624200307548035a005241c210a015103241907500d884400d000e4400e03003a04011510b149414100e402030b003154410140e001c220501007120380d00d01a0703a80706500701c9a52528010319100d0b020001c681c00e900400704024098000e02000060071900c036003122056a0282c205800c2c1d58442e00d0820111700d01502d50302910307402881d03141c0001ea020b40040d560082c0c8a005603202c540c040d81c00035244000c11181c05540030382c2d9044814550030842002000ea40c6150007000850034274064600a03007001030003445001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 990432769 1250 990431519 990431527
    0x80d05121e1b070c030b011a040b0f1e07030206010618050d021203090603040b0411010806030d03090c1701020319090c120c05060c0c03061614030619120606060221 72
    0x6421040b080f1416542c00c100e40d00e12280d01ea1800d560804400e10502141c50700c40300710f10f240a18070100710750880d4100d510b541d14205001c4450516038124103c00d80d001c103500300220504054480c014424140300360f01030603c40d810300038080d12860f4031540215014803005020310094551707100d41c54905030110f03142d4050540941c03450745584141c22809801100c04000d20081000c00741540d4040c0340314000c40c03800c420091004490310b84c81118542c7d031551182c000f035902e0178046c2c0d0100d01028007911040b5101601d503d162080b840c20403400514681d400010411940314440d50f103c010040b0803410f20002ca90780d142c60302210b020340924180394080b406070900700b0091100c0440140303009000c0c01c3c0c035041c1c5441c1842d2500d420440f1030740603001d442c0009008481d1022005c4010704140c03904441c904008544001c00c1e00001c2c11160032003511000706a020300c1c1d206005001388a0110350880484042c544802134803081e6100c2c0003594000c0c10901c01c691800065440447c885003001511 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 990434019 1250 990432769 990432811
    0x18070303050f0c0706020a11030c09010e100308130e06030c010c24110406020114010503101d100c170f0a0906090f05071d1b0c07080d05121e 62
    0x6602c14065100f4240c070400301300145003038011410884050040107550420781201044c952564488d15805a01c290100010f20031092400542030f000032404a4511889840f96035444144d0304c6610380c03880f008450700003001140c0340f0089840d07100d1820350240c60004141c40c00039016041c3c88100800d84049203590700c40070040d02100081c40c1c1040007091161180c9565103140c240e0050283c500154200102441460941c1189038101c50001c0c0040034285503103120140201178201180e011100c40e90509810030300104100c01e1007955012001030a42035003500a01090805880045107082400800000304100c0d05103e030710070034070440492000411318101d00200b8880da4010414400d547e1f0200034090300048001c16035580d90b04c0704030403c05200c07200d02c121004079910400d00c0e54001d000b044201c00c41020b4a10007210408030f4084a03260510141400440542e1000081d0081480400e4106103c00c0903000025200e0708480c18a00da040d5240d04400100608030341c142c22400000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 990435269 1250 990434019 990434047
    0x20c0d0807140604030f0906020d0e1c0b010803031501110c1c1a07110705130218062115031b0112110304020f190e130803090a0b1807030305 62
    0x2d00201400c00799500c6107031078a0301074480740c1e0380000400094094440440c3c914000102c0203c507003034a440d8411000c29031810003801d4501c180b400e000e0b92034040170003000030721b0004a103400307002c410340610380b00d24040681c00c0041c0c548982850400a00b15400a41a4000324440041410a5900c10510000001114884405494010700c540301701030301c04072580c985800e0706019501c1036403201e164400c80f02600d6590101800741992003140c00500c5a2400c0103a030041155803c0340200d00c0c00300803c9030001e14250000c90007811140c100e03840b29441c00c1243e44c4010350080061324503c0c1811005801300b030381d038140c4002d2050f03400701e03000354165540e0241340d10700b4150070b0042c414130075150005680e03081d0740c005803400c902036500d22130b03100a03d103408904824003180380841c0065080c40d100a6000c0079802a04001990804154640c01b09030940001e504c1030000c0c0f802080304029528040c113800e900103104140041203441502c0081c117000c1034000032a0b4251619548420304907200c0e031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 990436519 1250 990435269 990435293
    0xc0609030221030f060a050312130909050d080c13090203060d05030d0c0210110a14091306050f0a1401180509090c1201020a0c02010c0303150e1006020c0d0807 70
    0xa40c1c041041c8000c03194160181d0b009620030340010340124010340341c403030030301880c40c4250180d0b6901d90000340c455011038107014060000240c450142d20f400310b503a00e00002c101d51300030105a07880d4000e41d5001c0b40c0da0307401014954004402081c01c6103005500340d140c0c0510380040c00790624032034000000c150309985000b000b2950503008400d0b00c0c0d40b600f400d14101c0003001280b4201016000d0508842e07031410240c03098207400e00c41c21500301c0c5404e0481108444000c1142050709a01006101e0041d194580038942c82c50020403101c0080c0f254105020010400c44419015120f1200e09906201405e03d42c5c60b07a02d0042c000713007010161040b0100301304042d40c01d141c0000360444805400c0003052280000c00f1760078050181c5010106070394903036030305090344106180721011500d00382151005500c104007910515001e494001072030101d070b00110713174071400c590700c00c102c00040102030143e0004c10b500c8210041c0440d000400c42c28001002083d042c1c00d4a02000e821400041048002d204680000c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 990437769 1250 990436519 990436543
    0x3020f0112050901020c071d01030f0c03050d030b400e03070c0e06010c0c0e04210e0a060c0c0902030901020705030c010f05010f05012309040911100c030c06090302 72
    0x51020f4075141d8200d5000350030103426000244540040000c0401c505500908407001c81e01d0305030344503805c540350201040e059450480e02c2c0ca0607494000302148c4240441c0304200e0940e0703404141c1000010030000010001c2442525070701c81111100c03010356514207800344540b00440c08480c80c0400c901c9000050018101c008524000001c81e041000110301d0600152014609025216255140111500800c4900c020b040601400e07050025800d84294141e029104202101d429150980050844400b94038148046205080c1c0c511440c40e00c01c1407200070307040502d003144920700e8a440c1c500d180c41c0c20b0301c2401e00059001010a4407040c007034049444080c2c10400310b80e0f80310000c0924a000380f11a081e013020300d42c40d00b0b00214508084a01d240202d500507035504820141d15030329540400c0d18903003483c80210301013000001c01d0322640617515000d4000d028001e03802c0110f5050060b03080314a0000ca081290304501400000d80080e001c11866822000000c3c3c546541d00d021b9150828030300c24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 990439019 1250 990437769 990437771
    0x170423011406040f0605030a080d021c05370f060e1e010f031703060d0212250f0303140403080d0204180c051c141602060c07080403020f0112 62
    0x200740581c041e460128001c000075542008561104200b16040b00c0c400c1c0112a0716810a22065011800100190014030b08515006141c07982e00020004194051040031422540b11420000001640a0030407000e80902d00c0d00c40c0c0095003139201c10440054800703405100c540d90481c407001004540e2264010307019565244055050002003c40b841c094018164110140c82001103400c0101d030044108595200d50902c0b584aa1400d01c1003c0f504014121500140b180b12180d0141c0d68900c020307116501400d02a010840c4050910480901c2002d101b00703642105002c20001c220340201d2800880341c01d89810103034819003e20b400c1da684110780c030150000c1d4002c605104040314550041044643d009912003820001c9031440c001d4500116a00000c1384d0144200c9101071030308400b407942c0c200e056000082c2c540f2040001d07060484181c17000c1d0944402c00070420102e81e010400c094010b0000c80c030081c141045940c41603198452030100a006007400c4100525507406a40000e503031b5040840 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 990440269 1250 990439019 990439031
    0xf1d0307090624090303200a08220806010308210906061309110906030f07090c1710051003060b030414060604090b0606073f17042301 59
    0xc200c01030406402083e404a03110641181c21001058010740036009649580188500c0c5407000d07614030720102c0c0c2404100781009100c00c00c424003804080420b03403050403a00d0b21030805084480c000002e2080c00d00d030f207416802e0244800302000461074112584002c0150ba20310030007403044000c150f02a80758070b0356584002484010744000c40c42c2403050004de1800c00000210507100c5003681c1e00d040300030342540c241950007051410981c00c01c941c800d0014041b601a50203c0128521700440c035801031129130790360140701d8101507000c403401007940826034425501e400c084242080b8072055101700b40c801e00c3c0c030360b02490b409030282e0400b03130003400000c66140d00ca18044c01e22648800703096503415420f003d00e0b00019502d142c0f40c4580c2040b0b940220a841e240d58501d414011107602000003502c50846010741404000d0312001c024054100030011020602c4503c02e002004d070100e80581d40a010040308041c1e145040094a1076020b80c0101031621244080024501440410f514503c001d5081c16 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 990441519 1250 990440269 990440279
    0x30a140a0f03270e0a0509010b15041e0f15090f060f02062211040b041d07150c020f0f0631030f0b0910060e180606010f1d0307 56
    0x4120142c540000f41403220a44040300c5460703003a00d4140c0102c00f5801c401c031000c030f80452000c1d030025038445808400000c9203420b11002500201400c43e45400104e0b00103410700090404072440d401080012101655440c00c05103150301d0321103035018002c03400a0507840809514800d50480e8000c00020004560700ca442c0d5000800007003104000a0240c0b2070000441c08140f00b0040e101c0710700f08005001442d00f00030340c0c0c80c81a030394a000d0740d496000b6194070304060169554400c4852000c460314010303800c1c0c4a60202c00d400c00f0b02c00d47c8504180f81035651300b500c07401e0308110301c0400d4550490340602d5100103900095580314208507281d030041001b184500c4042860311586440d200000040320315420b002c4d401f6942400c1500005101c0040e250341900010081c03602c9542250881080c0c564104900000d00200c3d04c0540c0b212401c6800d9a0a011020051041c1c0e06120450300d8007900c0503141140000c0e041103a0702d6464010850f040403142980a8503100101c0d200500409507082c00e5039032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 990442769 1250 990441519 990441527
    0xb040b0f030c13030c05030f1b060706060906060309030f030504152403030f1205090d0c150e10060503240c1c05070f11060a110706020a080103050607050405030a140a0f03 75
    0x15011b840d01a20404617055000d0000103040402c96500503c810780b045a0001440181e030080b40084664940f80c0c0004034890f100c60003548082e0110f1b07038002403513115904009004004851584d0141413924040c4004107038020407010200d400c010011038200502d907503409603c0400d160076881d8800d800c80200c10907038407403003041030168a596544d09860a0520b14011102c0c00e48182c1450b82c01038240f5100c0074059885844103902480342d05400604070405402134541465009400350001c00d8103446251040c441c0720003602041e0000c1500e074a03620b03034074108100340b20300c01030780100c0440025480c0c07403040741110550051181c041e0b0b6081d003001c04801c0036200c161800e10104044176540301010340300f10401a40c0180707400007407200340c1f00d866103100180000d1489450390354040158070046810780c0006e00100700703140c0d00c840340796145060480c100480a4000010414100b008000940c1e00051100307216400aa400c074002d0ba40381c2d56030b40303804d1102e08002c0200080c820034406050304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 990444019 1250 990442769 990442793
    0x103050c0f0c060f01090b0105030a0b040e07030503030402040615120b0f1809010c0804030f030b03150903030403080106050c0304091e060305030726031501020a02030609010b0a0b040b0f030c1303 86
    0x140e9101d08281780d8840b05248199501403190500249040c0300241c14441d0640109075500c001400004541040d00b02e46030a10500ea04241c5007580000140811801c091280100421281001d860360f00801d45008000400041416a005884121000107581c1d04c002c441d2804400a00000300150780b000403510410040728861081d51814032480c110a000e9040940b00700d500d9030310b50744001c078001002d44c018075007540c01c3c940520440201c18140540c841c0b045e80103c204000442d26480e2528000b0b1118070160070100c10040c00b40466600e100d4000161815258015804a40c3d1a0082d441845a00225402404180c2031a60000901901000401e0b00a0080340d0a5410884020945d100242a5860012030000400001b02001284418040c52600c144160381450f0041d8002916001e41924580b0075655680c06610fa60300d08020b04100905104481c01d0519142c000c1d041901e0241c018a007229020000001b04400d044404a622154080780c0400105480b800c2c90004180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 990445269 1250 990444019 990444031
    0x7030906150608130501060803120405010c1409060d201207090609410307051f200703030e0109090213090b06090607120806100e0103050c0f0c06 64
    0x45085909030305810060000310a440d410f0302c507500e00da00e5070b507040b514880f0a00c0c025621556100c0001c116510107200038000740c4282404840d190415040c15421180c090018a0a004005d0b45d415071107006102602d5084004541050311035004014100103008039040c0700035110300380d00a0281c04640d06003d80117080e4011000c503003640c1d9028041e1402111400361102084e01000c0810529401e04140040e000c5041d60790388580005c081600da00e050403105003200c45500d07040c5030b5424102003103580000c00c0200c0300448185015111380e50f00c60003da146201300300550070b04400400c00b200c0644804900300c003c82e004030350f5904006040c4010440d40ca40002d003003c030700261050440c001c0d61030f044484500003408170300d0504e2600082000070300c80da802507400c1c000c035100740d500c413800351640c180285034002d1450103c040c02006504028606c5c1d2140c1c09104602041c0c66004030782020240b000c1c28002410744904030317007041c02d0040102da0b4003d02000100700749202000b08142d40654 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 990446519 1250 990445269 990445271
    0x100305060f0103062706090c0e0711010e0307210c02060f030406050f0717071b0c031401050403090e04050312010b0a0809072106091a0415020a08010302060c1507030906 74
    0x682c015960105845c900012100a0b030007229012000c1101e640c4003500051242101480d40c695407a42605114000c480c4e88010030216801940403500c203006008000d01020044e51034004640d079401c800c400090114011452592103c2020b5801100f81001c038503001842c841d200c40c5440c200400395032049070101c480341c0c1450301007040501e0349003582d8007800361921655202901c445104448a80c01440c0400300030102e60401c101d00c00c50207000312501d0203900c0854829085013000f0440b03c00c6022001031030380c9008100000310b40d12100380b10503640301c0d10075010f458540e402d1036451030240001010340d14050000000e1024030b884020030f1200b69984580c50584c1c1c85050051300c1d15900e01c28060321014406a01d400d094a000c40c004825100d400e00090b0340345152103094507000884840c00580c0c01c103d06001c14442814400c1075100001d00341545054010b4000404003501840300900071000800e003100303144800d01403d0701d2080c611010021714a00804024054980403400b600c00c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 990447769 1250 990446519 990446531
    0x30405060a0e0c0a060c050c1302090f03060124030204090c030605090f0405030409151a0a081005030a17121501090f0f1502070b0d06170a021503100305060f010306 72
    0x160b000c41d03030940c1ca010040a076200315103000810b660060500e0f00c116100c2c0100c0c0322122103907403044400041007654400043c0c44116090620852a03040c441c01e034400d80c0f01500410909844000201841d40e84c1c1c0003880112034050000e0b40603000c0c1fa000896070909090180d0039543d0301d58481012aa000c407010301185d00c1d002c01100950200740c1d0040e165800403c0244150140c5400041407400c5550980f24520741e1604503884003e140c103095250312100160104241d0b0b400b94800b40c20042c50600002c3c0c181c0740c100041e41d1958848801810140310410b550030f5807010100780c60302d8081d64004102a8030309203400c0c00003c8808201ca5011401c0d03000040f810300d6070a402e000c00c0d00c0c04103283c40e405a007020322013240120820444001c5220b00c04010a120203008007902411200c5030002c0742c03140c00d149240c1c15031904944111090350201d0155809a0b458014200502400121440c4e0b41d48581d60b0b406103034207403504040c0291007084144031500c820808001d040301c1c0100420411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 990449019 1250 990447769 990447791
    0x1716090f1211040506130b01020c15040603110310060309080d05100e0711061b040803040303020d03060902250309170c0f010302121504091203020c100b0a060c05070902030405060a 79
    0x21130b10184c40c0d8942000b61002503180482641d0f100b07049500741401101d031002024800603e010313050a071401d4404802003010030100c0c0d014003503040d542d05840c00d406c2c114074001074043e03041c6903540b003031714101031b21826038800748108107084801c0303494005418030142c909401064000c410303e04c18105480071010004000c9803003801810300315802d400c05007003035480e80e6140c46d1260400003150406100d080000180c1458100001c200461094000e0700f50400c1c50342001d01240c02e150320003070005004100c07409444002a81e81d0854188260410340c01c14101e0804030303101007451300705100741c10003980030b4031080d20005000b5111001c1104c040c4e141506071401142640140b400007240800b61402080040d02d40d95440c01c0641009000058909400d4640440f000b24140044000c04d0b400910000005014440300041c10144541403202c49401e1010a0010b402441002c080101c40d42e0000200300c004e0207907800410b40c144042d5164106402c28503101c100a80c2c00c014464038000341c510b8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 990450269 1250 990449019 990449021
    0x405030c060f0106090e0c04120c0e100b0403031d03031c051308030402060d0b13050412090b09130b06030106030501050117010503100e0a0b09060105040c1716090f121104 75
    0x411390b82107640300180c95103440e83c29028041e000d054400340c8031041c0030200e01c8001c1860450749640c040c80d0b000e4400d80c42d064007042c08003809810300200004248051090016020440d401c072907062400c2d80c03400070b01d010b20000d40783c21a1000342e418003001407010317010000f8601002e80e50100000410003a19079031550441c8442c0e10800078110030040c4002000740c901000a40301c08038281c4008117141c841c3d50006666a401d81c0c01081502e83ea5000f40401d0000c14074031071b00c0851240c01c002000b1401d20404005a0048004951081e0703021400c00310400030302d40100c80400e01c060300b001d0301c80d611141c018024002c2402942d00080b15400342044038032256202e68100d49020b800303008010041130340140904080616001c2900c11200014000341d602c09140e44151f82e10b40241c0103d505000802c000d84500d06804001c21000786450309100803518210741c0c01c8800200141c03110800854240c4504002e544444038607843d900d070001e4008004002c0e00f0f1024418044840c0c5c076081e880c1000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 990451519 1250 990450269 990450271
    0x423100501021903030209130203040b1501080f0105120a0204060b0a08100b1903020702030313090506010201140606031015120f06030503090904021306080a1b060f14040e0405030c060f 81
    0x4644074000361441c10111740aa8010040003a02030f10140f1245004007003142660b1042e101119891005402c101c41d60b9400e03041441d04840034a4440d030300d800d0031b058a45002c101805003038454402c81810401e0103034108140d114059000e0014071140b5980c400c60b8015411100c810300105d81c04100280907105e400c1020800d4400c800c0398182450b481022100140160401c12000d05a0070070642015a504001508200070201d20a100c4182001040b000769130014000d1415a810000c48580158040030441d9100c1c038180d070625101c0d942c600050308400d582d6405a140808644039100b1015440b130b00030804050701543c288440e80d01a0b26080c00c44c1c8a500c8042c0140d041844100078501d030041000c1d4016000401d05100c980c41742c02c48500710b603219885103c2c1031b400503a5071030420000d0002903e009407011003030752195162030b1014140040e6100362004203e034080d204004003001c5010764029100b40001c0110503d001d1411a542ea800f003030404050b8401c0c480002d086490700385000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 990452769 1250 990451519 990451543
    0x1e0f240901020709090b0402130204050a0b0702031501060f020c19061805060a03090209011703030c0a0c0c0311041d0d030e0106080307110a1d15042310050102 70
    0x1819024002191000980e008400d090381180185080002d49015034080c031003410340104002e00340c1303007420310400c484103040d008420981070040c0020010750341d500c5181400c45011042d196a41d280910000307040036003501c1c1e2043c81c0a0b4240020034196488007180e81c4e2440305400300c407280d482038007c00174010284440d43d021500201000e000b041e1281c07000031455100c00303c0c08590151283c0003c0c8090b0400d40e45240048c0d0f880c2120303410351801e085c40300c2c0140f0340f00203a0741240c0c450080d030f5030701c92100900c4a410b03d54000b4182030031601c81d2090200060304403601d090311548034500141c82c0360224003c0d0348240d040046650103001c2c803e002468101801c13004004200703213140d00742c010f000384860f01041556070340c0001418080510003000864801c08004210040380070420504004070307001400070486103603440c0ca0501c6084070580d0001c81071502d1844043c243d00c0024040d04031351031020900000e145144081483c0b043c1c1141c01010180071500010382c551004907660032601d404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 990454019 1250 990452769 990452809
    0xb0c03040519110120010504060c180b2d03041505060909060105100c060608010209010207240c1113091511031b0c060c190903020108060415051e0f 65
    0x40f40146601031081c14180300100741048030000c051138a0642101d40480303041da01c56481e203401c2e10b20207500001c082c03030f03094203140409805410120007586074019201c035521100c16890141c200c041c01003500301500302d5511510b036a030b4034040c502440e05000482c4513002c0e00c0c3c244008510545400002c00d4410303883c1c1d1001f088107a180404025100c4421110402402007800000001c11050302616024210700800035a0380d21a9500081c1f800500e5440814008a001c0c5040c0c1d112042c0c038a0041c165009160110030640903041c200002032400c801249d2002920390450004c40392074100391400d6015407400354500052149040944041c2e05540b20300190400c00100d09544076200c01c22200140303207005040044034014649400c00c10340e441c3c00ba40754082607128103000100314195046c2d15510346034168500e5903001900c5040050110340c4215114580c0c030b044a074010564000a0100501c2017020b41d142da41040f44940c401c91845001e4200424000c002c3d06200d403900003009800c2107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 990455269 1250 990454019 990454043
    0xf040312021e16090915050c130f0e010501020d02100c1b0f06050610020c0103091e0813090b0a0510030b1c02040e0a03170403021606051b012c07030b0c03040519 71
    0x88030014000103100c8103002300140305140036494012401030145c01c540c4650302c0c3d0182841d180c10481c03401688000d0446d40b1501d605c4440d9540418040c10048a64802043c3c0c2c19203900c054a400b076040900910b40c5548038a03100c02d0048602040c40c01600070300042100303444000611071241744184240c1c0c00760380160b064034100d51082d03000300c2c2c10500400302991501100c6050001c01014100d0541d8485001b080796003c51111000c0040180364030700e000c0240c0440900400c800301c11a1042e10301c41e01c0c0c1c0d8000e0060b41ea0003030304040340a810003040c044074042e01e03191200c9403440131001079000d185005924851500001070001c40d81e901502c500d18074494a20304c607010750300c0c024001c800314001d0701e10011070704400107040d9001e041e8545429072500d14401407548039500460f60340603281e04000200f0210918a020a03400441c100c0046090100381c6c28010310f08851076000030f2000380c0e098100710400004401450103a03120340240c9a000001402e02d40304642d0700300c00070305800d12000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 990456519 1250 990455269 990455303
    0xe100309051c0507020604030309060210141501170906100e060622090c0309202d120f010e1605040c0e031f0507050f040312021e160909 60
    0x20000b1544074441c0303070542c6007034442c1c0d000c2500341d04180c3c400c0b808148120000d000003a0180603484081d40741001c1004041c45544800b0340400d0040c3c01e074841050700000c0d401d40c5910500d1030015503041d115201002d800c09041e203964964007210178000d84660740c200401d00d021952521401454010507242c07c2102d201c501083c8007007004c11000c5000d8854000103001c00396402000595680c50b10001140515030034003600d03091841800014a001384040e207410383d92402c1d035104040d480c00c5414420380030b40004203006040380340c0000b03038480446200088100400204400c165060344001c1c4136a907103541140d59502c0a00c41e800d4603144581d503040c043ea0400d80c0c4290001c851310b28040c81e80d41e4411002c00d081c24190440c4840e0034804070711400d41e1071264012141c0042c0103107442d61521640e103607001c9190041c1d01008110b9140c01c030701e07150003d100b08011550504841c22402071907a401099035924098020b0364101c1041640d40010450080d2003681c5146800c42c2100c1c0800c0910 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 990457769 1250 990456519 990456553
    0x30d0e010e100509060c0c150a030b0628050d060f080708060906150103060504020a08041208010515070204060332010c1e0306170c01020114090a1716030e10030905 72
    0x5240d40029100c2c11f446071801c0c2e44c070421941140c641045025030399043e03510004042e100304075800340c000c450030092140071a28a43d40b03604698180d500c1c10012000d03892040b541807084241000c400c81c1001004603075000341c1802038045034000000c03202241d81d10403a10381c071384c0e0742150703100056003281000903072150003103003010b4074014149000a03100780c030b480004003203170403d00900d8006515502003004001446040800b05100350905803495890200081c9100310080d103049070140003c07680320115162900128045c65120360300c0b0a00c8900488405800d148060040c0d0ba584020030303070310070300c9123040c407034010741d841e03159a15098410b0145d14088003014100b000410180e403000000380c0001d40b4103044035600340d81e0000d00030354001c201c002400d4420030b5054610444542061268100f0001103002e0001d0707200066104a41201c0310041150194800302c650b00310104c110701c0101680300c0b01001441d00f00321200042018500e0b4128119030082800a065500100c010b403000024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 990459019 1250 990457769 990457777
    0xb03030c0f241b071a010306140405060a09051204060f20070303110c09090c01170112060917030403030c1e091404110705030702101407020f0d02030d0e010e10050906 73
    0x2583c401c0c51800d013003591848082c540b48a0524104510a80180100702480c0280c0c86910301d4180f0410807401c041c2c54168660101030884075005980d44200c0e010001e040c001c409510150040341071b180c0d640c454000e00a15015108800052a0351110f007000f84c0034030a002110040310401010002d04603601540c8005000030120040d104d450340c6030b40603607105028a403140d04003030040c000c0d0031041030000d02440c20300c4010006040316980140140d6041131005a44560061008070b200b401c01c1c20000b40b90700703900d402128043e030000200f00901d40c00d038110b803030400301513611204801401502d801265052560740b90009404090400608820714144003122000803c0040c103200e14410307134100c540c040349040740c8903000410144203524100a01094040f12030422030703500703e0201105072a40c03280e4500248906070704005103641c0d803142000c0000d281e030b000d000c9603000c859044002e02524440702c0824005550411074910500386018052901c0b0001d440e85400c02c8a4402089500c0d04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 990460269 1250 990459019 990459061
    0x40602030306131815061a160809030601120506010905040302150402010e0a09060f080c1f02031b0a0b01090b010509091503030f0c0705010302070206120a0b03030c0f24 74
    0x920b81d81c50380300c4c05040d485041c0400d0b100b82144030030304414004000070f80d01960721a600c400006001030324146d032580103d50280350a85140120003600c1d00c0c200219005002c07040d0b40500c2250004514140b0640030004514002e0080b64200c1e070742e8840810507100201c1d4024016004003501c00316407404000c500d40c010b0b10505080850002c902c0208101426503803180000700d803201002c000e00300085140c84094540880640200001e2001142001401d205140601092903205901c840d03c2070050f11441011407100500350902480400c1d51010004003d441da0513201e800000c1c5420340d0b205203081850103840d15400c0103002d90401c400140010300d03183c0700880c103d403407607031a039801d100500c00030500460303850701c1712800d2400e2407500d080741d04039905051040281303102582e134101c1500c40038038200340b00c5541c03507940c5060349001e40842e1120300d40610012a00407880c80010940c000202c404908540151240741030040c00407a4040380b41001100c3c0e0004101210003a440d251002c1d0f03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 990461519 1250 990460269 990460271
    0x30319080405070e2d07020c01080405011b05040302100e150c0a14030a02150603030f0d090606031416150e0d0c06170f10060e0f0301091a060604060203030613 70
    0x9603980204444c08041161a0000c0d007101394003914440c443c8850b4061600402007018a81d441e100d03031b01a60311614500c4550600200800140401009400200310301c41c0c84000249a00614840504a1340042c0403c034803034100200740b40065485503000070101c06000b0f1084104d40c28003040000340e58460814902c240c0150b40f0070030041810407200ca40d801c01c03004001c3d6078034a045500207050500072440e550614848906108107590700005481142c0c0400070259a6000050346810042c0300e0306c040109100c0c24460000280324259003091288004c400649040a42c2200300c4000d102c00760241c1140303491a00d903060145403103440c039002051000741c2260112a40c9490301100700740143c0c0f1034800142031010003000300310a58601c0390880c0b0001c40c0d072250b078144846000031200c0c0c540205402c104038191a142e1681c2c92010503108808003034003c204031003403824817540b280031810f00cdd158011031140109006061070803c6800300d070341a5000c6d41c116160602000a42c03160218044019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 990462769 1250 990461519 990461533
    0x2090c090918010902031f11040b070618050d1701052e05070c120c0e04081902100e030301081c0c03030519060e07020f01051501050309010617030403050c030319080405 74
    0x58604007c04085004d04044a0003c2e00750003600f0410313200000e60718102500e00384810409100c2034420340740c01a40c413900c0418601412440401131001c030b608058207071b120f14540c80c40c94a070403580140020410240c810410780e01c440030f0010300307800070300880c2c00081448011089000125030f4907600d003603d45041450008a500e40f59881e0304241c001c3d6035000c404210204c10092192140f20090401c0519420355203415240e8a40c14082d030600181010840c60f040c117889403082c4042d034405003104030104004080d08000e9980d81e002401410703c0c1d0310170b0096400c0b03e00380e02d009118140659581d045140400c607507084001d05006840800c7d946c20b641c4088d0440b0303044c1c0c0104c0c0d01504084101540500d89900000e10702a44442401e03481d9141c0702c14021071001c50404007001c000d00307082499076030f20340010a500610941d0310110030320100c50365480d03608101000410459008070b046810858408040640720701c564960b094003404e0301c20440c486c50b4080c4140320b42c014080d605a80310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 990464019 1250 990462769 990462773
    0xc0f0806100503151018080105040b010b0307091e1a0906041a1306050909071e0507030c0c0311010807080f0a1113090f11070c06082505030402090c0909180109 70
    0x401c030603446000c1702007801455210300b5052404500c2e0020407640c1c00900442c1005c1e241e5049245060203220b5100c0000800030f020345014a08201c0108000c15542c04001800c072400d8202c25100d00501da21b2424403180808103d0800c42510000400101500c3c900b5182a0404400400d000148120007006219404c1040303046001070000705206d803038859589041000f000510750004007030074148242541c0d8840000824051489400c1d0a824010b98492090600b038900700c0921000406015054401104020164251000421007038848015a444540c01555610b6040380c9040c00215200c4c0026203081c0e4507000b1115801050307019900e07010b4a908aa41c143c492a0230038803501e074076580c0d002503410882c41904000c1e0381c00750780c0d40c1c14007485a8600419100600c128410005010302240d00c025a03000403044002a420034406851440000135105030400c0b00d0603442039401c140050f4480340000102c95205000600d150542d03034812140c079040010180880b00290358034905000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 990465269 1250 990464019 990464029
    0x20c0a12031a0910060806030a1b0503011b0516020d08070302010c0e010908120a05130f060e0103090f0f05030f120603160608010303052b0c0f080610050315 69
    0x440042a5500803560800d040c80b25070400c2142101d0324052610f0008101241a403410220103894aa04d0160066154100000d1134005904d07400340c003078044001c01c0f00011484550140403580c0540080c000d0181d418880403e12070a44a500081a03041083c90000c1d0384070150b6003409032000b0608510310469803560607864204010440141c0e55500c880c1c0820380d08201d500c1d04004091904040719410702103075035299009984000090030700030415403c000c0c010801d0703410071410201d1040e6a180d4072403508030000201e1040c9000720b994090034500e2035200f03004100c584c03034000c540c8000d03c004a5444450b610500001942d940c0800c0c00480d010085036001070000000b40c07070b022142410208205070600340340e00000310751080c2d0307044100091030300f16986504503601410300c0358450b200c0984003003603210010740a1031207200e03041c14000c0c100615809020380c01c43e655030b00c1c031049078000d4042da44500252206503220116042a00c5c01034441d000070340d800b0740064118440c60301d07a8800f00e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 990466519 1250 990465269 990465293
    0xc041701020306010201050105090c18030717072903010308070f050607030608060a0504120f020c040f0522020619030609090305030f0c120601030e010b030d110c04060b030703020c0a 80
    0x1446075000403d0018a60b03090143c507014003c11181c0c4040d0342000384e0a482e05104091103555285486240c00340e00f40e81c10700c4114020410141005800405007c425844490f50300803001c1440c0d41600442e0284910b41202e181c0e104221034a40c0b81d80d0a580b501c0d0788982109604403030b400c9040129000144050210b01c0c003034451910042022824003040600301840206240500c0b8a090200008140e10680c602440482030a01c2403102000c030000300d0401d000c542d01c0303507005400c4c251b500c20f4280c001d900c807603c54515856039905040d154030941d0240c502a07907001c0c1d0705c1001071103440b001485034491205000d0362801d000070b002d80e9030305d070240a81e183e4a405402003100407082002181480c62131540c400e141c181060315025001f45000b034a80009003901d41090b540703140740025130342d09510100001c1c40040440d0309809d003281005000312320000304400c490040d030220000e181441e0154006545400c01d0160840c2c0c1c60180480080d002146242018420074000401095041c0c03610 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 990467625 1106 990466519 990466559
    0x1050102011d1b1305040302100c03151404021e0712020f070b0706111303050c030705061e0744030415060b0d0f050606040b120c04 58
    0x10407240300125100d84c1100345408140424590002002188040030400c240680100d200d0210107031010790440c01da03400303060318040c40f89140e40e604444038001c010b0300c01420041020910035003000007100b035868545c2c2c00100315042c032690801d80b8043c0340300d078001802da1890041c000d940c0d9094a01c01e0042c5141c001c5464820001035400410700e03904061000c544814503070303403c1003049005200481c1d0274414403080503074a0802250b44421100020507080c02c2500c05440c8401c402031002c803c6480c0700c401c00071800040e17154801b00030b810390500d130141e4000b007100d0f03610b10140807010b401035100311010b03074694030341c6603140201da600a80c800490896000c0d114402800307070072240c01614034010041900c0c002452140d01c050300c1540403030303c180002d03110a414800c10b40b0490184415032401005800e00109190003103c4e00220303064a05494180d0311088682211021203071 = true := by decide +kernel

theorem cover : BRFrame.Cov 990287769 990467625 := by
  have h0 := BRFrame.cov_init 990287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 990287769 ≤ n) (h2 : n < 990467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
