-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4579
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:04:32.78244+00:00
-- url     : https://prove2.me/submissions/7a3e2814-618a-4428-bbdc-248e9e8fb17c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 823381294 ≤ n < 823561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 823382544 1250 823381294 823381337
    0x301050a0b0405060f09010b0c0f0a080702031627020915040315091a04050a020d12020c04020c0c0103090614070f1b0f080a031b0c0218061c03 63
    0x420100000107030488001c1c00300070946102510703450080c4100c804050180e1070f00c4151505542507050116035030340b03003251020729250b0700a0040c0658000c00c0b25250402400c100200040ca000f1000c4401418000310071445c1c442c090310880003030014400000a0110300f01c5544030150400000050030482a90045446910720f1a1500701d40c0704001014001c000c24a01d50780f0064031700d85800c006080e81640c5840d00311030b101941c69180210f00e4000b404100040040e04611039010b0720400030b078040e51a200e010b011581c1c0d640c03070150142e0000c0705401d05243c0300391150910104018103031508564010740c020645c803902130320712035281c02d64188400314803404980144100d03a60700e4001140e07210010090300407000025620070342005850f011a00b4401b81c09102074114100c69a0cc82444c03030164002c0507584a06903280c1070501101000c2500311980551032402070302e4000e091018032610441c5400d044484640c8064214034206c00c030b45004001c42c00213403107420544c62112821001c5280c2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 823383794 1250 823382544 823382551
    0x1801080714041e0918150207060609020a080934080604122d0f120501181109090103030c0507081603060f02070f080906040f15200a0201050307030b030105 68
    0x1e11650342c2c40c848881020320503c0001d19002808000c0c00c0d102c4000d0303400744140030f100a0421501038091400c0a0441d034101d403401ca0303006104100141c0c0d10401c01002c0d400c15000407000c9480280003c00040c03003ca045008409d0b544820201040140a1181184101c2103200d0042480540c0410540f000b00086409580034040000869804140040003104100040c00d07030700e5400c03248050358000550f0040760b03108803828403525441d19540120f903801040ca80a240c12803c110002a41c100b49094407000849240b400740102d88421102070028072480e001241c10000304001080071030700c516400d03140745100b90700303448445561f04103e074585082d0802c10001803009550070020494984181602c4c810071190541c1407072401c0d00c84420040004101a101d0400010031400c256600c01c115000342c101700d940948200d40b20001d1840c181c4500c445680410500c001c004c042468500d403a0b140c2e00a810000c11074507074254011519038002030a8501416142c8020070125030702809501e20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 823385044 1250 823383794 823383809
    0x703060b030f010302091308040605030a02090402070f02040b010c20040e0f0105010501021009030e010e041808030a05010e040b15060910020309010f0305010f170a050307080c070506180108071404 86
    0x2c0754154010407607064006030078072000b071301c6c0007082c0d5001440c00000e070b4045070010b041280d00c2c3ea03600280c020282c4503281d0081c2c2e104d03200160741020080307225000c003038243c000c0d0340400104500000540e101881d10f14082d2008505031034150310501700398038088031103401420214038030a0034021146440b600140240442c0d4461005105550b03041010b0355000d480b5030410301680c0300c0c6031070240400994425090411481305119503142e100d1740c1103002d0412180c24041e900d02101d0030400c00c16082079502c0c020950a0400009407813852590150040340c21040380580c9440e85203600ea80b0301411410079400001c03d20000100e07503541c038102840304007103401841c0d641100c040014500314000c4031440c28589000c00512003501c0c55030b02241501c440d191a80000c15403413080502e4040d800034010072500c000561081001021005000e043c2c1d006d00456001613251405c108450051101041903c9802c040d00211903119180058121880e4101007010700bd1000111080e940503030880b51 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 823386294 1250 823385044 823385071
    0x4110d0e0a020a03110114040807080f0a050c1e03030a09080c1e0f03030714030714060108030f031f060e030f0a350301090b04050109180b0703060b03 66
    0x141909220300a40035a02030140140c08851082d5000482008150102401c41e080c0104803000c140d02a103a0708080e00060602036131241d07a100c030364a0b40e900341401249054099040c070243c4c1040b0001e2540303101540440504903040d04030003802400c0001c9a0fa075a01c0d4218585130b4041a20103200411082170540d0300c803c452400c0040003464003110054241c010030404156880300000580900e00a403401c8450340498446580003a01d075024a100180000300082c3d5501c0d88030b20000010300c205407041110402c0302039402802510758209104542098000b04032800aa8060703000850340204c445081d2400750940960511070680c0c1a080100820031702c0c04071441c549401c0102401c8201054020144440c185d0368020303170010f10007000240c68034001044e0042418815180984520340c1c5d0f5265265a51140c10202600307600010f540118680b0f800410b86040754050032a032021024000b480b180850b5032415138603c401400c0d40101a5500300100e00c0101540040d4003c0303002c1e40f03c26 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 823387544 1250 823386294 823386307
    0x40b0f0306012a030f020a06140718150507080d0c020120040311120304050904050d030f0b100c060b060a0e10050405090c1303080c011a03030903100b0f0411 69
    0x2420050740e0410f0551040e006498488080400e805142c100c0d0b07501d8176120359130000040f01640b4110310420001e0540342440b040808905032040c10a12030750b680c4e0340c1e0764000c54000880d17800701e80071030040c44590400d8840140a5034000c000600c01648074070052840c1c0160841458219414503a2010050751546a00342c40600032900401d15101c000f500c841c9068590381c3c9068410441700c81341409158455102075145406009480042c00d0103032014010349800c4c03a146450300100103241011a00c2c0044c40410000c80d4400c82c03501c0080540b2410311101c0d0780100340da0f8504180000c0780c00d0383c0c4440002e03909403641e8003c1c14600c01c050b01c40250a296000401401402e200d08001c100201171004124960360b0050581e00510100c9050395075281c2202072800410094001403c0074100040340e8241140550051a4007001448400f00541c0060101500e0348624072995905612846503001015680e51255000050041031032802d18104408034064809444000850043c0400c1c43c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 823388794 1250 823387544 823387547
    0x1d0a03140714100e130e0604050607020a020906060c01061701020c0c0d120c0501020915032d0106111c0e0102070605040506040b0a12050c0315010804150c05040b0f030601 75
    0x10020b002041241003907020b110780483c000b02d0601c14000d0030020346034810f901036111124181c20480c9030840601c50105600600703a40c502c01510201e590344110350001d5521132000c5024038000f54010700c140480d03180d850402071030350086480511a07541e5100d0004040c0c1c40d00030301c0480302504900240c1c030340204608041c20046103043c580d018403001c8071894000340c10501e041c0107404040c107100030701000f14145039009008443ca9a13400003c81d042c0007090440040c00746220308114841440044850356074400095080d40c0c80c000446a00c50050003811301800100006031840c0301107402c1d00b2805e290703c0301268240100c402c08903003041c0069005580c1402140f000e82020300385203107458070341390101d4454841c45c404c4d800300030000b08620161900c210784c002c1d01d0980e0302d40107001c0e07030400c042c0412050b802a944401c424208400c2c20030594010812107208a400401c1d140310540d4481140012300000d0b904481040300c104400308007a44c0341e2015080540c00d905403a900c9203081e800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 823390044 1250 823388794 823388803
    0xc0c070905071205100e0c0f0a2a05100506010e09010e04170c0a020d080c15090c0a0e0c16051c02070e01030f020103110d090b04060c050309030a1d0a0314 68
    0x600701c0c42d403130800040000f16249881280200c610208282d559a9140c19260480e401015100b0514150002d54820215481030040a01e50074030450701150081502908001c1080064014029049000040229102a40050350100b018140f04480089000001d070400d0300c00d03080300e01154001d006110501460002240300001c030309100f40d140000d400b0b0b2050395901c1c0a10000d2103255229420410004c1c02000d4400c4c1c00801c0c400c45184600603d403205c04427004a4543c1e18521030030385610a5031034104445821102c507000080141d49807a00000182e900c0080104a00c02440d0b541d40b001030b40030030001c020721880001903c0c2403c6038040003401e02450303901420a0425410041c03001c980500c0c0034041e5943c1c2420001008040108505514024410000911071902540c402072203040d50704144500c2c440c9a04004c450840342080c0c1c0c02d80015541508a0351050212440b02d90080511100c0c03d51172640920b4028940340c00951100465001202d1130700b220703028505103007010007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 823391294 1250 823390044 823390067
    0x4050a0f1d0714030405150705032521140c03041103060708010603023f090a0f0213020d0f020403030206090c1003020904020c0a0819080118050c0c07090507 69
    0xc01070040c1e051080c001040081d10302c014518460340040130a081007810402e000d0407a003085004031440c40d041d000a4051742044964882c0d100031041da4050360b134410200210810744a48801800600b05a202c1e009440d251740c0280e5442c2d42c90103001081c0c030b05c2d0481c19100b12102a8a5680c0e4581442d10410300d1098082c12806544181d044c040c001d608042cac01811b49016160040c0c44001040b07444102040003a54900304030b09980a902080e1061400354500c45202c0c25415042d484030700d4907e0f42c1c0c1c0c1c541540a021480b0751408000140340c10402d0703001060381d400d009810a110290410200c40000d44030041081d40010108101a010310901c2c3d440101d0001400c84921341c1c80218003100d140000b0f030810141d00003501d1449544035816164022552401c9405500f01450f1508aa45c00840540780084c5020f19038820184070300801da058504903401540b0090312014140e011b03160190503e84440020f00a0240104d030800000e4000c240c018000b00d86401c00d203802070030042210 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 823392544 1250 823391294 823391339
    0xe0a0603140601030201051204020d0b010b0c0d0e0d1b080613020a090b0312031e130c05100509090a020d0e07180b060313142410120b0c04050a0f 64
    0x10b0307004002603a000340507540c040e40120750268550344ca910001e04104644078004100409200c004201604000050b2658090382340072078a603a46038000a0350b84002d0047c07100d03844005000c0e9075001400e50040c0b00515046480e10410351510f034042d141c01d050b812590103d00740d1102c5d42c0d900c00c1d882c0011a6000404402d44100011107041d40031940f1220759a5045064a0002011843c03005440000920f082c071a03002048450a2002c001d50348a81044029180441c0c031120210b43d80c0303007600c0000c4c1600002c0d2581407602404005202543c2c20040080401550038440c20325484070f507018900d011422800500111800c110b9030004d140c0c00607201c1001c00b4a4040c01d81d5154880304201c1e500100420240c280c03202640c981070ba1402808203034648613000f003150801e90300245103400c0c0420b00c40482808030a5507204210302c0029128800e4a4059000002010106a00c0000d494005410203181440c20307465101142c9501c5441d4098801000525420010f102c001c85441e90202003d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 823393794 1250 823392544 823392553
    0xd03060905160c081c09062007031412070e09010816050d08040503030c030d0e060402010f0f0212161505011508070302160b27071502070e0a060314 65
    0x5882e148800c401c0300007800500c1054001d00050124000599088603003c824074400043c04580ea20040e2840d06002c445c3d00d401c003402c4e06e54642c4840c021a41010b0740c016014100300d82a20304650482028504806e044070070020f105601d08611b41d02445149103880c2c103409099040240240b140d016440712800da01321900914000807004400320445200310340560b51200355040c17425042c41550b121a0b494400002c6105403000702201403c1c02c00700c003150401180126011098903030740c00705e90090000c1d614640e00c901e480e00a501015000302144100c40480b0070801441d8078940c0107015014081c00001340290411054914042400004850500065140040119100302500f80001c18020808001003c0310301c80e60646054144404203010265554200400032800a03121700303415410f2a00a1030300e205100007804c1610401800034a44107180000c10009444081c202004502401e8000900010f40f5081d1078000c071441840054820714603d44400640d40241350100603400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 823395044 1250 823393794 823393801
    0x72a1b0506030c1309020403061d0c060a121401080609011a1f0c0c0b090f06191404050a1805060102120304020d0807021e12070e060d06021201080d03060905 69
    0x7200c105598104407a083c489480d000b40385401d90303030802c668020300605031000c40d0000a001d0513802c0001d0302803188195072484510150100d880e2035035280e0b0760303421120070008000400c0c40b445a91000c901101030014980b070380300349400014682130b4030081c65a8041401d0003004182840b6417844e11035a0f41c1c00001000d00840402e181409045031058111012091400440c1c05102d0002d045a0700241d6080e49070786070445001c40e50803641000d03018009a9040000720f0411008550350b000002051281c0310150301340031540c0c400f040d103804004036400e10001980d91606c01d410806007518000c1c085003003012400c1d944c1201c0004182034110340c40001d0500c01c0c50b08120032607811503015108a5418480350608003203034419850025003080800000c41543c100120410501c81400c5a050101c2c071440c0e8245607a0b203e031030284005c59803000c070200c0c61600e0a10a001c134900d20550002d03040c802007214002d207441099211003003e0f0408500743e503100b0f625202e24005818000c204200a08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 823396294 1250 823395044 823395049
    0x1b150207030f0c0f030c031b050603061e10020f2e02030a060b0a17180304170a0804170c06030106080f040c0302060d0f0e15040b072a1b05 61
    0x2441c1c400a015428840b45840510412600b0600035100c8500c0080c08903660b4a0302020042c040c0c8403e413003500c00e07440038a114401700700021085031001021542035445110410959210303508013012240d0f9910401c404540301e003d010103d0000f99006000312403c052511820003d44c1c500100c0c210301032044202410780c4001d0b0000c1c580c41200c90050b203903900c01e07100c0d5004010075040301500d02c02c041210383c2c036160f110ba083c09184140d81803194190f1260100a840100028541e4550b50014003040c08410303620075805036194001c0007141e18142c0e903a10380034440c3e4042d410503650f00c80701c0b840301d2203605010000108040c0c006e4802c14a1585040341c0101208005407114201d415090045818000200c040700061034004100966a0070302604c8040109102c5400702c1d400ca040c041c042d00e00d010040b400101c0d84c0c607601280304555542c0d40d1a8800540c00809c01e40031721030740400c540f42c015000c80c1c00d0080514416a0b00c80d038042e550400d04141007180c4055001e1030600f490500898 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 823397544 1250 823396294 823396303
    0xc0b0a11070b040f0b10032015090402040528060206090a0212030702040f020d0c0c0507060f1103030405010501030b060d0c05060904020c1501050117071706040f02071b1502 76
    0x1c0e50410034080e20b030703200d42ca0004854075014002500c9000c1d040c040c00700c0500241284c0044078882c00401510100e03000060040681410b045a807020700b4141d50703080c92007050002d00341e86000a00051405496100040c0324806e12440840918040c14140d50f00320340c0d9051920207030081d07000078901840c0c0594599641c6080c0540207016901070100390b407101d1020002c1c2c84190342e000300b00348030107000c0142c07100003900443e0388142e21504201d100440c45014061501031540c01c100a0440b517402c0c500d05484000d4200782d08400c0140902e00214080014070256015503c900b0020480f5451403c0180b20018041c20103803041c400b030011140010403000d801d0007120b000307441503521259100c0000c0c0080c002c0c0c2200701c1c014040d24910703418105201c13410a040e2042600c0364206000c40790440404481c0880c4c50b0750202e0003611001180400c032596255002c24020000300c0c4400055142c00d059070401501101c0700c41c8003d0303001605940c1441c01c00c024181906405404036491a03009694 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 823398794 1250 823397544 823397557
    0x70c03020d0312050403110d14031b04080f1b0105040b12041e1a07090b0a140702130b012304050f0409120f02061b19020a02040c0c0b0a11 61
    0x5054a010700c441098003421a800003181d00c402d00300507500e42400e01408030303415821090b000c0e000711508030480b01c2c081d8103a184107900001e41e250650b5039201640f4160300c00c040924103054010701002900e030b8010003081038200015800b40441c50300500354048400b18110815040c400b00b8042030003030010b107400350f41c501c101c6a59241c0460300e80c0e003480348403e5140c3d81d4000140e2610320303080e0117102d20a00f07100008d103088051400300707030350310b901c12110002a0702890342d003480300b004240d8400b4070070100e16000005520185103050500e90004c1d580440801d800c3c1c01007a19000041415a040082201c0d10382c900460800a210801404005485540240d621640091000740b5072603d469001036140391b4071000b6440c0f4096400e40180080c001d00c40300a0040c4501030000300d0120380c503c56105580c0e012550380d03041c80c645007800f040000d404800c031030462003914040405641c841c018140407030400d072207075480b0322100c0c180040001c1d0020040707084203090544444503614204106c034130307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 823400044 1250 823398794 823398799
    0x614070c020136030507210b041a0132010503240a081c02030405031e0a0512040611010e0a06020c0a0c09050f06090709060f2c1203070c0302 62
    0x6030400303407200f2200c5160100c0d041c0910751840b0a01a034180320741e002c018058900407422a43c0301d0b40d031080d4043d40c440410100359242da0380c1d46c100900040c10707031500a030060303c150a942c0c00c000340140e140a01034401d0f40f00c00d452420481c003440e114005440c06c088080c00f250f03c0c0082d03a407070040000c0d01511000e41a820700c00c0f0001030188a01805d105c0710078038020000c0003042c80598582c106a9903a101e0007810003072440c04a03000c40da240c000004c5400b2140c019001e002e0702500c0e20601d80c46400f0a00c5030b9182409000780c0c2a00080741809401c10108002d0803030794803a03040c11802800914484a604016858080c00846608001070382c8000c095004402590311001d01c02100d08100601e60010f0990744120004180f510090308401d00c00e102140d1260501c0d95503c04002c0340304410f5030504045004440c1c04d100c05841001c1c502d9501d80716040001d4240c00c5e1842c9102608902044406086d1105040340e18a00d08040011304a0b000080158205240740d2560740b041003180c4802807 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 823401294 1250 823400044 823400057
    0x20c0a1502030106270608070509060c01060806010609150c030507021c142109010e0a030308010504050c09010509010f09150e120f0d050a0224041101050a020a0303360614070c0201 79
    0x40c1d13032313504c01c00889010f258081c05440c3c0b40c005100344d0b039018090071f02842c601802620000b054071071154140108699610045802039402c400f82075406c0c02c0051800e80c10002e08000060250303c80c002d21840481c41e140344c00350041014105801d40b02c0d0905034424480d0800094a0502c014207401d0110b151296542c255071500140010b0311071040c2c045015400c0508103200000740354002c01c4483c121030003030310244050303600c004640500344142c60440d0f011071024005000254802c44080d44240d0b500d050a00c41c40ba1280164602c0380d40c04890400041c401c0108a00c1d6410301c00c008082030306075075008140c242030700d442c1075844442c440d80311020030001041507188a41b003008040140030018445920004140542a009040881d002d40c2d808010654146240d4802c2c2c0c00c41d030078100b203030b40640f000b1209990114050400d0000e614840610b008080810540341c014020340d0101124903440075860a05c0c042d815900084900c500d4441c4010030000c6964020500807542c81c2e09107801c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 823402544 1250 823401294 823401301
    0x15070221040503010914010c09060504350f100207020d02061309060f05010f0903020f3d02070f03150c1b2a1206020c0a1502030106270608 61
    0x20103039001d10b41c0000d070b066082004003001c0c00b644a04141c500011403009000d01450103e0640d4507001a11400000500030002040032070134084c030605541c020340c0510078203404c00d034030018010844040c01090607044440d030070a0028081283c40030a401c10745065041c020b03181c000804003020460041d02540c40000e00344003020148031000040d0100c044100401c0c2d40314000f0303805020441c00b4960100b48840d40c00310074130780950400350032290b005240a8076050900c0a2040c00e00c4640180c10200304100c8804500040d840c01d130b2110401c0400c00c181039010180f0f802031070b00c1410740c040f03e0307101c0c0c1000041c008560340e0b10710324a01c0914901c011a400c0c403d02c0341141d0f44042420440a64243c01140c201004408100004000f92008045d008080c14000e11894010140f0402912120654144000807900e40103061001071140a556a003443d90b10b400c0013041d05561500080c0c0c0d800001803001941016a0034001400400100c51303d901c4210382d1005a00c850190409004141000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 823403794 1250 823402544 823402603
    0x31605180c070b040c1d04111009051807030615090918021801031502270f060409020418020720031c02010603150507120906090b0f09150702 62
    0xb260305042d4020503070f07403c914107428040040d03441401601c0081da0000c00b46040c8080142c00907000ea0703048075039040f85100900811028416401c1d0343c0c401d11262540004060365243c1d21000075089981c0358480c6460079100040440300300360404002800c0c01310741d080c085a0301c00f98400c2656407203c00050701c0c810301d01184030000f50300c041c000c8d4041c003040f420740200c01903240b2850482c0d206d0402d14030720000d2018a041607000c0d100c42803070740841160412000a0118032000e1242d04060075400000d00c1d104045011640305811520b041500020100301c0d03c110304181511400b8883c0c030843c00e00c2c800f0740c0e502c40c50888004481404d920300e107110000340d5400740814040c910724040c00b80c040c0307009018003a019000c0d5200680d0054207414210f07681020900807503100c0d02440da1031900241d40f9440510040040b134005071841582d4490b50310000b08240b901c10f01880100d551a80d180c50480d14040c0b4005100306640c0010683c0c80502c401140c0001c1e240751303c00e01840c0d8200c0c032003164008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 823405044 1250 823403794 823403797
    0x10501020a0f03120b1302070b070305150d0c0e09160902070f150f0515130c0206010e09010e24090d050d0c020f0607030504050f07350109050c031605180c 68
    0x3006075105082c1b441da0b60310100e16a0041c00070505c18900b0781201d40c2c0700f04081e01203590407100b030b1b072004512411701145071400e8104c4002283c03150b02000120758942588180040c422219650a507011800390240c10001000840081005010641c98127006036600781d01b80e007188000805004134102d250040c0316507a0003480c401c02c1c41d1803040040e80340ca017640000c104980c3c42010b0095104030090405104140110224040c1680092949034038040a200003030500401c14101175507918080e80c40782200b0300070240722549a41031100c4410340000095507203000074012005550001912011481e00705040c0c070301c0341244c4c07240000c410000d004180d00b802c3c2c81d030a50150038001c3c002003040781d542642c0024069806a81210322207411180301e29650301081c0070309180c2d01c0d800d05140c294009100072200304000c000d81d2106021042190990a41c0c485c400d00729620780001505011a0038100701e02d010061004540901042c075110115107140c0380220301c0880c6400c02400108000000030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 823406294 1250 823405044 823405061
    0x70e040903020120120402010c1a01030305130603020a0212181c0c052d0117160e0102010c05340809101e0c0203100e01050a05010501020a0f0312 64
    0x810510140d5501c0c50000c1c000c20610000481c100c160045644079100d4110695942c4180d40501156036202c54005480807011080e040f1552203450b41280f0520001821040c0218403c1e251180c4880680c031080e807d001c2e090f00884201881130203550612035000a580c40ba611810512654440d0280b41da0103051200c07001c490b07088a054107200317218240c80c02030b4520050040d4600703480c041d240d400704a1241848540d14040030101c401d0005024031203074072446000e805050001d8041e10343d080700410720204581f81881030700e0001daa15007c5420070010700c02e0034400d20007000240c0d005a00501103000d05140341c180481c0400800541c280e03030320641c0c22a4140810b50461194451814905551200710710900400804070b0703854505026540101c0c8003000510491540901404110303240f001c1084203a80c148182801074640011510801849800800000c81d8034034052a0355001e0319010f0f032103181158030040e40800401c02c140d0140c500d03598145802030031300608c0c8401102820300301 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 823407544 1250 823406294 823406299
    0x705040b0f0306030d050307021e0102090a12020405060406050a06110f0a2009040c2c07020a1412030408180616052103180a05010213060206011a12070e 67
    0x10440020007504001c0e6100340d10803402c4544c10b0498a0741141c0314001a03078100056402500298842e045508500c0707400036040d07000504000340007001810f001080c3d44280d80c0c55032410094001d605107401840d03406070301030303400703118591030301c004902076801e45c0c0710348410044081d08030311a0000a122244003d61080110f89504556080c4411505140d41c006810a05506100806070400805242c452900001c0790610070740341044065549903924818820416210309044d90505550803503805640b483e80284010a1149440084011a850350350920383c0445072118040401d40c0450303130312680c81890191a82d5002142c01100d4041c6100d07583d0088010402a138164100010805140e025030116a427056000c8580c1c0c41c140540d003282600c6003410000145030300203e00091007181401012188103425035154071742240c0103480c0051000b20030000401c9590f0f810450310740508420804c0144c101c143c0c002c120120b11580d000800070407041000500c00e50f000b07a08540004502 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 823408794 1250 823407544 823407547
    0xc011b0b01080c09070813021e0a0f090c030203061e0d0506070c0b010e04020a09020a02160909020a08151303210c0201050a1509052505030103110609180705040b 71
    0x1141091600c58440300540c0f40070304500b60008201c0d0307100e00714050203092000d81c0e1018446d01f980901c0016820104001101904642c0d205100d440b0a800c41c1d00400030b0102c000801c1c0d04203002d49040d00c240001d840c01b0180148148042c60361683c422040c107181240d05400c200b84d0b5040030610354810703180084e011703000d11410456140c0c0c000c00045801403184d59000c030582e0f2a090b034100084016103003e5003040d101c00d024042813603c0d9008004005030b500407641d41d004280344481074075400d03401a45480361220a14030841c104040c1840160200c8030142c1210b94844919003441000288050903a0141480320014140106600c80304800e1030000a0030045a01c400308014084d1100c10100540c03070300c4009908004144503000030080c02220104c1c4281c60002a40c0c044c02006d445080081010614644d21552581a03c0d58003102c1d1b4032410b80700d600d90f05003495107072101c411440c081d032010080c9041e140c0d22481030421030494003ca0302001e84550300101c556000360b40103540c50b40c60 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 823410044 1250 823408794 823408799
    0x170f0709020306130c02030a140c01020d0204031b06120f021603030209011107080307140106050d0b04030f03050c07060f0e011815200d1b2604050c011b0b01 69
    0x440380c00031846200e080e201d4580c040d04c46aa04811100031844180c0145c10610280510034401c10340001469004450603061102c103286050072648403144140e096a130000d4100204401d542d100081103021380c00c006170312450248050b082014008844200c50340d00d01e40c10004103c01d82c1603503003001c244000039291032014a0042c0c020360244000601041c0da40c40c241005100000e08202610170800c05075080a2039907070780444005140707403034500c0703552184008502138075035603240030950340110301c400001c1c1400d05000d0302d8414422581e80405044c60100081c000d1814200c401440d84203000155040d01e0b10003d030300402c0c151f110450315501b0b09405c20301c0e881240c140211b007140170304608a464130340c21107500202c5443c03d40f4149107942e080440700112400700c0107050442c50f99200421049586030051101803602e8201c4030116114100e8000c204680fa2689811441813071440c101604060303d44640c0d40f503142d284603042110701541602e424140d440d10548081d880340d4004603558 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 823411294 1250 823410044 823410059
    0x21c02071a1219181109060d05030a05070519030302040303080c13050d08121513150e27010f0501080327060417010b100f0e060304020a2303010e0304050901170f07 72
    0x85d401642e0b01d01c140c1544020810743e04d1716801401c882c0da0b01c40000d500d00555028280c41c180c20080382954240103a101100c2c10390603003031845045a103e55001030740e450440c5005050b106018109904804091042e0145484492400d07001c0e904100c610100c0145945400c041e94410000462010070014017808503544404840d42110601100d610f03429030521080e110480d60828800c02c0b1060b0601001c00c880d04070b26a101da004400383c46000f10f8140190320900c800094415412501d82d1b48940300d0a45030054030800e40036040d40310103149041075071368980501c10300042c0300040c2c5d5801c105040034556610400c680080607140c2d000c41880d44001c004900030007680c1d9449000382d20004100c041304e0311070344007100034000c0e9440d8154402c0f0703014184520b581000300101d0300001080d001181e402e005e1900a4803902514a9411030744274100241425100c1188405860380e20038001813000d69100b00403541520a485c050305810030b44200544e20b844012100500c071030084003030124035032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 823412544 1250 823411294 823411313
    0xf0d172502070608071b0b0403050c030715050c0304080304110a1a0316052502040b040207061e02130603090204140c13050307050a0e07021c02071a121918 68
    0x1246181c0b030b00d08540d0b40d414400c0d150104020001021040300d0b110060001c0c00111501da0440e010b48ac00a04000904003803910b1613210304802e4a1101c040383c1508450a500d005950380b001c80c03002e5890031030070142d817841c90358000a8070060059000400c0c4a0341038071141800e2006010030b1401e550084828801c203040d85e417094440d418120709050300b0005940c0100b04540444210a0281d90141c4030074800654807020028200c0e030280c0c07148c0441c14280d82e98000ba050907402034400084158201c50003410354003200c0c04944407680107104445c0d090307103070b40d0300602194114100461a402c1c9407000800500d030400513500701848074018007004248501c040d0404403410a506003140b41c64904250f03927044207100b02c50b0710481d900e00a0008a4005000a0708141e86004a03a4221050980c00612000c00d000800060f80042010400c45651040300d44810701d41702241490042662216a00c1d140000c1c07070b9000303841c40c0b01c1000707070a50003030341c89280200801b0070020101d000a00d0541c101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 823413794 1250 823412544 823412549
    0x1a011d09030403030c020913080409020a0f0309120309110303030a0203011a072d140607030f060509040b070903061b0f110c09060604050d080702030f0d17250207 71
    0x1001940000140002400400c440640350152540c0c0d80b500e2280d42045401c010050840341e403100740d940c410000402d4803004c1c00242045000c05a141d280c1d040c0001c020031540d0503d24101801d004032400441d800050780705031580180340108082d44242000c4624250403841d00b50103200000420510110550103103059030002c11400e02d40e502c840c3d51051003405280e4024084013005800655400c4c14183c08201040d410104c0c02401400c6807500c800d052684242c80182c1d4000000300704409506118490a036080403604100d030906040c046820301c00000c00c000c2c0502c803201c02190040c2e002e441004002c5038800402c0c4116048200040d40443c140001040819482004002c1e0f150040444c000403150b0b64000b000805044010000a081e014040680190302080045416203461100e01483c500403d1266903d142910500d460800c9041e000c619a0b00a41041d0f00d0301540b080706d510120703100c040c60700700645070030302200d80410700c09000d003400c1002c21808504203500414460304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 823415044 1250 823413794 823413839
    0x203131401060f0b0703020714150a030903121802060a110a050a0210053a0609021e090108010e06060d1d010e190219030623060303040509131a01 64
    0x2560350703803130044046010b50440100560041c401c14010500207201545504c4c00040604000541e41c0d804140c15a000444043c00280c40324000800e00d500000e004100702aa0b4504108541c02550041801007050360000e01c81d07480000d0300b200ba18410b60081c1105e111001c16141c0115a0f850b00c1a941c0c540b10b20304a00625100c40f000030107a02a80c1964846905075400400c0b03109031103142000b0b040501a5020040c440b5510582912014030030b1401814802e24010395401e40c0700c10050f80700e41000e4414404c0b000410804080d079034889103590454040c400d445071980c13502400211180520450740358140e2401a200d00d00b1041c600c003494003050040b001b00980f42c803145d47c00c0e40b15050308860030288141c00c0c81160050801d5000300300e007204a2044801055105c1d9141d4060341d1000d250403507840404601c10083d4030408000f00d0708034030100c00441ca007500e001d000c45e61810340204030310305038500d8150000038880342103c14483c0395005480800c00c0d68650072840c406031003c0c0043c85 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 823416294 1250 823415044 823415069
    0x1811370806010e091e0907060311090d0803100302030318041404020a26030a09061101050709170109120206070f030e0c04150b04060f0e0303120a020313140106 70
    0x18260040041a01501d4103075541411410500140540c01101410382c0c8211007010b4034604154051400c56400342041c200545011881c00a00800b65110503000b140700c80810010400540c0c1c0745880712220b02d901c01d02e41030303c0f5552032440e244480c5290b800650180800034400380c450245001c2c0340310409003200c08000840140ea00031010034000c4800a410403a000c0d414007505540c1082d0800f8104001c2101e4180811503401d1401d603000724400790046428080c5c140406070704a040398000c81c40e040000c21040c500b803040140b4844052060541e100d12012180448000a4224810713030b9070419032140a1406101c00250383d644102d408200044640c0552020b051090140c030744140301c0d010090110602070f4003040001c0142d1031500104170090440021000c8005001d071004040640b5251880440550090400c844003e409413103a041089880c0f80c400b0b6554030143c00580b280320040c0c80e96603180440040b00c1d03800300003812040c0d000c0480c0801481c150000c9050741c102c1404403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 823417544 1250 823416294 823416397
    0x12072303061c0f0212010908070f0309080a1110031d0a020a090e030f0a0302190810090c020303041b0911030a0c2c0109030c1503050702071811 63
    0x112641002c1840091000d410482103038058900261103003084540035000013001c42d0305a0b507600c0a540613003001c0b10013142d6110454145904084800d00800440c000b41842990030317039407074081c2100a0603081c41025011014071095100c1d0b805207070760f816044000381904002c00f03e0241c0d28001c2400891007842050404200c0c0b41d401e004003c03400c0c82082c015418410880b89a01650308011160800c15a081c030040c0d081000f80a503d900050058560403a0b5041c00c0028018690040e00080445414005e452034500da002003107a9009402810700d03080440c1c040d40041044040307501000c1380c3d900300210072501070000700c02540503811840080103100e08584040d40c0400c9004540c95900303d0107080b8190400b000da10021482c00c0503d0071200d1291241d56021030106603801000a2841255000315402d40502c902d64021110340003c1002c036241c06002c1c1d94043d090132502e018581c07202001034013401d040c015034000c040407140011040003a015411101440c44865001d00d80b96520790 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 823418794 1250 823417544 823417579
    0xc080f030903131a070b0a09020901060804031d15070201120204180b0a1a13090c050a021b090604020706180f0302071a0301030803150411090120031207230306 70
    0x1a03140c9032a1450b40f45017031034020348441c02503420081a14101c1505c1f8030381d0400507a21481501d028184903201c1d8680341c00d180c10020104d01c00c9100000728016480c0145e405a0384205003140c0109101400d1540c400c510301c0101c0d1400e4880e801181c00301e00100340440c03a9000c4108080110701c0320300d01003010340380e14400c02107980c03c0c900c504903541480c0001c282c40052401e0040407517074009040340c040303655590313074050481c0c8041601900044000c9604000e00e60705000d01d40148504802d40c01c403042c10940003e007001009010303140706542c00030b080e07010484280c00c41d070036004c4031594091181d800c0d4149610440c1442c0002c80044c002d0b6400440c010220198001c3c04021030704400d41035030700390b580e0320032260b001411400928114600001701d6a84600520038036950170142580c49402480000d4555170209501d03000c1c0e911601d1490f08401400000d554000790070003030803441510340075809d45410040c02070074020720202d154003820304488600214044c200035a54070f40140e40700402e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 823420044 1250 823418794 823418819
    0x70806090c010314130c0320010e0607030f03021b06090703120207180b131a0915030a021e190303090b0405060a03051b12010f0b09030d0c080f03090313 67
    0xd1184c007281442e00403462804001c115254010f03c0340e01010805a180d84400074804004070000c461440c5040440311a0b5903c000e0b01a00d87c14251896400c2c9041550050455294004000c0826502040b005049030183c050020b11425100503680b03a0b05100fa803171500e8000c01e0005507080c903615030228010368070005404003160b18502045040c06035155103280078000c0c04003500c0d401001c0000c0885844901d10030980b0003c28001020f03d00d1a005041c00000c00780144422240c00405444111544000c125501400c1d411282c4503512810380b035100c0040303444c2d80380a07900309251a504516081c0403c200c00141c0f406512003c810a540d104448034901c55805642d403c40018003901c218903000703800954102501c03184034031040c040742e581c0040c5500b01044102c80d030703240c3c0d100412003005091496800340900000403458415001c2c0401e40e281a992180c10401284c4c2801d4414000e240c82541d480300d114500e00d07035490605016040c4e698111a26801a5441c3d184002a15240c03842 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 823421294 1250 823420044 823420061
    0x5040e060f07050307050d0608061602010e030703050c12070b0a0501150f050a09080d09031104060b04030b0c0c16030b060a080706030e0106090c03050907062c12070806090c0103 78
    0x115128a6554402c0121890b400207003100c0709000c014004005d9a00443c041e01010f800d804000709510701d8441c403d0826001c0d110302c010156458203d107404444004011034a5240d010b0600b075607141c00170594107150090040080751500c0012a42e00c027088115904a0300031b40142c1000d0003240d884045203143c03030004042c01404206243d0b07000c00c02500800181c2040101801c05404071580e500c0c1050608200b0a5514005010740d1024820042c040c136000030011402e540400a1034201821310704103202d580409031000132074100040b141810001102d1403201d0210580710400c400184004044401d800102c481c80340301000103d180c104580726804446106004210040c6488426002001c00c42d072140425521042c1c01304440c6404c5c010403141c2002550000f43ca0700d0030070513050510302d00d90040390400c1415100c0d804105404c040045003191807005c024032020040000510a14001c00d92810740e01a02c0c6000510003804a03c65114180300c0c000d43d003a005160740110b0032250300c80b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 823422544 1250 823421294 823421311
    0x60612021305040908160c051504080303010b0f04080d080a0b03030a0e01030c0306030c031208090d0906030b0604050d060e0105090f06180c06040b0d15030201050a0305040c120c05040e06 82
    0x2074508001601d41500130705081402900c10030314244903500008104040701000392000d580d100010030403801c00c400010a5520660344035230070241410300017602d0703200600ca80708199001140700815401041d0803a402840007104948040c02803544c06004042c007201c120040900c3c0c0245211107090200807513040c80c44070ba070703085050345040c0c3c0150000d003811300c0d184017090354500f4044001044a240940514010484501400c40b140070003098000020120320f41900400c1c102c1c50780580140d00c80c4152101402d0104008030700f0b2000c0343d864002d40d03001136805052900a54103001d00f0b94011606040150000e02c865030340d5078610360f6240d68000c8420040d44c024000190f10101450708071569880d00e4013641d203042400400910541c1190300308404036031001403c4000c10155200d10560354a80da4100074105155070000b900718050041101d0500d911400080c04024804850b54084c086607090700d130801d01182840c00b0036034907074040d00303000301e16004280601041c0007805510403410b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 823423794 1250 823422544 823422577
    0x1e0606140306220e0312040c080708070306050415020a1823060706021e03070206070e0603071803150c031514010c0501020c030409090b24040b010c0f0606061202 71
    0x107201c1000200210748070b0388403420790350700c4000001c80130078001402c164052003901d5030300b03041c6420118214a1a0f5102e480d050f031180508001d4000e000c01c503603086035004440000c41e5036031420324140b40015048015615480050301c0f40d41660814141820110f000840d54061900c2d4094052064105c00030100c183c0444405407910303207003007401002020310400c40076090a98a0711112402c10030307105d500f4060b80c400f104101c08a87d040040310f80c4a441850702c4461420080c000c610a440048c2c26182001900019000380d40d2040484400456110303d10090050003c05482e0040030100c2d01140080d040818030319606181e0040032040d04c03880308003140c2000281006540740c0401c2a801c40b282c0d50203004020845400340050002040d520001054288a40c941032020a1000340f05562440d41d0994030042c2481d440100c2400100558001480e8041da400680d44255040030003860318190380c0d10402004120303000203003120a66200d88040140d810300000036070090703109200b140e610 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 823425044 1250 823423794 823423819
    0x1908150c03060402130b070f050d03020a05190c0203060f09010c0207080c091e0a06051c030804060e0708060c12060117130807021804051606090e07031e0606140306 72
    0x1c0a900a2142c0012a00041405c80e61200c4a80701c1d900141d1082d0740c1d1611007104030041c05002e008850012003d40341c00c61500540810291484c042c00c03140001d41e112601c81c20190a00641c1d001014a80050481e8003924040503d005a4001243c040c040c950810140c0c103034050000a5943c00c0d10b07404005403640c80032a009105540d00b0080903d010203401b5504142049820b0408500030324000300042242c0d8108070034044003002450440d5802440090540b0109030301c406d1181d0400d0380080080fa900920520b007034940b1180380c00040e41400340405000c1c0320f9080f18018135a0740034400c507240c03440d5210401503980390b9006100c83c071481c0c507540020b007000c40c0c243e01d80705603103108400341c500b01b48031754010401070110030300c441502c4107003a4140024004204403020407083d0407140d1580c0c0b5030401100a12006107031050580d000c2030030740850305040c081c2c2c01a01000428842c2e4449084a4a1103000506481d100da64041030f409894035800003081c0c2c040f40e10401004d0510b01400b03e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 823426294 1250 823425044 823425049
    0x1d0a0201120507030204051201090b1308031513021b1c1d0a0f080a0303060b18211c08060102030a0e060309011508030406030b12190f021908150c0306 66
    0x403d20402c0503400c22000c00d05544804038050b2014280d40009075220071842c0c180311800014208541000321148a41d0000d0810303c11a036015070040003140c86070500c20701260420404804020381d4500202c1d40740550f0300c40d455100700c4c21081404917103056a100c0f19042020720200950000222505040322800c0c0300d48130745401c0c00304043c0c00703003503035030350303400000c50304c130f1003030307003001050303800800590050581c9030040c03c000d0400381a04c6840d00c1ca10541010444446d0580d43c0d0241d860804800d000701c40c20118a03482c2403c030801c1c0c030340281d0090400040401048140310229000d54042800c0e54030010030740e900185a41c56003190024502d04001203a00010600c0352159200d001100c2e803803241c00041e00040512800660711181000350140903201c00500080c055090150000f80d00c0400050a049240c030f0014101c0a00d0200e0401c0260312480d010040d40007541101a9141d4400700e801c0002160494010b42c1c030311010103c0068460b0809a42c04035400d24180003103a07261 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 823427544 1250 823426294 823426301
    0x1a01271112040507080a15051503071202010207050a1508010603020c07030611090d03051806090a121b0303090e06040902030606010813051002031806040c0b0f0d020309011d0a020112 80
    0x14003072011034003845d41d1000918944800454219554800742032030903207060701c50150a030065042010541030204003008655141c0140c82508031040c01c6481d070a0540e4000d1101c6400b50001074100c21610703854220110040d400d41c0b11400024003181c0c00002d0480c40b80c1b0a0f0b039048407000c5c014040c03107031940d128403001d841030110f40c00d0380d51010041c0741c065542d90887c084080c1e101c1c0d100e4903194030404003a0441044014204c1d806078a0400103907465941d41d01012040e5001070420505059071030800c02d07040442c07568808010300e0046000f005050304a40803e08071941b03620501c80b295122000c2c0001d455603090000d40590242010130140d40c051110980e100c0521a485d03d02d41c00700b40c980b5072622018000d4201025800000c1c45044080c10100c4440d510100c4010482401c0695503040c25440500c03e04c803802c00041005844a050141158840c0c82d44440564507030400398010b9000700007010390911a2100d0f80585980640e02103001c84c442e0740c05840d00e10107031004100c403c018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 823428794 1250 823427544 823427551
    0x90903090821071a04060b03010b0609181302060a120506010c0506042a23030d1b05070b0f0d0b030c01090512190b09070918020d1a01271112 62
    0x4403012401c00901c4c1140d4283d003d4400c501a0780c001c150300304213001b41402c6442036040540120004c0200800c039455074a41c1c0a4034204101320684941d490300c0080080c1c02281a0096000c179000131191607541e482840840e007035030b136004108103640b2400d005441618803c503004160303400c0140000d0102d16071955a8483c024043e04248034110000b1001e8200c0966800c2020b1407504c1d52101c2c0b00f00f9513040f84401c07942030140d0043c81661410180a045001c5101c0e45101401c1a421660100072090040c03030f00802e50700c2591510b5140c000c0701541c03190070105480d55490320303003001d041c0c840c40d00080040c1040d806848400100e414141401400d0688c40c2a10700e207886040b1440010b01400d148440c1c2950144202c1181d034288540c40f1750815a40d584a29050b50611404800c400d05000d80400f001c0d50455544074106500c1c80c0c02e03503840c41c0e0140c81488040c1d41d000005512000507007045010b00340ca9034616600a15213080004030703505100d500e403031404188602c0703203a03540c6484c5260300f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 823430044 1250 823428794 823428803
    0x5060f0105042702040f06090204081b01080402090c04030f080405120a020603012d03051c03150b0a170709060e0303030412141312060c030b24040b0409090309082107 73
    0xa040d410074281409890740340d40001b03c41035002a00b00b152070300900814402540c07055404c4cd10304a00b90000f0020300001d04082e01c20307500d03a00031079495025075044400a40d07011014140c5e040c00c03410f001d01650041d128407801900c00c0c501e101e000440c01f1500103812a4010f100e2070450b402c10f6121403d4075501610326031880c82411103040d0f10850704000f4402107200e14014038414132903100c02c04030a50307031151041c1458141818103c40e00c50041108081c1c0701003200c03a944440f24850103ca0310480c105581d001903003048180151150b01610b48020369442d907c400358614014001e1590b81e200c02c80b000b0300200802c11040d001644070b82c0600620100820f251400d120154a58290b00840c075030044608042070b01c1a4130801449006080712507005007410084052198082201045560309191081e4001600400300c88403036130682e000340481080c0c0c80c0e00c071a107030010303040103196a040c1900858056500010010700028220101445e1501074040404164050002c80c0d04000001c44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 823431294 1250 823430044 823430051
    0x50a12020a180b062811060705030601050d1d06010f060815040b030d0c02090a0c020a1101030f06080c150c030a05071505130b070e01020c0105070204061205060f010504270204 77
    0x205036a8510028207240841d80340d50114446600a08005c810a444000c006000707401030445140100454032681c850510705086a4075070340c0c100101c810748070b10762129400c940391008031030482d641e0f440c000c58640c2c5110122002d50b43c90301c030006d200096134400d0340001081c3c0c03800161100460b03800c11a41c1c1d04041d0000c11100d4008002a050210250528000a082100308001d5291600f031054221303d8903c4204022050403030000e40301c040a25014100c0080580d100b0000d0340b00364819145c4c01c080210800c609a110003001d5103541d05900031600c203441103000c08074183d100208803591841080015490302007203000588041d00410b50a0f01c4180d0b05000c20240110640a1607101e031400d142039400030080ea241404200101038000020001d03c911042520398000600b5141041c09081040d21004944001400b411440c0c000c03003070303400e1101c04880c100a000501d0901503c40009090300b03581c5ca071018031044508981c0304100b08a0400c002c50400e803035490003c0d0b0110300190020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 823432544 1250 823431294 823431311
    0x90b0f0604080d02061018021c0609060303020c060a081314010204060503070f0305070909090f0203010e01050601120e0705131d1c020703020901210615050a12020a18 73
    0x14400d40c21550140c80381e074101d000c80034001541403004580c40340105d1000308580381001007851552201510030f2001d240c0c00180ea842e02c00c03400341e000300c3e500c0301d001c4140040f580396032031031015040a1204030094490403000010900d4844140c80c0c1c00d010b42c0c1d490a80070354540044502d003400c50031080d0b074100101c0c04000d10007203080c001000502403d86030107980f4101101d0082040c3e811050203c00c05140c0010320000e01c0d402041c0b00102c482c104004a20781c141400e041204246420000798190b1030600041030315801908001d2258030262123160300c00c0c070070711072110554001207081c000f1a0803c000900461800105071220100100030004107003a444c1d811036503512440107071001e01da00407490b0a0305018800a4090070142078806415254910350101c1c0181106004003559450011050300c40c072107004080313494068101d6000d0106466417403e204441040d4040d05000d42d20519000c80c3c8207117403100380402140c0c05004040c20078a4085050815000707400e40c28141d0f511415413 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 823433794 1250 823432544 823432549
    0x2090d080c07030b010503010203090c010e030f01060f0609050a0609120c080610090e030f0d020c0c0303032d06010c1515300c17010b09130b0702030310090b0f 70
    0x58034403100010000c064490850070515084e9505a000500c030380c0c0100100314000e81c0104220501e000d080c00d100b0301d034002c10000a414090b600029824a6181032070005c0c03400308608002003100c079141c4846503800d894409005c4541031034040c180116500798000c0200c5681c1c040e0a86030503002d14801050181c880125604056080e1100b40e0080c40001050000403458450010740c0030351040110310704084646c240c1881e0007200c0303140602a40c00315480840500034803000b4450340d001011740784e403460800d8a20b01482c82c0e08334010b5507800081c500c4900602d20251080c080c050507111600c4090140c0e560021203864051740502c1161a00648900c0e0460040c262018000285560803103000318030030526295140c07081c1554194a845498010a8000d140310b000d51790702c10594040401da694840b805062065103268004245004115018024882c4490f040d8814a5007401c1a00c0700e207800c27a56030006440d050341c501c64440b0100640507095201c04420100a0f044102c5032607103100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 823435044 1250 823433794 823433797
    0x1b06020403050f3c011407112826030c0c240c0a03140a020a080702071809020a0e040305070210050a050426010603120e0a05030309010302090d08 64
    0x101d41030f500040004601540521507865090301c00000e04903006140c4802001500c8501003a08000e40003116003050340348203402071603042142030610900c50510f41001000005c1c20720b40603005000e040035035031142c1080c5080303610f025011030040070502c0c800e0315217512490031b03d002404001300808500c407051035450040c0d40300300000c0102a4540184205182c1086500320007000341c0780d90312405816043c65030603c01c0d00040b841d8070043c0c0b291180c41068004154601e01513400d0880101081001c80d07040e00100100c00e05641d8685280e200c00d10b040e681e409090240c3c0f07010000c3c004c0460003070400c0754407640e5130500040c5005000b80c3e441424280550064400b40c000500000e10b050560802c03440078054490b0070329290703250803299203008045010710b0250030014400440c0e40400c0d9a0a10305241c1a48502e4008111155980c0b03011309442c00c1c01088003011038010a268030346403500c10320b88000c89001070046c51030064548011402980300c50b4401c1d5201c007002840001003604d090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 823436294 1250 823435044 823435049
    0x3011815150e0303090d0308040218041211030a020a081602040908090312041203080a27030f14040e072c04050a0e0a0b04080d0c030b0a0f0b0403031b060204 69
    0x38039107015044900d0300410042102d000b043c0694000c1000b007115443e0048440017007601860488442d40311480010040301612424040d07034607907030090105002d10302c04041a043c0d82034807501c03130303060044074540e0b241d0042c020000090b0f0444004400412410b40040441e9841d40303035007490f0008154001011a00000070648801d07a010490700e00500b010032100c0c024202e24201c0d582468030307012084000b81c01c003042c001d04020802000c101286626040810a00402070a01c2c0c080c0c2d13540344120b141e600304824103a0008031902031a61a4500404006090001d0a42214945810210300000e003244c007030401010081d450b0203c809010001c00c05001d50340075401c40b1181551000d0401054400c0641190205441c0c401300c88925100060301c982442c0c0d0110015410365240d0501580500909041d0119182008421000645d055101c04071140f42150382c02035645d20750640d030b51051514021721010410410050011902695010541000c0b00201d100d00c0c8800b80e44640a82c1c1099 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 823437544 1250 823436294 823436309
    0xc030206160210021315021504060e0c060c010209090609091e030c01020301121101020d0509120c10090905180618190c090c03051b0c011508070302030d1403011815 72
    0x117400900c900c1d69002054180c1720520700c010415204240c1406030134010290004005130b55400001104400070f01c0340000c9d071071000305100e80b10202451268040c0d88160145841500c02c0c1c00000e9142c5030003c4d40900803a01c8074018400221828503940400068140d8401c10b40700c01d01c040828100240004c40c0648555202d9640112a91800c208101c1800740070a0640d0001a5522031103070748603041e02c01c02041122040e00c003094210042e810800401007241c1c02102c580c07442d651054101144000f01d40c86d0010030403c80c1c0d1902c10002c071510034481e071b95005410207400b01d15019800303201155045d6410043e00d443c040f440030250310150f09004201d44104039850208400c0c041d40c03003001410f400b203041c00d100d149404105846800790b0444111401d4902003202c0c00404401d41c811380940c46660602030720303907403201b403140d035501d1061000b00c0c0311748a6100810101403250240502d081841c0c41d20b81d0469013001e22107103604e10002411100581e03100d201e1400415404444e80040c4800c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 823438794 1250 823437544 823437577
    0x1050d021b0f39010513060e2103090103020903070b1c06090209030706030e03040e040605060a0812090f011209141c05030105060d020c0a0503190c03020616021002 72
    0x803099941c00c02d00f1803080074460810761510685022004412054444240f07000d030301000c0101d50040e01c59004014000884803540080418016004040520515401c441c0c00750142c40090315034140d900c0100448100760014403500340c15500940142c0400d68000f4182c400302a290810002d00e074000b038084a10790100c40e81e01c01ca01c51050321400c80948620041980f42801c10382c0401d40c3c032005441400101542d420005640d00c0b4184141e40c0504074015480d021820a8201398000d070008be9000303880746503881400500c122000889120080d410080f05040c40090420840c1c1d02d08146a01c90500400b030040169140c118403070781c585940300340341140d0f05041c029142850b000218149075591000d0401680369550420700340d90454204070740d42652001403041c0e1101a000b40118054207104440314241001402b02c003902c1c0300800a9503c2e16806411403080366401400c0d00b0140168215074089140150070700828400c00d03100d401140e0091410141180c00c0360721840b001d41c090f404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 823440044 1250 823438794 823438813
    0x403030f0605010813200d03180b030118050c0d02190905030c180901110f0a0219020a0311010c120306030212070303090608100812030a141501050d021b 67
    0x40e20440700a000d080c6040f0007149005441013041070280d20015101c01031004203001004080741380b145001002030690700c00b000c0309180140c4680110444c0070001c04004002080040d8001d05490480c0c41c1f110b10214040701305000a801044040d25103556a5401c12000904c42c055000030481281c600c01e800039100b4207810010107581461700014401d400142e03019000e0350f10321500d00d40401c92005500c0e500d454215125005082090000b00c4480021482c007800740504009007040001a4083d0f9000040c001101c0a807a0050300c4025801191590f0602c0441c20f0007082c410402018103243d03656000303d4807000460381800f240100040d40328481070003141400e04001d84100b810f040180882c0d41036550140c102c401c00c0c0602010403a202c0c0000d51007525905d00c03400289070300010348008a000f030030200e401e40c1c0121551014581003910b001040205a00c3c403900c07505003210301c4051816201c00458807a480f032601d0198044d001d218481c429642d104607010400c0212000b00f00090b03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 823441294 1250 823440044 823440071
    0x40f03030b09040c171c0513030215190c0302030f0a0302070b040804181b0c0c03061104090e0a031d01030603050f1c09150c06020c01020307020f0c03071802090612040303 75
    0x400341c1180c4c1000d402842d880304a0106220542d095113106d410308a80300c19481c100000c1003a2140e0011350b22000e520710410320320303200c0c10042c144401090001c01e01c500804205035560760880c1c2006005030700410666485070900c0c40a0b01d1a055580347c05031510724030380c0300e1201002065030305440e04080003030100180317a4000d107801c2140c01702c07110a01c01100c4d5501001c1602d554100312030180564003030a00704104101c5501e90203182c0c0700d841040400b00d903a0000866400171701559419600e01184500050740005049810a80c50b9564482202a901c061151041505040340c103142e128600400011018071118071350004803c02407490003d5208030017032200d10310200a0034401c0c44841448554102c0350710301089105801e02c0c5107441c0c01d03490b080000b88240786601d44c0c81c1d4804000c0c0701009601203203400701803007101c0072910002c054004040d218204c0c2e2083e0103411650130284040150260040c00c000c10f4000d0605042a00250109070800b404550482c00242e44401010010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 823442544 1250 823441294 823441319
    0x10150e031b10090308090d1e050303010603060b121b1603030509070f0506030a090203031207020c100801060e0d14011e06080c06070f051606050a03140906040f03030b09040c 76
    0x5031501c0d203010f4a40c513688924419110b410704407405150b55656480c2407051807140f01c0025445016440300c08003a60801d16141c0c0c0003030080c1d000280c10044006204210032042d100d89141201000c00a511180d0b0341034110102200c5181c0c00c4d90090021000139214490401c071503a02a072800318441c40c0030b000c1c140c06c3c0310760b43c0c04c50000500045821300c09a1a0181a04e0748582000d900044081c06400001e155010f01e48ca0300e0001720110080151031380d40410700c840d00d81401c2c0c0d49400d0843e04004142d03102242409188005590b80d020140d0300d00d00203850441c620300920280004c0ca07141918542959904018035a801c04426000800c0100611840d8028034003240a0003000e00400000348061103440005414005120113820078004207211080b001310b20507a001c0012030703407408058500d42150103c400400d18003c0150612690070b05258412496100608525501ca5507031074002d400314a4141e0405d9913400288296071580000c1c180103601460010300124600507228040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 823443794 1250 823442544 823442569
    0x6150e041d0d021002190503130804030c0602011a0108060f0a050a0f17190b06061303210c0f0320032703010209100e151602010305060910150e031b 65
    0x11171310401440d28070224030100800d42c042c1e2880e10079625250100c00310341c600c000040103400311000203030000400c00b006145004403400e0380c00a10840601c40014161b02c4001c0c101b250100c3d0380d450018015190019903030100e51802042001071903258004900d040350a5000b07010130300d916203014031404d04c00c134001e101c11114400c014102100c031861300000c03140e5140d4000b401404a840403924550780d030300549649011707464400840326030700c1c142400810502e009070b000e0b01d02c5c4aa150340902d4801c92402881da0f401c801c0c5103030030b50055070702152907010040380512200401c1041d403011740300c1803004192450040d00040740c40c0b651002201c5240d6042254544203070310400c01a506a280c0c925070303400d02030031828a003620800c0380000c42c0d4200c003c3c4000750303c10b4000241c105001ca0801045125850007079800b00480e85d211010700c152120103461703062405168410800007030b492004582c80017113040c6410150300890002003403400800c0502070003001080400c004607402c140c0b21102c0f1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 823445044 1250 823443794 823443823
    0x150a170c010201140910050c040b13061803050705091308040f0503070b0304050c09150315040b090c0a031103010603061107050607050f0a23030c040906060306150e041d0d02 76
    0xc0d090040d0745c10394811042002c0300c01c1c5d070b84410000352042c4041c07040e9030042007080640e503aa120080e609410002c550f000300e1020429441500141c2015415098140e81d40302d00203111142c100301c1000424140141440049100c3d1200c00d000949030902400040000740070700469903003400201400e0032481d4002079002002401000040b98001a594805e050305480000c00780d00e07145d4260803850750030b105c0d094061088990b0380c060034158091041c411030103500d0300c040984401e05000d45403c00d5103a07141d4003000031441480460502048140725003801000011340c1c554aa031410240c40307454220b01480d00c03000c102d8000340680ad001c0c44c1d41c451031340e14009180840c00c40710a003060080203181c0003009500510200d40c081000d000c0a50b9606051142d6103e1410700c1108055512a0003241c3d0050b04003000060454000e000744020785120484060206000001c100c541448148507241e01a440d0a540205810700300c0034400301c13201c0f11300a85040f41910740701074034100c41e0500048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 823446294 1250 823445044 823445081
    0x9110406080a1e120e01090302030106140310060608060126101503090507060e04020715060f0e060603011a0d060303260402030a02010c031404060302130815150a170c010201 76
    0x4000898011000400c4c0d402410055171101c2e0001c01202c1a07042600001e406601c0c1c40c00c0480c2070420721801406801044045500400800c02c450b010381d04070344a1100480d0035200864150343c06420040d1419205c0a0360f0000700289131015402c801e826648110400f07160401442012440a40b68641c16003170b0400384040035440c1e841944c1c0b101d1034030038130080069844054075295900c1e011602015044800c00680c4009210040001e11700f0340304041704182000e1002031028a02d250141c8500c400400386800d50786094580010740210300200c07400c014003041005106102d41c841c420280d80642e4440d500f64109004c1c02540c040c000d8010300c401c107001000c010050b940003540c400d03417550a02c4d100464149a20f002d4940f6022148010117008000c42c01141c100d50550181444609240340c0181c21a59804040d4550b040802d44000c0c0f070b06100006440b08a0f4001507034640500500604801e0781d48242040c18442c520a1820f03042e0480c0103400065a824002d55140c80003000c180c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 823447544 1250 823446294 823446353
    0x9100813062c07080f2e0b060a0305040303050a021c0207080403020d03050d1a100c0206131d090c18071806050d050f060d0609110406080a 61
    0x11100410220020407141e1505008070040380c0c01007024401d0068641d4241c19140d01500480e1640c1041c01007003203520500e1000394001200241c03a100401d403124000005031070b803a540d2000c075048130811050003600c5000da4480360b21000002c2c803200485030340010702803c080ca0300030306541020b400540c680d40188480d0108183c00c1402c0400c400b03010600581c1c450661801184500556001039031100a1070315800606800030002c1038064240d15041090602c030395a0b580700040c94008068204210144071300310f080c0a18540352149000030a40c41c1004d08041c0c0b101c8103c003150304503016071100303003032405070003c40030044035017010740745c4064101d000c1220085a04540d68284a030b0211001c0300100308414000c0402030b003007400e800e00281e030064a900000e440c41c0d000121049510b0b01d4100015a9250340715421801480d000701007400071004c039180c540c09041c03610020b5803c01d80c09592000f4070f955512605005000b90000307400b400f0400d003884081214695010396103040c010011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 823448794 1250 823447544 823447561
    0x70e042f03060a03050f030316020604030c12031d0d030b060309210c061e07090305030f070311011a010f03051510030e06100f061b14120708091008 65
    0x3508800401004941c0e126940d01c1c0020320072101c903034000351850096590300c100860300030006600c1038881d811003a641540c611822a034414084401600051009500000007045054600c243d91114500401e500380805112440d0400c40070071051280d001000c008642900360250007a000f904403255811481c041003880d0b100e8550300210720801c0380b0108020446003070b850a0f2031000c81c50504035035181c40c284000c0c1c500e0500e16103030740740b250580ba0005080c0f43e11484c925000d89a12002841c1054505002d98145422240702202884501600080400030034860b1400b090400c18804c007000c070224001401034003200d10324004040c103203130410401c04a003074950389600500303a075103100903440300328110024888406e950340240100402d03c180c1d003c4a001d80c0c02540d003a010b201c0b40855440360181c42e6980e010500031102800b80c01548080342c51103040300d02009052040e00e030080710502d02e002440e445800e041b152800b020074115182d007040c0341404664800d90400310502d0500041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 823450044 1250 823448794 823448861
    0x70210090c120201020304080d05040e180a03030b030322060305070f0c112809061203020a060239160803070f03050405120c180c0703030b030a0209070e04 68
    0x3921901e0b001d502940700031a40708004480041c11a502910030341050314100501d035500c24441c8a09141c000740c0071850303c0340021503e5011149110040588221390341c1e0690107041d040c1c01f10355150108bc05140080946015500442a026010440d40c00d090500203401c0f1400500901c080007540109010b00c81c1e08080c46801158000202403203007682d8000061804444004401d14610a83c21040c01c803480f41010300140e8404a1050150b281c42d203540182c8505031400c050010b0341701d2038000307010600319401440d4020071003041c0d14110020000034900c0301e0036000c803200c1da2400300320391014031401070110551030345040c0304c0c20403050701e031002940e60381c020104041c01900040040004150144044400800000d0046000c0305100034490303071107201c0d02d4503140c000c0001c0710035041c54a00d02c02c0507034411000800714600384038641d1800ca00411501c81070640511a072951034004d41c0d40e10810b10301c00c00c078175030305c02581c0c641d44010b0205036100c14030041036403900000e60000c052094032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 823451294 1250 823450044 823450049
    0xe0a02090306010311030723030d050f04060e030c0d03050705010605030c0607150b09090c0102070b030f1308120c2116270308030906070c1101050705010e060a05070210090c 76
    0x246451780200840002400c0404503440000d244a4810303402c83c00c0d02d05100c4018200304214142c5001030411203064403c5e1180c8080480c1802e0200400d0043c64002c05a01504e810050110340c860080f100104d8181c400440d0154045640411184100102401202c2c05010180c2c064003c06442c400819424003801400510a01c1004669400010365a01c00121060028050304035030814000030364032000a6403000c1e005006100b0003240d590b04800032240580b005410000036035031b592252403d200070003402140c03070382410800340490750b0700074074241d01074208220550790300c251104844c8003a400c95901119255825802c11280c48000715040c0e89940320390074041c0c556030003504032811200d083c01c01c141c103c00780c241c404414805248040c0d031207200710000b203e009890343d0324140c44046592900601c070b003c08021650180d481a070282c150300340301d90004284094444041410f04e5811070b0000e0340990786204001d20290f042206c11104c81d5062010061020f4641310651101d6090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 823452544 1250 823451294 823451303
    0x3240f040c030923010c030204082e050a3806160b0103060203040303061703040506130b0705060402031c05090904140312100b0a0813140d020105010e0a020903060103 73
    0x44000c140154043c0c3c02c03d103652030740141c0c2c1484148140c0e0745085100d6600c0265480b940c68040b4840c102c50180c402c807010389010800401c14a40380700b41200c01c01800f00d59002c2c59680c0c0c8000401c10710524001c4034054101408041600c8860070f021485044410804040781240710744401c034220050702e5640c0c0c0c00d110a035000c981c0e60681d510400290441128000c1203120030340000414812140d000e14002c1d031003650f041c0051580c2e080c1d0000901c40800d10a48a9002000100543e1601c03500400d4407460454140d01c640380d458140101c43c2c0c00c180c409403001e80240c1c040104516060144900781000c01e090070721000c1e03840348010210300590200c5401450290082010f00007000c6001380707010700c41c00440b030b0b561103203019015280c1c1c0203444001c0c88220003040450134201140a44401e450180e484042c141d503040c1e08658615040f41e002c1d41c2c480f2403506105e00c81c900512250008141540010a59514202d284460854001c0030940541d2062241c2203180d68040760041c11207820 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 823453794 1250 823452544 823452551
    0x252d080f0405122a150a0e0c0a09020d06090c0e0603040804050d08190c0f0605130606120209181536060601080f010b130906030302010203240f04 64
    0x310b25016140c01801d001011044102054208036a031030114401c002c0040b5500c0e180030000b10b28121a504c03d9000c0c8920b0600308200d001800103812540040010070551003260042c42c00c110125a00c0080317900a0041c0c0351b00084d00004100b403d01643e002440021803c01020f8000c80d4000d003403e00ca007450038403078180003001c142801451070560b8042c1c9030007419070b00542252b14218406900c40e00e90f07150700a81813810f141885002c4c6103c40d80c4a5040150500b078500940e407010000c2000601010b52000a14520700220f5024410100507201e0000120b000d5440c5004020100380010040714849014607440d02101501050b5000c00001100543d03010340ca640c034542500c00f1444401402c000341c2880300a00d01d0311341c98804940c0d6003062050314451f841e1400111440c22040b40c00988540c072040c010000744c0c004130010054495500191200140c5901041054a20381e07030040d00182c0d004004d001e80d2101552a0202109910070700030400b5000c0e4000ca8071951903103103114803a959 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 823455044 1250 823453794 823453801
    0xd020f0c03030c04030c080a03020d032a030e07081b0d022407021e030d080702030c0a0c08190312050a18061d010603020d020603252d080f 61
    0x816016124110039090036039440e860158521802c41d08076104c142c0c4c18180e001070010b1885004191941000d030540c2c090f140340c8003200c0d0103402404911031074500304032221141c0d010b01540c0c00c1b00c00a012000303070ba0203d603000c41c010307070320341307800b106401c900e1481d04842c2034004902c40701c1d0444000f0301b00c241c40207812682a400026a040c00e074090a88280c07035030b542040064012040140102c1e40b00319414650440d4003030b030140350110807110303c54255003d440f242c81080e00652030700ba44500144101c03440e202c92080c486041010391030301141c0c401060001032107000c0301031240440c6804051010348800e00a0b881c001d1019440345030041c3c28a03582d0f8046400e4070f403150008848001e040c2c80c0101c000303d03d0f1074118000e203800808901c140c0c4d00c800e81d1076281c0c0d40c103014103411a600240482c5000556400b040780c568000307080d28501000c000403a00b0043c801920180790108644c640450508c000c0701c0e820750155482c2c0b42949480703150900c3c001ca40c1e4110009075048181c0c92000e070016074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 823456294 1250 823455044 823455067
    0x70e0906030c0f13021204050307060c0f0e09040c1203020f210a050306011e020a03090504061206050a0e0d11070f0b040b03070c0c230405070804150212010b04050111120d02 76
    0x10606406c1c6452408180802060110000c001e00e8424460401001564407568085400700d0944182e980040c0000300074011600d09031740c06d607821a004002856070305a9542440d10703465180f900c02c0f00585c001801000c0c5681080c0042403141c0110400ba203500a5641c50200a0b84143d0041600344040800458450392003244240d400c40082d10150095a90042000c0e5580309414403c030001800d0800c0403803d4107107800703407104589a01802c40d07a11101d540d1041e0203880d00800207001d842da00c0052042c942070400c900411000310740c8402501583c500101070804860b80c0003c50070310403039041088444810000c5030110340c0c2680416890b9100c00c0011540302c994250003610001c103c120208d03404403c014481000324440c0c0c2c81c0b04542c4941824003042d07e20031943c24010440100000340400d460042440032210b92000046c40c2140d561000381c0700d903400b0b8008250042c000300d810722655801034409558450803000503d2000b4510303010720305600c980d01c90b041c403641e00496454100c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 823457544 1250 823456294 823456297
    0x307050901270905180705010e01030207031b0c03171201050f030c03010e07090b03121e120a0911041406010e030717030c120c0304090510080105070e0906030c0f1302 73
    0x2071920040340720350b09a84200001c040c1209442d43d00c5841c141c20f000101d801030004102c0119401a111303030000d11950401940250020300042d8144500b85402e20001c00220307400d601c0380340c402d1414185190440c02c18606110700000fa5039401c000400001031004407060f901411540c0c11100c441c911100c24020a05050340294000e40560800346045240701010461a007503845e9075104000c00034000741010340d04d030402000000d03500c0040082c1d000100c841c0c0440964801e9a66140786050040010700b080150216818020640da03006003800304400b1481c403081400c6d0417213003070207080400909003080110140101c1c4c18003042000d210030704c3d2007d1007010014031190240007403582135120015180e41c8001000c034441d000d41c2c84c202c0c5500340c200c2e090321042122200118202818041621f008041c05000362441446850001540a00900465100b0091651103070701920303c420900513011300c0506000d102e40c1128808001c2d58544407841b410086d41154125800d404190041c0020f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 823458794 1250 823457544 823457597
    0xb060d201c2010050d0b060f0c06011e1401030c1115150a08150c0403020a03030309031e05180a03050a0c0e09010506060d0e070b030123060307050901 66
    0x203952503284a4014000244450510380341e07004088200e00b01d840342040301c24207966524070b000c01c80030b00556500780709550081001e1480540303000c3c80d2540e8010b44070b40c80c0d005508030b00c4095100701c0040c040c1080320750764010f40395804c091518949080400c121000c000c0203114504265440200f9038090784100c00040256042c84159510b4403242d21408120aa044032440480b400c0c0c2c0d6420241e50030300d8860001101c004002903c42068400c600f2030702a28050441a4080740038040480941d0f503064031000107501c242c80000b40e810b02e0b450b014150710f00d180c183c0601d801401a2a00d4620307046001c41b070b42030890300340855070700003480001410a400303604081c01c0c5100b1a070020f010040c464040f0419904a008201c40541e2611001d50070b0740e508848040e005a01030200c0c1d40440d106800110400c80c8103402c0e00d030403a8440384503070501e0304240c1c080304009c445d25043c47c084c07105449010f43c0c462000e840c80c0d451450864000b41c15841400c0145040140c0c1c00c41c044406c01c0c0300b00e200d400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 823460044 1250 823458794 823458829
    0xe0301090f0528030f050a2d1d010f0c03171e0a090203030301060c0c0308040b090108130c05062b020a0f0215012c0a020a030c0e090f070203090303160b060d20 70
    0x141405041c0c652120101e2360920b05c00314420101e0044204041e404081c219941655842c02d1081c114404480400c02c80b1740c11001d010b40860710309220b00c42c00c00c025202d000040500d084d551841d640c0510b14000152030030909514001703142e40036031000b0003120305403080c508010b18100503615000950b286a13030f02c09402048041400f1607841b4600707004082986c001da80d02115921003881c41181329207000c0000b0a4804203400420040c1401c1010300000d00122061881030030056880e1840940c58420320403035a98000781b01c090141d0001c42c0f9852400316840100b2058800c2654001881018007402c20301c4502881038007604003440310104025141881c1100050508041e4207005e500020b0742c403030102e418440c6415100e44039007842640715900820030403540d240c00486183d103840261019085020802202a480e00c0800c000c041401100c41c080482d0700c094203120303c400101400c5244a28a143d92241c0410340d0340d07030b400305d108a102030700300d048902c1c0000040c5400c007201c20008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 823461294 1250 823460044 823460087
    0xc0318100c03060509010b090906041b1106091b0f04090f2009280e070803120c0412080c03090a030b1603020412030e0301090f0528030f050a 62
    0x24034001240c0001c0294650350700e0500103941c4500402662060034021029980c40c24000104d203803910000d15900282c01078000508003444d00340004e11076a01c084078a010425141030903003c0c1004011140c1d00900a00c040c00400f403044204040185030340301603a01c10400310440c255565a950300141d4582e5002c030001210106c180741c0720040c440000341b040c120101c6d02c405a54141440d06c5094840c4100c5180c070754003000300190f00c501a041d00701280c0d5000b42d030740544c02c04100c4108000c402911010f0004c0d916601d10005604601038001c140030b10240c401c1c031003000b500b40d030740000000860707000c0442c03900c4a50300c0c0341d4513207580640180785510035416500082840f40a507030300f501031030481e1041d004030380600c00298140d1141b4450448a02524054040428440c3c00160360640c0b0040011850300c41c1d03a250110030100b165003c0d18290800e2020f40c1b000b010849500780840042d412554030042d040d24040c0c0f5048921100500784a0009081043e880c400d15031820006045411034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 823462544 1250 823461294 823461313
    0x50c19150c090f061403220c080a0b090a05070620010501060c120e010e04091e050312010603060503030d230109020c12040e01030f170a180506120c0318 67
    0x1041e0042d107100d05000f803001c003080420380900c0b52910380030a00340c41d04540c2c9075032210b4003000c0105080340541200e05048074a24000603001c2250100213000c0a0000c04103200c2c83e0070440c203043c5e80079040030300b103511200da914002840400e41000f1210141000b44001003c1c1c104100c0c00c0c3c0c802403d824595180c800040713441a0002008d04665024150180c00441c2d02c1c00309841c40b009070b0741000c1c04590b12884c0600340d490140c10070700250b486101030072208010316002141100d040d031000c881c603400100e186060040c4c1d880d00e081c010501032406015031450180401c0c0c4034401d10100281c216181c140391030103000c50003204030280740c03200c250380c40c0d540e5203404a0000390450a065921030042842d003d1b21614007200381d03020385100202da60040d07482d6940312020100142402c65040503184800784012500070054507094480351102c4200300c07a04042042c0100c0c2c2c030307042244681c40a100e62901e105001145a62200100e5240d0307542c2c1e15034401c4007441c1c200f031a0058090784030f9000007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 823463794 1250 823462544 823462547
    0x60f0d0519060c120e100b04020d020c250303090315061d0108010c09081c020a0b1e070c211e1107051c060c03020d110a0e01050c19150c 60
    0x1a09010310141e0351016090f400c0b0b040e03281520b04621a601c0d041c6c1c01075150442d952015404a064540020070041c90b020700018900e007aa001250030000b035402022000b0464400e8603041d40007040c01000c4045038908541c2c0103001d1548034000600032003a0b44d5039040f550082544030300050241d0500207941c001240303038060100c400c00d02955507654205485070314403e004141c444240e03208107010348400e2445056451545000c5403081d0118842c0000f00004210725181c032500907000101e0701011014035034018842400042d101e4400c0018204400010401c0c0301d400d540b903400d21002c04c5d03c4043c0c0109040341d40b5480c4902020b04807500b000b003034454540284400194140c0101a0340b6015510300421a081d00d40c3c0009128007070300c0140f124001949584800c0120765141001402e2144003483c1104895020509042a41c0000f803200c3c08190005020f0714801400d1030031901c9c110302c02c60503e071260111481072040d4841080d0b901d04010150209054124402c207003000010501c030740 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 823465044 1250 823463794 823463801
    0x160f1e03030b030105061e13050708010303020f1b061305131d0706140c1f060501080906010302061602030102040312090e010b071709030f0f01051e060f0d051906 71
    0x20110086490a1840809414180102c9100c1d210007003403500005035070000107000c4551111090780c07042c00f82e01f0700c0d80401c03100e2251b140100180c0c1c0c1e601406604618010b4900240482020700ca50300c5100301d4100e403801c04100c503545142c240e42264035942d0350313003c1e2407144480340c0059074000907217560190058451740c401c1418410b40c5401403c0200005505c3d030705e41ca403a00a01c00060201d41e4000e101c000280020110400043c085901c084045020700303060980c41050b4410090701c0e500100702e03030740c1e000d200580c025409001800c41545107034009480c80c800c2c80720700003000360011040c2c0c06540d801e42c183c50043d50040414010f011485400030004905401400750107014240040350b4108024159124254030070301504400d041111002aa900200313a010303803500c03621004401040040c09409008041d0720f00205590500031081e80d0300301e002481c0110701a004408002c2182d0300c0400140210b5401d882860f980907942c10031904040c6181d04850390540c005240303001f044070310390 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 823466294 1250 823465044 823465103
    0x1c050d24090608030301210c030b0711060f06011202040509010f050a06080114060d091211010609020c070e040203011416120e030732010209090703060506160f 70
    0x415061959141c061801c100c81e424000c3c1d07600c9900071310041c030031100540d04400528100c255001040380860f42c401a01e84a00d4004803640c40f080818428000d8101d11000c840441c4c0c8070103401c4901c0c1c22003202c101124010f140b223041140c0301520349522401941228050100030f41001c4441d038458661042c1c0c003883d889100d000e42c4c544280003e04074442d6007034078183d9843c1c0101e6000011584208006901700b080034480f8140d8549590001440803041c8281e082103984807150103140390642d243c03c4801542c0054403550040061040142e0b000c02e401050302c20b0088003000a803910f00109004004d407200e5821001400400d0140100b4241c000c180100c069668140f0f40c06c0582d0044c1023035942c180d210703003655481400800d00195020700c3e40020342d8000250740f50744004a010070540320440f00c01e1220113950000f52400789040040c40e055020b00181802e0201901d070402203881440341d89945914992107201c140c040020901c00d07003078501d820007055000c00c07000d030340303c0140c446018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 823467544 1250 823466294 823466351
    0x903120c03230910050310030b0603011514030d03060f0302130f02070f11150301030b04022202070506010e0721020d060303090905180304060516021f0f0c051c050d 72
    0x42c003980103130600c41c0c0c040701d10138100c18031800d058520710f40c0d0329411018080c5c0102d074155220348140040c0c102e885012801082075205107c00075042030149070400340320310100c00030542010414401150321800c04000c8950540d144a180340c070394102c1000521250300c20040c0c0b2400010700209102061038015455030040c20441c01c915290000c114030703120b04400000a0110034401000880e00000000f54400d0001d058400c0c40741d40484800500d9080c02d00f0300002550214014090000400146014210400d028845400c04c0400a80130442c02c00c00244481c40000319402442c00d60340545800401101c42807007100d03120301e00540034110794007030515401c1c500b0b00042c8190040104c80391040b80d01c50041d5141c20f04017a81180c40d0343c85188540d460000d20a601401602e6500c9186800d6501110143c1103081d204401440104482d44050401144031052408034202044001c0380c4d41544030708192136505c01e4070a5419001c0c07400310840561606100c40c81a03038000c0f15400040541 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 823468794 1250 823467544 823467559
    0x91012060b0918010806040f0302010b0a090516020109020f311d0303040c09050705040b0c100507080f0a090f081813060b04090c0c0f050d02010c0903120c032309 71
    0x42080d035240080c0c0921a2040d0340c1e01101c042008a810188551401c0e80642b00109404e04108007217420509194006804980d5400401c1201c42c051131a002810010348000d000200280c5c002524007103420408074450121243c0a000d80ca0100c1c04204160640b075030490402c010b9600c80800401d0044171048050344002c030f002c00c0009010007140c1c403860b4000051080c460514003200000c0800034100d009019082201080032205100a080c400740100002c02101d04603005880c142c0b07602901d80f1041c091100140b007070070401500b145034400d0303c00c00006001c0559003001a5003544c1100701030070000780040d54462502240d805000040b030709440d10b510a0445500500440d60b2521400c84220b40601c010700510545030000c20480f0410b1501000717503011922800070050052070202c400703030304c0040d805c0c203c55020f00900300300480d142410f00880e0715645858656140f6000c2820400c52880c468008043c003c0140f4a501c804c1901c41c040310811650071814254080140284203240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 823470044 1250 823468794 823468819
    0x16090902190e0f0411031e07050402122202091e06030715080a020c010e030403150515040903020a080c07080c03032107170f040605090a08091012060b09 67
    0x1000d03591441260b001194944240e50f50342069058000058000c480ba5900081c112086030380401802c000810f410b61400c808080181001c4e1802440381c0c07040f8000c50040c0300300d0703100e41c46600c1550380c0964801001c041d050015030030780c0c10300c1d440360000a40c000252824060490074001c2d1020703180141400844075a01c0d8581003540d0380401d881070401c0003241b43c1d19420110b226040039034004c08824000b600f0803001448003401e4542c2081c01032500d60010500f08140802e888040040724010303c030400076801c1130b002171300b6242480400e03140951740f505425000c2500c208501d200322500044029140c2aa070110035864642510400400b8886d004442c0c605203404022903d41e0328001009a524590031001c0c411010030041141c800e1081030058002e01c3e03071505000da4440c492a004983c203619051409600322a13000d042c90116a015103640e500140ea54002c80e01904070480e1350094213081c89804952003030400d80f2003030045043c03440020340341c09003401411040300125021041c10f0b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 823471294 1250 823470044 823470079
    0x120303051501080f06062803050403080f060d1e0c15091d010302011103120c031602010b0a060509040605130f050f09070b0702040608060f1f050102031b16090902 71
    0x20400d0b0b8841800e052138001245040c503140b001071052208014060081840d44100420003103020700000307001c292104100300030161710600d23407580640e50709040320013801c0690108101482c0c00100500b0301d54449130903407a01c807619216440c641c1c0c1c8040141c41098480002030035510391298841d01084040c0c41c0880e0510307003100100134800050210300344aa1030340d0011141c1004040c40107005000070805004809810054540704e0700400c801c45660b03003070100110800e00d0030750500c00304592612a0300d04603030303588241d08030860325103241c69a111909000002d00501042c1d1003207034014540003401d01000415046800c144c03003000001c10060341d944484142c028000c5032003c0305500420310900c00fa121540140492a001a1000806a480f400610300d44441619900800e21305d040400c681c0c030700c10803964075882c0000c001c903040c100e2074000081d5907801030607200300540888544800f0604401c10120b015400d07060080d00c4800c0c3d560701184014914058180d005500348500c06000d03c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 823472544 1250 823471294 823471307
    0x705161a0601020a08090613030b04120e01171902191e0e100f1e1d040e120c0f0312041118060402030402011106092b05030619120303051501 62
    0x50340c20506046c035100226040045a52001441c0c400000c09881d010003c203002c00740c0740744268401c6500d013110100b50b94020340f2103644408c05a0420038410546071100c1188880190410380200006495468151000029020300d82008000749540928071094560002c2c42d00b51303a006041d01c0600740100c0210451741c2da01100103040e0010300d400303c039441e454441c814100300d810300e615002e41c5c189401c03880804800d144028407030004403142d080e480c0c0d0b07107641e191040243c04212010020382c142c001380d4076242d90700c621002400c000c000c07650700740c941d005002440b80650400c003a070359109003400740404071710010b540c141c070005640784480345030341400d03003c0ca9201003260161b00182d03034404081102a5100400403810032288035404100040d04000580c003a1449001501e44201041c0d1441c0003501c0e0100c4a0040c070cc80c181d41c1502144c0c000381200d80144040d00d68400c05601c0301501d90041041d0b41c01110b400500f1550721083c154194001801040c08100500c80c1484800044819 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 823473794 1250 823472544 823472563
    0x2030f0304061112090111010f0f0f0509010e102334091802091906020d020106120b06010507140307030e0f0f040b04060906150201140c0a080705161a060102 69
    0x20031300803c100e01881d03020303e105030f0120110000205041d4880c0c8001c3c070542d0900298580d00b10f1310781c81602809400c2c0c0c051168845c6c0e84c0402004500d90a1814607658a50480c140202c03e5558a1501202d048600111a80b890212442145003403444c40104011924150894a01c160200d0b50b16001d4641180d1001c888442c0d460b0280141440c0e015281400099a000b11059003040078883c203441e10820001c0d174100c5a040c0a4209180800181c04c2c0056085801e00710b91400e43d091000c1c02012072828016074008400380215a00e21006903854420410054041102c0704034402d01c52030008010091584640d44041810750120103000703040243c2480c0c2940f203110301840d000181410342c40200c1e44003000304003283e0a13940d104003500710b90698001040c201d208282100003a60240204840c8111081c02c807151440c100400208501903007031045c08100c1c0ea500810705181c0b198007940c0c241e0705814004004480e9a26045409860540d182d941844440001801641c008113007030340ca = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 823475044 1250 823473794 823473823
    0xb040b01080a08120c071506050418231f0902010f032702040b040f050a06080c01200721140c0a050f061608030406140610050d0902030f03040611 64
    0x4c004141e12101c4000310014501d020481d420b005010106411301500c1010030050040042d15604007428082518199100100c4100e000d1950000041c12441c4210000c00402da0100c40740710054410b40c01d00e05001c40035482c8414a6458420b80c10f141d5000841d00b6201b41c0fa030250400d4520016402d540826405e80e18406003482002c00880c88160b120b2680c5100500c0040e528008100003130885182c078112840041d40c032010440f03406d1281c8a501c000d40310500c0240320014058000800701d0800041544410f0200702c0c0c1c40000040400805016200c4d0780d842002e12014100002a0142d0101e01501d50a459a0140c60385100204030285114000381051602034148001d128042c1c1e80d42041c50b0300102c2c01c0080031420038500c1c1d0f542c001c1a10555100e51740341080d0500e90103440c003044d000078000300000300740011075035040203007002ca0310301d030400d0340c0c0365243c2d10b4491000b000c2452010750180503070590b00304126000f00084c400d40d0003c2d12055001ca810030a81680ca0b80341080d0000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 823476294 1250 823475044 823475047
    0x11030103030c020307030204020d140603070302090606070f0204320601090623180a090e070501030b030f0a080c0d0305060a26030f130e060904060506010e0603040b040b01080a08 78
    0x800d00c075400c0b160075980050101c41c030b455502c1c1d001c0790403a40202d00c490f01550340c1e141c0a08289500040d400d03000303a8210010500c890541e000100d1051001c0e1065100c3c040c009105020005000100341d0026002407041100b1a0601078980c22201c81d10409030308a0f4451f40d60003000003810418138050701041e5980400e01c0d0500c41c1c140c48290310003402007403812001044a14031048a401042880d81d1000381c20381110804041c800303246210340180b041c1508011318104d800d503000418a080714070034a00425000c8068010a003481030380700b1060214059005210144a8010002c03d1612016421500c040d07030800c80071012110241d0350a54004410b00d01017000c116001c14a0b001806600b1260044001003420f41d80385a0007480c04081c100030100d01100583c0c0c0300c0c0c103c0c40c002d0102c010b11004614010000070f14198000344000c0689a8500200b4107a03403050124211580d8094015a92030501b030600100019040f2011250701e9580c80021480b800c0104600608651044049 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 823477544 1250 823476294 823476299
    0x1e050405060f121e0a031413120f0b0a09080d020304031107060903030f030e100e0304051e0f0a06021515090408070605010608160e0f180a0c03110301 66
    0x800a4100508025800000d521840000d80d40329040b6001c200000001400110742c0525021484146042201e07203a8000d800c000012982290100a85102899050340e64010f801201800c1e2010790b042480103013440e803019020403c100388603015a5018010070350a03542c1d8013035a18141e901150000b001420280007100e041c03402a000742d50414031a090241d05840c8040842d450505268001400200c500904000741038100c5480714250358680340034410641c011140039643c4445490314054259a03004000307100d5018029a40600750003410361041c15100c0086c403900050f010000c0780301d03c000300c06152540c5072a850101c1118682d030003070400c030011006005402c400050543c2c100014402002c082641c80b0b20317445100e5441138850689400f800c3c00e100007115016040781c4140212042070202d140191030441c81d000a0914150b403100d100780c2c0108201c0060988056088401c1c80c0202001600c80d481d0b541c813840c8194000c200e0891400c4040b0141c61664070750042185040005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 823478794 1250 823477544 823477549
    0x705100c020f030f061b07030f120f11130e01120f050703020a03060e010b10090b0f041a090306070c081b0a12020309120c030d050c070305070803131e05 67
    0x450390940000e06880142e48140046400c0101c5603484405a4020200300035000c0c0000c0301c810040c5150071060350404040d0764002c3c0c5168103014118051000500361174941d00b0842e00861001903d81d141444450596004600e454200546178a0b07001802d1101152611001c3c291904844910110107070341c5006441daa4144241d0007030554071030154160200c05621581c1d9500f004601c6414001651102e504d099400c444030813014511a07001d14005000c2c40364812014400d407010b10001f1540d400545024100512170341e4040c0f0141100481100400e200c1300c4003414010a054081d1842e6564040d4103ea2052480a000b030190005000b08080c0603104014000c51092420441c0d220b510b003501d0301e941c0c4145a01d10300c1c00681c00003840243c1c40c148070342d03042203c00142d0020002c031a034034000a5110000c0e00140ea040020224041d10008400c000c443c00441c1c0000540385119183c410103902ca50048242a66820107035500003a491406004c0404500fa00075120b030815051008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 823480044 1250 823478794 823478807
    0x504090309081501061103120103030e03011d030904050106110a080d020c011505030c060406050d021e0d06091119030e100f02030405010605190303030525050307020708070510 77
    0x8180c041041c5850089018901003004000da440c6890302c03262603602d041001044412807030a41076080c0c0042c081032100b40500045d440c1543d5160810010b2524a4004a4010880d4a40101c5000444d52541c05014404801400e2444058500340212782c4c84060a55101d00c2084800c0c44961100071001d010801e0303c406000140b0170b02602510381058821507a01b5500c2c10350744550f2180c101c400402240c81c0401c84200b0041c01507500c0d90400386002005080e9002d10f40c0c0c4403030002c0d00001c0e0031204041000800341261004c01c00340361500c41e030003103d200a00032805200615460050101c00000d01c02094403407031407072803a40d1146142c240e0000c5010700b008005a24032440341d0b02010040343e07918001c100d00712500c80d50058036441c1c141003040c00d46180c1d0340302d5805404142c1850b402e0100d0761480506036074060901141c13546400c08034003c085030100780c9558074884911011711655006c0003d42c01807240d942183c0c101a224140192180d0f894440c4591010401900196080c0181c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 823481294 1250 823480044 823480061
    0x151602011104080609010c0e0f04050405030f2208010504230c061602090a050f010b16170301240207090c0905030d11121603080414011b0f0503100504 66
    0x10000c10a054141c01c06038503900150040c40031504807030f0402c0076480c0d0900c030380d0800140310714000590950700004292542d400380d181d40c0c040c50720b4078001418071008104894821810300c400681d5031000c5610b039881001244070100070700d541e0540c00502c4160501805006a8100c03030b2492540d48401003070390b0302c40340710f20000c1d05034002c0f074006a2032569094040d0031401045042000d03002880c1c41009869100100040c40040c9441e060100030741c0096086c0341598915109030350755102669100f100c26031901c0006100172680c0c60030f908d1301584a8080c2d4100c0724a110f0078900092000050049c0c614005070340c10042e8070440e010084061103404c206407141d481d0501403040350302c4201103401c01c103002051102040c58126442180c500c20025480c10600c101c2e034250070700400c0d4003109aa0b43d650300016081201281c0450140240c0c008044050035018008201c01c2924080d102c02903012002c0030301c04600c0c40c0402039090790280d07044905c2044600c2d0310280317043c10542000024070144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 823482544 1250 823481294 823481297
    0x40803010f080a1e1407141206091b03030c100906050604020a0806090601110a050105091504080901050f0d1514040e0c1c0f05031e0a0e10050d0f020712021516 70
    0x4140d080700d4083c05000a001600081c00343c8001c1d1210700b0300740408d2a1000000760b41c103600c52403c00c8103440d404160040100400c2c20f01034130001c4150006413460113075080a01c4140030707030010302c103041c40d1644c0204011840b4200030b01c190b9503a682040100d00071103800340301144000f4000781440c901100b1980e8005014109080144d079a18410b0707203030601c480001c8410f695100144444d0701000c100505503425190300e03d500d1071030580d5807c110380c064022554180040400c010b0881001c0c041501c0340c514801c0d400300003a403444400d40c1ea608407203100d9295000401440d40c0028180382c016141600359060003010743d10414028003d982c080d4140040b03804209100c00300000f003030010b022640e2401a8011525045c01340c1e591110350351020042003004008001c4101c50540040c1c100965a008442c4002645501482501c140c419070034850306070341c03a0101d00040180a540030b414100d00071701c4403401882528005980ea03d00c040701208031910680f00048080d0103070400c13129440900e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 823483794 1250 823482544 823482563
    0xf09060a09090b04110a03080403030c03030f180309060503060f1c05011e0e030301030b040b06011e0f080606250503071e032c12070806040803010f080a1e 68
    0x40e20054811219500002c9075458214000c4c0014040c1c614240c02900004035070010740d07980f4550f20100e007842680710003070500c40200107035000e16000b030b03210f140e40750f5200d10203000114083e04480d84c0e00850320341c102d0115014420200741c491081003620710458015040c07120070701da03ca0820654001150400070f0846200703403a140015030a0044a01c81000030301c01004125039001c1d03110581d4103201c0c00410782d80c0140010000f20700721841d0b0a030415080043c0b000c9607101d03180102c9032040581550b4507042c50382c044507500c2550000d203a060308051503407881d03d00c3c2c440c0c2080080c240300d04a019042600d480611900d0040701c06443c00c0540e2160048038502042d81d40c074000d5181c1e21180e48413009242203100802c0c5900101c003429410100c0b103221400503940c0711161141d50f50010f1f807034003800e4160349446800d2420040030028106803c00c0301c80030f1625252243e007230f502c24002c0008005000000081d03410000408104184c3d000c0f001490b299120b0180030307285d0a20071010b4900000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 823485044 1250 823483794 823483799
    0x13020910351006080601090b090f06011e022103042607060e06220507062703060b030c151801090b07060903020d021b0607050f0f101401050f09060a 65
    0xc007004002c031040100c41c1c020400034540700d401030901405900041c21a82055580021a51081a5140d102e00030004081c51515050300480e2070364030003010200508006500e5920803500011410f801101c100c4507564210811009801140800c3d14011f015000034014089500b90341c168070543ca8104000650401d05070b51503071001c1d90a00400300a840d001a01801200072480d1b00040c84580c092144001d1915103642d00e9507140e140d4444c5c0c3e400c00550100049007a111007441c0701c1c10021000b00c04400035240e0402e10f005149002d2820711901c0750300700800d00350805800c0c20400700203000d1160708119034901c1900d0b03243c01c09240300781081a400000309103060030f03101400816000d00b100046007046031501900e8512112400b0040d0341c407049200a294008a0744c652489500340c1c3c0307058030f0302c48030300d00b00746042d40b60034100d0314600540780d010200001c0055140320b00540c04406000c40d48064642c0c089110b020f00a113a080180002106038a00b0081d140035000300f0042c10341c1ca00c281c1e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 823486294 1250 823485044 823485149
    0xb03090c0a15030b010c1a1008120c06011202090109020309120c031c110405010c061104291801030515030d0f0305060303040e06010c0f0b13020910 65
    0x1440d8210700c1e819840b200d1041611949842040c400103000e0030002200d40c000e4507050306440f030350b1124040c6a841400014032039840c5082c02d50050134040c0480f10a030741020807107100b9404c0400d0740302d29481079800026001a0b2480e2800d049174000c0c048001590810b9481006544001c1c400340391849200802961020408010800100c1c88d402440e16500b50602c8080154481880d13094250700380307180c816445100f0000c0390200c58003402c0c0b20048a0462410102419942d40302d280b11410210b00040c011070a400e0442491a6224a80300500d4071908450707035a000c4c4c6c1c1d218a40c4e01d80b0a240118007940690320443d044640001001c20174204800080e00d019480c4038040000303080706044494454050280c00d40140085020714100341c102100c103421014014001410030007070703150030024803545c040c41d101c40c140c10103401074191800d402c59031440c20b0181822405001d144000585400303120ac0b0318426200402c030dc020704c0c2007404a04041c50281c42e21152040d41400320328035030b4113 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 823487544 1250 823486294 823486309
    0x10030e06040c0303170105062b0204030b0106110f06150d02030d09080d17070309020d0f05060114030c0901061808030d0f060e090303011a0c0d0e100e0a0b03090c 71
    0x11842601d03a03041e2107040d80780c028150446174071410102d051030380c0103001550b120300684407060600340d80790b01c1c0c14008006000b44d000c102411511805d1000401100f4000c90040c914165081511038501405289160725503802112440074020707040311010668555020321100d0604400074040d02400c07c69400280c00d0810002810012500d1a101000b541d02d051041c1d101d4001c16051191702c5004110102c440d00500074800002c240c1d4807408541155a0482c1e103030800f0760080c00c04060611070b468040e035140c0080c004e00c480203022170081c400178980040c0d0a500c4e644040d00104090b4a02041130325800f00ca05a80c6076162406800482c003560100064039080a200b00040380d20400d8a03d1a4101c402c1074000a441180320000c20221913030000499044078103007800c0030b500344480e0140c21464041c0c0c0e002e8040502840310050300d0f60340d000307440782003010f41183c6010807100c0c1101705403850120030340300580010b4442c50800580710880c010f158071a01c0c410a640c03d0150082c002643c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 823488794 1250 823487544 823487551
    0x204020409020d05060a17030f0c070f120b0a0612200d0b010e0c03041a060f04020304060507080115020712060b040e0f070b0405011e0309020402032a0a0e10030e06 72
    0x10f09644208000c2c2501c3c150341d9400c024030610b840c2c1c2c407684450880051310382c4030350002e07403101c1a80001c0100c101c12003000328000a0030b08040140629885040c800000d808205054658480c2c0c000032a800320040e11a41c01100d141c64440280d50500b60b031401c216046000c3c5040f091503415034a04840d481d050303084a42248603842d1800a0340c1010250580590081c0408505400600c03c000000e0000d040b0400d28450024138100a50303224400a0303040043c402303180750094008018401001010740021b40100d48580720100141e03201d440d2600c40c44000001d10b0016030007954100002506602c0443c811030080d00c0200e9006080c40c0030030196a00744142902c0765104507a080c04180c0b091180c04041c0c40e150010f0351a040c0740400003400000741c840760703c4040b002c0c400d210422900076400369601030f50190040d912460074100180e0032443c000c10f145069000c00c00c2c20004560a00115150800c0a0303c035050b000100c0014400c0d00004504513405066858241d00201c00042051902c0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 823490044 1250 823488794 823488817
    0x7141f0f18170f03030705041703070f0305090108070201091e17030c04030b07080403230d060b09130510030803040f0510091101031506030c02070527070c031209020402040902 77
    0x200b030401140c01031804900c0250503140b80c1060040c88a059884411a0300b240c480c01b5070204e00d44080690a802c511a8110060400b0701000c1e803541055080000740040c090240c80d6452969200319080cad003070718a2850001c00d084403181c00020221034030400310071214050030074a030450417680040107603540241c0380c0c0000448041410020486d0518003240d00c18014905000c4c41c2c142a0380c080c100070607400d10170000500c07080c94245201068030030b88101c0c1181082c180700455440d1103408283d403060f02068007c030340001c08804048078a0145e20700a1000740b08000d0918030b5915820010380020b13200300c8041c6940070b51040811010086031035403603c1040006440340182c47c14440d0196002c107014141802d003a0003031550102d000198080799614200070400501e04603040f820110142c11280d8002c4c100b035480c017141e40c010600042e040b01c54504c92207081c0c441440a8070001d40c0c022005000903030010003c0302180954200c942034600c051300160816850328010800d0f40c00c49100440d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 823491294 1250 823490044 823490069
    0xa0c020a0b0d0c05070b070f0e040216020a1d1501051e04050109090605030604021302040504110c0f0c03030d09021c03080a27030507050c06030907141f0f18 69
    0x101445480c800c0c0d41d00307980e0b20301307299217440302c00d640311400c100c1c0c0104202c00b48800c08628480c10fa005180030000b5040c018000c640d0b03144507581441404041607000c0e4050040c8480c0420440420088103040640244000b1110369920502c60041c144810045040003030500449855440c008040c42c4045460401d03643c071581400001441c1032420341c00034681c0d5003498000c00c0300d80ca0104400d600250141c9000712240d5a40c00d00724007902c00c07035020700e800c5450300305004229900752000e0310031009000300f1344420a84130008070f65203011031002aa41034004020941d10041c50b5880010581d03c05030840344152078106d01010950000001540428500002c205480080b032066404024024888071040340008002850003d01c0780c40007407e000d0005003070030520078104900c80340c00c600100341a659180c0030785456184c1c0f43e80e00c1185403050003450020668903054101c51222000c100c85000030040561048032011840402c0d50240000ca03e401a901164940c0070b001a017104c0d250f85 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 823492544 1250 823491294 823491307
    0x50612250c0f0227371a0a06020f1002090307050105030a0603210e091603020f090a090b03150912071a0a0b03240114120303072019080a0c020a0b 64
    0x3031003206130345c1c0c013200c420408007261030074007980301021203da41408000840c00a00109240c5803424140810344c4156420340004d903417a40041c0c00380b035503141341e001d446483c030161050300107a00540303030801e034181c002e01024081c07544a03401450f1305c98403070003000c030712a0b54a4031155080301000702001d1101c00b41d442000c1010350810700091099101b918089114030f0030b07021380401c140034580f0074010180c0004002070f0075007810b800c1e43c01042004180c840229a80d440c000018415200d585010703001b5a0b40320004d10821180451013607100802400d00001e48200e040d05035403011504a0f00c0b00c5041c10340c15003030b2042d10390381441019030a200083c0903110408040c5085100035008200102500101b039110704e50300b01c03240c11581c1e1442504a00780901c1d00042c40300320203084e100b00510010080000e640d501225442c24802010020111228004440c40e01d03580c000b0450300c0810140c18000e400206140010800d00b007051034104010034a81e400035000f080c15900030001e040020400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 823493794 1250 823492544 823492561
    0xd09030e09010611120c0a020a0f09050903120415020c15010e011401441e040f02100e0a120c080606010f0f0504050612250c0f0227 58
    0x2414054225400d2061007030350f0130f40c04169510a11807407926000710205115207020810002c40040340d500034071460f40c1c81e880700141d6110a20074881ca0000ca07003402c0114500000c0030003144c0054504e812800042d03911034643c161214240204030794415420081210041014440d01e803d50903010010b0700070354035141d01a0120745043c0c0060785441c40c400b9034600030380c1c0c11a1401c111020040e0b10020183c500456107120b010072a594130142a10082d0305501c01c10071200210711609051500099094652400c1500c03200101d84c0100000000d0b42c81d44094075008080c800c203949149802c054410044c800f150204d0115480141d10800000c150320070800d00e15a000c1c080c0480a005283c0c4d450305c040024500f00d9032001c02024851104d548490b02880fa1044402400000e04041e60719221035019940c4400111105080904208041240300c4061540d030800c4009541e04e451300c2c00c040d622082c40c400d030040c100300e0380320740302c6110282103501b4034410b0038409007400000c200510b001c0c0c0c1e1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 823495044 1250 823493794 823493809
    0x71809050403120b04020a090e1b0a050307121104120501060819020406080a050c012105010b09091320030a1e05070605070b150f0315161d04110d09030e 67
    0xc03450702c5036006110440400fa40301c40010226511060270140b036840304602504106000c1584c00380310440050072030354158002c40118004d407015550070440b4104101c44000b114040214100110030030403041029080303540400280034020000040c8a81d6911400c40c5040b0504030031304007440c8800440c2c0d05500e4a0322484008298040141454401c107548864036402c0000d82c55043c0806094036000325080d034245501d0348884000100403950312400c850707145401a200301442103843c800018900c0940c2042d0044007548500100e6003070500f4012458104002b40805400d031080b04500004100000454851344034540e1422059000301c0c10140d0912410343c22481c1808010005240002d0fa003000aa03400224860003a0035941804000703109040444021039140c86002c5055034804282d07826107008000700454502e03642403282096445e030004500c803030b40c1c2d1080d03410180564101034001210f2442030086251804540644100031118504003ea0000e00041c40044407800c0044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 823496294 1250 823495044 823495061
    0x4020301030f0c1e27470d0c0909260a08010b0c0a0c0920040608040206130b030a2c120c0312010f05030d0e030606150d0c1806030204060807180905040312 68
    0x540411500644a95120b5500390003541103000b5961809103005001048c40720b400644140c007001d2010396001d04146460841c0b846403d22a407030100a02e140071140b800498040300201d40302c000583c0c1c41c10300162842c1d00701c43c410b90003900401c0b002c1c0c800203005120a030302600500c54005054529109041215599444d032103010710401c00c000d111807074003c02c4150380a03504442140d40c07004c0a0241c0c6000a9065008000c04a00030090059883c00e90300401d0a000401d100c50320050300c4405004442c40b1500342c400400d81014808d00c6610310391000401c4022071440403240b070600b81d4000020400001d81c0010300b00d0130510b40c00e22280c5400c0c000340140034034914101240407032010019032900070251400d48101102165010008480015200349003074006003004503051901c00a0008103207450464404440c900000c12680c0c020702c02e84041d6200380c0e9601b6095034031104141c9200061411000c1500441000080c0098190040611907440307a9a039203119210540244196040c98 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 823497544 1250 823496294 823496381
    0x1b03040311040e100f0902040507020a020f010e010f1d0d050d020c04110418060e150102010501050901030305120a06050d033c050d0b04020301030f0c1e27 68
    0x143d0602d02418001404045070f9a060f40010314500d8089400c07008000c0ba21000303410030308044c2007000d0b031a0085080c03040c0e01d0003980e40e08894a4100c004440c02c1000e400c0f0640412400c0c0f0030344070a244103d4401401c2d9285030b5898000d4403d80303000416101180e80202c82c50b40c0040b1849500c01e505000c5074005c1e0000741c500340080d54014160020780d010340c0c002e20820f820000803a01804113543c101c14006c2a0310081284c650802c0500d0113108030f0810b0407203015600b0040005018100076000c00d04030380d015554281008031600e405110340101a1044c0764598a4441c04920395658400d84041c091003a00c1d851503050b1804409030320712001d0040c0c4c503000994881200d10700c686441041e03003a100e0074541141e940c1c400c0512940145624a045500584048004030801490840090318103000e0701c81c82e8881c6550708817a452004080e030200b0b0080c180380c2801c2041461101c000350400201c1c2450b60b240c0c1c03690b9243c960403205203920300d4100d81104111505602002ca00510110507103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 823498794 1250 823497544 823497551
    0x9140111121e1206010c020102010f06030303050a1a0315040201110d03020712030207052808190e10120504030c0203250f0303141b070609030b24151b0304031104 71
    0xc3c0300381c2400704500400780c605004401114504680c400e50145801181ca244100301c4a40c903402c0080082004541c510b1203035181007600701080800030038024074000300600510a45c40c03580c5044110311406841207062040400e16258540c80500c07003035080b00d809540040c1c4407035441c2046543d43c0c8a0b1080c802c20306104002070408102c01007011000c0030350700306c680306860207100403c003a5482c030349901901c171300d0700460b10a20714814101e0504503a42d042c0d441c0380d2000b0101081100c611078014804005c140c0d2203032580540d4190342c0043e9407160290401c8504503442d03401083c20000d9022668038600d0982e00c0c1c454483c0c0100c08120081e05041c00f9031401d45082d5900501103044040600084450203c0c2c08458070145099101003030303540c0010341d4945590b6580240202d401ea01013240c000c0035070b4000031288411307545255525900d03a021600010307030010a11005400350900c04080010821805507a41c0c001d104041da4861400300840d0b4442c80c604140300d1001302d00310507600c110304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 823500044 1250 823498794 823498807
    0x491a10050d03111218040c050f0313030c060906050a24140d080a0203070606060302090906040216050f0708070824070302040e0103111306030309140111121e 69
    0x32815007190800d90305042c20415100d04181c60b501d00303451030350001d007801c1000500140301000320041c12107500d000e81d020300c5001c80c0200d094030107000341900460341c00c80c1031002648034511a000288054060300b0461440030460f00c4503400c1d5040c1d8602a6485900e0304184508070006105201220030300910400d080480d5440c04903c5021501c0783c060f1000020140c100b45944001182c40042d502c41e910a9071440c04070381c06512030300505000d4034070604c4d00000203992070081c000c803000300b80010400071240e0788130000c2000a420220302040601080e0713401c40c00003030040014583c25040394000381441868100c4c013915020441d001019940c21407040214401a40410301c07018008c46440051140ea41440480c001c4c043c982c014400341c010a8000401c3c408038503101c2c4a00c0505641030840c03004d6400d00c0c0420b42d00700b840010001024402c0403c030812486259484ca42414900030700440e40c455156441d000c01110300b00802c15001500e000040d070740c0264503221482241000c0e04210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 823501294 1250 823500044 823500049
    0x1a0c120f0603030d150e0a1d0a020307060305040807020405091f0e0303070806060f0a0305071b1a0613022701020d1d0a08030c06070e491a1005 63
    0xe881e130a039221030303110260400c1c0c0100c1200a6400f81c9091076603e10b091402d00641c4010340700042074030b004400c030102c45420b5160040b41312189580c016000300801c2e0b1814038118003d201c000c0c403e6400340c030140043d40043c2d03a00e029060003600704900130906081801100c005840015514a125a00d049100c0320008400300540e40d208006042001a039945c000102c2c0c0301d807181a250300f0101d8070000b50f101ca00e80c1c142e4003a50181d01655195400c15030b200503008010700581c0d00c054000306001e01070203611804140c0c601e44c0404058081100491815540810f0340c210b0030301030300400c0810220300c50000c0d10401040700d102c8244010b20f0a10b1340c2000c007511101d62020f40d200d0201d12005c0400c000d0b105c0e045003100524105049a58910018bc846501c480e410342d40100003941502e00f0340001d2402943c00300720351141c4502100021038015030804600d40d2402d5190082e0040381d140191207014544207000c0c0c0d40100c0d480c100c6840c25160810206400410900c2c0b007550784103081c0b000d40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 823502544 1250 823501294 823501297
    0x3160e070c171e070503030109050f0606070b180709020304050d050909010902092e11030f0a050d0b06070302060f090604030c02010e2404090e0102030105011b1a0c120f060303 77
    0x204104030742e5596800c2200c3c444405a154142d8403c0740507400103c450400070008020360480e0700c140010051030700d8400c42c010403c60b09491a83e03110001703011410101d80c80466068210111003040041212000303c00c2c1e0134440b0690000901e164044100b03c1400070030320450039000b0b850300e0064030b0001c20000044505e1b006015541e030099001c98100500c0c3c82e03807a00d070320b0030b02418a070091200d1840403819948820320b010a000184030002480c440c90b10000603500b810584c90582d5080c01408082141d194000d00803000305151948400100f64a07004004c0c1500c40c041d6004d050103181664070a081c2c0034019014407800d07840442040042540000180318003542481c00d4807250100b100003a0b8070800c10081880300e1050401c182004005481c028011152406410b018006181c1c65850807030100b44515408500c0aa01c031a0300429a051004a01440b42c41000c05105118032520030200c01150f030681c012034000350481c40d0035031041105501681012002200b4500040483c1c2c0740d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 823503794 1250 823502544 823502573
    0x8030307021e0a1707030e090c0d0c09090608071a120f0c0706140106020f03090904080c100615030e010903021002090d05010f2408031603090503160e070c 68
    0x1500b100e8140200e490505101c1c0c1d402c0180c01040c0a42c041c0c8408201c03140903030241c0c0b412000700710b482800b01205d00300700560a10403035481d8400b9007001c0c50340034280084c2c80141d04100400c03011010200308840c40344100030103405080b00038007045060007045103011003d4421083d4140c0203114411151008441d0140e015101c060a01003984032003070f0800c0304c0e028444000b0461410103181901310b80c0c00510541c1240e40e15800c81d10380190641350f00c4d480c2e00c1407419a54000304900009000b0036000d80051511a580741c007104c0654901d00b509404881158001484016590200c640000d074140109034400d00d820008002101156501a584140d03000890b10403036000700703160388036039100c003140341320260071000a004915240d070030700f00141240c4400c6200d000c55031000c00d0042c5038030a104804d540d10503000314506080782200e22250700030b0310411000c20810000104042c0c80074006911a011025012001c0d02c0c00d1401040050174001e02d440704000c0d008903000c0125800c05000043c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 823505044 1250 823503794 823503823
    0x91101090b040b0901030902030f06091009152003040506040302100203090d0c02030718062409030b060a0f080d080c0f09040b030a0605040c140307060c0212070f18060803030702 78
    0x250b641c82132005030060940c1083c040d5040c02110f8801c5101d40c40030410b140b02d00f4a0b481650020f180c48400c10003200c050010190201c51800350094402c105a8440215a81102d0343c56001000d0301340410059481250101c2d100e4010005110405404020715144551011030075801c501d028840c1a5480e25000c224000300003142c1140c80c25500e00703008201c058010600c8100c000154009010068000c0c0e21030040c1001b042c2c0b413294020b650030b81c0c0c2c00c1c18000b280c0d543c002c031035480d5484c0c0109100303028101c0707940110b641c0390000f030017003843d40000010903800b0040e01c2c002081c110f014214100041806041c1c8208001030030840054004076884000d00b1a0001005022200468600100703190000d28140c500302c20b210034800038010b10401c4440f4504805050f0005005240d2900303414824070000c01c2d00030105030b0043c90071007480240184008225410740382d8900c85000317070788116031100100601c1400090101001c80c0540d01c0a0401d1500135881c5081402c4001d5a48061380e41d11103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 823506294 1250 823505044 823505047
    0xf1b190803042003010f0b030c06040509071d0d0b0601020d0903170a0c0b0703021905070b0105040203150d060209101d0907110703030210060503060609040b070e060d091101090b040b 80
    0x250400642255500c0880b005030080100d120311b801d106009183c0b45011a02c82e229210341d0303404c0ca01c4c1400c21101a2040500b9000d095119200e058401600c0b2540e1600d00303290307400b207a82c11a140d0115612840d0b000301014001814090000380c00d0502d08001e0300100010160240003040b290341e19a000d094049545903503990714050222800380000d0801130444640f141482036995040e00070300001d42e80401e4824198442820550b0306208854004009001600041100d440c1036806158818503821040b00e41c0074403800000e02d4074081c0c1e0006ca40380f0358046500100e60400c050b52085602c03541c1082c1032a11890b20751f0360045a244c641062145850800103120b903842078080d0790070001d03a44219580d050700c03450041c0d22010300c2c00000340384a01e4103034000345601d80082c0b40c5001e014003410129250f11540c80ba0342c1c200e600208a50140000700550018603103c80e4018510084141c0000071084c0761131a00c0015000030268603810041441e07000c1c03148246803c200d90403952210740d80c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 823507544 1250 823506294 823506323
    0x306150c0f070312021e100c03020c0a05010c08090106030213050702071d041505070f2d08150301050c0d020705011508030a030e0f0714060f1b19080304 67
    0x1468201c0700c005072401030061560000030044d55500f100c9070f081240d000c1d2690b0308140030f5218190600c109076600d42e94001905603400c051164060f40440f0341c00e19015141420003d009172502d5807980040760740780c3d0355040c0c41d0640755001c10043d801000c204001c0c010b007891900015900c0302032000d606047d941c1c410110314801e00800c82d58004080f80300860816000c4844003404072102100c00b91002d01c0308800740d05021196114082c0702d400e59440d01e00d83d000446200f100c204024201400c0004807800748102500d800e203110b002405541d07542c5502c14645040b40480240050040a00a03814801801810844401030f2800300b800e0000050b2181340d00d0802d107014241c40c9000c880c01c55040300c0b0100b00200301000034481e812454030248080e00e6040a1641c1ea80128a808020727a0082720082c17208100e04406403007040402459241000d54424082c29264080440802152690341c104540c102d03062000c1c51141aa5000c13910381d03810a500c600100b840010401494501c400451 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 823508794 1250 823507544 823507567
    0x315010e0a2d05220b190b2b021b06040c03140a1e050c09040209160302120c1201060e1507080c0f070501200307110d0f1214030615 58
    0x3010b00801c0000d0203040c61820002c4e030f80c03c2c40070601000143e280e050444410b080d007002240b060803210b5041610310440d103400000d4205030040900707540d00aa900091090742d003590019940b080c452898016500c4404080300c458903500d00710b4900a40d0411410072000c5490541d01c06c4c100c98010406142020f2040011403e10111800081810301c40d21721100341410744240c00c0c000c03103200364120f91003c0c11341d804103c0108000c4130000c1d40070450400003001c14440b001c0348141803000341409401c085080f100017560400c12580c50700400b40104004110488120541d030051065051111007030b01c690000c109895981c0c101031031901c400141c2d10040002110403101100c8414041d0380c0030900351411182c40b05214890b20340062440e9803114800d01e41101c0c1c1d07540c0003090710021450184a680c1e03c0a80441304000c44da4001035a86600010030700030300700702c8003045c0300e0b24001d0008901c0180c040e100009601000088480500070810b87d03482d001c08e05002c500300c040c0915101c3e160b0445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 823510044 1250 823508794 823508879
    0xf1203040614040e0c120604090f1103030909041a010f0b03070c150f150801020c0a0f020d0503030a0c12020703170a020906040915060216090515060315010e0a 70
    0x80d144d4a401040140081540340035044032080709200792016103540080009503821036002134808925800d182d00015a1501e4031447c009024055a090510f400b0004010b104100d806683c107c04469140204442c0001c0f52805008031138100c00c58a800e1858030b03207180c040240020203011040b40e402041c0f041c0f40e0941d549044a080c0144552001d40909001404071090b048081d0104900d02041c0041d06001360f919205c5070b00001c1210008a0701c070010266203010059820000480005021030400d1008522500f070b00900454003070f4007100001c0c501d265007034550155520501c00715000991240d00251555103c0c03040a03982d80782d1012040092103403014850b4056800200014948010303040001d456040f5806201103d03078401060380c80cac1900c4019040400c08005083c0031300c2810f544030b80d4000d040000000c441c101181e000c540c040d4404d9032400c090034500c0701d204001e5a0b1000c0d5020b0905004c1e6440c107210b500d0802030342002d00c544c4031010841840001c241c1000645c0d00c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 823511294 1250 823510044 823510049
    0x10c091401210c02121801080c0d020f0a111615020c0907260103030507081e0a0905030c180c09011e0503061806131a1e0f120304061404 60
    0xb0071502c0002c1040e0045801000c4070102900540900e03200b03521400e200c102030b540455051240c08140844c128011a00110000c00314405807a05020351b00391901d440c8080c286c0003590707140941d503900341d07030202034819845ea00c1600d00b0340e4003a030494410079804030640c00c2100d00010000c0042208540280e04014800110a400003980010000000d030302903824030419100203950520b040c0c0181e000907000c2c800b40005804100200005c0c000100f488000b0076558216070030422074046000000c50300c03680809412000180001c00a0066150500002c10f0b031000c2211055100c10182100c5100703513400509080013031034007046803044c0da405000c510f04071240e20040c40c0c0841d07113003040191032a0400e49046015800110344401c540007118251400343e20010303d51510748030b41108400150135503107002c03d0004502d806198080e19481e503421071903501114000400403510702404403482080203114419042c03078805182e411400700441c0c00341d0748103191170b600584055020013220710559 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 823512544 1250 823511294 823511327
    0x12709021002030405040c110d0f0210140609090c010806060c07030c0b03090601061805150405040f0c0e010311090910120c06021b0102030a0c03090815040203010b03010c091401 78
    0x440760341000d558088010b00655008130b130304212010310610100c0e0981d40d140e80140c0a64001d0440f554206d02468208920b2040d42c411520b1280d080c01242c400d84041152180c0b1103242c40040c40018178103280d0b42c40d40580302c08014020080c040f00000c00b46140546558058140051080350311042489040040c5400060307111090303a41c0c2e50100415841142e60b07003121300802c0c2c0080b4805101d81c952000c00d10348080000c01c1035041c40c0c10000c0a290408000341ea5045c00c000008281d1101d008501007940c0098000030307182c2681038081c000807000400c2c00e04151400c1007145c08481c0a43c02e55102000a85040c0d00613561040a0740d4803812540100c00440822a00d2508008070854048180c0310103a0940e000419240300301e6810700015102507004d40c1090020780c0e00540b003000a408854002e14003400c0039a03864030414109040ba548814180d5014820082541000d00441240381e005030020021081d10100003010408140500317404003e581e220320712168403031030800d4444801c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 823513794 1250 823512544 823512559
    0x60f0d030e0a080a03050403060f0f06091a0108061c020f030109050721030906030e0a020604060f02061803250b0a0c0e0a0602060613021605010207150501270902 71
    0x150401905400419510a101d0309141402082d032120104134213000c0350b410380300c50b818a0700b1503a03028003600c000c269002d0200d40d80d0305401c5002800f030288000521007038000040e54984d1510345c4214a450310141e034103200000c01400070700e0300c9800c00c007824900301003140c8480d01120310005203480d00c0540c030264503600304030300c1c0000e0000224128040302c14482113003511519501342a40c0f010703804d503000381c0030501c02c01041102c0c90182c0c2180c0038460100f0255100e0440c10381c0011240d4025410003000248101c1c80c0b0b6000503010417009422841c2e00301803000078509595070035901e210302811142031034540480060890401034001d9211076100100e44040d03d0440c20343c1000700034041500c40000d95130804940c0740c7c10142100d1046c0c4950707502402241d5107a005103c44c0750170301d010218074141c4c02c001028a00c0031000c485216644118005a40d07a000e0381004500442c900300100041c920f4000100a0310720f42c02c259500076060000400244a0240102e10003000d01c4000130b50450304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 823515044 1250 823513794 823513819
    0x1b0f0e0109180b10021c050304030c0b010e01080c09042612090c041103060a2102030102070c0f0b280c0206190216061d210a17090d0209060f 62
    0x340340c00ca01020101036600c4c0a8400d01100100c1e515090f98461051700400021071004261041c0c009591107402800c14603444000b03030740da100c11858243c0c4850442c0b00c1e501e0050101d80c505111801d500c01040b40e07522610b040940f503000da8880030700140c1c40d00f141c0600e502039440c1c44174030a4030603d112421443c1716a20302402c28a0b150404003c2c200e2007145000702c1c411740180c842d0103690195501902e06072a9506200005c0b9a030202c0c1c60742c801c00c1220741c0c14014016079090009040151281c0c1c00080d00301c1ca800e880c0190035000703811100d1056810701c100d01c06140c0c6020740d5a20f07251a4502e08101c903521403402c2d95040401400a900714900041118840101800ca21041245607080301d000e0380814901c8066600c5a0203204001840c0c0d90451410042d0300b41340c000100c2e002807808401034040c1400c5c0d0942c40a401e4020f005d9044a01508248103542e8028022800109035480c50300d5000b1000400134640e41100900c1165040c1c0860a151074010032a4103859010703241690416 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 823516294 1250 823515044 823515089
    0x80318091536010320011d241b01060803040509040809010318060b150f07080c011413110a06080f040606031205040e31050c040c090503011b0f0e0109 66
    0x10b100182445000c0300713641c0245c01c0f54031841e01c81d2148104499030607003002c03016041003030311007141409482000b00d4664480030b9a20400003001d9a009900c00010507003040314606003550515031001426400038802041207454800c04039610603030041b102aa2006c10900580007000d404c008804881c03010300851041044550220030142c804131400c0e1030310408100590000c1c444e07101c01c005081c5081c0070000000da0500301034024240f80c1400400c0007028150703101003464044541443d0386101c40d42150500504200408441c007099459905c000e00305200541580005080c00359905030040014051040c0380e40b24001442d803000030020100031b2008001d10682090007000c4035407a016000c01c46080e0713003804019507006004600400c400b100c00402c0f0140c00d0200090f40c85000390300050541c0d03505ca12030002e9005207520741e04c00c0c15007402c00b41421034a107030b0100c02e0120f82c02d0342d841c85015004202d81d2401c045500d0801004118400126644d1141da070148450704d101841032401c25 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 823517544 1250 823516294 823516313
    0x603041b090207060b0a180e010b0913020a09092102030c1501060210060305060f07090801060f091b170603014d0913060803180915360103 61
    0x1580031300d80a0112090171810404520000e12400c001c201c0e01d40d14030000400243c110f8200c0b032a114000103050750f20300300442c0c1001030854681040f0f90091414508500e0700745409009003004100401c0520b0144d9560300040c008000d10500c1034a2104122420070703c00c00449075480c0c0d5410645042c00586e0140ca03242c0c00080c091300303025000300c0100c0d82e0184058401c1c1d41c2100e0f00000203100f82d03158036283c5040108050600d1080264446004c211031109028800041500c0261465058500701d4a82e00701c2e00e880d804004101110300e01c2d1402c0743c0d0300654103501c1441050941e840c41c0c071400002401480149407150800c003001d540e90175981e0380205112050281c2c030104c10400f0201c2d021400000c41c02610f801107824007442452518108100030a80102d0740351000512140c44484807446d44d00a04400d04403616000b002c000c1908207601c041c2c1e00f22500c4000380c3c61030b03d540300000d94508008180511543c002e0b01d111142404452940319022503a03030414003503540c40c1c4c14014000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 823518794 1250 823517544 823517557
    0x5060f0d11011e02070b0f04080d08010303090b0906030a3204150e120a0215010e1f060905010e03150403050a09270b12100207050c030d0e0603041b0902 67
    0x300310400740c03ea8075030b041c0010608154009a002c0c0c214541004108001600940d000e100391050a0001190100d02080039100008240d10b40c1c0032650b00d9807a0090603090207420691200d0000d0003044003507141d10b0f003900c0d04465034400c0480e12640a09098468403400c0d41120f07000c2c046c003022003981715003005805010754001e03040c1a200e652106851002d5071280800c98803d40e1005030303c91a1000c0410261801c0340e000d206035010000c120088050b5820301307800840703428141d241840100d02c1c1c04101da07079a126091103000b4060f4603000005d41041d00354401e06040c0080c09820f09210b94041c00f041d00030380b2401d610465107041c00c0c10005c000d5041840c820b80402c0c180140030032841e0140e480300a00c40b007113000c030151240d2001c90b40340140034440101900f00c50443d203804084442804004901090240b0050700d03503100e03042c21481c04203500c2481303019030440e0705108580e95102013490898401511b01d00c0d0340b6143d901c2d02081c0022010524107001c0644103010400c1c14094004018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 823520044 1250 823518794 823518797
    0xc1f03060503032d0d0c1d040c1b0c0b0703080912031b09010203070c0b210103020a0302060c0a1401021305031902010f0302040b0d060914011805060f0d1101 69
    0x60140c450741459a20712807003020442c21140c40501c50716030207800031303d06110043c881219003000360343c408450aa0303070b4100e1284089226010075030a1544c101100144003c001c1f103051101080b009405890700c40300303d24840c810b1502c80300032414421616018030083c07907078030481c5544048a040050484c5004d8511039014040d281705080c001c6071a9054902481000c4054030802d0850980318034564011010641580010301c075400108611140301c80c010710f100900c032562280786642210b02d81590b100b03c1c190100d1840700500150700c0e09140305d81901c3d8180d600656441d0340c40001450000000c800402c0c1003c0066108440d00303064001d05402d00074404001c0c1c6164407482019107030707a1051400b00d4541c510a141801540c070410302c1d0850250b136070070010f2074591205600380c8194030400c50291580c0d19104104052140b0f031103074030303040380861140324115414418414000c00980000c5000b90b0f031a4404a0501e69508000001144006220310151011864040381c0c00e1181d2501a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 823521294 1250 823520044 823520051
    0x6161104050117070b0a110a0302010b100203040b0904020928030303050a09020d0215190806030d020601080a0f060f020304200913060e0109080a1205090c0a0b0a020c1f03 75
    0x28106440f0401424a610208060300c00301c0e00302800c0080e10303001880240b04000904904000c850028004242c400b03003c0d80c0045801e000354014001042980e01182046500c1044100404c04e02c900a4400381c5200300c030b025076510b03140c00018020b5a86025500b00607d9030711101d600b00307151420340c1801c2b20321980f014000c50b51031041d80d108031600c0a01c06500300c040c460130070006140c2004c1000b444070020320400d0424200001d01c031555032100106c18017040c420800c3c13111920f410032504038400e0852005049645c1403103182174603a004104010095403404460504100403604010240c402c140f00031920703441d00d400c1c0210b8407160034004510040c20010204250304110100754820000b501c468600e0101070f568802c002d1819100700c0c2d01030f550300d8151720000f8034080020601d4035410743d51488070303c0407400b5400c01c80b4000351540300340d584240325030741d071740c1d10b456200b80100c60a43d01c89070b448500c4030505a082185249816a04c500140605a11045c5001122074501c0321643c041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 823522544 1250 823521294 823521299
    0xf120f0609160501020a0c0302010e04060905190f02131206140f07030e0111040632070b07080403090b0d0b0a03080a09080307200d060203041208220b06061611040501 73
    0x10398607401c6d0400050150280d051040c0055401101c0140e504c18000d480010a01d03541c01c4034104503402611403d00914104651100b40c5010b4000c000d5102615a4111f2610000c0c54402e0310b0035200b8861000041e03050000342050011039800395400d10f64042640c6c9003071070b0441054007084422200c0c01c0c04070b483d001c00b0043c24181403203030307852022200e442a40b1307050501a0503181c4e0040341d0001c0d0b003080d01140c030010b842e01605c201c110403c0b041000a0303171256000e180c52160004020100420005403208000100b0b13400f00303a450441d6454000c41d03640c0c007001080c4201a00800e100390741c0208610100008000d4602c00406050103241d6400c21001e840d000d0b55a180d110340d000c064580000b100c03000d02046261440b910b4500401030003000b280b00c0603507500d406d1360022101500d90000700c0d450010081d40001d06103900080c1c0b220000b9000035001101041d8544284001e40f81010480c0062103d0b05d501003104c00c101912007031085003900c24074202c0f00c02407034901200e00550030030000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 823523794 1250 823522544 823522547
    0x41b060215060f0d05030c060601031b0203030a05040c120c230906060a09080a1109010e1303030f0618150909030f03020a0c080c010e07140f120f0609160501 69
    0x101003880c03000c0140500725888200c1003000d400b500141103584007071101c82c1c41000a0041008080c0c1b012803002500d01481c0c40e600140469201094610b0300d54105003449042550200480740c0c020300c0144000b03500d40751410082d403190412f03042031003802e4944074040306100004500c8400c640340e0a0405034006402034a00c244109580c00c0c00350030040c0040400c04c00e1414601410b0710401501d402145142d076802020718110a260041e0390640941e244d0003400e0400307032100c034054500d14801c410340e4200003c0c9407a18800f81d11010f000c240d51002012135a04480d04494001c148070140c403c24a803440080e10020250b0741010202e05004030300014410074180140301d04036405440c2c80c07400060054064001c5c0d403042c098002007108660419001404240141c61079000500c0001610b1310890310851519855030010310045090703403041d1440d0707a03511400084219041c0e40c001c95486241c08520b15101601c1c2d07c904442c0941710802007410800030303030003070051f054900700c03d005c41d5100d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 823525044 1250 823523794 823523803
    0x4060b0a0f060507050f010c0f02010f06031713050a06030b2b030c0615060302090f041a0415080307050a0b07140a0528050d1d1506031005041b0602 65
    0x22504a0000750504110a40c0075038042c002c50341c010026250001c500350205801c481d2107000c84000310310407142c041c2416a09120720b04500303019607802c000490440e210303070980c0c1c5c0b2070140190301c00000140e80f006400c114034141c0d00526019007640840c03916070303601402030407110010740d004040a5511540d44400c007204c0d15101380101101c3e502c0040709490456481e40001015100c8549400c0080d080909a5680d080101410b83d07005071595074403070400184107a01403030584074500304100450f200c10080b84a808880080702c00043c1e140601c0101004e600e0154085492400301140705414440040b030103070303041481280141b12603500d01030306903081c0b6100d400710310f007041703043c0701d40e00d0218041c0f4010718031003000d0004402c4940740300d04c250100500c0007080038005240421200c2a0351528090359800707070404004201c240002c18040e9a49020002c41601009111004a111754409000314840464101000d1180c0c0c90181010325034009038800040041242c1100094031500c0402c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 823526294 1250 823525044 823525049
    0x9190801050a150e04023010111c0b0111070308093d09030803100303080603010b0d020603100b0304060b030c0904050c150d0e1005150a061407140604060b0a 69
    0x7403074100c485e1110b07024030082d10100c544a01011004400d040b6a45088141e4045440c00d08402405099002012034084e41c2103950700500c032170000c1c01245030b8105e01d4040030380b10043d10f441c0095084003000040320102c5001903e4032030742c00b84020202c1031051200081010350320070303542002c180c8102240c00c80c20500403409281c05200c00d000014059042d0484083c104c619841c080e213a080d102d071640c22403a40151110555545005800c04c201a0042c81c2154040c0f800c5000b04199420707040890740c2d0300c0c4a80d1009209040010010380c000305003c440d02d020b0708000c1111a12460b140c5000030081155881240c801c1c4204004000d0303a00c1d01d0200710f0321a40d40040549002070f6400180282d410f04220701d411442d4060040c000c4040c1180b0850501d106080010203610f014844010119030020b04a0743c05c061076807504000a07180c040003a01190300603d00782c010f0100600604003a40540c0000418907458010080d142000000e070305801a4020f8000b0070041d035110042186114503403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 823527544 1250 823526294 823526309
    0x4050c15180d0606150206070905012012070510060b0403030c02060a030902060d06050a08070503031b070302060a091806080c0d14060108160e0906060609190801050a15 74
    0x80040e81c19a0090401c2a450304002504038000041c40780d0f915003c1c4c42160700425802c9030480c038441000303941000491380185003814092086410600001d22120f40040412501c56450005403140c060810208103a61307040e150f5540c0703541c0c83c1d00c0c0182e241c0c0d60442428bd0024144180410442e0000e02214200e80d49900d9034402c0c1c07a1a0b500f806075036000200004141903440414030003603100c040090985a1009400140316400c01040041080c00c40c0c01c00d034029031000d5030502c1182c50000407100d0122132070078042c5005105e0310415151910640000f9081440031940da403405400c0003082c000d0b03414800011900c540310b009150200c0d88503114490783c1c0e5001140c551000d042808110304458054071140e50107900c20140540780c044280d10211896111015880d6050510010741d8040e1046500c072040c5802c03c010700c0360307440c0005098503104440c0021b00b12030700da48200da60b20540e40c000112501c0780c0c1c0d441c2d445e0360007000119140720115040a4803203e05411580564040e10000b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 823528794 1250 823527544 823527547
    0x90712260c0f150406090303140423070b0a0c0c0314030d0605120c01110c04050906010302090903070503070b28060819020607060b0a030b04060c020c0405011d0402150d020304050c15 80
    0x4a4032501c001d8201c6c0c1005074103150351501c0c1c0d803003600300c440860b6109500661480c10506954013110032441e000c10741ca42155004858103100e0343e11003004841c841c0300545418014901c480c108508417418a0744010289070300300403445280360001c805010020392501041044650f034070f05101043c2a2000b1950241c1c104292110749503002d0312103031030800300c400304403000900140c000c02e049460580c2c403032007a9885a0010021880c1c100e00180d440354014001c2c0d801c00410755680c907901e0040c000024406100c0c0800910811a14044031100e254629101c2e41150380c100e00540081c09a805000d90a010700c140d1400c404010185104070035501900003850502503446402c01080c0b00200564040680b43d000030104102c0301c100c600030343c050100026044a2a480a845c0012103036409006a040600401c11103000341c801c00c0c43c040000445009998441c400030b10f080410703a030008005000031171a0a180805035015510440c0b14004495080c4003600c2008401d1480b500d803404900340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 823530044 1250 823528794 823528801
    0x90605070e0112110c01060b18100c0b0901090b070509031204080a061503050d11060a0b090f34120509060610030b03030403081c05090712260c0f15 65
    0x44690061180900d84c20010741012000002d550a54519906c078517a10000851000e61504010000b21180c8008071a440803950300030740b01034801261000040e0402c00f42d140054000882074009507440c50f417101c00d0350301910340403c01400c1c40c2c2004207403900034490b41080e1000c0212010450341030b1003140e0010300c000752040c1c0e502005040d1264005501da00c071001c0000004404100040e001c00c070589840c0100c5104441c0780c0e1130802d00074144003e80c2d00307100c103071685500c0303e03244d8a8100c2041c0740c207603a255032071199001307032015560310904a00e11240b1255842c1e40350304400d00c00d01003295503441411510a1005016210140c1300907003950060004229246401c047c0490911900d041c0410390040c000c2c00642140c1085d8001e4845450000d44103c00181e43e61010307841c0f501c80401000b5a08000c007045560310340601070f2041c0e142d011150700051003540960b1100c174554480580340100700303e080b0121240c204410182452050408400703401d100816030302e0788803d640280c070200c0e41c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 823531294 1250 823530044 823530077
    0x140f011e15082b05040501090e1e0a050a0e0c030601060c051002121b0a080a0b0103020933070512070606091b121e1a090406090605070e01 61
    0x103407500c50304968000030704001440c0c9010b115111945103000940da607001e00e6610004961995010142d0400408000c14070003a03030403002c64810350304e114202004980d200d08a00180c00b0966907487c0006000100700100c0c0c0350b8a4210f24490140604148410168205c0b82585c0d90910403032903030b154101e140140442c034428004100c140b8060380894140442c466441e00c00c0703074071090906c0c0d041c100603410000340c1188140f51444825002e64803d15100c000340340100320550103031a400400f500c5404001440c0c1c440d0b010b032607480000420750750305800f1035004000e00d075280301d030b000c0440c0301c0b5100b080b0503402c0300f50306855119806c04060100145448441602076021860840701c01c0ea4481d400308074240e03544918101c512040e003001c0300021218001800384c032400624113074a9420061014040701600b024101e4010407440085125540203514200040110303800d0b640000a0004000174006260040000c050080f0b40400940e00c840b0000c80340c080e83d0384015408910305240d10040d41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 823532544 1250 823531294 823531301
    0x20d090609031104020915030a060f1d09010e07080a0203060a02040315020901020a0807030c0b0c0c07090203040c031a0a110a050405060c01091b0306111912140103140f011e 76
    0x11800410042ca00f1865100040240700181d0703400d607c4003004030812020052904c100d03400782074421180da01340d6142c0f0009036500e01c50040c80c2c5901115a10101d8410781003500304040e105010820750325919106c2280c1c996501c0c02e44816880b80c8103450210b1801c0b8114800c0310305981d005299054119041a61080130b94030120002d8114810040179001182c1c442d8090301401e40729a0b14481225001e091903801c0c800d0140500444440c00c00003003009100010700181201c2d501c143c056283d60702c50801420080d41c0740c1c409007044024840d003224040d0800c0140c0d100342d800680800c40300f502506603890600403402c8a0b0003150041005001ca40b5103200507140411180300003248502140e0b0300c24204e12890710052007882c001450030303c01c000107030003811845400700750881d0400410003440184110000400c0e0103200001c002c6120121503500941c2034015050301500181d40d40303140c070781c05103c038400d40c0f10564040c401c1d0085130001c2c10300548051b40e01c01401e28841250521541004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 823533794 1250 823532544 823532573
    0x120e070b1c1a0907091212110607050412050c040f021306031802010e120136051908040b130518100e0a09200102070602060910020d2a020d09060903 65
    0x2c3c40305c1c60200040c010351000e6a410341511641030884000722418010b4107070340c5110600042c40c0c000da400c0081942c0d0260584048404070440d0554401c060701303007a810016034000130354115080265845d5040b4190300107101901c01c04500b40e1201d6034a1004604680218a00803611334511403040007542c0704881070888500000c001241c0b29a001c0c01d59403c4031110380c1c0b110030141e440610b0106640c1005124442c2c2e811100012061514540c1d8041d1105041521410035040c0814410203100c080001c3d600908844030780c0e55910145031132000c1028440d4481c852142e041000f0445d4070170007030903526024040410036404078501b00304600345040030041040b21802d69448050011900e007004541580140000c0002d550304a07000081c2020945d81000003994816418004107510004002c100060301c0b901c010380710b02c2c0c10f0700000d01030030703044494074907056001d407207032490200c00102c0d040030300b40315001c5500600000500b60b41c0e11203681703e0781e00415a0180700700041903141155541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 823535044 1250 823533794 823533797
    0x601240f120f02121504061d04140f07050a0b070809040b01050c010f0f061706040803041b06050306031507091241010b0f01120e070b1c1a0907 63
    0x203400c2c1003140c07441c040340c024140840071485541c040c0b00401c2c8082d04000355611081e00c00f80155828941c481003c49840b22603d16559803d1000030240084510f80c0b0350f640042e10251000051150045503444201c0d018241c403410041c1e00000303400c0810400c44a185500c001c4450805a07a403017040001c24040503028184002004203481c070707110a02c101c0c5552070b82d01c070002500b40250203d400031243e40b071b000303d000c00f00300144050512600081490740250720070f00c910f03038954071860900c504071340503280703480e101c0a80c030348c0482c4158000e005984214015012180b5024602442c4640140155a0600070a050700410300c090b0189001481e5124012503811585601c8010710048100c030400c0c0c0f207103c148a480320841c1c070145003000003103580c00705d038000d10064440c0d50000307405500c0072500606000095070901c502c048160403018030a00f21406440c0d44596403004400c1d03036886020246440a100e281c006d850350424805e2004d40c01c4045038611401500c0b1041c0b11020802400400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 823536294 1250 823535044 823535051
    0xf0f09070c06021b0f070602030919080106150201050f01242102071a0f130212010e062e0501050c03041a0406080a02120f0a06170601240f12 62
    0x11401a0000301004013070a1456002c542100c0c80c2a070812102c1c5000d4913082d00070003401c012841e800016100240000c13102040d0105104680d0a040040ca5010310415420300400140c10118240744105103480ca40081c80582d4801c802400380400900510301030700c1d99502d2481030a0741b01c1045104107a46400e00d00000312a00a01058607150821b66803110358000521004005c124030440c0912840107146181a00340340010040359000104803089540e10205a802550f95800301c02c40e654096800800603051001f1441d42c0711102180c005060201c032440c164145684800507025080061140103545402c0c900111441e82c024100d541e510301c004d00002c00c1d80e0a4011403201c00c401090107850b622407030145d006e0b040580050407107940768814000300050800c0180d24039800100c01c080c50300540c0d44d41c403070750b801025250490001700c1c2c108400510919000035005050341c0c2c1581d041c04014050381885020b078421100101c00140c004103403603044600a0600100c86980fa80020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 823537544 1250 823536294 823536317
    0x210a02030a050a03020c010c081c0b090a0b09010b04030201020303060411041e0603200307031d030f0705010506090412030e1f0c030c020f0a0f05030708031003110f0f0907 75
    0xd1800207101c50582d440c0d0031140c0f0b2a010950100044440c008003801c0441d00c0c0101503c0b070707030f050707010b16003080c071151400b00500c1185070320560002804090080042e041402c0c280b80c44001418203c44c0c09014070300500020603500070200c280c800b120b030305078019032469840ca0280009410303080041980e094007400040f501c3c4081c0d046c040d0170140b0500e41140154a8590010240c49100703204156214036013299202d019030a0080300d61001007130070702144170400c0c00c010301c80e640303a0780c044144103000202d590b0464094080040000c83d01900003404251201000c1111020781580c00800c001ca42404c4606160f00a030010340e50402440107440c0440354880c0040403604400380c00720800c3d030b42c0e080d02130500e607050b00c1f80c410156040c1c030081224807c1c2c1c9540e00ea0b9076040342000303402180000881c4082150400441c0c880c540c1c0f04035600d489081510401000c01424003080310702c0030a2840414042c00c0c98500308042c40002000c00342c03c02400030038080004409890f10f42040601c4185 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 823538794 1250 823537544 823537549
    0x6180721021804110619180812070c051918020705010c03090b0a1a0607050f0a080406021009021e030a0b04050d0f2c1f030209010f0c02210a02 63
    0xb0b8850b01d80d030801c0b01140b419113030091240055402480c4180e509000500d651010040c0d0010340e50f081d400d1146a8000c00080c6006000c140d034400310f010b11071131020455184041e009801000e00c07a800070074103c1d454004000580d1991004002824403400042020381001c00d41d5400f846858800145412411740301e40f403d4486030910117001c80e40b180190001c00c0300201080e035014075002410082e280742487c520000d0f03c0300401d054400d910204042040c0181400f1003200b0341509011902c1c000014034210701c2c581c100703200d40000340c001e040c1d0f00c4690b001c19001c2c07820031540c0248080364000901c1e100c08800390074401c000d5018450031070802c0000b10100381080c005d50050000305130030241001f00405e44002c050054003001240308040c0c0701a00c4c4021040301c80361a1a1003407620441070408078104003980d0442510b00c140c80701001980c0c5801d503004141e8000c081e84c0344115142d0203c1c044c1c2e440ba0040c0d900940022200210308140c1007005007001c901d0504d90140c50584105400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 823540044 1250 823538794 823538809
    0xd030b011e02061005030309090103060c0905030106170f0303070504090f0e060723070b040b091510081002040302010c0b04020102010f0603050f0f15150102030702130e0618072102 79
    0x1440780581e020300c00b4011080301d002c6001004040c201d00842c5484070320400301d01184011320004003070584403440f40002e0703405028800c2c090308028000b04207903559011138980d0658021641801070144618407690780f14003204581c07040f26a9200c451a04d480d0072000710040c8180503542d440c96544408460080ca03050003040d01a692a40e40d94038844040100c01304900942030fa0301e02043c001300400030000e860b410410358059003003201728600f941c80c03080d400c3c00c0000c08216080d000407000108890030307040440003402c1e60155000c5900318624821082c00300c0c415404080d02044045441038001a007085400780d201e4418070012447c40200300012065074881d80088031207401c14018440b03050010000440040e9242000b0680c81c401410f045500600251037003210940403c1e0450581c1d0080080314400395009e0524404145050038180040110900140301c901600000c2034985400b904860700072900c6c200903062191034801c210454440202c240f80002d84811000005a0b807400d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 823541294 1250 823540044 823540097
    0x7030b071214060a060918241e0e0f1f0801050c0703030b0a0605300c030108010c0206010f1e052106010611100e0109020909010b0f01020304080d030b01 67
    0x41d0b03451410050b00f045032034045a04450100200700e003003003100c2d0920b0000e080c40c03807001e1940001d071801c00c0c2d01d4141011034001000040781c0ca407202c002800070b02d43c01c2d41c5070752110b00040c00d80701d0303944070050246102001c3c1e030803c410900300703000305541581811340720905840301042c1018403541d0343ca6a509484003120002c002d05001300b60030083c5601401046d0315440c040390124071170760900344050010b009295006422581d001824801803150240318441d43c082c0c84010001807400b654480c4c1194000d01854800754280704d10490094000646641600e2448200200c03d03420004540b4100c184020710307641401c19420002115225a0350403d003a41d507200368a40c4044130352800d103107080010b070300c508100041d120150500b101c0c04101b001140d10340d11300200d6181c155901c03282c0540950607000c0d502101c810140142c40c00d0551010741001030654103412001c541d54010f90702c80c0194030549025411043c032400965101e64803084a6810504151030301c00314040c4c00c00c41022440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 823542544 1250 823541294 823541321
    0x3031a0307030b0604140c040603180828030b01080f06030109140f07060c050d0e0a090f05040c05060f030412090f0602060907230d020a0b16060f0e07030b0712 70
    0x1800b130000c60300381070261225446040b1503402090602200c2e1000034415881054209940c2d8802002c3c40b8030704403100f80e0300c11303004606c503529086c90b01c1d8045400c6003001400123040c00908009104a40607000d0f07650741c00c0050b191007095990b214a46190b04000515403070307155585110380000076407a420b6892604030004020040c41d240c00ca01c00d8a0b0a000b1b0304018140080404c1080020b90009500e0054440c68549800755105c41c001240ba06010b5400481c1a00d0803c8218401c1482a0744590310441c010544c1001040c2e61f403007030019900c034060302d0708815101000020041081030f2261300c8030224520340540c46d556500030a90403007800e504007600581045c42400060401080044007a000800031030700040e046803610349231411038054190048641c0d2180809541c0c0342d010b502e004058684c0310581e2500e800e50166001c140c81d80f0102e84d0a45098044075460101d4071a503a038030410303c00140311450650b144c0c404840001024030040000b8540880102d558a005081f202c1000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 823543794 1250 823542544 823542563
    0xc030709021c050c04090e0705130e07060807090b07021c0803160f0c2006041d010e06100c080f0d0e0c040c1b0507080313180c090303031a030703 64
    0x19000502c580e0880d602412100c0341040280700c803004000040341c003250100c1030001044004900c02600f0503101d540100e501221040307610315100713043e40025945010368020740c0d2800b900c82109840d41c90301070340e01c100046d60101060102c0d0038150700920250b40010001c150b0f0144040300c1c0300914117484422945084040144041c0e02d220302a80781503a0b400d4105007001e140e400000800030411b03010060900c401c40c14480004103084505141080406856660b03255182c600b140350300d610419401000311152000082c86222030818a40907000007084405107080c0444111a058503041080e90030000410501c1844200a00200901c2506000100e14240c41d071000b681440511844130b03004e5820055552002a800718010091071544040e4a801148a0034214a048ac080c3c102c49a54840064641020304030042000708a4400c4590120a28010a502c400340c0b20009005404690041c85c10b00001e8007d400030140b00101d1414610221000000079203071040d10350054400248 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 823545044 1250 823543794 823543807
    0x60b07030507050f2103281b030e101509050f0403110f06070f0504080303010803040f080a050c04180b0a0f0513030813050307140d020714030606120c03070902 70
    0x103000080c10103507861301401890070041c00d0090551051034601c002e08130f00000040c07480d90385007100200e02d64800d40c03840b16000540c1000006200d42c40851720100b42c820b12503241d003440f90080a01d14120b241c050403400e40004003a001812140d844080000c104641c0803480e144640702d0076209425441043c100e500301824007400c80c40f40496100380c1e6030080060b009228200140207070308014149040001c0820900c3c088a150240c1d4110040c5400000000a10400c001025206640f040400c15034210341c1c0704000c035519220040d000780325030015044058686060b902c010710817008940c2202d41202d055a078030391054411a010030146a90740000040748100344a01540b01d2403285402c900c4084546010b09510401044107286074050501a0f08103d4248283c030041980b1818954030000d0107003a5a032252040140c04005203d410f100140e20652806412100c20000d000b504550f11002c0500c652086030a101c6181881140440241303520100907810040440c05c10045e140c04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 823546294 1250 823545044 823545053
    0x213022704140c1611120c0405090a02031b221505150f03191b020d02070308120402030106080f031e04051008040615030c09050f01060807050d060b07030507 69
    0xc1007840501d094507000d0003004000d8005808460441156007480c5485454910b40030705c0321900225202e410141d4105143c90b094000291002952411602882156600c51030f10b981d60702c27680000ba61581c030134a01e220301e0390841c058801c03189001509085600101c0394508118240b0441c20328081070340c4140b0443d601c004490120007070541141d02003038042c40d90303100f003846d07004d0050f9041a404001001c070301440b03d06211030200701c02d0f40c6000c2c45000742c1400c214035100c84c9980c4940240c0034403516040750610115030b000980303a00c41d040d1f6041031103040a9403070140b0014003c0f0380540d070b1207034007080a040800580e07038002071100c000e554604902040990905044034407000066041c04280072969601003121542585481c100311550f6450070a1000b400c07607449803200c9043c1554012003071205100407007041e5290481c003485107865084200c085c00c50244507010002c0d07005804107089a02c203400401c00d60383c41100100b001500c0300703080c0c020350384500c0086000c2000080d9820400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 823547544 1250 823546294 823546301
    0x12030e0a0c030618170a03020d091101120b031033080c010c0f0803060a03080406090302041d07060e210705030c061309110c030a0c02040612030c0213022704 69
    0x4c01062144104e08400c69507000b0b0040594401202c40300713008102d42c60042c1c801c0d41603400c0404a2001031040f4083e509050201041c0b4003650760005a0340303002e60151100b28025801240006070041543c0b40c0000d0b0108004c04040041c4c40140c5020501c590754504084a080c0d4075405510105041c0d61410710403e20702041c2202543c18044030a1000c004500c0050103603004a8100c105140d8942d190400109110740c0c0b0740000f001050301007000305078180c0c0042c403081640e1090b1030411000d42c4e041e440d000700081a101e4106540c0c0008001c2c04917900c9070044201d5400e002e0030550180341080b95600c041202c0c0d031864051903008150811551400300849414114262061850080700b2030b4031100b002d505014182c03440351505c5101444421220403540e50342038641c10f03241c984000c800003c040145c081d0050f4030035030a100c0301160140410b08803a21103a8192031b1944c50781203a500740710954000070307201050ba5a013840071031042002180040c4c15200401c000b60501031950003000100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 823548794 1250 823547544 823547561
    0x614010806070906081602071a0304021005030c0315060d3201080d18120f02011103030c0a0305180f0a0b0c0901090501120608010c031a0301020a05030412030e0a0c0306 74
    0x10845140c508000d807a81100c5e60301e41240010001c0401440403290991a01c0644c1d40640b000244203a10200d501e03200d900598001c1b88210b40f4241d248815100480303c0d0700003a80e45008841c81003011400a444c0c0111044c6009405001141400100d550301011210b9482103459041204c034000380701d031003158044588082e104c0c04075401c594100a251580c840707140e43c42c4824460b02c1b41416000140e03c00c5000001c03d1b21042c0c11041c2d01d1180b40241c005405910124046071840ca4282e06407200801035031f1080e810400420f080078207480c41100079103c0a40f555054031444890440c01340c178240030f100c45c216016801421940407618126203154802056900003110a005402e000d80c0e01c9040e042c2218000d00c4e00c00407405803101504000c0200743c6c80151b1075841e100c813080358640c250304800038190754403807201e0103440e400003407500347e1040c0146000000e008200040c0028074842c01c22034080380314078000464500881c00d886c0f404080020644040f0b607001c404104114040c02814103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 823550044 1250 823548794 823548797
    0x90512120c010b0310111204030c020a14031606050d020a0c0b04030903031107030b0403050904150f0f090e03032d090102090a170606040507030b0a030602040504271707061401080607 80
    0x80002501c1c040c0320180100482d2001f078500d08404942030502c91611080d4081d0003c021400c61036541d24503940403841400014041d006202c030000307520564074252811603441d6112546000c0c04581e175030000b58480345041040c040e44c6c590030800300305024050f501c00e41c402d40350301100f2030660a010b821049032500125195024070005d000140407140000d400552604085890b140150300003030103000346004040a1850718100021080c00503441c24080315a0750b070a04480c0e5458084a009540024120303014540c41000494400305824860584102c0c24194040d00c0398802024503090240c16540311299a4001c500780900c0d141070f841d03007402040b003441040301021007440d0998079682c00405440c4030f02d94840000e00407501030f030800b80661900400300410f0340d03101c0c43c200000350402d002d02800340380790120180a4003182c3c007040140514003c3d20007195860b969800c510b0b484032801c0740d020418107111400000340c040c00b910019902c40f00b0880c2c00f40d814140a01c0c90100014007050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 823551294 1250 823550044 823550051
    0x708040810060506070f120e0621060d170c0106050d03030212060405160305060a0f1805090f0a140709060603050a0b0301111206120303011e120201090512120c010b0310 74
    0xc081c04400340340c0a911080f00007e4102c01c800984003100c0340542c0f560030500c005042001070481c403c1c2c420b9001020031031541030391125400e200c0c18001d1840020144584040441819520300e40544000b0400c20004075045031102d000c0b0b05140804601140801d80205000301d95210000344180d10075000e0f10100481c0c641080f0f42c05c105001d81c544d807414036660303030040381040c0c98450313001d805810b00c082000c940300d0f03031250360f04c0d0b0007011550700c10070360303498200480d2200300c01207000c0003100340040042503c0200350b2150300c1860038480300c202d2903100b10200000d102e4400d0140f01c1c001e1095440010391441c1c148035000a0724a481d03e414031a902d02494000b6682d00c1100f030b60b0b01131107986440030f00c59840102041c40289461505c1c0c00390300c03010000040d0517008500c2031300c039101c00a5950103060364810400d4102c450200b0002e000c05c652480504c0702d4209100d214201d05000c2c0110b40d2224510255610303d43d05c00e4080401d140d4496081e0150360400704030003000d10304007070000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 823552544 1250 823551294 823551307
    0x603160f290406051c051e0a1b0819061203030b030c0306150604030b18071409131109041101030c02032a12031003030306050d030918020708040810060506 68
    0x800042c41980160b1007031010105d0f00c0a0b03040743c00302001c2d816504102080040d03003040d254285107001c0c03103822406580321034400070744540c00900500c501c210707150031001c0038a41000c0d0140d51100c0000e180001c00300a041000400010501038030004000281d072074680e00145042c01420740d4a003131003807030103540400e080e903005441c001149640b00c104220a1420340c113004001881d01d11480d4000360194400318184400101a00c0c1a0750101c14400103c0780301550321201d203001c01240010040c0d210181030006110b8ad520080141f000d60310032881084110034150008058402c10b07201030301d03007400c401403e0f42c007540c051044418078481800158141102c0700b103400682d1036560509003490005a01110511030100312103000303641c4580f005616894100c0040303000040346d01c001d070006810040002a241003900054416a40655031103d070f80b0305200101925040d0f40c0340720740402e40d0800850000c240c0c1440500b003d003d440c0041c041ca20b019412007000d81e600741d00541d20400080182c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 823553794 1250 823552544 823552619
    0x250201140319020a0c050106091d06041101080a06051905040c02030c19030c12030b040b01030614010c050c12010207051204051e03030d060e062b06050603160f 70
    0x30b00011503280780050303a9283d01850499641c3c4021100a1040d03007060000314041460390420314034400e0101641800000c0280d01d15520001602d001d041c1d0110b1085400840d445003c015130f0103074011201103103140d40d84000c0741100320360315152040c07241d0409084c00b0515042c05040b41c00c0c0303501d200842c204204400503d448451807103c41c1c06079003811010404250040c5540120150400340420800500b006c02030050014610802d1003185044401c000d150302921a81058075140d09245140f1041c1c000150740340c03442403400381c0e040e1040c010070942030f58072444e0b100e44a50000c4000360711025945061442c1180d0f02080f41d060640612091103551203490385d20b40c60303d8104005030341e966058030210341188500c01c6244a070905140d80481c011001070003141c0944401c0d0b4401e00c0300000c41361213041c00490900490305031200450f14101245554002c540c00010050640300300b801054650030440f100e0f903202c0d000c640001b420400244881c1c0340d158000407030a101c50149800307014507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 823555044 1250 823553794 823553821
    0x1a0a080336010516060c08150a060f0c0c0806130209010509041205070c210b070f05031605090d030f090b030f0406050a0207051204080705040915112502011403 70
    0x1a098100600401c442e504c2c06220030181c1d03a96a080681000a0002d00000514204084604070002e2840c03a00b000072a00b00324120b20112030050341d0300c8055080b200b10860b80c61031100c03005e407109211001c01050700c0400b400060f004d00c0c80246c104085417030070320501c2000d01b416444203202e819108200401b0071203500c22440407649034a0308035074030301e02c0d0301d0101040b1541d9042500045600c0c103031004c03642109040201050b0041d1138000d49607039007400456400b0111010440004c0040c408a408540c10a0703800710890010b0070441c0c1440507480100e01c0089002e44241c00258036003003c284001d0304403540034003412204442364518a800c5619074012140500b00070000340e40ca40c0016903030049641543e041592000c291a0381c144440d500300815081340c0210181c0340600000090246880d200700c0e0204c0c1d81c04084012800745101d8140e0003440710042e000c0c0740d07030801c1204100c3c6251f050090311202d00c51f201808940c020303a00005298200540001c8a40c0d0000c009028400d00d0250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 823556294 1250 823555044 823555147
    0xc0405181014120604030207180e1c05040902131a0307170703060e07080a0606020c0d120c02061c1109090f09070909031d030304030b0a1a0a0803 64
    0xb00c54400180c580491a0b04400142c162814003604003030004259000c2101d804860001c6180c52554002e100000d04840303502500f03040d0350b4800e0400c04c01160b454a000d0541000741d0410070304060f035405003101a60303c03c03075010b540c0d6038410400b800343c007000c1e0291b1154641c0000000e4114a400040504106040781b10460045420b10004810382c1c440e40094000d0600404184000d0600082c050702910301607400302803081c20100d022550510004d402154508014200080a545502c2e06c000c5d540c81d110650b403c100b90841c01e0b00260f124800180f400c04002c1c5c14080c0b99004000c41c00742101c00802048196400c200a084840d0390386102041c0c000b101011000f071203840d0b89104a02d03040c400e5120500643c00c0c403444000f8035400128514002c038445036058600082c1c1c100b0580c59119900000b001f000788903020582224280d4403445009030034101d6110484445c0c2c0020ba00b0405560101c529a880096a0314003100c54510969458105500319902964580c1003500f4040c0d40c2d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 823557544 1250 823556294 823556309
    0x120703020d0c061506020d030e0639071217010323010b1306030b0c03011203050f0408070b03150a030213181b050a0f080d0806060c060c04051810 64
    0x10510070a02c070444d44010000c40011400503d500e644410194489084802c50400f091800400041e540d4001c11158800c00b00c0c490459500c2d0102c01501c91079001c140c420303802246e420034114180c132140d00c0013803800d20b0141402c022020100203008100c000c0c030101c0d1010300803c103001080003407080f411007074109002c0d0143e60301c0c0c010305002a81c0180440d2100c954842d0101c04003002a1029602c40c1e020b0764002e0344480300b55a030340c0046a001e44420302c540581e8921103048200828450005480d80e01050702a651405585030701e40c41c9040c6d01c5801c840c120b02400030078405220302441c101d011098040e2000c07461a451a00090b02000e03920004042c1541c8078644d222140c81c45400145105500809445002c80e800b00c0d000c40c004194041e06004106221000c601c26009201c000110b0380488004d18907007800480c21184c0b244054270083d04014144890405c1e560144943d5114203c00c1c4035003622a40351600b0400055515481103520074551001e1004d090080391a44d01958102c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 823558794 1250 823557544 823557557
    0x1305041427060a020a0c05011103061516060b190617070305040201090608070e13050603012315060408100b010816080f060a1701052401080f060301020c01020d060503120703020d 78
    0x2645e4050321030f8444214020081d500e00325610001d0340b030041c042e42c01101c050700d8841c580c2e03241185c00f011922444410b0195054290084800241c0f1504003035688a070107404a900079842541d0810303074042542002c00441e0107007000d0314918081241c2c955101d00c0c1c03403800788640e0030241c00103408c150716030088408102d188000140360a0151307041842c00300024100c1190b0f41c0c1100c0c10704008010a40b20680f082d402c1c10000c81d4410085400441030840e02200301c40c031a102c10080000600d40e0720441c98202009100014608905000400031800c1001000c105a000d02000420b800c00007411360f4241c0010310000c00016034044141f81c0e02c1401c03c64110001d0f12074030009820012a82d01680c0003102c4d803504202008019086940a2100c041c500100040580d41c4607144003280c10000d070005000000080e608154220451f1700850f014000501e4200d108041a00f1384e403007070140d2400c0c60740f0b1301005c1205003010020b907e04071803280380840c246003507076030000d4491444603544802c0205 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 823560044 1250 823558794 823558807
    0x1f060509041b080313421b0803060a0f08030706050603010b120319080c0a1b051e120307090e040c0506040303200f070b1305041427060a02 61
    0x1030b0001940240040000702d07078981c950100100d030074080c180500780c081040751130700300000000c11750b20042d04000c10080c26803610424040e48820400c03440804100680c410000407a800c24505841c01d190141c480103540c2c0c540142400352203442d0740d20106a07005e128004000c8420702200f030725042c50380311101007125181d80000030b001d400461201944034044041421441000000400030005018040c041c80ca081e014141e6105108032440034402d2402c021075030307100b40304c5d07494103501d1211040b0f076041200c4a901c410b450034801d440c00e40107195144a0103141c1d400c0412450342800c4a001c0a145075151000000b400e41a2911030351150245e84000715042054213050301c00a4400501100e858550341d040007405c0900c0c40e0030115520148440e824141c00740401c883c042c030440c1000900f5035601e800e08101d02036220303a0302e64460300180100800c4035600e42c043e846503590360b46040351003420101003042240c00b400003900e84102c0201c980302140200420683d0703000b601500010385425 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 823561151 1107 823560044 823560083
    0x1110f070f060f031104050103091a0a02040501090b091f200d2606090a0908070f0611070f03140705101b050708090f030102040b0a021f06050904 64
    0x11714200010301c03841d402908104141c40c801d18100c055106444c2002040100a0f03810b4400702d50009001c008940c1c0c4001c2c00001b4219410480f03103030080d0f4400203081c00b042081d0103d680b03600031420002c3c45001c0d00209240031074072030b4101d00030940320301c1c403070707180c040b40c100340030105403e0410192039107000d200744509804031425181c29922107200b0000024401080b2410494482d440c140004240708040c00e0420f118480f007008280007490460700795402625444107190050140e0008a00c1c413140c1d5002003501424000d000c1d2101c0f40c5c1e081c1191103480c3c00a803162003159440c00c560281035014404290354a5456071022001e080d045440b0701c26881c01414565003480303506640c0c42d047c051040b031f00e10010001843e080d0b5646041120b40c000f44140700c0513800c1130003201d000598090943d01c001100c07410801c0041c0c1090000703061560080d002600c11805012841c2002 = true := by decide +kernel

theorem cover : BRFrame.Cov 823381294 823561151 := by
  have h0 := BRFrame.cov_init 823381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 823381294 ≤ n) (h2 : n < 823561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
