-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1338
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:27:24.968679+00:00
-- url     : https://prove2.me/submissions/81c94764-1c18-4745-baf6-816a1b797466

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 240467625 ≤ n < 240647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 240468875 1250 240467625 240467659
    0x8040203060604051909140604051c020d0905120c0d05030301050a0501020115030b060a030b0708071b21090b0c0705150315010c020a150906140c15130807080306 71
    0x1405005401c003c44605072245c042d140807000d00400001519906140b240d480c603204c1e418030501d445103102d403010380300140140144540385640017891070115405020910301e01c2d41c202c0c541506a942c00c071550f8a0b24213014420300d241a4100b11400d4005042c184018200700d0000301440c1030741d008a840006594407240124200c805020301d5a41c08200604100f0124400540440c0c0145000d805118055180d4031903078400d641c19035040b07001840c050208041c25a20540c0c400610700f01c203003200b5001c4001d8842070130060005110302a020000c03090302501074000c050203c02412209040c0d919654041c041c1c1d500c80c0141d03c0368038006d440314182024050402c0045a2180041c540310300d22020000f001101c907610408000c0740c000c0312113003001c144841c1000203040f002c40141e440300c59903410010020040d10100800c03044151051000180184000c00d4903407901c400c008104d0b070704c0c2e521181e8000c0e00e4801b211014248200000b90081400b5035580158807a41003591501100910280 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 240470125 1250 240468875 240468881
    0x20c1005090a0209041401090209040f030207051518011803140c190303051813051803030702030d090503210106030e06010302150901020109060501080c15040e07121b08040203060604 80
    0x1c0d1310524507800200001d0003200d40340301c1454807000006000d582c55001c209a04400c0c1c400360760341d041c155104010554104480e80180005444a10b03480c1140d91a48850f40900b44407010304da100d100e42e454407030344242021046014418030407400c0a540342055414180c0c0300b80950014010008104001c0c2001940c80131812070b204040f440039880c0d0745040b40d058001402c0807009244200034100159a419070040b1301c9044043d00003a00c0c20a03544420310710400b4802d51074550814030401030459000b109484d1000f10329580802c55040f98503004d415481000140c000b684651030412004a258030b01d114160785060b201000a900400340341907a0f00070903c00294081a52048020501140701c0a0407840b081800045401c1a440d40c0301001d44da0300360418886d5501c60719003136819240c8401c80c403520707040c0d20140c035140c9410000d046280c00c1c4014000418041051403000301c500c8194000180c44911941c403a80140910400a041d480c081d1010b9100c2e00c9200c02240c45898188 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 240471375 1250 240470125 240470143
    0x803040602030f0d061212030b030a0308220f03030b1201090206041a070b0c0913020316300603020a0b03090604061109090901091406040b13060f020c100509 69
    0x60000d50610b1801d411040340d951144c02c5000c14030381c0324080020040380c00d0039000140c6105084110001e145080010111060804644e109600c14500880802d8020800d9a001030b003613030117440b01c0b11114984102d0f0020390040208002c20103e4240141035140d40015602502202c0621506500c51071170350984444036000317540b1510412041110240751040d81c21001100c809042c244020740d2147c03402c1040443d0700d0084501c0000d2040800d2502c0a00381c480c07880762040440c1941082c4030004217000041c04800d0074007420b210420954850b11346980842030140e030303800c2c0c2e0710164400544041c0810344012800b4240003940822410803200c1524807070f80300b0303074018a0300e03039900c1e01c500c1302038074401740883e10040c01009045e00301d40743d500c004c910031440c1c44004a0920020724086515455521001c64942c000c0b1042c44002100c0710715640d00081610700c0d0382c0900d400b6041540003068100700c1110b06c3c505c002019000c65070049149061248840070801c6180c1e217081000762225010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 240472625 1250 240471375 240471377
    0xc07030209100612200d060510110606040207020105070c1202130204061706150a321819030308040b0f1003080f0c03030f01090c2607030b031002040e0108030406 71
    0x10074540c0804219403084a43c01003952100f00d11170b0701c0c0d118800b000c0d07001c005000341080d242e03c018803450034000e4000b40c0402043c0381803894000080a0340f512113001501c0306100e1600000c0c6402560f01c220f00341c0312929001a10400300c0d9540d90b810a00e641d901280480c0994030a20314071500000500c2075a0403611183c42d1041c56144074904212480c2c0300030195540841001d080d911000c0d80f24000c6d0070100c400380c442c03a00e03910100c103c2d00e0454040c1441e600460301c0743d0b10012a0000c01300c09440c1d48024075450086254802e000244c5803c5120000011280d095803000007419480030b5030601540c0a440c2400aa403214003015546140c00c840700d210020a4003000c000181d810350040164030380c040031a90600c4003040c049402c503882591b03102d0b01c0d900824010321500b070700c902c0303648140c8401d07080c5148117050030365004c090b14005912921442d40003400042005000740c01500f005c5c42c00034150b83c180c2695040200c0203403c54040c44030210040000031403103d00010442c0c00740d800d9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 240473875 1250 240472625 240472637
    0x803030103110d110d0c0801020a170606040f0b0d020c010507120e070f0b091203030a06230f0d020409060f1a0406120f031101051501140304170a140c070302091006 72
    0x811040c8107221700d10f900212485030748054006100789080c406003252501e5956607115619044030811001c0b0405060140720b60410803040281811621100003200d002d070072950340702c030060564070000b4003c000b12000e055091504000300c440e445032101d1000c110310002081001c000300001d0303544240d1070003046100c0000080c14801044241c019008880340100400840d205141046003180c00640307802600d039480b0082071203c4820341d184840b81040c4040031030100202c800c000b90302985690b10040c0518602c114a5041d91959040700d1031840e00480c0a000700c150600c4504002c09009001c01c2c0400f120305450f80b260324290042c1d804550750411046e0139819543c550000d2041c0500040b400c4c4003a04c1d0341303c00c12030300070702616104002000c1610740141c0510b00141c50404543c208d14941c2c502081048001002282d252a14901c3c0c1d01c400ca80b10039500318203a0b09003c200511000c1d4100100d400075200c038000446005aa200b620003034a46d4855040c464040100c0b1f0003404042a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 240475125 1250 240473875 240473903
    0x11040609021809090316050c09180c0616120f1d090402100c0b0405160605121f0b0f1b0619090314210f060d02040906090209010803030103110d 63
    0x1030300f105100e4104580f10156031521042900d030369400e515601084409402207581d152003490409001ca51200c115100f103c103c0180e03d640c10b850b1040022880d1041901192034074541043c00d210080235684013154815a480003000940300111196a60000406504041914080c140c04039030109001410a4115071110303070800c007503202e034070b9808400c03c4413500c00382c000f0505440c14680128081c1001d0129592080d0003211130f0072042e0000000d00c4801c019403991104015802648100c0d160802c40c2e400d200f400303010246c2203150b80315030007248010541000b810641401889d000a05a072070000c0c0142c2260090780b11038040707034408560003522043c80c1140f0741c5600620445c034402d01c0e0600910807541d1001195030818050420340c124425440ea003142c0541c504c407504100707094400009858a03000140c4503191800009001d01d0f01d41504504001c581d030800100075600401410700d540c0c49030305696032030700244815154010140020049400e0540880700c410f03030810502002c0d85 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 240476375 1250 240475125 240475129
    0x50c0d080402040b0916030e010203131b0807060908070806010303080c0c03040f0b12061503010603020d021603032403030504030b060607150b0a0501090506041a07050109110406090218 81
    0x928000c0082c2d80203501d64080f03409964074542030500c141c2c003109130780f4440c0c021000020100c1e05c010429907026807041040c40008108040d03000300e0540c0c1b152100c1200d419941c00042c02d050a68231021041c4500800401e01d990000020b505a601d0f0710f00312109203688041c40c5958a10a200140200d9030072000b081c0c214807154001e14101682d0b80807240f42c1580c4440c3d140c034900382544030404601011602040200c0c4140071107400400807210109103039100083c0488034403043c82158141a400103d03103940700404e4050320700708010440f0350b045204c9107082c0034014000c50f103e491403182c90001542851190042c03941c0c2501d8140d81e0300d40c2000e0840c0e81d8224500c50140c2041c0c0e0240381800024001107603008000d119070604040800e10451260030b0055214644c4c2280381840a000f0301440300e6102d1400f42d40884102150101c0703000307030404184615214030070000c1e11b25400d122341c1c0c1d01440446a80d20b030140c01c0030342d0208030182d43c0d4554041240a219500340c480507810101c0c0d142c80c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 240477625 1250 240476375 240476387
    0x11a1008190209120d0c03110604050d0e010306030b04080c0706021207120507020613090b1005030c030601031e0c140306010e010c030207120f02130902030709090c091409010606050c0d 81
    0x2c0d80024001100460510480c80d02c0d0000c4140c02000003000c1b001c1c08404c066002c0a505c1c4030582c0f8400520103410140e85440e180c00e6801040003c0001403020703c001c50f07100f0740103000110b4200701210b074175040030b00b05145190310107d0221b5980c07041580029501d07100184540e21a1741074043c00307061000e03d0341c0e42000b01258024103001c0042c20321070500940d40315030042c80c103280a0340ca442800d0740340041c2c641c255014808030340d00c2205018944400950098101c0c3c0d8403410500c6000d41c1c90365800010b800078000c038000d901e80c920700d205503c44008920752060070140c0742c03501d807a1380c41051000c4080d900c0c80100c4607140040e00721150b54240354016400101581d2080c0195040c854648100c009003641422090398142240000d440550520002201003100c06038000e010301d55140d00403d544441d2440741c1d160f800ea56403201c50a1108101e00d01c03000d04501d4000303100b0242c0002080300c5901c416a00c2c00425440c20000140702c3d80240111014200356101810140da00136009984d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 240478875 1250 240477625 240477637
    0x201080708040f0c080f0715090e04083015060a0807021c02030702040e060c12070c02040c030f0e060127020904060e040b07110307140f011a10081902 66
    0x43c50100420040010740304103007200541401e200919154009080300d600d400e2003507001240c1d151120f100001c14541c803c1006069a194151119040c1c841d4075000c5000e03c0380c1543c0300e41c000401c1d0111000c000c448010945201c1c8827101001c2071391140544250a0300300101190362000c010001c400b41c25000c1d615155000340c20380159199644110902c50041006268080060b003001911008500d41845005000c0304400d0080416141003460103d8903c94060540014054040040c014900c10003c20200b154054000e1046003518000540580200c1303c442c02500c5c2403100b0041c0380d980002d2031030f04075004050406840c46080082904007800c103407070b4818003030f000c000c100403c0e01c4900548000702252603100842e441c05080c41011f000d40038007407a042000a0041008951000050b01c005a80108408800c00400100c82c3e1070304501d035030400155403c06412207007040d801c454a50003d2010384981c0e020840f00c0200b00d0f0780f00c03c100c40c0d01c5646c0d9402c14499018010550103818 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 240480125 1250 240478875 240478883
    0x901020c07121e030806120303100b0c0313060503040c053106050d0503030901060f0602032704180201140f1b0a14010b01021902100305060105040906060203031e04020108070804 78
    0x10b514160841d41c0c50f5406054034040e00829419024040c1c10b051400c144075070328208001031401d6040460a841800420b441130040c010300101d05c00a500d00140103c2d800651182920120181d4454010300190002c40d41a905100c501b28001894100080e40a411341980c008a0000c0031070f0b86045d0b840104041c06030800e080d80d503640400c03180c4501c40ba50840c14001e4004503281d29150648030300b07680765038021602f080080441048055000802d0f6241d03e1810785081001c1003204020f1101100031880a643c8103003030060000d02081140d1000e00d00d81c5c006e9803820005040300140b10710364402c070301c1c0e0144003440070450741c00031015141480441d00380b82001c4c2d4008a1043d1a015038070700301d2030005540c036551400710105079030301000b40d52282d403030010111015414a40014040c80b00020549061688620000718980c3c801c200b102c01400343e2035020070810381c640400a55a400403a0303051400c19a0302d5421b0703807080141c040d40388296416511000c0c0c03590b030a0300880d90600042c0c1704032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 240481375 1250 240480125 240480143
    0x904050903040f0e04061d030a120209060f070611090105070219090c0810140d06150f060e130b0603010b16080d050910090b010504021b1902090901020c0712 69
    0xf0601c201035a1031680240a0455003046604290400a048030340729055050160103026844100d0301011042d201503a20301d08141040d800100c8410f40a48034840703849030300220000d00440d44101b480040c100e1b0728003813041002002c2c4141d442c280d05204503000207003c18018054140145010801c41c0f4000f035645510351600daa85805400c1034039105810070000c6180e16003080428803510034503400801000507108024183c03040400e4105000d00e01c054005c60716403c04aa1035110101250b0003091a42d9030107000954801c2e0007071815002e1000c0302e11400040d040024010918019900411b03401402c907071869103420200b501d164084005d4440f0900e84144260100c2c584801804c4c0c03107190000081440c1c03412241c1a420b1100e842400c000061400102c02d003c18004001d046c150360341503600581d501420704400b1500300741904108042d10411070281011000d58005400c054401e488104650715026003030f50903800b8100220f801d643c004a41003060031542c06007024007900038840700c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 240482625 1250 240481375 240481379
    0x304090e010906050a050105090f060904030804032102040f1703040611070b0c03030a05091903110c0a0803130815130204020f0304050c130b1f14120106120c05090405090304 76
    0x3a0068810854017802c007182d940c0c004010320700b0507044250b4003022520821301d41c0d00c1e018000a180c004050b10180400c41060700090400d4003c100c2801300300e1010a020342240c038022240b40295009014251000a507900e0009480c10f41881c4003204c800c00c400030b1030900f030402604403a8000c080910414500c6400000520014480014a036090803240074564a103048002d040548902502d100180c0d8841090740201d07444a10301c031840a58540703400744141c01f00740700c034529040840c01c0c1d9550202036002e00090007030000000741100103001d994116000d644d1020035803600d40031f003e10005000481c0c00207208110402c4040307030b403c0c8018401030800300b40b4100702200da0000c58040b2001d038880c2c60748003081c1c07a002c02071a04602103080300740000b0006c0c0000c140414103a4034916030108a011111113414002c4600c0300001d9065501c2d6500ca4001c4041144102400c0c030649001c5241022640c01c5154540035411403030005407295440c1101034010b02c0010310300180707031010600080c440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 240483875 1250 240482625 240482633
    0x2101230408181e0a150c0f140111040306050c0307080708062202030403022b031a030d0c0b010b04060f1d030709021806190813060c050a020f0c030304090e0109 70
    0x4900c059031071140c0100701503c0301e09100541034150014842d20f40d80562040030240e0041c4043d6001d03500190941011507140b910785168115a44054070650905421215400000003d44101d0b4003810040c05280c41d00700310b0000910044e20580f0000e10304000040829004403200d0360001e0002c0c10f4a050713a04003043d4030b0710540c0320060003002c3c10b40010511040c03580c108001c080c072407100000b40c0c00c015000c0482410b4101886521010b15449280400440d40c2d010150f038401e0501400ba203000301c4400c04000d084514500040704c1d100618800450307a100390100b42e43c240c48aa86400e84000f412000035103504a401b0000c0d00b04150300400c030b40c0c950302c090000b44c00402c01024050380317403059104044074280c2c21620440c0503c0c010302c0000a90301c0781905130b14864449080200c1151038180c8003144620300b00c00003078005d030304000051944580c84401046000681d6080d180e1122003400702c1500c0f1101d94035526410382c030500040c80650b200f41d00c038080d0300c00c0081c00003411181d00e542e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 240485125 1250 240483875 240483889
    0x2503020d030818070605090d02030a06050a050708010902030402030337050a030e0f07030b040201050705010903170a0902090106050306040f0f09030e0a120609020d02210123040818 79
    0x1040700025800000d2000b245a01910381e100c02d10360350042d200702e82c2000380042c0140602c00003144100c40312128242951803d02903150746a420140500c250718001848030058541602d1000001d4015400002d003480d16100341d0f4011540240076514200e07112844101d2034020507080546480c090907080740745016107401001615050312441e8490703208903030180c1250b804106505160b040007100c2c4003405008a4024152544203600c020192958001241d642c0030b00b01d4000c01940c6084000700c00c0c550002c842c0341d15400e0034030140d0303419030b107400311803044c0d518030072000707402c42c55260040c411540520080c40d0301c40000740c400200040c40038019400d0328218a071514806956407a92424140d01c0508a1840881a28892841454250a0000c0e010040b0000d09229603501940c411580c5400345d1843d205d4004141c040c4151007080300d045900181d07411a001e541c6841c3c0041401e0086403042c103441c11032031242c00710035543c50300c0d908860380c00900d0511202541111300006569054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 240486375 1250 240485125 240485149
    0xb0d02090910080606010c02150d060315020909070e0907030902040222050a05040504030f08070306033e010903021c0501050403080405060a020366030108250302 71
    0x340720802c54515100c940381c141203018181c241080300b00c00c3c11001580708c94484041c1c88440c100134541d42d0b040900d90031b004100c55040140940072001020004100070f4010b00642c030004c440222081c0c84000080ea032410784e0442044c2c104d6404000242014020791000703d11500140000d441c00032814005240d20300c0b00350048500e640700c814148041c1c1800000c11019000c191010401c90800c2c1d02d0107449820001008003c200e0480c1c00544640d109811045c0116807002c103050404080001c14058600b02088a03450101005000543c4200000d1442420201038450740e6600d0b080d5001e10180109218904c20f0742c01000c0130380d10014400340704039032003140a0b544011950070945000740c282200a808484c460703006002740b2000c041e0300c030580328200d1400c01e28200031402280c500c0300d04442100c20590b41d5508003002d41c58030b5036604182c1903024502e21440754034114865951003540030078050131940e980708000302c1c0c103aa980052200c0390307003101a05c600c442551741ea00162040d00c201d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 240487625 1250 240486375 240486391
    0xc17041109010f06031a2808120306010e0a060f03090804180203060306070503280f050106112505040207020a0b0a0f030c030c02101109030109060209010e0a030b010b0d020909 77
    0x7807001044015814411b8480c4d40e400c01d5151416034107440c00140003c48507210800b240940e12910b00800c1e4210b19480008000120507540c98003281d091026981d08100c403814007180c00185041c4441ca09070300c0d804160790541c0c4840d1162030241404a00805901c18201c41103401007002080b2198a4001000c528441d124007581d07920b06035090600340300c4040d0800050100900a006030382150520760b80160602c1e104a00004800c800801c0141454050390a015407404001246a0758005080c40c50700d004003003101e002c40c1240300f008221000c1351502d1a81c1c881c440d041402946410b4000f07084550005041c081c40b9a1514442d261641c4924281c8001c80c110307064482c5807540500034048080e059080030441030310420006900c03154024104501a5944c0b4000700804c01c100003660100d000250007048042389a1400e82c009500280004d404641e0340c004013580c600e0100c0410040c0d99109999540b41c1e440c020b0350307a42640100e1340381e0303c129409000e00c1c842901c0ba182c1007840740c010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 240488875 1250 240487625 240487649
    0x60e01020901180b0f03041509030e0a06090305030306060901030b1203030601180503100c0201150b21060d2607060504060506030f0a020d0c0b04030c03050c03010c1704110901 77
    0x44000090807070046200e903100b00f00d8451004128030000c20b001d07074031540c80030300419649565a01d4425860315050304526044da140c116200c06159200d0b01540311800142c40714039015031a5841a10202e41c1840010141d13841040010102d0034410f000e031000000604001c035041c0b440c40c00065842f106c0007110071086c0d1020041041d40c0da4130080c0f0400c3c41105400e519891410074012a40300d242d0301010901e42911101d006111038401d50000300317800c54800a0044144c0c0300e110504160307000403049207a404030728051000d440e903a074091078000d40d4028403141e51b0050b80e03940d81038001c2503000540090016841c007800e0001c00000140051403041e81d000525280925050b4216400070304dc05000c0d5020f90921140c1e24800103006e0381c0d01c0d0b0116600c924607001898040441a2540c00c22100d130036000c02e00004214451801c0c1d410b0324480c0701a1a6501c03041e03418103080740c1105000300002000d00c41c0a02013405001e00309038006004941c1002d051400f2404034504d0402a403054868980c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 240490125 1250 240488875 240488887
    0xc080c0105181009030c020603060f0907020a060b040c0905010f1404060302040315110405040f02070606030f050d0e151803010903091a121501021009060b01030b0906010c08030a0603060e0102 84
    0x609101d0001d94000f102020414451541c8008007180440e6500030b0280500002240007903403488840c0540c030000606505040c5071018009407602c490213001c0341c0d06818442c10840038502801090448041640c5084200e0700d0b000c0116551103210900c0800d201c040d00024101048480c010009040607481c05603640d461803822060304004013480413219460102c060000e07400729400c9404680040303901054400c080c3c02601c000b8442c141c802031820307140150000401c1503100ca100f44460240041c1c3d0040000742000f60350b000c01c14202c55520401440b40380040710207400c040c11005018100e40380000000e40042403c5410b0340c82c2c10ba01041e510a800c019881002c04412809208006c2003403c08019001803d14510003030659104940c0ca64080308460740308101126008029900a003d00000c41c1003980c020070f0300b000c131079001900702b00701c075411402c055410b94041c03081a52017075100503080d21501e8160300040c0200800315141c840c00400b184140c0100720368910048001a9a06 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 240491375 1250 240490125 240490171
    0x10f030b180d260f0609091908030c160f0c06050a0509060d0e03040f0e060a0503100507140d0f05060306060a030b0703060b070b07092102010c080c0105 67
    0x120009250724040d111140810110607804035482c02c507545035081443c00300c2d90ba40450351000340750121408001c0207401c100484032504c940d60318050364040e260310f42640c07110000c0548030f50286282c4440c03400c503800000005501c01c0001c44d4860a01c28059050030840d48000a41d51610102130f00e40e1100025140b052024860040c001070869050861506c0107418000d40303907000b40c100b5280700d00e1010880151400098000102581291040d203503a286c907548001030000c00d0713008243c2d9078400c510000703019040681071001916401001400a16011303800c0d1006408000c0020040002000c3c0d2074091090b00c0000d0103005034840004502c0e6094064000e0032504000c00f6544207500440070700c030181e1111840e400c103880d046900303442d0a07694020260701a0078142d21203110038030002205020300c4802000c5a010703a1103659910301c000e40d200c10030109000002e1200c050203100c003010000660103140b000308698403131800c50303051015074142242191003c403180312501e161380c485149a5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 240492625 1250 240491375 240491393
    0x102060601020303100513020409020f0d061203200a050304120201020114011208031f031a1302090105060d0e0607170106080705070308060f041d0d050301030215030601050c0303010f03 81
    0x30080a100a50a44c41c00580c41010f02e80c1c0b0341305550041c003840300d108820704400e404840107003001d03000c1955030344006250010554011819110701c940f40103000b0031b601c4000351b841c070750998060b42e0350b05c0d0b0b00b408414084071081700c101e4203040034440d043d4010001a410f1023744002c004a080c1045000603900000e42943c003050101854210b20400521044055288000d152500440d12646941d11322420300740410040e0610680d040505400100b000005001e00e0690740700e0084080d82526038104400354210201e40084d40030b2030362401400396003800d4014010030900071b00c003c00d85400b0110340310305101007500e1840003d04a0f0601610461000c01054010269440c0c0240c451411450050050050587c005c041003032107004610a03940712402464034030f100504c100000c400c16500c958680140091180007801036000282195002d0310580741200e40182c0103484281682002c074800740e0000b41020706110050121500e070f02c20401c0518064000d1001d0300641e50708600b041400c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 240493875 1250 240492625 240492631
    0x9060c080619080303070c02012304031205031b0c070306050129040b070816081303140a0804050d0302010618020c010b0913140c10020102032203050307080a090c0b09010206 76
    0x2e080c10400d041111820000c100ca50200d20703131170210030b82a040d00c01214001c00c008044161a0340170b4000d0308030303481e43d00700030300441e0701c01c00e4092000c0c003602400b540d07a4007084030a123a0203c0f240303280d06518900d40c80100240300100051310911034031780c0c1d50407044600a8101104040350148200740c40c08010356500c050383c1d00c1103916810140380846065407442a004c00604009000c14464450b0524242118140380c0c005c0e112629268020342040c0d856440c2e21003603600c00c4c00d038480f100c8501d40205d0000400c5400100a510305030521080c40691b400300c010440c2199a903c1000840c5025054402000021080f001d0b99402200803282e007500d0b44922000e2003125040c040c0001d0300e10341400010125405151141d0104000c031646003040d4541d82070a070010540c601c0302d80e149a042d802507200d20300002c0441e600400c400c0c1b04188000b80c0c002c00a0200c1d6040000c1510107014008040c2c0c81380754900e0220b100001542c0b00c00f9040016400400c00540209098031107603014004158 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 240495125 1250 240493875 240493909
    0xf0203010509040602090301020403080d0c0207050f060706051017070e07020102120103020d030e06031509090604050a08030a0e07030b04110915010e030c06030915160807080a09060c0806 82
    0x109550510000504101c0040d2008141e1a0300080440444d2429010b54008603004200c1e03548030b041501007030700600101ea442c00c005000c4d0000c003045902d80078548000ca0782c4040c0c280790802c1c1c0107644d0080102400340c600d0031001000309000603241c541c290300000340b07100600600301d40d9181c44404030f080c1c1c5014200c0c00559005008968112810500c0c0c14110fa40403900802408920304041d68040c5c0000c6031290800d20000403c0221400d0036034002c444542030300c07940c01a995001b41543c0303800c810380c1e0082064100c03c2c0c040004c00d01d518040c6400034020900010360000740c0c074104e842c000540d4070455543c1e10442c00c000910607540950950004156a042541e00d0090061001c405501480b076050010701e2850705200d4400700541e200e51000a0a030030703528104040c0c540e964030400c1440414910051002500b44030741c42c9024510b02c0c14a880303d241d59191450181d41003003000b080019003503540c20740d442c00305481c0d005407800c8000ca07498841e102d0400c5018004000382e501000c0c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 240496375 1250 240495125 240495127
    0x6020303060f060a030b03072403061a070c0803120106030f05090705010f0315120b01050d0803040f08090306250207140409020613090e011d1c030e10020d0f02 70
    0x181a15202d100103651902100c0540c1c0d035000010082d001410307441412601442503000110f40b900c000ca42c144424809003186900c0b139071104508405075002e5025840b072424009a00400d440700d42009070407a1031091180901e8903464084c0c084c03458106510103d0032101c240010048a609440fa80007104d0600304240700c179142000740300b6610300d41032045504201000c64100340b02d511a030300c0340d05803080701151a4505a92a11000c84445c00c1520503120302d8401000040c051030120701e481303642035124043c1825540c40d505c80350040410031034142e0781c500e02004900a01c3e030301441418480c01000004540030641c5110a80408440481480c15948440802d000703404040d0b80d0000039000c1110f0210340d00c4000d1011800b10701401e4120b040c0c0c141d50b1000465404c0c100d800c100c0c02100080003c104015441080b000030440b1600141003e0300301030580e8426810310481c2e6810884170b801e0214540080c5030351680b0304800c260070031001a50114003403404002e9401144540c1100040035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 240497625 1250 240496375 240496381
    0xa080402090a0c2309061309050907030b0a0902010c021305090c0901060909110405040e060403032304140f03130f0e040b01050105030718030b0105190303080a021803160f06020303 79
    0x1034004803c0d038a8115100c5002142444404c5100048414554000e4049078890104100200d03028060740948a1030505202c001140c0c0c0c140021403030100ca402040c4030b0303110b0320342c03800d4200200011481a810400a8111b03c00075881d40b0082080302000c4000000d03581c40c0546811342456010b480061007619030900400c080e0341e00051030303004c0c0d030f00600c0005920000c1281103070f07280c440c0c1d501c0385405c20b0a00c5101c84840401140f681d21650190300c00740710b0401c694210000504120031280031561030800414041b42c40d02101002d03401c40e150848036114580d000d240d140d500a83c50b03020b40d07021100e506102008240c0e000d5402404071154601d41c9090070342c2c0f0070a03a81c505008a0741000004000525080d20070280f4128621a1408520669071241000d1041001c00d0142ea4004d41051603103440048140f14a0350880760155075903446d90721001080c00c0a507003d9450100c0392038110b840c0910a81d0306000750005a040c2030071081d0700c2440c0c51300c03d00548000780d109505540080c410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 240498875 1250 240497625 240497627
    0xe0a0b030d121418060a060f060c0303021204060b0f06090604060f05070f0308010608090a05101509060e01080d11120d020d14040311030a021b0609060a080402090a0c 73
    0x30541000303160402c490382103010341c0d0b01c0c4010900000c1c41c10310a0001018004002c0010100c4883d4480100559215680c4c1d03d0904041d560705102e8441d031701c130031144208801481100501049442441e001d03241180c070142072985c04105482c02e0303032044c2c1d444512034080e207004e4034000200b401c20b841c0e1500744051000001c101c0d008074070900040c821400300b040da01c18414002c468440d0ba002c0c468a124540390f040c000e100381024002c0002060141c40401c2c1008800101c0c09043c07130f844001000038040c1640c48a01612150215001048500c0400708000c4c5080c0140340242c4034060070b100c20b40d03140c036010700d00d8128510118003c1c004000c02c0401d4150300851040d107601084c0c075406958030230803103141d4020b02c6417216a01c8028600b00c140c050103403e40312018002c1c0d001c1d0750f0304420840b4001c103050f01c0744500106040907900203a0900c200f04c400d00d0b420885104000e101e282004011800f0503002e074401e004450000382c40c40e04000840c80e191142a4001c05c075074200300500218580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 240500125 1250 240498875 240498883
    0x30b09070314130c03020909030307020114040b071808010f2702032e0e010b0102330c04050603010f2102150903010b0a0b09041407050a12060e0705040e0a0b03 70
    0x21405203080c64075000f803c24845003c80b18001550b0240824106243c40a0300c6e944036082516507000550800f202d80c42070303010405801b401140c100301c0310400e548601c001174510600103c1e06803140760030603000060055003840381022142407820041107a40002c2101c402546811b2402d42460a101e00c04201685000849072030480300c0e030354201c4100255a94000d80b00441308080c400003030500120360020038044d000820204020b0f001c64042e801240740d10304100155085201d0305000504640740d50105c4032400c43e800c2811030680d00d1a0945a8012a035154426008010b100d6200f07841005000d031803903100b12890311584014504010940d0000c1d40800042c3c940c414031a0000c1586074060b5002c0d8086005103030300518101e03caa585d40c0c0300380e21710780282840d00d100364500b64030300b00e12498000c111031141030107994881c980315101105413001d4001a050b050082d940f502d000c41c4c5110044501c500682454586e50303100c61070b003070022101000060442075001e091904841407501c00207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 240501375 1250 240500125 240500131
    0xe030301120b0a0b040204030606230603070309030905030d2d050304080921010b010e0d02030d08040f0c06020a1211070b030c071a1512060703020f04090507030b09070314 75
    0xd1480400e807680303a00c41c00940f134501c950750341c402d10020f80001000070641c040401c0f03a0320000c6200600143c003194404800e480c0c15040e401100030400200e42078480d40c014100c2521a040c940246038440c00441e24080700e00000070701080e100c0304c4c260020200080c103451205410303070143c0380c072640b141c0c0014214040a0001810f030350022070b00301102d07901c2c0c0c4600c404031612441705108d40340b22542000e01030142680139a0100761842c0707140d10b081c00c00c50407440700281c007e00244500e0400d40e404130340903200148207581c0104080c404500048aa003c00802020654010000c002c45802c00c141e40382900d582c0c40781805a1070b9021010701c4004a03e0360112240910210303107a40c0d40c0003a00440340f0039584001d10f408070788003c908800c0c925140190181ea04194204400c00c0910280817521032003800314850344e070080c0c00040c1050701c00e030014201120303d10b20f2a420a03039203200800a494003960000007003910b8403a918bc0500341633070001da003c0d5284ca400d01c03645003202108026460b010b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 240502625 1250 240501375 240501383
    0x40b12030403030e0d020319030f09050307120609050f070806010501031b0e0f03010c0c1a0105011409010c0210020a0210050f0f0904060312120c020d1202031e070c060e03030112 78
    0x12104a500c141d40300961710602ca074010742910030028840903a05410841ca150460102d081d072003c00544a2041d881041034490240003040ba40d030511188903449508000219222a225100c0c84001001070094104440c4140010180d5600380480380782007100581080381010720f0100c044c4a070007500390340071300313400c1d85400c016640300440800300b812083c0030a201e581541c00d20942c0c181460340b26441140c41c42c000c00c03031031180600d1032803a5592840e00f88503042c00900c01700c14100440c0c04a500900700200141083c4061040f01c1d804203a48403c1041c40c000940c0182083e40190304081101c0065012541341c2645004050394071550f1600030f510400b0071041e0007082d1031076a03807a6036010704040c5401100c2c801d48000300c11801032001c200720703501a13421070a0805604e406400007a0100c4ca892030b6842c1c400c0c00301c0028000c04001d400081c03030314808000e24200c000c007200480007094002c00280d81c0b406100d003800d00380390064a040203500c0c45103510803c01040040022922034000d2a80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 240503875 1250 240502625 240502637
    0x30b01140d2003160e0a0c0e10030902040606050d0f0902010206180a14010e07060203070b0613020904050f06030f06100909031403090325030c15060b0f09040b1203040303 75
    0x10032114202075200e1111030b19010310602207001c164810381c4088104403035440100c0080b55030741c48100801e41307035410484004102c0512020070755103086a1040400c2116180c00030300d2a00c00e400040c16103580da0300541c040307500084d6150307800000c0e0003405d42e000e00300b0500788080516540000d550f40c0307008007042070031040c0c1c6030094940c000600c448402d0f03a41290480d200d104000c035000c0e000b001ca284424030103205116002034500c0c00402a60603481e00240f050f10280e44030400d006125002c2c180d07403541503600f0006844640e503070340718150040300d41c4444036005207040024503280030002c0368140c030b02e1303400340d001c00404500da4503946041e01d50002c1e0209207641a483c1c140c0d40c00201844020402e0008810051190000806014041e84014101c48155040c42c01c0b42c0340c0b030021b00b0025000030060781d44c400c0441c501c1006900c050240b0741000480f2562072042ca801900301c550045c103c2130000a45c03d40b5445d0600074045610022180f040085404054665680c86188402014044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 240505125 1250 240503875 240503903
    0x3030e0d0c2c01090506190f06031e0203070e1302040e13140a080307080a0e190305090a030b061002010b01020d110c0d03080703150501050708161407030b01140d 71
    0x11808a02104200c405140b0703455844103130703400190204482e03503070261400f01c0c01d103a03040d201c1400f00400c658416212403019402d041d41103010341150b5402074902da40c0c548011010084c0c0340b0046100ba44030356a409a0040300004101145000d05600c030300c401d00500c803c0c07050410b641e4503142c00c0b00e8500b11402a1544918000c0c61000000402c0161030181e100f82c00144621403009602c43e41031952240d90315900c4100710002c8890100d0003690640c0200b100141c041014012004001e000e0300301541014200b000090403218650003c460041c0c0e403100380a01800c144556182954803030000740000840480001d542d510580059000c101d000102d4180004060000501450001e821400c0a001c54180074018180617148040001d240c420b41c59030100882c034051b419618140c2d2080e00d4810151580d111507000702c2c8850728145040d107202d03400509806422069080820043c2c495640380d8101200c40d4001607009000d61a0003149480c81982c0d00c41041000300e500c0301100703000c0a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 240506375 1250 240505125 240505169
    0x703050c09150d180807060b1807050703030e0105010902070302070503010908160f122a080912031b01090203070806010b040902030705220503010b0d050307030819020d0603030e0d0c 80
    0xb0140002c01d83c40c10112a00c00c2c070a00c03088170010400f60b40510414000c800381982071006114095441a813446200c20102d04824420001007103001e00070700e400720701034180002d0b550031140700ba4003a0f41916800110b00c007c03d070301440404010101240204080340d0310b40c542403c1da00c158464944e4101740280c80c541008042050a80c03250341101c40c24003600104807000e0042a401c00910006050303130600c0c0d905140d41018400300050b4030000c2a42017842c510188655050003a8402d44180014003456519a036005072070300d09010f00100208960441d40185820302c4503c0d0424201ca404c04801031003c030070b111045030f088600ba0000180d80b959613813000c4901d401600142c4502d07441c01060004220034080220054810840007048a480380008224128100f80d50041c0b65400c1800301f1000f0901440107154401228240481d4914250b601c50080703070f100340015800a962141c01f4800c4c10360100d158031003084195101c0c0c0c050682511012800b5520740f05468040542c503680111803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 240507625 1250 240506375 240506381
    0xf180a0b0a080109080301210201120209030f1626030f090a030f0308100b041d07020f030c0a0c051c0f08130308040311010503060a090e1c080703050c09150d 69
    0x4050350b1008001c4200580350032066548203120703940301c590419003c1c05418074810340d588016a0b050b15659408100c1101001c0a500300188190341030240006246d5004814800d403040c50b001c07030481c105d1603403c4c00134030400d18000c0046416003240c0315641032082d031000000c4030381806048150a454040020000ba1900741c1600020507050b20071660304205900405c07814040c800c0c40c4c89480b412b80c0c8503401600035001d0f074840c99122605615100030071000442035071383c000800d071040d10201040c00900c1469a4001c844240340e5500500c103040a105099010308080c2800b2510300c00b503807071140101424028040700252501c04118000720821445004440100305450440c1615036a00e0600112036000707480141d035103102c0c40100040b55845681140e02c00d000040c00414a41c0c200301c0550001c0000000510b01407042011030303008403a8030000300140880d10f598018140c41e2078800107003910f0000d8405111500140b0100003a030352034601c80c68440c141070701000d03105d800214050b006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 240508875 1250 240507625 240507629
    0xc06010608040c180203101e120203010f0624090e0a020a031506020f0709090c030b070c080d021908040302060114010e040f0603020315040c0b0705030d06140f180a0b0a 74
    0x1180c0800c095220100301c0e5a0040c40c419003001d0000c4261641c0d03000c10800769180002d111180c408a01010b0002d600c1049e0301c01c2c121400a0000101450854803007821100e16402c1190540c1c002604000314414401480510081e5458500d109602e01401d9041039040a002e07200c001d5000b04001540511951008580140e21150603031569514000a521020a422145041d014104002c2003442c0c050041180c4c041c5c1c07001a8080242c51625230340703507071078014080780100000000014041103100020305005402c030000141c0d00d0003a11004007140d6070207941e0701c040c0010002048040b0f07802007046030444d0500c01e03001710042c011500484050300c10350030b615802483c10151100d04040c3d5400070059034402d5045030011208501007252042003210010507011100c042402000841c20145c00c0d02407142040720304200b9448c003840c0c1610855008000d078440c4840200702c0502d481012002641425a403ca130507101e21003031144510380090840b280d268441145080031384402801d400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 240510125 1250 240508875 240508889
    0x40c140f010305042909010e0601290d05010b0d0b010305070806010f020c09130507080604050705150f03040f050c06120604050903040321180b03070c0204060b130305120c06010608040c 81
    0x3817400e5007101c64103c040c0303098801c8010307507182031034a210030303c00004c0c02c1c0d058030540c40103410700c545a200d1290710380280401843c404803040c003035620740b98842e001d218080c0000c071007181e40312405170480104842025400c03504160038070041c8072099800500c01e07500400c082ca45064034007030148003689070100040142d40c004a020040240c95001045a00300407441202600c090790340e90100e2a0b518076069078050045d0f00100002c00241c90620000071018048460b01c50030b111000f42c141e60386070030854040c1c43c141c00f03e030100c20401c80103101c051951001118010f0600c1c20710007a46913074420040c031960150359104003003040d015040054400a6902c10b0300c2003650882181c03854480b03a035002095001c82c0c1100305240c1c80324035200310002610b07064804a41580d4442108542ca001c0c220b9041e0380055031280d0200361807625100522412003034010500800345949070041c904440703807000c030700c00900030b020303000e40d050011074024111b0300185000101501c8600b4049000d86c11980056 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 240511375 1250 240510125 240510173
    0x141504051e030601090b010807030507021c1805041104300311070605070201050a12060f080c0a33030e060106031b02010c09050409110901060206040c140f01030504 72
    0x600c001c1c1c9521039141c24a0000e4054400c182d985e140f0100c1a81c062a0319240403c4600d40090b00f400d20076803201b548442d0300d1040b1380c1c0390781001c84075620945441d16088002490704132000c0500710703880d0500e4014002070b07d0400840301c0e44501110b541c0a83d00a003800325030310011030021003190b50340e02c0c009403030f52980003610242586009001c0051242d07846d4a41d0160150005090b4007450580d14032540603100c00d4500500d0040c1141e4031600a651011445c1c0e0352800480c90a81800d2820054910b07840200781e0902c1e000700300502c1241c1a4400240d50b000350143e403011130035152400e207030309000b0400340c090040360f15401c1e4058000038070b424056100705800010400c0d03045d000780d43c3c1280020000c2810000000040303003600d500d01c1d00a804905041410000ca0801f40e1226610314001d01845186a40760b1002900940b802c1e440000181d021000340030900c20403504200081c2180c48803401048082004503012046114569044c5581c4100190500c0468808201c585958800324 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 240512625 1250 240511375 240511399
    0x30f0d0e070e0105090a020307050306090402041b05030901150503070509072313050105070b16020a05060c09150715021b010216030201050702031314010513090608011514150405 78
    0x1e452800b024414544030f50804008652010506d01c2101d00510a960300c103440c698030a42402584003028108030b030469034a050350303a4685c1c02a0b104c0c00c0c070781496982e445d80d03c0c100807040701d00391004140303800741d103160301282013145640004542d011035901343d660005907652518103580035542c15004804400201c0c4000c1b070302841540003040030700e1030045211811034070b403001114240119540200108440008a0080061218458581005841140d00155443d914141420742c1a01c44061140c4c0129540000f0314004c5404482c0d03104800030942803c603142c039104100c008004036410712a900080645500508500f881c5200e45510004d6546d031002c0d980480c41c02c2e140c1c807000c1c0c0041d440c100101c0c1d54070b44040100c41d1009440da004000350f40c01c042c1c4903040c4a0002c030025040c40803c00c00d000200070100801c4008000503080090140e1174040390700e0035642130040d11030601c80130300f401b44000c1440000248441c0410b5414a0a201030340380041c8040c890b82d00150750081d01042c103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 240513875 1250 240512625 240512639
    0x11160503041503050f2404020c0c041d0a080307031107050c01120203060f04112a0c010822050106050301020c07050f150316030603020d080405010305070e03030f0d0e07 74
    0xc004807006103000841440202c50700724100c0c0c1050350384e802c1a02c1d10340c3c040340d07140e00c17001d0340038685403124200c0d8500c640031480060b003268041c065a0106400c05208040030b407034588508803c50540c3c60507401c0c10401155185c0c0c40c1d5940d20f000802c540d8010001c189428843e92040c00300e00f411083c0c040c2d079a9540c4c03c14a03969880380f020300303000800301c80402c81103800034002ea81c0540e00c05401810340d1030341e5108000c0989017a0110415400b024401e040d0140424003014640b01007540c101c00e020849036a070b203420054104403503410300100340c2c184540041c80c250100c60605d480e04064000d190a8603000f030241c10306030701290341980007151007a00c401000c21113504603a4102d40000c0d414074000c041c0040c204082c4400341030f60b401071000402a6603900c492851802084c41e0020340b081e1281d00007004100b543c1002e03101080e000ca0b00b0300c0386507098881d090304655542010002c0a07040c03800aa601e1184402080d803a1001089009a0504c0e80d006a40744404113402e585120b13032107200b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 240515125 1250 240513875 240513877
    0xe0c031e0c07060c140f07020d020d0809120c090103020108180105070e010207050f060a0311070b09060105040507030203040b0103080a050c151b1905360405060a050d0611160503 78
    0x1502d9852511583c010038502030580200d070b0301303804d0451a040c403802211b01b030000d42010310142c1e0030050030829600140d40d074440300f42c1c0142c480c09819843c2d010490902c65081c004480445107603002c1000500c1d5541d0381c1058904480c2e0900c0d200d07061303644d00d1110540711440500c0d295115070900041c4802190010200e4800b0602130f801c0300c0003946d03a0030801c02000400940304d90030203400c1140141d0103200303401c07a4240400d1240303072a1402c1e0103a660507a507084100c40603411030304094010306c00e510703060080c16000403807460309500b182040d071202d80322020184801000c0c0d0b07400150900066004a050740c01526421040d50111000c44000c1c1e0000c2c0000c4030348006407070604d0b03a160395280f0007034299003841c4c240c072051a201202940c0c0642d107039130010048840d1001080380c0c1254546203100d074000694103083c610b03a500045042400181d0fa00600405d1003a0340c2c5003014046500c3d0800b008800e01e8014801040c1d10f00c1818103d0644c0c40394101e103482001c0706030814018004000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 240516375 1250 240515125 240515137
    0xf150504050606120103060c03090503070c0602010b010c02060307201e07050306010303120b03031608071403090f0d0204020c06040804030c09060f0506130b160506100e0c031e0c 78
    0x5a8144025501e40d02040034610618503240640904c000042c00803e845030b010100408180c10300041040702c1e61601c61842d0003141c422924000ca400b01400748550a00409030b00c0c49007800c2c000954102380e40007a001d400010100c40c104500300c2500008100d081004103c6082c018060300e104100354503010078a400c0030180340121f03100d002c1000400b814001111812aa019500c040f41c0c2d904519100015196082200394140303c21301c000700e11400f00c22460401c1c80c0c0f24107001951100a450070300c00e005c1906160403c11340060201000c1c5448056803000c004504490020303c01d0511320002d8000d01580340c0b0004984192020841000064801817055074050f52010159941e01d4040005072001806003042c0c0d10b4800c0003c10450804202401e002e100d031902e900d042e25145d003402c1029400c0810482006050f0030407060900a003400f02e250040000303020301000741e0801c0c00c0103840c004084d0a600c3d50308000000070f244012440794403840c84240c0d852881039402c04840416080e0002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 240517625 1250 240516375 240516379
    0x909170304030921080a030b1002070303081603110705060f091902060f1b030406090504020c032a010f09030801060c02090403180803070c08010507170f07030f1505 72
    0x41145440010100503688100c1d4181c0d2000045410140070451008450030b04a00c0003c81070f015200051408014000d09a043d54000904c04410070800608424182100040d0b4000074018000b19074452101c646c840c01c0c0100c030f0100894404c0c011001044203a030407404540c070214000701000ba001c21564011202c0c4a0602621384030403981e203889901d40c01c08560041c0c13002d0000704c01030a003d000b4108040e50300601d80d003801240b242e44400c0c9040d00003032501580000406000c4240c1000395035018140503a811402c003080c9401751175403803003080c404505400c10844075030711020300c104d0366880b10f102081c02800100500c000110107040d0307a0300214042540080080b440700c1c46104212103058004101d100a40c4960300c00b9a4007600045149102c1e249003080410f5010040005000e0240303e090947c428500c5d00b0515800c64401511800400ca0300d29000b0112000e00294150010907200081900b0b86a003072003070f0f00408118100480003400c0c405101d000e4000f11281204980003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 240518875 1250 240517625 240517643
    0x80912040816210f11030f011416020304181805010903080604020a0203121f121506051e0d0614040506010f0602030f130308070c09060602010507050a0c1b0909 70
    0x2103404003014500c60030b54003031000f040c29400c4008507400428082c0828000c45001e40c03409a410301013810440d41e00c9600700103a45801155140e10016440d07941e1007000a62001050f03009088001c0d203031f100324032482d005000080d032440784100f200e5021b1034090001f110103904100251a10350702a001e0b0040640105080c03070001881c80c11f050007181c2d41c26070143d016500d000700343c151556a00e50301400704a03140070300c0180602c881c013a201109010b4802d0101c60621900e02d440e0240d5207074a05541c0c0414070b414180200299180c43e0241c800e10340720720744112144018840410b0350842c44040151807907042c03d032031580c005450350b03266000380d0040055540a80e2601c46124541d4000e100342d0005900800180c1c402c001143d003d0000b841c1000d40a01a040c1d1b2510380041d0307034001c4541994624000c800030810403070f8911401c00100014002445545440c0c42c01a001d801121501014802096550070801820001c4107400344185c1261403560303a1190960001000c1c0120100c07100341c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 240520125 1250 240518875 240518879
    0x9030d110c01020c091f090507050405131b05221403100507020303150d05070b0a11010603050a171b07080705010c0b0109020901020319030504031716080912040816 72
    0x4804900303a50300c81009070400015032100003c0340c0e418901c46d410060f042d00304031000300e031040243c040d150040c1c3d22550351945075410700040003008c45203410002c0d480c614203c40d5418020403421055038510290803d44c2c2c562885031312240d15020084010b4104007002e98010840131741c01110b501c0c0741e64090f005c036440740c041c400e180001c0b54415581d0354003681c010710001d0501c445a1091071725401010740f0740903c8001994465183c00042e40060240704408145c409c4a82c0d84484036500384e9404800903c911403030350300c429442e58200c910180000c1c0990b0f010100c02d085420031100c0080c003143c0012901c25841d42e0040c0c0360460b9026031109405440000a480e40c80340e203000d400540c0210f41c40d0100c4e40380450141c000c1d804480c116040d4001031015400d21040c0400b600480c0030380e618045840e207040e00e40101080c40c1424644500040e40c1c00303000d5400800358140090b84c41a052241c41e82e102c0d41c1240c1d2074052018418610400001800300d40c103e408940307404001c0c00c5c1c0c541107003555 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 240521375 1250 240520125 240520127
    0x1216030e0d0c091407261e041a10030b040f0305041509090c050a0206190b1e1503010312030b21070e06010801080a0609020604050406080d0207050102061e040809030d110c01 76
    0x612581a2000e0250002d4604c01e901ba542081c942200055900014500540032224607440044034141ca90850350703440442e541c0003a0080c964041e149a401d401d215085a480c0c87c0c90000150024200c240044031010400d4041c0003154050403043c8032540284075064030050903629180280b425003810002e071122003500400c180d4500c0e4007590050040d6584440703010340084d0110b0700907800940ca90310b03160415142c00010440c8041d0002110a56a449100b401125107031400f00c59000b4000f0401000841d0f01c01c0140d149101e039130310700071848030088400500e603422030004110212000118404a0110001e090f00484012a0710011107640c0d000054590303107001d104926290300101c00c0300c000240c103907014a242e14030041c0024103042e20381c4049411600c1c181c20481e25640325040707005500d030301002000010002480100320a26024207240c002903400d5800400744070780c40000c1010044041e0941d800d005d0060101c49241a07566001000c101501420395010700818582015039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 240522625 1250 240521375 240521387
    0xf080c181c03020f163f0309050d0b01030308040f02100f0210060803030609090304090f0204060216030201120f0914060103030f020a05030304120309050109030504081216030e0d0c091407 82
    0x48003105250010503843c00f0710300014054a507007104986d4140c5079002c03403032891108a0080b1940304070010808640d061034080c2500764039030407a62181030003002400000c3d0032144c030b4a054a6061520050980b41c40c0303420031100000810095102500b5409200103d43c400800080000c2c9a401c45048162424805007118118003c0c401c050300104000f03403040c205211101d13081400fa82c200c0303140c40d661b40303105021951520480e4004680000c2d00b003002960400c0603074240031084820400091440c0c6c00604031024407140551140d84034214503000046a500000840381c200c9450310101064450140d21041e00740421400319414103222030300d85d8400140c010080380d20400840ca1600d0390b03100c50400012003a00300c0e00b0540c40d9400200000e4013806091106071094840c03d40703c900b0040d0711405d101a035240c9c0c50f0b09010a00003d61130080c258182030105400d42842c0e0300b0601040b022402c0380c1d01446c80600020071581001608c1300b0941e005401002c4001d030281c0d40c6842d02401218a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 240523875 1250 240522625 240522643
    0x51014030303071103040801090c03060509010b031b0d060609021308070803030c031003140a030806010e0a090902040b0a030f05060705091003050c090a090605030c010f080c181c03020f 81
    0x55482480000e410902400100c20704c1d0b556042124141541c40c01840e0945074200d80031903d071498a00c0802c00c2180740d00540380c024842030700a000c078040784070100303a4951074510704007080c501c0e00400c41402c0e02c03030060b40342c08183c21030f00900040e5100d4129070041d5022207000041410603240000342c800d404641d2000b91802d0304c0c003851840d10b442d0700b558032a4202034900c4560b4003d41d00004001541c2e018071200e80040040a050035034074505000c0c000c403a0041202703040c040d1503004603401d662090b0382c0100f551240180000c0e607482900200e00100072086100c1d4018800f40d0003c400c2c01703001c8415480d807505c160101d1b90b150345c0d8441c0441e828096884e00360380201400c2400000076000740c1200703034410b0b40b21074590b0521a0900000f041c299203940105c0e20030365120014401420140101e10002100b0b00f0b01444202c80194000c24a11005200d90000d08011a560720301d440000b0300e5200b0064003c290444041403000b0111005040384c50032030151180c1c800e080c030700072004180340076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 240525125 1250 240523875 240523879
    0xa1d010503060d08090312190906180e04050708010c110606010c02010e0609010c05030f0c0705060906041a0403020a0308030a050a09021c03021926041a0702031f051014 74
    0x52000f190780c50740d2080c4c205224041c0d050040140c1001c04490540207003c070610009410201001d038881c0c0507141701c496410031420407103a140107002100400e49aa422240511407080c101d5071141441e9041015039000b1001a5003002480014541e1144070400042c8645060340d500c3d032034000064a4030510100300a0110700507402843ca1480c00c0c1000e400c07442010b051042c103540c4980da6203411644107448030600d501c0c02003024a041703170040012502404055640710319240d600c1c0c001030000d01641c45041184610cd002c44992445001e044c0c400441e03024101c1c1c490700c0d49910345600700e82c00448103454400d140c4400940c500340c0c14003e01c3c0d921500a007201c1e10100188502070310440ea8040300743d0642c030072911001388180000f4004254280a451510303241111202880300345e01b048500100b4440c0140018001e4502d11180c06101345070038611207548484034800300c0d040c203040b81e418144000344120101c40b0075605422541c03251048003031003241540c4404d1292011440c181c0115 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 240526375 1250 240525125 240525139
    0x10f240c0807050c090703150b030f0a0b19081b040903120c090513050603011103090304141f020705040606050c1b0607050a05010b031513030f030609020a1d01050306 73
    0x30110340720600400b0018022800d9607220350040c00401c11580e000c0e03916a0000e039660311060781c0b01040b154000081c000328042145107081202202d041298040d00607039890340c0e40c00c80104155105895061008081a00c0d000c42664030001c1c20344903d40c1c0e0082030449806602c404c0c501d454140309081d00703550300d40c41e2000c260031680813000007810846402c00600c20000d601150301e130782c7c68844070001c1007514004515403a00a0038103007035a2070503688400521003071051250454006c0280c406980c814030b655018045010300080c0600e24950080440324506001d01020a42c0070400d14141c950070f6909101c20b5689050480b0b103031041c60400340036500888404928000c00ca410a40a00802080705003000400d0b222141002c039845422191695182044c1d4034030b00f4248000841e907500740c503208881c0d140c80ca04180c02038041d00710080412403110416080c2902030782c0280c000d000480011500d44a061002270034140040080425003861411510b10715881071084074490340000d0421 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 240527625 1250 240526375 240526397
    0x503070b1303080420120a0c08011112092a09070504050a060e0a0819050d140a030506011110150509040503090d08041e0e090105070f0c030203090306010f24 69
    0x2016a9101800420040d60041040f10b09a035580d0108403c401904030b01610319035100c0e241070440c3c90320b00c0e030009c1101d03410039680c41240c1e2400c509171200d40b030100d11480c00e1030f56802c4e070715420003556030401d000d880b0410303914070003a80702c4058420845a0940d400c01084c1c640f200e05403014020381c0b00b055400200360405000c41c5201c0c501000d002e00010b440d4400e8507407504451070410b51280e50b441c02c480b04c1050b030102444020400341000303100b00d040c500010401134051242c03510070910000141500c410102e80715034802c0f4009801d0003001415034040b900704c1161540500a02500110610305904012915282c0550020b00076584100103628082d0603a050010041e100401942c80f51414040040c078021000500c62200100001000b9407905080381c040d07408101810014082e807406003042045034106c0940c840d201d00a00300a10400180d1a0880c95441500041c0386c06001b040000221900c10713410220035540c80150781410480e8100382c0184013101c094050780013071924088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 240528875 1250 240527625 240527633
    0x121207030834030c020703020904240608150405160b0a120b061207090b0706020a080108010b090a020f070510060302010314161b050105070c0c050402040602030711030c0d0503070b13030804 83
    0x8645004c4545005650111342d80750000b8601a004540c01c0c2d560051921a18081140c00c0e0000032040e1030601c000c101140c2080d80059aaa25504952940c40e001c600030a05000c02042504813455031002c605c04001d403160501c1032644c02c0f4074031303803c003003080000d600e410100c05014402c0001009840c540c10210342103e074916440002d0a00c20500a10140100303d10901d24000d08403030707008a0380580d03503244c1000024400301c3c0580c4003d136182d24040c00312a13140e5615440c0f0790011400c600140c0c440b00e0360a00c41100344180400108184645041842c01c024150404811607000362004c204102c040d0800040d00391044440905a101e0100e00a4080b801105801801040f42c0c1c222660f00d02c956560a00b10740007521580003052660884208003e00c0d09000e030058001503400b5800e161400c0ca0107903a0f400744e154024101c0c0d511b5144076800d52805c10010010060007450450015418140a42c580d0301c6040140e0b6442d48041c006028407902c0c00c03142081940c1981c4049103680c035900c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 240530125 1250 240528875 240528881
    0x17120d0c03110a05040e10050d171c0605090604021e070f1a041b1503051e011d090303070c08033402061f0512120703083403 55
    0x9003502896981c2c5500455404920040d0508000c0c58480e42d64407400c11540b611490801025040c0c2c80780101070034440e0740c88000390102455070240c100300140c2d8100021080c07074040c00c86105403070500500d148800086940103001110001e0b180d5078110b84030041848160311030704240c1c90b10440d4800248006080d504002c10190303000301941008444039940e41c0d00b80c0c101001060040b03400e480c05000034440652551500409005081c40c0250f00d044c060121148640e00340301d0505039618000b0707040038102c8682c040072a0907084d40076410768603014401c00e41903103d06d01200300404000024410b82000007102e0089000f91500d1000704640d030340c0c1101a600040921122581000d80d8081780c208a4944109001c50b18201461005075408002d251000050408000703410389500c100d00c22460300d011900b91a019030b0b000b440b03d2005d070030607031a002800107150000b14000980600745540708011a01072000002203e090081d164001203a041c00c4101c001d1207160300012290b20607001c0d034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 240531375 1250 240530125 240530141
    0x9480906030e370c0e0f070e0109140619020616090f0302100512040c061b1e0c0e07021609020c1e01090b0a0902012006040b1008061017120d 62
    0x10b01c002908510030f556100c40b408031544210b8031400171405004124041c42010340d407002240c43c140884000510000f4094240f51080c408082d551a0300e0030b0540e260b00342160034080c0f03084008140301c0c01401c0000d58905046410354440088075080c08402c80c850741c3c240d41154070301c3c400742c02024119001c21140d0650510028244003040001c003085000d0951810311560051035640901803800402404031000c2104500703680e016803240c140010b00c40340511440c1c02e6480d4400c85202120720344800d082410341c04c48103111719840100314a442d800a64090b10202402e8966000c0b0756a84144d002c0c0c5c040d000d003221450704200c13441241c442c5c100246843c0286240004103580016845560000b40142d444a443c56102c1150505558210302c00780c0701c410204ca00041c08140c0b40c280e25840e28030143c8010403100607180402c42405c0c007860300030007070b0100340d00341d90b02e50400c58120f01c0000b819100710740c5a1a00c031072244242d00004540f00070648102090f0b1440c10384155140c01c001e02c1c4107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 240532625 1250 240531375 240531463
    0x50607050703090e0a0f0e0714010905061602010309020d061b0504060206072a030503060405090303091504020a030209130308010b310f0e0108010609480906030e 71
    0x24400b000500b805901645030300e42200c10103848c0d42414101608225004015814144200c905042240e5212603044405d17819000745502c08184544c801280a0800108080e6004030421320800a00455074040b100c07411900302c0b10f0452004d0034600b0380701c0c1d001d607100da40c0c0941c201c0c4000540c0b43d4003030710311880c4c031b018850743c60300742c008071003401300002030490400b51b0004201004006190500c1c1c0310307058021207041d00075408c510340116511703621400c0c0d031810350070401039101240441d03d4000d4a88043d6a0050071000303d8942440407900308403c00070b05400161140c8000150881c05404a0344100140243c510100e440c11601003610000003404028030b03142002c0001d0b10b00325181c3d4000140902056248455150440d203d00355485604050402c61038481c11416810400d0124030b206d12203d000c02d901c002c0a108003d07080c2c3e0700e0700381e0741d6088025803004800f1a5401903000e01a0fa1346910200a640d000f40701c20380c0c0d1510110351a0394111900402503001141c3c40307040581e10000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 240533875 1250 240532625 240532631
    0xf08071b1a01091406042f0f0f12130302120901021014010612060b0a03050a1e020c0f070b0d020304051006060203040302041b090b090310110403050607050703090e0a 73
    0x701240181c1081c0d001d0b402484032641d108110f504405414503a1034000100f29024030000382c10040a125031202c6540804608806408000743d0030940ea066419030441560000c8c5c44001c030116100e6203910060207108900d0201c000618a0b41c000c2101e10002500360380240f4000100d002011150b5010306281410362045404181802c8002d0040344c0d00443e80900c540c106514205000d0306d41001a26000000c50030a102070100942040554000780814540440d0b0390300c030103903200010010901991920125045496540b182d540c008280e124a8981110540030300303401499260b0580c0d006006800008001e031718261211078010796000382c09038080d41c001c1c03180000702c00100c0741d150313114a0258201081c100b040d440d180c410b0040c3c1056101c0c040741ea40da0410002000c0d81d085008501c6000d03804941d60031241ca041203142c29070807102d40100000d14200804080d142c126101c211424412100000c84a070b1160007682d0003207070326480d4080c450781014003460b281e00000b003240110a513 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 240535125 1250 240533875 240533903
    0x161704052d041805010e0d082503090303060308131806080714040204050306070c061103090d0f120906060f050612040311010b0a03030c11040b06070b0405070b030f01060f08071b 78
    0x201c21b01c104142c00e45010700503c0c900521900281113448000c14011903050301074140281003801003001c20348849140380c0003550140c207203820340003496540c00142600d00007080100300e621805401400f690358029800c40b00c000071508100994119015200c05500714030301c104504156004200902580248090b04064170340c000b0902d400c2c0109c1d0000009a01102054203104d030a00c1504007a0031071601c0c00d85107103001c1b4034460f40d030300303403655240708210208900c40f11042c4104040d01d400e012003901031044d10014203101014100901030640d0340071004074005904d00d40328048480010b000c0c00d440c2010764858401b0350300104098001e0030302d03540740d6280641a0755078039210400303075210b529801500c401c5414801004111115041d01444c601644900550b0710402070b6071509174015851041940d4a2906506201c01c0307901c48041d0080210903c10384046a03c0b603981640e090703541d83c41481d0203c0104480d44001542c4100104044c2211a05100740c0e054000318064050540c9942c811 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 240536375 1250 240535125 240535133
    0x3010606141602060703090e09010b09010e0a060906060306031a06010c17070f060f0b0f0f1504080708070501020609010510230d03020c04110915161704052d0418 71
    0x60300c401800c0300080c1c0020002c0c45000c0c4485234460b00000100f000304070b01c3c9000c0c40401c10b192170600501542c04a032200080e048801600942c02602c0f9078282030042c01d03a26100500503281c0c5000480b0503850032003444a010541c508068403c00050356440d0300c0601c00d8a035041100140e080140002c0400c100078804030308507192008405215070b0001030010760340c50742e1000300d41718811f240d44242c0c0091041c0c12144c0da1810075540c0d002e000c4500103030a682c94000f9030858031490303001e44041d01900b000061000710101e906811100280c080d608141c3e90f0702042402c841c404c4034900c07082400d180003404440b191a40c0c4507411110100540c088885d210002034001c03204aa003100103a1264080340340508260085e6800420007600031403e00340040000341403114032001e952400400030484d000c0071700f0b10f242225546508800d80000000480c43d114403564854054640280c02080301d100d10188008035484d14100d658081400f01c100c110100f00c0030304820b104125114a80007038440c045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 240537625 1250 240536375 240536377
    0x30f0c19030e0f04090c030201031503020a18050702060129090d061d0307020d0209070e09011502070b0315011206090e010e190804030b062e0e0301060614160206 71
    0x414000d0311000b400741c16903001c1108a200d89040f1a0240781008142c000007041641010b05507542400c0200e40c0803100d0f0803040ca40c010a500203588550324900000364004c042503a42c481685070340c0d00f8072003580e0700602603039140030a100741e807138070001440324010000d0411444642d040d90302c90941e00c0e01c0c44a01c000351006544200949100395580441401c10b1601e07200d0b116040344000140d03040030b0380e54000520b28200058042c3c0103032102c0f000140d00300d00c6600300302d0b800040181102d90300c0d41c40d4030810060360714a014007009449151000306982c200300043d2440b810703650071f034403121038204401152050018409035070042c1c0c581c940451118240d001d1960000c0000e8000107108105c4806103151445001440700788814590f4032001281042c011142030343c5e0000140c40c050385801e40814044030000d920100f80900840048500d078a107030142031801002d0781d44001d10040c1040405003203981a106e80e0703010840c0c82007004010707040310303020b009401c0d8600d200d0760500c045c640100b203603 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 240538875 1250 240537625 240537673
    0x10b09130f020c0c091b030415110a0924120e0102030903091f08040f05030405091009050907051e010306090c05041d040503030408090f100e03070602030309030f0c 72
    0x1c00354011071000c1c651441004465031402d030884079030f60346042c0150302e6025403040030800c00c1070400000014003840111000c400b181c2000840030080107205680e000d5840e00020590400104130040006481e400c44030607100e003d1040c212080c1c800e08480e8162028410050218a0b81f600d45c02010040e80c003e1001e10321489444001d50340d0b52040c0010020440d110101854151699071a490382c0d19a101c0900355003d80e120b5103203424440b16060052a6001e0355200302e500c03450501c20490f00c0e0200564440498803200d0b0b0501c43c41d01c4550002c0c0d1260b0307543c01920f41065080003010316555a48191130f00c90340c07040c1000110940c461030254103a80b450015040802ca00003400c100710f00e5483d014200300d1005564000080c1041c1d5209030b00c030b220162020704202400311f1062001e41d1078040b040c10b0301b00010100c0d11403032180135003c0c0160000d001a280710340910540001c481c1d00110403a03200d2081240954602000804422070130340105d03079440824071440c0360301c0200c01038224610316 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 240540125 1250 240538875 240538901
    0xf010903080702010e280f080304030e0a14010e0f1809030c1513060207081605010603060f0b01020a020d03024303030f12200306040b06040e010b0913 66
    0x2460b00d00312602900f074606a2003108a958002000002c0d00303030741071a03d40e4004800c080c0400300c0f0019030401061604040030090028440001031104040e04000741041c40107040c0d0340d6046035a521400d03c0034080ca64880640450f07641e02c5942264074064000742c0c89018020600d034844070382c0700121200202d089035001c800341d00000300c603940404100701084450700b42410318810f83c584404d0070811140e10101c014085138012400d00e04000004c030a80c2e010a0349041060204500340c10b10a0280ca0944800c1d1016442d281034500c00103024040c040701c520040c0c0040207682015401e20000103a41e41c810360850007220000c0061101e00c2442d1400264002e1a05560300d820340c5052003444614803107051141100741c81040042d0f046203001c2c0001c500707820300d12160000d5a00300409441105c81d242c0101c02c00340002481a00c40c040035601036507044d98104410310440046c4461441580940519983c0080040001b003050100500001f00007a210f14855015600003005441f03048140701 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 240541375 1250 240540125 240540137
    0x3051b0408241603050703060b19030507020c0f060d020903120309012a030f0f1d06240603070311120118060605030a020f070c06180905070e0d0201020f010903 70
    0x902c030550100d08200c010140100782d81454140001d0403409881c450455400303058846000461a600030360000005216047d0305698030791140c240300d908001c540c004a40442d03e080041a040c41c400602750399001400b80c01004d2040e0110204841c40e000440d0380c07040903400300300001c5207440501041c03000b403880f11011b84d146e007000301e8550300750f070141d85d1017420800300f5800709104a0051101c18181c40c0f050708000401c0c1605401c0702d400f5000b480020b810050030181c240b800e154a841001c1c00301c1210340c082c0c0b00c0b5a11810300f04034500920714030070494040400541806440c1c2400210303007024441c100040c1188160b8401c401d00c1d004032004c0b401d01c0b800500100b1803040024429505c201049008204050610750091300502003e841e1040107540840c200c0400d414079400c55194640001d24030b00f4641d43e0322030003018030340c442c0c030444508441010000b80000190040c41d0054a154444800c9410f8110074031564503000b0505a045108510b003140e482603081c0f1804907498000e036140303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 240542625 1250 240541375 240541393
    0x60b0705060a110304120c02102a05070510090e040c0302040b010305061305060609090f01050f0a080a0210051216030b010207031e0501020f030703020d0605040603021003051b0408 79
    0x10605100009250340394050414031039441e5211100c00b207950040c0d00c40006c08600d510381c001150602c1030124004d40042c040c0401d00e03a03260b0000040029440c884520310384c05a9208100404103100c19001003807948418003d100a240c1580810250042403070106001d42c0c0e80c1c45000c208010a0381c040e5040c246080e003d006600f8035015048a00740282003d001604006001c141e61800c02c081c03800445590310040b48060391010202c0f100740000803d051501d04003055810800c10080c41140e1041011107031141301420810b44035002c5515003006482400e9168081c05a2010002e00207410090100646035804240d0f0202501960304d6000c3c0d80b1b402080032401408a80030070011034159440120b0030000140b800718100000d10304000b40350400c3e00c483c60310030301a000d00d095025502a01104001a0903815400340102d069000d00c1070244035541c0042c0400c40e0303543d00019422012074030007800b01c10302a070403245d001604a06040c0c12409001101d6140341c02030341003100d80350050b1000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 240543875 1250 240542625 240542633
    0xf040501030b06161721090f0c0a09020904020918040b072c06071e0309300c030209070216050405010e01030f050f01091a0702211804060b07 62
    0x2480c1465481519421301d030844e4901d2840141071001c000a011070382e00141e41d9940e92111094800900d0340c014144a008040400d02007004070031259003040c0d2213800500d444aa10018040109542c09040341c00a00d0038401c040d006548080782250300b20360200520409a1286a43e004001c80c40020344c82150800c0d28200d02c499001238540000c01036011511841c100c6014651041e2080303050030003141d05030035000710391b040c090040041c0c01400c0030088040000030505c00c0d9401e140c481c1d9500664103840f07002e01c10007040303030450964080c0c440c261040001195000c0b0301b00103c4c02206801380090340d03a80020b4078070308100c0710400140c01031002001e04a4214100c0030203020116007e111710760400d010314480b002c0511002e4040132140120405000080c8000c072200d24845000b4040e003041c81c2441a5802c4042035211413004041001078203c91012070381d140340b40d9a0807108800c0d601d00d024088400d420001542c0c141d040e1080c410303103030307940d80e440341c040207040c1c00b13401540303d10f00d80c20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 240545125 1250 240543875 240543881
    0x3030f15090405120c0a0803040c0315020a050a0c020f030f070602010c030b0f060304021207030f02010f030c0c140139050a0801051c08160605100b070807080f0f04050103 75
    0x148040c02810030400340b20000304082001c520154240c41415240d0441070031442c030380792200c2c0c0040c009100000070302007449102c200714000d4a000e0031001d100e105001d42184201d201c4c401c44000092070a100f103c043c588524441c0300118001401d0413080800c1c2c3e80000e00348040707080210800d5001c040308002a039028000c805482880c0d0070f00308071030f0f540440403030036150050003840d01c649000000541103540c0c1d5007008001080660842c0d503002d0316440c04102003803d140d81a4003080000e001060302600c02e000e078150b03d090300d030b54100300020b1139600c2c00c0c202c01020749841e0603952140c11079410038800e45c400000030345201402e41d81c0c5458059001c8441580c0b07216600410004000c084402034104440d1411500c09607a03a82c3c5101c4040900d4181c031364441c0e0010019a0005107100c40f804c0321709090040a070281c881008144c8804103986080710b0640f0a190002c0c00034414880411a420040c10b0424024482c0525003141c1c0c8000019603440100c20f001c44680101e0b0070701c400e59147c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 240546375 1250 240545125 240545161
    0xd18090507030e0d030609180b1f08030406020303060a0b04081b0103110d09021c03080708070302090d05060f16020a02060903070f080303041b0b0f1e0d06030605130209072003030f 79
    0x100c1c40b989070103126151558111401091441000c542c50ac200c441e48281c2d1820342c00410300502501d8031640c03550002522540103403402403040b0301000c008185c02007045d0494044813041001030900e00034003c50800100c108140c418145030b036485081d613490800d000109081e10485100141c0c43d03803944104800d0301e00fa04c80c109080008602c014000a03040240b50340c002d080c40c1417480850b660304a00300d019200b070001c8541c000c00c0b40c0f00d121040110018182e4000c0303035183d0950003142e4401181c80501010242081c0059000804010150030041c0013403200c40000781c1540e160585480303180040701900d90004c100340d0700000400051010748551420101042080c1810f001e15000f074400d03007030048102480301144000390308940305400c0354090102c0c0c2510310685841c4c49081c41ca4070014800c62106450017801e010000d10451a050011070780954010700022054030385540c2103500e144150301c00407200711700c41040013040c4004c0015611070030564800030f20b83c1c50f02c448491a5103444c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 240547625 1250 240546375 240546401
    0x1106031501090b070812130203010924090803130f051c021e1209041e020901020d0302040e0c210f07090e06010e090c040905180d18090507030e0d030609 67
    0x24001300380010340e07600442e120202c1136582c1c2c058517103c0740b00005044420240080d030643c60144072000304215490119141280034400d03030701c2c1800030b803658000c0d240303048002000020100300007801e902d811260020410b00601c09902e100b02d82e0340d1124a045801c80034050107200840c1d80b8403c1a84c10021403c28100b000038515058001820300e40c0d59003032001800070011004034000c1015203455012030b1400782c01100800100c03100c0c4455030029448500c00600501824460104260084c02128210340f1844a84072896464194510300d607001741041c50131554002007000e50400c203440c8102d001c2d006c03181c6201c00508002802801e910741c5503101d00354400034002044542c0ea00410403952514017034034120113942c2c80e4044117180744219040610124130740001d00444214440c20003103801e0390001100c144207514082503038940c14104c03511112001521042c001901075401090300118903040200b407491005484500b041d01c41c07051000026982c100404c2099160301941d507040030701d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 240548875 1250 240547625 240547627
    0x60c0616090f03120309020607060b030606010914120f060106180906120b040203031b061017190206070b0403030516030b060a0818070303021006080712020d1106031501090b 76
    0x540719280310002a030707100c0681100030040b000c0006a01a4002d00106ca0340281100c1d602c0d159860000000c0104130255030281c407607440003821035402000032074140d17201e00c1d1040c2d0006925800700b1011014900500400e8010790504000000e000c1001078041c1090323498140c90710740c162510102c0441c42ea401f1800c1076081c40c80400c002d1075510130b410b0800e070300000320086c42d5640d800880c5c0f8501c544c51006025003201e0500070450100410b046e401880340c40c20313403d94585e94014000d09100080c0c008029078008110b14200c16410141d00d007112440a80540e0030110f254440c1e4060f00412181600820f40307600030401c0400c08a44c440d0900900703070508001280f1b61a02254150040030305490030700c05400301140c14400b220704114200c0c2c801a00303c070320f81354685c60300944462419180d42121414107102143d400808160f07041562000300d001c100054071340c2c0800c05490000d440554140801d040221850740710000110721982c041d000e98071005201000040c61000194450013000b54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 240550125 1250 240548875 240548879
    0xf2c032a06130902090f12030901031415011b12030905010c020622080408060a15080604020631082104120b070207082a010c020d06020f0405060c061609 67
    0x1a01d02402402d540202e00e005071a0500017010442d007005c2c076541540c0c400310014428648503030000091109060030b98040c8003846882032001090403096580f00da80300c01c030402e01600c551044840418074014480400c1c0254050303250582c4034070010424400180d2107807403003c10301c04240201c014491261000301202d11b41441c074102660f000040050070703041401046018095a42c0659015118000036035500e82407a059840043c1100e0904880d500d40c60840001c20b40300108816201e190050101031900c007880c0c02ca15a030b4100706804104051028a40b0b8180c4030203140f000f0050301d9074000400414403404000c14003080340c8143e5500b50807040006204507540c078266040301641c0107440c42c20300c0d220f03442c0070303130501c6a2a002000075120341038103400600e45900200014155445107090000300210044500680088c000f07900710720007002c808001041d990040443c44810740350303d81425150300000308180d00c101c409554a03840341d424000d1140b125503403035080301303124100451403034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 240551375 1250 240550125 240550147
    0x613060522080606210705010f020a0501050a0609050603030f09090703020403240516050d0b01020c1c020f0d030c4e0309030c0b0c12041a070f2c032a06 67
    0x192147c024907040103452102035500c0c5000b00300160203690711000034445803a004c840c0710000e1111b44902d44141e41020041080c60a01100b110041d52010030813520b8864841d06001003602c010302190304059003044000041019a0144030349040c8656140400c5550103440c0e106070750014000803201d0341c481400c0740d09580c0080c03c8890035039160001248080e00c7e000103134204884800c0c419003001582c6030b003003620281c01070000348a52003181e040680100010600051b0851150000c1c003140d0500c2e591004545c3d8020780c901d002480301c0122240ca00d40d00444001000400d2114180002c0154a03002050f204003221621086620302003040c4c4d203a5490040485080100141400c1c45a4ac0400c2c0006918400c276035100002400e6071030303582440d20781202e20700c030401070801e111410800410303042da100c1c440058030480030350348030b40c102c58403400d641d480081f50900c0c12035291001111500c0781d0320203001900c0d240460520302c00f80c220000070000d1940c045c01d900c89105035001c00011940c9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 240552625 1250 240551375 240551383
    0x40e100b1c020f03160602030a03140f040b0402030a140312060d1e1506120203060f012402030405030a0b060a08060402010f030c030b0406090204060905061306052208060621 76
    0x610b404403201c0c004440e000300480c1c00e00040d0901d941e029070502c907021034111740000c000c0c48243c501e0755040040b00040d40480b00401e40035190103066800040200d00403650101d41c5c550003a00040564500d500180d482282002c403488128078542c0001c9480300d2860304a022440d0b01074802e4030702c41c0d00f1011682d590150009940001c18180103001c42490510801008070061400109003c2105540361914a0505910744100b01c0c403078841c2400040704804640c01c5c19040f101c10b451400740751001900404030a481c5c3c10308040c2144001c0c00000342e03580d0f0800074504c6840c0110380303059050070944240204000c15804c10342d903c4c1c1c0504140300060741c1c0900105010f400d80d103000544812014003c8000e0300100180c9907000d8101840411150078940c028411200180c40e0030b500c260340da10500c8124068041d4140c80c800c180e443c1000018010001800407079283c8490b854500b6000c071180c8010880764001145640c0440c0400c122400c1c012417492369110101c2c42180d105441d84515956 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 240553875 1250 240552625 240552679
    0x4050a0602030907030b0405030304170c0d2007140405010b19180e09010f0e01150306020a0c02130903030b0f10140408030705100c030204060c0305070f02040e100b 72
    0x300c81e81c000001072105030103011030380c0555072110f00c901084c141800c000741d4030340060f00c00307943c40000b110514120311000c1c0115840d803c483c02c05007000340c04100040d02c00800d030001148180031010f0310400741c05001d00501c4090440010b031000c81060326010b00045030016001b204090504000c12a60300304031244800140b119490300c1c15420380741048a1940c0f06183c1d00c241c80c04400f101c18807284c2301064001d10780d00104074104000410221652909840d1000c2c040c01d058240c101090000c070350660010082c02c106409c1640000000f9808241d150b0784000080b40000d40da12030b80c404155060241c485000390403250f2211110948000603d002034104d0ba88040c040c550300da440036520304030140d5006250314013359441d0011418000d89034401c0060819001c0d01d00381c00081c13403a010740b09803002da070099902c03400356102c3e41d0347c155065132121000785c030008007130a5290700603516405002d50032000130004d00b070500c443d0140c0300103171412001424800c0c25005c00f0030420842900d10610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 240555125 1250 240553875 240553883
    0x24031103030418090c0e0c030a05060f010c08180d030903050f031201050d0c03081b0114010b0301150203070c0909150b031f090f060501080d020a050c040b04021c06050f0904050a 78
    0x41201c4d0b1442c005507210210740c403c2442081c0f0004001c4e003017024002543c855207086000748a159603610030086012120103a03103010a0380d5650321008211600d02401c503072003030321001030024880c0e44002076045401040440c000f6150000c140100704052000340c0750300c40c00800550074a1b42c004001090401d05000782c0f40524086481c0c0402d120184599000540e000407503a56140307114032060b01262150f5034946040d42c24001c40c01881d03030b05601882e040f26103150a050541e401e0003041c4654170f96120602046200a10400300403c140c00760500082c24148400034009185140030104802110710302000c41c1e10b00030800241d03480114911007000050380c48403a4020f6400c007005c000744015000608010301340c00500040015507405281600c254000711543c0d20800141265181604a00203100b9081301c080000035044c190040460382c500248054280f034180c0c08052440308214001101e5292074540800c080c0c280b80309090020f510070b0383d040d5064036054440740e98610320008014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 240556375 1250 240555125 240555131
    0x20d080601050d111c06092708090a0e0a06060909050709030308061309050c04060e15040c090510020c040b0102030a08150402070b07030b032406011224031103030418 73
    0x100c4d528508000c40c1e00c0292140d00289075000c00c0c902c001e0080559009044000c1d21301000c4601040031800c0c90024010010038014401d00c903030381c810195030448041d1036044030388980b010495800c240416441421008030006074245000030042401105900071624940b038081071000040e44500c4c4003080d26014104158a80c07145d4000c01c00d44c1c5c4e50000c43d172454070300c0c000c210010054007064203245034904072401d000058440d580b4150407080bc0d02c100e1400c0c0002c0c00b1890941c201504590704602c0a41452000b060781e58020520b020304070070386003005030000c040b0f8402e079103040d1040868844080c0b0082d030034200445e0300500112001742c8070200e076400081b20f00b0340c50380d500d80407244100d40c80700c0760030f10a060100300070700030b4a21921f115201e8050510b104901049001c1030355401e02e040201e81c040c5442d01d03801540c088400c0340f142030078507807200c0f41d196000051082d007009107850300898404461460401002e01c034181c8c1d00080c46070b0800c000c10889209086286120031240c6c42c800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 240557625 1250 240556375 240556391
    0x30c031116090b030c040b06071b03020607050a0b070801060903031101020705010c05040812130302011d04180201020f0714210118060f0c0203161b0312020d080601050d 74
    0x901e081000c03034000400c0110208081a203214541115a140c40240d04560340e042c00b940c104010744405d40b243d40e40000c0103020326000700301c4d0700d50542588000045640c10040d141e802140c501c0c2e10001c0e05444d00d41c8814080760400148001d4a644001c45240100071541882c10003011800f46110140411132020f034030b200e08400c213504840040358441c0080081441468010700305070040e00c50805640500301284075224105001c41e1010411560300704e040904540c0117480f05643ca8150355040b440350050084c0c20703103032445040000c010030748401e010080c2070700c0024540342e104003401c02c3c142c000303920130061405040d040c00b04c1c44008854041500749040c01c4d14be42d0300382202e6242c0440d0b0130f00b940c02d1100f0a4501c10780f1481401201c00b8030860704e20414110503500400786441c0181c2c020030254a19a00c11104407507100d00c25228080c009050303039010411454280c0003900d540700a40700415030a6010811124007811038105001507103007800010f06180144521034110b0340d200c40381c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 240558875 1250 240557625 240557657
    0x70201021204031a0c1809090115030c080712050a060e12030403031d03160b070e030304031101110601030c030b27060105041a03060417040e0906040b060d030c03 71
    0x950708500a020041948032540e03401d0445254030056000342c058075501c0049485207050070300700e0b0252108030410880ca03802c03a40c2440351b181001440c812145d540e0350340c0c4069441c0201803c40056005052004030142807809581c180600e80e8010704031241e040d18900e00050707000c202d95640d40c1d0080d500068a0f003030014400c2c2044e068902502c8004400000c100425130541e00149005005420b6005e40204e6800407994034415041c80302101d004100800001503085850190b02c1903103403801015405043c40841d15542080e042140c8004c00c01843e80181d50703100320100305101641009000e154559210500d03080418000039020b43c61801c0041c0d0022000030280512180c01440d03420682504110756444007400e0081c1c91189080c140740d1984075440329410074800c0c4000700900a80d4580d42e88420607a0400750010f0b8501d40d050000282c1c440410323800c81e00c688000b01c050700440c50107103070896040500a0540303208418401d054000710382e000d4588a0346960500308900c000b199a40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 240560125 1250 240558875 240558883
    0xe031e16020907050315090c07060b0f0604030804030615030206070f02150a020a1109070504090902040905060c041703030c030703020c0f160611070e0c0d0e150603100c0f0507020102 80
    0x4080d401c086601c1c01c3c400d40307683c400011072041c0c41071200d805600071030200704446d610040d240145100010722200c404142d0a030300690700c0102c000c280c28800000c4501140700c90700940c0c415100c801c800705040043c040c260180300310315180e0400c1503403c0380c111b03400130740107014038000548660440d246407002c40d128080d4600000c003101c0d48094071161261b074002e544451a0000711400840f200081e041170800600c001e004201949602d4201800d000700100240f411900070703a449030310762012002107401407000720302402102e5426070b500c0e41000f03800c4ca03040c0351880940e2441c0e4410030401c84101c4803401078a4102080f8500543c5e2003098000f41c41c6014031481c6541c1060042030b0760b04038640c9008501700c00312640390325142182d070b55284c0d03219121803562062840c025145000030310741d42d1601000b002d0400002100141c01040800c0603032420100300d4130301d4102100101031103440c1c50200044650700e4102c15003844113100001e0000d117050301518001060003070104400b421680248 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 240561375 1250 240560125 240560167
    0xe031303140321090f011a10020307080a021507020a05070605030606120a020c1002040f03030c15020f0421380c03041112060c0715020a11010e031e 65
    0x744034400822010030f5284440340b01611401c02d9442207a9504030090018043c2c5850112002e007081607240003007041c440c1410b9081c6400b4214041003090000017200b20001d04048462a401000c229038400c0940c0030400c8081d00280079540418040000a40d00150080a07034045180c25a01ea0b200c106c0403402034090303258400c0390480d6907403c118006110380c0c040c14510f40c0810448404881c1d00030204106d1299008040c0b80900c00a410b00100c0e0042810102640c070642c0f0411807000c10600c1d02c0101d0304415202100000c00040400090700600d0380401621282030716810700c0c15490392200861100c0a10000a450901085040c0c04040f0122100701d50b01d120000891880e1440c0d070803020b540b003158200d904e05220240e182150501203040c01290350b40000074000b40e1507110041d02c00390410102111005080c0398004c0a622480c00a8412860359072a0502d0080041d24014259128110048656442880718050f03e09100490030089000180da1a641300316055410507030307d25031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 240562625 1250 240561375 240561397
    0x306100e1027180317060d020f0f060f0d0501030201080c0307053405010506090f01050a0608092406120c06160f020a030b1504020406050711010917100e0313031403 72
    0x2681c0d01e2800d064004080b120300078188060400e5981e030f20000c1021f03160ba00207003c1c0d0401060002c030903050030141c4c640004d01c0f0006080034204a04554540715035804540d03800441501c41e0010011540c024090303e030084400c0c2c03212400d42c94040341c001c0c48d9010300d805019121080000d0703140c44c41c201d01e01d0707240d0080c1c00c3c120201c190b042d01e00b8024043c181c10341c0c0c1c05d40100301f28800140188110b0341200c0c1601c034010000c04106103801012108000c0c0035100110b54010490300072194000c801d82c114000c03000341d40820303203458800304102e04075010300714a031402e4005002c1d20340640d80350030480f00910350b000009041c0689030f00f4809028282d050009400031003a19000c414044011407243c81981c46400c106420020182400140d0145200c0c10002c642c0034040400007078500d4840101a500c10314051161540d42c581202000840007003009482d00304188810300715030705000f00041c400c2c0c0b0714000c52511840302c003006040040ca21020303200c0c0402c1f90340318214a0003071080780c00074058 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 240563875 1250 240562625 240562661
    0x5060a08010e010c1107080c010f11010903080103050d1106060d030c0605011202120307050c0d1415340f21021b01090209061c020306100e1027 63
    0x44100c0c1d0324000d218080700c4c00701040c8004904003500c170001400d1000e0786c410307201610380a2414001135a6a11280c0e4246060002d007410300a0b555009105608004c0d01a54074640d003945941000350405c4207061a820402000c540070009072075001580540091055485c152004c215082c1126281c0d422400100501d08210001514403ca645a202c5250086a2681a481564140641c1c1c0e00c030b198001495500041010060b40c03030312100144a041c0950f5032002085c2c1c5c65660a41400113605020103016681801d000741d440d405007909050b00d01400a05001141c4182e01d0042040040405010440300b031840c1f42000703104001002e4100842180070007540b0354510600c021703410180084d0069520441c0d040c0040c10140100c0001d66005030807001c041e141c000501448030300c44a040307501c02034001150f0380107031410084544580c14003500c2c0702c241800c0542c1d031244c1da00c02a01140720000d01002c1403200c0d00241903002c041e045007001c1d40841d141c2c50314200c809816079141011a00703403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 240565125 1250 240563875 240563891
    0x613050108060f1c11011701120602090d0507060306050f0a090b0301200405010f030606050a030906061a030103020a061403130f02060703030c02070b04151107030204090813090c080a05060a0801 85
    0x40c4c2c403940c0800b42403080d004038408050400046882150748945031000a0f0a1001000004500e0020103201e90250001601d06030b071842c049180104080310032903240d4040042008090350500c140380c040c5c4400c44480c1404000c2c00002002d100c040c3c040c00003102d94a00c98036000c0c0d6030941c0002d40011050344580ca9075001c007414054250413600c11a80071490b086000e01041d0311a00c42c5a068400d00d454841c2485502d000480003050004400c50f001382d42c6801c08100129007403c80072408842401030f0359a58118030501210301c0455000d4424418107114140c4101c60354401d59a0003800440c1407409480c19061907100803440b400041d4000c000012140c040c19890740007441010015000c441c00b60b582c51155460302c5c071130391044070030030307440c1980c10f121003880f4413030720f001010b40c103800c64210640341d8001030200c0c6c00801003100c40c044001804010450034241480c0103046805007007110140c2403d000e0300c1d02c800100591040ba6a6800007140c95842c0340c500f5004d00004402044100c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 240566375 1250 240565125 240565159
    0x2003010510060e27070c1b03020a1205060402060304080405060f090f01020601060e040f020f0a020120121302030a060c020c031b060703032c010603030e0613050108060f 74
    0x7990107401c00081183c42040c120341456441400028011401c034980c402550b040804034078000b501000400c150441b0003004195032213401c84283c201804c02a40c8545144104462000164021b1310600c6881b0081b00101d000891410b40c0550144c071802d540c0e541d0b500d001c40b00c601c1190400b80e401a000b1420080e4030001d00040c150700c1d90195000d0601203207010069030f981d00240b08001c0000c0c43d0000340b8900f42480d0300b0215580d540b011025040c101c4551012040d50041928080140e540d40d44990004070403080c00c06446012100c52490031620156070300c1c420000900422440c6000c0340e40318219281000b48000c0a03400c00c03030030402111a04c800a442d5140400c100e44039100b8115841c3e00030003100e04030084400c0c010705030b5150400030781d002c8d4064520741018040b0714494030b100004080c0301a200082481e00c00e0000900d8a09510340607080103c000102030140d5800e202d03029102d841100d8003010340e9001d08043c0d8150703035241d0016002d02c11000c940c0c9d82045440009003c51 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 240567625 1250 240566375 240566401
    0x260408180402031005060a03090501090503031017061303110a1a07050c060a050a060806040b040330090516090e06010e0603060112051203150a0b0405030a20030105 72
    0x20100068404200308181410041039000a0781c2c0108000905142040645880c80081400100b18200450074843e20b49400f400c40f0010342051302c041e040041040311001c0300342038282c0a0007031030401c1a107100a055044e66640c1005140d45241c0c480d90400e00c0a060103621800b01000c15401240c030013610038505080103c46180810680f03243c0e00d40032440050088040e40d100b405400d008203c235a40d01c0c148800544009800d984119596550204403401d05103c0113108600170700800b02c00b401c20b460000d111038508c06040c81442d03040d0004550340707841c1d8803a00400684010021410103005e00340a424205842d00301403145810150018484e40c05800ca4406059840240c0d240c1c3e82c1d841c009202e4690013100c981341d0540203500140460848403a03447c408901130300031686003c014102004659009980c4501441c010703680d40354903881d1090b6003002500c1c03c1a829402d0515040200c0d6407000c402703078018041c01e00107014480000b4481ea0a44550b000180240070034101201a8000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 240568875 1250 240567625 240567637
    0x30f0c021912020307060206070f0e120f03070b06010c0c0513150f06030e0a080301170102070f060b030f070f181b05090a090e07030b06030c03010509010c020f010e0d260408 76
    0x1740034580d80020000d001040152085103240c131040c4000b404260200d906404071110f5a9110300c480c24007a20a03030302000018110300010303008580d0f5440074108031049081c0144218100703c405851000000c2c4010203043c2200d006465001ca20303c409482c200c007900070b0210308141c1c5a182c450018003c54104820812a05076072810490078001d00302d4161a8550428041c8c03100344100300400192484c010110308111000c3d00060505003181d80310120268034640a440d01d17619400c86d60342c5490705000409034040c800000700b080519000002d24800c00600c94405945186512000a0350070364002101e0601c00e5081460b806002c04c1010b03102d0b401030446640a01c69400010650aa007481800702822100c2c3c010300d0766502e190f039100326200f00140b8054043c09011400000c51b2824040d16000d02c07040c1002042c01c01422200910341095009800a41e0381012801c07103509a0206060040340c40030301e0402e00c140700d80e40103007100809406d44040c405498204001c284140c43c0042d1030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 240570125 1250 240568875 240568879
    0x9030418020c0309010c140712151e15030f14010605060c0307020603060f0402032a0a05070204051e011d070504030506270d0c1e030f0c02191202 64
    0x16124114085404030b01480c0115441a03108102041107580104100c101c003030b03c108030baa01f00d514103c400c075081440030340c0803980300c042d000c00d40c20030416200081c0c01c0329003199804000403140d562140107544460b51200014596070700028480d81c4445040c0005947c0000000a0300000c0307180c8268100181c108a011551901c0808201c600d083c03421200c0d0300000000441c01d0001603004c002440d4005040303154083c00191103490380e07443d42d00142d44104920007050404180070481d80e0025180604001008030040020352980c1da04030045d6a80250150350000d200d54504c216455981d40580000d44906081000014424400503080085107109101500c050300c0b030040c280c40c0c038061400020400d40103000002c000140300006d00d50b10401e240418441011400030803410040c4043d030f18030025209a1b03e550500100b031101000d4088000d00344504c10402c0c0d10010404411021000304000c8604002400d40d5109002e221400d071422003c041d1082e41c441000503a8800c00604038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 240571375 1250 240570125 240570149
    0x1018171507020a0314030709050409050309090610050f0d060302040504080c0114040210050a0e12032703060c03150901150e0118060309020402070b070203030147070b090304 76
    0x144640e840483c00040740d50f81500e8812010602585000290304001c01c1300080005801e000526543d80d030180110b4240071380055551807640800b0b1200402c00104443c0c0a000c030500144207056002046640901100040d5a101d6941e41070402c06081140d1001e540300b41450b080c0414010442c0081c140d40728040003c0004001c10800703422614809c44002c0d40c800d08800407959120700070001406203980c07502e442551414442d000440c44c1c682410384e401c0982c00440e41c4030517858640d0301e40c2c642c0840d00d4413840303104106500199840700c000708403d54510004c0302160070000c008107840c207480c42c0140603105560311880221082d111035140080003660609600103154040c15042400b220700303100c034540f22802c0c01c4060b03028046404040341c100e5801c100c40e00c003099189110764020503540e070146940f541b400c070340c4054040701100c504445144a1096a803000c070080c85858119a00c080030401100e01151081d0850081a0300074140080e88010080e00003004401001a02d510035101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 240572625 1250 240571375 240571381
    0xe0607390c1d010b0a0809010e0d020d0e1c02060703181404050708090604031b0f0b2502061f0902073e13060b1209010c0c0210181715 59
    0x20341c024034081c4a11320703500000300800a50f0074481c48003e684648a0400442d5501207003140360328007840f41a6400040c0c01c008004a07005a11580c43c625003c411200c0405000c4044000501120b091200074403071a00000e0010406005039140c448030810025001c84150b501e00081950380c1c5508135070f40c840c514100010b680f042c0202d44031030054072403000402840c0c0e200d40d4180e0344140b1280050181c68040e0200d800050740810343c0d05000ba10bd0202e145003402c2480c18401c24102d511742d140604c0c0c070301c51031900480740e0000c0c11542c4002d01090503c181100350401040708030075034129040b954000103982d002c0c8585c0c03c1112250003262008900340c482807400c4c0c103080040c05454032003480034420310540b0702c0ca440304003001c6050021034000b98550707071070406042c03990100002500f03800082c0e080080585080c4907280c00c6204a003003041d05c40b00030b82d0000e540d010341411500c050201044043c814084660344403005404451000100440003000240d03131036001082c00055514a5400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 240573875 1250 240572625 240572669
    0x201060609140906062203050c120a0b0a09020406080102090906010302041a0906160b070f020d080c0309100c050d06080f0a0b1510080108010e0607390c 67
    0x1c1070225501801e021400c0d90541c4204184060040c11481d80724400380003e084c0000d4500100b81490005101c0540301451407800905028007908454031506003881030044d410400300307500c9092a8050010112590b40c007074400010400a04065005841c01303101043d014415801405240f5048a001c44e00740d4072200110107070700c038030f0141002441542e140301d611406544050569154000c0510b07080c11103200c00310141c00b03003021044c0c40000801e424000c0d03041d0045082e601d00b8489201401540e401203001400140020304a50180c14000000a980d41024020700c1c1e0715007030b80d09080c02501c50310710b401403058200d40c499000c010b00c2e040d03002510440000e6001c0660030300001804a015a42d16420b411076402024a10714041071204042150394031540300f104125141c0398814a94109a019130071182d41d0810856030707a10250500c50f0f050340008000e995112441c010804d01d0241d072000005202c803125031245910007c491500c10040074001341d0003542d036214203030b03540c61200c3d8034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 240575125 1250 240573875 240573887
    0x120f23030405100608211b0120070c0510021e010b10090f03021903170711060a23070605090c190303050906180603040605040c050103090b0c07060b10090602010606 72
    0x80b56091582c444603942d00842210b0b040100c103054080510360070407298034807e0300344c0122081a0b40c280c1c0d650b0051710b0030100818221103010815060b54138182016962800030031b0100c1d00426110b041580c88640d4072910130050b100f9208000c030780c41200d1200303c8501502900c5180c0c1894451640021801401485900c2c210119031a0420311242c7c2451602884a101d9188080b154268907141001c070100e6241000401011801c2010f240c0d05c052078101140ea10b17608080b041d1158500708032003243c0d40e40c09807100e1045901c1c00880c074503400360711110a0302e5224002004010504190402c4006075000c506ca00340880140d0b0841c180901000700400000c4440c00300802046040c007004a039814628040c200d010040d422400381c2061480000c1c1103034000f2182214402d413500c3c1007004116200982c200101001c0c282403083c0c000660341c098601e0f40060291130744a201140e2403040c042d450b040b444064001414003801c8191158008010301c00c9805034a025600b480b8001500e80e20480b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 240576375 1250 240575125 240575129
    0x270e070f1508160e0a030c05030622030f051603080f0c120c09010903060905100e0d0507060207050123040308010b0a0921061a03060a09120f230304051006 68
    0x180e14000960f4900032040c9211074482d10700b004105040c01c48184da0b885080460700918000c441001e4030518200070107181c1040200f82e002003034000c0340320a940300c510007001014660315040131440350342d848008507441d0045610807040070000c01201d03401c0c1900210902c2c0961900c1c0080c086955a801820765140f0034580d4691000075641c000412251804000d41040720052603c0d641c001d6036612918250303011607000707075800c0d0011070030021242098407990344068a00000b622010300c0583c000b912a001ea0304001d40030640001d0038808001081d40900c48030400c425188590300507184445000302d50403503003127002c200c51500206014100b10300390749028640da5280000c041c180528403030607004007141114520881c0107500002202401015050b4498100100c1980768000805103403a8001d022500c403545000581d03008101040c2207010202140d0401c4400e003928401e045440840b103001c0e0341000c2d903105028150f540142d06c002c5019070300071421a080284035000f50070441e0a18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 240577625 1250 240576375 240576377
    0x16090b01030b041404020d050f0607030204080c10020c221503051014060d02030102070b01090e0d110a0b0603030f030411130c120f0608031c050c0f04270e070f15 71
    0xf00c4c1c0010300603d45050101070f05440f036015900740c005a00c0141c0d217041e205039803007004242c021a091000800070031049035407000880703285059040b1280069206d0001442243c05520030f4507066107440c1c2000340d503d0f1603500c40304080040700c0d0304400f5100c40039a5400112141d0040c4140412021441d000d44500010700907107080c5192511410040848100e40c03041b03800d0354090010802054030014014020701201d440071511070341012081c1d09000301601c5400a100ca03164200680001c001020046940d03c040715443d942c5030320000074514003d0080c042d21802c000420001040946150070140302400d94031151784180640c01041a0340e400072070780b00020603800303001042c0201d03a040202819180d0000040d43c0361030381101c608550102e0700602c07c2c440d100c0100c001710b40e624816542e1003c0d0200720a410142d07203e20a80da94841d40c810920a00c400031241c1ca041c0c0040702000c03c5412444c01c00b00081e914446145403541c04500c00c90035210700d805800280080000707400d22002c107203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 240578875 1250 240577625 240577661
    0x30c0a0e15120102070303051501140d020c07030f06020d0510030503070f060b100519030605091303090e040b100501080c0d180b070908010b0d031704020316090b01030b04 75
    0x326012488440030a8180990207068400b410080c40420310041401c01d011b03507404140c1d840c0c460300b00c00580090031441410419403081041204170b00750240c84c40c200c202d4101694517088401c01c0e070b00e0f0000139003010b84007600d4100c880080004d1a801070038060003010040c005a5104680c0c80c03440c501714407010b80b25800412160000511841801100074400e43d000949041c0960100d104c0101ca60030310000700d40001003214500102e41c8040b408200d01d0716061240318200b80128403481406030488a00a01508040301054010b0488038040d00e14118090403e1a085c00c5c1a041440c007500c102c40030160220000c5425442140c80c1c51160688000c0a032400760b03207543d040010156203500d0700c0b10710441089003000844204445000d00840c0d507441e00c90034240f000a41c210384185096a100d1010281f11000086d00301318049460030425607078076015503542c0086810110b001d01d9030341046001b9480824000f589a00c0356500741000e03a0b041040c840300c00107020455000402102c40b00c01c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 240580125 1250 240578875 240578881
    0xa14150a111b1c14011d060f0412051c020a05031509100512070503030a050304050f060403020a0f1b03031e030b060301031b2705131a07051c0506030c0a0e 68
    0x403c040400803a584698190b103014448882c07101c0c2140c3c030440e0b00314046410445035485007001000000d07001440007001001c04d00f081d9641d00d170303070903020102e00c1e081c00b40c08980364410b81505800c9520740035040406556500c4d40341c500505c0780c0d000b1030300289840311031141900c00d42003042d441c038460234000c4003081903030741000100050030585940c000e01d00e20500034045061344040c005040c100d00c0da900c4651716401c1600c0c00c5400e0000c44c88680081e644403904004c0443d0380042c2070503c0540200e0010074404640c144640d40264018050b01254036070a000010550f00051081d0100b94580300810403445840003101620b80c03403400c05601540c240014008241940500502070422900ca0340360182e4a8050a20107102c107084400c4061940c4d1402d1100009405503540c44a800100c40040e048180c3d07500000d0415010b00902000d5000c00056043d4080c500316002c48201c104025145d122000685002e0403003140d078680240900c0848030310506210901c5400c0d12010012490156 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 240581375 1250 240580125 240580159
    0x80d0f030e010906140103142b050705161502030a080105040e030903060408030610030b061210050d05070311040509030d0b03011107120201050c03060a14150a111b 72
    0x210001e4109560380d055000c001141c0303115200c0001e0242031450510b6155003800f002e2003000300203150041c6c11084a04803142981c41e06241c00303c0d410140403200d607414003000c4805001d10303107000f8503c1c41804411407020083c9100c1400310742c0645001c43e44826482d00c03c0381c581c05a001154003044d1807000500c82450603030481c24100c0c0e2101c04603414810400700180c5401c03402d036802c2e100400000144007240c245558024905080e0341001e00882000001043c03552084601c104841d512036004902100285910407000b881d0040c0100c0403032401e81040c944a0406202c201d4500c009101032600d5424075000d69403040d20200b0195040881d0816160090012201784d00d505542c2d80c40c090141000500203031403040d0107440c4110b0749400826000e0b086400203010f44904c41c01c01c0c030400c2851b03030340c0f01e06040131303100006001fa0500c0300030070205061002826107400c1c004400704810055a6005051080c1501d1030030854400b054107140381070520005049047d0802a103c060321950 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 240582625 1250 240581375 240581381
    0x703020f1306060f0f0806010509010e040b030303010b090a0906060801030807060605030304090219300b03010e012301030b0a020a0e040f020a260708180106031a01080d0f03 76
    0x140d038060001d039001c01540200c202203420540104001c00d8007000080d00742580550502c2083d090383c1010300f21820300500280481c010396243c0e80c10012505e5030380c0307107613101c2d90051001a04043d046035240e585880440c050b54102c02c527014016103404400040f940558040d160859036152140062642107842d03242080d4860b803400c0d6036042d00c1d40700c00116618100020001403940130340060302e1300c0039840c480c019001116210002c01000c50781c4040c1101c0c1c150307074155015680080c2250740b002c0258401001e0401e0f03244841e410b520303250720750302c0108042d0062100020b8640d0420501089020385061070700f02070201401440c13481c00051200401540100070711491410019114592100042c00b07903400c064800b201260042444811650080300c206000300c1c5400050700c0310284540d10543d4980c0040c1104100704401001c504004e104069542914111000070321880b91a800c00d600480d0400003078035a20286c080000802c9a00490203542d25421561001d201f070480078011405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 240583875 1250 240582625 240582649
    0xb091e070203120c0a030515031b0f03030324031906020304030c0503070516090b010c02100c0c030c030b07110d0f1e0e0f03070513110409020a030504050c03030c070302 74
    0xa500c0100407003c00d190301c2550041c0300e242d60b107080740e0b92031032a10b0008042d103101625650a120210700d150201d668041a42000d1048101046040614550000c1c0b000551464010342500000040c0401c0680b201c10110310581c0c41da00c03400d129040320061550362010200301000340d54035010340b00000f031040c0c2c0003184c00c14041c0c41c2a00c0081d00b01d844050455102da402110036a01114480c00900b0300480741d08007c2041d01c50800c420710202001a00500d04084024440d00507404030051140c01070f102c0d04103098000207200c922546910b4441d000c03594074001a180c0c00c0c3d0710030010300b03aa4402e4049513242401e840c0a0710314030b0710306e44d02560181880c1d000c1700180401a07490b0300b44c9090f00d120759032800f46140c1e9507c03400c120704018041c1254551103000d00a070050041403220fa202c100e1441c0040c400701c0000103840300040d5010507240210303000a1038450001406607181540764024501a07806801615814400441019664491104a40b1054020400030002b41c1b03811540e00d50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 240585125 1250 240583875 240583877
    0x1020d05070c0b03070f110d2001020f191106010614090111030d020d1503050d11011b0801050405060109030b060f041e1e050106120207060e0703060f0b091e07 70
    0x350b50381c803040004159001201c03c00c00250f031b095801041d0715482543c0d000d81100320b10143c00c00a5401d44e0040c40c0003d8510307c98a0042c400044034200705e42507040750402d13807280c281c03680c445980c00c85075544c03008c079541041c0002c0c00700d200c14001000e000c101340d4102c48480d201c4503007250406050b91459000524810f040c0f011101804050f07150600c010450b42d82c0312000140e0b22405661b072002207070070340c2d03121050f620f925400c24000240e0004400a142c201070424400c030b81d41803000c0501515041c4200b84090769045d5032141002d4218003200d05981084409000b2070b602c0d1401120842668840502844128804140a804c00d501c550140030406003020030503c502020318501c480c641ca42008005584229680c907a401015000e0140c401c0b8000c07e002c15490440004c0100c50380c400011002a030010b0301104000055211024000452068030021503407404c0540060865004c80e603141d50420105440a1900e00b021501c00c2040804511348000e4208900c10070000080402d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 240586375 1250 240585125 240585143
    0x3070c0b040518130609050129190509041b0b0d14060f0a061103120903030f0112260912060a0e0a0302070e0a09020607060b0f06040617060109170604060c0203040501020d0507 77
    0x40420200c0c00b0915279480d00d200e020414481d42d0b9081c40a490552003c5000a0406503001d100e00c1c0c1d00c250a0039001a040824080320300c0c45900c40080d410410307070041da02810f000480b021241031507048000e2003100000101a80e544070380901908406030b084040c0e10164522041c03110318000c8140d0715017200480c048904125242c4213803030405800f0780f9a40b0f065030000c0108800c80c440105001e0143c41d021940401e041c041e96500340e20500d10940c411085040d0b12034402c4103015101c1901c1480c00000e001100e0001040e404540318081074884000180c100f41d112405502e0000d08040c403198194000d00301c1c60f18004240340d00c0c42001d0300d0681125210798120025a8074000608203041c0101070000f50520407000704a0000408000c09006100510041200b0341e04040818903110061030000f809958000040310241c1180e00300894041c3d02c0d05266085250009940d032080d849110308103c02c3c40880c2d02aaa6401144105401070384180003840010744030701c014140480c0305004003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 240587625 1250 240586375 240586391
    0x601051e130305010906050c16060504020103020d0c05030a0606021f0b0411040314060601090311040c020a02030d020114060603012103050904020d05071b0314070503070c0b0405181306090501 84
    0x440c0405940364010343d000e070b4481299505010315442801d400c984880940d41c40c0c40d15004000d09602c0448402802d860394500c001419a4003a4040380e0b200e002000d010041074000d2813001d07003507400940b150a240351400c02c003c1003aa000103056a00310007624009aa40b0f4003103a4504040c2c60f0340c0d1100c83c5c105440b400790020405401024001843c0309a0b018030314240982000c5107050300c010121810013500030020070120300400d10071000544207842c08a0300000d800410ba20f060303204c40c40290103214210007840500d83c19031280a5012081080107126250601040f9180c0028020020380181d141600c3c5c0704d401c8214910002903209080503824544004000f90498000c0e80c60044001d4445080003040c40d4041b400c0020650110000d01450000b51401000052114161650003000083c04000e010040082c1ea50842d4420b2155005a81311508845503810503ca2180294405000c543c0d08281040a051061690a40c6844030107200d44904c0d02404440009550315583c942d09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 240588875 1250 240587625 240587647
    0x109080607051b0309180405011d03090a091a0d030c0501020c150c070c0b0d0f0204090c020c060705150c28091e03080c0f03190201050105090601051e 66
    0x22031040c02207407101a1540701c00390b50418295144068900542c2040208000d195201011086046d00036100107000360b840e4944503004281e1250794018090044c402e207110400000002c0484000903180700c00f1841d0364000e828141c40c2035004121082c64800c0085080342014190703401954028901070080c1c1803030703846403822648100d000000c603402180d4140e600801d40c02080b07801121104200e407508030641c03222200413165000c0e0301c0142c00006800003182006820840e00c1900303900301190350326901c0d520500189040280140940101c151820341c5280201c1650442c98000010f030400068407480c844180100800c00450401c0c00d0103202a08070741640221000000c032036290309a441d2241c00136143c054203a00402000780044000007070620300c0038030041140e0748502541d888100611502d4140302c0321803080141c030710002c904a005840031350103840007540c2a4000b0003061b40c84000344080c114049501501188041040c00070785c02410b1480e1101031500b2401d00d06100c4074240c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 240590125 1250 240588875 240588883
    0x603110a0c06091a0a0207020301050705120a0e2107020907030e1b150301030615050a081207060209040e060a0501090501030c06080a0e010c110609010c0905061e07140d080106021209010908 83
    0x50b00f040380e59401b29147d0110308091080640101442c201981009110142e02c0300e12400184001c81450300d6512100d180502001412018602c12134034141800c00316802d90207640180b907003a807003100550702082200340a403080b0b51300400c20b6009403074480100040d000d21b0702c034428003940d08003000c1c0c1c50401c0c5010401010f540a1440b803007000c51815400c04200c5154481508200d104480c0e501e0108250100000c1c1503000c2d07214103440d1501c41d450b0742403510080c002c0c42107031070304107042c40e8140b0324010020950a10411002d0410007450f604c03414078070304903002400002c0c50070b550078000348010750040407501d90080780311030301040e184841d18407a8250b41d103411440740070a98080d61001182020310400d6413101000b4001c2051000b050002800343c4590720a841c081c10f80040c5024201f40ca100641d007983e103500440540e80d500c0e5140401c1d19511150884c0654040c5000c41d1030f60034403a81c94241220350300c2c1d0007402a10390350035040b00d071541b180c01402d0502078201400586000d040c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 240591375 1250 240590125 240590131
    0x1809070c061505120c0109090b01020f060a05160315090f0f0903030209100806100e03070f0b04031e120302030604020c06010314070f0b070b040611130603110a0c06091a 74
    0x941040602d4a09001e10040c02080c807403042c42070b00040b01440c040d903407081c1841c04a0303492010201c0c14100f4400183e081c000c682c0350500301d502a400800c403154517607410150003103001d01d42070100b02c019036100710220f483d0030341052032550366408104090100398010601180300100c002039014481e03030180c000c807019070b58220080780c3c000c0391140f02407600c0d41d040e0284c060141000f02c400e180600001700c405102012150070b1104d45a035080b11610108200400392a07001c0050100b0364584041031035542091000b1240c07408100440d80c0507070300301400910203a80c480164202c4010300b800070b4010303410051989400990a21804840c000200443c42c000c5000704808422000d100003c2c07410010075800c01e00c0b01018401c0b00700000300e90202107425881c0c1000031900c1d1a16545400300c044e013810345040801841c049504000c000001d1806d504569440e20f003000404400001d0060b20700801e001e00c00840e01ca11106004110b590304003004141c8516000310040c6400180507038141016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 240592625 1250 240591375 240591401
    0x6041e0c080a02040509010b0f0c0607020622030512070e100e090108010b0117040c030b251e03020f0c0105010b0301170c0f040e0708030d090b06061809070c06 70
    0x352054030100c40d084a8100d0300310340080c9003035203024100700214550603018454002c0c01c000003d10180c0542c1c040342511b1500c22254107443c0d0303038200000025503441d420703202e03141e0b480b0382814034458944034249149003c0c0d905403075903810300c492180b00d003280700001400300003480000c04100110f503803440e0855200c046d00d622000000d201e540d00b0f00110400503080b07081300e0b80c5800050841680c00215600180509142003840d91391140b8000c10140c2c00ea500041c90031446006105041c80414640c0c060a070b442e00760000f0840c0000300c110f070700c901d030502030401d00d0351540c031610181440390300107151040c945019240340024200c00300d42111026442483c6582c0044018400c0280c0e031503294034032518000003007c610604074000b03128554260000d910481c0d44420512001d1014045503004140e6942079a1310340c5503c0103400058030060300204c030003500040024035030745400300c203540310829190b50800d1580001b2047c000400c0b009040f64052008035a000070000d489030089109010752 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 240593875 1250 240592625 240592631
    0x213060609090b030703050309100509090708041407031101110102041d09120910051c0f0e15150111030408070617071d060d0e010203040809150c0303010e06041e 71
    0x3500d0041011943e010703010b180b02e60400041080031138000400d682000c3c600300c034080304002d100002540d840c4611380c0c0c2e00341c0040c041d00c1000001c03900400b0061060b4001c0010180c0110440a025140c0250380402000e0f400d0305080111705503c15415020b005105000042c540b45d01d0344410107544070840c8402c04100d04400402c012160103204e11041c6400e80072480741804e081900040310507402d00501000c200f00070480403903840c41c40315400b1000b60000c10401c2070740040e041d5000030300404140c4001601c1122510843c0217101d002a500c0341400c003040507010070b503582c01160035948400c0b00c007503603110900001c2040302c42400820010045034840d54040c00c9a03001c02450030800810076003d00510070001400711401240600242104640942d070380c1c07403002c0c0700b040104021503d448003584040108410040103000401c1d0320b0030300712040000c024400e40c0c07004940c885d8418145041d081407004000804d40701d22a1a040300c0010008100c03141808044c400c3c910b414900340b800192 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 240595125 1250 240593875 240593879
    0x30102121005061c020703030906090302010c080903091813050715020607080c0304031202040b041d0f01120b070201110d1a06090a0513090212030a0905030312010e040213060609 78
    0xc03101c8000006040640300310341004c081910300b402d003589041840c1441d907000103002c401c05d8403960000304581e60140d02000400c0d6203040c000d008010342440390010884a0001c909040c2e80003007030340d0030b05000030100034280e03525101111001c1070140103c600c1c5000300c04001c000400600c51070740a41004a20201043d15150700240340820140030103082c00420b0040c0704045c6d03a00e100701c0341c1c0709401d420710000400883c42c0c0e8000910803513000e000c6400c2d02207070120740a200580300b905442020070030f010740d41d2140348801d001d0300b0080c465850420f088042c7c0000284c50080c01c680d001c0803a0000080c2d181002041424683c0024002c00c18180d4455240482001241441c88aa401555618141600781c40404c11001c9140142031290382803280d441580d100b2078201e8003902e640603010700c401c0540e003462182d40c2e8021040304808241941001b0a6a0030700005803140c1e0400d032034070405164030300145c1c3c0464800290041e13800c09c6802d20780c2d1512800a005410080040d40c1e40c003442c81d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 240596375 1250 240595125 240595141
    0x30302031207050301140f12120912010e07230307030b0403020f060601052d0a05040503060a290402090301150501030b091014060403050d170109090b042003010212 72
    0x1d03004068a041c000188014000464071015114450310255100c0603003911460026071224440b01c0000c50710b12806110440c0748110b8406094005020b036070742170143c00081549801c7e10f4a50201c002d1b50751044000300100301342c2c05814101d144c0e003001c0080011081c00042410320b37003076801c191522491117040c04109079041012414640300b0001801c09800d041c00020100d1040c6c0048030120020003c1e440041c46071000200d01e80b1004524450b95619900c5010b8a203801c5031080610038010000052600c0686004885075480c2c1287c45036003042002d0a00e0020440a45200380c1050742440852060346003445403921940220342e840810a00d4040010103950700d42085034002e0710490148160150502d0242d000e40f080c2060030100e110b80c52001c0f91071402180c2c005440ca02c21007001c8802250011041d084039410340c02502d406a0302e4405038000c0e10007010b801441010b0f03541c00030300451582304880c8182d0040380400c404640d0280002401d83e001403904642105d0340e03c090140031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 240597625 1250 240596375 240596407
    0x105070f06020c010b090c0a08070e032401050307060f0203191205070809120406140d18030906030b010e061b01020d020403050733030c020c1e0901240509060f0403030203 75
    0x1002c05000310901c2e006540100130014a00900080d02f80040c04040113801d58090007400844200700c1c0d01c600c8107018002c5d058506070301c02e208050103802121000302d06144110800c000e000e842390003c51511700c4400c0d400f05c0030850b03080300c98200440f10b007140014190f0b6003c0e00c0d000e1003090ba1a00e140d418640d807058201400c0440c01c211008041004002c615007004070301e44080c100c40c00f120b8850384000d00300ea000d0b24000302c040c0d007540540c0325130038201a00f103402d04c020750741c4070341d0b081240314100001507410390513900c0c46641c03011060200708a81c0c0c103e452503030202e0710f03020005400d00c07080346105801e070b800c03e4104980f076801030b0106000c403a410340401010810a50801e80e80c2c1c65020300c100c03040504c5082d030356041540f203103009280a0b000700032400c01d00390b018040e5024801450000810100034003a040e21a4440500010300b10060001e2018591110030244803260100e40c02503807158055032855800c4030051001140c00c03ca180060401180250055035031a5050750304a04a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 240598875 1250 240597625 240597631
    0x1092105100c1d0a0302100f0806010801050f0405090c030f010c110106061e1407110f010e0a0b0c01090218010812160201080a02270a08070e060105070f06020c010b09 73
    0x250500d04007049501d5a4030031040800d41e0800300044180202030703c0400e81c442040d0304081e4100113429a4409140c1d4050303032804420b070a0350f80e00e41e060707200c0c0d200451300503c0030310407140d2092810449074a94074240d0706c01c541100d58038003141d10310345075040841d0070400c1111410425941d103a03d0801c100d5040546841e55000d1079008021007424000040c00421503c5201403480500016000c012809800c1400b40d24220a481c1501c400d202e2420841c104210402d4900031218050b02c24520b5000741c5131a505200d0050000340880d060222045003500b0043c2c944a9664a4000300b03400360f00c81c0300d41d80550500e12594000598100024949802005c16020366040c2c0100402aa041d450082101c4a03d9091905050390b444030307070301d00000c0d0081c465000c00092001004080c1c2e40305504210701403c00030307603900348010303a0b1361000d98403000c0a1283c2030000424200180080d07104500401c8805e11540f00e0900011494456030700700c1e0448100d10307845d43c3d135504c8001d40626043c444564 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 240600125 1250 240598875 240598903
    0x71808030c010c030203010f0603024b16080307020a0b0a0905012d020904061701050105040b0102030708030a09230313140f09070e12010b090603010c140901092105 72
    0xf1442d40361122300504905148500c0341056804582d64407511000b060b10541107402408042c0c040500c0300c00c002c00801008803480e17061540d0810020900005016500800c030b4600c5650000f03021900c0e890003a03800100903a04500803a0300100c001603410709070a01a52440c00d0019001000745041e5086911029000308114100f5884c40040f8442d000d2490061400c800003584422078400070030058004c40d00080755096a042550200140c1540164101c6100300c3c0d003130201000000059889110300e02d0085c21b000c0c4200000789411030360b0f400990440e03200d903500742c100c0e0355030310001003a041069041c01100c1d08000745044008828845001c00340c000c40b810a5003407108070340010454591420301c1d50180c03c0c440700085806009802c810321064010b0900c00c520f000e001c2d0454000c0292a074692300c00d10241020a405040500c511443d00c51241c803400c80401e103036a07080140360030080205040241850f004121036010100f010449180500700703000d0358600b40f405500f45003100c0160b41c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 240601375 1250 240600125 240600127
    0x12010c030906140115030e010b0409060b0906100c020d0f1403030f011a12191d16050a0302011112070b060913030806040f0e03070f1407030209010e071808030c010c0302 74
    0x400104401744202e4146442c2d42000a1000b421062460151103011000d41d0700c00d241944020500880b50044a964001140d001d0b0841c0e03540010400d4141c050213003140002c54224401c80142801582d1440c47e40c01001d418030401e01603a6005a0801c02e00030035040c90f000401840869068280058054249140c1c64503085040301d14045283c02106015005404c040010a0140c05a40e1401c21001e85850040c002d030788081c40410b0805450100030091032140c1003408128081c04c2400009440c0010240110305285800449040004207881c6805000d407a148592403401c0200070301e01140700b01c04145c1c06107040d02c100300380002c0040904605074031280119000903030280360300d54090811100000c04588900740480100751960718403000348000140d420a0141c441420f089486c800e1891221000728860130300e844510900c4002e400003100303c01402881c905004444d071142084c98403840071032191000c803041d03500c59841036083da0000640c1c86500e43d428090402c540300282015 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 240602625 1250 240601375 240601379
    0x70804210503180d0203070b180a050a0306050618040b0106080708060321070503130f0611030409021b1902030123040209090109080301060503070915020a020f12010c0309061401 78
    0xd15143d20480c0e68800030700192041c4000c2d50b0303a94030303c2c0610568000c0d08030341c85242c03255070140065001021154151401e1184002c0510b0030710f02510540e080a004024144c1c80c0d0b58030803001c0d00014220f0707640300310b00c804203031501c0740c003442124802ca01030f003294a1035501d00100500340c508060004802c00880d0030800c0190b031400185100110400c19500b18000b80411140b220340c05600d40c01032280c040060608d032281c00c0110030005451906201d420103540d40d400030b40c0c1c800d2000305a00540e4005020403c4045065070140070301d40c5110f110710074052a080c0300541000c0c0c803400e120189502c8602e402c13080d41030910a010070804032141d40b082c50b40ca0310042800c645c000500091155004900044655800303400050005502c840d600b40c90f940c5481c00503009810480c0e4000c00603500820009c3c0c00110903203d186202c0d4182c0180c51400300c40c0d001c0c13002d40c00d01004440d4015a403506400002c060912841c1540a0f46580c0014502028980f003420381d1010080141981c05101c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 240603875 1250 240602625 240602633
    0x1c0306030b0a090b040b0405030c0312100b0705060a0f0b061209011d070e150d03081608150607030306180f111e0c070e01060e03101a060706090807080421 68
    0x4c182e001031b004000d282c00c994403840c165145110313420110302980070101701038042ca00f07509800c03030103014403403819810035444901d4851030b802440c0c8042c045a0000011a06101c6a5400301c101c11080c0000403469901a40c04940164041083d080701c00c40e2950400c401c4480030b1081d80f1025800d113140d0002c40c402041150341c0c507405401003110303200c2401d001c5941c0890840c8170b59181c40d0094440f004c00c480c607041c0948006000c0391200d10300c4041140b0900010f07c5000300a102e4410990302d000b800394130394248803894000c1403084041c50355803040494883d13000702c054101003140c0080070440c0003640b80008152040403d80f012403000c140000f01108010048140c5104200180b01c1c0c0c031010f049450510341011036002c403482e401d114001084c0f09910620b84210020150200c1d056068030385100001c6a081c049450070b440d54440040354a840d01307000818403940109001700300c1c90710300c0d01d07505182d83c400007080303c40c1d540001313041200c00c0d950003411001c014202405c0d000c12400382c507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 240605125 1250 240603875 240603893
    0x1502010f0524010504050a08060702120304030804060902180115121406010f090902070302030702270705160c0e1f0b090f0d06020703030f050a060f09020c1c0306030b0a09 75
    0x4a40c448207038021840c403010f648140309990040000078011074403940e8401c0320303544946080e00d03403100601425080c104a2107030f0008030382c0500c0e03056580041d280c7e10398440c1d9004000f01c210807648810724403150481d040702c40c050075001e8004034880c503960b001003560203403205201c100358280c158100703900c0000952516082541c040f4081c20300356260850081c00729615082904100304852012600c9c005050f070001c09404000d01c251040c1f200d080c42c040b18070200006074020700100001000018460f039100d84040c1c000c41f10201d2800b50361404031350f0780106000141c0c10011400040f8810031022001070f008411996500700250382000703090107400701d254415008010701030b81050714026090b848121840b14038a4000f54215100c6031249030080141510741944c448650402c00420160000c9210f940300b21450400c003041504d00e403c3c5080b010b0b4009184205490041c0d06080e21800c6078484040f46890b1941d80c00640c0c01d04600e4108000080035107001c040c2032401041741c0000300401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 240606375 1250 240605125 240605161
    0xc050307110102210a08060909100e0c03330c0307030b010207170105150924060d0617060108030f40050a05030105070507020603100e011502010f05 65
    0x114007007812020a8006030310344442a211100f503040141d91500d84050000e01402c2c0455a80e130f03607115941c50b96010041048000d549182003500b0241c060079480100e07600c8008807019a005a84004280000103414048c074864000122640d009110041040d605000921410044c4c0c417070742e080c103103200c02c0802408018409010315541d041d00074107030307030081102c1ca006100721074440740030500b2480706031b0291a0640d05d15640d2070700800940c8441c0307040041c9520900b0081403000b40f070315286086421121040d00140c0e0881d80400801414201310702490300074000c00c05d54444140c11b001c1c02e003403600c14160711200464100717012a2180128003402c032a50400800e0480b044900c9829840d0b10002c0400b0820045440f08020314080c280486500e4017102c1e81102c07108a1141c0c2d52060609072041158024000341c4100f14400040c9081c40155403c000707041760307081e4090307190640c100c008032003070f0001c4200c0140720000403a100d81c240150000317451001014480c40c10101c0f07920386c1182060f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 240607625 1250 240606375 240606383
    0x1306140a0507031107090507050408060a0c140f04090204090e06070f0c080a0201020c0610090c090e010e130b040302010212160e060f1606060510020a03090b0f12100e06010c050307 79
    0x4001c2400d02d603804204600c01b41503448010802810007071703c094030a81c420722411085005080001d03d00d0101c0e4419450031038241c0c0c407201c1d40d1991448506035194405a40d02c4141c640500010929090360320140c800f0300030300720340021010380f0900c40602d0051700418020800c2400011080da184c0e00240e440c0081da400024147c4500d1144402d07406030040c0d540c08401481900c0c200000c11000b0788d8500111190721004101408582da41102d050b41c81b4016030f1315030808a130040201c2014800102c1e408420300d036038400d101005030740b0714408007401e803416001030703402184142059414000f03040d0072103002c3c248601425a51440030301100c4440200320300c90140031038030f986000e14100031542c011202a494100340724840c5840401400f0a000d068040c1050361040e0600c03600004109900b143c041e00c89080351498801d20761060b034800302c82c10380c50283c14000000043c4125841600a00f800101316219500703200c895100301c1c41c0284403c0c100514490030a000c188040b049541942e00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 240608875 1250 240607625 240607637
    0xc060f090d0f060504060624020304050607110d050309010315030b060f040f0c080406050f07141c09060518010515010323010e04030f08060a0b0c0a081306140a050703 73
    0x1c0d06101e00701e4058103001525141c1040c04200c100891948040c1c16036070105218881c40d1904d000902c50400e0000c25000568410401400503191a0010309140c51041e4440703481c4040c604086001801c20200807100c0d5480459100f6440d03815000e891890000c03c040400c401e459a1195120040b000c0c040d51700501c050410100540c8841d080040f14140070501031001c07098100c0014003508088805032851407500d4080346100404c0004280503e210f0740e50079002c07180701c9841e20f445920010a00021082c02c0300904030703e9002d030003290125409450001454500203078180a00c04071180c03400101c1c0d140c041000198508140010803088081c6400101c03d2003800350456041000c0250140b1107a0740030002030011600c0301c00600c514402e03900d81c0300b1408803e0341681d42e1503054071700c1603000c46500824041c01100f640940321400074401160215000d68440a15a41c0f2480b109104810b26840c03c0c8812500582c62560a075860282e0340d00e05030000368001c10074000c401c001810084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 240610125 1250 240608875 240608899
    0x20f030601121401060f02160e04151401090c0e03010902060a03020903011401080307120206041e1104111801180b0313050d0c140625050403050f0f0c060f09 69
    0x80d0f2006801c1141c032000320300c0c2941c480d04040e090600000e2240b0042c49040d0000d00b51444204140781240c5140c0c038811a180c40c1c99a480e03004103414004070070401d40d01c0914040301d01c1820400e82c02000c41000c00110541d61a200030b028600c0c0340c0d03059000e40e04003200c6800580361034040310040c2580740340c010307114110180081e014000b104020344100310000008550340c04080018002141314103078001d840b01d01024140d03290b0300c00f02c4020300f41c110080718084038180c0c44144044480d100700e8010b00c2115070900082c088800d0070300c0c40420302c4000702e880e443c6d004100b103484260704001d003492402d84003110040711079041d40b806400280400400070901c505290b000702c40c041a448020307101c2c401a00c410003481440c00610a80c0c0c11440c0e0080c90035403d9001c14124048d00044401b440d400d04810300d0100c4840760001004104034003040300101240061104594207000000078054507030400e42174515165129404520622042100c00400890b02d400c40303c7e00b40081d81d03800700b001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 240611375 1250 240610125 240610157
    0xf050f03063d09050601180b070201030209060409090f031805060d0b01030b092e03020f0f120313180c0203180301090f050c010207080c030a0b150a0305160801020f030601 75
    0x1c2e04200444110416a40d00841e440c9080e8200501c00c610a130f868a0720540040548000c2c01603600c501c076996181000001c015501c42d400130600c10402034411890103940304102e000701c8503605000d440c0020b0300c810120800d6841000d4060760205c02c94591a21410000040c40030300c00c4200548180360303100d88a07810b9034000d80081c910090010401700072403504000f1142c0b00c600301903c042121002044080c0d044110400034811f0300d0700603081252409440062046408104150552000300282c1d00309480100308000c01000b40d540100540c010700c0e200d040c4c281c0f040f0591910100130f051502c001d0000e54000181d44002484000c0101400c8600c40841e004192424015002d40b107106030030010711030700140d01c0c1c154607030a83c00c40d4240d030b5a40c8412034503074251810140e8036030442d05881d0f010a040c030304141e40000303990f00b1440124006c140041c01007000c90f8012113403600062420010004500a400c0040000100070361a10b840504501513070b100003000d0906200700f041c400440c103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 240612625 1250 240611375 240611461
    0x203031608091e0d1e0806060912070b070308101409040314040b210615090f0301090f1b0b2502030d0201050603070f0b0406270f050f0306 61
    0x80e200500c440e02050090140300e58440100100000200d120b0b00a0450072070110306111145e00c1240c5e40300200b40d00c0390401c00400d548030002c801d0b4450013030103240f64000b00c00d1142c3c0e0000c081588400380c0e900650320300607000c800c0040ca43c02c03501c00c0c0008208043c000041044000308000c5614018594451030182e480c0300c8156a641124070000c2400714010500b600204bc1445901c00307010b0100100140d506100d500c01c580903a00410b144540e240d8410040005e08841d000080429003400d40c1038000c00d084034091081501c400740303016100028040c1c03052517101480283d002802071907041a250120510400b0071643c00790032101c408100c000b400c440f450341699802000e84a0002040400031301071f050a9070118070900072110002491240d10824104481004c045113091905e0718030255500010a03800456810343d180718000306010110449018085036280c0c0d03000141003106000617031458800441c06640040d00f4090842c40f800241c10400c2d09000114203030395030031100300b030003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 240613875 1250 240612625 240612643
    0x307090305060f04150506030c060f07081c0c08010e04020910080610031704180f1d010609050f060102030d050405070b0d020c0d02151302060403150f0c020303160809 73
    0xe1400b0700c0043c000181c85001035a401580914090038201c00554410f0003215801c0d580c0175850b0b8040c02e031a0645003411400740000c03040d045001420148142c440281a40c07104803090a8075108865206000d4911302c1021081c00789032410800380d40c1004a48038402001800c083d1052403c2030025450881c11128240900703095025140340b8140040111111511808121070030210031009401d04903440040d28101c83d83c1c0c4d806e040001c440c0305a00001001c2061883c0d4103203840301918104503040786404420b03000d035000001807031807030b050150302200c401400c030000d5440d40d102405016a0b00000b03842219205600028040d00d440c542036141c0310b01948407422980c0b020562011076442a409010443c052600b541d0740c030306c00108100d80790004600d1511011082c18046030300c8421b11010360880e644080d0135a071a068403038561545c00e40c040c001c500e84084d1124000c0000007081d025210780e901540c0025800d606101c0491085444035048440c01c02c00000d0001e41c07041c03c00c20000304 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 240615125 1250 240613875 240613883
    0xc020310091a070f020d031505090c0703030e0c06190201140c091c02210703021903050c040506090601110115060206011d040503091e030d02011d03070c03060203070903 74
    0x54000da86010120030058560b2854280744000000d101107020703040c0c030a0440e45540c0038100204440005400030690038a4890705c01d81030712000300345038444401c0340340a078040c04a015220b01c040d29004040e100c0101c0600e0881c2c002021040b4142ca40701e06460703851070310081c400603625810f00102c0c01807809070701c1d00d16002108001e003c048014140140900f4109441d6000f00342102851a81c00c0c05003400002d410800e5107400010540b840b1440d5072182002c0310a40310310aa498000404080c45264540f502c0c441d4118100100a0204064101c17000c080c1c405228610786640040c4503150010100c42c1404824030454030744003029417040b0802d410b14548208101c2e101c220095842100f4040c0300c14105010701400c2e108400010214800c070340c00401140b9140c81d000c280304a25108440c00e0111020750000b50a081da400e00c008072540d03490341e00020301c1d104044072040007208030800d844855002040000e011500c0f90b0307101015250000c1002d603507500c841a0071210808182c0c00a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 240616375 1250 240615125 240615131
    0x3060e070e0105130f1505040b161b06020d030c020105090a0605060f13090501060b07050a0609080c010c0305100b0702032112010f090b180f0406020d0c030501170118030c020310 78
    0xc50f1a4402d81c144a013038402c0e64040440707400f400c6c1c5003035400c4d100c2e50160706400b0009001c4840c4101c001c620a1100702d2050201c841c2c0100c3e0740d09038003110100740d04a00007503008440b00314200c03a4540305007a084000b80c03000b44401e0808802c00d503120381101c00050803458517800058065100c0319009a0780e10009003d030b800510035914000014040080b0440e425404d060000489000b020103490550b60042d01501207040160784a000810020344201d0741d03c00d0074405800300100a01c1481251403081e140403e40d454034484104401440e03030855202c4a90920421001d81c400081207490408a1240c035240d41c01140c4401c1341d20700450049800e40c02000c000429501d01c44c0c2440c0b001c81e01003500603c02d56040303000304102c100c0703c2c6103a0321008004a0005e500b24803850401034105000b4240149018540712903601500d0240b10000c2c0403c1c0c5420041100900b611b80b0103140d41c0f0507400803c00702c1b0040b0b441450450315090043d04100c4000000c500750b640a00c500020324240400c10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 240617625 1250 240616375 240616379
    0xf0c08270c0a06111c05160f020904061b020f030d0f0f020412060b06030121020f0306090d080f0c03130501020903010212180d080105190e0f09070603060e070e010513 73
    0x40001558054030401402070030795251001c10b001c1710003825895651140780c1000a10303540d9131345c2c80c20b00010030b880250000300d218002d82c990040160055000300b00200d4003044c031014102c41a5844525182154406440c00e068001c01109071a40c204d4411004030710301070079206d41c00282801e44443c19035580300041c001044074038041040002c0384191002e01215500b00c08002d003170700091054102e400004030018141900e10300c94001018801459031560700154400710380751490450b052041540004115403002d0340140e401940448609000304007860020340d45045408058184000d155050903200e0800a080d0155032102801900031500d94082c5559141d0041043e03800c02c41c00d078150800d482d900d19010131100780b6080144c6911800764a000f05101e030184060f05c1103e40e92404407008035500345621340381400f400c05015001040e042101c003150a01d8a00c1d8000c00a25152000070000361076603444407503000c0e013a41400f2803281203800040e02c013032040c8000030090303144000300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 240618875 1250 240617625 240617627
    0x9040e0f06040302070b0307140901051315020c0d0210080c040b0f0414010f090e07170c03060108090610051302040305160801060f180905010b0901090f0c08270c0a06 73
    0x818802c60280d0700300d03604c05655039600107452006840c0200040c0c41100d41903107060010303008005c440700601d041ca01c2c00344910200019480d45401510041d980402000b8060350f04103c40d4103400d5040b1103409402c0040e0740080c5d2210f03000c14114090110480c00200111440e03c25980140100007410b5959400040700107a030758024012982c141002ca8420507182d4860a402d0b050b85003103031501d565903030a00c0307020015510028010003c00414900320f03070324201d038030007003038080c000c028611516400e20724009021a000201001c000d40d001c1317010440344018002e8a078048030f07801d41e448082203042504030b10180c82542c00113005071159045040d001040350203800d0848844600800c45591a07070400c02540a45c0d1141902c95051480c0307101c01b082103503120810b0316102340c0000403040e20a2020551150090b440700440c19038441d050428043c560150040b84e4203940b4044006280040d1010103006c92022080e80e050314401d80c0c0c2d02c00c444200158500800010714400c0c030559039481c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 240620125 1250 240618875 240618883
    0x515040609120f031103131403060a18030318080703170603030a020c06130905070c031d0d0803040c24090f05010c02011d040f0204140a150509040e0f 66
    0x1040c1000150008400500d00d900c1c2d00300c050410303900c401a02d1010103d41c500725021000003400310118041042030030b5559513401074000041c803001000c0100c400310f203000c05042602c000c0003000f500c0d0801000c041e06010b404d5601c60341d0340d131500780090640f900301121401e1540f007400003006024002490028180c1101a210022449081040d515510001895142e000750440310000d42e000150000b030b945488dc010780741842100c2d060340c030b8103036440d2441e00a0b00d5041c0c0d0540f0101b20408140170505900a640d402a0564005c02180003815100410118142c10501411030070010001c43e082000c8400c0f03078070080408540916862420090440143e51a010301201045c1d19080c000f171010b45c241c0041044500586680c10600d4480d0019180151151005103400b09240b4a15009581da84200c4402e02c40d4181e00580b254209803400d9010000c0c8040d40c1d21510004004203c0c0014200d000012030b10f41d844d000d0b440384449400b14000d40704248191450340a5103410b03218000d8006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 240621375 1250 240620125 240620129
    0xa0201151706071823041b1409010c02040507050912100c0c05061303020f0f0604060b092e030204020c060a061d1f1e060306050f091b04051504 63
    0xa42e00d1a0300c42c01402d0b180f4001c441100d0000d40ca07016020003092240b21824580c1041141c15490204140b400007403c5421559000641d0651602480503680d440040000c17212044036071580b9141ca02400640385041207440281711782e80b03c01c0064821440723181a500e01030806400150103000220720243c40d800e123003050f0024249020180502c041c400c00942c1d8005ea046005405241c40300e0890040107001b404060b0150f204903207070700c0752211081065800c074002250150200c0c5c1068a132a0058500139081a8842d101142c01c1c0810a00f91020b4a1100300c10702c0503011240e040c01d8103407030a00d100d44d800a94018800304510b5030342880420082d12034200004100b0140b07456070038841200034944241580c0308210300020745c115059102800198401100c5181d00c41e90300c0b40e211340c1314289044401025444039804000d52034140c00f6860250078103c1d003040f19081250003103811080c00901b001e41c030304100882d0b088040b59100807503001c0c040203407007880c1c0e005981407a0f1419501c14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 240622625 1250 240621375 240621419
    0x8010b030c2206120902060909060418030e03060726090f0a110f04090305040603091a0c0a0f052d0c07060504030b09120d0c02151e010506030106020705060a020115 72
    0x101c404d80c0794501d2403064507107640e401442d0a04040198044c040c18090003070500f60040d96807904d040f01d03d9144292000014401e035034040d034461620083c941010f41c090240403e220180d2a9031410f040e0b0320100a03d0074500800d170015550380d592100b0305e480d204042210050050108003410711400646400b40714100382c03031450344201920144002c6502e03280003c0c1c0041c606100c144042c40c4603030011310380385028500044003200b442518011440040d07429081c2003000291040599411004070604050340d800d119041c088034019407040d20380f4481010f0703c3c1d841c0041c1c840801c82e50240c1501c2c1c46c0c001c95000c5a0015484002c09021503000d400141c8a0070010000a46110000038101807007060010200781840e103e4042c1d04c01801d0322414038001c0d40038290f6411000700c03480c103100d0710495040d040440510045c20b100d0300040010f1304914000c050410050204540004406003151403d4903159501c1c021440304a004048002c04604800a0b4580008070410564861a410400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 240623875 1250 240622625 240622637
    0x1031e0c1116030b070804150507170f010f0b0a02010e060705040501170c07110414040b06010306090e060c030424060e0c0901140a02030903120703021204030308010b030c2206 77
    0x10b4190402c6060a0b44070080c070400d0a81d0002d2000e5120f00d5200c0c2c1c0040c441e860300c0360100440340d904000c5da00121070381c43c00544003400012402c8400104c00360130042d406c4004545505204421061000034014000c00325800102c0c01c580ca0f20035032046e000c1e10140703016194a82070000d4020701980c0103204081c001854250306480100425102a000342d1200c20018a003140c0c664070b8141e8444140c00060f4001d0341d0340010a209114840392911488c0304002480180c9040000502202c0580c2c010500c600d242c200c09030812180050200c0d04000c03014212a100c2c0c1e0741d447c1c40c40c050074254404041064407881040d01551040c0c03c610159520101c00d09038503038403d503404181e40103084240e80000c00c181411103008144900801d1244000e1058a140940d4400802d05c0d00c04800c002c81581754000401c0b109059050011080e0740c4803d1000c84d2816103036840043c031a100602131049450000070204600000c49400c0b15072041c1481d48001c403441500e0540382c2514110b10516000c520 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 240625125 1250 240623875 240623893
    0x5010614030c18160c0503030405071a0f040e1f14031b031b1c0f02030c01140a0f030914060f010b0a02031209010b3a03090501031e0c11 60
    0x14255007140c0803043c0c40c92007600d8039a50300858080d0380541c0c0502c1014000310500c07032000302d0307010310007988118000d60007812410300d0039038a1016051104400c0b0450007080c066035112001860032903040380d180741b041c0c240c203844603220542d00080403444105030300f0403510300164203400d81c0c04100895908405503200b685c3d10303455514900c440c61911030351541200d1183c0041042c00e400b000c03c14000508003c141242130014848009042d010680e4070400e000c401c1ca04601d001c02826901c00d0003842c028903c110780300000707096405208507407024080d201c1400c110a510076400140c60342e403c08000c0507a81d8040000d1510350300245c4207401041000f500226251074108210b418039011607000718942070403941249156613010b030402c07d0b65500c0b0b980002c0c6560720580364114040740c2e2909008486041d00414466982d40b050866105920f44465008250030110080403034000382800301e42035a0543c00401030030034810491449520f00480726500c5070303000d610442140400340854039240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 240626375 1250 240625125 240625129
    0x60d02030910110901210e0f21041a070609050a14060609040b0a02130509100602060906060f04020d1b03050117030403050d2703030503061008091005090a05010614030c 74
    0x101c0382000071030206103a030140800c980031706682048440b2628800240f5260075400b018201001e13078440c03408c250f118030440c19070200004425008040c0344030703a0718502031410704402c1011940066941000101094034010301038140c0206d05020791041c1612031130f12540c50310b0b214410340c04060040c94820140010110f041001c1854000c9800c41103510b500d9940e41c0d1076102950060528144040c0000340001c0d082d1211f40409018203a000c0e03251200e5070070240002e21b404401842d049240e404403051016a8643c00181c08508a0649015a88a04d054042c4010704504207080310541448d10541e1031250b41a440070341660030a040c0115000d4240c032200360703240500e006c09010754101e100c000028a02403000c211514401e4140000c0c501c0100840da9015041e6a10580c04203500008010280c035020f180307580b0721102410f20700424100103d1645e9200352600c1c0c0345607e15030780d01c0414a0b5090800c4581a41c1e9070010003071144a40307462801e0083c041500d00c050080c0301c0e50704201c0d014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 240627625 1250 240626375 240626377
    0x7080301060801080a03090504021b0724050310060c0602070f032a2121141006050d0c0e0a08100b090402010f0c080909010b030702060903040501020706030902060d0203091011 77
    0x160155500031f242420441080001d6015051911030661502c403e1041c1c1075041c0721180080c204445203e0394104014803850901c0305a11402d42045400c10401040c0040b894101003070760018038000c01c1224251506000900c1184000b50030080f00c0f985107010503500610b01840300d4049201e400c10002481d204200004100d800141989610710301803d4290614400b5a0364462503c0c21070500090a01003041444500c42e04141550321803201c10700d8107103080031180e00940d1038401000800d190440040a6004004122810b140c5601c80105228410228100e17418030040c4021a50b0707640311000c55440d5038501010144605103140300049142c86a03070b0b14402c50301a10f0300642d24186400032508400c2da03000445800b40d05106008403500d07a5441140641024a49141e4034104640042d1501c0002803a5145680c400c101c103200590b8007051a00c200d450500300407603202c03000d100107031050103810340400700d1610110401c202100e0002d0200d80010404d1010818040c06c4041800c003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 240628875 1250 240627625 240627643
    0x30225051b10050705070e091006060801050105070305030a0f0219030f0212130309080102070807140c0102070b0d0905030f1306091d070201020d05250504030515060105040b0708030106080108 84
    0x210a844001d00b4007018001c5005100c07035480342e002d03111034540316550014598810340d21f200c0c99600c04201d20228550705e10981c005440c050410714140d40c035100c00205a4810800010104540800410b00a81c100d80080d09041d13083c9030f082d5181c3c020312009100040305107081c40000b034200015030045020314401c80380300007030320039408031a6a02c21040542c0c1c0040f0100803030801c141803000142c440001e2014111141c45010020ba03241074074101281ca020510040d909141c0001c12825056a00016144220341e0000e0603180c40303100300402c4200134510340401501c64040003c80440d04202c1e44000c0c07601e5507500a0031031550303807510000c44151a05000300e501e49200740038000010840240e4196000744544005450195200b15941c203580007652402d40c0000004108428221404a5002000154648141820b29507103c00350780e840d681ca2154038181030740300801d42d10b900c075000b210040c00e00c0b644015134038012032401132420b9009210349000200c6100020035520303804200745607 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 240630125 1250 240628875 240628879
    0x604060f1214030c12040f050306130b1f0b0a1b120e040204091e05060d030206060f0109030b0f0609060a0612051005100915030b01021b01030225051b 66
    0x10344001e00d80e840d00c02c1c64a03200c0266049100520100221180412441c80441900007100303455034908500d8400a01e0283c009510a412040c03c01c8000207560102c80096904405d00d1340c40b5445440c95000f030301d200b8800c240503039108804003080c0900400024441d8100b15512510b000e070750400d9910810300030390f0380203009042c0400c0140c83c0074416000561420002000185040d665082c00d10031921840d08664070142c021030564020030480c8113180e8810010b907060076080d48990342c02902c490004101c4da20405203000c40c4440c6901c5030a5040103540d001c0d0500c8070314101240d19246080048440c07600c00c2d021003000601c9410218ac41000312000d640307513100c00144685560340a481c00800404102142001c0060355a4403031508010851039a2100d0412a0501c0003506400c0d5460000c0d00a040c10180714440e02c2c1d81c0058800f00c4034101042130141d8002c80c4004074040d125440c3d0940407020b420000040743e071400394520140b00c0c4140202c81c092800c808032500e00c6480007001c16 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 240631375 1250 240630125 240630149
    0x11010c12080c040506030a09020a0608010b070f1103060c0304121e08090c03120703030605040b06040303050a1404090b030c090f01060309050a1e02010809030f07060e01090606030b0604060f 83
    0x80c880c54050080150054034068916003071503141c0c00801c05e19003040f24040203440c1ca440c102001d48c144042044060070013803510402a43c10300e0b04002440c0715840707000b08000102031404052000030150380d42005001401d030307410340c00c04c1e4594502c1074005580c00d540c8488901615001c4a010352440b40a510602a90342c0c007403114140280c4400e4801003004989001d06160307071380f0a43c0d0031b104231015800b2a00400b51030b00c4c59810002c044540c560885401b4a2400d04050442da81e5482520700322589490f040c0c0d03503840c00c0d00080720b000c0d00c03101020064007001314000c0b03044070681e080f80e12030040980440b049443c41c64108954801c0607503503a040e0201c21001400304501c0b0703402c6460118010012035869112130764582e0603508541c1640901050241c1d4210115070b07112152540004c6820003c60514060313541c040741e580b060610042403507540d411044000324081d008043c80f41d4002c0c00401206503a13092402c070365401210498422781c948200482c0c41c9101980203c1070b10150706c090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 240632625 1250 240631375 240631403
    0x3140106150e0111060a06060905090c220306020f0306280e07050412110102071e120201030e15040b0603030c06010e100312050c0709020301030530040b0711010c 71
    0x903590b2100d842002410032601481d11301302040c0c100107050080c0e1144500140c194540a40104440280d4000920030351800f402c0c001080103c2d03080e41c015050480182012800c0045941a480d071503500c0200a1800811000409410b1034080c6100d00701c29652402d103203034000c428041c2100394007070200d980418290140100c80c5036001d00765015600e401c0c0740c0d1826403034540480108006044c11120405802c00000741075a041c4110b400904450f945c0d90b2458080c0d01d020200110940107411949425441e168103581c4030780c002001d0170700248150740844450400022000d4421201035270540711501c0418460f040001c03c0b01c1c44000008050501c590070300b1f034120350140780541480000700700d1030380102c00f1410150311460054040d445047c0d07a603690412540c203045440d031000b00018030510040000c20310104a05200911915407a84403640c080800b5110f03410600b12025030075004503020a440504030010302940340141c0100300c04c2e040c14001101c140a43d008000d1040c8910180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 240633875 1250 240632625 240632627
    0x10c0314040b1918060c020a0510020d15060302090a0512070b070501020c01020301230904031224150806030a050a080f160f03031d0601050114040506040902040314010615 75
    0xc2e082d000505929440403803900c4244010641e5020718200c01441d80c0320341c0c00300400c045845040d01155081c0041e00301a44203450b0301d03072140d8000007405030741da0f00080e07201c0308250f0940c01414800307600f18500710740a8840e03030024025042075442a02840c42c02002181c41c1c038001501c0140e42030303684014040c86007407041030b400300e4110803003c484543d028030a00e10901c0d020300245028014010064060075050140c0341914540c0e800e1041c003030441a070174080485e501080140300b07080d01a1000c210010600c1d18030300e1038203081da50b0000e0300d03103000e4007c00c94031450b5201c0c040090399681c41c4190b58441074101500c40e00b44910041c1242c0c044040d80d070004410001418031300b0340c2d26a5181c14258019401080c20480c45021985000039a0b820b004150f010700c220084020410a80d8012088400445070340d010b06009007418003880200c500c04503200380d0100d038080e00d40074003900d441c1d640e5414001c001e174106010840702d414040c4190389442d0b80511940c0110b81030601310288540d03500c60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 240635125 1250 240633875 240633893
    0x10e0d03021606110306100c030203030f090c04050103060f0b0a120f150c170702010509071a07060e0313060c11300d0f022b1808010b03010c031404 65
    0x104560001d00a82c007100003144103072007041e0310034003200000355807031500c0d004010f02e0201c075403c030000384209445441c0111380e000060b00c1e40204440f0381030000d07840d818130040c40d0004069144d640241840c00101c10003a554214100e0540c00c8503060162445203c00c201003023a4500540e139550307565030030703240200e00007585000108e0300580685100c2900890a0015180b09015200100d200e559030038003420600b400499004090303100801150a02848580d1210003034420070075130000815500d20514928012a5820b503400542006000130301281280c5035006040c2166440304580800550750703001d10313a04110917500230385000c40311100c01e0821001c6607a40c20010602e208000f24420b000501c05010441143e80900800f100011000000c01c62800600030104541060550356811350300d282d4410810800826046a802c142d40e0701203808062503516484010003035070b80055844010f42c0a0041c0100030350090100302100f43c0c041c4d0a8413241d020f424690200e010000f40420382d000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 240636375 1250 240635125 240635137
    0x1080705211b0c03070219080a0204050c0d15050315040506010608070507151406120d2115080609010b010903020105091518030c030d08041511040e09010c02010e0d0302 74
    0xb103024a000d820001c1e039032955085800c000c1030a6200103a00800d605e031501c0c00b21200007881c07007121900340c1056801e54803061202d00090040c3e0701d420204000d40341c080c0a4a8083c0407410b000c00c42c80c98107000450741c0d525684503446c044c1c0103400001442a585100300780c41260400b004200f40d92030018110f03180c40e0b004114008104050126000060544050002d415059580400c042039000c005022600025188520602c011003c1d462105008201e224503c091130030324000c401c1000ea00d1319161164400ba40c54010300d02880e9602c0d15044402c240c082d9540f1808841d80d59995404031802c88010b810f84c6400320382240004c02c01584104010203d2500c0035001c9541c1011754044000d4a4000b00c40303090100345004455117440c1801c000015580d0f108070006c1c000711100450140903184050400762141440c00428800b0410b1034220000305220307101c106a655599114040c000701c42034558440719400c00711300e802030910502070303003901c0c1c600500074001d01c408100d01075009500030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 240637625 1250 240636375 240636391
    0x9011a3a020607060b040b1206130201090306020f0304150204060e09190509010501080111040e07050f0f03010303180e06010e060a0306080a1202010c090605090d030e120c0108070521 80
    0x4150400c006031291005019003511480021403001c0d207a10410085d9049041010301940044004007640c035400500700e504180a0100d004134030b2454001240c1ea0030b1180c101a01a81c00092200e071064140c00c0218030883c014a5404844981445240301307a215038403e640000b4011010034000b8506444003075080003800c8081c441c50140d40014000360741049034819080d96450740100140082801800500722451101031b180c54101003001c3d800756009401d620800c0004181c10b80f8140c07055045840071f45c0601c0c3c200e0345035a580d160003000300310100000e2407500104000002c07450003109029001e61016110440b5810b2010280605a00b00490450400da11004d002070641c3c014400952294004d010f8181c025941c08406425504640510030401c84a00010440ca56101341520071081084850080818050034212540d80c084022942e20545044800003d5100001c0d0814200360030380355040c0700e94940c0800d0300d190161850440c00c03d440311010751407800170002080d91142075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 240638875 1250 240637625 240637729
    0x41406070209040f0c0f0b040e090106170303061806030c01030b2b0b010b030702060112030e060301240302030712150308210c0301030c140a050909011a 67
    0x460700040d02c00d4205031003e032034136000801514180007011100a01910421801e0b80300c180c50071040c41d180d40304a100e101101c8440c0380c049540d06c0342c00e404c94402000e4130018040240c0d0013030121910307540305859143c03080b4200002c09004044450f000c0d841502c0003009002d0107029800150080c00360f02d0240e0394810f64441c034a5610100f011703858904c941202075000640700192a15419140068200801c118814020014610f60000741a41504c020f03034000c02036003000b407509840c20300003c00c210b503010001000116202c3d5151140484507460407105400c4080c0407003065049100c19504640000d850600031a03038819aa00401c022540c202da00314030003030352602c0c0d5802941001c041d11844d13201000301582c00006031003195070060014840a46154995a02d01180c3c003020f1140708404507286200880a83c0c030303504000010600640b619009191100e0454002c041c7c1c1c0400b032002e4000117090510ba0306122542546e55404100c9405d40c2d0300a222041d100c20f62048100b000b4481 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 240640125 1250 240638875 240638887
    0x20307090606030506060910050c0703150203040302010b12030d021b030a0f020601140f151903020c01111e0f0d0e01020a0318240605030304030516061103041406 71
    0x10100004001464052400500305080400003000d984005d0121803240e9414414028160390722042000c01d00364a040159a4406d0880c0c46030400301264005040510503d040b0341c004482034008510607882075008010aa1401c0c0c00c021013000a4100d044080e841400b80203001c404036802440303c0905030120f201d0b0410342d43c8085185034811180b800c0000c0d0b0f14071040d00d074160100482405010209a000d0494240c5c86c0812098000300240038420f0300c2d00ea5a544981707101d40102c5540d0001800140c2a000c20520050041e44c403200801803039600e0300d81d02150700da21807030903124615a6405c4484103039010205000351500480781c2c00307403d200c04011111040005104100c1101c0d001070001d038a60f00c213001e014048600740035142d4070002c0c15181b094005401e03199070340c000521007035032128500700d40c013100d400070b02c03590b0045038241c800000c011040c400d0004480304034541d003811fa13880c0242c0300c1da401c0b80e40200c0c40310042d4181e0320900c024030607204010704141d1038140181100342445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 240641375 1250 240640125 240640129
    0x10603020406090605040509061902030c07050f06090d0e06040306020c010b030d08091207081603020c060406120606020c031f0b0402031306050a020f07030804020d050d050c010b030a030806060304020a0302 90
    0x11003c0d445859541ea980d04104850708090041e1688681c024000d400316240c140311090911501c440c0d40ca001135400400918102007072020744800710b0700041101c1880a24a8016544010a0343c11441610501c0b48904885203c0c0f404400000006800c26050524607611100a500b0080d5100402e54079800581da850710100003040b05e51515583e01d9502c2d051089102c2d04101c1504426040080c00704800004105030b00101c7d1a441e00f4190303080327000d515508003241030404183c40729901100011300080c075a640101e011202c81844001084000c1d0b4940003640c0c0c41c03001c00c22150b010b402c02c10762060782c45003612492002d203549150100712403840c100094204c0e842202e03250b0078044800c0d580814014103204580d40998080c42c114030b041c161100c400000c1c011400000c0c10040000009400c5407038243c00798049640c80340031030300b401c140c41001a005811885007001c0c95842c3c035640e0241480e001031000701064164592001540340d100920a15a0000b070090b0380010f4002d800000503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 240642625 1250 240641375 240641381
    0x1101020f16180f1b09050a0b03041b03020306090c03010b03060103120c0812070c110d021c06090f0614090303060a06030b010c141b0a080c092502070314031207110106030204 76
    0xc08400400d845401301280c4000d00540801d402681c041c4900645c00d202c0d4186110407680c0054000400e420511040d100b6448541281d406c02900b50003100207109a001c800500c98a00c071404078024010744449c4c8050564400d02480041c09032081c1c880b000002d14094481d095440d40150481e6145c0949002d05940c0940c013513416800042c490302051b01409038a40c424a01400112140c60b03940007a40c000800e00c24158042076440040b06c4403c1040101c0359110902c041e82c0130003c607201000300c0c1410340c020300d41e8041403640020342800042c040d180c003000301c0b44190801030124009504102c002c40080201025050510540e0171000d00800c403040d0029080f64100c00c01065518603420045072050141440c0c140a0083d0160501c5901c20204a80030110340940d4001c00301d9542c00c07103809124400404103a07075140c2d29080505216408141a82a20700035a41250241090000f040d82e030312800d86c80c0c0300386c002a0004604100d100c0c03207400300803500c0321002040382e64481d00002e0403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 240643875 1250 240642625 240642641
    0x402090406020c0304150903021201181101020a0510020c01050f01080307031206210c051c08210c0c070e0c0304060c050f0d150603060305030414040213031101020f16180f 75
    0x8030b1160310302002142b0304408417840d4030300d50b07500070f0100301d1041c0c0911655003440c040003010b9868804a9841d242d00c208000308003140c01c00111102d01e8504800c120080d84503501261007542000f00040a04504400850485031604011840c124030340d00c04444d17074580c0c40b034501c0d491901c3c2c940010322001e03c0b00e03000c4002c42642103040f10403401031401d090300c2052a403040d40031341420a0040314510b0843c2c01003580701d03041001c02d07907039810341481510b8030b1641185901c0700845500034840e5090f12200507010a420740d0084034006034894088204070700c400c560034100007a007000083c00181c00c54010030300c0b41025050080c1024001c0b242100c0030b400c803402c0c1c0d1003034a6550711222030f66058044904c0003462281010800d9608684500b501ca02c22409409070b1940d066520840980391b6a0480700103151213010f0403000e94480c40c104a070401c1440070180107100e42a140c5042890125140501c519000404040c00d46090541c03100d920001e00220301c07a60f514070f00440041036038080c3c03410f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 240645125 1250 240643875 240643877
    0xc1a07021e011d1b030c030a030c110904080a17010506030a3b1b0105030403050a0207230f01081009091406010f0e0709180b0609030a030504090b06030402090406020c030415 76
    0x140071484843d81c3c0c0e0365408048507261082d4081b5900c06c590307880c00304144620a4141c5000c811550650411095000b48166000c0e007100b0a04c040006025410014101262a07503032550500ba400b4010b69031401020300415501c40004c2000ca2003011099020041400b510b00404200d1180300c0f4181450300030000446101c0c80036441d402c0034030741c414405420340d200d4100c40b10403001c140000087c018000140010f081c4280091940c60340f5008110210081040e91040720700c01080c500c40b22500c0007208040d9000e054501c04008656000d0303245580702e54070440780100e490740317490b44c4180508420103096580348200d03502844c007c1d4091041c075000e403000415001807140307005c548000c0d49900034001c0e003c22010340c006210580310b11740600010007c030300c80442d50b2002c62000490b41e1140144250349841039441c160105a0010045c2003140c268180803c8065640001e2040f00d00c41140c00030760001c1410300140c000307121a40030b0f0181c542030804687c2816145ca401843c07241e61162888 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 240646375 1250 240645125 240645133
    0x1e0309161503091a150a0b07080304021c08041206050106110c041104030b04120e030a0c050919021201050108070e0105030a02071e050a0b2202010c0602190c1a07021e011d 75
    0x14041c0c241b88844000400100407010300d400c1c50341c1c036001814000500004c0c031600d490148454441c81d03505140b100c035a08803090070350711039942c1181520185030420484803181840700000750746025540808004030700001502906d22403c04210040112850682c0d00983c2800b012000c0b80720b506005220314418400105201d01410002d4180403491011500c01e50100319110000b8100d0903d00c01220070654081441d511198996a5005c50b0a204084018404151a04005100b0f925030341202c00a0700c640510341c503280400c503030150500311071302e000c40d80410120ba0144441d600805046000e440741000d00320040340c8080384118224003c0e03800d680059003100a0007210404650082e801c030380d6826a081000703035000c03030001c1c481c43c000e0305008401035204240892601101c3d0702c1060304000d99004010751038040c2c02c64070301c00c00548045804019400c0d11040310b080050259401e900284038001880c0010700081c030203000900da080d52034180c1e07604101d60075900824000c60343c01c060 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 240647482 1107 240646375 240646411
    0xc0509060d171605010b040e0d02070e060a080d050a18031208060f04020309010c02060a020a02120c070f03030c0213090c0603111e0309161503091a 65
    0x40303443d503c200c441c030b0003001010741c480412000c089404200100398a50790595803150710421401580c000c0c01c080c08414000b0130800e5001000804826845855012003401d1054103005000403450214803c43c00e9034104100f402c1808840c50840074082c6152101c08003001d018141b0018400340034007054254450ba4404003001c030740503105560728103282070b0a0303008101640102c3c005001d11400709609600c2402140c9601407035900038407070610b01d0a543d0081d58040d140b481c2c880d115100c000285014602600d000640c002d0b191140711007000d005010003260000750441ca0580792202c1c2400051249146000391141850005a8007195984918291141c00c4a00469080c44c819041d000c11130000298814805c020546520724114003511394003498601481e4076001405500d407450074442c0d8040d89505026000414180c0e500d4011900d05a00c00e9508800d40c040c11b03645 = true := by decide +kernel

theorem cover : BRFrame.Cov 240467625 240647482 := by
  have h0 := BRFrame.cov_init 240467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 240467625 ≤ n) (h2 : n < 240647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
