-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1435
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:58:20.995477+00:00
-- url     : https://prove2.me/submissions/8618d234-22dd-41c3-aebd-ad982918cf71

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 257913669 ≤ n < 258093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 257914919 1250 257913669 257913683
    0xc0b0c070f1203080c0c070f03020a090513150204210b150d14010902041d070f051509010314090f070504050f0112030e030a08041707031104020c07170604050d0203030c0d02070f 78
    0x4da19018000301106e082d01c4140c0c404d011010021482013328070500b0301038960070018840c0d619070b80e603540c0e404440742e5004600680d400e00c0005109102452030b485032083d49041c000b50810320f0b28007094035a0002d0180950300b10400d81c459041d440e80000c04055940040c80d9420052451403068050b041080009412a040204011028000c410b1120711004800113440d00c1d541c039000c1e002010606886540c3e03115140e5042505400c14a0f001072039140c40c185408100c0746040d80d0781c40c080f81c0f41500e018006500c02c0580c582408010300c98040034110803503041c0414103003c000049505010b01400381851000a0448100341c0240e507020503042c1c001d41a900f0398881c6081003c084c1d04070744600151060610780d1110407280103d0718405a945c00441c8542d05c6154200303200080d00500700d40709091240d1380c070114592110804010300d980d6080002c0c0441c1c60180b420030300301183e681e0041d06540c414810f0090000e080c0064030406180131400503254452030400000c848032006000c3c1a83d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 257916169 1250 257914919 257914933
    0x10e04061a0406120207030f0c330e1504170c01050115111c03020901110f03030601030c0c03170c070b07020601031211060103060e0a0c0b0c070f1203080c0c 69
    0x800c01e035002d042203031a40c0d104c4440152040c10044143c0c4284c1301c0040018115250301c8072014042d821109100b4022461018058684030092440da8807000c44194031030342c80f02200c18940340a000d40354814030340c10098030241c000b1445041844501500c01040100d00c00c8266207003000c03c3d070999000030209002030200c0d5035502c071240001c40000c0d4240000030007955040b060313008000b55581240401890200c4040060395040b0300941084400350704200180380f990340c4003041001251800e10880028550728103200c0f00140464130306002c20024000c9103652000400c1c0c2020f00d1230051405c0442a05840e40e40c509540c60070f1140000040202030041c0502070703001e500180c498140d0344146058240d0b030100440075511118503d04040c15030307000c00014030006a03543c01c00112100f060084072038038001507803901d40c00003450b007102181030008203c80040110400128006080300440d082c440350411402d0101c00110140140900642c54040750020340c286044038411124003082e5544 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 257917419 1250 257916169 257916209
    0x60d030c05060f06150405130b0a1a030123090a09081902060f010501112505060a12290f030c030d050a11010b1c0309050307060306051c0b06010e0406 66
    0x143d420690320075014188a481c014140401501180c0c01e4450003000306c01161041041800a0956141541c1d00b000b214400021400400b40244a004041240c404d482c3e605040b80c9062200a18107014107801801d00361420b15240c10004642102c1d21000101d001c0c01c450500584520401444071011050802e5600d0144c0e0301040c9640140b0040c0801145641d88a0044507405082e400f4994035420042c1c1c030108218110402e0380c002003002c884441455901d0380007541940003440810080b9142c0d80c2d8408009c2d01902c50203100030740a030603040d05110010309500300380586210036070141104038058a41544c0421112120580007030440d402e28141c140c00400c2c80c1c100c0545d01c2c0105a282a8240c403010707041c0224081144064603045c018010720307070a038020070903512081d02803001015001c103003528180080c0d0090510b0307840c007141007403030a001d0104004031804006c155451a0040400060b0b9055400b6005002441c0c0103602a0005001a0041500e40d210030b640300d030041e88000c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 257918669 1250 257917419 257917441
    0x110904060501080d021c0e0102070305030a020309011e050910180311130203010e04020105030c130f2d0512010b0d050105060909060405070509040c0504020a0210061409060d030c0506 80
    0xc1030343da00a00307031082c410006a0990752811140c000c1c0001c1d00c80800c181806611a0032501c6071104148120380d000e0755261030b0182598881d90420006820026001c0d00950700070ba0344041b020006405448020350030b0a00515500410758030030320642c007071507000e1019803003540d10a0304100004102850950b407450582c0307241504450282c0980040d03008501610303a00d10a6074101c0d0400300005810f85d46550045a00d40c0c4020324a59042106002c10110001644413940240c00300301441c0807000d00349040654800170009551181120020780354220242d030303001c0c4c076040310026111814401e100c0380000380503240410009403c485448400028841c054000324090002910702d0034003a1216811591513540c1200d0161a0382d114070b600f005141805204103501c00d02561710080348540f144001801d0342e204130304010069100d01900307a0403050a00c508801081d20084074505000d4040c0403034250280206814032801c2c0c1f41c0140f0741803500a90103c80c19940c0038080d07070001d01d80880011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 257919919 1250 257918669 257918671
    0x60a0201090203250504020d0225020f040207030e0409020a08150a0b0303160b040302010212011706011e060c06020c16090b0102030406120b1908010207030318120c1109040605 77
    0x1e0f11030b118204d9440b42e440312586030300c0103244801080440c818103080034413020f5801403070404940d0394204011022049400d4100d41e050807200c10800482c4901d004120904070500c071014803030341c0704005160003c0d0b04036014a5110009580200705900c050000650b100903503400700b0854010f01e110580741300911510980305d504102d10030480c3e01c0202013415074900507541c24214046141c542600801d00141c11294424868400580b911002400c606107000d42039010300082d505940c010140010240010382c0500040510781d035080c100d180415003400703400e00c80c020600079007441c1081440030701c0d0112800400000116240300c000720304070309840300140c89240403142c0b1380707500c40d0701f10340c404011902200c43c56501c0c180038104c0d03003010600501180d4851a4408840302441d41c106109404580040a0040006845130f40c107007000350588040c1c41ba40000300c03031100001000904951419511034102c2d203028043c58815240c580122480100025848107554040008000c2160001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 257921169 1250 257919919 257919923
    0x30b1b0f0a03060f081906021e12061008060d02010909020c0c0a0e15041a0301110d0e0106050306010e040309090207080d1107150209030c0d08070b0c2106040902060a020109 76
    0x100b103e56540c06403411300384401d000355651034100341904607500f500113910a2000d40504001461b207000074114000601c2503943d13100c40c840d8086481410440318040256104109494044908000b030304003c113000c070014a0305205072a01c1003510156403145c1c042d60b02800f12040215520280742240a5036007245019551049013881b01c04641c0b0b9401c80d0043d801034403115480a0010303241e600b040090a054602c0a10007401e022074051540c0d070900850101c034440a2080d030f0b41d04c1020881406440700f40180c18038580c10800b04018a850000d10141140d00380f11049a07191a2468100d03008410740c0c4c401c0383c07094004109402031000050050400a10810040005824004024580b4000c02c80301400e525281600e4903e282565001030124400080c16035140910240005107403512140c030988403888003094040801400000e00780d003181031681c4050820658054030001002641e094100000b011408202c040d2210f420504045900a00854860000a10090007807000100c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 257922419 1250 257921169 257921171
    0x51009020a0c02180f06010f080a0209060702060307081005063412080105090f061e0118030b040b070809060403050a0924020d05030106050a050c0a02060f030a0606050310030b1b0f0a03 81
    0x6c28059070080750450b042061540304d24820340d8500518074029000415095004201004603100680d5500c009510911351511000880d0130401c40d95000a02c46030405170041404101038100381526071310b110b0003038020300d89a03112001c00c890a500440600322000b006800309002070280c064101301858107aa03020f46064a840d9195441070760340c5071040d80c9954010781c8022007501417641000b403804c10784a060400b9080414540010b60120394030380d03c04e039400318a00040c0410400e804d854250049050b00e8011618107203850080c0e1558400742009040c0300c00001c10b0510940120310940040945401003030342c0e00c108024a101176000003883c100107014440d001d410b110300600650b81600e1701c544e41c5a00308003504c00265841e0703002c92824480c902c5055015001a55620b0007800090404d481c00c8e40c9a041c200c3ca141c080d500035070000e0040c40800d0007000540385508401d6001c90340c01c0000275440d40c503100b0100c1d213a46488605030009480c0002c0c41d0312000c0889005100d040b1860350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 257923669 1250 257922419 257922421
    0x80d020607020d140705150a0b010306081b12120409020c0f0a030504090906020408010e070e070203120a1e0f06051507080a030c360504051009020a0c02180f 69
    0x400c07a100d022280340503001c11440c03c0c00b42c00c2803019101500c042481001103c8160729032171f10b00c100ea00da080318103601845d1224515a402d503818041c0200412050307001780348112160b851711607885425840c440c01000081d004110030001000340d0b8a0706401000e5850f43d0310b45035031284000c0e62000c851401140300c0d11007280300300c02000070110b444a40640d60303142071908101c0340c00050f01d0f1242c02924819002d0001082288080c0b00c0c6042d200d0a0a000340f84903031906d442881410070050102d000c0d50811301402c0d80c9900c1c03a082156010700149000251581070880480b812140e1440109940d171521000801c3c841241c0d1107030050320b800300e138035950308042c1d0b510003a06803041900080120805004106070035020390080d1071000c6c0d90782098030b55642c51404140c04c1d40755034405211204100c201c843d0102020503130500280406440c14415417629222050f4401c0081c40307020001680006c000006601c10007643c000c1d175a0040039480904a00c132548260702109950603806410200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 257924919 1250 257923669 257923681
    0x1309060e0402010314040203060c030711012406080f070c0f050a0f140c1309050a080d140a0902010219020a0902040905090606010c050d030c1b1a01090204081b0d050601080d0206 78
    0xe1300c00c1c2c03141d47d00030001c04240d9984581006039030000382c041001c0c01180070481700101828021140c0400f400200307818848415102c40c0c40c041c069a01c12010b01013102d003404441d1000603034156214015045c5031401003d107151140e04500071420151150203a103540070108026a201c444040d4003603c480599180f0300041980c07110042d009075a840218603410407040000c035041001c4990044080d41c0c104115526031481607841800d080c1c4120740d07a400000d05900413120001d40000340078000b045a01c0d040d500103980c442400c403124802d410448590070842d44c80424260150408110554896a644a030100540f00c140c810002c2c034080c0100148143d4440c222000c1650303001001042c0101b268802500281403c0503500c040011200410281e0450a402c12403840e102d030700c000d09029400011120403010680001e8881ca00410041003c0980000ea0400595411000c040f2140c400b00000c2d1400d140020028450f000c0c020000507520804074107521201d400d502501d145a58407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 257926169 1250 257924919 257924951
    0xa0201061e03020d0516030f1407030c0302090a0609020c10051e04230d052106030723030703141608101814011e050903030106051309060e04020103 65
    0x315400d20301d24414900c1080503240c601207481d0070300d00500540d45561041171040840340c07860303042900d14811800c895400c007c180c41c0b5040d0311018400240604605603034850800701d5051001a01c505400e1020664020b6503034002c500034200008110b6990134071a0b015602e4103803030f00515074080d2901e400220740c1c007140d800039001c1011802074403a06580d1680c90f00e01940c510030034884000314100c50808140000c100100c003001c219111140c90b82c0b031454a01342810700e044a010341c0742711408140280c40d200007407140d0586000d400006000c180400b0081102074a801c04982c1c18414003000106000b0320b03180c0c09201401d09c030242d42c200043c5a40185010420b40f0402005a018082913181c2d01d405038004141c2d1820300c43d4004031100c1c681c4842e01041c040440801303560f55078964005143c09404407410f100d5800480a000398031b01030400380c0e1607000510070308050110019a1002c2e28036a5038403c40500450741013004683c0c0c640080c4204000d0455080b03000c2481d0580e07061902d004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 257927419 1250 257926169 257926199
    0x302211e13020415120c0311060a082703030a0606081320040b041410080a03091e080f0d2c1e0604080105040203060f0121020109030c09020a020106 65
    0x1c1e0390268240d244075402c0c00300030124106244240d11030440b0114256518240c0205880d014026002e400340c02d60030041540121920220b11501c002c00126000315001030a031503001c900c2100074000e40340d06600018602040141c0d50900340000010050030b0b20056200700c0680381c40d561110080d9031128040f040f00d2365201c4002e040b2000301e05024003031034450104800081d40241c804102c41c900e00380882d06907a40014104480c0f4482010001000800b24070200107000250040900161580700070300800340c1805500250b007002c40c1b440a2001c08458010010700c41c507000c540034150500700050700e8a15001d981c070001060304a8145009545502009040c4d030710382070b18416030b1007071070801451aa07600b030600c000380c901c61114201c80e607a410241008211820010940e845c0c148101401c10300000c299204042d12140140300038508003410303030480034074150b0640c465217250005a854000d5580020000040b400c00402c00c40e416802a05108a040c3c0003401540d448006440203440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 257928669 1250 257927419 257927431
    0xc10140907030b07020115120b0c0405011706060702060c0703060b030d05030115090510020a17120420040501240201061802070204020904050c040608010b071e030302211e 75
    0x849200207001180801c0f0300d4507000902800000740f2801c203240640350480035075100c01c140750145101e20040c00b0503252216400b146681c00c803450142441c0c0040c191943d0a01c1e8985010601000a403164031a502165034950b00140341e00d440d02d0307410f8205960b9541c0780c08129a044c0c10948804000d090008001c902084151181c1d411030b0b007040b240680c0c0c3c041c541000020440540c00005440c0c41e10003940c0c1c852280c85d4003a00300179034107040c810302d0005081c00c902c400c031908001300c25030581211070710b5410580c40300c40100c81a040b050403a03900801441c22903400f501e00300000811440700752074612040c40610140c900c07002c0000c0140d00300c69042c07103506c282d1150003005940c0040180d00801d01d091000b17100504200484011504440302203980c1d81c000140041c0602c1107a411101d02070041c03001580382807920146998a0140c54030750540c241d1042c00443c190002c01d4041d030165030403104051420a106c4200301908400000107580410744000009100c95441120b804e03000c0c400d034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 257929919 1250 257928669 257928673
    0xb100b04030807060222030308070f02070b0a03050408041802030106030c020613030e150714010605060a0c080306010318060c121a0907020f12071104020304020f0d060f020c101409 79
    0x31082c4e12144041c0d0301450120044641034115040b05031013140071107015500030b0f42d0b404002d103041c00e0060450102d806211056500101e42041440c1d445401c80e11380070141d1070b020455488514004042e40100e412a20000a14441100d0464910b07400b40d8126002c0750703401c0c854080100c9050381c0f102016100c0d00d820b01d2200086c0c1c0d0110303000303210810000f20080c11005c480744103442c4080b2035402801c822203988515580c940c0d40d00809000e030602401048407502e10f44003107440007034184517028100600b100d80c08800034415a000760f2014500b04500007075850240101c1ca0410000c1681840c4007010607040c070415000080503105008120046000c025218401002003000006004206004520411588a22001050000f603032503002c00c131011600c80d01e007480c0c0441c22110b5103c21324044c81c818001c001c00b5a82e0307101100b030000c206540840d0304ca555401c12601404c1d00d64207a400c800c0c00001c060101c80c40020343c180348448680c608100300030344140e4400c0d1020702076801074810b03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 257931169 1250 257929919 257929927
    0x1905040518150409031808030c0d0f051603030c1701050a09050c071407060e040911040203041a16080123190e180d180605070314070b100b040308 64
    0x101440994a5802601000d40306646124050000f41502d80801d011800910240d9028001403281e54603440030300b40c404040c60410a003049004d0381d030306554501f0070402c040a01c10f450654001e1003200c012000307420070171100207070a046c0a0050030f070241011300000e608607645111036407058420b43c160707031009019541c0070b0328107801800500360144c5550a103040411010340040c010b0b0900c114030440520240c0701e0310346000c07409842c40fa070044501f03000d1410110402d000a08900020b01008402c80b00180ca0f038a5a04001c08031880c02c1c14011541540d100902805228003511442404001d0383e98906580c2c854000d4103070400c0c414003102d0600402c3c1103102c0c191504c200c283c120f9030032404040c1d08207a60f640030130320540350550b811400c0301c14030300e07071060600c5081c400640360401a050a04500364040b18908a1145c2881071004202011503910708161090101c00c200b94211407035943c840c01507040c02e2040040c2075601d008604801d0760000361601e06103003034034116900082000d0074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 257932419 1250 257931169 257931199
    0xb071704082a3403051e0f0a022e02031b0a050a0f021f081608100b030705072a05121b1305040615120b040f0614090319050405 56
    0x5054000f41d0342d004034504540111403012078140c421401140107500500710a04540308503048400c50500b9110a5000079030700c2241a00300040d41c0008540c1a5001c03a804203800c6542c40d0040c0c040040740900a10520602c540f050b4000003400b5000703000c18103619214500a00341b642c1d000264002071903500038440040214108a50140c1240e00150148440c07080701c840c04001034508030005030106224405001142c1190841400d107210b050400401f0350404800c0c07082c1c142c01c54450044000c000000044060303100e901500d81140e805807104e201c4182102e1130034411600810010b01e011140c1b8000909494001c0724803070b903000c08102500c0c3c05176406500754410680c40902a80011403c40b40035092586c91040c01c8c442ea001301070015a9900c0512420703403420155010f080521101440751012a0394084c45a070420340c00711850490518600d007060203000042d0340d418443d14401d0030403a100201000801c00c14006000c0040f501800c600709407914003a50180c2c5400403501002c0d190 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 257933669 1250 257932419 257932453
    0x602060c0c03070813091424040e0304090506030c03060705030f090a02100e0f09070530010e0f010605040e010314071a12220b071704082a 61
    0x540c07a0241c42a01e103000d07002e0302d568100398032000c20365101c88034410301046004220320400f040480a003480b2003035800d104048079200c00d1445401110071000d0303081d40079250707078540c030046006d29401e050720344a550f1134000b0030042c081110346500030b0040190558240c41c010030b4481c495082c0707032205411501ca06000301c044010041c640e42e0148551403481c000769035407800f09018000c00b69160b1103400b007120180a800b20900000b980a1081d03001400402504038042c6c030040302c40601144403800b0444014540c074003000d407444070340803210400480d01c0e4889540142c440d090400d040900f59036038080840341c5100da4410518a002990300520000e4040a52000969101c0044824541d100c40f0307206085030b030341041c9900b00303c0c0c009003200303100010b00645d41c0e05c1490340742d110300c034000415004c00380100081d000034004480329000031301645c01070b02d5407460210300c941c02c40d85c140341901e04041154090340391807060708440500031803a9100c0c1e80c240740804000002031b04200085000c205 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 257934919 1250 257933669 257933677
    0x207021c080f030a0f0e0a110d0305041502010c180302030604030e03030c01050901061e08030a030e07030b07080708010e0405070b1c09110a08064c050102160602060c 73
    0x5800c078038104030908180c0d00c000091400f0750600e50000520f03d84280560007190012901e03201d181d000640004089250020203441d03000301030740c6070001c1114903d000c4616200b1500001000b1003140d031661400c80c0c1c150f208121044854550100800c000c0c04015200031003880002d5041e44010700150000344145440550b04201600322424402000c15170350a542040b180d209080c0e540e00c90402c110078860b03450700e075007000c000d044210603410700b41029140c0c0304500110050581f41c0c804000f80d400100181c20055411454800c824246014028100d40723040d214100012800c00000c0fa1590404810078003c80d031110050294514080040e5601c2d00080740545002e040a80c2c00001d80f8118060002098400c1c08142405010f682c01c20030710310b20b00d070091000c643c4801d0400c4042c0340f8410000000103100e05446054012000549800141900b44030301032501c2000b41ea20100800e000c9030007590002d8080d190008481c0740c0100c40060340c0c0c8104001a80040086078004020400030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 257936169 1250 257934919 257934923
    0x150301150509030321010614180a030203070315051501021f06080703050f0706050f04140607021003020903010e03031b03040f050601060f0e01020d0f051c0e03040603050a0207021c 79
    0xc0c1d0801c07a00b000060300b140c2025030306038503061114040b454118411a0651301401050034014600a10203040304954007404130110301310750305c03288011103d9450a044070010740e03008048130050360b01e03840c00d00d80e07000c180004154820700309008503072617211a507010400c0003810713401003070f40b04400e40300c501c0002020900d0003007044e5101740200308100244600c0002e0750048000f0a481c00c9006c0f10300303103044103d0344880c003041800c0c01900704000d41d5904640450b0f4880c1840481c0e401d209000030420b10408070020b6001c02820895150aa0550003520382ca1742c045008000c0c40050f81c403156100d1100310340782c441440c20100645100d0300c550021316041401048500200c0303965980e00791429000380c0100b4003040c00c601d11034146981c44803180d03032208028800707000303a0304501c1e40107002c0d54441d030076403400d004000c1810079510b000b0f511405032580510206005401c101c03103803140c0300ea1040c050f100c00a03003040000b601144a90080b40c2d202c55001d025441e8458221401b000c100050140c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 257937419 1250 257936169 257936177
    0xc020d060f0f0c020f03040e07050307032d1a0a06050705030f04030b060901061407060203070e0d0809040b19030204090f0602130e0618010b0a09090207060606080615030115 76
    0x10500003450740b00c0c510740c00b070404200003000c01e04140080c0c5000d2200703004031000e070700401080c040700b13012001c2035401c014a41042c64aa0b103030741c241a0003808410480755852060b08003600c03c150709003a07620b035100142c80c104000b04a891510041c4580d5142010340d0481003507441046a41e216400034a5001e0281d4156410080c003201401c0f180ea200707a0040d03400c0041e000a104d40c500d0640c12041c0100b8603400c0c00b500c6544140e545034114028000060103159000c4000b8020a020f03811007003001c90010088882500076113401001742c0c0114058a000d0341c03611508214031f081c040c0307040050203100c0c01d012103100d1450f402c01c030140600c003408403040405030941100203485800070b801d180e881c0c001c0b49004503003054101d000648008001c0341c441e6010703c0c152424801002401c5d4152001c600c5207940d02e02c03c4d40341c00c3d2450011030703001c00c03080c51002502c0d1050110940c4031405483d07071aa218022034941c0301c10030860a51030741000d00c55010420040000c0c0c03010f942c1c0c0d170b420302c502d0b814 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 257938669 1250 257937419 257937431
    0x4170a050f12060f03280204060503151f12021e06030f0402030613080306010f030e121e0a05040905100e0124050c1018050106031b14010c020d06 64
    0x81d00500d030300541c042800100070b1400b40401490000a0500142d200364018600010345e00c0b9101d00c4000c01c01c400d00b00441d405290103003076480340e801c036502806000d8102d401d40702c05600e5088030070004840609078109200300e544500c078101c0d100c10341118039030303144045031062980030044100c01d0521032070b150f59500e0411450700e07100c43c0c1c0903510400303440e82920329525250040c141099030040c04100c01c884003548100c0040c1032102a650481c000b0b103803141100a42c9002a4000d140c0c00840903424030038005a800d413455000024918078200b5589030f1203c60900100382282d020390081e03000417820a100600041d04a507110a9002040310510201c056540290041404080e00114031442c01079201e1210b070114800c4c0c105a01d065403629900e03020740224040c3e02d855042d000e100341103486645000c001503034244d10200d180d4011000700042556490b0902011903244034000d44009900c400244a40800820164044c010b0711480c81d8000f0700d508001c0e02d080700b040c0c21542a5587c80d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 257939919 1250 257938669 257938687
    0xe031603020f041d0303070f0311030a050405010605091f0f0e0708150a06050901170705090f0d0605071806021f110c010c03020a12060b090405071b0c0315020304170a05 74
    0xb03c241548084e005014541d42e0804500080690141400c143c0605007404101d2154000500841e0342c804455000011691658540b25001d4440e99000740c1d4400c01c40001e00510b0380d80c03c0c654007050030980e0041540599204d84480380340b603440c4100c9001055120001d2440c5004044955101207800c4c0340d00d8140d054400041da824500750041c4000800118a00b041540c20890140900e50420004101e82c82c20041c021700c40d103e0b41c5e6106000d00f1031428004801d4507045100391400f0f0b84060284141d18000f80014240c00c28501101c0f200c00452500050542c00420b41000f0f5850411507041540280b4000c540a4880241040b48000c4108198071a1038001c2c4203000b00d10046960142ea07911141000509280582c10100d84079031400c1c00802207040d940044440034a0182c40c0850103030383d8400d0644040000980292508640d1158441080384a030024820b507407003040c000301c0455400406500300d00040303d0080c40306400040c80722a1000d414060101d4807028030f0141d00e040c0f207034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 257941169 1250 257939919 257939951
    0x3040323011109040f020313020103020a02190b09010605010801080c210f060f0603010204050109050d02031204090207031e02063601050604110702010203030406150e040807030e031603020f04 84
    0xc42945508030801040c100b0310340c80c041c091a020171584100650440c200f052454032a440441002810306500103040494507000b80705c40d90210b021404a00001000d0f41014840500111884d1382d040d441e0480103e07083d8020a22103041e030780564000e1003500202c0301031000004041c01000c6000140004220f48007808101c600e400d87c0c044005403140e41000c400d424a41c10014003014402c0c0d00500080c04039980c84020300045480449d2150850300c0907002190900001010044880320005000f040807100f0350000c1c03e81500c03c2e03480c40e0603000340c0600d010400ca120040900160031240128442c04032890800301018028203511008540122080e003003440e0303460719189240d444070204242444c080c4244c03205101584201032500c582540000e46a1000600c028802c664480340320b910950708032042005010071429149107030a250600809c1c0f41c11800080300051104003c07001ba40c01c000c00d2003140c40304000d0030080080e04650070415100752849034260029694108100ca20b050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 257942419 1250 257941169 257941181
    0x20402180102060907050f0103090c050d080a1205010605031602070b1b011d0304170106080d080f0709030b070309020f0306010909030206010623030705210a0b0f030304032301 77
    0x140003419200150910000380c00c0a10040c220495600118402c00041d20358042441881c40f0900e80040c0b035150301d15184101305c1da1038202e5500202022509000c02426034010722819840e611428283c20f9640b01c9002928424054500001e02c00c0c008103a114160001807141c0342c1c901e0060300d01860301c52003529419005114800b07803100c2034420082c11424284115051f051407071801040010580c0c2140340e61303100c2e51042190180e041180c10030740c00c0080d40030300c001d0418041541c5141c0d1828800070071041c2e0070303144e421502e0b0001c008524142d00400458007100d9102440081030707034541c0c40c240c009002200702640c02030401550076800f5074040c0504c030f02908210a00088071941c0d824003d00d485016081031040c4440b11151443303226140c94071420a076801c0e94242d6032583e4001d01183d03103006004005030b4005a100f5420345c0e1002c2540410303c41c541d80f00c07040181200c071008200d400d6101d0202c00e0b03016042000140017044960124085000b000c9200259000d1b05401c104e08540c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 257943669 1250 257942419 257942437
    0x90308071104090c0f0f0305030306011b05060f07111606120b0604030c0e0c120a0513050307060605120102073503070c020112050403020616210e0c010306030c120f020402 75
    0x552a201405007035203140b020000782c084072031b01c1c4d408507045903101552844081d0000e8180010340a00140131005170065480c180d0380f080640e80346007072140300c9289981041d43c16a010030740c0346600c0c5403061400143c0f032000c40c16031241880e005250017420b84060010140e5402d03000e494030131501068499000a20082d8400d84007503000d1840c0c00203c0508150241c226a0105020071000849022141856030880803070300000450303481d032408900a10181c02c20080580c0030101d81c00062008950088048603c2500c060402030b47e5a901e007401c07807040050041586040f0503922031840528850307000070f01114088410080142c1c903590b180e503001200c070040014410301182c070031542c1c0044c1803204540b17100d900b0b001a003041d82c0c000c0e40300c2000a188600035240c1c21403510200c1d100714141c00d1002e041068034115001030085460190110010121051040e200c518655500c00d224000450340c0101640407544d05180103c00510b192600c10740e110f80401400c034000d43c3d99417004001c0c1c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 257944919 1250 257943669 257943683
    0xc14070515010e070909050712140a0b0f0a0e0c0c070f080d08100b0304050a0819080c070c0501050a0509040f090218070806010e13060e06030609030a09030807110409 73
    0x242440140e01c200142c010408462400c1c0500c0000343c0c02c5102001501d0b07100f4804166a07641c0141100c411480c400d0000c84281060907900c006d10421445034012010f031201030290400c588240720400542c4242c131a08148804400c00c0602240b0a01c260007c20840205142c50701c082c5540d803410006400c200031410403920b0400041034100404400d0001904080b500e0b8540f15031a0843c104942c842d0340100b45002000508100c028041c0d80302055100c00d0f040e844194802e40044000c0ea003502c040082951100840c0911171441e007a2150240e000a03205803442c249401143c90740c201000786000e0200030311920049555a00410741443c01c1d800300054540c5d90ba004104254000511942c022006075040c00700070383d03100c0c0c0446da1250003820310000714190300010036681e00e210031108580500d00352022640c91220604240240400c4045540c2515656125a08d0744564004140403d200034401c00000b141c01d0080c248a41c05030320304a01082e084000303d402c0e9444840222500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 257946169 1250 257944919 257944933
    0xa0b04061503060f06030e070506180a0b09040606030902030a0204110c030316030507030e071e030507080a061506170403031b030504170408060a0b0a03050d02030705071505030a0c140705 82
    0x781408113403040103100c540340038003821000c012074980f00d203510701813103005079000184803580c80003040d2401c080810180607400415070f20210500c030307500611007107440f5506000000541612034020241c0c104d4005000d44910706107542044001c02005400356407400d402e110345280c1e4402400035501c1242144528000348028400060842c0c2000b0004010701d4904488004442d1000900c4416510702d541e911220f40c052207030000d1445550383c401843d52042c3c001c0030071005004140c0a0141d80b0070301c1c0038011011012120420440e09006800000d94010302c480a5215190215600280a070600040c1c0702242c035442e038183e07824041c10b040802c0e21101448100071220101145401e500b104d824101800c282c01c0c01c2d00d801340500720401c2240c661200000c00d0355a0940c00c40215403007c03c40c0c18142210001031340b079401c0320030b06840384c0c007070088000f6949000f0710036903408a0459589600e140c0d542014100100000490302003080180d418000b81030340518003c21050340514024100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 257947419 1250 257946169 257946179
    0x12070314030a0215011d060303090402130e150d2d030c050d02120d0b1206010608040b0c09010c14010b1012110909070c050f01020409050901050604090503030a0b0406150306 76
    0x2c4c1807225488820070303041c507038010040d070803006040d4107190740d0103a6800001d4440c40b0000f80b450080b00c1001d40c1c010320000b0410040840c0c41c1161085841e0080d101e03509544585100e04864445041290072503056040c820010b030316030003114002104802814842e45000f189640c0701a03a8150440104003000400414231004100350440801d2910061548480310400741c9854081c00c9031000c0c00a460300c90340c44255031030903030601000f8402c070115806517a6609004000010995055440324521404906945481d10890391040c0068480760208140e555404494424040d80140295681c0741d110b000c503507078050741311000707601d07540c40b031101c901c5800b00401240c000300fa81e80f0ba511010058100c094440d41e199607440085400c080c5580308540c18140d081c0500c103007000b46107510010300498507003201c1c1e00c481e00070100c3c0c41c004c10070765aa101c02c1c00f046501920000d07205c3e074014030020303010802c7c580040c141b00710090310100e240c50380c030000b10800c42550002100420384424040c40303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 257948669 1250 257947419 257947423
    0x3090a032406030c14030c012c06030a05161404061b020a0b03010503100501261203070201050411100c06051807030602070212060714071e0f020307060f0e12070314030a02 75
    0x402c10214084d0010403480000a0700703854401402d000b0342c4c800d03c241407271074250f134603000c45501102600c550703541d04d0700e1880400248411689180041c0355003640c075000d00c1c07240c8810301e0360314400c2d0120b9291a0420b041954401480c00035407015190013040c000060700c40c0140c0300024002800d03016140e50400c400c26080407030342c6205035803c07842c0c180100240f80d40202c1500305c03902101304100c110044101340c14240000640d1180a00c1c1c400024020103d41c1581304030320032402624100049144501001400b820b86c25141d000a0940d00070359000c02c003a03510040e00b050030340c0080d125441e02411001c0c24074200c0d81c4103540c850350104001d400e6060140c059644802840c016080615080300c0141903107a901808010303080000c0f5440d01000318281080ca0803c11510f284085180c4134075068075074080d0368030124024000c8006c001541030155200c1040a80591940181a200e82c000d11031000d105169040913032288030000030100700d103460003580d081540005180d45040c0320001034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 257949919 1250 257948669 257948699
    0x31206041a03031e07050d1d01030203150910051216050604030b0a02032706180303070f0e03070e07050c0c0604180b041113030303060803090a032406030c 68
    0x4490301c0e550300c051040541e004400c5034070000488040702150850101101c1860144040040142c07099004040d1001e400405e5482401d502c005034000340094000111705034041558100200014030500b02100e2501d200002e50040d041900351a40996450000303100c1d0100c41503802150701325911914011501a980002504095400c0c0c1e2403c0c6c03465030b41c15403645009185900c060b0340800400c0500b040041d68660714001c00a040703602c0360b0044078041e03c030072007540e101000da0003040ca1200d40d400084162442404a600c841100c0814800d043c0c40b9284130850b025414007900d0404181c24028001d654040d1345c440e074541b0f07228024041c0d140c0ca003006503006144656070a100c10411443c000d801d0304180f40c4d80300c40214540e001000803070301030700010300298460f54011800c0e25000a42460396000c4a00964044c0220f5550381c03a0036403248540307a41c403038210150a0050002c01c20721216600203018081d40710600303010a000c50320445510b40c2045460b42e0070704400700440810324001c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 257951169 1250 257949919 257949941
    0x9060206060312040506030c09130c080a05090c2e05030103030f0e030703020103020d15030308090d030b030d030c230909070e010804021516060e0d08010308040b180303120604 77
    0x3c12218410803040f9886000354802c0e60f10401000002071000310070300c025250b0f03220000c0d0911803025902c1c0e51050103003408812440c002842d510014126001c540641d60040c26808048c245054642091007110704070300c009401d10b80507941c124111100c1d0511001d600e0303485aa9002d0300ea5055103002004c1980c4600c4000401410100d81c48480e0b402141c2601140d174242001a03075006281d0401d03001d80344100034000d09912840300041410b8106441078807807503090082d40c4058401031020b8003100c655240d8150540e1241e002460000c0c00b170390040c0300e500b0711424403094000081e040d404c641034000c0030583d03100e00081100310a80c14400344880d000325841c180110327249682c3d40020a20100200060b100707180c0850f41c0380c05402c5240481d801c9030b1030315440340d00140c0386003050000340042c4540300003240b203100844001039100e88030550680754854074207494289891084a00c54204140060100e8602c3c5104006a50104000e107070f400d44030350040c0701e649420010001294401114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 257952419 1250 257951169 257951173
    0x130b03150714030c0d15030609030309020112020c120a0203160c0e010e06090415060b07080403120e0310050636010803041d0a02071703040b150105040504050402011101020a090602060603 82
    0x1808140e021800c02d85021700000d074800100310103400030074154403100d0381c400791400385800301150502d03a16802040444d4000e880302d207080d507008210041288124a1544000d400c60a00a03a4a01708607000700a0918144103c0341004074007107100c448070374035010881d00208841c1080002d4080d80418900411103482c0c040d50318a070007400300e10041002071008042804d50803281407101c000741e1040014144c03928105845184c41d251001e01980580010340b0201394240072410821b1142c800c0008404016000d0100d13501d03070100d100c0141802030060380e80882a09441c04001400a40343c54100c03004200803500161710071440e00d202401030b04042e0b0642c004001c2800403849001c1245001203490600b401d0698074400c0000081c021f11400900003802030320660301c0382c02c0741405180518013036540c030405030300c480705141c1010007984031160200e042444100b04910307042d448140e01c6030060405403ca1182074209070308a9101d0ae480344041491000c00f80440d940c1000f54a41c131510941c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 257953669 1250 257952419 257952421
    0x1170601060e0904021813050c060301120209040c080d0806040c02060c0901180911070524060d0614090622080403080f13060302031605070c05130b0315071403 70
    0x5001002d400008529a004154030300100d01151195000011011031560045a03181008000d88188102034801a5258402c4005070780f004d15087d8100ca0413180c07455168860308001d58248070f110307d0014026112402c510b00002132100b402c1c885c18600c0d012a41d10b00380c0d545441002c200031520100300301d0b070866110303c5c1081455141c4200f01d815012007400d00c09003800030300c80c80412409207508110b4165081440f81c2040284007005010b1113841101605c00c1c4080032603981c144102038445403141c034040c078408143c0b1070030185e00c200c460600505010130050021620101c910006803071400f41d035071021041105103444c089801d0300751003129605a684002d55107918859004500000c0d00040c0e000505e42d407003004100840b041031503002d011108107907660030040c3c029001203807010740810404040c0c4002034420340c1161300c41350b4401c41c800940d41c280018410f055801114282c04d1a582d00311310b0002ea9010803400240780500700001030b8920702803500506600030031a607018000005c1c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 257954919 1250 257953669 257953679
    0x109061107030e120f010e0601050a0605030f220f0c090c05041d250306033f050417030304120c120e03030405040509010b0f06040f030201080c04030c0e01170601 71
    0x120b0841c941d540202e855008444c00784280e9810020603004214242d0b04e4202034138002031003c200c0c24100c0350b084808104d81540c0f22401e540c1071104961051b810701034200001e40135440750815000d8920700c00f43c0240e441000d07546919400e0141e03002540d441c0c12805042081c1e0711140201540f00921385407036410140362a60b07206e02c01d00e00c0004001c901c000f01c40001da80c1c81c2d105055240034650003c08102c0300300350703c00285c0142142c1c041134035943c40b504828040104c040c540d8110050800480c0c0d050010390b4036003688000c90700d000b07c0302000340070400001d00c2c00d10b01944803100008140a107a403420039250003485211840c0480041c8009111020081404404282c0525166050a418142c58240028114031891f00502d601074a004203010709114150b110420340a81a40c002c0c014007203c1e0100540c0740501d214100d10812032440520040d440355011681204200303008a0030701c0d8403941c0b803404049007500300c25018103000d0010890b0340c000d02c5200c5145c0d03816802074103041d4101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 257956169 1250 257954919 257954927
    0xe0405010641090c070c14060a03230115030f06050105031909020d0b22080415030b0d030305041a040827030a060506032e05180102070302010906110703 67
    0x90b003001d0181040340c0381c1164141e00c408103904440c0c00010b010000e10b1071310a018524a40003c0c0d0140e840640180001c1041c0d800308401000651000340391034202503c00000f1800341c128458654124002e00003090900310300b00350050b01811485103c2d85402c4203903139004089070044424244018240300f000c01190760484200c4c0d40050202d800c0640d02051035030154085c01c00383d80c000750000da829800209101d6031100c41401070607200008103642008095142303405080031009415010100802c110010382d4825114612500b4100030528001860010740c145200c5103043d00401e480704c0401081204980c041c1074100302c031405070001030525440e141e1031800b815501c440701d45820410300c0c030829880f110300a07805400800f1a0500c0041d8035028001d82001d44203507000f4461403080c03840100c00f034007100c640080a00c01c411003044610100c02c010700f030b018180100103501c840d0100b5142c802170004041590281e0008186c00c0141d1909104a03445c488002e4501603003440180d001a82c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 257957419 1250 257956169 257956229
    0x308091203061c050f060a05010510030506100e01090b0c0a050610031a040c0b07050d020d02030903030d050c0714031201090e060a0c03060918060b0105033c010e04050106 75
    0x100f100b420015883d1490007600c0d106240b4500310040c403034001044480d08107508070a0581e20117507a0780742e20710f000c00381c10340984005451550344a040540c0d448111071043c10400c6245130145400340708107030b0301d0002c0c16103030703100704c0742d601c00d0350012030901c1e0a02a041020540055400020840d0301c3d1541d1507910025803150123449071071a059010505014804000d9005845a034141c266038901da07241c020b5540314544881070141c05000350700c205203800801901c903d804054080c520301200e65010f02c000341030082007000c0c0041d060204102040c035000d111003400308003100550390380b100c5414504068205903c20310b50315040c038051041c14403000c20016000b401011002c190341120701000e40190095820010401d880c0401340360030350006031000d24841d40240c0b810031800c1c0c3c8440c01150315101c00c0b10440101550801616440d1803181d400129500440754003100070b1021810003414114280c2c010b60300c1c16858420312051103001c2c030a0000401d007400400c2c10300813125130000b580041c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 257958669 1250 257957419 257957449
    0x8090a05031609050a1e020d0605030102090f21160906080712110f100203090405061215090a08070303090b09010603051b01020102070804080a1b0308030f0c1303030809120306 77
    0x610381c4e0225070491182c0e04010301d86070507140c030703200c03035610b0610828020b420610b0090111400c0070000500c604041c4201d4041c1da1010b801c0660310051201400040755000740404840a104104a84a46028086c0300141030b21254a851b0451504603054140e440030740100b0306a0b00001c034100080d2146043c080e0141c0c1c0e015003101c02244400c7c00041c04039110900d1a60081d0106280302c007496070200080214080c201e804212030345807038060041d41e1000270311044507548241c038101c084070350703101115a00045840444045003602e54400c070041d041600102c011a881d9031131141082900c401495004940a000300021340c5175071501c4c3c3da2030001424582c5948011040d40c1080e91003901103d0045401a00c40b1750340350755038582c05503030340c0038090103449400c1680c0100d1803031041320245400712a000a0803c2c01c50300e40303407194100782c00050400004201704021011680780324502c00700041d802501d9299491500182030b9042c2a2100e00d003501c0e191080080007079998401200c3e0307404e52 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 257959919 1250 257958669 257958671
    0x30c13081b010c140d03050703061707050d02031009050a02010e1e09060f090117010b010203040605040612020c100501150c0201270b040b0a0f11150a11040308090a05031609 76
    0x40d42404c1c201d402103e1011641c00d80d00400300c031182620b8160b009640504003550301008030980e0760110321490740b9170088000303107604411800c00941c580140c0c1d109035180003c3c00d40307825141030802e020488803030345001c41c0c4a801c40005101590703048851941d16070b405880100e941528985c2101c1d0444051a07014420045400410744035220004011045040501205d4255031101d04a2112001c42084a4419800c1025040d0300c0d502c04000d6400329070070f50703c906003060b040c2030041d180e5a8460340988407955003440b0459104008100104260500d44000a1903506081411080c0401a0002024011980301010050342d0044000e20f83c00b80500070406802130075030780ca0001c12456440400ca54a0200d00031030440c9a4400416024500f034580c610141f46c5400d0035610a9000f00000e02d07a6042410210150111442d800c4d0380b1804000d000510a90106c08400d000d4010340c0098410b0751001c41c8070603480c1800e810140162108a001300013560b03010401310b41ca68940e0281c18105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 257961169 1250 257959919 257959937
    0x130c0c0609061e0902150712030e1c120c030b0609120a0609031e09031703190606030906060509060a0b07051c0507033002180402030c13081b01 63
    0x100c031050780310481c07643c0307010554405900c21040c14400780201d040103a02c00d15000082d00401e807034003c01c0301c20295100b42d2800b42109180f60a034002c01443c40c0c0e80d0718074000c502500a11070207904090703a00044503125203100c031020070007003400c4500c40300344002030501c2c100d010034869850005580640c20100c6412150401d01160b071800c2c2141820024645030404a400c010107803c65140d0b10103250034941003200d82c00c901402c4441001520014048281c10300b110803100c0881001164480d50424801070345001d82050b00048610541c002c400180d695a014001c220003070013220000c28045400c1100740c14540300003111003010b44140c102c0c030100003400e6000c003c4144400c0301c2d0240c4803840c00070490411100036000c3e40c48140101c000500c401b00001442141c130100c4241003680e0406400d02c0c0385d03401d2100000b58401e41c0e00c4000440442d000701050f581e140001d600c038115141c07503640c075111001054240706185409c0080c258010110b00255989118050411a9000d207480448 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 257962419 1250 257961169 257961173
    0x141b040f0b060f09090f160c050307020907030f0e03040b1614030d0609050601051801080c0d051003030e090702060a1503020423010f030203060c0f040f0602010b130c0c0609 76
    0x181490381c6416006440401c40407002070400028040c014005e41e00007045544203402c100030072a00329426520400803032101500a40708029440b00d6070312540840789004201d800003402040122640400240c884172003078050302050207805c440c1d250301340082d4100b5041000c2408217006660880f1901c100900c62802070080c010700c02020b9280000a40e40e40c1c41c0e87e0b0310f181d00900641d02440c140300d03007020301007150fa5204508944d041e003419101c5406c3d040140004460314000541459050f0750148404031101090b0311803540600102c007500d4101510754500a031190740c0d00810340d03110f018401c0802c041943c0110341d4590000ca4035000141d808018407000c2c5104540f0303040603400914241c048ca41c2e041c00c2c25180d90305036003041e170506640e81e60ba03091490641d10b2030000a4150304004041307030a64030003101800c41c0c6410104618200340d101d426002540906074824401030b911403034004058100348001209580504000f4009030a0300400509000c840410090503030742e5806203042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 257963669 1250 257962419 257962421
    0xa052d07031d0a080a0903020a030501050114060c0d0e301002030c04091e020d0b09090105010803040b0d061a191b030f0216120605010801092a150c141b040f 69
    0x10147d1742c0200740c03400003512801d080380204401d015242000c08802401c080510380b110031f03100054600001030001280400f022100c0c09084e00d83c1c20b4205101c1c8940200c03180c1d205058034000b00243c05060004006201c0081c41c000040c504115403600c100140725802e0080c200b01d4003551065480895400c1d541040d140d100900c40504030103c42c80821298800c54441d0003c10204004640c0c81007240c462469650881d5000c1c40303460302030b60040008014504845001d087d030301e0382c002e20019900340d5542610080c5d0310101c2d000128200e0000d8043c000711134848000c0d0b90801030b4500244521948520341d03402e03070750320b9201a0a22038120041d65004d48200240642e841d030b000302c17222030a81c1c0d4a100b101c40880300d5070704036011800c04c0008035050310141300d003c80703da802401004a0440d49400341a80090280c101003590001c102d01080d10b000714040402e0b1258030350365030074100f002410000b400e040300c1c40c2400090b4000e0395585030b04000d094842058040d04690004032413200c0c02d0307200c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 257964919 1250 257963669 257963687
    0x120304030b040803090c03011a040c03060504062c040f03140d060b030106020114090d0522030f030905040e0a080d0e060901060303030c02150a052d07031d0a080a 71
    0x80842441d18100300030806401c020703600503041d40045842e2480c8020406007a1640c2c0380d0003260b1001c50301c40c00c1609107002d4001c01c04c6062941400240f00ea114400311f000c0e9925030700403102000041d51900c2c05400341c0d4004140148141100c20358a0900366581c002c09c0d80d013200068100300d01000c0d24045d05084808072100d00e14800320410a440d0340d1b44548005030800d00c925400b651034035981c0c0c00c2ca0307030021a10921610310100580300f4216290415241070304000b1140074906a880d40051008010b14444009103016403001d440f40c2180e45402021075130b01c3c2d00043e001e1810401010003032800040c4200c00386a00c07981c92078503101c18403803100041c40f80420318131280c4070390410301c03514030019030011080d45d002e65414004147d6900060303070b81d0140200d1028640401c00001410000c40d644090b07000140c5904d40040e402460050801005820300300b00c030000801000c0c02182901032090700c41211400b07a07161085181000c6803a100c0c0c42035000904000c50000d2003141d50391291100c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 257966169 1250 257964919 257964923
    0x6070809090a05060901090e07151404030803042f0f0328150b0907050906040f090e0c090c070305030414070f06030b0301050c0403020f0a0b0d020d060b0c0c12030403 73
    0x80005480e02c0e2440c003028041c2510f950b4064003074140003003409801030043d07103855103c1704001c1c01014a0002d8211041145115410801c40c00d010344d40c160424201c000c10007940213070b050940f01e09107420903801244450502854141c0d012813014403005010050b4545883e08035200100c162803140480c1c10700609850740d00c0c0200c5a0700e0b400035004030203004030b03d8081c041c005612440d100041004200c9069000096001000e880011181da21440c010003030410043d102600f801d50303841e0714140006903138000750103e64540e04801600403081010420745274044482900da42443c0488062500c0742490140800a0000008051100110486c04080031010440e518965680040360031b10145000d082e00090418a5000039032805008031405000340c0500c3c0781c81c161842d07080000b911854140c964028402040004045072000060600b40121001c0903a4030340100502e40116201c5812006082c2c0b018413031000030100000d10058002c000b525404c8140c08101060351941c0a140c3c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 257967419 1250 257966169 257966179
    0x10142404050c0c3a020102040306020f0405120106060e01110a0b01121a090d0c06140403020c0f03070b03040602072301020a090501110604060b190905070f1106040206070809 76
    0xc1c0040003000e14000c2128501c04000c0e945900d0f1010300e44600140013600c0550302080b55000503503460001c04541d42c2006060000502d442d50f00d959400030b80e008403504c11501c3e0f40204040045043c201100c0b10304460b4100204203003400e044000e000303807008586a50400000800c1c52041400400000090355000790009203150781d5100b50480a0f5800102183d484c1100c1c1c0100750f801c940340a40c507009141e07070300140c0710b8214110011528000c0f84079095403401d1b1149107032902841c08140041c042c9000307074003030b246401c5000188080425901d43c0c4034069402010108482301d20442070740c0c0c0003580b2100250713030b0b014581030092034440b803c0640410116034200b609000c800560040c100002140c846610f920703034a03801501c0901d2481440c289030340004c400140059074a80c40240b041000030150640304142e5492016010706542229000340d0b6950203000e21039170403150340d60b0720803228984450381282c140341440d151800500000c0c018280403031400300b00101030701524222803010340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 257968669 1250 257967419 257967421
    0x20d0f0f0203070e0a0e040b0c12040308010509090f0a0f080c06070e0406140303070201030c1803030315080c0d030c0c03140a03031413170403020406030c081014240405 74
    0x140c008001d61065a00402055444448070f90303074240b0072490400c4401001d8403003034070b5513039440741080000e0080003d02c0c0b09004000c030b410203102559034580218040e80d11500c0f20b604100512a8805000d0145440d550111100d400c007080001040406d00394800328206000d04645070040c001e00072560a81030900407007040001e013550043c012000c2a03c00c44003423180175942c0c18052001900f411203a90542c000f00b080ea00954081d400810703047c840b5141440c0c82140c8000300051001e02c0f80c104030000b9032078102c11400d440c5070140080c06000b20030040c001c41c01c2c90000244018081850060601000030404820301000078401030095030400d010b01703046c640101102d80c440002000480201c5e2900005004591a0012040c410350342d00305083d0f0b00231b40d2a15400414183c00e00d03101114107040202000603160b0340070300c40045128404035650305080030500b03070810340c120f0528030219103030525201e0000c0025100d40d80015001d031080f1206009140a00c0c0c0300461812300d83d8000c1d082c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 257969919 1250 257968669 257968691
    0x606161b080304240c0f060e0c04020301090c0e040e0d110c04060f080f060f0c090301020906070807051b1005030a0e010903050910090b03061507062309030705060109020d0f 76
    0x900c2038400480034403142c51001d020401179031313240c8881c207000e00620f044c41aa400010000d5009241c1285002d04880c1548110f100003001d0707a2098000303084154840b0281c0e174616400942004941d10101e80c207001100c10042c106680d5009a141082042a00c400d03403007030303803d05002c041820000038100f03000740e0b0340303a2200000414080c828564688100c5009040303001c40030400900480030280380794500c1c2c4522100d548240c204040081d85554200300c20081c0d5501e0f40c00800f02280f03d80052500c822540c01d01c1030030042d9450803590214466900d10324075960b46022a045000c0c039040080d1203031145030303820340104200202144250310f4030302450141900300010344200e103000c981031252024100c0c0c007141c0c1180c040c440c038442e061091020900502e8588803000e00f00e00c4064980d170809005441d00700a07200481024a8840f80c0103500b50400020940c620750b0003011400118500702080c0c2d0b40301e0f9655030502c150100c450340850742c5070381c202d51504105180788034a801482054100707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 257971169 1250 257969919 257969939
    0x13110604080f0c13050702061803090307030c080d020708030a032309070e0612030403060c020109080d020a02060a0203060d0209100504020f03150a0e040b0601051903090b0606161b080304 82
    0x911035a80c1310300c0070916070403549015405445d10403615603020304007948a96021841a400103500c0005502041c420074100352400c1020350015401603140d90441454039a060b030900104859900464200103024440050b000081300d0761741c0110318000071f00748031860903070204511a881e44400c1c103c4150601c541140001510780c103651030400c0744040360b00ca590401a002d0b154600c10070300ba410600042000c1001640310700d07100c906600002c13496021691b1890b00355801601020741c0030341d000c242840a20380c100201c682c0a10751400852071410007000040c0c0700b200720b0300000c2c850381d001ca001511940000002d0f5005140281c015502c0314032081c111600341d04206c450215071201b0038201c600381d1030b10308507080490f100251709841035105c80d140c99100c22001400d060500000f040625516503141c0807540c4900350556000030402c0462030583c0b50140c01401c40c40c49254240002c401e4801c1c40104051115446280140f03a02512019405201e40d10b5114281c02d00000c10300048400e04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 257972419 1250 257971169 257971183
    0x30905010b10021e280c0f0b0415020718020a021b2211070303060504051f0902090d0b250518010c031e02100e010513110604080f 57
    0x21420080c002504280203208440705941400e00042c2c0c00307814a643d40385052004040b08024100a4402c500c49a10400800342d512212031751400154683c0d410510188400c01d001402d0480d90040401d85810789000040c0628051101e2800b42e118618103024020041c000c020410040c21291380300d0140400402034101c3e2410001501400c81008040040e08440c10b0450744000c086000f211251900d5001880b03420103400e540666031000c0485a0310100040c01d0f00038032035075003c02c11500300f800b4001903860140004488a660b40c6074585a81d140c200b101003640d514040050f00c032580c2200007900503214500240c5020101c0060007503e441c02da0301c48050020080c9800580c96145a08403494441e0074505442c806200c14180c800303611804444050b0740c040d140511031109044d80610b00c00c0d5038000c1440c0542d00180d0310034511003c0340220650604000c008125500d401031100003409600880207005640c20743c42c1307c440b5a0f0311001e6501a0062008032a000c40103e002a40e5401e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 257973669 1250 257972419 257972423
    0x3060426040b0d05060111060f0115051e090103020702190321050904051512010b030d0c0302120a030914030a02060c032203030f0c021c030203040b04080c19030309 72
    0x45400c0800c55100c400c0c01100c08980c82c480c012403519061544000080a02400c003504100805036030340e4040d841048068011035282d0044c001c1e075454140d0039030398824001c81d417030180302d02841540136207803412015214044050001d10390754192000124028400c07524000c1d400600c0410040c1001c0e0303000e48440070349128100107203080070115803811352807111251440005100700942c1016080c550010f41d00b043c2c0120003458521100300005103252170344580c0d20250f079503d81511480703140c100400051a021800d0161406016403002501c840d01d416074140b1440001401b084124400c3c0c0c802c054441d0000f5040d0100044003c2042d2030f035102100792001881403401003800300c0703641c000300c9004020181041240446201108101c4142d6031025010725903a40c0310019950b440f80605020f14080740e010300b030403155109440d807603401804400c0d402c15105200b0000002c101d00c42c0da640141c0c011410300e840d12006602c01d03181c0020080c01c0c81d90b0401070056a8105505501b0510000d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 257974919 1250 257973669 257973713
    0x3181f02180a030b13030c0b07030920062a030a0206090c06040e040b0a0e0105270a08031801090c09090b160f0c2102030702130e030406120b030604 65
    0x21541040220300043c08040c0000d00f018000c10040340110302c120500c103219041c00d00d0113a003191030388058000101c40c034401080c0c86a4240d41044140526540c070a15400f1200c00d01180103008241c6034001e044000d42c012483c02101c05c401440403024118500328042200d555100050000351181d5017030766800002d1080200200c00c40c1341100c2a0b400340d40008400000700e0b075881d1030b68031030114040c0014030170710340d0f54007401d40c440402c0c0a40361040705890302052106041c5090549018208103030780c4c0c1c01340c020ba00c2150000310008101e80d0410401d91820b10089100f8500a0051a9401009103040c0039803100103a4100244c002c0580305010b81d211401c06c2d41c40c400da40344000300454019000411364490249240e005466507550580503404890041030086880600c01c280c0b10260030250744003141e4141140b07012040701c5c400004804082c800e80d00340f859043d0f5240074034007c0c20280841840700c84540341b00c0b54481c03017000000504032500c03402c2c0703410550031050080540034841 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 257976169 1250 257974919 257974957
    0xa15090e0906092e060f06020f0307110103150b030a1b020309010c030f0504030506040809190e060d02060c010f0e1b090105040203090c0303030403050c06130803181f02 74
    0x203101289040c4200341e10030181c1482c50258a01d02022040c0d001130f4490321404256030b58078a401445440d010b001418140c000d82800d14002078600000140c580d9140d90042014030f00240c01101c404885070b8082c20089407241c1006d0b00b00c041c0030000d81005001400200c1040308100c090382000e05104c0a10001140c41e100380b14080740c0b40e124804420340403a10140c0a030300001d100718480c080ca044c0500c0d201e814140c49944450a110043d60242d58641001c02c40d0310307a80c0f034001b000d9507041982a01c0140018548201100005c0e0b0041050b449100001000001d40d190030089490b04d00d40100204604004140400003d00b0700101d10380c030341d200b08140340c001035410708000030b10700314005c1000003541e1800c010170000c0d41c0010521155800b0b07414030101e098508201550007148039844c0d00d84c03500040c254051500700018852044201e1560704a000704141c942182d80110072001c0c0d01c00080d00329000c4a14002c04055034001c40000904a06000482540138020807695401c4d0340c2a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 257977419 1250 257976169 257976181
    0x201020304060b09130b07020f10020d0c030e06040305031510080f010b2104080c0a080315030607143109140f0105011209050106030c03021c1e020a15090e 68
    0x441c13542100c402c403104007011070250124031516149a8003011a10403900c0d8083c0b8548240d0030b024214544d0a06c454000c10189801d8400c1c0c01001c0d90a11141740c204001d045103101c441d13958501600c090140880003001c01c0411107401026010054050011410600c410600a01d08042190049403810102d000072984241340c0c4100d07484400d00c80b4100d1740115508848070b5142d1400303007003110304400030040184d00b40c1e400c0c00740410440c09910519144e00d412403c400f071880b000405148030b07801090410070361603001031125410750300300c14800c1d1311a00300001101140103680d04046a04003095a4800c0741d442070704d031460507035400c82014000142105414189204151a03000c0013180004c01030000d54030a5850300492050078030042151401510740508440158000b9030301170100b03071001d1065080440907821100c020022084d01100c850f190340e8030303032030081d10360003003100f600b220802c29541c510701090081e0604900b400500c84200501030300007801c611075820f03011401000196 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 257978669 1250 257977419 257977429
    0x4030b0a180201020304060f020a120201050f01270b061b0708010b09040b0c070510060605030a060501080f150402071401091a0c070201050d0f020310060e03010204050a0905090109020607030201020304060b 90
    0x780581d03060b0000c40c2400e04168069400907098001c0ea07045101d42c0c0503880218600c030070f060305d6079041c9400010749410583c03803004005605800010042d283d10a010580c2803202c1d4130020951200d000014003240c04a000414a21510010030000c609009070f640942c200400c45c20200d990b03800c001c0044004460030301c6200c25048402130b003184021030000e40b0140886d00140301643c410b10580d8a4401d505041000b05d410340c0d0400310000c0c0002c004c10071032410700d00c17480c3c0280c8000d092031010780c5800e00040354040310040c01800c000b000300b0901c50103034940e038041d81c10756a44102040d9103042c0a2801d2402060894000c0e10003943e034803896041c540c1c164030002e005030b500070241441c0106a800564a40e80207118101045940d0a401083c50350584051806400d8070101c90405074984a4000c102004440e020f42c4646d1042104100903030300c0402507811940090804030711036581c01400c0303004049580010f0742017040008e0709410194190300440c80389220301e03404c208030540c541c2400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 257979919 1250 257978669 257978711
    0x130c0e010221030a05060f030304030f020910150c020109050a1d0c040503030a0c0c05040504030203070203100b060d0e010906141f050117091e0a230712051204030b0a 73
    0x3401030a42000404c104401940000d0380c08100948a400048044004a45186d109502c02e884a04800154804501d440701005412003a8401c1c100d201d0703410041e04104242401000e0018003001080a000316405003110360006c01e00144071004c105c0c5e4966100e00407a44550365001c03a40002d10004490b000301c10162826144094015170038500c00301c5003a2190341d100b1100751481c2080e41d20000305a555801036601c540c1c840e50145842e039a05205041c9003024601542c0603041c206400508591034040682d40065010040801c0140100417100d00608111001034803160034000071001e000e810b062464061541c1c070201100001c1103034200c1345040d49a016050000c1d140e0258201702180c1e910a90380c00c2003c20741038071904200340140c1782100b074440600303c0c0d4503005845080d06018804071454441004286160048858400a15103442880c0034059402225140c2c44080c08400c0203a0410080b84a4035247e0322504c82c00e000e107403644d044655010342401c0c4100320304500000e030460 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 257981169 1250 257979919 257979973
    0x30c1719150e012105030f0a0e0d050c0105070f0605010b07050706022107020f0a0e060f0409170705030f030106030b0a050d0c030825060b0102010e0607021209130c0e0102 75
    0xc954640d0030444c4900441da40c02c00d0484214503282e40c000d01040b0300744011f001013030301c103903819940e00c1010401501c2100b0581045101e582400400300100d00040303000d500541007440d10340d507140f90a14040b03000c05030300b40018060500c4c0c03100100f000c0707010710010040345014a080b102d400750380f450100d13038a60301c2d14031220307560000c1d04054000c0c00e524030191001ba880240708281821036400400d4540042e0b500c54511010030406000442c104080581c1107214107950901c652000380d103404000b42c140d030300d420902d1000011500b00b480018010b49141000c44031040c4e50702d59440200070301401c0c8004010748140e04a1400261070321386132190030726a5a0042e9510912b62131920341c100f0617042101c81030713a125003915040c00d0101110400461035407191000003101c0d55200300081c00c542d10040d08880c036511100a101c400754000680c10101405020740c0c0366107010070004284180705501d0200a2a424803904408c80e58201901c000405002e900716190740b100070003028510481c91410b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 257982419 1250 257981169 257981189
    0x10b0409180b070f09140d080919080a020a0603021815040801020403080705011508100e16030b150306010b12060f0612010f0602030f0a030c171915 65
    0x8100040384080d08008090185891035450a00040d100c034070881004403109000103043d0034078100440c1d04a5401409421070740c0750b250600b041400812480348007003202422500003c50300259907620300341065100c0300100d1000d61302e00e545419040c1d071082d180500f24811803041c08040743e140e10030320a40c0c100c540c800f2400905800303c80140121841103030781ca4440030904100103d01c0140c01d00003040210700c90006259680e102e41440c03403c445c83ca010011945c02013040c2009030060016601d584c60040744000261041205003092404114480a242d044908840002407001c2041c00c2c0f4841c58400e10ba85146582040406888001c24000c94500090a01044882400d11500c0f03681c084005086d22640840f0000028001d80050751045c681101040041c0180c0800c0001c010003841240001c6041080c01800e01109001d4000d01d03100301035603500c04a107102e01c203680142d40b01007900441300c03481c24882c1c00100c4410002440c1900181488500d10141c0007a1584104880007000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 257983669 1250 257982419 257982427
    0x3020d0206150f040906020310030201020f0a03090e2203030c030c02060c03072007030501091b050f0904060b040e0d02010c050712030b0120010605011d031513050601030524010b 78
    0x4010580c81c448603c3c1d5085665000c1420018200e4801135002c1c02030f01481290300340c99440024034024028032115102d0700041e43c80740009030841240000da412480300700e0519070780d00d40e5903100f24507050740c81240908502d25550515800d80e001c1003964690f56400d004a081c02002642d81e6541600c0b007aa00b10400c100183c0c14078032840c81c205e0806040c01030074004485004a040c500b40d490342082d0342c02c1c0d40d985441410024000d00c42c03000c0550100d034450720b8504c0e01c0d0010380740800d00c070109401209804002030400560364801d1188005c0200104803260304070343c0b460344d10106c007d0400c2c090740ca0000d00711546401102a605202d61101c989500b003400c069080b0003501d031a401040c148601c0c4240c90366403810b0b890b003204a20a0800000650514100c001080300220048501079540000c95004032600d0100300c5800b40140001c3c2c4c0e80307081c2c0f103103894005e181d01c1c8803202800600030000048100980881c0c0310a0244113040c0000b8824070441040e031000304280301e240d0792080200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 257984919 1250 257983669 257983711
    0xd1b061401050108150d140109050105180616020304090b0d050109030806040b2b062d1d030d0c050412110f06090a270f050907060f020a151b050703020d0206 69
    0xb5070700a00300301000027080b4080c00f03035074032400c1d120251108107040c44661a01d0f00d002008200e040d40c05a42ca40e03041c2c0158448880103500c911560103040e10558440c00c0c41c1603603444105003110250b51017802000b0301c005500300104040f40176500b0134407c40c14071001c203a0302d20b042c0d09a084000c4040c032a8900d1040c1d40411003424640c1c0d0783c4100d03000c0b030322400d08680312000c0c0c00c0410804080410300b882c0c40441d03038a150044a000d0404406031565100c0c6407201040004152050b910711a04001501d0860003000d640b00d0060364845001d00d05511b54801c20481c100303036070140d840d2007071f500c2000d071840000c10092540030300b0290b00c1e0080c40c8140200a0b0034560040180854610341419503180d03803282c0044180c2e910440d0780c05c1d10548600610841050030008480100a145402000c0c05005e2030001e4650b0703a0088041c04200000d070707001d15400111f9005042800c90706800013040316007104d000d400f54101310401e0300503020310550201294004035480b88283d403110082c441c0a5581c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 257986169 1250 257984919 257984933
    0x501060e060306040f090506040c0608040c0618051509090112210c2018010501090b0a030209031e160b1c020c060f1501110d1b061401050108150d 64
    0x1043c141d401354489180900c400260b120311401640214040c0c07205103403c1c1065600c50403540e00036400c0180b030404004c0410701035644031050311024902141b0840c0c4102d803160b40410981c0000d03500040c8a484e0615900d1100000c1110f80c50546241d0116a82d600028080d040c4802c0040c000c401a10125901d007a0072007184031010581d400d1000c1184490340300e080c1f240342450915400c1c0020b940c0020103901d0b24400c0c00e1b0750070480c41c4054480750304000c0003c1000d0b84510440800300f0001c00d54052560180e0165068044050104c8000c40400030ba51000d00903914000140ca0044240460302d01c3d06400b0003500fa0b40b2620802071410007100c0342c0c0c1d24100144040d05070025800e00504c4c1c1d04a10600c01c0c1401184026000659820148038801d400314405e50740c3c905204040c22141200c481c0456210034410403810031990b206400c044240c0c105110300e4000b010309113042c841d01c1100b00074140560603200282c0c1c130100c540e501d05032441d42c0180c00303140d6254421204c42d41c182c00200742c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 257987419 1250 257986169 257986171
    0x303040501030c09150309060b09060d08030702010b1305040b100f0b1305120c011b0302060402040c18060203340204150506120603060a0212160c0b0a020901020c040501060e0603 78
    0xb080c902040c0c405d65079103048107001541c41100000a4945202c4020b200c1c141c01500c0514504540518840c24801d0018414110303c40700240528408000201807034002e500041000d400a8145900c802000001c10007c08040f84c080780e20340300d103101144884032980d1048040c1d400981e459a4010305117000300e01c85401c02000f500003408262404200c40c1c40c0c807149012180340e270710002e107100780d10f40f0000761070003040c890807454080a2131041d10102e6400a03e5581003601030390009031350100a001107a1014440c03480c0000c0d14101c8000080199000006000000c4000012080c0d01054002000e0203951059869020140c208400340586826484200700d0081d503002c603980d0329620030128000c0d801c00340d000700001c03030a4020030000341024000e1650001075600c00310724010445442090282020f08260148550a8100140399000301c1c49161082e4100c030350b12203d45087c1d510f1034003030740c450700c00740c3d006000c3c03840b07113000c6400c007800b441d8140c3d082038454458a00c0031000b48400c0b908 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 257988669 1250 257987419 257987441
    0x40c0e01080a15020f07050c0906060a120b030a06020a0504080c030d05040608090a02040e0a0c0f050d1412030109060501110d080a0c0516030905120d050406050913110c1209030304050103 82
    0x340c200424031241d088000108440c0344204050b10780108d00300108010050000c001d5400392400b0410022001e0340002640c0440f00c1204000800c6403503500440c0c40c00362801c0e40201140d20005001c0c21240e040400381044408030b20442d03060814a60078542c0701c84004507540c003c164140000d1280c0d5020b1b0001a074407424140440d01100cc5076000070f02a41e03e044540651031700101042401c1c400031030349400140003c100450080341c5801e01161811046200190902a11103800003082000f44162031054210080307447e203d58455160000400c114070500b40881c0d40b00343e0021038000301082c404103000080d103c04189948024110024014034403107441040310030440d410b0842110490041014041e5a40008550900b8240090f0001c0d0241c6200303d030707000a15141c01154020201c80a603000342c50407540305d81c0c4081c04900c0c44c84010f40802d5019040103d8028405a840040d0030200c010030201d0f902940c0141303815146210300c2202b1340e00760304100018811035002e9044001d101c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 257989919 1250 257988669 257988671
    0x806090919020f0d050d0504211203050709031407091802030c01030c02212d040618170d030c03020c060f040f0b0a0b0109090219180803070b040c0e01080a15 69
    0x2003190303440301e00b1b00310000300310f00c08120f01141c10300c070031188900c0c40b02105104c0f100171034601c1e2242e22404c844131020041c400805440d54002840390b4400d2420500442c0e100c41c5c4860048a440002901d5064a01600c80d0ba1860490081c07410280001840d042c01c2c0c028024045070004400114080d0803606044410340c070940c1c1c16500949551814000326800d004140e540350030b802c441d4031807204169a40d2440414152122141021156040b00e00312145400c0076520310501d04101ca000f030713040798801c01c1401d00c0180802045180030a0381c140c082d2080d0f5080080408070f0006404074018030901d40b8084d4444e030009500e1006404155810a0040e4403580311aa0181c0d035070610004101d50100c07a40c0d45590110029507000b2024501070011600c0640c10b1508401180c3c80c2981200f0203c810482c03003d102508118200e83c0c1c41d000f41001d038054907038521079804d151744440d40588048500c00d02c0f5480000b4168800d03819030341130307400308006003c2c3d00d03240fa00c50399080b1807e02080301c101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 257991169 1250 257989919 257989939
    0x1170403140a0c140a0c27060b0d06050603190513050a0f11030a080306090a09080a031505030303010f0302010507081908060924040e0106030b070806090919020f 71
    0x52142030003401d00d00c020b039603811404040e14500005145038008015019610085138880000c400642500596010441600202101c0d0301400107a03c81407502d412498034004001c18607101d110010001084203a400b4003c899803802840054881143e40c0c00e0040c00f600e0a40101602640026821541c0444100b074003200a40380c05003095074440e0100e0760b845800ca560390400c2440c102a100d017400032000744c8082296602c40c46070605c070060038148114084800200754401940c04500c40c6034104900588405117403a000d00204041f800d92001b903003195100007000d24000003228145c94001001c074030068038542c0155402c0d00b110608840b500c0c41400000d0748907a0340178060254000507500d00c1004e04091013406050340d0050319102c0405803410b8030400c2c1200340d1003403a80408017902c000079001f400142403401041c7ca600020302541c41035013440f82c01540305084500615085a000489480c0c00b1082a40d4451000c2000d1070800030814540161511209441e442c0b54050710210f04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 257992419 1250 257991169 257991197
    0x114071104020f090114030c070f050a06090507140f0a05060901051b0a06050a020310142709190f020105070f02030f0d02010b0a0602030d0c020c130e060a02070201170403 75
    0xd80e0044440074600c03c00c041466000d07503070300035031040e61414000100d03482d500b060144e1102c0c52140c10030182001f07400340300c100c040142c10000c140c1d880d5007040d000c00687d0110b107040c03a120040ca1043c4003001452104000c81c2e443c0c40c0d9940c0d0f4030210001d01c824401c51400c01440420b030032200c0c1c0c05060000920100420160100900501441480152840024514100e011a207003d0402051030340306004104156192a0f01c00099481d60290201030418810001d4100c42c042c00b200f102c211501d894009901d03040300c1025000d00e02c8981039034101d000400700c0d03030400c440d9024090300034030580140b44050f5000f84011300409004448407490320181d41c012a1a0481d40080701c1120b61003c0f41d0010309903428030030b24400410031902c150f6141d107000c100035a01c1c000e0718908041595515a0b20090758020042055000c0303020701000d51082d4280c00310300003403c8416107038134980100c6000a0914840b40300312080103505840e05001008000c0d419403551000810403014040c040d20500740c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 257993669 1250 257992419 257992421
    0x9051012050105010905070c0b0403030b2b0507120302150703090812060a050603010501051b0a0b1f0f210501060812070c0506030108030708030703152d050114071104 73
    0x103400e00880020a407945408100801c492005100d201040380c03060208000078010042107070030541600d40842c1c441240c01c0090710308140d01d140b403024980c04030714000e0807041d1070810404003030203082941d0001d69074414070b9929591100004005070401d401200e0100403074101d2980121a80c81c0006444800e5541c540036540722028040c000d040030401c201051038900d9000340500800e40e80c02c0e043d54580400601a4043e0301c04070300c2c2c02004200e4060b8003400412040414a03003014041c2c3e441c1c1001482c0b60340802841d1489041c0c51603000c00490717002c20200c090004c0303841110326030b8405107462045904883c3c0d040e20445945d520360b540024103800800085d00300b48586043e0550303d42d9245491148443d01d90b0000d13010380020310042080716008001e4404e00c94000d9503c51b0f8075560580c08800500e03040c0500315011400c09000700740d207146086034440d41c100020f9450001c080003000c1c072545901600c1510b0000e070901846405400c4103401034034a4038401d41c4603c2d400c0d41c0e2080050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 257994919 1250 257993669 257993699
    0x702090103030e0906010e01090909020111070b12070804050c100519030c090f0e0402120f0f060a0501120f1202190510051006050301050f0a030501150510090b04090510 74
    0x14000920303603211050075103404c29020781c000030300742024600740181e1000030b0440300e01d61003908c00803903079501200e082d6400303200c0414031100241c0030b459003182c440711860b07069004400721790b8504200800044803203000e8201140201d4100006041d02450340040000648108001d1420030009108031034201c2c00e00301401240b10038640380030030081c00d4030fa0000c02e1500c06500500c0030000310b0304200300c640c55004115801c103406840c0f1100c1200495501440c00030001c840003494415011900701000011503480e025128610060000c1e076030f909603244602c00c0440c4050007615640c140c106c0047e0b4115000c2c0b5070b032040c6005969001c1d189402103d00e001e0010b009880640141c04064a00e1045104451380103201d60302689009003810b000a115000501500303005040c600440c15050740e4011022000319441002445510404a0741c0303600148240710b05c501a4032000b031100302c02405500c92001b90764040c0c48250510f468890050003a10000c2d003907030041c2070310300c1000c2106442001b0070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 257996169 1250 257994919 257994923
    0x5130b0a050114061e0d060503150708150102100c03150b120a05190c0302040b04260f0d0c11030a050610050301090c050f03010f020c0a02010210020c06010303140702090103 76
    0x110796160510031404041d403603142510608040107824450050400c0400700511410090f036100c2d10aa1540350003000e1035009958140316900d14100842c400d099098032401456680e180350b0345407590030701d21398040981d0442c0940c00c9804007200c031501ba5407080c0104152440c002c0741e40e14115070b050708005041e401440f100b20300001d203201076440040115030445d84991041040d0f2520f0520150000700006211103c240c6901c0d1214005203e5010346024005030720003d555542e840c1816140021010481000800000a81702160001042401202c000b001c041d258500d44213030103d484150031402101d14540580381d1904580f010041202c10358071540040c100d904061084403200026640040d100380c0c1000320201c00182034500480483c6c006035003401180303c01e000040d002d40f203413401c1c101d040342c4041102041c42d07500045414030a8002c1c1c007500d41c0b1900192040c410b82c4900d01c1c2c4945668000001080081d105105008900340381420550411821354002441d055080c0c3c81 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 257997419 1250 257996169 257996171
    0x90117090a0605090705010c03120213180b040b30030703170f0c0d091a04030e0a050f1e0102030d020c0312090a03080f070e030111070b060d0b010905130b0a 69
    0x481c01c029062080070b4006100c03c00a0111a2411000034034001300548000c04101c02c25400d807008940e240c041d140080d44591002c40701399141d4804c0c2500481c0303182100d500c5400c200503118a0308261150280242c009040e13542d0110b602c0c4c1020745140a10b11082150495041e010202010180080c2c000d071072080e90380c10040701c05001403c558030b0010b40248268009801030100d04200c1408561001c1d00c016408a00e0000b1030401240d40d1100c54000072807d0000c00401c420142c0c01146100d481e0821184085500c0d160310a001443c01c1d4440e40030341003400803400c01c03c001c10301020300004a50500c122460500c040d54080182e8010070301000d11a44081282c000b1082d6140046501c51300445c0282010410b43d2402803201901038a01840341e01600080350340c8500c01d60424115080140003805110a004242c441d598894142030701c40c2c0d440500450380b13a1914180000300e0326001100c181080e401d1025a00040c04050701085a220354152030400207540c13100d015214101c9140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 257998669 1250 257997419 257997433
    0x20060c0609030d060509010b03040b04031b230f03030a0e010e0d0503010305010c0816082518050603040309140402270306090c06040311030a05011e1104030c050609011709 75
    0x480c102942c2103074000d9442044040c6c014808000318a00b80c86d80917070007401e000025115070500356645a000204490b00311070340c1d1903003001c1c4070001800241d640200c1c241d01600031903443e079580d10741c4101c00c441d800755041040800d90048154220b84c000340e0054000090b50000b0401a9241c4a54901d01201080d8088010010b00c4828810344441c5900d90400c0b00b8a85030843c40301118455a61040040c4642400451711100b0035880c0c50f002c0004084404108142188002c0d01190300310005806055107141c02140c1402c004040d6406690b140e01c0d6284042d08010388044001c6000241d150020b60038049170180215089079103d00c000c90680143d9811102c201341401d08400904910a40c0d00040842280313031612021a02200d412514520000c01c0b040000390800250440183c40c41d0300300400a0400c51048aa1140350301010303004000c00d003807607400900b881c000c070300c0060001c0307006d40350410150401c5c41c0102040801450302100d0a92850f40480c0d0b1240199103121481e44040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 257999919 1250 257998669 257998687
    0x609060c17160c0602150406051b0301090207050118020913030e031b03010507140306040906020408251202010801060302280f0e09040503070609051504030201140703020720060c060903 81
    0x110003c0090709051020b4410710b40094075400c00200302820003850f042d503036000035080310480c220040003408000d603144d036256510000c43c0e0183d004900140d5803946002c0142022410000400c00717070f10340c080d00701a401d40c1c44801b25105020310f200d007601030080e6003a540200d40d03420712010b01221403100d08400501100c00501d401c65000401c120184920020840040c0e12800c050344e0b4030050490b408074214046250a4010740a954042d03001d5204040c440c44200ba4500840310605613039070110211345a694044441003008036502a001c40d40140c01840014441e80040a50086152988540f03040e1242c2c004503040101c250800041d0300c0015405140740e100400c2c00c402407040b02d0b40c000ca0f04203070321020b850340b1888d4001005c1b65650f0240c7d10070004180070558140c56650502240f61500b418060b010b050040e0f038005900c4c0300c1000283c6400d00038400e986101d42c0048940d240322f1544080706001c500c01022540c7e020030300b03210f9400440786c01c124452154480401458483c41c0c05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 258001169 1250 257999919 257999933
    0x230a061b0609050a03110610171005040b040506060603130305031e10030b0705070507051c0c170c01080708270706050d0b0f10050306010507060608060f0f010609060c1716 75
    0x141e0507081b800d0300450300f0310451540c441c01d414155942d401a03400d600140000d418909008010700002c1035040070100424800b041030158411b501030003d030b4034183d44075020080c20380300484044059000c1401207202003031044003c0d5074414115880c034180d1b01c00940700702001040c105e41083c495044541d052040104a801598012800f41000c504000e1036660329511038066001d050f0250080e98080036041c2440c0307030300b007994030341045140180c240c4588081211005081d04400f0902c5a00b0848107554070415200d4452121580c800001e500e40501e541009540c3c00c881006031000101c1601e40c8200512a141c001e1940e5201c8503520104200d000e015183ca10102c103108200706162030905403a6080e01c4100b454191400d55540d985400042e2114024100043c00341860400d012a818000003485c5009102c01c030074105280d80c4030406080e20020074017070f5600080d442a0b041091034050911005807520801aa18180660a065414503002888681d81d130381845883c0c041800a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 258002419 1250 258001169 258001187
    0x5030f0d0903110f03070803091c112103040803090109080d091a04030903030807030e0a06020c010b04062402150906040201110f0606010804110405070504230a061b0609050a03 77
    0x10f82c4000e00700703c1203002c0c0d94503140c0c01000c0c009005118000001401802c06000102c1c0d0320154500c0c800400e40e150000400c08000c0e410044020320400407200c204003040024071050f00c1305100c01e94a507030358554410900c0e03000503240080700d40d200c0c00d01000040300e560250049000c81800000c0300c404605040d511140460010316820040c002800b000c43d600ca400030094030b805050016190711405822801001e0340020140f1900035018180100b1420f07400401180000708002d201c6420404100000c9403414400c040c0d040c01c041c410305c110060b00188401a80b6032600696100c81e04220845080e01421280c204003500b1810400045603000800c901d044e130042e07401040c442400224180e034070380d00501010305000150300001d08002011405185114010b0300138032260902080140c015000341c00b515280c940170404140302e0110000301016880e2004080c1d042c0c0c203103000426102400c80400c080805051140031740041680390003020f0349640321b60000e200c40901c2e41802844204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 258003669 1250 258002419 258002447
    0xf2107060801050d0b040215030f0f0703150e060402070606080a140312010501080c04081608060a0e0316020604030c2301050c0d200d03151e090905030f0d0903 70
    0x4100001842151503010036000f02945c09200c440681d19640001000345100285462020b40000104641c1d04925a0170500600d0780200456403501d805000390140d500e60007242501440b050020480c0803401d501031908444007400c01807904030385444e03400542c1e50395007004920358440c01c038a500300141d02c00b0b004503c108010145080c00100c0000f20003640041c85820304002d0300300003044c10300c140401150014000e410884026840140315281380d2400741c80350708140d00a600014140359101d001d20442c62030031030051881d01d40703602490481d80c1c40c1e00b04140d8100030240800b03c0081c7d20f02d607481014042e151741d40381e2a1224017440800c08440c0c0c003800c5040110900949240310302c00210a5143d42d45030404440449402c0e0001e1703504441000039544070701c15801d03401c0c05143c0540c0212110806440c584c0002c507220120b00c0020020800d4810760914006020002c48425134802d2040f648190140c07454030080c0343c1c0c4030b41550440011711280d950350340b810348205034021415145002c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 258004919 1250 258003669 258003677
    0x1020c01020c1c142a0a0b0601090f032019080d0315090216150e1c08070807050706060303080601080a09030203030a020d0f06080312010915050f0f210706 68
    0x849002d02c000c056102d10444c01020250106405c80f1050040c000100310003441d50f0700015a107000042c1c1660340080440940c0c0c200c0000d404105a94400c0600900343d903c100c07808242a4076554400065a000308860100c14044080b85a61655100385106000b00c942800b100600e04203c1300c01d040c200003a45450038946040102200000c1c810710000c119a11154016122900016a03004400603c41c0c024580c05107000210030030b0f10254480c07400380507010215602040011074101940000c08495404a400e1100007901207110304079196000020345030031f500f0074400d59200e0040d9085334204502040100d0104603981d6031220032150722003a40e41041c014070b0011348000c3d490b40301c040c002e4010a13800140b102020310b09a0041000c24038030322010003800d03a0300c1080c00d4981c0c200c1310816149603185000019400b04601408980d582141541d410341489c1000300b0000052018106400c440c514011070749650750010141e2034042c0d058810a500440c0700300319030402c1c03500d0b00304400744 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 258006169 1250 258004919 258004963
    0x5090d020606010e01080606160501020c0d03051014010c060504150516120c090506130302030d1106060918010f05160504080718110f0a0e0f0906041a0301020c01020c 73
    0x160f84c0018482035042080c00c041400d82c4038000403620030f200364203000460000c1c0380c9259040040c1503000344229040c080a503059101803100440c20340e1001c0e81d20600c0a1101c1c0424801001104400e4116072414180842d8040c080d656074803d5030030884064030b0000340908010056512406401d500c0404076008008401039244094420030441d4803242030a565100080441c078000c0b60214064440100040d8030341c0e4805046002e00d201c40c0c00228040d028001c043c402d514090460b0204010204000d820299a14030900040840040803050400c03407484c40c940001d2400e100d00381e1141c844400104d03c0d480c2c07503056600b40200410400080110400040080210106404080c0c0301d10841d080c1108003d10f500720040d051400b00b0115281e0b00080b00c1e00140c1840d0010120000b940d20b81c40c42d000c041c0401c00c1842ea103455203c1c0e0700300015100040c1c0354a403550100d0652100c00242001d41440140403a0032a0031400d01d2a60581d800507288500e0030042049080411003503e1034440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 258007419 1250 258006169 258006181
    0x81005060f10080a050a0e15060301060927020319060905060709061403060f0a0f06030f090b07110a0b010602071e05060a0f0c0f0807060f05040803060f041b020105090d0206 76
    0x1c3c200404080880c1d50740e6011907403405050b0003030550366040d20220b41c014070714000070018010040d6030301d610035817800c031000403035050030302414071181913000c08050248026907203031001440e041c3e800ca07414007a0160b51650a01101403c82d0340d6401050300040046107403900341d04d402ca01800318014411089410412070740d0011420101000c04000c0039280d4840c00b022131040d64602d81080c0e801208202d0100c6d10f00c01c0400300c01d080320483e580c140301c5084001e00d22011220420340191070320650740c00040c3c0d201e000390381504150003c0c2c07040710074803071064075038401c1c100003a0070040040c5c01c100010418102c015005141080d60b042070b83c49002c1c540f0000414510440c1400014450150a501c40803409600341000003a082810005084607515021303000303a20140341224518540114969030076018071903588920b5000d9001480c41d10b48008102c03541c03240801046e440bd845810701c21001307102030045965800150004585414460502c50605403ca41e4160466103c0c008001d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 258008669 1250 258007419 258007427
    0x3070201050f0402240904140615040303090e04030c170901020d0923060705060106020606042a0302090f0a080604050c030f03030106050a03110a020a12020a0209010e090106081005060f10 82
    0x11740070000660165a01038003811100203402021b500e50b601510740141c1d11a40400945924420703001100c0d10603404818010b4902c55002d280805030004008074002e00c01c140000e142180c00c58005d00300f16807a0420780c0c1d0341700d40101c503401c1d0782c101241010481034025601089084040e1709141001e40d44203040066032200c404101c002200507501400c1200c1e2952203035412100b040c3d0b00041907c00035a1250310213950f0b0841602c00b14010b80c540240740b40c980c004036418802083c42860600d000d6101144110065081460044e502c03104500d8002416900d610000c4c00810b01c24003d0415032070a4105a41000c500c03000042c000d03040f840001c06101e8010045905449182c10b2050303caaa00d5031040b801000581c100003540400001c0d01000c0d545c0000d000d41405120b5405440c40e4164104100d0721544031100080d0018a444014413248a12000090707200040e6000090400e03945c58090703250002c00e200d8200d0300381d0b0b10014070000341800c5440b14041d071403d46112030300948041000b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 258009919 1250 258008669 258008689
    0x20c010f290d0305070209070c0c0b030c09042a02060406051503150903160f0b1008072c01121101081504090302120d020a1206050a06050d020409020f03070201050f0402 74
    0x7078070076a000315001e003c050180081e9800b081d00030303105007a1450480c9020f000b50042ca807095541901e000c100041c5c01d4450801c130f910840d078502d202c42c03c0001610502000e01f543c3c0c070200041a0408100401c01a12030b180450078611a60040004d810941461011603002420070816078036064100805038800003250b420b61107000400750280c2d5181e02129095000d0789540e90710142c116a141001d0180000a10030b41c40d0180c50a20703e00c0d1680e078006000c80710240f04414080e0405101088452000722041003d24480c0c1c903100c0320051180c00c0706504000036003100842240b00c55460092001c05070020000440a090150311403c020701c0c100180e100340c0348854402c1e515038846000701032090080f001101c2c80f0003903075a21006408483d030041c0d085220401700050b10b07213042c201e6400d01b80c01100e0840300d014140000381814240700321780c2940024100c2d8040ca808010006210003140b0084c00c1c90340c014551503490f400c040c64000c1c2540c0c03002d071410b10b428540c441030002590f2805420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 258011169 1250 258009919 258010001
    0x12708030708070903020604030c0305161526160909050603150a15061d010e09010b03041407060903020a0503010b090606031003200418080d050703060306020c010f 72
    0x32030460703664003c0c01c86184070300d034000a4000c040801c001040203e1100040c00307403840349040d01c0d2003002340c24000a1010061141a02602c03240c4420140b050003402048001104048003020260301460b2002000e00d09031800003040d043c03803000f104243e45c8402c4090251144000c188a141082c0b00080e0b0b8a1044181084031220b8032004144c00b00c0c600c1c0d12168543d034038448079081c2e456031440042c00c0c0d032203645c00082084100540a440d07a41c45450101904200108800b8131039003803400a44550300000c0040383c1075981e120420501d2141040b09000900055071016802815441444600072890340300d24000d83c1040b40c00b42031031f07451103e100d41c40a02510320540326504e10781d03032901590040c1e10140c0701d8098483c502c4400f12500711006405e04080d2000c4c443c9107098506208603ca4140b00506503030418442c403020500035410054100809241c049091a1a40c0b241d600303c0c2d100420000c4aa0341d0b4603101d5100c50200e00402440f02201c4424109010a0700d11100d010a503403090 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 258012419 1250 258011169 258011177
    0x5010f110d0e0105161109010f030203280b0f0106020709020f070303090303060b0d06030209090f0a20090906091b01090501140d0603080a09050607030e01080907030605090127080307 80
    0x40300b503141d02c00c0c402d4907020583e01102400003a5039007030540e9009441c0c0000e5001d88041030010840da620b2210341030440340e014004009a101d44c5400395401580e5004a10f80006660241400b00b043c10039900d0183c83c19034510310081d458480b019262011652010001c140107000340c0058044500070381f005103825040100c2d07104014902100100030340d4118215180c004240703540507100c0707540310340242c80c0b007601c440da502e40303400368201d9075000301403070140040e0b000041343d40018401500115174a4000391001c04103006440028902000803036120740d55901007420450b0b54032040018216043d00c0000320000241c091000901b226098003c460601281500c02d8158140c40760803034181d01c41c1c448041001a40700d28014089602106035640000c3c020b00000c40c5601d01382084904180c0c2c15180d07c00c80f400313004c005403803407400100404060300607020004080740c01c900615101d100a800002480012580030303002200c00030041d01820003c0c080c490002440300c000300d94201100d070074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 258013669 1250 258012419 258012437
    0x601121103150a0b040f0204030203070b1605030d0e1b090a0e0304080a05030c070b04140f130c0f1706152a0a11240a0507021905010f110d 61
    0x101092805010b610008a61201d0408001408215900c0309080043c103c0c2c2c107102581d0000586016800f5034007000e940340c1c000450130852030000c08002e100c1100d1f048507903841c41100d40c88003810340c2c10035460781c80350540711005415008014018080110b001d03040101d08401e90b100400d46c181801801d5841072941c03003c00c1000d5a074104107450080101c2c104460840784c5c0b502e0f1103503c80e000524480c405104010010030700c06a0b0400382c030281d803000d40c015001e00d46a40c0c00c01026400c10708485030030480d00196282d400d45d6600a401c00120292105003e115440c034004041d6480024100d1415503140d0500205c0c3d6226400c58004e401490582d540303408500610800c0082c41e02100f4007546800c2e0b4444003520f0300441e8030103610b8080d86917411511b41380024082c01c5200d070f2364142d5000c0e5103414082030b104034140c05080c45038058501030f0b080829a41c00300f45510130106103200d00b00c0320404100850742e80f016030001080300c6860706030615221903c10f81d0b0354904480030b40c0b05014400c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 258014919 1250 258013669 258013703
    0x180409050c0f1c38070c0f080a0305040c1202090402060a020106080d1205011a0a0c0623090606010e18040318030308090106061115130203120d0e060112 67
    0x3c0c4040300046a000101c4019200c0c50315980e8400c100303202c0072101404103071401c001410700a0110700c1203035142e03a0b07415942d10b45400b210380d030b010602e045900b1940c1510410204079040060b18014240da18001007070b0400d03041044005420340d102c00d201c450010714080060711b600c86440e4101c4c2d4107075482c0d9110500300509034090042908048554411807043d020082c0e48401c2d08131596401103000c214503600c0d82c42550600c1c3c142101d045a0302c0e810041040a00d2045224180841c0030b0310000440c0171040d20305500382605c101a4200d85100c1c081800b150744824450341c0d42000c0c090a003810070385150004541000d8140308048411000300e4009002d060061060042514803150f40b01400c5840c0d245c081c000c0c40060f503d1300d54961070040c0114669022b40c48042d0802881c030001c0504044043c00100002001441000b1040d000f60f0780c100107031010040225949080b201c15500c8a851411440c1161403a0403806c007150322030b1004215811075100c905503810340080d944881444c01c3d07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 258016169 1250 258014919 258014929
    0x1214070c060b10200a170a27030f030207080102031003060b0612010312050702041b03050f010303210b04090c0515120105040207031707030c32071b080102180409050c0f 74
    0x41c26003c2c0ca074070411440f80c0e25000f40c02c1e00400b1400910345900c4c48501c0c00032240000388c1c40402c0030410000c910303603052011074542c00303400509612901c1100d2040b603c03080020309a0300251401c040049502c4000d000300040b5009407803c0300d10175600e05080c80000300380b81668500610020b07040407510102c00c00040e02c202c0131180404d4001d0824030000c0d00840071100002150700c02c070b000003450040032844200210a805048a40681d14422200ea013000b9100070107200000c0c4401040c1e464014100c0e54503980907900c50a40a1020340640c0c42c40e01052004102c4140719002880c0303001c2003907001c50b6100c07410342415140706460050326241d0b545811754000030807a0050355618a4481000380c0d60340d0540022a280c07105694000d130103c0400c050380305004081600c1d01c0441c0700c468a007400e2035000380c007528946014400003048420302e60a204407083c0c0581000402e65000201603c0d14491819035102450f030540d400c100d51a05034445544608014488178480c03034040000074029a10b17 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 258017419 1250 258016169 258016183
    0x906121e0c0c0503070807140f0604080a0207050a0e0114011e03150b0d050a0b04020a05030a200309150112020d060b04020415051207030506010207061214070c060b1020 74
    0xf102d41100c0c0d0f0781c403050402004d940c01c44881268900000c107410308031708401140d15100303154400700402664032607030350301036454000c204801d0461081030000030721942d40140c414028400f450794440c4a5040c80140306482e4090140c05050040c691040e4004200094160070038107002e240004e4401c8600c4255010210b06501500b0f1414021801c1e100800280e031006009a01140040000901e00c00c1400140c0c0521680800860700a10015104401036007001140c41910740c0400c002c02c101088114041e0016181282140d01000702400d41c204c050b400341d805010314034604041d9050590015101601c0c54500a040ea030301c6148200482e20303680c0556024240004807800c00c0c4501040050403908102c03c00504103002001040e0401c0c0070788522800f078201039014282032401c00308295820004240c01240c0c00e60341e280c4078880c000407103015600403180765442d00030b002000e00788001921545582c1c20b108441480c50b4a0805030002e09002c2c0707400d4002c0c4000001c0914001d11030030010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 258018669 1250 258017419 258017423
    0x3160e0a1509240501050d051819050c1903140a0501020d14010504060b03040f030203090d061d010c021b03150901091e0f02131b0906121e0c0c 63
    0x50314207002c50745110307a8021002604106004400c030854900e8589504106441042e000c01d134204000c2100b80c4140e0440c0303070711000c180d803800c000c64a4520348519214980e43c1d0040340c815000f10360401c00c1001e001d0103440c50302c11107180b82e98045013034184155000c540b000501d00d0451085d0115404014450342c01c0141d0131000864a40c00350300f9910300900f1000c3c0600707120310340301c00011440345001e221f460140d50000054504507a20396580c2c4c010240040029019440203000cc0c000d10341d038020f040a1018800c41c2c010079903002c160480d002000d00480c080020f42d0501d0350120f84980e0000b140124448101e020000310100c802c080390030a030005a840320351500100400014010540102ca00315105071401410300300043c621550404407030707000174441c012403108100507107170030385190030401503080c1c1c001034803403421041343c082d82480426500491031510f4104009a04010600307054400024207107c007038607a203520005c1d01401d039503001803166180090840184901640a01c2a03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 258019919 1250 258018669 258018701
    0x210020a030b0a09201908040c09110403210e101103030109020c061609050f0612040605070e0607020108040206030405010213080f12040e0a090203030c101a03160e0a 73
    0x151101500130242c051540a45209002141d0f142d9003101024200c0b144168400803a46500c01d02c5901240c025101030020340702003034204408141504070b403181d48030074a0301101d07413940c451451425040382001501c1c0c03400403800003051840000d4011245840303602040303a0210b44001d500b081038031140c0210f58820241d200c00b00c004a14900f8503401800d140d101a41241c0301941c90300914441d18074540880b60014051401c03c11032820048030000010310010002030401c44428403207110701d002110240c0300c498940b410300121035004041c10100d11010703114a40b44c03010640018060804c0540000e000b480c0004c00182480740a506a590050896110281072079480700425600c1c0143e030702e2400310f070256191040c40c4007001001c6600720707041d07410070108959130705410200078107031610b0a80c0c15010410030000081c00c140304c541d5013040c4040000941c0d241003607603000448000c0014078007039400402c0a0750b0600d410030710101190840400c14a459840080380c1015040118600d4081e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 258021169 1250 258019919 258019939
    0x9020a080f03031b1c150510120b01030509030a05090d06060f031505010e150301061505040e06060909011701060e040f050d030615050c0a0803041b08010b010210020a030b 75
    0xa012008501a040e1000c0744c14841542d104603008911170080103850a100100702840101190340014681102d15281c1c2510b95640c1c030003003039011401c3c424070703000100003074220707042a0610b2181d5a013005e030a2901b0407892a0140495a49104440d000d20500c40c02050151041e51150561003007690f200350244030056079561550301c1c20700c180c081101c0305200d0640c1d03941c00e400f2a1091034103ca0300c00703042582d141c41707640591418848210805d601552502000718142982007203c80f40c402e5151790701d07036996192013a5203900d020081c1030329120340300c200801000d40d5250405c0905454003102c4004d550551728541a0040103a1340c031a1584080306803c2009101001241c90311181c001c10540f2094084508210300b194440e005400d010743ca00105049468803460181805c4614481164481c00f12526942c0c904c1c0c10468044400240b403444d00d00500161005200091003504002d10290701c40500103074460401200c1c0b12013965021408031003052081e0041d58500c0f40c054400440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 258022419 1250 258021169 258021193
    0x50a0b03010e0901020309060109110d06140a06020a0506060105090d060923010c17060a08030d05091204030c0501050d0f022a07030c05190503030a0216050109060c0609020a08 77
    0x654200344035500080d158000000c400d22818000c5a1003041c1c80e80240081da82003541c24401000e40d00741c0d140121a00b032180318402c52040c401c150113440e114a80e0703114050b41504115040300c50350071200454003d154244c00140780012030503000802401c1c8030b608e9541820204460201c0c0190140016040080580500c41e8074244280804052142903c6901c41c010754142641c5a4280b00000680d80004401e225050445020f0300500010030140385151340b902141c2c03a5800103001d4030402d41d500c50900c46000c201b0000900841c41c2d200c07006050600c2c2d51901d1540100a22070700b1b05004000803020600300b42a40420303e0310011220840d15000c52502901080c00410450f503142500c0300c4554001c0d540000d0800300b02da622007291843d05040100b80080344d00d0540c0d440c02e41c5c0c80d61070004204d55900340090050f1a4080d401401c0d801b0820100320344402055100905204080720180a05a406402010400d800281c0420500c040b480428040e405603844460180039007018840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 258023669 1250 258022419 258022439
    0xc0919050108180318120322080a120e0402070b040812010806010b07241805120310030201262706060117070c0203102c03040b070804050a 61
    0x100340e410030390b1210703455610410031401500c4002c191255680c0207019001800c0c100106600c200a0041c0402c00c50310f80940e40396185801441d002c1c0000703180c6455440d410310418050314010810310006111610309034071040401144010301404101000046582075195a0110752a4551004030b91000b440d00c6c2c28007800c00e820110000e41855400b03800001c04200c001846410303114101d05c4540342003101c4e680c1180028040c2d240425040c800e40380a00d01090a200f0600400c01c3c00e020b9411082052610506100c08074000b286403c00c14170610100c2105805c1c031205a03a820300781840c890b00101100d84200d9140406002c1c0c59200904226017145002000307440520809185e1100c4010101060b03100c0108413111400105840c1403845010303078141610350040414108003c2210b00e81e00400c4c24003408903012004c0e6515404495403049501d480c2507190070700741050a91407000045029224800c6114040d0180360110b428000e00c9240f208940c010280200500d84a541e542d2440e5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 258024919 1250 258023669 258023719
    0x240909150904060c020105060a050112020a17040c0302130515060a022104050f030a1a130c0306050609060d030c140c04020d0c020601080d0e0d0309050402030703061703070203070e0c09 81
    0x5001542047e0200f40f9500b06410208181c80301611a9580c80381100800300003900400700660410003071540c4440305980c02681f0381d024034003d940700301c41da90850050003200712040007118801c034030b030004108500c4145940006440011542960394900030f0031b0032842c1c03110100e007201010b00004a0100a00c007000020301c1200d4007a039801c44010428010141c031102481c101401a074416107459285440250364160700c404884002094592180c4032054221919002118032941e83c070144480d9290440d41240d0010048880c00300c00c2d45242e4004011011003503004018691301c10310203510b020b060010940b00140540215140d010900440b405400150718050146c0905000810340440201d00150324105503190f01054010f920103100801c94450410350030480381f2000401c1f10707515400258007603051560003090b0641841000d40d00755146101c09281940200000b60040c0c80119400c01260124415888142c1e11780d0400390b2940700300440c1c81d602c0460040c4140442c075102400c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 258026169 1250 258024919 258024941
    0x24040312030f1b0e010207140909070e04050109030314070e011202190903021509010f050f0d090f0203100506010c060207020a08070b0d05151e0307050a080c24090915090406 76
    0x98038001c0840d04c0166101c101300c0c060b12010300940202e941042c200041155044000e0604a400d80c1c3e0340c82c0301c1c0c407044c8030007075030100d039a03944620b554000d0607814040c03d00410ba0001051049080c6100301130445c4c026038508a05018050b204040408a03d80c1a00c000c240744d101e46009541202c40000c19006890000b21722032259a0070a803004115081070b85d82c200303010303101c58000003200d65040e90280c11031841448901010000010790f1021030040380100c5114030465100708009204040c2001401840e520910340381c40100b00c000e81c0c4c04a80300d00526041040160b81d140c032400461450b10458100c841c56101380240025454001e8006001090020400700724a880384403004004480010000d540400044540c0301646821140380408140040469902e50b60b50004a40a034801303603c50301294010810203c01810100c0403080fa8440f928081001c0b00c0c0200301c0007105009007410740303000e450110b0001e2101980481c500c09250b0b4010061402c514051900801130030b115010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 258027419 1250 258026169 258026177
    0x513090503030c040303020f010603020a06050d09050106240e090106030207050102120f060109060f020706050c0c190503010b01023d0e010b0a080d02060403030509010b1e24040312030f1b 82
    0x5e48008c10040c85501c081d039500602d80d40b42c41d0324040c2d007224150041440c002e09280d440020400084003403081400400d01c2c580d028401e038541602803480d545001e0211401d109440c00d54004170303510070f900d403410742d4014100140c440805040031802806440c001420080c9101c043c4400c1ca21280c0045120303402c02d036100d00c6101d032034401c1120745a9800f4500c00242c1c2c401042400305901943c094a07100f52000103d580001061002612500f4030f400b640d900d1025100043c0000d040a004405000e00280000c00c1420b04c00c60f132080e4101001d803201d42c0200741c041d02503d040e48141c039800c5005094103030305101d08101281003500a1441e501c025105030115070300083d6035580402c007805890980c2e0040c242075911910b0982c09000001d2000d940d6540c0c034a510400b6940320540801d00c42c00501c00001080804c10a001c41e0040d10401080180d0200c0181e1020095003c01c4038240d036844608190b20013001e0070182d0291a81d4141d03881e1030740c10311203c90103508d04c0b0700f0b149009045542d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 258028669 1250 258027419 258027433
    0xc04030b10211e1e030e01020105090309130f020910030506100903020306070c03091710060b03040503190302160605040605010b090307062115090c020c0603010513090503030c04030302 81
    0x20b5011000000b100000702080310f15180c80d580c0d44100300d41041c20902030800100080d440346010710281c15201c0c41140031503034071601c402c080c4d40e0900c41c445d8001ea041c0f00940c60691500c002030900d201002c0130b10b44894548410640ba00031640546600b224090201d0700d1258090b1405400351804441c018012407402d040403400c00d10a8560034100c81d00a800382c81161200401215110840c0e01e060f42030048816000855004445800c0103a240080c0941080101001c021013507898650000034089018001d02c0049500407040340d0722404d030190151300740000c08100750084e01421110001c0a032190042005018a94100c80d01c628403402c0c00300941da0f06c50280310701b240030b402c80858240e8010001808018022014411300d40c040c40300c10360313440300c07100c6c03442c000c0c1c980b58a1075980580401d442080b084203507002c1c0c68140c1d29240041c00c514161031003c40c0081c00305206e5a4811860764480044c1401e1660005032519006800e036aa680f81200c00015140e029200880043c41012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 258029919 1250 258028669 258028709
    0x4110c0322030b06010c020d020312210142030b1002121b0a06090302031b03040e070e0d051015061103040e1b0c0a020907030e060a050c04030b10 64
    0x1041001903a500c0f200160f030640b1070310011aa40342c600d20b0f040384c101d8015000b0a000d40d44c00c00c1322032844010050419641c88030400c6031105004083da12072011304000006000701c80200394112107054011a4844400c003000340f0301c5d20391011201c2d503d00840c02da010b5422801d0f506400004003070805a84001401000c42d034126030352484403108600008091000600c00d0552a242c030a80b1000c4d0802c690000090740c03551012a0000c20040f00540e10026900c4070041d842c1c40a500b4010032403000e141043d2800020040030314000700b00608121090741c101c002c0b5075400c00021650b64010040b43d2812016041d03a034010000794a50003420111000d0001e2002d1094010a9000c039410f009582018a498000c16600b2400703491071100c0e8610010842c500c100d4071000e00701e00e14a08005211552503401801130040340070b082c0780109810008100c5501d5000140203402c04901c10000441e036491540000d0107000d5604024296008801801040311980c0980000e8808001c55151620906 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 258031169 1250 258029919 258029977
    0x17070303050c1303120504090f021305060c0a08030604090b0907031704080a1707140a12030c0f0c050f0d1d06070213020d06090f0e0d08090c060904110c03 68
    0x880720100120740308120a000007611217000b4000d030131150520700c0c01c0c5030301c8035403a406072642044001885907002c21340350308d040491040c0400070b12080c0c031124a49401d2007551074803058100ea000d0f060000000c04208140c8450340000f078602d811060800c1c8605002c142e198481d00d49101c03c0c3d401c60000f2421081103c408070880f422604254000c0c02420f403141c1d46c000000c07061540d0308201141c188208004076194a28601c95282808064044111a80b40031080f44855002c104101840c02e918035960759045100d140595130582000c624924652034010301c2c001d9040c80380c841d280240651070400340d4112580c0c9043d00001c0c0340c10300c6542101c3e8140308c082d00a40304080d41c805144880781c054501150b0080a88910030080490340c191075030302d07000640b4410007000d00520364940c91003922100c14000c4241030b11883c9042c0c2400d06202414035039540030380c40f001d031041d540002e00040780e030742d20780c03000f110941d80d080c44030340380c0090446041d280e070040e81c01030711440c8082070105025105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 258032419 1250 258031169 258031177
    0x100f061e080610030515061308010f0603080f07020f100203090405150306041b12030c020102011d0d0f0c0b09060601020607030c0f0f0c0209090304061b020f010e010c17070303050c 79
    0x40503011003c07209a40408a000d01800352200c43e100c20500404055074865000070584010000c201c54440391030810b0641c00c4418035180c440602d460720b4405d000145014045482e0314220070303681c03500d440c00360001a81c540210002c0c0c2c0d500c541031107080710000340c020016216064085408101c0e03030780c800c0984404654003888696041c0c00101c0081e0010740401456400a0801da50b031842080d216103d0b24040d13002d00c6026404a40c51105000856a0900480d020a09130a800c21055506001d8550340c5800f07980d070310400c0c480c0085500c0306080c8161b0042c410035410001c0d4603010b0070884403040d110182074a2180c014050040050075450181c018511091601d585502003a4100070381280c200814401c40402c02009241000141e65200c100b140602071034009581c0d2540786c80005414826240003a298103800c0130f507220701580d41c11140e00f031075100a09104e6901401782d80100e0710310710020002004201040e103803882c20341e114000b4001d02880f030340782042107803144900a031450003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 258033669 1250 258032419 258032431
    0x90f0c0e0d0b070212130e0919110f04060905040606170c09220b060102100c020304030b040f08031501122d060b0a020a020f04180605100f061e08 64
    0xc003401c408009040750382c880b94031a003503105807118840140b170007540c07980c00340284202107003142c20706001044101e00640c2d04148501c0040041c1c4520480c00384280c004054050141d501c042d40c0c08200b5125a001540c007807000030300030030401d91913800020080c0b0098a0542346945040c4001c54000c0d1981003080101d090040280b804900100c10402d0050f40201080440a0030074040741800080c01d0882803001c1c03140f0910a5140380c84400240f5040001940402c1c5505011400d603602e5000710440d01034a40250340d4031055038940c14608220030380c5501c0285a41800400c211462502c001d50741195a02641c51210b0400c52001100c10759850080900ca24032810050041c008030011068840b00d80740d400209401c0d0b42c64840300301c42d40112000001603000310f0b04100c00c5107411400003802c0304040f1801c10156001c40d1001611041c55940180308136620b8000c0b03110201400c0c071600082401c07600e4016803584954001b0600003100c03a011030515500f01895490307500900c00c20340300701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 258034919 1250 258033669 258033679
    0x102010207080301030f061b03020c1506010c200d0b07080606030c12180321010503031213050f060a0b0f031f02070201090509040b040c0602030a050a0f18090f0c0e 72
    0xb034217546031812030004104086072080d80e11036100c904c550340701707026032500e505075180141c03079030302c4000c1c0303242820120484502c1d40040ca20801c0311681e0802e041c52031841d040701b02e8038a0200401c1080e03142e08100c0e40f2842d407107208031441e03070b0410100390b00e110320444882c5e032107100c81c0d04c0e00c0e002d200c4503007c1552180e4501805110b0001081000980b0703d510011108010016416981e0b40030b066600540d0148282c00050141481514042c2041c50042c0000d400451521030900041400b09402400c50707202d00c81144840e8003404010401d81d44030604510550300c09090580c0040f00501c04042c200e8003800e5000031000705481d0101d000c109082c8020390481c124102071030080c000f0340c00b2000c228113024810b080821240c035004c5003184078074810140c0d0315017410136083c20740c60100345034000700841d4010443ca42900342e111007a40c0000c070b16030500c80c05c7e0145000098440d00502381c52140041203403400040d0516458005100c5144200c1c030410000d00070290484238218540c140603000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 258036169 1250 258034919 258034921
    0xf060f11070e0613060b13050d020607111906031d0a020102120307030609050a0c030510080703150908181311030615070c170d0903240e0106032001020102070803 71
    0x12002e00c02194811801001250284011802001140c246421031104608003003048440070f4400d10f001070150508842d40d408240403a03000424a103d5240002c040440b0550740d00707200d441d000e80100040c524000c100c1c000c2510750500500a1410b13207041d940442d0000700400c012440407507c21380641d01a030140a000b03100000724440d0340d0025061004241c0c0d5480001080c100d036126090003529504000310354014400720080036560064010002d03010102c008001051002801c001100c1d13114000e101c030001e070061210300500315000c018164000001e000d009003204940385034540320f021513011107011001c0100d002200c0541d0b83c00c401201e800c101040320351030b1a510841c01045046416441d0218a17030b035500307241c0040c0c2c0c40341d80c806440600c071180f100810300415149800341d00e0000d0900745981c440e41d101d510303882c966802d07003034400404018640e40307500300301c50b01c7e841c441c024000f035560782c0352070116135000e50000ca50314582032866482541c81802140c0549800440d41421 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 258037419 1250 258036169 258036179
    0x10605090a0f1536020403080c0606010e031e0c0409030309050f01020315010806030a170d06240f02071a0d0e030901081f0f0f05120703031e180f060f1107 68
    0x2e240003a03c124012a403500300541e040413640000c0000d0b5104401058031b07800c000d0515803800c0005481c2034103000b00b00d80500d101d51400030344c020854060460840040c2240700721123042110368042580c21a00b012580014190550400540644074004448030302615508182c00c0340000c1e181c080351f6401c5121a10041e6100e20841d9070450710040c141c882901441d80d8060b0600c4004c10744012680300455580807040301440340d400200100d2543d4007880b04001c41f42c00f10301403a50300c3d140c28440040c0e56401498404c10982c4060965440c561090010721a0514441e810403200c1c0c2440505040c82d1422545010007030707802c2e004068548803590b8640408180181003441c0c0c0d280980e040b55131002400161030001e0100078515409644101c0c0e0409052009042e500403c4c142960322a01302000043c0e4820340f118400461001050348408880104540fa910180300210880a400c0c602144600090364000708552803a242c15203521104d150a8550b00c900c500e01071070399000403104001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 258038669 1250 258037419 258037469
    0x1b03081c0e100b030f0105040501050117011b1d150327060402091e0a05010302010f1b0b0604060513020903060105010206070801060f050f1c0c141803010605090a0f15 73
    0x7602d00c10060a86044045d510001405c441048174196101d80d141d00041103090500b24000c110a0030240082c00305034070500a00101c2001c40604408024008030200740c085012800302080180c000c1807103070800c00c101d01030310a50b001a10a2821300d07648040340325440100140a66106103501c010701640d65940e0200f060641c8001e03c0c540c8030716078540044924140380a0002e00c5030000b500c00254079415030000402d00c85041a14200740003082101c0c64000218141080c1599405680403103180d440d01e012a014141c281e10003034000d2401001e88030681015000b8022940081e011900c05aa80b200120707500c00050300d8040204100000502540788100c080d8988141c0c01e090481c0b078000403002091807a030006403920b4a64841220402c2c1540b524081e030402480c0314076010845502c1101c030015688101090a8014005101b60b0703082e0781c50a401c02c00c01088000c2006d255441c101503100c000e4809081c03003207138440c41c0052100803445120b92900580c3c070858400010b003402161040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 258039919 1250 258038669 258038681
    0x5060d020a2c07020d20030319020c0318092d0c1b0303060102010e0c06042606190609020301060c06020310030c090207030207050a030512071b03081c0e10 68
    0x100442002c25481c052240342d0552050003406070b40d00401e01004a908010f00801060a0f907102c00384100004544400c80003080d25040441402c02c3c13012480305039120002445030000e00035250201250000200c000844074447d100300c03d444007486031350f0782d60048076600b41c440244222002c91841080074208107140055108410405140c80e08020090244c1c0c2491408400d45003913100000b000b400d56820301842e42d0200020004080c0315001a0000e08940503034040d0342d5079100341010500690031841540b090031200d0760107651103801c20105691000584002882c1c41509240000034103203521700c01c43c0d04031000c5649800d1031252582e43d0030040d60002e8248215026010b1000c00441d0080494500030038950500590300c082a14000e810300700c183d4050ba126203000f840400100b1004181824100030801043e9615186450031503801c4000e800405c844020488000c001c00071000003c0a094000c12048000e0300084181f00382500c0b80c000c1d4544460704142007550306007455410103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 258041169 1250 258039919 258039959
    0x1d09040807140102130501020115051e0109150201020403031403070e090a150b03070224011703190f14070c050402090d050a0602030109180b0408030c0d02070b04030305060d020a 78
    0x364042c8110001d014266085808050601c1321100001c000943e02445210f44850f90305403601641c0b841c080005500000121007105000e0102800c802c0c160710075032010000e064a1a01144c0c61050181c00138000d4100b030008a0100765014a0035140756823140540c0d124103280c0e07030307150036800019083c0301e0f0640c00503042010807030f100d2b54440c40da80e59501e01603010b062046482c0d601c07868455402868450500e0496592048090101024031561119a07046d6030f1191900c080f0100040c0c100c0d0701e10710614074841ca11104200e901c004c3c0d00e5224207280d4000c4084e40c0c0e400600103074901c6400e80b42c8104040140007241c0300404100b9800c154018111a010040442131070780001d8031005d007010a01d4100700c8106134004014016041d00b445650360404580e4030240360342499a641005204000d04040c1120300d0200008103050303c00c1702101d505501825055440d014107203000c04ca401e030152011808a8182000102c030f600b45548d40c10703611074004001075545c1d45040703141c549803c111940 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 258042419 1250 258041169 258041183
    0x201090f2702070209090a0b0a0b06030412090515040612050702030702120309060a03060906060801060f0c020423090105010519050f1302040807080609030a0801090c0c020a151d09040807 82
    0x6500d0142c0e81e28001d45100706c0201d80544540f19072840c041c420884014401d448075860801d091031183c5075034003901d80c0598040a69400302e03024103016940340d8490b50010394041c005082c0022600320b80d0025004880c00e648640380b00c1807030640e14005075881119003c00580c0103010300005880c00e81c071321000c140c03074a406483c0b030141e000380070403034a5112142003c00300e074641e4070030003c885280c42104020180340c680784a0650505400074020709108041c0000c02010082d84e006540d039961050400c8001004100d405028686800c0025281200c140c10b055182000010711814040800402030b9a501e00c44888035040504000d00480341c40c1d0115040007400c65000c08210301e0b44010006054070740300500146150a0f216880d008000701080c0c1c0c9604140028005181c215050b5415200c01540100e00381c03817640c204945001e19140065030042800400040007030b40d0352000c1103407060503903840085080c2030304071100e49070008004c1038005083c80f00207400310b80642c020301040ca01c2190 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 258043669 1250 258042419 258042427
    0x4140112140c0307051504080604120e0d02011b030e132406140319090605060a08030f070305090a03080c03090f0f09010504180f050a0201090f2702 65
    0x50100514409030064240422012440310900ca4091840444020210300800040d424400400c1d19103c81d4441c00307001d403545a0240c056005078100707a80252111a0440b103407858142842180f6280c2c400c00400030481c0070414401c2810b1070020140101d40613110f10040d0840c401d11030a620162100540400108030b014041e5680c2e002c2c5400c400c2440c401002c56404000c0c21103605844402440d0200e0300300c5840100b02e03560308010504951704826202544940c1d84c2c014030110440c20341a04007450340f501036400100540c6502c801e0040b441601c03941a0725450703003601079403840b42840c100082c20082c000040068810402000001c1c0054180300c07403c0c1d41c82da034020032900700301c0490100e900b0100f46001541032414100d00c1344003086070400414400c1c200466190750040c040c2d00d00807512a41c000403003036102030180d00b45a40c01b2651140c400d505003861910795038504d401b2800035036448000680714610b0201d140c15100d20f003c4600000070711072004d00e07040e02606602c0520a400748 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 258044919 1250 258043669 258043691
    0x402030702120c0f060f04020103050c03130f08251e02220605030a050303090d0c11011101180b010906080a03120509100606080601140406020d1d0415030b1e06010c0204 74
    0x2105c400d00560403040c241d50a801c02c0d10002d41170b40d100401d0782d055144180204000c000100b0860180141c010710008900e041724100703040984941800e413000d2000204165000044600c000c1d450b03a8050510300300d06000040517a159045006e9020f54032503030b21420710310144480300f03803a04401040d010000340140d462010a04102c1a42070907aa5600080708020175140c0c240041840550301d0702e010464182ea5a03103d0f0800900007000ea81008103888044122410940c081d50302105c6240b084180001c8624207a001844240601c95985041c81000075007181c000a1420440364503496031010b0307140b03000504005110007040c3c1045d0744074010000c000c05825103e04070141c41141c3da10a100e14100c030000d094051a20070f8a552018100000c0020503408140000d02031800e01c0d150120051801c00014030102a801c0c1030341c0103180c01408103866203426540c000302c0e441041b540d16036030390b00390410021400360300f2001c00105540c0d0000b50785611074031078400100d2004000049040e400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 258046169 1250 258044919 258044923
    0xe0c0702041d0c0406030305160303150b0d270f060609051306140402010f0318020301020c0f06100b0301030f030c1a10080a05030901050c030403050102031005040b0402030702120c0f 80
    0x115610716818240c805604849000500c120003c000003580d080c010b0f00d155950051492203400d5140c004080f0810000081500c00c0d044241c403a11100c4091800a071222040e00d40342d40050310014059142003100c5034840916140030321812000200402c0d54030058590240000c00c52404a4683c1d9603020b02040700c21381885224040c0d12000421010481d56141000c00caa0460f01401c16120440082200503a80000008040c2c08545004034003c0003a40092000c0820180d00a6055002188024840c1000a00403020f2030800e0300f29901c544621134110f8003c0101e0044007a84502000140041808080901100b41c801e19011018880f6030301c880c045175003140c5d4202c40300050402842840162028620060002e50010307003a121030a50320b0380e80d60700c0307049051814040d001c500e01003020814070584c3d00039034000b00290354a14244ac4410448890340c01902d10031481e00001c5080c60501d8401d0380d2003004c1075001020b1914800c00c01d815250008448220544207a4561030b04007001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 258047419 1250 258046169 258046181
    0x60b030a09032a060c020a02031f0915020705060112030530090615030c0a050d02061e0c1b0d030c020f030a0305030a0e0303060d0f1a0702060402040f05100e0c070204 73
    0x8200da819181d010740b80410580701d00305c28030800c65100d12840070250f9008104400e0f0b905241e402e41c1c580d00d04990410b0003401032004003500022406129003448095a0028401ca9101d0340c259003d44c1e807100c0004140d5181440007a00007003060080c8101c88080c0c07464083d0100d01e803011201200201000150f180000b00e64510706034002109000003071919106003080400c00300d0207031448181c2040890b20714526441030921a004203c0e19070259180c0c0c1040701c8041d4148610103510084504903002c7c0340c0e204028021640c1706007148900c010300c40c2c2c945104100c2c0000e14030000c1c03100c0303520f04036006540c403501668001d49410902c1141d80d004c20500d4206482615817a0300da140080000c01103a00c05140720240303400820811070281c2e140c50407800f00d0ba60042d0504d44100e070500302002c84139252649054000d00800030f0044c00e0f0f0b00000c9a61140c0e108940c00e00202e41e210786c03040d050702d2040e40c00501414400344c0c10300441610110039070313000300340712285818880143c00040681d40303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 258048669 1250 258047419 258047477
    0x60c031503210203090d0f020406170d090806160302090a09021c06090209031c180303030603050c1f0f110d080106080c031b03040623090d03060b030a0903 68
    0xc2c41000300248000b1038003030304440c030b001030000d14240710441d8045104215649401807001040c10070f00d5046640d039900c91000b52405c27440f006114288aa420b9a440695241c0c440109040c03280020b009080011b0151080e00305102d1400f00c0440104141d001e5009213000307661001310040c1c0421854214030240c18100c4241e14043c1e42020908113001c1120403a030400c0080310700410004407252400078603049030701d1625140d08040c6a44070011107044c2540d0881c0c0109804804000080c1035054100d00b05607406441514441c944420130040c400024643c0002804030515a5100160050400491007550750501880790320500c50703074508100c180180000802e000c80014403803c0d42c445075090b41701100781c0000b881d5003041d02801c8000200403075008040329001002a0030081950002540e8904090518901ca1107200b10704800d01c4044983c003140f0300c104034a03107801d9803107400f07041c048500c000040d9145850398400c490152100c413030190709120038052103000d206800320000310006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 258049919 1250 258048669 258048683
    0x5010b0d06020d0b0306040512250809040c0c020a06030c1206030c080d0f02121e1201090506010e0a050f03010204080709061503050601200c180a0f18060c031503 71
    0x110554589000c1301c0c000d15100b8000e90004081000140e40055100c442c2c5400240c019220001500c140b84030026000d00da0b001210b5002d800c40c10080c1c2c21000e000e0703800d000c40c0c091110075640b0340100d58806582c100694442d20b401801c02c455401b039403184100200702c0c5030101002c0c0042070480c007961040d9004442e45000c094041010030824040701b0b044078154a400041c44020100007503903403054200040781c91400040454940da50f0308007800c02c20501410391515951500f00c2c007110000f09100d660302c003505000005a0940c0700d41e0422015400c020f01030950a42480c050080c60350301d88450b582c0645d1b0030080800c98620401400000384a600c001141043c00d10310003451045004481b841858100000c0c840240e8010910034040300d100360b20500c4a24040c007105103800e181c4c200c1d0070b411601906140b41e065200c0b20030340f40b080300c1e180801d2084031001e01204e4112a034058450000d4901c01940c000010744680000040241c0d40c540401c220810010b1f049501d142580100e410b6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 258051169 1250 258049919 258049927
    0x6060d1103100e070507120219050303040506070905060d020c0a021915090b1206041d0706080f010b0406080c0903060c1207230702130507030b09090f1905010b0d0602 73
    0x100741c031690401400c920200103c1d14140060050528041c0b14401051810140b400d600b6561003000b0010301003500e0140410202c0250410075201e40c419101610740c3d00070100090a0302d800380e10703000c0889a004d0101b41c80c01d201e140b4150001c4d048000b043c407040c01403c1c0f441c00907a48035110010300c01c1c41d424a41981c507161000364010f04034807020050512007940d00404c00b80244400360b4801411001c5c1c814459551100040c0050000c02c240d01c2105a01c41a55079441000143c0c40702a148252514202038940c1e81c1c01000d130343c13000d10609c4100749042005000b018030640300713590400882c112050600e11000002410108119404c0304046000700300340e8040142d820965401c0030040c00c0c000c00810001840c070481b070002916583e02400700081101c219190302410164107007090b541081141080c030002005010f803a0104c520841841000c14032500340800c900c1040b404040080003544410000030a07008020b510a03105556944e204000c181c81d00c000405900d072195a0050366 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 258052419 1250 258051169 258051181
    0x3011503140f0405030d061403010c090e0c071a07020c18040b062416020a060503070f210903030902011e0c06050c0915040602061e0a0506060d1103 65
    0x1001105404008141c10944800030908894005a80180030580d07141c840b9511401e0983c5117205802ca12500c0178078062000803080044001c0702c3c910101200203100d001d44180d0201d80c1700829000f0314461003070f510b01007002c0394200302c0244940391003008212030300c040d4070350451100e0400702c4003100940c206402000c228600481150350740122402580402c3c1000d0701c40b40031440000b4080c60003940511100042d41045582c802d10000c1c1b44000c0c940d96500c0c4a085012010440508070b001e0700543d400400c98030b0050341620f08c5031419503181d881000c01d42c0000c58003490104000740940120007c090344c2030013140030340c0080a0182d1004182031640740300040038282400c60319141d084408003032494156118140340082500248003003416185c0c003d100e44a4403d4019240d8040c65414a61403d181020302400c21103849400740c4001d550b5030440c0001d0244802c00030107050503150002a41d014a035440650086809040203080568000025044501e0b009815003142c40c08020451 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 258053669 1250 258052419 258052439
    0x30b19080105070516150b1003090215031b031e01080a110f03070501080408130e1006090506030606070303140c1e0403030203160609050601060512060d0507050d03030f020c01020301 80
    0x500180383c0d02c0c10300c0c60042c0d0850b20008450340346100500003028030b4203104110380544c10080e84500010090041c004088001038018001c60004074001e000c20701c800c40303162110606682c895501c0e0403009400102440d40c20715164801094806030340d0480d0b100d0a0362050408005001e010048e00600c1d4030015800c010301e45c20190402c0c188940511a000d120ba81c0380425000100c40007820947d400b40c4030f41c54541c489000d80c0003a9201800070010010700140c0c21151035025a82d001a0b442c1080d480d5207007161404218016142c01c05030800100b4402e06200005102050107450001400041080448641c840503281c50b07201c00000f084e040481060a40c0ea901440904402caa19091440c0e401948a0180e484c100140c003d280d88140240302054212210241d4400103075204c2c1d40e141c500180050f00800084a10802801d000804509110705508106a00900141001850202044103014820a04904040d214220b00e000460325002401400d00d090b030000da00c075814414419 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 258054919 1250 258053669 258053671
    0x61522140d020f040b040207020301021603120507080f04082710020106050d0f081606050a05060d2310020d02070201020f1b060306040912030f05060d0c1401030b19080105 75
    0x241c4680500d010716001a50f42020449a01d40c0549001c908414104006402400358a502035015400010015102d41c007800b01c41c1003180c803a0b00c031a200401e25691035801c40b1004c03102c45001c134402c103020903a540f4000713150703c1e0300501c0750511601c0c003c01c00c03208621a003500221a49495950300101c80d152801c0101041d0b80d91841c8020490030746820000f4000d15605400a4544840303070701c800301030004040807030b4210304040414005207141c0f07203404001441c08a99440d1114a0300c80496070626001c025040051b41110032101d42e4603c00d242503070f070010345200c003d500d0710900385402640312030381c00500b0302d04461150068880c8180d00019080010b2a0030b0400b09030481e200c0c081980c42a503103111003803031080e18032a44a90f903503000300b0018400c00c0d03405445203070586181c80503141c2c190410541c00280c2c2000b072141e85c4610051002280015900400f41c0040c01001d0210340800050449190720500d0040340c00b44210010a0160310880c01800c4182c142000611400301c0034000c00e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 258056169 1250 258054919 258054959
    0x150d0e060a09050304210b0c130b03060306042010020304080d020102030609070c02042702030d03180305031b070c0f050a230a0f09090302060f0f061522 67
    0x1404400c03030720360f50036840b8402e0340911b056808250301d150001c610000481c0280e950300040c0704400f8100180b001d102070304000b90401c0c5100784001c0100e11020050256400342e0030150081245031902c2d55020200140e483c501105e03003005a01a9851fa501c0d040885c00541c41c0e80c000d10760740c80c140402103080103e241d2005040d680100140445074031001d0500358048402c2c81c242d84200d03540d100260203400c84400450003851070340d2501c0e00040c810500700c2c411500c02c40448501e1481c2c0c0c40d058058440300c400040120b0714408020001c40c1c0120021984035040300b20958a0b44503698007041c09800004d000d444103c84e03058184a683c12165820300500b900715000411540307031103245021414030020031444030311021002840381c0c941c1083c9030040d1908803040550319407a00580f000030011240154014803894011643c25583c0320000c50056500e03020704840c41c4e4410341807001c2c01c03d07900309250044030204024a011511050320310b0103004101004522640740a46019080480b4210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 258057419 1250 258056169 258056171
    0x609091104260f0d03051602060c03011815060302091305090307020d140d030b040b0109260f01021215100c1403040305030c01020d060b030f040809150d0e060a 70
    0x5100c0110560030080740000b41610340310240021460090a0001d10700d0690b00500c664202c19a1454054008a118003d110a0404605c40100d000c90b55036900b0b5429940c4013104000500c01c90b1f82100b41c1714a5581001d802054600e0800c01034000e881d031070340c440d800183e400310f201d503e2813600700c2c442e00c030310341c6c078000280000d0404c666019224840e41c0b0000703110f1064075200c1170401000c00c20704102150424183d81c040c0e5140c92010340500003004d1158070a0b843c0000444aa40c05400d03014155008054114110030280c45041d107500c8511490311214465041d03a41203503d404d000600408901030308038a4942410031451180040c0110420b200342140d054034000981d200c01100071268104030144003110b0f24a2106046100c0c54001805600002490b070004180540040100004030300f020007a40307907904240204d0b400261000c3c0703000e50400010a01280900c0c02030403c250004014150743c2d0060881c030742166000445a0308000d49400c00b2074000203060100c198004c2c1030703401c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 258058669 1250 258057419 258057427
    0xb041d04030e01031a04050411040e1906090c03240606140a080403091e150206090a0b09070e040609060b1f110a0f1b12020a060e0409080406090911 65
    0x600030b000c007508a0b91a50425681d0300c0103c8003144034a04100d81c050000d03104004ca410181800f0340c000d031000d60307028006c50030000b40c0b40c91400d0019039091a8006c0414460028405940e200d0142900520076503050914860200220f000740343c8000429480310301c50365031450000741c0d00c0e003554919880780c801d0101075590440080c031140102d400c0c28000f49007200c2280d9a41c13405849201e0340780c10440303000c00c001d006d02000341081d038103010903221301505807109c1d000b428000b282d4036a0704480011143d0041e0380c2060019441d580c1658000d400b407420345940c030343c44d80809012800c0c11103056686503124066002881118424000074410a035400c0b0680c20b420101c0d05c00100d000e084040420411102610920b6818071420442c02d40c8203803900f503000c0e400e0515040c085026110003d4124080a0000720465600320600c0c14a901800c03420116141510644d90030040c603005c00d802c10f494141180018001c00001e20241c9025101c0000e401d0510320384004039014480e00403c070442c104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 258059919 1250 258058669 258058673
    0x50d020108070e1503010b070b060909150c22030317012402150a09020114090312030a0e0d030c170f060409140d3f02090f06040b041d04 60
    0x1c241e039502440c43d00b011002c0281a8002c01e1100c4941d400110607030310302000104840b64600010002c3d14081c0400100c991100010428560070a4407242d0807680101a0600c0b5408003890060784550b4860340c07141415a154054104065804140071051030b070b0160500815420803400050300880b0b04044180f50b06004001104082c82601c0c94140403070100c0004216108200c41050350701515401c507400e04041884070b0140003091b030f089001c24584030140c0e440016440a469144400a00a000140c44c2010040302580003034884c03600039848290f40c00903501c042003590160f540e2658001180e17280c640d0004d1030552a0b40e0030030b40031b5841106001401828540003500541c00300d0740002d501c880c9213000800070f11030000700d80542c02214450403c49810040c07808031940d0101030308282c072001d000c060303500c0440040c05001c40800a80b001e60340039053f9020700b40824028000949608505000541d82e0304103030302213110042c1c006014464005040f2090403800c84141c48002c80303050a0b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 258061169 1250 258059919 258059927
    0x80f07020f21040b0d0905151510030b0d0b0f01060903020f281202041a01021c050913060810021e070609021c0506071b1e1406010609050d0201 63
    0x28040302482c00c1c950b5103031848060601c411580204007103a41c02d903440717000d40d107a480541100d1400b6122070181503800c113109103038450721a1244444800404902560508001d4125aa006c42c030003096a500f501c2401c5440f145210b0b103055000c0d4034205007618105001001014058000c8000c200c0e240c030007000141c4400b940c540341140c04444d20b2091000c40c4014030350705140314400740c1041490351000035100d4011130f86001100d0098400b8020342400c4601c13004241941e850b02401640808402241d01059104101c50079039249031152411003000d000a816000044000f401c031a0381704810461400c041219040c200c030041815400c2c9002d0740620546010051003064041c0800540c160800c1140d9025a41050340105034461200c11902d446002e00c0528008403410f00c035000110f003c0e1401281154400c80000704e15030078481180d60b480c4804101036410741c40e80c280200c000c10008000000e40752a17040910010102580751050040662060f0380c4901d0085581042d2600541d0b44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 258062419 1250 258061169 258061183
    0xf0c02070501050f130611010c09051f020a02032a0d020d080a12060603090203010518070b0912010c0c02031c05041413050403021b18010303140c0706080f07020f 71
    0x1007400c00743d440300c40410503441c2500c42d6003040d00c052105600081380c6c0d0b54000c072403c074800320811b0003004100d910f0130b010b0341c0c0c9c00064010036a00c084440b01034001039100c010003140305111403069a41c5200c0c80ea0110f03142a83c00303541600446c82c17848a481d18101c0d01000e24051308011030707a068070600581c010910841c034042003e000c9800c009100c142007401078101c43d2801404482c10800c1030f58548004000b803041c990202c0c8031f5401c000204440e078801e00d0510000d0a001405020160303d803014058040c3d00030801660400800d0308004803030013080c802d10145500d40e0b00c8240451010340b040504040c0010220000c800c1e01102070840d4542c054291010385107141d009131100c0030440c001502005101c51180803160904080108140c0d000c620074a102c0c2c00c0b081d61002e4070600d0010080d00500103003904074161590401000420b01c1804034800c00580000794a150140568050b03080030360035084400805d1005007070210440f19200c8856000d5890702c0600321404d180311550b611842 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 258063669 1250 258062419 258062429
    0xf0e015f060d02071403071506090c0e31090c150e0904140a060c02070b041a0d0204080f070e06090702210f0a0c0c090b0604170102070c060509040f0c0207 68
    0xf40c08500201044039540c036540020070403008580e122030702da00e081c602015084410300d40440c00d0040000311000c103802580c1710325140340c0b034141c580b046040510290031a8100400055282c03031305200c40f6604401d000210b58051024007003200300d41402c01440150441d401444401e281164490003691720501c03803201500c007110b400c56652550301301011105018410781c10700f03008844040f8100100b691000e0074040389030b001d40701100d0750791a0200450040744142c045090071200041d54603c5003800601c00701110500050426860301016442e003170101141d111583c0c00140d061094140ca01d440c243d01a8080f51a100d030fa2501d03100003511158401b0300c030400f01c1401d0358648141c0380c3c3ca80940307a10040203c4429250240b9400c004c007409110403055507260110390307011414a4060040302d00028010701a9441c0c40c1c80c0c008207149081c203660ba6200c90307560901a00000800451245000b410607942d00354482c540316040004071001c0400b5a003c040c5841064096640c0106d01101111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 258064919 1250 258063669 258063671
    0xf060c0816200307061e03051801020f030406110306181305030a020123010e060d0c03020405040b04150618020a0e0a0b130f0e015f060d 60
    0x71810784508040000200010181100072640700c2c08504090b08010101c0011011034034032560300c840550b42840d02410b111112401081c150620500035013000d40c000310440448600500242d8030242240c100300c03103001d030050b0004144000c2c8000e5005045002c208401c4140c51400d000700080d0b4015a8003e2901c8000e03007007130025181503492644810015000015a983d803d500c1c20024028101802c41040c904404100c19140040710300c10207043e503a004501c41c04a8a400c0200041c042044070103d800f0f810085000c0016203072809114011032198151101038285403520144100080d0307039526003185484020030484481c181e103101c0981f002d1000607610703070200c0307070450310002e40c0d018141c1c1200b444100090401e010000802c2205050080d107a0480e840d1070040308601c0072441003d02c544840030052110540111910304403070713251180401c0c0105c11a000030010747c42462409080180307480310180092280716034190304200501d1101c14000e44000040c8103004903e007802020f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 258066169 1250 258064919 258064927
    0x6080c1612030b0a14010f1b030c05101104150c0b0106080a020708030141010f030207151d0f0307110d0b090109030e150909040809040204030501150f060c08 69
    0x56070090340400790f1204064910f0543c0b030340300d20307440b64080000034000340054040b4007081c0c02d2074403c81111001c04558035034243c844610303407422505400b004000365410b000e80000420203c1d03182c4260030200342d0740c03902070f9240c51400d0240307282190001c5c40301050004140003030740007400300c400c0903040d14418208010b498a5030311404000380207402004040b2140080081035544c0c0121040d4500c0c3e004007645109054107600c0c0f21b2454009245048941c0c82d00201c10010798000e050304007243e46540303030050525590f0707252840340c0c840001d03c900c03c255a509130204400b81640e6030309217441407880240f0041680d48038030f5503a88a10500074000d86010b208803c2c0c0b0f565004c5e0b203c1c50413500410005a20b0600500882c000d00800c4801c5001c03440c0b264a4066074100944c40c42ca501003403260603400c0c03142940502448100051044a903406c0802c00e545040d61144043d10165003e0703000081c1e2003d142554105052080c4c1010000b403203005410003116910041c81c569141c0d10505040d25 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 258067419 1250 258066169 258066203
    0x30f120b04090c0807060c050d05030403021906050403090501080c090d0611030906070e030703120305062107030b090f060402012006130615060807031508030703030606080c16 77
    0x309080d80d4030315401814150200e06002d04000340100b641c440501341d071805a5103603019684840300301c1d00145240c100458203802240210701440d03001d4060f0066440440b0342c50795500102d2910581100c143e41d0742c200f07010605500c140300d0005000c007800d287c40c003400d0a10030724040d4094080f029110b0a003444000003040510780003804600e1482d24016201c0c180341580645072541141c492000426007040d448980c500010134100301c80e0400c6000380b10418000c0110003074030008201903001084a0003c06070200d1445a00345411410b80141100e5403c43c0b40c10140c0d854003910511456020116415081070003007846504542d090070081810a402e0f03860b0800c2003403a0303001c41d0072800f40740d04200b1007100c40c200710151140f1900f4200002c818029649401c00030038017400c0300042c0c1c4100054900c500031b502c8000d02c10700000a10350300c030707a4902c03101d461680000b20032800640c40d050100009904028440d070080080e16a541c1400d0714841c0904d854200008081e002c484a0b101c0000c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 258068669 1250 258067419 258067421
    0xc010c0b0a23010303021e030702060418021315120501081209010908070609050a0603050f01170709020301081513050c01050a110604050a030207050103090b01050d0c12210c030f12 79
    0x700c03400288181070b050744e07403410041d4440c07a029200920402c00c0b05120082c1c19030201c12030f400158006c00150034070f070800305041c180c102c000c0c5400703411540c20450382c0c00221513200050b0003003590100c3c5008100c1c1c1200010032500a000484140b070b420f00c0010b218124021400f00008241d0300d85141c0c840d0380708401240d06e40010340c030004080c046c000d004542035a01c40f564405440081c1c1c0c1700f9000c599a50000c40403194103d4805452400b420014000f82c0550030103100c4127580081206c1c017082d1124a0381c4220b910a90262038290310480c5440548000c440242c0d40c070a643e944407020760006920f82c2504c81d0300c250301184c100000000c50030003141c01000c60302d01d8074604c030049421900c0e081c9403003642e0350318948003074004d80305980300018151311901030b01403560f50001300c0c1c041991801080c0450140140c508403071581d819900072400494561b41440401c0c02450151500c2c1c40540720084010b1040c0c0302c50081203861040c40c0d01003a08070406030303918030942ca0550b02c00000d82400304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 258069919 1250 258068669 258068711
    0x20d0b090405061017031608040906090504060518030706020c032803050f2712160c05091302120f1009060e030a0f0f12110a020c010c0b0a 61
    0x9900c16030034024003080c404000707001407140d0188052614659141c05405501c0341c0513415a03001a1700070031021010303400700042c507481c0600c2150303d141081e40b42c50002068461982000400640c1c1e04200014402d480c01110b42049142c0841d025600404002d16244e115170100980303101d8002541c504428030800455469074071400c41c2e8040c040038003400940078074028407080300203828400451007141001e00b919000c0e114081e1000c032022070761a9000c1141100c1d20381c0024900440451327028040200000702007a4090319030a004210044c03030000e1040410f031308011b00802002e0104407c000d1510110048503404603110070084200d20761042c80d000e202020003400380169101100c190045070010314255105110502650030071400c01540c90044030840700000310f1001511021038000e5080e01044c42c89441c003070520301440700702d410030307601d82d81e90049800070b00081085d400b613814800d2200c8404240703443d6040c0d08460f1100e01507e40040c1c914038080e41c0d9510340303103c101e070654120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 258071169 1250 258069919 258069941
    0x305070501060b07060b030d1e0c0c1403160302060a03090602090d060c0e120703060905250906060509012102041a0301080708060f041704050303190e22020d 69
    0xc1c001c183d101c00110311a6045048105ea00340c0c01c021300d06800385008a0010900009540d919810402102d841a4003a0800071040d081c071405081c2400852013014410010b400d070702c90317445200803004040c146041807481c00055401002202400144c0c1c03004211246401d40b49000310f03003003099050000080c404c040040c0e80c44503107081c079101004480e8003c414841c917184c46821034506805d082c0029510501d219034400c3d04030300320900004086501c440c01040c001c1c0112900f202c030440c403c0e06000c08501f603400d16184030202c00c001c141214000d51001c0e00301ca18083d42800810b400180140301d4644004114006200503403002e80b8880d0706450003082415441100740301044030303000e001c0d8803e0113120f000d405016804600d806000601500651001c210000d99560340d03200c60356564541521888604d1007040005160303a001c0018000b501d260b113000c9401c2603e0380b40080d24010034003883c50301800201ea00d42010582c109440305144280c1040035a03903c004054500c003c1500102d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 258072419 1250 258071169 258071171
    0x1b01051903050601110106030f0206181503041b050102030711031f0207050f01092001140406030e0c04110f0306060f0c07060306080606060702100903050105090c010e06071e0305070501 81
    0x40c10048681c150407903801100284c80d802240d07424820014240c52960001070020650104800c00505000008200104c0f05600c0a02c0b42c040990002d90b100c10500300455100201009000a01501102c00c60307480340840c5420540c24176000001c0d489008280c805095405d07860749a08040d101405510208240e001e0650f0003d5803080e0004020f40203400107845038883c1110f071403079800051041141d0550802200a1a0020030000c0c0404e44c408142944c10028016100c1000209840190020b80041d40b03000c103003808401d60300c03454903a400b1082c5d446203003481003024251108078222503540161a840035a259034400c040340c0144540200201d14120004100709004000724684066610ba0703901840096920503640da40c814003a540d89900400410210700145030880c0b2580b026050f1381002c000790303940c80d110756003121011a2104021342200f5900d50b4a9039001c0005e503c140b10452f5160305004c0326803649010307000c140030440324154103424490241070003403003a603000681c005c2c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 258073669 1250 258072419 258072457
    0x191203020f03040b040f0e060109030b1e040f0b06010f0f03020a050408070902070b09240702010b0301050c1b060f0c1b0a05071a1206010e2706030c01050703021b0105 73
    0x74003440b60f45e0051103a40581c010800740840d810300960300ba6401124169205061142161104001c00c113001e4050b031400e0880c02c03544a840c9079400f5034680300d2401001411440364a44c2403160302100b00030b045074108044141c04110460308030300490341d420014640141c59141c83c0005a0307082c817898010031106e12801c4000204114950001d01c2880c1c4105160800740e181c08611641e1080300c2200e0509403030b04000d900702913201170501d5640c4001c5034400841c49001d030700040f134216002a110010b010b1800600020124004001c01402010b44c50041c0614602528003d1f5004000380850300d02031000506400030b507480202104100e81000251912030f2601d1415507a249840c0c400c9042e90502070b82d40d88c2010085006640115404d080c8104607540c0e10030044403000c440300c3d44903a00c846d400840030740c4c078150402c8a50401e0301c0d80170507007100d0415101300341c83c0072500c0c229070f41041000c004240020354040b440e01c01408007000481c62014a070001a2010b0148030807081c0c1620a00d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 258074919 1250 258073669 258073679
    0x18080303100608010b0d020d060e101a0702010e0904060b0907120510081c02070f03110a05120712050715121b0e0f1305070503090c191203020f0304 65
    0x4001140203128010003046080ea6885040e1082c010910803a00600030a2002007200246c980080c0501c2d1800d000c0021016160704c01d1080740c00e002d40d02d51559141500060203801c507079118001f60500c40b810100e060440350b17400284082d502040803401000008081010440300790070102070301500400e807210314a410309005201d41c00754040c01e1a07446c2040c0c0072032401d000d44006c41c0d00b51140000a003102c100c440790400b1180103117500843c00c40c49031000c0012400384920f01640918401c0268214160400382049110251a005203115a00c1404005051200010300d0801c5a02c4185061805445401d25074100503c561000040c1000749403000312144c0e210f40c040e0108580741e10204600c050135600d281c1c601c68480301c4c800c0810b030741c0340507651030340303006080418000d0380240040701c0d81a40414140c2510010365264000c01d40c04820b21100c0041401140c00300401a2002510300701082040c0d1040042031040c109542210b00803030f4207061080c03084454031600c1d841225038941c1e80d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 258076169 1250 258074919 258074923
    0x90d0318030c06120507030504080d02030405070504050106020c03061506030105150d0c0503010806070e0102062205070f03020306011d0a091b030b09070902040f0e1e0405030d1803090303050a1808 86
    0x344d03c200e111601d00701c00219218001e128a07070103580c00c820628140070310740e40c0e1321000354001740003a10380703100e94600040d955071075006e194060419503000c3c108084007081418035120b805440700c0c002048008412419482d000c1c2a281140e4084840d00c50700846008015810b120b02d0303071f24003602800c0c10409004160840f0007181200c000d502121079a6a0300c2d50110344041038507042c4d50042c0c1010700030808418000e480800c0740c0144d20f4800003110210342d01c0c2e0b4600703d2194400141140060002c0046d45001e0041c280140109144184014101080c1416080d0014201c1031000d54440700281803000804180c41c0018502e04000001a102e05250070001c00441d070340c4960b440b4000d00410f0302c01c51030003a181111298003001c60030606105003240800c0c401005149081c0e00c0081c0180c01800c5c00e1003147c010f81c01400519030310b40e000d5512001345d902d52840b0264510503451035000203075102a545086a800d0300d4120b0311482048000ca41c184020a0f010740c64800c014030100d482e80c80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 258077419 1250 258076169 258076187
    0x1c0b060f030109020d0822150206060306070f03180b09010b0a15020a11010c1502030a0f020a020c040f020c070303120b091b070203120d0e01060b090d0318030c06 71
    0x8a8090352440004410907080e9444844000c0d04a0490100580000c074164003034141200b0003100000503509001d40c030030800c9091f40c03000c0342c0717034511203c0103005540502c203880c1c01000c01d03405001c031803500c00c60140c01a04e50050f60000c150fa07626600100003a03c4440340450380e4029400301c2c15003003c1d01554041c2100e00d125920a452020700052031404d415000e4600403100d1f0080d0880c0b05141c0c031200308911850a10a0502107815000c10001c0d01410b00d0440c0310003000342c0140c4a0030b1484a0004032074a91f420b003284a8410070003400c0040d000200d804140404031004902c0788442d00e0288003074042c0001103125403040e20b0f004401c054202c0000801c0c000140402c00034401c080003001a100c5040d41d01070300d1540482c0c003c8020600c450003e181d2280080c0480b50010700e00742450b01943d10841c1c8410300f49070742d00c481540310321003030060000a1600303080d540c0c144028800015221030166130010b0500c05d02e040740c581c81108403a01e0320015504145c0309003d196481d0405452912 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 258078669 1250 258077419 258077431
    0x100603110301050906060a030f11040c1214060919150b0a1716050307170f06030606090103240f0203010e100b0304030f0f0203070204050108070906060203090d020f1c0b 74
    0x1090030f000502070b250015809104035001000160014511384400c0b4100313090f01415281207024207507402264489005010040100d80e862280c100b004000010072290750810303c0304a04148420700c200c0f9940e00c5080e03500000b262076000222042c1c034000c01c0c006d00042148490140089800180a0314404043e022800e6207403102e0420030ba00803100c290700d03102200c0e016015408012a91641803050015580c804514105154484180780c2d041c841007108650580c4101d10000401a090500340700c15504100223503600b180710b5041d51754030a5100408100c28000107282103440c840507a00340c2003c6180e200420702150ba80d45c552001e002c540b8002c6410341c40b8100d0024000440040704800c41c0e1003942c00d81e507111501c00d841d11003110780c025607010880071440300b0300c082c101680d43c612889001300340c40341c020040c81d4070304a00316090340c80940c070500c1990024013440d85182ca400455110455045403c0f6891894880009507901040341c2c03540340c0341e030f40c0d60000000c020004038401e009076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 258079919 1250 258078669 258078671
    0x60a0b010c0b01031b0e040c090e10020c0106030303060611060402011404050901030602030105090702070b2502060d050f0901150509071e0e011e0507110609030a0b190606050f0c100603110301 84
    0xa52a45214440904141d40041c123004810004000b0b0001942c400b4411500c08001e0700c01c5168049441001c1c1d82042d0354502660355120380030001c068040c4200001420541070180076906401c2e1084c2c1c0320b03071b00140302034180402040a504130340040b00450b4081c10004098151558490070b1580082d00f09004060150180f4408580c20500014420080314100300700280f910303401a14500e401c60200851521108140c0700400059032800081c200164000c0380018a6141026050500140c0540703502101d900d03102082107044415103140d401d1b90030584046030a5141c0d11001c8660080c1e500c015035510010441345140e141c0d103e114001801402d0341c4026422102120100040303666004c03110216070104440e400040d0351100741710000000410441c2006801400719052642d885030446111455804010300681002180031038458130702420848241040c002914a11039403100c200c842c00046080300002c201000f0032250100f600b01c0a100482d928503100740740000c1c0c82e01c554829 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 258081169 1250 258079919 258079973
    0x100905041401150c0503190909020a0e041409070b09030a080c07030c09060e01090902030124090e01050906010b03090309030111030609090c0a051210230c040503060a0b010c0b0103 79
    0x3213842801541120b680040286151035100c07400c64003801c043c14202c0061029041000810b03100a1019000c0621152144030030030356840104811a070301c1405030b810300038404041c007861460015103c0c0a031411005440c1c2d0758100b03540000c3c508026a0030041c00907100191a287d944d001051035002c8038402d405002021352942003600c00d40d44980103074145030386560010809442c072074200c51045400a00002214000c454000e0340050b07144010710a40a82d150040220520320b06c00c0742e8070a40b041c0c00800103400d040503141e03150841072140341b20b804030210201d031072404240101c03480c1500050003080510880c601e441d2480d0000c842a9224070100c400141c902d0070023003031300302c1003240003880303821407505000070885203920503075480d0294800c1811a00028001e48203e00c06a40c502580c0a105a030000311004400b0006058103ea102c05200030412518002900c9402041050021a12049600c0101c5d814408604e01810074541403000000f8059407440c080c0b69442404a0040341d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 258082419 1250 258081169 258081209
    0x30908030a062112030c210203071103090f0609012109060b0f010206040209070c06021c06050109030302070e1503010c1701080106060e1215010311010f0e0f100905041401 75
    0x412000c1d20703001340407145043c0c1620600ca1003544062502d40040c03c0100b180b121840d4964041004000d085103c20703070010510444a070090300d0046a4100c1c0c00c0110b00e0400c801000c501e60b44040c41141d40600d1780030031901100da020f84e1130030f410350700c0a40490f940721403c1c0c50044e001d00b0b644901591601e01d007080600c09401e0820800181110603001040039840d030360709018802400600704d508100350300321000c0000d0a03a00080100100d02000c2c002d1495903000c580f0200d501991020b410b214640300700b0000a038002c198081103403901541181c4541d00c0c0540100d551a65103545a41540382580c0d542905401c8a5210080c80042e51380d460b03907a880351195800c82d4a94000c04003c9905d80b4881a694640603800d66426402441507a0000c0075010603098007520a0300202c40e03529503100ea5081c1ca580c00544a00526401e25080d030b5410014000310300700c40d96100c0c09600135644201c0c0140f5003801a600346004200140c002c0024002100420114100c2800b03048800520041c803600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 258083669 1250 258082419 258082469
    0x1403030933031509181501030c1e090209010e150a08061005040e10080a0302060f090303070c030309050106260c060a0f2601090e0c0114041203030908030a06 69
    0x100c21080f02d000c0d580c01c5038890080020b00c0307070018101c42400c40d01c484450001c00c3c050109065118188071469950350540c90480043c1143da0802001d0b944062180160781940c8520141210ba440c0f600507640d05101c1c0040300d800640e0041e40e5003143ca0300740703074203002c2409800034040f4080c0342d55920500d072141e40070042c4071506910b00074000f800500c810b02611020a0380d02c0d800a0814022450155030b42c082c142c10b020b140181070f00960440003c10414908240348650b218804001462441c0b41c0000301800181002401408050341c4658541c01c021003580214046c2c02460241103140003c4643e10180c045111114912809290072042142c1480002d50380ac07510281c03100100d133001d00d142140c80a50110705800c1941e42c04480382ca80c91266808540a0714918001040c40e10044903000d00d4200d004040f5030410142d107110008680740c080941d000e07501000e02c1d00d48129000d00b000c0303029000c46440505020b0f00003060281004856000200710740c130cc3c1050f000784c1241c0d100c1c080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 258084919 1250 258083669 258083671
    0x5040c030c0503010b39190c120203032101050102010e06060a0e040f0f122604060c0e1c06050105031f020306120d0e01140a09140303093303 62
    0x41c082941840144803006508024000f9850f90110b00030155802481507402010228580c0141900c1150003080c401d0f404d1001180550000d07030701d80445d49642e44c038205200318610620070501942802e0504650b002d2046500700401051001c2c1441c003072a900d0240740c10203100309800356189c820504581c1d200852054402c01d8010052101a8a06401c0003a035032001002113844589403984c0c2070001e003515640c80613071030140c0c203205120710b4108000780c10004a020183c004541c80e80381e4401c120034028407240c0c46035110b1000305d030100e44a00c1c203403a0110303510f51859000034038050ac1c1d014040c07090720010000c0d01520003031003581d91b18024183c55035071500d0151020603c107040c00560104a4000b5500f00501600a440c0302d024441541d04222015162400180840054421641c1c0c40303642268950702032800c41e450030300941006015901c0d00e106000d0314a0500070302641503901413090320030101c0c0141480811032003281a081d40c010301c1010001104603400b012032040b084078002d803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 258086169 1250 258084919 258084941
    0x6130b010909030302041a040f0f030b0a090302011b050c070e0f280203040303050f0601110307060506040e07060c15020304020f090a11042c04020d02091f0f05040c03 73
    0x61016420021448054030410000340d09040e000c00c400541010301500d02165408507240c04c50b111410190300c00c1e00c00400e540b10114440c1a0f074002d00202d110b801030340e50058002c1800007511035040c40c00b41d0140480b076030034480200c500a100c060f0250844010703c0002030850903520314070340310022a0820641030300c201c00f050100c10300040c100607030220400682c1c5000d0104040c00a200d94500080c0d80c411038044000a84400500059401c45081160010000d00740407450700d03848074001c1c3d40ca01a540025051a8860001c0380e41511260f0014a51005040940f2000c1384c407030802038140a482201100c01c1c016032503180b5002e000c03a100f60313070203198000c10420121441400b0480e500c840034000d2038545680d140c10b0103041940a001304010003c40425203000070b00900c20016120740c1224411a00382c2c80c1042200503911242410045541111035811a86139424000d4610824002403115105d82c02000300d0151401c1c0c18050031288211000e000c0180200390031000d0b900e1010f04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 258087419 1250 258086169 258086183
    0x60e010204060f050a020111031501110f0d0516050a11090a0603080d0e1f06051003090812040f0f0501090605090f0d1d06041806120c0308250606080613 67
    0x1ea504141c440c00c0240317a51803407440045410214105c00250a50042c1c0f1505803011102c20484a0b41d6045401e5850103021a009411240d4117104442d850700c40e49819001042000207400d50028182100c031840550050708540e9840ca0500d003614029800088641c0f10300401c00010746855050700a5a0640e54400b00040c20004070301400303406000b0341c1c0c60031400740c000c58000a40700300c41520648980728602101040b01c0b0f2400381401050540704213070108140c00c003504d22010503c40c104481c500419003059201c40e070313902c2c2419500344000010003000108121a008140300c4150040c405903809458100140c0c1c07214850560b94180c0710943c500c48d500890b9003003450340d005110711210000303020010300c0859110b60015880e0b43c05904504c81009600400c103404204e00d1140e81302800421200e228402c8080d216151502072031311000300781c071500284c15210204108028580c2e85004007034210004428500704c40a05a60302a0300c200e4424440041c40c00943c001d000d0117180d8000ba0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 258088669 1250 258087419 258087437
    0x60c03090607060204030b0f06090702160302063108070504020c0604020103050a060510030510080106030507032621090c060a181d09070803090f061303050d0903060e01020406 77
    0x414441e05801110098a50301ea007800b00101103000128201e1141c031070080705030709030b2800508010500a010709010708640c01295030340358100c01c84441000380ea40458486880d40c1003003100200040c0d02200c0508100c00c0080401e20401c41600814203860006050740d0f055900d03041800b040380a004200394550f03100d40c02050140d4042d0b48401d0300640d1825001c5002500c850104c1c0800f045040e4200010340d440e402c020040a50403905000761090b070000740300365855500c420f0740d5018140000381ca40c041c000c000036900c044400c0c5807003800341d4100c0c40e42e172101d4150022883c1804c0300e6403101074030350f94400000e8200f1008545183c0104004103407e0920034208003c580c205001044d69450b4803503041d0100da80c4c166488045280b0f15840c004e20302616150500c1800d110441d031003002c25a00c1400040b84a40e200740d05410701c14019110b1076261441d80d1680d01c0f5081c0380d03601c050064064015294845070303111904009503030266000384420b1016021080c201d10891213800001b038101c42d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 258089919 1250 258088669 258088687
    0x106030b040b0d032105091e0a170a27080105130314090a0302092a0901211e020a0e0d0503070206032806050f0907090e0702010609021314060c03 64
    0xd102540520703010003542036517290b039031285044580941d298003032a0b1084407800f840c824010400f51504c1c4250b80a46407124565845881403503e2032026040b1403008946010800c2c45010070340c00c050000144404032118910381442c01850381d0285003199401c000010b881246040a42c0400d198169074800142c3c2000f42110500c0d00300101d074a621510340b041c00805139440c030700110701819031140c40c41581252150408420307107441c1c45000000c0420f1003108800c0c1e801071115895904c0c00c0c1c01c6081600020020f01b0010a811900c4c4205900e5610f9580c801080c1a80540368241d915207076110505091420850055020400100305a000300101d00c014107002018541004a00c034555900c81d214007542074002c99071700700000e5601c2d80d81030708000c585404031035944000815101e400c5607003010400106400014040c5000c440b8000c408560160710035440503004013218241151501030000595007a241c40f4403429080d40d28071002c06030949404000c84441c020040e004516140c598 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 258091169 1250 258089919 258089927
    0xf130b15150a091e03020405011419031e0c0512010501030302191e0203031b010c0201060b0901080f090f0709021e0a0c061112010914070306080703030e1302120106030b040b0d03 78
    0x9000304d8000040e0100d40040142c8850080a0181050341003002c400b184120600405810f26614001c00059031001000800d10804031408402501044d281580300c490400c49141202070340165009968030100384600e20040d030045060700d02c690709644c28804280104454038201c2c8601903d007454407020b80c80c01404a42512148501c0542501e042014840034450740380b2a5030300079141c90f5110395030f444101e6420b202d8800940814220142054191000240010002080c403480c82e2184404210080c00400036104c40070540400c6406a58a5150703c01c0a9002000c0024154403032001410210400b0000d6800816a59494002c1034025444060140a070303003003800d250610030840c14801aa0f44011140a4065548041000e80d071884020443c040e0003041078041505e0002e01f03002c60180840e00070104c0742c1628054207a64128030011748060707032050381006064400245600c0e2200000b0320759040b14a651020409000d08030207100a03035000b612020344c84003e03100110000b9000b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 258092419 1250 258091169 258091199
    0x30d09060f020f0a0807021f0506030705030303130309140603070513052d0405010308090f060d0903030b030613150903050706050a0f0609060e0f130b15150a09 70
    0x640310100e00c9040008491089034080381d40c5107a40c40c400a1103241c015041840da0f03404c8000791000b80750f100b0010f00403000141c1d001070403490131515280454103c0e0b070100600c0e170250900a042e00e03941e003403c4040a025810480f411008248a003d0004102160004584410307002a0403d0701d50369a11000300e5444d4000030401304001100000881c154170b501e560b0610a40c402140341100808542002da190350b00010000c0c4690b040800500005141c14150f0750568016111840f204da41d103c0020418014269180c0520b4540b03c000424998590800e41050314154141d4a00c1d40b981e0030b200074074043c11000039110f00c180b85000668040a680702d501e1641c041e241050811909a4580d015903506460741c0c1c0c003141e2a040210b090044610450300100083d8400704881403400300e0108600c00d0003001d400c0824840000202d0040135200c08908059202c402d42503a807401d4030507410245049010280a81c1301020101c101303500c000d00b03c4104001d02d44030120080d24280092103c1d02ca = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 258093525 1106 258092419 258092423
    0x1703040b0a0b0a0504020a050d05160e01180302091305010920010e01020601090507050f0301080d1e020a1b0819050d0903021c0204111207020f0f030d09 67
    0x2490f0018a400c40320182c50242c0c44218000041e1050f0051040010080741001304000c42c42c0780680c650b0712090519110001c11420400044070342c0e40d200d651880055110752010f1015140041d0300b290700045408500c0100380301540c4450035100c5412040380c0c50500545003100032038030140070186590080c40c1c0204150907490000303650340b5042c803039111115a1036002c20804d5104900b111100c0203803140440c0e5a5030340f09415965018030040c2070f4006840303010701004d807248211425007281c040354001c280c242d1043d11920281ca2144a04081b02006030800241101060100c0c0d460080f00c0d070404107249403c1d0134914102002e4030805810800481800c0c40140e803008101c01101c0c0c1001000c025905c4a840032600800e054411540400303030104071034160b03072107091290303200b15040d074240c60003000104000b60786e0311213846c21403400e40c10610034880980000d6020021300380c = true := by decide +kernel

theorem cover : BRFrame.Cov 257913669 258093525 := by
  have h0 := BRFrame.cov_init 257913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 257913669 ≤ n) (h2 : n < 258093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
