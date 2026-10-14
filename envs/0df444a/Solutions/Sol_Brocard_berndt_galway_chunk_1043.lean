-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:58:37.752292+00:00
-- url     : https://prove2.me/submissions/633a845b-b314-431a-b46d-0df390d19f50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 187410071 ≤ n < 187589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 187411321 1250 187410071 187410073
    0xe0604021003021303021002030304151a0108060d06050c19030516110a0203030a210213031212020304060501050907080f0c07020301060f080303070212030106020c130b030f0607030b0102 82
    0x18202540098034110341d01500506040d0041201016460f00d00300120046401400320740b41d07003071700030002900c0782d0088604499070291503903002a110254819405205003400340844031a0280340199000071005000b03642c40354843c100800081e140b40a054040d07070200c0f061503112101d51045c40903040b4486090b008251400c4200324240528090154555029040640c1a60304480086040001c500701c042e4043c400055204035040e0301c451a20401880c0c070001e407c52032400003140050348603643c0c0148411800100500108201e4a500440441941000e900f0a0235000380030003a6001281c09442c12035441c00104410704010310b8040c0d102e0240c0ca4181c40500d00001c905c01c803001c0141220040e8100400e41c3c40c1151400d61018001d84004204034002c280d961910980d41e030b0084921000500905002106401d011029070381610300c42d0b0040c000b100b07030a074144501040094480200c060f16051071700300c9510705000d103001d01c1c41118094410b1303203040c00c00503040e00d0403101d2040c11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 187412571 1250 187411321 187411333
    0x50c0310150311010c0b15011412010603021b1207060b010507020a0608090c0603040506010f0621021804090309060912020108061c0c0815070302181516060608010e 72
    0x10424010000d103042d0380c0d02c0707850385180c0c2c003c0c803004907804015124020303d04085001881081e0f54040c0307142d002c00c3d0090742d9200300c01d0004580900c09000d1074501c5142c2c0d034140c02c014000300b03000f5006000101c100c03a003100782d0844602960780c500180311070f5416080742c00082505c28006180104160b260080c03e20618184595010450749803007807107400100a001c401240b41003a090254051090009180b940c0f24103140c148103445140c02e20913400f22030418480028000d00601c0280510740706150442100506a244a8040d40c80410038004551800103d098a555180f1440d2246802545e582592354100300e0040c0070b440307030b981090124030403245c030303500041c2c1c2c1c442d4080342d00c040700303032a40b00100341c502c14402010090b810b002040159002c00100d60010001125040000825a205410344034440d00b5002c80c800c00b19800d031210303694242d1101a003040da0b842000d407018840710502d0254903412010824808034012160b258560303404020102007405841c002c1a003010160030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 187413821 1250 187412571 187412591
    0x6050105060a0e10050f04030b1501020d0203030f090c04060303020c010207081b010513050301050412080c0403020913020d061503030e0f010203160809030d030c02012004180b030a050c0310 83
    0x10034000c00420544c81660b0129100004a1090040d42c200e0605500c0c0651520788a16108800f00d504680d4140e190f40c0c02880420075602c00a0350039030040003600550b00d15269200d085c8200034005180094074800e80390411120f4640f0301c10b400c0118040d034090415061104002414680d040d4042d0b00e4030b6010440480170703216402e084170002d10003428125074440365490103407007480650780324aa05518080401060040c00b242c2e000c3c0b08996030741c410515035103450810314103001c0d601029412116680004200d1000114001c0070207000030107241c1c11290560341e00050b1074070003900c0c07000b11030300d21020002c141d0452688450160f04560b841c1503c3c80d6400004e41d41e01560105840002903040c04009101c0c90308100d5228410190a50b00541c022002c00342c0a0800c10203850015840c188818041043c1088020541082d03840881d00d49494452241e600c00d103111190000c03240e41e40948040c03590108a4140e69031b2144011f008002995010107003805035800404000703c0c10820414 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 187415071 1250 187413821 187413827
    0x619060503151c05070e0f01120b0a18060b030c0307080c010509011b03020105180105040308010509071719050106090e0705070606031a1009061202061608030408030406050105060a 79
    0x10390301200048031101041c14050002d801c0c91110110141043c07100c0907030b50306005000c181c80e820303101c0464850205449a00791050300810034400c02700c001010003801b0317001038a05101c0710f410071582c5001140410088401c8410700303010f00c2c0121811070f41c50300c0e030003580e09040c0700c045036101d0120b02a1020711f107401141521000d00c40304840c1003020024101400c0e078000c0707074108401c040c100d03070441282c000d17860040e000789001d07683e04019030191018600c0704c803814011580b007140d156030755001c1a4a0141401008030300034009905000381c0341c1e1900b4a115101d14014496150304c000c1c80e10940e0017580103002c540042e0840c40030449840c1e814840200d00c40700e820b42049861030f01030758640503400c0500040c00240c20080115000c1d5444a482c0101604018019020581040d24407a640c84121003103580a2007103045515007856805c3c0545005006404000c0c08100030b02844003030399a51400a900454084511080100600c001e0040c03911416015100c10f603456460720030380c00c0d009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 187416321 1250 187415071 187415077
    0xf06020c060d09080c0717060a0b0618012006040b060324060604210c05090702070501032a021b01020601050a03080d0b060c03040602060a090206040513090210030506190605 76
    0x50321064403101070004000071202203032100416002665405507c60710070501054030341d0841c44007031140102260301c0840034465400150700050145241c110210030309000404044403c5041c8213145144400d0f4038921007050440e154040081c107003c3c60a0b1130047d01c620300180c060360003a841040110000d1000901e40301c480ca003c0d90000c2c0c0c250b82d8804c000b41091280750403005080385c01856070820a00086500075078280f05040e4506d140349c0b207109100c46c420342120b841e801a40903801c20807055010743d00c02140c0c1104410341a540c411840b41c44410100f8100352000140d024148008104003000c40b1030400900c01d102805855141000181c402d55607400064411000068001100030702944150240036001d0071040c1c555480811554031f81e00240300b04c00c0940030b000c0008444840707611882c66810f038000c104034103041c1000700f0311542c4086110301c0e001c1c16664584000c0541d44442612401100c141e8001c10700c0d2400c80c0070b105604050300c6106c005000100d00600c01150410f0503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 187417571 1250 187416321 187416337
    0x20702060405090a09051005070f02010c210204030f03050301170705010212030711060103112106070c140114061f08040818060c070806070908030405090a0b09100f06020c06 76
    0x3e440310b03440e01c59260b4001d03e00e2843c010701e541f15451030443c00701d003950440340c80b568940e203405d407008000042c02c3c5d01303941d190081e2100080c440301000e038a002c010f803040080b81403800303401401d10b9201d0f59048600a41c0840a5001c108040010010314441d021030f07040011915015020b11403a02001039641c60070581d9189a00c13a002c030000d0701c807a100302002081c4160410131588107503074034140340013004512100c0e94003520865940c181c510160283e101141c0071403000508050392807042c1240c224980c2e1604a800b05105080703004400400d004044034004510710f01c00c480c0c00d19a04009004070401502c200b8858400b004041141e04096440c0d4000c1c1c004240542c1e41410b0707074564924145060003254440404140c0110b505400200d80c0180d030440700480e0003c0d01c40c200199480586031003481c10f940c0c0308003c00d018a0409954403a0401003215021810b003407010000b55002d14201c803080c10344007500e2800c001c03128001c0402c81c000d160900103404807414550200b2034900c60510 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 187418821 1250 187417571 187417579
    0x7030c06230703030e0c03071a030705120702010c030b0906100305090c0d050102180102070e07030e010609050108030a17130609050c040e16050906010801060e01020106030c0b040810020702060405 86
    0x1510007181c581458031400d0341c01203000010394580782450050010a0040300e000303194822084241d4280c140040c0140030f0f207040c0c000000c0b5280d4900b4080300d0701d500042c0190b0802c001440320702003c03000200c2d140e008031056000840c8403000004014116842505194440c1c0c04141c107125179502c915507201c02160741454085060f94640010300d252120f50017410307800a1409100c1c03018810194050401d00500d50b12111684d0510001241e50f4031450080b202c0c210b15481c00f0032941400395022800c2d030030080c070002c00e031580c1d01c91320380e01143d00980c001c8031282c00005140c448564080d001d19880c200030030481d585404d006500c0007409102c1c010007855599992000014130400300310940c001c0c3c90003402405a150030130710240c0c03200030340010610814181c3d0008140391521000080c810b410694503504107030310b40841203d1b5001341c02e50080c150356a5442c003001041c030700503059010340303214038400d961149083c02c0a89062890001c4450540c8180310307180041e0b44540c121811203200312 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 187420071 1250 187418821 187418837
    0x40504050c0310090308060607050d1d04090f06150b1902010209030607032a12020a17040804080d050705071e090608010f0e19060c0513090209040e07030c06 69
    0x840c1562a1a1031040e070160b252164140420242585411804034184203507607440072500c41c0810301006000b56030005102c1d420400d60070144a108000e04030040c89400140c070b140b6100e0f900850304603061600c003070302d0418200100e50140801030040c1302200501c0241441d1040c988010a02a4014850054488604410b40b03010003803007501612000710000381030f2102c2d40ed050601500034001d2942191038800d84104508461030802c135480368010240c0c0712050080d41c07a004d40070003540b00381e9800302801118441060f4840c004103005114500c94480e80d50f885003402c6010b45810400c480f00c00402c0740c104071400001d04007003584c80403586001041c0540c032180c241c1911403e00940c01521030145448000110001c054001e04800c294010701000b6028244514039152090200410984040006108009910b035840003d528016141440c100001c050780c06080791800e600449001f42c022601c00306c0e07890f29200b01d404a80700e400c010500300b451540e406094441610965041c04840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 187421321 1250 187420071 187420073
    0x620030609060f03070e0115030c0809030412170a030504021903260f0c07061403042609120f1c020d08090a290105040213050d02040b0901060c0510140105040504 71
    0x300302c0391000e4000e003071b00d0410b9581c64840340719a40d5100420a0700090528071200311940c058002540101c0c2d40c81301451a003410840c94001c00ca88000049071041600c81015043d0345280000d40604519070b40e0100b0142840c2c010440b1880d14034500300c40001c0524001c2000450306100071408a011081d0fa410102685201003414012584c1c0e0007142403000694015003080403c41c041910100e1f11100004411003d5a03480c5000c1268010103c00703030420704090f010700031101c0c900c0c2150300c4a58146003036200b90100e000b51003a4800c09c11160b11004098429003802d124402c00c0030110300c0302e440d00c0c014601009588824800150040c0440c8030007140d84090244248810386800803840215030500082800c0600302c3c00c21b01e20740000140001044c0c0345041d001321001c10080c40500900d20b07080104006100a611f44104d0748165940302c8442c498030341c0b41440b8001c11035515410007008180c2022420715481c1100d09690f180780081e410050480300c1642d42c191641030714001070954079 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 187422571 1250 187421321 187421323
    0x80303010f0e0a0f05040f2a03060f0e120409050606070b04030f09030c030807031d010504050616060e0609060106050c030301060e03030d240f050319080d02070620030609060f03 78
    0x100d413040580c0f481c00e0404000c01e000205a103078003090300c9049000c4011295000c00d008000020f402545074003080d07074042021840da5000f082c11402d84002c000f0700303201d41c86101c40c584070507044150020900031908110340701c1c0600c203440d4000000d03210545800903907070b603504c098540100001e062214100304818414452011440134551201196140584a09100e0040d8000d62401c400290001d810000700c03100202c80b6110803441070310741c01c0c10305041c9800c01c441c542100051200c2c804901e50311a000c10304502400784004c0414010300002c2c1480e201ca14101901600100c00b401010007078440d064800004590440d411840d10048040c82c8100007429842010210a00c1d24108003c09003041d403600102e03040e20400e88100020a03541e04034810f000103da208450303060308011941c070301c0c012003480c001c000c007403040801514001041c203013141203030080c42c1c040d80d03650381d50522200d004918680305500c11416000c41811454050000b0b065a000104124000c0d21986010899610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 187423821 1250 187422571 187422581
    0x112050a05010e0a1e0b2805040602041502060c1c0209030a050d09060905060f0f19020a02010e040902030303070e0102010b040603031107150f08060f0604030813080303010f0e0a 78
    0x81d000000b805680d43c85841150348a07042c0f6400d4810f09040f04640660340c1c44140422031040e48440072003500e50300c51002c4000c66200030b1194240c0f11a01d00d40707a4401e191032182078469449000d005884a00700400c0b000c18142208032a020340d440342e414850380c40240000d444000404043c4143c071307440b400140030080c0c0203900c030481d01362045a800504101d4045210313142c3d104640e07101210300396200003c441030071b5680302d19038000b04200082032109080000a0030004080d4070028544000705a09041411b901131034200140c115818281c00c641c0d22850482e44000f0440301400500160340001e5124407002e071000040c02182107001003240d000b03400109144000600401103181d80e401c001c1d190001041a20b1180d008089001c10880400f0401c0480d9200c1e941e9042c29014041c1d005a4001c64003425069001190b11880100c55944070001e0020f9445660700544605410700044102420b07034200c0552074000380014002415000300c5030301195084400400140c44680070000209 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 187425071 1250 187423821 187423823
    0xb0c030d02040b03041b0b2a0703080a0207090c0e010804020d0b090d120c171e01230d020303031b04091103041a0402010804080d0f0501080c010e01170112050a 70
    0x180c000b00d00001c0c2040c6450240d4469401100700c0c6d540c107150280e1036004660540510812400305010400200480c041600000c00418072081e82c02480c10400c00c1c60710080d035104840d40340000807d81311071907042c0115070081c94003803002c0c0b00c21f6402c03074009055804620302a80c10000d1500c00202550303a004907009442d6000010a501d9051040585846640c0a19000c006c60b0385620380700300d440e9161054076007020155490040303200c5520321020b800c1e0006000002e12250300c13041207507101d40840c110f034001c211541541609600400c22407a8403130383e140085105800c0f0003299005030720040110783d0312001500050703800901b2034500110340d0060340c01c0340e00c14a150650b0401c3c03014004004501541c00340c4111030001c44031203840184c02c4801c8400078000360400011400090818001c1c7c81640103000011603550800c0326501b044070301c2644405a140d2110381c3c140c00c50b58120f1003d184524080c40c041c1c1c3e00b60615140280e070b4078010311800030365604139103101060120600c1411500c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 187426321 1250 187425071 187425097
    0x11a01080405031204032303040f06110708030f10080303060d1e0f110102010b0a030f030804021f020a1106070b060628080105040b0418060c03020c120705100b0603010b0c03 76
    0x5007401d09006101480d4807007c50903460110284481a54140c4242e91090744e008840014000c02c2c0c1c1d403010003030705006000d140038220600c0703447c0001e24003c02545c441d120841c800b101f0392628043c1d02c00881100c1d444581160010070510a107902ca00f83d4244059030000303c4020f0305101051900d103001000358000d00411b8805982d0400c20070a000b072042c5161007607000f03001d090b80d04010881d00981c035200c001c0081d0305100244c00028014803101d944240018036818150006d1404c00380e6014140042d8001a000017440304104012203005000e4100c083c7c034001c0c00c09140e40c0e0f5005130200c000e032000b4810400881c0d214010b840e0541050340311020313498603211421205a0140141c0c5013130180500c2b950524501100c1c0d42810703c03c1400703481c0d40c3c3c90402c40e03c0c0b80a81302c1000a00c0e84006109c100b40d001c0101c143c000d0350400544401500d035401d4a6516142c904160b404e06c045d8480c0800201d00b00381150466946035000d9034190340f200b402c2903641d01240d49515207103105440407580c0d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 187427571 1250 187426321 187426357
    0x2120609090f160e06040c050a0c05031c020a03200706150b0f12090c0603040609030903080c0c030105090d170a021c1a1207060e03070801051302030f011a0108040503 73
    0xd40c5698a0080f000c031480c0d4030f88850070b500c0e0b44081005480c50381010b400060024041d00c0503240c42684552000e138000c034162840c1000010300c403d008a003101e80e800500350002060703466164141702da99440e540300c0c465803c07038402820003801c04c4d225186000d0304480d215403140c8a054031a2074210020003004640654480d4110f404c207400c0e40080b448134441c4000500051013031640031403507000c560710040240d4515030301c3e580c41d1801040c0012099040010031500030000400310402407580c02c0c07801c00240b000200c5c40c020107003034a0004001e446c40307410001c41410110781040d440d0105c0d000324000ba03036040c2d803014000c10080c02180b07416400c01304004100a803401e41d541c0140001e078140002c1c03001d200100024405042245002032080b070303224800401c1f8451081d91880e8401100805807180303a40d4540035242900c10607680104032990280c001c90442c84c080000f1650941c0f090001c3c800407030300ca0003c000d0801d60030a528184007560b000141041424011600703062580e14203086 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 187428821 1250 187427571 187427593
    0x605240d0f06170604050d080403051e090d05011e0e030405220f27030e010e030f0a0b0a0e06040c0302040c03061223011103011707030203061306060902120609090f 72
    0x139955005440513186802012150500c5922407050700d03124036011780781c981c03901e4035030140f44141c1c0d883c00021003101c140500845d451990354148007003016003d0000459161072002c4103030f0400e403050305080e049514010625100c8400070050340c04880c01100c400010b400c410384112407415540a1100c0c10307a03c0d00850100701017030365101c989400511300c60306482d4045080e030200b0f14000003030080d001c120141048100b561089009501c9250301405440401c8181800c1520300300c4403400442d6814520020003924610510410040c070681e10020011801c140d00c03078204803805400041d01a030b0700d6218441046010b03800100084c50710780064500b0700164103003c5c0c48401d044900a400c1c01e0030080002524405000301030f1084461b9039040d00d07603443c0240c50081c1001080c2c16440e41c0c0100c10001015036003d1103903034803c215040c2d084030702540c1450b101040381d000360001401641705101004507000c007007510300d50001007501d400a0342d44034180308510300300142101d01d15501c118030f8204 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 187430071 1250 187428821 187428823
    0x102091804030207171e071203020606091003020108010e0606070b0403050304060b04050114060903071a0c0d03020a0e010324270c02062802030a0605240d0f0617 71
    0x340c4140c0c002d40c207903110251240481004400440c2c001c00d082c0d400001d00c204011813000c10424140700311021100155614000c0c09980f0040c22030541c00360700100208001130501200030759003d00c40024000d4004d0440c1e00280c014007042c00303020640a80840002d099480c0c80b000c442c003042d048209100d40b8949868001d02950003104c0c125040d80c1404818a25400c280c080d2506803900300c181601142900e5040c00f80d650000008598584a10000080c212082d00f0030704400c030490010255450001780403d600d0014541084005c2501c100401d001d125880b1610520020003407a001c00d20b071031503540411900c24004044a5450310244000500c05529000740240e80d2000b517003412400c0c00316a8480803544034261402c0581c22810009010710362a00c0c4c0806101c0f103458940c0c9507401c84100b0b280898000f01ea03150f4010340d4a460903c1280f03000d00c031502d150400d40d502c0185c91600305d0015031007405004202c000440e2a01010141085540c000c000640844060880750001c2e94040fa = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 187431321 1250 187430071 187430119
    0xf0b0301030218010b090609030c0a0e040b0f070e0105070f0b0106020610170303010302010e0d12211e0209030c09040c05040e0601060212090d020d0302010f0b0105090a09020903010209 81
    0x8910406041c4a4003404050f024070182c100e0b0544c407001c0b410100c00000b40111680108076065041c0246944107441e030713444010841c05409203940c0f0402500c4c0030b14080001c1f500c050000b014154030174007004405640850447e400400a291003070b210100380c6401104507035040c00060050076000d0000c20b05981c0050006d100c3c1c0109082560056502c51910b104003410805403842508200014000355004031505052188080d01c0407000203195140c00c04445030f507680a0002401a003a02804520f80010010300340424510401000c0303e404a810b8407840694124090a60041140000707581d050021a5160601030000c078810300e410301d000702652040707000302c91003035140014118a0450009109040c2c81d5150001d041e4001400b0204080b604051605940a68005116030040c0c8840c02c240300141d22a40003c01e003443d182c5030031800e948209014038104a070900c0900515501d071151501110040070780180e407030311a140403d0291040c002d02c0364020080145095540c44100c0b11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 187432571 1250 187431321 187431323
    0x2030a05061c0305030f06280302030d171807090e0a0204060e010608040f0c030c170d0219080c010b0406060c03020c0d0807060c110d0f030617070b0a03060f0b030103 73
    0x402c0340b41a212164506a40c480382e140a4001901400021a00085403495030f0300540c00500540011600494144000b0344415040c1e000501180e000c0045040c104141c0710003101504000340b50288020b14810680401455140c448807480c080740c490700c00500c0118081d01e41c1c8041801f00361280a94a0f40d20300c40e8040c201c1c012454420300044014511407014142c480c80e0396846c0a0342c486484000007480b94040c1a100744045110010008215060b0b0400412040d2180d40d0034040103040b107402d280340554080c05540122001b0009802803942400b442e03036002c8143c68071007d50605043c010b060b103400264025140c000c010440320780104500d01e040f4880c2d400ca801d004000c03802e02094407822613004003c64001d114803800244140c00507800c4041324600000d1140ca40c40070380c2d1500c0f1149404a02042800108094565150145030301501805011a0381d3301c0011101d1591074826110b44c0c00c2841000c6400c00c2d806100381c202c24003d100c5910104c0031192510401007140d4004c0c88 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 187433821 1250 187432571 187432579
    0x10c12110c04020a0f111204120209090a0201050417070f0b040e10060804020114070605040b091204030206030a02070f0f05150a09030e0f220608010b0303070b04020103091502030a0506 81
    0x40381e81d0185018000c40d10014080d42c0c130b0241d030200840c030640b685400351064a000340a00550032000b4880c1101401c010701300b00c41800080c603180d005020751300300b02810403070007508041c00307081c0540d8104048400320f5000800da003c1c0c1d0307200800d5160030444e40d41c008800d45054120002600324600028209607a0001400d81c00d5407552856103048008511404002c40c40c00700000d8090343c0507140d40c1a83c00b04000000b403801806030340348402c07680229401c903911444030f81806840e14040010050b80c01e88220031a00d40307415030300050001d00009000240c8942c0000e44a02006210017615041030303071010042d40500020700d0519110040c0030014000f601d0320382e0009004c2c801e18001c400704150980c8603401700c085024240220802c1d1440315070740042800d06214507080410f0300782c01c4010000c140000b00b032801c1c01001405d480d07115001c2803003544140309550105d450720500c0c68005509080000c1c0c141038a00d4044480c0500c0029560b80030b00c0881000b55000325500094840c0d88111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 187435071 1250 187433821 187433833
    0x50603091e0601061713080c071502010606020a0b180708060402090a2d060f06031409010203060604090b0d06020c0a030206010602060c0403060b040b0415033e010c1211 74
    0x200d00030341d80d10720034482c240000e6000c0030f460100e048842c102603003001d882485485460300c1c6d6201c900b055403083d10194003a600002d41004050f90403c401e84081585200034403c582c0f40100c0290f6030807120402400681412010413502e04a940c1d4210500f5034032005e40344403503582c000054648508917070590007811001d002032207a40052050907451682e0010a18240891078072540e1004011016090701603a41c00e0081460343c001691400202555503000c603040a0800700a01003910142011155a00500510030a03030344031001d40701a200003580000701d80001c0c03000103d02d00b210110260155100155150321340d6400304080f1640c9000e60211595642c0c0d41c0d004030380d0759500305d4000349011400e00c024000500c058100354409400104040b0301c000c0e600340094100c2d14054010f42107512400310410400070740b210b50800540011010240142c2c1354004102c07801e41810681800c2d5120b09000c80d100d0380180640704400350080c04041400c4004100580f103440c0182c440301c0e281c4a10f07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 187436321 1250 187435071 187435123
    0x15050a021e070203010603140313081b100306090903090e13050c06130302280e01120605070c0b0a0204051c0f020d030c080a0f030b010219150605060309 67
    0x19000701d40710586040701e2076054000c5001d480d2640c1d0014001260325548810002010030704111541c400d0500c200040c660f02c2d9401c040565420003664000d4181e9005140b0210001400d80d040340e050600c15180241c0d5001c0c3c51404400904254111240a502c0c100001c428564443c06c4030040d60049800108542c4800c44401e00d4850a000000c249500103240ca881e0340c100003026089c121030b103101e441e010649039030004200340181641c210000c420a8951001200405400c5004040070402e0721110750409008501e85080c0f100c019000984030340106a41c2c62140c4244a04160407040b8820700e8100108440041e61140c4146842514424451050040790051301464076a2118400c0c0c00c40c40d15900380054848003043c1036003401813050f0041c0210f05031340020105039200c0c4e56079215450242d180501210b001f107a840741158400c085160a42c2014a501000e4607004200c507810749200802207000307002245c0003560800000f0090004480380060030031460550b00900709862006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 187437571 1250 187436321 187436341
    0xc060c0901030c0215011404020c1c02010605180109021804020316020606010905060d0515060c0f06010e010324110705060f0a0216150213080a0506010603060b0406110c0d1505 77
    0x8000205d0102c55203050041001c46010743c40d00f010014045d1015007080711801440342070200d950344152000a0302a542c00740160b080c41402c0140c2003c0b0340494101e2445048000c3d1003c050150030038255000902d030b41201d00c5031100a400d083c009000f0b540e031f03152000408428002601c0c00fa809032042c400400c0140d8080c0c2000300075900050410790a0652194400006d094054148140503401038001500c5445103002015030902c9403005000c0640b010507040d05d0000c05170300c810941c4c4030303520061000545003000010340c0002005121a005c00046410340188181310f00b840e10040d0009680381084000301310030307104040104041500d6603407015004242e1003038030011a908549100c0d0740000400c0d2000c0400c41401c2c91100504207204e03501c071801000c2c0240c10000d020361143c42c00c0410800100b004034050042440c0070b00c243c0303280c4043c1c2d0504d405203001d000d080c01030080401e80e84002c104014003161000400b00d0a01c5041c138201940c40403901c6105440d010700300710004540e180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 187438821 1250 187437571 187437583
    0xf1214031513020403060612050709020306280b0a090e1003170f0702040501030605160f08061e0402030115021e0a03120b0306070509030d080610080702030c060c0901030c02 76
    0x100a181d48103412088020030909800003600d00001c541e0074800800032414603c9607402810341e494844561008e94201585060704ea03901c511040d5004108100150b120301082c886141c000e08205150401444540900d4003040d80088044641c04a494050030b0b0740000d0030310445080346541c00c41505d66160491090350140006000d0380308800820300103840c0b59000300b603200102c40d056403d0041960000d0241c84082c1d0065404a44420a004d54168101421440c02005040c02e5160030700340708014114000c01444507200c2c3c11404280b040c8400c07980e03411041094003c0c0115a25030f1180301c003002c685031107000c28005119101c0c9c55030131a05218440c094020f00c0000505040245079004c490b0008030b007070004074031611442c01c5030454800b00819402408140c4800351180420000d1500e00780782d030b100402c1000045400e004450711044902c2000903054508540542c4d14854140d02d9403050301a4a002441468104010003800c90054070300c0c058260b0303041c002182d06000880e603500d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 187440071 1250 187438821 187438831
    0x51c03050c09060a091505040e0702030a091802070b041209060203130905070c0f050c0108060d02151605060103030306030b061f080601030608071805090a050d08060109030f121403 79
    0x1c120a000754070b00f0001400070201c692822200d80d94032400a01c02c0c0307500b01100240810008a0103002d60420318054030ba010351244029401d00c074518000502c0c00c41c240c4a206d9070084c407100180b94040300c9404a4920981020003540d05044c14a0880006000e01200200044c00c40902240d05840841203803609807a030911125180d0400c01000300400002d0041818446640c0306540010346545040300c1403030048003d0101c58035a8000541007070382c0141034034031070b00480c0e050400603a141c403071601200300036100b242d4407103110810240844000610203070075842001c00010030560705800110680e4407801d518056500e420003882064142d488503100014150300380880034520505038103520040501d004110550fa915407035003010400c0c0c00100034120b550b50b211070007446c1401001d4211055000605a8002d20f8680c00c1d29180010410010801002c010a405a214200c1c0380042c41e04082c190070f40c0319451800c41e91031102c03640080003048011101400c010000d01c1aa4854 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 187441321 1250 187440071 187440091
    0x1e0c07050111060f1003020a0915060e01090e040f0218190507080a15270509030a1403070e0406120501051003200111070b04050307121703090a0f051c0305 68
    0x140c2c8655440c2c13100380c3c2c0020919130701807103c40c40000141e500e01c6c45400040444e8040042d501c20b9541000030201ca15410441c240625401034580c2640d019414038115611504840d1054482d450300a100b1841e499002c3d6102c13001981900140c000d00c80080d0007000310451105414010194001c103aa80c12100e80c0045001d04000501c046d80c1504a44002000c40400c010450b48841602404000c11a600113441d401190b1305110021a0710030643c110310000b0045040081c0c801c00103049410740c410a078020180031000c04e4100d07008020b1881818401042806002c2d00c44031008042c404580d01906e8039800e10300403800020030020040144c98000060050034100c0c1c0784452009000203417814100020b030b190302c615421041c040c0340301411401f441a40d90750f19290030103103000c4160700700c14031038084c13030041c000019140300402c04a1401b4080d0503440303680b0b801d0748074103120249002520a04050308000100000811194440c02c8211100100568205011002c8560483d102e03918 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 187442571 1250 187441321 187441333
    0x90108010b01090b0901120c030b030c0306090303010b1b10020d060e161b05030c0703020a0518060f010309060e0604031407080405040b030f071706070503071b02061e0c07050111 78
    0x2110304c58100500300790300181090b04c41001c00e451080111100d81c03422400107943c6031040d8601d4542403240d1100a40708a0051000b82080040592684010303c69610951000281c1a491000ca40b1400d048101ca00782658002c1442d03142807006588510088a0b800d45811070210b00080700890190103600c01f101103a880703104410042d12408050304a903102201081208800558100002d01c0b45480c501c024141040c6103106200c2502000e400c903d1040e071130503c0140d01601d040032020f92090003195240f480042c5100143c0c014005084d0240c800f50800108440ba80c4e00041d0980c0036610035503446181800000e250041c500440d04028502d40782080100900e141c1504088401e81c03000303040e500c0e0039141c07036403076464031005034400801042c0e0503d40c031002d09001c0c00803560008180c1003c91442c42e201c1e40040407445048100105803803901c0b0081d0954840409892178400311283d5480021404200703100c1c9500003030402844d9106001001c01d2075480386034121150003d080040c12 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 187443821 1250 187442571 187442579
    0xa060c030e030309040f0614041e0b1801090b0f03070501020c13181401050907031101050d1104121e0b07110309060f09040b010914210714090108010b0109 68
    0x80001054191030b038184810700407a80241d07154171078031400506c0d0075000960649844001111200d40d904400d20032464500d602c10440000900c0186400072101e000a0038032240c00054800c201110004e2000020b800001c60021a04e42c006281c0341c10840c0c02c41e0004600004240d9501c4c0300340a07480c01604240d09141c1e060404101c0c0007003140404601140f82c695015400303024464010342900d0f681080040c214118000b8031601d80c1110151000d08452070954882c016005000a100c2d41040800201801a021254445400342c03880d8040f50303541e05e41e903030000444070701e00444c20b80702d0b0700b02d040e188901941c60050159415500802e40b8100e0390f61202d060342e046a641d0042c982e00d0004112010707159075a40d000b00b0652070303501c2540303445640f007105100454082000960600888170001c0c81540c44580c001030513040100d8000e10700321025070107181c440a207400e01d00f801d4440d1000100f42e589800001502d0004103441e0401e6076070382c90354641d0a9030741c280040303404103d401d0400e02c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 187445071 1250 187443821 187443827
    0xc010e0a020a1502070338010b16050c030d031e151401180303080f0114180702010207050105040b07141e0702061903090b060a0e0f04110a030605070801050a060c03 72
    0x150f112102d00540316800e90703075215040c012010040c091403410303840e0001800c1c21000392201710380a141c400e0041e000e6040050801c9035103c0ca50203031000100c0001e40404120301049000d030541c00240985541ca040f030340010307010b040c031905503e2004039065484401c0c80460722901c03495207944181030807030501c0e0560030b6440002d20074196040000100340d540300700710302c10720480c000c500c241d440c1d20035460070102c18640d80c04107801007520520f074880b2010701691903294900640041d006401c009407a600f5059009110b00c440080c21035080008103c20f003c00c604505109500079259401c8a40101544c000180302e2340180c000402c03d40101220080030141c05851404e1000d040c0318074240102000001c103450308442440060349400b003c030104105200c0141d00f00c0000c1d00c0e40070301d05040200f2a0004000205455100c051840c0003905110000c070140c0d030605405804007490381c0d1a4100400038000885000740030400120001403a420000040c204071002c9a60320388500b25155401c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 187446321 1250 187445071 187445099
    0x206040204090302030405030d0206100b0c06041b0906080102180306070822151e02041503091a01060c0506060114090415050a0b09040b04020306150f040306020a03020c010e0a020a 79
    0xe50440c8001c6c0030110305510b041100d9000c58031950010321041c5031421918010409075000020309803c00d00449065007c0000e1107074205600c03185440c082c419031aa416030000040e8025031490341401130000e2403180660040140207041c0c500b0b405040403200505950b20b40985070706000402c074a002400c0900d040d482c0b4861040c0c03519520b9000c4100d91103142894030300d07030742011803190340b0118200380e2200d80000e66401c0c0042142507003070611308502e40342c00c5604021107100b8140c5031004030040041d0000c001420034900c44210f00c56584940b0010081c980c190000c0b21188600350201d6503030340c001c040000c105080c0020f428507080d911020302c00500326244a6604405180c0e001040c40c3d070700c0c3c14049024281610708541c45500a500304001e41c1c0304c0d520401d010324810070900180f5114a8100781000322024400340d5030720361081540c5c04501c519070000d00140d10124001c000c5690540007880c01c5880480240444d0000640060302d03404405002540301d0070014080184050841e41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 187447571 1250 187446321 187446323
    0x4110301260313061d0d03050307030f02091e0a0806040807060e0a0c0806070f11210f0d0f0b04021206010f021906140702060709030308060411160b060f01020604020409 74
    0x980b0709291420004900106075038100c4004145c05a01042408200300482540035034126034550f00281d40703844c06006440054091402c154459880112482d9640c04a941500d006044589001403400c4203000f406c01040034144140c8100400045a56002880034012500256034601d803507460364418004010f5085c0c07080710390194407500c10203e000c4010320b00080c4151005861113280c1600300400911080240c201407000324249848403120014024a03105071020070040e440d0f61400d1000c10314009c58011780505280054540000c0701070ba0082c14601c41034000c280580e080890400c801d902441300e048a81088003000074140e98400c0d0285205107219005560120401d10310f05070b125a803080060341c0c800e03244d04601c0c2449484000c0d0550192084c4050101410600402413440c1540e20000c0c04100c101404203603995280e0340400d560148a155075a590101020404900700626800b602e5848490b0000b03110f0741040115882c40c52030507400780c001ca81c1d969003000f00809031140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 187448821 1250 187447571 187447573
    0x3180a0b1603140c0c1507080c01090c0e06060319060503030c0f0c041b030905070e090d0906140909090114130c06021207110f15090411030126 63
    0x40010242008001040780603855111424150103038100a00200ba45440c184032003001040711410340d2102140e102c00f445421180c1c3e000c101700f200d2250b121380c050400094920400010f4200400c94154001143c031480340521100140d82c8400301005404100d03003441d0071500800000e081040c488030706020708101d02100041703150316000407a103035402c400302a00003640a0154950089030070016101c40380c2e02210b0520440c4414040c02c49010b646810400c14581c8a008000070071000340941d0300030705003030004501240391000d06690b940401c02200750120305030501c0454001e210b10382d08110b10408004052500d85004144204904020620441c40d541c41c800312000b00f0209542c00d000d105521002200c0c0600d07400c0c60f02406c04940e003c203003950702000161640072a10000d5402c0075412140409510300c160000c50030300209810255401520701041e01c501090b52400380001c403e05503420841c0ca507038080c4100040c8030a01030102c0c0500c2c0403000c4e0581004842418003e80b41d030700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 187450071 1250 187448821 187448839
    0x80c030604200403060f0b01090b160f1217010e0c0d15031a010605041d0a0e0706020d1803021807090b040b041d0f0a0e0307052a0607050318 62
    0xc8103400c120200c000302c954000d08000b9040050000354011524011907045040240101041c006002d088003403040b99458040402c02d107035404041c1c1d905c0e9404030b40003a184d41480001e0724210030400707004184031020403524426041d00488c001c02141c1a5240c80350400c0c0584c846500c12402d80d0441403c0c6002c86865040304559410459484001580700360f1030807400d5010804071104094058225008204007030004200300060401d400c0c0d0855403c0c0d12160060312560002c0024085044201c0c82902c0b49140000380140e00181201210120380d45001214010920340801c902d603034071000e51f10812402d081d48030080c82220701c0760805514103103062a40d5072242c19400c2c5070455800050700140200d0100310806400c91a8281c0c9503401c0c00f440c0091802100814030050003030016468103650344030240c003d02e010011501045c0d001011640c68100074004088010303c000d9000002d08441e80380b11949040c44e07000c2d5441c90342c1c00340103103081c03c03030040c000c082c00225010030960181680c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 187451321 1250 187450071 187450091
    0x9020d080d060b0417010c051303020603040227180703030806041a1201090c060801120b090c040911030d091a0c01020d0f2c1506031203010e04030905010f080c030604 73
    0x1000100002d0600151182184005e680350718210342000c00198103010041248c00b455000a82d80c210680b581140d0302600c03601c85001050910303183d8414451700085100003d242c81e840c1005c0a481103621807100e488040613040391a403100d11920000300422941408075100e49003e030001d00280380001c03101c0c0200740d28138000940784103007640d5044850f5035400c010810b000300302100e00041e0019041c600d8080d49041c102c10400c0315418801717469650520081104030500b0b00080d10300c014002c00601c201c24035410009402000b810426209219541009045034003412003041201d40c025030200410024800b003444035848a00603c0c865517080040002c140380920820f03c0b4071700007a50020310700c42070884800c141000510840c000d61000b003440e2030010000034118807070542e001858407480d02c13400c1c08240f0704004018081c001400101c0081403000302c5001e0304d403145000c0e59410340e1080d601c40041d64546168040040080d18800028001d20b4498001b95003015019000040941d09 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 187452571 1250 187451321 187451339
    0xe0f0a0f110a0308030711160506070212031c32090c0913050c010903021012150b07020306070807051602030f0a110103061a030109050712020307120f09020d080d06 72
    0x40c0d400848401c41e010041c44a556404801e602c14803400750700400c5004a0b03040d2248c01c907100c034460607101d01000a034001c110341307030707031004851700ca001b0f40031079072200740343c020801001204041c000c2000f403920041d000d9103c044182ca10070300040d2402c91314081990000450f0f040b100411210071445020a0182c0c9515120981480313965450841c0c82c01c14042c0c0b0b0034900f80700c0f99004a604000ca10b80003407002d65a0407140044079070711070610001024405101e8000b801c0d41340b03c040d000001d0002d0002c0d0100f482e2004100c468806c50540d0495a501c0d50f068958000c244c81c03c1c8005402441082d0030005100e2251842a0000b8101d580c80c1e0300c18000f0368500354100004503200d0400d42401070b207658060113507401802001d20071082c0c4000b030000d011640d001c14031880160382c0e00c86c00482c0c00300340141ba001c1c10417166500c0541d80c81ca42984058014540c1c0843d1607805444d105101c03200b420320303203d6040f034668001c120380740721801c2d5141d086440c0c00909819801c59a60342000440e151 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 187453821 1250 187452571 187452589
    0x302041d030307032304050d050d1808070203010c09030b0103061a060706150f05010c08030703150b0304031202030c031329010f0b030106141305060c0c040e0f0a0f11 73
    0x1802e83d0003140f860203d5050b0307174005e820090034a07000b800e503c0a01c00001c00104142d07a52100310314020f0b4503004103d100c0300183c0841c1c01803c4255107105114014072011070014550b00740254020310600c002c80c0301c102d40030006071101410840e5072074010f02c005001e41c2c00003a21401404400b508001440d030000c0d090740c1c4000c0c030031914075584242c114a421150300c0400002c1c24142015a403051030080083c0100105480c02008590004002099280070b80e0040c40e418804501100c0d5417074559000c0001c5e54030541c0d040e0046140a00902c1d0002d000c3d0086074401c840b04581c140c110b07140e20300381006a503c1c905007100d2181c552101501c0f0702d04030082e0380e003c80b01c02d0b030001015545018249682c40e5915001140d5050041005015003a0404141030041c0801c042c540c0d03940c1c81c9030a0f07031038202100d03030416644108009103108416100144042c0038403c04c54080000b9844949116591003120420703c0c566008503e14401042c100a5141c1206004100d500051412000000c8c4010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 187455071 1250 187453821 187453831
    0x60b04091712150f040b19060f02010e0703110d030314090109020a05032d0a020307030b07030e070f1a07060509030a0f2609100c031a0303090a0302041d0303 69
    0xa0003142e40c03080c0301c01c0240e169402981e092503070742e4039408034404138031000340301110140115111700c6400e103039464030b034141800760038082c8641d452903888001c0203041e02400030140c0010342c04c042062820740e07804110074088a60050360403101410600500c11024a0b0100a07000c0c5a40d800b911820a903040d0b4407a0302c11035151000080000407441000940412500a280264400c2080008100c0a0040c0c40f2402b602d00c404541040c046403444c1e0700e80710061a000b500f5000d400d1000003003191400d189800346e55030b5102400556801c0f0070302942e40c0d00034400d00b0b8207611301300c40030840c0800160851103a036000245403450919151521420307180e0a8507403035030960000841c014000d0344601d1481045185150001c1030b245042c0c403948002011503860480b511100c40440c030390350400c0219509020040707034280440c011660018004101c0c0ba10b5400b01c011641c0e46840003443c001c012500f08440040514122900359000c0c072006019045510314a8490302400c6c0d84520700800255100f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 187456321 1250 187455071 187455113
    0xc120e030d060603020906090405280b04060e070f0e031615140c1b12061503060928030e0603090309010e0603130303090830071103030103060b0409 65
    0x10040d00340001d003190103660003c010188140300b031007941c1e80d99504561480d0f208031030100d6562507100d15000080f02c10381c0394000f100180850f022084a49170000a14901c0445003081600c0e07507405202c146030350894035400010240c00003500e0341030199900c0c02c0b000c1c5002e4211080224800c02413000381009820034910510b150201d81041c42d07100014018000d000809179003031100d9031407061340c6c4c0d0b0810310300d50224107130010045005d03031100820020804036250480f0118202080302a603116141c0318014024000d1000003013030181c0c000344a00101c0c0d0424030382a07200e1200030f03401c009180240000ca04200c4400713544c4080341d50305000755000d4420301000e5592080108005060101030040b4180648010b00420480c84500e14441711440e8041c100421221014a042c03641e40c03143c50b5807083c500c030044408170420030384880b60403208110f020025804c0c3c0c81d0481c040e00d007110105407151403640200018000606541c00040850300d001e40040f500c461140e864601c401e00d00700100d068 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 187457571 1250 187456321 187456327
    0x604052d010807050301060b0f0c0a0c14030d08060d021516200a0e0c07020d0605010f0e090313032405070c051005190914033006060405040c120e03 65
    0x8814403d0000c24010310044008200f080d01c0c0001400c3c8502070b0490011102901103020104102c0a2040c600f1199003d00c0e41b046141d2580d9680c6010b02404007403038007070f00c03c0c42280d1400b036002c1c41469006044c01000404c020185500f008451303001403c24414020060081c005e42040d060f800e001058441ea1030225000f02050140c981d150440c002035100d1a41c1c0700781040b180c40d464402c2a0030060b8182103540c0c401c1a0700104054018008000707006520300400011013800154000c415104c609071040590740f1803010b015a24060b00398450001c0007485070800001e42d03070320903270b500c4285602e0500c4019401410444100c90048036144003040100310320703c080010511031000f8140034444208400d0410030905052070141582248107140e45000c40b07000d202403c40300e03415000801040320341da04440103141c03207041d12481c1c00902c06195001c00b48610b26000110603c50280034101e01e040034944402c20018101060902c828000500b5016074410100e00416120710704090046075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 187458821 1250 187457571 187457579
    0x50103050607050310031416090203060a05010504081b120604050a02100c05060a0b030a0519260d2c0703050d030e030403110a1d0105030c010801030206030604052d01 73
    0x104100c0010103160400c1002c00801c0f1600e1790b520403400a0340c0d00642d4080c244649199800c6c40c228148403403071042c1100b4100012283c10035002503105440541d40051095900e41c015100d03400f40d0300a41010b604207200c801c05040300c4d1800340201c860010004a401d000c40b026842c00c1c0002a1429105900f01108240a505085040c8000448646083c0c1009501c81e100c9640710780000e003007021030350384a19406002d96810007040030900e8101054507000b94610090240204000070121820110070544c104c088036694200045180c525810350300e82480e40700d20f440100390590700311b070401c1e552480c165541000011001341d503000380c1000300000760550500f03610305820740c8012010141070201d20800c0040100c1980e04803580003651040c103d00070760015060550350713003200d40e01001c2c0b609008400c0c5e0082188504032101079094030300d640c1002c001101c617200c090201940010003040072589a040c0b6900c200d03131000d00c44d800251403640c15001d0b0000c5908019200e034040c0c06600040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 187460071 1250 187458821 187458823
    0x20f0a08100b06210702070b0a0815010c020303072603240301050702072912011e0f05130902030f030901020708010b030c010f03110307031b080f1305120a0305010305 73
    0x10b9485401102c600d800e0500341000100e01560a500c5846508510808500300600810205c0b01529030408059299092501d0003031952a08450214240c4410040b001c5c0c03035405460351950b11900035000e5490100c1a07224451450110b00c121001084001044041004810302075405480c240c404003401c0e1107803042611380c01c00070144452023645800c06000e645038000440700d0480754404003a9032000f00c4598980c104208400c0404410f01001803c00c41855407400b049044e80c6840140740c0c1c20b5581080309201c8142907006400000c8100e89042c0540d03c0c0007002c0081c00f648031a004508481c0c190f001ca4146401009143d1040d80045040220b56806104040281c03d2110003004404100c400083d0f590400c0b0f2000d0381800162502450020700c40c0d0468030209220200b610b64a0410842c0203000388809044000158400e40008030228401e00c2640e00a9034907440024a6232901c045150240000c0c030005c03105071003445220003440001c90042e2080790b85941340003d080d031540c100a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 187461321 1250 187460071 187460081
    0x130204230601080624090d0c0509010b040b04060318200f0301051501030b01050c010e03030406051602120a03150b0d05070c03080f100509130501060f03020a090504020f0a0810 77
    0xa07043c000035208110710380d244c98141100428184000d490b6144c000d226603030711351140c134440640025034030300301c034050103202c3c44880f04443c029106003046a07030b900c0c8035400c40d0003a4010b21a00b41001c000c20841544a9001310740030604818010380300480e0799489044410b1100f20000c2c01003c80c022085a9140c9245000080c040980080c441403501d000450540001d0071110380c1415503420000541380d2081d029110a00e0b404e6008100ca03c501c1841c041c1d40e5002200c0032605103042100280002d4811903007030010038226002410040b602c0509107003142c001408110800d44d48102d42181080451007402c010200c408025640315042220700b4190b030b074000d080c082030020b0520600300282d842240d040d448121450454410344a0800c5d080f2544c1041d80801d07404075802051100090400c0c0440003150300c21002000841c0e036610404d00801034034440a07500c0311260f5000c0100104681296502510040c050601030701c242002031800700c0d407071300010382c503601c40903921405c0e50840c855 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 187462571 1250 187461321 187461331
    0x20309011401170a0b0c0403050307060b03060a020a0e010c030315060503180703020a0605070512030103060f0b1e0904051e030705010609110304150905030a050d1803051213020423 79
    0x118075109142c00318039a070340ea41c07914010311302c542010000d10782e1101c2d5411f98014650020030fa07682d544090516401620600c40c40c14030a010342004115114800e1080302e820819980b11030140d4003001c0c0041d2010440341d42e05609054444c0f100078482d12542c07500b00040c005030341340c09032203080902008405221300c291a003e280e10011050016139030358880c84e01110007900e0032039035a031528a1f0050410603d0030080e05480400300020003080080e42128035108600d06040040c4000c403400c000000181d14442541e0510142544034507042404a007540a8090400c84801445c0d0320500284a1040000ca02283d00007151741000c0040078096400200100c11061041600c090790b942628400604020030310042001d84002280c00c0350440383c000b035081002e8945400003480050700a0340414a8042c400c0d00e03155100d0310248880b04100452a0140d40b842d0800740e0001c601c003820b0070094070b0f4640290030040d000c0f0060382c55025209c022095048600c10120012550119001000d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 187463821 1250 187462571 187462589
    0x10f0507210c02061902040905070306090e0c0a060c0809030a120908030f03130654030c03090305030301180c020f0d0e06120a0c0e010516030f0909020309011401 71
    0x204142d00307a40c0000e20981203107240c0100c0c0c900d60b408002c2032000f8802c40d406044040c0c00c040c01c020400d901548400121841c44400b44070f42d80c0301005440d15040e00603409940000018024000d00d4440c00247c00c465218080345071400461500080c50542080802c0f2044898030300e0641c07203c2d80c4121304034010142c090046081262700761100c101400014049443d01c82445200da0a002007500180c2e42c0f10a06011a1021249210303254082180210b00480050154859a0b508880f002103070320740b106240070308a9907000595049482c00e011a0068041021042002c40407407810300c002c5000b01042550362000140741c00900d0203446c4280c14440640d004101a01c243c1c80780898024107404043c500b01c9040b8100c1c80c00925140500b15900007410300762010030144460940c81502c01c030b20607445010301d20007001d00440c0c2c94402e91030f10700c00740640c454007040000d0145824031002e503001d0621019a0340c80341d00074004c0760421520b0035200da44032a40d840d001e843e030a0b403d0340904020300c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 187465071 1250 187463821 187463831
    0x1206150e011e0509130e010b011d01140d110a0f09051e0103151703040f080105010f0b090a0b0c03071b052d040e100510030c05090702010f050721 64
    0xd1248102800b01c40c01c00002c0c0076000030916a29510420700c0d1808048404041014140d000541070003040a100780c80d01280647d11000852800b200c40355000200c16540c01a03044045094070405800104000b1b209517124544864030420b12809030901000958840300502c962801c01002004594000d5016442d0484001602c18241204144402d000c6c00e0116161040c56180610305c1c00c02d03841105a4941040c0c5441c1d040400320041048030980600c030310341c49031602219400ca810070b118109102c003060f0400c11010b09107901921011100074034120a6540d141c10340c00c01c0354040c20050341c0d04d4000248103020071003485000b010030300050046103a034a05000c0460780c0c00c021a1030410101d0000c010000c01c4140d01c082c100c1c0084d20180c41807003003211000d59290348002c6000d66200a070b040c1750004500d00c0300e50788250304803a0040200e8100070700e004207000e00380c43c010b07285d02c0c115500d441c03c0308511411800743c1405108580e803072000b04503062000055000d01968840f075082d040c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 187466321 1250 187465071 187465097
    0x30b040b040f0203011e2003042d03030605100806030c060d06080307060501030507060c08070201030509100e06100501170f061c08030a06080a0c0608071206150e01 72
    0x51010690140d40000e00226584880c14035251a20711210001d60542c2045c1014a9401000901c0d0300e007528090814803000e10420030541070440014029501d4200c20301c00540411200740c003c019072411708005002c1903606c040200d00b40c82600350160080b83d1618401c02842c2040d000809100169180010722030520100280d100d6005c402d07143c0c170a074404200d01040700e0055200038000e00b00321013201e58581652510754042e0109120903680d030302070b120300000c0950040c0700c402c640d9640418030626024156006500030300000d0641201885810700608800c2c110740f240b06a00c00e510402416603240000c1c4145d00d034041c94011a0400c00c41054400440401c0c5201c00e41150782c20f00e81560720794031200810184001c0030b144410001c52526910280301c9103c1c0250300902402a00307010982c3c55500481d40e03014849002072915081d20002c010301c82c45400040d4010006103401c5021002c3c518402d0140c1d08070342c001140084500450540c110341080e80303006c2200080c2058101c417500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 187467571 1250 187466321 187466333
    0xa0c0f0503131103150a0506090609010608011e08030a030609150509010b031e19180b070e01030f0204030506190e0601060c0501020f280801080d03180803090d140403 73
    0x84500030160f005856440705565014403402d003031414284050f0300e81e403074900c042c000507020547c0c0f2903004013001d0010034418140b13107112a0590b50710351107078000e5074038000c6c0603107850740a401030b11600300d0074601c0880d500505200400405001e42d502052640c14140c4030012203454422036001305c034240d041042142c48003c031860469995038130303544c1c50360b8420442403030602d52101f008500680c20001c0104002030201d07200030403a10f05a0400c0800b6100848101c2540903e8001d0038083c5080000340c1d01c03030310940b002031010308189408102c0c080e008604000b41d1700960421035403034009c1d10030051810ba0040100c401145d440314248020034825400a8a851043c010f100c104010748c0c88104c20f20109404580c441d02111090360740e42c801d84072140f000768400100e17142c82b4241d2295203203007481c45480741c00c1c165250345000d0080c8001010003070b00105209600a640710404842e414042002003000d54441c1d0704400141885071042d142c01009a20581030501507403c1c188014008205 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 187468821 1250 187467571 187467601
    0xc080309150705270a0b071407060503090d03020304170304030c050f031e0f0405120705130902040b010f08180f010903030b10140301181b020f0c2b020a030b0a0c0f0503 74
    0x1400f4485681d12007d40c146003c07284071100054580d07209000c000105154000000c5200d0f4819000782e034249241028100c040e840240c4014103010303a01034040619020b480700541c1c01138841d04185030003600642c2d5083c01e01281d40e81c0d14140b50004500d2414001c028804070851042d000341e154900002c0310300c0920a40610300909000b90040c0b0050356421b00c00304012009000c00034455081000d5902180000d4461400100d010710308040307a140003540070f40c8142e4290080c1ea25030006965845550100103a600466003800744520100c0000c41503081c032803103e07058001c5c0d80101d60441d91605100c10484805d02c2d503420030815404041c2249808415681558a500411004020110302090150401010200da000f1102c4500c200b0760b0340000d80000d220345940c050716007118019007044541d40d004501d07004521002e98042040c840c0d150119402144000c0c0942211520398071610100c100c1210540c06450703a40c0da5910f01d098100b1030b40f0403095203502d003040c6503242111040708048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 187470071 1250 187468821 187468829
    0x703050405070911090406050405060a18090f051b06030910020a111606080109020c070315020c0a0606060e0a1d09030d1a04050105030a030c080309150705270a 70
    0x1a51100820100001885020000d00c100c00b07050103500c0c0b007481181e4417a4011613411348124038004000519003824040d00380f08110042c10300010600d030021710fa609088101a148451361358412840c000790810880803005401000203110f900380702840c42c4021190105100d105074010700030825510070001d02040120344807180580c450300c2e6150280da0040c94a05025114081c0c0140464030f900803007170100444140e0341d80ca0b0101c2e643d03403000d2400c82c40703800c605e44900e4000c2c002c00d02c045a5082e0203440b1035043e83e44014a0501c00001e0141000c2e0403210449513540c03110810028181d0060814180110844c1d001c01054a400d0440b00341145002118418003060b90000e02440414000d071049001d10354028800c15004080c1310030381c050f20b01506446603140000108040c107002a441113480d0781a00c030003074100c0c0191610042c2d0b0304010041d01080c8070f084401702d980109480818010440c035101c4688440101e80840e520120010240c2c5040c920302d42070715007950350f200b200001c036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 187471321 1250 187470071 187470077
    0xb1207030213050a030503030f011e030311121902010b0136091a0103061a04050105030408070204020f04090506013027150204051011030912031b070503030307 70
    0x3902e54840903100441194080c40c0d02c0349800d1800001e0281c04001940704001180740d0520a84e21440c4004c0000c01c1c0311400d4125481c0e4000500000e802010302d0031100e03104030200d41ca030080d0302181b111581d008500200e1007070191000145001d809014400700f49009080c01c8102c400315010081c0b040940b403250500c05681f00150120116146203424050071001d281803011820007003c40500280b14400a80000e140900001d0408080580068400c45244c0e056262a113842c004450b03a400290096034006d50030804040140c0ea81d100401811500101484d112443c20b4218021580300401c214107200d08038010400888411050300c2c43c00f442041807110b4080c05511800081c00c6844218040302c4905040c803895143c5c011a0348030091203400d600e980c0d514030071406010b034010703841520f1b00980a80f03441c0000ca4003030880e6010558019003201d081009410002c1c01410798288880d000350000101c0c4c280400500e41d114046c0300003200141452841c110110b0b03a0313484018684010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 187472571 1250 187471321 187471327
    0xf0f0a020702010c0f0308070216050901030303050907090f05011a34020a121209210602090607060903080907030209010306050c04080d2615040903020102270405010b12070302 77
    0x31a80581c81c03c240c11078000d01c1c00c041706502403402900c0d60f0741c1607560b800903209034510980d00050030300350241074420142ca544c0f116441c42d6002d40107898081c11000082c01031420200358010a40302d599401c2c480d401c0d0225565140c10751180c0860350716030003504000c0c400c2200c441030104c089411b80840c054000e200c400e150745180c0b00014944e2440c4000e60201c0c3c01600029401c00351200f108910340a01d140c01c428489a140a80c0c03400308900c501a070101003082c03203460f01210041c8c036002d03588c000c0002500d40720442000645940c85100c0032107030265641c928100f8141e00c01040d075404100c0b00001c0201c0b60950300080d00c07a02052100903c240e46941c0050328001906003968020042c001c00c1307038800c1403400c1c0c020b80506580503004482503031030843d0114480c1e8810343c550064040309201c000d10351410702403101a005a140c190301707643d000c2003a0510b141103040380c244004840180480090808010002035400c103900a045045044c0050700c1e044940511050b00180d50f42070044e0303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 187473821 1250 187472571 187472573
    0x60b0105090f12010b13021e07051009020112020f0a0e0406051e0402070203030406090608090c0a060503060d1509060b03060705040e130203060103080a030f2703030608030706090b0f0f0a0207 84
    0x1000d45030b0b060403250803421400d006c0d00015115006050101c0c05d0f055440c004445c0014600100e02608001600a6004110001222155a000b10841e40c018503100c4100c000c0190950280e1b0f03c94060202d120600245d59403080f035205502007510402120144416481c0400064600d68844800181088071155860041c0e60b0760b2f044424466014040d0380d141c6548540242410b0318920582000c5000391001405023900485c865107041d00042000b41c0c45404d0040c11038198200800c100d40182c07240b4000300c04554413800c0c06034020488007000c40c1c0304080f450085c3c1616181442036000f6404007090103070301c40e000b0040d50207640c8501c105103505d66541c401c000410b0102e100203501030040b54008000c0c40310000080c10481a6510180074a00c42a04a081200d00555900c2d4440d26100d4a41000b4070039503400c0c40c0094081d10740440c1d0756454103555401c46c0d210034411202c00f03a07144401000c0251038220349601c0700c201e00c520710340791906030380314a40004014a0310900340c0c0d000802c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 187475071 1250 187473821 187473823
    0x80103120804020907180f27140a05090309040504050c01021203090705060a1404060c0c05030f1203070c02030f0c1503010e1308160c14030a08090405130503030c0403060b0105090f12 80
    0x1300100110100134500c25902c5005a0b010b1808142c03800e11500c2e440d510844523140c6026400c05091300b1103941d100e0303035100080e800081001500d061000d001c10070040403036640f130307015150240c0c4c0141c0c0901642501e4400191500d0720090200c1301c0301c2c406004000042c00f0101c0d152041300c2050702c000d6a2100750030310864605034121a5589445400305012940c00c1d8400c001000d500d225401c02101184c50b40105a0355160b410108940d9500890760030410400c44405141c1000710b03800c0501004600c0d500003814103044098200140c3d05c1610100310f9460081d0281040c0c1204191161455041c00802d0a48180c0102041d01519250540740e00300048030084444072400c66594026030101c5141c459010b072003d01c1821011241c4410351403240c9030116909043c1e0394454039092411064a0501002c1c080040c0b103000717940d0300c141500010640c140001c40c031030210003d40b140d03100e08502e0290101d5055000c1e0904119060001c508651500a00a032500034122808280020007000c05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 187476321 1250 187475071 187475117
    0x616030e06070503040f0f0e0a0c120608060627010b07240207020112050108030a080618180d020703080301060804060b0616150209010c0803071707080103120804020907 74
    0xe9500004005040d0040c400080060010f85a090078110780304c0781e40c1e04408400d41d15a000e180c0e0032604132004511100b0480d0305c000c15180007803c1041c000303246100d424048405540c46840700d80c00460402c40c442c40c04031300210044003044130440c0c0c420402100503000360014010f0b540d154030001114010b10000c00e220056200c10424000202800b44480f240070b9044074801b04d0209403140c1400011407481e0003440d06032104080118144000c150088a600c3c41c0a84407540241c4400c2d182410003400300d44a40c824054119882c002e603d1400005281040b084201411908100418000110036004690450f161880e0100c00303038580c1c0c20041d00500c02141110b5000c50f00154406110756042200c0b10b0300c0d4010340030329484c40050a00c0c07000f6441131280c0c0c180054000c2144000081c400b03405540c00405900c0c0016410354031b4200e0f100b51504c140c64034000302d8042001002005800520f22004404614003003940e41850740c0410340c20350010b0401303000c0c000c15051b4802036003074035411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 187477571 1250 187476321 187476347
    0x28080c030c03031618081009020f03010c02030307090b0403021c080c011e0e01060b0a0c031e0c020a080c010f030c030b06041707051207030303020a2c04050114061603 73
    0xa803a40c82c181401c40d00a04202183c44e04045605107802001c0c1c8094a82c00c042200c008101400342c03d80500141002000207620032030f031101f18040581302c40e480901c140030440d171f110b4004503607904142c2e40c05411b4410aa12402c031020081000303000503241e12442500d0120820740d000780d03141d03c601c0c084015000306d8480c0c2c481c540c43c1584240000c000241d442014400c2040104110500182080d0980381c00c0d01801000701d10412490165500c50003034101325074082d29100254002c90481c2c07084140a54280d54001403030054200c00350301c1d0204000004111000060904840d5200003a1844425030b0b030b84801d00d9a030300038044041d402078004804405009002176510b5441c0d600e10020409000320f1b003c114032508801190a0070201031425030040254000d240252071654110007940c008007145040002042085d9038402048020800d00e1025400c2100304018590601045600503807008184011454003111b00b616004119400362341107807440400740c03480d4142a2850500701c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 187478821 1250 187477571 187477573
    0x5090612070e010e01111f0e120702030118051005061c05101a030304031b0e01030807060516120f0b120f07080303010522060b0f07030228080c030c 65
    0x41015042d40003440e140c0107030b0b00342c9400041e03c080314011a10024001e84400c4660301464803c04001080c10454881e602c0d0f503900400d8110301c0440706410400c8a6821046184002c5482c0045280a01419641c40c0340704000e114201e00545074295101700f000c80070b0f0244e40c0d680f80030680d6074030f410b424a109180800341c0368403d2035103490129502c15841001400851904145101507901810a5030030404002d00860030242980c8940c103411034141207510060f0800d400014003412150b440c14001d500511020b130b124411410300e0425200e000b44a6401ca0280c12904200d040d0045154100045c3d000c50000d56540002c003480014016091030540c000c07000484425201e00c000b9895a102c0054000d0b208200e03600c0410559902003802071a5101d070340394031500c2800c18a00c00d00900c900150a000c0f81c0d940d81c3c2d001404d0315501c814000707070003180001101b505040d010032244035030f00c000b00310041081d400c1b05091240c000368950001c01010f400262250007035010015200d400d42d4201c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 187480071 1250 187478821 187478857
    0x10020a0b010b0a0306050a06050403031101060503010c0f0807021f1806020d09210e1315060504090605030303090304090e031309020706050a0506031b0d0c1d180a0201050906 76
    0x1007034414882e080f807000c180001c0c3c1041030204840c10300110000c01c582071034407042c0c201800d41e9410f5a0004251208045640d0f98100004e4140d800340074101440025464200d074002c080715000f403561000400b0300081d5030081c01c0070310410b01d00d0b5214480d0000fa035500010719042100e28107082420f060005400e0320b002050003100c0701c681d984102d1400d4851902c0340d41141d034041060321421940e0240c040031500791402c0408a061042c0040c0401c00456000240114205a01242d205154005a000801c085401c0c004500700d48905409020118015402c0d46030a1401503035a100394010140625124825882c20340d0040003522400d584001c400300503940c494070008000d401203001661528107110214000c50124442c0d140110000b80c0a0300c408070424100c64440c0c442c440c02c0350b1b00074070605800c2d8042004902010003a20090280030406644141c4214000360082c4c007129402c5401c07500c401111400240f000da0340c507420708005407255082000685079000785100c55000c0141340b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 187481321 1250 187480071 187480079
    0x705040f1e0501090608041104060b0d09020f0d02030303130c0b04060507050601320102030c0f060604050c0f180d20191203031d03040e0906070f080610020a0b01 71
    0x340000e00d00e86450200740540c080da6603801100d8200d80c034890000829200301c04180400c980283c0d0079400d55014101181c1107981e0318008006610004000c2405613990340c584007140740c61100c403605a1011170300910540d403241c00094803484041c00001c0f0000018803d1002c100c04441c0c508014000361584c1d60311070707580c0c44000c0c02940c0070038002c036554000c1c40004a40f5038a20b0b85d9401c041246060701c44440700075104501c2446040b4405035040d80b005210400500004120703174046100158007400e06401c0a40501c02600d40150440d90003074000c0c08406400e070440000d6401d079801d55030300d05d01d007001000c0c045180f103600c041029007034007228020602161418040c44070444010b403581240d0320011482607031400c2b50303401400d0f128004100701c3c01c04a4425040201c403401e2142811002c1d510f410210752941c1d1107584401c80e090a80d6080000806040c07006a920002d00d0400052080340c0000c01014680c0040c0194403404d4800e15803a825407080100c00107460740002084415615 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 187482571 1250 187481321 187481339
    0x501061808010c0906030f0e01052403011803080a140103062a020d0c020402090409050105061f0203070f11090702010209030106060918180519020117041a0705040f 72
    0x80380da015840c28411800024010014030900c62180e600d07030307a113007515820b02c3c1040b0041c1541d1309401440f82c3c7c881c402c08503511028818680502c98802007456005800b90520240105589000303101c0d0b45044006104e0303022800c0460801e41d490300c2d041083d40c1d1405004001081c100201050084500c2c001200304280781e48035050608103a10b505511f241c100340104000d0150050340360060300241c511842d01c0340a101d419032b00d640b0040c0054203103103a080101b4103c500c01380b001e49040e07443d5005e0200034180307541a1300d07480f103014103040909aa030310130203580c030320035060000c2030000300d4003d03003060180b028038036114554010106c4d05c03039040c6588000d000c0e400c0703030010903c01d500c1d04a000fd04540a460800c0803241a60900d07082500e46001e500b006001d91850b105284128490344000107a040c0f1003000500100113102140d40138a0000509540c03600e410000046c01d0b01042c030011030040b43c1185010260070a00121a603146e000480300d6001e0b41c0c0c466038448052010101b0000a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 187483821 1250 187482571 187482587
    0x3040314120a09031707090504050c040902221a161401050403030501050415030302100f0905030403050a05061509040204050910020a08040b13030807080705040f0e040213020f0909100504050106 85
    0x101030303030311860105d110705000c1c05038000c00d50741741011909600040040f07040a8002d1a404040c0139213140c1059030703891481003039078040340703103544038800c0615030154281b008111000a0b101107040840e00c2c401071041860700f0712030784420075a840c4040d12050100400120003406100310354000b80f061f814a1b1030050007628081c01002e10031420034a00b0342071540c401d03415008076a00755000b00b807496040301e00754008000c510b0b080c902940c0c56a0045002c60f50800003000194886c1005100000c820f041440c24074102030448260800c0e981060b444990322044c81035003044e0100d400141a40780c0c2130b00c0d2840c040403240300030445400071444288140c1c00c180c0c5103120302d0094901c2d009079a5080100615080000c0005003c15510300101c0c45031845410700b198001c0325810054039141e1540344185003400c0c5030303000c2880c40035000100000c606081c0c4120301c0c0040003980c154100140e4070498101ca003c1c040c074082c0541059000646d0307024071030605078000c10016004200e82d5031180c0b4000d064038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 187485071 1250 187483821 187483823
    0xc03060f0608010209011202070c0b0f0304030206010509130305092803110d030c030c080c01050f090d090f060e040b061810021c050901030e10021b060c03040314120a09 74
    0x1441d06a00207000e45040c000c0f2104000140c0d283c99034440d03190740300c40003504160380503107202c000c104011a80d00701d04030040901d40c4c41c61074a243c60b0b00d09440c0091034204141c21641c0aa9a2203040c0107950b00c40c4000c10302c46c0c82c1e240c02d1154035005400042206000d031510210540340f00c5c44030b0411500d03100300d21001600d0003031400c14200c500d42024091a180355210041c005004001640d010a1048440003005031141d003050746841010f4072400d003510020707120500b49200003000d001041200708840c480860050a00c1c0d040b640c81c01080607a4669940300740030601142c6550000f1680d00c60740003484d003400041445e510ba4940c503141c620340e64071503080140255400300d00341c484140001400d41c241560345071041508800e04000325095004880100d05140c0c03240c03003824080c0d0040c001c0c0603071460800c3e001a210b9000003203228011130b29000101d8103401c80f005000400e50814110399201d60541000c4540c9080d0010101c050701c01c0040914018680009003e48000c00c4c0c1c104030005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 187486321 1250 187485071 187485101
    0xf0601091a0102030f0306060913020f0409050603150103080c10020403050601060e15161103100e060a1a0402030601020f0604050304050a0e270f0708030c010c171b070c0306 76
    0x1c408950040e0781e01d2003480683c1505290a1001480920300200140556100034080200c0c43c0800503c08003030360440b16242803600c40208003400a0704281c840c0c80d0b4000030440007022900d41c50312101101880c1800060270444000480300e00103d000c0098110a000e0f50100f15900c40d5603080440e00ea00080c0982c0b000100d038080c91761040d1520b002c2c841140e466401d0f09601d424244002002c1854541008072444800d0340d040c01555541072001000321030483e4008215910106e8a560400400030f044c84491031074092075007001d070080c041998240406031801603036a11200010b078136020588480d083c0038441d0204010400a011002d04102e46007543c22800c0b99450701c039408440d000490740300400c12413000b60340c0601c4084141c005107442c041c900760f03142c141019403c06c0c05c203000d41d00800150781c0000740c00307521039409201d4a581714036145130480d806550f4000c10b0004103000341200594203800d00e540f2500450100440320317490b42c060310b0b9018136603880c5000d0010b003000341c0d105101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 187487571 1250 187486321 187486361
    0x40f0c120c031a0108070e0402041104080c041125080403170d051b07030c0312020c0c01080603060103031709150106030506030f0d08060d0501090c09050f10060504030b07020f060109 80
    0x85a503c181c070b80b4141c1e8501d801406c00d190400070036024201000300181c1e8059101e20420402608810050002e8400301c1c0107400503001d1202408169859614980b81c0d010003001400007090300c41e409449410314031500c0351480c1d0390900344101d07a40102d402c068856804c100103c000e04212400071b0041d0200c00d503040c01280c0d50841c2048103e02030400e2410341e0f02d0b04012041c0024400c03140150000d1090070501103d0909990300400c070780140c003008105510985402e101580c0041c01254808012001030990350305562f00104650074a40c02001d0040b8044081049888144102940b11041d602c80050540e9130f03607001005003a06407a070354064040c5000c02400b0300070209e038401d02160241c8a184141d01d40e102401442d607440032081d9a995070f10344180c2e0019a20091113001440300040114160a01d0140d0040d03001014007035030342300100c40d01d00300050b40d005001c0e03c0450350001900d115507541c8a00c281d080c84421038103117480340101c1c40049071125540d403015082000920103440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 187488821 1250 187487571 187487603
    0xa230705071205070306020f1306090f0522050c25031707020d050a021603080304031404030309060f030e0d120e01180609030903081305030c04020909040f0c120c03 72
    0x308810b1040e8054415000940b0a00214402d9001000345c0d100c05106103282c1602c1c040748203840e101c683c01240000360442010049280100c00f514064001180c081e5554951070f031200740c01c603030049000c00300140c44000042620b03070003400350381802001643d06080340380101c020b2165221610340450115500001000d0001d01e00c1540c41d1284070513400904042800303510a4805403c0307456158218400c1140a0030040200c006c001c0040d13105403c0d6a849090602d406020300c1660040031300c2c20340d424803041000c00d40c444203c8007202c2d4582049001c0f410064012009010305030980800791003003100005005a01c64003a0350a8080354504200c034294005100b400c6c6d55068149010300d10003001803030b01203280d603400101703a07521900f40b0b9850180c0d2642c3d48030240d044079011100d4030160311420446800d0501508540d00c03800c440840c6006414030024a1100380070744090080113681195100304800010190081c000b10400e5850b1788186151200410109010441c1c186c0c6807050105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 187490071 1250 187488821 187488839
    0xa0b0f070c02041104080d03051501020c1305040620030a0c0905011706040e0111040f05041e020702040908040b09030712050604020904060605090103030f1b02060f0a23070507 77
    0x160084040c0d5a80c002510841e808000103000c5038820301040341c1040100241c8054100401003c0401c280c40c046030074a030207040403409911540006065410081c410751590385c50200410031002203080001d09500c440c00e14200914910420030382d82001c11120807100000007014501c81c850400c018001403c034000101c0d0446540d1241901003002d81d18035080001030a0011035210074060400038821000800850070742e07000c081034500c05500040c003070040003502d428800242506603000d001c55100d8000411101400810b42181c250340414014119512034100702c2d04190400d6216489540314400c0140a07030190414621910588200003800c18180c0c1020a810342c00102a180c0390341d45400384920305200500c1103031800c2c1d4404021480740e460070151406540680d840901c421120003024207007031040d051005101580c541d441d00141e954034211543c2c04178040c0c0890b15841014010381e400114401c2100701c050988140c02a110001d40141600a00520403220300070f0740c0342d02103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 187491321 1250 187490071 187490101
    0x415060305030405060a031b0e0102060108060f070c0f140615120c220603030c0201030c110d300203041b06171503100c0809010b0d0605061c050a0b 65
    0x41481c2c200307001c200700c285402030151804210300e06011940b034040d280c40c5580074000340d00f141e000c1105054008000d5a040144901400c40070703008102c2801d082c1000058000028000010000020442c00400c4584c00502083c00e9006606000b202c0ca404501030b102c080807100e84a05000c0030030400304500d0b100100c80c420350340758000b40c46421007440c140014181c81207907240710310fa1550b0030b1034030007034051045000a40c00b03942d030b80b10205281d100040985968844120421140f144140340b144008a0901d03501c02e5541002c6030b01e02d0341a044180e040e5503020240e50240041c0200c49940030310b6400841c40356104040c2c0480000c044100d4004044a1b405004006842d02640c00e0f10f07400d40e008130a8222440112241501c9075a90000c2d1606180b0345141c0c11668a0300c3d215103000740c016031804e0b0801c40010081c01184417990100d040b00e80407060142c9041e40300e102160454903168450b041820140c18200c10101c6c075401c00540d51540081c0844040545d080010400703440c0000d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 187492571 1250 187491321 187491323
    0x10807020d091e05030604060509060c09031c030e0115090c0201020c100e03040f0b070201020105160f051b060408040303090501020d1202070501060810090b09030306060318011b0804150603 83
    0x900c0401500f000c401c901000000c01c0c1007401c411030094080342c0740c2e4080144520543c0309000104183c0b0b4804411410610083d007034000c40d80d000d02c40f45915550100341c001d5079242c4030102412403100100100c0180000c50070410070384d440e00c0f1040c2100b02d15401d505092b614001010301c00019030f00380c100d0807807103003400040154102c003000380c0d103010b8a5040000d0541c070702000c4074205a10b888410001c2c5240b64413001d08a00000352010855030203009060340241481d0f42c003811046469800b402c4691020349039410010000f41494049241d0b132884071003e0040302c119407441c070b001d10b05095070350b109010680100309a004009502d43c030000e8a002145010b07550340c610381c10100c40031030194018200c22500365482d4078000c20b40504c01c02030700c0420b0340c14020224110a407400c0588070034201800c9145903400410070010030386c555508598220541c4e012203468964158200c90040a039412a100000703070200e039004002e58840c880500860086021410f12000c800008049401c6880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 187493821 1250 187492571 187492577
    0xa08070f170705031204031a040309050411071a0916060207140301091b090608010608060408130806070315170d050a050909010305060901050c1819050409060b010807020d 75
    0xa080c001c038003426200401159080c0c04a82d0300a49400000b802e10007542c4015100c1180810108103000a00a40c40381100c2e45110300d0700c40e400c050b100101a0815130042d980a00d4079000d80424005401084980550b0004500d000c82c800403001b280182e42c054603010007074414215107051050150390580d04a0758035400a0010302d1808000d000740d40501e400c0507605540ea501b415000c10b500030b217100c116580282c071100885003411500030855202c4d81200b105a172401c4014491000b00003841a006a002114191a0a900010ba81424100d50018603072405060103004115806400802114000010400c038450311030b022800d00e540701c80d06180c0240e00c141586080340c0c1c09040280251765184c46c1040c9420101070204020031402e038821200c0c0c0d8013a20401004060a204858100001c1e9640b14a090221059140400800400d044c400c804400d00819601d50043c00300c0000d00020308240040c52082c20405c0c0100806502c20780442c5040300000d05580c800b24420143d07613002d413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 187495071 1250 187493821 187493849
    0x2071b0e0402090c040306020d0504020316030f02060708041a1c050702060403120b0a03030c0512090a210605070c060507020c060f0d02040b0f0c07050f0a0311010c021e0a0807 77
    0x5001c1001c00840034080c413038100004c200110100b01203000804044a01c01408109420248145072800380c0c00590038076402916030f0244000740e030010401034426011a00c05440e0003850418071172500c204d50002015425104004a840c1707503010140c060800110050b00400405108203400c1d104125615401a00041c00150010b8003420b04141521910310001600375514004501c10750010740007540420b0840b6451003c1003400c1000c5960b41d02e118103410708215101d0042340c0b100b07120b8041c03600d221502109407558003822509000603103400060520190a2502c0082c244002c0348400740c4607207003044001603109000103012102004081c0c0650300d401c0c0c0d22350030414290024005504017a03020000000d40f01c81c500047d0450344086004160384040100e000351a002056000701d01644018000141c20703910240e801044a4014005400030901c640040b00e01c2843d02800a52226051f0f40c2d55101e5400c5a842440340031055550500d0325844904881e910340083c07040303024480b100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 187496321 1250 187495071 187495073
    0x70308060111100e0f01050c0a020d0c0f02041404020f0306060114160f05030c0f0d05040501030e16080c01090905090a022b0803070e04091515050a080102071b0e04 72
    0x500b85011018100074152001d0036045046482510369001000a40390b20694044074424420b01c1681c1d00b100061190030b18101104401a4072910359500580c1442190b41c0307402c0510940d101e00c8518994014001c100d040401421900444000d4400f603020303d840000d4440c0c5402e00092042c0501c4050b110640c8088040b00d021107258880c58800f840c9140b00e0040f48005a01725543c2100c8500c540003454980712080a00d0f441c15424880850709540088600c2502030f8001c41242c094440c00e10b804903041b5001c602c0140b0301488480d9880380c0d0180d0a9002404641c04a101c40001384240c3c2d032610125622029034050358002c2e40d032406540c100e950315100600d0041c2503483e031891071044080000d410070340500c100c05902039094989000000800410990200191074240c0c4229410010708003161204211a6094807148480640d2210409000041e120b010001000b000305104012074644031020701030342020404494405480010b07a0b5600c24000c1900c1c00d03102080d007001d41503a51 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 187497571 1250 187496321 187496327
    0x60501050903070e0603160e040b0f01140409080c0307060b030c1909090c0e0c0316080108060411190b070b010504060e07210507020d02070e0c090603060f18010f0b0703080601 77
    0x10317003800d41c18455000e003041c682000c00b01301c00041429070b0306104140703070a0400b1068400010070101e00901e0329030044c803200d5402051440c0d405030035603002440c2c18040c900014180b04005940b0800d101c081a000101301a07500309c0041048161f054615840003035080c0321644841c590042a40036944400b402070609640c060100d20b80036102c0d50214507512010010070a81c1500d00030802080041040070700c02a0301205046103446140c190ba81c1d41c54510911788030400604001c1c915840c01c1502000e42e074a8408480c41114441100620141d4132068160307643d0028000300c0750729407a44000500ca1030244034510441d8034031751103086a0368441200301c1e2440040d2041c10039498019803140722108c85032180e83d02c0b03501950010144040c074400301070f103400340e030741e10040072140114100300302a0b0024069401564081d90007a0b1651500b02c0040d511250544a007908a40564113180000e210030550078126074207405900b49175030710340c1c2642d9043d104800019000c540e100b4007203100d0b544 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 187498821 1250 187497571 187497599
    0xf0604200702120a0b100e01060c0816050705130e010b040b0a05120307080d0b0111010c0912050c10020106060f0f140901110a03030507020c030115030b04020a080d09060306050105090307 82
    0x5981e009807000744c0000d50b14482800300945902c440c4088918080c48400d0122145501400c40d81c04e0003095075000b592524400d00c81c940d00c040d0804c141d608000104281000306802401000317090f800300b00d487c0c0c00000020800044407180540c2000081c0b00f0703600f082d00c119110040c024064500b0b25003406d00b40440742d44240304120030b07031104100f800003240e01e2001400000380b410002103030200c26800014008028007400d0004c5902d4024172841094008884400f06c400080e214480600b181c101681003441c0a15141e420006202c00144031640c103500c8481900e46a407601c605030020514101c81c2900c420305007034042030841525803000d0700000098000c4400516001c146594003445540c01c1610000081300440e8881051105c0303541c040c00084007a05098008100c00040082400c21424440c40003500d4824414007003015512161a600050001c403422500004503207a0028203000b003034807486000070b15041000c01c00350f1140d0b080b140300703140050003441d0460420850321a880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 187500071 1250 187498821 187498849
    0x91e07030c0515120c0310120c0b220b120a1404020f01020c0607080a17070212090a05030307150c0e0a180b1c030f1d040f150311090a11030c0702030a0b0f0604200702 73
    0x14040f42c8003808800bd40c0b180300009042c1480c10103450f0440720034180f514001c040e11300d407042130501c070f400b44100e0040c0a89030b90103601115141000d03260300b0300503428440d03042d502d29000703000000c1480c14030840100404c0107250342d943c2c0c424448420700100e200c54109030303400801a0008080c01004596050180107600340041007000d00e02d6445d800281307560301c41d14080703c1d8605c18100003085103c1c80d200301c4001040fa4204a1182100f1a0000f106034245000e00703406071442c0035144e00c50604a504c2943c210314082c21050341740c0c460703100210804052141c00c5001038204015165007500c98141c2d9003142c1c2030054050744605030641008007070028008035136034447daa006442c5146d184100d80000560141e064240350351128418403e14090007005541d41d1030801c10000302c1001010110f980c401c100c150b030585c03a01c40c9840064140b01110344045c20034620001800a00700c00948580e0040c1c0003260f00704805480c01c240403070090104002501d85071410301046000d8107000244100742 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 187501321 1250 187500071 187500097
    0x5030705191e17060306070909110d091a061801030b040311010614010305010504060b030606070311070b040503010b030f12090d0b091e07030c0515120c0310120c0b 72
    0x1070148040c0100c0714001290440010001840f005101c05000720b210b80290341980a80710a14040e6800361a2218910443d100c0380d5032000f0a217806441e500540d000a0180c100c00d1019503064202401c00929510030035101401d8480400d51502d0301c1d2500c0442c0c100103218001c00c581c42e685503d072021400400035414419600035081d145d04080c8a284054881082c111002c4142c081c001401c64205820450155291110a00082801d90b00f540c1c0d000004a0b48941d0300c814038075003100c070261120a036040c50b01ca1510082142007518010b40251030064008204010441081555404c145024040941c000c91080000d06e41900001c10125002500340784404080b5a10f045501c0403c4445040d2500410309600900c0c0140c1c0f0005c0d00c10002e00001d00c0444e055031101c1d0070710010342c0704540c07144032000402180040400c040ea015064a5261503089190032800d4501c0c0e98004c9403248000b46260001044020b09003006510f115040180000800d08003000d040159100507510450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 187502571 1250 187501321 187501337
    0x203040e1b2b0b030703081b0a060c080103030e06090901060318080d050115080c09100c020402070c03020a0b0a0c060207021c0f020109061704020f060d09080711010503070519 77
    0x6504640540368102c00c00710000020b0712601d030848081240c0e034407040113210781c00c041d40401c0801c1c00718003690720690f0700c4251720300c0354910780200500e4290000c03001809182042045001e1540211505040b28003a44400850408403000c000c181e1180c1c001585d8000880001403125521a6102c10000c0b01c040100940ca030910362500c40c02d40d0410800b07000320b5601c0c0c40040c0403000c0c04d00681811000c00781005459810015070f40c0e04a80a03640c607c034007525500d039104c6440c0d8407854164920a4000c2c0045545000b80d0401d046040c00c2404141d000d100004c1c2c0005400d03d8540407200e44080131b03079411101c022070369074803000381d80b042505a9104206003010312024882d104004201803080e0300080c0d50f07640600c00036020303403031540c05042800700d55100e041203c0c05096005900a6040311041c41d840c04d20070020b03226000c5c200088030043e25000804040140003c000c0c5801c07409080d00884d2036034034000449052204941083c0010340901c41203c80e075942e000f000314035104600300191 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 187503821 1250 187502571 187502587
    0xa05012304120602130503011803030509030d0e21210606070204060b0301090c030c0806062212030315050d0b0406020702033a0e130f05010f030b01060203040e1b 71
    0x180340b040d9010242e41c140c0d07002540841510302c152684c00204400d074024004206030304842c50700304200c40c0000e0207040e03e0300300085851006204540c61880e900001300113440b0f5501a981e03071010b0f544140d0416000c900000100400200203442654003c80c407042c81004030041388010261002c0c3c24203810010503c040c03c010781c1c1c1c60041e9006401d2407a6842e85962400300750005940c04401000103241c504912241d00c1a807064990364017190030355801c1d59501e5060403a9034031414045000c4010001610040b90042c92200c00201e024080ea800784050200100d04081e14003951203200e41c8021003485080000c7e4100030060750141c000c901c01818003183c1c0d0041b03418420700309c01c95007004016450300c1c4160301c065401c065039800300c00c0030300c0300448500c2400391603484850015442044030366018800c07031255400c41102e00c202400c0500c40740d42d440f00d100d5045401c40c001260742403c145d00200b4001c1c40002641e0495401110540301622128001701c00a01d20060700c1e90021010007030310b5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 187505071 1250 187503821 187503839
    0x20a020607080316030905150601020c0406060f02070b190f02030f03040303050601080a0c080109110c0a320c0d0c0509100e0603070b12090c0904080a020c0a05012304 73
    0x381060150b0a81680c911300002c3c81e4550042c0c50702d0200c1454074284030f80740403c0001607080c41d04400d610301c0440070b0303c1e4400140d1526020f031031020360190a01c2808101c159105600341a03510240d001c950b040303174480b03101c414035005142e070104104d4090500f18010503c520500c448445050043c0e91800d0400710074004d259000f2101900403c1c1c803a0148401e659100d40b00540c4044402010081b10280010042845006100790031105845440e0070f1441e8071071000700c40020307000008642d481909850903007880242500802640a0741c02c031070001144840b0702881c0000d407210042c000380c592540401c01c01409001e025a03100540c07070004910790b22158000d6000303540e503059120303084e0700c0d000c0c55111905000f418076019400004040080c00a41010350304809485904480e040e52001e40003071074a114501c000c0ea0043c2c049017848103000c611b03030003801b02c05030b15400c0c1c541d040003500c180b1441100340c0c800c4500103400c0e2541c0c22641c03001600c580c60503003d8000c0c0b103803603e81c1e034144403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 187506321 1250 187505071 187505077
    0xc02030c100e0a0f051309030519091d0f09060103051906110a1107050f06090f031c0c03030c03140705130e100603051b03010b0f210f07111c020a0206 66
    0x904082c56943c0300521281c5004240451b81c0740c8045801c1c4a880055070380203129006619043c010041c403102005400d41c000c1e1550409402d20003824200118207a07407200384040143d4070700791050320800210b2410440030424a060300c1e0041e000b010030581c0d0008203d607060701a082500d1040c0d8903042d0007000450b000080801d1030b00d540c1e4a900c070152214170a030500c00f255005a11420201500ba140c41c0c41d544150f91403c081107440032541d480400c042030606580107603c8101840103a040d104054000900d424030f640030303a608000d40030701c400042c2c081701c1c44c0c4032001001c40740302c10002d5039030b521480003130501c0c001102c1181e0445640d5081101c501c0000d079000c0c03a5030078032030009001e0294148103099200075903803004040b94052138100303100c91006005081115900043e0f40b280b41c01d11804072100800c51411031004011081c020f2044181c0c00d40f41640c001d0b10310001320341c415104400c80c204207209903014080c189006001d2080c0808213200040039405100c218001583d10000a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 187507571 1250 187506321 187506329
    0x6071b09090308071805041808030c0a08090a0206070204092a081002030f060103090311070e010e090c210a08030103060c03060b0f07080708160c0302030c010c02030c100e0a 76
    0x4240d48050345409400346400800802c100a6200e040c41e0080b141c90402d041111b0703040d28001161a6040c0d070110703503864265406491850f0020070b2245400a0100500381401241d40d05d2215465105456071900301080010350700c00d0050191601510f0264060b462140c441c41c003500c081c0309020120b51903d800d000340a40081c0002c0d42c20019450240403044400c4a0380302d0441c594031b082d00d040780201c030003e0320707180c10180e035107401c8010103002c1c10680242003080800c450703030659a040c000d05403000c24018840c008003001c001c200b5444001410312800c5500500c0300e448a0780314180610850310000d401e440c1803280e15041004600071200440c0032b035009240c0481c10807051000641078620030b5120f240904010014418401c10031003e403840c2e680d00807103030703540e69010f0700b00b4074074900449070b008a110706010540001c100c00d48202c038003120b1080d025201c1c1b0210f0300005459982c89104069016004191040301c60314100c85090a662214103201c4040f00700000498506005600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 187508821 1250 187507571 187507589
    0x6040e07030606112a03070806010f05031207120309080409020a02060402030d09080703170f03090a0203060a111602030f0a0b040302061003120503070e1e0117040b010506071b 77
    0x1c003e005240c0d110001503400c1031484018a030144580c41045031514840c031403034016406407003403850281d400380b2050300101030342c104468055854540c0c4100f007201b14800c040c0f280c41024400c41c2948000001c2e1881e058000d446010311041e038440540103070160000840c0d02400c20807001c5003840c410310117068480286e50040906240c507105240c0f5140004812038140301c100c5104111031940020365409480e44003100e603007212041d42e12042d081c054101501c42c480804030401c002c03d080020034004590080f001c460440c0c80e5800150100c80c0c514000c60f940e40701c10000030811407030702811514024800740494800d00d6038007041606101100000b210354101180502092650403c20650482608101c280d5070516582c0c0740034078081c00501c80000c6c010084001800180180381840d00b03142c000d03100c41d00c1c510f8070f44501210450a01c41450101d61140f0440d4201000c508819100340c2e84403050f03000c41e9091400b0800150010002101c50340059612156904010340c81c8a0041c107a0075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 187510071 1250 187508821 187508831
    0x10b070303180b070c050304030f0809180705031f0902030a0501240e010e0409121107060201050613090206071401060f09140f060a0b03180c0a08150606040e0703 71
    0x850020141d07461030110008202d4150603802c08240e41542e51600142d03941004814081103150150450007182d00c090403001030b80f990740b401e1011401c000e10505038112580c5403461031030850751001040548480002640c02d02c0040c0f21510041004031120200b08424680030303684d0841001a82c1c021110b0b1360303605403540010000d0301c030f0740d96054100c201042c0f4140c0500312001b500421000e2082007650401c214040e0308220703515264008010144c000c100d000c4612441d40d8040c03e68111940180c1440c490f0700c900164591061103114020440100f00350380c00c030548101a00606404002a40e0040c4208262000582c14903484400f0585440001c22801c1c5840d020b40a904101e521071071983e424104900d034582c40220101d5800171401020740d8642c0c0351798004c10441012504648600500042440502c03462203420034481d00c42007007141d031421108424400604c1551113003012660083c405546641a114045a80000040d244a0400d561080b0302c14480c5000d482e0200426036030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 187511321 1250 187510071 187510073
    0x6030204110f0702090c0405060a08040201260105040c1107080d020d0918150b0f09040b060c1209010309150b09011a18120327040504110603041505010b07 68
    0x140908100c1d2000d031203001e424540c084501d400c8900c9407043c02480307003501d070000034605048a01610040c1601814884d1038088400019182d250309450690229030811f070280240c4031521450040164440d02d501c0c4184d02c0c2c01d003400042c2c08444003140c01c0c0907160019001d5010304004d2a0001c1c40072038024480300c00100c01c041e00b0400b40781410410840d003103100b4810800c03408035000005503088070000e0403030070a584002000f00c8540210511000000d41c4800143c0064040c1c41002804c036010070004000b04100402842000788442041d00300034070044c505d10540000d8404e0480606000c645c4151965906550140064080b812282e9419801c0b00908103080024003618856400341d036444548801041e0030f0084800142e403070048070580c2019503c03035441003402c041c210003c17291600901a00742c0c1050141d092007081200c2080e8081d11030b46080e026103170081744c112404c02050901c09003401887d500042058a4101c440c04000c0144145845854001c0132680189512186a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 187512571 1250 187511321 187511329
    0x203040e090d080103031d0a060c0b01090507080c0310030f0b0f2406090f0904060e0d0503102c01090b011803120503041b1202090717040b1315060302 66
    0x5030203800264406035511500c990810242030560350182405409410702c41f0341d1005001c0075007012504030078a00720001e042504196038039103d521500442c4c4090b81c0b20180e9600300c80080f210000081ca00c000495070804440c0d004580204010010405080e200d40742c2e40000324a221040300d000d1010820440c81d42070207050517402140c81c0030110070040c6205c45107503403010000e11651190318001002c89141c0e03079826a4514040004d4003903040c52410b814000c004001030380500401c2c1c02240600703c1418414400c8901c0303100d86140310200103081140100152010904864421116402d040d9000020f040420f00030440858007051403d80800010007102042508042314145403e040c4005999400c0810504600f0700d08207440c0e43d95820406850140409441b5214000c1003002c07402c03014011040d80d1490007a10140226100c0b03001c101c0320010070755001400c0c092208c01003000114518040303604004011141905004d15480712005034074082ea06519480d45c03500f040045041c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 187513821 1250 187512571 187512599
    0x9092a0f27030c04020a0908160311010810350a12020d051b03041703031006050421050f19120201050c18060d020a020c191202120106080a03020304 65
    0x40081400410082100441c2d43d902c5105000b138071880d0041001141c052043c0440001840014103c61510020341c12400e01061140001da562054500d0060500d500450741c15008031a8861409072951605604c0c00c0c88d285048034070707441401005925645100c0761480581d45041007000b902d00d015051821407661040303007900c01d095401600344140c0b05500301e401c3d998480d050180700c200e40a4101035442c154895034010103021001d603108589801000405580b141c00e0000c5003441c05034840740140d616010340e00c034508085241010140c400f0410b805485070072032283c012214400a41c035503e44c1810b41000b80751014003030188500051040e0628903004001c0c090001f080603050030008008203105800121050408184154105440c0e4108584400e05a41d50845d12440c1d0340100949070b907820090035118840c00054120590b400c1200d010844070410040002100140d0034003601801c01c0ca03c10465540c0d82000240020060040c075140a02c2030340a1035640f030500300855081c1c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 187515071 1250 187513821 187513867
    0x1d04030f0e100503190501300b0c030718050d08130504020c032a03070b131209081e1f060305060405010902150405010813020d060f020406031109092a0f 67
    0x107410003004010107050811101100100544a40c12390004000f030901c1c3c00030034a800034001941d500c1000003100381d20025602410196032817044c1c221824008000445035402040d030300c9400f00607241c0c0007d6000000380354072000354496614447d0707500700040403070700245003020f400c2d000090100c041002400f4203500f24082da07080b40c1403000c04803051543c1c80c09131180092199441c607001c990700100025541d9201544003500b0080b00340c03120001800f404203032161301c0e414482d071140011144110301910100d800d10348010aa00168131041802081e40603050324001076941c400400071079070500c0010710640c040c030700104895503039106201602d84031101c8814008e80601c0240605d03a8000c2e0381c0743c2c105655420400c001030181c0001040f42500d110020728071881d01c101d511101495401400445642e601c04019600403c10720b00b80c50b2203004a89948441c10b600004c0d00c0c0c410610100c200142440c4400480309200422081154014401034401a00124240d0010518043c00825607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 187516321 1250 187515071 187515121
    0x10030e190c09110c01090804061d13050604020c07120210170613020c0d030b010f03021804090809030304030302010207020f061602010e1c0c0e011d04030f0e100503 72
    0x305100341c640110448507806142502525044050481d01d81c0c80103550f8007a01100081040e090709281440381a84684600808654203442c0c0c00c80800c00a0340c4405500d8005e00610309646000399146c0c010100140503a5025909110511414600b080424040c1c0030b03140c00600da007451801081046d01c04103000004102a0404270300302038003121412502300c041907601a0310b45000403500c0c4041d000303c12a281951292082c8980d40c1d0303074960850800f0000a03256158102200032007103080c1c2c46107c161420815400c0348164107410154402d440c403a004000003400c00d851000043e0450b0302507402035006031740104107801545010107a82008840443e0f03c18900703840b0345000b13016191041c401070b0620020380b20740d02007034980c0c01c821800100c48080c0c000644600785070036600150b19005032411100c180d00040340c8988100c040075034111316070761403000d40c2e51260b038104d40401484100c4c40421200384040c0525485140c60010201d860703442d040e0b1030b460b08003400c10049600482d140340e0707 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 187517571 1250 187516321 187516363
    0x100b0c010e01060e010503030f34060509010b06070209060d060c0f020f03070c0e07030e01051006030f0b09040f03020f120307170606030c07020414010e040c0e0603151510030e 77
    0x1250340c002044032001f0509c0d19040d91101080d07000900b83d19001c4109610009810b112140c1c00c091940c585101d0318810072003000240c032410049400c94016540407500a0801c004100c050314241180d9a4040c070010b00b926106e0669680e03400689100121440225400711160f0710740070b07018455440f100c1e40c1c44004500740341a984408602c403a00b4454080111a40800b0485891080c3c00c0101400032600c024040750500d850003118000c040d208000010349850100d40500e00103019460702480000d0646031203851301e80f0703440400340319400100c0c19849400ba0f030480a120a00000c3c501000700208103442c1c1c541180003a0481c400c00410981c450410360410283d03680c0c4c981980d400c000300460b49500d451071480854010280d03002040b00945085000080360305440d0009842107220324007400d215a91680c00d01107092080c2e0703005505421884407175012803c400c05031681301540c00340c1011f021070400c0105407030006c840c00002c0007039102e061491441008101032500d0440045a03108 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 187518821 1250 187517571 187517579
    0x1602120a0b040305090301020d060e1b040f0308090d060905010b120a03020706080c040b040f1403150406020a05040e04030c050f0f0c040e0a05160906170d08100b0c010e01060e01 78
    0x1c854800800040c1800404207040010382c4007541500c00240103200c04110064403001d406100b00000c5408104801c2e50014410103404840140c40485020903041100e45095036210b9106400600302e90360400c4a40303c011000c00c100f4010580d0550184c0c000017080001c03e02801700280410301d80d0649a07114000b000000381c4c0c0004c80d08100c030014646409031351215510002c40384150b41c46460b2075900800c02140ba650780e604140d044588ca8251707080e021850b2000c2c1030320303410b60404d50301c0240441800a400310303003e5002010130321700310f141543c50187c941e018903191903401c3d20107a000441c8440e00d882000f03410403200c20403001040090400d0703034411610680d00e00000c6000e50140c1e494844046c10781c036041001e1038805620900340d60200701d1800d50459078410500c1107003019410b2000c00903580031040000000d0395140d902810180511080035902e0000c060071030740b84074100090025000c0f980c4000f0300b480c0c0c0910000400c1485005a2650075144650898206440103c0c0100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 187520071 1250 187518821 187518833
    0xb01050306100e0d030503060a1a120403090909050c03060c03060d230601170c010503040f03030e0a080a0e0405181c03021917070e09060f151602120a 66
    0x190748003a049441c00c59050b4050701c12129030703104103282500301824a568208160304400034520030041580da00c130010b0ba032809007440208200e80204400c840070088a60940f0813400610703409406807d0060300c042c1d541c01c604084940c0244196555040a59100c50070b2809204994100c1895190142181800d4001580034216603200426801d40c0503410040f02440b0795080c003510b210101070303e485e9039484518616490000c10000980d0140e03240d0445258000c00030b990060790400c2902207030031496a42034000b0400318840303604501c03aa1080d100014443c07002080c1109041e0354144520607210300303100c10713078070b01070540003903d4004055891203180020354200480e001d00c90700400d04541502c140c3c024410b40880f55054900d0704c07286103405400c4100c0c1310b44000800c080460300d035107002048801510f07855466500449400101d00c007494106000c8565800c014990740b100d080480030001c2d20344c850b464020049049039070b040e05521b041078944048621f050060000c8002640c0c0e00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 187521321 1250 187520071 187520077
    0x501050a0b0901030e0706020708060a020408060708180718060e0408071b090e03040501110c09060402130833040302280b04050a0b010b090a050d032a0606090b0105 72
    0x41d125180020510460a80c400d4000b006085041c0055804e00c50320380c2c40c025100c07000780c05041c0c901d200315404112080c0700c510850703003101c0c03524000d01615164101d0480ea00c038000751028880ca8040705440809840910034000105003400185115105a10340c83d01035a6940e40030030b2001600c0310410002c02c9640c0704560078182e00400c1d81064401c81460504100500e030040e1840615159190040b11000001441070f103109898801c07001d03030f0165942d641c40c8210142143c0140050012401e02d08013900500801002424020901500c50207080e1034841c1c0d0103843c4c500000b001c00690380d6543c1e280c2c2e000d440c0400d02c0d01d901a1900c0e0907100a07650703281800c4092400745070b508480b00c103100b903002c403034901540c01218204281400d0400340c0c2e507801111b40c07d942e0408640000600d02000008407800500301500c800121454202007114482c051202503050019001700303000124070f6a040030500c014000c2c4140c02d18a0726003031207070455880350000410a40380c44403614007a80c121080d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 187522571 1250 187521321 187521329
    0x90115020a02060a0c0506010308030603010b06040302100f11101e0c0f080903070f0f110f0a0501050c01110a0c11010f0518040603140309031506060304030f110a14010b040501050a 79
    0x2a2507552001104c00700c8600c044188003400501401002104001010004600a01c4100d0007405083c40d1182084818802c9100082d070105c1c101202c0c1c0c01160144141400d04044c2d0f042a200d48003e900b0001d081000745858921043d035101c405201d1446912542e46420308a8501004184903804000e040c0c54450200c48007401002000100c0c988402c104551015910002c402000340341854090505154003008a6020319102c03882006030506402620481c0d100900e550101071400c0e0054816511030180844a952180401c1001c445100004c04843c90a552070821131000d07400c0500c81980b084490604000d800d4801f0a031540e807020541c3e25076000921900f03035243c41900000d009083e1980300030f00a0b40202000c951603d0302001030424084294190f13507041e06880019a4102000c5a4140d84000e050000c200402e100f02c07050743d460b010310300b4035014207001022070728a0004000c40c11613141c000d5580b0405031100c01c1c020040203031400d03202407246506140019201e81c0c000c0c05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 187523821 1250 187522571 187522579
    0x11e200c0c13091103060408090d080403050a0503091806090103060b06120109200408060a2c06010f090207050a0602090a031505060f011d041e020309010605090115020a02 75
    0x140c50000c00001c0c01600301e006001460300058154042c2d01d50081c214649050328400c90030081c2e0421403c0c0410310900c1164402e8080703181102c00b00800c290440d0b04002516025410b01012000a60810201d0f090038080d00003992950384a03401c00c10b0000e0f8120307a841e6100220001d01400c2d44035211810b06680d80000041040265440031074050701441c1d142903031340c000880c0005480f80461f03001d03d140000980f085540d001002e08407001c284181e01c901482ca50050300007500899450380207200a14817030041d84030000403a5108020707241c40001814075a0000001041081c04005c003240c02000d45040c19802c200d61a12903a8a40c081c0d20406846143c00041485041e500c2502c0c0e5000345a00180c8602c0a80c1d951120030010101120190b0003811102c07049112980a0004004c40c001186104590321507000c080c08041e00120b4011100480008488075880019001030362041c241100000740c083e1401c030070800b09200603440100c241417241d03a86081141d0206130203540d030307805407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 187525071 1250 187523821 187523827
    0x9020433090b0a030912091503060e01090905030903060924010b0919050607050309090a140a090305070b041b0f05010f1805120a060c0311090d051509011e20 69
    0x3d441a8090320282d100180210340e100c942007810394000002c4000d45800b801d00507405410200140d080300d40d28090b01c6940b4007520300400c1425852781080300720601c02e00c156400d02d620400824500364040c1d5861050b90410340ca010b1100811602d000900550410b070300c1c150303500d4825a0300c09403042c82030340d03800780100d400440744401c880f1061800800d00a09102d0742d03080907003440c130345a13001000703403038800c0802101080d51413141c1e00a2608124a40c0f104e82c00707035168410188014120000c00f00c0a000d020300540010594a05aa5118074041c0d0350342602201059242c030222103d40e00b1007044640621418802640e008a43c40700840b21814001c4c2c0c507200304482c803051b08461f603000541c4241d001400901d0a0b501041c800f080c584502014440c084401c2c40503410b0f5100c1c141c0b5001e448506002c0c07034050b450641e840002c2940507038180c826911001c585e40100013012070311981c807603458100400107090b400d0309000101e20384d49030170000c1c04803034840302d03c1d115450700c10907003450404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 187526321 1250 187525071 187525087
    0xc010c02090a140910050f01060f0f02010e0102030103062f03150102121b0f010606140711181e0f0a090503160c0f06050a0c06021309020433090b 64
    0x143e200400f6034010401c03103055460f0843c141a5200200540c80c007000b0300741404a03040c10048800103050311195210b40e080c07020303100400c6413040250141351003103640b10303c2c42a407500d400b0320040d0702940c05994049010072614030ba45c0d550340300c20b0100e8804210304a00c42c0030607005810a50b50010003000100d0801016040100d1030703d4081450410307908000181c07400c14151018840540100c0d002c19220000310000d03282e8200e5110344154070204800d25100482022034000802c1924032444d0500c551603034003400b00c3c18001c02d149003400c4c441e00800600044481540001161404485880326680707880c0a0007803009001610000f10b6544a06080b000c0000c20302c140c800c40d01404030b8403901c01c551801c0060a1410b14401d50900c00c0c2545004100c1c9031041084400130307411501d41000702c005995484000307501004c1d00e01c3ca030944030382001c910110140014401020a621103081000f4000c8407002412562000f1603040101000200c40060308230b2103820407a00840d14441e196048 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 187527571 1250 187526321 187526341
    0x601030213080f030a09060c0c290c0709110708070f0c030f06020403030905090c030f0c0f0a03020c07090513060c051201060315050405091b04060806010f030b06030c010c0209 77
    0x602d4020603803500a9402940c4503510001c054081141190307111203000340c2d280003d031580d0250318400341c5041e607244010320011610040100f14044c0f680a00e01d1031050300d00c40301105d90081100290b00745c00003201041603c000c0d000d4548480d514460042c036100c103d548a50542c803070820018107140c00780d10b004041c441c110203074100464000c0810100f421b50303858040c0080d1700c40e0000300e0108404100100e031504028548921400c2e04039001c43c0745131200145074100440060480f000804104200c403c0c0000000152075000443c0e240943ca5a5000070f03000d00705240e44e0840c5c09280e10f88002c1007900c21501401030030258010764006152807019400f01c45500c80e56031403500219540f80009a00d5038550300c1023400806101c40005005d441e40300700401d8890a5802d00601d078499030301c4c0c3d0324500c1c040501c3ca400c10320040000440d1030742d034204242440000d900c00c10480450440410901140d440c400354402012005058182c2080740060901181210068000d8a58600080c01f00c42 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 187528821 1250 187527571 187527607
    0xb0303040f0e010807150e010e041512210212070c050a0b03061c0201020c1009120809150f0f090d060e0303060102100911060a051306020c0a0602031206010302 70
    0xc1c114001a400c0c5440e64078154a075902032280401d81d01c61940000380d4031100c40e00aa5a0b140541c2d240300e03035043c0c1040119000c940300500503500c030351b441c04001e219190078981000203160010000c41802c0250030400740000f14500d10348518590405185c0505a01042030f125010717165510b00d85034021030034071546013811130b0011500001854000726a0b0aa03240296200f007204941042e410410f00c10304600c00c419007100240540d10820010070b2a01d4000388a5406c080b451130155489565606403182e0f280b5001d0301a906107030b00141c03011183c00c114456000c54480c0c002000c0c035140040c40c00310080e20a55901d08110032000c034441119030b6401d500400b80300d03040b403000c1c000c5d1602ea91343d494980e4020360381c160141c818980342c200c0e0341100d80114040141c002a5920001c20848203200b0a9407042d50000100031081010502e03e2030b10700c04210244c1101d07801020030324000010701504040790b40041040d0f50091102102c040c0c88442029805603003840c0c090303118016101c02c1110700e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 187530071 1250 187528821 187528829
    0x3030601180e0a0f06140a0b030702010b041103091204080a060c030b120f06060d020603011403120c0607080622090c05030d0806180402010c0308091501060c0201031d0a060b030304 79
    0xc000c40051000c2c01d105138101c5041c01d480e0341c0b0304220071a40c0e0038040d94440c60700076010b034004003600010804100640c0180d64007100900005c14001140310001d400c544241040700c0c000351001c003c2c40044203003000001c1c1040394a02c101031030329007440ca2042d030740c40754090000c050a40742c001c1c0c0c0f041688070340c020010341c8201034000e4058a502c0740c00f580d1284580c52360f003036482c42400c00103045860b150596800e4940c01801061669017070000482031111004031107501486103294510000c0e00310700040024440d201c0c054201c90909820051182d48c1c0a0b22461041007a0580c1242e114a14a0b00a8480c010000c0024018200d807400e16813502d0250b0101c6c2e814010b560040c4407080d000050a4481d410854030740c0c07103811507500800107041040d01d029000405032003100300000d014507005038020304840100c91142038070041c205071600090700305800244800082204558050165601e1b0030511044800035a80c0c22000300e44e504400700c400f42546480f0204840291010300864010b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 187531321 1250 187530071 187530089
    0x4030c08120f0702010209210c190905010605030f010527070201150909050a02010f09030204091514040b07050901120e011508032b1811031902030303060118 69
    0x1070384607205050440d401c00c0320080340021210700064500303441803007217910020005152a0b48041c000c1c40c044008540403900001c54400c2401d64011a9a201d8511610700e00e0f0480c155141401c24a103041500d00c1a880803080c80802d20511400c41c10600025040d00d8003a82c490070b06461040c028038803611110b1941181c060384030140424154190001c2e84015584031940d00c2c4985d44070008804c641c3d8402002d4003e0700702411140040d8450030040750541d00e507260800e04c03152245c000504445a000b41152100ca9000d650310b1000f190f0300445002d02c0000c2c00210f20b9180c5600c9101c548440140304808200c0c2c009110685a130003070030a03491400300c84104005112489681d180244111000a026001c003031900041d400780020807102c0118100c04074031600f00c103507101d031104a03070300c480c409440903120000001c280d040d17040e0324942c15008820b80c02c01501c0b590141824600144d00004400e0030540d407240242c2c800204072030f040b80c028a861004a00b91803c0d00c500c0402c550058444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 187532571 1250 187531321 187531327
    0x30d05040308070e011704081308100204051003090b2d04260403030e0108040f060c17150d0b04060617030703020d050a0c0f060213090e16081504030c08 67
    0x41c154840c6555210341850344a009074218a5001518076070301c1700c00c20b02d048055520024001988003000340480c0c108106a00050b251102016030900060f1551004196070200c0c01708190700e0300400c41c004424140c20200201d081c2d0f07071960440c46d040100025481010034404220f82d80803100c80140403004001140206d041528007448115050b191480422a04251010040044004079412030f41d240e21000401a0840015038516100400945000030000469004200203000d06d0070003c45542c0c0740302202003171866200a242c00039000c0012042001300c40000c41e00d4466158104540040b07142c00c4607566807409001422017038200100e070003540f4940c1c0320b5251700000a81880340c031075003d4480c0ca014240044801c0e014245140c400a8428903a441c04589096102d01d45c0d103014040244c079120b1005c01541c05040d0300d0740481502c1b40e80e101c07244000304007448010341c004500b041102042c0e19140d41140d0741c0c080350701c500c1008200d4001103001c15000741c2928000541c071204003a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 187533821 1250 187532571 187532573
    0x1090f08010603020a06020102030903040915231509010207031515080604050613020a050d020312040f091103010f06140c0a080a020105061005031308040819031101060b1803030d0504 80
    0x1000e80b006100c00c900030021940041841801802aa842001d102c401141000c0c0b070b200082000d407005964052204000e00e40200742c0a017451140030628104602c400841c5900303905001807804014600c00d51240240709a0030103a81c0840c490701165008001d088501120304a00001000d50215002d03201030700d810f0004044401085080c0f045001d0700c00d80d1000e60394400140748111032004020342c00b20360144107011a2410003008042d890000d001c03204080003201320b1140a0b402034000e031154001c00c82003000000d906006480302000645802421945407503d1b90700202480e019003002e210350f8160440b020401041503c1200841d4401c0b910901954180030b15550f0120072010015400d240004125060201544590b02090790301c040c0345603244038a504030360072104401c890380c4d10100800208148100001c10040500c9000074528001c1d903d4003402c1001c0822019503542d0518030100120048071050790f0442c9441003511b50003101c400300003400d6125045410120301c1c50441840 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 187535071 1250 187533821 187533823
    0x80c032710050402011709070504020a1e09051306150c1a040602040509090a0f110604030212060f01060801080703030f031428090b0a0b04060f08100c0e060a0e01090f08 74
    0x10f02031030003a00c44080208155103001c9068030301302da0842d2647c0c4168810041d90406900038492040c041c82c0890300075160750250941000000092000507143d400300784490304e40310000b000401010801082018a0003850f44603041e44c3c071020310180142058244280070401c89060542180d02100122610b05031411000a4205000d00c5004420b003600140f40300d24002156000c2503001f003825074056066030380d29981d000b02d030380d902d94001106100000041c0c8907003c90125241240000d883c00d440e00e00c40c1c0700d4401c0d405034814070803c00c820004220b400c078042080c005a94051420044035013003030000358060405121480c05a040000810540e07134901d81500e101d240981c540350300f00000101203141a04c03040c0d13030043c040880b0107010410b44c00c2d40e58882c1c150044041d20101e4441e64070720b071002090007540c0c4041501e410130181640050b0b101e11641400807080c1c2002c160325061000070411a0280c1c400501c113200642582161030786c0112200350040048408601a503501c8501071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 187536321 1250 187535071 187535081
    0xc0d0f060b0f220f09030203070f02040617010b030c01050406080c09010201151e0603150e18030a050c06010f060504060503090111030a0e01060b0a05090d111c03080601080c032710 79
    0x5040c105182403003840c0f08130010b0041002240d0107500650034030040380c0301c40601c2c08207004100d80c090364484000860702501024220000c000740000211205a03005250910320600798243c10004104810301809401140d12604080d03124071164a4410610050740102080c0d2403516550600480001e1040e0b21303492030311603035190002c9503100d49646540a60566080001c4001e078491100340a10001d42607030005544a900d41c5c1c8401e02002807400310a06650140c0b05000014000186400105074204001d0303004101d400b508402e050b04e405401400d6010328003422081280c000049034142100350058004058502031140d540d06010f608100140812620303c08503500340382c000620941c7c00030686002c0c1800c0c0c1c64403803a06000100b000780800300800d04544400142c52794409603202e05404110f00c2a1409415540444605014100e072000621440c1000352040070050384007070b1307c820350b600854030b0441041c61100c040d0b0b154200480b201040c1030b942c419184103800b820802c3c3c100f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 187537571 1250 187536321 187536379
    0xf13050a0f0213140a020c01150e1b0f0313020102030c0d1107081c0e0a090908030f13150c2a0c0e0c04121e0b01080c0d0f060b0f 57
    0x50380384070300c00d590900c0060761130f0110308480e120030010014080b40c00726001862103410240000400c120129405011402250004282e105a000800400c11442d2407001e0104039004200e0781004c24001c0c000b10316100c0104007400e02000300c070040b030440e402041980e20107502003040e1049600410740c0101101d1250804d450b0310f02c0707140ca0000c5c00701404103141100b441c02c21000f00019400a00c00d40322041d01c82c0d04035400c044100000207111400e0b00c124003a0b18070803100d041c1d49040c403004e4070362081c2001e8054407481904c48485000076020b9201d505079480d00d100007040701c91007542c1c1502c01c80b2041d4201c19042d0b8030b001c0110042c8400d4140c60848a00c181c113071540d16521040740181450048410348404002000284040e0320760b100d1039032485104218051081e5000c640e107185d105540c2d502240c210010700010f008502e010311008110150503105858150800e40b2210350802900c1e00140c2840d80e41d07000217440b501c4048103d41c04500282c81102515a02180f03c441030604081c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 187538821 1250 187537571 187537579
    0x17121b01050a0509010c030c1e0507080a03020306130203160c05030c01020c062202011215050604030f02040f0b060904020c0708031b01050708060625061a0411030c030f13050a0f02 79
    0x10307900306000d00034820036040031540c1da684041c00c80400427401c3d00304a034403e41d1051100900c400d90001e245032006204c0102581da01503100c0c28080c06015285500d030544100541c014030030411150115601004040030b1854a52400302a82c2046400c0d032013210328154440d400050072984000d0001102800340c07622803400442c0a031840b010408903404a04000c0c0014190b140601801899411201c0c07070781400c10700186480d82d038000284252b0700550040b40c241c031424010030294a884d100b400104080d00701c06104080d0070400080041c0304a8015038804c40d0b02203581d0441e094200111000703456101c040340c0e6a0b150083d03c2954104c1c0078940c5240369070a201c001091144141c044034092a405043c8600300300b4031003030312a81900c00b08284408020420810004107155000302c190205281500c1c5062904140c2840152001d400800c051101c0c20001e2010400c1086c04699010402180100c0305c2c0c2c54460a51030a0b01c400b1070050220b104200c040e506005510804d04000c9108031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 187540071 1250 187538821 187538831
    0x91505153313060c03020f0714030d1805060c0106030c0e040512041505031e160207090e1509030706050108030421030c0b090f0a0503030106030617121b01050a050901 73
    0x107140c030303845104100c440310b0240c8640000300841d501418403185001c2c03082c010768401110070039155240040b59071283c070350100c9800084845050500484200f03808500e0442e50310143c1c04040d03403401c001c9203d0940904000104409601c20a602a00143da402080748074007035a90755950742d103101c064605940700e00908032515150300b1108100e4040b540e455880c2d00c810b400300f010507161600014411091034014140300280c3c2402c90f030f43c00f840340520390501c10b40c68484610081c5040200d0b0402d1400c1d51800c521450b01100004400c1541c4406200c1d84a85941d08210281035001c0c6000041030350781000c0000c2590704001c005001525804105020080710010300c260040c1c1d5891406008112140520310114000107209940032078150102c6036840801203c0b20700d0045039120a650030382011005101c1183c0c036000311070042240004080055048503007240d10303401002000c8891541c0082d40c170074201c030844808041142000020841032608807100000352400701c0740042e665181c5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 187541321 1250 187540071 187540159
    0x1181a041d0108070e040c030204090317100501090306020d140703200a120b1210020702040b0909100e070b04080f1e0c010804020d0209010f1809150515 67
    0x81c101c12030482c0c10603402040514605175100e401444090015140510700780004000742c0ca40c1e025042c6030318030a641305403541031101da1003480544051701c1c19100482140040145a030711a10385070640f41c015200503038401a50b180e40e8001c00d080c1442d24400d042c100100414240c0607031061001c0d800440d00d4002e1200d031100380000034882c80e070300303d00400c1200f4079490010b013156018190322600900404450021100000c0c50301480d0110580610b80000e180d000318142070062088900d0151910b440c030b403c2020b000c54030346451030366121002d5a80d4080c0c01b440803003001250010f1005036140d43c1d49580b40e41180c2c3c2c4a000104660020748102d8110007001d50204d004600f400640d80f01502440c5410401113031079110290080c3d80c84040e6400007000f59648420040c003c00300c166032400400c0c03410032242c5c029482000c0300640b5030300d0001050085032100382c1d4403d5803103090800050f1503668210f240c0c4820007c1d0704894108522030403680c201503c003c80b0b052803240c1078512210500e11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 187542571 1250 187541321 187541369
    0x50f0109050106080c03180a020312070c050307050105091c081c0e070501020d05070f14030318060c160f2a1e0605090109150305040611160201181a04 66
    0x17500d54203c0394000700700007158200c10006418072001840d00390b900240c040d0b00064500a400345456415480001d00e02c420020318100207001420190013a06440707252400207061809a0174010340660f1143d40e0f51058501c20821640805501010091700d41a02d201c80f20041e0541d8000e01e10b600b4688800415030340400500310342100d2050740103250001602c6401c490980041400305d6001c0e00c5c5a0344540010140825600481021307001140c80b8074040001c0800d8454042d000c50503600000309000d928040c8008540500085062038a5100c0d49460091200d039042c00700541503c0e0400041d40051000310f5041103140100341c10481041e81300c544521454036503410800c881d00c034840302007065900442c0907000c00c0e001410030b0391903103030b0701c10b6208480c8030b0103c2e0800c0042e03525070801003001600c1c41686050f0304010080c0d0305094070202e00a00d030300312036103019042c41045447d0107890201c4d446000c0142840c3c41100b1009103145641000c980c001f801003140035480105d101d159816 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 187543821 1250 187542571 187542587
    0x6040309080a0f12020f010908070506011211091312020d02010506032d12070602090118152708060402030c0312040608150604060e09010504050c0f0d060306050f0109050106 76
    0x7070050098001200f01c2d643d0440900f08100c2e00d0810745c0140c00840601d00d40a01c0340344141c42c02a0100d40d0b4a0b481841c0031030a20905800a4020384403440301c170004200303c1e9008a0010100381c442030495194000c801865050940300100040c4510010740e51552380880c0c1d202044909800030300143d2075a000b010b0301d400340802c0076941d603070006540b80302c081580421910210502d0065400e10b004201d02d50f0401d038002d900c00d6450a80010b03518180c0d5a2055004c140443c100003940466424000c070308804d0381501c1242c50412646412030404100a04403e007000b0000c80c010340c0c59265511081a150081218217038824084c2120a504c2803c0200e04009803d1882c180985000d08007041074810384000381c021030081c0100c55203002583c640c40014800b81803103898258820802c2002c020002da4144c01450083e42860280305021801000b694540071000184a446084951540c0010400c1d07a102820440c00c04040c00b542d04062761100d8180e0701440b030140300c2a82c0361b1500340e414031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 187545071 1250 187543821 187543823
    0x605120601030b010c03030b0f1c1b030c290c01090201020c0402030f010314031201090506030f0f03030a020d1104030606080607050705072d0905060a05010905030c010e120a0506040309080a 83
    0x40d4241c01c207107000030701c00c4c0d20003c0c031100020b00c800009180321000c9810351010341505000c002c12b0140740c40500c0760503011018180ea08030420070040d421070b503619940c5c148030b00c200140504003c0d40000a9003d002c4000004194224002e40310851183c0803801f916030441c0a0340580900400107219041c54002c0340e2245084240c00e42c4580d20b56038071a0380b125611114025180000d1022a07800480140380c58000c101200b000b20380c071309002d01050f0500140c051040b0940e0310011602d0751420020083c1d0f6448624404016194003040a00c407004d0600050400c8c1c4a00000501004003c2c2c0d552200c5c050301c5041e811100706540c0e000090b180743c860040054400d90118804001e0a4600d11803e80c901d40c284038402e0712480a507244440444954100010070340e210002c00203a03040912050004082c02d02e85642c0c618030b480d010030b8a4036042c3c11014100030030071100d082c40e43c640c0411040c8441c0698225008190719080954a910302918100d00280603600002015100014420092 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 187546321 1250 187545071 187545077
    0x6061409133824030607050a090306180302010506010507080304060f1d010605131505040c0c0203150a061d0711010f0e03040e0912040311010c020a0605120601030b01 73
    0x30709207484222202c16091078400c0c079101c0341c07426900c2d0740044840e8180a050550070181c010b09110a50f410107120740403685000300c2c041c480345140c684c1e002030360340c1d0440c00b1414055920301e01c07004c04850403452074102800c114200804030007a8810050441f0086001e40e00030040c035220315004503030350721030514080d1006205002041c00710f002c9174050010072001d44000101d040490b40c0074103d02c0f03202007010000d030f5981c0504201d1402c08503082c0f00b580049203030030081c0c031503099400b60540c40e490052034010360b034944094400d10b02600415800640050450345111040c02a25a0750b80c0110f885c0c0302401d051210000c4d86000082c00070a541d481185444400d43c0c0d040070032103800c0d1911481d001d0664a031007008280c208a44521401504054081d69803a41892407250700c400000d001411281c3c0121607058400d9100c905075015644d0205840c206134210a00407907c2d1541004040d500070586103000a241d034108009080c03c1002c60302d581c46954400b001582180d070ba1410351804 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 187547571 1250 187546321 187546351
    0x4140a02012c0909100b0906100809190b10090603030c1b0320031501080a03080a020d0f020702030115050f0f04060902030703020702031c0c02010809010b030a06061409 74
    0x521100540450101d0a4088800d128030b64280c0c00a84060010395200320142c0101c40121015100d0317001d401c3d40103e09407028455420b00781c001c280f507007030310700d0082040140300404104110410f00100c00846c00d22185445180d04a0030050304100e002e807458001032103070000020b4000e80d9801100200c036019141d01c41c10240580304c1d50001c421550201547c81c1e100e1101000040d10798404040c98400c0701c4442c01400055810b043c40c0c07071407100c5590100015100104000c00000400011030381e80f525060486440b001c5082000c0e00400800190450820200c0703074441106d0b9014240c0b26001b03c000b48444035500c00390340050381d694041c45130019601c00012407641000c00c029410304202900010751a0340d00c89031102260025600300f000207030002030200c00d52808102c03d1140740601950481c2a160032440904025100d040082c10700180d2000680748100a600c204103152010f41501c0b11070b00c03689451001042c0c14018621103820440d958041c60608440c0e81c0d108403540031903818 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 187548821 1250 187547571 187547597
    0x1704020108010b160510020a091d0105121903032711010e06040308160c1a070f08070b0906090106090b03031e130e06030d0503162703030804140a0201 66
    0x241913000310400180201c04101c0360740000c400308035104a03040440001602d440c0710784002400c400a03503120410006140054030840d0510011b51070446508940e039003000c0f480c6468860910591529510341d0b1140381044906040d0540c0048009064000d8044030100c2c14110003d052038a5007400b0b40000000302146041394001c04202c401c03441e00410b96400e2507640d6a80700d04603400b405070103080780342d242e58000410041911b450003400c060100081c43c0d400e2110a844c19004120010740010b01201026042c0803054003150840d9402c5150381d1560725102c11600e60b9045c0955580ca110f40c64020001000070441c45503000c1010700401a52030325401d1031f481c200c142a4000c40302d110480420048284110b801a401c0044c41040c0c0f9203403c41c03a25504041c10000c0d8004040c05100c010020044110000d1002c08a16413041c200061403410381075500d141300000b001440c282c11000003000c01850740040c440d520035031251182a030310901411007943c4500303240c0d900038081840481564 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 187550071 1250 187548821 187548839
    0x1506030b06012d090801020c0120210a090b0103081e03010609060e18090d02100501050a03150f020301060509040b0307030b0c03091c1d030705010819200a170402010801 74
    0x81c110041500c1e0904c8010b498000050880c2e0041c001034a8030782d5140940130328030320008040342d018115040000d082052141d1151800000e40c54000144400d2000144503680d040d07003d003282e1034220011510f150303101e1030501100c0c0e000005140401d0b20440280c4c4200c643c080440381a20300a69a00305420b00d01f0409841c1c2d0001100e41c907034029007581c1d08201c0d0340541403015101c0c988840040a401510a101a003068110403220316501e0400005002940f6102446411241d000c1a5858443d00342050000180f8814020150003800000006180e5a104014003060601294200401450141010f5617001c80f40b100500003180100000e464183c26400385510908103010760321161140418018401c4042c0b1484000c42d10115004903185205ca10205400c0000d41c010881e0a0521001178101000102607581d041003080599a51f50302c203420186540d01036141090303040c6a03400e80c40455400c5541d15000040070940c140c4c8174044da0444450103140c060b1250000f0344d003010004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 187551321 1250 187550071 187550147
    0x605100f03020c03070c061106040515130512090a0801090c1214010e030a110d2003090a120203011401030f0b0604180506010306050c0703090b090103091506030b0601 73
    0x1010034190300f400080c0c3c1c4200140000d08240b8852100d00f50b0f2242445400341450004021084140d03101c1800c100001e0307070025a558034160ba07d4406500b0742e403500551100c048821000074954012803105041c28810740000d8a248030044400c544070341e40f605200f500705c8036102d40c0909540205401017020b107840080c9280c150340a81c40d107100c00381480100500792050200070b003181d0b82c8002582001594098007190150007203002500c02801040b90041456081041d1001140015824078000075070030412a00070719005031280c000300365140120b14206101c1c240c280d0080d4200300101015108000d04039050344d40c42039100c0305d4081300b41c5501041c0b4034010802500035580344800d02010b542d440c40340c45503e2050b00140840d40c107518040c01034034005800c207081d5103400d000b540000b07034020101c0410348180d4200715480b580c114004a01600c12140083d18660280303c6000301d007111600710009803401200d644c400c0d5220303c1d004549040d8040c0f54035801c3c24100d4410100381e4000d0b844 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 187552571 1250 187551321 187551347
    0x310090204150e010315021207201608011a06040e0a0209041a0f0301152c07120e030306011403090c0907090f0e0403080c1c1805010f060510 62
    0x700040c41580100d8540c007000341500490b1030b040c600401001000341c14540400107102c80c038010360a200305c2e0b221030444088068090810306c045214000d40703040c005110098151051011250b8904c02083c80b80b222000c0c6000d1011503500b031103980715084482089420004030003400046c941440c1c0b03a6414054071028010103441a004c0044000c1035655000c0d100c0009a40141c5040c1006100c041102164414194038040c0c3d0400310302812030341d0160340641c22659036440880c07840100701201c066811681440c02c1c01306400c207003071150150341300c9021400640741d110204290701c2581d103511399901080b90f50a0020301c8104104400c0c41102000d0740d0801d1041040b100d4403259000001c80c0785004840b008009014400101711038801980c0b07e00003000740900c0b201d4a8149920014a1042c00038080280144000344201009140701c1140c8126401007204108021002c086a001c3c1d00b00400141d03501d608040000c166080c1c28802c2c441201d00050082081d00d0381e0807826182007215943d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 187553821 1250 187552571 187552579
    0x6071809050406050601180b0a030e01060302090f0103150515060702011107030b09070902160209060118091d0105060a0509220c08150c0a03090807061505040b040b03100902 76
    0x4400258150355008150041e0b20480f00400d60f0302d403071400100f8681c4614021204480c2d02141001005114000c441d0b103804a40b80103c2c12080c070b86001405001a41e00c029007100d0304004100f9542da414205c42d0513a8480c0c00134904034441081c0c80c4080d24000d6940704281e101d00f5081c04e13000e01d0508010a010351042c10b0a182c0c00d030070314607518100401d0364420341c0e8030b0304800c00700001c140041c0302c0c16003d40305041e011803c0070006400e42090003458400240104070130343c0460340a1b03000b507032141c402000d03c80c1d62606072030301e80c06108050010384103540f4006119280c40c4d00c07100f0060003114132514020f0703d11900507140800b040b607800c80181c850017080004408080d20351000b507512502540c01500a41271451400b805503143c000d03201c8900c59079880e820f003484070013100c4c5001c44400510f280360200e2040d4040c02e20440038801c8070f4000742014034000c2686494110302c00044220340044500b00600718006c000e12041e00d1181d140ea41d80747d0010011b0100c108180c1e0710007000c42c0c1c000740c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 187555071 1250 187553821 187553867
    0x6070804030c1a0103050705040204320303040b09010f0807020a020409080910021b06040e010e04030207090903030b09010e011a031f030b09060606120606070525080601170607 77
    0x520380d6030100360821010103050f03403420300500921170100400001807606480851916203010885c00d01c4102481c021041551011100d0f41e504001c2481030608080080c1500e54840d5030b8141d00066a025084460100300842c110400050040300114400c1c0a26000b500c100c9010780d08000c001d0543c520111440c100c14000c4103640d0300c503500003e02904c8950001c0030900d1180a180b80740c00c44031040c441c45044108000d01c04440310784401811100d02c0858204c158a84c1d140603130510400b1f03000300d54450310300505031040c564150410200d40d0301c10740c1c21070046d0343c031040c10118811090081c41030709030006d80313214004076105006544c000c40304036040f42114001c9529000c0300c5041d074404e0340c291746081b0074850b0401084c41003540109080f1002032030858040c01014a0f680c00400c201e12604001c1001420f015040c00f490300e014030186810601002407501e01032a41c2d281d07016000e254428880080b9075242040d40007018500340d04001c00c0b2941c2c608008695514204500d014491500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 187556321 1250 187555071 187555073
    0x3120301050616061e2a180905040c05040513080906210a0e07081c0309060f0f02031b03040503120606070f030e090601030b010c290f0604050f0906070804030c 70
    0x620452441703145074690f5070144040485400d040d0f4440e111010b0780c80c0c2242c200d00d80e02c8511101d00910076911814005140c0011942c03800d0300403440c2d800030301410300340000c00c030802c4400401031095070012a4200003503144e000440002602e400c600410350326007001410007902d00003004d8505a02c0413120408401d51140d40b02c011b080041d1518614503480e060540b400d00014854403002d080d03d80000d140301b000000b15034100c0c4102440140030305543e0b07110a4244101508004105041080306001c449054a0900003d51084501c1d40300c0946071081c008416100104503406150008019400e10064110075018084007501203984001d0400103903000841e1814080c001a00a880c1c01181c46080020300580802c000c04042c10145007801d400c0c0160f8211569140198000304943c0100c180d003005040500c80407815240801c0c0c42c2020042031090b0318440320b20444040d60240b02548800000e010b80880c143d0342154260131442c002180709200d440744946c014028581900785101d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 187557571 1250 187556321 187556333
    0x60504091b0e09360d0c050607080c0c0604050a020f0a03020d080c010b0d0b0610090e0a0c1211031b0f0403030e01020c040905062a16020609030715090503120301050616 74
    0x100300012a0501000c0c851350040c180140151200d110050910150016103950383c0e03500d52800030029000c3c04480f01c041a042c503562400c0d910352511000841e40300b82080c1c00c20965139017442d1401c900c42c1c0840400c4036580d003001007881003203036400350844a0410555444610580000c0481505503607190205c00190340c275540741c83ca03203c0c099100005a420008240400421128048014065190340400c589600310081591008642d1000910490b0b0401c00301c441c0c0c544007000d040400e00300310481d040700b0494001140249070307081d14030b140c80810702c1915016020b44800c6104400c0d05003c104007081c06100301d0421003070144107845114040c940058203e8811040a42d1103074880020881c290780b00268582441a0500c0c04405030f0113100008445841440210024140c210071020304544600d403c1d101441402400e0b00d450310313200c170320000b012189429080001800d0540c0050541000715a03219003102c4030407007d01d135070700304024800254400c1160724000c0025501c51004101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 187558821 1250 187557571 187557631
    0x6230f030312040b06100c0303020c1501091a030105070f0809011e091a060a1406070602041d1e15010c0f05010516020313030f08070507060504091b0e09 67
    0x24030020345001c1c01d113420090501e120080c905030140003501441400c0c9170f0080410b200c1a0b034036150150392810035070442402e00000200300c04051040b24000700315008107400c00400d100803840580d00020b403010800d401e840b41500c8140104086c00d401c40101440350403695441000500041004a1191110b10515074480038a042d00c0c0d1366864008204035200e40308542c05c2e540303914107150b24144600000c0180d00c0d18844c0e102c034200440050021504c541096507000d5400a10454503a507403042840c140c2c400540c1f00c55802c00004002400352200b100c014440c10130f07000840140340c2d807500d0326281d0030074150509605000d0b1900410b40010306003000c1e8031000303111340e0000c120ba041040148208000a400110039504140502c070584100c0100704401c580d0400f0b0118000350490510340b4152050f0a0301600340d029185000c070740940c010b001482180c480540030448082085c1005114140031107a00b000228015002078039440d100901a0300001d241d4003182c01118590107441c0040c2c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 187560071 1250 187558821 187558837
    0x40917070c030201030c0302120f090118050309030613080f030601030f0e011506031a0d08071506140d0305030f09030d1401031415010902030a14010303020a050607020106230f0303 79
    0x1440c41e03806004659041c054074100c1085414190300300008031510781c11082c40248094402024800007421068007500041860b280e40e0003d080b9204241c180703030752250b10012000d0f00a1140b0b41c0070a03606d00c140c0340400b003d1a0404442c42c1030240e040c8844260354009010141050f40703c20701d40c07070400824032525040000c9600002044031070342004c00b180d10715990020062600e400c1e112802d4480150260003004800c407004401c1c60110300e040a80b50203140d40182095603c4441c0c20381000569101400783c1e41c584207011100403546040004c8280d03040c03c0100020402d00c0818814100708401c960040d10840036207007094030411f828003c4403180514450b43e819204010021f216007042100034001c800b20180c916000100b205503e1030388103110320304480e0b5002001911109060380a4001d140840310401c0d030303e595a0030300075034030550802c041c1c60500804c400300b02140c1c01441100203e40740380c042026848200340d01d0700556404411015040a1800710204041c0e0701800249032039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 187561321 1250 187560071 187560083
    0xc03120807080a05091009020a0b0c0706030621060b01091a04050a080109020904120e04050a020711180c0901020f030c07210b0f060f041109010314010e0604091707 72
    0x52600301c0d0000d01c0b140000e000c000f6140e1a120520981c01d1002c07178142d4541c408a0b401241c42035003440401c495500940c8143d850090100c2c100b809400003080da01c0803180580c1d014441c40c0c0d00c1d00c4007103290048002100c00040415245100050016040901c90590504102d801e01d40e541c01504a0030b81036140e05101035400013800d01c0701e841d2501c21200580100380003005035201941c00b01d040902c01600180002d080100d000d010300d40701c0c1a1020141c2d901401c103005a0615909400194014010841d49484003000d00354007800c014030110309001d1000c1e42545642c990809915a56004c00c690070b0450040451400e9040d100704010030701c03580c1c00300091083c3c40ca8111020411204030004620703640d991000000413940480c50b40345c0090301c03c00b01400d281ca844000500c5000c00d80c0c00583c003d0700b4130481845030343d072180c060509083c0a0700c1c1804034207210464001240824000d0203030341c950000100c2d0b854281039002e1f91401d40b04800c204030b10b652404030003c40d900700d00d00c110740c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 187562571 1250 187561321 187561337
    0x1003020408011103090304030803060a0b040603050a0b010507020d02040c02010e070f030b0907030c06080601050c0d080417040e4201020715080402010c05420118090c0312 75
    0x1d8603424400d5120900d045182c60303042d4203002c26220344900c1284409880080d01001103201a0795529901000306048040300b5543e664941c800360203060304680c200e40d8185020a002810350242c011101943d600400102c00000c0035400c201c01403210000200071596145044011188100102005003e51403007184000c1d185141c03403250110000c02c85140d503040b4210810026951107020429100b042c00c24060568030200122468040c118903280140f00b800c204844a80d0800b40d4680182e000d124017510400d009103414549100394460801000175107400103c95503c10607000917002c00440020b33010054581d5106000d10340c01d880c860074220600090078041d03804200b440c004200326038401400c1079910380064001c00008002a0621241c0c0c06440c1c200139041c0143d001000382d12072100d0414100440b400b0407402218100340604520142e00208086c00750b80b000c0c1240c403125203510b510030a09121002400408004580c00d41c0400340c04000959440074060300311010fa038a20a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 187563821 1250 187562571 187562579
    0x909050a0b07050f030112081608030907060207050f040f020f0309030a081e180a050102040909020406051203032d01060c0b0a0605060306040c020708101b02070e131110030204 77
    0x1d5018007900510902c442000b480c0c416400d0002500d0440380301c020100340c0d1003c9410300300898411100f40d2907450703001c0038014040052640c065800f07015a00121030126885140a82e030b50f0900b406100d030b0000d981081041d542c5401c1e04140494800094054104900030340c4007180d540003070700c00c0259500089001e01c4415800b90445038040c544c160413442000101e0100000d015003d80301d81c81c2d440a210a010111504010b40c4980d035500c000211b5844d0341d100b88003002400701c504228413980c2480c0c00025546401d18801a00101d05006907203943c885510341c1000300c140e111481c90070070207c040e001c0d50b0644504600d00074500e81e00c88180d400a0340c83c003019914001058451800d04c3e00600b48026201d41c0282c960200c400d0310000341011481c0400d034541070341988200901c2c49841d2141070300030030035048682100030b0310b40a1074801c0f041d1542a81c1310c4210303014246e0710210107000140700101202d0240051405000c51100c3ca88205004c101c1c8501c500c1820070200381c001034104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 187565071 1250 187563821 187563833
    0x150507060207050c031510090203070e0d0b2a040e040c0e0f01050405092a0a0806181c05090d03030e0d0804200102030714070506070c080d030911010c03090909050a 72
    0x5011b01e81d1411348440c1c0e40b030850304800c414803144c004d000101ba404000190f04d1341c003601d500401124020000c0300101128035004108000440b0703025406210350798601016030340003075855100d400713081d13425040030300f406046c1c41d075503e0060090310942c11060f00003036060f00070b4a01d5030203120400364001032036040209220541380081e00300e050580c00010705807080547c50607941084041c0700d240981641c3c10301d001801d458203c0d0400c0065000c3c0d142402040038400720282a01d09a4a0546203d9807441614684c0715981c200b10202041c1c0812502502c3d1600c000d0780b4000ca84241000540c3e210303003510031850f107260201c0303560200f20b0800900c000d1040d4261343e1050303c0741003480c1c03441d004240d40000b510f80c0a4001c004017107003509512941d0f0031005100340c601415001c0c00807130f01c61200f8100704400b000140301d01101806039020007004070740b180c020130001d603410020f14408180c00000444a104000d48190108180000301080780c1d011070040c40c209501503001021500c01c182805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 187566321 1250 187565071 187565083
    0x307050301141e10031d1b010503060307120507180504050721030302030406020d0c050d0f0c0912150213050f0901050913080705060711010509070609150507060207050c03 75
    0x202e8410004a444207503881460b0902480d80e84098400752061a5041c105a000c1c05900005640079000381d508101c10180000e03a10760802e84181841d04420150001580d8a10050b04e500d5015000f60000b4000c0554414005002e544103104070780b10b2541d41c000b005518602000c1403486640c544007840140035040005102902810601d50103a00000038225011000000010107140d000300005080c044183d050360190b46001e0b5040c0900c00910800501c03030781c0702841107190740303281000039002011144030b901418042510703104882070618070101c001a010440803194a02114000944400f80f03001401c4203c240e95020342056080070700b004120304c1041c0c1c0c41802003490000401060340c508215a80007a5109048000301c91503007820344240c41038600c0508144915424000003aa010440020341c3c820383d0f00801031601c858285545680c034502c100000903c10040501c1100000c42011494a000303080092802455558071402d907001554203a6103500204c03040c040508043c004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 187567571 1250 187566321 187566359
    0x11d13050d211b0c060912030b010801080102030601170402190f09110f0421081c0f020306030a11040e0f0102030718080a060b130e06010f0506070c140d02060307050301 74
    0x10a00c51070000003800180710b800383d42e6580401405080300c40a014942c0d0004450b940c000184650030300c2d50070700c0500a03181007400c2900141402c000000ca500c41071080e207002d0201695907000700a07000485154085000e0000c2ea808a1020711050f000f184c42404800103101900038550014980500b400488840c04100011850304012212030b102c20031040b181510503244014203c10040ca607a10049000703844c0043c0341090001e52202a2500c0c0d4a009034616010801030200c045100c1282007640801e6452035050350196003a200058102d90300c403e004180500300207000b90101c01d00701c1c50170300c0520303541020365800018002e2940c2e01c2400e00362501c50021943d4059032504e404c45994000500019100c555142c001507a150303902591840034203000d013001c0c045074900d251a15242c040c00c4c0b2500151080000b000182d50038154155001c5540044020812905e814005622500744c000d41c681d10001102c429030060f47d03080c0185018420580d1182c0c5c503503051842c079000d19910100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 187568821 1250 187567571 187567637
    0xe0a1208090d080103080c160f050307090c02100e0c0d080306100c02010504030b150402070302012406090b091c0507140a03080a030213080717060c03011d13050d 71
    0x2e4245106810481160449030b10800b107907942c1e0a030002083c00c1420b402c00900e05440756503c0000c0b0a405a1004030642d1411019a829541d503544480111000c0b4903074800560040403c1401d600d80551040e0760080842040c0c4d11410b55080020300050700300c1604441702c40011060144608004000e20030b080e8050501d03082042d040d0700080e040d405130384002070840e44001c00050050f41c501c50f000c0c0f124800070340195290501c80c50081c2c0070304844000181100302c4011070b00031000c03441e01241c0489104d522016000c40c10a4902140da600024205400000120b0104901d00008032070700c00d0302e8001d1002c0c05030f0310f0070300445d002104c640d540c0da14800e0407520030610125405c8000c403002601d4608005a6601100004e410440c2181d4084200f9000741304002074243e908200800c0318000307410a880d4a45d0b1140c0c4003185500007030046d60210301030303110030ba11102240e5148503002403410305c801140c2d4086d562384910708030281310000000f4a1310000705840420101c040c44644106107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 187570071 1250 187568821 187568833
    0x614030712200315011e0b04091d0604030c0c0b030106050d0b010309050a050f0c041a040b010203070c03080405040606020c3001060801060e0105030a03080406050601030e0a120809 79
    0x1c1d0700c48a914a5448018000050140380b242640b51200103100b16504007805a0303034264602007a55070001d0007441501010b203480d083c14400003c58810990580e0b020000c140d050905040e05c0c0c0c1c00914004503d000800c0075400214100d860801040380315500c40d079a80c000401c1c0f80d1400340c5209145034001115501305000501c003082e08442a140c22080315030b000128691100300403000f40580c5a409040c50089400c210144180402c0e15015010ba01086400c54071381c04080c08215640f110040700e8200e41545000c3d540d10701034000c4242d540052040b06e00740305c03060300c3d88901c44605130300844401034005000c00550405002da40000d00807030024055030300c03004012501e01e071b803c10b11081c2003622a00024124441c803c1c407205080c2c01100007009010b444c1c901c4a03008001c41e0080807a2009200c000044038030b400a0f1648156903d1f030394410742d0b40c4482d07461074050240600468189520ba40320030221440400c1511855030062400e00b11507048004041c0c45280040c1c510486a0010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 187571321 1250 187570071 187570079
    0xd1e170421060b1806010807090f0e09010b0a060e0102060f0c090f0a3210020d031109060a1806110309090a02070501060e1e04030e010e0f03030a020106140307 70
    0x6041c942035034925541c0c076040e40401e0303860720703070010041e40000f0781e40808030305502c40031403503c3c1070703242d118030000c5e00d8200d640e444400c002d462209483c880d510100720503820074415250f010b550325410940d808004240d064a00000071008038058000302c00096010004504543c0e041185541046029809107040d0802000424540c400c0d81013181c05680b0380c4210610580724158010010146000680d030494400c0c003e40b0450000c4031796030000860141040140d9191020021190f25a5500100648030000d007050b03000e80403482544090b4841071101401e50b4480c08018a651896a0340305240b07040b010401900f0b0321401d8110004004030110101d07110100001118800c0307808a80e07101e1280d0300da98401d0040c0c070902100401d15400c013900015a10780041501c1e00031040300181940031210084c0c46c0c40703014000c45002e000102800717600c2340c0c03550140c800c880601001400c110004501c070b80100f495580041103c0c00181e540e194100010305294106406e008011800303000400d01c0c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 187572571 1250 187571321 187571339
    0x60711120a14070201120c03020706050604020f0322050d09031203060b0a050906070f3203040e040f02150901020106091503121107060306210512090d1e1704 69
    0x51042510b4092000251040c2907a015110080e040750140c48140940d200400008019400c002d000f01c8040d030500d80450381c2d51410340280d850856030f9a07185170955980d181820a01918011b2000540b0b0b038090b884400b02c0c1b024018044203070403540711009803515500d00381c130340c2d0000f03004540304040c98400f082c0f01c140722900c1200c80c0340840b45402d070380340c019803c0042c00d20310511000420390600f0203c4001000b01841000005c0009111a950003001c04848124659460782002071980c1017000103103d41e640080c3d445406c41d00410b40002d8088550b8003107004011300480c030903654440811240b42d550703424012003000d40044c003410b0044290490742c0001100315408024141050703c1c650a0509218030030981c4001c0340e00d000c0750441070341c0d40c0001d0014a6a8000c82c0100d0440e0549261501e4417400c0e0f10449a41c450024006980e505602e031503940c1011384000c0d071000a2850341008035258030a0350403d043c591068059421440ca001c1241c0d0541d10b842802c8406c1c244010802c26030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 187573821 1250 187572571 187572587
    0x6030a050a150b03100f060b2511090f040c060509031c03020f0f0403060609062718110f010c03140306040b06031315051b0f040503060711120a 63
    0x19120a107000d070107075099602d1001d044000e15050301446009600d00b54501c00350001034112007849410041c8944441d00100d551281b5400300183c4004c2c2243c90051089081b5404100c170302903000140c01c602154002101c01805640c0401c00410040520080c044c2c1e0529080080c216400c08600c1c0c180e00f880401c2d01c5041c2080140d000c8142001107030100e41c000c0e0111486e000b0701c0201295244100c03940c00f25950003500040e06c18910b800004508100300348520801d4664000d131140d985541c60242a01c520a0b09403080e6800b031b240c40c0301e1010000c8440504803428820541c0500d0607a28000307011008aa10b144981000482e42d12000030940011201c81d01c4546803030036640d01d607911400300f4042c21000c00c605410080000c01c1080c8480d030404d43c00c028620440360301e038101814100b581c017a21016204803242040030310316402c3c61079000000b0900345450005040c107250b940c0c000641424400c0b61450007041b05041c40300d484040030320015065000450115080880300040244251 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 187575071 1250 187573821 187573823
    0xb0a050307180e070305070b190504051c0c170f1005040b0402010f261f1a0a03060803030c031b0a0207051c0507080f010e01020720181e06030a050a 65
    0xf5640e80c84808100300030f2251402454000c1c0c03c944050b0b0f61640e9621055025640d000b210085a01d203a041c114440c400700c4040b640e009104a42507c4265420010342080318411a81644a00c00c00a03031401d44416120078400328034054401000b20510040c140300c800040310000070310384801c00c800281c0306400c00c1c0c0c21640a103001c2840c030301510010b031803068074120104041c40b00390508650251401c0c82d940e12504403c1e40c1052041001001d42845022502560041d59100c0c4220f4020640b0355014180d403100514000c21072541e181520780c1568070542da1a20880e5001007080071f5250790b0510b801aaa12a0040038a09504800001d460b80782c0303405403600c20b034804107000707402c07a0821284a880300d411a0a4400107a030710884a50344045440400d406035082140d00065000c1c18406d9440b125003106000c2030a1802505070300650500300145540405030304041542d266a440d080707403003008001c49541400d404943c4140c94410020850b07886580101d8031200096008281d242c086 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 187576321 1250 187575071 187575119
    0x20a0807060908040e04060504030f050a08011503090c0b0c060606040b030f0402040902030d23040f05041104080f1b060c0d03090204020912250803030103140a0804090b0a050307 78
    0x140082e03141c8907035184903582c0242040700400044c00284899035010a0103244aa1608030303040d10096800d41342802029981c501040294004000401c685061680b01156030b02e00069042440d40c1d40c0080c914481d08188402c200c042081c09441a0400515400c40005c40c0c2c02c86c1014900502030740248030050003013001400b083c0c080750464030345801192a084c0d004003910288280c80200410491450040d1070107048012a401141d540345412a41925a0402c62000b9a81404248005400c14107c4200c002030304000c0010403020134014825481614000b034005036851840303d2181c5182c0440541c4594010040d00808500014601c3e011a00608021940540c640005002401240c0209030080700304840c0200720032022171a2000900e2a0600d007591a10003902c6510808650160b25070f958410001400810160301000302188220f50407a040350f2096a41c11120750402d5200302041ca8660351441c5003490072104100103040198000c140c0c00e4504640d44501400e241010085 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 187577571 1250 187576321 187576331
    0x90f02041a0c07031a0412050a020304052e080702100204060e0f0109230102061e01050d050708121803010b06160c0b1b070e0f18010f090c0f06020a080706 68
    0xb0980c05104510065802521800000d201024070303000513881105c0448008040700c500281a030f014805031151000c03503074011820701e8180014014641c0788001d00442c541c0044658450342c542ca140c482c00c1c8001c17141d8465030141001840640340402d00e25043c2540e600601041c091740d94085464681d0040c1219105100c00c4050b005a4035104242c0200c08404c4d402800004031410b40141c9084a00e001e07401c036a1a0f039503e41d01c0104081c50303406d4031080d15503904010011032800c10030706140d403801007068480c0950384504451503c082503041e03c83c039500104440b0503000940c1d80c04070310030350160001d001c3c400c00320300001c1d12403140e00140c2d0307920810300e060001801a4104008007401d4451403055980404203400e485280f40f42c0f2942c03803944546503000c83c100b001c0081c03c40c040d41304510b008170583c45804202d4140b00d103168070a9000c0d980c070001107081c00958050119076502810484002c542000c216103d1241d1907002107040d94007000c1c0040000b07a01c2d50844a00f50f400c0100020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 187578821 1250 187577571 187577587
    0x91614150a050d060602070f0f0503030f22030b040b07080424020d110301050901081b011b05060414011b140d0204050a0605130e010302030624030d0504090f02041a 72
    0xc0d54080d0740c003001c04461908131301240e0942c00007104400c5e69250b826500c0250b80e40c070051626290640522038140e0400c0c0306c239000e40c46020303015011130b0500e022031043d04d050408030242c1d000380f194001d0782d03d190144280024000c850280540020f11071414040070325060f21179485519507111680300ca003c11100c01190300600b1f5059035480108110140101941001c881c031190b0070a0164501c14072201d8000103109900040106014101039002c2101d0710010380151460004202100c100755000c0c280d40d0002841402610b119a00c506006050301d41003848150841e1036018800482d82e10b000c0c0c1a400c515040f103401504100894403003a503e90b03d800600d00a40100d900c01a0000d0010801059190b0030a0251410250840d00d0b00c030f50654441c3c807500200030a11000e0341540203040400d5880102d0280c0c1c51300b1f0300d088008500340003400d2000c01d240005100081001510202d803c0c81340803424000c1109101c88a075040d400c1c5030402d00b03a9652800201d6400d4540c2d500014420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 187580071 1250 187578821 187578827
    0x40803070c0201091d09010b0604060f0c1506030609030206060105030106090e04050a0c0b03090c040209060301060503040606050a080c091f151b03030c030e0a030e04090c030b091614150a 82
    0x100505441300301c4044060220b207410701a4042991a2540c40d42000760122482c240340340ae5030f04a40081d900e40103c001c020000380c07a1800d100d0415100305407603076040c11035004540503450045200b034200080c010301c2410700030306090010b00703054100207080004001056000524006540c8251180203454541c1e00d00946840005000207104070104200010909042c0b4040c6100300b5101040d2603000c003282c82008107c3c4a804e41150303200c8411700040c031100d03128401550b0b01500c00c000000340c0544a8000504045881c0e00039280366200d6140e4a12600b05030b2803d6030088214107000d20804614442ca482500e2240074440715480045003611040780b1942100000040f1100c202c2031185240c100100506690300c003440c042401e0241911003950000742c400e1f9030a4151b80c5080500c0721080030003002d040d2050058604510310503001c0041000543e819024007800b00c0108a0711201c0c551000949150383e21a50704c99801c1c107031407407854403182d81c03103c2ea211940444541d6089111016 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 187581321 1250 187580071 187580087
    0x6190203070f0b0f010603050403051603120e0105101202090c091801060c030809030a020715111e0c030a11040903090b0d0e0f0c030318040915150608040803070c0201 73
    0x14045a00c00810302d400e0200500c01140112070303409003156980e80316141502590810b0b07600800241d010071203040611160414128003511915005990303c0c000510301d000d69500e80003c0359140d5651051020030030002c1402001032440d50440c80001d10507400107000014000d04e00c404202000880039829582c05000c9240f0100304d1a0040c21561202d600801d0a240260701b14041820900403518114001003500c40c0001c00e58020003203641000c04020340310380c0c1184500c09100840030b1007032400c4014849014002d580e502212950914161350307910b0214942192070290b0410b0401d040841c800101e00680c449e029580803450721400e260840b0f068401d503008501681010a1208124200f81c20614100c1649402c9400c4403450001c001e0329540a41007080d850790042210701c030196044aa1440b004d000204005400d806a0303c0b015946c034485400a1b0840b0798407021500742c5020b4500c2440544514985550305c1d203000c0e51801541d100240c9060280704c80a580413045a12946903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 187582571 1250 187581321 187581323
    0xa0902040b0616060f020705060412050f0d02030402031905070b03090c1017060405090709050405030904051609120b0103020f040e01020a030b041406180703090204020a0807030f0501050619020307 86
    0x20701607942006542c00c0c0b01543c0c503039404803103090400032031802400c201d00a0b030b0a4640c000c1c001e451541c550b9610340d024498140e120009206080c42260003100005010300551500441c0260366031800744109814152480e84158071002c280410784007003a40001c1e510706079450102c0903607903912030000f158a440d01208400ba80705409195018010b079118100743e403c240c4031550074145854031800c01c41510320483c1c4050069029140c2042a00e640703410040c0c016008106891801a548001c10706442080301c1c2c65201041c803103041d00010303900090441c018a9021200f54013144141d1307071034004050600c4060700c00e0402010030310041c1d80305e902c0300c40782480c1d140003190390b06a19900500604805699244218034000130045400503400c05e0510a4a0050040070f10b00b00520b240a08a40081c2c0b000d010190307203100c06001625284010541c00d081c1c0d80f2011060318117000300400390703210403004058050030600100f110740c98080580381102c1d125060182d6020389000124514001c2c1d00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 187583821 1250 187582571 187582579
    0x20304050a060e01030b03060f0a02070317100f0621020714160518011404200c060f06040b010f050a0315030b0103060606020a05030304021507050d021c03060506030a0902040b 77
    0x41c00601c442d0401e0080c00202802c0c1c80c14449240e0710800c260711100111500b04182070840005041c2c028950b0003401d40b43e01c05e003802120300b4500c80460640c1300c070480d006900500401c00502044d0300c0005124010861481c0070200781043c440e1100c2c01c1680850994009a0046000c07001c200355602200c66507054541100c801d0503a10608449115280c45094001da07010303d07000e0402046c07808442d058444005c0d40310400c80b01501400010070400c40f8000d504a5903101d141503000e034220080844001ca00024030303a50a00241c102c0450700c01501c440e20442c5062400c40003a46c00010450a4003280d06007941ca8000b404001c0d0302800840c0000d400b220441c100102c20021080c90b0503040e64002c50003000401d8036060709a0b83d07401081c902800c42e60003880064010700d4201220602d20a410311528140020341d40c4036841c1905024444000d0703008041610b045640c602d0448207001c40c00c1c07401780a01807918010038a684000703440c01c0e1100e602d41c00071400b55116600241024200a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 187585071 1250 187583821 187583839
    0x402060403062c0304050325080601030b06010219031e0e04020c0718050c0d0c02120f0c211806070206160c141003051504050a090b061002060f0702030405 68
    0x2c080f0146016001035603007810204001107000c81d5002081d20f054801c045c00800c9100c2000000416402e03005108584a5030031040100700180c003806203034001c501c1401c0e80c41c0241454400039003040780d1102581101c0400c0035000340030aa2003058a5200400074ad04480d4041c2174540c112140c1251080c859001400003400301c041506c0000c0080071079114810718410540223440755010740710b06a07801240c0034401d110403003031405c599014280c9001b00d40110f5680c503950042c000e4803600b0040301498407040124240d00d1a00050080104004a035410541950582d08010200740154285490190350036001c4034202e481d030304100c1c0c000c10380003040c2c03035105e40d4420b08980c0c1101201c40122401c13103a07088d001900301d11007030031030940d01d1004000d488001d070103800840051000801d981081c000c0820701040b03940f2a441014011500d0341c4000c113182c2e0840c200482c0f0301d0300190905004411107050007020590110f41141c0101c003a200c140d00036210f20004a14501554006aa01207e51 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 187586321 1250 187585071 187585091
    0x31509030405031005010b0f0d0f1a210622170406091a07080d02070b09070503070605091f11010f050f160929070b0a0e03041409040206040306 63
    0x54021110210102c0320700119007503400c4c050318800c0c880c040107508184070882c1d00c0007061010705500d0304840c00014402002012100540b004020404e01d1594544c4a0ba8030074140640c14a85030900749558055840d11003840b65036906c40244584440c014421244030030f49042d038000759425410087c0074074003c00d4440521750661141c071a42012032015040051042402509001901440c40545041c00500d4540c040035030f120b000e403051103a5003004244005801d03581c400d40114500401004514244004d01d464450035400040a1000900600001380d0340d400e024083c40314903a0049070300291409050743c21210034550038200d942842c07038001b5182030540c04179101d1480c1c00c001c15060f844e030101c41c3d02070f1800d003a01007000502040f014440178030110025030301202c03864060048440402031855490f0043c5100b110201c03c840b05020002c500c40c05854030303a1404001440c6050300e00b4850031241c101c000b0040d8002c16031000003e045d076940c0720a0720010340e04203030309020041c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 187587571 1250 187586321 187586323
    0x1808040b09120d050d2310031106090a090c05121e0f010506120c090d030302070506010b0405030d032409140a20090a031e0303050105150a0c02031509 66
    0x440800140601040c08007042c000400007603003040303035100c0c0d12064038000203c54100090300c2c1c01081d540d844900300d5031000841842c50302151180d034030040070034002e0307045241504050410f0868244590b0060000e50781c255135a03540081107540170300d800241554080c006498500a880c1500d05011802e01084020500b0014030001001c090008401d159034104182e600c0210a000d0a50440824404601802c480803587ca4003c0b103204d4141e0b040006150004000da85440400c40000750040303171010421000f001681d002d00f01500d202801d00e0b081a01199660000c0d030390160400d0b44880e04a28011103030481c0810014a400501c3d1070ba43d110071424015107118030a0480b001d8110001408001040c440c400c034079851407018201c82c444011911030260000320800b58415401e030000800281955201c04416400007420724a1617154180941140c138160b2200b40103a0074210420b5003200740d2021140528a507081070301c10024079001291500b007043c035080005800d600140000444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 187588821 1250 187587571 187587577
    0x30303130c0b1c05070908160906081b01050f040b071a060306060906010c02010527090a090201051e070605091f02090906150d050c09010f030b0f041808040b 69
    0x20050211202055885108801c5485000307401d0f484440c407070000e01106400c0790402d94205c801441d0401000d501c0d00701d5a418030a564070408030429501c68100000d600b6400382d1401064010b0281502c5c01c0120380c48195200c90034001c6041140000300320381c104405400740d501910071120180c0c0c480e01d00d0310741200c0f010b00030400400440012000500d1620300021640d100d080d014215130f180b5100c0342c0040d07070240441c0008a0610030184000b030304c1072020408483c0b5603a410001044148a410203210700a54054500100103040581d03850160b43c020f030407210360304c20201c0c0c89420341c245401d0f024140c0c040c0d043d0003882503040c88140400c0e00c2c800201c000b01f035411382c280441681e0400c41d201c0105e1003000701c442e402603014000183c05240c56001c89076811035003554640b030304454030158001c07075604a9011a1001000c10303078018a590101402c0203402460800b00482500d0000143c609519101003038403481c3c42d150005282421400d0030403096034000070741e64a407600c440416484d50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 187589928 1107 187588821 187588823
    0x3021c020409060207060e030408300d050907050402090d0803070c0b1305060703060b18120a0b0a0b0f0604181d100606021b0d0204090203030313 64
    0x1600d0394060800b80501c50000141d07a04443c1c070f4007408640d494941600aa030090200340124400040c44c031035800782040000c01c810f622059034540705d00048149242c040808902c204040711146c0089020713581d07040c00d55804a40301c07814802203005849026a12180310440c0f03002269600e00110f400040b41e00c2c00c10709041c0700e034468040c065000d40702e0149110030620744000b4010184500360300110b6a06d000e10050740351018801c2540140c10700c00145029103002000e45966043d4440d40048065094404034059802c140150303030021a0558062030900032030b400140740000f120303002c1410051806081605000c00e02c0c0000b485002d504030300581d100c00b0700220440d1400201a1850b14100800748000c10703e01038819100b2641c00081503600100200600010b140c0405c003005030f05443c0200d800115000050283c1400000650580800000c0c40716941c880c2d01404401 = true := by decide +kernel

theorem cover : BRFrame.Cov 187410071 187589928 := by
  have h0 := BRFrame.cov_init 187410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 187410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 187410071 ≤ n) (h2 : n < 187589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
