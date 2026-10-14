-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0267
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:51:42.031395+00:00
-- url     : https://prove2.me/submissions/c6477e44-dd0b-43d6-8b4f-0569e8112169

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 47841730 ≤ n < 48021586 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 47842980 1250 47841730 47841763
    0x110d030c0c11010207091d0c06030708040f11030601030b0108060a11160606030602040b09030d1d010e19090e0c030705030d210c02010b0907030b0d0308060102030408060a0504020f0102 81
    0x6898000c6a4100c2e4038640c203640c140101c440301c59a840c0d011003510005441120b1821152003144c0e0440410300c07003408140300c11583e0500d546800b03600904816000351024140c110065030311000c01442866000300c041d4000d044420569507442c0047c5c508500f40034540c01e500448007ca05544040d00900781083c003080101400c011604103013491051002c070b02652440d85600d0004046446480200007a005d01240140d80d91f0090051529081c0440a92410081c00c800c407000000000e032503000f8202d0007403a1100080c0c0012001a00805508010903080104458009007508103607210301d0000b030254050f21480302000c401c25860b02018800c1c2e0341c0507007042d00024441d61103140c03a6101b060000100e850800358070500c80b0110340c0880c000c1c00c0075039074448040c4038903c0d0424510354041c15a103414400481d10781e010902c42140b291001b41032007101808900c0c168024002c1d100609030303c008458940c507000740302c40e0140c2011f8509034003075644202030032520b510200c3d038032011849000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 47844230 1250 47842980 47842997
    0x61b120c0c140304050415091b0e19050306100f14010519030617070303080a02091c02150a02070317030108060f070203040b07121d0102070902030a090b07110d030c 72
    0x440b809030091200355005014081044041490b03a1a44147c0740a107003500c004e0030b200c0d0305043c4000c00326520b41500c8603007035851031040f01c078040d400f42c2c2d9440381c1041501d0003000d5042c00358440380c10758419005594103000c0c031400c2011040d5803440203c11074107100002002183d0304c061850201b03400d8609503001607400c00940420300984030ba054900e410074940058081d6440310f10200d1049500261800d5800815080080c95032221026421032000707001145403841c01c40c0003500968403000911080040c1850034001c3d136a8039030886000c0036410038134603682c0541170b000035116009800110342203101010210710030a042401c1d603050751032841c0200310310b86038061102c40d00f41004101c1002c510013001b01060b0f401000010b01621445058541340940e9500d40241c4007000d00c419130300301c50000c08411549070f80d002503201704642a1a070016501e4662034080400b81c001120054038101c11503040c0f002d02a0300c240004206000d03001502c42c4441c6042040b030a9030303200c4140000054071007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 47845480 1250 47844230 47844233
    0x70f15090602090f01050a020d3504030807140d09030e1e04050c07050304060c1506090507030e120306130f11090306090a030c02090a020714030306040c03020301050328061b120c0c 79
    0x2070440b803602952030310b203c0b8802c2c5560b0603140ac1012004002c1e21055100e08184010981c010030503a41048c1c55080c030200b0075a6103008800c83d80035220316100c0182d112504081814041c2aa007510040060030000b108490a000c8540315048030141601407450100050561200441a2545a544031000d149014a000c200b180c1000300c192040c2c400c01400300d50014103621074130680380204034400c00403d540c40c0440011301210000f020071140754024411131070020721040d00b10b0b030f4048800c958840480221080503402004200c51000001e40b4050201d800712070030310302a001c0300030114119071141d900c40c030f107990712099080c1d4000c010456540e03040c001403919142d10b81d401b8034415401810160280c41d0385d03071441e03c507038040182c6801c000309100035410700c1d01905050480f42d08003949507501d0280071950301c80d44450000c41d500200074040c40d82030394880400301c561350884000e000d15010610043d101441040400c00440c0c08040c02c80700456050213030003089500c6480d0501030072407a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 47846730 1250 47845480 47845487
    0x6060409020a050c010207120e01020c031c050c0717070f030b01092d0603020102070f0605030112020103020705071e0f030312110c01090302060402100203040803070f15090602090f01050a020d 84
    0x140e0b40c44184a01800440c1495000344050151640203003103a0001a00d41700c00601b0040c0c62407035182c1103400c8412150981d8800180004194454500c00404410b035035000302e9103401116000b045500810000050744100500319484601e0a1415100440d075680c400c003a485804d03200c0104074412160040040c800558040750303e00408540046411904804404a402190802d000d14550303030a01802507581c100b00840280c4800825460090306001004c2c01d00c0c00b05225001e01941c000030180f00310f903c83c1c0c0548803241d51003012a8442500ea440c20503964140010014001181150004882e92a080b01c03504494040c0c0740d949a45542103100005040009440594071508120501e00c0c004244100c0c02164025406807031030381000e20402c2041c4080003104030440d40140428802e800000c801c4800301c541c4126001004000c40c45d1003108000c501e200181014546804c80c000d200c2950020907400704112401e481000d03880c8010340c0d2078000d045045006902595051088501 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 47847980 1250 47846730 47846737
    0xb0405070f0f060320030c0a14160b0405070308070c14010302040609050607140f03040303030b04020331080d020a0f080417070203010209060328050c0d051e0a150b030606040902 78
    0x10091405c41c0c414512250b80c0e01c181d84140c0d0403800741100000d40020f03169003c5e0340070300c8064103030950710f01c0e02c04100c980051724080c00f03001404604009001c6000c01000300130f0300008591000009032903268a00f00903c91003280c0c414004100840c140f1000c05611030710854080c0d5000b0340b2504899810300043c805160402d10003180d81d03090304d54040d1004c1d401001107241141460000f181c0d03c50440c41c00038140d610b800d003503502580c018002d02c40314084c5440f2a40100001a000c00740500d00f5810061044003100380241c41c140c0c00280664007548a43c00a00812580703860303503014090000d10480c3e1000048030050a0030440703818050140300044001c050440c0001c00240c01c181c045800524954829200c00f000300e03134515400909a510805072002031408068100151f00d8901003051a0380306000d03100101a54800001d182861311070000b4040810b240304041862406181841c01050500d03141809500c8000d0001454804072080341e20039140640680d04061070030748640c001c0e40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 47849230 1250 47847980 47848001
    0x50405150306010f030e011e0e0c0103060803070311030706021810080f071b08040e0a0605060c060606030402040609090c0f09021305061602130504020405070c0f0209040c0b070b0405070f0f0603 85
    0x15200c2404460880122307190380c100c05044507001800440d90000c0529003146444403d040c0b6052440c00c1016680c04015030301c0d4680c04d8102200c0c045404416542184035184c0010030b894804a10003082d04841134004000310400e80744555200074284040e25506030444000c001e0b429480006000c1078803131006c010b1500d01c07540005c0c11a1099030f80b0380380c081d04550001ca0b5001010010441c0d60109801060001d20b411781c1c10318541007481c034250340c66010081c5070500851000000c58112f44a540c0040000d01e291081046658510300e042c609490861154000081d00301d0004030703660119200303c8a0300031048008541c40b03032400050040d90f8020394403141d1011414459076000d41c0326640b4a01e03144801240018551901c0e104000c11660040c003801d0410403400316400000300040601d14007550126003060281c0d590f45042c80b6000d11580013150400004a20743c0100011060718501079445035043e22511030b02c1c0d8034503000e0381c50305125100459486d0102008418000d0b0310001c9140e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 47850480 1250 47849230 47849233
    0x618031911030406020105061509010503070305060d0609080309010509010e070501080405030d050c03070201060f051309112106150105090108090712080d0b0901180c021507050405150306010f030e 86
    0x2403000d44041c505640042e440328001d03035165410401c081c81d10081002609a028801500304040c03d40001c11900000300000c0605903640041480f540d5902e00314000503502403400d1043e601d20303181a05d80c5400a4407001031940c00d15000c91070b020818026404400c4070320b0b00600300a8640740c01100c600700c0280c01a82e89000c00c01c07d13035045034594000d203031040ca0800c044a41e2800c003c54000d00f160030b194062200103649030410300040c0d4945503903102c00d2403030080c08281c00441d400e00c0041c107555410181d40c00b400c07920f03c05068820f0b510580740b00740940c00603148580d43c0c0800c80c88804041029050002d84104407960301c540c0146040d6070810344210446000a44070400c3c4809015111019110160089020705149000c1e016040302c40388169403c0d46070707515003064026058800d050445204d42c40790745810286108004036240c4a09480d81510300c3e04101e40040c1080c2c2c05402954043d480c1101c4402100109404072801130006a40f603610700c50615000b100100410f000f40c0150703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 47851730 1250 47850480 47850497
    0x9010e0402070f1e0c0504090515040302100e15060603041b0e0a060914070e040f06090906050702060421110a03030f0506030a08070f0302070e010803040806180319 72
    0x352901d102504055114503c5141001e105003415402e40b2900781d0030f40140030301096800d00003003044200704201c4030181c2e4040b80e01c001e81d02d40705040004451112105220b80b00812050580c00101903102c1564021301300b0070002000c400b0f03900c3c1c0c91054003000406403400c02098107801e00d41c00a42d80b0502407800c0c03803140600602d411003c40816484824212260424032100e0141e0303104480003022808001c010400011000f0244580c004100405110b40540f641c42107460f02d400122907444501c104010658892106000428010304242e50041c940350008408034000217134940200c2d0004521841e00a8110000147c424915a02010040090200c5041102c10083c1401c058802d85000c503074280d1030841c040031a000105220b100303500409401c0e0204064900311483c842d00151440140481d41c03d00303903e0403409910010169030380000008840802001810035280940c054a040d929103030041c0b0786002e24a10050030680041202142c0c01c0250240010040440d0920300300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 47852980 1250 47851730 47851757
    0x11803080306060a05070b2d060d0201120204090e0f0d020d02060f280504120201060f0905091e1c05180603040204060509090706080f0103080f0c0c030106030609060b0108090309060901 81
    0x2047c0c4410354a001c03070440c0c82e804401942c42c8610002d402552500054160ba182c0074002501510320000082c1c10700c80d4030380102c17a18800e550101e4014042d0b174a414801c06001c018220b60b100c921a50740c09040c098480d0b04410607101050080d040c0500e40d005081390303141d0070078000c500300d4041d140090280d40e4000e180c00383c19030391401712611b51005d03d0000d11403925040028003003201c0011081164504002444a420020003140035a80190b10020f0596030300da20f65032400b10325000c0c81010b0094441e800b48000e0000400c1e00c2d107551038408804400e0107030300080d1180d00512400e0301540040e130031403a4241c10408091944030380000c1c40807440d01c0e565000700303e01600c00e5540350002d80051000784131340c42c1c102105a4004151071b0082c82c1a602d162a90036050242507012043c626000038424aa45010014240341c050010002c0004951701d2503d10300074084024221000c03428602055070340d602480c403036403052030a0000b46203880c021600304106988280301581c10301000c800400e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 47854230 1250 47852980 47852993
    0x809010f020309040603060207030e040b03030f0f0c060f06130c0e0111010f060905060a0e15040207020a0b04060201020703030b1207090b0303070c080106170a0f0605070c05030a0806011803080306060a0507 90
    0x18021b500a41b030050f03035a001414000c050403601210140914203140810b006034400008941c0b841c1070005005032500d400c04020301c400c3c4200410102d0a00c0392900340300520201c40c48203801404200e600500381c3c0c505070a0b000030b42d41e056611202181c0b4a001000070395000700c19500011102c14000111203c0020706c8508480242c0c1220011654490400600d828020310840c05000642c0d4052017130f01c0d007c1105181481c0769a0458001c503004600341d011034503604407030000780000c4032110b0f0300c1e5901c071b180090003504601d006a00090070113540c02050305001e41e80c69008542c410140030346904040c0d240d40581040000150903102c108040e05c0441c11491005018048450002c1082071070309480d8841c0c10841c0701a1805a044100c20304001658006220085503000c1e4020489030750f51201644c03460344101014042d800001008654241c0c031120444c0b00d200e00f41c1342e060f141043d09036011402a1940001008070a080011071041c0c540031010b84041440380c640145825403656448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 47855480 1250 47854230 47854241
    0xd06030501020a02100b01050f09060f040308040602010b03010f0c0e04090809040903120605040b0105120903090405130c080c0105040306020f0408010e0303010e071805130e030a0c050f07030809010f02030904 91
    0x18010b805c01c80000415454900900500240034607099040825000802c1924400da100b124452440082c0c5041340440580680d002540c0084000c1d48540d07590034081c0c00b03031443e030325810710030f51802c8047c03c0c50039a24410804154443d0396850112015403043c8002000b00001c2070b550b0182c24800c46150b41d840c0e0003400300b514480da036401d10700741c04c0018500a8600030742200d48540c0c00d0500554441e40e01c1b030142d420891078130b404038040e52298618582540f2400c0b100e150803909000410541d0f40310030480b061624815103550882c2d40da650b035080d442c0e641501d103040c00141c0400003000401d490780c01800340401068aa1407070603a4851100c3d003100e492503200c4e1340300e0f000807004100c0c9406001c52142d00030400d06110b002a0100c685030301c0620424000e40c1e00c24400050b40f20000c0309581e004a0034961941c089070360f103815011003c5c100da200201c003204c1c107100d150500c1540f045c0104a6001f140d41c0030b882c444c01c00e2842001541c1c80a00d0075910740c04c600c418024003020b40c2d214001c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 47856730 1250 47855480 47855497
    0xa120f0c15020709050c0a0f051c090b1909080a030209031203010608090609070f0303080910090c080c010e090103020103181b051e0a0324020d020c0d090e010b0d0603050102 76
    0xf0000e40b8030784103401c400d41d20020300b2006510402c0c8003070580660804051218046a8030301903990f031035130407490b0205403240085007050302d1400c4000c504120020302c40394000c030500b039622644990170703805843c20782c5c00708000149404c4061042c690325078040d070064121580000c0c107440300b24000006501c0c090300240c2c001800645810240082407806201c8181c01031001005004070074203101c842c0d580f02e00709110040800c8074210001d10b100300300b0710a80f18104150003042c0000550b41c00c005048025501404080703001e1109142c13419030141380f8440b0800005007504681760701e1500150010720112200320b1840e0804407442000862a02030914034207454030a0190160503c002c0c0181070348403450031045c8886011010301c1c45d03520400e102e4126035102906603018031890003c002d60303207030b4007250317064440c00070400b04c80d840500c0d0098512007000d07008807515402d0076802200e03240746a00c1a0f403920317616800107001501540005080040e80c40102240c015500d07600c1a00b264041c01c0c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 47857980 1250 47856730 47856733
    0x509011e02030a05070c0c0e040c0503011a1002010b090c0702030f0303090a060b01050708030f07020f15040210030213030303050705090907020c0901050306100603021c02040b0a09050a120f0c1502 86
    0x708003e007642841116009011481c1007084013006940b00c41f045030482c001d091507007070314400040400c00050b01c9500a080040c0c001d002c401d18a0f405400c0d9015801c0307102d441060b60348041d402d07103441480b40c0d0000800060075130605071104041c4200650014000742d03014000c0d203003031a82e042010402036000705280382c000c0450001c03c5c1801c0c4100d404000003d81013000407c00c42011545240a80380c0121811000f00515100c81800341d15003c65031b4500c0300d11b4060541c2049000034100c00507840749009980440d881e14800c44110124881c419220040030010071045c4007080c030950026a1084507410007629002000b17001031081039084403540b005130301c0b03000c1d10400d5003412a14280100000d600421040c02c3c00c14055610181c0f0b40140300405a01090141c55081540c0c1d005082011688045680381c1e15554a0303902d540c46a01d01d2000f04401c0342000400713007072040711002121035039031030030645458560341d0118001519000b0398140307000f0140481d042e00407080405e0502c2140c1c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 47859230 1250 47857980 47857987
    0xb0f12120715060b0313110102010902030d120b0406030f080f090405040b04050c030f0607030c02070506070b010f12050d080604090203060f011805011a130308040b0a03110711040509011e02 83
    0xb060790b4103449164104c0d0b1441a030520a108200d5000703c2c10844046d800321030a0390980701140100c0c0105000319019516105c3c3c3d481c141000c1c1d41080042c640c1420864084c003e8a01c1c510a1200f51003051000a102c0f0901c0d001f850045240c2c48003800321104101e0090f8940005100050103507842510140c4040401c5400d11040110801c2000091001a400b510000d90710b0004c450311060010410010701d074848800b035201920a10130310020308070080070341d511036045003061624010300f406406005005900b001c00c210303007401c504481c42d0741d121004000c1c0c074081803400c4403114000741559400546810307220005139003d000d1648542072800d070946c12589007034440c00101c120b4400e000f41c12883c100c011b0105520343d01e0030206150396188181c0d6900c05640411398014410b42c00034100c80030110300407612855400007480d49500035542808190040145051944100d040007070504011181030240390402d031704070640c8104c03100700001d0809016241c4084411840c0c08a9000a9000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 47860480 1250 47859230 47859263
    0x60206090d0c0318080114060405100509060402040b0c010506041401080a060b0109081515060412060e0313080106080d03060b030a0b03071211310209040f140f01090b0f121207 77
    0x10343c0c7c0307154054000c4030306000c80e040c400c18070460801c241c0076003405140764000041117512a90100c4008010460300b90343e03107043c00c016641c02010240c0704d1314031a82c100bd80803c00440484200da068542c21300180040000b20b170303910402000c0c1003071101e0501c40c2c00113001550b05424000d095608000d032524800794540351101e650768484c0146c06a22030300301400207100d6000c5401480010580c00140000d0942c00017107214a50b014248051040380000704000c030b40301c0c4064020008403580b00c000c0f600390882028095069400c20302640c1d46400c02400021031010560304000004c4001501783c400c25521903114401901c11200103a4014006400c0f136041410071144030540c01845014002e40d02c070601000c6801c0c3c808101c1c1c0c0e90580c41d001b14640d4401d44e9907a00c0350900c0c00792030b0002c105081040c01070881622080703417078400740c130030600000964485901500082d20700090240701010714440030081600170006c201205c5200d00c00b45121801621801000f0081c0103001b00180c1000c0d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 47861730 1250 47860480 47860511
    0x150c0703150903020d0201020f070201080a020904021605010b01020c061206130507030b011d01082a03010603051503010b03210705030406081006110a0b0a020d0c110106060206090d0c03180801 84
    0x521480b0400c683c41008270360700a5414005480780158240b90070300480d00c410402034082d0241d40b252a6120b0710000d00300d40f80b540a500e40001080c409c000a000c03a1032a2401a61503445500f00e0b2a0041d40400560349100110300c0c00d1a03220500404029501740411f01040494004944000200350340f0341e50102c4542c1c200468004034404107090b4224605207000003000d221001c6e050f44c40000b41c2a00c8082d04d5003400a4825020801b850f92a48942c1d51701c200401901094429220b0300c0c084604036503a9041c180190042401302400a2503004000541010780c1e0000203890019020180040070002e0030034402080200b585a4500700f00d03084c220b243c01992481540424207000400c203450740c2c0101d002c140461150b400c03c0c00848a070740e030b50348500068481c000c410000c0f039241c00d0030300c0545a0051003410720002c01c40020810035444200a07030381c1e09401d4138840203e070701c810001070200e4852000502981d210b45407070019410034851041c40c82c0525003040b1007994640607000d070040c56 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 47862980 1250 47861730 47861743
    0x1309050d1119051b01050d090809090c070209060f01110102070605220314070204090b04230106030b06040c031805060412030c0503060111010b03151b0702150c070315090302 76
    0x411410280110581c0d440e195101c400401e20300c0c0c4c42da00301aa007883c603030045090340e51f4180714144c1807001c004186002e030141c0e484888164840c0c0000d0000c40c80d800c0c00304099902d0350703a01604002290f100d2104101c4480c90305803ca90400c1802081f00465281c203001800307281e4070510000c80c95003411400c2107411403942442c141d5403180882c0c08008039502c074246409018001104030398402c82e41c00824040c01140c078020302042142010b01c03080152510b070b00c80c118042c03681910720881402da407140c265005031001074103800d120740100b40c59140642c0414240300082c1800140c541c00c3c0c100e1007801d07140d9142c090700d07544c000c03004000c01d00180005501150006180420204984080c003900c140806048907041007443c80f6900484603003580128600d440040c1180c0308211a01c0e002404203800322481220502800b10080072521403801f501e18140e8010000c000c4480d002c03007400034075081001480007074800c81c6000401304100144949030200074a00100b000b011704d0402a10340070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 47864230 1250 47862980 47863003
    0x2130f11180306070c02100809121207020601140a090b0a0306060e0403030b010f0f05090a1e03030e1e01051e030103030507120c0503030c0a0207090c11060901060e061309050d11 78
    0x281d41050040c1e60349040c003404001035023407648a03500d401031500e140180a110704008040c001600300d5a603e250041680304644035400c54549030303201c1d0041c03c40406c21706003042d00068208800c2c007110300303e50000e01000b00058a101400c0d40c0d13940b240010b4030007540c03046c2d440250075428030091550500038000034001c01c2c20726210f00c030301d00d14005008119042c000e0701000004141c6042c035682d441c1c001d1004100d40b60700074080001a21481c84c03c28813500c022000300b01c004880741a1030501c4001440c2c1111029010501821700074015109139118052100140640d1100c041030b500c40070010318046c42c001c1d0780c0d0350b8940e140c030f1074120700c002919400001481180d00960b8009440081140d501013880000651070b5092001e06a1500000790000c004090400b5440c1d904c803980000d19001010341241280e005490b50440305007281c11030b014140c81c07090710000140310b90502d100c04083c44005404000f03480b0405072180c50402c000740b400d130340000d4100562880c03101d0040041c01c1608 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 47865480 1250 47864230 47864237
    0x10e04021014090907210e07050103091e05010218040b09010501050a020703063e070303020708040b03040605010f0b0a0c0f060e06010306230402130f1118030607 71
    0x1810240c00044030011640070381c034100090580e540c1d0029400e0001c0d0f03050038002809418540c01e21000c0500284030a080180204c104034000d9440b015075405400e0741480c01c5800f9054003801d1500450283c205c0d00c0c0d058071200314100d5140016148600c903003d10a004500040e10b03280c0d410000c441c42c0c446100014403503420414038520f9656180c2c00541140d20134202281c4e00c0c00880c405900b40352140d031014100318a07160002990910720440c13282d00500d0a4103e200001e1081d490f2252a5610989002031050074001c1130700180c02a402054500d010315003440c200f40c3d4440c003a41c0554800c13103046503510b4442004020311021a03000300d02a1004900c01c0c0c1c00c0c642581802880b52140c1d60b40513180c0710426075007100707000c29503109526024260055802c1c941e10b03418102d0103012a0511100100b5014041b40010444180d5440c007070b6a0090031442c002704110943c0c0d024241c000081d03d4000d0b610706943c00034000020041c124076645c40c0201c80c01021020030141071400007803010051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 47866730 1250 47865480 47865509
    0x313090e0606040f15060305010306050c0c1504060f06090e011a030309010c0224031f06050301121506080d0306080706080105090903090d08090906030a03020607050903031c0b0901 79
    0x620310082107150b4002001c0d07400140000040300c1041c09043c1400300c82d0806220780c0000300e525685900880c0c140c80c00f0b100c1c144519110303c00b001e0694403504110078036640202a01c00d80000c181192150010b00600d0b010481401010168041303880d55440900b902e40e03680c8442c0742a110a0140e0f0701e0001c403802e00c8003018945840800e440780708180e495410001d11a10b035108650302d440702404180f90010510f03110114600344648681d20030b40e803607411411030f00400b0050407038800f041002c1d503402d0b50f40c003401c2d42d181c41d080c02003e60301c25008647d407103524600101c0420b40d42c480c3c000142035035001400c030048591005001c5880503000481d86800c20241405005d4000301c0c100c0c1124019503580d9841e5951120403829070048440a075801106501c41805200e5090060400b1102c00c68031100941c6034401003643d5001c0e40e1400a0143c1c01100004800901031000b070300c007080303018060783d01d8584441100d03540050654103000d21f107603407540c1090303c605104d0f00c030b507015003510501241e9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 47867980 1250 47866730 47866751
    0x110307090e060d0816020102011803050a090b03090c040e0f120904150f0b07020a1d0a06080a03020a0209070c1a010602060708070903020d020607020402180909010b0918030705030a02031309 83
    0x80301d11584092a4010601762030078821a4800d44c840d202480180d17458503210700c40c038a00200550300078503558000802152000c0750f5901e000088038010724120004011206649003888003030a0103012048140c01200080403072540d090000181d001e035618407042d40c8c0d40e40481000b085413000084821410f01340c400c140b084448054406007580c1e0103070301c4a6100c2c8240d200144034044035800c11411b0042c4000c0800b091003403d0a818000c44900e2810f110090700d41000d107948000c3c1c4003000d0016880104101d0150406504e127903001801d901d4135602841207a1204610021b04040401154801e40d004100c1742d40d0501039641c100c0d490340fa044025062600307005001e61002d00010b4400c43c0420030400444da1004120b510041d8007610541d21044e0f0003c1084988020350680d44c012218000014800f00040c8100e001c2c4480040c549180c2c0e8441c2010100c2d906480801421148010001c40e000b0450803c06071508188550045640b07441207503280714421240e600c080501400c01400e041d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 47869230 1250 47867980 47867993
    0x170405010c08160507090219030207020607030e040e0f0318040c020607080c04170a0201090504061a090303040305010e07080706050306010504060e0a05060a020f01180507030b0a110307090e060d 85
    0x640c00e604001c580d500c40d10f09030030303803071260110300c900031320714802d000001030007034030680113401c00c09860384000920380080c5409030164072512500a61251b002c00040c0c000902440c18484010fa01400c0001c01e800040c8201c0d151010380c0c0c0304081c2d00d46c00400c401aa180da0030486090f081d0f4280d900f444002e0401c10080d648860160035041401304202c006000000b444098030000e0103040c801050b624a107000451b112090007000f039002403402c1c0400305850401e0300403001222010360700784407041c1075607641d40f5413a0091452658180810480080030480901400070b1030301002000d8506140303400d003000d11301489075114a050041c14820400641e0f0444c0988089070010f0905d0f0702c9030308694000841c2c002c41d80c1c00c4035502210210300c1181640c0c0c00105d003d45100c4050003009242c036508400b80070046098001072140d03000c1d0406000003941c404485402040f24000451716042c0180510450b030000c4454200003020081e0400080000601c000e0b0440000d039000c0071941034645802 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 47870480 1250 47869230 47869247
    0xa0209060703082a031602010c09050f0a0e010e010e10051008150a030501021c05042a12050d0e0603090a060b0f030609010e0106050303040b0909070509040e060417040501 75
    0x780c1488554000034041a08040100c4202002c04075107848504c22201c1404441d00b050302c070020a4440f0030b00412445005101d03a10381d1586a4950395a094a00410090889101a2140e030441805840029012000d4051034042c02091014a64941c102a41c48807643d0004240000d40300510004001c540c0307030841103800b582181d140c50307006503849a014002040509200036084500400000180807040d4003801c0c2d02c014404000045d8400f482070881900d6081d14040c1a01181e4002030011107030311101480032014050144100940d02c2981034503200c90042e042d6195040810741032140c0c0d41c441c110100c42641118882e05600b011000d00303964041c00040207054543d14003a10710316980c0e03400468683d100041c110b62076850081c1c42607019101d540c805840e50744c20048045034914012040d075054841c4800b040c2e0030504180204020284050003c00c00d20004000341407040d1070300d000c0c944000383c0003001403126041510300f80464101c0381e4021800c014003401f051005a9100400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 47871730 1250 47870480 47870483
    0xf0312010308070f210e0d030905130e03040303090801050c04030b0402040504020103020d02070305040911030610051305040606030b011818050c09030a030c050c0303031501030f11030108010605090a02090607 91
    0xb40792140d5140c0750440c01495004000f421500d03c5d036425803160041113400a41c400180d0341d50350f0040b00c1d00c1003800014525040001c0c0860070310383c414440380c10001c290507548041c1400214048200d9a0807e065030301130740064001500714001440700d16024002c2c2d0b50403c07400c0700e015141030700e1a1102202d02c000600001d118940f640d0110f000e581c42038040d1011859040800c41da503d100e46400703000c40d48035120303181586080c01080d510211101c0192403203600c020b486401c130010036035001c540503841207420f415449000702010400303407682c2c031a03140649a5914005022592040050b10034110040001586101031005111002c161722260804000c0b841010600751586542c440260280d030070016050b111307040d1040241548421708000040c003403401c0c1c415a9030343d001450744034031080b44d600c205a401c0360745460043d4400d41c041140412200c600040790142111861825807080e404000f10342e44a690902c200d1800c61500c507001861508210715007041c100100d22540107a010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 47872980 1250 47871730 47871743
    0x6080c0609100c2307050906010507030f022b0305100305071203050417070e01060c03230913050105040b010507020a06031d0d0512150102060c0d06080609060105030f03120103 77
    0x219940d00502c14001650350101480700d290000b498180c03900031848011821394410310000040500340816494000c14069641070314100c40790f1415100813110b1002502103200382086421200400b02d40340803000c0030115a0305002503011b10080c2a500c0250035100380002c45a400c1000510024104041b1038800c0c0c4120f444070380e14117064540d405154000703041015803400c050b5180c0c0d4049864000e0f1400c648444505036200d05c822103000401d40401808a00402e12401e40c0080b80101d40b0071047c2407500d414035080802c00404c04c04181c0c0025101540e03180e134018000c52405009140c10304d002071a1540c140301460700003031130751360309803092509060340c88003e034140501100d0440c0e10544903000712020503403c01d01c000c009510070452229200381d200f0100340d0b80045000b0000340c14605900819080d142c07010343c3c103210351020078118800703650303280b00090140c02882450700c40c0120310081c0c0010743c50842403505250459400800c0c039002080690061610740b0b10550550341c1100303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 47874230 1250 47872980 47872999
    0xd020c12010f0905010b03010501060f08190f14040203071202180a02040308040303020610060e130b0402091002161e150e040203040506040201030f05060a0902071115070606080c0609 80
    0x10300403401800351545120581c0d0400d0300ca4000d011054000c04840c9000f90000c114aa030ba400782140c9603c8000d030340d08001002d90000c00c5c002e055104201d5101e00d00d0350000a41c240680c48450101c400080b800310b20b54880800304000e51405202e44c030001d100b0708240300514000c81d800200340c0c08480c00108054101c0d200410045d2074140c2c16207002e1580001805c2e0b0f03aa8070b90401941d0340e88112084402c2c1808944c001c10101e02c2100484000c003005081c10780860340e2401d054001c0d001d00758615400a07820b0081003255075880644c103018401c580c001d400c61030445242030284181582142e460110010624a60f00809512030000c40d072030001840308201c1010011603071000603040c06640180040240000d020005c101030b80523074403d0f00c082000402c0c0e0352030003041c2e03001100c200740d0048050314100001c0044e03400426403d413203110311101e8001c080000514070096140052032041e000308010081221503c200c4000c0c20000e401031802490a00008025110700450701e4000c3c400f54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 47875480 1250 47874230 47874259
    0xf05060c0309030f210f040b010603020a0e090603120f0903010501050306090c21010c05030601030506011107061b02060c070503060c030112082206020102130b0f040302010804020604030f230d020c 86
    0x81c00c4e0b040e4030065601c00700a01c0c0c03d080c1d141d086c82100554040d02c1d5441034100001703010703009108907060868a92142c00c0c290f0703c14010000490401051603806000c0d462180200104000080034441512403070b40d03480d41c508000b418215041600304174081c2d172100e4180310400030001000559880111003454807865260505240c0701c0140007105101d6003082030340500c5941103805184030301c600380d800b0861903231024011911003508034450b02d8142c010b401c0c1031003114414004004039a42c000d00d90586068181e0100e107040e403240005508541220700c00b80b1451806100b0726402c10f114900d00c900703550400d0041c90b81004452002011003c001400e00000f0546400f0038402040c00403404406c65070b6494042d0103035009010040c3c1220300c105010603041281000d03548040003285659040600310360040d112000042c00607071740484144800400142c184000c440030b0b234400d0a00220032001061911458215104250703616041006d84810700342c0c0c0015038516014088039800000d81c42c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 47876730 1250 47875480 47875507
    0x50403050706020a02010204031103060412140f040803030108070b180907030b0306090c010e010908120a090503030f0a08010e010506030f150d050304050a0e010b16030207120f05060c0309030f 84
    0x74410010000c500200f070740b1880c280c0660242040701e0280c0080300f809044003081544402044500400c0072113000550310690340700e94442c2c4205041ca403681c030301c0c0052894940c4010380082d03000e58904e900000050110000500ca10001000c0341031011342481d407041c072420140c000b0301c051903019070075400019409602c83c0e004130400c101c001c0d0a840300c0d410441034054940803007000b03c1d804500c25200f51411540305002d0181200d01d488080c280400a41541c28050f5010208181c20014802c1002c502035609200070030701024400001c540c0c0314441c0002411400d0160300c401c48009141e0f00401c0340d0384801c0100da501144a40b200e440c650b54134540704080d40116410160406a010004810880000011310035244129070446907107a0f241c4490b072440a09000d20441c500051183c80c03a080c1c00042c610f29194424016905060340b03038524450145480750080c0d0302075049002000a000f8140005030b00801020280d62031444d103490031907580c0c42954400400c1c500c0006000450321103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 47877980 1250 47876730 47876737
    0x30d0b0a030b04060203160e06070204110702060f120105010207030201090905060406030b090c0f0906030a140f01020d0906140402010905061b060115170103053406020f0c0108061305040305 83
    0xa0002c2100390604243c14048002c0d0030494603650242200d5076408142c6004503203c2d60442001489585000040e90910000e05007502100e030743c3c071100380314580c0181d84000c040e0003055000390006d91640c1c07030308584841046044e40000d0654000f6041400941d900c10010303020f407403072b078030340410a601c844021400a21203a0b02c043d041041403070600c000c2400200e022004404111014241803001500708491040169255030b456440010090005048004800104071108090b41d0230b4161001e241826640110540802541c2d03903643c0d4410000c82d0b104010100800c1c1449200e280340650000e4080b2007176020303031882441e021548141d440c2d403810380c41420b1a290001c2c4c40c2c465035a1030034000e44010901e50b107004124000003041c2c4900c96081264126900540101a00350784500851030049424002007010b10b6042030081c503200501c0e00410090000f540100000c200311062a4140f0368141c2035941001269000c0c4140c0c1d9944011512144580d200000384079242c5140585a922 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 47879230 1250 47877980 47877983
    0x5060303070c06050a120204080604140a05060109060e16090b1b010207060507030e0d0c030e18090a020108090c0102070302100c0c03081e090108040308060a050d060e010b0301060305030d0b0a03 85
    0xb8542840400c2041d404009800000015120b107203008080b084500181d005902a150b500e501c01c0000070040b810301309030002c0108120042d10750140164440c01c1c20400c003604803c1015441303440400403900504542503102c0480842d601000400500050026616200301c40784424003003000250b56100088141c41c1d44009802190703202e480c0d00c2c041c0050101200d0711004203140240860302407102003141345400c455603690360304407100c07964190b402e03100c0b26020903084a40c5a4810680040b41341c01c503800b61401d04010051203203188001003d040004042520301e030842081c6900c0d598002401c00306a17a4103c807018112040250129200a03c101000c1c005108000c000001e0008180040800c0084242d412644041e40440300e0401c1c420f140d9080e0003d10041e0005002c0b9110f0095150018801044011410394440c001600309004010590701241d65000050f5407a07403d114007810941c0560003030080c07600d1a00d525403240102c001c4c0e008500d4850140d41380742d9031380c40542c3c009503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 47880480 1250 47879230 47879243
    0x304080711010e0301290a03030c1203022502030d0306080705090c12070c060b010206010308070201050c010905060901020a090911041509090203070c0b07030908090418081602090f060904060506030307 88
    0x101140e902440d8851b1600e481c500d180f00d8040042a01382800151403040c0c80c0c2584440d0410300300360369044443c20b001c01d500000c140d070902260400c801120000c06c0031203001000e1026010490042500b00304000349000c0605282010400604001141c028110782c030848bc20b1015550354400d0360014458a084941c24807a200c0c02c00c10700e25000342e801e00c903250180c0401c01001c3c0803130005a03030300c10007804054143c3c4c1041c02281c00645c880c20080c513040c0110800416100c040344d40b0b843c030f041000e40b184400c42c0d4010034000d11095000e01d00400030081e914062000054001c520140c07849580030b00807802298400c1c1c03802e8517000d00700800c01071002c403c045680b884c00b480020100007580750200c42e202c5081022a460383d00c20300038030030910b4020b200c49142603001010400100202e0020b100d00a0303d800035000840e40f41000740c42e104440b904201c1400038140f0401001c070740c00501308021030340400107105440c0c079030554060740140d20460000301600c4407000240b41d07014006004002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 47881730 1250 47880480 47880491
    0x20907050c011e0509120304051005130506160e0409020a2114101d06220b04060614030a1502030604140a0609050109060303210204030804080304080d050304080711010e0301 76
    0x3d6007807a4000340c400d010b0f6406603200c0703040c4102d84001522042d2000741240d070094004402480d50755201c103810000d40005468070a100b9a0703581d00b4260f0803610500074a4644041007051504060704e0952801e00b200d0820bc1c4510344d60002c1d0011900d0701601c09409061080c00d5440e8042c203a0200c2c0060f0444d02c0c1c00861300300d401e2029655510070841c03c4980d410500042490000d403000106500d040700050314072a520130407403903c3c6120449401d541038415401440205d10710340101801103005a0b4041003203805e00d51400301548801910a000307074041100312001c03d800c015001c004554025001d40d41e611040001005019410382c1116a0740801003030003a0642181c0c13112084a1090b0814044d5a03611032041c4119022440041c000c070b2811007000b100220410010402800c0b41a401414161603442c1d0310005d42058010900319440040c0610803501c0400120003010031a103041c62542c54141d4915420f8014104014003000c8902c0840702143c2c003500e070140c00c01002a00070080c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 47882980 1250 47881730 47881781
    0xc030f1f06080a06061e080a1101021c0c0c08190602070c050a081e1b010507060f0606090e0108010603080403020904020406090219030509030a20010f0c0c030e0a03020907050c01 78
    0x45c15907105003d11440f00c501114a151400801c420031102a076001d803480201c5515424840c02c1007074120390460041c070010f01c03010039602020505001d860398403841c0d001240d1506401c1e10465401450403039001c22004052000c41441100203540d014101684503021803130b0a8101d440244c012070b03406000f11201248040780042c4205a11100c0094691140601c1100b9611901500600d036020070900c0c0c4420041e5024000034049280726800024a42c01d4802d6014202d81142c0c005100141808034108440d183d4101914051722400c0020024180342d07030f0710615503100394880240140a8100060190b646a50000d001401d8500e0295641c955016215004201e0030340d403003010900c1d00d40031400b109000015940c2030541512141c4180c0b014402070308010742598909245992111610305103c070b8280541600401c00d40c9400c4007440d5140340240984607a0003038907008002c505810009641c80808498000e035a038100b40c0c1d4cc0c0d10f04080d0700d07809003e0380002ea04c0b010011003100d18 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 47884230 1250 47882980 47882993
    0x5030901121119200601140d0b04230c22020c0d050d0c0203120a020c0a050d080a0606030b0d0602030c0706060f060e0105031005100507120207080c030f1f06080a 71
    0x12031902c1c1984d550007050f0540c083e1125030040d141070010080e408070b001400f03c00802d071100500140010604010781c50b441c0d0b125422014200c1d4200e404003103803c00d140c1003440c58025850380300d40b024040e1145440c85000f042040350309a03000400c1d48910035421319040c8990341124050200700c0d0a0310011140b040c0050607a900ca4040441998500020b0f092502d00c0403094031541c00300304103140c200d600c82c100503802940041d4079020303281c091500400700140042180d03200c03d01454841c080d00d45040400f440455959901c94420301d4141081a18280d0703c441f28035020700c2e13114400580340c0e12544101d614900030f00d0703001804a807500c0c401203050f00302440b040c0101c4486a50312125420350000441d02408195045018030100c042d06005c185000c205c2c03060746d0f1181d03103000f41c10b104940c1c50380956403050307840740005604400400c0c40105400e0100848590050340100541500030314110f9442c911102c42c040c0c00c0d03800004c0c00240ba100381c1c01c958002c050340e038100c80340f0401e00e00b03000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 47885480 1250 47884230 47884267
    0xd1e0605120111040e09120711040506010309030203120c0c07030f06050604150b03090c060307050a03150501020a140109080c0d0207060824010e060c071d04050309011211 75
    0x9115a000d40340c41c0341181e205000784081c480d1603401e02821300b480e01700355821600c0d010744000d4241c02a040c81098441c0003601504900d40681030301c403040d000600034401150000b51040741054140100c82000c40c0d000400c075204910081c15880d495640c2d00b075806818050ba0958403098002e084000082c01a0611071070307003150140100b0040d580390360303003044200c680146065000005c2000200040c640c0400075550100030001510407030390010b40003e4540d402200d100010440128011071441d52512821690040090700b0745801da0030480080d50301d128840d00104514a240011042020207400ca646504d80c081003c1d40c50f039002c141d21382d0f12045a003030180014442c3d0f00001078000d03c10030105014031520044204608050141050312155645c1320174107021241d0352120781512010002c000c61062074001c0c01c1c45c1414207103602c05110b541400d0070714116101b400d000c0400e5000c8125800048242089140c0ea6a109654000740c400000e011010900119900340c00110903440b8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 47886730 1250 47885480 47885489
    0x6150206090303060a030f1a0708090c040e030d02090a030206040801060e0702030a05070f03030237030b1008090a0614061f090e07050409060b070201021207170d1e06 73
    0x380e55855807144526a80c03400101e40450b804480d02d8000c0022841000e48940c040780590b941c0b60250103020400c7c1800030007510641e001174201010808d25034000d0000c070620308400c90713003070000b00401400e07180e4038000c05042d20221580022b0240860755410000d800960b4050900b589441d5140242d5000307200700c2c07250100c60b200e94000034550901c040216109034840b62502400c2c40340344d40362148414031151041742415804c0001ea8008052600782c080c644a1080200060b00b2003002001d0850300c0d0f10030360006150515840d522035684080c04000200014505011a913842034945894614a1039024041600c0e01c4000500380c8850144281320301e800f52002620407030a01130200c40c05d4183d13040c00000585c1054148081005021b182d41c02542c18900981403e40348d0007440101c4645030b022156024000400310115601840020000481541003e00b080e0320b03130b00c1d240860f40c418951841c85100002d07240c4100c10659000340380c80403111100c0001d4103219a001002008540107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 47887980 1250 47886730 47886733
    0x605120a1b0e0103080d06050d050106050a061404051314150306070807051207030f0c0203070c0b0301050a09020a050706140612010c1209110303070c03140105061c050a020301061502 80
    0x100724090003440c03922482203030540480d00c00c60f82c0ca19258000b07950840d400c0c2d01142502c0d200001100d42c2c82200d10b406c828002ca0002401d146004104030742c3d0905d542c000e80a010900d2485c4405c0a039160035201211415510055507020f80407008000345151209a0141c0c0654028420a0417100070000ca4901c4c041d0300304c0302107494030101030b01d00c9401107801e10f0015204009103c01440e00d02c80b140c2c2c0042240c02c0c04208a40c20300c082400b0307540c101c001600184c2c004960181400800b180e048002c0170343c2d40d1b24515550421000c2800b11005000c2d10404540001300b0070140c2d44184110b900c40e0760081d000300051802048150b8011509454140c0305500c0000e40c5042001e040c441c240741d514070f80d21500711300148109403101170091400c050b255561903074075044268801380000d00342c0a1240c0403811000b81140740c00404102994804a090383c5400300300f2035a80c840f2442190040000740c48420701040a00e032141c40c140003444000d400d5401c0170381c00503207038013400e44503c0303000000c1c0c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 47889230 1250 47887980 47888003
    0x9040203042105120420030d0203130506031302090c04030206130602060601082e0509040501050115050a02030304020607110d141002190810080d1d0108090606060c010605120a 77
    0xc2164107005610b0b251380c0d4110b6000101d80043d0b000e001a071110003440c81c1a6100e2a59080000d00b4031401c40600c0002d03030000a0201c414607904045030b005018111904d40c10350904611480f5507544021001f400f4800d9000400d10b810012410340c1c6c010341d40140060303902e01610204d05c10602052181001501c5004007080fa95070217071015902c10310102000fa00e4a4001000201c81e100310030310740c03810406200b10046055240e260940f48514020000400ca43d45001d0540200d074102410328410048184002c4000c1c0340d001c01202d411a8040711a241c481c110740c107207600c8002c044400700d41d0142c03d002c0d580c42000141e00039800340041201c141c44e950200032240f0b506a11401e28410f000180310303c200b10007980160f03000c0740c0102d040d0306840301c80c588a1600c20310b08001040c0c5c0c4c8000c50400c81280c04011a44240900c11104c00e10308009036080c0007003038650b541400b51a0b1071045078041a0401a04c10175806180103002c001c4c24000d00e203031a060082d84510303c1c030f8402d841c21f04001c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 47890480 1250 47889230 47889293
    0x30e030607120b0f0306091501080708070e07090b1b06010501140301090903020c0901121106120f0711070608040b06040903020303070e130504030f030c0e0303070303110904020304 79
    0x455150321850700340e120180301c180a140310b04000c04071140d1003540442504c86041e0203440030080c56104207080c00040c000850811141902c03540f050f4013202c40d0fa40f008a0901c4044c8003c03411030125582c02074503090a444002065440c2c14031b5810010b8419004a611403001804208032a40b1003264401d843c42640c130342004440040100d4144516104100010084458181d010f40c072058000c0c810b4842d00e11b040e2000504110084c0d000300c00043c1d94800c070b0024400f14181080101d042114814a00207103601d5401d00c41c50000c4c01000e8550303c042c00201924004c0c0c803203c142e0200720b03040e51080c5403200c101410f00b400503241a208a51680e00144080c102440380c4003450781c06400441c215034034030504035082920b0280d07140c3c109480c450b2612000045000c2c0394082e610a89407054070340c0798810018212030040b00c10318101b06880501d4801900c02000310381c08039030180f4021030714003130380042c2101501c902e15102e5009407001040006000c010440f00e00001011610b1000401d00c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 47891730 1250 47890480 47890483
    0xa060e091b03010b01050909040204140405161202130504030207080d0504090e0c0609090a06080a120e01020c01140a031b081602010509070b1605010504120905030f06060409030513030c03030e03 85
    0x25402d4160104004122071007507481c294414649c841e00c0100041800440112043d007500c2045c1d0f0300b01d920358091000402c0300e218011340c071b0340030340307903482c559818103d0381c2d00012498180818060511540d82000c075013850300c2800f4a0000d40000d0040300c3d10650301c200b004150b80d00503c03036450b140380b92501c40c000308203000c2540c2c601d004000301080c1c249039081003040500d030000351410130f04941e550400a484003050281c0c440300707800346025116801030030a01419064041005504641000d07031007984507030300003804d00002c0f202c1200301030300c944150505070010b280001202e60f0040b002e403403228140d58080501c81c400e0380220721500c842d01a000099099602c1551001c009410144d0148581d00784440503054200c9000302e100c110032080d03202c0340d00b1505c042e2000d882420004441102c056044990078008260550007007811102030082d903034450303d010341981e1049403a2030703401050521034829030383d0b15810441c00d95030566403803403c61503240782448202e01089100d442c0c0b1485250 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 47892980 1250 47891730 47891741
    0x304031502030603071502031201120b1603110706060501170c0f0306060d020d0b090c04030302070e131a0106030c082205011b05030f0c0c03070b0a060e091b0301 71
    0x1805400640e0090311540000003a420003881d1a81620036100c000600c504840c0c130342029010140c024503942c1c0079503c03c11140e008160090305112041903030070744c00200c000c2d07a00342c1c4c440341260040e2064801207000724003a00821100c10345000c00400c0d400b080c01490350046040343c4090f200e411005450002d4400840c004846804101100384130050300e074000034008640c040401420346103005503120414040380c00280c5024034250b0744002001c0e050405090340d503000400054243e0601e8510b84d0000d556004074007c0c40070b210607060101714982d19000c031b59441541d10040625507107480e04c0310018218002d00c5000d0009040201d000100d0f4081d40e00b95005404408a400031071607228010440d0702180342c0204c030550341c0c80782c503410740c5603848000c61200d0080d40d0381c60f03030780f400d200481c4801264040c11500c0c11401c00c020310302d0134403800421075001c0c551060600d4401d8ae5001c041d213004007004c0d440400d520180c54100104104045a1400041c1d20500d50034803d9002200381400c80345d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 47894230 1250 47892980 47892983
    0x7080c030a090309030807060c110f0d030b06090418060522020906010210050a02090a0503010e0705130209040203010b0a0314060307060309060216050703030801060201050402011e05070b0c031503030403 89
    0x1080010404850380382d0019000c05020b8201000d046070b0b40d50b2802c0c030f290310154007600c41c1aa107546040724580d1000d2a4240508000c0c000c000c40300c04804910380702d020540140c000c0c0f40e80c0c2c00008046d80c1301c20b070070345401300c400400c00c002c461400d000c0e214044460480840307090f403030a00000c0d5942281030f09100041d642241d00380e120a800d50030310105070303030203440c980c15482002c0107888540e00c0c81c0036080c0321310411030025032901001020310120300080d070006072203030341440883c94400380d0024240b400c540040301c240c21030b980404100d100070300c07500c1041a0007500000022038000790130741c01002427030030a82e0204000c2da4020501c10302c0c11416aa001d0f4150000081000041e2107074109000381d6004680c0186488600d07504681c01d66a80380080300c03e5080041c4c20420302d07800401c603030700400050000380714030b103000d5000030103a440341050b00c0010b6513a0488480828030800a540c2141d03800f406245030740c2410310b610390740d0f41c03c1122440010705212070b014070b02e400c01200b9a802c89 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 47895480 1250 47894230 47894251
    0x7080a0612080a0c061a01020d02060c09091906030c050a1e050111070914010806090d0504151407060b090a0c1407021f0c030e040c0f0c030926060708 66
    0x65190340c03074440c5548042d4a00042001351006403010030214400c815a0058020803200c0041403440060705040401e008802990080c400304186401032104598201d94101c84101ea02e90b1496920204c0c6e00226910098051400b24080101b12032030320000c05486084502060721683c81540034201400d030b000f40a40035030112000c0080f94051f80044120318071120941e101e803074441900c0ea0072944400d9001d54400c0c90500100007071030060001d03c0e08141c40030301030b00b5508402d41d00a8054843c41c0f00307c4486240e00d1401c00204d5200d0500720320070264407620203946ea030403420000003400c00c034000c16101d10350140100e00c89010a120f15000000d650715015449900c2c07034400215504101e10030b07604010742c0c0752030360030b0b00d492801452400ca08a8661846180340c5003401000114840e01042c012450658036895954000800c201080442d1401c0d0381c90092629003104c0c1d44500358007442d0822a042940c1c070103c0900c01500c00d281d0480c4046503c1c81d554150f00301c407403520555250201 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 47896730 1250 47895480 47895509
    0x200c010b013b01030b060d02030f13031b170c0f072702090303070812070201051501080a0f060b0a02032101120f03110a0c08010b0f01051b010605120607080a06 70
    0x24400303400b580401d200c4141000200e2540c0390001c990140d01900301c03018060b60000401004049525219401505003491303c030b644070403554050304ea040708030a40c1c06400c490410950401c1681100110800c0d0b01c411001d84605042c10130540d11681ca50284107180205603021a18440461000452000540c0c00000340c016601024000394022001180c01d808100464004628407170002c1040c00f68107030280d2031a00c0e103490000c0c00c442d005400b80702e03d11594a0880b07201c1c0c0e4005521508040c0c0a40d000413007413107a44050008040d00c0d840b00182c00d0012417100840350700800900b2480c103160100800d12403080e0340500c9542400d009480e4260302003d14040401c4d01c84500901171407107400c101d9400e07140c00300030034600260400c04440c19110349406120340c400a002d801c1d519502502c4101e1411010000a4500c1c082c0d02660142c0307081c4d40451040104e82508640001d10340a44041480c803104051192074001c1120307500041180500854080c094620510b421100c00c1045202d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 47897980 1250 47896730 47896817
    0xe070b0a020703021203070314090607081804050405160b04050a06030b0604080303010f03060b09041a060312030c03010303080609090a0209101701060305060702010e070306200c010b01 81
    0x496400a010340411440381000120050301c0342c070641c07480754810000450311045103180081c03664002540c46030784107105025045d5507840c0c81041d280c075079900c28000703038550042e40304000051010540c0168010b0501d01840700f4000d0124508030310705548540005116100c951481d030922582c8212030b045110f000080010074420390121740500001071032940717001c0d55070384264074603003080c1c1264000c07180c800002c004002d07552003035080c81081510941c0040c5001e8482e41c1c240ca90b10141c507001e00c44a42e0020f201e41e5024004840d800186110751501c80c1400705005002d03030405d000841c041110100854103919284540034859403116005000aa90310360074410313608000b070915081c5102141000c1083c86401596140d40d20f5414000184c403491821312914200010b004003082d6407401000011841001c0b4110066a805c0000414090a0080c0e45500032140301890162000007041a4080c52410340100220410990b9640300c8001c0c1c5c4c808030101d9884044030498196001c1f1208034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 47899230 1250 47897980 47897999
    0x6020703020609042322031205091204030b06030609070302090403050c03160f150203060d06021c09030f0201060605030f01030b0a090c1404060e090c210a0c180e07 72
    0xf80c208015001007460440280b01c915030101c40003d4020800c003100422041180085a50304071051381d52030100c01503040d0300c025144036a0000e000c2003044d143c1e4002102c50000b0084455030506030400d050380da075a00d040c118030050050352118401d020b510b0206000250014031b01c0103403500100720390942d85030790350152210746c8180003003059400280582030002ca286882e0105060142c03a400040b003c6501c4e1581400c14542c8652043c10310510034098aa21002d12980c15190b00c4140180d4034040d514080704507030500082c0c450550700f0141c02004051b4803c010070f15442e1541c0090005e40d0b220001139402d4041242c202002e800000010404528158090b07500800350b16000200c60805860f010310f1110b4640080407482d18111161449040c20302c103410040c0703a244000c5c5400d060a20f403803500d4200c44100303984207050b410180d0151010303000803400c082d02c0340b5040303030100381a03850400007600b043c0c0b061114001480d4007810070504280a5011401c0d001c0340074240f940d05180590 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 47900480 1250 47899230 47899237
    0xf2107030c0e060307050319390f090512100f090b07050301030203031206040b150c070509040f0201030903050d0e061b090a170a0215040807050d030e040c11010c0e100207060207030206 81
    0x808d003035070302d82c0c03000c1020001c2c0341c1d8082100a0510b002c801800e2154a02c1580158003089031020042c00c4101403440581c40a9100280cbd0b00464cc040c0604888101e043d1400a180010040c1d05182070110320b000400c640c0000d074118031444d020303d003594540b6020341c2e1601091001a405400400204103500c006c00f22465210000401c0041d07501014400319210b0204240914064080020380580346041088568000d00e0b040741c40868a02e00750717954880b0b103030003058000e042c03644680d2000b04250003001a034191019101c07040105c2010406401c0e5030340e40c155020200007a44032000da0010000c50200d03a03000f8809854200c42c203182070078000078109075042c03c4030700b409010040c8006035a007040030307480b00009603031030742e2036034108011503040c40001e5103c14440d49008244c0d1700000d800460300096203600701d40c0000c1c00c4004000964000164144071101946803041a590403078000e140d401c40e04100703562a2101181100e42660765101900608003d603100360410030051809200a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 47901730 1250 47900480 47900521
    0x803060603040c030602070b0709090606050d0e0f0307081e040b090d03050d0905010204030204050c04080604031206030c12050c01090b070b060303071b06020f120f2107030c0e0603070503 82
    0x3480246580c9485e02d50490304504803c80d481c0090710144034105034020b0740360000e800d000500b00b00c00c501d45800900103100d440341000c0450f80b114240c000c040360610400400090381001e40eaa00d04051074500150740c40503842c0d03c8003180c078001080300000a80300750303026203e4426030140361060410400012040d104011410803408015148000145014280f08107210304005030316070b400c40c8100011382c1d034028210b03850b01e40306000030407c1000010b07100390000d4043c18081e00c60200c00070400f01418481c2c1000d0000d01c1e00410009070307401c2189045034017034000c9082d1526440058011a459121071049080341c00b03051044e000426030044049d174018500070101e07031420403035580f4103124003e23150001ca507003100c84d2800c022854041c01820030301404440900001c0c00090344100590182204c4030200c9000032494802071050144c2034040040d81042030402450509001030113070040c001380000003030302d2071400d00392814110182c9000f4103050301e6840c25651801055000305000d2400d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 47902980 1250 47901730 47901743
    0x10f0306021303020406140915061b07030c0e01090506031c0e061c050907120203061303110111030108010c0e06030a020a050403080301030c05041d0c0f131a010f0903080306060304 79
    0x2c0000050740c1340d01c5004c00500c8054607480398641c40e50204501c5410081c10910f24100e044c1003440e40396102d0040701c004114422041d20240700b580d0400740307000c0068100030700012509801050f0000240c030024101c4059500c203004a80c1d03068103150321b40c02030724040f11400100340541d810032070080c481c09100c154060450303401c4c403008161a900b0341c0c040404003464540d691050151005041c8100d001420001c0040c0c468080b25034007003903603400003c1c9030f01200030310f02140380100f510401d08000c0320071150707001713200f060380051444025038000c4c41600017942c42c100703903500054090700b4481d400020041c020307415070b40c075007409501030741c00100103804200b401c02c40440014003402c0614061030151101c10803503420700043c04219284802e41090300d1001c5e17602003c4074440016a00901c0c0c0c0d094480100082803d0045808c2d8010f4000c4652414280280015901c03a21810005212400da9586035280d40030202983d003e003050001600032201000000c5144c00c1000065410a203d20b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 47904230 1250 47902980 47903017
    0x320010e0c1201020c160305060c0f0d0203060d050a1407081203011401090302030d0f0212090d0201030e0c1305100b0a080c0a02030d02070b0703050a0b0a03060b12010c0215070503010f030602 84
    0x206450401020345469000e500c0f06c80c000f0710600c4000c00140754800c05001031903180a0310181403800a0050303801900740f41d40c000001035025101c5420303002105500c841282c00d03d00701440c041c1d403009503401401c0b806204161300080c09510000d061502105440003071480d50f401c104003ca091038501d5410f505100f0710000000040e00d0410003c0d071802c103160b41d45d185890301074200030708016440350001301c0b0b50300c144040305450781c0700702c40240e0305682407d00247c00300c2407401c181e06040e41820079650050380400d002802003160b4100522503000b4403d0000800c0d22998a68a10300604100c2c00c0043c00d0a80000c05030305074080200090340140c011a030034110300000712380982c2d0100c0f40848005003003000340300b07509405000301c642080842c0010312407032201d2000300e6000d0901d0300c00948039076103076400482c0326210381d86040802e0038410000d02031081c0d40d440180d9216a210311003408040d00d00c00003003813a0b00c128240da0513645c01c070411850340343c5951182d1003c0d4000c40000a030007000e44 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 47905480 1250 47904230 47904247
    0x1008040609120c0303060b030103030e040506130e0307110301050903030f040503070f03120c0e091f0515071e170d02120a1b020303040b011e0902070320010e0c120102 73
    0x210812403050b4100d60390324806000920300201a203c080c2c0c8004103507803050005000090b01310240491020b0180c40004041c2d0320100045c1207022403260741d11140e071074120000703901c44003c00148a024001d141403080507215805060032280d080381c000c03d881d041880800c01100640c0302c020b4002d4060801c40741800010b44400c1c8540700020340031004100904600340041b4858000c2c0100c80c4160f0600102e01d02c9290301040c00f800e00200b02603241c0901100e418020401c3d1840d40d400b61201034042c1c02c840d240c403088055075601070b08040d2210b94000c0c0c54991140b5104900c6d90300598020500340040b11010b01d149082c0e081900c031032404c07940a00c40c2194818044010310f12401c940130000c10403c4102404541c481d4a00b1200341c00c41d0410801c01c030129099100c607504503000b6409075104648501a0032103000084d400940c00300b0f000161000626500404a9500c811180d44181902d10302485070b0b4201c88000740300c507200340c11404001c100c03403909440b0b20f900c048801d0000342c6041d688 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 47906730 1250 47905480 47905493
    0x304020a08010c0302070c120c0303050f040909080a0806061305040902040906020c010501050a120503180d080304080304020f0d0b0601080c09030f0f102702011b03031407030b1008040609 82
    0x10312580000290317000c1581710a01c40040d11120044c400600e590550810310f0312159240fa00d1070002806206002408040a0705108210b80043c1040f80040000e00032a180c440850340c8000c0510000a2110700499400e00d01030048a807200304046540900301d2815042c0400707030001c490103a9005603204114004075110b4002408001031440000601b5030420b000c2003200403158010988002c03007020b101c00000c0f4000102c1e00c802c40b21194100034203030780c00300294803459104402014080301005000c20020144082d602070f501c22035500030010300000601902d400740e228042c0040c0b2610380814125406002003d420030703c1100250300d0170310844080380c5044140ea041650640c80310100744610003051200217203610101c041401101e061405216041d448880300c0c51032040904c05071021a03010302010600c65600304288400284036090141c010003c9101c0c0c001e00e000fa11000801d4944170b4418401e00c420b000b0b122a0f4800b406007021640f07a41c0041c402c84100c0d507901c1041021419 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 47907980 1250 47906730 47906741
    0x5100309020604030b040b04050d0513030b04110303040807090b0301020a080106030f061e03020108060915010f020a060c050301180603080d0f0b030709020a021b01140d020d0504060e01150302150304020a0801 91
    0x11f0170032004142010f02e072443c9094500c011000411105005105c0c440500203100070440e03410030304600c815207c1e800c004c2c02d054951100180e1501c000540000d0205012600310105d6500c10420040d841c0300006241c2030707104030340c07101c1c002821200051203024004c1c0e02100e46403102d200d002a0064030f41c02400b0300f480c0d003038214140c0d505c03038040d00704119a4000030042c1c0c0210103490551450414040d40c4942ca0b40201c00181031190600f01829044e100300310070610a6041002400122821a030143c000da000b030054581e0840b1000f00341c40b100240e405031004890f440341d501841d001d040750011004241780c2c0030000c82c05443d01c0303110031a035400700841c07800b4140c0203030010f0b615101c0c001c0c0a0b14100c1d0780559070052080c01010005503a0300600d24001d01500a0b017040d5950400c01250383c000d204a42c00385540c0d51070a0f06000030b1008541c06120300869100080101c001603921030820070b032103131000a600408004c41002902c001802441d0090301c00780c010b01525440d5400d090075902c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 47909230 1250 47907980 47907983
    0xa031805011e2009061b072601140a020315030601090501090b03150a020f1b070906290c0309090c03040b01090207020105090f010e100c05010f02030105100309020604030b04 76
    0x80182041800c14440c40340301500300d03480c0881c680310707007140080321480e0043c000213502c0350324007050000404900b0014694080741e10002d6032425070f2200e10000041042c40820900b03c61070440d1039124100520030a650103064180307051b901d9807011441d8001c1d50006042403003010711b40145c440d082d103003080058003800d82641301090780c3d8100100101142d90b13a00b4664800c2c1d01c81d0083d028219002c20401d07800c00189140569078011075010580d45109081c07072040d800300c940b40b045512000219145069448002e003d024641d6184184142c80c055008407103100d440031868081481031a0005126174280b48050301c0c180306840c0000380261004840520340b501c00001004104109914410701420202404508049540d00024001d01410459a0044130000c0c41c0c0407003a270290920803003541d070051141134024110f0760028401d42048808446560074158456400a40c42c000e4034145d03070026002c2e080c8000401f008502501c0107c400f03a8029104110100c0800d420f04591031003a07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 47910480 1250 47909230 47909261
    0x4020a020106170109020a0b13051003050711030301152609030703020f010908180f0901080a020102010e15040209100e0109230402010503010b0c0f0a03180b0405060a03180501 77
    0x2074070f0203020340481c1d101030b070b1560309913450030485000590300c010400703003907686003180241c80d4850030111424600c01c0c0e03002980d00100c291f031450803040c1d154100300d1140341540d0310070054240b40c100290340d0f0b02007030240c150211130942d01658200c1c072030640c4a4941050300ca0700e9104103070b103400c0e801054809440301100354000080c0d03402859010011243c1e500c85000081002d505580c4902da160701801c42a8120701c816031915802c6903aa1411060207024000c0c0b0044132075a54a290b00d03521030f20301304100d0265086c28014890400b000c540c025450000c12840407050340c2c4c6900308030500c0c070300424484021148180115500725011134850282051034800505000d250020b40c181d0020403243c03848403900101048010b036404420399045841202d5100e0310384042d00c6165081041b50013810f503c43c49515414414140e21440780408503480aa00c5c494080e203401004180d031089001d603030b40210040101790740861199010681114041c403031006206041d581e01030075107490600c054101d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 47911730 1250 47910480 47910491
    0x501090c060c170c062d0c04060e0d05060604091505090c13020306130c031806061a07030815040b030a03030e0c010201090507090b0102150406050103030806100806150904020a0201 79
    0x1c102c4600c001c03104801140c0c540d02c0c00d204c030388605140d5800d0010000003e0b201c542c014280f03103603a0b220242006201e01c0e00c4200f070500e8180b6099075160050300c80c2c400040d00902c3c0480380703803c1801d0612120307034004001c0c0040b03589110078032005e81031100080310340d500881408414400030340b0915002d9102c40000d00fa003143e603a804c102c05001d6602e980d03450103204109101f0b203941c07070002c0d00d04c103450302410206981d81c070690300358020812100118203130022000080104503565001c030782624045103600c0e46030700500503010800c1c05409801004204100042003502200e608880300c5100028004140040c04001181c141910342808030007207903d401c444d00440c1028004604d001400784001c200c016251b49802d65100c02d148070b1140c0184e03444008005591090040d000208803441e421151400d2130300d01203001300f20911096000031014400b00e0001d16040b0080f01480d40d081d5242103068941008214400d170f01100d030661a11300c1000605180e48941c009070844c00c9482d00000781 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 47912980 1250 47911730 47911733
    0x7050a060c09050916030608010c050d060e01080d08060312040602030d0605031b13060f06050409140712020a020f1906051006140307090906090504110909190501090c060c 75
    0x699140d0041d90341403010440d024001030f100d03580160f41c0060b10500035800e003031104070194010510340c2c0011a01b9401e00030890305a6070004000c200b407000340901004010307030700c51001985100c05c0c0034120340381c0c10041a0302e0109205050b483c1d00a100142502c41c504600b03400c44240350b01c9036009002603000410343c00b81c0709080e03101c5d10000780801c0d4081c1c00d08c005038480030304640c83c0140310b05110b04448520900c081d020f07a8084c4001c3c000d55030788903030084d0303c1d008042d05c43c4e0018440c0004003820448907030740740c00c1d025240a0103000e9a44440680b410100410800b03504441c1e00c080c1140700d04007400030f14500812068580076a4669140468030721410458141c0f0300c000c01c0704028140c04101004865442200090382820900d0019225104d1070400c035007078000e9a01c1102030a0518101144140e420350205001e18810180c3c042d030545600e06101c03a41804650021164219800d00007950382d501c0108451144128000608507001d540e4141b500040c0e60041000180d00720302410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 47914230 1250 47912980 47912993
    0x90504050f0403080a09050c090405070f14010f0518150c070503030f03040b06030f0d09060f1e052203050d020601061103040302040c051c0b0a05270c040b07050a 71
    0x15040005416024807928054a000c1d00c0d07124080d10304600c8a903540b40600030b1007410300800c0021940180b00381d0650a0a05049680d0b642c140120400314810704000164602d402a4030108480107840e03120460031008416030307180c4c005040304030100a540d081c1d43c40c5503540e1880f13811200c50300d1038200d40b9a21120300c1d1516100442c0c0241d4007a601c20001d030f0001d420017006690380540d10a070009916540e1001007800c11003d0405640e00f84201c0143c00000c42d0841110b07800c0e01c0481d542d0381540350106400711806070746040b803602615405081d04810610840013410110111455001651040c5510002c01c0c9050341c0b00759565040002d0030f800142d814408030380108210700d40031454051841009880740714501c002489250b039500184c036524059005d44203200c3c107581c6420303c4000c01c86a003001504c0d0341c8078014407034100020082418079080f60880184441d00d1110808011010301e421034242c0050f0a0141d8124107010020341f01e03200d000100780c00b62068003d401003404510303161 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 47915480 1250 47914230 47914241
    0x9210905060a080a0b03030c1509060601030c0c02090a0e0f07090b192306070614011710021303050f0709060506070b06010309210f0809030705031c0609060303090504 73
    0x40c401c0c80d041000e014103076400308440b60848252030001070720310a4240000c0ca0761040700914001400780d00c129544900003030b10034038130541104065038665a10000110125410a90424045210024468007508248000f140c0c006512000003803040c00f805c00300c40c41c04012501526040e40000c40503c5010094014904a01c005480200c01040300d07040100c1c082800c0d010795003170b03403050204902e154404250040125080074000580e5401d0609054000e0816442814000c0a1013070001580c00c2074480b01080c00b0341008003030202d801d60b4004a901960201d81c1510080380c1904003c808100140103200c10003940400034200c05140c110b1220030303030703c00c2d85c86a4032075035050151038042101c0504040e4030107001d02e40000e048a403890305c1c3d084540d401c0c010340302d150aa0303245038030340b41e80000030400d01d01459154032140361358541100741e40c3c0c0b0500130014460b8105201016050640300c8080b201c0205c40c4c440441c0d840d86400c820011100e055000340c00040420000300300710b0406100d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 47916730 1250 47915480 47915489
    0xa0b100303230a050f0405090103030914090411011101140129030105060405010806010c061b02010b03010b130507050f0f041401021c140706020301030f060b01170c0904092109 77
    0x580601019030381c1e00b0191409061400c0e0709001002405d400440c896100322805400c004241c08000d5840e0b00340241148154080c803034482008000004880ca00944900e214076440500d06012240d140b0045440182440c0d04c05502d40d25140c0b043c41c5840c6d4629280d0180c01440008800000100954032601102d0080c150849000300014032440d12280215002c5d207030300382482001916000012101003141c0c140107401245807070710560592003601c803a0840905164003d115200401003014205c07641f05400550120f0f00d0103e000f20a04990800d5a0054240c02c0c16810031240b42074014050f40514180d86105c03400060034030161013002c13040c1c00501c400b0f20040818021400401c6150401000c00600f88071321150302038422705d0b0290442d1b280a0384040c1c259240d50796490003042c5000d41140464003035041006000b165403003852060504040b2820804913511402e100f4041c1e540706040c0150000d890340a550040f400c0740b10202c1c8010301181c0303040013101c0c42040c01000e84506410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 47917980 1250 47916730 47916767
    0x1207020c0a0305120319050a141e1603090b070201050106021209010f081b04030302010213051504030b0c0d060303080f07020f0309010302030903070f080301090b190306020c0a0b100303 81
    0x7018008904000b6190342ca8590380303d1036070b90b251a0f2079101020482c2440c42da0001074208805c0025000b03550b00951940c3d10100c0c0030521544502d0300120700b1003413080700035901741d03180c000003010303102d42a907169802c64460a001400501030340302c0301c034544400c84d00b050241c0e440d030004020706a4100301d0016251310200c100c03414070a40310002016085c42210f0241002001404501843c1011035106140048860016617440d03480c41c01070301035080104005515001c2c00e0000170075052260010101d5007620318054905400c503600c0e1002401c001c1d0102034080d406006030f4040311541e1041b08007441c080e0300c9078a02443c2241241c803644c0c000070603c1045401420703003010415070004c03d84034001d03400d003005078032a5682140989036001300c8a0107070441703103800d050f003090003454401541030350020070b02407001000141c14001035002d04420780742c4070240960308101051869014210140c2d42209503101241305483d22041c649080d601d0140d49250380000b041003682040700b02c0c600800601 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 47919230 1250 47917980 47917999
    0x30501060507020d02010e060c0d170103111203040504021218010b0109210204090c170304050d03050d0b03011515180605030601050403080a030609110c28081207020c 73
    0x940041881c000c6040080c0200268220ba20841e8000c020f1f40d40002405800c540d103992840140d166111401255034022402d6a520184408201c4900c0350681c2c0c3c01c80081d43d2195001c0b814071034034170010070000d0790a010912020505035604c1c001000320110309080101d40f401c08246010001c54405613960303c41c1c0c94000d5550031030344c100800b4011512a44002e244514091102c0401100000b2000794040c0c5410040000c101008801d001580e0046250700001140706120b0340d5680f2417405000e41c0040c7c0c6415500010303110f10006c010b80c000c800d8021802008000119081d600b041a40c1c00d6010b504580c10b100b54404401a001400414504120314203120007a9006843e804d0040c42c0130804004009459a40204122401540d100015590306c5000140043c003c0c00940240d40400741440040b01a100e4200199902c507281e20001d00450301d8030b03541c8480c00200600ca03a211a0100c0c410310004111000e004d440c1c02c0c000441e40107001e18006c0c01c000d04044001e20040d01c03c940d06c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 47920480 1250 47919230 47919239
    0x2070b010302190801020f03090c0d0302120912030c0c03010b010c0b040807020d02030616170115110f03040902030a060e0c03130204090212030903010c0503060102031c06030605100312030501 84
    0x2005403411280c05442845801495442c40315540700076030000d26241d800011113103403000b502002035100e50b00320b206541244104108101c04070640e07080c081c0069000c00e090303409503800c00004004c40c200017801d0307144000300f26846038210742112441c041150002d00d041000741c18280900c0e0098042440c0000040a04d9550400106000b60024020b014003080300d40443d12081c40d108000d603001822202c10f40760070311061840502c5000d6141c002a41040306008405200c0c04850580e444011080f04020f00190f080391300741600311038104240700340306102c100c020003800180050a9481400343c0e0b00e1030521400e5003070b2032260340b00c4641d480a000420161706511001e8941240c0d10f0714070350302c00170840c1c00000c0c050140b401c8013a500140304e124941c03424100000030030100c4002c3d4001d0068105090f41955580403c82d96540960001c102c400104680020b42002943c2070b04030029100b900c0b91244001c503001150091050b00766103605100740517120b81480040e0b85946014001903051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 47921730 1250 47920480 47920493
    0x60513030f06060b120114030102031302091905010f06020606030304080d0c0609170403030e03010506010905060c0f0f03030402280b090619081905011a0705190f03030f0207 76
    0x54440503001c8180041e200d001c00801c1c1d0842d600800c5450701d00e0751180320755040d2010b00030081c442c6060000701250700104070704060080c3c1c7c0c4501501c21380d4200e00c0d01207409000d0b20000c01031030511000c40340d0881041100d494817a1070b01810121401d0b0704c2150030050060b14044000d06194800c1d1300600040240d401d0000b4244030310300007407400e0040c03428a8500700700940082500200703100b1681c041030103079060f0403000e001240d0007544c8110b04680c00c007040c03500b2142c0503202c6074001446002d05000d03e0400f00018440d841c520710803246104005e21440e810b040c80c03064403503610f4000005100643c50300908034181d50140c82400d10240d07080c03c0001400c680306e88214820040301188180e0b05607281c1007610801031307000c907031714100c0205000000d02c0c044044400b031036500800c88849400c10007071305c6258160394411848038100355240e001061190011a400c9803980306021102c11101d0b0171020b02001c00e8070030007510000c0f151616001d000d842e0408102206240b0501100010451 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 47922980 1250 47921730 47921767
    0xc0f0a061107090204030f031407050604030e0d0204140708100b0316030b13050406050108010c05040509040c030f03050c10110307030c111204090c03060e1503070302090412090605 79
    0x141810201a900c1c0c80300140d60030b10316154085514148082000014019207814081c0307000d22039aa1012160080c2003070a2007402141c10140c603a501040002340084d0041100c48c0058600916070310042c241786d400079082d01c0e4050064904d40f1309000c02c3c4003d05802c03048464000c01c0b00003035001124142400c0c1012404000e1030350311792040601101c0401c2c1e00aa00c0a02c0000340549001008803040d1020005400701391012aa428a00400014885010701c41e5007050000c41e964645450303e01000c110641d10702900940300c000350004000f000400e4050038201551013615000d84502c0641e98250400d0340c0240398021032810404060080398080d0103e9038490950701b400100c1c0400650202c404501003140c46909108031900703500105410710140c421120052000c2c480310300c0182040f82a981a441542c0c102e40442e00404c0760455a5028035060400140441302c01560300d40008400303801c2502c0c00c5e191522420718105142e03511040d400b018013220f0400034900b41095244a03902d46 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 47924230 1250 47922980 47922989
    0x111e030d0f0e03121512061503010c020a020405270f06090703030906110a0c140f1e0d060f02190215010503030a11010e01020403030e0102060906040b0a050c1e030106020c0f0a 77
    0x22440000f031842e4154100c0104421000e00f100740001081d00421f81c1c0c41d001910810000b03c0380e403044120b01e2405001700e29801d40d441c0d0207004070300400d40c24840035140180496050000310220344c4a80790a00343e05800d140031910080c100803070101c1140c0d0410002400300f40c041e801050040c03000c80c0e001618142110310514112915404c5250100d0422525020062410842c1a00000caa00b011041d0304164801210703491210824142080300c29003501c985c03a01c2c1b400d0700451401c03462420304241c00010b4000e0501090418090428500301d03800741440401410050f4419480240d04014ad90141801d4a40c50040342d41007100080c1d03240684003081c0100400b0005405030007401b0341011105420031380c000e54840d612460080c200b80c90b0012014014403440c400a5100400087c00a00460304140c070542d560315076941c14805000007d2401a0040f0100880c070070300005c80089a0099807031545c1d003622541400d400070304020400e60f00601c61030303008070381410603522550b108003100c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 47925480 1250 47924230 47924257
    0x1302040e04150b090a060807060810170a05071d010b090a030803070314040507030201030c05031603020906210103061505060306040b03010603080c03280f111e030d0f0e03 75
    0x1010710030440b005011071404064120301904c042c0501e200481d0080019a1140c1054038201510b07803408462180c4225418444903400e4902005900b1001100f14101007007c0c2c10f5450314489621990b1402c0180c0d4044654202c8000c00f00a2494903110000e01404906800750b151207000030009040c0c00d65800701400c690380002c0854007090080c5c0c405d505480c56402091018a07103410001c1d00c5203210300c4240e01013420160320f60b03141842201268424000d44041d01d1409810a40c2100250004456607400920401031051045c910184c85204030444490390030340317503040d45032190560703403030520100c094956484180025600c1e40e00362035100c941a100050f00320903001c0080d000d044a940058182100040c07042d61041d004001001501213404100120030100700810121141c1d0045005c00a03100e211782c540c3d414421000603410700e010070f003124074204980c981214004082d15007e862039100180c1c04003540c801707000b000001c21007000c08001c8017040c411221b480c0d1048090030b4201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 47926730 1250 47925480 47925503
    0xf030f0c130303030207060b03010209090106112e0b030c100503040c0b0301080a0b010f0b0702010c0314160b0603071d0a0623040e1c050a0e0d050c1302040e04 70
    0x200c100e51054540040095048660340e90340c0741009002540003020668100c0e0404004c1c02903818140200c4848910103003000201e80c1c40c1c01422244a44280309071101d034001c40d00b548140070f030410f4111500c03002e1140c1090101c88207a40030800c850105514074002d8001d51205646a600e61190091100311410619620fa8442c6803c160003546504075002d014404000482c104000080c200011403040c1c082c0e541c287d0721840044c8094880c0c3c0b0481d0305c0b000007004250010752060701c008a50318030a041085e1108461100e0141c0c6400c4058107020800300c04052000344031090610a0f08a031098018101980c100b8410242046028020303640c480030301004140607414a0380b00380010010310540d030316062641101c10b07403c80c80700c00e0b22610035414004980ca0482d40420780300c0103803041c00480c0380302c0d03503207040280c489e504a8001c0d2130a004026035800500e48400e241d004d403042c4034002800342d8544010801a11050000d003041046105010600c0860030031340783c154009030801c072460750 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 47927980 1250 47926730 47926741
    0x9020708040504150608090601140f0301180308060102011d0606010e030709050703051501030506010c022818050f040c030b0406110c010f05010b0705070512150411150f030f 76
    0x1030610540e8410741d04949001070003030150800f00186405c1e21407580e500111920342c1191181e903030b0006e0180381c08094900400840c24500310309402d10910001d4000314060100c500031812940312804140c001c600d082040000030b41c4c4c20300c00c0040300b40b29070940d92040d6003000c030381a1380c1c0d07400103100c24180b24810030f0b040401d41e01045510000d0241078800e1241d1314104c8002400382000b51544a803a00c84c1c02c038005003941c02070244601c6050180d480c200940c606c3e4080110400c0c0042d000e01b80380b650103510784100d42c51110200084c1142c400d00001e070902042c000c3d802c8400042110749200d280c2e800f4040001d05400c1078070110f0303800c2a103450850310346041c507400a09849140f414020000a9a00303e100d41c1900140c0c3c000c0c22512007001075070399500810105205101005180c0d401100e02800246400364486030003000350000c0340c28003c8465031102d204e401c2940c0c1a50f26002c0c88142c94500d18001c480101d6032501444a24100120103070441e0aa0101a15a40000e200040020b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 47929230 1250 47927980 47927993
    0x2401020f060f06030a080c0d0905041b180f03050f0d020604020a030b0c040f09090203010c0e1507150504030930030e01030e030a0c0501060506090a030201110c0d0308090606030f0304090207 83
    0x10541174005c4606d6a4800c00d1007101607a0303a070300b00c42e1803020814643d000610f92400d40b1414414136000081c0c0d42c0100c05e101c004444000a20951300580c0c100c070000803540c07181001d81d04002d184540001c02c561032000d003289103070042c0700440400b1540124208801a203c2004950440390301c502103015035122140d001245004a4001034210440444005200c120b00d030019121039000390f000b000403a8040c01d00300c5d210f0036000803913900b0014501090151506035030051500c90301864280b803500020141c0c0005845084d1019000907003001410711a905100d60200030300101c043e007854190b25401700144690f0030b0807002606104040d441d200340f1340d019400c136000e4011244150703a42d610050b400503060201d52401500d0662800d800442c140c03c0c4101140e42c111001400058490b1865004680003464122100500d0040d03030078004241d282d07070300d00719400e07807080c1c5946010313181c41c9149918102004200501c69070110801e481d2001c4041700300c9080d41d518450260b40e5462600b0b000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 47930480 1250 47929230 47929243
    0x6121802030c01200a240c0503010b07020406080106060801080f0604030807080a1808040f0504060815040305120a1d0a030e040b010c0507090e0601050a0305030a030b0d0b2401020f060f0603 83
    0x1340b400e02071050643e0820a50b6070030a10642d010310092400c0b48070401c0d003071085450b041c0124010450400041c0200ca2115010f0000148010408515191035040e05801d40d803455000d10007040b01103006020b074000611a20740000c0700302e4010040da00e407a480080c00560058924400d1001e03203004143c1021841e08006210900102c2e4244045030a107842c9916a0240c0b01d0040d01c3d4144100c041010700c2c05003c0d42c000c80344900000cac0501d1880c50b00984514002520450600004029005044202c1e6101621400140340c0018240c4244107880740103032803040300104240c02c002d1100f00085d42111a07904801c01c103940008201c0e0f103600050301e806078980030240c500d1056803400101c0614a030013940165801400740e0340f499071384034144541c1c560a408020029003080c4000341499100b51300c114003146004210b00c0181c40c2c90b0300c441d8124513065130009040403011112000d161400329038018030400078401050301c515a43c06a5844400207086213110140010100d0305030754040180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 47931730 1250 47930480 47930537
    0x8030a1a12060402101403061e0306160e010e13050417070c03050f070305070b030703020d0c030506030601050a080a170906040f030b0601050406090605030405070b0406121802030c01 80
    0x441c02441c00010003582d11103045500305d10444c3c1c0700e881140c6080c41003101c60880c00511008600f9902d5103410090040d062002c0c011441460200075903041e40e0030441180540d20000e041c4000c0c1e440000c1c002c007580503c3c00390906006641510f28600d403207224089180d910302c914000343c103498a03d80700c80c03184628601401982004030b00e25050222283c0c0c3c0b902203d120724200e81064403d200c482c3e495032000c1c407020b0300c01d8000100801603504030100a65004c0000e1600520b054400380007181200c06420550340003a90312410810541000c00282d405884101c1c1d03500d80c81c901d0441c1c119601c64060500400040300c4824104580d102c810564081400081c007144e110f81e103d90400802102d5480161030001101c0c0c00315800e54024800c45094a41d240d464503615420110241c1d100d500250080b40c3c0d6100317604000440c3c44248000c2d10140040d59540c5140e40b0502522005a954034216a28102e940060703010040ea00050101000442800e0a521700c0c6108403000811540c038248 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 47932980 1250 47931730 47931739
    0x724020d0f1214070324150507030c080a05120901110a03020702011716090b1809090a020301060609091d150c0f07030804061b0f0509030a1a0414060408030a1a 70
    0x6010130660075803c50b200701c0024421080688800404001b40d20010744943c0201d4003039003500c00c2c00503200f4002022840e0090510344082d186035603400d1001e42c0201030082c002600824101320b80d240701c40b0083c0c0c00a1840f00244010341800900052901c2100b00d501709140e4001842c80440e400b80701e450328807161515a0148900e010b0b80e22529442400b68a0000107d0415010810311250415640d5401000d05c0041e107004010341817000080020344a50b0780d49c4030303811000c00180e40c2400b80e2000f43c0700715552040254a0726000c072066880481c0e41a56001c1d4420303041901010001d8522540c1c580051001c03070176120344007188810703c103200810303106603000a0b00340203164001d820980510b00c01c0c1010080d11504486100310350410042020000e4040250003403a03910500140520780d60041c00d59803c00516550304480c9184103c0c050442001c00c0c2c2000144880101101724407140700c0050100f51400313581e50034007440000d00d013040c81d81c3d80742c110702480b031000d201c4d00c081d02c08040c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 47934230 1250 47932980 47933021
    0xc0908060109020a02070e010b160f0f120e060408100507090f0603050910060e06040e01020d090b06150a0f11030d0203010b0d0e0705010c0f020609030724020d0f12 72
    0x80450003130352003c100500940f09800e00060041d00d003108840c100c0e02392600e1641840c050694401003010b020f0402c1e00d03a5106010345101007420900e400701c800d03103d0f182440e0307400c008090203041e080070384034414403802092008001045003c43c1a1004041c00c05c0c002450341d07201c00e4281e032032031072540009480351210300000c42d843e030300b640c0110702814041c4100c032070303100c102034258059070f001c1e0150107101c41ca500046201d81c1401c0d086200c000c0a1b407400541400042d1200300c5c1107030320100d82950a9078049043c4040c03070400c0d950403140441d040c0401490f09010810143c500d074225950142007050700e8081c540400c0c0140261500d086c03c0071820745d901d582d9440d072091142c111440012100d45403440514503407900060182c11500c041c0c4400322600010380b5003a440c1000104181e811450070480d03405103640500050014010790800114102d551000190164071079000c040107550210409808568000c20031142640051800310011000b03559910007074088840120f04855051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 47935480 1250 47934230 47934239
    0x30a0f0503091203041515050a050d020102101505010905030105040b0417070219090e0d21060306050c03040308072d020a060515120606090414070b0307020115060c0b07030c09080601 80
    0x4c031a260302ca903118007e01c8080b0841e41580a452841d104095110b01082c44c20070a500300200101c0e1b00c01d0050040d92290322007185040140d49541c4084844100800010b0142d503800c00c04880203020150000c00403460143e45018200d20042c0010f0540c4a0440a8914540e40c40f030442d8640c9170302070b01a01d4601c002c102c07100c403807017060700880005c9030802103520135001000400e82000c141039520030241034105085c0c181c5085415180c0f07001551550004400315655004250107500002501643d034545810002c1c003081c0050f1500e800c210a5902d99415030780c1260b03120010104000c480a1052078000c4213030b251128441c4000e24250405d400c0024580a201c5c0030700360f0341410b030303044d0303d1b14a4002e1401d03841f0b02d401c40707000d58409a4800407801041d0081c407082341d0044400200c0d00502d44440c400b00d9107820858004005039150780384c080c050500c0744501d000810032810704502c1442c0b1561040c900110080445c003c042d43c0d00e5060360b00a00c2040c62000515031802590001c1d61103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 47936730 1250 47935480 47935493
    0x212010f05040311060f070e03010f23060108010317090d02030124050109060203040e070516050c010e06090607020d0203070504061d0c04050604060c0206040f0b070c0503030a0f050309120304 84
    0x49030103502151220300c05641148005c075065101300208042030743d01d5a6035100c161003141508210b2034040d96030307607696500503c161140d40e281c07070211102c840908034540090001243d0003017180b810000d840c8010000100c0507104504c6482500c10950f40301c00845020030882202d05802a503d5030a0031449001f05217041254080030001c02c0752140101c0d116401510113545138070801c4016403013004200580c000c0dd04441e40c011f10a450403500d4407020510446801c0703040002501e6a81210950002540c0c00505800c1e03050000d644403030602c00b00c0300004455002e00c031806800707420703203c4030b603021540c09008410182000420811901e0788940c00706c1e900e1442000040032403503103007020581d0070451030b094030111940280490702d0641401412204107480c81c000303d0300134005020200310b0000c04001200038184160609443d8103482c00c1015918280b075000e14040e4008021030052150f00c5500300648407010b0414680d02d445112040b8030f040814419410084000300c144010003d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 47937980 1250 47936730 47936741
    0x307150905070504021804050c0408010615082d060d0203060901020a02060906040b010b07060204030501110d1a090a091a0c03070f02010b0d0b04030201021b0c01090602030915070212010f 82
    0x240045942d100d40f14002d100481c81001d019410b4428407aa1200c15443d00d0380255620040d000f0b100d03820285e40e07201d0a800d50b40c4030f4002c5a6a500c9180001c0411076000c48400d50145141d803c1e028120380070303080054000b05120549104441440004601d515a85100403099a000e0101c1c2c882e03240c80d04200b4002e420841141d001405a64040b41c040440001c05900994000c1c4483d403899103080703d10149a400400304480e04c0b03409100010100744203100302c0503064048070005584000d603040b200b048031140345a1390501c1510140c0001152614861b0302e0b4012111140014000640c1c1040300d800402c12040d1801c114001e42003002102803003001d18020138403900d540b8003136045880140d0036568081170140c3c009002880c40004120400c645a41042c02800014a03003c00d2141e4641304011100340046c907503001050076070142d607022105034000c154a2014504003c29900040d0100212124207125010007141d040c0556a40e2103114071221401c0700200b1600c0c24500c0440f02030903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 47939230 1250 47937980 47937983
    0x7180303180605030615071b031b1e090b01050705030d090b0903030403050703031a09090d020615010c060e03120f01030606060c0206070615081002071b03050304060f0203071509 78
    0xd40d4500040b003500610136070380151402048a00c1d01c0408010002107500103450507a00c6020b00d4045e0016070a200034100d000e1400740848628510564030004070440aa0f40300e44294031401031420411101c0000020658840b24030204a00d450f01004071200c0c00b9041001d425030200140c04141c01c0c61582c048110103104d008201c500796614140c050301d0b4003086a020b00416000c001440c000392180d80024090500090442ca450030500049145000200c881c1802c0381e0142200080c8542c040199035840000c42c000e0040500c89040000c004003414000100300944480c81c4815105091040d114004141403105409181c185104c5a40324001e00c800d44409180043c0403501d184134401158407250040c004528060f0190b41e0b102c0200394855600003030106041d0081241d440030700034003103c02a42000561a005c06060060400312030840144e400b003580c03002000099000b100382d038126103503802c041c1d2401c90b10002c240e0841c4584480140058444c814891401480d030b1f001d80042d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 47940480 1250 47939230 47939267
    0xd05072c070f14070204060b030a1a121b06040815072307020607140106080109030201140108060117010204180c02010e0d050d0914010c1e0f0c030807180303 69
    0x251608141900c0e80d914030900600003610301003e900401c0a00e000a00d0460302c003a20001d03605a480380c1101c05a0000d42e0562502500c0d4139500c5603030040d10108282042c0c0481d83e02a442d0190000140c0c0c92216840c2a1070a143c0840c074a003040c0c1d56001620014613480c0243d4074407502c01c0d8020481807004130703031070804541500468441c444115403413810254000c504e0078900703000741e02007040c00d400103481110b4900402c5080c680450f028064240200192400801d104c0f9145c900a400d452092940102002007000104032000380000c1e000c0c1181d030a070326800c40c0a100004000d000e0701c01c40c1c0001030304a00c038542144100039940e01140c540a031560007002200009030002d500c0d4003000c40a80c001550a0006079100c03540b66100340c110b80d200700a03178030905002c2e035803c40c00d44006115144c08640303010b9100301c2c0342000c0036901c03130f4260240c5808920b090b440c1c3e8002d42144106403014040015190020318071501410342005803a910300303101c0c0a90b594a1600420600b45000801d540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 47941730 1250 47940480 47940569
    0x606060c1a070f0e030a0204060f050f04020306030303060603060a030f0c060311030708180c0d0f060501080706020303040803130816030f030605031903030b09090c03010b0906010804020d0507 84
    0x2003046a86200d010300565640c803003401e000e604003190203150b01d01402d5407600900c0e5044006035282c9c410440107100c1000d0303010440d4039200400041186a110642c0203600401c10054660b0b40481140e6000000301c0b0616203c3e180d900120381003501c82d0308024507610301e00d400c401c1401001c5208104a800650f0b00344410041180c005074180419940c040c08183d0101c0071900e865400d2150590b00600901120070001000000034003810071610180e0720038402c0c00001c01400514000c0030301410388440140b552074076091009580c0d200003003010b8048900030000c00c90400d00c1800e045c006607004007003291225140c05005180c40c0304100f08034086440e0390080340a045c0030f07000d140c0c104c40004000c0c000d992a40312880a1602900c40102e003050782d20044d803286981d506001a02032005030b4001e080c81282078060508440000f0003951290349004104080d81c0c1c2c3c0594100c1c5d001d075040d9101100c40407903141041c6040b4264101048409034100019690024460a0042c42e5410400400c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 47942980 1250 47941730 47941763
    0x218060f03010e250f030e0d0c05010c0801080601060518090a050603010b1c020111010204050301020c0d0e0d0804050607031205090307021503041713050a1503050a060509070e0d0606060c 82
    0x103451009130044004965007401100c0f5014035030071009850380382000301e54002032043c040c0c140610740328000702190080b610501484024449c81030403009a007003400c503950400c0032041e0b484005204210801c803001440c01031141e181e00c00b480041101a00300301c1682005049400617210464900e8080c0d07180216182d914501842c090b0030303107140c0c07100000e804101a001110300703450201d0040c0040d9020080043c158500348010003845444102901541c14580c0c0018101003010580c81c3c4900410407002e4046006c00080720b0403584200c94495450b6014601621220030f074101c06182d1038904030803c41400e07030110051900510840b4108030009000004c4080c6006c19540a04041c44012005245643d8000103020000c400c42110b6010b82ea07400018042e03034180d4010030303012032101100718416a014024940c10032200300f4184503807410400072803044100144040108240607a00800c1c607142d0480c4e0f2010303140c015005200132034440308081c0c4144540ca40458100c0c503541101c11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 47944230 1250 47942980 47943001
    0x1090b0a0302010f030c0507350307050f07060902041e0b0d0b0f0612030304120f02011a040213090203130507321503040c090e010c120218060f03010e 66
    0x56940c1611004c1001c20790000490003001080080001d00404008000c04545401014000103035000282d6420203086400401180c11a0490407042d84060080c8085a034000080c0c3c1d01e0707190814811a124245400d0520150680c98030294005107416440030034070f01011040d041400352400c0c180b1103004148240517600b90040005000101140b0105140000300c408454000304d0081591340403900141440703083d940162012100f104030800442c1d4880e03040f501d0301c0100d02031400204203d45036902c402c801c0207040c2182903c50707540041c0000001141e40c0300d19018092203802103440c0e180c04110a03920305003210060318141320b07401000070b10020041c4c02c0020050715442d16603039529020881d1968952260031143d1200390034100b0440c0c00174100156105a01990880d002103103032942c9032080b14454070701a291641801c10a121098000c8400c07400e0301080c80c0700580e1440c00082d42507121018184c0103511800000e00c60141035210006103050f1100c542404c69039454641c0b40c81c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 47945480 1250 47944230 47944249
    0x6071e02010f140301030b06030114070c12031a12010e0109062405150a05071a0711060c0403110a0503010e0d03060f140d02010c06061203020c060403080f0304050106030507060801090b 81
    0x40c034503c0104011300001e64010140c80d0020000b900104102c04090006041400211002e03400100c20700343c0c4906002d2075041400c02801241401c005540311040752081e50754142501c00c0c0200714540700289d43d030400358460a100540640200302107051480d0840150010b00324056481500150b0a506801c00c020380b0b40441354000c0c650794200480100c0070f80c441e00b19900754000c0c031105008600100c0c842030002c983d201511401311042d450501c5000d891030200f601c210210790300040c00c00103003800d45011a0b040d2034120b081c5044c048101400102c454503c0d130800e5405500303061003811860400288001083c0050f10140026521030361500d03804411441106030b51000c0010504040c2009032840e550107006242c402c418100c1511880140d0f00390340e00104900d035200c0031804c01d069040c03002031510102258100d00d05440c60711261040d005111408643c204008041420042c09610a000031a805400e40e504140c1c0e8160286c1810800d12070885080d050240d00e400d64980400380 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 47946730 1250 47945480 47945507
    0x1205010b03160c0507050604030311100b06090f040e150108070b0306030a02040c0c0605011517040c140105070606030506070807020f0709020f120103060209102c06071e02010f 77
    0x82c01201c0d20103840494010040743d00980c0c4a018514020403e91200802000034501070f0303c0e20801c294000001e5440c291824200381c1c94249042c40c10700c0c05940c1c0342c048800d80ac404070340d940048130320320300050000c1141d15803c0c1c5442c4245201040504c600c160759504032041e01003500c0d80700ea0b40d242d07652120b200032100c855241c0c0040704c0b05070044c5081ea01001c2030402510301001070350f807542e84090846074207820071400a1701c0d210b9801511a4000c4442d8054400180b020840742481d58504501740e0990150b01882c3c0030790000803029900c290103884009801ca074051020356520306081d500d0300d030141c03000c900181d07202e400581c0c0701c0e00001300c01c00c6c040c01f00d5009000607072400910400a40004a1000034103130204415009600e013941c0060207103000700001aa1034090004101c4885010125201401000c140f6402c80004914514402d40d40000c00042c85202860009034588101100182004402c0e400c200114200c900100b03030681c403e03240c400000040304800d442c40d40301d1102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 47947980 1250 47946730 47946751
    0xa030506060907030b0303070c0305070b090d0b04030201020c1f06050f090a0c02010b2115040f030f1b050615060f090d0203010207060908120a020301050a03080304030216061205010b03 81
    0xc41e0060611992069200d60240f038002418480b800019045500c244d50603160400501801e0051000900c6440010910b0003019898440c01401103044805030842c081c0c03514074603000107000c1c103000f034049039641c4010038140d9146035400c0e07401c600503030b4010f101010403900d004000b02d020f0074441410199010024040d207199074810b180080600000014a8115500c41e007800c81152140c90f20404407401000315403100301107040f9224548601c0b142c100c0000c503007640520011941056a441e046501072404c00845c07030144100b5106021000702c0382c103a8100000215082c45000700d0f109011303880c0601c07990910395a50302004421700504120343e140f4601000906c1c618900840b1100003244080d001504001c882d480380c40480e0110001601d686200140b8441c0c0220a0304003142e10204041c0708605550400c0045074542c441800003c14980c4008041402d041c000c0102e08800c540005100002c00d449400040c050003060501c0109107080c40c0012072080146029244203134000f04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 47949230 1250 47947980 47947993
    0x305010b0901140d0f0c08030a0e030a08040b0a0c0c0e091e0601140a0b0c0708060121030309030309140f010c03060e0c0a0c1709100c0201021f060e010806070e0a0305 73
    0x2040000c02c00300b20740201c0d00c03a203030b5045c0f810009540d616010700424082c00038586410329023030082d1440343c010800340d1107038004030905000074110070207640c2603c0b50003080315110b896800056601311030000c2c1c040c0402024250020341c0304c40c80d608003131191800d0410340e00075201c64a0300306010041042d080d12550031640060240034251800100320070002060094120b40e11100119942c2c046042744c0a26003240d00c050051580c10000540100780b2101da0112820701200400c441540e085402810541c5542c034030000d043c425000300c00065048805c9007205640400c40399521507810070300d07950315400c0528554035140203100d001c007111301c00180154156641e13000001035620445526040c440503010010110301c078a6400341045510300d11240c1da40c4c03500345c20084070b214902c1c044401c12800955110050740e000c03826405031001403001000f0a285941880003406560b001541580b16610001502000002d5124022074071604c5814023055450280015001e140c040030740a680030303e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 47950480 1250 47949230 47949269
    0x50a140a0b0f0f070b04030206010b07080a12110d050108010c0903020315070512010f0303080112031d01030f0c0206150303030f0115030f06081c03061202041a0907090305010b0901 79
    0x540100080320128007020310300f071001514000c0e01e412032481503540c0c200719020001015010401d1a0140941c0c0041d907081c04142d9482c64840d01c00d0300d0240c0c040200d404100010942035800030100039000461803070b203e00410340000e008120911a090556003461100309d41180224042000c0d01d4000d0040c0041c0403000402810340c10010b8071003000c0002c02c0003100c0da4111001e148601030050f00310610a5145541002001400181c000e8010036540c02c0b0503000294101644181c6507941c54201040f8100c1040141c0080040b40824003107141007610019a00e603021074494410003071950a02402901407007416580d0204407180c440f51506800103109900902c20f00300056003462801150711100c43c20040141c071182e60000035a80d00441c0316103004000c600344022004030501e0f04001c070b03520349060f50075100d0703035800d002c0e0041d0350300c6010451310400c50380300303004404d0064030125143c10248001030040c0010310044d07946501c3e05000030942d103800c01c0d040781200c0980d14801c14a4504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 47951730 1250 47950480 47950499
    0x9010501141804020f18010f0e0120061608010b04050d0b04150204030c030201030509060f150406080106080f0f0d02070501030f2a030c020c090c0a090e04050304050a140a 75
    0x11040c0142c104241c0d800c800c100e40c0d120700051254002c189415a1100b507451880201c180c0c0c40110103044c04a0f01305040e10b100d03070280e10052030080034a0403c40450000d25201c0d500c8602c07240ca09030134068202000b4401d40c01c045e5002c81006181d443e0440750b079a4114603001402103020f074951042c0001d12100c0410b240e03500c4580c0250044015210021000201000701e078040d51040300c580c403074108200195a013501c03840c0c0e130042d6040301a2a4034035005d0035a1915040040843d08050111251180303251a0b592196025150450080000c2d5840390000e6035100300f02c041e0a900d9101e150140650198007007002c0c004e080ca990002c0000358100f00066019110040c02070100035034400441080340c82116034418482c2d002c01d0001049203040d54020152240e0460240565000c04001c1d28540c44100701c5070f501c800303020701060b1940181d00e0122035910080c0c0c0404980303110740c2d00740418030070302000600440f481259005004d640e61500c81940113200700b111548040044c0c0200500100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 47952980 1250 47951730 47951737
    0x10e07050307180303020105060108130f0620160b071106060f0103110d0c09090908030103080c0a0c0303110714010509190b120604050c040e13030c0209070201050f060901050114 78
    0xc49043c18464031080072029041018141d1003900140c3d1038000b807200d65608034030707103c0c0c000c401d50030420300251054480056007144400c008140c20380d50420901110f4402c000085405a01d24240d81c0d20069000560083e0b80c0c555415603e50184a0200745060700550481000250190107480580d40c4c00c000c01541c09000341015042c15162801803180300811001014841d020032400110380c0d0841100610209050b080710640925141c810380c0031440c40003e403030450381e101c100151f40e0341c0d54402c49800c0048001d001801e030522803c01004040c3c01c6440030401c00700210481c0c0c2c0b0b00381d94002d13880c3c1140f8040d2089012403000c0040c6005810421024100c0044240080008599500e0310004603404005044640c50314a82400038900d4103008007500308601e00445410142000b41c0f0080001d4042c3c042c103080c4140e95204001c160240c40400207803500200303000482d1a0901000c0d0203090100c0c1d224040d002018006002403500c100846d05994040e9074400004040c1f640c3c0040550 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 47954230 1250 47952980 47952991
    0xb071e0e06040f0602010228050403080706091a01080c030d0f051b0d030c120207080901120609050c0306032506050d020c030409060503060901020307170c09122103010e070503 77
    0x16000c200104143d008143c1020091200c1e034001a5210302c90141c1c070090040d02031001c0751820103042c441c0c81c0d035644001500c0950790003800481e078480c402c1c988100109410740c1c00a0042d90f1110255646143d43c401260490b6032803002d56610182c110704043c1c85111460405012a541410b4102524401ca000c2d0031121180a11040008019403c01d0320740441c1e80c0301d82c0700007601d400e04006500d900000020f0101ca45910644c2040801d5603042418013072880c2a50400803824038040e00e604e81600440000c020f0710804028508110110b07954641c812a440b50280c860b8541c1d005440e040e005940c1014003019070004159810200100d43c5540301036680c0410a0b001d102c0b5850856040c03005000078110950700241503403408040c542030900c020288200c0340d00c14400c003c1c0300390300726040305607003401c0c07800b600c01d182e4a07035151810078001d007a80d02c4c6d04400140b03244620914005400003404402e46902d44050400380e859440c9840309000d02c47d40707410408003241d00c0c140684040e54000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 47955480 1250 47954230 47954239
    0x6070b06012006060a09060b0d0c0903060608030a0e180c0a120e030301050103050c1e07020112090605040c090c12020c0c0306070207060e04020412030f120e07030b071e0e 75
    0x305035000c5008070030428090b005403240c008405010715450400038060040241e442e0610500d460500c001646000e807001c074141d0f09888030156040e5606c0782c00f01c407010303540c400000c0101c50b0311203400903980d4000c40c006802058041e0f403003080341e02e400c1c11a00300c0c404180340c4000099503990312000083c0c018580c46020f0104419481c0e210780780c2409800e61a209000080d41c41c2e626100c00102500c078080c00500402e0401c009403100d400322840700841440e0007490b102d07500c0c122440100e40c038505542c420807000b8607100228040107815048070340182e005100524010303071070720045001c540d4100c40510200b40c0305100d607a1001142d07000341050184400c103076010180e08901080c01c0010440740c040041c1c0184105000d9107400099103691070600341d8085090030700b892001000401c841d040a82880403154400a0140c42145464040807050406204040384d074400d441ea43d0a103808102c91fa51007800004480c1ca200c3c0180c0502d21044078080c42d4640c0c80d144042d9000000d001d0701d990031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 47956730 1250 47955480 47955497
    0xb070309080c070e040203010b01110a0b06061201080a060f110405010e0303040f030305070c0602071401113c0109020d02100c0501020a05071b06050318010b030a050105011e0506070b0601 82
    0x2039a105003c00c00c028030300103a601d13140c1c0c5402e00c101070840c1c00048100781400500d210803180c01c900000d01081c010b6111002c43c0f03403a22200001040b600418080c21428030001001050760280812032149452051209200701042400c0c403038151003151a01a000100611080019620851601c000344074060309aa25007130b1140c25507140041c0c142c1040d008100d00150140400050b100440c00610036840502003040c1800340d848bc1d2251500031540c10000000506002e035a014810a4040c040d101726501150f954190040d03400112601816030005004c44148120407041c001c020039154010400f41c010181c81c1d0801c4150501d5448001c2084101054000000d600340b00400590303880d80c60712030300c0b4104c500d03000e6500b04a40c168142c110980740d0302041803e42080a5981101e484d009a43c401070000003d0703801801c2c01c00600707615201c0c5212842c2845410742c0b20710305a4086010720741c11070f00702c080d200007000450310035540c0010b010080100802c5031034607240e41000f01403400084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 47957980 1250 47956730 47956747
    0x20d030f090b04050706080c090f04020307170108160806010b04060c050a0b07090509010605070b07030506041104030609030806030609030a08040201030b120601090e1506120307050307060c090902070b07030908 92
    0x4200e8103c2d0111465808000e062010716084140c07951f02c059143c1c21107207800000d90108940c090300c901e2190181b500230003c60921070107041000d00381680e0440654071580e6030705040d41c1c5d40010394102ea0181403081c0700841d52aa0104280c0e0684044000303051800c0d181030fa007201c692000e40403d4407140210060395000600c92020395000e100107a43c1c481c0e04500b414100700b04a00181d00c05c806024003040140005002c4404103640b001c13050800041541d1040042405841714103101805020f000030003004109480d032050741d84a01a0fa5805050350380e2070103041c2d85a50654210950b80c0c000e10940c400c0d103100f40400355000e4818034010403500c1508010990401004d4000d089582103203006024442084c0f140343d1001c00000e000709000c079080ea0350115440400346c1000d008030103020307859038642c804204a400c210303031000c22681e44482d50b0030658024943e484d810400225200000504204140240c50a46412000d1500d0b030b070721035040540c0285a091000c685041c0d0510082d070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 47959230 1250 47957980 47957993
    0x807020a03170a02010c0c050a0209180d020609190b01090903180b07021201060f09110f031008070e04020120160902070303050a02031b1606020a0309030f02010606020d030f09 77
    0x400c51800b8000b440e2241c4034524040d0940e000d2903100d0041007002d02550000c5200000d0041020b50113860425040d1502c5a2034801c2c031040341d101d5101c40c424140e0000b20742c0c2e40010064400d51209050703402c00682450744110042e86401c3c041e200038007080040c84503511660001400078840e081c490002d4000404d0800c00316501d5000b0320b01128049150810750925050000302000028000c100141c100541034131440d001d40164504a9510010f0341d848090220445001110840c0d040c0e40360324005805606074005802200b0381070181c1e40c8001242400300810901032035050f1501003036611101140305444c0c000b014030342c0c1c040c8a819148007141c5051420400039259088016991392030741e080113010b465028120103007480c03042040142d40e000c5c01500f8074100c03100840c801d544404880c2400123041d80c0207030103040701d403001030410a0070303415a000c4c0d00703428441e48450081038200c2e90281d003200c80a21421015800600c0c60100b9141329500800078080b40020010700074506840c2c24 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 47960480 1250 47959230 47959253
    0xb07020a170702032103180106030f0c080d110c101b0b01081509030d111b01060603181104050c040b0d060501091a040312090504020a090312030605030a0807020a03 72
    0x2101075280001c0d8001941400c2c08881049170b00b16541c41e41c44c000c0300c5115441440300400901203d0103209246030345d80000c2d0801c0008517000f021a000942c91401c1c000354501161058034124860325401c088007502906800000c2e0b07e40c1c00182c4078070b500c02e00502201d244016010410401c1043c111030041c03000040700c01003075000311910700391356042c40d012501d031590215103000b070840c40d6410060080800030840300401400c01d404070307900c1c00c0240c0d445603c4c040c664000b03011604004c40c00e1441d40055200c04100daa06540502080c119801c5000b03e04050b16000b80031111071206060f61070410790000350b04544240b400c1ca203000c2c0d8642d170040c0d8580210a04e000c0540d1210b00030001c0f9030f4484d4a00c00074140902c01e04500400304034014000744140c0c44000c090000f00c0040307d91003805001003800614018200b595181040c881c010404061400211600c10096403042d013864824801c6901340ca101034001d045150941c0c0303608520340c10041c07049074000c09440340400028280902c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 47961730 1250 47960480 47960513
    0x31203150e0f041506030c0315020913020c12070f0204050603120a0e09010f0602030403060c0c080a03051605030c0901270e01030b0105190e07020c1e0108090d08040b07020a 76
    0x1d240d1500b854039080c0c1354000c00042c002866810b08406001094203180d20724116035100300300f055594001c0e991311000c0e02426103850350003820301c0c000d44c104000319001007428040500c01d90703050041000d07000201d402100005880442d40940314001400d10f030b41700c0c03600400700030100d0755904400f000e01c0061390703c8001e98000081400611005900b046444076026044843d901004941480802036483c09107100140800b5200c004850804d4000c4900b12000c90300316400da941d130002d42c1009000740c1005c1c0c4041a280700c005030f0001c180c5100710300b941d001e50b184100749454120583c004466800c0d950238003909403456070740515194503041041d41c00a03d15aa8800e6541d85581004040c1c490140d210038080d10940c15441003120320309506609035901c070201d0014545403001c0403440e01105880d401e80080507007070b14005001091003400d4000700d00340e031503000075681c082441e6151008402c040c400319095002140005a4600140f03034000e28520403a004804161600403408001009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 47962980 1250 47961730 47961751
    0x103060b121015050609090c03070e0603010303050301080d0806010f05180901090c1b020604090c18090213060c080a0f1101090804090c0201090506061507050601081b0109031203150e 80
    0x3c0c81856a24400f400c41c01003804581c0030341007160040114920303030070042007075646240c0000000c15560240408140325400500300a4485d81c41e40b0380980355500a0046082510840e0030f02407507140305511842c800c801c10307512240290b003444000d99441d004007804284034982400400c0b1380f41c0700c142c220717030085c54103180101c0d070b07401c0a074400741c25962655080908516910340f03900150300d90408840c2222072a1400091052408000f120701050552402c072810f00d1503e000501982c181d0080c048a008407269102c0041d030b0391f0420340300342c4034820008000d91014813100c0150b902035036081c200b000040c107003052018071920500342140c0d180c980c202c0d0600700100b0f085c00b0000c00c40c4138540d00610350340000c1200e0503458985954030400100041d01c5008801d5482c8a44c544442c1564600b9034040120384965850710600303a22845800d0000900b1084100941c602d584640e100800301c81d0031500107100c0500007141100608220b2900301048203100c40c0000d0902d5207400160f03c00d809004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 47964230 1250 47962980 47962991
    0x240513020907090f0b0d02070203010c0201060305060606130308090109050303040909060c0c050307141606030516030204180207060b0909030901091401020d05030a090f05030a020708060f0103060b1210 88
    0x410040d109001600901c10802002d00500c02086070391406420303642011211900c40d0700c1b8040100c0a44143c100c000e41550030100d00449580d01500301c1d000740c901c0f0724107445842c1d48802c2809060f00480c0100300c0f81004180c0e0400104182c180141880710061410301e9001d61141c012a245900c280c1c032070144941e0300d444900c18004240f181045184c1c003490183d014444c1078a40b15901e004a00c801381000b248072042d51f4003010204010251100c0743c080380c100c1a039442001800400045031020445103c0f25041c5100612910031079082d201250a0031400344010000c0c00000d42040700c0845101e580d031001410b5039a5605505403050303040100460303440464030001002c41074240d1102c81c000e619819280b9460703030041401d0116a5091400030b84a41c1c840d161000907045c001c0c000b42c151039040c1400d42c10701c031012000305602c802d59003c450070b079542c800f07009070380d02c404a49900300080240018030003c1c0d0950401941a4001061052120b50352185242060240c0b042694940e42d81c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 47965480 1250 47964230 47964233
    0x1e150613030b01060503010506180d0c08030c01060506030f040f0f02190611010b0306071d0604060203191806050313210e040506100305060a0e04030305060108090d0c240513 76
    0x22502e54090300451800b01d0071949402c010407040c0c001c41604000d0110884941d065549480b000c00c142e40d40c002d0080326240c0c1d96200101d880368030180030b0305015402c11202043c03d05007402101c0c09040c1045113854960740f41e13180c0b90030003a080a000c0362045409440800969240e49040c00c0c2c0380c040110304200c091a01601038000c42002c2844401c1c4e90401d9100b030742541e0003041865000d201424400150f401080742224201c142c40d031843c0c0c0c1b000c00810040b4480e44e000002d0300a124076000c00c070b107840307440110584a190000c0140100300c4084102809000e1260000e5070b00001c10075940c1e41c85150b00d6560042006406840707010201e085c0c0d0300e10100581c081c7d41d001c03403520190303402c000a0030301c9004214200c03210312001092540f100702045198940109000080500700310003061410070f450001c0c05010165145400219a4008950400004103801303107800400e440d070028000e45070396100741002181c005818407102107061140001c02070700409200328821900c1410002e0349 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 47966730 1250 47965480 47965493
    0xa021b0d09060e01020a0c06030c020c1905041401080705061803010c0809070614220b0a0201020901090e06010203031311030f0610170304061d0d08090a050301051e15061303 76
    0x104000d1304545c4611404004601010844000c0d10054900400c10081081c0d05914203241e20429039040040700586d51504440f1140d20020b44004550074800a50f403014080e1340b056007030196a0440c1c100b10f0040013140742c2400103103405d0500481030744110006d031002900715088064001c0124490780208038800c0014020103018000300d0900c0407002c2d00c0580d04400301d000c0c190440c0c485031220300301c6403000d20711140c0741c40c001d1001e005071540d1404c410000074040d402903024640420701c0e00c0030129880c00001c109621820040c0e00441c11650303000304c030341d968000180b82541c0324001600b01075400c3d1010b1041c1c0381d521281c5402002a810403e000035016001c44d03000d205c0c0854248004483e2840201c21581203503c0c0d841d0540b60303078141c00b608a089110118986030700c50000c40d600000c20001001038a011202104c0380381c0303829640c074241420703501c00303d64034030b009900780c21030740051100c0011540c0c01040b4001a00c003000001e0010403010b600c2002c0810135107010390810020842e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 47967980 1250 47966730 47966747
    0x2070f0210020303130b10050301020f0c0f0703031403060114040603060303020c042007030201061d04120306080d1b060c02030c1c050702040905011b0e1005070b0a021b0d0906 77
    0x1c140b00a6185141521003030041141d1014001c2000300b98401240600300c111045c0340240030b00030f000310360b6076503a00542c1105900450084506005156812800000100e1803c044907050780360320500f208801c04203030466000400f43c42c1030200c070303417858003240071030401a0015007000c0e107000444a0542c10064a4039442c900004d200d5800c100b451020000400d200c000704120281a064513100d0520702640505600d03007255076105181c04002c003040740458441c80c01180100220381c03845845100460503200d02d030041140300d501a80c0c441e0740b444c0c40b42007035040c60309219484030106520340c0d485030141ca03080300d00940107a00120302c0301e980440501907000112400c00c4541035544803048050194002c060019100b159a03d01c0c02090007020340007804001c048c06041186c10000c600e01404000403850b070396000300c051014000c00345018804881005812005580041d42d404005034080c0d030110500c201c04855103001440d003450100300d0b84000800c035031202142c25007005c100600107070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 47969230 1250 47967980 47968009
    0x1110d0f09050309010f021005090714010201020c07052112072f09040c0302180103050609010e0606100201020f0304060b0306100e070e03070b120a0501080606011d03070902070f02 79
    0x500e0468107078009030000080341c03818142070800c0d09150440000981c14020440d00070500c1505120402100050124030801600c0c050b28071460b07031302c0e141e2004900700c0c00342081c0780300503a00054041c04186000c10100c0404006140c5802600c0c495428950814a10464400b10f85001241100800204030a011400b100d4070021000070050a0f940380c1070030040003201809002054042000e000d00407100c603015580190100800704200c010780b04085400b440181d895008075004100c4e00d05060003550807041c080303402045580c4900c8100b00f0401c0e101c1042209565081042ca9151f6424001441c890344c050300000500301f40e5002810300740312004144402420b5540414010300504a507071b16003101051410b0550440e00c200860301d008002d07000201804404030305c0551543c00a22154842d800c5000180000d9a0b40d08005940e12401c1c0c0c3d81e07030701050303a04603a8610a03060129405511030020201c0b94a6540c0d034010300200d038422442615401d00160411086d801d02d07060401894 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 47970480 1250 47969230 47969261
    0x50a08010207020105040324060b0306010e10170c070516150f05072603180f010c09050d030327140a020a05130207020301020c0705010f020304030b0c03130501110d 72
    0x142d100c2d40000d00178071031030000400040840403000501c0406503000076504820620410141d80c440b80da88072544c108a079042d000030320b40300fa03904660404080c4441408090340719120594540b10b601c9813030510060070180031f40420301c108004240c08100c411b800605c1c006015001c241047c132140840204003a0305014050150f040216451303000d011125100d400c034200303640c0301d051208a40603442052113240b0b5030403008010b00c4000043c424034441008100c808490f0107503403100310700d426030306a01010070200e07082d43c008000d030781050044a03200911919000490340241117840001049a12501e030308800907140d50000c10074030038507046803405004001c10561281d580012854511070040d180a0300001a034004a044150155072080394010025510b40740e0031180c0c46d9807040203115050009448081507100d641c000700840301a6a0000c3c2d00307100f04c0c1e0301d09055052035030000d0110303102d8488407541c100106500303115001c075200c103440e0525030311030054003040701342d40070307007058000e40d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 47971730 1250 47970480 47970487
    0x91406040305090d080903070e0a0b1c020907120e0307061103060a170102070501020f0702030114010b0304020603070c050a061409190b060d02130501030b150303030a050402030c04021201050a080102 87
    0x110381c002d000d8a040340070881d000324000a0510341a800303801030720030719a01032082010118505016803c00d5200f201c10781c9040282c150020f0803c982c03460450400b240f4045071100480160404c2500c2030391003001810050005041c00d04024201c505d256041043c03900041403540400001c0c0c05000d610082c004001404e40c00d00000107050f0715150702c00d210804031903104d2803803015001e4050b94102e5400030000c5448100c1d060030041c2c15802800100d11a510703000b075810104080341c2d000750594180e01c00fa2429640c3d00c0e824803130700798005003a210074454005812400100204034621880b03208000104031075990468440218034090f040d10300c0e80e086204d041008800c800c42149400360041c0100d0303d03039110840440d16500c00c0c0c40010703422070040442549505015000302d4100c1e0b04c96582c2e8046e90341c07201d03240204010340304c500d142e06410400204213480001e800254000740010190b9030782d5a000d50004013280c0c40300f0401d88180480c00010071140c500b11004500420900000b940f5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 47972980 1250 47971730 47971733
    0x610030203090d08040311030a0507020f0111061902090a120201031406060702191a1206090f0f04020109080d03090203060c070c0312020102070501091103060709051309021206040609140604 83
    0x121601c03480540c3e020002580001401c0c58822982c14054030307640010390380c0d40c101041005051350701c004801d078092070400e4440d0300b0701c2d44240e200c901202100e0000d0916074540c0c0200150345a4410708000300e00d0f4082c04410969565101c6c4400240007400c04860000c0c8c0c0d034400502655000f02107110314500d60402c00c070483c3c071000308580303100d40d0481300d4a0700101e001c0c444000e035203055041840104070580d40d09502d80005402880a8a108a400041c555442c41006500c00c4c04a8000032a18100300100b42c84401801d1a41d070054070504002082513150500f540c50300c2c1c130715510400081c3d04c0d4000c1c0010760034240405a0480c00656000d45080c41c55201c2c04486d110034400140b24000715952220554800e6040d02c400c20360101c000d12003442181808904c41c00d16003c00c6210f4068000420f1000e4002c4111000301c44018080c00c1c1c81c43e0600301002d000300603151050707801c0031640440b0680c8ae5414449240b04134410cc000148510a90030440328002d02e51000c1c420030f42c4488180320 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 47974230 1250 47972980 47972983
    0x30f0510060c020418030c021e060702011101231609150804050f060408070c15140d020409020d140f5208070507020604030204090609051005061003020309 68
    0x8080e5081820310b071020540a1010134000c1007002e17020314035040619804002c05522041d240041c500807a1900300324080c02c0c1c20b41014412031401c880c2d10440400580e4010f50050354124418550740700006406207441c00d0310480c0044260f0103141d840e46860400c035400880261101441c0707500d2400740030141c10840c10030030320820720700031006210b138100000341013050070019a00d54075004400d503030060800d032a24008a8101d86001c0303918034030540001c190680340500c3c560009040303a0f1501d0100040c0c026003141d0780d200c02c0700d00080d56020040031806015600080c0413541d00c011000070503540f0f0610194000c0c40c05056003003d1000441401044280d00700c504a406d810b03503c01d00c9c2102c0030340d00c40c1d00c801c804d100c82400c0d02035401d01140291080e00c0304105071543c101d480d103400c56902d0780c1041701e5512071030100035404501400140050b040a0307002e0812079101d0403000504003c00c0d10f48614021303051800d84140c0341c45900300300c03a50614004217406501281003d60071030801c5c1c08082d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 47975480 1250 47974230 47974261
    0x10605031b0a03051b03010b0909030d0e25030b0106020703030903080903010b1f030b010503011a0d0906140106120605101d1009050909031206060a02070f090606030f05 74
    0x281d0350050100700c2510650340d400d445000456225086540100b404010007220503141100700e482946842c50700f03000d40c00e0030b10115109001c3d6001071840c2c1065081e141c001081d80c02c0098005119100507040441c6048cc0350050426503111200902c5203545407040440b40144c1103401150804801000041d030802140c0d42030300d6120400a480d40d0f030400210740140400d980c015408159000d101409255010701044504240e5509021709001c1c03500560710b511080c80303500c5001d2a4011103100256000f0050040c0d020543e801140c2004551500300542d00004110418610110300400141c0e0b0003624805075000d0120050112034503050018007844c4030031724070b00280040d20312040b13440081e415000140b02401030080d41060422a4020481c035007600891f400781b42c9800116441410000c16201103200410000720f85a40c0c1200340300c4182c0210000b002544500c8201203064a01c459a080240c904428000740e59490110003c06903010101c0c40350322180707040207000c007410700308950 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 47976730 1250 47975480 47975503
    0x901020c0a081c0c030501150305060f060a02070e2511150403020313030c14031c0e06070503030106031a010e1e06040302030a050102040303200c010c0c09050a0c090801060503 77
    0xb464a50341d502d0030141544a4080d2012640f500d440720901525400d42c0c0440c0c140c41c0781901070940014040c2c800d80896200343c44a43d80000b0744030300c8810a150903c01441c0100c0d0910540700c01c66641c01e0008a0321009891000103060303d00b20802e000340e40071071000314480780361034888100b130210440652154500c0c0e01e02c207034403035000b0001030600d402042220550810300002c2940c1c280c0d02d05205007151100e000744c04540780c0c9000300d801285400030700251a4800300551981140080c0310690f8000030a400c0140c1011050042c0f6002c110b040c03000e0741c001d007036903113011804198202e803803011022401d00090604c80011004c0036551203441d20788141a240310450540142e030f1000041d01ca0150341e000944c94412140d10030104030341074010304201d07882034640c0f8843c62440507154035011131b0030307441d403001d54441040f4550303035031244403250241c50041300401c2106444032982d4080d20822144001d1894030b032403001307200c2680046004001c2c200b59008002c021b08120029440354800c211 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 47977980 1250 47976730 47976743
    0xd1407060c0e09100303020f010b0105040b030a090b0708040506060a030b19060f060507051e0307060513060c270609060e060f120f0901090206031305070f1d0901020c0a 74
    0x1000c00041d02500341401d030000300400100780b5203800d003003482e02c044c1140130441c010300406541c41d40c814014028202402d205031510f9080c2810072500da002504020415412513450b2104d007404a440c80d400c0d5402821190f40e0701c000c4d0319080c209507240500c0035140c0790151100003c1000030071541010103030803940c4801101404075004160b071000d0142c3da001090b170006102c8001481940280040105d40c0c480c2082d25080c41d8030900601020310202100e05440d042005084c00151050f440164820041c0c449200c00004684500003107401041900011948800e10101c8400c03440c0c41006610f001007261000e52420106c004107418054401c0e0010300881030f00983c1941d60f51001d0760300301c5203103491140d01e0390411001400705403c20344000d00882044404240110410b029500401d50054406440c41e00c0e91881c0d00d8480952040c107175a0f5005228000c1040d0b80381c065040c2c0245040c100400c44028170340c415594041000c1c060200980c410846810301e40c0000c035080039400c0c0c1120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 47979230 1250 47977980 47977991
    0x11b060509070b040b0d1103010b1905040f0e060306180c010c02060903061f060e061207170c0901020f030304050d050702060f030c030a0f0203040c0e0a0e010603080901020d140706 79
    0xd0403079180410a03081200d507410040740106a040c2c0c4007005d88a81c1c0d400035000d002e102c4801403045c0541c4020b00881460030410007000c0e4400280e9040003c511400b032070154075041d942c8011120600058001c1c205c100620820f0100d640b80c20003900740c00c03180890042c03000541c02480e507603484080c0740e00d040c18010000225800d540d11041910100302011382512514a4130002d401c14071042d0f5284140c90003040c0c1030100712a48102d10921521402074400e0340b902e0f03400042c440c0c40d003070028030550030801d8529481d407840d000301a41304d0081807000361541d114091180064102204200c100b48039610600410010800004140103906520700b40565501d40c1e44c0007007144c2c0d10a1100d260b22000300081070010702c2621100440c4103040f40e500c2000300c2c0110214401c2039120949018044140c1c0784c03400e2181c5200c42145135008101c01c0c0c5c3c0000c0d0401d1100c003035401d4803c42da00c143c445c654045074500d140d50301031051107007071901031400c8440caa80c0449101c000d4025050003405440c0d944 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 47980480 1250 47979230 47979241
    0x60906030a020d060203041202030a05030103150204030812091902060f1608041d0f0708061e03010f060f0f060903030c05012d0f02040b0a0e0a051008010f05011b0605 73
    0x1403001040c0e241e00038050342c4203c80a0b08000020703520a89040300c0d400c405e008031b00d011030310200035241d80190594030240346901e9522141c0002015085003034565900700b000100007035401c1f008107114006644640719501d0800c5e080c50801200720890042c0d044d900009a0069945e036049400d1401000b404585030701111303074140c000c10034041000380035510004003c078200c040e05110071130048000e6001c11065a0702c141d001c041810035500780000c40d20702c801140940c940ba900000144080c84c07040d2801005135000a42980c0800c24400d00c0315a85d00010710a21500c9a1140040e00f21240011402490218020300b500040d00c4003804201c0e42030030b002d04028080d00b240d40d01d2072441b1a4081d044c3d0f000900116502c10f821070070042286007000c5506008040e0095804403500e525409050243d401c1c015120900c03080315017503210401c140c020170307255101d0a104080314819600e140c0190b0400340805124403954002c8c40c1802410401c40d00c0168031091b03801061540403201161a4446 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 47981730 1250 47980480 47980483
    0x305040615031a0105010f090909021f050c060619050d06020405040203010b0a02010b040926070501060f030c06090302360a020c010b0111070b0a0207090509030a2606090603 76
    0xa4009012014080c0000020300070715600300c890700021080701c0700d000c1e41d80c1c0005550394500481128007123460703480d04210603070342507000d46403150000e06075101d805200c04146240c00030340d50000d0041080030a0410100c0c90421507560300c494203883d84d0f0300355040d030900003c4510807441114810014800314204112068040d2002000003034403d64aa58440c0c2c80981980c111145c042d0056107800503c10f010b01d880d000e03011000d6040031311042c2c0410b0038800c0da048100d100c01807a4581008104000c0040c00904c6018000e00320508103112043c21890000000407469000408100400d80b09102603602c46140d03907034140103403039078403c07496120343c0700107c3e0408000e01d023024007110010006007000c0c5030010281c822891008201807400400107455601074418030209070391180009102c0c00302c40800500c01010340c1d0045880b42580d075010300007914001c0b201443c9540010520005054008008000c441c0907804181011000321100c1107500c00b00915842c802c0070703010041925902e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 47982980 1250 47981730 47981741
    0x601090e0a06090515060118171f060302010807050c060f100806070206060a08010e0309040b04061a09090c0a120f061e03050d0806090a020a141204060b15040603050406 74
    0x303202e0414064103510b07042841e100d6400741c1d1461a019554130008401e984900a40c1c100820551011180f150411601c0300d5444134203e034241c0300742315003402d1240020b40a440324241215220021602a0a5100060190801400c03400502c030060010310b65000000c160180c1c09094580011255611001c0002c0b01441544c8140ca00b40901801e010049030b000c903490f480781c032050780c01b280c80d95500c22100e422103442500f030015542092091312054501381d0000903c5440081001c00c41c503032212040e210001028a42100502d00080c20f2401802d203050070300c0d030003511400b400b41407421800015000c50002c14540060a99411500e50018495480840035002c18140e100103100c0007090840f80d40e40c203000c1900c40c0c3c8501c00c03841c10514428900c1364032540d0090030503007280d03c8240c880320103504000104030502443c3e05070079140c07446400290044181380010395446080c9810310408031880b070450540202668208035256100364400c68048980c0b80c81c000405960b80d0400100810 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 47984230 1250 47982980 47982983
    0x30809160b0d05010609050a0e1306052e05181b13030606170d08090307060903120b010305090c060c07180219090e04111807020d020d0e030601090e0a 66
    0x200c42460114189a0380c0c00505410400d4440030070032a600c82c1c00990f034900540c4506507008080d1041070040980c8451119008481c00e10035640d400e4403540c894050b91800c1b225088002800c3c00030032900752201200c469121440c0007810792250800c400f14070f02c00d100e04c2c49403800326040c5010841144500c035840f03454901004155448011100c0c4004155803d1321081c3c54003030402c00c0c08184000252070903010100f100c0d00070300c0c82c811129420303154140010303c5400310340030920180b0003203521070060300c50b0148290382d08403444c0e81c40c0200208481c0b51040b00c40c10140341c10300b044030005000428404289040b6011516010309058503450002c85400c80d404004140b49802184d00c0580c02034803d030344842e03042c0c03030305040000d6007112280351074444c9100d00e00b01d6101040128207809012100d403400600f400f098100240c1c42280d0498040c2c0e0f00c00010703849101c0c0c005805505000003451083c0c80d2500d070035001e40b40000640e0702c15040c002c100741949d403120119545941000b0351107480707 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 47985480 1250 47984230 47984263
    0x20913120507290603150c03011403030c01020a02011e02070c0306110d0e060402180906190216110a05030102070206030412030e0f0708060f01050303070f0c23150304050a030809 78
    0xb801600e08081400c04184c0d5001e009120784e08407059140f0119403400d1080f990800b00d0760a5030300e0561100840103010400d039805020410001c3c0c009002030000345840035040d000490303018104c55000c1e00704610b00400c2000030303105201c0e03440042d00780c00103001102c0d045600490090403025401c01a03100d80c1041d1240176160008600d0300d040c000c20000e02c510b001702c070780d4203c41c80e100b5140400304000b29481401500103030001080460402c2941d034054584060041c1000981c0482e40400d01031003205031082100300514240900d80700f0441c1001d41005d0f8025400d060582c0d01003101e5000c00f80c002090307011413140f101146440b030383c49100c100c0d243e44100c8411400c1c0781e0607107859010340d000384881c130302a0100141204119640c0c1c1e074100e03000640114540390f45601c4100164400783c904a8200d960050f001038181800b0307507802004080720030b2084840018a08104540d402665001c03c0b02d9002e01c2008080380e070114440358581d402d424a5081560790040303050905040a5101c82c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 47986730 1250 47985480 47985533
    0xb01030b040c170c0c06040b100902030703020310090605030c120c0a2612190e03060907170d080408030415020f0901020d020f1b060904060303020307020913120507 72
    0x4590022040c220f583e0f002c1c0110030b45489084103d941c500c40c0c60940d1700e081e8010f0001c46c0c005862925450f0f8004203002c101c000392503c030301c512000da0f44195180f20000380c001c400e101100c195000d541e40200500041004030601d0000403c2d156011301c002c04d44103000b0b00a0700384524800303019080c80340d2801040300030382c581c80300d41e4601d0b4030024100803030714807030100c2241c0b0810400103100203441c440c0680c89400d15400040340f40c0b4140b0744214030b50410281482080380d40c0c804205182c00303009510043d0030150300f810300300903c0f00f14a118102156110003002c0e00030a4201424940003600710f4102e1b503490382c2d0b80c103250a8201101c1ea8000c0420300c006071010038200602e001d8601d001e0b0036401c1d15191207980791304aa6840b02d01500c000103030010640070205c1c2c4024011803104c09400340c21582046051400101207807215841038015030000521803045180203d8500c0c1c0c00500d0b00c0c040801900d80b512100343d0303412040c1c00001030010002d100414040c540040300c103501d074400c032007120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 47987980 1250 47986730 47986751
    0xf02120d0b06072406030308040206030a0b04150911030c040b070201020a0b190b03030315100903080d0509010b1e04020d180c03030f0c03080a1d030f1801051c0b01030b04 75
    0x104480200e4408122040f0f403c4100351507501c4c0200d0003287d41581e51601a6200e81e02000000da2001d0302101c4801e9891380c41550301d407a5401004440c0d8070100d0303100044c62414094000307540424240d00394032030081041040c1249000290b400f6142c0301c5000c5615800344c1e100507480d1450507500681107840000c10400244400200314100d640b6100f402c0c40400b4040003810303640d0209076880980c03d0850300c015085410801c0403956102c00915001801543e2034a40c203009a1060f54100c050304e0710703001003140c03c0740c090044085105080d14140d8a03080c04030f008001c00e0000c40c0b803d03885241c00284185003081c0b44d41000641150149200c030f145000752804000741025480b048000c00d02c00c502c00400c1314000c51030300d00d8a83c1c068035001e0a50f51003040140051070400d110b4404030800c5a0100850042000582162582648226507580a40c0564020210b0900302039040240c2000301ca1404218500c8902c042000c0f080c0208000d0a42c00040e809860f10000103a0418035115800701d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 47989230 1250 47987980 47987993
    0x1b060608030f1306090303080402040e12070501020d0b030c010504060c030e100c06050601090f0504020c0709050709060315051e0411130e25050a030213030303060311010f02120d0b0607 81
    0x190658010b4401406155103003419111445c0700e01c0054040b956150000b409801c007500b00704c2e83c9480c2c000956403e40c2d102c240303000c0640c000180c103039050381d03005c540403c0a4501d4403036804000c10807030041000c600ca00c00001c0183c811801400300300900441c0b5503080500415412046210003000350202c22020540203084048140042d41d5041c2408007040030340d401000c1c0007064070021891500c001d0300342010b0101a5001011014080c4035152001440c940244289405170310141c0c1c03000180c9181080080c199180d03080401d1019000820400c40c40d542c010718441c0e10361400d8103010030081280000380003441003400444410b1130014801d50148041b00850b0151412403c0e01c0c80541c950481c1003c6171880d46c24103500041c0341d140e010050344d0207180a020b85c03090603e0058545142001150055541c07a40201c02103070f166030090080012003021860306840a00c0c0c104000c28444100a540d112114900119543d000032078044128081e04403030446100901031a0b51030b9490301e03140c1f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 47990480 1250 47989230 47989237
    0x20a03080d051608130203071a1b010c02060402040504140a14070e01030c050f1c20030d02070e060109050d050d020705030a08030105010302030a020c060f01060806040c1b060608030f 80
    0x108451074070002621582403000f151400c42e81c142e0b501151135540c0c0c58541248000c0c2d81007a030340b500c135100002072004070343e104032540807034950440c64403138856080342c002250843c401c0b03020782d904205220400356030015605605c150120760220319a00c2e10304050007401c1a5903807007446405840c0001042c403810030407180c0002029011600a03541e10044142d5851081c08000e00b820411101009246000014081c0210f402461000042e0f550b07a00e8a1a11100c07907801c8601c0c1000b465805a400b07001d5060000317072481039015090850101c00001d40380d0b41c590091060081280300401c070141d20bd920910090300019000c0c45186a0394109581e94040e40d5402400602c1000404a010300340410b505400c1035003d000301d41546d00b808011740103034200501501d000c650a005803c118a0208211401034481c1c98400c016541410381c024102030f00140850b01a604040ea10030107140c0c04080800204126524504080b1061401d1030107050540d000c03c00074407012620074120700d1042c000307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 47991730 1250 47990480 47990497
    0xd0501020703021c020a150e010e030304060e0c06030618070201180804080d18060e0420030702060703050c0d0906020c07080717011505090405010902030601060504090f0212040816020a0308 83
    0x148031311520041040b41d5980d00d02038001e10f00da4000245841e45103194114107103502c120400420004c0410700000e1941d0001c5609803915500c1d40c04140c4054802d0104130184141910403c1ca1440c011000c1030408440e820032035400320040c0d0004140c280300390300900c03583e0403030043d00710540300d181001e43d007070707005070103040c05070301801e0203d00d01103004060002800c900383d00a0416507140c010705459400c5041e01a83c0c00c40e888000c9400391010009008260800d07082c3e64680301d05000030001e182c04401070408092510300740901441010010956800c4440701c600130400855034a420000390241c9030700d4803050311030710070b010442c20004030303008043e034544040090b01c4020100c5d241e403c0e02c0c46509032284090f1042c0d0203119606048616541c030070f004034000300340e9914a50129240034000da0104c2e00049000c5003e015000c007078016010480107101c419421300040f203c15610410000d8801086014002480e00000428200a020b016001400007a03060750324280840c042d0b100300b14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 47992980 1250 47991730 47991763
    0x1e030f05010b13140d03050d0e060f040b06030604051011070215122202090601180803030907060504030c050603060a0905090a06050a15030305090402120901200703021002090d050102070302 83
    0x3400f05200c4000618200c120300000c4c013091741d141c1da0b51006c1c0c03500d43c0942a404000354a42ca50500130890400c20340c1e00540b2403510140e107e190600780030407242405058280310360080c40c1480040381002480c21603400b02000c000948204400c402c16072403003140c00088d00035405142c2000d68142d004081c2c081c02c640d120410300703d03a940810b03100c0c5171144400c2890303040c0101d010700c1015081aa411980c855418107082c00b04949501a80c8541e40c015400310340c0603400002002008101800003200401c12410000c1c103103030442e0b440b006031a51a00030340d80603541c08400103505030340c0c511444004040844003042903003030410801d51203c8820b01c080e99071604040105112000030701c40e881c007070400466090400781c290398080f160390703001000c802e6006400340402c0c03180504182c90580030f2122540005a42082c0d5009020b030721180100e4560340c0d00003070002c0c401098000c00c200050301c41602c801690f4a440200090610080e47ca001d08691f102044070010540c00048400e4860031044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 47994230 1250 47992980 47993017
    0x140c04050109060807050d0c0509090a0f06080a0215220801021305010903080306040e2d0c01050322020402040b07030302180402030601020a0f02030a050a03090306110a1e030f05010b 80
    0x20741921113507030548812002a108001500c2c03901040da00c00000105a880c01c070f89080c080b00005022660161047c41503035554000c044e00300b01c414413540740182800c41c054a821444d81e00042d02141030582e080c0010100040c0070341d0000a011250080864000da17600c040f00e0303d60801600035040860980350103c11401c01103a0fa6004640c3c000c101ca0340201d1651075651124188006032400403418a154440c1089001c141d54004800a21241500d1143d02a1912015503185031003d100040e03818821b007001441015400303003648a50b0b016a41e21201807820701c07440860000d21036980081045107001c590380d810180d054004008402c00102d04848525a490400089110a40f6500c0c007503404081080300091881c2c0d10f1140c10b500040960b029070390346880d96806d101082c00b044001483d488000c0c8204030f224030510010103940f4a020f4200805084089c003031a03140040205107501c1c2400d5203400c10310940000300700c41c180c41c000780203550b5590500066034015003000c508020b49076 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 47995480 1250 47994230 47994239
    0x40c0501050f0901110a0803090f0c040c0206010e090304030501020301060522080303150d0c0603050105120d0206040b0402130606030c020c01020309031207140303070e01030e0a0c1701140c04050109 87
    0xc1d030944440015400b07a003407a00007444015500c0302000c1e81d501c0402d0148240300b202040d0300101940c482c2911070043c0c01941c44416420b82007640715409144900c7c90080140c1020390b002a4240c15541c02000c419116100d44082c1841c6004036171001300a980000008114198010040d1480c0c0e240d030f00a0048400d8240070082c2d204a903400b90082a900c1840061842c0351489072400c3c21078009440d8252681c15078513038a00051440d01310360040b0303480d40010045401c11241e0321140d04140e6000c2e1508410190000351075180280c4080c04400300c4030086804c3d0b50798001010480700c4c40000401c911561110040c01a000038032405002d40681c2910740e000b0750010048034544203004000d0b185000810041d100342d40c1020406440e80d4200016501308002d042000314081d02441d19580c08000b440c0c400107094400d503050381d058907008506010b00090350180841c042d40c0b00903903248070101e21446014018515034040d01e80c0329071520305211456405034028802d41d0000e036208401203849 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 47996730 1250 47995480 47995487
    0xc1e03020109050909060a0507030207020613030516080a030507020f0d030f0e0d05120703030209060304030504050a050a050607060e16030f0b100b04031b1214010506030601050f010507051203040308040c0501 91
    0x403201c154103900110002140401c25612203130727120303041d41001401d0008903000308005400801070301da88203c401d6000d0041c0001017041c001c2c1d090ba40c03201c1c10350082c00c4c04109902d8070016a4002c007800004180c1008669880c403e4180d8004050002c902d00c000c2d50900a000d00065900e0501245000d4410300710350a0107080310728869081070040a0407283d210300200e86500c51a0280e0030140c0c00c0c0070750784150303540c0e10003940218025540c040e07c942c18402002001f0407154070080c480c0300426400c1006849510a5600260300440d002404007402c50101c0c0c10040724900390f10620407075004c080304010303500c0c0305613034030301c4c0280c813805040e554203512400c1c2d43c40a0f000d003d1035210140000c00000d02069040410145a041c01649e116615003100f508002080c00444000c0c600c0c400340750000c4824402c0e00c0c0d2201080303000b413846e9498000414005859070b0030181c104600011040c050040810264543c080b420704566942c0c82c081c1070060144100361000ca8515060b90b40029040d0311 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 47997980 1250 47996730 47996749
    0x12020c0705010c1b030506100501030212071d0a081e0606010e1002030408010501060305090c0301060b1812060705070b07020c0303091e030a03050d230a090c1e0302010905 75
    0x5009203009800d1800544201018100484240c000000e0b804500d02e441100c54005501c210300400c49402c2c240b41c00100300840307411050415105000e00394850340400c00761358011903182030041181d030405410908520591190703035080a800c0c4000900c40c240014804600164403414203480c0c0780300c900c903d445280684030711340050003d10780303078055142101c003054030b008043c01100c1c5403d40d111070103030a4407002d0303100c640402d1f520801c1007402d0384d0900c02ca5401e0320040307000f0000c1604110b030392071160103a030760000c50390b058403429600c003515009008104603450000301c0c0d40700c1c900504018800e80c05910301b100e103100d00d1008913540740d000044801240300d00401442c205074104090280d0a5414020400c410084200c0e02030507480900002520702d0007039903102d940d404154400c070140c03008003402208005507045184000500001d0301500b00c01001d90124ae05c81e168200f01304d0f5140103412069180410348040c61204903610442405c0f240300b80c8926451940d10020009102c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 47999230 1250 47997980 47997997
    0x40912120207020901091e230606120a0b03010204090e0d0e030f0d120605101206061103041a07020a060305100b0324031e1011070305070803040809150702011202 71
    0x144200502100d4042d4011054520400200b0300001c01f860500500b03440c0c041204200c222a84080c01c921a1441c48016910180654050385415500c2c41d0509080e40000c1090184903618011540c003130303900307404940081c5143d407030900000e0f007812050b0341c64800c0303c031103100840c0300f0f4120004503040c04a0070018120004015208005d0302c0780f0250f5030000b203280a1b48002e41c1e189804602c907902d034014400109119a904440803941e00c10440031540150400018088071403c503211140e00042241e06071201c1c04400003100d00c4424440001e03015101d00203601190740a400b0482035410b6001d03612840b0300c800c175440072a03030b2018a164a0b1106461803880c600c484460f0040c0e42050b182045d51000003d0121217603c2d048080c184005032300010b030081d044c0c2103c0c024007003198443c01008103844400301c50a02d81034440d58060910320035030b00e0003000e1420220020b001d02c103981040c1c2e0144d0714090141c8501e2507400341950381d103a10204040340812240300454a00c03084620030b440952 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 48000480 1250 47999230 47999239
    0x90b0307060f0c031e020606030d0216030201050c07031205030a0b0a180e1608010e0c030c0f120c030601030f03030513020109050d051e030304030f081e060d0204091212020702 77
    0x507039044000c54100000f001c06a0034803025150750140208190f000c40441311243d809024a400c2c20b000301800d0410481c040303821580504007034050100c1110004046950909285e80d955a03001d410742e040a01c0b69101606a20040e484000c0181d0010000d503c645480e20007080515108010044103114030700907501c90842c094804281c0f90560f502c201098810b140858240703028103000c00705428007075040320130143d4540350008012002005102105442107000e4440c040c0b1120200ea07042c2800b0b9580352051561424501e05082d060080342c01b241c102405841aa603140e04003010050100d990407070020380381c980020041750f0058290310156078169034459140f4074003c01c20040901012041d20540a4441c4404251010803d00020102c45002868581c034240c1800307080c009554040744107100d05c001c100034102d4080498110b660b4080f40c4600300c0b644030340740410061814108000c0d08035207440081814000c411072003103440002035403103858403085068260701f607010f00040203410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 48001730 1250 48000480 48000497
    0x70b0c060109110702030d050d0b0a05060d02071b1214030c0a140106050901090f060f080a0f1103030d0504060c030606051209151006170c16030e041104090b030706 72
    0x7000c00341c1c100c1e0300045001070303c450821429800082c14521080e00c448045039002613403285000003401121400740c0d01301c413041c808901c1c00005c1750040c4103060000c1c1d40e0300c1d0f002400000300805a00000825a86400900016130b215030710003541c1203214170243d5840302400101360810301c0c00005c075441a02008040c2090a280c0d81e0790b0b0720240b43c507020540d0380395201c16010804d510380c086c445009010006c000b00303180315502e4001c000c4070400e412a15602500e18030620030031030300003509200c940d40107502c1c034101045401c03d5010246860078550f07250200149a480d50800d5030452405038ac042e2808005440051805508650741ca00c0342d000031a4042c0440c01c0ca401840640d03d9110101e141500c8003620340114414104401b10340011100b465072009021703550b40102c9410340c02d21100034011150611268142960040740f074060440001c801a850400d80b00384401da145800145c828800305a4440e0001d80d290018012260380b80d242203045042071070009038040c11240143c075070307081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 48002980 1250 48001730 48001739
    0x120206160219030203190306090e0606010f140906030f06010801050334082d0118080a030b090a0f390507020604090501080607030b030319021006030605040203070b0c0601 75
    0x41080b03400070542c254081449040d08101c04445460381c40c06980e80c000401e28280428242100c060700711401d06540200104410780e6003180f944045224a802c1070f030307400d084034140204644180384000d5008035010043c480409605201c450040c0d000b6201c410740b981c0c8a005250b603529810203840c0e07550701401000300d00c50f101c450041d200b020311500c0b00b400180c0c60740611450301802d4200b0800c0070342c0e109041000b071070b0f8209003140d681846500134804003003074081c002c201c0c180c41000a002e41d0000204000414001d038030590343d1488c00b40c0b0b07078032280c03a24965880041110704144030542cbd090401d608400c0b1070781d0455500103009142907040307a0354081148140b82002d0b5569105200c4100000009a65840003034001072202100c0441e1960500349201e040c100054103603c00d150810b40e494825650100660700407201e6801d06042c904170008080f85800006803c83c034146142c010f0100a11000340c000e988218000d5080764407641e518002005288110308001d202c5070440c100501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 48004230 1250 48002980 48003013
    0x60b1206241812060106090807060503090a060b01020c130605030f0307020607030509030a0b0c030103061b0905010e06040b1605150f01050904110306070314060a0509060d1e1202061602 81
    0x8a0780043d042e010740d006510034080c41d0a00130b80025000c01e00c80c91040000c074038100102d9010f0b00440c9001425420400c80143c0e550f94410801407215440d00d5281e07440303910800904c03550f500014010300c0c0031803a1210380340c018161405014040d014040301c8503c1100004101c445041d40500980e250a48070348088036070381c018840c041c1d854040c00d6609030106580301704c4580203007100303214141d59501d1807400c441114082c4e030a02d0308503600031101600040d080007406048031400c2c01e00c6035006941c20006052841143c10003c803d41c00415105140104625414185440b4070100c615000c1d0b01c101e940c5e085c1e50100c84030441c070002c260043c050790604180035900544240300001c804031501000134149036044800000003030ba940c5100c050310f80d07840c04943d0400029204031600a0418000c10840d000003031625019414101d9840300300070b03044a07900360710b012210328100b00801c5132034103030392103494100600700511403003021418803140108001a040c81c1d81c0c0007002031b07084020895 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 48005480 1250 48004230 48004267
    0xc0304020f06030103030512010501030501120b0c090d03030911041401170a02090f0a05010b030112060203101a0414040203060904060e01090804081e0105220501060b120624 76
    0x1280c001040030300d80300c0c540d200c01010f907020354400d880d55034941c5103160030034510840c16400981054203103001001003c515588034040c098110307001030000ea8403070049003891321580b0700c0c01d034216981c0c030700b0340341031642c50740c84110920f10911080c50010f00d02000c00058817000c0340798801d1019200b00411501d19a0702d600e00490401c04195a141d8540742c00003052500c080310f205180590890030030144414501c2454090b252424850b41107506210440203c400e412000400320380d400070201c0d040410203107801c0c00601d1419200e400300c0301c0a4403d0440c0d13030494880c020148030b80b03c032021042d24040c002d6078401c0801404115050b03540c0e4a0b00c0340500104038562070707155038403504a400300710160000c00c0030b0b066480c01424400009603032032140e4484139250200d5039241c0014041441403c42c0c0d407a4200c2650180c048125a243c02d100c1d00400c850f9101d82c421000c00106081c20200f02904030303218490465448039107101c144281d0103040c0b16200d2010981c0c2e8101b09080790200703a031010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 48006730 1250 48005480 48005483
    0x10c060b030102070303020408100c050d0b120a08120a0b010e04090204150308041811031b0f04030506010e150a050103020d3207050a020607260708091c080c0304 71
    0x40340d08080000031034226803051206a002a80000b024444410208021100403100c10700820201d102400c001b0017501647c004903071815252041450701d42c0e00c1024260015a40fa0280d614841241c13401d000c0c181c0c413004880f243c0203450000144149107600c6450440001030b11100c0325207016a00700002401041c5040740d105a945000b601200309420701c4101840c810300c80035130344905000751b80d90030380b812400c0251060300b4140001c80a084540a0765000035044c5412110b80c0c00321a00001c0c03900071610940b80302030000c00c000060000004140b07040b122030000c401c520b51204030f4540ca03406000074481d9000450303408100b02c0755100ea0300800c1c6103103004a0006800a45910540850100904600007084003014000301d00300c01e420195040005401c2c042d00e410f003031000103911307890f00078086000c4c05107610307100a201c40c40503101007030a00403207a080d60341d19000e017001d0072810095840f01603503c110500ea0050303a44840040c00d0243e0b050311014066a980d241117009940002c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 48007980 1250 48006730 48006743
    0xf1608061015050d02070f0506060307031104020318060c04060e0109120b0a1806090501060b09030601090c020c090a20040b0414030708010c090311060306090412111c020105010f0e0105010c 83
    0xc40a8a40000c2c17015040c1c16204810303001140c4058200745e413034000c018041d0341c82900030010410000c0c3d0480d1150385130900988002d61a03548106091241039403940846100b8003a0a003003125100c400d1004000b43c031001e031600c0030720b80e400e500116100d1301c407401440900200c07801c401c00400d4141420350b0307204841c40b0000c9030f91380c803805d0314199841c4041400c4a10984440d00241003100a004010180c200c2e14580c3d0b003000e4005001a0f96034206114040c4400e503210030601103140f09114018244401401c07d21603810007070260303002440c01100b5000c05402e50b01e00040c80303a0003030381100c0c11215210b80300c9050508107020f100d4454105180168188208000043c01c840f007806a005000c150782c40380d181591450400441c80842c81d20b04902c01d4000f0420000c19031303512201c035038002d41c100e240081018102d201c1aa046103c550744514240f0404a01c40a140840e01205c0000c4420394000e100d03e0743d0b81ea04580000d00d050140600001e1008014069940f05031448a200b41c02501d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 48009230 1250 48007980 48007987
    0x40317040212030a030606030e03031005010813020a0e0402011b030210150e1602070b0702090708070e030106080c03010b0307030b04020613031703070f020a0b06210f160806101505 79
    0x802c0703902d5030b8041c019100129495007010007003150184688404001c0c00d0014610750300d09005a0540140b080c0585410300000d0303c00b040404407a000407071101f50307002c0d220548068489842400300001210100d00280f542c01000030003d48040c030442040f945a0020f280040240e990b02c8080c0c40d1800820010820802c80054161000c9030001e01510805034652047c01d20401c0090801c080f40d004803144010070000d03080180c813001240c0750b100d0181c1ca4040c026840720f59048450340421580954150300b00400440c04100114645c2d8011104500030000b07040e0440605d61105403034407003d018500c0101c009009414540c0051004850141c1d010074040e03103e6940c0c0402084a1200c0c08059601004000000350401c1c1c00340c02c801e525000034031400b40680c0e2600c440e101c009103800c3c010554846007907a684036178000046000300520a403085410886007407551000700c500b000c2c083e03030441800050840d1000c42c40d01c2c000d060380340d02010035900381144201c00c5041c00074031108014040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 48010480 1250 48009230 48009259
    0x210b0705070611090901080a030f030209060f070c0503010b0409050a060b060705070602060105010f0c050606040f1806270819020304030605090c10030507050702010e0a0306020a051e030403170402 86
    0x14401e090030100c1000941d130721480c0710014442c0e100c1c01600f0107203055200891090109822449900001070286405a0350307041c002c002c0b4040d4062443d186000140120702ca500704030681c0030707440c152501a0020495444803034200000c1c0c0b15a41e81c081c0898001414030004601c40d6080300e48182400340103d8a0303c0c0040d07a940c3d14004040d0301080050300300301c0041c0010343e030010782016440058982031215081c69100c036074540340007400c154071585e138891144140d020290040e0000079680010700905107043c2c2401c1002d00281d00140c20181e00c1039210000e1400304c25078622007260413035183d604121460401c4004c280c6020602c1040d4402400b001000500c640580341c0f19078803000145c054004030000340314042e545182c0708000c2c10300b8603082111503503000082c0d58586030240ba0200b13a000709a008940c1108990300081d080600009541d0300c4103030860024024007000040c2c8812a21354005541101e0100751801000190104200c00c504014004226001400100100c0c0b40803101d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 48011730 1250 48010480 48010493
    0x200d020d0605061207020606010c0201080115020a080c07060e0a0806010605070f0501090614181b040204080708070305100905030702060c010f060e060f03010501120f0c08060c07020a210b070507 85
    0x200c44d40c1601e10844008000c02d640d8180501a0410740070b080082107100280d00180103650305015000c42000300c0e4401001ea00e20805c07448401540050a49540d204000701568480801d4000c0101042c001d2003080350300c1c180056010102c402960141c10180d00f0141d00319901d0b8408013054640403900742c0d114000c12420f01c94155640d206d140006440c0d21416869500351b40e00400002c140c00c000d60440c403402c03001142c0410180c02403400ea010070004400054002d00454000303440500c0f80c55030126008a00150007400d032070080003100c0e54040458064400d55186034001003243e04103208100060400c4030141851801030000450841c400555050880300d8540c003010000361400e05000131428410100c01400005078001e003d907604021142885011000000f40b6409100500e4010b02000c00c40203001340c0002d0044d00c1682c01e02c04810040c0d40c01801040e031140d4aa40320006401c00000810b58111810181d81400c022080d151a444c1c4074008002d1010b1210030401500090302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 48012980 1250 48011730 48011737
    0x5070e0f0a050918031308031c150b031b03010e010503060c031005090402010c060203070c0318050306060f0d020a0803030406060b180d0507050402070309140406050102120a0e060d0f200d020d060506 87
    0x40c1d00300231600c601895007030009480742c01e10782105085c034048030015400c0301070b80904181d40310250050390726100c0642c82800840020400341c800d520202c00800c83d01134401030350381200c000301d040715055151038114041600c82038a4040c49c082402c2010805420240304155100b4014100118110b01781d4070307460241c0e030084580b0300c0000c10240207041003542100321000450b2460380302d032045c981094041b0741d803480c0c00317001703588a01414062801e00e07030f50710400d41d0462a400703004160120741d00c03e1398682d20341082e6400c0b83c020742007000200d52843d4200c02d44480804801001e501006034605000c141e040119003542c03540182d400c046500d880d04c0c0000d0940c1442595040c9107240303080544591129002c404910680c24590200709680e07000496440c00b03000303241d00c95070f41d12898005490070790300192100d0f0041408600a000c4000c6544030b991003902525003030026480500f82040345100e440c0e145100340b8001e00100345502081c2e8040d02000020702000122603483e0400108244c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 48014230 1250 48012980 48012989
    0x2030313080606100e0a0605071707080307031802210a061508011805030f03090327042f070c05090108010603021201110d0209060d05070e0f0a0509180313 68
    0x14480341c140314040c186140090015030b13551500c100c1e07176503144001650341011031244508001002c034414051103070040c614429140000891952007610f4034018805030803c603180e10102e8501201d5010001800d5912806264010310040f054004007000c507121f54244031803000207200346410200040c14074414441648564019412028507000209080d110501d101104071401040c1e278400080e03000080d0398100012410b401e45a03510f101855156001d0400b0940d60040d06040d09001c0c01c011060742031035a003080d030307060021000c0034a9071a5130001384144103210f60040300c207070b800211080d0042d003115840740c9012076110361340e8000101801401e0b007060a041c1d43d100b2041046182500a0429064480c8000c1c00f00c0c0c1c40c41095040320340140c68902902c01e40001d00c865103035542c0c4081381c3c01c2c55850381d17040109042900008000d18550700c501d900510f820040c8004030b2404004100c112a801400740b00c4a0796404440306a81c22a0f900c0c03801c0510041c8082c3c40030940f8260040060b1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 48015480 1250 48014230 48014233
    0x90f0b041802031e09250b040501050c0a0b0a06140609010206010603050c0c2409190609060b030d11010b121009060b060406030e010c030902030319050d42060c0203031308 75
    0x19007403002d002d507406005803200180b01805030807c101b40200003003030300d0440f40309080c03098079810040d400d41d041800c0b150380109a441d600301041b81e681c5055201070151206182d4440f528000c0e441402a00e01c214078031140540c7c04440108000351098002035400b83e00c10381003600302500c0c1c0081c01d103410000d011402d042050002010a01c3c00801c481550143d1020014103c0241111340700030025004040608480e403903071002d0050007480e4014050703030350015085980c85140f40b0790040402c0d030046104842542840400003403440c0c03002e0380da400c0a1a01014006200504107401b000f130280f5a4202c1d0601e4031003408048590340e01c40078100800044d140481d00c202071910312421507204180301418103103003044800c0961800010340d1102c282050003a440307c01420300698050140200d1080040d00309a10920320a507010814100410201c2034800b0445600080700d43c001d0700311190318040724043d6001c10180e032141b03083c80000b90001d41074902e418003079299181030013202c1c2c02c0791b81c55 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 48016730 1250 48015480 48015493
    0x11190503040209070207030b0f0702070e01080a05070608150d020307050405010e0f0a060f06080a0b0406060c1106340206070f03020c0108010315020c030c01020406090f0b041802031e09 81
    0x20360812605195004c0518400b8120b81420b643d00c4c3c94903d0409403440b007144e00d008001490b21402006520042e100170000780c0510740c0d43d891030340e607152010300d8111100d000e0b0440004020380100c2010b400b03401c00941d00350041901005000390000c015100342e901d071080220008080d01d45115960180c00c00d50406412031038001480071034040c0107450940b5945c80c000c010082c0d1034640c1c0003002a15039500d003440e01034559210b4803010340304000203503a02615000000403031503040000e20851078410070302c1d403010303640b1041000030078004c450b1384540c0303801407600c003070901d2069400801603101002d00d070145482a617004202c01d81c11007541140e4114541e41900d0034160100071102c442c00e02441c2c0400e403076046517220b04e284540c01001501300781c0c002c5042c0394076450520503a00e801d00040c008544940c0d4034880245400a103119402c90040d8000300418168070754000c450a40d610707074515542140341450a14020343c401000c0601421155840c10f00e42c151a1001d1030181c45107030010501c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 48017980 1250 48016730 48016733
    0x180b0103020a0806040302100209060c010e0705100203250206070b010b07020901050f0f010305061c05031803030a0212090a090905070905090c090406051b0a0201050709060509060d1119050304 84
    0x12880c1140d08800307100e0380134108100003c1e03400905403500c0009440c02580794100c9001080060244034030a0081d03508181c000d682d210310005d420170031a01c084404211076540804141d84174403a901d106081251120041d060409040505100c1f007480036201c01d2801c0f060f41c5844c0d00c1c440d000e030040c0901603400038810065180c014032040c090502102c909052218100006507d02d1011640c0c0703042c162a64000380351560350304010522110845518000c03083d01c1d28110351640d0001c00e0452080341150300042260400006a910344481c607001802055503102a802d00c2d43c0012020681c84890101d01041c045414052000080e21807401018810700300004901074031001403075545035030310000d04040680e070745200964105400030701c0015242c581f001c0c4410b0f1540c8540c0e03040741402c0000394170040d80b03905500a6124000700d6503225111915610121014450805c2590740b1120a01c201c54a0100642c407010b10249d10800079442d1200b003105401491040c0141d803000700b4004400c020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 48019230 1250 48017980 48017989
    0xc0203120408030d05040204060b070506040209010f0806040807170406030f0c0518040b0607050105040c06020105010617181e030909180607051b03070b070e120c0f0103180b010302 79
    0x240040341038032116003000c0c00c003075040355030340901c0c510150725546503804501507440320390140000c0c040c0c18540d142d96a2060038010390366002580c08074000d005040000034a500030a150200b92800440601810746864543c6401034001503001d85440034920b603d02205580762001b80020702c0350351404961035034031401c90411a41103812410a0060811400c0e82c1d9041c03046e90346d002c0f00310446001401c2442240171800901540200811070340c81c02c814002803202c0302e801582152010350080c04283e8a0b2541210541c00004c02203298080352008a02c5148001646005600076142110080c0a11400459040004002c0c0411503000040c10045a007019040103070301c0349810351800500101c8a00075640c501d4000e05032020804003080c451034508401e88003c102c1c030072410440e83c0b04c0c003085c1070400c0c0c0039000b511610007041c000c1ca0160780d2400e055034210284a0040c02810850320300605200c088000c48031242c0c10550341380550780310b6400d0061008403903070007200c0b581500e606501c10710 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 48020480 1250 48019230 48019243
    0x10528110d0207060e0613030803070801051207030506040f0218040c08010f0b0607020603071206080606010f0e0108071805090123030f1903110109050d020c01050a090e04030c120c0203 81
    0x101c0854000c01d0341440742c1900516200c0c4100400d46020b80e035040020140d01200040d500000c124401c00018130a18590041c04181a158202d80d40d2805031080b003c01c6a071695148001801c6e1f070450000200821201287c10034168000340291a08026210035455000706c2168116800008088144a8440244109846800b4883e0100715148641000840d1070149840c0203110301800000942c3c02ca1060444c048400001c0006000031526503195940b40c61046543c5400100380000401400344184144001e600c0c060f16090440e4803000000c6456a44000c1c3d1004410250f002c00196621046c032001c0c0204031441c0701c032421007140c10700000f02d006908292846032703000c0d214855803080042440110002c5203191440c20b14032a10341640d11480e01c89100d401035180614000a210b0041648888000c0503030030f503081c070110300740103541031f0048a0031b100c0004c0305000d050000b0500c102020390014040c3c10400e55a202c10759600005000144080001814941c1c01004600302008030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 48021586 1106 48020480 48020503
    0xc130806131203060311040b060c1b09010501020715030b030a0f050d02010b0402040f030204050a02190f08060a03120302070c0e0108010209090a0e070501052811 71
    0x592455030240d4030540b0a0021000500b40040c4a0301c01c20098990003045034004e0790114060000801d2035030552500008100612000104204414a0070506001145030b429801205224501c40306174026415544041010f0260070001440320102c280c9501e000900b0070003200000303103490341207600035124825000d1407070148240400c0400031240da5800034415501207005000803071041c0e11039140194220181440146025005030703810401040001d1f080c290755007a000c21190a8041d50008a0500c549120303050303401894451f07020000b142c0c5a8041031075520346960014660050000305940000c540b01000701c45074604001c0c1c900700050714040e6840b850703140d0007036101541d840d100710b00d0100020541c6007a0300981400301241c202411020b460303e801510190002001040c6590b404000751821201eaa540210000b840f035a80220008248803000e06241001c1c59 = true := by decide +kernel

theorem cover : BRFrame.Cov 47841730 48021586 := by
  have h0 := BRFrame.cov_init 47841730
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 47841730 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 47841730 ≤ n) (h2 : n < 48021586) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
