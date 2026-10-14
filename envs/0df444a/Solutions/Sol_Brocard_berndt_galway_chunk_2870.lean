-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2870
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:59:20.275858+00:00
-- url     : https://prove2.me/submissions/b8dc5fa9-33b7-404c-b581-dd3648140806

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 516007194 ≤ n < 516187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 516008444 1250 516007194 516007213
    0x80d060f1502120904051b040b0d05060a0608040209130c0b0403021905030712061407180f08100207051c0503091e0c013c090905240d02040608 63
    0x4219219a1120354580003c1c0914001085181c001d801a910303950712594480c1c00140072210f280b100b9505410748016440d4903184c850110004a40102c94124a142d103043c00040b041d02d045064407003207840366282c40041c1d495680a01c0a0f0440c020100741c0c440c1c2a1140740c0740060724180180c0d00070030026910701e454608610400502ca400414005011a48444140a0307980d01080380d07030444e4084464000403807200c1c603041000e800f032441d800c222542e41070200190301c3d400c0108145420401042c0010300380c0c98400405005880c2d000d014110741c00030035800504901d65004000580c000d0084810003000c02019464005030441d00b134000400c040309100302e2181c10020280020400c00098407101c48002290b917442d8a0301003442c0c1001000c031520407043d8010800c91314288040e0103518a1070005944c1015807680c448e00440001e82510400903007403005e482103a004150040c2100d943c401c03030b002c0360802d01c4c000a4509900140c5441604016035461203171900410703d10707028007610346 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 516009694 1250 516008444 516008459
    0xf0605070305060922141e0f03030a0f0e0307150506030a030e04050c0c060705120c21060103020d23060a03080a050c57010c080d060f 59
    0x1400a80018141800c040030310440d5644e000040c0c2d03002c00000d28100203030030310032032848190104803800380020740e00d4449080e810308041198400200509103651041c078120390015629105400301c031003190014008075220a085070003c1703035140721074000403030801c45042850b821035000c0d10040b81d1956540400c6503441d0024020994040d40860140100919a0320040c1c40700350f0180c0110f02c1599104000f952201803207040d11801c82e0304500300d031081d1401e40000340c1190300c02a020700301603401c1c1c000100c03001c10510031a203080c48524180c89000c0302d02c08905202207002b4040da0305140e002d100e0300001c00d0712445040c208040c0000c410b00c90f0505140b445807010306c05010f480c01025400b401b0300c042910102100c00d10509850540e586100800c0d62034140003038088541d2060f01041d00d41c1c40b810b06020920321890300015000c00c0405c0702c0304140c0d1140d4090554000e004c03001054070990035070141072080c2c01140100f0006140040841c00c0d401105c049070090110f920b5402810b20801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 516010944 1250 516009694 516009701
    0x1d0909060a0e0d05070f0206250515010f0603020c250302121b060c19061a12120702030304030b010b03091009020a030f03020a0204090605150a03120c0c030f0f06 71
    0x41e10705401811039842c2a0800070032070b1050010152180d41c0d0041811b0842d00d0f0101140e25000c44102200d403102d0752400c00a00000f4820030a80c2c0c0c0c1d201d10740c001007900c000d503171031141268010811011600d1500700c09901075000f19030160800d0081c80d01da20800711811b074502440c030b41c03480302c691138181c00d620400a09080565106e039136680a5100400c201d50041680b402c03a1038100c83c2c0a1300c0b005503d0500345012100782002038040c0030f240045040090342c0d0001c0d143e00396246002c810f02038103803007417103600c190142c8000700e281d100c102d06a40d20611100203000e02130020703041e28039160300c4c1d4a4269410000f0b80c4526050032002081006026007488a600011a046001d20a401040d00014420044c5000160501500200b50000c050003049050043ca602030001d0103600c00c80e0034654010801100c030b00d440e1080c0c043d420744031031600002c000d0580341e2000300107601c00c10705501258400d0108008a070303e00300300d84002c00810003a02c908901c807441520400880c00040c070f0f0802c10b8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 516012194 1250 516010944 516010961
    0x301021306030b01120608060601110325060e06060a0603021e070f02030106050604120204022a010c18060c1101021906050a06091103041101051902070e010602060c0a1d0909060a 78
    0xd1724a420030a00082d80c0114166801c1042482c04a001001180e4100d0a41c0300381c0c0740031104543d407507540800c80118050000c403164050481008503a008865003516840200d68460b0b001128401c00d2090601947c09400c60385120724106204501800350b04050303500c82141552864164071018003186001d02401c07001d81800e487c480d051070724005241241c500c501800070720403a00458944444071001c8801112000014903520b6101c040340c0c049402404e904c404140091801e00c040c003d62000740030468100d0305180e4440301a03a44584401c01c0106000301d4050442c00742000c4a00709245c030078404034616002d081d00082c1800d0a503401c1080b41e10a500c0505441c1c00c10f0301407865040ca2000352640b02d034002c000c0300041061100100c60b144198084c41c1c10074120006c51550852b80040c0400507141e008404044a0340c03580720903641c0b0b4004a03940300035200c1c00c210041c0240d218503a40e03181d8070542040b0030324900010001400e0060102c400c00c0701c540c0b2001c00c218210b00f40c2e0044c6540b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 516013444 1250 516012194 516012227
    0x7030204050c040e010306020c011e090203060c0313030509040608030307020d1d101b0803010f081e0c2b150c0f1202070807020409060e06090d080f060301021306030b01 74
    0x5002d2805500c2042000141b001501945c3e011078200c400031801c2d04480090b0800980401003801c00001000003403884240c1a4020300c10746c8000758900e03048030b08603030088000d0f2104041040e401e507012034890744a240d040350040d44807000029410b5081004d980101444e070003410084200346d10050600e02010b1402c038803580360b600002c0d40b03a00c0d00041c13581e10001ca4070304001601404c110000f41a040000020068000000001032209002c491942a10803131011344064040401a15800f4040b4496541c0c0582007038002c8080c51910b0000080c2004003043c14540c4460b100c2800711a1950710b250540b050032650303003842007001c001d00c80c04503040e01c00e040024024107403a100401c0e00d10f5500713942030700d294005050400d000240c01a59000d590042c403e1218400620b0b254010380901ea00d207010381d200c0d90012480540001c140d5801d03451071a610b0500d140d40c0d01545925a440103001103070595805c0150700c0542610f2204200034084540340811113452840c001040950b810507a280c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 516014694 1250 516013444 516013447
    0x403210804030806061b070b1801031a09070909020d02040f0e100905070c060e0a050d11030304020405070c0f0b010e090307110f0111190308060402040e040b042307030204050c 77
    0x200203074200c030f01a504080e003a070f0020b40f100800705007203c1e4281e070004503458a124100001075442c4050b40100031040c609190700943d071007250010340544461043c0da41d407400581c0068001401d190781a00e42c010030529040300038590394448001241d009080d4240004d40010b41403100c400c1e04280e600051070000302d1794200389091100310080e40803034003c0c10034240e142c9002c54112440f4004042e0400d0f0001400c105035109100001d5031100280b5003110f0a0042c006e42440c03c2c1c1c0a0010b01142e4400400030f940b859850390301300002040c004003020305201c0240f1148001c50114140094003034403684480d41c0c1541003010404071250000e10115440c0e0080000b02d0010301c44019080010a0944003403c04101d0880161080d681d0541c40203002d1188821040941906c002540d141c98000d445500b40382d19104184401c3c1d2281e0f00801480340405000701d400601416105644140178117030340242c042c04040c2d005a02484074560080b1a800b0410a109501e0580304440d0054014032046 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 516015944 1250 516014694 516014701
    0xf010b120708070221030411090112080c03040e010e0702010f05060f0f0a0308070302070e060a0303080c2b0212090d020a020112090506180c0a031104020d0207060204032108 76
    0x524140300404030810459240041100070303000700400b0100404005000c850399005681040154008880030359005810800000c9a802c080001505a039900000509142c4050b2078201c403a6004817420f403006d210070040000c900d075905042c58041c1100d00070145250414600c004c0c25201d080706245a8585004280b140039995081d0340c1045160030790b9a040d84a43e02d40c00514541e6240c1c0c8050411030340003030780108040c6d02041c08016181001498000340d1905d070107011401045000040108590343e002c2000d80748400090621804100d044441c00d08064442c14040382c40d9402c03581d0381c6a00499650f4240c0c0b40600d045a100c0f01520091a8501074108000e41c0c500c00100042d05000e81641e07528214407498218050060f01700044580c00e040201078110003c6040c2ca40c1c1001e400740d000e05410301e1402048500c200d07030b08504008810b40d2440b007004001e40c021142007100c950700300b00103000601c0358009000114021810410444441840c034102200b8541403001000541006c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 516017194 1250 516015944 516015967
    0x50f01050c0301091d060412021209030307140a0c0308040504061d011715160e04150501180302090f010f1707090b1206040f170a020c040902030a02090c030f010b 71
    0xa80f4115000020049980c240785d01d55100300702200a21100c09000360400c20007804035140c001c0d01d103044070b0760840f20003000d070030555141030042103801c0303034907800400514002c14100c0d000300e42180c28550a0303072200d01881d42d07201a800140c1d0300440324004045400c01182c6007501c02d00300200841d6640003c000328842034202148014055144034004540384640c0c841400c1004280020861086020a0504141e0015441540c0c0c010070700090003c143e41000b030506024010f81101c056007000007060801c40103403145042008960f1054002d05400400f5a4411040f14042e00100543c0c00342e5505104030885d81100070342115072000c0075040049881c1e00d0000b0000b0884186280025480c0b0040d80081c135005504860140140708032000c2c031007481545042448058450346901000300c0503001811242e0042c3e00c440d0015800c1209009143e0420350011700300140700038151860b1507180e0f80080c101003001e80d45264080c00120804c50b05224001c3c1039409086007143c1d46080c408140700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 516018444 1250 516017194 516017197
    0xb090a0527070e09010902060d05060a0b09030303040308040311010c12050606070201021203130204090303020901020c01110706050d090602040e070306060516110a03050102030114011b02060717040e070c050f01050c 94
    0xc1c3d40404801d850001d0039501e4203620010034a58000d00d01c0b40d440c6500c54103540070700b2003986c820b03201c3e61700044d0009075003c21008850b50b11030b014000d10b0031030351076480035608207000078000d605000c43e520320003000c21401c1c80f42d0140b0b402d0540300d1075000000001e2040c11120001c0c41180603050400200e001340c0c0c0c00082400020340c00c07502e035070303500d07500c0c044203400303900d00035000941190401000e0400c064040e0050010302c9003e90896144001d071000455407644100022500c82d00b00420500102c2e103d100101507e03101c1d014003166a000c5030381c0341401c90f030065000381120300480d41841503ca43c58050200202110715015040040c082500155144412002412040703100d003010701640b10980303180015508030000315201d69480140d0814509010140c9001900910028992500c030404010146401a2685081c03000030f81e5410301101d03070b003001601d160805000000d078229204070b590388070702d103565941035581d0103614045180c210680ca01000d1a410b00c010007500190440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 516019694 1250 516018444 516018449
    0x30b01030b07020a02130c020115141002010207021f0f030e032515020301090f15171c0215090f0a110d08131e03080a0807030b090a052707 61
    0x60301c645076501c80b44026403030000301c100000d4001c400d80c02c880154144d1a44605c44d50307032660f0001c2c0890b03900100c1100f620030340c0740250314034425003ca1400d07260504114407851070b4007600006281203d036400091401010600c452003810718415104401540300a00640d040741c00c0c00c040c890810b29600640e101d0040c00342d9081c4110202006075240704951040c01c542941020501f800c4040314a00b0001951090186000050a0001c0045010414410304441d07071501080c0100580c1407644004107001190311480640c4210700c1c510b40c10800b4a041c014084017541c000f8508d01b5030a03186014580f600070034440440d0021014122888000f08805503038644c442c0400044040010000f0712044810303034043c1c00054003060310014295031150b080e0585554603000d0008982c03d0852503621912400700800740b0350107002e10500c0d24003a44100c2c0c2c00015604021a00302c401d000410400401211380311406038441040c4142d480c0301414040d07200c81c4040c003010003403c20011407540d940303d52 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 516020944 1250 516019694 516019703
    0x1150804080d0b01051b211804230703050a0b0d0209040b0712020c0102071502030106170901090210180e1e090f240106020106060c06020a0e060a0c030206060a030b0103 74
    0x100480c801c00da11540c215000a04070b24610020021b00040c0141c0c0c1e0440303001d111035920710030890681900007080584036020002810380c00e401c400344007400080c0003a0399118140a02480752100f40c40c1206000034480c110a55000800b841d003108040140c401941c0903130302581c0e1000030b940c05615210f950a074041e4000c4020142621403076001c03592a0007180c07003441a01e1004c1912484040190002d02d04035006040302d200c5400703241c80600c202d20081c8078450220740c102c01ca403016008450996507000c1900e0f000042c081e810f039004105110340f040412400131700030b01740030300714181904001d402a04000700340014500d46011083c5c040c84c1c102080c11072060030300380000ca1b0290200144075140b80100c003500c800c0c040011207021040d680b6070041200030003072000403c643c5c1c414400e1000319107081d5101030140403a80c03141c0000794810b108030804c00007044403408250700c1c0c0000030003d0642c071b83d58045042e213084c14024140103000d44032030301c0b503c2d545c00d00708080307101c3d00300c480d040d00e800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 516022194 1250 516020944 516020951
    0x2a07120b16140f07050f030406020a02090a020a020606090406090c030b010914010f0501050705160308070308090d0903110d0501110306040b0603090616020708070609030b0105010203031312090504021201150804080d 94
    0x40e06011b032800c0001040c0d09000d100001300440d0300740c0c2c0440d0040c0b41c1761098508240c0b544036120104240e01440400c1c00041e84060005111890103803c100e80080c001e440c00554101070761184547d0b0f54440c0c1013500c0a80342040108520740c1c0301e2007042404151403034041e83d15410f00d07100103000042441141e04200022840b0000d001c0c0621155035003116140981194503524945400c654204020680c04a404040018090000030405043e6801705030f403290700705411a41c600382c007103a4040c0c4a40e00702d9614030044001400900c116240881036055071502c071711381881008140c495000540e80514000c0c170500001d2000002c03556000303600f10008910100c00410101e14004e0254400c110700d2141280000300a90804000d81c2541d00942e20326030280e80341c80041e40c0d0ba21003981c9984001c01d00e2a042001700760008550454081c403880d00903001340e42c0c1e00015040e41c01160001100c0800d11004101181184140c05200300d41c0e41884501071909842d50304481c06203094034011680c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 516023444 1250 516022194 516022207
    0x10e031b040f0212060415060c0305031e0f09190c0905280507170103030509041a030a0c150f0c060e01090209070809010c052a07120b16140f 62
    0x990350080c20340412500011134580e140b9540d0006800801d0715803d000d5071410007808020000d540030407069451035100c2c100c030b4441c0f50740c1c200d5407603100820301101c8191000214404000d0024242e00803071000e0030b22030b0682004050f030b034105034004801c803110b03003454250342002441c0d00d019501150303040c6500180d07650354001243d00315034044001c0e04042d42810180c822100c4aa442580540407684d200c04c0d0030455180d416030103200c2800043c000ca42c003440000c1d850315142c1c00400c0c42d43e180c1c40040301c1c0d140c0c41c4000b192030315441c0c2d0411034450410490501c00c0658100d40340400f01e07003e25104103911858040540101d141400282101740c90742006420703850700b500030f030360b00c10b81c05400d030030741413409000090001c40c090350307402c00a508081040b260b062194040e20042c5214240301204102c00c004546500a280003100d49036001d15440095880d085d8020601d03620b008100e03402c0d492400c46208001040014442d02c24880a80140201000c10350b096682252131520866038618 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 516024694 1250 516023444 516023449
    0xc04050a060906080a0c0e101e0504050c0a080c040521011e0f0c03270f0f06150609120311161502010608060408180604181a010e031b 59
    0x7542195010605003400003424407400911841d54a01130030300c052045468820000c4081400d4412544a0081100070322828500010310b51240b100c01030f9030f0741d0f00d81c1d85034040390544404603480c2d8418680403e9180c0c0e10340d0010090380d801022081d40a140c6802c0100282c8445415000e100100c508091000c0c1ca102c000d60081e80114a40031311007a551031a008180c01900d50b80103000300340c1e410044002001070280c080c0d6017010240c806002c2402e00d844100902540c9031040540b680c8008c195240301242c0496402e2891500402d40070600c1c02e035a8591706212542d5900400c20070807007842c200100f5030940c205650003a41842c1084031100044411850000f41d00720049098a8298002615454502c80401d0600a0b030300207100850366800041d0f1101421074001d058544108003054610454034144482890018110f07410203850710800140e00c500f500c95512903a9444103030b0005c960703100c043c02c28656000d00e09220401c40000100751112015403419030b040c8401481b014856 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 516025944 1250 516024694 516024701
    0x203040f0b16080c2d0c09090a0f0f0b0609010602070e04080912010605090114010912020a1203030b0a0506090303120c0d020a0201060f0605030105032a041b11030c0c04050a 76
    0x1c5400c00380c2c030740c0c4641040c0e050385e484001c00301d01c101c10307000703400d0200705042804103461442d114000301810410104000b4800d0780341009040e24114055a400140080e0100300039010711406180340185412103480c0c94000f0120141005108481c640010405203a000880805564500c40c41d40b245480700e10303200c1040d0040c000d5541d8412594400c1c119000b5055010b10200c030030441c1d0046150741d0702d585080740e0121001c1c0039800106919030501600e44081c42c0c14104520252901c104a6600c4c1d000100b1180c00781002c0f000240c5a04078113600b4600120000007514040341d10514155201700026603030710600180c5917801c180c01d40003405040c110ba0550700811b802443c02e41d642c50541400900030130b40e0340501004101c90010110f03029102d0001e49040e207030040c00408607100414041079485a80d208501035680f041c401d90f083c5620359004005034040385050704520000700c50000303080d001c1c50403032035151580280030020342c0010026041d84440d50a440004894640301c5544000c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 516027194 1250 516025944 516025987
    0x9030a0e180f1902030c04230301020301030b01030b070203040e040f140f031312080a110304050d0f11150d090f0f030f14070203031c020d1a100203040f0b 68
    0x101e0908020806002c98803900707240324410300c20181d10001008203141089000039299903102c2c082c144014042110715190700700300760300c0c5001c54a95640c0315000090076079209800032225000250300400c20021000405604081240003650509080c9030820052030001031000d4124501c2c006041c0a1000c2038400050700c0c3c1440d82601c0f0944e500d4062310b42e50342d021810035040540c0088001a075000210303c5d00c4901035105040341d103003141c0740908407198420040c1c21074441c00100000165951000700c44504035202e414800b0b490992810319040001c03000ba003040c094940120300b0028064001e08441d0702034409080000d0412141c20969000b4242c60310040c0401040341c0e8a509243d04032810048000720707039a070b0a04002070100030081a0054110082d050f07802840304100700c44520074030350012010b004e4014280900007a845040d5004a02006451a55003448180718100740c0491a42c3c81c8041c00114509803516400e482002c0340381c031580700c1d031007404a001c01036008a442d80851 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 516028444 1250 516027194 516027229
    0x21070503190e01050f160c080f07080c060103110a0b1305120c04020f040e0610080417210a0606051c0203180610050307061e141309140a0509030a0e 65
    0x1517242680a100300e10030146c03a915200115482009401881290003040d895407050072039003080300401c030003a1160803655017115004d00c14440000d0048d4100402e034029070040141c0d451000101c0c083c8900320071250003001004004002c82030540500b11404800c0318001d0b00d40600e05183da40e0420b00b841d812000caa0341c0309000280007116080c40b200a0000d880f00243c1c10462a1140c80c10406100c0326100200c0c04039041c3c00010f0041546030b455481300c228804021450051159510951801c1c201c880006850f000c000740820380c846071003020040c11460030701500d49142e03c1d85140c140520891026142500080081c04901005aa4600345c44100085a240d03080201c440c100700c85c071070300605009224521000a10300c1c070a4450710401e0039018440290958512821500b0140d002079980e0f506d80300b000201d2040801744100001460703000300000e9104201c4107055080c403409000900b105003400140845043c0200450f081b0010703c0c14054640303590b250102e024178130140450031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 516029694 1250 516028444 516028451
    0x10060f0e0a0906091a03030406080c0306010c120c030905040b130e1e100f09020a03060b12100b031b010915031401180506010207030c050d1407090221070503190e01 72
    0x5542c0d02690000502030900ba18505030361780c43d41d003d250ba6030080d4490040040c3c2d00901241a84003060b005580106040c500042c4043c4261070b030300ea03841d02000b11040003640d0300c0310794400c0c184c3c024040e4000d400100c40910540743e01000080d0180387c000714010800e0b44d211101c0350105000c00c0300784105007911001940000c00561015151200c458a08102c5424502c20304200d400070b1154241c056802001d030b004190450b110400100803682606030048030507031000800040401009001d031082035000300e24440030900f41800c1c084441c0d00340c544e80c0760714040c0000c83d80c1c00660042c01c0d20303081521191004000c1e2411401b42c58040d10701c0b000c80500c0c1001107908903c2100c0309172090080501400346407103242c01240d542c6c0c451321000e0140c0410080c01d01c0395180102d900d4580f20f0080d900c201e000503285401c0c50610586034800d1011a038002415000e0001c2e480c00b110021040da1001900b034685014003501510000b0400001c0013610340c400f915160a551255421070034060081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 516030944 1250 516029694 516029699
    0x30b0307060f1e0e1804020109030f020628020c010507080403031404120507050103060e0f041202240717070504050f2d130207031e0203090d0503090910060f0e0a0906 73
    0xa4132881d00c9480041c0180d082400c112034580034000b83d24015541079407a20005803840d16140313505c1035122012a4001010041c258002e03489030400d01000c0c60030707904211005609c04002c1e240458000c502414001d050120300c02003503000d4241d5040b6034250801c1d0201d121b80d40799483d810300c503a07002010203000209444c0b0500c18001603200c2078031803c0e2804c00441d43c6507525070781c81070700459000754409107060000c2d00040b0350f18403100f0315000c01c1c0120703035018514007403400c0041c00800e0711a250114043c100703e60680c0c41074880c50b40760440200b600c02c1d400c04c60380081c00d40c4900c0c020b01d40039160359032003184c0e1900e0315101e4101c0d9030020221100c5812440010b0400b1800700400700d8440c0c0400020864003040038400c60701144e03855100c80740c62020100780003505c100c201840c0411750006100f004916103d14448040c0b05200e00055541c50190000700002100080c000500240e1614414000c840e0880000c0c00c00540b142400075800c4484000507000d0540d90b00001101410003900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 516032194 1250 516030944 516030947
    0x418050709021c051621020f0304060f090b040f0f0804081605030115050d060914030a2c0f04240323070608180607120c030b0307060f1e 60
    0x24022000304426400328142c082c81207041074501c10f40d04d10a0b43c0300071502055110b030144e02c0e407031201b007282d040500003601488501c01c1241c102c2030619010040000411080082a206203c2030400b0785104111f5918141c03181e2168070802040100805030110505060002150b000010745500c0b6602ca5501c2d42c58500040d142c803202c801e044001d00c802540800c191406005030100b850101d0041c0130568541020030064910407641940c103942d4909202c070205502d00010807090f12180c004640da00303000c850092600c1501c00d20041c0c84510070314100c0c080c4034140315030301e0900c6088032405010540400080c00810301c000c20401c8041c1030014003441080c2c140030000840e0f015160790304030949030504610450100c40c81847d01d0b078201b02014440030b07004d405890740196400c2041d610b010343c49480c0501e0405d05980540c0415103030165190300c40c509000c1c04800305424030303044c07012040400101c1c2e40c60415001d0380c0c061081d4255201300b014170881c3c0e10180303132003000e080c00c8960b408442c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 516033444 1250 516032194 516032197
    0x2031b0a0203042103180b031915080606010807050909040b07050d06030b06010917060a0e031b03070605060d020a06080a150b130609151209052d0714041805070902 72
    0x1117001c04c86010402e2444034005228408903903004888515507640d545d810b06102503e40c10308040d00341d80b0040e88030403445135205d1501500114008100c40c0c20a00005000e08078020306400821508102a0901e6110110308542182d0300c140240440d071540032069071140140a46658400d141120000500c9204c012041c02200f084e250354401540780c841e109014240d40e801c0c0541e650001d40801d2070180c0c1171348040030305001003003a00d003031505d0107480014490400c10b004c4440c0e030011400318180031540c80b131640c000b034048400741440b02055011036440b00ca00d1081000384142800000c400890703a4000b05800340c2180c140d030340c40c0c40e200d80040c45039030024541400c0704107004602240e01030140070498107881d030a50031000803800c81482192642506100744408586441045000440070440c0141c0303401040c0c60341c0c051141404859020041640f001503541d44640350400c482604040b15440166081da00841c1d0410760004455545074070786c44c000d00b50b1040c50000218103c1c40d50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 516034694 1250 516033444 516033509
    0x4030605130b15030601140109080d020714040c0807030f180c080c01090501171911090301110412060b0d0c06050c0c22020c0f100b0901050402031b0a020304 69
    0x380301c00e441d00d8604000c404818060300760f542640c4224018402c0303031581440040c03040c105151000800da21090054107103100540c0f0360016034440d84003800744400c050540d4070202c00c1074904000c40341e00c01400808024002d4402014556151410500e0311042e0b00844c034400300c2040001c4600d103440c50203800f00300755440341211714001d4030030360a0030350302c03c010000440c0c40507511440b440405201c07840c0c0401c000303004401802624101c0c071569a2281c060648800421900e8907110394005050500391039020b0913691015008010501000b1100445200314540050300000c1c0c0000703913004100781c885c020304054245900301a00223012544880180303440006041030b2082e400c0c43e08180300c152100304140820704280030048500c00c401076405400c10481c411b00b100c0c51a0301400015040000c8180c03111b442940b200081d608500300740a40f1401004256800c51552511455128cc0000400810681010b000070141045842001518040c225500e21100c00340c480036400041c021046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 516035944 1250 516034694 516034703
    0x21006150810030c150c0c14030f012a03200301030c0e0105010807050705151515040b040303052b06150305070f1b050609100b06190c080403060513 65
    0x90700107164802c40141140489a10000001140d410280c4441d0303085e4201d1449010401e010302c410010500d40c02212000f00790807041a030122403000c3c00d06040c5601d03005664102c0c3e04000300c80006110035090603007203411100004400b00d1303010a088010300003081030002524021040842504000401035048134800c000400d003d40d590251b00c1c854070000d21075103000c11080000114524000c030300034614140300b1000d0390b01c443d9140f103840b030241100b92194a02038420550304c00c1a801d003206070340300c1408103000c9541068034040c0031401511030b40c007000341006808112900c50700500072445c00040340f182070562074500c1804254000300400d10401c8001c40038045a00301150080c0706007030107141c1595a845503401424016110b084030440e945542c446c00e0008400030501c00e1000c28080d04000014181018080200c42c040d20450f5950074403561003004020510710201e00c88605519190500c1c03502c0011038144580310340030301c0d0b1026004900b460100406a1580e44900f252030303205 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 516037194 1250 516035944 516035957
    0x1c03110c04020d0f0e0a080304030302070212010905070603180b010506130e0108060403020d0e01080708101211030c0108130609050309060a020319031e0207151e180206041502100615 80
    0x110315682e9000c106c5000740c1140300410200e40402c0c482d8008011440c0040c00400d441c2400f10880c82c212801000203480c6074201343d1341408000e80c103004034460320300105800101a03546440300c42c480c51040c403c2c54480c0c9030000d0f90b4003942100042c0c0d400100748191000400350f035184c881c181c40c1d5004076002c038018001e450170080303103034058443c4240b16401a5600d9006940f8103a0944140c04060440c00c20351b80000c0780011960394075030a070110148604c1d4070480808554050600d4068a981e41d0350600003a03200704001e8030402100d01040c1500b00d900401c2804031410858114420b25108941180b00050100d90a03038002000b04464410001e8400b187d84083d00100e0440301210181151944810350242d11018181c014000380d0b8002e091a40c006501c0181038412191b00e0030f9021000d04070005103c40c46506403103211014042401c51002c2c40000b6400180317280305134001c034007000c8401244903888038800c0040d42202c0000712810040c407601e407007c001c2d40350740304088800004d07070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 516038444 1250 516037194 516037211
    0x2040905060403111506060a020f01021621020312070c051617010b130b030c06040f0e010b030601020c0405090c0306010f0807050604080a0305070f0614040209061c03110c04020d0f 79
    0x1c8505d100c40f00850b41982e1358440a08102c01c40c0d00124a180031882254203680c203000b02840144015404403040381c800d40f0641c0392100014074034850801c3c4068108441070b01460f008001c0764072001e0500c0a60071250345007181039411000781500034141c0d105070400806c12211000182058810100d4900340301075050f8205400d076541484540e0f004021044c00000c5d62a058010300d1918000030195042095298045003540d00658000704e1030a208000820864080c004003038054280c010009243d843c014001179922a90b20345124081da580b00001070007070b0024042c640226030001c0c00c0c4d9500d560b55032601118060701c3c1c002d61000d8020041c00280b6072820800712000c0341c1c00a40500801c22036030300c06459a40002d08241c0b4240c810707428800014072580300700011926210085001420240180040900000c09071406001c120401c2500036424444c11842a40e06240605011100d4000c190404107038140b0310f50481c1c0040f0b600b00300341401d60841c03169031070221004c0141d203c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 516039694 1250 516038444 516038477
    0x2010609050c072004061805060406060f05160f02120c10022b030e030318010f0603020f04110c2a01050406090314031b03030f0606132102040905060403 67
    0x4262540140030410080110000c004555001d4291040017000050352681ea1202d240321b0b01c5100c032050395030310b60315002c02615241600c901405003c41e40741c0b2050840e13400c0c101621505c46d0704c1180f10b034414900d08034802c101101175283d4480358050035210110029200c07441e40c03248200e855600c5038400203d01c8008a10008007400e00000380118640c1c6442c40f41040c80409074003014840402d80c8030b0484212500003080110302400318020b000384042e00c8041c045085a00c00c00302c681c00c1c2402c1103810070240c1d0b0741804110000100302c400040080c842c6030844114070580703007080050b000c1c04000107100b46151040d8400400e0040a10314441c5100004440e541300303038003412001c07501c050024004155a42c0c0401e080e103032a0001c40340f900c071000f10340400d14040e8080e80920f0b60700c00000c00010030014807a4075001001507070410700382410460058500182c500403c4020b2914000c19001d2a43c080c80a134610f64014108002c81d050a040c2603440365000c94080c0c01080c0c0c0021603043c2d20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 516040944 1250 516039694 516039697
    0xc060c02090f07090b0928080106081f0b0a030b01060c1406040206071511040e0702160f09020d02130b04030201020d0c0203060105040507120c02012f0909070c080a02010609050c 78
    0x154420340d224000c13107061400c540001e400080185404c0450150030080342580344102001c08450040a06029454a0402c2d0700f901d48680080155810010744d04084154400312175982859034207021070200401c5d00895004500f550010b001d4410072400041e0181e040a01164081e000d0342c00084841901c0089660704c100c02da80080d00038400700319003400b00e10310061f0044001081d00001c100c40006600000b66600b0641001c03a6003856101441a5075804014030b510100007903441c500b032585440005600920640708040c1e1242d000108185280d04070750480e0007900d404132042c0c1c01c6c01d8944003500010317000b9010403400352040a0140004038081c121400c50349034000c2c0240b2071603003040144800b07420049c12075010300c0201d6880000d0500c05000d00b8000207600d500000305144105c04120480d11301d00030782810598860194001d0500c401c0c208d600311401510200019200d000f0200d50306213030100080d010b0070004c100300c0d01141d4190000d0342107035504042400740c4c0e01c0b040030700c038540d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 516042194 1250 516040944 516040951
    0x605030601060e12010e1b09040b0f07050c1c02010e0610090209060f0d0b0915030303041b0b19030f05060f010f03020c0f3a050708070c060c02090f 65
    0x540c003510040090501c621112041840f01401030a44e6861920b442400d5442801904010b6040b030070800407490083d12801081000849000489007025150035800030700c06401d526440070750000080d60540200100c904c10b070310b50b0049a200b6160315004850114514840d1001035013000e000c1e407122000018041e000325900c0100c0c1c1d8402c2e1400100070000d43c048028146c000c02c041c060059160744a10141c00401c9140b000820540240c0f400c004440c0c2d0018000b89000c8810242170415440000aa99202d03511606500c03490554800f41d1494516070380c4604a000400210141d0800c1c44c40741125600b10191020b0100c50504007819041d140125900c40d04644000d4207a0442e40c400e5240061400c0503040040c07410450510841c24034160320b500c2e1000d64801d001d544000140c817040e00070041d00c1c2440d440c003123844941d00c103c1841c40040e5682c08004011902405014400702102c8246500800b82c000b880e690700d40140601103400d00580c403902e0f54000040490f400807203070070311 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 516043444 1250 516042194 516042199
    0x405131b030c02120f13061b20030604150605010206060d080306040b041508120a0203090111070b03010303090806102904030602030a0204150e010c0f0f062d0605 71
    0x440d2900300d5000c40c000c254a00d0711100314840d0307112641c4901803031001001c820b901045095a64502000540c01406079030784484200709a20b401c1780e03c002c5101c41c1c0e81c0c81e81a80207921070900308459001c80c50607107029411907854050030050004001d80c1045410040b190040e0a00c1065900c2d401039865010448136940c204c3e400e20800e10001d814200210380c4000e00900000c1c0e010510307030203e4125002d80ca1510a03800d00b010041c0203111040010034044020103445902d8600d07483c000944a01403524054140b086212085084400038002070015240700c14034103480c0d40e5a814001c1164400f0700c00c10003240194001314907000710810b1947c082d148030f060303000100071180000e00040582100e000d500f4400500001c40000c0c0207000070340c0540c100d481c01503100c900f0100040c1150380750681001c18801c80c12020880f90b600301000c0d04c031342078018450740c80504042c241241100c401c81001004a40780c0709942000000155044020942c06820221640c0210340103008a400c1d0740601380d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 516044694 1250 516043444 516043481
    0x506010207080c0916031b1107080c060708070c08030a05040302280314210d05100e06011202120a15060f120e01091203050f0f0103081207030b0312040513 68
    0x40d245d40d02034440031801c2e84503140010305044508690040600401c40100010700030f4400b60000f04010401c2c000a400c50394044d02510901ca0009032851054540c01400e82002180e50b8040c0700070700501300b00420605081e82d94641402400030701540c414002248111503000c860a400700d02d00d0240040c80081000301c030849800c50f1680b039011a00c1044041c50340c480e01110b804504400010b04803040c01044100740c4644002c104035080d0303140203081d40f42503144103904004070030500c14800c6d00003400303080500c0c1a00812150102038410381c0583c4a81042078807c3c000b40f08415481100341c0360b075024400410948400040781c407265885c2d4410b00042c40c3da88942c20580880d030001c0c41d600c000d0f60002440c40900d40c0d03003030140d1400d807641d0000310340e0b2241080b0a079060000300c0c85e0300075116200740702c02c1e40c1541e8400c03600340641d084c2c0312000038010001820050003544006413480d0000d00310386a4166090075881c080e402030003881c2c0560f070035144e1a400804140188820f41500f4030501 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 516045944 1250 516044694 516044701
    0x40e151e0f04021e030d0305011701050402010c060c02121803060601030b0604030b09070302151b03040e0c22090b04110c0712030306090c0806120c031f0e0f010506010207080c09 78
    0x21165844d442c01c030034000a01840400210364080240c900405116200480c06624000202103403294150800040c0d074104010040145e0380b01175514048e9602c1003000030422034111040b403814001400801208a0000e00030403081280307161010030410480480d4101d0b51044011000d54250a81603900a0b0b014003003840080c00f0515055404824802200c00003a5070344c000415a01603100b45556800e800920b0000d00a100c00c0118112145070000310310307003807070b001480702070250080c2000040c41001c2403040940701c000e0769a0008070103400b80003440303903102d00009000307004a00c4007078462884c1c081e070046103011000540b1082401140507001035407030101d240702d0b00c18400d04c0840805580d000e020580d20001e100781d10701a034099590000602e440e005010390403d00c200701314900e038005c0c4032803000345d600050f02c81401c0326121001c50b00360440002201c0540440c1100071a10f004002e01c070340700390205500c2a84640301c26421107100235600c0710360b180c5550000007150340104688000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 516047194 1250 516045944 516045949
    0x212010f0e060a0609121e0305120115020307060b040912020105010602160f0b0a170412110f070504020a050708030c07033203070e040c12050c09030309040902040e151e0f0402 77
    0x600d00d030540504840d04d0072141d2030078039147c02121240110082407000c5030710f001d055989501d480c090301344890800004200ca101c003941d24002c2400c000c01030380d25034032410069100c5e038100c003d038190702181c00c510061320034030084d0181a09014440041c41891404070039580108000ea080350541001800c1660412000409030762020a0345801c2c04100324800745081455036140388128001d043c403812030004e01e040206000350117030000c5003581c820f9500d204205ca0204401080729412140181c0d5038506aa0507102c50003019401340c00a0f10100c1008400441d0320001c01070184030ba600c500010400208000c0c0444082d0b032420344080948050280440c400b0f001541c1060650801403030407181480041d041d40e0400d000c29002031601040200209418014240c016683c5500d541c00c207540c5034082a03032401100040e5218585500c01d40040d503d643c0d0002e00101e02000540c0e4035000103040340d454940e029241d1170103500c0b50031070407a280c6c40d01e512082e000d80c40c261a10405034a89808 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 516048444 1250 516047194 516047219
    0x302130308070c17030a0e01050c0c12120403080409110f04060e06160f0210020105011d0c1e0403051212040209090705040e0c0102012901080a0212010f0e060a0609 72
    0x90440e2440301d1900f020405820038440310031040c200000950341c40c2c01001008001141c45040b0f607042c0181841150341035900844e0418041c02c05451300358143c2c1d42140d07101e01e090754014482248650002c0d01000b0700c07070313a54014415504002018014140c4190b1048002d101b1401502443d4906010500025218050300031600500805290070311440c0040c0140c00481ea000440d81d45000400c50411400e2151402e0f0b101c8285000802031985002c004002c1d10318030503034041c01c600a90340010810580c440984800c515541c144403054a02c20301030001d9076000780810388480c41141610b40038000900111111200f012110292a8549609001c0900300151150181c3d01904801061075161b51040b1504040702a004100b0343c0f000d0380c00642194001080310741d52030303640c14010045142103050925204001e20303020710300341c2c2da0800f0803000340283c1100718600b18940000140c0c641d9441c5004041c2c4407d0300b0744441607180c190821a0382c2d141c030300c44c21011442c41e0320100700741101043c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 516049694 1250 516048444 516048457
    0x1d0403020a120e0a0b0a170402090a02090d060f150b030c0901031d12030601090503030906070f030507120e1002191e02090a060305010c0c080d0903260405010c0302130308 75
    0x8040f03da60160800140c206002900110070b500303c007050103021146c0c0a0a1100100704004000019007072940114101440040c0384044c030640000380c0260780e07150800a40b16058102c40100302460252205101a000d401104020700300d090300040782c10000702c0c00300c1380900c40c04500785280040503030041d000f400000b0728024440c1410a01e155008105005002c0c1c500900f0240581c3d03840c040d0000f410800540e003110b40640e00c24454650a07442d01422a891150465141e00c0001c400749000c03201c603c2540b000516005251a02c600019080303928a5401141114404285588000126903881d500c0000c0d01d6410010408a00854884170300501900d602c07040c2c0e540e40100940118101d454142c4000200c150356040130810321400388191016207105281100321a4070300d4440c02c1a500808004100d0159500b0300d500405003e02c171021b04840c5004169a0b05001064501054110403a400d4640f94206089142c21910034401c550000720706888150070541143c03900b40c0650040c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 516050944 1250 516049694 516049697
    0xe0a0e06010602031c11041509232d0d030305041101050a1704020103150b030a06080706080121151a0a080a060f14010b04031103060408031321091d0403020a12 70
    0x20007021455230b0800b1003c1d41d071085c0c0d5444101080740b5086000c02d59100c0b115801a143d01c84c801031410f140e90b22a0503007000c000c88485011941c40c4070103002403c25001c80c51692202c0756a00041c10150150041d6219a0041008143d50035071030b001583c0a100300288500051b0710620f0701410751b005a200d0541107030040c580000c460407098959403000850707800141c40e07039002004129044002d4020318014008010150030070a00c2c00c1800ba207608010700030440c0d220704220950009404000c080604950000c0503098141141c0705001d0040c840c904d1035030b0381085486004401070906144617030072900080011b00c881c03015912032400801d0100c46410807103448582d45d01c000d024203014140a4846008080d6a5030300e1450600700721740e14030704428042e402010800c4040350000040c1c2e07a000c08000c2e00d200700040ea03890101200302e80400038012101c0900101340780d0030341c040c000c1416a00d202c7e03080003403d1a5100005440301003264001c3c0181e2050020300d0018a4a041030340040c20103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 516052194 1250 516050944 516050947
    0x21020304050a0219080f011b0f0e03010216060e0a0201020d031d06040c051e0a0918390b0d0207051504210804030e010503100e0a0e06010602031c11 65
    0xc1c1e40c009411300320240d00002d200380002e181840260000c0c00f08030f014884a80013080700343d04110400520180c018044010310035034000c420420f6004280782c41440500400071540c490300b5410003c1000701607901600d03100e02c0d101c1c4001500f04009252003035030790160002d064150031780d581103001c0c0075020a2803007140b520309903017918100708100c190f02580c400c82443c415241484103111140300c009121030080c04000484041031380310642400e0903202c0c00c000c04584c3c1c4c0f403590300c0720004403da10f100520055141e541231040581341d100b1603170303007401c036200b005034044104403009840e001c07030b00841750f00320b81c104141c00d208060356004201c0f0314440c005440c0380d11034070400d20324004800c0f02d060365006017544590281001c0c1d03805108a041d140c2c1444401410192400dd084c500d24000d0141401400804a895601800c400c080144011407180941d854500000d00280854954205041c032a00d400894258004010341d21102ea0400020086039240911040034110746605031456400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 516053444 1250 516052194 516052213
    0x7030915090e0408360609150c0c01110115052701270c1704080408010e010f0608030702090a0908121f05010504050109030602030603010e071d06012102030405 70
    0xd014501d5101d180501c5100e600c1e1710303982ca030441c003e00e481d13100c0c040c0866115481400c1c4144080601241040654055031506000404036081da284295180400712002c80e5001d0803030303030015100c419448203a86052060605088103400c0c3c0781103482c4481c2000c4602e50600403424881d210303880c00403841506900821341040441c1e41c901c0c0a0300102c06244000d81c100c00b0582007050b01da0318505c0d800f0410002c44080080c01860740c40210b641c4c094640000001c2018407070a881a1005002c2a07002004410022619039008010f002d222070340060422500044d044008001d0340c88594000e0105000c60b61451300020040280e4402202d030048107218420001c1050140684600c04a8503011744002e560003004032040415070000381000001c21080c00281d0307001804070100c0381c0c441805070b26515540006405000c0a000d11103180c4241e110005040004243c88041040310501c0001240c0352440111089070340d6109101d04481d5400c4882d8103841d40c4e900655115014074161000b404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 516054694 1250 516053444 516053459
    0x5010f17190305030a06050604120305030601030f06080f07080c0105030403180308070c0306050a0b0f04090507080a0c06140408030f0705010906060b0306030c010302030f130f0605010e0106030b01050703091509 92
    0x80c100700140c000540200c108520090b142c49903c025060880d026403c1911b03042c02403444000103240103080000220114040380d0103604002c010410701c1c0c03402e00219465008042c5d82c0d00041031484500d12540500058901c1c000ca070044034008107a482c41d296a030790f52019074001450492080e410242480d0000c045108100035005540c0706030312900809145040c500c007a100050b000010792403501240702100d566038403458000f03110a84000c6460717111420914141020ba82c007400c440e0007030000301c10402c00e52014140076204551035082411080b8041c500c43e5001e05e000b1030629600410038194003071244030140a56911441c00232500400a03070360b46060314010b504c03244034041d0200500030b00b4503042c84006045c02d000c1c0707001c5080d840c103180035440484000d032120030b00c1e8008401160600c600c00940c0700e0340e140c001c0f00502a5507580c40020003000000d100700000603150400ea99403035880b072401c5508141d09039440c1208e05080c00740080d01c440e43c1441200a10420140016401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 516055944 1250 516054694 516054733
    0x30a030f140708180d080a0b06090a0e0a02090d08030601020610150302030411060a03060509070c0b04020603060409080f070204111228090606090b010c0507030305090f0d0b06030d0305010f17 84
    0x24082c0c0d46c1c4014504116805606661403070b61a01d108801c20702420f101510f491113600115110200450b02944a01c2c0c6404001e01c54541055041111071240760107006001009600692080c0e00f110000e60b00d50703021051002481c020142c0400c0b08000d02154a0300c80d070003950300140201c2d5004a00d404c0000041e41d07540c40031148002003a1224810409031401d009000d078084c03407a081114440e0070580c1c60012206004000038402d400200100d240d61b10f4550100c6a2198030003011030342c40c1c0c07003c0314011142c0c104403000c0340701e5820186901c1a1181d240180c46171800314a0300a44607488100d108620301c5999111005195400d500304000d0701c00c0d034007071411101d004520000b1005c3c00d102149040c1d45aa55074a418042580c00200c00210001f034080c003180d41601d07000342c80b8054200000d08081d114603503580d0000100e040c66042c4801480028013401302100cc8440c6542440c10942c2503640901c540200301403054800c00c0f01a40081301d481d00e0a81103016100103641407088007015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 516057194 1250 516055944 516055963
    0x703030b120a052a0402160c060c060c0207150509042a08060a1a0f0403060f1a220b03030c03133206070f1202030a030f14070818 57
    0x100c0e0310280850003800801c3c0119a1112410ba030714420700d01000031444084c0c22841e920900680c2c0c001a15142d103088019039580780b5030301c6404909055503e410081c40901300c0e090590b4407514200c50150150300001b0340c14110f52048001a407884285030303058a042e0480d103680c0782c20a03103d18945c82c02c001d4001d280c41c244400000c00d4890345174290f8005000304070003402e440c0520b02403041881030244003402c01d107000300e15000281c0d50703942a084c640854052a48014099410200000b40209554210007040c4424610000c441d12156040210700c00c441c0e00103489081107801c2c0e42c940000b013604000710052004c1c00f103d1410f078050307a1891642d44108000007010302c5054080c04000c0d184000130405401031415818039a1401000301109264800c10502c54075001803140100100c03001840b141c907402003c0c0080d00e480310b18001c1d407650304c181280e00c0000d04d040000403603070180d0311440110300e001c3d4a442e0140da0300c0c0c001c243d6136924080c200ca1040d171140760007045200c004001c04902c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 516058444 1250 516057194 516057229
    0x21504082101030506160905030c2e0504060e0402090121020c0303130209070906021f0b030f011e1406150906030718090203041220030729010b0d020703030b 69
    0x300b0314003141b048589804034900341c2e040080c40b0f030080066a23800907001110304e504490764940d26062500c1d864902a9400b03043c101c140384c0a41c030340841c5422401910843e25035885a5101041e001c042108030300c2030301511030200d842c00484100e1040d403001405c107044039500005223403c011030041403840d001280e07800c8544050912420841c2005c0681c0c42d0032101605149501c5414200044d481c3e0003284101c1e490040e802d0700e01d0707003d1480da4100400054000d026038401c5980410202d010380444100d4008400107160180d0021109108039030600030005c003c2041502d8000c10004e1650002010452801040c804001c607030b580c0900460144d001911103030401b0a00303d030080c6191143d82e0103588014414010880855a0030b07034090036200440c40c0000c551100704110b520322050180c2041d40c4c503c0045088820040702c05030441c0000b01d0741071010940b4402c4180034807064000d000e84890a60180f080b418403180320b40181010300c0c42070030045859802e090120743c1928102a6030308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 516059694 1250 516058444 516058453
    0xe0f0c1c0b130207110103060503151302120607020d230f0f0f0301150216030318090501090605030f070302031c050c0102070303230727030c060305160215040821010305 74
    0x3420400102c45d090b0a004081c201405068075040c00203171910780103803828030b40382040c0380001c0e099510b681620740c000354003d083e10080011120203507628082114084094442e805030355a1441c020b1100c5007008218610354490b422841c46690890303000350481700f00605084c00881309401d6050f01814542c95001c8400c2c1d05c9614101002d01484500340d03800056400014043c103029040c6002002503c0d014101003510004412078500c205440d640100c0445242c6800410b0071440b540000080314021422500340c3c8910044990700c49100d807200070340c96400030702802c1500c0c6200301c0020350303050745052190829510810345405e90340050310480000b0b6466030300004c04480f112070009140880c0380002c00500d0910ba000c0c1801d500c80c0c060008562003401c16034540200b01c0030b0500036661194003044100d54440b0042d02038035081d81d0510640300781c03145500b1074502c0011045a10910140c0214640d1959100e83c86035902c1042c91025000c0661009106e100c0c0d015041c90007188180004c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 516060944 1250 516059694 516059707
    0x3070524160210050313081c09050102090123190c0515060103060b160308090f010e161509140609280803090906130212070203040e0f0c1c0b1302 64
    0xc10740d240f002d02c0180600800340140508171402c402c860404542c00306600b030f6034030b503100700302100081400e542401e110b040c210350310208401900034082030b4001ba2503c031300c1c031a00d054501c183c00b04904162248000e050242610705540f0700b84e046034403450f5003814120203495407162414442d25a5000a0031061403091021550b4544030b810700a00390303030441314100540040c00d0101034800c0c00002c0c0c104480400811a01305040c854400e04054400c02041141e618084694075034503956286104041100b9000035a00c2d040b50340c4010110640ea6074a144900b80280c41c030440021000c0150800814001c844154417000c96000d04102108d05504800401144142c0004904e40025086c1d400c1401a81080c0d181d40365481e4210754102d0341c04c3d2505c02c001303a80c54000d001d00d100005951445000340314503503402100800641d81310240e040902d0f80d4040c25030030020401c4d50281c8506504200405d464680d0581c4511180005103000c1110703100100080d4030031170041544d803401035002030754 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 516062194 1250 516060944 516060949
    0x10021605060301030809010305040503041715060d0308130c03060c02010209090612070306020f0c03210603010b0a12240b13090803190e0102040e16030b030705241602 73
    0x141001010304071280791440d0305554031111240620390300e90341410784030408102001810700585020f000c4125094146410b1010900d940b02c080c103800c800c00300c01f40f0b0702140c1e0038200380487c0700000350541c807015403540750944c10440c100380004040e101001c0080001c800520140540548580b0b96400943c44010000c10000054005004584035040c6603800310080c110114003242126009007005890344000701d0707019401e00c24a0185800c601001540800a96000c3c040e50800a0800c0c01025a0761f80c00086c9803c07030b0745600700355912102000007080381a031306006c02444640b140a2a604008c10340c1100c54110880004800a164550842c1035050402148520030b0034181d16051002c0f403880e4491007050b104c042d080e02c10417801001c200c0b00a61154000c0c410581d4450700071982c0305c0c1d903000b2860603604240e54500b9200b00241000407824468040c06841d108018040c1103801d29210806c010f0f002c8480910a042d81e8100c0001000c83e96000600340d0007900400f5030400e41c46a104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 516063444 1250 516062194 516062233
    0x20618180105090a0e070906080a030807080912070807020d03111504110f01020a08040312030e0a020a090e0c030a0804150206090615060d020a0e0301270b0a0b1002 72
    0xc00e108400195004011039500c407185960080d020600018941800a00131818901941c100070f02403800e140c000500103100050140c40c4a0203540c07402010348481604440b83c01d015203500d01d46a01500407614800300400060644511070450a0700d0820103030f000c94041c03000c0b10015000b04500d003202490144040c0304200840c450000543c04510b444d40d1078202801e4400318141c06050132803804020341e4002c120012581e904541c0103615266689480107000d11000c089400007402c04170071204044000503a1143c99500400c80c01805083c40d0080c801800c240407440c1843c40b5010584801d03440070b101d154600c0340078100c665039440c1041255121605002c484808640c080c60810165040100f6101c0d0460401071201c100c54468400113004d5015501e101c0f104035200140c0502d105070020760030800301a05400900c0b10382c0103010302c050643e1030301a003007550111440f41800001d282c5900035902400302600041e244400d14007042c601c1c0d130702e40000030142c1d001c2c0904001d1b021604c41e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 516064694 1250 516063444 516063469
    0x303011d4b1b2802071a180a0b090d0303180b150604081213030b0c130503010b0d02040504020414010308070c050904120c050715050a0e03151909020618 67
    0x4072060310f841d5001d0003901e00480314044482000c100c040c5081c00191080c0b0480d0018034241842c82030098864251003025801041e0510aa42ca00d4405180904004502c4000c5030582c2200c41e0a10300488180002860803102c11010995611015102e0b500d04080426600c0c0c020400780c01c0310300d420348400030312280448040344680c0e024002007121042c00030700f001ca0500400c0c515603c4085882d480717040d014590b0802082100c2c1c01081010003483d460242c15140d645c401110784550f40c40c01030508130f070310000460b6001070240d01c00d0030250900b900482c3c0c221344003900000b0810200784402d080c078442030308111020380000070500188849400e5100181c58104d6000d0140d00b0640c1d2680100b00000d842e0006106210b0f58000c2407143c14400d0f04004d1600c044c0388101d841c801d040003050f50380890702c0400400c0c081c05c11103509040000f804610180000345113a41505c914410000405a08410000240e15100e8550041e00d510010300003404082d03541e81c119644c1d00c0c042007181c1c403606 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 516065944 1250 516064694 516064741
    0x12050705150124050d020a03050f1819030c021e120f030a2a08030a15050d111201060902130501030b1005031e01080303011d4b 56
    0x410040c032400800f15400c840c10104a490380308044084a0252114020282d1100c2c01d00d1010a8108415400da0071941c842c000c2941a5020341d0b0f190071100b25580054004030380541c0c00b880b548800d140360000c440000b18001e04184012140e503a0004101d848a8004024200140380d0f012a17a414841a4038440700c030030001908079210b000c000c072556030280741d40030010001c240c42008001107001d07220742c0c4c42d01c2c035010340460500d03454241009140d10984040003564034001c215414030703a2888a90701942c2000703100c07004281d020348821074110140c2904681c01f9001d000c5031440c4141c00d11400c00207052a04015840b40d0b41000742154040d5603611680c10b245c184541c090055480001404180d491820925241c0c1c50344d2502854800642100304078a800002c00407441e4032000010b94100c0f102c2180704211000200701003503a020303080e2002115000d072103c440d4840d070300818101c0c017200c0c0980511800f49804504003150004038007618811a0203120510007841c120703080620055214 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 516067194 1250 516065944 516065983
    0x240207080a0b0f070516030c1707051c1709010911040506060304061a1c0605070216152a02121204030602031e100602010516121812050705 61
    0x154640c10002c040080c03140f61400c80800000c0c012a000303074150791000c500c2014901010b140341c0340c041c1480c4168101a1210039400341c80e01c040601c1241121105903002c0080d0140611840d81c0e00c80582007000c865061040c0040100091070510202c680301d4001d41c0c0011801150501380864510640b280c0c560180741000200728954803248201c0c3c0d0055800f850000702c0a60041c00140003a415030146984110b0508140c40c10743c849164515031140510720030801d0751500c05059070b44002e1041c0308545c0d003c01200403c01c80030654050b40203a4664101a0b414800340641c208501e002e00040c07013020b503030003c01c44056003080040e0101e0000010018150380f15011072040311800f9511000302311a400000040034103540654804014640c0b624105c201d040a2045642a01450103803400661074417001589010381004140700ca0607968960b8408075100c041c1007000f034890603d5480d010900c041015000441b000d00381c1405035404d55a26494100e645017180c10651581c0625000840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 516068444 1250 516067194 516067213
    0xc021f050f07050a0c02040e160f080d051b0109140610050f1509030a0b011e06050d0203090c090115090e01150e0307090f060f06080702100c050424020708 68
    0x1c1800e03800d4101c2140e0814a841c2c1c1002001100c3c1c4685d034010013034100d4288080d513180944000b64200c468031219070b0341101c1e10703120090b10300c3c107207502e1082508552203a0071010a450048004020800c58020241c0d0700a20403603281d070944080030401c40c0d51840203e00180018000d01c0001d8200000b1926000024900b80000e0a002c0294861034481c1401007954030800c00380508a5144840280c01d442144147d410401c0340d40d54240709160002502201c0c1c1c900300740703c00340120103682e80340c0c6429040030781d0200404003c0d04020161005449142d0307a503040d9507240e0321603034020400517807a01400d91041c04018481e0603070b54805840c03140780c04018001403c040b00c485a51200c0340c60008803003410344000a10b4081c13941e01109a2034503060807100380880940010060b80d56282405202580c0c0f03000440e051301e403c881e00c50040c1c00c214601030102c403454200e001100c2d40d81c03400604003502c40e8540c0f4101c509805101e11004025503200a14580600503440208111400303802d00a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 516069694 1250 516068444 516068461
    0x12180608061216140103090510060f120b010303052a06070e0a0f1703040f080a1e080313060b130e070f050a15020a0602040306020306030c150f0d020702040c021f05 72
    0x24050141c4415055484005540b1740d200740e004c282c083d6044800c91342840c056a46000081400e1300480200e00c01d414008640074880e400b029101c90761003004142aa0b1854130704030380d5a02f0204101400c008484490045544100da610b007901031200007801c2c903401c4c4034401030080b00483e0302590140800c0101005011940c146903002c9841c101d1000c0d80c42500c0c4404d032421442076401c1116001c0c5030b00c8001c0b510302000118030f80d00764442d44241d00c0d441883d10600e0001c00340154020302140f003c000003080c2c40c0889004012a80c440c0d5004200d881e00e00d00020207a50460a44e0310031240d0f0b078500900715400030040d01300100704011001c1c9500d800d25003c500701031580d01684204001041d51280710740d100300146920640c201008540b101d4a0f0f2800c0c2c0041e50041c0c403c0d45c864441d0304103d0310076213001a6542070380c0714045025403400c406480000300a411142c00500312603420b00c245e07000340c0c41d140100c05a910080c0c0c0501225081c1c000c42001140a039480000068a444100840ca1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 516070944 1250 516069694 516069733
    0xb28090506090a08010c09090c03020414010f0215180c1215041703070f021c02100b0406030209040501090203060a050601020c04110d24061b121806080612 68
    0x118400e440c8581d5807024403003c5240368003960f008501542c03034102071034a03480d400440304080c4c80300050140400c2c50f041d0001c405a0040f070240300c11942c140c82c5030303000350b40c02220489460304039030055454060f07260640c41c1075002c0403a000070740c0e1902090008105901480030840c10502200c14403903000e18007280a1f5034211452110b038204d0190f0000c10705001c000c0000782000303e1040c201e0740d80da01c1c01040040841d12002c00c07143c0503200308028a2000030710415014681d00361a40200705600700502a00301070011000c00d01e4003d6a200d10200140e00c0d500007441c4264007503800400d4502c85c510500d46460402087da8421038035280a001d0b660303074041213840f03c02c0070445e0041010102521011428070500c511100c0c07461614000d50350848240851920201c42e444207404910b90380c4c4410381d5407209088048034004030a09194000a211000d0141485441e183c0010b00358a01c4040e05d040c440290000d43c04981c540c01002910301d04030307400103041480d2502400305a000c104100640 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 516072194 1250 516070944 516070949
    0x1b06010803030c16050f0a0606060e130c031503081222230a2d0209010b1b030d240b090d061b0c150204030308150103060b040b2809 58
    0x2290340024081c0c900038014040d00041c41d81100c16a801040c018940c1b903990001036030300310313007090a0100014100740900551000420080c02030f140b5804d41c220050014030f044801d54043c19a200303402142c8904541164010394400d000c00c513035a01c0c10302c00031102100010700741510b103021000540c40792840040c0700d50103150b200c07070905e030020340510000410b259100c02541e0103205015200302400703030080040088400020b0359010500a032403000c0743d148030a090107034000070903000410040d100b40d0b0050072144400040040c44941c4070f1803007030641d8800360304448516141d0041250030785510200c0d161304648004c061209a2420340c880704d85001b0b000400f48120800c005803c00d001e0035800c0084c080c0414030041000e00b00e850800b902094000b07400740c441e1001d400300791840c0801c5100300e500743d981503107440c5030381d0b0b90f03803002034010390454000d0f00c1c100350b291040043c1c0c2000010251010380b6164407181c0d142c03c60195000c009007042c2d40321490b84807000740d0315101d094010790741310203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 516073444 1250 516072194 516072211
    0x1e0304090b1305070c021509010f1d1801030308090303040c0302010f0c170a200c0d080702031e06060301090201080a15030f050606031c0801140d06050a021b0601080303 74
    0x3481c0c00304030001011400080c600c449101e0510040010382548a0014549944219454070310401c81c150030440901500c0009070100b202c1040304d080c00c90048034980740001e0020504107078014500042070303002140c0344429055501c000d00500405401500d000d600c10211b400460540c5059181c5004007d03030740c84047c0c14014030520508141c1c0c402c5481e282c07a550083c105192440b80e18150a5242c0e05c88a0083c00184640c99140c403050100c2402c0d03a2088180401480c107003424804002c1e11a84440e0704440703e4001700081d40050324144900100071418501e100c0060b2048550b1038204140202040e1099240c01554070060307070859410354005400e06d070001000100c50304841d45e42c9c28180c02c00b800c0d49551164100400000090b06841042c0540a0b00c40722180028210301e224900c0281c1400706205000601a0345046010724002e00d1004041c1560302005407100d00440c1c00035145401a142c0004812025654103000080c41220800080c009585024042500c0f070001034040f02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 516074694 1250 516073444 516073451
    0xf0424030b0415140c0a030e010e07061d06030604020f0c010509030d0e060f013605071701030b010e19150303080108070f0e0c040b040f0f090b01020a0b04060219050403051e030409 79
    0x1481035119600c5a10041423407402044004403e8404030f95401c014030070000000c0e0103842e0706404140440c1802c0d00400c0241c015410764a81d001080041e400124841521030402e001c10301c04441c090003524003503c0c0c0b42010356550317481e946203031095404180c0355002c5d030381c0304805106076400d20b4108a41152030b014400310400350021603510200f041b814008a0b020825143d20140b1101d561010f801030040717031a02d0f540c04c1501805a855103100b440b02401e502c0c43c40340100b010715101d8400e01e07804043d00b070070300c0303145158030038280103c8407a068015030041c40040203004244d00062051f02524441009000d12440e100c0c000c0145c100078003a0b880a10914400310302004d203440d0517240a4a428000c0702d44454484060784101c079124032503806507280300100090600082c0c46030ba1400001a4054907200303a10340c81d05403a803000030b4401c07202c0c541e0803c083d403c2c91360041034071a510b01e00b0f941e61550301c42c5941011850000003811030611107609041c00e10b440d5074004101c0d41241d00021010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 516075944 1250 516074694 516074707
    0x303051207020f030a0201140a150e07030212090f10180f02030304080d05031906060c0209060a0b0c010b130c0c1203090b070801081504020f0424030b0415140c 70
    0x201c1c24860a002e520303d8501c00400c5d006503098040d00850300c4080d8044a00c00f00c3d5444507801c80c2920707140d40c0c403076a01041420707081c08a070103452003090748001075090140c1352150300d028048145108032280c10440c2c00401003075220320300a10903400d890749114010710500e2510180d082d0b8002150350020900c922803201c00046440500c1901d00500a403400c0c5d86c1303107038880340e00078103150310444000340c034448202c40e50644201c6038450802901c50036034a1400680f055824000c02c040c0c094011944105000c2000444ca20000000e0041ea4850000420300c42403190501c454411941191980d1a05000c0c800700f107560300242e00e640040e001090040c00c1050000198001c00d03481002501410360181041001da4014105034122605038040701c1001e41d4000b2110901d85d0b0945000707600041101c8080040e01c1c2a400c180c520f00c08030500e02d04000010b411003852045541d00803034000385000c041105208a140913000d02a2002d002404110743d149400d0200b10401407100e8580003011414 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 516077194 1250 516075944 516075947
    0x506031216031205040f030206070c0c0303030c031515090b03010e04240e06010501080a02070b010b090301020c0f2103010317131e03050609010b03190206091c050c0a0303051207 78
    0xf104403900312160100440e003072a0520040486803c0404c0c0c0240c482ca80100b4040c07440380741c4031143d10f0342185c190f0344d00c54250380e01140986440c000081c201034445590b040000c940001e02801081008402c0e4030741008100b02901101d0a94401140848107000412064210141d0781d9440340c0e0041c3c00303000941619000c03004c03101da40341030510410314044c2001682400091454141c40d800d032600a90b654a03407401c201a8030503000020300f00034900c030040128a000740090070350140b00400141c00c2007030281045180100d0456202e1f00c551141a440c400e0790030b000018481e40040340f91040c51036040d61102c1481c84060482c034040341000003031040300604e40c0010b8001415006a1a001307041500ca1081c062022030f002c19511070084d5404903408a205200314640c0c4900a030203002c144070008003085403d010f0003811303030700240108141c0c030030f5948000c0804e242d0b00c1da40700320b07801c0c40c002820203034a00021907440500903036050300300380003180d040030680d50094410104495540c0d5007410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 516078444 1250 516077194 516077207
    0xc0d0309030807080c0c1017091f050a05010b12040f0f06060b071b051806210d1206030c090207050a02030d1d040b09040f080405031609050603121603 66
    0x58900240030031540704100c414130040c81d134549540d0848403030221980c00c100e03e10406400541c0400c5801c003818840c41c3c407040c1c86590080043c001d031007a101031000340140f5441e41c42c003001c484c55036850400c21041c48900c6814054240100c0250a142e000c4801c1e404056005d48040d0984a40141d454104034841c0103e0071229400603090041c60703514101c141058101c0b89044400c004800c8070328a6802c0407044110071660028454001d220030488451444d1380c02501682c5c00100c54a144003107509124544568481004018016039060610040000203900c0000001e982090703010008680b0f0b140e440b40a0350010800160398510625080349840302d03c0b20001d40500866010b411034540100c400c02c10041a075460010411000c01044101c45243e0200b0398012406004600400c032952801c01c0180d22600d5034502c0d043d119400a0b00d000b075648070a0703680b001c40600610a0b4400f0b4014160010f10030b90040c0705a00c40c12035000854010a81c000d102640b1142c00d40081c1846100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 516079694 1250 516078444 516078449
    0xe070803030c03151f120b0907030e1002032724090a2a050a0b070830100e060f0f011b06091b03030804151e05040501060b0703020c0d0309 61
    0x38484103a010102c0f00507010310109540b0280403800d440d03016808060310b8010401d610350014108c0039280e448400640050107051540c0d8203074401c0028907100d00c0d8549c8002d40c09041400c5201104022040300c9010000c5144002c183c590440315442b0308800b070b00b0420100c00c11056101c2103259403074120701440c020141501500f24402c401c110400001d400210f28420003524070203805503038440c014044940082c2c03150807500c003020031800e004501014050b0030310a8001a1103103184000c025000c44d90342082502c006946111420311246281c1c9a034000300815080030742c1452440d103080007540f5400041302c007a004d0052841038007a030341c2c4500c1003055280d85540b004100a440c6092010081142450440d0210b001c040c0449000c814910703c00101c6c0e603d5036440c1400d035644c0d0354007a20026184600d26403241c95207411902c855500c40201484100d04000042030702d041c0c20404d0a403620f40c0c0c030800300f80c0343c2001034001081c2c0c00320740d0324a00315003550b4161050500d403404442c513550f542e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 516080944 1250 516079694 516079699
    0xf120c050c06040b09070803070f0f080c060c09010201052410022107020a0b090a121a042906010e01140c0f0f160e01121a15040e070803030c0315 64
    0x8100000c00000d041a1402040171800b12200291501f500a50b2481390500203031911116020440000b4480c030540001c0c1803159100500300f00c044d00b0714a1515000f6121407210000101e002101540e091003426480101c00d0108003045103000352003240d03d070004a010b8001c0d004213035280b0380e0707900030441c45418074000c10307400e0751802040c1c8034040d0603044030908903c51180c1800005803880c01a0907605218001820000d00c01e03e0030220b41080303031441000f1148105c48450f003919110602c011544624044c0c01e0004030324031492486841c0b400401c40e0070440808400a01606903401542c03485510030030b0904450001c50f038920f80410303004900300d0341c11500c80c03050b98640f180f1021a042c0107038030340401110180180304e0400c1c00d0342c01d5180181c0f5500c02e8600c00400095400c1511182c00c50701820364a400d585064005811400b0304a032480e00183c142468940c9130b0500d40b08038080c42966078003616000f03042120700307500e0f4480680cc00c04d075041e01101043c5441402c821489a50400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 516082194 1250 516080944 516080953
    0x6180601030b12070315090327030b07090e0f070e0402070305070507031101170105010c0f081c021b03091e01020f030c060415020304022d04050903040e01060f120c050c 74
    0xf42590a595812280400c68118540306c01c8403482c00700d2030040529a0381d054845603000b800d90000c4040d01410710701925040d03421204000701040d040034a95001d5038203a030b40e004400e820910420503840d8041e2140d49044e0160040040483d0f00c0300141007982800c860141c0c4c0c40460781802c46841c007840d14007911078021824000204070b908119500c0030102a2206c9854901c20300c80a150907009100d154041110100240005541d40301192f01c1284242c2c0c1e4142044600c0c81d00341443c0e8500c004030300c80c21764002840ca100c1c3d40c00300d00358070000c1c99101c011440e001e0340c40045072001d2803842440d0f0700102c034003c036220f483c0e0007806414101c002000c12680c4421059102580d1990140c0e002d036140c2950141e14244111603000b228440c5801429540703c0c1c04d0301d058450b501e1041640c9942c003545105465501d60743d42ca01441c0d001d222550011500d0301d0800d4450039204506034461014403200200e0070030303200d411581e00c3d4000d9250703010001e010410b00d60103442c0741c8602c0b0149000d034002e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 516083444 1250 516082194 516082219
    0x525030614180609061302130c0207030c05150403140123060f012d030605040216020f0103060303080a0b010207031515080303060d08090a080a1202010c0806180601030b 74
    0x50800ca5148540e8101d4094412202c60204940e114030b01622503c00a0b0007a20024060703445035955040d54130700c0070389440751a10705101c50400305e13541824180e0068203c0c020800a0013400002c800c007416044440e442200040f8003150400e1089110040035403100300e010805016082d4005503c1c0c00070541080c2d00708080c6002c00303001440c01c0380c45030710070720035810522015423181b103041e08445a2035400304100603400d01564950243c80e1140c104150300c0b0b43d4040380948a50002d001c00030204201d00141d03918920402103500351540045040519120301007001c26400b00080d6044400040001600c445000040741426040e40003d40813543d025404444884a903011480d140008115168200e880341411600c0b032005803503103540010340d06501c1c00825112401411003140c01480380070720b15562a0b90340e0400710481400c3c3c1d0b0340c0002c107103070008060302030048e84290701075464a41a00c0c0341480011b10080140d40c0015050404000000d00e01c1e402640b0035551b44200a0010031440c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 516084694 1250 516083444 516083471
    0x10504050d081b0301170c1e150307050f0703030e031206090907060f05090a1502010207170901022802040608030a1b0b1b040f0618060c05250306 64
    0x44800400c80050558000a2454036040f444031480f154516a264610f074030b081c2c5a2650413000340d00d080d210f07000b00b40c1000421380d107622410b090390701d0100c2000100d9062804010100b80c15138008040c419040040007642d80d032000c00c407400c89034400c011503141c20043c03d04400078100290303110316901c8001a1840802184108a44141070484c3c008020350348000303003140c50701e07003a11905000c10b00034425900c645009001600100f10054200c0340c600d82e68601c5020904286c401180150354002928824031040d01c12034031007141e03040c05162034081d200b40000e69410040d04001190380314201c2c07100b2000c5800c01c601062a40083c03003440f9081d12145201c1c1c80340d0002c0f400f01c02103400c818075000d00741c0d04407540c880f1098020410303440aa40b9400c444074041c0420210401d0854100000315002e40d42c06c07a510040c214a65407400112052054480c4100c0540c02101c03d000380040b5180005400040e0072000e500180e5005d5104443c9460500103000c0c42e800003801c060401f2045000a0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 516085944 1250 516084694 516084703
    0xc0507080d0e2d040f0207060207080306120a0c06050f04050904110a062a03021915050c040506032a220902070203030a0c02210d141c0e070801050405 66
    0x7681210f00040c84410800d0111007600504504801c00c1d01c052966810380c41c1581c801c0e1404600c5c1c0d1303400740c41d0040c540d880070101d910020003100d148901106000d0381d410040340f4051240107640007040141c0107130f05c80380e03031401c00c904c515001c000740000c034250799950203000e450050101400230382c06801c19181940724400401d83e41801010314880c002081c600c10081c010034581c6440381004400281660a22421440141a8250b1040a001d805559424486844040d00401c1c8500003014500b244000391240503221040105040c8014002952040c0446c0d4110700c0e1241841800c0b50041c0c03041d500141107038241061414003060710002c070200c40243c8100c0207012840301d00c2c55a06c83e0380481c22801074980180d0198418402141c100340602044070f0100e000030312903c9038105241314811034000300202004107800020400c07041c140c120300130361100c1e1075103103519080001e030928640039100c0e0141900d884644030880c0c10700340201840018007a1142c00d00a020515041c10500c1d9103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 516087194 1250 516085944 516085967
    0x30705010c141812070609031209060f050d060b03011206051f0e09010f0203040804080f150718032a0f0501020d080402040e0f100f020403120c0507080d 67
    0x15401d12078401101d42c41651481507a00c06000400d003040d44000403e00451064040e81d07400c0400f004411202c543c0402800b00140059500e04503014154035006580311110b207284014005520018003985030020440910400d0320315155454041c0000303848081c01c602c2d400070189020000021400780c0d1000d100059880c0a40f00038005919400b00056110300c00f00802002c0050000060201100070280e960b00f001003000046100502200020200d03401614201c80810001400304080384051000000c11189940076001080034a0440a247c4e9002001c41c810084c54101c00949200c104400c18080c1d0b0700114031107603032010504180a2030b0303180c1004100700e10851800080d6503403120b00180681e807041c0e004e4000b007510a034013560340901c041c0040f64440d4a408089198142c02c105800c0c0c5405080020014680b4441c840811240d4000010504170b0041006001003400c00c900c000703411080b0305d0011501e0300941081030401e441908002040c0c01000b0750444ea15a008528000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 516088444 1250 516087194 516087203
    0x40506040b090c1b120304030503040503120a02040f0503060709090e0703080327030313030e010e030a06140a0b0d02060703020102190f0206010e2401020f01020a170603060f130c05120307 82
    0x1c0711351072a41159a00e60710040172005910405c00240064400c1011b941c0062180c8226070030210410010126114110388655400d98081010048415510784002c0202801e07400b5049600b01007000070841c41d224042c15034084e8940c155000701800800c03001d4011900110f02c0e84c0c907420b0060180c11421610034460000901c405000d0a0216005c412607000321000c0e418007188440355075040d00e000c1282040e0301c0c144011844803c03001d84045c4500120113100d07020001e10041c0403031041c000c0c5607026203154199858540d000c60f00c1d0f180c07403a01143d031540407200581c13564400d103000c03400b912401c0d0324520320070740800140075040e41001a04080101e00d4099508580c1c9407192403840310741c01c40b01490013410030a201482c2c80804182900d0669061064a080c20190b04031070382a6404410001c0000d00d00030903004144890000c001c0e080707513085001d8a128204910030b886a02405803014907404c00d03c440080c100f0591207803100040c00094608180058008449a201c1d00118015034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 516089694 1250 516088444 516088477
    0x618160e06040c081e091c0305040605010b0a05180a050a080d090b0a3204080c090610170c070203060c12100303090b0f0c011418010e0606040506040b090c 68
    0x83c4958000c1e054075120704607010740190601c0008410140344000a044522035000340c081c402483c62656072240c40e10200c41d00d000c201400e05113801400c039001680010100ba40900641607400ea02074229800c00024502c0b12a61141d001d00003100c2c100d5542c0080e0b408130020b40b0006210002045805c0090110348031000459903400d03000903544500c9000000040301c0c1ba8a07240315100d800c20715030150f44940a04041c10181c407400e509180d103e83c000900960080280150625094000304e922680603120240700919082000c2e014041024940c9007291814001031041d140705019180c0340c5400500f11825410100b00c0203403e580706599004041e0400000640f0481306001458100ca46c150b0703400d200c1e02d1500c9010400d940100d5612280540204109107028209010b0050801191001e210107070900f10684081c401406107011070690600300300c4a620324010440a03404941a540420070740d83d800c001070700030010b0b0302c0740691008000d42445402181344018001c070318420359514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 516090944 1250 516089694 516089711
    0xc0a08010924020c0a062007050d08060303160602030411010509150c16080c27010e0711100507230f09010221030901060e010501020618160e0604 64
    0xe003a5203245001419090080d0312407142d0341c424007580c40300e10844400c0142001402c143c81400c00d11401c0069030900e444907144803107031410303a0b008442d440e02c00c039140740740540c2a91425143c6d03481c9104541071100c0900095241e0b2000e0040341c50003000c005544000f00300a00d0008000e42041d2001d0300c030406246890074040d40a02c0c103c5000c42401050300d002803031442c0301040c466010600340c141a0290720482260002050020303009804840007a0140e0107005043c802510304000941e22888803860340500f5540b40d08002d5410340d002d010610145a13145a1300b81c86480b0580a500700f1031141c0074961a4000f03141e8003050152005603100c1c0030f91414600c541c8504607240c03d58a1100d0010060704001c141480000c018042d41801610b60b9040000a0701801286500d50440801000030030010000800e20558018244010304015a541400c4c0002e60f14040100036002603035040c00000284c400c10099080c245414070004103401d03403150b040c080600c0301683c01c14029401e01440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 516092194 1250 516090944 516090959
    0x10c0804290301080a060b0a09021803060903130311010e13021909060f031a0d0f0303050f1003020d030212040b04080f0a0809090a020d06060305070e09010e07050d021b0c0a 76
    0x202c90484070300d100202500282520307604020308001d90700035400400d042000a40e0401400a085401c43c190400d0640e4040302003854142140246694070b1504100001c13175001c0042030307001058941258004c07000c1040c040040e02d0346504824210341c000d207042423440c1c03203151640081500420020703821070f03121500c00c419a041401809504003040c441d00c0c0b11401daa05c2540038541004500314894072001001b00410100c9030049030076a414000d55548206164043c001d0603000000140d039401c1c1032030000307004484131010313000091150900d81304450902d44201320403102d204061b030701203980d01d5503160751440e140d01c24816000d50b40540c1d4604000358501041640e800390304043c0207880d1400410402441c0c0c000100314990581d42403020004070101441800040c01140d20300250b40d040c624000f5281001c5525218421401e100c01403082c0038041800c0e603084819820203544682c040c45181010f40070f410b0391394038001240c441c140e25800c2c00040d0311504420594031042c035903848000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 516093444 1250 516092194 516092197
    0x61d0103051b03070923180d2f0f0c010503090c040c210b0406080a030210110c01090f0309080304081f0f090f0209161409010c080429 59
    0x38086400c00d840b100700103501480d807007640140080c142c03980903480300c80340310881e20382d210745218000044105520403440705031240d80002c1008618641c81d0302e603c01d003541da500b074115030504000c4580784101c040b4188602100300130104e802c18101d140314045266a0b15085c0b4000c502c210b100350951b100e0380d9401202268002c000020181820080040030310001d000000c2d0410104900101000350680b03002501c4401207422103c0416003250110400040e039040d90840c0c60340343c101c4210b1500207900001c032840d07451440764000c2540c1325003250500c1d445c021841e6030f0301e0079400c250381d00d0704000b000082d45003030754401d0311844c8546489031615a076a00550058907103550112030110107001200d407a100d118940480041100550806010140c5040803012070305e621194800e4011450f0859240c3e90040b92020451101d550740c8400801c0302008940c2080d003414000381c02e07001d60340b00700d1101030526000b1480c0c07907545668140702e00003049070303400e0140024200e19940c1c4204060a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 516094694 1250 516093444 516093449
    0x120f051c020a0b070203070c030803100b04270e03040311100216031b031203020910051905030c040b0c0610080a0305040521010606090602150708010b030a02090310061d01 75
    0x3401800c0c04505550b074410a10005404c00c3c05510041c042e800c0012110400400a107224184550302c3e42405030180180300305070741150b000d001c0240000c0c0120380000c03000c00085040305a8100b0680b250a08000c0184103420404c041c0d030000140100c20300c0f8502d646001300d24416141006400c10022040b61107a01008403d500a505201c0030004156401540c0c1d40f00484003070040c100540e41c0c2d940101400c3c0c03908030140480d0300032900180320b04d803c400700c00000d41d032402c2062811540c80c1c00c590445484c94482c9081c04004004a030348660120140c0b0058000c41c1d00003507a030100304282c5ca41d00c01c4200c40c0552290b04400020841040105500c060140c1c992a050304150410f800c10036211000c03100d2810003505d410025803444824001c10000704115150b0800490038070030008e04203490850f0403000c80b8840740c1402000b80d44040464111001180101d0322610781d072004501074031986805070b034113100d014807802200d0b00c0ba03031014084603103403448040c150b80010041c0400d0182403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 516095944 1250 516094694 516094697
    0x9090b01120303110a031a0d08040911123912070507020915030706080f1305030f0301030c170a030c0201050a030603050313090b1c060b0109120f051c 66
    0x84010400360788540700c141d141510a08000c04e9604050020a465411404131000081c1d2141040a201245400564a03201c3c09480e00d1410a4403600ea408080c411485403544203595180401c2c41c1c0e101a0056581100e020300c030402c1c15050542c160400740144a548401413038629446034001e5190b111450398055500c0107140c00e05c1d000030140c5038a04401042c0c201440f008009440041c0e81d440030161090142c1d8210f5032100369008140b5107840b1140d007080741403241c4074060051034060301d01460713440038007544c1800b1080e100d0f1815900318021414a00c10001e004400403041141c111000b109071210300c0c0c010718182c0000e080460392010182009804180c087e00c01c1c9025500ca81c2c02010122307401d0401291090b500ea442a20755400381003400100840d40005000280d01c0c2c0c000c280f0102c204403001c80400c400388910b00c0000c0010040108101d40d81d003c117111a03409404028024042c0d00c012012100751030514000005d80f00c40111828001c02c1782c43c0c40a040030103880340041c2500d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 516097194 1250 516095944 516095963
    0x1005121902010e011101021c0b1206040b0408040b040e06181608100f0b071112060112031b030c0501060806010b040b0d0b03010903050a170106052b240909 68
    0x1190010b4811000c40403c4038104591443c1c07101a4a1090000b850742d80c501c2140f202560150840420403100a035000605c1000303200c03841d6003441c8002441d00c0c0c01c40d4008944090030344991030180c1c1c0510441c3c5c0b210342e1000303000c82c00007a20351214076a030340300c0e440590b551107852501e82c030001c0326020200c40c840590540140c60080041c03150b26010740c004000001c2000707143e12450003802c0680141c2c07052039002c80026910080208840ba0842e011030240c40c20b0070520b00c25404251505014054086000d40354042c00040c14440c1c500c144081801c19844d007400d88060a00400d03000680c0c1059a0541c2800400680a6800500c950407242c0c0b1007006410700c2d0a0045042d0300364064040c0414113510348054194540d000c0c824081407900c203072109a0749061080e4040c03c0c601003081030341050010000104122508402140c0c0125006c0c004c4600e400c2c80158100f000d880320010010401c0c2c40c004c903001e1401110544a401e000101c41c6c10f018603680c038080d00080e2801400300400c2c9081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 516098444 1250 516097194 516097243
    0x1a1c0b07090f12170304060f020c0106030c0803030108070e070210050f0916061202090307030501110301031a070206270a030809010f0912081b03100510050726070b100512 75
    0x1024003540d0828801c1e0070200300c0c8654006114213a0b00039152a02b5103940d210390820420017448110303002050401c0c051415580352407031254540302c0f107102e00c90254000030006501c181c428030230301e54840b080c2c080403c641d0401d500044030420b000c4520348440d115500040132078040da001603d04a4403565101c0c4110340041c45080701a41081007204d806209181010002410a02840c4010501c1050751601c941c5541065071418441c035330b44c4165900c41c5414062010360101d4106d82c042c02d01145204421004e840000d210007809002c1c03d03850241030206420182c2c0041c40c240070b0303280704000313000460b0000000350858016601c01801c8815920085a00a010f4007179954412107580103000b2400740c1e50103080c0c0660080b00c10310624401d82d04140164503140010070103001c0380d03184c0617083c4001a42e4850b4400c1642c04054000c03004008440c95030030300c050890b445164403003d08030041c2015205042d44020500601e442420300052241110500280d68900d11405a860204009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 516099694 1250 516098444 516098483
    0xd020c1b041814011d0105070e0105030103050303010506070f120201090c0f0e06040504030302120c07060f050c0304020d02041d0106050405071b0b1b0a020a11041a1c0b07090f12 78
    0xc3c0c0381010107400d552507902d403007205000c81e0551001001140008540c07480c00c003800071f010000700440281480802c0c00180003195002007543d05517841a10004d0361603c1c03a0826590300103040e5002001104d521b00340e85003046c1d0641040e19481c0c403804506000f141c40e003040f10010720319030094a071403141e04c5002401074170b03180d0819a00306000707080051030104103000d031000c180800c6031029108100000c1c80310400c03c031846031190612200c2010800c500300340052004900c405231000e4403c44103002400c1c1503659a40c449043c0003d51104901800c0d4020304e014003a201d02d03c5060710480c40c25000400e928045c42c242d580c00700402c0340e81580b904256440c5140c12030701030000f100e10601a130a104400c0303082401400d040e8440d030010030300b1400c81d190540c00302c2c2081e060180618203002400800200d10000710b14180004c40c5c3c00712544c01c1601003003070455407809001d0f0a950100f001d001003990400a10b81c11b0b20004404205419250b940c403d806513103089005046010300100401c903034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 516100944 1250 516099694 516099713
    0x7020405180604030203031006020114010308130905100f1a0a0c05010b0a09020c010e0d0e011b060f090203100209011d0d021207061206030b0f07050d020c1b0418 71
    0x28800e41c01c40c10503810407200c00d454484119801c0f4096440002032141c9400400c28245c02801144020300000c1481d00102c2e80313680041c0300c0280b0010002c03421503481c1c1e02d09417080000d012504400c0001e454046c003081040c4070b09104411000e500e036a00442c480307418812990b540d07402e6001d29441d05202850848843c40740300b02c00d5810b5540d0f4030900c042540c82603408401400010400340e281c00012003202d00319401a14103802a9004c580e401e082c0b15045150a010b20000f401d03d6020201c1c10000035030404031114004140c1840c05000d20313015100c6070b000006c018000d4085407200c840c00001001203219200c04a404600c41000c4209601011502205500e001410700c280c1e4090304d0340410b90b0021200c0440c456070b046032209120043e40400c0d14650043d0042041c0071041c51600ca9117210b00c00500311004054910001170304c864065001c5401d10000d081003103550f400c045030f119890345021701059180704851600c0c400075280078002d101031103c413140e00300c07501803440e40c614000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 516102194 1250 516100944 516100951
    0x605011205060a140307080a0b07082401050307180f0e061c1e120207061404030215160804030f231c1209050f251e0504050112170a0507020405 63
    0x50f1241846c042803550050001c80d00e80b07449180403403034506000e9406408100010082c90301c10004114840003280e6000d40c50000751400c3c00c00c0e550302c2c0c0340e80c2000c50740c0240d039000700300c0000c141210000b122000d001040048070101140701d5815200c034420404800e41040101c0d6801c240c60701138802003041c42240c40700441c101d0480b0300c0c00c144260366080001000349078490242c0c0109000b04500c98019102e03154603c5040072551419003076500048c0200721002c0d03410000031020602528401c503040f500d810f25030b00020322945599807441c04c000b24031000c0d070b0b084900b007504102c0390001040c1621241444005080540380c07000000c03122051000340300c030f0000c04004a4015076036452a05100d4500654007400140a0903481d018109150001503526184254158040491960100e00c100c4069404c040c40d0b4050008550103800048150364002d158814904000080c0700900480600540e074400c4410660410710307001017a20901034051248007040d410801c0400600d01548015031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 516103444 1250 516102194 516102199
    0x80d030c0c0b0c07050c0a050310051003080c0618120f0705070f0b041a0702061b100515040506030c09061003060806090109050f030c07030b0c1209010605011205060a14 74
    0x1010301ca0301c0341c0d14070020903510601c44480c00101101804010b204044410100f551042c004a2604020030fa940c5061280e6a04156a032008501508100000b00b0004c54012405c00e48417000104003a807100e0003969004c0e10280041f06c40c034524000803641c1e00c10034001584190520041d0045044c1b00d9001c104215094091088045000d030900c900000c00b0b0048801140e0700e650909669600c121500108080e85c00d405010340d00050745e403c000c03298040d9000040301c411030740001c02185415501d081c1801000e080604000e0f0b044261205c0701c1508500312418042e40d11a0381c145a02d80903159140d03500300b08907000281c59400e180c0074086101031a840c00140560f90b03072642d5800c0010990b01044142d4403192000e0611004215889002c1c030110007943c40c100d50310315480d0f40c4c5d000c06d1000600003241c8000050325500b00c14160b8020708542140034289240c103c4026000303051500415000c06c00e800f005454905051142521421014000c0c654071400c00e01a40d1841240e072808a5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 516104694 1250 516103444 516103457
    0x1503030a0305150d050106050102010b0604050f041817030609060d0f0809010207030602120f070503010e220f1407090c080f060409020604030501090c0909030e13150b03011707080d030c 81
    0x1603640b54144c0320412940148000a60b06042c42d000a094400c0341d82000c3c4a004c090005001c1607540294101c4000d4048500207000710016240203c40244c07003402a1040c45030402c04070072106203074015445218200d95141c0d065840700c0400c600303c1c65010000d0310360703a041c6640303000140305c6900a00c49040d0500403605855640d07070f1400c4c1680d002c0a442c1907802215020f0240c40b4801211090b048540c1c0e04120741190305041c000444000c0040c02400900e01d1001c0d0101e6080141150b80215a04844105015010390402e0303041e404152000200c10321903d90f0000b04000584a0a58403071035030303641c00030320783c440b03103034001c68410058501640155a003206500594070a0002c0006601c0307500041030a2029080141e107681d02035012403280c43c10070001da80000ea002e44031650a400c11940d00c0b00440c0251241d1000b4601c0307084888140b030301d00c400840d85014010145040310b5080141055541c3c66200d00f03a1604468071514000c0e901101f070201c1e030540282c104101021043c5003a1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 516105944 1250 516104694 516104731
    0x150e0a0c09120c0e0702060c0f030a090c031a06040e0a021908061806060609011e11120706050907031112210307030f090c0504090807020406090b01081503030a0305 72
    0x19000c0301e02c0e40c841100c00040443c3d00b00300307501400ba8815070024880c00581000c0c03504c01c004604030f00c226441d00a07070940010001d81528181d85c040000540c02000b4600003945031314010b140401c03021034041c0c050b0141e1000407028540b90090803503155040002d822604229800d005402001c00200c000c502081400420704c1c030010040d0b1881040700a060411305c4000745192030420350040c0140f4015141003120121a17600000d045642001d6030304078009680300784c4400c60b20366101c143c0b400010300849052040b0032003105d0240c414503018034001c010a40301c40140c199249010320000b01203480101d0425800d2515290a543d4044042e050368001c0394180c46c49040128040c00c94030f08a10080148094941d0622900186e62081c481c104012009510b6000180d04944a460310640c2c4403e40c050410081c4010361711300c55400350040c4181600c44080358007411280a025000925083c00515180c0c400d850074001198085c0165190103003c00b022000b03030900810901902a215421 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 516107194 1250 516105944 516105959
    0x10b0a1e23190e190b040e0c090a171e1b030a0501020c0607080a050f0c1e040905041b0608040210050c061612021e090a030b0415150e0a0c09 62
    0x660502c1142e5550845003580e040d041000c200000768507005007510300c41052000f40c11100848003950700e103401d0960665214400401c8a1040c101180d0b0442000680019890012000e00c000148080c3c1600c000c11503c40000d42e000c401c80c443d01403182d0120b000c0c01c41b59003104d40da1242c20760300a41540d11004c5192a00c030f0076a4040110a086079109000300614507610201e4103400c09084102131107542080400c800c03030110b01602100002130006590581030241803040c003081c0c00c1c0d51500644581e40c8004000051004403010f40b00d480d1086400109640f29003800000d0b50305030303111120340751555000d1150200414040e04103002c0200041c0384100010000544141e4440408400da40d28a800042211a003a801200e00307600600111442240600030840c4039a1000c010035166801c45001423920f0040c0d61001d401445000c0600c020f014600d0b4800a040c0e04020041c8040d1007246890101c0503000c0c410350516048090120b0341041003900105054441442c2030412a604d5001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 516108444 1250 516107194 516107227
    0x30c05190e12060402010806010e01390b06120a0b04030302030a09080304052505010906110a0b10091404020901060809070b0a020c01120506310203010b0a1e23 70
    0x803042e0a070f804101084115a400542e10b58000c5082c604000c2c0d2003410b40001e03100d00001402080b8020380b00107540b203640e0005c00e602d2140c4440c000c41c022185900c1c200506124400d0310098004c2c1200c01d94101c400e080000c0301645558403c6140c01d0554071038404600a410140c040e0000c1a1a500707140c3c082903032040030b14015030080e800352000d42c0a101c03088a4210000c1c0d41c01c1070134000c110040001c0d83e0050b40e540b04135007030b504044002e144240b500318102600a00300900c1910700c3c02c240b1a10034407100c0124141d4044c9442000b800f0350000d02c2c60584d41003160300941c400b14107401448a9445092882e40000b4003104a505650301d03004040e11640010a8400050f4800050764681d5079128600000c0030003000d10411140c00c000000c80c0160050f810300c8c0306c0040064080b01100040c0000d0f01d245c00413030080854072961545801c4080758048403005c00016003030b02c0091604000030508118000c620707255100c4a03079240616114803030420910480e05030042c0003c1e450302104c200c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 516109694 1250 516108444 516108469
    0xb0f06252102100e060117010207020603043503011419231c02040c0504081b011e0e01140c060a02030a0608121812030d09060606030c05190e 62
    0x103191100d0300741500009180c000b2084070340b41000e08100c03c54000010101c0c155040d42c4056a035550954070030441c0c82c4c0a445080c2009401c00000402c001c10321080c8101009481c3c9004001001d840c600d140c80d043c1000c54501d002c480b03910030001086551014003c0100000020f0211403103810817295010741e10100e0360141c0d90401c0c400700940303480c0102000b648001e08040320110b401c0100090308044204c0c071500001d00807680c8110a000740360054007907030002e01906084640c1c040b5120361450480210803009030106880c030140c1c2d4081103601900034070200c2c181e65051800d42d0860011a20310559040c1421202c2c0c040000060707a04080c8522807060340301c0071001d603071703410402400411034225a206a200e9040070f0078449039002c0d444100c031441e58a20122141e503001000c00a41a2540020301041900c800600302184a505d81c01c0f85421134021042042480c2e0b44881c00d5080d07400440f41900059010498003480c010250000074646105261449a0321565030210340e44407101c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 516110944 1250 516109694 516109733
    0x10e040e0c03120a0c0206092806030b01030218010f030f110705070e1e06030712060510050901080d03201b0705010504030305090f01020a0b10090b0f0625 68
    0x201e0100304a0604101d0034403a4070014040d00d26202c484400141110402c8500070310514000810103408c2c3d4508a0000344000d00d41002140003281821040e4900e9480c810903001c00c0c2050fa5000301d030b40c000d100799218100b0007004030003681c4101c0011142000c1340c001c01c07018103649080180842c4020f01c00d01100e83e05010010750b82e8800d070f042070380c680181e41c0c2c000024001504100034440c08242d101b51450002d100d40c601d403640b035800c000390030900307160068048406032040110610445800c128007a032040c0038610310a03601c0c0c01c00e11103541c1090041f44c5843e4002e0041180c0c05200340c1c0010b103007009150703154580300b4a81001490543c000d101411407500111b5800006070001d1160000429003400e115140c1403079543e02a1143c00388036070042c0b05440703180a0b040700741d000780300a80c0c440390b011178a980c0c01e1900095080c5503000a011304c1c03c08071300d0015508018207080580300001400180400c0c00d03c030400350148000000b940d4035400c2140926504000100a074000900e1050342c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 516112194 1250 516110944 516110953
    0x42402041d0108010c0e12100c1d03010507020c0f0d0f030c03090609060206181603080301080708060c120402031c080f071b0201050a0c02120d02010e120a0e010e040e 73
    0xa00200c1d031244010f03004203050741d24061960102da50008007000c1520740507502c000f13100000008841c00c0015140d440e4543e541840c221800c8240e000c0c42a11180c00700103503030000c092204040c11b080350401c23114540940e0000ea80c8641e546490b6040c4904940000d25040f0800701e20346d0340070008131820381e00310041741080c880c00007010341150051340030300054507080700030f5483c18000a699080181494500b0210541c1038409030750248441c60740c0204500a400c8002d070b8910704200554001d02c0b81945074026050b01044281003c00c120b40a015045000360800407200c4820034050000380089903d0b101c1c0c111007405411003414025820212074589459600d0403a451034551007008020344100400c6040705441c101e6800301c490b880b42d80a10b485501d0756140381e02034402c1c2e0100070010390301c0b80030f805640307502c041c0000c2c000400d060709078028007400403016681036031078650000b02c0d000190103008079941c09101d20320f40010101d05141c041030307460b00c89012604580380210308020a421 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 516113444 1250 516112194 516112229
    0x181b040209031c17100e13060e070302030111040b0301030821090a05011821030f09080903010c0507080724021b1605030d080624071505010b0304240204 67
    0x404c02c5911030050280c0040c14018038021400c801e07401001d0141039540f44124001c908038403d2444000344c0b640d03218000304003c0c58130325140d640e140540d1004034440c0d07007048a00700c159007243d030540341160b116109683c1941d00303503901c6000340d412100d031003040880211100705120880304081c42c0244024001b0309454111402c041d030a55040191905202900c20621400500503490000100164422040050001c100120007074a0780b0051107444c81d0a1888200c14014210000c1103c180c00300c6c020401095001c00c01c1e1864056403101503c100003c2c402200440d81d4452081c00f1030500010300c500c52012812101c080780c10600342c83c4c1d07181183c0151a83c0c0420100000c00080301001407199030380b458580002e40d10b0350503201b500100b003542400b02e10f158031008642e440c40044111038909031034600030070001c5504903201c00c3e2031004101c10800d02c1c2404611600741641c1e0358074141851551151209145004c403043c030320550b55001300400001c40c00034400785c00504a510201d215588 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 516114694 1250 516113444 516113447
    0x906090b191404110406080106080f01051b0405060a0c0f03090503011d0303070c030207030206160308010b0403050c0d02031509060a0e01151203140a0215181b040209031c 75
    0x4450314000c041540740014100c0c8003001d41036a194091391204400300d140011502040142490b0b50102c88a5030034090701003542d01c8042624241810004020006980c54013006060b0b1522031b80080e19404c420001401241403000c0100000c0c1c0e240d0925810400b0240da03111411851060103500203100c6020a014070300d02030180003070f64222003003500303901e0600f403c0b0640c40748405404078007844080780c901d40c00c060092014100441d0005c1949449902c200f40c0b402d0800300c2403074201e0004101000121740709803094190303402e8035013044c01410480512024052031080702c08090f83c0c54032445254216540480c0d0059102c0d6036800c01500e114200030100708207070b401140100d811a414000820001d02c10034040004584502e90851488442400c0665170002640d80c41908254001161011b151300040c101e42d03188040302c0c40c03200990b10800b2400355414071904104c3c071070b001002c10351244594032810684d4000010801403400300031000103890000380001040030320401d01314005405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 516115944 1250 516114694 516114721
    0x9060d080f220e070e01110c040905160501090308040509070905090403020c0f030106050609090c09090c030f0610080708070311040602070527280603060509073203010906090b 77
    0xf00ba40b00918000d50038000e8016014030143c242c41d50410210810410384941d080099030304034039000e00104800030305030500c00d4880303010300c00c000b00c000700080d80000c403548143e5001d000c81e41c0064505041a00342401c0002140024107003004010f6806008202952024255030045109030010075100641c8401d210780c0c86c0e68221410300c2070349414420802a100d4030704440d0300750002c0f200b2142c0c42d07407248224001c502610a8003500000d07590100440c003000d01c030085016110340c000b03120a5503224410003100980e1040305400044424001c140c056004100d1140c200710700f810007150b040d40714081200d0743e4100d030f03200b040142e0128000f08550300f0f01034583e2054800b000c040343e159000e160b9402c4041d40001d0310b12041d0302c4005030042c040d10350240034000408440c0c801400030640d00d040100c0500310a03a520026400b804400003810103142100c0c041e8501d0681c01001c1c8600c0a0340c003001580e9a8040031a019500c0360781c0d80b00010385612078004180c1c071500604543d030400d918204c000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 516117194 1250 516115944 516115949
    0x10312020715180f060e010c0501020f210a053c0c0a030e01061d04031b241e1503150c0206011a04050907030216120f080609060d080f22 60
    0x40ba01001418817055621a1680c0039411083c20100c00000d440c0c40e2003802441480003140340c105000c109001c2c121032512442d0070301000c140c0741c4489070325458465011624181d84103441c1d50030030149004c1d9041295501448800d0321041000403203000d20110b40b42000880b12022104000500e501c51182c040c411064120180d030001c012541c240035200301000003070802c400100c5070000020741018481c5480c1411442c4130340948802c2c4800c0d190040700800010b4804c0110311400f2201824014039200300412200c1c0d59110141501d81100d21100901000011074031924107c10302101140b11440140034580c4135100008500034824002420310b4410b80161004500c2d00100c40e801c08005c500750f4043d20001c882400c4d40382c860400903002445022001385100341108811024444a0f00742c0c3c607080c15a9444400d5140b090803012203112108480d07155101b10860b000c119035007032200802c00d07020300c10200300d0703e056441c9841e1400c40d001410a56880071941500c03100c028103000c0007600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 516118444 1250 516117194 516117209
    0x305030907140612090f1c110613081e1b06070906020a120c050d182c040524060a05060c0d080604020d060306020d0506061201031202071518 62
    0x1030340594007000402c40d11070507039144c541140d1100071030300e20b40741840b400018402c110300705c41050102c0900004000c1201002a0104802c0d039201c02400d040031840a104170032840b0b9845064140341d41744111a00300c45604141c030418114070140022085004011302c909502c00301024030442080031740f03070010040c1503c081101001c02000095000580d0307042941e0302c1807038200340303102800e81180c1d40000c01c00042c1c4184101000306010903040f440c4800c0341c00450b1409480703551140300c8002501804060b00001181c00d810504c41d4000c603004540d040381c494410340b02c5050b204800d024503809503008080c2010101c40c00d1003940d01d80380d1f00a00050800340c070b038141000c490940c015221000000d10f4030510603903030700040a9a840345d0403503691300d610b81ca0400c88161241410320080d003256401c400302c40c1c0b62034042803c1d8a801c009641c0d400610001040941c0e0071070f0307610004800c00401c1c0ca8150311a00d6008141c2c6200e0188400d503070745090342c5181250f6103580350081a1205a4801d15 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 516119694 1250 516118444 516118469
    0x91506120b071e121107030c03030f1e050c1e0408010606080c160203070e090304140303070503040612090f0609060c0c021513030b07080601200312060d020901030305030907 76
    0x140c114076022008507001450a00d405440c1134210908060071941c071078034a202000041c1042010740000d000c0c1c1d4410b0081da020010300c41001c00810456218204180e0220030080c4255082081e5401c5190700c2940820110304002c0c1c40d800d2200f0114a111451256510101e41230111034800d11440008000a26280e4600d0400d200c1e4101c4a100300e10700000421000803281c0300307544080143c10001c0000d420300740454038020b08000d0301c907080fa001e040e045c840e079032a0841542c5000400c1d1247c0c503811501840c50586400402c1c0c6102c048031003120801501d43c041c003c0407401c626014040b41e0300a401c08036100f1010710b0540c2c101c450300d00d00c42041c485c0700da20f8ad40151310365854034007069099070701d0699241001c0c00c1303c500300001c50f4401081940d0280c1000304d0554010150350040c4003c0c5c942929241541101c103001c100a441904e10651041c401c0001801d000503215801441c058882d02408845801150006d0000d030000d60204a002040c40342103101049804000d009052440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 516120944 1250 516119694 516119717
    0xc21060608090111040302210d02060a060803040b0a08190207060506090703020717090117131110120207030908030a0801030c1505030406050405011b0e0306010902030903090103091506120b07 84
    0x42451700135800042e000e02a03031606100d10300200c20841d05000c0522044803451448614001c6d690710003190440800c030f0400781c00083c0e5800000c140e40690340803104403410400010811250654020310030100032004901104c40c8150500c000c0105a0080c2d030042030303074682407081c8208050080d04040c1003500c10841d040c0491030a04c010620000692556952640898012603074046505031880344000d0344824800c8030b840403649003030154403501000d9144d60b4405d00b0004216003980703100c0c000c01c0b1885095801041a680204602d900c2400d00450194999403818999000350f0709450100350300d40010b04c1402400c4100e640142280a10039400920282d0010540e003c060001084180c94401043c1000350079000303560f103408050358015540141000c000c3c02d401905000900a00a0703000100305100140202c9214104900c0107506e4240908011001810040c0040d10804a803051500f030b80c01041c0582c100400c14003c030f048d0055030504021302c0246003c0e101205008401001c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 516122194 1250 516120944 516120971
    0x31806050904050604060504020d14011401050a0c03170f0601081515030a06090c050d0f021611010903060216140a050d0507080702030d2f100c210606080901 69
    0x12224440c07400e4401040a40381c110224002d0b000daa001282c3c010b0000c40d102e4001825640441c841303000d01d91041501d40d0b40c40c000150036101e014030540c0012001c100d0800001e000d405924a000c6c882d00d0419080d00d8550b8072038503003417419a460150107403590144070aa40e401043d064100342840f0b01d100c09044210009492090f946c0500b4030446d9010000406510b420303800100203004d00e020034401c036401200d0041131584000700c04600c00e468071340903401e201c00b81d00c2901d0b1400314500d8421a050001d441c1d91204c1d51011000c941000495100480090b8042c006400042882103440c1500000d52800301c014000e0480000380a41c000d00206000c03130310002c0c3c2109501514103146a40701f0540c108903001e03101d40040613403d4810315240d80da5071584141070036004c05000c0b0341a10300a644c402480d40b0594404007418003a408034551080800450b404100e416869040c80780c82500c6040400507610b00c3c2240642500c4d50343c010400c501a0412619a44101c0300002002049101400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 516123444 1250 516122194 516122197
    0xa0f1d071509081501080d08010e0a0207021306150207050409170319110322120513050a080607230403110a030807200102150f100312090303180605 65
    0x10718101c412009805100450162030101d0141c40054103407814801004140d24500c9000c1c41985407911aa490a01c00c0610584140d4141c0b42120400c040a4451095850107504007d0080c0d0b4401192414629410311911891008000300401e030882d020041c40040c0c24992075521072801141425406030020301e580d9001c031410103417403190716181e403101d986041f202440c680c0c0400c85189020b580b11403105e9124059403144202d0302c0000d02c40c0d9081c664a003240500040020034415851040c0c2078010700943c0a0101f0141d056051203603242e0310030014142107042d502c4102c640c0c01c80d1003030201442d0b011400035000260300d001b2a0000d40c0e01c1c1e81d80d04181c4980c0c4005403102c0408104900b00c1c0c0e564222142c01560050426038a8129604080c04d880c20305e0280b51041c400c0d4901840e8007540007040c0040b011000001e408115a240d00a011441d8401080707107036081860032020000030083e03841c4050307000365075440c00c00e000c1c12342c58043c245014017042040a0314282d241003090300c1c2e1010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 516124694 1250 516123444 516123449
    0x20102070f140c150405090109271115120901020a08040f0302150f1006031b140702100c0614010b040315110d0b01030501050d030816090506030a0f1d07 67
    0x2c031500d844a05002d0504100c0c1904100b940450b989880e0582c1c0d40e00000580181c82c800c0350a100c02d070b43da40c1450710898a8050105a685d01c002c403070f00d03402c036040e400c441b0201d40c05800c8195408003030000003440000740c84c4d00140d400078041198031005480c00400c40e40300010700021850319070541009050700400500007003541c5001c03020b990406100b80080f0842c100a241039038000e0034194031041d0b9854048030a01840c0018120014860f0300c00e019a0350310010b50a11102c0c40008e241003261a03c010f6110002c103501d0422640c0b005031180a09280044201d0b65480200d22503860a1025034074a1a40c2540c800c0c445001441b10242100440b011a60b102c840d80308090002e90005c2c01405103010848070b603080100c1d090b40e00c05190340001443c040c0903601005140c1c4c0300c00400070303111000040a00000c07031500024821b4a80742e120344e0898102c508021b000300ea6103e001410f59403003100c103451411348031054004125424064800c40940700e5040050700c18101d00415950320192 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 516125944 1250 516124694 516124703
    0x16081912020f042715060e0103090308011a040b0a08010f091a120f0d050415090f0605070309211e02010e4b010507030e0904111e040507020102070f 65
    0x42c240c040419a14180d04112454080c20a1100c2056205d001c03016060b41e1040750f0204901c2c20310070110b07610911807a03d41c0382d0f247d142c040480e4280303001030b4002091103215112042c02044041107007600480500707824081c1d50340320b003202d604010002c01503410540c40070030346c1420301d00d48144c0c82c0b4441c00400780d146010350351a1030303102c0241d0700d0515040b5648030120540c050f400074800c8956010b0001c0054610f40c03034041c50511003d55080320034007100d100d54581c03030040074400d11425204500405140b4040c2c82c1c80d2001a032a841101e029891302d0040c5003000012100c1c00042201a2408894400704078180031404c2e00c040c1c001803c0d850303015407450b11031076400250312420001150300c000c8000104c051900402c40d0840f914828041340307005030043c0a82c004c9403480350341c8120201d41220380d16641d22910780c01c0000500040040240c012940400f0214040c107998445170325549030100715000000c40070040c44c0500040364400360465045900402481c0301145018610401d0f55501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 516127194 1250 516125944 516125969
    0x120308061905130e0d0504030f0b0702010608030c1605100e120f0a110f040c140f09060a0c060501050a1d0c090306040b01140609100516081912020f04 66
    0xa014030300e00350110541003983d100145580743c00c2c2c3d031501039000c80c0b500c0013141e080b9008446160b90a648901072480028940c0b030000c100f0500150740302c1203040d00100540004981c558076001d045003075401810340b003180b42d80a0317001c00b07a054200c071002030010a0240c888040110000b00000d108119445032980210740c0008854148141044040752008680055902a82d134501d00070180d588405052031103020715071900d008a1030184510384003241c041d19844549101501c040d105500110f032071a514500c14041d80000c0d03140d4800604010150380d0321454810043d1405000300c59040e04000d003e0000c07140103200058016102100c05038280d4001540381d50341c000054a10b03c1003400c015010300a0314144400c001320740800905950081111a815440c0c80c8240200c6018501103150300c6103096018540d002c4c0258001d25074580340002112a802c49034a9140d8a40e1080d00c001c1070103107444111052207035200c029004d0580c0e100000b5440c08030810b104210398001e601a50050090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 516128444 1250 516127194 516127219
    0x4081f1103070c0f140c0103060b0a05070f1104141905010b03220813030b091b01084303090203030a050a051204050a110105090901060e0f030f0c0a12030806 69
    0x521945a10031550711000c0254803409072400c45e030301c5140d800e1265000c07c0c00c04401280e032001580c01e036603248603142c0d1100c0c06c06000c0d4644041c4100360a0054400d018000103195540e2254060310b0804001c0350314451035420b248203520180d4500c1800558085d14280060000502080c2180e401540450603000120040d0318124101100014024007604000548403c00b8101d92024011a4010400b0600075030f42c0380e0b00c0c2525a1100c26001c0d80c0100203154214a640c05094583d42002c260341500000c00f10301401803518101d00d031101010580003503046060509168101240d050035031805000c0f62105501003a92402a5207540041c0306c80400c4003050035100314180c8595a1855a40c1d07540ca0406060803a10742c2503120080c3c80e500084014019194002d000300c61028101828440303442e8039120b411103041150444066100c2041c60303140305144c0d010400d40d210703644a10041c201c41c5813506d0402030310790740f2070740802490402645060042500040e40340c1d48a40c003600c4d580301d10074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 516129694 1250 516128444 516128453
    0x108010b031b040e010f210602030c1207031e14010b0a050c030d060801051005091302040605100509090f090601030b0a06090609021329090f0604081f1103070c 70
    0x46610340180c1a9008200040c20f4201344244a0480d030b0301c2180050390135101c0c015000385280d10a00c2d40d4021080a164a000503070a50086510600300d1112034241189178106202c07911042c0c60ba500001d4584504400821009403219100309040700b08104020711205001c42d2003105104180f2200300100b000002c03580150700f11080d0408140c2507031399440d6480800b8000b4201402a8220b942ca02400a111000500d6001c01990f50060020505560305242c203214040301001c200c0c1c0060311640000707400e4507a0030070201c64000c1510742e40d0703e8500390380c1400100b0708010003011011800d074040c840341000c04648541901c0d0001c10b120a256240074201c800f802d6164442c2d0b944a18000001030184420350140c109511158904d40b071045d9145100008840c0e10211000c0c41d400280b0f95000d1000e4490041007200c00140030101c2c0340b10b8620008010b50480e03440b010090f00034001c030b0500309071600c0c0c1e01034202e50114400c06c0a1070f550b0720840b05074040208210144681c4514150520 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 516130944 1250 516129694 516129721
    0x71704021c0b10080c06040302040e0c0402030703060e0c09150705010b0d0602030109050f0108100b15030c041d071b140f010605010e180601050304030c0f0c050f010e0108010b03 78
    0x9040340c0100d03140c9001189031100400600303c8030301c03c5564080002190744c4001190308541c1300d00042c05142072504540801c0018170314446146078900c50410125255252800618400e98040d00d00154151400c4084180040c000b040903403040410410806195610901041c40c00000410b00b910740d09246480c41c01095001e115a41c455002d40310181042140d130002e41c180c0c0e40c0c68405110903150344103410044070007800ba103a031716080000f001441032601d034400314081c4d4000307000c1c0101902e148600a030340d40c02a10b1032008204e0006003071003413002000b800c4d541d040e240882c0301034a1070554402400c982a42440c1c0010078604440c0009114400d00307000b480c4401c120a45240400b00744180b40203104e40d2003814049540d1242030700143c600142580c0700c0c1a01000c2041580d0b0b03802004585561009004038180000401104049041c001501e00c0940c80384840802c654206007c0042d190321260f40c05041280400148425980c0f0021550441b18480c0810303031661903113051300540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 516132194 1250 516130944 516130969
    0x1142d0f03040f1a060f15040e01030809040506011407060b040b0415030201030b0f030703120315080601060201050c030402030a030807020c03032b051e0601020106171f0507170402 79
    0x110020080c0018001440c00c0304143c3c922594074500400002c14a14403002002c80303201c0c1e8402c1400076291349506062001d54080c080103000d40d45880d03201c0d06012102c3c0000c0e001601d0f00140480d030305000b410107108460300000c003420320065111010100740f40b90320410400404d0241c952100110685841c0c00807207020704001c1c41441192031032210b45440158511060740000d04240025410741460901d038107080344058080c0207441d0540c0c9508014102442c4401e003019500c61a020802340c10a1824000d0024031000c0c140c194500b5000034250f42018004200c0481c04006200040c0c0c0c4c005440c080d82540b40c180640150307100c00c410383c01c0800100d29281c2601000a03124500110070181480608040d400550400c4000626404440080700c00c2d00d080454032000049d0105e60f0a0300d00d03440641440045000b90701c60414612285040007a481641c2c08a09410341107200b82d031520b500034100b5842004240f504d01c0005055440d402e0401c031180007854042401d548403090080c15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 516133444 1250 516132194 516132217
    0x80703020a0b130203210d0b0f06130602120f180a09150602060a110304020d0c091103061003110a05070804030501020403080c160806010b0306120706050901142d 71
    0x149420410301d01020070b103410032440390044240005d8000300344400039541c8500006643c0c200752401907e00d00810a09881d10b900032003600e075800031039072007000822600c0e05200e10343d5030003450301e40041d1408052410122012000f8480e1400d11044142030b181483c1c040039003601f0001201e400700b410b808650f000362220906113000c09580d4141a8001e000b140c00710b6003221f0042e65004a09c0f4201c654520001e0015074081002c0340c094944824488806070203226222095942e0303070f000c43d01711406003030400e06800c00841001818078001d540152504407604052010701c04442c025020b51103032070283b0b028030401054440a2164003015500919031180c02150307115142d04003110341d50420032a50315644112006022903115600f000400c884e010320007040517908142101d5056000107140e260415030b8014081140d074000c012103801000a03440b000c0d5038040b81c0d0300050903185410b1075008000c0c01004070f5040c0c403021481d42c1c040c0020480c80ca603150070026206204903c2000034160 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 516134694 1250 516133444 516133463
    0x807080d02160c06120b0d0602130e191a0a0b0a030f090b04020406060504080a0b0a110316020c01050c190519030e010314130f030201060914180118080703020a 70
    0x400104a040b24140c50160b04c0707006480170b52054900544400000d0240c102d9103040c0018006007003600a4000c1c1c06811040c03000309600c0da0303007103d4a01c2c41107030898050441c0c0390321040c2d4040c0f0361013004054074a03c515021400c1110300801d90348000b82c400c841411100050404144d8403035400380d50410506c400500c8030102a003841d0300c0e03070300055070142e214074500b19002403401e000303400b2a0304540c40d04016040740302084d00c502000900080409080c0c945590018800d10442001144200d94510103990032610a5000070310340582c00403040e045c01010010b007490318100003091030600c10a51112400520180340813420311000310074800b0150300302901c4070101a0800e0314080c3c14000fe82c2d04106a005989402100100a0b80e09001c1c9001d4441c4a0b0081102c164190340c55034000c0c0008240a0340d02e06140d0111840200c50004040d604c0042c06a81614001880c00a0307400800a001e0b003d410000e17a209030318003950041184d60001280000c0500903c03001000c1904001d510 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 516135944 1250 516134694 516134737
    0xc050a1b0506040602031306090602100c031d0105100e0c040504110702060406050415090302090609062e0e0904020907050a2a052109010e040908210907030807080d02 73
    0x5c0d40d240c100c0608002c00e25601380d40420342c98810481e900c1161481d03401410340300c40e24a0454001c203c2c00ba82c0004040d12004002d007080a1282c06a2003e040040009801d05c0c11000764140d0700d049030020380303c207050306c014098200440c2098506840b81100c0c005195255000c52031114030542c0e00094101c032000c50005a11ba03001400380046412060031500d028100e100c080300c810850340070003540b000400000c1581070901400380340d401078000e450248140c0118034400301c0301c0310b850b0006003d000349004000036035620080e00041000242c179a41d4090916a00107085124001c2c225000c119000c1489135039148664011004103010071800d00d980c1102d1003100180c8100e080c4150f81380d100d4486200301ca400c43d1207011344000c0304003000c9820146450011500400051130342c55000d620340803480c002c1481840102089220743c0080d860f07828400b04014843da50061141015400c07400b01080450315650403544802e51020141b940c1d664501d600318000d00512960305d048403080c0c81007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 516137194 1250 516135944 516135947
    0x12c040c020a1406040b04060c1b050f010f090c03030305040206120f010f060c0b0106140c060c070c1d0718080607110709060609180e0d050310060c050a1b05060406 72
    0x1810b1158000e500c1492810050303008103507501000e44004100c2a020300c0040c0c0490166402510284000d1403e90608030b4402c00c0c55030783c03403d03040c0140c0e000c1d0051400c400c0c00d144244240710840100010500018140b074035481e00a514034030015041c0b589034000a801c55441300c0c207e60100032100c4440c106410245240b154800007401100c40d04003003d0300108040d13018540b44000326900440300c010b940c0c01c01d80d00716107440c410045205418824404442c020400b44245449645c0c83c0c54403a0700c0da101803e215540c210a64481140d40c9440c4620800684503a0300480d441061070414213103141034245281401c00d2164000b14242c003030b80051114040c0d00c059080404400c04088a400640720078001c0c0484003544211004030b100403104100c02107007040c3c81104080b44c3c82e070015541140095946c03c180103040c040d400508000100022200208800c03000703450b540c58040e4a40340307503541d500d58031003010314081c0c91207081521000c841d40e40e40300395001524000e010103403601e80d507840 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 516138444 1250 516137194 516137203
    0x80d0c0516080315090610031e0204060e0307140a06030903210e0c040e0c121510091424030106090c05090a170705060703020c03031615060302012c040c02 68
    0x502101e1341281500c41c024074548452214020703400102070143c00410840f0540080c6400304444255810300b51180b40a070020740b01510003000580c03100041610021300f05420540c4d035800c41180c072007035043c800d400b60301c540c000c0505480307450800140744005802d040c1e980103210302c7c9a000e40a80c00c1c108424004598102602107500301c0101d50040e4603100400c0140e808002c0080c1c02940502288245460040c03000311031070011b1801d446619055940300b43c4000401c941030032000069400800010415200e44190281d04030122038560901c4546c2031140d042d000c95944030868901032070b5086580030750040c4024880c50404000e810344004c2c014140380c1040510fa03109400c00000081c100000c03402c2040200a1701e40600700b0356085c802005159082240150308510a0065120301510100001c100f00f441486404a40c95114604540c05410f20300e000c90241d410400104010303600900010214416071040003250500c8420112044055143d20340d0b1203414145400443c940119 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 516139694 1250 516138444 516138451
    0x2030c1b010807112d030705010516020f2a0307090b0a050a051c0812040807140318010e03010b0402030a020904050603030a02030a050d060305060709060e030109080d0c05160803 78
    0xc856408a5070f500e0030582e24500c0c105181401500003d580e800c880c0b041031284109000400c4d038407040c101d0324040031844d507001a0001c4034076a65030760138085400c00019081009001c00d100400040c0e1030340c400580c603000300c0e1540b10080020b04170b6840c0340140e40040c21441301c6010702225003113039035081c8600140c11131491203801074001d0300c404034060400d4210b040a841c0090140070380c41c1c00301c01640d48540c038007100548490b00280501c405000c070078115640558000c1440c244c8950203820985000070448032000400ea01c100424030901c8180001782c0301d80390090a0035515031200c240030901401201901c20b500074070010130451603221960103041c04c60004c0e94200f102d55a00024140d4030311401c454800540d10520a0201c4c1d20720540042441c0c030182e44000c542c1c036a50b9a00c0780e00e0190181c500b40040340c80000c05000c00343c1d1200d00c07030b0701c081c0003100240450b040540342c01e240386c401e98024203401c0c0d489005280c84540500101d031840000d241000304614082d080000b01c542066 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 516140944 1250 516139694 516139697
    0xf010501120c080c0306010309051209030d030504030c120504180207060e030c061b040504060303020d0e0301060b040303051312030f0e090103020f19080607030b03070e0907031202030c1b01 83
    0x212842429901d1521030101d0b6001c460315514007940f5401411600e03900010700b0581015202c040810004505100c01c070600b580c100d148644a00b20481050300307001181a07608101441c080070407010030b5025400e50040c5400c0303501542068280c0340e003160280306c0d51300804442c4001c4903003a4107000041c0d000307146242c010b010411038500e20300d80440d128450078003060065403001c800300341116112001501380c402c05950191810340d540300402c043e103155900650150b000309075004c0d0015000368000c0c0100204800800078281041000840c0e40a14000034041100118a0070811008904c40102400c415240c1407414603c503d4000d10000072060800f00103092002c24012070f00f4152841d0307059aa00610359003480300c20205002e410a100103190b07884070407108001925030300a00c0118016200c41c0c0c0c010504070040810b1601d0324440d41d004002c680900c1c02003101400010544c43d00390fa61200c03c040d40b24411032012071940c003171811503050502403110440b03c28608080030b07034540f450070f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 516142194 1250 516140944 516140957
    0x110706200601140915090a0603110f0a060311120c0405030d020312040807030c23070803120a05040f05120a0f08060a090203070215090d020613150c050c060f010501 72
    0x2550380d1515402e10400c4541004840100a00c1c0340c039075101e940c0111400d1031160140d28040000d0f002040a690184649603550014814010f0322050030300096025070301c440083c0543c101154111074580f00381020141d540c1620541c0b01c3e5400100e03032140450801c4a10b80703040c4504002c01c5a40b042c400d0501c03a00c105001c40c41914004004d40e008030304098040044c0e682c480d00c600300c481e441050218104480e01d10503070000307006902100d00a1411f5080e5905290b04018002d02d820380c02d40026030183e00c14050400000d5841a0440d07101400c072401045640700ca141ca5800d01518110003400360003103548551040400d9009412011410350310107440c0c01d0b0651095038054000da0303d03160860851725040c040201c581c0c0003076030081e40b940b049801e00510303c0c42108410b107003903c254403282c21500045003015070400841da04009850f41e0403600c03000542d50017085020282e102001592200d80d0041c901b40101d054a41e043d00038010380741c081c0380611b00754041d00d0003405241c2c0410700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 516143444 1250 516142194 516142247
    0x501060806071107140406030501020a082409060625052b020309100504050d11030f060105281706090610080a06050c040f08072310030c110706 63
    0x4251104080d1203803c03406441e1141c03d02d59071194450010a106400941b00c00000000403c244010705002100759661215820200d03a11024002a191845070301180403141800b242c3d02c030701130241c004c2c1048030002c0d5542c82c2e110071030410300144a505007000140712440401e0000115071078504511300740b0485c1c039010403251118075010b41d4051400040c0e10a11a0050700c5c00d0004d00c8204c3c41c035036402d10505165a447c001220009080300c00c03a21034441d18089410f90808102410003403c020014002e550304160104011214204042d0621100c4c88404013101c41003c400300068002d00102e140d1040740a4440c60741c0c3d20741515412130350f216810000d910100c034810880e041e00c407524041c10250203162a820040d00d0090103005030302e9810800003440e00014000c5034010034003100a40710342d40c40d04003807400c94120041d502c0138030b074004040c04466a075018203090285001d810f001501e9942a40708507442040d003c2e02800c61310504a01040300d58000c0800340244510006002c01c404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 516144694 1250 516143444 516143447
    0x5100c0b10060801051309050715030f1a130b042c010614040e0c12010c0f02010c0c140a0209010308090a050d110f0315010e0105010f230d0e0a050106080607 69
    0x1075200c0c2d0400203000342d005020920b4141e0700c0080e44c448810001c90488210b445050518540c1da0004900c0041010540e10881d054094140a280d02030b40c10881d100c0b87d8900091011a820300c640e200d20451981d401c681c86540c1d2001c460040041c204000000401480070301030011b41c60100b0100c16013031400000518140070b071800351803440720380e262482901028031001e40040340da40c114034018601c550f0000d86400030028062800080082400c0d00c101402a1980e0b204008406c00c590501e40020b04c2c0d82d400519800c0303010ba00c40041e60004c041495542d061035000704009500c4844140008248001c2c08045c01508208503400110181d4650820454001c0d001d00201a0302ca801c480020500c1e0007051034840800180c140c1e1542d46800c51400300c9104240c2000e00f103c0e0085c001407040d540c0c004441220301b0034504101d41d041c1d9000c072003a07654042009804800e08000580e0000f03400b400d400c50510121220100c0362041000e14005001c0d082034011103e0a1203904002400076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 516145944 1250 516144694 516144721
    0xc040605040c020a060e03120c03040b01050a0311190513060906060905090a0e120706090c1508040b0c0f160204270303020705120403110f0103050705180a05100c0b 72
    0xc0b03140c0c0c1c0003014076000075601c00028003528404200300740824040007200c060802c00c1a88203c8102c0742d810358a20b0b00303240c101a03054041c1c00041c02814561000e2001810b40c5540d407401400440f02448200b91901142038420300076000f290300300c801315a15400c0100181c100c441511101041032210f80d0300c6440031190225940304580d442018100071449004aa82c4820010039110003070f00c079950b450741c403c0d4107254000b010860300a40d030340c1c00c03000920110051480140039007110141c2c070110520320091075102c0190000c1d009840020202e04408030a100702c5410031154a0f00136110561103d51503010607400d0000d9008608100c002175144011080d000308129102401c0003420b0800d4034110003e40010008540354401e803a0324049ca5201a00a08015440340c80301300a1298034800b445001d4901004031418941800140f002086d0007a0913980e00e04030307171240b00000402401c00038098031180e500041d000100b40d00f02c00000c0750f0081c00c001c499801154440400d8440740a4600c25 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 516147194 1250 516145944 516145961
    0x3060109140303071115070c1e0b030c031f0b0408060109050702030a0f0c0b0a0b0f041104090c0c020a0303020601150504080d0507151109041a030a02010c030909020c0c04060504 78
    0x40d081005000c000403400f060005d15108094403642208032000c070340d101103601950301911030401c114010022100207610090300c41c9850880521a685890f480d6034450001030b0644543d12800700004046001c0d685916003c1c9800e003080e81022561190740780c0c00356006005201c658080c0e200003149508450103403500a190725402180b410300803034000c0381ca41a8414000d0104501c510001c404200b04031190344c0280e0342e0000000c1d20b00c50311010440120b0315001d0360b60046083c2040c40b8022880c400540d030444803e10700c0840c0310180c02108885203c5000c2000354840c03401c031404800c1c1580040c80303131305940b1400215201c84503040001d80c2c15000381d10401c449a444800e485013064480e0000d8014284100c030400307050211804500252200380c203190850383da0118118480e4681409441c50342c0307021641640d01c0300f030903002082d10b03104841c401034144582108042c04251244943d000241140b403002c5445070961003c06440b150010f4140e03100d14103114020840d0326161050207803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 516148444 1250 516147194 516147199
    0x10609020928050103021308010f1514010c0605090a051009020102060906040b07051c0e0c03070605160b090c030601060914090c030708090c100e040e07051003020c010914030306010914 81
    0x744140f40c03200440207075200c81da050741011060000040c0042c0c090055000e00c05e100d040104080c0700c4d0300d19802000302d5550142459680780d01403c0030340c0c0d80024211003500d801c80c001007615598001034520f4444852002086446001c40d150242c0403140d10000101d4400d03400da03402a11343c4620183c0e81c10040d00c0c05402a014000442c02d07003409040100300943c0e03100fa078260b180c03130380c07120702401c90321002d044408070341013048507030102d16040c41840064409810b01606000340e11308018522030405100800344000c0501040c4c1260b002c00519568880090854a0640e100c500040100f2014810340801c00042c80e40900700b03280180c049032188820244041c00c2d9614900112444017010f42654950700909080d4003107610f521003c0381003520b031512500011010b550502c42110342900001045420001061003199030702e5242540c0020380e4607015844550894a540c014814400000c100c0c450300301207444c1140d4044042c500c502402d8a03101c09140d52900400e100310800c29203142d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 516149694 1250 516148444 516148519
    0x11160503060a0903031e14010905090a03030b0612131101030203060d0b060109030b070f09050406050a05100306090216120201051b0d020715060810020f04030b0c0c0106090209 77
    0x160302e50b070140d00c00c42c4014020b150120721403040800702a001e000b01c080c0d003648142c45e80084484824414034030380c01840c018a00b0412441c18811440c0c88408001000f0700b05a2141040701d0030355521f800341e40003100720403880402c504240000b0000700c414108200c803203a01c6c5420b07105d5603601902c00d903442020f014002d260021255921080161001010355040c44070020001c8085200b890380c140c403400603504d480c2c4d4080300300200a0719075103059004a11450805405100b2509c0310340818044880030b8070038600c0310701c600f141078010b4146030300031620b014404900c4d03100e02040c40000c41c0d640c81c080c020402a5485c00310741203003a110112101c1ca059440446001500f0021100a0000c000220401400d04071180d842007191032210705403080040d01e405040c04102c5083c00030b001c0311a50f0140842c90118144203030f08640c0501c1c40098800401800050041c60b0327040308541c0101003440007080401d803206c8801c0c009400100000f4010071640c101248501c0d90300c5c0c41c0440e024140140344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 516150944 1250 516149694 516149701
    0x9050906060c0d051b070513020f0705030711090a02070b010e0a020909091e06070801060804150504031d040e03030a0b0a030f03050c1606270b04061116050306 70
    0x950102400c49900240100440b0000c0708040c4803030949066070303a641c2595413440350605da51007a00301c518098160401c203c20801552002c108980701c100000c00581c079840d4244d40e80c40035009242003e06180400140c07813040004e40c410010504c03130101c400214585851406104030300995038001c0084040000620030003000042e40d66012095100240c5000f80140c00300e030800c40241e40d803c500d903010300c0d154039049841807040d55003d50300300b001306090700c1c2140c0024010801840f5040c00e1103d56404039040c00016442000e0440d0410010301040c2810326005202811007a404c078515041c00785a4880780c42c05d40110b03031400003600000e604648074101c14000415800b40310a600422842c00000056540c02c9040c8825000342c071025107a844105030380e418100c56842d40c1c020b5011203507040c48581c1d040185030058013012518117070203040b030100440c00c40303403590400c07001e010b400b2900240c2c483c0d120805108015185042e13a5001205501f264020402c034003400382e158001c00001b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 516152194 1250 516150944 516150949
    0xe040812090c13060f2c04050705120d020106060e220b0a08030301060e030a02011b0311030d1a03030c060103081c0606050702030c011e1101110d0e1603030905 70
    0x60350442594016140c946142c600040c1c042801500300000882e00d07000104094000c1c0f2521100400e900712403140300d41c0c01c0300036400c400b1407000d5052880d0800070010400340101002224042c0c0310250a018500c1048021180c3d10b0b00c074084240700641c00c1200106189200e4504422196000780080005100c00a02414100307611001d40140c2580e07048841001d40e42d8003808401010780101541d50b0394100100240b40442c20200c0710b0282d80220007400c010307680901400c015514001008501035000c4c40c04843d8562071101c0d80c0b80a10020984e141c0340601e644c0300f0403886243d03002d06540304d640142810b40b01e02800e80c4060194100d00e004201064140006201c0b40300402c08041c01341a43d02c1c215001c44015030080000104003185420450600b000500700c0030342c003420300c2c03a840b0384488031422207002c0e138503249000c1181d400b600416401003508402e080d00c00e00000355403a0803140c03d0501c024461317050030104621426009a1364003107480041010759400d80c0d125072056052906 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 516153444 1250 516152194 516152227
    0x122903070f1a0d090b01030b0a0203160302072406050f0a03120c0c080f0d0305130224070501110d150e0402040902060f1602130c02150406060e010602060403090e0408 73
    0x601c000c0340c204103080c143d507028810282e2852080700d81c01c440307504506065404244c01408143c1c400c0c0b04000740300764038011254000c1701c0e0341246000b603503400740c1d45080f00220380c84c1094899900518504248444a140c1044003030303440903240300c1034262243d410060041e803548805081120198148044a03100d500001e400c0c0e4010400c0290880c0d03245081c501d0100b40c00b114200d01d03040603041e2041c0d1a450700485400c944101030440b05001070fa000034218203102004031031044c0c0c000b1502424407072000107446106802000801030b076640d440310856154400d140e55400c452410000001c1100c040031001c09131007020800076000c1c0e46036030a11006100c6081c00f0f980c80402400546081742000c0c004000c040501800c1040707040440c81486440c030001d00c4007015403410b0101158000f07070b00050508442060758180c0c101c0380c4a07820302000a00c5035030800c01d2080b03008400030035400d0300000c00c180100e10980c0c0e0f1140b1140d51708190540030400b0b84009106d800100840c0080c21807d24 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 516154694 1250 516153444 516153479
    0x120512040b0603011a13150f1d06010c02130f110a050c1c0c030503090a080a03091101090b070201030213090504140d080103080f030702010f180c050a030f080307122903070f 76
    0xb403001003a1030b2184541c041c07041c1d065100c2c450f004801000317030102c12761183c42d41e134000c07a083c205118a52182e5000079103184128030341c402c0c1a07940e1000443d0242e00e640250349109003a0403070355501d001080c00149680c1c004c200c1d4001a20403060040d909208410340d148003820706560303800c150126541c040f90301e0b9001070241885885640c0b02200869074010042c0b151640549000801103014501041961800719407181440290101000314483c079804846000c1c6d824a801a51001121382e600b6500c85903400c15000d0a01c0c100c100001c01584440303000108600744100e4000140c1584200c4d068582404002e001d50802e011640c035050403280655080002030001003050790110318008121049207005150b41e56181301c482040c0101541ca950150030196607040b200e23800c54403000e040200612009115900020025550911515525040d4551800e0078007050050b030750f03945900700090700c054100e040345051458652034002101b0f41111500452740d04002e140c11244102100d051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 516155944 1250 516154694 516154721
    0xf0f0a0e0c0721170702060613020c070902130f12021e0904030e01140301050306070e031f051005041e0b010c08070f1103060103030903120512040b0603011a13 70
    0x9100702c600280c291a503603003079500543c604690303111840c1c00050400c1007016201115480300c1c03040c00103039039000c40d100f40c0c0724070161484c611410b40d4041c214001e00c03501403011100d000e40d010103d182d00d401c0c0c0040045001d8200030301c8031981c80e81580c19440701c95200341c4446404089042d80182005089400c034484a0030140c84c072039540c4404145903034400c4a04a002900141e0040304035a0013111041a5401c1400003500b9981400042560340002400c0d81c42171103240c5041e60743c1c3c0e40d0100406100303a40c00402004202054181a00c080d20302070318034100d030401c404000f01d0309003458450480e06001c0103016405001c0318184850045c0010881a810011850154804682c140c001452018031030804200f00d800c42c2d04100500090040d045403181d0030200c010008668400115400d4a03004401031004444001c0300f5507041c855840ba00b0054a1124100801d00c02e81c103201a100300b600b68024003801070300c03a0801c05d11081b807580c120341c03007501002003a00005a0b6400b5110b41940c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 516157194 1250 516155944 516155947
    0x903170d1805012912120a0c060f050402010804030c020f0d150f050405060705220801020c120f250506090d020c0d0b0a1a060c0307020f0f0a0e0c 64
    0x3203010019140000c00d0031601e440c011452000300700c4244100c0c44429401072038030990101d081c1221900e0510000c41d1441151106488084039209006044203000303402240d0359100c0d50b00401400b60042d40c007040c1e4139a4500341160090304468000c55109982c140d4940e1132986e11554192030722442d540b01603030010f0903107907000407980f20034046003a850300490100362030300c03d29402c02c800c0d2441900c004543e50b00700310a200c0000e80000350940c004000341401c0b508e0f4110350200b1804103030000f150164070002900e0000303020f5010742c000c195440152058030081c43c03010180410601c2501d102c2124400704010364008828803103103412204003d1441c00080c00a6a211145044400d0b41e10040b00c1e08130703a200244081d010090f0100d900d00a5614081d11901a141c10f104c20310300410115041d43c9844c540d4048913500d0b113031002707a034030010710710b41e100c0b404034107072a80d2034001c010100e01607140100003800ca440c04248484490200600e000001d03420855100c20b01e140141c1548101d140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 516158444 1250 516157194 516157207
    0xb03070c0c0513270b07050f120106080901231501030603060911030709090b06040507030e0601030c0f0f03020307170a0c0308090405010605090f1c0501050c030603010b10090317 78
    0x3190748616544a010600120301d205180c072004c02905503200310041c50300030081490002510b0250a15800030716420229201e00c00300000c030b4014850b00c5684100742d240f482c0040b1f091754001810502421003030300200600441c00c00d0a906180c2d9011100c0682c2e400c0c0c00000d1050105804842d00e090010714010500c143e403592010260781da00e07a811900d10728014441c0d605030070200070560040c1400c1506002041d620340303c070618081c000d020103004030380380c0c00011545c5000760001004c01501c83d02320b502070342c1e680c1480c40c1211002c1c0100c094141c40070000040503140c04441c001600e4008000c1c00400b4a012010044040d03648003280140c00b82c0e04068020464140c240b0700118005c001071552445000e041004843e03050f0080014800140100c01c100d03184e0310542039094a055400400301c0070141100407040005540c01441ca40c01d110030080c17605000c20166002e1a0190000d1140c110510304129900c240e0000d84400036070410801c01c086610801d00000155084000915014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 516159694 1250 516158444 516158449
    0x11030615090c1b0c10090b0a030906180501050a1a0f190803030a060306050a05010b120c1603030f0606090e0f1b0c0a0c090b0d080d0f06080616030203010b03070c0c05 73
    0x5040d020108165007040c80740303070514107054040e103150002610305032507290b01f4004803003203501840d19423404040d41c6414110420540c0da1000304441ca003524900c100304600d20703265004c2c01c0e040b44d0030a00c131410400084403483d42c3c100e004004038001000d0100001243c01030000f030820400c91000342d4060000c1c0094181c1040c00114000c0d000c1d0a0003186850850400b9800da800250114400919041c01008010458070076107100c1000e10340d402c0c81a46980801400500070904030320308603503074288940c0406415600122400b0880302040c0110303a03440c030041d60741c092036101e00c50700503203110b000990f107082075100030350f003c6076614885550420340d03010884550001c0c100380505512140c074280500041507030320802001142002e00003c00502e01040b4000705000c80104800d40100c0c13411141c52443d001030584a8010004102c05d81e603030030302d4540c1d0b15402e071040381c01003020304000c400180c030030300840e41a82e100d00d04a0345544c0700c07800300720340043c060507040d203000307000d2107012811387d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 516160944 1250 516159694 516159727
    0x19150b0c01060905090f010e031606021305060a050417030307080f04031b0c032310020702010207180b0a080606060a1b05070e010f0f0e040605060a0905100311030615090c 75
    0x85003038200420306d0344c402c07003025401c54014002e1204541c0c001d00401c0c051018041003002e80c07230381c07010000d616444141d5080109100c6e58101c0344d40220301041c01141554000c0142c000c0750a0b01809114102c13a1000f415201d101c192080c00002d2841800a240c10420000c66608140b03e4901103c01c0240e000900c00003404a940803030300d41103003070010024031507511002e02524a00c62507400060700c03003100185d43d444480082d02c440d5a00030a034442960b0090081c0b100074065410447c00030386c140c994507001007a5900047c1d200302c1e040d41010076500070024409201c1ca5001c3c084034900614504180c8503000381c4080001080601089540050710501081000b450712292007600340d41014100300b540b00c043e400c41c003070304181d400c010402c881e0105009500030390420400610703600d5610210721140c0080d000041030074101000d108591210940303407070850380070306a00007024442d04100b684030030341a240c2e68002010300d850034141c1d00d801d00c0413942241c411511249810008410020718 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 516162194 1250 516160944 516160951
    0x14040c050d050a050a0b2707170f19030f050a05031b0f07140d0509031b0406030f14070f03120f03020d0906060e010905010b030f060d0606080619150b0c01060905 71
    0xb1002e203c014000c01d08151042c00001221a250284c000c2d04003028055982048e4891a030500400d075000715281c0405000142c06240d581054a01d00a03411642c0503045080c2c980460000e075250920040c2e140c89041a50002506965010301e0340e2100f03880c004000c2403140c00c43d803507c1010051200e0b03070f40d040e200401c030251113154070300f1003001000c41050800b4204860442400810007070344d54641d07400b1034400341011841c009403a20b2410500400d00074202508020249070030140c42c90107210314040580c0b21031b0480002c8600241c3c603807030781004000c007030301c00205020394100558900301e0041030003004000b62440c0060410300501c00c07202c00d840748035a065a05940e901c006000208094401030b0140065040c2884103514082041c0414800105005031601864001c98605d40c0c40c40c90546e1110740100c418000c654840920a071a00025120b11a00c0c1882e50000c03050240c040c01003804810bc2c01c0002603140c1d15144612038140d116083c20480e55517500004160494984a0b8030301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 516163444 1250 516162194 516162203
    0x30f050304121b080c1003090501062c0919030503040330140c03010e0c07020d031205060406030510020f040b0705011b020304030203071a071a070314040c050d050a050a 74
    0xb80d2840020b101ca220b80320384c1107920680c00c60140c1414640f201d10b080c101410861030006180305060408c14010300a68101020700384510190310b011240c0341c84030480500d0b40900901c41074454050003a80d801a0604050000d0025581d00011a000d40040e680c440c0c021304108c4103176940e945213106c03030110201648040d00d504041c0040012218494480800d0031215080340d503007060210408076000510801c0520f03103180000410840088c000e1b00e030f4680d800303000003a50321aa850060502c40f0304d200003943e018501300000e19103240c1401604100e81e0010041c1c020000140f010750f002e54012003400704059010080015054042c07002800034501038800005e0111401941000e5110720540c4581158010300040c009031303501280040031289840350750700e0800420304822003c2d01981c200540010140c101d1016580300702c4044a20031809603030200280302c6040072840c56003009480142501102c184140200d0901c09220301c0800d0160080315020082135842d140340c1203405000f06e0303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 516164694 1250 516163444 516163463
    0x100e0c15120115030c0318080a0c1505040204180c09150305070b0309191110030b040c02160501030c021905010b03030310030c050a080a3005040e070315030f05030412 73
    0x50702c49078503100e8141c00303005c5890148480d2804498510340a0b98014000c1c02d04a800200c0103652070040442d840419132104c0d03980030121804180c0030003090102e5050f03014900784006083d1703186401c010b15200952044c140c3c03050a043c4860b00001b05541520145105d172611004400702d4000c00010004240002ca1036a4a107400c4c03100c0c509061204442148240d0000c40400010711a003507184070b1308500b2ba6000100c10542079007203000d49400150070345c01a1400400b50341c840d60100d07a048c110759a81034900c281d0369941004408551482d0804401038024907a48a40740b03084074a00c5144a00400020072a03040200010342964800d94401d071400340c00820810130045010510401401d0842e41c01c14164580f01c0c0c0c19448118218000706101f0390401d40800c403100d100301c550f80751b00d1b1080742c441501e981640040c01a9029014031205840150700081805200c1d001300456403046001c82e400c0c0c0f44c80d43c0d895200c0313010324101c100d40b6404180000b10b208171440050101d0309000b0343c000b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 516165944 1250 516164694 516164729
    0x60f070e2206050405041e020301020706110a02010c0807050405090c36030a0b0402040b15030a0f05102d090c050a0e0306040302070b09150c01020c100e0c151201 71
    0x30300b140c89681c0518095410003040102081d01d032031903000000c1c6c0f007040202d0a00d40703c0c40001c1c028401c00030001c2181d485c00500080c00f100c00c0c0c6c040d0600020940080104016040060382d00800840340e18000400420086c01141090a0302d42d4100c0744090566043c00e051015010400d5102c008481e070b00c5019040356103000550b510041c0c0c00c400240c015005000003611005401d5000030000390044e51103146401c9142c0b200b003240c2400400441c0031a459051444840d00940400007640301007c1c01c14002c5004511f13142e01c0b0404480c4400e0701c0a400503210f02c4648204110045c0b00d505403040194001000400d500940c100c1da1515910320b0755840300c20074080e01214041039940d0081d40040b00b0000041d400043c031038144d0b801407503183d440703580c0000021040e41074800500da5400c00420110082c13881500586030518400042d40c892021040c441822210480d0101009500c40740d01385a20341400701e07115005403401055185091102c0e29101e01444003a0702005c92015101c2d0300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 516167194 1250 516165944 516166009
    0x909080d0c020a20061b100e01060920070b060118290c1b0604170105040201030516020705210105040f0c0807050604090f15060507020f060309060f070e 67
    0x240d41407011922071806072100f038030020030700e170b809030510341c2400f034140d10784004140d04104041e800300100060107028505451746e00b18080c01c15031140f80c0e00641002c43c2000a070444901028024180c500030b0340c146041901d580704080c0004d070006050164a01080c51601070254205015041440e01004008441da144c500d00c04203000d01c040345548184a8000601404280290207005400094003050100c0300022079a120715880341440c40c02c50162109200c0b010b4220522a0b07000341c80800c0a5958032014812004004009a0050700840402e200c5480c240045560300c90810000e40a030007044050310382112015141507803500d00d01356051040140a80391180500448400781008a1502001c06d080740964002c45000c81d0700c1c3d0326084003c0d0b0050384020344080b880700c4d0116029035103600183c026406460180e000b95451001c1d500241810421207005007a11b40060005681d250580c104410000e03104004100c1440750140c1d05940362013003004c000302c03945849025406000c54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 516168444 1250 516167194 516167213
    0x80714011b0c0b150102031c0e070801090c0e04060f05012d0f0315140106050c010c020703020907110f0f0d0806040507020c01050307020c03060c0a270909080d0c020a 73
    0x4000c211115031141c001515183c81d903034000c50700402e181c048a400100607415800b6428111085150354501186201c405801c010070201c400c509844c01d05840303040c0c19082c1c4022040c080d09000c0c400340100890980089501d41c014041c040020b044807820b40d0840c2034801c01e90004d00a02c200345c0d4181101d60740c6c0d004000d41009184023102076145000100c00e400440303440301601e507229000590400b401030360412400f9010148590040d1f68580d40091b101e0340200300141c40d10b40c6401420740c0c045000058810550740c00420b9000690b403002e50480b15441241e00c555018000c00c1072490507040100410650044444040d000000000800030301410005141c0c1d4800c1e4200070502100540120324481007400031f191860f80c03591000303016031510490300000b03070300340c400c14040050005c401c02c050300c200d111941c1c0c1c620b43c1d01414000852130000d0700c0e0640d03207048a08041040100c0c3d01d50f0000701050701c1800300e203090066030300d00f00f400c030b500d903003141005600090280d8007004901d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 516169694 1250 516168444 516168491
    0x1b0f120b06010c1110030f0219080a0507080a020c0316111305010b0706020a0207031b090f0c091712030f1503030a0e0f120f0109050d091404050408071401 68
    0x2034900b540c8503c5441c1d001e8080d00c40040580900d0210000c516000d1113500444000840840190341d81e2008074074a905903003940e64140000b608482c04562101928041d040c01071640e03a503440001c0c0c5502100000079409408044414402003103605c1c5915403043c003004089001d1000f2052194450050011840100b0424110245000014030404019405903410039400c180c005840b20300c1090280e107410710031f810180c00c80c43c40310f446c4001c0d2091900c0100668241e0301c010300c0a0b481c0c01c4114004e4420251085010a0036400188500001d04042c000d800d1489812244c2e81b0b0754072594100554801e90b22042042c500708200482c201910410407685101a4011803500b0014040102030461840407d841041030050200382da0381d55a40300016800a58180e41c8030b168640e0410b4000c0c060b54104590303c0c041c0b04240d000d480c0c01004100d003142c40000d50f08034080c5c01c11301080001c180052040742e0000041c482400070441415100c0c060701003080000880352660f84c1042c50040060 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 516170944 1250 516169694 516169697
    0x161205091f02130b0d0e06090601080c060301030f0b19020a09031e0c0b0d090803010b0a020c120d05030a0608061303090b0a0e0603060a081f0b06090307031b0f120b0601 74
    0x402ca00001428200c1100c403c80c0c001411117500c82210700c1000000d0f101b0384120100d0f61040c130f820b101281300d02003000e60403241074a00f00ca0300000a4003d00510b40000d10000e0a58002012600301251a006425a1140480165030040994a4403c5080b078004101000018526050920800042541850400c1115002100c0842543c1d40f0f40e010405107015440320f110002c41da02c04c1014058029044180d44820303090b0b00ca40e180c2151101c0d0b03800145000c001413003021070100c16420211110860611503c000d0306200a142400780e0b810fa00c090801c0c410729641d184000341906c1f06100c0349004002142e480c00420b49942170040240304070390452211844c0c20403082c1c09064006040c1010f0b40307000e444243d00d030f41e00c030b0380090f0061019901100d002d002e03000c00c841c458641c40803402018080c840c010400500110300f40440d602494111540651103030343d052010900003843c050340a4003000c044020607885001d50314041e20a64010030103035224500039010030401c8520281e200100307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 516172194 1250 516170944 516170947
    0x3090b130c05060a030605030615091308162303040501080106030b09071110060915060203070f081303050f16050339150c0c090708161205091f02 64
    0x40e5160008408114403460340f103030a001920407072860003a0445001050020152007803490305502c0442c0380c000c4a0703103061003100300b800000d206804203213240445c0c0e038002c008141000700c1890018840d0b000c00d071b810b1b00c444c4000c8160210380d9048207140303e44003128001460b00d80b494140050324041701a00801c00341800c024a2200329120f00400d1070780301c1c5580c40d00180394403440929030304001180d02c0c0440010309000c000308103800a03401c11641820044e0746016100d507110350484c2c50b40100140141b1110340440c400003ca0b0384100688102c01c0c00d190010101c1d07a40e55501c1d460241020300c481c4054211056400484562103418801000260050901c2c99410510b003000c10300d455000c2d2554807141804074807846105082d82d0358252001e403c4a60400d54400e2180c801c5d0400601151544101c0300c1c1c0c00c0345402e241d0289801810140c5826949440e64070115a200e0036101e880f0081140542d0340203000540c0340541c1d400341034000041d24110b00040c4000008000c02d41602c0b654900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 516173444 1250 516172194 516172231
    0x11106011215140f1501020712080702031e010b010201140c0a03090503041203031a0303071505060f0d03030207050d02060c07082a16060c020901060f030e0d03090b 72
    0x88098119203142d40302d81c01916400801c0e9012000348448802c010f2032a00000c01c01040c030035031050f924080c040305048000d12845070401241d403a0014055428042154a507660014101d400030307003009480101580c2050003240b0f900020141c078003242c840e030f41e911030426520355602032144100c6544a1400b103416480c1c0000404004d00c60000381900301075840848000340728041c002e0310003410060180c240911035a0a00034007800e80d200c0c685654003228080340d407681c50700208031079465031311441030241d4000c004004001040c004103101e4219017031088048042c0d07034a000d00c150aa1003070f240140c44203410704059103410303041c11101040d0f6114205104640c03c0b01e00540d0b2026621400c1582da4001d4445090b0a00c0c100380090341444102d03081200b141c20000c5500d420b840d800c03614000d500344d074606084802403900400079401c0203039580103010705403040001805980c50307030030082810130103c41c280d803401c84c0b011b1102d00000d90b01e041d50000c219411641c030382c09c412130044000c1c03a882c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 516174694 1250 516173444 516173459
    0x30109060509010312050901020f01051006080f0907060c0507030203010c0305041208061c0507030b0c21010f030b04020d02150a0e0f0619020a0506010617060301091109130c0b0901110601 82
    0x19514110f0300c180940840d0f040407070317031003005414510180b80c0e00330b21040c140030141000e00c0090f03010380700104c0c0e00703440010548000000384911071205c5c1c2e002032104520b01a41500c8160306250199503078042e082000c00076031024000c124403016141d42c00140d1b840e286c203024005481c02c00d079120030007502d00d0901105944403450a2802c070305400030034501100300e02d44186000416440104030704004010400c0804031040503048200358000c01105005810401c140b90b074509004051007002042c04c2800441c00110355241e00610103010746c400300c20540c001030f003038a00030307440c059a100c0700181109102d41d1200c050300c10900103a45440f608450100050990700480c00601140c1605480c88000c4c00c2c82040100380854010702a240d40396100c40000f400403100d42055414482c1301004582542014401c0000094005500c1c00d1003034168020403100070f401030300000b61600c444032034030089000700003800c1c01450000c51042c0c4e15000400058401407191035103040d540c1061004101d805c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 516175944 1250 516174694 516174713
    0x415020316020f0307030501051518070c060c110109061a010f090504020f0906030a051b04030f030e13020a0201020706050601032d020f22090615200d050301090605090103 75
    0x803a811200c0070f21034800903020031302c0c02d07216030b10252040d800d020a201c41e14140c2d550746a120301f02a25542c2619032101000e20f0000829034401000680c0181d40e00041040c50744043c00741017061602c0760340da1100d085003500351510341c0016101290745a81c0b04803d2006405450014079003801c02d02a484040c00014180e0b0b82d451007590701594002900c0014030012004a549140000304002e03101d040080c40e0310700a2404503021fa1001c003e054aaa003414854030035282280d0748440c0c030b89001781990760125024020b007948940c01c40d4140a0348040912140003030000c1508a600058544c02c3c241080d0050b42c0b000351105050503d08400c030881c18100c541d01d01d000b101041494a100b1a241841d6402403003290302c0b00450310008910701c00340d003c5c001ca01b0300c800c02241c110034850b43c1c1c5501d10407040703d000307121300188403501c00540380480303020342224a000d81510040407040d82980115508021041690100143d030020041c801481c5600c2980050007080d01c0c04c003030719811030b542d40d5480c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 516177194 1250 516175944 516175987
    0x10f050c0406361703071101051b0f15011509051c020402130512060f16050412060c0807021501120212010c08150402210405070b0a0504150203 63
    0x4109080d110700030b081c400465a883c0076844040c001840715102003000c00d00441c2c9002d040c2c42c1100b003003d0440214800400d5580540c4c2180b03985495401242c010359143e4010040204290101051158409414004500c0807040d04002e41a022905060351040c035205800212070740801e940d0840466034480c2d892019294140c440001011450000c80d030f815640030030095000b400016846031041c55518600200e642c2650440003402040c0d040035250302c401c0710515200b0011a00141c85e1b5619000c00c030700703440c0140c03c0242c40d1585941c03071aa1804841407003990b0550f15880340d000803d50044200b50721018520140080184c0142e0300040550188500d0b000b5603400c0181205550b12040f0a650102c00f8400801c072025040c0d2002e840d5134003c9030f241d42e05c15410340c6481710b01d0170030f4002c646500540c90546868110039840700c012400c00034200781c440d4801c4c1e40c0045010440f41d4000c1070900f0903a10b440b9107440c0f80902400c500c0f0300d004141411504244489802c208040044020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 516178444 1250 516177194 516177197
    0x20f0705061e0a020304090b0603071d0a05090f011a031003031d2701300f05151626041407030c0e06030606010906030216020a0314010f050c0406 64
    0x68454494680c8020000e0060142c1106100040c695014540010080088a840310014821351300000104070050000320b0300030b0080703500d81c0394503100410304c4200c560b500c0381c000300324061807030320f030f10100c0e007801c1c01100c0c0c2c41c440308000c0d40140250201100200d13882c245200009142d031a0040b0041007102241c4070003024004110081115400d0b840e80d94211a03901508814605d4034003581c50103540c0d2180b4904c620201800d0010400312030303041c1200e0102131103065444200d585190309030b00c5429840c3c1d040e00c021507001d1014002820911219040e030103020080141030410005000303141122103089000d101d0300d4421020700756061a12282c0145a1905912166680d4144a14072241801e010f04940c011032501008003d40c400442068036a803030383d22051981d488040c182c2d28541590068041041940e0811095111750002c20143e0000c0348007810090303140d07000c42d803400056082111809880d8100e002010b40034400d565040c1e140354410703c603d04000c40300f00d0643c804c0d03005240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 516179694 1250 516178444 516178447
    0x40b0105120a14091c090f030311011113030524010e0630160303080c070c051512090a0b061201200c0f03040b040b03060f030f011b020f070506 63
    0x14200e42083e4842c0e0790031811070440c103c00345080d0704d45903100d0f102221580382041c803090170074900da8854881c103010740f210000e07100140d50464909603031140d01e40d0381380c414564840050307a111a00c85805840140f03030b000c070100c8519066150041c10080140c070340e1515115034040c500900742420b242141141c0c1502c8400845849243c0440d26551907100440503450740b6141c0d041000c0c1c100310541c0d0b440c01424003a900801500c3c1040004a0b00511001c0c00007031825011503003e9031a400180615840ac20420108a41c2c6078007044042d40c008580c1401300b20049a05480c0c100b0051040f46d2100510f409441c40050701d03610301000b00000380000d1300440080c6600440c580c4c3c25441650403070f103807240503000c00b00c00844030b41280c0d01400034448180210142c40211190000648040ea0b407140c07202070900f401d090b10082142c000400d0158040c03c000c601c04d18907141401410905955000003094072940030002c40302c1d0040c0e4030420011075000391240b00303440c50081805402c0d102d0032140c49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 516180944 1250 516179694 516179701
    0x13080d03062c0a09111009080705060f0a0503130512030403030606050304052d010510150c051009020f0d031d0d1112030403020a0f0807090c1d060c1207020f040b010512 74
    0x4071454031082880c0d08400003122241c1d10135088900382003124405804c81c0c9c2516112818001e080c01042c2c4030310810001401441d2099000310701941c1e01610580c100142c0248035102d0610304841c1c19590842040d0001c1404185a8036006a030050034260030458a54140f5a840ca43d0310244005200d00190b0a00d1542d030040300105034211032100404c000b1700081c01e09a07034100644001d4855000303035a08035030390040200e0240544888298110340a0310b00e003014011900098031f655141240c3c8540c82d0401c0c14481e50700c501100d0126070003681c42134040e6002c59441031902403102e940d0340c46120b010501100003000c07480200b42c402c03802e0342d01c040800c1981203c1413443c01a504000d511031040c1e80c1c0840c90382b95004c00c00003101c81820417100d5403943c2d48182e030101c0f41041401000540c100041c000c80d20001d0390f0340c550400740608030074605107d2090032b50500d4160404189034074070000790441540761980c6040001e81c02200e003000004510780000c0e000c0d1041c100d22709190074840000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 516182194 1250 516180944 516180953
    0x1060e030309090718080c0a05040c09060f1e050c010b01050405030a08070c0e040506150f09150d0501020a0504140306010807060c061e0203070f0c0b0c13080d03062c0a09 75
    0x40240f003420304005c00000c29102ca00039612012214081e070b00480c402403002030709107064001d8011000c0702c0c0c0c444101f40d5042000480349003400c00d03424418801c0b00365050400c08d5550300d00c44500c41455883d6603e030b01c00a000c039400d480d00588210f0402000348420310950f0341c041215803500e90f0100d241d45d41d402d0289050814501d00b91b0104600061100400c030510002040c1c1c1d034810b0742488489140341d40d01c802040702000c42181810b8014070010001500c4c0d015260045202040040c0008404d201d41e80e116030999004400b554000f6034040b5003040000a001c414a107a82030490180c8001c0d0304110100f0381d01e0915100310020000200d59500500565034004402a480e503950405440450303000702000c1e500645001000a00607040d400407644036107c40315149502c401c03441525100c0d0200307047e0b2904400456504102c00c860000340c100c10402040e0034002c8181c9000c01d842d8640200a107041c001c4801c0303282c01e4200041c00f024421641c110311944014102c00002d6030003403a091 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 516183444 1250 516182194 516182207
    0x30b13150c0c02033301030c182901020f0a05030306060307090b0a090302010e0409030f050c01021b07030b01170307080f090402070b160219110411030c0d0501060e0303090907 77
    0x14069014010b2460401c81c41e03088071a20b012000c064003040f1480d040c041071a0b820011709100140c00070030b00d40c1c028003040490341c5240510f072254580105041c0c03100c050002282d40400c9010070420394001b0703c0040d95070144180e01404c2ea5560203010048159203a9a80340c2c0b2004215605c1074400200003030810b406072407030002804001c25010788602d40941d01900d10142030100380c1c081129090045104d06d014020b510125504d65540244040c400d002a220790f00300c035141e00500d54003849441d8040701000e520001d820000c100400c041880e41c2441182504d061708100a481d0002e5220b66512100204860301140d000c06220741c0c1e54005c901c07090b003074001c1c581101d0380710307000040316001e001e003490410340a181d02c010340f1444400c1c0c00340d003a40d030b4150541070340c0d5200403480f44250209440b500001844040130300049100140c0c896a002664003c40310450038043c00b2a018590300100e10419024040300e040c04c1e410b82c4c050f0382c002546c81c007c00c10450302c50000140041c0406200343c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 516184694 1250 516183444 516183467
    0x70b090f10090e0403020d0305150319020f06130e090d02060705030903071a07030f05060a1202060d23010f0303170414060c09040e03040e010e0a24030b13150c 70
    0x2020070003d410903140c02074039910301081c0d190002c0d04200204036209038214081d030f44100024001c20800c910840d09040c00c03080b140c02070364001c0d007080e6003400301d468050003402840f0f2030344000302010781003c002d207402c2c041c041c150201c2541301045811071a82c0000301c1d60b40121040c01c0440e1655a8588400e245220b0303008000d00410480014078190802c42200a000d035040d6241070103a41c3c101e01000041b030b05c1c11074580340e01c58688a801c000103910904850101800501240e05e85449404224143d900901c401035020a6940b12007000c40c0c10080c10b240908000700a14003020b107907440083c81010081c1d510b240d106030700400f1508100f003c0e54004640d2030504107590303440c82c1c4204004a250040480ca0f0301460402e510804003003030110864003a00e60071071854003143d00748502091442030081c03000e0704441d50750400140348400208c58808894015003496400c81c29842c2c024603038200505440c0703200709064401c0000580116007983c04424002c1c001400e0000322001b200c070408182d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 516185944 1250 516184694 516184709
    0x11b0602120702100c12020d06030b0c1c02040602100f1517160e0a09080409021201151704110f0603010f03031b11040b2808070b090f1009 61
    0x510302104407040341205124103001d809030345280e20b1000000c0d0556011400390000940020900807240c580d55025215084042c04006140d40e102da403520210038081d581e0708070356440801c103c1c1130600d17000c500507140080140d0179400c1c0703843d16102a6451070b03c0c5085100701c1d0b03110403400013607215580c07004006007c0d007d00c00403201c1d40c981c20a5a818480340c40e138100e40c000c5108000c0e60003e11003412048510603510f9414075511811560001c3c006900c003201e00a0041200040a8400d400a0180340c006111100c0702d44d45041c2ca609490304010702403600384540d450390f0080c40c09200d420594442d802807c80301c01004040001100d03d2050b0301e00300da00c03c101100102d41d20321200380c4c0c2c5051324841d845529100000c035800000100d0240002010b1108070154240c0c2c9042c15007005105081c041d200b1045510449080318054015044c107540c2814010f00800406104120b048000c109100100e80303002000380201d00e130021500000c500900000c0c0306114842d1064020358010402c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 516187050 1106 516185944 516185947
    0x702030d0f18030b180717010204330c0203010f0608030751090f02030c010e010e0f0a0b0304030207082b0809011e150902120105011b0602 61
    0x911741004014081e141c40001c94440e40c084219044100800150301c8905201d110720f8a00d59050540e03006407600c0035007441120fa11540e5103804102454409644011b03800481e024004c54025030800034941903001480f10000b201400080e4820f8003245451200c518481502c58485010f00c03ca103179116200b141016a8000c480f41c140d00c0c1d00f0b080c07122803c0801c1c28030080302c080642c161501c0350401800c00442c40c00b840800280701003403e0020400301d280f800241030061300e642d0180180b4015210070f01d143d170740e020711500821009885551300d00d80742c40c009403203039103612030001c151241450b400b000204c0307a02e00f07251803540382c2c50b5100f09060a51b0115010344024010748002d541e1074504500a500c55101400c030400c0307140c00490281c0000d191104180c038036600a0103a10f10604c138508068008000940c1158024a07000c880350040264060700c00541c00d1005219a20 = true := by decide +kernel

theorem cover : BRFrame.Cov 516007194 516187050 := by
  have h0 := BRFrame.cov_init 516007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 516007194 ≤ n) (h2 : n < 516187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
