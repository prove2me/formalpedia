-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1246
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:58:09.005584+00:00
-- url     : https://prove2.me/submissions/72f0a7fc-d160-41fd-b02f-1bd615229062

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 223920863 ≤ n < 224100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 223922113 1250 223920863 223920869
    0x10305151012061a1815010305040507060e0a09050c0a0807020c0a0b0319060b040e09030a0f14040905161b1a06040b031f15151d030a08130609 63
    0x100104080701011032203d40c0282c001160760100b0b500c03110b0700500000c1e0070040c2852009580300003c1700b84861058484d0b011031070900c081c281070200345415100c59449a40e144980018000c0019080e0060340c3d81a401030090300441c03d041000c2e00703002c0385101c901d80025a0420114640c0e0010400650000411ba440250700400328441030b410108420540c0c0c201400c1c541214100c61420400c03581a8017405015018401c1e0f004d8942c3c0c039184122071a04070207072203d9915082081201e40241c1d12254007118081141001030000510b0500320b100d0344695440403d8861900041c0084078504a0403000f02d032100e0703568003d50030806400c840044010704402099000c0c1144081400442000d12a500440c0140009290007151001c00e05000e4a84043c48104a0030340c90502c04001c648034512980c2c03099101b0321050350504030645118942141d044040c8442c0901c55200881003a070501002040501512240915468042016000100400044105810089a034074440c1c001c1d80d0803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 223923363 1250 223922113 223922129
    0x90a06090c05030112031409100503040b0a020f120c0706020304061d0d0234120308160e06030a060f060c03031a01090b0a030b15030a0b09041104180b0103051510 71
    0x103c41815034080c0d5550580d0a2001c47d0000103120b140440d0307403460032650101e003480d112940d8030300e02840c02c1c0d807006200800c01488184140118644020070b84152800c89200c0340c032000c42a155000341c640e9034020081c00401d16400041003200704551900403188800103603811304900c030039421504e520b603283c020003800168824051a418910440d588038000e900c3c00c04070601c0b0641e100130b02258086a9008486100031002d1250100340e803200a5a0340f09010350400002c0c03407000b0100514080122000700c0c85114040040741c40000c182e800b501c010b0402c1414414442c0d501c1c0b501401e204403101040d00402d140804100107141626089003465005030750718851281002c6428640e9000f070300407e010950b9031109545d80382c807182c01e40c6a0010a0b4008980c9a1400031945000d840c41060610b0182e00c86500344000500743c070368442c030480d03011500402c0d910794001c1c80b001491401440074020103a80f00000050100200341001240d000000002255847d9101c03416110310a110b0707030507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 223924613 1250 223923363 223923389
    0xc0a0f20010c080d110904020a0e010206010b07020a0b180904060b281a071703040c14090601030f1401030b06030c011b0f0c0506180a1a0f0a02010902090a06090c050301 74
    0x81d4404545d0020340035503841156a410010060b0224040343c1090b00994085450428001c2d510342c1c0421442d801071180b1381015180c002e00c2e5000c034000100c1803044d80c080140200e184203014050980d200c0c0c41c28005400c030046c51819040070b0000e0b00d10030b0348490181441c2041c981d40e4141d03c03540d0061755441c5d4084030718424900300310356800d02c1200400009a020501c00080010910786200640600070044940c0b20304150400d0070112487d1f40c05800e1080341e50013025207a465201c240d03988001c00b42400181d405a15946d080034051101101c10251111000401003141c030380d400c5801010240d04450210041c84015506010004540d80d583c4a64001001c00a02082400800350380300d0240340c000b0030382e0742011651a401c15106400603031f60348041c940c81820080015401041c90000700c6140304040c440d5007445200f11459aa101c030000102101001d00075000102c03416800303006d444e42490004e0030315004118034014099042c1c241694841c21074800c800703581c10703034039240e0b4100f07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 223925863 1250 223924613 223924627
    0x612150f01170619110a030605190608130c080a08040f120c0306090503090d03020a0204141513140c1903090305030a1d24010f06050901050c0a0f20010c08 68
    0x244c0f100c8130000101d05844e450b010b50f0031182c42400040c000e484030340d40380400e40f2810b010801c50503001c00300d40d2042d116618403040148950001c40680c0003003e48445491084050030889440c7c0c90b80d42110b80217100d00b80f07000c8100f010001c0103004a6580f10342d604826070320303a54402e101d10038100c40600202d901c4401031020030060352200764070b144641c0c1203a2800742c101c000303e07001c410059419800343c1c11078042c850540c101402554a42015842180a54585184030440300407aa04e6050b018849840c2030b400350b010b503580302d01441d2929100d08696846d0200c020511179001070a40125840d00106c8048a1b40c0240210f07460142d00d034071085c0c291350f9480d449100404c000203000f010784000202e03201d400c070024003001c0e20620703c0d101070f820203013131043d86510500c8042e4402117040b80244001c1020a521405456004009280c556594014040103a02c0c08400c00000b900801c0074810040c01c2001c1e8000c0003000e010707113840548000503c140103580c1030080348409400300800300111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 223927113 1250 223925863 223925881
    0x4030807120504030b0f010e0601020705031c050c010e0a12020a0f170904050a151d0a15150306180903080c030c070807080c150c120612150f011706 65
    0x10711118645880ba042c00d40d00c0e1685054801e003500c03108100240d91005101d030300c0c0440062030f4420002c1c001000d4851500000c655540c14082c2242441e03907501380100d01d890f01c2401282d540b94007000080c4104071a081060b03481c0c8142000807a9054001c500c00490300d030010030b15601850304020701001491040d214241c0521290b44800b55040081008100c10f5031640700e200c3c06508039074800a1800510740041d10129410781098414013103810924050200303c1114035408201964041450030074003015151504003a00705989050001e00740019a5a06601400464280c61a007001c3d040c02520750200301c4480c0d900c003a0016180c00e0000d02902c50201c000c1d42c0004410a103185400141d46842100360800a822514144009480d0721401d0041020200014030603d0002c42400d10462200700c07032064810000320700015800083c0260b0310346045880e00c0400f01c040d220a90400360078000c40d0007045070002904449003002184c050060502c162500f48a02c00030b01090700da150340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 223928363 1250 223927113 223927133
    0x10b09160905041e0c020705091b03060d02010c020a0311090115020d230a0507060501050102120315040618021b0c150c0703020d08070c08061e06010210110d0b040204030807 76
    0x41d04942c1301501100c8030700440544100020324140358003901005081c041004984c1d00040c092002405404012240300181e00003107a8205108440d10410444188016903912155800c003940c452443c510000c14008541011170007040102c0e446d010740d81c3c0f241c0307000d034000000f03880300b0005034442040010028041d00c1d915180b20f59031000b00c040d14040465402c01588050900400204e012500100700941c0e80a100d0241c0824005007402d500940b010807003d00000b03118458071003481200202c42d448613070151015001904646400c511806030300c00203980245e210304e00316000644241c40c100701c0801c400070582c3c1b0003060700d8080301800400100c240c00010481c507080c091300034004010303030301c02a807000b2a91080c41d601c3d8841000d414101026030b00f640c00034a141d045142003150468070101203e00400700170003044450f403280380040346090b1140c4000600d4514188030003d111101c000a4080928640001c2c0400b0b640700003880103034029407000800c02d0700f06002000c005040b0480c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 223929613 1250 223928363 223928381
    0x120b040507080d0201020403060b0d0b0403050f09030613030e030a0c050d23070e1303080109270c0812040810050c13030f03090b1314060f040305010b0916090504 71
    0x42107588007515102c0240c1000100b441c4000581c4d03001500300b003000346a01400403800411501c44108041e19100c4024280c0300800040c01c001c0005400d002121222081e6600b0130740190448a8504d401586140d03d110307103a80a4010400510138a501403600059a6001c01e034058480740719546840f042c84403451072094200e07207040003d00c51600b1006035050f1007400040500051010916105501c0102080a8500c0c4812900d040c20640826004040c080c1182c03200f020000b1043c460024a20502c100910310300807400c2c04e10504010301070801e4004069a1442c1e0a9460080600303941c514940318504c5804070f80e0304081990704840d54103902c200c2e4011010007103945800d580e2805048a86095001220602092908107049c1644100241c01074010610503616044680800060030461446581201c2d80d010508101c1520740c10142c440c90103059038419221906c91404038041c0040007216402415100d0000d03030600c400d801700300c00d00d20301070700c4001406082030240009480904 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 223930863 1250 223929613 223929623
    0x711060309070503010e1006080d02071503020408060a0603062d1d120a030506220b0406170c0f04110d0507020319030c020c031b2b0804081501120b04 66
    0x1060010b0552006c0c0581552484094080c007640d2803c810100c04894040e0000401940200b01caa64155000200310341518803103066440e07440060340c4100e0103440750303802c061600d00504060001a0031a0341104c019a8400c038230510107250031182295041c00b4141d040411a6400b0402c10f0f00c0300e16030ba0045c1c03050107007196212035202034026200c0c545181d0428400c11000d000441010a55040c4113007074110304200d603031060240c00b4070f202d4010030312070241c0c441c10340d956401c28454540e00c5510907401824540242e50840c1d08034551710307480f5252620124042c1000c4a0030400d5840d162142c151118040090f050600443c8440d06c001000010600f90a5210030000e2807001146500e000c0041020f80c0d80c0031506240b080c03002070421a89000d071900a900c901e803a0450440c104050410401c425120307400320b070407921202d44904544028920500c0b1140e20b0744800d01c520302c0002c1040d039030030a0807103040d4015604041070740c0702c00348a203400c0035149102c0c0e41c001032145084503400a0241d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 223932113 1250 223930863 223930873
    0x1110703210c020a030e03120306101e05040503060c04050d0f03020c0301021305031e0d05180a060305330d0807050f0610120c0b03220c03030809030711060309 70
    0x6080c28100d800841042c0090780c05600c51400f0140d20820301c0c4c0141d90305502411401100c1406503046004c040c0030244103040ca4096042d000e489000140c0003202964006454921024809030072079015004d6980240101d20000f40d000c034505080700c0480b00094842d00401c44952540501d109408604400314050b00000c000241c0d401d0018040c800c841407071000d8028582802c2500c0c12650b940e0002e803100102e5404920640c000c41c0e40d0f1085c07840d07828034999480c10444403402c2594101211b680c0000c0c444004600c40c0d82c10ba00903449192401052022211410a9500034901041c0194441a8003103070481090908040d2648070502c5400010705010b2540d40c0c0d942811ba038604402c40540c001c5040010740c1c01010b80f4000102144075111f405510745881d8400700c1c4c0d40780d0055180c00781c4000040f0f800701c6203880340c1001c01001d010814000000e40e280115100700c140c0700a500081e000d40100e1002c100100171a0480340e4024030f000b540000c0303502404003c1d00020001e01640c010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 223933363 1250 223932113 223932167
    0xb1c05030f030709090506010f0f030b010905031c02010e07180f0f05040b0603010b1e09040c030c03060209010206010504060e070c03120905060108060a0501030c060e0a031e020a060201110703 84
    0x3903640554040c0d0f100e034039071144907400c000e0340c0821030728024211410011500f50207040c10380c01c40035406502d40180f070301148985070200165800c0c0465400b4035010302c51203c5070308001c80e5032881e09a078500180d009001d1143d40c0802d059856025000e41161031508102c07a08124a880d03200c0b50b400888018003180310301e440c2d003419089420440d03050390512801c508201e0b09190170300c0b0f1140700201c104c908040c4100440c00c00300802c1c101d0102e0314011000c06020030280b0843e0300c807800086501485208000d0348a01d002d00107900003940680c090b1169100214052425000c0c07803054481c5050507c1103640c40c007804560345040c00900754140801d100000001d010540100d0b450303540504010a4103501d084d910700d20b010002008000030514210040c000a0180e01140049818900d0824043c200b079800280342000c00b40d1008110203070607000c00c00300880580c80e04101c0e600031100588401da83e600140d0030703554500f05e01200c100e400c0003180000380c00b404900c0714180c4083e0706070700780030f41c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 223934613 1250 223933363 223933387
    0x206072604080705010c09230a0b07050a0b070e1f090b130f0f14120f0a0b01170604050601050d0c03060204143d021507080105010908010b1c0503 64
    0x14040d0340c1a100b1400c001a494280002400781c0034140c0b12074034250580514040c3d21400e01c00304040403c42a40d0b0042404420b585e51001c50b50192880b801d45590311161031802d180d841c3d00040046949114000004034514003458850b451000701401144000b000c0904141480584100c2c180500041c0f003c04507407223006002400061511041619502d03007402038031040d000b81580081d18928004400380003820722000a120010000d5a546866512140c03986050403000000d180f004d209540d80002031000c0d00380785074102c41508034200609404162180e8990714100c5024060b41d01903c010000780c18500261098075010341d06507105140c0303139a54030003a07038130a42c400a54400c10000d040c18524281c01c1c06011507880e0b503141c8910196502e81c0d48a4112624200507140f0142840d0004107402403021550000044181080350f2401005c0030300844002c0c086d0b540001e00140000c078800300c0502c01c1500c0b070000180320340002030740b4074000c00c0d00a000e03400c112103900045c800108814 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 223935863 1250 223934613 223934687
    0x507062307020c0a2402071a0a1706011d0f15031005060c070509040f02060d140703020c1c141204150b130b2403040c0f06020607 57
    0x10380a003030006041c1080000e2900450b40d80f00c2d88141241d2800f003020640050094000551010b00249280314820040c1c1c20302c2d003070341e120044a0000c58001e1180d119003c0080200b2811078451803800c401c8180e2000009800301c44050219000d504406c185081401622014940040c4103040d50310803c004101200100c1409040d4480d02205018031500300801c07003809000309440007800c10900c440100e5842c03496103c0c2d9806403220402080a001e004048100500d401510340d41c2d80d5070300d264404005002c20444070440c441c00e140800c0c0c000344280200c0b29280100c00061102d0b11350700590300c45070042003102d40140078100640d02440003111010340070b5a0b02291605007989072900341460440c0104c11060001403030464100010307664040c0b079041d400300c25000040d00e0120f101c08030344103240031240106245103c0944400c0c403c00314004510840c801c5084e2000c1034bc1c2c8440141c80a907d60040c0c4015802642c0000d00e094400c448a4030b811215003240240132a114100c88030741 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 223937113 1250 223935863 223935911
    0x40e0a06150b0306010206010311040609180b010906150e040f0912020708071520010615090b0304020105070b0a02090d0804032a09091a01090618090201050901050706 73
    0x98660109008003035601c0080c0004210b910011443e51510301d0000f921a0780c140030041200310104414112625240d01440c090808031030f003049000907105000114085001d030844100c0c0e0311070004900d28510b4050761084484800c554240d8075030510341581d8003250b4203503068220303607501e0303516070744050b0360140c2d48016002c1c030503403210045c0204000b070500b0500e8112617603950010781c041204440c0c25158081e00c01c000d181010702a0900041482d83c50f80c0d131a4521269030800b840404e690009980c3c1601d0003920f611554010303540c40d0882181d901040380c000c0d020440511001c000314030300c480320a5029541030300051908640c440011840c608a0006881880c40440c01340f080045442e5003541e40300401c1f652400c2e180c41429592403402c0760780070740c00c00c1c191103070b004004200b284600c09518039070340040b41c0c84640c0c45840d4030000300304920034901c09541280c083d61b8020400c2c4200600f039a0180c4d81d5a241c004100e0055503e40c0c8411011103003030790350340641d90481151001000318 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 223938363 1250 223937113 223937123
    0x515070213050f071e02030307030c020f01050106020f010c02010e150606040f03050c1003050420010212030a0207060b0d0c140d1221181b1a040503011406090411040e0a 74
    0x20fa420b010100501030114410340c403003801c18940c3d8201c42e16030000305603903124140c2d19010601c07021081c012402d20800f031070311100640c00d0000109606401181c00d40000305608020050510007107012400c1e42d4040b050a88203401109070b5008030f0b0040c816070750f40184c000d4841c0303203004ea4a600e606403d4a60342c2c000d44164010b180001d41a00d044150304003011203903d4103210905042d210001030282203240c680d901d020089aa2125034024011440840c440e00417007070f01c9141069000c0007075407044d00129001443c000540500340340800c110344406810111000718242049208101212003170b00c3e41d503002440e402020005404da06140f079810401c0d40d10710710320f4440080c6d2625060301c0010300c4450340c0d040c44c195495055501d640c010b1003540140b0003d04040c0032005084491102c0e4000149143c11014a041c24418110041044a030207030000c010a88c141c400d20a080308043e43d0440e40201243e000c1008a260300400718200a00104000790ba0869a403440d46800c1c065501168 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 223939613 1250 223938363 223938391
    0xb01150203041a0c060612062a070302070f06141209010212070216150509010302090609030106030c031505062805040609140f040305120901090b0a0207110406051507021305 76
    0x134584020b0000981005c4107440000395840c44004050b1519401440c4880034502c9281c418080e10703580342034140300049d8030600c0e47c0d20105810020f444100754014443d204640c141c00251079442200a203030f00d8416209014108408800e18888000780504181c08964080c04114001c000c40d09521707005a170541c004208007184c5040d49880017903a40d222400280c00880300d5004103030020100c0340d07608405d10380160745031a4800003901e180101041141c056103052004402c2024423005002603c3c00b900612400c4440281c020058940469020340c0201003004622901003d581401080184032140090b140707403a280410304441c4c03958440c00c0c0307191b100c8000c140c0c00c64000d8904c0b908400c0c071040c26641481c094401070f10902c40d06da00b24580039210b1300016900c12080d44114100c9600c19041282d0f41060585840607421058003590038804c08521050076140c284108801c480010303160a00c1048100702c016000d40020070142d8001491241c4080c62000c0340c8184c81c880c0d040036144003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 223940863 1250 223939613 223939627
    0x911072111011d0f0705030601090b06160b060306090d17040f05121c0902060901050936130b07030509010e0105090d08013606050d0302060708090a0b01150203041a 72
    0x40e1408100b0b104c82d9059801142003801652804244e85054848507400425600005004074515102d803074068480030081948040800000080741342c061681101252034940b5094aa262207440c02400c00d80840c9003100c10031074800342e6640143d0300c240907408000c528079aa48a05007000300045031540d030200000750070151440000001e1040401c050030401c0291042e0380410f13010710954000c0c5041c003c0104441c1c0140c0c0c0c40d103107091004844062689446003200000500381c0d13520034042490a00180300282c100d03000c44c1c0c0100c03445504007110101540b144c1c07000340c0003480050044800ca5403a521b42180310b9000340112402900400d00901c0340c480906001041414180c021102c00001802c001ea10171144144a0030484201e05050784804612800c810080003158881038101000f075294200703040d0017107141c610540ca241c5419200303a80c1e9408640e00c41503450070081615080303e0043c400c411100c03126054180042c01128603060715454000120351100200150141e170005100f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 223942113 1250 223940863 223940921
    0xf05010e0c1039080c010204230906010804060b04110d06060516030f050717180406050114070c0f0b1c0c0507020409020a031704091107211101 63
    0x120070035260502e0441d110f074091a82492810803205010107403075581c0401c16240055441d4110506640040307501e90703031400000c0c0c1e20301035001445040914105810300032120b400200c004800c2e4200200a0104c0f5916a001034844900c0500140e51a80d41c8818070342e96621184034402504078442c0b0b83c0c6482d90b0b401030303240c000c0e10f003e0b40002c000c0190911004860b03014120132035800715410700b42490582d42452044800c0d02608a0282141d80d161221909011510000709a010849650500354400501c103003c20b58506106150000300312044680050b070a072000342c50218130804010f480540c1e14000b201d0612a290403200c1c1000c3e0000352080385802481c03500c1401313059640300b4807251030b20500181c0f65004014000c2e00440e00c44e10108110368800188a001c0c5038007100c0260a0940c1c0b4140660701c3d08540907103680c0d189840a6000f403548100d0540746101d038062038000b03132506031074070f4030100310b4160802000380000c0c000c0f102c005d00801e0003600c1c03194040880c03040007001c0800c11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 223943363 1250 223942113 223942129
    0x3020906060a020601030b07210f2a030e010b0a03030e03190b0402061b010c05300a021315081e06100f0c020301020705012f0702010c0f05010e0c 64
    0x4510031042040b2003001a034000c103200d03044940040c111240ea50310750030266001004110000380d042c0241403120046119a40320a4604020207410080010344031428010070582048402440490098402c0303005c2c404d41240c803840705482d001007100100c400119082d50708036002200458a005820546ca040400011041c801c644108101111941e1030f02000740c58080e1019005001c001561004205503000801207629998001c00140d04101e0008015030818a0096480003011a40c40c3e1408940300c80281442d407041540b5200e510b5103200700b002917104121140b40b400d400d480009180440200304000b8440d40e0b20748407054079003854000c1030071842040710749061884006205441d00d60420058400102e41000c0300c400301011802d85640f8038104000f0340c50340c00050080c081142c19003107840440c03015800310300c0e040030301c904490030103406180340c0c01090700c24410b20003d036120341105130f0450b0190312407640c0700d40f1544a050946980401215003070380080c1e04c004980c20b00c104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 223944613 1250 223943363 223943371
    0x3040503060c0a141204060216020316050310021213020406080303070e090609090c01030902040b030d030204150201020c1207030314130309080f071214011409100603030f030c030908040b04030209 86
    0x1802c5d01d012014a211081c1250280024142da613001c01c00050f00101239080e1003005800600b10340c4140e11043d0050342e010968001c06002c1d0040615410310b02420b40291500e010f04501c1103401a42c0783c0388110a10241070a09076446505c9030800180510207000960003940d00307944045010a40e0010b01c2030481026110900070b10103103040000f4020f0204004801030024070b0045240581d074000180600035259002364180500c0c902c0320020b68060780100211a0002113040144d0b29a082c142e080b8003d03400754440640100c01500b41c42007822005045052080c1000038050a804540d074074819411030b600c0c0000902e140f400824550400c4203540203106242c02400c0c000e140981590301c454540c4107015403030041403015002c2002070b04200071544aa1002084544101b41d4804510b02c0141d40540490140800d5001120000e015400547c0e41507168010400d03200b1f13000310000c0c815412108100f50707540882400050090340288020006866501d40790780c1180104480e055010b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 223945863 1250 223944613 223944647
    0x2a0c0f0803040801142413020406050c061503060c251514061c050309040e16142b0203250b04080a060b2115090109050601090b0303040503060c0a 64
    0x1030400941a0083e18000704242c1006c140740038110752040070420b043c0c503201d80d2082250001c200454100e502002400009944000702c3d0400d481d411a005059980491855010781050000a100c0c001c840020503c03800001c19403910007080d0307400d100038449101d80032a66142100000f41c0361400074080c0941810700b80041c101541031007800100303039003c6404540300d41800800a0300600405100b0740d12001c50107041400b0f880103295100d41c86034401c07031040c00c0a0074081004140f0f81090144004080009030141e82c03c41c40019280d5505d03500c0021405c0e020303060071406401602c09224003500e0b41440e403001051550345810200312540d19130040d49200005000402c08039200041c1c1210303580e044100090011007200c04200d040c0184d995022140c00f41160394038842000003a04003c4e0030001c035029210b034484040da1070a81d1158040940154002c030018003542c0200e6000d0826003100400311303840c1c29a65004241045d00840301c42c00c2226000c03440c0c40703280b500203500c0c1d05185605 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 223947113 1250 223945863 223945901
    0xf0408070b0f01031406190c110106090b03010509031e070c0302030d020f0607050a020a06020d060f0b04030210030b1e1f02010b0a090b010903060506130204080f010c2a0c0f0803040801 81
    0x9207240c0700300b0005901d401f451141c0303400c0140540c50141382098125251075000740042502d40d040f10f800380cc0f490080500031362810000a10380348010099402c6050300005015000c5110b160096180d0090301c420340325400c0b00300c80040103a80412001c00865219000b8210f22002602030504200e0010003060500408200350f44415501203600901264030420042c2c494034045154002001f10350003c000d5650126404030b003811717a0b000540f089038800c5440fa181e00b246a803089045c0c1c0d403d0b041141d0030880c0309a100517001d44c07512072440b4916002d00121915403507014a00c0480800c01406000b6035034641c81440030b07041c8003680c43d000d8480d81401b40219207003231000a00c0c184d518400075000d01e60b103038003240540c0d0b00c0c80344159032280d6103d025034607152564642030300e0705d03e800740e125888d40ca0b0544501002d40185822a1062002035045140885100a214215400e100d044030b44030220f040218110611901520117458030b10011031b00d40741090105421120f00d11006600f0101c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 223948363 1250 223947113 223947121
    0x1209070504050601050405010c0519050f070902072f28050603010806010b0c010b0a03060e0d030b03070510030f0615021009120f05090d1b0b04030b0f0408070b0f01031406 75
    0x94112407c942c02032904200b01082401c24508090441c0c03203104a003070b1160048801e0010009180c0c0407060000142d0315040d80d507030004822446100720080c20101c0c02401c40e20700141c000e41004107078401402081f50b0700d00340c500242c2d03030029041c00e426003008081c4c400784501c4040103602001d04019a030081c910350401d4442c1e035642c2014840c6078566140015880b60010007174111a20024000d014000c00540380c0c542580900f1128204190601c20140c0b4520010702c0781c044c45401031800703005010300908140a10500755400000d410a068aa158440340c0700001c3c42400000c14406e50f04180900c14480c1c02400c1c40040b80b18a5603480c14481c0010119052030754410388901942000031542d002d07404180c5840c00fa440900c0d621161609144003407001201000140946c9003d41d5510075454241b0700d04103003d10f00014286090002c0001c002c10621260a41c206000e036010505004043d030f54445c240d0000c840c40814030340c00034010010052262a02d400910046002e01007c1c03074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 223949613 1250 223948363 223948367
    0xb0901110f0d023109140403090b090418050d0201181a06120f010b011b030203041206020708180f04060302180a020c0f01051806060130021209070504050601 69
    0x1400303514010156001400107502408142c030304e509012030440a940541c0b0000c45244440719070b02c24140c02d14204000303048801070760488a8440d907899240d44d0320490800000704080e401501c3c403907800c1991b0700030000003d001845c0d1400f209103d40001c01301c1011400000f801d41e0b0b0420464003c8101d244280320004005180041d0400303d1030341c100220f1390381c060014200b0b00e040d981c160340c03600074802400c00c0c015064001d0b007034907003082c0caa1100740c804c10340704c00d00b12080d00c0c1e0010300103800900051000311101c00f03910f9550703030003400050708146480d15108115070045141c0c510250b80303258034030707076a0602000c42c2d02e940c98212001c019461a54001c02c1c10003030040c040b95401034800c000591390311540e80c16a46190b400c002111444c1c1d441c040c0d0303d4000c2c041902d0305070804110f4001b0b06001c0e0030005060740724280c10394445031a064208080c3c2071b031400d60054900404890f07030039102075007280e00c094109102c408540380100c1c105010054202a240d8000c0c3e8001c600340007c100c503990b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 223950863 1250 223949613 223949617
    0x121511090a030f0f0204050703200412110f030f070602070e10030f1a09010e12030106141309020a050306120c0306161107030507060206010e07080103021003020d090b0901110f 77
    0x81e0031418500c20b00300d00e40762139400300c0c07000ca800035070161508051054041d0725510400304048103080d000e92178288008200d070540503610540410744152000300c40010401c0c0c60302c0005100251024230118140000039042c100c01c802e04402d164001c000070018a641001450010a5000120903041c1031400021499009038080076282a1025070581b0410010b486c03061941c4540c10f078a04000c3c1482d0352114064140300c1040038039442801c490890321101b500460f41202c2c2d0588581030070b008500342c03228044d006080084484040c0c49000103829407580000c16000005540300c5030359182c803400300030f00c026400d0142251a0300c41c040c4904144ca00003a100e8012502c0711a24510800e81d45040703558039016031300d4203801d004040c000030805c03a00244540131b03074440e03400741c48290381ca030200050481d20440795480010503a400400250501c06043c80c13030035409290142c41c0066821114041e1104007100311001c1d501d180401030007407028070031501e01a00e921962458048140b000312028 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 223952113 1250 223950863 223950869
    0x207060309030c150c032301150507080304110a09020c12031b1303030e091b0721110d1107030b060f03070b09040c0c0302030a110106121511090a 64
    0x300d980c07908036406050140f09115041640324000e414600305401c8204007902940d0b0b080c3c03000c41e0070845020780620700401580c2c14100d2401c00c82206a10b080d08240040900e42565020b011040181101080b0305c0c0380294070881c000e40f803250020b0340d16000e001182c0a940d2081503440d106002d108010340000c20b0341e00c00082922451601e9840d40702654180da801c07400c102c05030309400145041320003017410300c0000b100d000c0e407150386215031030700d09102c8030b0300040350b02045c0311003410700c141100143d44004d44441401400f0078405c00d0180c00c0401b03008000d078240e41022954107460400f174524200801444031600f031403c019072078885a4190fa6131542804014920404100000d9030340d141e0300c400321a0654018120380003290780c1c031180b050b581e001c032101900960500d2850040326000b90340000196074554025460700301d045100b1200304c0e21025030500c1954031260f0000ea03180e505e00b03403030251500a009102400c48011003000072030b4000d0b4502015040284805013003035a80791800d90403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 223953363 1250 223952113 223952117
    0x201180503030d1d0106030b100b0906030c0a03090c1410030e0712050f030304080307110111160309090515040e34030506010605031f14061602031c1e020706 69
    0x30410b9100c1c4004c10050b03d40d00c002e10075843e0500000500c02080c80e42406103a00c1248080e0007615010000072920480c0641600400700f00013140a21542800514000e156450006113800143c2e640c02c045803c958060070607035201122054a83c0f51542d61036200d0007440c2400c1103218600b08413151200f155209082c10300c40b14403206018031105210725080500c203102600d640386084c0c50041203540042d140000014a25841012110414818064480c807254489802c105c41e0003d4411718100416048080146442c80083d1520b5640107450041c0c154414203007046d0b15190500c8111524034021a00940c000808603418102c024100d0840560083d1640000c04410781d0400e8001d2580c0d10090851150000008007554030201560045200014024585084044801360310348540510000b80c0d01d45900d4040b50300d440e5004101ca1814075160b031301c5007000ca4000905000724580030b0b65032400301141105a980d0300c241440107115005a0300c0b501d400583c4402540d90b50903002d4401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 223954613 1250 223953363 223953371
    0xe15091006031d0f070618050102070306050601030b1921020f06070201020a0c0803030604060b0315120c03240f0103050c0d0809091509010f050915180702030301030201180503030d 79
    0x66280084003446422000c14000c48045404c00710407155207654070301c14480018090a603139410f800112204200b1220164010200c4a06640350b500007000b010b0705084c141555007100301c88580303899845040300d00e2082d2241c48281d01e410580c10341c1d00c4000c05043e00c40004500e1020060f501c40303108400d14071040da401c40e141c038003910050340780c80d02800c0c5c0074001d86440c520014030280e00100540c4602c80980c1c0c00e10030203035140e066250a01040e1000360503006000261a903604044400c0f40d08413842808585c4010603034004642066050f041c103420301c2e602d1186807070a00c1010060160030030358103440f40b051074bc50b50700c4007a25402244c403d1803282510070040300500810701c0590702400700081010440307042c000303044007200700c190706054060f00d008400080c40403140d42c5900111880541a2034203541e69000d2050420f1801603c0781e44803581e90031105d030917240d00803850722500c1d90360000d5940354110f00014202540b884030445828240c40320900194501205070b41c01c14100c00345c045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 223955863 1250 223954613 223954631
    0x100509010b03060103110a060c0b1501050d060605070b06100f03091a090d020609010e0a03050d020d150e0c091e0d0b092d0a030c1109010e1509100603 66
    0x15024040d41e4001e50b905114010000c02440840f000701e101c903040803074041070358980d0b0300030903a01c445980c40d000c1c141014400c0000c0c0404582281e0b40180841498010b10301070001480c40704983c030300d4015400080c0085814420000c001c04202c0e0800c01c05c80340f6801c0701400910060140c11a800320b4002c02d515080d00d4810821508083c100d0515007503145005894025446a40c071441c0090301c600510440d40070a041940600c60004503180e00d8000d084840242e4805541c0d03540640b100e500b40b1313542000301c01c2d0500b582d449903510020243d40715003032081c07809251004004025010040c410301c100680304043e5600402c0112514040d1203011076095810001200400031040c060151840714003000002000498101c0100400450751b1f2003000b00d000039a1048801c40203c043d05500c103840348400709014540d9603a41c030341b0800295604402d0307100810320026003a402015000d482c88203000c0a2030755040c03c844554015948000345190800104507203e119101d601d01307066a0342c00319 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 223957113 1250 223955863 223955881
    0xa080a11011802271b13091b0905010801090902030f0a050c030f01090b0402010810170c010f020105041113090204150501031d0304060f0c060c0207050f010c02031005 73
    0x300103805a03000800c42d42c000c28a803010040c40154049214040c40c0607426201500b080070078050351460002007050351340f0800301031714192450741c0c66103030000107112284c0f815010750a2100030f4400000f011510b01070401c4211154004030b9995824045142c1c000d1150742d1348043e0141c119501e800d40418589081c1c004a81088103082c80349604e07000e079000c2203080c40b10028415204071026800c807041c25021524003400c07104505e0008210400780f0010601544c851303180d241d002801050150103159503401c01d54610041c0000f00c00454000100015107580c1040c40359080d07001c5400244080e291031355550175607985060000788100144100c5800c039640c980d01c00d400455000e4401c101c8509074503068800c603405403280c1800a82022000100d800c084410881e00c100d2102c0207504007801c1607801d0307980340c021221080410035070036841404a2000d004a9080070685e030040c1080500300001e0201d1301e1005003c4505204104241100507100028400914000c00900003559203501c0340c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 223958363 1250 223957113 223957127
    0xd020304150203040609031202040506041202030114070c02041109010e10110d0806090a0606080403050703020c100807081602030d0b061e030906061905011d041b020c120a080a 77
    0x41d00c0312184003004000030050107501006041c1c0c0039440c1c0b4042c50a02c020040240c1c0314600605410620911080100708100c1260700102480100007254040001a260075244c804031084400981d08444040c01c0d401e251103810041f401d081c4005190407da400041e00094503021118003501c801284025410f00c50340c81003010301c080b00241e540c001d002210003071642e08103580840c443c01440b80822440d9800e4480c0c0f0084030320070b0b00e501c48160b449032019601a00441c500b5800d50280d280808910755074000110348050030f41e1613803046402d000400400040c401400280c50310300c05d59540d81069000010f680c801d010410340468000c0f10000400c20600803400d43ca0348400044990180003020103010314480c092513003c8800079074400c4204000990900d100b640c245090700c07014801c1c2c1d481420240c00d8020a2103c080ba040c209002080481d10303c020114108440700002050382030b418000403140c0a8119039007042203100d0306900c1d0325100503400003030010b1030024040c0c900710f00440ca = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 223959613 1250 223958363 223958393
    0x809100c05070606140d0f050304120b040b070f0905060f0c0d0c05390f1f0e01090302100509030712030906200d0e0301090f120e150d020304 62
    0x29040c440c0008080019045030421801110400e007402c0c0f0102d140f0b50300076003400400c40300070308030003a848a03a1107290081200d5602651a400204808030b1621200c0f5804404540304020007031262070309081030000080054981800c104100060480c0680d0000c0302d9816544110340f10361f518001c1444c60b607064401c1c50700001c041d0003481d2444800f19049030031020310300e0003002650502010f8030304402035400811188002c0800c80400f03a040c0f114800c054810b040c4028160307184070f00d6a00c0020724042503038803518a66140c00d401d500d84456006c00310b030080c42003e090121401d41543d00145112140f6840c03001000000304009100d6681005010010042e001401d44000c0c16030900802d6603000307000d2240070032000340030500c06e200b40c1c43c03e098881d02c584015100c42c140c052412105440a401402d81c50b42d240d40d0050045a050310350701c0a580d03c03c0c1158240e100c480c0c44050101d01e42c2a801d2403041d00004081c02100a081048900c1824030042c0141d49958900e0242c22201100c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 223960863 1250 223959613 223959643
    0x30201030509061023220c050c030f1606051503071a0f090f090103060510050a15080a060504230f040b04120c0c0e07030f0b0303040317281b11010809 66
    0x2080d8184d03040d031b011501080700c0c0b041c003e052000702ea04840c26030b400d10400011808075802082058510724102018200c1c0c29107400d0b03203806030461520749000765171083d104c20001440090510b03509240c100310034801010595240e031701c121900545c801460141c42444940e0b1070b000102d8007019a03a0050000605034000c20003403071561242003200c000d000498106102c80c400d000081028501004003030100c070500780f00380300e203d8082d030710817585014081d203002c03400c50320760320003281c150343d54001ea04482c6034031311010307036050016500074405800140c105003a003070001c400c2c0030208800f180c000b0b81c07040e0000c403e040541c1c040c0400315400c1d590303464017411440100401080440000c80582d0143c1070342d5801b444245030444044040321451620743e603250384100f00c20000110990042032188048240e003030708000210300c0240800744240501d65800204000c0c40015680000382405680b4160700e01c0d02580d4001c0e900c42c032540c800c01440e981403006050000380003004c10440751209035400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 223962113 1250 223960863 223960879
    0xe1003150608030a120e0c0603040210021002180f0402070f020d150c03020703080f070f2a08040f1a0901110f0a060605030c0111071208040816030201030509061023 72
    0x5000045c0960107060040e011681040807006001000284200809000a000e90315548565080003c08120920040158020040703000440c103000d10250019000030400070100c2a49881008413407030340d02118601c260720511050022985619105000b15030540d81030366205218104200220800b40e0006013071410020120036280d07164000d000300d01c4c0f081c1c0350f20101e504c0d040c080c0a01d54204503000c0d0009a00c1c12000e007000e900c9080112000c8001c24803000c0001d01d162121408043e10940c00c3c0c40e58500000c040140142e0b4200007002010340b01350700c104900c981450058944a456001810032668480010441900307102d01c094440f07254084a2042a0910341400500400d1007514801d00840d0611442940144601c0240201260161046c1c0d82400b2141000d80d045401c0ad45070640140408580340208005e400d180034411031440c03010070f24500c0010140c650003003050500360820424802c00242d036901107000d07220800f00c5080d03100c0b41460352400c120a140b01166000c001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 223963363 1250 223962113 223962127
    0x50f0604020906040308070309050f060304051c0311070507170d120c091e050f0d0305030103060e070305030408030d180210030903111e01140603070b0c011d010c0201060e100315060803 81
    0x20039202704403003085da83c80b0b00e29942c440c10881e807070004440c040d0141d0000d40c480c3c003501e6001c00004c40e807520303103050004c1d207108607030304180301a08400c00c01c640c80d50144200780240e210503142c1a803202c004400a14040c810384038010035030780100d85200d0030175440720344407031109000e0107130640642030740e18068a50607134003050070314103509070b00c075150280c41c0b000343d1600a400c080c01d04140d0b09030141c6a45145074a141d5400004085450492445008082003c00020742c03d100400003440a00e005584900d2800280001c0340d1100032114030b1803010030600b00050300e4050710142010014100050303250440d0a0580e20340c40210144c2e5064041c218400c101d0701c60310241d031142200420002c10421900c2d8400c01308007001928080d52682c8072400c100004220140140601c0c0502c07000894040200080c48450000400101140c3e945440080c1400b0364244135160007072615030030710301d082c3c201954058815078544c040a800c0e1030b16200b1030038141c00140c004600610011007225a40c4103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 223964613 1250 223963363 223963367
    0x13030f030203101220030d051602060f0307050301082506030b12010c051305040e03070212030c0106091a0406060f1805060406090509011205030405010c020d170c01060603050f06040209060403080703 87
    0x1210401d40500d641060f50050342410001f464000d41840c5448140c41c081d0095031283d1a8100307000200d901500401c5208129074441000d940240080e4580030780325414a03004604285001b805401d402c0d51102103240b43c10f290401c11400c44500b800c0000342c012208000c84d2840b180703036002c0d40c0e40f5030801c0020424a9071007001803200b030142d21041620a85c80d503040000f0340749403002c1140c0a50042c413442c00580751030b80d0148540700940b8102ca1034990110f900b9800d43e500f07580400c070010f594108030b50a90364001e1070403180035404c44040148500f0540082c00a0544008400400c115202002d50081d540702403040580b0005000d55100c641e2850000c0c8040000d014031800b0701196000013404800da04aa034802c07a40c41000f4508144c1810b00445d606441c1c1c0100343d1313210001d140210085851080403800e041080e00c08955030307200c0900042c0c25600140e02c40c904061501c000c004407030b40029140c5070001e80495001da81c5030300f40700010300c5501464001402002000900340101a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 223965863 1250 223964613 223964633
    0xc02031209120f1606180e090a0c031101030506010e090f06010c0c0e0109063002062502030d0203180f041401060503060310051302010c050102040b0409050f13030f0302031012 77
    0x3001300c6071104000d5107444049a0500c10741803c4440340032807403001c0c0200703829101203076848030515003168000c0d1013036103403400c1d40341c0e00b81d20079a00700340c081b4101a02c5581c180195607001c0001c0c01e020307451605c2100070407112000100f10004100105000c01c80c0b5a01c5040300c000c0d05d980001d24402d0392520741c0404d02400e002841840210b0f4a000340004a2203140c0444014460030072900440d091700180c10070080c2c0140301c00480e8402c1d02001090600706034a500d4110307101031381a418503a1540f52061500e002452205001903600a0007000d4619181000d522000d1750247c8450701c079450910003060280c0340d83c20440b0905000c2c10000b1403015030120165100721021412181c400c0074a500c0d83c03048030010b80e480341108113107900c02e801550040303e080603414030074030006142555400e000011a00315801940d025510740f028000c4102c000c0c031035580c00006100a46444500941d00a4500d00140003c40141600440082c00550780d48031351000800218941c02c481540e1460608444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 223967113 1250 223965863 223965883
    0xa1d010b030105010f03020109090b3c040203010522090203011b02070f03030807030c020c0301050a0c030b100f0c050709050c0a081e01173301060c02031209120f 71
    0x10358a00303c000142c502800d000f160450340c042c3c6800090a0808200c0f00240c107414640301d810181a43c480c022802000054241d01241d203001095284e02044050081790044002240f250380140010b10003660b0320926a074500f580700b500320b022950992500d03406002844070180d0f06500c1d04045502c503000354070070410b17244200c1d400c3c3c8501036100c41802c1001209400040d00058154000910950003580988046c0c0000d0040b608120141000613080d18801c6455a00d560344400781e80484a400d8001c00755104801c03145c12070011000c100041c07805800c554600304015015010505020302486050064007210701c003417100c0e1a081060360b203141e01680c050f400084101d00003551040c1d040d4150803409002c0380640e0b66613403074040651030055054806488a008a031001c8480c004000207803440c6051096038000c0e80800501604541d6505134005c0044c000c03015903000059402207180d01ca1903500034131861b103030300407a004a02d50941e10583c141d10381c41054000c001a21001a200e124 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 223968363 1250 223967113 223967119
    0x50106060912031d0f130209010e0604080a020913080406050301150c050a14070b0c06041a0c030601050d110a02010f0f060305120d021c0b190311090a1d010b 69
    0x146544038582c0004409140001e0000b07042e2200f150304a0622003030003d640c500041c000141c40343d0714030000d1003d103452000c07403544941c0007640381c1d1596001138160030080c1c01141d0182c102450082410b88650003000001c0c8204c0c03081001402c1615030315060b07804940c100340060745880d25a40c0161640c0d000380100c4070003800305944038148504c01e81514441c690304c00007808600056271369000c03011304102c0010003680180580480c0303031100e041c0074100d0261280018082401c040c1840003200c00c0c60b00043e210020034000b000580c08201c0e0850f50004000c2c0780c4240e650a03220f03a000000c0a0002c5002481000086c0f0342402d00e9054200c5010090004402c10003454003401d14011103007244401041034000701410f509003410280900803c8041d8403001d890101c4504100002403451034064841580d144115140350400700188080c81d1262101003c00c641180c4a411202c0d207856a00b500c150404800150051035540102006070405001130a01ca044070b034080b8082c0400806140c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 223969613 1250 223968363 223968377
    0x170a06150c1511070b06060d02072303040803031501020705060c062e05040f0e01060b03161805040b010e03031605060c040303200c030a0305031905060a0501030e01060902040305010606 81
    0x10010000c3e125803440030703034554a424645450f80d030f2250300424004104a50041080c8880304c1c6032841400280b28141c840c0b0609030039020b4032a0781e00003101c00c0310b04403049039009102c1800040d10020440e0b8120108509001008141000403450f12143d0f8100c1c540005022421006940d07002030717600c2c0166290884030001c09681c0344000300440d0f080b03c100b440e18081000c108032604151b1700142d0f4078107052502241000088282d1800d5421941c17040500842c0001080502ca900b043d52901d07030446460700c40c0e40d50700c0100c010032420550780145486640e0b20260f0340c200340c1c0211000203081c0c602506030b90311000480203182c900800440141c984c9d009100024500b141b031303201210107030f036495107a9070003c02d900310038008802404c02c1d40c50317502c0c851041448180d03641005041c81030b910964529503a490404000780a148810030348207039460070315050041e65543c100c490b0341136502c02c0c80c1c0050094003042c042d90140101c4d03840401201d200180101c24814190444c0382a12040d8807896 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 223970863 1250 223969613 223969643
    0x9080d030c050307050a090807060f110d0212160507080106050a0501030b0a060503041703041101171504110d0603050703120219120504090212010e070f170a06150c 72
    0x15090725001944080001c1040000408050244e00078200603000761401c0c010190302e45081603e051041e812280108419840711000c003540304100104d62030480e000b030b00b8001c150003400303540d680c1094070500041001045000d51006402c88000035150800102c1e460701d542c44450310300805450040070300170301003001d01080301d50090040d11400e0070040c08007201e0a2400340c040b281a007000e001101c1142c006441c4070180078003500034500aa0003100d5a446500340c01d000901841700400c9848109001745013044003545029800b200d140c0401c0c2c5000c542d00b1401101d25502d489619240b401d200e00e8032101100703001d40082d000003501e12420711000910400072003641d0310702d103194078103c00c014244110303800288499075a208000c0c45042c41418580c44003051400c0e600942d013518140c0303100c080100203c01c0b44010150300300140d4203000c1219442108002c0140b20f905014000d40946c2d00c1c0855000189a8000320050102542e000700c00c03005507400a105880c03001050300c0449080c0d05503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 223972113 1250 223970863 223970867
    0x2010c080c0316142a0d02060703020d120606050a030c0224041703060d080705100f02030f062202160b1006170c09221505130203090a140c1009080d 65
    0x40400240745d1004206008100c440c030280d0f01e8852400f694101050b0081c600050f02e441c0e0150568078400d4006d4000ca04c030440c001040031000d2858030806a080010811078290024100c0f840304043c1c2c0740100d140008003401760300e820719a10036500300a80711800786605000001e4090b000ba4403408881c0000c49443c07510005500081d15400d07840b8002c1192000001c0e02d8000819881d88241c0c103903074000e40c00800940489400e04200796440360000100050180c080440030b900a10413640302e10041c0181c2d25442c0480d00081d03442c6040c036400103001e1642034070b281110f90f106501c40c40c10b85051401010100000340240302e142c0100e20600075405040075108012440340c680c08000600b4840000e007008051b5a004085081240c04a100320000c60344a000e2004290181d05c540210507140c01c0911040d600d000404c00840c03841402800803407031000c240d11118541000c20003141c131600004190901c100c0001c2c01da4010084c4071801d880a070440000401c80d0700324400d45104010140742 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 223973363 1250 223972113 223972123
    0x30f0114090c0a05010c1505070509010e18011818050d020d02010e1504060e0604060b01020709023a0507080403110309010c1b0b1308060105180402010c080c031614 72
    0x40241c1c031042c0700b201030044d0b52081404280d6036016040c2c1c4242c020903090707604200d9109442c0040054400a18040d030341d40c00600842c0548803c2c2d0345108905184403503c1c0301d0744e00601801c003401c256000c40854840b81034001410380300c107214030310481e06498980039a55005000000015000d401d100b48140340c018850303e0b1110408101921000e407108030806c0740200300034001c40f40c41c3da07a40c0e0701c1d420311102041344a216a124100015007000000006490415194010000703d40100700c1046894903015001f044400481c10900d2000e45032120712510720343c0000300000c40703490700c001c1104455120340c2c4503005601a444440e000b0803405840c1e038980c8980c031740080c0030a003580841c80000e2880f0709000c0000010f0b0002d00f2040da15030b00c0c1d0a034607071300c542144041c200e4645010f11071444180600b42c010082125605000303215070b41344040a0400800190601151100c3c40080c4102241250002c2e1045000e89030b9490154402403581070306244143c03000b01090302c0a041c00100050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 223974613 1250 223973363 223973383
    0x90a0b1e040b0f030421080106180803041206091a0604110307020c091b070c08010c111002070c0f0e07080106030b010e0f12010603080d0c021501060e010905030f011409 74
    0x30500b450240410f503100c01c281e0025000326a8442e0132002002064821990122002d0142c0d0b1404055450601d00402005642ca042c01545202107800c000301100003088030219101c140d608168500241400c0d0001c2103d540041c2018454691814000205900b114840d0000f11810030040b201c00e071940d610347c0800c0301c0c0c0314007580c80100c4004040c40c180b800720b580140072003001000900d0f0040c04900e907400c840e00c03c4544600148050000350020b00078003940c10868508a11041562000b02d0f5a81443c80030080d09694002916014006440c40040280159500040e00f5035035900d2a9601044c003140d0010024940c240013181551207801511503000c416926251280c1141c02045141e5100e0b9a060354010307011502c2240050b070170302400000f18060b08010f900c0708011400300050b158803042050854002014400e45034480385c071074505640141ca04840100c0c460300058070968219007090754907120b104507002811505411000006640150b41c1c231a5881c2c3d2100c039a52490962 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 223975863 1250 223974613 223974629
    0x6060206040318060c2a09020c0606030a0804030201050f0d110c101109042f0a021c1706061b03090a09020f040603052806031415010e0c090a0b1e04 65
    0x43c4e0910081a040700121040f9480c0c5511b0004014202000da0311180c42035015803079864010070800400b0700280205a40000260040c00801c5ca555444082c0d030710a5010083c1400000304001640c62048000d5030141880b03c136080015141114459030316800054140720709201c0d14601c03500803400d80c0217901120700c14101d0141040303021030402010703128014010480c00c20200000c40d041404e00802032603485406002640c900e04a48028188035008980c51680004604000f400c2580051040480745d1110302403602d81d200d050005440d8401c0c0c130381c07544807c04c151003a150214404001840200c0044460b061607591301c210301c0d801e030702030300c08002501d00062000300000d9009c6d400c200c1d0b000d5105609560a800400300c14088440042d55a441c1c2c41d5076120f0900c00c22505210707a01c1784042110080c1034a40940010600c4098140210350166038004040362031407000005680700d000c00240f40300c0e501034079490241c86982003a0300844100888108a9030f14110074002c0780c00b961562 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 223977113 1250 223975863 223975877
    0x807031710030210021926030a02040e010609060c031b150515010905061b1e10060504022a031c051005010e0a140a1203050909090706300606020604031806 68
    0x15140e500c04001007100012003c2003840c0909041f0301d04400551041a1010006849508010441059140c16080141401040203003484245c0c1c1003d1020149035052030151690385600000c500021210580140f81c900020080c0402c001207400c05482103000e0302950b91503000100c01107401c450b561140e6500090104040032800c80c5d160710354150440304a048416102e00301d81d5251503a900300c03454001d1508213000d2841ea540076402054020b040488065040c20410340a8902e205001101203020280c1c0d50320840d10180b00b40185c56040100003005811040705800210180000321140891003500480114456001c5e0b80350040c06600071704003d03e0707a41881c107002002585041c400782d000300300c454001070301d084030050000514401d41c2e90343e0703c41503a6803d000a10b10003400f841d201d07420a42061004aa11061502490001c41d6801000e2400000e0b580c440b05000e4141c404400c1c02d0503c0401c0c11900040c0c1c40d07005508ca80d42d09000207480d404282e0b0190b105005180004140d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 223978363 1250 223977113 223977163
    0x30806013e010b030609030c060a060501050d0c020a081908010f0803040308030709090912020c0a0302090a0b13061203090e07021e1009120908031204080703171003021002 75
    0x1842035403a140681d07800000404040341d20000b460100c003100c4200342c584c170002d030118000f01c003802443e0300289006400e000780d0b424000041c00d44d015000710b401c0c216980d0032098202910800a104800f40c103d1360159582a408009200d20300f61a0710600215450400000d0045100302c1950308848102000d1030600d030171a0b547d101c01e075001410801c100400f074100424480118410000c81a1103a184020103030341901c806420040200c05062156010302c4c010005030b1200e00d80741d40d00c07004035000095010000c10025405112101c0e200c40e0f0b8601c0c00e00c0108814108001d001c1c04c450003611003400070781c1d5640381c0f602129403c440b810010b800c0344000381c100b40c0d8040c40b0090346181100943d009504400115011034411a5007079404541d01d003600311a02c5d4104c1003460140c061000a1031800040b6698001d50b9880604000c0c40181d00007404000e16105000c000901e8a0400b2403000a00b401d0304a0f0b22510104e010580c8a00442644984420700010303107440d0304408441e01d040641c0d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 223979613 1250 223978363 223978457
    0x10b01050304151d060901020a17060f04020a0c140d020f19031d0303121f030f0809010908062508070c1b090e10150614030606070f03080601 62
    0x900e60344c80003203d8440c0b40600c4200d44050003403501c0b40c1d0b00130b0001a292039002e02c005241003421240c030540c111540b000e00210b40c03200d2980802100090b540940d0350385500d0320445440720281400b80c00310f10045001140c0f03820100360450030404a03402c40307082e005000c05058542c804840a4581505807580b0701001900480441240d20394000c03e031090103170100c01290541d84440c00910081d14041c0411840904c2568141442581d00312048111800c642d81c24100100184010741003960104100405a201c3c1081501030a1080103485144c20616280010030030b0300c10740703090b00b0a002e20f1140c510900c969030710752182c0096940d070381000102e84c0700e20b503603070700810084010180844004070b81001c4a001d0035404002d8140240384c440140d1465100301c03802034820580060500004104c41540240b46050f00f109500300c0c01d40d03a48656002500c42c3c4640d0301c0080c160220111440107048e04120042d02c140b00030b8031032045003210480764011034507040c1d65080788140743c0305102d03071010307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 223980863 1250 223979613 223979621
    0x5100e010507061a090a05040303051f06110a0c06020d03061d01030b090a12091406070c060809030409060b1b0f0601060e0103090c0806010f060815060a2708010b0105030415 76
    0x2000031140b45040385009010540e0044106d45d0490805c0e20340091004065061007240d50003040392081280310f89002c10f529040200a114240402000141400809400f030000c0c00c00d4950000075841e01e02d0382d44c04040c2d100c417801c04070340002c82c0c0340040000fa089001d031100582c5414174041c100c060380c00d503655280290b101801c90500342c4501b41c610130014441c4000c3c80034400c0d150b201c050b80d81d07160144100d045030090345040e0041c5014040301c0001403130f5030b583c3d400b52111410009200da4070061054610f02550b8040d4a1003420240700040b101ca00320018924400506c215542e0072020100d050341d00d681c485021140c0f40e1145004201080c82044095600041450082500105601c030003048403030070b8004400d5500003600403c481031071000000018003141c10300260038940040420b4082d12000f444a008203000213480c4060362186000301040b003040828118200068880450b50340054041c0380d0680d03185c059480b2240d0b0080082d280f00e954806251840c03c801c9154000180c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 223982113 1250 223980863 223980881
    0x907320114070c0f081e07260703061e020c0a060b010912060203160c0b0705070f060c030b0a080106080c0d020406050d03030209030c040504020906012307080405100e01050706 77
    0x101000740031a4000404490f030082c01881d1001545a080303040c01189410310b04040d10208250009081c542e0b8500303000710b004411034008091004500070180c085409180320024010018003030000d000c402c0111a60140180c10115001040100742d282100c60482c4030729402c00d405607000c3c820100020300c054126180d0081d06140c002d84145d179484c200c0b0300b10300b4040da044468a4000c03040050a501055059015a842c3d00d0480b0308a1010388441c00c841d0400782c01c01d8100440041c3c0c0600384000404040c08850b80302204000700125403000030000c140104080748103006904001a24840500078401910900006040001d6a034000c203c0d0342001e203501281c00c140c44100015070b50340d0f600c9018141074081d403030150f0b50364401001c05003002c0c031610143c3d01c503510706030506c0b0141c2c83d15000c03940e201c2d200b0308102181d107108140e440403070301050511800c2c02c03200042c144c080140170405001203d1064807508180584070106543c140c0e00d2091042c0066020f000010110305150015908 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 223983363 1250 223982113 223982147
    0x16050715060f0b0d0c0c170307050f0c0a050f0f070b1e070b0f090118150f0c0512010f061e050403051b0f01021515040605060309073201 60
    0xa942e551440c0c030034941c4590004420b400c2c049400240b00e48a4094030484035124a000303059100c81c3c1e41d4140c6408105005001c0c803645c00300008211a0040c01120080c402d503415180d124103074980c0155031401c0b400401c94890164910f2240e2488002410710b1550701c0c0b00001d80000c50500c040310141d5041035294141805070040c4001e00c08001c000100509401401301100d0b620b402c5000100800c4040c0c4035041c56858504801103103802502c1c2c048c0c06951145404107400030005100303001e401e54004150320b03149840341880c10755420000902d07203c0c1c4c00c1e00c4030300d4085c3ea940c81031030340c2e00c4c0c0b030f900c5840c02240800d88401009844c001601d40c803125641891414240c90341c0740c0c80c0c50284403c4030303151966850901c04c121803070f000501d5070300140248020507a0300300c0240102021100030301300c07240078030403100b10301c00320350b030725081180030f4000540f030b050f00d901c1e00007151540c1b0842841503101e00a901c900c002c400801c400201003001c9124900b10b60b80000070001110b0300f5000c2051920 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 223984613 1250 223983363 223983371
    0xf0c0a15120903020303100b04030b0f34110102040e01060c021306090915020901120e03070203120d1404082d03150909071d0402030102040305030c0601030b16050715 73
    0x4041e04081c803074031102500030750003591649450b607040d05104606410070441c1c91001d1100700001040c001601d036102ca004d0f50900715640302c0c0d40000380111008041e403040702408602600027420300703035046256401150b48e82030100c0000a0324078204e11035030013071080011000c0018800301b07010b5111140d18034030180038961800032a00750751044416940003801d017242c0781d020f50424880200c698030711840948608600d030010f2140068144ca070b44a014046181c0c480c0007203002d0140078026540d22580143c10f440303286143d101c0914403a0b02001c00195403d18112008200b41541c010851146074041400b52a24810034499005442d6030b086005e10a074410710400b10400b440e50142d400b5440503196100c20060403c10090030b250018019000e5034020b0004000d2605d030f8240114000d160045101d003282c680380007080c0644180d80010700310348000280701a03030f0803002485c0d034122402841000d2450322002e0031405003803800303e0740c10300140081c07200e60049000410315000c0d60300c036800001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 223985863 1250 223984613 223984637
    0xe0c07020d020a06031505180a0506012624090f0408040f0b03040c0e0601050f1b01020f0421030c0209070e091801060e0912030403030906050a06080f0c0a15 69
    0x1441031240f0782c11a0000a4443d034402100e0140715042c4070181000f284c06862510000c0a10032100d08010b0100950945420110301d003030740030b00d05001031043c601d0b40580301340403003400040d4007010980d40007031b281c600e4210005910082030000b4054100051035400607850300541e200c195040508117485404040000080e28030341003007500001d2030340314481526464035040c181c860801c1680f02458040b40740080109583e40311048800c0400501c200c01c0e01c1c0c5002d4129591600031a501d000c040c1d41c40012169101c840741c401400448038400c80000f41c503040048120090003250000401003913960107154014a8400042070f40301c0d0182c5000485d550391040000c0349044299000e40ca40c91590903c4043e5600a029000c06440d034a40e00c0640c504040b800d86a5864007a408941e5a520210218003014840d40185000e141c000d070723040c071140c10440605c6008051a215428181c4205810800618008503018102040c024074544c0101e00c0c0590b010180c94401007a80100b08001c4003903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 223987113 1250 223985863 223985869
    0x406051603031401090f180c150306090c111603030c0201080606090d060c0f080103231005040501020a03141b13080307080d0b0a03050604062a0804031202040e0c07020d02 75
    0x1e070003821194408911a090003800c04111f0300c40e22500e041c02c00840055a0215070415640b0003244d02001d250011070300320460403401001282c20190310306060154840c02580e02c03501e40c54007400f21a017034074400400d2a040100e03914881c07200402184030040140b0156000b4000d86a2006001c1d280e20b19011404001a50540686004a0f03a89645080d00b01555138020782c580c3c0c00144900f80604c240d4115100c04c0404814126841401c540c1c0c0e52422a40318018030400d0b03040340354840140160300b03251500d68040d41002600c80c00007440c10182050704400302000318003911003403a11150149030100515500e50150740e2014010110140004030003608000408245010758842c03501d0b00b0045100030f0907034110100e85441098030090070310103c1c0e40420117581081c0c0c01701c40001e09640c2e20382072200000e04c1250600c218503601d1070144001c3d4000d0101d030321452003561440041100c00308c8040c128040d900540420347c3c510170000d00303059a10b038018440980003d200001d001216400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 223988363 1250 223987113 223987151
    0x90203010207121101140c0705010605120309090c0910030b1903230c06190306150203031e011401031a0909150a0506060304061802150a1103040605160303 68
    0x1183c169208080b060f603400e5012004d64008100f0000030300880c9070306070b1950102080600001c080c0440000c4003010040250b2052000b090054004031180c2d8030402241c0e1207030090010140150100340000358803c049004595055038018078809a00c61000c8044009003241c20506400c92050281c144065800c1405000151300c41d641b2503203210707660729150402032102d014004a40e4810a18003909a86000c162020141e000160f50401c8040d1101100070f882140e015111885515092240d600e50202c01503205620003e02070078a046907100003101c0841c02d101d00c1c00100b16124412000350721a80180c0d03c803140c60040c030000041213000081050106554200496104600c80e44003500403003507050703005050f1203040003185044008100184401000181003c1d5070b5020981c0110054105071074440e0050a10801d4409601601220380e0101d404d441c0400d1340c90911810000e800030480d0103640c21070355401d0502d003081d4144805808204022020316031101c1002064440c7c46030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 223989613 1250 223988363 223988377
    0xc160906050f03010e031b03041a1b120d020a090e011d0109110301090b0103090b0c040504140610081306020c060610030b360906060108010501050a0806130902030102 73
    0x1500040036880c00040042c2e05490000d024000e90401d184a46000c5020041d180520000e0031150801000000040e056101d107811403010704610a03941d401d1201200064801d0f080022083e5030911b10302c01e59182e032184108050700380c40b0b0081210414040d880d801034220701a481c2000340e1002e450741d407001c0100d8000d820002040c07896150600a411a01599500500b090102000000d411280250b05440140603210b0f000d500c1d07203244c60030f9034403a03400400b0b01d541001e01d6440e44e040007402030005910074404c6a1150f414100700c440706c5030403402100d00a02006000380d040c0649013100382c80442d4001e00d80c9120048000220020500d00c0c001410707448a40f030050702036031405c4010442e40c030a1501c280d00416280c0100c18009031200d590386032020718a4400412140041602c800b41d0340c91000c150f1641c8402d600611212034000a0038034046e8000341c031078103156030726200112170078040c1002120010f40e10786d012620b181041c105500000d00018000308200455401007401d82e4000c0c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 223990863 1250 223989613 223989629
    0x5040306050f180f120d060f1203020d050408071e0302060318010c11030702040e0a0b040605040c0b03070f03050a0b041107170703020a0b0606070c06022b0c08090a030c0f06140a140c16 81
    0x280c1d0104054bc1440762450746074641c2044e5041c0360030440000d945004a0050701c418125103d9a5900050701101c504021a40184000e90b0f85c0f80805800964031030050320014150700300b0303501010f0540244c200c80c480c10310700c5e4010346c2041c825408000c080c01c44a00103040f503000302050b04021494030141244180d00507c00498a4101841c0002e61454250300c04005164140b080c424801d034000704040140005143c041026100c41301c0441c02000315485503079000c0d19003507a221446070068003811001d8020140c01c02440400544800a4818070790014016005081310300c0004003041c1c0c0080e040300001d0141410207802d80d032010300240c0d0300e402030405603110400d4030445142d003000220015501d841003608000301c0d80e01c040d10040000500410885010032002441e4492103200001075401c4001d00d00c115613280343c07198000815004140c0003030001e81400d02d4116600d400c4842c041140e540d14100000441113501c2150880c2c0c00c0c02c982d6002e240b070114030030442000e08002400c1d0718 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 223992113 1250 223990863 223990889
    0x91c02040c180602010b060409051e07120f09080421120801080c0d08030703020a0509031203060a140d06090201050d050901063209040305040306050f180f120d060f 72
    0x942d000360010082d4421400c680c18195070007440d45500c1c0c00d40341191400d85001c500d5072207402d541102c0c6c0c011604002c801001400820200c4e940c001c0e032500da500150304041210b080c03180c0030642524803074540034202c41410001004414044201c402448600303d8010003da4036582d1101e41b00c401c40f04403d00002c8030340d001404124418415170500d01c4c011114041d00910782e685034181c1d800700070600402c4c940d0104074101d82d94041c0003200d61807003004081d1007c100901081203203540041d02d2a6002c1c86403840085103403088145080540100102448050003069803004050b190040c0100d0401c1000e102c100800030303280c000c1034000c1c2d6164001142450828001d0100c2c00407050440a981f280ba19400900c04041c00d0081e074001d10584000c0c50540d80c60800791100c0c41540d000030b00803460300042040682d0200011070140c004162074005051454000541d5500804210034481c2c01c070880c461042c00080c401006003158050012130815070301c051512650119512000d000b41c02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 223993363 1250 223992113 223992137
    0x306060914220201050a02070806010803030403081303020c0402071a0a060810020f0711010207121109070c0201121a03010606080406151511010908030a02090a0801020c03091c02040c 80
    0x4100e0803154001c0c0700030500440b008480c1024201c020202101034140400081c203003031994030030301000740640035904c115001e030b5940300c0006a89610840b010360005035100c022171110700c440e404015449406034000c10b00c0c1c5044d0f0040200943c000700e0200c855810481c0d45e1080080c4102c0620305c25440501c000540601c1c002d8a00d042004402080d210240b0400041e4003444552058a0490b40c001e666000c9020003140142e140c010070307030024405076030b4491112003004540d401100c52000c080c0c410f4003164407800c000f507594116146009010444000d41c01ea211180c0381d0014541503c0d0580c402e4014500ca00441c3c2150059000030b400a0008800c00040c03109601501b00c51105681c807004289240403c50f81e445c2e03005070783c0c0c6001c0000c1e03603071400d401d000250840304007950405049550b82c1000311a050095111114040c00f0f124070341c000051000c0180b003600c4840c5111000b46150050901c1048520003d0404028051030704e44001405030300c452207100940e0300580c13a01d1240843c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 223994613 1250 223993363 223993391
    0x170702030a090602060c180f030a0507031202061e060f1e0f0909060105010c030201020c0304061706040c02070b0c01020d090503040608090d021c050702031606030e011512080403060609 81
    0x1502d900300310199406070007409001c11600040f03814400c00c0000340e03200e4035103400010340040f603d00e03451784e454850780c0403600074030201150100842c0d115000302c13035411000da40d05a031107050840c2d900420000e13101405074960004104194014001040181000c0702d101c00a01c0512000c0e0b202c4404884000d400409801c00c0203060b44400d600312482da8192a2000d0107640d146014003400c0d0400928444030020107000350181c942445110096a4959846120050600c4062078019520f1070421000c103910741000e215001040810794054201c0b90309007001c4220701c0d4000102c14074030359400c000d07452803070350709205803003500744108061580c8900c1d04000a002c044040c0c40b4540c0d5030400c200248500360000b030740e0b0000f90104003000c0600c0304950300030381c1c140c05048e201a4160160305140c2d00f400381c0440840c0d00340d500325102000035031400d4400c9402c880c000d01c030012042e00706080c2441014450b01001840c984942c110600d850745941e034580680b41181c0c05001010349403650b1204a034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 223995863 1250 223994613 223994627
    0xe030a030504060f0905330c1006060503090a17070503040e01090e1b01030c120510210512070f080d0b10030507020d110c1c050d080106021507170702030a 68
    0x134251402003215400d103000a440000f00700421007c50303803100130390320a5121503031882c03a000d8034603511582c50703142403c8000d860718051030307240e5412460305e01e01150703217030003907040d40c0c064125100180740051640d628103112080d184c50380501c400043c4403030000500100300a001a20803205105810f5260880d1034003070300c9003062742070b0042d046948a0658010808007402c9007140921300841e1300c0364850f90a43e405031060070030b010124104010007495040d026a404100d4010051440350854002c0050800c00385039400240380780c0181500d00c1c2040306590140454038091841c640040c1345682d152a5a42d1180e84440b10321510740d102e9210a207001140108941060304041c0a81d00d850070000b52180003205818090164007800b17030101c403008010101113400c0103041007a81a000408800b019002a038044400307101e034854a030030407442450500e0494060b50020480d0041d07030750440340c407007100500001c100580c251148815000c000c6200740508910b03006503540d0040c4500080c001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 223997113 1250 223995863 223995887
    0x11d010e1506130f06170c01090f0b04170c0d0b090c0411090d06090b0106020c041a06030105090c07060501270c080a0b060706090311060a0e0307120e030a03050406 72
    0x20808160811405465610a90241c0700e55002c0003d002840b06201d0130060034190402c072451120000d00c0294860700143c1400c82c45026290220020303600e4500442424180c081c00b481c41e202844204510301450b020b00c075000602000395221805e800f40850742d0342c0f005c01c10030381e4400d0700342081c0300c00c0003001d2240400307a11081d81e003070204980131018440c56106210095004801940d144010700407a80c1c8000c040c00c1c0e1003e250400795a4400c03000395500807041096100700d107818150000048125041402d000014100500f5603182404006041e0320050420700390543c10030090001620501c10385018042454000c0f0002260204c54070a01c0d400c8405006c0052030711021180d0030b60001005988004110008245458a2000b142c001c0c081d4610041496085c800400304040c0c120001d500f40e155028100d0340c00b50740d141c01c0481520703104031111940e60020000240030580151100c000c1074080e003049401d00a01001080c54614803035000d03000540301003814480154850007071441 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 223998363 1250 223997113 223997143
    0x1103010f0617061c05010c03020d0c0c0203060c28022407170702010204080f0601090b0303120c0904270302010b0d021503070e060408030901020601120f020d0302011d010e 75
    0x2070481e400c1080100b80c50003514040c441c1d10083c4140f0085020450680300080c3d01200900c8030118900016001e9040303050800c0328207052002100b00706d803042e20103506150700100141099220807440c819103500400b440c110903042d80c03612961105007010107030304008031075006242e01d42e0060800504038096503a14003000d00e1000601c641c103680051031840c412915040b90290781c4414009034024845c0d0307400300c40c49004021940300c0b040c1c0f0118507103040750360b040000d00c40707641c0301c0c000c04d601c80c4a20600701c4001810080850310303580e80b61004c1c0c80b01c100d000d070000a03074919804000c100e8203c41041c0c500c1d00c0742854601e41c109507083c026845010070a072561a622040c1380e002031a4a2202d03902503d1050002c000143e00b9440b6038900c40030745c0e001030304680e43c0e96140c1d01e20b03a0712940281201d41c00b45c410500005007425050310701304107460b004128406050100d03800c20800c180d010070306034215074a810300b51501e121003070488903050104100000b001c0040745880d900304068141e0b400340b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 223999613 1250 223998363 223998377
    0x507050405040222020d1d0f0105011a0702010e060f13080601081b0609040c020618060610232b060303140d060e0a020d050603120d09020a091103010f06 67
    0x100589030240c0142d0320140c2000c138490280c01080700c001c000e0042d1800c3d0300145082c05128282c01c0c0c80a880c696039502010f041d1094a1107401c2c4180c00c2e60f40038801c03a4000d00070005159207a40040e8040d00c8554414980001e020790428001106608a51440914284001802a58000c185c06c18500600380c1101414203585001c07001c03078480316803080078205083c4d5071001c04a40c1e40c07104120782192500820410418589030b170025a10fa804544003008504400050151028005083d5100b00303002012050003590b862030840c0c5160840c904494000414400b011000705002c0150000d03c580c1c4161802c0c00241c2126948441061001014400e28003603003800400c0d404040c07508003114407260a5035980c00d1200041c02400ca903030000780000c0009050084403041c44e001440224101407061103c0d0b00c1d040b042607103541c42c0a807240744045040102c881500260340211504d240010144691f03166100014001d6440c2d10504c00c030020000801485402e0590102801401d51454006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 224000863 1250 223999613 223999621
    0x60e0702070509070c02040e012f07021f03020d0f150605070b041b081506010e010807020c190b0301090606020105070203480a020901120b0406020c0a021c0507050405 73
    0x30310000f8000c0d009004200e124192041903444d10b8020040c0e200c4854001c20500005480f00159174003036200c2c4040d402c140c1103c0b070400300304160540340541d40040c8a404289a8041c0c00004144070604902c1070540900c04080c9104403803003802808815018045a113402d41c0c4562202d170b1701e20b0303000081031180c24462040401d1080c00a998040c0e80411201600c84003c01c0c501c01607190740e80002d8447c4250039041c4515140514030600501017038968503000c2000900545003018100c0e0820010f0f8410940300000b0720b0101608000e5101b4405100e2a590b20b4440180195000b6000001d031203498010800c92507509201e003551220503880a0b42c2454003090b400c045112514094030b05074200b1402900c80351030714403806050205c2c108811005804550303030380307a10b07001c01030403d074803031180f200c000650302600e8860126141c0d480360800300300d0360369655148000c4d00041159119071084618220040e251409003005881c00d40c00e6842d00e01c0300d2450468074195160301312500450400080c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 224002113 1250 224000863 224000869
    0x10903030801090b010504030b010b040e10050102030d0c032003010e0a0501050a120501020f03040f1202030301121415040f050601090b010918240509010509090a0f1106030406060e07020705 83
    0x490643e03006141c00300300c61640340d0040f20719000d1030700040c01c4403500ea00009101c805c01001401180c140400d03001c541d68039110740041e104181d208082c0940c004100341c0c100d10b03580d03a020044003101410001503a02144182004041100b000868182000001445101c24050351164000300c00c04d400c3c41190304080220740c0581d030364800d114404554100032401c1000a4068524006100380016103e2629052441d00d401c442d090581e000e01082d007200000a01c00320840703041e196400d40310a000c020039a1043da950740c10300c41700e5005008840d038813101800e0f0b041c80039001d280100f0b001030743e00415003005800d001060703002d1034840c1c0c0391950780403031a40c1110714041128180d00400e070000f90000c002a02500d10b65400d00700900320306401e0200c0503910740415040d074001343d5035004160b8a03141805074840c400c1c0c030440c01c4c551101218900240300740c100c1a149a225400551a102d4003401082017500142c4045aa10b82c450324180010442e0362050381d07000b9000c0c40140340561400c804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 224003363 1250 224002113 224002127
    0x6040501050f0d2a140901030c060507020409020603040501150f0f06120b090103050d0f080606030f0408040e04060603140303270c150a0e0604080d03360b0601090303 73
    0x3001c0d000d04000d007110402c1c02861424045008105950b040003583c900756440e00d60360f2180100540112541c0d045c0d10343c0c0c2080b000c0ca0381030369400380100418a08020041c2e485400000040380c3c02038607040701e00c00503200c1d40041c50043e80f0401c000f00781140380b00c400014912030758008000c0c1f0030348400100030041552100c00c0c11120315040c4008441c00a540030703005020481c1c202070700034007060000001c0080000303c8441451360307965406510b0342211801c0b11b1544090303a050b58480340c14400b140720f4904503030300c1c15000342c801c0350400d05c0c255680c055480c66540c201c0d000d0358259600e110030010702800007854080c1000c0b2502071481d500d000b551b00b03880e0840714003060340c010354144002c02a240b403c02080f03190704030042418507204081140c0c440380c1d602500881e40020744040843c0030501701001a2015070f25a8005001809148a070442c0144418102c040c8034020004041041030021102d2081e503411600814942c1440ea0a1144a1078070150803181000302c030750003c00110380e002c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 224004613 1250 224003363 224003389
    0xf0308181005151e15160210030b03100b0f06030f0f04060e030f0c070801020c07120203150103050307260a3618021c0b040608010516080604050105 65
    0x5000507641d15640c00080420581905550b00b20040040e000d0b240b42101d0701e241c458071001c8031728210000745030030b159100b4000d8904891140c10020507040040c548600380500c44012480c0000f2520354082c0082e01c1c0080140d08044010758407441c0f6140c2d414442e07004010380e0401c1e95154510b0420100c24244444010100600344044d040490200310007500a0041c1202c114216912404207000d03076041540009200c032058071490301e0014003070324103009962070010400e0281c6a0540741c005102c841c01c0c4001000c0703915000380079903508a074400b86001070107180100011030b2580140e184c41d01002c07422000004442d0f01500401030301c0403c1208039054281540fa04030039007082800445000900481075858401180c40101125000300c4050b20445000d1140c07869400002002d503c1203200342c0d15407d040903141c2d00c507030b80080b005810804605c1d9000c0e000140300ca0b038072107030b003421548241d41710b00281e001007078218a0036901c080915040740c0101d80070403055260000203001104648 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 224005863 1250 224004613 224004643
    0x2f040902040b031b01080f100510020c130207030206060f091f08060c0705070e06030d0e061c0204050a0605090a0608070507050f0d12020703090b030907080102070f030818 75
    0x141510110344030350308501100c11014007284c0400c8800d0440368a548507080007030303000407020000113104000121706940640d48002000e06550f080c8001e101a00340500b5146055104100c0008103a888424881c401c500342a8001070f11a0950301e002030034040090807007441030b116980b00a00f00d5552914264001c0e06201011440703440b840105130342000c260b444103503680205020081590a11002800781a01c60710540da513107501c459520761800c4054441c0f0f50940d010174121000c69000e041e0310f03441901c0003003101c0e041090f080c4500c0e4412120030610009582c02160400c580e040009480001c0c04c80c0b400d1050500c0b8a40010401c1402da6108a408005075200403c560900400446162540200954000f1401d040140c0d42c6c40d40c2081aa00001d1208014800c0542161080c0c503106545a958940388a180140c0c009440e000900303a1601401040d0b030028201c40244014802e080c850560340840c413000f820003a0090340300030042d80d2107140f082c036400c203100e00104400781038050304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 224007113 1250 224005863 224005871
    0xc030c06120e1b04140f090c09010b12100302030f0f10020c0a0204090317010803030f0c070f020d030e0a060e040609021201180f0e061f0501090608090a05010203070504032f04 77
    0x3c00000b00078240d481c210800c0d0300d010b582441084568481075a2241d0b488804450300300e441c101c1807003000ea40911480801110034001054801c0c111f50f000c82e0840800f0140604442c2c980d00000e05000c1c0b13030021401d0a138000c500d136503035100003440068182c020414046040c105081c50702511148100710080c82140e441402d5800c15000c1c40030401c14801030030105140c0d40c4c4501c001075680e4000d0f141c0c003252688030707400164201d402d00e0498400341d6000c0e42c41c203c140e45030307800e00039040e40d11702044051041c51000756070280c41c1c1109010060540d82d807a8a070158860051000305c801a0304078400082c01000712203040d1a800011904490255460203400e8103048005c0e4014040c82c0f0703012004504000c51242008000a80c0b070b8003a540c07507103885402041400d84192601d0076407140034007150040c00100582030013846801d501280031029509016502d907280307401c99104940110200e08081001c2c0180b0402041c000c01c815a010060310b1041400b00c80c41c0805201040c42d0f41c865621 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 224008363 1250 224007113 224007163
    0x7081b040509030d020403032001020301030201050706020304021201020f090109050f0102060412050f0f0304020112051021021201060e0702120d02070f06060806010612090807030311070c030c06120e 87
    0x10000c07107001c08207161003191101d07101d150082540c1c01c0b04000142c4424071245440c071949d81842228101c950517151540f42c8041c0303540b02000f941004105030383c03003c6e030000b0001d669482800100204a41c100790955500740210000d000d00016801c40ea0190a03460340380581640c0001312190400c2e000380410340701103184202202c0d284a00e05a02d01020340c080303041c004040d07034000a940901e200343c0702d60158a50b043c545804840c000c40c2c00301c90009180b18100148501403950403009080440412044107064001c110100545d4044000c1caa41d602c404002c0300090485450300035840c0d1000d407003940b494403034080403406170140140c00b03035500084803c00c100524030050740c250b61048061060941d070b451420f46502007442558003040f540c1d500a540d20906115006490b079004c0159401c151a548045006145250a898840d0420070513640800c0900e5440e00065100f18041305500b0300f8000014a5440070842d8400c545060006072142c4910104003e0f01584c2e180d40510300540d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 224009613 1250 224008363 224008381
    0xa051002070f0804030c06030f2009060904020c03090a080a0b0105010e130c0207241d040624031103010302091f09061206060f1a070204020910020c0307081b0405 71
    0x14842c0c4000b070003014005400010001500310b03900c03c80302c0c951010000343c1c680305401425505909090401100d010705161451031801000c4c02103120068585070a00203c403000c40c0881c1d0000c0e0108899078804580030000b858401c04200107040200080c150f140304c940e5541510060600885043c000c0c00c0d0400800c42e110310711000c115800110041c1b02c612192580651034124900401d00042c3c0c851002d2a1081c1c0c8515904c011144c042d0f8030102d4090700b240804050f4814200b00c07561194850600242142c40101503034241440300c1d443c05400d2100402c0078081352111800340d400c0c40d00510042000d0b03034070741144a6111161800b46c0507d0885070b6590b982d40350b4079030850491a0f02e404004a04020310500c0785c40010300c00d00c000c00000b80c0f128a04418904580314240844e8800e5420b85070b000c03904405800003601c00b50025040c07285080000d0502c21900d112000143d004554030912860b0402001d001080c0701070140c410100c4640e48128208640e01c0094000c0c0d031514040340c4204 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 224010863 1250 224009613 224009633
    0x7080d0908030708060108070207050a03080c030c0123060910091a0907030b0a090608030a0f0309080304060b19030302030f07050a05060f04151103190b040606050306120a05100207 79
    0x1a0302140e0a6078a1400350783c094040e5034241c40140c000340b003200009501c60300010780726096980080c040700c105446c5503034100495100d5041c1070500c1c0401e20810400c51424020030100809051005c41d04400a1101c5100c1480c0244402d115000344000e208040b10b550356403c00b51119410301040200d80384c4401c03140c0c152640103198110f110071b01000030296055001c00d56000040303d119003180c2d0354403510015181c0900541a80b40c000708080860140101c4040c00401c519050101b16010580c0b100c0c600750700201c81c19607010307440310300508807072a12800b200d50b03000500e48845015425a20000e542e8040c070b03010301d0050b032000161481807000806c248071050758401e0440e191894407061b000345c0341000791802ca400c2c1c0004201e181401c401401a0541e00a201c0c42090441da22484001a046100b41140b904190303146103040c0107480e1030086001400c0703140c48065807400c1034014003c04900400302031446410186009000540100c0c031421103449842d809602c0300000d0030a401c840e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 224012113 1250 224010863 224010881
    0x61d010f0e030114010305010c0207060c0b0609040515010e0f09030726040f080703120503013005012c0729090d0302160504050103030507030f0905120a02120304060507080d 76
    0x40c1104c1000041004030541240740800c003540e080c0c40196a80c0c01098420b00d501076401071542c056600000d0b00741c20464081917002c5d00030320444485000c00078a8031711a0030203800c04c44004c020001004030f04c494100442d90055100c070015071078503402c0e0300e0f0040034580c1e107454100e030b24810720301100b0150406170955028100807607450b020300380d84000c02645c511441c0301c2107603001000c0b00c3da04011030182090300e040303440d82c3d1b0201280c500f00c0701600c03650140d44103810b0a0303a4003a45010001c030301c0900c50310103444480c440d90340090044078600400003020041818081e0301072141407028100c040c0e0320841250118640029020306056010821301680303803080c1d04031a039003155000f810b0380020010040060f00c140d03500d819480c3c20034001a603109003c0540030440400c07102e000a8442c0300c0703c0140c2000e07441e151520a865800241c440d8441c90400c044030350040340200190714021060700c100c4010100114078082c41c0c04c201038a01e0040c0c1001501e401c002050085992846401030311103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 224013363 1250 224012113 224012141
    0xa0302012304170102030105041a0a29031302030609010e0d08040c0e0c0a120b0d0206070c03140d11010b01020c0d0510090305070b100b0d0e010e03040b04061d010f0e0301 75
    0xc3c0180080020300030b400910603548149c2c10301c02c104940a403040080f0071b2046c1c000d00203407961402d20301910f0340300391089661400c40304880e40c0318000c5519031000d9806640c210050036240e820ba40105443e202001e080502d0592601e0303441c29034108001034200c1c4d41a5282400d00b9155518105070009080315072082d9418402001004450000c00c00100700051442e10323106a24811085800100c856441299800180c1d0804000152900320040d11905204401c0241741d6034403565482d0240c0c544071005212940501c5031682c04540100e02c40904040040c002c2004010800000f5521016600484d0045183c040800709000c0d0a0101c03404a4982c040184070005643c80e009080760b120035400d0b0b80003082c900c0811107031601015220219804407400909150301c01d00358000404901030040125036a8109003990f00074240080c2c0010a0f038001c001e600c4502c0e121004e4550803244c10350392021040358071207413400e0ba081640b50040c10620f1512060a88410000c2801403859030b9035104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 224014613 1250 224013363 224013389
    0xf030c030d020d140f030601030506130c0806120f070510091508040c050405040308060603060d060513060b010f09090507031e0b040f0204030f080c0705100302090307050a0302012304 80
    0xc0c1c980c001904050707581403640c8594050b4240d2000340454011101c02500c0c001003000826101d61003a0019600b20300010001d001ca24101011b403001c9030b000310005400304002004010742c901e0a114016108124840a0301a02d07443e0248a92920890700451f4400c4524400460102d031281c0301000107421a40c8410428092814004c1d01909044608a030700c03680800c1d004c503050074540680790140d54103132104040c0c0d80300c803400c022142d0001401e89401100c0440100c02050b042c0c000d1a018148208009000c088241004000d68030603200d0340e414040108540e25089a2081207101150080781e8001495202d241c0101d01501b0440440d4011503101c203025410342280d42d000090481040790100405d035110802c40007079028030700c0040d040220018100c40450401001030841006200c240c8106035100c40004a00d00345245d41840069030106080310682800c00910020b090102e40c000c00c0321389142c0c002403c070401014400545800308029004020700c62003940c010748001c0000d49 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 224015863 1250 224014613 224014633
    0x304030e0f18071202161506080a020a0306020c0a0b071e0e0f0103021c06170601051f050901030b12030d0f060308190c0c0312020124050f030c03 64
    0x10404102030500610942684400c0c0c1120724040d500d02c1e01c010300ca48035502c865640c0d11401c2d0740d8940c40704482d2a00a80030031005017907820380d25805081c02c0c03181400140e00d214140720001100d460790802c1c4001e5200418600150b542e440101003101c0c0c0c000800b598038100141d520b4100380c00444001c0c004080d03101803210598000c04288c0e0810000340d0164240c111040c0100c403046940c49101b5000f4908000c0c08140d94401d4000b80b8210032080d007100344440034042c030039045414551000813454801d100c1c08842c104180252030052500300e1b00e0419444110070f0700a040300c00d024111091010000f1800340030390094200c6418400010851800081d0b00078003a5103035401090310075030700c6140c6001c0c80085282441200203680c0c201c04020305210482c40805800440a240304c800d0000142c0c0f01400a1030309020440514801c54403001001c00a0070f01900b51105039811481501d44100c01040b980406401c0c070301111006c88454407988410303000709080c150660541e54250055509107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 224017113 1250 224015863 224015867
    0x1618030809120607080606071b090e070b090303030106050c010e0f0c04060609031509033605010804020916050c060a0204060905010c0510050a0204080a030f020601170703121103030403 81
    0x5080c215506907804100054403440b03407925502d00b02c0f0420042801180481d415043c040050418240b1441a80c100d80071382e009944030181c45a482017035029181c1d081000a8502840342d64024441c500d50141031800c880000381d06da00050081008000b400304210041000c02d40006071035940010079140484206420b894030f68941c21021402281416070010f51284107601403422a60005803224211080d421020058096040d040c2e00304890301181da08410f40f4403030621080c00b56a4280c42400c9000b0243c10302c965659400300c1e040c070041408020140e1510f041c260380c0200040000418116030602c242c6603805007510802035445440100602501654010008d0340d4a0f900d0300801207550750011941c903d402d542c02800c64104c4584a805021142c000e0350308a5000c14015080a45850a0300c0c1b90064055040c2c0000e2000400024002c0d014040389000d4030f0704c0341011311102c4e20103d0465a07411a4480107001d10322401310158218070070341c0e06410204035101941da50341840d041c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 224018363 1250 224017113 224017117
    0x8070f03030b03030a020319021509060603010c0f05031503012301050913150b0a03080a021f06050d021210051009140f04060e160803040e0109060e16180308 69
    0x41140071030b20300000141249000010b4482451440d40118900b03e024409404043d41058104e025442103c3c070548842084508142c4100340c41c1000b003240c2d282c550101420744d0024940341c0180107405454000083c0e000b41220383c070508607603825100082150129004006001b09121400a45d450043d009510003d50b01e04803101121210000d450b103294028104040800c003d100c96000c580ae520b44041907000169082c00040512051503540e0b1201500759201e943c0e4040181c0181000c0d04004003046654440401100e408210080c10b060101d05802524078002e40304d05062803003184d4501c0c003040300030740d60700c2c06c00410700c074074141000d00e2400203045001e600151803c1c00c2a0fa200c4480a1010701e1103011840f041088903240c0352078a00c02400c920003041c5041c000c002603a0000706031280910700500749c030780084d56241d14000351042c0341c1c001a0040351420381407040030007040000b1081150000201503807242005101d2400760752140b810b600680c0502d1810400106205403240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 224019613 1250 224018363 224018393
    0x30c140703020111011802010c0f0b0c2206050a120209060a1e020303100b03040201030209030d05030a0b03120d0c1e08041106071a06061b070303170f070302090105070807 75
    0xd4004c60b0050100302c9600343d500703054240741d100281450090144d0711402c0c10007000f5000e5000480c2460302c588170501022000c681c48050403100080c0d4600035410919256024181c028003461898204100284244124a01103007003110f085104100002190f04844038460300510b60380c0e4600f8104005804000c004003000115200700300c10400c1300b4004812644121480d032524030416007080c3c01200c098102400981c10540c0c2400f10742003a071001c0102900d5141c007910bd030764903880c118110f9411b0351000340001d8081d0b080b0091450108480310152416000d0301c0001080c141c2180004030f40d02400d4514991594400512410610381c2001d805070159003c0d0102600401c40c19090082d28450b424004102004020460f01c99014900e41c03550065002000c8918142c2d4044500303e000c00e810741c060b03a1a8000c10000c00070540c0003040107400000507070718240c603840c103c80c2180d041c14005041c8030034150002807950844e2304ca482214060f640c401140b545074422820f0203507080800c61 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 224020863 1250 224019613 224019617
    0x5040824011706040213060522050106020a170a030b0904061b0504180e0304050402040b0405100201050910050c120103080a0f050f2506110d0f0207021c030c1407030201 74
    0x1000118050400c46601541502c1c0c0340010f04a6403102d5083c4884141401c40c0100c1c1c1035950840469541c0e95400340c01d0300b0005c801800899840ca81078000200c03003040c0e0083c1d080d036225240500024002c15010711401030750640072911007000e03c0f000d901038441100c415a2021082003000100041d603404081c64801c411903440c0c00e04007580b429201071040b0300410851070a0b00e1100e100c0c00791250800714240c030003a41600c0c03e007940d40000c20240d0300241c10002d00c2000100b002e11082c10704001c0030202540301e1009005038180301040c0c03901d800038000540300c1c2c00c2e1a500055080a5014200d42c200314001864010542e50307401e0900b0160402d00d03c00d40016070410321055198801d10940700c01078600744086150120b00e240325544912401d24240036000e03250811404912180301e61410704a07401c02e40d680c1e40d1b440401c3e8004031900381000f030741300d035206000c00001b58451500c03892110342150045030202e90641030071344000402002c0100103c41c06407071444000004241c1d1801c503407007a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 224022113 1250 224020863 224020933
    0x902030a080c1005040201050405040906110c0c01110d08011e03050a060f0c020d020709021315050301060f030908180102030c2508060103080f070312090b040b010e060a06030c050408 80
    0x140640f0310030344400390740117030002d202407100344000c2c5410b501003225184503400000700c107289840b008200340c128511a00340c42d0445c0007038190079600082d01180e13003050f160107001c014100c114003400044060044903007541c0e12040207410742d15001715060141d50088210b41b0844203920b0b00102030f20602900d121117604080d102c1000d6400055141800c0f5180d8000e0800c490801660030002e401104100c0005a10301c00c00080048074480302d19011005580c0e0103030740c0d605180c405407070071012510690805140000041c0440c10710000c1c0c440c802e451000d00e114500c55200100e01d14028401d50003601d009a203505000b1400010036001000100e540304014561b60f442916102c185c00d02c0098049071041099840c3c4d40b5040e001007078200d02ca801c0c02c0b4042c21464100804031070001d441100c1070705454043c00300b4071080c4218a401040a840180100e03d82400890703151174561090100381a210b42c102803140b40100309070b4010303064540460300c00e5000500c5100c240001d00c1d103080c911301e0341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 224023363 1250 224022113 224022133
    0x1f0503010b010c02011b1403030405010e06041205072a0302040509030c150619030b01050f121005042a14010c020102190602121303140903120c010902030a080c 70
    0x81030180a050910585880d902101e00350015a60342c1210030b22407001010702c01d0451300245040e20800003c3c40c10b103005545900d000e240103400c66182c80000c1c0d815034044410003000840701720b4806800541031410b02c0d2504071500e0602d00c3d101c0c6100c143c8904d1100352002c3c9144007520840f0303030101c13030007210140a02c3d00ca071101c01d51a8822101480301a030000d010303501d00035416100082d04018050200c0540008406040c01c0d403140035042103034260341070b030300402451820b50440c9030090380407610b0b240007034440d9080c603a88400026071081020340342c1001a051001d160240741204064000700b060740d031101d8905000c100303a5400f400520307800e00206090340354030441c1e2007012180e041c1c0050010594520344605a00c15000c01103482d580c081140012089084505600900c1181480300c0c800c81145800f030600805043d00c01d80701038042c0203811f034541c0d00160303c20190407a614036980d0f0301c05600d4030502611031040d0194240c03103000f00d9102042400d00041848400e044140c446903c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 224024613 1250 224023363 224023369
    0x110418050106090609121401050c0c0f06060612070e030d0327020d02090c09060423090712091104050108030301030201081b0307050c0312040b01050a090513291f05 72
    0x842c080c2030002498040f051264500c1c0046c040390550044d0016004038400e0b0048a0a40fa0225a10800d0800c08903101c108841c01304207110039450741c0d101030b2000f8600340c800b15541d4001d01e46158001400d803400706506901591aa42404202074243d03840000d0019000e0040c01c100074144050000c42c03604c08000c040032526800b0401d50003400c61600078066000c01110380b8002d81070b00742400d0208100c0c89281e82c0e01e402000140703c2d6035040f0050048401610500b001d0248440307009d45045e404201c1025444540c44c030084d22050000919080c0604003003500286040c0b40c5a0080c1c03400300049010318000000d50b04070781c400d0340c50321096070301c000d5600d070510807201344405000300c1800424185400f07039001d0210801d0141c202c030b0500e0188480ca6a481106803001d07a01298220300511072402d1220314203018060701c82c006d01250416140c3e60400d000c0e01400a841c204000c80968011859054003030303000309648a040100d400c245443c40c10b0f448149014944100146a00140e541 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 224025863 1250 224024613 224024627
    0x1a040305041e1d0712021305011d210c130510051512061f0903020f030a020a0506070c1d2203050a180b0c01051806040c060f03110418050106 62
    0xc900410f01d9a04210003d14825a520090b1160080c0254000304600c104510700c06410101d035030f81a1032841d06e20b0980054810350800b08400609025a01c032684030761034140100100700d08903d660303480a00c2d414030f0903081410748880d0383c1e8804a0708040b12046002c5030000b07401604000d400564455030360f010410341d031019008456007003a0501c0703071504103c0d490014550010014050a0b4140101801480021145102c08010030b50b200414401e40c1003007507a2048414055009124151068000807102e038101d1141da032003040001b420401b0071001d14030f204024000c00d40e60702056401c522454842d0070701154801080280a20028120400764445031400d0307400d5101c1c645001203500003251611000c40e600e03d0030100314140003407401c0e5800020b10902404100004460402c051410300b8007861051040c0c1d586d1000c030501003c0790b00408000c00f221418100001d0750001502d06030003418040d441956082d40c04a0001143c44c42c0d0001c3c00c54800280d4000c22050ba00c0c0c08007640c0c08 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 224027113 1250 224025863 224025869
    0xf0204110c06071103040f061106010b0c0a060b03010f09051b030111120a06030209010801061e05030d0c050c09180f06071407020406030f06061d01140402071a040305041e 75
    0x9600281c0450b07943e60140c0d014090450100065a00d01034403000d440601c0c41c0c03503500c18400601e0b6000310003160b00062080b1400351000c00210707450442e40444090b40ca0004910123840700380c5e564500703210366400758026a494a5410b20500100d80035041860712401c604500500c884002407010702507140610901c2a00c0c2506000181002d81400071049107940041405002d551799160210242e502c5001c02402046d42400200d9402d09100c0c000c114445c0e40001c41c11451007107682444981d401080c6040c04070396a18011220f01301c581059031a2900c1c109090b07400444603024881a1010703290684401403805040780d4004c19400031883c1d580e17400701d0724000000c4807026512070f480c110ae4010203d00b4001030010803010707140e0b160318003400712502c000c484107940c0d0041086070040100408400040c00d4000400075807408a80c5060011086040341c85a54000358050800c8410050702d802d00c5030b030300441081490a0714001e4155403050080d056442e001004407411a0718800e205415 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 224028363 1250 224027113 224027137
    0xf0a12090807020907032306010512010b030114061602010c0206040306020703020c04050906091f1103011806060801030812130506070309020109051e09090322050907090b181c0f020411 81
    0x407d00c0341d03203041c0203400d40190105040013420405074a20900303458070b05002c0c1081c041195a654034007611183c0203424107910a01130359091050740b445030110744a0040c02034080c24060215000c1c4e100142040c40365410080c4440e20100d80c0c801450750000d030014032288280c404121039151060000e079030345411516100c00341d2000741880007690000d200440140705d1101e0100711018035103140c0f00590400d070408405403415600740310043c0d0700f03030140100502190038200b0055054ad11012450300c00d84040640c0c4a5490b0003181304032019a01c10044550041c1c113459440c00e00180050192000c068142e002a41e502404200c42c54420070942c1d130300c90840603002c407440c251800c4c0442100004e1064a107400280b00a04208050819001d82c1301d0f0880c00101140d0709010412900c5680a0b1450f403c0002048082c00041156412110340d1070601041c0a4100720310740c0001c034211600400c60640010a01000c41003014001a6195041c400c642c2400080a0000440b03024042e0080d030ba01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 224029613 1250 224028363 224028401
    0xc02060c09030d03090204110d0504050601050105070c09050603120c010c110105010f031b080109050601030c060f0c201c05120c030a180b03010f030b0a09080f0a1209080702090703 79
    0x846a00a0b40045c0c48184064404255869440303c05141a041119500034180e25032041004200080c882c150242c036090070038030308080c05525078000408042c0203140e50599039501040e81c0341e50030048041c00d2115400031070368078112601c031980640803400c151400300c1c1810780c24244040c0d060003958113a84440b001111003a107940c5030400140d05010740783d6003000600c00b01080c0d6030000e001e241c18250040009003403652452070011042c580944c000800c11904400d5400c40c0c03903101e07a8050415400c100603c0e000c010309803483e18210440840a0fa01c0040354500c800119190801911041e000d1000e8446000c9075400f080094414002c4a82c0e01d500308100010f401c901510f80c80258085855018030081d4940442010325402138104084c4d042d1100740030001c20004a250560064124006000c00c14183e07403844154000c17a0f20b100010000803543c041504e101d80c0150341c141c001608248031040640c01c08030242e40c007000090740503003032003400501c40e01c1c020702603818155400b901040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 224030863 1250 224029613 224029633
    0x905040e0d1d010c060203131b03030e0112020c010501090614010e09040b0c070501020c011505180402041e0218030606060a0c0b070302040e0403181a030a020a090305100c02060c0903 80
    0x240301854286100c2d07040c80001c80701e49011a0751071016510402101040f419121807a05007022200b0380400c20382c65034002d080c424800a070703021100590890b000e0030403114610b501d00211001c0d00034030502108544c601070000600c141e842d08030004850414078228100e12a4000449041220003042e54000303070040c001c100058150380c6141e501c44010b4040702c1c100442651013a00fa42d20400c44200075a45846440d80c0d40500d5400341c0e001007004030b407008800b201080010f074030842d000307201900c216a030310156016408407500800f20780e0700e542070840d901c00c104240747c103451000000700341c0288294800030781e045c105407040b90501c0c5025280c1402c0c420090740c940b00701c0b10000340715800b015000c1c8000158526041903840c0254400e4a8040b029480c01e508607600048641c4000280ca50b820fa01c0f07685420303ca000c4980143e0744000c007507036820301c5801c1601c1c0e06e40b0f42d90005005104c0c1c4400c00040c06010760101d0b580c01116400e4403000e0312000d007040c14500a4012850341500680008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 224032113 1250 224030863 224030897
    0x7030e0c060c01020f0403030306030b100302030a020121152301120221010b19081501080a061505070311060103110609040609021306020f0d2c030d0905040e0d 70
    0xd490381c408000005171a042010641c40e40d16081580f0407004643c44100c18070400012060141e0f00c04d842080305031030b40b461038001a039182c9a801010f8140110500781d030128034000314a6802c803080031481440000e602d0740c600341c441092403180580c030044400b0401207091100204900050050350303540f00c00e1054800c200020351000d03912026902040c00300c1c0701e600c241240c80900074040b25800a407624041c408180c500301e120300451080200210800c0b601000150390492500c1c401e2816940a42c2d500784004000c00c041c1d0010604a4a1460001807443e84580142100c1c1d10a64940200410280c52159612030a00005106103641c9100c41103c1c2883d41c0a014011802003000c9130041d52882081e040381c1c82503542c0304805100360024048150100107040d4203120020003089040810340e0000c0c00f4640d038500c44a0b80d0010844151644001426080c031004001000e96101d00007202e0050f180349514400d4070b00840c1080010f0140780c4c0c01051028190141e619105c0c4211400440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 224033363 1250 224032113 224032117
    0xf0818130e060f09030d060b03042013020d11030109020a0f0809120a0e0a0b0c010612020603010509060102031c06050108090f060115020a050106030b040b061903080d1b020604030807030e0c06 84
    0x203203c4c40c0b10a11500340c40c4902800313080010007401066560b00e040604206560070780c08480d4083c0900c80100c5860070307888600da0030042c104224401a2034048000c1c0700000b5250841c1e083e4034001010002164074a0541e004200050580e02c41000702c204145003610b06907421114103074940c10006141c80024815001850105018540303420328590b40400500c090b20a500641083d8101054103d10307500c0911404000e4200c5140c8000603114a60000c2d4003444140151405003c0c421f02145040e4000c2041c1c0700041c040049081c840d056180060f0000c014900c1500c0c00901100049803110b8404601d070540048a04003502080e03080c03404008600c8465222901141b1410300c007200030132028418803001e0b610a6030700c00000e040a0620358201d071406441240f080389005c0058003c00d100b200001c0484c0d40c0041d0b6107480c0c00c1041402d20080c0520f1700300000c114112072a0038aa41d50108800d840b4074440c3c4c07030302202c5032100481142111014240b4001c1548034420042c00740c0f0300310300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 224034613 1250 224033363 224033371
    0x5420106030f0b03010c110105010b09060304020d0305040f0b030a0c0302091c021512010f05220b0301021b030904142e0302281401090b070f0818130e060f 68
    0x1901280703070716842010a08540006d000440041d0807038844140004003800b4150050a100a0f06418801d403100043c525110140000384a4400c1d00050701c00c050003102510001c0240c4200d075018907507038003244602544129510102207242502c000c1c003035802071094a003448030141c07401401103903842c150000c01c800c207032007a07a01031066000d8074034803a4400001e1144a0203540c20100c9940b500454542c1c401d2a0f401c90740c81202010340c1100b00740c980c440802c0700b850109802184512540b00840d00a2058210000b070381750702400d07400301454000005214054040d90100824100c6008801c1030780426600c09038a01841c210018101000b104201d42030764200e20208049503881d40020300c44c9081c1040380c0c0030003450542d40d00c0a1510b1000b07034001003041d481c49031071888600000804001e0a4002c0d40d210300d0004c501803003405401e00d5107a400c0c984c4a141603555140c0030150800b800b4030b00f0941d912501c2c0e550b1504110000324010b11032144103100080106d81c83d0000c806108a900134 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 224035863 1250 224034613 224034641
    0x30507030e0411190305090d32030114010e0d0b0c0703050d0f060e100605030c030702100e010b0a1a180d060204090510050102012003060a030542010603 67
    0x5043c1c030940041e442c0184010b41032100d90a0a55004d24030180c180c500040c10440c4982204010101072a040180e02e0b000c55140c0500c6408003c4140c0c40d4100480c0c0700c0b48540d61500d0110010808410780003081689078000d032184250702c00114100301c814014803030300500d002c4d004030105103440040c0e0301504440d0311a04049080c1201c1c103002d0822600d50340e170305080355034850008000140c01006420381000f070b030302c0350042d00f1070912a024120388800780008195807400000034585510030700104010390610700c2c0a2009281c10500d16020f008190983e80c4604038041e00028982044c1d614030301d051803210703290f5080040e036229074496925000c104a80094480740c0c6000055000e01c028005080c141c2c50004143c206018100c00b0f042071900724a066a24040008512991248100301d080103581c2400741c1e250340700f40119400c48550340c001401841120f46034202e4050203014140001d0129140d040c400b0b9044817814a01100111107220202144006201d5244260014840d1540341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 224037113 1250 224035863 224035871
    0x212090103140406090c0b030417071103160e0a021305040b01091208030f01050f03101a130b090c07020d0f02040b0a17060a0204080c0f120f0714060403030507030e04 73
    0xc40d0311800742c0441d4111446540d4001e100c2c200041c01807443c0107888091903450451910380c0c2c0d1103a2481849801c480c0d0740c600402c108003000080a02501c070307050042c1c181e0b250b900071440c2c0e99280c1d08950040d00b086075000000071354038031704603c00d80c4d0711391400c1811120f89a2800080c00300818000c00d4050402a0030340703010032003030100803600406601c9070004a40c0d0340344c8130080c13441901040c0c004500c5801d028407940340316600011070207108200940300240d4800c030041102502040080c0301070308641aa81d500b0100c134050360282d030100005440180180c1d61b00340c049181c40c841c0c00c0c00207500440300031010001c80c505140003110107101510003e5900d07003070303000544e03800d8803644400040e15000000100349401480103940003801c07044150b0a082c1840555a2100d60240380c1a0161103821840d0445580c0ca2602281c0c02610509492440c2c483c0a1001c0d1214540e0182c1004552680481c0c003103410030a044604880d0580d981a0501c0d190380d4040341c2c000c420454965004c1e8807 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 224038363 1250 224037113 224037131
    0x41403030c070c05061219060509090304090b100c0311010204030c0b090112050108190501021b0d08100303020718020c120a090801110d0203090f0601030302070906090506010212090103 81
    0x1041005500881000c0041525620b00b4a08140d035010550000c1d40101e10a22161520400e05108141c00c2000c0107900c0c1400c140304035603140200101d40c02254400461014070003180d00100081c010351700d10f00014010701c02c110b001d0002d0001c11240a8002031890381d809004241b00b1920b00399880807040002d46031030b64949030500186001d800c40300030108002900030181d0f0b040b554441002503400c1c0203106962400e003141c3e4840c030b80282e01049074803180d1001c0007002020750440e000d103100074a4035020760384015000c80e034454201c2d9104000ca041503001c580718000f0000d10030220f03641603006001d101d003000020b0269490114600414039024000f00880c00e005000e0315100007481c2308140e1300c41a05020003858114243d00040980e40351030629249000c2140444540a10440000d6981d1b00c5000581c1e1400482501025103400392030000310070198082400011507481e10010300c159900c522000342182c3c419150399000d40e121000644440c548030303000d07142840c070504000400340d070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 224039613 1250 224038363 224038403
    0x30616050c0a0f060c0f030515060f04030204050108030903061b03070f090b191e0903020f1c0303141005030a0b0711010c0305180a031706130c0507050606030c0a0b0304 74
    0x41000f1044944945502c000d290040d84600d5404410b2000d15046c419410445200c1802c103900820a9004082c0014031000c10164203003154021540500200b10569403502c0e0b0a0b101d03000f00310554428000e6902103000108160700c680c41c01c09280304038629544901e0310039988154103030b07144001e21090b41ca0008a400100380a0314062941842d0030101c1464000c00030f2035840c1c8060100321022018550a20340c0384d204020310217580d07055424108815003000012075412002d0706d4846d02e1440d0788245030400da450780200c0b0340004901e082c01000d40b0791007140d4403040d00c03138040d0681650000d00e120010a1502c0ea4031a005030030b80c18560703010490310407014292007038208241c3c0070036180d00a1000820741e0070f00d00b4a0b21100303100900a803144590340100f0810380e40100019441200000c0303501d503554980e9055440c0c250030030400c640201c1d600b014206402413030065505000301030000b0b138a070030040b0b1040c50700c00004001001003800c003544202c0b65000500150b520303020408500003860 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 224040863 1250 224039613 224039633
    0x30114012c0c07050d09080703060e160314070914060108070309060c0e0a0b2b06050604030c0e09070e0c07060e0f0c12070e01060c020607060c050d0b030616050c0a 72
    0x5501c640c0080d555110071300f0500d2170138041e141541c040080d00902000560004a44c0d20300352944450042400c2605c0060341d4131b000c400f030706120706410305030200008018203540000c440d115168140d4224503076503110b00e400c591480b2140b4041b00c51075070000b887c540c4107420465001c81113050005a01c10701d07845d80341c00c44e4440104140411005140e1703030742910b80a4140d2005100d60302c10146800311041c50307054228140c0200031a24600715101d8803030600c4642161001c0c0c0005040580c640307030f80b810300000b038441074800d0040000d08400442c03c0ca000101c1c444043e40d050322900b01091312034111034205e07580042420b4400550b00c000041e40c40c403007480316117110310755803000b01085000d100c1000304001c6400940d13003c540c4002410030410100e04141c5044034060304105203414698004105913216480c401400b051424504590068208000d00300a081201c410000d011100c0306040e40c0d940261440007940405524130a0001d221740018100c1040c100107640301160107580d204004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 224042113 1250 224040863 224040871
    0x30112020f210313051504030f2a060917060115031d0d0e01050703020d1b0501150f050103020406090b0c1f0e011802060919170a11030114012c 63
    0x7541000640030800c00d1821400c002130a8106d03400c3c500c00c06150000c80080c031880c0300082040d0307004101c02c002c0c045c502007500e2483c001c8080000c19100c01c0c1c5007a1086401e5070040102003106040042031090455068034035200c451401031084ea4244904a041c00d0220042c58081545503d0350040012581c001a101445c04400600810690020141c000440084040d04000b0b0a0040c140031a41c0003881101c2903890b41400200300b080b18003a1960050010405006c41d0708110035940c80d83c101c40740c003004994002540c01d0206444000440680c07096101d40c200103a041e02050140c108920014810104d044044a5541103201881e40e400700c2013101014965230b668050303030a20802800b4491041c1032603092204002c0b090750024800e4010b10130218005d01455a28404005440c1c040c040900b50200d151505a4001462555210300007942107840000300d4920701800c1c1414000c05c20317010801c0064200310380c01e0006484e4203908000758210040c2e040c104001c08a40504c02007409 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 224043363 1250 224042113 224042179
    0x3010204050a1706180316030203070f03020606090a0606020c150d060303080f0606070201120e01060e010f031505010f0501050a0302040e0703050114090f15040608030d0203160203030112020f 84
    0x703884108411981082c40042c003001d074425000c05d62038051500441100e02d00e00b03031085001880c544a0404901e50302600304024800c0c0c10b0008d500042c9600000e91f14850941160b00c6d0205940750300084040d2903c0344280405640b25071f0503000185003170090521440c12043d0000e0620b80307010710b61800d84520f03074030640c0800c00b030806201d035482040500d40e9014005940c001d14100e2b165000038118003110222140c0c1e2540c031048141c40442c203402c04002407060081900303455868002c4110141e40c81e200890340004407044c8400796180e28040c960403030311034201c620380e00c44c41d00d0700654165014500070000c05074208000324a0f404100140760160703880340e80c00501d541c100a4400e4042840c1822184980c800c50200142d03201980c05240c0d1004405510703800c46e03055100803c0140c56a03410045d01d0340004124503081c6005580694410a54100f050000302c0352321ba41643c40b03110a002e0104250001d42550001d410a103050103482d038000381c125650000040341d41c2c40c0b010b0b510100e00035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 224044613 1250 224043363 224043389
    0x170a0b060f220c1101020c030301181503060c020c030c090f04290402010f0309050703110f04061509050d120323070f030501080d0e0405040609080c0105041b2303010204050a 76
    0x140303642c04207204d4030012600b0000c502d0203942c034150540c1d9000c1417090410400c2100944540b6403000d802c10003056000c44e0505800940720726020f005003255050040c0103102d0382d000b105607440d000030703001e881c81d0003d030100c1d040c5e45804e14400c8040e403000b00280d4a134501410380d00400c07069443c014010b14141c41480415050910005010f03100c01102c030002c0508001c12840442c2000c542542200c0e072042e42084074810307010218080510111445511a14208000441d00680d050145d5800441c0d603508040e0f07500c0d03d0420900c8148072601400d88840660a540b4031402030b4404525a82c100103c0310b0807940140003910f800300111440400182c0e03440c05006803903054010140076140020140014080818004100c0115a9080ea200b2910b5101050074025258081400150044002030b0f0b07038024032446501901003524201c900d03221040f0758800b11081e540719641901c1c9903d000074604171544400c40e00c60840000c003154155130070400090540d440800f940001e00340d60365000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 224045863 1250 224044613 224044631
    0xf01050a0905040b060d020a0506041805010506030f0c03070e09070f0306060201020c030a050f04050d1406010f0b190e0a1d060f1c03050f0d06170a0b060f22 69
    0xc054441d91040d84031030300b41418000040e281c1d03030f08994812416a010354500c422800000e0040c942c0b40c1c03159070400400a408034000c04140800c1c08200c48415040c4510f036a160148a020f201c11910341001041e11310118503144440b400441d006031407403030000321030980c150000b0010079080d281080845e2051074003207030164150150b0402024540001c508040b80a49040d403280316001c064000c014001901541c048a00d07015074000c1c000280004511402c2d07403602e101b031180b030500c01603071621505000160301324900511106455440d0007150520105a031250326046507441020b060100c204041d60454070b0384442c8100030010f0b0507160980b455401070704d080c000707006800d51340603e2403526002d030903885102c80d07840c0c821380321a00e074030160b20350b41422101d40c002c5d0041400c2d400710001b0a2414034031650080d1041e1640c8900750080f502c00420791594a0000d030000070b02190340740d8005121460300c4208420383c201c0203455101b0700022414811440c2c00000070482910740d9646d229 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 224047113 1250 224045863 224045869
    0x403180906030b0a060608070509030a05010e06180109030c020f030c09160e09090c09270d03050108030a0e060a030915020c0f0613120903060e070503010c05040b07060507050f030f0105 81
    0x74540101c2002130410209041050050446100800402c1800000070318000c007610100030f1030035880c0d084002001107034141094240c66071000e80b00d40e20f400020790515940001e041c1b140d075690690549400624510b903074280180c0001c0d240045038903000e02c0204021a80340c0600c498490307801141c40034508648032101504406030340c0800740c003402c400001c000f6201300010751041480011a20b500f07082e901e03110340c01800b140c604400d51203122003000c4d6080340b020005540c100c8030415142800b00b60303240c07103001e0780c0d07401030f0041c03600042c120303085900041c00d280c001054000c81d18500460031042da6180c808504019140c500d80b4654006440500078000340400105000880050303d0b06003000000c0740100d031000c080c06080c80c0040010443c10601a54150300116800f503400d02c00c1101c0048407940310b91740c81c4100c234029401e145010310364510034412202943c4220002d00d0801d11291203850050800900450510a0400c40e0500c040384070000345101d40c10559480d100c0358141014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 224048363 1250 224047113 224047133
    0x90423090304060509090a020c0d0c0201020607080f070c050709060f0305120909040b0702011d01141b0a0c0c030f0c03030e01030b0d03030c090f08010204140f0d0b040318090603 78
    0x40032030300d81050000f40411a0f10108480541204a034070002c981c440d850040000d2141e07448040ea01d02c10450b14145003904404c0c400c00c03030f034005d8094480e01da88071882600c50400c1100c107201d940d844100001c1e80540107a010806489c051005c540e00d03241c5a5400c80111846500000b01d8406c800030704004104003040002c88000b10740c1d0320241010799600206546c881c0240c0700074810a40b400001f17480380c1c030075802240806103c4240001e035143c81c03d43c060081c6071030010300c0d00341a4410000786814520b6014283c072100c003d0202843c00041d8030088400c00352892040f1003042d0352804c00000710381610318081c030301c130f008620f0310403071303074558a8041d0543c0d51a14080f8141410407070000c88a696410044c040380303801d41000b0981080d659400c8890b81c280d41c0250303030a504070240128212905501400c141c40680c182580c1845641d810041d20640422403184c3c801d0305682503d00007804401203a070018401d0621205101c008080350040e0a1280c00c480002541c42c04100301744015228 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 224049613 1250 224048363 224048371
    0x6020d0e011505010f1d0d1103191e0507080703050102090922080d0b0405040b01090c0e060406051b030a08041203050f0a020c0307060906050106080c121902090423 72
    0x2d00500302078680000a065212803001890500000c0b040012084015a00e0380350180350080c00d087d041c034207038070b42010850f450101d228024030a03150500f171006c0c40351384d90f000031540101084c20314800400c11440025206081181c940c003800300d0024036100100206400355208500160f00c50011805000c2d01c101c004080c00b400c1c0c0301204d4042c00410307148040b920480e40100d081c954071410541040050542840001c0d08103103400d01700420b0000e8068103505a07a0140300500011038035075800c55815880020141c4d01200c10001000034a0141c0020f265000042c40755049240c480000349007136030000725940c03001c03941c030508100800100a1460750190401e04041000d424042c401ca880203000400c565150755000403ca00090010030a035142c0383ea04c24000d1106004918101d0040d003400c2c490036020070300a2001c00e4100c0303925000d8928a60008210b50300c0c070703600c0c40304d040010149007100029541d800c0100466a03140c90045030f1110f0025443e0000d41000b0700a00060904020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 224050863 1250 224049613 224049641
    0x306090c1005130504021b161a04030213050402040e030a02030a140a0519050d090602040503010c081303081510031b0f0c0803180304080a0b160e0904060906020d0e01 73
    0x1221450101e90300300ea090039621306030350040e21800e04108010112a540c1d82c4418188074968803800c0c100f140f1081c13041540c0c80c903500380300282115004055140210b02000b07504c00248180040c1c040003962005600600042002c14001c0311484094110384c071401c0318000603080014001d05070390704074902440300d83c40c4006d07862a201c820f2400030414080c00d940b03004d00040310661003545a205d50305403805000d1000007013141300c41e281303084c100a6105106241c003039401d0460500509000c0e142c049d00c14108079449008000d01c0b0f581c12240342078001e226402007180000c088041d929565100ca04030b58568070006001031032403034250303004c0b90f125452030700b0000c40c1644030f10601e511514030b000b034503440101181c8a40790500b6400300004464965100d500c00854000341000000400a44190182da8004c03015110504018a00c01c03000c0800004100c100700501094100040b206600600070f100020305c09455549100503a07204500420405485030303810307914040284500101d100840b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 224052113 1250 224050863 224050867
    0x9010308030f0f15010c0c080d0f0905190512010e3304051e010902060c03040f06090e070c05030910030501050a06020a051c1b060903140a140309010b0306090c1005 72
    0x4400444a940c00c1300b83c0039030410000901200400009041142c043d1120340199640310494143c001e120301034502c4240c0010b0300c0100002480d040c0030703521342d51520201c0310b0200e00074140000c0c00b83c10071004e505124a0740d600d031000000f800c000c0c0b0520418101210f0301400d52102003000903401c1090210071010100c01e4018000080c40000e101d85071a00512518000c01c40c4940e207203401090380c0b0740c0280d04444002811071082000ac8000c201f60b595102c0114210384c0c0701e0f2801c4403c3e10f107500a4003074040340000030441c1c3da80105207800580b0f1007501140d141c5a55007001c2507007020010548804680c89a0041c40b10f80752512000010b4122807008107071108540c0c03074051b55510080c22404161501e080b8140390360f0310540301030038100d60860152003008110304e0308000a0848000c143c00064070070358802040c080100854010000f0341d6542c40c840c508412401e402a880907116450942d0386110341150354800b40600351140c60640058200b04900c070b400c0c880ea17507400240c40000c004007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 224053363 1250 224052113 224052121
    0xc02120a050306090121060b0a030c1e1203020c0d290714070201050313031103041d07090501020303060f2709010e0102040501021c0302040e010b07051011120408070209010308030f0f 80
    0x4021607210040d407c0034000c181a642c1e40d021400411150304090110209080d0100c0d01c40700441d00180840d80713140c001081d031070761021041900e44d404d4400a0040c5c10525101545242c801014104c183c042c4903510540700c2040a80444600000c21410402451208003e142904425152030140511885901d00f051550000b03243d84401450812040c280c01c1003003050610908201d80c80c04040c400701d0307990f1030311980c40008441400d20056840e135440e070001044c903807280140404560781030b0006d60a5441c1c11381000662480c1007219500241342c810b407140c80404204145014181d605000380f84c60610140031425200d500300c005600d40c0c0108010880303a6800212090310047c00f01c001ca244030144c1344103c019100d00d038001c1284081c11800030500c50302d1800142842e900c1942103840048640009500365101c0d58040800e440052190040e50181800c3c05940a441529900d1618100b070f40082d480c0d100070703081512880310110420180d400030842080d04070401d03607042031b02c030300e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 224054613 1250 224053363 224053409
    0x304060f0c021f02030c09030102031008010612030c120c05100905070b0412020123121909030906110f06040506041b21060f0606020607090f050d03030c02120a0503060901 75
    0x3c0c282c014010b0742a400030000c0c0d4032241003000c0d25a1008018000d643c0c9003011409100403c5040c06a0140c40d4682040040d5410900d511092001d52649910b440c24006480301c4020556280b1010103008000340c0c3c002c0080d00c140040000c4000032000040d9101641c14070614201e0190005141d04070704100910403219040e0307114914030743c24600308034080e1040d580c3c00010040002007840134200030030740202d07606403004070520601c004070710000428100451842030f20300041e000740118000140a00078944a0301c19030312050200c0040b0f0b10040191641e41e1316021040700c007a1750b980c0118013808101705540860100034020601d461b580b003400c09103106140710301c03052031205c849194130410040200380c2c0c2001a4190080300104000c41d583e80c0040e4a422048540700b00003032040350042119264034116609441c00541407840c400c0182e5001e80042001000340c00a511400c2503058032407201d040100003100207030b650360751a070400b0405d00c00b1161060700100e10043c0c06801c10102d0403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 224055863 1250 224054613 224054653
    0x6110604050334150b03031305010f05040b1902010c0c0c090b1305070806040506041a06090402070b0702030a0e0108130f11270f090304061d060304060f0c02 69
    0x5603d044655801440d40320b031084050200819811501540107912400d00112800c40b00280c1500e00050100d000d18508150300c0b80b107800d0f041089040300403018040c0d54860052014030b03981c00e0401c5031031300703848a460001d660050011202801030000c4000541903082c022400c00400e00c0c10f04242200c140d9984541038403482c000d440e1940c6e600c5105503242e58034050503c604001c614800c100f00e0500407001804140100d403003038007490815011802030b0415219010320040c0041c1000001c41003d41000480c0d400060015403003a002d000803c00b20344207404181c00740c000ba40040d07030b4038114034001404211001e110541842403602c00c1219480101107060b000c2a4400700e40c9900d60200e01c1e121110041c8004141e42202d0f04840c840311403110800c00290b9010b001150341590380e15101403404010742142c0b84409508280002c0001c40c2c091b02d2042150306180070200d61400390710340800c42540040750305035000703600c030004074189440302e01c0b500c4ac00e0041380c030103009500c0c07130942080c00d81 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 224057113 1250 224055863 224055877
    0x2505120a0507080f040f060806030706080c0f070f121701120320100627020906120703090605070c120e0105160c030203010212010810062105010b09040309061106040503 74
    0x8201c001440e4081c2c1314104121800b4000101c4130405045c1c50b20001400c4800449015000344104d400c0810b41038080c2d00ca885c81410241d40d40c0c1d24100c0740d0f0400070060b81004804403404441c0300240c03400907030040d084a03102c0400d0b03580c1c0343e117034110040e8400148006a00030030780c04002c0d0540c1004241c0c041320340c4521a150029082d0001d07100005039103026904040150403602d080008286614500040d410340b407081c2022608940d40704010a00328866a842203604c2201007014136841e10201c1a2540d01113094240064103c203103071541000d903001142c40000103021064401c00b002f98400100720189107602e0301110f500c040742c0001c2c1992203480c00803098040381c45040300400200520403406158040c0081d0340b07616042c854440c90074401e0040105c0da020f0203000d0344800909124200841e0240044520002049010862604c02a010540703965480d50362550300760300c40d00150303406a03220b80c4d13802c402c2600d40a0014070001501d6031000b84c54101406000102d41e00206417010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 224058363 1250 224057113 224057123
    0x1502060708090a020310020a090501140901031508060c0316081303050c030f1605010b06070c0e0604061508070201240b0310050312070b0a020307120902062505120a0507 74
    0x20780d1107030a000c1d46041d2104600035454807072140361055000e03454001c2d0100c1205619403680e2103407200019104600a04074009030b0388014411351945d507100703400043d41400304102d024140c07915032000ca0706001c0c00322500340e600701c00003041c032070030840180c110506490f0703d10f041080c904081044d0300c210764480070090104403010941d030003030342000d000700c4111500b003c01c0c182d514041092501c940781154042944d207546041107507035060030208100d540095000500c000001c0c1061504408086d001c4c02c05a001b039a034000100e603050041d50f02d541c03100c9070307511001003d00c5c048074000d082d1000e10f001844810900c030345e903a01044a0b09a00025180c00303c00d40341d140d544042c8500d2009195a0080b903140c898180080d13404880c803801001402c0c00740360100d410303542c2d04801000368441a28031400050030943e401184030102e901c04107100348010083e9141c90840301040801665420034649000c420b26481c0381040010000783c00700c5403d18086e14200355104a010b803540c0140200541 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 224059613 1250 224058363 224058377
    0x50f0d1a150d0906150305070302090601050705061609090e0a0b100b0703050c01090b010b040f0816180b150c0601090501050d300c110103060f060f0c020619080115020607 75
    0x10402c04c1c039810500b06841080b640401c05aa2030600964131039080c44140d01906950f40802c90a51041040b5000c498000c4008d01e95600c5006207170b41000d50810806042004135803002c6080d4409008407450504444018282e03880241800500c2ca0405071003030303401740020a410441c10402405545075a031701405e0080c0c42c1d501e110300c86c50151403c076800030000c1c1d54007800411140a404040e0040e42d480c15070b480c1c0002d07160780300d250742c50500c0d240344400c15044580c104404036105084101c2d40c44450030104014450b1808198404428441e4180c400408103000110030380c06c01041d8010140300c8030138400d0b54501004500401501d034070141c94001c50300b02c0000800740158001101e20070040103141c40d801188001800c030104020121610581c020948102d580309004400a45444607100d030180d603c0c011064942d00302e50780d81c40003801400c440035005a1345050161081c4080c010f9540070310078070440f00400038041608000d400d20503210610080c03e5001501c00c0c1d0001d17082c2007042c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 224060863 1250 224059613 224059631
    0x1802150d0603140105090f0c01020a080307030f050c0c0c030703122706020604020a0909020109150e0405040c0512030703080c030604110a0309020321030412050f0d1a150d 75
    0xc018101a42015284680d46081e0030403424055002e244120110b400b900c0c90303518200c40c0181c54000d40c1c0318842c0140d000c05604804504d85200840e003080542c02c001488004014010041c0c46007280c825546680200307492015070000d100d4101c000f4011000782078141d00350f540b03001c06003070045503070b0040108100d5a024002d10a103268140f100e6040c00001c4160754505c0000d41c0c034035003124124000c0d170b5200d0000400074000c8c011070021a40c141c440c55019814a01c0364002c4c44144d071000000c115480e00b840340c0c15100ca2003a1402140900008040c0905180c00d110b400305031828540c6043d802080210301095200100caa003003d48107000c2d0750359403104c500250190021035000c0300403000c00a5003e040d02c4d0194405107a185c42501900c113000c031001d44082a5000c403910726051b0250820001d0001054600750f075410f028141001070801c820b1035800340c09030304580303110071007903943d000720002403807413800d0b040040d0750121484034503800f4101d44c4520301c1c0030300880842c050b510b0318448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 224062113 1250 224060863 224060887
    0x8070609090b0d05150403030f0b090732030901050c0406090b070602040906060302031b270312070309030b06030a020d112803060605090f0105010c03090801060e0109180215 76
    0x3c180d40540140450300031030341c1264601204142903e041b00880e01d0101560b00b00070340390140c040c030f14400400c9204d090751800710030f075442c0c00d2031b0400110f00c90560340d5a40161001030702444e0022801c0652540b0b91901c1100c603403c403400604200c042050a00041000300d07400070a82065402c007407140e50700c4450034581540a800785801003038419080003000b10f545039055002d5880749044040c0d840006044403040441c500c200c0c00d011040304907090b6800000031007103044046408002c0c040702d100401c1190384512980180034201c0c0001e00050040090115003504c454000340d08801402a00b038030760b4000345103038489400050028411103040c0b05107a40303420060b03000005203000b201016446030202c1c815100c2c14002210306070b241c00004074140c2030040d04148905a40b1b8218120380c0d080400644041c1e50341d0100702c082184c24180460408803e004481c0208030038250b0200c2035040c02d80b00016102d4903590100346120784040e16006d60f60b60144021a0200c00d40444c1c2d40b00205919 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 224063363 1250 224062113 224062129
    0x3110d0e1629120a050613062607090501060804210e010c03020c090a06090e1f020c120a020601090516080f06010c0609050a03020d21021b0f0d020708070609090b 71
    0x75900f00d4078100701c108680d51080707030003039481590200c0b40c0e5000d2409481070031044851178041d200d0f216440c10880c42a030f84d11400a41a010407050846aa8a640e017050f4015640241c0044000400d040244000c1003035069001800c0540d4514135001d100f1031810040c8140d002c0780c0a1030410848084c05400d01d0b0081c804001c0d03900b80501614001d10b8001c3c01d02024100c644582c412451811007110001100810009501800e5000342140101c1d800780c1d0801075041344040c0c0d003c50003892006004078015400820f07080030309030041c141e5036150200410444000400b8000c40301e07a50800510341030761015000780c0c07091036082441082e445100040b43c80001d240f2004000d54a000c0c049401d00c2000140e81000e0340c42030b0b0031a02448900b80c0110b68051040c130140c1924071840d2510000a81250041c3c080303030003241503240c2c2c03149028824a2500030401000f00341c0d5081300c5010345d2520340c144214406440c1c00c0c00100411807618100925406c2284159501d42e07648a00405075aa12100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 224064613 1250 224063363 224063377
    0x305040c09091a0c040e011404180605060306060607020f3715030e0d080415021b1506030d0804050a08030108160918030f03110d0e1629 60
    0x810002c001d840d10b8940b1408812400c1c0011504103180001c8480340f85508413801e40d1080e070000c81d820703480c0c0500381a8980c10701d41010382c0242c90fa030102c440091510303d00003005020388000305030307414100c0a16007440c4010307200d54000d080400c109405625026401d40381e040081e034143c24080d22544c035800b035841c41d503004800c0707480d094400580c1000018910341c0c02d4554003c0400c0ca01540c0e030f5015001c480d201c41540131280c1200080700711060081401d00e074030071300800c400000c203810f0340c814400301c0c2c1c131203190080004e4000081d130000315410800f11541c8181014800900c2c1402c50002c0e0b0b560b6211880d4078100b041460010f010000e0174080058816031101d6080d40300d50311481c83c140c4881200c1240f07000001400d4001407102902d0141404900c062000c4140c003500ca92001c40b00184e5000890341030648459070403031140c5146004000c07081c40040006800113040c0c80c041d0411a00130504000004280760a1101d100035481c280b17200c2c0c400407205555245a035000e10454040c0f80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 224065863 1250 224064613 224064629
    0x120f0402151b060603070501090e04050c0a0f090b030c010e060c03040b0f03060306070c1203020f09120303060411030411010c051006030c0303120c120f02070c09060e0f01150305040c 80
    0x851104090109a8000d034000640c0d801510315513681c82062554550140c812103000951940c010040d0fa40741080741070304203005078151a90200140049540d495159211030782070303040610200070f064020321803c0c088141c1100a00309a40350b00000070003804d0103030300c0f0510030180010315059100e41081100e00410580350407940300d200c60350030501c0a401c1107c3ca00c1c040c2c02154006401c091240c80000c445645c0420710300080240e2001c1140290001100400082c038200640c846c199994a0310705590a00d50001710365a00d0402d061100b6240020700700407a0100500510001550071889003920103c01c0c40c0c2003440750750508219141c88944401008401c1c03411401105001400404c6e00640740039071500391a80301c08521960480f04c0998081002494880d4141c51194841d041210303242e1191740c0c05400d0402035150b5090140304c980c004082c00e5600c0714100000c00d0421540d03540207841e0000c00c030303181d85086c2280c130035260f0700c1104070105540e440006080088900766000a00408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 224067113 1250 224065863 224065867
    0x10c0b010308070605010803030c1207030e06040c14030f1c02012304030806012f071a120c0915090612010b1c020c0a020d141f06050105120f040215 65
    0x2802d01c00241d5200035810fa61890130320002090080002040740e009041844400c3d15145602070701100350223002d031807181010303162002c3d0041c0b10720030002240254010120b0540b035600e88020304141803600000c0e940281c006440c0c440f8000e2002c2090350b0002c0003034284503140e41c2d00300f03000c9005011a0f0868105030300c0c0302202c16017800314003000c42d118074443c0d101c0c07104940f1002d00558881c2145101032030b05202c403001c0c2020f110300074901c000d40e8015003012100380340d4076050a520900d081171103100e014040481e900c04010b41c045046900405040752403072410f840040071511210f160741b005806444006042c41036a15130324115080c20701940100000b03035868090403403490f0302c010103280c1104070005013003070b845103d8070841d82006513102c02808102c0c9290b00f40030032090614800c1d503980c64400164042030200f880811521180d050b0054413000d03043c1313191002c0b218142c200c07504010081c800c0c41200344244100c1508806a20402003443c0d0b11440015900c242c00d80305010480c1d80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 224068363 1250 224067113 224067119
    0xf0a060905132705010e060417090a032f0f0a1e0306060f05010807030b131e0218010906020604030509011d0d060b0414040f06051801110405090f090a11010c0b01 71
    0x701a4003018a100f2002808404a5401b1041e66444140d80141c400c03000c00e4080400c2d502c01d203008005000e07001d800002819503a8a03008140ca04078007250003e00c40c25460b03d40d01c03800b440c0300e80404410445440c980303050038101040b4901440c0c0207040320100d0001c0c1406000c581d070f03240c8a0013190b202005014182c0c6501400c00301100f1841500c0c007040c641c4010501040c002d000794a24101c014140140c5110300000300e00241000302c5510341e0b034040d0444000c43e600c21500040500c2c0e1500315840e5180c3c81e810380010103515665100c43e04642144050000095020040b129848004d00e801105400b691100d600300d40702e0400b426a100c400c0303210041c1040129084035040b0001105d08026151845900d00062042220020000410590b01000144950b4012034102a401c2d140a45092049403040c0c00c69030002c0522981800108040040307181280720701e07501c800c881140d844103040204440f50785110910300240580008031490035203074800c1d400d000381b40b5045036a01d80c1705d583d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 224069613 1250 224068363 224068421
    0x30f14120c07140102010216080901030204090614090c0a05030103030e01090803120106080c070f1b0510031407050a020a020f01030f1802031c0801140d140c0f0a06090513 75
    0x403803481a045051184100e83c40e40790b0062003030305e00c154400755440c0c1134400c850fa030f0740c4d80c07603440505020f043c160309001c045000700c514451000a08152204a86000c5440c010058010001044040500001c21846898503841130959045035410304108043c0d2004c7c81c01603440300c0e45a0049041c911020481c025621400000035040b65040d80364045580c9038207004030810301c03c0b020090030f5282051070700390005070030107004039400e44001551050261900d00113030310154001a80c100180d203505c075803a041250300c440340390804442d00b0000d01d03104090348080d4481d000c241c000391203500c80b0f00306200c169020303411103001c07024081d0b010000384140980038904242c201000364040e1080122251300a151090100780c410700c952100e060b66880d0129404218a44542c4550400301400070a0000b900c0318000c030100604803005482010130311018854940a00d0091500c18140c0d8041000003a03004645035050f80c10580f0a0068902e8000b0b940002c1c0490600302c500c2c41550502d504060348d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 224070863 1250 224069613 224069623
    0x181403040905070e09070906020d0513050a060f020c0603010e15011739040e1306020307051803010605090a3306090b03010e0c091807050c0c0a030f14120c 68
    0x45412143c1702000d880c0d440c8201c5404109015010140e4084002c0404042c00b49019046045a940019030019120300202d0100c0640340e2003100803031074206040048a40621031208040420740b40e540c2591b24000300c1030b40c9905c0103840e941443c0194081e954150340b24103001c413920441c0340009969410200e403400145400281d14a50340703c2c6400c1c0b503641110000c540202119a000c0201d41407a082102d000e401400c05008441e541544480003400500b82d4009940304802d00c3c0c4640d41c455141c04541552111000b04440c130a034034000d8103009559034540c41ca5044800b102000840119031031210042c9428205407626981250310580400083c000b140810341c0c0d500da64600c80c0d166169a4200180000e0103540000502c02c80060006603130b4101910704881c0003081100902030030700403515140d00556100001a8000030b00404a000030498022941d0041c3d0321044041e25645684040c0302c2320b00c0d8010014241030b025045811400c014400d200c3c03c1054080d40c0e10711802c0403c690312 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 224072113 1250 224070863 224070887
    0xf0305090d050c0a05040b09010314030403210e0303070b040b06011b0804031e05070e0c040b0d09061d06040206030903040b04090903090906060e01141b070905060418140304090507 79
    0x132000040041102e04140c0a03400c00c1c0180036009410b180d0071907655401d0803084194880a40c4020b0000002258880c41031241090304103000d4091502646002404011480d007001c2c029842000443c002820354941d0720750041e0030080c440f0198660000403100c0740c407a2030010b001c0c0c0c0d40008440081c0140e18004104503032003012904004800d0b4034120b01c042c2100301c00a42143c2080404005203d000d16100d07500120880c0854603042c2c45003a895840c2d080106144c00d0103035a00031202c100315051040030314401c2c640c202a00307225030070307018695107a400074002400b805001c404a98012400c001b51005898a00c40e0140c81c0d94841a001004018017842580040c5503090000395140180c4314038001d696071550f42d001900300300801524050140403d40051010801c058000c0b1919141c4500b07600b02d0400c0070b894102d02d084086003d0b100040c081030300c124501782c020600c00c0b015207000c003070059000300300040c007000e19880c032402c60040d6480707007810310b00703000c100203072a41d21180e10605 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 224073363 1250 224072113 224072119
    0x312030f01140d0308041106030f040302070801020c03090f061b1501090506092706011203030e030a020d0f0c02030106030f2114070203011d030a0f0f0c0f0305090d050c 74
    0x22503a620800c070b080d18510030407041e800c040d06034071040110f4800c0c80c00d203a00c18001c44100b000f0036040c0010466551081740c450020802540c18081015410b000030001095148002d609146034a130741181c40c2d2240101c9a4030904091030480c555454100a41d000171441010711000c0020418540b9210844203007140c1d00300031194008980003042d4882d0600564024008aa8684d034011003200184a11804080d01106c81c0204c43c1002100b00b12040c040c00c0c1442d06102110480d16002c1c054610f0316504400541040c001510343c164001a800c00c10401850f0400340e0035000e00040e1540750b00c41e04069055400c04d00c01001b8403940c5184d100c0901d21a00c03600c2840c00200c005040342a000081e000001121035007000c00750a5103101414440d80001d0000031083c940303e0200034607040e902038060040c1c00119080490b0394020030004911589800c20484080080c003000308616100c400041506010483d40018144100150f0b180c04401500c484000100c50030025030783d8041100d04c41c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 224074613 1250 224073363 224073391
    0x31015030c0e0607060902030a061b0801140d0215030a0b28050603101701090303150308160c1203020f06090d0804020d0303091a010e0c0301181a031203 67
    0x2598824411118440416a20701014880b000e0800407940d01c620815208983c40d08070500150b91705114405125101d29400a01e080d0300d101120300344100030040c076003132003550001000070030300b440320550054100b01c6d41d99804480701c0c400a05001412400b0254140c400701c2000941e1800b5880314498001c01c0301c6a5500415040e0108141024440c4505031100109001c1100d402c010014580098007000d4200300e141d03c510b0750140707002800b00540c0407607441e4a0b10740145a010310406e01c0b4152903030460303000d01e81562511001849845207596220003000c03500010311803007441d1500500342900c5090080720765030500940d02e01100030758520602550002c201d42c11800a4030008840303664403800200d40e156000c0000c840c924000560505881c1c1a1910004d0708500e55181d140c1d800007498a4079504043d10b030f00300e68900501c2e43d2291181000140817203416001c03100d0203000b0760100441e0f806826103241c0400707500d9000107a0548100c1120b0362041d0b107071002071485064449980c0e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 224075863 1250 224074613 224074649
    0xf020114030114040c03020912010213090501060c1403090d030f11030c070902090a080607050c060604050c4303020c0a0311090c12040c031406150f030a0204020310 72
    0x8144000c0c0705202e9031120030030b00361991303040580200c0c0a0490070705005013001d0280c008a400500700300c0307040c00c0b580d40c0011441d0046a0841044024081903107040180d9810000040c04030750030840060402c14080c486090241c800308116907907100041c0604050614601d800313001070400b0800c0c400401e20410041900a20020940348003103800b0000b00440351500400c01c0095020158454019084401c042000780003081624003030321032036642c0c82d0f944081e462070354240540900128842d0f403d003424840d4000c5400d0540d87c001200c40b440325040280440348110180045010781c1425554800024148000b030301c460500718042c1e000d0b80c8040880300d0070031034032080900000340703100c1c1c07041911040760401c013200e29070005420310304a00d4202c8010040001140071602200d400d00210700030f000300301c3c41c0048100003103013440c0100114108903081e000e00040141d402030060718000302032031603580c00300602650320340c001c1c0085607242440d05183c41c08410f6802400604c52004000b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 224077113 1250 224075863 224075897
    0xa1101110606011b0303020c070e0403090b03060a03031b051005100f0f0308130801050c0405151e130302090f0402030c150a0302030c07120804020a0b0f090f0414040f0201 75
    0xa02d1080105948005582c2401c828144200c1122082501017507404d0206803113003402048448050111115000a145000d240c001c00108503500600c244020030300034004642c0700d010510040c2c03941030815000b03015281404007000620460b0250180c030038a081c4224154440c1c0c0320034010103134010424403064503035031021403a92492281e13520030840a1070030000729454401500707500d481c0208480189944031071003401d44406907010401500300040400070391809140d01242d400f4100c01c068141900c0e208051b50800c101440d541034584001001d20500000040503c065a8000c041060364200702e00c07450882003080f18100d01034440e0428864140c40c01c0000d0340c0f641e02105aa040c50002c841104901070340001d00b007a1310000c03090100c10005010350390300982c2030a6950301c000f502d2600c1e0040000c811780517400740907101400c000000000301f004048800e2001c0c19985841c41e0144400410b000346001c10110002c4080c1e00148000c00111859a04a40d4001d0780d885407511051150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 224078363 1250 224077113 224077123
    0x81207110f030706050907080708031314030c1912081207140304030509010c0f0b070206010b0903071e0306021308071d130f060606170907080a030804140a110111 71
    0x703450455005020490000c1e00c29000558400c002d20140c0d24581d0b601c4100d117242580c00d030408515500702068192440590013080002840d11414081c880c0c0a2507000c43d84900110007660300a83c3c1c07003a900600c400f851101e91009004041e100c1401d000282000c40040d0464408900300103450700208140e103204181c820080c00040403803518588884e6029104c80c1e224800490510149440100105149014040c8403902803d107010640c0703414007000741007500581000000680c02e11420100391000148081550282101c4900c040740403000c0006d03142d0190301c002c124900000d141d9518644200c640421644200203c80542c3c2d125021403550f5540c41c0c699020480030340740095041d944400c00d0703030310207030056401d0b1076482c07490348449064030119005140840e03050400100341c070080703a0100e07610000070006800071034209601c041d00d40340300d0310020303003005004000b141c248100c0780740340642c0d0f50010044860181d82460034070080d401c48501d45011403e00400d10700c0310800490 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 224079613 1250 224078363 224078383
    0x19030b0d03020d05030a2a081810090303140c040314060402060f03060112090507081216030e03160f03060b01030207020a0501110a0b15090606210a020708120711 71
    0x35041c03c0340d80300f008550030340000340f0300d00149407205111308851006030b8110b1070040601407016400c0c41e6110000e4809100501007c00c000441c3c112005090004501c0b90760140a1040100300c403941d90a04602402c000c42100c3e0a4400003c18401c50320010802881124446c000710300c0c00100003c03010351202c0b4120b40283d003200c0304001001d2482d443c1d0340119440750050400703c0c403490300d1a4001040700d240d960f0840d0264042d8409101141c402c008030410b1070b400c15142072521850070f09000c10040c0c00c0000401b4010180b611102da0b40d414411403102c0409200040e074210750b00c0c1468010103101d44010750710649002030b5981c00f03501c07a0088034452a0094a010504c500d0000110791110f21a803100c00300d070040e00304110008280c01c1e0010b000d060b1001d0031405503128102040135199014004501c503010401c03841c1c0c00180162000b61110103408040ca496036640d20490f800b0b480307405030040180c100000c0343c00800300382c500074900416a99030380582046604080a50b01c02c1d40f41c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 224080863 1250 224079613 224079617
    0x2010323040204020708040b0313140c030319030605092401030b03030a0807031d060a0c020118030819020a18051504090b0402070803011d0c030402011b02011419030b0d03 75
    0x50001000b5090540040c0301851046541d146080c0c0c0d01d5401c03601c02d07002914a4001c0340380801c03415003880b0000b800020441c0d5818080c00764072031500c0000c3c2c0e4034440c10783c11510380c48003e03864030100c6010798041c0b002003c01800c40c01051030441600c0e01201e01140032882d041041030010f103415442803042c40d441102c0900154034101c818030b000d6070f418400600ca50201071329600304c0d030944819280c80b901400301704c60041c030071402c01010b0b80054403014030140c001c580c9028140d020542840724080106501411300035803940740d0303400044035042c40705038000d00540002998000941d119010114140019039401c0c00780751503408100b00d2824131031404942d400240418046103c0c01d40c414100c020005000503e04031150b5180b1032590400d0303001c116101000c52144000c20707405085c1c0c591110402d4401e628501e0244c2c0040c04d0101c0c408071410815014015000c04c5901a80d10a0301a0095000881d181c040341210f140003805080444c0300000d045c1030020b003c3d410071000640e42c480d495 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 224082113 1250 224080863 224080931
    0xa060f06060503072d020f101109060a020f010504030806041a0307090e07030203010c030b03070f030519140105010e070908160b0306060f040603020d0b0d030806100314090a020103 79
    0xd021903544070300301c1503074514100700c056200005c0e00300344d0710b000d41c0060303600038282040d00c1c000e145003490040b00c06c4c005650306040c00b8001580070081103600c0da44c2d04542e44e542b5509100e104a16064411050340c0041d0318020a0106240d000440c5601c591000c6800344140052100318400d1103006060726501a44080400c0c4000019030b040039803170603e0402221056603490b0002800c4d2059135155402081c0d851804401034141440020007034101c105110064601d0340d44c42c1c0b0307580c81c40e0241c2c2c3c1c00100d85103242c08080020f4100265001b141b010004d020650f124004000c201805a90346404940c0004000884c04808240030b600410325a040c0420246410801801544001c0000b07502c02010084840740742c1101010b84040d001036940141c85101c640101c4007101c8841d1041da00c2a08003401c0300300043d40c04510356600c04800d0743c8000e21440c4042066018050454400000340051810408158000250204100c1c001da0302880020504200f03140185032841c100c1c02c5c0b000320b03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 224083363 1250 224082113 224082121
    0x40201030b031f06030302010e0601031235010e06010c030804020d11030601030501062306180a0503030c1c0305040b04080a1709010f0e03040f091a09010303020a060f06060503 77
    0x6036100c441c0810014098400e200e01150f02c1200d401c1c0d5901e0b00c0003585a40b1388044c418180c1c240b20318a01401c842004141c0c0e541191180300c8918810101501006000080110410300b1000d502c0c1c2c4c810b400b01240f0503c180380e140307030400c410b000b4014841c1181e8940000b03251076100d10740c00c00c411500364031820004c0d2034035020310120108000043d1400113032851050300d151010445107000794040e0000098050802002c003659401046402d00309180d403034183c0405a403000210303200b14503030800050103141c0b0040815481c0085901c081d1381804045100d00711124007140400044185110340c017483d1140d62000d408031141540c0143c4a21007a000040000e401c1d00020400d402041c2861a8081c480d280c45041c2084120340c4040282d442d01e402203600c010b680103200da1502450086d40c10030307040007030000c0807184503c13400300440d40b102d10501105101103a00088260041e20f0081d040d80c480c20302a517038411403c4211409850321650031b8075985144a00000e071082039031400d01d9501c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 224084613 1250 224083363 224083367
    0x90b031005070e0409140f0a0311120d0b0f03010e03070204060509040c0614190c05060f01031101181509030b0c03370603050c13061a0705031c05040209070215040201 73
    0x30080307088440a00510030380e21046c504001c003109408229000b0160a00c00380307070060020662035003134451540880080502111900c01356550140f00800028404200ca400505c140c500c885600b43c05500e40200b01c18039000110003005158005d40303050054070760f10014404803e42c21030300501081000282031003a503204409104407080078103482070900f0846c146580084a1080c07561000c103010031041410400d003031014941c050800020045190700d16280c1c11024000181c4103410084014500004821b12402e41c102400c0380e1a18040e402d1040788010303211003410f0001ba52100001c0002820301d0300c01d80704036485031b10b4801c81920b00314800003024024901c885005d070494058051000e03149211485810000c1d40540300911420400d40240200c000c503806003603e007181041418800444480c15250044446405403640e402c41c070b04000b0301358080e0108285949008020300c81041c44a0303000309004600031a140401500d4120090341d0310307000045140c0001071540b00140140d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 224085863 1250 224084613 224084621
    0x30304092012010306050601020c130c050d02220f060905060a0c02040906091502040509040b070215070201022701021e1f0f0b010809061605090a090b031005070e04 72
    0x780390010a03414021600c1e07000c1055005a03603956042001c101c010800d22a00d4040c00b40c0010f030a0003d00130350320081011031182c8050068888130181c039204085680f510800131507090800c902001c5444001842070120500380d070040c400d00110b81100042404403111703103404102e0b403043e25a05403603460a0140b00e02504080610403d1203400c05003074000d40c859004400c002d506c0340c0c400181c11403603481c0180b000c48180d102c0c030f2600d61050006011585650950503002500400e540c50f0980c1e4030501280361080855040605200300c7c2e0134482c1054054029085042c855a0b8002011040d01c0d0940f0740342a00c2e551843c01a88002d18004000d03002c032a020b60301845e007100351165040c1c40c584400460301d80b90140800980d40d00041c038100492031240070300601003443d01110030306140343c0309656a0b20107000210b6130040c4889105900740035038210b0310f1681c0b01800050b43c141e514003104009140100c0018040d0040d1907103036002440604c0f60340c0c410481c0e529450340c02c12440b41880018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 224087113 1250 224085863 224085881
    0x6061e06070f29090c010c060905030a0804121409270108070e0906010e010302011419050324060d0207050f03070f1203020a0e060c15090d0f05070203030409 69
    0x300c40200054004681c10301000c0c034449000b99401d44038110000e00411a006140d6030b40441103040c8014071061807008a00101c1d812070900e041008030301c01c1c2c14034130020071403544003c1983c40000760904409400000880c4110700444515206414000c030a4900e1840f5421401d4461400c1040001d0b40c034001c00c25102031303141042205c07072041c1804980c03500d050003a00584e01d03990001404008420089800c1940038054070040c1c021342d4944100c80d0310000f01800700078144007403019480006a24030081c1c645a104400c5540040122840040c295030700a0340e40c942d0a181565400420305d080700c40c00f032504600078007101d1070705020001d00317402900103a07421549402501e04100102c0c0041001c0c244032400792854040c8a50306240400504101c0e401c0038062500610039071100c280c006c4290043c004d0700350b45036659440b84840c9207040c050034600d500e00c6080d182c0e0503c8100500020000c0c80b00c40c440e1104105c00c40b02d03c0741503880b8020480d0003075041d40104010320510a0f036800072194 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 224088363 1250 224087113 224087119
    0x1090909020603160e03060f18070302060915120c090f01051926010b0414090705090103091104230a06030c0510020316032303060609041a0402160c0806061e 69
    0x201c0f00c02000090502800395080d001c0320154000707200d601c1c1c0aa8403401c0c280340b03e00e0002d010462079a07001c4dd14900a207024984609501e540451400311401d00b1903002e003074070300e448813801d1811014904241d00203600040c01191144a07428031540114112203003070b1519004503845918008048805880d0200e5500d40e041c01c64001b8000200d6402015001c1c01c03030b6a00340c0b074803a81007440d000e81a0303100300541c522454031041031200761a044011100c50890038038004c52101218100f07203c0c0c02250071142030308145010210f051049c0b042c000205020841d007050795803504e0700741c0c456056441e0f60002900190001c00304002c1d07854255012154547d01c1d00560381400708400000360003000050003a0701240c600b081c0c0b00c0341140d100a010b00d0701c0da00e10703400c90b0440c1062000b040060048001040c01980e803031041e03034007c801c804000050707400014415507885000c0b41c0c18040110040350304542d00c2903011004101000c010070309610500d0050b01c1c201e140c00140804081c1408503400c5130707030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 224089613 1250 224088363 224088377
    0x304110111070602010b090901060e070503042d030305010f0f090b0d060507020f0f060112080703030b040606030f0501050f010807080703090506010303091e060e0f0102010605060d09020109090902060316 89
    0x780c03440003484504020425500002004a401c00c02d10110090041c1508401d07490f05d001032000c1001541d00c00e070400164a4040c1d180c0e030b901c1c41d0030514801c4003094440100281e5000b1038050b030341d44c90a03400700c40c800e540601450740e132116650401d09041c02100b540c424043d00c00c0c060170700c49034414a0080b10080240c030b41c4440f030317845100803107a00355400b50044c1c00001c04014000030800904d820007003624000c141640c50541b409584258503040100200300010b90310707040c5071190b0403020600710020000c20100ba175039000a07008002e00b0f00000800d604140000072545004002211014010785a03400c0d03594917050104c5040740000d01d40c2060581d600301840105008012a0380031718425240c1446860174600306079152084200660301810f64807070188540341d88401649103010095840703400d010070240060380035004035001a90818004290f407a5104402d0f004044568000c1c1c171001c03051a201c0ca10340054400d50708020350009402c20200d105010b0840d5041458002454466 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 224090863 1250 224089613 224089637
    0xb0301290f01030b0402130815100e07052b11030f0f04020307080105041208091b060c070504090503091005031506090f030307030c0506010b041a0f040f1206061a03041101 75
    0x5040760440d0054110195a141f814415640304020f44032052010031b40b642506e181c01c4a600c0032980e40c0303000b414440c0010304081400309000d8005d480355020642c42c02c641a42c00100c0034030015a4011003003081c1c504001e05007252b5485c5604072401003107501ca144800c1c1da162104200c05900240040313805101d00500007c24107003c0c811540114450350419030b0400140400410034000a0a43c0d0038581002c1c45120801e650184c03900309070360b07058440c42d80329041114000c1c01e01501e540005c1d085800e080c10041040030100c0100010602110450903c2c0ca4000040701c142c0011180615680d4070420503484d5843d1a00181c4140080201450400109840480d0035034000700c504801154003217000301e040000c1404024003402084031002e00f000c0c501500a9840c100310014060380c450001021302036121034078111b5024000c6049030641c000e80c2c940039800b4240c0c01500a4414030704c1e105010945200d0100442a0200140c00460458030f03191500048020303008039007818441100000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 224092113 1250 224090863 224090869
    0xf090f0509150d030c030e09280e0703051f060f060309050111040b0319050c070303020c011103090a060e070315021602090a090308090105060907210f0b0301290f01030b 74
    0x140c1e1000c0c0c0f00755120081c034a411b00c0c000c1e150401440019104640c148100800d48510f25402c1131240c403080908036000f06aa04140010180c0c4542c846245c002c41401006018001500c3e5461030340c4154001c1001c0c411040102c00c54000380035403c048000002c041091500c2a0403c04070140640000135480034002c040d41001d0b80613520a0600c1d89010040114100841000d00240800d040c0c05010794502041040c980c1d2050301d03001000d0540c0440c0032000410250b102c440041141016a6500e007840f00e5035a550300001801100e13440d05288081c00720b60000702d48101100e0348071384101644c68141c1c00300c0c07010b500710000c8809092003c070541805a61001010b900500020310001001c84507400e004140382c00040401041789e042400f071040b02e440390a021517200e09640f6044801d140c011f0422004d00701080313600d52446080c02ca549012101940c40000500c04c102c0080000c0e8007035102480400c0080c0c81240c14005040d818454503080015070405103400514002400000b80000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 224093363 1250 224092113 224092129
    0x2090c0c1504110301050108060a110c01050717100b0904110d050403050a020f120f030c0706020a03022a151f030c0918050601090f09061a010f090f050915 68
    0x80c01091060070301480309109280e0900078148400750002d2000b507041a94040e0703104006040300d018140d0380c0824030312036005072054a8607650b61030020700c02da06100e0f400038100150b240403400d140c0d0341c00000c0358a910101d14080210344803908402d05180b400e1040100030101d003800c8100c280420498685040c04604c03449100714441d03219540c542e0741d4400d000303142c0307000800300f6001a440ba03040780c41111440d42c190307001c2c601648a690b5807556001c1700101e10340105400104480d0010584107900780d010380281000c0c4604403c0326580c4d04150042050400e01c56066010b2500815443c2000740740c0002d0350369203c8240c10300140d901c4000880851188155031080e00c41120040c410300615400340200760303135074400c5400d070341404040e0b450711512541c4c18458130004540e504482075198039141c020380b072015007000c0c0c2004490a010304004406c03040000a034000381c640d010881c4d101d40100821410741d8110300610f8201070822082c0301c02c3c40c0300a040c030010030300c600315100b040340d4849007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 224094613 1250 224093363 224093383
    0x9040c080403120e0a020d0201110d030e1c0804151b03060906050108090d0503090c2e050f09041104090e030c0607020a020d0f020f040204060203041d0f0402090c0c 72
    0x3954000500e0a401d00402240b85a200840494200b00c062400540c00094000039a41c0446030501184500c0c070068036254640c0034101414020110303a81d2449406500522030080340f9000e0f00d501c00100e24030401d210001904da28041384401000c200440d01241851880f0008802c1c0007650a00d8200440e5689060184000000e40c44000c240240700060154000a000030b003001071003800d01c0448943c03110040540c140400c42c1c04400aa1034020412440b114500302400311000e0300800d8803841c0281189107128500103610034102c40c1c2e1103100e0401c4903260081c1c2c2010505080b8000c0400c4040c249642082071080c03000d02011480600c68440c600102c065540110b54980c0c0ca0740c18070b0f041c030f17a004000c04255002441072001503194806840c00c1c40b135002207001108401ea10004007001d11301c1c413941c1c1c0c1040c408a00456800c1d000402481a65590030000490461751154140100702c00c40b26081ca450020020070b0050529840c019084484901d03041c3c01d01d050b2060f514035004108ca = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 224095863 1250 224094613 224094617
    0x5010c0f11151b0d1704030e0a0b0d0b030c0f04200a02031306170f070201021306050405030c0a030f030305070c080c060f011502062202030111031005030708071a09040c 74
    0x1c1c0045a0340075035480380030003c103000c1c0034000000c0d40200151203256004e5405010241d0720001400f058030a040d01c13915100001d240484882d240e140001841e001f451036400c05900c0c003034250005243c0016441c3c1010760040618108256100a02024020710a26400003011440304212051000d6001d0100700000303500039502d03481d0b151a80c0d15000d04941c0520144402c0c07240b503207035130b00d44c0c0726400790b00c500070700c1d5240220386a00c10128020310400c864a2081c0d01c2412021850a074418000d00454400300c0480b07101c00002c00c2040301072030f10362100810660120103030700000790203a0000356100003c4d00341140710b090141c803038444c0ba5024001907125900010204148071400944060142c000034040303210b10490880080e5942a01918a10030007580e1804c10b00200800119070095540c040e0080c01100c0f0076284040341d542007518100c2c040a404003010a0f2410f000505404452442e001031003160b2902508100c60342e40c500c56508030140400030307414240c6843c0240880c41e0419 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 224097113 1250 224095863 224095867
    0x130b06090406030624140103150b120414190f081309050603010f090f0b06060405060c030c0105060613060e011218030f020607090314070305011103090c090105010c0f1115 75
    0x2008181176002143c0c00400504c20a0f107500380000c25499450901c0c5810a007000109640209803803c0c0034001030f40500d0100b100042e42403002e4000249503030141e407051412448082000013110744401c0c46101d005003da04011403c00810740201c075102071240200041303850a101e0404c003149500d001e4012524050b2543c0a00409040074420200b0010400000700003a541690710301401c0c1000140c040e00c43c480e102c010036019548e0400b00c8004000c0140b074103590700014190152030350091205400700354030300b100003226414100201e807071000c13005100381125818800180e5102c0d500220590411a0703608881e50100368a11440381c070000705a910058035101c6290090042900081d01002c641110341405443da0300f10b20100d040e240e100d030201d0947c1c0e260030141c601d008011b600c007900a40c00c0010690032090301d40015805001035034181c460324000f00c07090101d252400c0c42180e0004917501c40300c10205406002203501513100c2c0d00d441003203403007502c0000c418a0345008164048840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 224098363 1250 224097113 224097131
    0xb0702010c0c0f17042c10090902030705060a0f0207051c031d0301020f090907110d110f1501080607030e06010b18030d0f0306050a030c0317040f030f03030c0509130b060904060306 79
    0x41b08540c2c0d41500222040152039141c404030801205200c0c6c419140385a80710780c0400304554040c48800c0251501a001d03684a0071202c10040543c1e05000040d400342c0926480456a403c2ca010303421140c2e00d00c81095410b1981684d0304075400d940e10040d0755544100210b210038240d400780010318a90795071100041d00c54144408101411303d000d408c01d414130078904428200890b002c01c1e089030130180d50a018440e5106140080e00740980100344950310300a0700b500305026074000f40d40034180d840e0801140c255558410003941168921910300d0355907070080004111616442009085980d568024003080c0e035240d0001c2464110705035480d402281a210f5908640d070341c5071103040000c0604031090a069441d45d1900c0e02420b005003c0030345154000714407112528040b80840b0001c014080080c0b400b2a640e051418945079a000c040780024146800b0500d003a10601c1036615209c0002c10740642c030844a03500c0390003410407a480c50b4100c03d05002c1c000142c1e40b50710800c4011801101c0102e0350380c0c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 224099613 1250 224098363 224098409
    0x70815060409021809161701050705070807022e02010c020c0307060e0618090405010203010914150910090e060a060503060403020a1e0804030f0b0702010c0c0f1704 72
    0x2000c0600403072900010202603590300c0f04046000d5480310303405000342ca492241070706180040000c44034070a02a000003880441d042800c0f4207040a00d0001c2000b40c0320f400c01150240701e044000f50606205100140242c81c10300d10b40c2c003c69a400c4510150780c1d400352480c00000c4140065000581d40d2844c505d0061901400040d594010403009400d1141c1001009004502505040c0b801020085069500d008806d6100d110840380208144400c0c50280703481d030302032350090140c85229414111620080056602224000d4500c05440c0030711000700b50a2040b6180010054030742c0d05046040041c182815105412042e0302c140007420051510141840588800d544054000e80c411402c00000c81e602140ea41545603124441f10100e030004990b51156044424001d80442ca00007800410402100c0403500704920914100d4065034521000b41c1c02c13140e11000d0340021800e0258101c000070702080054498621600800022150311003040c0c950760814bc110f00207c29400c2092600c1c51 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 224100719 1106 224099613 224099653
    0x61407050d0e030921010c0f0c0b06280801140c19031d0f060c0406140a020703020a060f08130b0a090804091d0f0c030705010e030f0d0e1201090803040b06010c050708 73
    0x2500cc5041500002420310400034190310340003051070007510241901d03104010031f840190800c203d64607041c0d001c607884280d101c01c043c0d40d80180703241406205807800b0058801d800402444801c156a185002006000310303050100034441080200c0d4042010303111402c81c10f40031601e494203410180c2c500152508000d44c001c4648801040031039200062138040b840385da889407400c4d115914010080d500c004001f91000c0c0c0c0d074000140e040348007508000082803084200610b81951554507800f03e600d10401559000140200c8031081401082605d01c42da2280001d4080148544006551354200c1e05c1a20306102d101c66081c00b040e90184034044000210a05858001e0b02c0204000c15800c007039074401d48240300c0001c50071052141440344026056004c1c8207940345403640c0d25a0144013400411050401c01814038800001c0d03000d1010500505440c00200380c0711039078441d03070a041 = true := by decide +kernel

theorem cover : BRFrame.Cov 223920863 224100719 := by
  have h0 := BRFrame.cov_init 223920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 223920863 ≤ n) (h2 : n < 224100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
