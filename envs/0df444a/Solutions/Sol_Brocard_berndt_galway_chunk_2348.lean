-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2348
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:26:28.656391+00:00
-- url     : https://prove2.me/submissions/15442877-f28f-419c-8c9b-dbc3ce1819e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 422122302 ≤ n < 422302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 422123552 1250 422122302 422122331
    0x10151815051201050f0a1202042a0f0201060602190501020403122102090906041a03030d06060306090b03030715020708190e010201091e030903020303130509010602010e0c0103020a0c020301 83
    0x1450318845481d0803206613a82d034070801405641e00030486411515504081041c1c1c1e01000d80c44a0700c62000304081108140b4016512119620704541c0e06015000c9035036074142c83d000f880542c0c12255900c001c0c00054281480039542e0083e00f0140a90500c0c42c681840610401307505850107140d000640400d0b00021020041050054070200c510039003035200360703000e040501e01c00c840c800c0d24090b0401070325940e0002000001c01c1d00c1042c440304a038103450a0303003040d54140020440e01c001260009a482d05145004048441d29004056101c1c03030607500041070b070b0b000801e0340c110300d601c0080780620104409107240640a5494000c0c0340c20000f1516000d01410014042020f800710354424102030a00401282691120500900002859015011204081030000307180b1402414a6600540e482d404680345520514000c90b910894000a05c001e00c0d01c00c2a0a00414541c802800010344002000d501c41400361800341c1410350018100c00801e014804544e10076400030020401e10b1942440c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 422124802 1250 422123552 422123557
    0xc080c030a03020408070b0304050a200d060e010c0804020a05220c0210050a0c0c02040b03070806151207030b01090f0f0e011b09030c0e0601051b151015181505 70
    0x5484072030158560201d0141001800d49102d00c0e080381c01408bc0d40c0d01501d506984071f081000c02d40150304008210220398586c0a4800e40c49441250005901c030500c406240c00c50741041c50100030400c0460521000d03a56810318038090b148216800c02038040c03c1400e0102c3d105050701c540002c0c50401201c142e6898011078a41540c10548500340305555464030041c0850b03201c1180c04021400250059015007440d6100d030302500c101804440f0303159116030803180340c4042102e42c40412a113030310b14510310b402c1604150040d8000030001740086402e43d61814052241409940300316a9154a166100043c5170085046031000810401031460a2010305028024800d42e507603800841803519154244526111822030790402e4032030210a0920340780c04034400c00501418100513003070011a201c0307410b03401c0169a00400a000300143c501d1000c0030f18030351500900115031109550700810035204d01c80d0340020440005e20f0124250201c813182520b000c1c03001c0d040140c0110b400e2f01d601d1000c0345c10400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 422126052 1250 422124802 422124809
    0x3030705160801050c09061e04050406140f090c0307050c0a140a11010e03030409050903130b03010303080a090c0915170106091104031212020d050403050a0e090f070c080c030a030204 80
    0x90140361707074250424800b407244826081c0c111008004000240c0d49540008c2c81c0c55000c0340005140650f104009003d0314210342090310b9415191080485524000b5080b446880b4281c8520311070b8903000d050201c141c00300034441010301c880040d602424130002d101d0800310551140864080801c1135030b90b140e880b5031441040365840150301c0c1d190b107990300440002458940090085107010305040f5104007401002c2c01507e00381c070007800000d60103036840d0146800b030100c0601064036980355050040401c40041e0014003914904858040814521941c100903205c074005c012403a161106040c4459101d560700c50040000210031441c0d40300e0041d00100c00b110005031043c0108100b85a01c40d03080e02c1036100060442502d88000075200780520103c140c1485180801400e0014400883d000d4900444044000440c00108100280c4e04005c032164558800d0341c0580e00c503c1d0440950240c494050144c1d8203110610166504200b21141124214035421003925150048100f0143c0690031500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 422127302 1250 422126052 422126069
    0x101a0f07030806040e0604050706110712120f0305010506070206090607060e030d15050622030f030503010501140c0a17070204060306060e1303021b01090503010e0a03081006020601140303070516 85
    0x75011790011200150041c0115003100182032624070b02002034525861071407150005000e0f6503000141d0688086040c00300900542c68071114a031107400c020b0040b000a21810141450000180066100e41c0261348400e54140c86d0b19a46040c1c03100084c00c0341c090305e00014460360030001c40546800e4084094a8441c03050001407010b03c800c4c0d10381511110075801040d4010300b00384015000d41282c81e0040c402c5001458115200685903210000392680404064010910000040002d9607000b5500c4230201481c120450074442004c8401e922941d211101404441e6081902100c8851000c2103840843c0e00500811180703a491800c0d50262010f4480c80e602400b441c00000c1900c08030704a1803060503030541c00b030007102489601d8903001c050511602c50400c000070342c0208440e00c00f440303910140d54a03400107045440003454001c2c44240018011004e180b0540410000941c0009034903040d182c0d16101c400c40d000701500820702c2c5000382400a07050340f00d000346030034090070b04491050641d80c404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 422128552 1250 422127302 422127311
    0x301091a0a1415040603050307061509020708070b07050d1e230f0415090303020c0d03021e1b06070c0b07081302210717010f05101a0f0703080604 64
    0xc020020885140700002c8800350b01c0000054040e401645205001810081c0001205a00c0c0d4640074a10b41041c03804a80c15035583c4554003200c220380880038011300681c5000e500c5c000e025950880d150007100c0c4001c1c20456600e002c02c1c1c04900840c23381313841700f00765181000108030901d20341850701c1030546403c004d10300d0081a803d084011900c80d00103440c642c8610030442c2c030703104441c400c0e5020060003030702e1200700082c044d00c2d942128066150858003d07070340540c540386c0380000c40e8140050301980c0c000785441005104100b034190020207046032688207405032155600c2400c818620a410501d5885025000070481c0c4244c01003480803206020b900c1040543c1d036003000a80d0f05020544400e40f40ca40d9100000d0014a84242841c2c0206806506607200160480c007591521040d5049140102c1c05c400642c0001c0d4001d11030700796030042d9580140034a00b0140504820b0030703500d002c0c1c401c195400d90364444180354040300710b5802d944044401070303030b850990400500395181a00c50034456410b1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 422129802 1250 422128552 422128561
    0x9031502120609041106030703020c0105060a0e0703020a021c02030a080a050105090a09031b0b070f02011b08250c0209130302120c0c120708011103100b180301091a 72
    0x100c0c4207480c01c060000341000c1080d01d0303020410802c0000100100c40c0c800300c00016030802e171220741c0558028522900c015858002e18445c190944000405036400360404403001c02c220700d0780c465031b42e41183e114100141e0310428403800b20309058a20706042941607070001526001640000145100d00480d40c601140c2d40f43c00c01550295a000c2c840d071540511504041498034a55521080d00a807007810040c800c03443c3e14111500049604105950002030300d020450190f030001456a00c0c02120b100800034080144000e000007403001042d0005c00490303000041c00c0401002d8a0795408148a41142d80900c010b80000c2658001600490080e003950012034429039242070305c1c0003856455002b40c81e0348120300a00f621950420344100c50a407040c1c1d180c0001d107407a004c50402d00040c1c50740150030540c0c1400600d50030f4412801c0a1004228108100403205030883e00c0729060307580420700c1d142c0d1303220f40404952610030046070041d8154030f401c1d04501001034980c0303100700080181d02e12407902d60300d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 422131052 1250 422129802 422129843
    0xc050c03070b06040603061406040e0129030c090109020a1b081c0b1306080f06010305070b03101d04060b0a1421070b07060612030905011d100903 64
    0x46a815054580c0300303100310300009480310441607002c0d2015000250031607030b80c3c84d41c0c015580d4180c03481004114100c103200301c074102402450182c2880311300a110041160152a0b490b4000342003000c1d041c0b21143e80d096890b80c0c2807040c00d10703003079000301500d1403135850b4084c400c001e5002d0b05140001c200c1c1d0a440c2c042000440b1240c05c00c4036000080d003810450300d0045411040c125451000700241d8072061205580e5030b580c12a40b0030310041500041e100e080001d021320700001d96055609960040004000042c8002141c0050302d4021001e291030341c540c00703960242442d441d000120031645004000d414482480340c2507200320f00454091058202c03e6080c40728185c0640150828030000d852404514140710b83c494101d15400b8101c404402014071803642044180e42141c5442140001d4600c18015a0301486016202e07511400800d0511542c01030b00c510990321400d414001501031096183c5103c400e0404050009003640c0b109020408000381070a45900007100c1018000400071651907 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 422132302 1250 422131052 422131057
    0x40c080d090f060f02010f110408070504140c16020d0b06100903031d030a02100e120304080a170910020f070b4003080301180b0904020415050303030c0c010c05 70
    0x408500341442240c0c00c03c80200d8030a0050800b490a56403582d114400c030030194880c188030b001203c0490354446050644003801c1004651000303104500700020f04241d583d01400464009d035000c0941680c0d0060344440301c003144d41c5a40c000c0d6202074005800300c1072200802005100b540c0881e10000c3c6601078190584101c0307580d005c09030004184840c655030320320000282c03100e1068020116190503280e940040c3c5440401c510a60000e20b6500303110b145403c140000c0340c2d10cda0300d400a17500f01810f00c1495692020f540b4009021003540200161796420207800321010b41c60b0140020304000101a006540c600b0692181d10040c4588000020312050180513900d15891400980496008000c007070043c100c401c551034034103880402100c1c540c4420a011103002907200709526074030380d850b2441440b252000e10740100d0312181842e080b02c40650720004401e81c03241e41128009070519013490704000e028260f0704041e070144000000e02c0035017588907001c1c04050070020000d100c00d401a4400b00c1d00d50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 422133552 1250 422132302 422132309
    0x6010e011b020103112a07050d05030d050a09080a02210702030601030209060301020c07060f1e02030d09110a03060902031c02100e160b0901030b0105090117041505040c080d09 77
    0x2044011200030056200340c02482e0f40040b07442d4000e00f1b1622801203150040009042030a0001c00121013605000040c041113006182c04c9520f00c0d411002a1900c503100e2103080102c5815550703408c0018180c402551144d40b2494124460039201c00141402070754a5003504000400305c0b48400c500c1c0440035a0900300c40055078054060101640b07103509105060b03101920f09035065409011072030108400b0492030f03000b007405a03100450a00d103400040c2000b046010706501c0440401c0c00d05095a80000448083c5100c110300062075050500f007004143d400210b0940e0700540d1144000107024581e00034181c0e480c0224151b44000700c410344c11105442110100c180960401c01401f51903100d82d6000000c4024000266220110031940c1724221200d2a00151500d4102080c690510359043c400c3c008618801e00704940350030703203900018080c00c9150700ca40ac2400540c1000404000f043d08080c09459080f01c410700050520380782c05071030030f5014043c0c2c4a89100f94803001c080740744115100d00c00c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 422134802 1250 422133552 422133587
    0xa1406090114070803090715050406140d060305010203010b09040509210a0315030321050601050d0b0a08060a020c0f1f020a1e091409010803090907200606010e01 71
    0x2440ca0600056600900c000240d42c0740380e80038441c0d040800e80000040d4811301707503400640001e03402c1410b5005100c40c0d00002c84c007000400d010901007140c2119a4101c81100d0308140d80d01e40348042041c001500c00368000030140d500110000a8620a10007c0e10100c141164141f181c0e64501e0002c95451b4074500441c81d5101003040b103080007114420041c14543e51034031f000304040c8175040758020820740c1580704500040380c50700380003507949212003d040f0202e161201841075050247c002049400b80c00a1481c080340da44c10686025511000c040d001032040509495103480c00b00c0d070702c500940084a1898841c0516513500540002c0402e110440820160b203203a161001c3c881074000a401c10700030070b024000200000e20100030585206440d882141d981e80181d00d0800304074140440c01c8290050143c80400b0040c4031800d0040243d500380c2c0e9050f103011280381c2d146c52044074100740302c0c03200c4bd80100f17100742caa1110103404100da0b84100c500717072030300309121512100450b5a017000c101c4000304c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 422136052 1250 422134802 422134807
    0x30d1e05070201120e1e0a03080402010806041e0603211409150c010e07090c080a0c1b1218120b0c0405060c060a062103050f07140a020a1406 62
    0x26540d0261019180c0c60b40185000e05044501c413003000102c1d61608408503c0350700c82450710340074a15a0b070b4000600809003010301765420702e40e6805030030394002805c0241031201c2c05000982946641d40b1421082d427400741d103103494203144180c040040c522400207071012a4045060300480c090384000b0901c40021390b5410000d81c0c410310f55a100790b0000d5281c141d0210300c0d6292141d607584d0300c0000d404c90b240d131200002109880341259600d0000554000050541441c1c0540c0c2a83e410401e8150700804041021030396203140102110030040304609000c42000c04807500c014000b80409441415485440b18864420781082c2503d600949120f104500e001d101d0750040007818805140390000c454881160030951600005212508241702040d0158040170800c540c003c89402040000e0100caa0101034031840d00d0034000c451589201e000e802d0090001d00351000d0803244089038401504440064030f007400c08100340d030311856002c5040e40300d9218500301140c1c00c08900002010814010302c2d061 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 422137302 1250 422136052 422136107
    0xf010602030f090604090905030307271206060302040c0c12050f03040f02030a060c0302090a050d020d20090106030e010506040c021b0103020f0313140127020f0406030809030d 77
    0x2c2499010b0342c20560044410b100010300704a0038082c200301244039a002e1030301d82c6400f400007800011650b40000100785040220700c5000803a8000800f920785485c0d5101c01445242480000b400702680000d412520701644bc001c041d5004289440f207610562544e2003c105d480c004591134051542d901000d524100082030005a41c4495584002e2028040e40c000c01025103801d0100c840e1100760f5004070741c00044d17621580c0b0700642c81030050101240c1c1041e50000c1c503000f01c0c420140030079000780343d03040c402841d64501010701d418041c0048000d044003a990f845410007406801100c050f65141d6003000046001894103002c0c40c0401c0080f940140030703050310f0754041e04130030030203228160500d507080000d900240d2030341c0700641c07103040041c15034442c000941c03400e01d0314105031460104090349480040c86c2591140c1070344040d01e00851504d01302e00341807400003c800c3c03005800b015601914104002080100c001d0207042a40c004030152141c10a080b0b0082d90348c0102820f030407213007800404001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 422138552 1250 422137302 422137327
    0x6080d0806120f1606030e0c0613080703050a1e0f061a040f060806070203270114070f030e0609030a121e030207021e220f1409060f01060203 62
    0x36a440740c4010900840055450045420510b54036680081d50b0012540c07940070030501c101c800004d14492500b04040c800d814801c0e6140e1440c004014400c020008651a100703500061500c0074201400c1500e0389140c3d2807a14a0362401d4018089840001f81c840300008140300d180620800d5401428a075075116069417000020084104003144d180c4540c4400c005d283c40714800c00b0b100005090340000d885050110303031454000010100d01c1150300400c41000c91000b10381351241034003940203102e840c2420740c0300160707080b8169036030b41d03c0c180001180030b005201c001303030310100c07100e0181e180c0711043c280070018442d072840b5102555425034004107100d00021925407100c000104240303800e04183c40ea50040c41d10304c01008100c00c000907004501603042d40b17070010a940c11851040a2400315003c200f02007018080b404e002c0078505a185410942205101c1e00116840d940300041049140211801c15004000c16142c1c84658402c0d800000c0492100303000840c1a907420b50000c600b00490720071f20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 422139802 1250 422138552 422138567
    0x90c170f07080604060815040b0a021c09020a09090317070f020c0f210604060605040c12090501090c08030a11030c0601120503040f0603021b21070809090109020703021006080d 77
    0x83d034120313598000c0000d82d00014002112004002190f036882810b290030003034158017001c1c180a203858810042c0b0080b8a030440360200e04a004500b0200744a1028000a90031400540c4038098107030504100340201039001103401e4200311149004002d40e11940c20031900125152103000169110403107591051070646004884610002d01740e007a40c07400c1106542070b51500d40e28501c165440003042c403080202c18007405020348000d9404202c03075030080300010f0108010b111110401661610b0040074032900303420451803da0044107401040780d032240503d03525840006140d00166070507118941090340481141c04003038511f00200f40903424401004640381042c501102d282c4010000000e2034099440c24400a0403e610010f89441c2d02e14642d000041081145400a802c500c50980e2852000301407002c2c81307900c80c0403591716070b20240b070a0040c074499241e41c26441030307202000140048a0b50020003007280f0170341c21341e00088015100701e01980c0d11409540c469030004030805050300d215500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 422141052 1250 422139802 422139811
    0xf0d0608010f09030e060c0a080406170a0e03120c1b0d1812110a0e070c1e0b0a05070c06090803010323150606090d120207051516030203070b01090c170f0708 69
    0x80d0f61234084541d46a82aa5103e85d00860100742d034203050200501c0d03107190441d488008100305104400000004079244e200e1205040d800c140c0c1140410724006811042c0d500030070306881c2504110218214040ea40c1030508039010000781c21920003544d01000c502400101c0345442606145510140c0d40d01441610f00d17002f0300d400518003200000c0c50101516244e0050695480381c07074005099080100421055045400418120148020015003d1000943d010300d010100050fa0340310342204540e01d10303842101411150400d01c0325002e0201c06c0001b94126441540c202c3c120342c1e0782080749428481071481000c80ca400030445090600c1000c0240c65000d00c000340040c0c0b80c031007404001000242c0245007070310052004202103801c04e40400c12540034103400c8034001c018548104040013940308a0890719007500d20740c0e0900c81014020070594000c90307400503800000e907840e2582103000700032008403000003c19154001d1005200c0325440341c0601c00c0100000e100f80da484c2c1c0306682d0010041c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 422142302 1250 422141052 422141077
    0xb060706020c0a0b0411090705040503060a0509160303051305030d021f0b04050a0e1e0304030f21020d020115060503040b10150e13021201050907050f0d0608010f09030e06 75
    0x70f201a0000301114440d611482c861540050000601d1041c005419801070009062200401c824449075078000781b00ca0780b0040d10340c0049203503030720303858440d09009240d03031074552010310b0013004010035802c8030242000e801c00b03c4040c1c8240d940c4900701980d840808510101507040162144c10500401840c06207209105402040300c4c00070402103000c8400458204450599803440c1004640051003000102800300c1e10328015503000e504010744920a40c40000c02605030b2141b1042000b408458205044295075000c403914500030400ec3d45030160f8040c414015460700d0041e4500b55040354401d802e03035405039211400e41d95030741c1d94071310a0b900281000c001c20031a035034009840e22074906200140c0c0e445c0e5540e60b003c06100c4050050208d00907810741c15443c01801070140e402c010704440c504480e812103800b80143c032440301c150b400f845480130f081c00b06400028203008624540d0080c0c012206480002c0221019210100c0201c40203550000c2c0041c85212441c811460094003074050344a006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 422143552 1250 422142302 422142313
    0x5030f0a02130f050117061e1c030c0c060f090303030e1f240e060402030612030d0b01260c0c101a0f0303040605030402060a053a0b060706020c 63
    0x582000161842c0fa4004001d10385100e0040c040d80d41d006015603d075102c600e21100541c21700100203500c081d844681008003202100100c01e20381c1d00c503e1900c088d003902ca0308180075600c580c18000c1c100f00840380180c81c036880a16000602c00d210300400c07413401d03a140e0364840d1240d00b1558200d0140180041b0301d00c85110310310860a044c40c8500100c0c80c51603901d0800204210807031f054444294070000300b07648079003c0000c00c00003800100c0d4070315030100044500590300d40c0c41d0030024600d0190800d501030544400724007142c02c01b44030f500c4416201400d80780d04590001c5407811061201001e070080b00c00154440c08648591504405030151111944c00d0b1206c4000520642d8200c4401501282018a0100d0302e00c6031400c203102d400b003c00340c00340d002d14542800c058002d0030507c07000d00000d0083c040094260501d40c400c0c1d0517203c84124401d40c02c014000001b0107810400e0311a2410080341046018149403042c06201d0840c44c0b00010b0f1006041c142151075110003900800c440b8542d60180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 422144802 1250 422143552 422143567
    0x803182a0f120609190c12030203250303050a09120e060d0207051e0703050d051804020d0504030e01090623041703030a0c0201050606090d020f0303181206060105030f0a02 75
    0x218003000c501107504600608251a0144840d4500252680c02d0b50703003180041c045d503001c95050006441500c44001d800e005584403450224994031801c00300703d0307803a07203e01141c0341d404482d01002804c0a009a40a100d29150386003e1405c44075200c00080031682d01030046801540240c0910b080004000c4c081d41c2041c66014101090343d0150200320b4680c0c02189654842c0900300d90b03695584e0040c000180161030456a07503968805408050740d09001021440c09402c00b0406007064408030044c00135520780f800960950064081503404a0101d428010003030415442840b01c001110b00540d54100b1450a4403120220100d81500a81c8288000c000224803100f6a150180300b03003c0a030007c503503918003c4a044200c9400b1000c04045904010a000742030b42c03030000340c500d040c2c01101c50101c510820700c0054142d44003955001d415002c0030030308048202ca100f0612030304032010703281300203482120b0420a444031400c03030340c040c04583c003070001c41c1c00142c15030103259200c00400d01c0140b8000c035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 422146052 1250 422144802 422144809
    0xc030103020d030c14010222050109170c101d150a0f140c0a1e0308010605160b0906190e060c0304050f070f06110303070f0e03010b06070803182a0f 65
    0x2035110381702c0003581d0001100d05e0070102049032030044001c500d909160003400c00e400203003c5102c4c1d20810411012580c00c080b0081b800340000d907001c4400800040c080080d00f0310180500048261600c402c0050301011a41e0381402548030129041d1103d99900e0101035581c00c2d9604100240c0300c03010801121480180400950700801074040d03540000c114900140c608080c100c40e02964003884440d4003802100000d401114441c103492240c100740e5290311014103002003801c4200d0002c0c0c844e20100080c40003041002c00c03c240039826542c046017092121040d49019500108211442e680c05038000968000b00c04c00916041071080b403d5540050000c6078251619145030880c4583e0202c9079003c0081541116010401501004c06903046180100f0050300211260650350140200b0090307080e090f03030b0294825901500000d194544519242c00d0a5809800072a884003925109518600354000005040e20f042008640071031600c00c20610000120f428012450380c020900000c008690765 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 422147302 1250 422146052 422146073
    0x1101020f0d0f0b010215130305160311010c03090206030606070c03020603011d060a03020d11030106271d0a0311011d010e012703110c0d03090e070302030c030103020d030c 75
    0x15140c0000c42c6150500034070504a540d0428010305561101450800141b88081c2090380500113000381c440847c55424203071100c1c45426420003030030501d01a80300400da0401c901002d0710101400130040044034010540848032034040103540170b5418400280c642ca811030050484a1180c03c47d004219640d40c0400e8407078000780c0050038480d40084000b0030b4403441d003241d0f13940040100c0d072950032145580c001c265811708400c03001d4207454101e5914805510f007500810f0041070340c96401d0283c41c481071101d001501170390241c03100c904c2c18005d000400d01d02c2e404e82400e8400c00b14000c0c080740000c0e0354081d01c0c401014464040b540d505c1e101a48d001110415039851020449000424800b04e1f01e020942100c00c0300941846c800900f880060405004007110343d50254541084144803000b800c46500d0601ea82042c0f6620501c0403403002e0030594070030f0f0404112420f101c0c1c1c0400e0b64644c2c80054059010031261100021000d00042002d4a4800700d03155081c0d0090a18968413242ea4076054210b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 422148552 1250 422147302 422147317
    0xf06060507060b2202161e021f020c06030403020c04060f0509091c031a090c27100e120706050301080c01050f1602031f09060c05070507061101020f 65
    0x36401003861018050b00340603407080c402086942d4564118031403004081d99003114910a00c1680c08180b291000200c0445240310f1600200e507441a54514400c40002041e6100205c0c02505401c0b8410076000c0b00c2c00084040d00c20341e0b0003a1100070484014483d0b00e030002030081d4114403407915954440d031564860702025200c101e1007410860700b00b03000d0200904028040102952201c2e4030012802112013980d06009518940415080c0b0035052032070070032420014145c0d10201c844103010722450081c1c010141c00603482c80300c2e06401c10368802924240030b0311034260b40040d490100d2600c1031303114140300c50f140d030701c000c118041c03138081c01c0300e02403038102d0030b81003900850340010040c810050100450701c54941c00b41303051450203001081141075801080d07072250340000c00080360401c554052081d40f1004100300d0f0000d083c512440640360140c07142c00c0301035901f00e240c052018190340c0700714122901940c110004040ca1460048102c44881d5000a903075881d5601b4018045e402560200070100d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 422149802 1250 422148552 422148557
    0x6051314071505120609060f1201020301060f1b082113020a090207050a02060d0e030d0c120612021210060b0408070b0304030804060507020703150e0609030310180f0606 74
    0x80ca81011032285942d02d0702d007800003c1c02414806000c1c2032030004140b42c0c5c07002090ba69480a600c0701004550a40c81c0b40c1c0000342c0c000000c1491038034503070b415030165040b03540d00d69848440142c01d070400c4e1689d020f002008400b0450b8000d8404c04140d9940044c008a42c590b820204080000107610741e00f0041502c0310780d03074051203401d1007040d450a0302c2104050318a40c00c08600c0c3c0091079171000d660300d100070002402680c0101d80700a2035601c0b540031010740c14000c8181c070740d6001d40101110050001e20141004035a6198888805144510445040ea81c08050229403586507408000c60000144818986881403084490010700036020341402805401b10403500c5a041480d01d90803d080c0341c00c13a001c4000240304210111340c0c4002c0030381c0c005420106c00240394544400c103c0c140000d541014003420032080840390a0441d039030280000c01c00000540c1d800c1e8445c2c01d415600c80c402a2020880041180014000740820182ca041d141078402c3c0d0010744102c108501d503040e50016030000c0d01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 422151052 1250 422149802 422149813
    0x4031b050616030203091011070b010f1e0510111606090602060c0c0a0201050c07150801031103060402010e011d030a0302010c1b050d1101021209030a030b061606051314 74
    0x10b40c000848003050001e81415400c52030b08000c20342c6d0b03d0000502048400d07480b00070990000700d90038210f0300c8407900211680c02070340e190080c2401c089031034403482080100d4050007500810039611240e00340d0380f00510180c4040030b4290f040710107036010360f61140c1d10b00039281c0d804003105a408541000746083e88900000703600e804000b030309244000300740c403440c3d080030403148408000100e002d20180d03a0908140d6101c0f183d030341d055460206907400164031030006100181801c0d412001c41da04981c0b09421600d0311040d4142450344500c0c056500a0100c0c106200d144e19960040482513803a14203c5440d00e481d20042c0b000901d04058603a081e000360b551401c2c100c04280d404903403000381004681031420990081d60340c5a560f540703242514010080000d8401e004c5903000c1d011180a070202044c9100c45080811032241c0b20b510404010020900d42607181c0c041d0b08040081c1c0d44500310f40150344041c24003d071200c602a00b001410724203c1c0c0401e042c0b400c00180b01400c90684102c1c2d540080c034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 422152302 1250 422151052 422151061
    0x30e13061809020312130314031806090a1a070b040b06011e05040501050a030e031305090601020a08070f05120c0a060b1206071409040e030304060609020702090f04031b0506 76
    0x1c01c181850041d4003405410404003101580b0f0018104205000104c800d0755108480c1280e414000901c0d00300030812000074074400082900080503240940008845030302c0072140c0020445140300b901580340c1c00c01c2215108221b284030205100750f164281461a505c1d00503036a845e41e2030071340200c408a65030310f41201400010f591103141c46801001b04045525448079842015016000c0c0741304203810002d000822408480c829008800b9104490089a4079010400b030100b5404065003c0d81b400f81c840c41c0c000954a40c40041c507200300c0d41d017201d041450310041d034450842d4002103030001d991910508100303147d40301a0074010500420304101078501a0800d29144091b105880f0905101e540b242c0d0900d0906213000c161180c00c442c59050001c514500818801018044c9403511503000d460301590880b44d01012000703501c5144260001c00c941611240204121700800401940250300d190000d0b04805402000c20340160003414441c40c0c29610987c0620301040b403107012101c40c1c000c2403e11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 422153552 1250 422152302 422152319
    0x1905011d070906050609090a0b01030f1404060e06010605070f0c030f0b0108010e0a170315090a02040e090a05070b0a0909181e08030615370309170304030e1306 70
    0xf403020301021504030f80f602400e01c000812020010788848041d69503401a003c0c1d17603010750300c031491482e094003061150307480d81c1e0002080c401085505076002c90504040c80c084920110b11907058860035250786081664548411403640a0004200e6013054410404800715a0082d92242e00741d210741014079580d03040c150514259551401103070840e5208035454400600c000e5180b940030061158944d84a5a58154901c21130707401400040d0040c0d00301d0140f00306440c2d07a400400554444801400703c6440b44280207a95041501000d0850703000071009011a240306001480392200d285070218441d03071103c1e8031800f200c90a04110747e8013030a91055008120341031600013000f0200b20000100f01c1d15607100c4150074800140100d2149401c41b04a0b085c0c074000c113082c2c034000150035004c00b030313041d120bc5800707549075a02ca40d41302d4040600d110b46240707091090140d07a10b0f4035407201d008043c0c401150040403050300082c20850502100c0400c0400075140d07412100071445040c03901103a51494500c51 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 422154802 1250 422153552 422153561
    0x7150212220e1e25020c030705030a0b0403081e0a06030b010b0a140a1b0b271f020409020d20160f020612072601081905011d0709 57
    0xe030080e40d0712800c0180c43e180b070400c0200e0b94030646200c080c055440d00caa11651401103050820111032042081c10306070380c0000c041c1c0403c038054048540030303a240c204160b62078003484001000380341a00c0014002a11600d5455080010503030070301d42503a2003d022101640c411212402610b41d241001c00500c6080e00050f40107146c0412120300e05000803400030040b41c4071032002d100c94400010000640b0344600300030520714072500040041c0d16000d103028403640a0a91702c0d600034400180401c40309010300f400d22038800303200800800d0803050641c210b40303015100c642013483c5158240000508030141c0d000800c414011030000041065140b00d1080003910303211800c4802c90818022004a2240b4000b02e03080650484003040213812184005900c51113000c0400a00d500d8017800c0c0500c0c960885900340342000080e600442040308007280301e000940074070820000790300c0b81d103d0a901020b807400d0258260302900c00882d0007010400ba40700c482d611010010b080d580109800c1009010600c07a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 422156052 1250 422154802 422154809
    0x18040209070e010f030b0316030308060a08032b090209130b0a05010b040504020d021b03040801060e0403050910020c040204152319091a0d1406030715021222 69
    0x1050803a0b4095800020304101444d4921000d05130349800e8a8140c0d03130200204190f11040520707c440c01a03c3c0d14000b4039581040d1851401281810004140110044141c40d15175030500512207040d41a50309401e0b103030552034030740f6440c655240100300c05a1a00c1d4005803041110408255411440c0c0c580b03660b082000902c008411403a0100500212500b84105c5080fa18111070150b12030b139101c1c6d585c1000307114854010200071244c20074140c03003020100240080301c0315000204621599100c4d00094a101190001e00241e0108400e85092130000c0b10780d00750f48041e20442c2c001c4140407011030b0483c6d00c61f410007500082c1940f40e00230080e901c240f45507940810070308800420443c1c02940303c0c403800740d884c1030382c2000000180611124880c10b03802c00200400f040151505002c0034860445034003558031600420704210010780c28803c18070600c0c0c00b40c0000340090100501d000e4001d220184d000c0404421030141e44100004000d600018100c6601790244403540d41241c2a599074052000e9070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 422157302 1250 422156052 422156057
    0x3010b07030e0306090712030216171203040c180f090b1006020a05060c0a18030f0b060607020904020111100f0c110a0308011e170d1101060b22051804020907 69
    0x200817011001140e140101d071b00045440d18003103058a016400c20000041c40c0c903104107245400240d030103440300740e280b40c200540255410480c0742a0642513600c0211406844148058801c11048074070000301008502481000607125403405698416150a8042541c00346500000c0c405e0031000304c540900103001e20700090420180d03a03691140c4030b2100820844891a010441c00105d074000c07070f002140c81c801403070500403890b168038001d045140b090380141d03007800039100014a642045c00132900b400d80c000f8540300f190765681d4011a012003000c8182e10060140052403210581c5901031481030340c20007071000c0380c1c020b041d40c0004c102000b01e03207584a041e44860030000c0031035007140340c85040d02c2000a00119550b644511110180307803d500191f9008482202e030800303607001103480c82d901d210b50f68804080020444041c0d09a82a5000d1060412000c0000c0701c1000f54240151180e800e142e42e001100d29a500b00140c00380078a03620200b20345100304100003c40c41c00402159200c4803e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 422158552 1250 422157302 422157313
    0x130b040c020f300301091e050105030a023001050612030306060703080603030f1b160501021f060803040e07030b101d0109180c12020304030509090c0c0303010b07030e03 74
    0xc0106540c0c80070003030001807040000d10400c40c4040780d015850b00245194030707a80e40d071381c3d6503c5440700000d052140b90001c00800640e00040800d0290040c0d504a40c401402030004502c19002c0000321240b030340c00c00d140782c9050000c0c400d4015644180000307405200d400080d2510344042800019200340421075942e0304100104042540d0700c00641e805648c0600d426580c1d170341c0d01d802003407452050580380a101031001c107203200d00800c041500c6a5061401041d0340c103000c1f5100131031000da2018000e040c0544c01c04214000f000514031002c500b40a10304a001c10007550b40c014440c2164040c0c6c01c6011120700f41020886c1c9903401d405905224501500c1c024039154075407200a051000882e5800c40c1e1080602c0b4100c55a84560b41d01e2002e07203c400c040030541100380d0382840c001e00641c45a1301c081503407031454000300d03411f500c2660300c103c0e05612010700d4400543c00304504103000070054000d5041c10701001081c1001003001e50f020300303101d15045a03030346801c5c05c020b0400507824100741d01c2607000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 422159802 1250 422158552 422158573
    0x61401090519030b04030302040503060f011410050d1e0903021c0c02090115031e0b120109170a091a04030c0909020307090e011d06040201111902060a030605130b040c02 74
    0x4142ca010460b900160440c407540c446140c120042d200300e0b481580d25110b04800c2c42094000000d80c05d040f50b2612242482c01060300c8140321040d000403003000b001c00c90512000748083d074581c00c0034903081c51181c0303940d100d03214480c0150304452408209400507800031081c041e070011180d041c01c400f04503a04040484003802d50000d10044c0b0140074030300010300002d081900c1c00b4040d4002040403900741d01c01c030801e00c801d4000d00008000d0b2524461003400301c2c510b580b12a40041c410116a20b800c0002c0710304100300983d000340b07641d00100081041004406000400c0800c0f03801407a40141d940a0480c0d41d00c0c99401d01e0038031000190008040c0c0361802d103e07040140d40000d000000c582d140c0c0b0b00880c0d004042c0f080c007801444c60b40c480400181c81c0c10083d0208070800300c2c82a102d10b00c00d0b200d40052841021080e44e5490300640001c01c02c4240c0016000540380c00406040c220880f45008a803e50311350340820300407c2000201001d403030315542407242514180c00703030240c100c0180c801801c4810341c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 422161052 1250 422159802 422159839
    0x106050d050a023a05060606070c030b0711070602030408010f020a0e01030b1f020a0b09190321060b03041202030f0f0304020d0c0e040501060801140a0507120614010905 74
    0xe030180001d10801084074036056240460b101140c0c0e42c1c02040c03030b05840311030300e6500ca00f01e04c0f98400d044595008840000711185842001d171118250449044c1042a04581d25280003000291840b02400f83e03a200f1840341500130003880d000b91075a075020750740b69031410780c81c203003502e009200c61100f003401805100052030707000300c0c4101d02c983d0918010400104000c0070030404480950b0144a2030f08541d41218019000a4140030080c85030b080da028984c4e030700f1000ca8a42c018004809090012400800d000c40d100b0f502d00811108465491030209291070403400495aa035800a144007201004010500040e0056000306001500145140c940100084001c0c1d1144330b5100d580e000780880031a065480705038056103299071000704100c2c51074980c0906c102d00c520840d82101d4540c00e02070040780c1c1a406004080c000000c581101c00903449181184e00905070061800041201d030800808000c2158010500200620b99141503035a031000d000510808081d04041c1c02001c99205111a41c44c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 422162302 1250 422161052 422161063
    0xc050c0c0f100e0a050604090605010e120304030f03020f010609060816030b1f050d0602070c09060e04030f020114150112050115050702121501050a0801050906061e030307060203090106050d05 84
    0x1c42d5803410b00710140078000003460181c1c0d070740c0180350441c0010070042180700480d400b6509540d000d80b50a0b90003014142007040020040c01e1081c56901700b400b0410000d04880079100025100b8010f44042250010b0341c142184c8442e402446065122141080320340d01c14000e120005d40c6036442c10f405a0b0864a44c10130026001e8121901c0c1c070000c40e640c450581c2442a0500030345002001305801e02d10a04040020350024441915101030800c8000341e601518400c50381280c1010350001b8850341d83d510181e800c4240c907076016040d0754880171030300da56201c10782c10103110321f651004140c4004583c90005090180070314109850502e03200042c84042c8008000340b03010310140c40d00c10707910410751003c01c0e021462880c0c4c0341c1242c4200340c9540c50b2011120402c9050f41e0003912081811650384070042d0a80d0410340f82c085d40c54100201180c01420003484000d1203410041d1480444000d860129140d944103182c02c1c5c80140e0b000c010302003a200f081c01507900a2004403007080070381d00540c59440d100c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 422163552 1250 422162302 422162329
    0x10e06190302011107030606030501020a0801050a030b01180e060405100f0e1c14041502010f0b1011011b32190e1f0f03050106140d0605040c050c0c0f 66
    0x4114104070b510122420017210300074642c4010140000d507624a8281e01030b402003140b901c04900100c00104680c1090b4424100b140e07008400e51100e07074a4452201d240610140038072880d551030340c5050072128010001140030f14071074401800e5184c9164815000c5413400c0504004880c04d0168800900000180043c1001151411440d030b00c20400c900356100414000190038102001c41c00003403050401c40b07180c5490200360000d00004648485000071200c00c89031081c0c0c4082880380160943e8412052800c01e96100c1000142c00e0654a0700002c0d4508668252130004000c00031014400503c40d426a03902048011ba030511150040f906003202d01410145e211100c40450380d481100b0300c203228040d850310002d40129107541e440540080c071044200d0f0800302048140840b4241d0900c6849030504a404070380e20090301c0401c290503503110343e02001410340410f8494402140c00da84500c281c0b084080c454136283e0380c52001803101410138002001e01c0f8456649200d1007030381e64448640e400801c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 422164802 1250 422163552 422163557
    0x182607050f0303121533040f060e03070819020f030f1906140103030903031e0e0105070212070b03090f0a150504021c030206090c19030f0524010e0619030201 69
    0x19551021103007445e90503490001948140054a9003800d0030010900e222010001c511180300c0010f440c00d070b208103115a1080c00c07280d641c0c03210308010581c8a09070361a00b030f40f0014192034050350f030b03501060316100c0c82c920900703c4500c12880340411403030101c2040c2610700054000e0291001d202a8150301d640441b10b00602da01002059007082044590003070ba08550140706040c1d15503144d08006001043c01d00084011409064244101e01079804103d03900c001c1564070302e00c242c00740000441c0e403500600c000700c0e000f0f01000403401d4002018401c43c0090072079088541c0e00da10300324101e1403404000d01c0c4514020303044564480045044036100e19030f03503c0794000c042041d0300c82c0d03c08100b0300b00040c0b403a010300c040c20840040405901003401c900643c102011686140600030400c4034068403030f0388800d40503010700400c10000c0c00d40c04054910b07500410030b4170f0064210b8515030412201101d50200d41250180050200b010710307a00064000100b65080d011640388119111041c49940c04064113 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 422166052 1250 422164802 422164837
    0x10e12030f160b01060504060f020a020f01050a110f030d060b04060203040302060717120406061a030f0405120315181e100510020304080f160303182607050f0303 71
    0x2860b22034408000ca69200030031250300c3d0303921030000303010350801e00503131000848840d51803071651300c0040c1424080ea0000c10200440f200000151510303448240d802090050000303040c0030501d800d0150186000783c00028640e144508001701040b0345d42c03604801005442444140a5640d000095509481d819a4001c1c2e03100d45d20f00384080107c5240c000825888800245100c409000c0411075002c1c130311440301800780c0c84d180d090f000c040c0d00d00710024418404080c000100d820300312000d066040341c0900c050f100c00b94402881144030380e00c1283c00b8929500202c400704018202243c03080c080505281446800b070a010814580448001c107865000b17183c000c0100f2000d41080280e04001d0400400c294645114404042c0d100e811034400c41e80c560060040300c0c03c198202082c10b0060b21000500c1c400c8040c1541d0f000e880e0241c02c0c1040e100480ea80490100e6085a003810700c0488ca49038002071424020000b40c114605104c070b0300b00c0c500802c00000400c0f803d071000015201c5440e044a035a01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 422167302 1250 422166052 422166067
    0x10b090c03010e15030c0604030303020706062903100f1214150703020d0605040203010f0f09180b04050111030103080c010c02010603081606090c141305040f0b0c09040507020c010e12030f 82
    0x1e28202c03400170f500f44e07c01000200041015015402400441e03c1070f401401200d070741e80715800c8601c07401107079801482c0e440410070310320210100c000c5030701c400e100b000c03400015140d800c550301030011908040302520322030040c0402e0010740c0c0030300280f4110180052605100c1504005510703600a40003100741074001c5985052000503402c180081c20001d04115165a590503c210020402e80308a8808012904001c00d00741d07102d00400c0b4000703110300d60740440da8020303a842030400c5c8801881581c2956030f420108252400b801d00460095003d0165981c9901081406908403000d10f20100305682c13400d001040012989025240d004c941810040d99404150400d60054101c13410020700c4088c64190100d00d921500c00e8014506109072845000050b1240c41d40c0b048510070740b0046c045803514036042001a8075030704003071752007222040380c2c0342402c0d020008181540c2041e82e1800142c0c000d03055000d01c2c1d59000905591b0110102c0f000d1074501062003c164480c070540341e81041010000403801d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 422168552 1250 422167302 422167309
    0x30a030e011707030c0908010b030d2303011e08013804050408071e030e060d09021804030305090c06040b09030309120304060906080f060909100c02010b090c03010e15 73
    0x400daa8001c841002c524035200d40002c0003440104410004203e40d140003140d56981480740780c2082c8000b400030003800f4042401510000b2410407a0915400c0303050380400c05034544000b860007059100b0300c82c104082e00c1422091006c00da43c01c8243c86a00d048080c000740423144400d120352031001c104640021850507a0560010205480c1c03d4209040c01c09100800c00c43c0c5004111860040c0541c80c0e006404035400c45a002c7d11110140000b44142003039000b61901000501603401301200004100031141d0101d10100000e00c1d540350145020300801c021b1541501640e9840700c0514058900e01e460703400007551901641c0079007070010f40c0c041070070111510100215148031030010610b4400394a140070f4540d40f64014000c20f40041c03542d0800084041c015842c0318022070001060610030f0b66040c00313001c180748008049209605c241c0915001060035132144e282c85034a20b60020400d403010350188003c1103000303000184044420001009403009140e1425000042c44120308078121144000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 422169802 1250 422168552 422168567
    0x8040204050c130b130f1a131a0304020315162007030b04060b03030906090d1713080106150206010312050d0203180115030213090807050f03041a0306030a030e01 71
    0x4403080003800c114085800d0b02c0e03480281142c40d80300418400400d4848801c40386050301440f500d50101f001d2403c00442801c0c0c0300103400031050305554000959618083d850304100d090703030403d489a03800014841581000d104000342c003160030007102c12505080c148403e80c040100803031401c0090813051035080d01100400c0c0085443c808007103850b11a120f040c90000c2072010341d000c8800a150404950190402000361100c5010041040741030028041c1070202c40c2460030000c81e106000d0700c40c0d400d2060030000141c507214594a080200e11810441842d08407031041e0002d41d146e0b108445101512607000401ca1b065a5016582c0080d2802d80c01080c0c409010780d9020084070390000c010494003d000c1003c103500d04140c0c100038820040c4000d030500a85016002c080e4014034400c2c0b140342d040c0e039603410a0b1840361181005510741a03441d140c650410f40f00c0000b1401540000500300705441c4100d00e244000c0c05280c1500d0318508000340025941c03c0c4410004051080101d0008050b0380294074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 422171052 1250 422169802 422169817
    0x1902010504150e2b08130b0103030c06140106051305040b09150604090911090f0f010e06010c060e060108010507050c07090506040905030d0b12070627030f0f0b1608040204050c 77
    0x100401c400b0380001100c04604c8110195200098405c00081c20f0500d001c642c080006801c80c0e0050f12590071a00d0403200f44003140001d42d4055264868043c1d100394810b05075000b00982d5452680382c05502910900b0f200c1c0390340c046441241001c000b81e569541750710030190040d680d0041517107545500004071380c0c18080c9030b100d8580e00e46008000c0c002d021200c0b040d24a00d000480b41b02c500ea550305200f25102003c1910504680f035002801402009c210400694000005040508600405607250f80950f0000156144c443c1c000030010081c510b024019103400c00400d0030060309001000440c15600d22480c030034000c010f03489801244040e252a4000f03040c45422105407556070102505500c090038a45014600500c01c0410451900c2d074041080c078183d924595820b03c030300c40c210b404807455640c0085900300300d001004e00000001c1e0680c0721440000d100b00c03905600b4510600745a022090000c0108140c81d0740928510b448a40c00b10200c4d601c0380d41268001441d4940c0c0b001c406280c001d005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 422172302 1250 422171052 422171083
    0x7030e060114011404091e0e031603033c0207020102100c0c020d060911030c010c030804050709150608090705090601050d0b090a06051c020d02010f11121902010504150e 74
    0x30340424641c00307e420540b12594002c20440b140d290b8840c0b41030440d060044901207507002070040b0003180325035036401070143c1d000b032030301040c08001c085504500080c213400c44002001a04044030850503081e8401c0141810080c0841c1452404d40006c0d40742e1481000359079801e6030360b10ac0c0c85a1540111154000260040d06011940d441c0f0302d070450007032202041c2030b568210941e030711490724540040d90048620301030f51b50107802c1c052503400796002400500211094010b14902081c071211b18070985034803e490380a135042c40c500d010300142280c200542031b0880b68200c40b17000d120710b855410490703822017020302e032182d902e003d001007a40041c1130491a440d81705003070308107020b10000d540e0440d0044e244201d506030007550300b207040134011115a400c020b4001c007401076802e01640c054480340034030b041d041c107000c3d0044190f0103079a4200b000074a41210701a80c049001d1501c4141c040400041130a140001c10040c107141e01c1d181d05004012140340c030340640720494100503170f80c14440e601c000032464 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 422173552 1250 422172302 422172307
    0x2011b39060902040b19091e0212010f060f210f06030809040b040204080d080606071a0414010e060a110f0c15060a21060216030e0907030e0601140114 66
    0x1e28005020340b92841050b8440c40c00d100d141c4503d85403031345ca90290200d4402c0602002e61400f004030019000c0800d01c41410b10355000800080c00e0540001d017002075000c2e42124196041c40d102d41040400384e0441c600304808541042011600300303c55920685000340c0503c4009441d0704daa00241c260104030030412800c00b00300108014100c0054500b01034222024006c80340d60f00e00307020807400745c1c0c41180c696a20455135a8400b601404941740c0000020f011103107415819103a90003007001c2611800c001440801c104000d2003c0203280c4048910307440c00074420b075048003032200c1d0303140300c0900f401c0216591201c1c4e803002d03980041c08480c0038129804005440e0116201000d488034654420102a42d0107500020801e1600068143c03e0301c60789142022805000520742d01c0102c0f480908a5103250b080045002301064465808241d074840d40c2c0c1c08030310060401c203001443c800540071034203040c184644a1200d50000ca8040d0540e01182001100b0988500048030641c185401544140100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 422174802 1250 422173552 422173667
    0x809011b1406161b11031501080703060f0903020c1905040906020910050f0703030b060f0301080604032d050904020f1201091401060c020618060d0b0102011b 69
    0x4102d480c421040140762014060484009594503251100c0803070b19030301041541c0300016000020b201c03c40c4409000c607031a503282140c0c0c503020240c1c02c0c6c00c64a5a68403020b020802c02007140600c0740350032200c03d0107008100340d5031b40107540c48a42d1603903a0711a40c458101802e0074101154131070014140200b0a100300302480c1400002507000c03800950080c6540855080b11901510031160a00400440755140490b140c400b1001000d00d489a143d00000811125409105180c080c602a050040c0544014202881c01402c042452002488460f00707482c3c41188901e041464143c1c0000c403400d100b03070b49041c0c200000f0002d1045d10312203031908202165900c4901c6001e8002411f86807101d0007081540ca8914041003603400902c1844005041040158014105280600200b01070f40006079810401100016003507040a07003040780040e41c0343d584841075079090140c2511040b2100040084207000800100f43e041031051560841d8800044030760700c03034022190720503600511858448240b0030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 422176052 1250 422174802 422174843
    0x60c030921110f0303011a09130c031401050604090902030f07030b0103140a05030301090e010f050c0a090e04050307030c051614040c020625030e03040308070501060b070809011b 78
    0x9104254000344200946841802d000561400b11802002c01182903a207002a40d03950020444260990400e09001e612840d032192288028105070242021461011201004003100e050b8100c464500700c0000040000d07480302c0c8119000c0d02c0c1899800304903042240007080c40d2011030600340f88184104440042032040d1028568162427082e030360703c4103482030008016600d503041c58000d13000787c00420040180c248240d00468500150b040041182c035046c189000444804035803440d840f000000b0031030051a031110b0120050040038900d4a124101604d909d07980e0700600c80c005080c043d428040405024003000b001031031000950301c2c0c15029071211100c0a540e0103650030a805641400e002e910064008900031b44100b013003808880314035420b46c0a204501d8206440d190038180d41740905d4042640900007080954042c01d085507a070001c524206013101d1040d4000c0500d810180040c3c000141c1c410122003005e0824a810349002c280013203001d50440c0403100c010b22814a0301c0c0000050711 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 422177302 1250 422176052 422176103
    0x610031112010b040501030507050f03060d2405060f040e100203130506250509030d0f111509070b0705120d0617060402010f02010c020304030204091b17120a0c060c0309 74
    0x5d03000e9038144201d4661803425105405219880f0030b6481c000e0000440c40d06000d0021040386000c4c2c003864034812180c0c1e01010111440d000011903454803503041154504101c030540100d041d007514100300412401c10420f07200d901d180b0103104280e80000108510b07110f0700c941d11002d690043c2c1540c445040c00042c01508842002040136400301134000010713918002c1c815188100700240103004a559510303c11220300e003c81800100344207c0c0300003d0100902004200d1241e19011410096818140720a528005d00c40e0b11090801c031703081046c00001800400c0071176504220040741501e610160603501b0140c403894101062004082510924504000034064019030003a00d4052403481c030180e0407400d98040a41c60300259004010400c0107003031a5100c4000b0500400302c15000d2580c4283c8109665415030051a41580c02e0607032207a522003c0c40508040605140075a14052a40302d006c0c122100000c0c015100c59560171154045030300039001380840e19804524040c140002c5218800c407207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 422178552 1250 422177302 422177309
    0x21203120105040504120e010309080d06050a0b0a140c07091a0405060f010503061507120207170c0906150705012c07120807020114070b0415050610031112010b04 71
    0x410036030000203a0341040c0c403495000300d420086100d015108400142e500d241d18404a504041c1d840d2001408500702c1c2015081100c110480451054500000c21866403a642c01810046c502000b4543c070f00e80c0c201c0c0c6064100d91030046185d4480d0310400300c0c40d05041e0650f105240541c181200c000c0113550f10000e101c0b84550460301000a62680014464040040b11405000c035104002080322843d01800f07504181c0303488800f00d841d0040682c0d482d03445104004600700580d012250030300c001c0c0b05030b204007030b81d080c208030007003e420303c50703400140781410701811080c002e1241c1100c000e1090003403401ca07030b84640c0240083c014000405000c182c0b241a002e410b0010740500744185480c0c210103d818000c8944c90070b504452103800f038580e0252a40300c205c0407810b00080961018000d0100400352031b5040c00388440c003040749043e04011108840c0015a0200d09280000700300e0340d0b6031380780d043c200d07043c41514000900300d180c00003104441c40b40d1a00c0b02402c0100c10b000244034001400240181c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 422179802 1250 422178552 422178577
    0x606140919080607080f070e010c031404030f0602030405190b070c02040e03130306061e0314010207120e0a050103052a0903120d0605030111040902030705120901020a08090619020c0a021203 83
    0x31f0f5a405c072040f5a402450302466001540038204c01e40402e11948407214090044038080c0c0c034040d504d6a844d0740c0130203e440100c031140d80110400040c8601484902e480c0f06a07915045111382141d40c440301001320090171041440b01e0788200600f55241d65022950f591000c1040380d95801d007030b4015901596482c17004075200d604015010418480005441d140342c500c5845143d21b0313a0a660b140d21402c2c4841c840c801c0c0c0b542d400d02a8074081184504c40c40503103900ca0b2214665400c0c0d6900b880700c17909403900920705043c2042c080c0118207180e0003140c4c446681e000e440981c00059a01106a548251f0301082c1c0d0500c1800b240c80042c8a00e60014003194603424000c203d45035581c001c0c5820b80d044840498002c84040c04200400e1203250011588080c09141580c0380406c066540c2c0724910007523030528100c0c1e43c00b1a5040300f442e0000c079001c3d04418003c0007001c039460041441c080382d5500c99181e900300740d00840c502100c603400700040002c82d603006000701c0f019030300108103540d250441c200c000302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 422181052 1250 422179802 422179831
    0x10b060703020f1002040f140f10050a0801091104030308070e1e040f050f0c0f0d05040f02030114040b1f0812030702060f130f260d060614091908060708 67
    0x10f101e656482198211600030a01f001d05525100300c0780304000d8155045a0051980c0c420328000d0381d600d606441c00c10b50a0744520740c541c504141c0c018417240d0140c10841015162240180160000c102035600b1651b1600e00360310140e5907034200700d861400c03054803183c02ca1030401e0204990b110103d00003c1c072040540c0c0c00c1082c1007101130f00e5003d4034030640f0303030814410700c203c0402e180708100001010006228515580b40207807000035041111022035054401c84010110b000c00c44c5400e005140c8814560408026141041e40710780030403c2c005040f41000402c1d0400500c2c80204090360080200303840d40c01e442c81d401d4548501212a4030480d502001030142200041c41494030142044c058001d1131141c040c8140170b80e84a0300c180b0a4408140c4401c0d825450303054100c2281200d010003980080f00711600c6425a00c0908141c4a15030480780600401d4442c81410240e62020b4075401c040455012581c030f0041605080d0205203900824564007411082000543e00102d001d4064801c9108800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 422182302 1250 422181052 422181073
    0x6041503140c061806090d0804090902180601080a050907080708030a030b0d030203030601030510150c120504140603270f07120b18010f140105130b0a03080705010b060703020f 77
    0x1d03d031083c0009450355000300d02410001e03050076406454218070182034400180c00d2900da00071150416031000040d192120300c0ca030b045044c01f110f14584a0764103d60700b0100e08041c000680100c80003002030f1010741e5554006007a2400401c1260000c0c944517052f685440c0d1a80341c1240c59070300807601c03080030a0030880c039510386003001c1d18021000c0707070940d02139401c5840d05801103016040c040c0c078a462a420040700801c8094524240844103a05074031141da0340d21640c905140c0b009040c824200a20000b440300700701740400c03aa07000281d820304032056556507850807404c1500d11015900c0b09140c22141141190568001484000c0e120100c011650220b543c6c101c0070320400407612005140c40040c4000c01c42000414001c141980c040304004207401c81c0b070380b40301011250751600030461059030400400140c00c10f2000c2c10583d81001d0010700c84003a07510f007c1014a0400d1100410240b0300082c01001d000080d130200060100041c2001d07503400b42030500070355a0310001c0042e011402080c00702c9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 422183552 1250 422182302 422182309
    0x40b120105180402220621030305010806060607150f0c0c0b06060711010c0c0e07020106030c050901120b130b130201030e011a0f060403060219080a022106041503140c 73
    0xc40c070495004056083c1194006640e172816004880e81c40310741a01c4641c0410000d00c420b000000702102d11000101c150180d09000b400da4406901400660b0011014041680c40b14021070304401d80003c0d51100303003114001440001e2803892140c0307083d030f0300d84100400c0407940201c8408015006248401c1c05840300000c2104600c41d90304020041c0005800c0744405500540c0f1400c0024092609812082e0350341e60b2003421501c00b2905c0100507556032409100304455640000081d2206940f5a140f642c1040320f01c035441c0d1481200600464281c4c00051108043c5c084040b02142c2d11400d01c40450419403039130043c00503184000ca01190804800c684200414401c07914800150f0304419940c20482061103c04003a40340b42030b4220100f00000320200d41980000c102c191202415421180950f620040600b1000741280e14110f004115035541400f00081140e070754040700509451586800d00064000e103400741510302c02600300c3d0400000d0043c000c44220084074101c050741c91146c0701d035080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 422184802 1250 422183552 422183599
    0x70803070c12030605090114030a0204140618100501031508070305030d060e0403140a0c02040923030f0301090506010c050a050706020d09051804060e0a0f02010f031406010e06040b120105 82
    0x4040d0004501b000411004050a0300f0b030f0461a806000d0b10040ca55640105056a81c4000c2c20400016020f06201c0b03a800d10300713a05036072003c2c500b1715003007070341855410f43d80b140c0701c2d40c414141003507103403c045000c40e405130541c440103160150468200c1543e9251441d2650801d00f5480041c5140000004004580c40c0a403486103516944d076480752008122145031f16003042c60142c0400c17280d81501c0740140c0310f80c42451100b074040d54002411292034604440da070001030290030b81c1070308140600c0b03c60005900559054958048001c03c1e03942d5a54012506003c41040103030035807242d010000203001d00841c080b41078803110b50a44000c040282c205450114a40c46180d82009203100448000290407400700e81103446154045034011a99490768945001e1a9041c0c500c408124000e100b1982c10010002624449080c18403c602e10b280091000600080110741404001010009140c0d24036085501406100400d01e88500318000403081c84c0c40c01b401410f000d01e070710710760312801e00000400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 422186052 1250 422184802 422184809
    0x10050105060a120e1204090606050a0c030c020102010b1804060b030d0509060304020301091712070c080306010e011701080f120408070317090a0e061908071a070803070c120306 77
    0x20091912144040403500700f4031040040c40a550b650941c20000340050000348a04805c69920399291400c0c80702d0719003103400f1030380284180032040000d001195000003a00c10358980608064141c5245400140e01400c025072030710750b2000301445250910820b8140041c000c600440041218094190038956511420107550f404550148100b00312481c052000755400b80c40a0004a200d0700203a85203072190400381c1040c001c9500100c0c01045008000c0034040c4c0c01003881c80d00d40480741380b640301c2e000148000303415541084011108407905900404002c0d260000111141c11a0b42e135441d0740940362140c44402509600522100903844000314080c3e409983c1c170100681411403450303079204124071b920741e00011401070601a80d6429034405400100400d00c035059003180d494918100400c000c00b500e18210414450078082c8842880001c45505580407061509042010903c4000c801d0080d004c004241000c00010456426480780f800c2c440c0520550382440701b072000f004141d0540d0b8a502 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 422187302 1250 422186052 422186059
    0xc0b060906131d011802090f0403090302041802090c0c070501080405070608310b01170d030507030207080d061d0903120403170901060e061509190f030b010810050105 73
    0x100d40b07031103490803a0320504081c0b00b4072902100c0d440c01c15401c98207440c25011130b0710812403901c580500b5800d0125101c1d83c42184900c2801c0320b4502650050319003c103500001e4056503680040f016641d00c0c81c5409092182c005000d013896180048205031b1542c000c0c41e014100f805480d40000d1154016045140200d602c0409480380398100702c41120307041c0c40109010004050400355007076503151014109103180346000c0c0b4200c600d045d070520300c102090684c0103608542102d402c0007201c841c0481c5130400090540b402240a0b00c4000044010b40030b10100540340540008020f080c171326031580300700308440031680c082c00c1c18224503580d803034000401c82c1e00d00e035240c1003040b020f00c404090141c5c2c49d50092003424041d8480308100c5e612119180100e034144010fa540f00b02c1030020303408031a05254080c40490ba00310418058001e0002a80148070440f130040b1072000c040c5440c0c0c0c0464598034054103400d00e00260761640c81c02d054807810428415030b45940250003080d03810423800c2c000c4c58141d4202a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 422188552 1250 422187302 422187319
    0x241404060b0a12260301060f0e0f030c0f060d020c06060301050127090201140c03120c0408030a080a06030b0705031503010212011401030626120304110613030f030c0b060906 76
    0x1500e980010705009007000c4e00d4900181e1414802d088020042c5028042541e41c03800a1901c00102405040420048074401e40e80b02101d144159000588140403420940300c01da0b0340d00c900000714499004512a850b1040c0c00403c007098a0240001c2c9a44100c0c0c00b140203000170390703860308980c0c00c200072007035002c01d0707900c4c0340c41003064080c0d0302d800c0a50210b01c185481038150751462040d1865801584001f40305400008140d26091001c0d4034071f03034200c1c0180100d5441c0c2403400c40220342d41e1050400e201c05020011001543c0c2c1c0c04950b2120f401035401900c85802d0b890420030041c15a03000301e940501e14940c28010801a040520a64880d01441c100d1190141d09028007050710027400d001e8907040689981010038100c0c0d40c2202010305c040103d02c4260800e0414015506042d40c00204e40c00d1400b0500401000c1040b130b4001030f4103124150fa01a0b0307103441d070f15625480d480d041d03000030300054100c101a8081541c808400010309004503a103046603160903080121902083e0349495014048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 422189802 1250 422188552 422188589
    0x118090c05090129090a2106050a020301090b0a0b0a1805040908040806071107060318050a0b0603070506071a040302031306020d08060603070207030803130c1502010c020712241404060b0a 82
    0x40455070182c644030303840c0c0c4080483c48d41d440e400d40700708440c0080f100c1e070040010804448240208881c0c420112502080142090341c171034000d00580d18507604100744e070964010700781e00e080c3c01a009000041c00600010320a401c004115903c18421021140326003030000302441d1044080c507e0030030b01304000d04101d41c5400f00850140c000b542048101c640c0e00400303d000584100300248140d446961468a940351880400d4142040780c1d005074025031041040e00005039040c0700d40c6180504080c415107060b251824220b2035409081400c0000d5426404081001c0e6000621702007603440300c1d0f482d1170304d903030380e1605000c21130000742c0304640982d111250900c0059001005954018984245540782c0c01d180e465401c03481d0180d5008600c001802a140c80170320ba42070040d0710a0760101d00041c01814501138104011103403108014200c80c080d50840d4a010500b070319581c005011b60441031041c01035480c40c4040381107056404840c00c0d803514a100d03215050125412044612a02c142200c1c03140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 422191052 1250 422189802 422189819
    0x207050a110d05030c012c030909041e12090b1810020703141005010f0b1c0b210c0301060e15150a02010b131803050c01020403080a020d0f03050118090c05090129090a 73
    0x10704121030440d1400d80c5441c1c1d41c1200f0710100441d03801007013711076402064501a00d20302e03003508100c04d000c03c20406d100f9003c14000e8100800c2c030b8181d40c02051224040d0080303042600c1c5401c0104140703d0403480c505059400a40d40b005040d00e05020861641e8945011820002e20f00c955840101c0500c49280c98600000614500030f1000d02c1c00b10f0055079140000d4158940507890200110448145160800d41001080700d0f850083e8000c0002d0f034109420070a81e204000c107101b20340c03d04280d08a00a498140030040c05807507880d4115205d1410500c040c0c081c0c5107000685000d00b1500d01c0c03403040d0707468078010f0621300500303030064005009050320300316a2540700b042402041e41d0200303c008000351000c40100242405540582200e6100307003c01000f01040071000402c1504100047c840c402400b41c1202c0c8a080286c4002825112442d00141044e60390340013991100702480000f901084211014007000341c0c0d111a61207050040020941074058031490903041082004103010002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 422192302 1250 422191052 422191069
    0x4030903110a0519030611090303071203020c161503060308030a0e0a0215220e06130b10020303060a0803040b16150507120c02010207050a110d05030c012c0309 70
    0xc0250150302ea0036110700104401ca200301d180c4003850304042004005100440c46103008410803040c49034581075624001a03900c2c02540805044280d280c402c10000e94081c0d4111040310074a03900350f07805060034000e1180f0303494462150400001506807450b144522a01c1000c1c1584e0780040ea0328150344441c0d0040004200c4161901054454603098401682d01d10748241c000c461902c5015a03601d001c01c0011105850160300300840e0b49141c0001c1c8100e04404407032542c4002c5c03d40f9224143c0003e03094180242c842c6071030f03094208440c040d07401c500950103c0214810a0140c030f00e503a407595175174030007952881584a4040c10080c14083c1a20307042e80480c0d507240c0c0074042c1845900b2054003080381c01c02c0340e4007510618045118540300c282001028000d2450240490000314280200c40c1c55041d00c804070804020000b42c24544000700c660b88103244101305035040f1046a407100c4440c0d03002402050080607184010000c1101c0210000741c00481d088407801c1540910b052040003014450400c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 422193552 1250 422192302 422192333
    0x201030b040516030b0d35070b06060d09120801060e0a14120f07080304140603061818032101080c13020708040b22050405240612040803090d0804030903 67
    0x14070450f000e03011403800c1411943c41f4010500340b001d02c1050b1100c00303940c124000c01c122031691087c403411010400180d5500c0c0e0205003500c8403560358030404003902c01040c90000051100240d4a51010096401420181a80e0107522290b60340d180f802c00f04500f1420b144580304840d04c41d0305511a442c102503e13601c0210220901700da402551444405e0b09019650300070f054280d001290030090004500007440403040150307006481d40c189070000c240002d44080c0b8101c10700d03040501245909a0300c190100f50740710300b801030369250041780c0040d1245005420a800282004c2000401e06131404541c85074600e04c0100120741304055000c0501c0030350842e400544924005002c005103407a106001000710b41c0d90036186980b8011420b1485801c035440b60003a600441c070700002c02a2003521251854907038499443d41c0d20040340003400013002031246011848010038480d05000c100882080954010801202a251050007200d4100e80c00c020885020f40001c50015041004c01c00011402800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 422194802 1250 422193552 422193559
    0x5060d0b0d0506070f0e100807081504020c0c0f060408031b101416110714030c1305011d040b190e0d0801060f081527010b070201030b040516030b 64
    0x34074002c0e01c0340d5062001c100c55102c04030301c0141040c44500c0d88a18010741640e4100c5803048141c0c3e5070038005003a09002050b12081c882d80002190800d0500c500030032100200074000d40d5501410009240c4804802f0400303405951600c5c04078040f032501105640c01c0c2c811400045007014446501002200d180c2601240c2501961950042c40e0055010303080c0b480305014021903580c24417259681c0303143e080b84800303410414002590701c102000030903014201c0d801c00f04460510040c0c840000c1c00d21950300d0740c0961204806808003040050794000904913038913004041075000741c0740c07185100c105045400410185203030000688100c0514860350b0481c0c0410400075200d000c4002d6545000314071010840864804001040740c203600491411400c122440c043e022401c2000303100c0004c00704451810321903007013000410002c6048084031107986444503c40340c0349594a00140445510548050340020705100188445040c24002c41c1c0c05808041009404505060821030013000c80310382c1c030b50f0f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 422196052 1250 422194802 422194819
    0x30b060d030c050118140c010e0108190e1c3e030c06061014040306020c0312040303090215090d1106160602030a1a01020703030516080f031e0105060d0b 67
    0x31860174824000d9044c0410343c3c071164a0450308004203030f0008190002507070b07441005850070903603200b501a141800300b8204091107446031035035220340c2081d2441034001c4030315080030f0801d43c7c40c0014980341803070901c4203600b00100b4100b00031144c0d0b01e9404048902000601080c401010b0b070260790103080d01c440b03180991046101c0442d1419644640000450ba622580a0064504d0111046150309045007051003070188101517005e800d004034800036104681c08034a03a01865028811162a00090421460545400d140140c020000c08200b030703014001052204030502d07110750440d1910903005045a400b040c2e13580c2ca6581a441940400b50018000d000d11014010000721106a19210300e90242c0c480c90b10512407030032945038a03880703813800700d01c10304541c2c8d266004140ea400f40c94141c54525a10b407049026220304583c0744000608200c40011410080d1041a019501490803909011a1002c0c102c1c2c119102c00028001c0300d80c0a40300b00b0602040f4580e660284081c2031000c1d00c11034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 422197302 1250 422196052 422196077
    0x11030a0521010810050a291f020d0909050f010b07050f010f0e01050a0605280f03032a02130b0301180c061116030b13210201060f030b060d03 62
    0x4030900fa4400b89460380503800c26124500c0d0740c00340551180a0f02d1040100300403000304500e4007159000e483d18810143d450310b417400e03100e00000409007214001c00d1031004114550095a4070500c01000c00040c050010124410200e030040318022900da101803412a42802c0210903194080f2404880b14800c01d02c04400745a002c2c050266403038540071002800303c840c2e0080c02d09542d801410700b01c0791403501e1814849651250ba001d08040e07200b82c0c080d0f1184604658091920a03d03801120f0030028080e000010541d214500b050741d410302806a84141c0e0492904803001c4807404030007980b0180007040b0f44a000d040f98000509004020004540f01e00600350b40030062014081c20350301000c0f00d2a00b40483c5410600030030b040100400241880140f1411180c0c85002a0200601c004014404180030700030701c585c01081e00d50804900c076152860140025490b6000d47c02c840d01550a02400080540b0407940681c00c4039003010018030207654640812028a030b80c51000c50512180580b0300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 422198552 1250 422197302 422197357
    0x60a0504030f2d0206181203150d0f050309040c081e090c1e0f060a0804020d06091410060b0901050708160c060305071709150402150c1c11030a05 64
    0x864080710f60307005044c080c00d09148146554004507008142036202e0001c1d9001c1c1c155502c100e0b94804031446004103902136060000d85c100140050117804e440e0f161080d0010700c4000300050034101c00880f0304110b403208800c0c0c20340d5510340440328008402d5240c407444102c0010074ac9060f501208442c1a0b45a414180f00090200d50003c00c56034041c181e11041c040150030842040160300341d04480c000c1c201349a6102c020100307100203000a0080340008000c604025464000880030399008010001c0c51045a01c850341e80c0c00e00c01e9000006a080c0a80064081003000032a1105a0181d480740c0c503025036900c0f00c0c45194801c0c01035280440c0098890008103441c6114003014190755603011034281443c007001030145901c003c605c1074242446044c04103411001500700d05800c40201441d20715035a5000248000058031a085a129030005086524081c0402d41007031a41c4440201d001000c450f641c00c80c0c12040341410034040e136100304004103809002d0030203404140c0a20385a0003460020040d41e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 422199802 1250 422198552 422198627
    0x9030e090405160b1207021203041e0f08092e080618010b0703080a020a0e0136181a0132030114040e190201090302091008060a0504030f 60
    0x42c1c0c00c44c400100c3c0d6500700f0b0700d03686441900043d9610090100c02c00c0d480c00c083d0180300141005000141000c441d00700040e051000003d201c1d04410b44074241003083c24026016404082860301c600e00c000c0c0c0280c0e003000030000d0828000102c81161510300340407441618205000317403045d0b80c0020403081108001c450303000c040b80640415401961110424035010b821050003400545105005100c0745c14003650101425020315000d10b00b03049031700c120540010041d010500d0b100c010340c2d001da031000b2900c03c14200c407808940b0240e10980146c81000c01070411551980e01128030600780c0c040c1a0215846444148814203c07034800c804403001d610b004411510401c0b094100a00d0003000410401604120385d860009055405000c030061112420fa00d030040e2001c440c07001030b50b00c0341820541e4420360f4540041c59000c1c05480380b900b00b00d180ca2028206511445006d40b15813000208280700a01900d802203a042d1a0302d071031040300315815a0342804c0a00340c40307144041442084000780c920b811 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 422201052 1250 422199802 422199809
    0xd02040903030b01090806040b04060906021c0b0316050d060b031e0705090609040f080f1c1407141914030a060e0106090609210b2809030e09040516 65
    0x1c00150403c080380024182035160390000c00f031504800b08203c0030a42c04170100750b00c1a4800320000d4406210300e0200d0081c043d0503401c0b50440400c072800280e01e110340e80003440c602021400c40b46110b201d038107000b803102400d001d00c0d40c01042456845c0002050b5030404d480072075000341502c140d8a6001508610490154a101000e900c590010021428407000d2281c003c0425540b501d403616207919501094000060000d001c0d50001032805808070740b0b10150b561020300c1066803003011444141c1c0f0000b0344558817020341d15080400c042141c8500400c41000700b0040303044030909100540d1204402007030b88956150620040d03007034800490204100851094111a90004417681030905060b110101600600103024540c00180f08940d089800c0d201264481c6041107081c100785481c982d4a01500e1000a010090f0700050100141c508500c13020780320941603000c1c18036a400c0000200f51800d064010700801c41d505415901f80c102040010b5006000d44101c0b000a0707800500e0740b40301c0001d40d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 422202302 1250 422201052 422201057
    0x30317070c120e09180a080c42090307020f031c0c0605060603010302150702040204030609061b0e0a090504050c0409050304090b100e010c171603030b040b100507050703060513110a0605180d02040903 87
    0x155800b200c43c030145500712003118105009c0540c5010010681d60741f0880c440603100309078103a80c88016950400032144c03035441602c0c0d12186150a4440542098003120013141e000d400d0600083d101e0a00d4016030f030499800400e0028401c44c0b0742c00b400c1c216400034030281c0e00641c08000c048041100c900500d140a40b10b80400200e00da02142415401d2184445500c200072404038007951a544021480080e40c3c200344002030241c8a6141c003614000401d081580c0060a04c1011010b218020001d40211b640404040c4000035006003007055070541c001942c0003103911aa031a0102d940b20343d060070109803044a0019001a034401c01c07000076040b0007001c2d8194009500031034201a4035004811106500340c90a02c5144060030001f5584100c0581520400001081c1076003444400c100003401550441310401450a03c03e001390340e40c000d141d409031107410304602c1141990410f00106412641725644184c204514000b950740303240c2010490a07030103004005c0340000f690301d0b8480c0540b801d00c81d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 422203552 1250 422202302 422202373
    0x170708070b0a050f27010c030605030d0f0c11061308010c12050c03070c053f070b060f04090c0f03110901030317070c120e09180a080c 59
    0x5150400d41400c000b00000010b504003814021130600180049070007080c0c000e0200c41040c420422039526072030082c668040c0c2d60801845a01003500350307120500380c2c0d400b68141c5460180307401d410313a1060303140c0300720b840010780b0078140002249489002036264180248603034a0413040740c5000072a07021542224969966481d55010907a40001100c420320390815400d200070b2a1480d108201408002c100720148460600182d040041c10f00c6820308020030803610801e0032803541c42404c0b10360703540c52072660007032026440218075048000c10345024035486210307444035036030310814420205681a00a5081510361020710b0010b06040c3e029006081110a401d000c0c0b461418400c812800f8910458084c2c00804014000303e58081c99030205030f0040c2c00114120703269100100e03044041c0101c050000840c541e000b0807110343c0030368051023a007021140d249142d1601c412040010104055201d4035a01a404103000144198094031040e40d0b044140c40c0038031000c0d1b692042030189020303110440541c6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 422204802 1250 422203552 422203567
    0x5090601121b0b1b01060f0302060d090f08030903040f140609040e0f1f050106031407080709050a0608090607050a020c011b051510080106031203090627030915140304170708 76
    0xb4401da4001f03068500701451040d02d1500850030501c140828100d0b000d44030390180c8144990705280c121a01d501c02102c5a4901d400d1800715280d03005402071000300010f1320b41c0060500100000c80b442d030340c4001c140618101d440c00801008250180d40e1928501420348044444001486240b0494003a48504d43d040602c48250340d0454405070400c0d42030601e0540c294141c030034886442070b4004518144010305480340f1105907061743c2940d1029500250b41400852920742c070101481c0640865411201c0c191103d82040c0c40e64010002941c0c010791203490000115071040d00001d050707210318814445441581d4640034101240541c044808446007000d01840c00c0480c0c0d010b03030091481d1f400801c5003a0071940c4485001d000403d81100309612100c600b41071100c1359001e44400c20040c540d040b4404418038150706040c500d00f009802040444c0d50000b42e02180b07100328030700c41d44541e590250b01101d074a110910bd420150095407280044940c40c5103551042c40105001800340d02c03095182d018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 422206052 1250 422204802 422204857
    0x3021002071d07091e0305010c030f1802090c1b1b1203030118051905090606190503060115051b2d0a021002030c01020f090405090601121b0b 62
    0x680d0041e4408036641c040c02c000030184c1c0006031034182d480f1a00c00201d0524000e401c43c1c042c1446800c081c2455290542c00070314983c06600c011041606080305100c1a20b206415201502011501a4201c014600020f103144000c1e0b00520259444803100a41000400b601e6850540010856598003003414161006d900c0c01c00b400100707074114000211702e1981882007022000e20303002004005143c6603400714007200b01c00c1c81030050742d550402c404c00040c0b8001100036555030040e587e6501501800d0341d540450b40d08401c001c01621405401015540d28001c1c0034103040406103141d6003085000d000240321080740340b500c10b07a5030103888028048412081215080184e4a518407103281d064071500c022074400200c2d441031000d4040b6920400901c08010603411849418111009544002280040c0c0c00307421002c3e050700c0006072001c00a964540035001c1c2c1d500b1080c00b07104416408010a840000e4103a6001148070340f0310383c80f001007940c1c0e907424010703150085000901c0c0c4081c100c0c0c502c0e1b00d240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 422207302 1250 422206052 422206079
    0x1b150414120a050a031d0301050f010e01050402090108010308070305190504080d0801140d02030708010612060e0609030d050c070b0a0203040201020607031503080309031b1b0103060f0905100302100207 88
    0x490307030000b0304020001a40e410395030315906400241880101c103a000300d85068020241e403100c001500a00552504a001c90510102400365284802448001290a040900c240c446002c01070311410388a9080d501c40726056000010204e0402c030b410400c0900b50280c2d1810340d01403120039142c09072502e00740444103050040925a0350104400a00100300d0749850140422040302c041e102141c0c203c10383c0c00480d080190681040110790b00300040000c1039441264109156401120f08102d075111500d800313922100c0a448940040e40240300d034400c20161548501d03002588610030500e41420341e510100700860840704034202a50220401c001d40d601880b4281d40407045180800c1008038031400045043c60740d000107400701e4030102c00076541080800c221003581c0b18401861465110150145503030381203075917000304042a014203080c11940a40182400c4c1c8881c1d1040003040382c1065285402001e0003011040c000070300f07010020160704c0380032500d40410b89550140c000c0c035041089404204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 422208552 1250 422207302 422207329
    0x1305220b04201804021b1507090515040e040b0a180c060e01090e04110a091407030207060b0a0311030c03030319020c0a0c0b0703120e1b150414 63
    0x101d09050700d01080b403000c1c40c03446422402503a002a15080c0f920f202c41080d4050078070041d0003d100003410140c1100201030710600c5c0440f9801c540741b240d00701424101e01c41d026110718010a42c003e00034422480c00040e50400101e461040c5824141d95007800064541c08bc1d60170f0b075400c0c12080600c003a611050240e90100300ba1800d404144681559900b1400d0b14240300e554104448804070b40c0d00c07a032003042d440005140826040a950038203007400380e140d41031644010b2080039142c030001040314650264003281c142c01000300f035895503080d0054020f58031180048610f6a541c10302601c03182d942e0000c050185004510003010345425000341480c10003c40d8116102e603000344104801c00150382602030071107032090000340c4c0f40c00300c00b5070051030000d00c1c1030002d004104403800450f448d00740c40081c0c00c22900070340c3d030700000501610190088921142c0c1c224442e811180d020705200a003440300f0f80761208041e10101e0240440e1403903120941280d0000300d0380d0120000c51188900e0010800041d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 422209802 1250 422208552 422208559
    0x70618060c050a1203020c030c0102030603012f03100330050403081c181407060c0201022a030a140106050105090919140c0703140a050a051305220b 65
    0x200d00182c40e40c95450290220050556020b42d000700c0c0c0d041d10039010b075041603d465040342e40764a008021306d0f020750000c6803014044e41c64612003841c02c0801a24040540ca0351404582e41d0160a88104542c1c0d8002030601a044180400006c000f980e650070308034a002500007410380010015503c00031500650f80c90404000091009101003070600c0100c6101f0b0750b442c883c425107103800306001009005a05440040001c00700300c03410a2140c0c9100c14501e660b16841551125600d4448c01d480c01001240083c0c0180e00171090400c0b500300406412462148401200e4041e001400c002442c0c0803401800710b840040502d2902c5804100740a0f05000d88000d0804e13904040501c00800c225800c000c002001c45c601c2130310064451401790f071100d04034103a000c0b480c020f00d10f01064805c020b41c0c421581140013890001d031a14003913a600e800c6e1070551121360346252400c2c08c00042240c0d6608581191600d10700500c200252598a06c1c0d0b0f00a004581c2d85401059003c00e44100710440da81204000d01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 422211052 1250 422209802 422209817
    0x3240d061a090c0a110f0a0c060323070e0d061a0117071e120f05090f0708030f1b070f150503130305180a14030f0307020307030b090a0507061806 64
    0xd0701c0c410f01c400d8405083e401e142c142c0000600002d140c2c50b080440703074408542c4c05004028814002800b40d640242e419a4505109107141018501940e1540748510350b01100f000740454689842945002e20b05007000340a03080036070b41078a0300011909500101007210010304000780140d40c02c21411031000010341011510703031515800113030110b800340b03d90301781d08040c4c0084401003900844201c3c111a150f12810058608000d488070004d0030b041d210002244144869100f0103c03000450805481c9800059402c107804281d200540b60440600100c40c032200c0c11101807130302002c108400090400b440f5920740e483c03074803402c0c02c2c02c0140d410101041003c10002c0242481001c4000e26815505d03180069864008901100e8000c0182c881168011240100061001c03280f40041036908011015284c0c0e03a540016030550342d202d0704a00a4058122401c204040307a200d00c03c1a5015110300c0684181003040e80d51070b41020345d42e800c02e41c00304840c29502d41140b55218030b2038003e4000c50809d440f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 422212302 1250 422211052 422211061
    0x170c09181b07080c030412140c100302131d070905010c0308061e040f0c0806041a060a050702060a0c0c060e0102031c060f060210050c0f03240d061a09 66
    0x60041c004840d0140300c0c2200000d442d001c008900c01100c010010840c00d90341c40369201c03c030091100c00580402c0d100d00038400c07480302d080305021605101d640c8004102d41c3d00303a40e01c02c0041d0b0203904000649142d56224010000704020224454190101c48144001d6103103455400540050410307003180b810003e0a0410b4070029400021a0360400c0d0100d0f042c400d015030b80c0901d00300f007100603200c03150818103181c4590300261041c0c2150b085101c0985038082d07503a69a0051004607820740c0c00a0058140c8202c11441070700b000401080340300254501076151201540200ba030315409001e0503000245101031200501c00071006480281206103007601041703d010b40000d56038001c00031041142c03801c501d045424400250f00480061140c1d81c00c03511580d03a52103010f9207603003507485800301c542e0514001554802d8580c040390702c0d0110030310b421411030702da9007125081d08480402011142031402003005a5613a80f000e0300c4280f034801c141c0440c014640c0c0280070b4485c590201058000c5003600d0034032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 422213552 1250 422212302 422212321
    0x91306060c1113240e060616080d06030317070504030f080318120a02071707150c060504210206060a1e0f03060623010e0d03170c0918 59
    0x4400306410080c2820204603400c002182030141c201c03d10b00072032a14400203a468840b51403101c031403107049000046a0f644801c4944084000c60ba030a40c070a408105082e000e4140e29200c141079405510414208880416800125442030700b059011420b4010400c0b60b000f4485440c0d540000c141ca412405e2601e10382c0c8114101d424454000c017504400710000380c00b440c900c05904c000c444031100700c440181503403954200703c2e440400050014011032502050f524010881500884101c1000b0a07107039240c51125028510b110711500100240b00100d40701181c40c80c024640568014415002c1801060388481d0340034548482d900c0c01d41d0054410007003180d80d4a40c9071b004075289800c510102c8810882c0804201119410048000c2d4100b02e01000f031040603132003c400d817075a2610300c103040c0c0c1c00d284400d1300d211915521540000c8103251141000c2c1400c3d03031410040c0d4805d04024814a084030080c54011404480ca442a46404510020030f031818500a40000340e5155410005041c0340200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 422214802 1250 422213552 422213567
    0xf0c061008010902060301030609020d0c0b030a0b01030605060d05040c0b0a030b0406050d1a060d0519060509062505090607050a0506180a0609031704050703030e09090d080613060602010209130606 86
    0x94a0309da502c3c00340f2429074450b01103404070240d002c0850110031340c43e085003005503003080c4c0e16148010b10307003d00c0900a500038813030f00042c0c0c0c5d0000e0120703003080500e0011001520300200100d0704006162400034000800d140a000c008015440104004804006100890385254095846a4254040440450b0000c401901103901c0c200301c2c400f45951f0034011404000c0c040c0c1004100703109140381480920811011010000d02c114400d00540d10b5181d05035a5a40050300c100c924410302d88102142c1100142d105901030419017080c60800d036078140010600d802c80b01c01030380c4a0b04600c032081c00b08803090110640c444502c000722090010000303202d035a50b030f58040d40202203545e03030352030b41003414003603400c0440501f0444c1c3c03940e8587c03415103880c90701d800061100b10f010610021a840c220329150002c0385c41605024020f01c8401c0080000300c418160250070641c011855986007034003942680208e4011381031540001da543c03d00d0b4414000242100030b0b040b02c0a40c42c0c2101405850b500011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 422216052 1250 422214802 422214809
    0x7080a03020d141b010b0a03080d0608030702030d050c01090f08180919090501060f0f0e13031718030f1206040e0d0804110a0609090b030727020f0c061008010902060301 74
    0xd400755424003c413103003801088628103141d0f215907170280002c00c00c0120300052004a2014106000c900d55403060b840c0c0d01d004122000f0351540119000305000f03807040028000700034a070b0f400800c5980c41e80d00d038807201c5941000203841100c1d00164440c0813214200e48409402c205079203d829500d403082075841890507140b0160440d540f00c134110000d01c07001750402400741040c2c0c00d504950725038403070603080595864443c1c1120000ea400014040500746452003514640580381c40e04e291031070703130315801446030300500f0318900643c21602940d180c00104081d041c00f28450826076902c1200640c2d21400e0100141118425800c01c14401a40c40300480c076020f50000c13600788161103031128030305103000001003800d154000780c1540c400164940d00030181403c60303803803100403c4081c503180c05240c0ca07a2694094101e40da0030802c07000e005007400039018540d96001e0348005090002c0300c500c1090590121510501582c03000040c410b040300009040401041050004c00c0244666070224609000510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 422217302 1250 422216052 422216077
    0x4050303360705010f02190803091e0106080c0901080a030305070203041a04050a0626060d0803100f080f1c110102070f03031b020601031106040807080a03020d14 71
    0x5511240400ca00003424880c1ca001090918065007400701456840682e84501ea001480400398001c010780042142c01e01068007000d400320b001c0258490700116071000c1d200071900e110344d01000311194035141680c0c5008032420004685546840c510074900824846403d108020a000402100d80c00040460100768141404143c656841000b41d040d40075030750141e25110f0465031845d43c900312140081c01a504100c40380e5000c2911001c0403100d00504401c0c1004001190300d00e50301140082c88210381c80a00280604040b41032540c664996400c180c1e0100c20f1150a01c1041c015010340d140311001501d4108001c16147c4884070120303680e0142c216901070680000d020040c0b11522030612211002d40c00d0b4002d41d500c000700e02c0c044010b4144103078207900007450712488410f010180300640f0b60350340d00b40d40200b010f41d096448440710800302c3c01710ba1f58042010400000d2b4502c040c0540340013068940c0141c21090014240a8100389201019404200513400c09600c45960136060f18014002c80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 422218552 1250 422217302 422217331
    0x30706090201030612050a0309092d060909081e09030304090c0e0a060e0102010b0121020912011508010e03120408030604090c0b0d0b04021e0c19030804110904050303 73
    0x107000590040030030350040525a44458501c0092240c0041e00010701403180c1e0b100143c0d80e82d64401c0c0c80888100c6541e06c07010380e800c400440e0684400061050005424000024400341d4408a21040303a110321011142c90b000810809406200c0c0034103110045640101079141000000c002a201d109501078505080c2c0c3c0c520703010b10780d035104010700c00038140007410389528a900ca51b005805c100303101c0300640c010760920140c03542d554418040c802480f0f007080c090000000355094024040c1d04801c1c9540d030896042c03a4003194442003401541c0c001a80c0c099000c0b041405d1200281c01d4a44010509a0552040015414146261103525801600100300354bc880e10f41d2000034019122408000c0d110741100c11300402d280107640d00070b0550502041c02040340800c4003081c0130590260100c04458110200310780807541c030b01640200403842200c41a20f0112030b070f0805c118000d103403892054001865003400c110030091540e0310080320141c1100d294045140560360700d5640e03c0014840149580071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 422219802 1250 422218552 422218571
    0x1e03030209090a020c2104420906050702090f2e1508090601050409230a150b030d030c09120b1605031005060a050d1802030106050a08030706 62
    0x3503064900824005240c0c291500740042d03550042c1d0007510b03840d1140e005440d9420000d01340101043c040040e400584e0741442d00d80155040b03104030b40c1c40350100050003100d4075082040410b580301481040a4000b040e811501d0f840144003d010390072100601c18100b20010159680c03a900c154402100c1c00001c01c20b941d1a021908800c00d510a000005880300410780f001c1187e40799540140c62441d0b0840c01da641d0680000c80b0358050a8800c1500e94011000500080c142508015a038a0042d00f04c0d9400041c121640c0210050086c526411a000350300b01108014050000c4084c8041225007800f02184c4a00000d403514103110881c0c05043e9a41d81140c0c0c001d00440a5000400d0740d4011000010351508040005000c200c81c034201000d01e0309201c083c968000c1003a0ba0003401d01c3c2400440981c14403040c09041da02c0945100103110040c403130200100c041c0d02685480800078100b001503041180306050a450480d040184920307112202800110030000075103030b003940c000d41c0203c1d09400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 422221052 1250 422219802 422219807
    0x61b14031003060e1e0102090d0b0c040f03110307050a0510030c120207060207021306120f05030d0507022b0516260a08011e051002120c0f0601050a031e03 68
    0x14580c0c402054141051404c44440e0b0000c140301903a64161100025031000c001c00b95800c034032a43c5907035540162144443c0c0d010654044101e80d2282503200210300d4207840342040c1e4903c807220380c0205c5402e070004145400a090a114050007844141d40403400c4d41d007010006060305443e40c254004050341c80d05222101e911400405461458184045580d8241400d00002a500042c42a8001e01e0103800440d22240688109412200b208003080740c4020b90350b43d8001d010340502810b884038401070112402c9001e86100307080c01218030b600100340d01010020801c034000540c24000000001c0817000201079a001001ca512070030b0f070300c2d040006170180d62501c000d0001c0544040c2f00e40d100c00815039040401200014810040e45031aa9920703603076101962164000d500300220090300ba0908108082d00f0b10007104507001a45005036801d600f4400103c44171500004644440b41d804001885020041408814050141600d0300301016081d601c6502a01060009815942e00b054103900141031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 422222302 1250 422221052 422221081
    0x80a050315060a0302090a05090c040612090b01091d06070509011b06020d140906091203041a0c03061905030d050c120a0306050405280518070b07061b1403 68
    0x11001020b20b622071000e188018000e401c0310090600500c0c1207100441e07185440c0740704501c01c00307000340d49078030b01402d200085030284c2c0640060700754661a0410303c000150301c003800a02070700100e4000682910042541807040d000a000105603801800134858056071180c00c0f0344041e10b082c01d0a85105440c10400b070240903a0080203814035201003440511100c080e0003180c042d03e6800810b450a80f60002c0140e1104002d03110058140c0c008400c00c150201208044d44d8004e01861031403510104810500c0c59040088642520a000000800c2070a10340703139829030744042c0c055200189190a000200380d45500269501d0240700001c40d107000d50300d0040200394116281902e14580b1019012070150180c0700501546114504190020303807150809682500fa81080381101c3d0385034000314280c00020030f4040c00307800c2c0b42c04060b500281e1424003000507000070701101c03031215600c09003030030207604480510f01b41c4030705843d1402e900855141d2001410004511104a031642d0740c680420221980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 422223552 1250 422222302 422222341
    0xb100810051501050a0203030a15030503191103090306060d06020c0f06070e0103020901080420060f120603010b0a060302210a0c020d020601062003040e13030212030103080a0503 78
    0x1481018400000d5440e55003080e8018000ca0116070484445000155402e004000c062401070b401480051000c0c00f02c0e0b0003081801c2d41e41e0802d04003d51301c03501d4003800c6901a140c0840d8224040703601400e5030380d008070b0340c2e1180312003a0007a604040500300000c0c0c840c04080d1000b032013080710030322800c240922030703044400f1742c2001d00469000361001011262100401c507034801c01302d03a00c44071808042d40a40215100800140e4441e205556203580b9940c0015524850690702a100020014a80c9801e0024980b0603a135860860720349104091441801100420950080c0d04005403000369031611480d400a542c02d50402580350001c0e154450445505c3c01004200704545030b09004d40001c040c2e0005500604950a6541d640b00346241aa9240320a100300c50002c0c045118149c7d04045404c20500c3c40441d24040ea03161036900e6603401100f40e8280c521002c4038034002024820140c040001031540a10721820600719071461300c0382440d82c02a28424000e0140010000380c052413900c0072407042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 422224802 1250 422223552 422223569
    0x2030c03070f0e13120503180f070e0a060605071401150303050301151701090f020f1201230102060a091a01080115061d01030c0521072a0b10 62
    0x460b0b0369002600420058030410420110f25004100c0740a2601074031400160800d0a4800d80a5000e0044649074001010380b08419034080354400102004c4c0b250030038020140d0000c14030307942081075603000031b5409803000101600d0404200407003500501662b000903001884800c01000c4c00c12114050105800303094100c0c2c0c007150020042542040156045c0e40b03c2d400b8405840c104040c0554903064000e1a5159091518004001d076a1860300420303a072610500e8007604100d042140550185c1240603c10320400d00d0000510803201c1d58500b1031031728000d0f85640360b00802c440700082e4031610041c00100d582500c0c5e81d0701d030080c082d00c41c4a10001ca03ca00f004c00581e503a69807403141c000c1000c840c840c1c09088920308002641342c443d02401d130500b061011074007544c0c49074000540040c4010b02482085c403100348049140414241112800e4003001c84e403035011313443c1000008001c0709290146080c00c1d404001d404401509100211145c00c0d0300429104c059100c0c40e4500b682003007d61f100601 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 422226052 1250 422224802 422224813
    0x21305121015030f060507080f24040207081b010e1c0e0f09070c050f0c0609040207030207050303030a231324020a020c1f021c030207020d030e0f06190c02030c03 71
    0x7080b00e9903115607c0745140307546030b00e030702c2d1503c4012191180042e11444003404200d194903840c01c540303049003183c50b4002000145010541c0d59900141d410006110802e184d45141c0407445d48028091440700040307440287c0007200c921040c20000c039544881120412100005010300f40c0c49208440b00021002842c0c2103503031901c2c00008200414403903081314513002c3c0d6003c462051000203500b4501039001070420341401408814400250400c0c0029411880b840e08001030648090004600540002c400441c4030740d10842d14620440c002e40140000342100310400c51b81e040401d103680e01682d0b011090500d1120480d55002602000c5107020164a10006250314420b0b0005081300701c6038000e441030085804440161210500034203801d50240c0c208698402401c200ba408800c1e6070416802c005060a2580c0c0104014481080c8114081502c50700b244c0c0c51881d00c9607500100c954101c41007490404599280ca92682021585030240404180c3c00800c55500b4444518810009000c689 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 422227302 1250 422226052 422226083
    0x28021807051c060e011e14010c15091a07230d02070611040b0913060503030f07062408010b0406060e010309080d090f020a0b07120f021005090102130512101503 70
    0x845001d14000101351b81d000451000490a603500d20309910104161580480d000c440d032100fa6a0065002c2d41e10712155075210818002414154010403009038540013070708131300e41580007408650018200d4500500740c12018a4007038180400c5494890880e1005038031000f041c0f03450383c0503181158440340c5c2d0640c0414042010641d01025284001e81100c0b407903120a0003c001d941100c18900549070160010040c0b640710030300c00001486003d00c1b1310700006481685030350304031040c4014101182c0d41d802085041001c003209010b0011000011a4200a490700c1c000001e0800640c0d82d692505250310f940304002840400c000303036605081035a005101050062920880048045204920414140001003007030072180b005d4400d256071151b800791040480060030b852110060401c041180f1608244448a240305c2c081c450103010a10009030303c0b440610101e01100d0b40b070350006406004204070090088200040f810450324a03000009103104d8000020200c1018a400c05001741c0003e04441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 422228552 1250 422227302 422227319
    0x509280608010e0c0405011511031608030610170601031a1201090501050c040b03010b030c0d021c05070507150506030a0c15090603290328021807051c060e01 69
    0xc600420f400c1003559a56203654007004201c0d2005c1c014644c11120046803800381d54000c090341341c1103444500c1101d0030003e80e001d490740d40c080c014000b00d4421070b001c402d100d075504020f580184412454202261f24840c480390f0000f4003c401420541016100c1201154940d4a100203010018002e45001d01410300c042280c1e0181190303007000c43e80d41d8039140020340420344010684040d140c07a144007510310392900481d107206e6000900301c1d840a403c104810f26411101344010101c0a543e001802d001c05422002c000889034010401c0b000d01508120150000e4409802d010402d200d1090016082d103510780440c0c60080034110041050040040119002c102c0d03a1070f000407198603684d94101c10351108030440036101c8c4100303650104042221650001031400c1c0003080380f80c502404640c01032000320036490a080165131118440c40c03046d85640d066040c0300c40c513008426880c03402d058440c1425080204544504d80d100301d0807810360044000d9a0071503410100080c0310420001c081e958444085 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 422229802 1250 422228552 422228561
    0xf1009170304030b0f090303070c060b18090708071508130506043c03050918130c09020a051605030d0606030501150c17130503010204090506010206070207050928060801 74
    0x1561040c500c200002c5d00c8801080404e4400c221100245046417584031054582ca40c0d00e030303011264262038404810b055200d0780c1d00d0070003242100c1800c03412410164032081c2441c01d26000380c0c03941c0c2c1041a060040d140e20319075002c00c144007031074400d54665811145200242c10b00600030304501840c02400244100105961002404111451683c89404007903014094149110300c522071000d00c901d038080780c01600a080200806001e609090b002c0c00c59024141c04c0031146203001500c1c84c00e200c02400000d252010103000034607800c40c030300711400601801d01e029280c43c1122543e0510710060400506000b5038030f400071044c20601c019905d030310018000d08024015180e51448510502494030b00c9010f1411095401581c50302c140381d00607039045190b501c4000030001403400000e0020b01500c1c08d00c020001014108000541030901200082c20000090800011580001820b0080e581d81c0d09046800c03038030380f00121076150700012107210300c14482d100801c04149003807400942c11806410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 422231052 1250 422229802 422229809
    0x10c061415100e0a030201081e040602040603060603050f040f140f0616020d0c1104330b030f0601051806070b01050f10120b010c0f20060304020f1009170304 69
    0x1d481c142540404401c559000800c43c441d503011001070400c10165010f9560706421421001c02400e00b0001a000030083c640305031000c50b0b090f54000360800c000c03581449480c0c09803040b032800744214203080b81c916a10040261001e02860b1010710700b80200603850203500446284841511070760b80004508a455910032200803d44032140030030410b9031840490040103580c500c2d1034450500501d5190690a0751040110036040303503480f030044408001540740600040106112007115860408000e000e508441e8406d00d6000024010300c42e65002d4071841e075602c09030a103400c0791501a0301c0301803c0390107126820150085400154902400b00414005060700c3c0309640b006016014070083c0b00b5445542d00450000580001192a03541c40760303000b40c02008014585440c0307816203030b144e1032005080040300b00d58503206550008000b00711510a100d214200303c07400c500b075180c60340214803049a504e08680c81607046039001c01c4c00f28050009980901400f8007441c4501d41040c1c0419a6030b0700600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 422232302 1250 422231052 422231059
    0x1c0215010b0c07140d260d02071a04030c0f0201181211061305040902030f06180c0105040609050607170a11100207030905090a021e07030f1d010c061415 67
    0x100104d100514a140c003040d441000c1e024982d032452946903001707030900704140b080880b1003400150088072640d81c06082c01d40720200c00141c0e60340351403910070392101400041800e041400030400c004030ba086030717910101e1900404074502040ca2480103d805066003038a0031550007030004042600d250b04081901e403540304600e2004180140c004001daa4080c08641404c12a1b88200601403410141c01c140f604030300c080d04440d541001c5401c0e00b400c01004991041e46010013040700001d440f410001d5040740b4000b0b0914a1808c3c3c14a05c006100c09580c0c01064080e4100040711810000070451071504040708000313454440c16014802401003840f01c40c280c1c040d02c612500300c06403440e2442118a1140d142e00c0f0112014a09014005804001007001c18030541c244900f24410f03030451030101c40020442401982c91400f46070107042180d61500c030408100c81c507800d07007050402ca160b28220802c82400d00900382032140ca000307400390490703146840318844003109014110240310401080242d089 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 422233552 1250 422232302 422232313
    0xf1c08151302070212010b0603010909020406090540060c110d08071205060307031211030706150b21060a0503100506011403090a1704120b060406171c0215010b0c 71
    0x118a006c1c00e9910007885640e0003941000100001c241642c84400a0b5201501c003158140d542e0545204485045804280740218001002c140d580e41c1d0790001840416440390041025041d103c103000c2c0c1050388401021341d60b49180304d50040f07000b1900d2404000300f85003190554955404010b00c2e20b1419038216000c40c0700400103551600035402038510442c0d000c1d00070000d10f071075911216007040c10283c0030428071003520401c0310042001d00c000d080c1c050007108045074900c0c003109010f034041072550002c0111001405404464292007207416490200c0156007481502d840000503e1508646d104590503ca10701040d50903204613004148200d4090302e661518054108400c003d5200440e0003014540111940d940010440540341003072600d5581080d0905490b5102d4800381c158001d01601c90b081d400f01000301174075081c090344000e000f16070802c10f22219502003041d551840f603991b9007043d4801c10540340b45540300b040055182540c035025581303c0e507590a0000340d59403143e00c15250a0254 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 422234802 1250 422233552 422233579
    0x12120206010f08031206060f03010b12011203020a030804030905040e151b0f03040309030803130b2208030c0d0c0c14010c05030612010f110c0f1c081513020702 70
    0x20342c804441222550400b4601e00002207a00c0b40030510001c01d8154004801d0103540320031404c04000d103003c2c0c1907800000e640c94450842000007500141e01445a1080c0c03441c0190000e039011031071000050303050900c00c4240c1c545140030b0b1180011500041e400c50710f00039080d80d81e003000003890501c000102c8116030355a03c862100442e40c2c2ea008c20202400e4108001c0a0101740000000750340c0300303000345403101078107840f03590b0a421548107403134000001c480045d0034014000310001d12900000b850300030f0f14040288030081c0a1013582d444000d010410f020000424029414007196019000d803002049a04640c0c20701604001d108002902c41c00384100000d9985141442007110038a5980c444d03e0456541e8000c0029400040c60808919500d41c0005541d05210713001d02211090b4800c045a01d503081c110304070745009801c84494603d42e104004541220700f8402c05038900346098540480e445e520030161452210310550555041042c040036a50074511590107003002034822903500d20040303c1d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 422236052 1250 422234802 422234819
    0x30613140a050a080a091d09010513020f06070201020a02090108010e15073c02240408161b06090905090309010807120f05010b070209062e03061212020601 68
    0x1400c1c81c00408030340c440306003040441c101c400a410000d02520700500001e44800400c0d42001ca446024080443e0784030074003250407802c0c014158000c9110008080c0d503107158001501914141f00a1806444001280303c2564420310241e64007540242054840b0350b5204407940c024002e1100704011406070389036507003c1071034079904280201207682d40c480c030420300d5641c99241c0c1b000707a101205003817003a1003544020600c590a4010752110b01d4000d000065042c8001600c8280d1b0300c188403540241708020400003c1940050301c00504480704601e800f08c00d14507004a004050b004500607070284840c0c00140380e5402003d410070360b070740d080045c480d680b958051a99240200741c4090702003601d800016106912030541c00461449110020a00902c0107640e1800c0320400c1e040f01c2c00560b000a6103074150b0402c0340c41c95400540031745100761200d80b000c005c3d030714080c40b000035180e060300300411440c0e1007480380d048100540f042420b200742d400690328000400344104d201442c058064040002407105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 422237302 1250 422236052 422236063
    0x31b050102211e0c0f06010e0703020903030f090a0512061f030210081b1201091a030a060b0a0e09030a0207091e02070c2706050d0206072003061314 65
    0x141e464036698100380507150098203c0d052500c041c00c450304140711944c071000007004460100c940d808090300c401d5060031080e040c030b2080281351105141c0100500000d03514000202c402c1c249280c90100e854003c12800100c2c52182c561246511141d0007500c4501e112011850078080e0f207140c0c80d80da000021114103148040701c0713403002940c400030507a044542d041c01440c1166001d80301d051141081240880d04002c80e4001e2921004c3d0310040000501c6001114411001c0b01c00248000303018280315140041d80d102c01c240030081c4090b4907030800160580b20840c07100f020b4801c492183d944c42c50701040c1543c0d26000702c440c400042c4110040081d403a01c8600c10810886600c00c14100050301c0d113486040650b0002d80c0894240348051800500510004120198074808150003400c3c0307020040440c06941302034014900c100001e4030711034016600d09080f0b0302016400000340e1000e4a8003c00c0068515411018a400d801381008200d8008800c1140e0701000b403068480b2104034030080350041d541c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 422238552 1250 422237302 422237353
    0x606010c020d02010819060602070e01120809011206030605042901050307090c1701062c010c02010e03010f1e0e06060d1e1707030e09071e0207031b050102 68
    0x1010b5030005540b01d2041603034007141c14848402c2074440c080038101141d0300c941c410b400603006403000b0302c05d10089402c828010400c022004550720b0643d150a0900c3c41031030130444c18890100c6900d1a00380382504014019500300104011520300380c2050380c0348420701c240c0005d4034072200c1d4a04e02a00c40340c00070281aa04064020940302c0e040100c22401000000c0d44601030007140784890101d0031029814601030050703562000c503424007014001400e00103410041c82c1c10410b000100320140d034401031007100f00307030246030180c8503190782c2020074018488101c0030049107080000410340500d1500c000c55031003a030460300b08440003400100b1911000c5c01da82c040d0b44064649840c401103034a4004011002c8181c0350032900c4c03011140c0d5000c012180450041c00f0358840805c0e01003e258008400c6883c48100740e8060b4080d26040d10010302a284040500144900d90003040c605c40e0f01c208000005154000d00c014403094aa80840c1c000c4da07258450903005100b21102401034100001e101c0781132 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 422239802 1250 422238552 422238559
    0xe1825020a0b0601050d0902040614010f0207031e1a0901062c01140f0d03030903020c0a030308040b090c0402070812060402161403070b0c09120f0d030f060321020606010c02 76
    0x1503c1e0100115020b03488540720006141d25016518003582c1c951180078000c1c000d034147c10140a640b000007400c0d0400700d407081800d54004c1d2508202007402d1010f10b130303141511061400c84002480c9003005081d100c5c0601651210000005c00c04058415440b0006a80360341140b00450b02444c1011001010001c0c1181c60006c0040010400f05001c050b1000790500020081105000380101040320390300d5106050f4002511401a8014180c050103030981090b4190380c121406421514040d00711034001e4001010b08c1c4070400025590481800b20390b8009400034015907030b410540c2071014444d0022217035005013002c4071000c102d062030f01e44201c0c3e840044006901300a140d42c2c0e00c4004603510003010004c65400104940f00008101e00e061900c030340c15089501d5121448801405a64046020900b0165202806042018100142d504244c0c48103150220303686031240f012901400450344000e00e00e1602040207410464483c026226200560707084681076034510004455035480e20002030741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 422241052 1250 422239802 422239823
    0xc030c042706020405121e06060d0210181e080106151103070c0609091505010503060d06061703030103050607180509040204090b0108012c0601060e1825020a 69
    0x7140310080d008141940d01a80c0c0040c24140d540001c103d0b140f0720801685060b0300545141e1091400a841e580ca200c204180102024640303000440c0124481600103481840003004554989200d0700001010758070800e203c00510b5031710088143d4120240f41300d0b0600642030080401d40440503c248012600c00c440714602c0038180590540f04a01c4c0d10351600c1103400100886004200e0400800009148541d0f5810300380c0e10b44411a030440d120442c802c140c410442c4070411051380d02c081a80d40101046900d1010011149001c00040c4441c1e170105160030340c50860205000b9010024604132409507050391950354510400f200c0c002281045510100184441404103081503407882d64414809440045d1250050706d40600c20a401d900c140940e0f91906a44402044c00031644840c007100c1c99211100c3e144541c20150710740b503050013040104180140c03c0c0e04550349d00c41d400039000c000fa5444e1000d07810310f001100d5480a45214150a5070720751401d100e8810b2002a040c00110380000c040d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 422242302 1250 422241052 422241101
    0x1031d070b0702190e06040606030c091a0c060405060708100b0f030403032705010c05161403070f0326071d0f03011d10090206040306050a09060606020c030c04 70
    0xc81d00c2e0020b040680c1c008184402111000202c005007802424041c08001d42e5407a01758100426600160415010141004c40a0090503007040700034051307a141984000011001104441c541d016001c0d12541e03911070041844144100440d550f0b000706402c0d90b0b09107942d40d42004d0310380725810a02c103402d0780010820082c2150b0040c8006144c1140c400c1c43d001c202416140d41640d1a040036102021040354121000303000c100307003441449400105404d1150030000c0750070440700781d600c03600409454000c01c00c440344580c04050048480f03e0341d00c240714a4151000b828000c0c55002c404c0c00c140a80c0c80425100c5000140164406110f07410301e40d61003e50a940702e008240702c080a03825103130041082400d8010681d801e00400c02e000700303c0c042d112130450fa1044001d1418541014408405203090a010056251681100c050340d410800c042090384422009030b00a121108006e020507281c280d003c248185d02280f0f003440381c1d504804664048094908100440783c030042c1d10480c4502c0c070359484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 422243552 1250 422242302 422242319
    0x5010f09020903150403020f06070809070915090c050c120403080703120b03030406020d0306170c10050708040b0306090a050f070c020f1021090302062413020901031d07 74
    0x2d00d60844080c042d94030110483c100400349080945044000da040301c07075002c070115801c1290030740c0f0030818540050750b420711010154680481d0b00a130551240c440007800141120708030808020044400104640d00551f0710040c1240c0202a031000c4901030311152444441040f800e0340c05507074119000900d815000e907802d9a054007c80da060348903d444035007220040d9400d002800060400e41c002e03003c10b01c40010010300721040380e0002c045400e0f010f104600031400028521081110507900381e0b9040e240e02e10150703800d0085880c001c0202030300040116912030b03c10040c50044005450f207005948503215100d00b500c030120b4410380340c184040002851540b2590448a00320b00160905040340410740104900004034104a0003050114585005403440720140380503801c1a0b079001c1021001c40e9074000e40700c54014210503014805540c070010b48540031495907842e040001c00c0e0200d21501e064080b000703900180c000d039010a14082003c00c4469251840300c41c00110100502038150420220 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 422244802 1250 422243552 422243557
    0x207080a030206270105070806181605071502030907031103010203041104110c010f02120c0703050703050a1e0c0302250504110c0a0c081608100b010203090307090213080105010f0902 80
    0x6212070b1201d05012051a004e080c460306003d4420b603a500d0301715181460a20121400d0500c02c000c20003c1c0d0700030012003860b641c404c1c5140210a181070340e512259410202100980102204d165910001c2400b0a40000084c40300440b8896030030b00d40161000400c0500700d00003250064849002c00c00070804500d4a507100c10704c2c3d0aa4400d80a00b03200c544010070f0300319668591031201c0b07036500085d164640c84d0f4820450742c1c0720030181c0c07155142038180d650080103406208401814003001266000d84103000b51541c121008880c401088014030500d00101080000101070740503000d14040902c03a4000d041402c24642d81c018008201c0d149000c0511004140100074016108420302c51200711031801d0010944090040001d0b0100c5030a03e00668105582c0b508950854240760b04100f0040720042410103085002c107000099480c103180043c1d003035101d140c80701b6a150244c180003296150050380136141980a20001c01c08039603c46000344c0c2214003c0c0034114000103048010411000076800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 422246052 1250 422244802 422244841
    0x6101815080d030e0f01020a020d1d0d0f110109080a03051c09050303042d240f0608010b04020a020703080307030603080a09170114010b07020d120e010207080a030206 73
    0x29141005507661888030300380942114a0700000343c58500510350100b08001110000d04204000c6180111040e40a543d82c1448400c66043c007103100d808030002902c1400c60007140c01c029100e02c2600c4c141c0d141c00a9038100300c1d003040700c911307040000201e072552181d5180d006440486000308a03e182c4ca403025140d54200b40131011108a0303400d1f050342d8100041c01030045c52480b441c0110b07200e00340740c90548000841c01e00d8060070400c4a0405441c0900e2415001d00c0807900b040701c641548001400c0e0b07a071200f000c0b8201d01c084071300700100351405072402e900040840b84114020410050088204400d910a0454550042e4080700040c0301041c551001560400d00724100007401554036a51110160401c41c404c0c808074200d100200548003062961000561004008003d148007038480340e4220001030081e0900362030045107107011516081d40c0322101076003000c1054070001e0b400304010056801c0e108410f0043c090700c08000385080000840c0c0980b81d61680140c00c080e943c0080706042c58072280c1c0e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 422247302 1250 422246052 422246081
    0xf0a20190804021020030403050d08091212060d1b061103091008071b03050d05010b131503020d060806070e0306071e14120106080912090609011e02070503061018 71
    0x10817240c06248200001c00046106602070b010125080e2005015110001c0034040319400000c0340300796881c801c00840300311064289140c00309413180300100b501e201908400500000c14600c00a8803d20944150001c44d42560740c0e41000701058280e060f102d004554030305800580560010202078000c115103540500e951803c10013603081d2500302559590802000d9021640020b88607600250320302449001d0f052500d1403900d0941d45031440d1000001030710a0303100c3c01000140004240c0d00c20b80450340c06900d030031018000c0c0394079031000d2512200c0070f031640400705440720310030086030801003010b0348107076000c1e2104c0c203d400700c902c08000403071a002d03400410402d00042007003190203e46e024041c4101807069080c542e40c10728402030411100980310750045e5100c080c2c02ca03008144d00d0200c8040090135601e0648600c48000181c40c6904e0031207078088004003a8528074103003980000c1741402c0311030480c101c485580300e052030038401111740c0c050105d24003404101c03a10300119a4200da032401c0f20343c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 422248552 1250 422247302 422247347
    0x2d140a0e06190201140c090d0204020d1d070501021c0807180b0a020d0912170403060204030b0a0b01030b0f0f0d050105190605040c080f0a201908040210 67
    0x30000550140d2107548542c2d1111000c0b09140da0a660900c28140070540c0d40c0e2803900241410300c6c800e001d0780901014175100d044104455411034655030103552100d8240e42c401e000d1034000c5050250113421000d5030203064803408a00141c950b01c0000c1c01050145030b139402040404107000b08603a80300d002405141449501c56003d0b040917020328405005084003410240c0301c1c29080402400e08524480020800c0681c060520500c50702d12004a501503004110440030000300d040c0503400e02483c3e00c043c1c48244089000001c2c4282705038041d100d84100c0a080001700300d400e00542c12204072664454100c07103070001000d014200a5840e00c89104010203040216005da622a030079180212003020054070340c000c020324500c400d401081c1c00750004840500145502c40c40050030b5140c010454000925500049140b8007026031081c00d040d0402c10f03030303001c4600e0341e205003003000d500c01d94880d141600c41d018060003c6103d03104a500550b4020446119154910400c0b910b0600c16001ea42c05056003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 422249802 1250 422248552 422248577
    0x40b04121407030503041a070815010210060305030a3504240605010f09030822030b071701080a02030a15181119080c04091e032d140a 59
    0x1500050b16149200c1d6072410b03564902443d001100400c980726900e5802d50940501880340e410603226030b400107940d41200e00843c02030340100d00d071881907410600654a072060110900c4008001012904200e484807120a54907031907007240410744403101c80446610426140709904920b40041c0c0050041e07501d44c81d400500c0c5c0c0000d640283c1b4035115501c0c941c2e00c160400007540c00c110703031a140101500b041440140b560307d5010092140890445d0145940b600c00c001840e11550600061030300240004090702d0650b0700a040385c44087c0900507016507036000000c00820000d4461445680600503202108656482d40314568801308001c0405860b895800441ca01070b21228201d10b010b0020100f1070295003043c04410b4034140c20002d03041c000d03204244007115000801d031400c1c03002aa400111a0003500f00351018401110350424420004a002014940c1c0076580012114100c40c4191850001c0b02e0b444412940401004001c542504019102207042e000900100403042c1003000660f107a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 422251052 1250 422249802 422249837
    0x7060c15020c070501031d030d050702030c03040617010b09030d230c0a0b3402070e13060c030606020a0f02060d020f180118090c030b04060f0311040203040b0412 71
    0x80c250410b00740d209000c1001503603414001c00b07012104115000030a20010b403451512403240e0400155016101d0020400350b03403080080b07070310320714035002507e0710740d501e58000804035500d0480480000f04c0150000c215041400e080b26070203c1d00400400d42d00248407820f45038030200e1240416120219044007418108840013000d24840c298098148030003c0d20f000c3c654114050801240c4507040b84004142d8903c0344204d00e00400150300544081c503e08804a16285503a048031032160310f40b80034840e0011101d50300101040c0310300c005209100d104441101104c06a11980005034440146480850102818903165600140181d454810709200e40000e980c02401c2c061804100003030340a15651540000c49523144092038540a168508845c80003030250b2409800316159403a5540c000e02402603101c1010210050018005540c0c1c1d07800c51f402d580400d1005907100210f071141140140742c540300300c80c030560707000c15288842d0300c458881028841300007030b520b414400171900906140744e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 422252302 1250 422251052 422251057
    0xc0b091e041b020c0301060b070b010b03150a14010f1419140723120d02030c19120c0512130201120906050105150a080c09030a080f1809040507060c1502 67
    0xb40540042040c08100000e0500710382180e80022401c090512241d00010b1410017001c1c110782098940f1070300d07502c5501d40d0f091034555515820f54050710588001664030114440160040707000d0700c40e88540d41101d401583c69080700c0603041e1407402b0030031407000020501d800d8540714001d035140c81d00b6203041301c800241d403036800650244c40c866846000b0401a159415590500207040d0b00030f400408420745511000d8010500055900d036008000158940c1080054400b140e040e43e0710b079103000c5120340000c3c28075900d40c1c02c00c2c00c1a500f043d60621030345000d407040358183c4145d0b01e661505a41da02d41a600d903128903810490411184002c1005641d0941c082c02e5102801903000080551502c0300300000c800000c0c0308400c9421080c400d162901e90132080c4541c0c17107084034200c1035403841d20300300080c18240c007200024440100030a441c0c01004090020f026407441203a1144e80356007100c001c10110b590304030303030040441d8002001403020b01d208450f030b01a2a4840c4405014a502d800002c4060380c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 422253552 1250 422252302 422252351
    0x40e1203040507090e15040201030b0f06070f15020a09120305120c09031005040201080f0408042c06040b13241502100c0c35070c0b091e04 61
    0x264809602884411402d1041c0c0d0b400e20b45c02c0005150075140015640d030b0506006002a06069440100c01c4068880e8072a10709c101e80002d140a5495200b442d203071590030344220040d84c20f0500d00765946800c0030380f072085841841c403030340300d65442c245401454241e5090380501241005000e2044e45204480aa2203a000d10511101759443e421325405240c40c1400301514401928200414040580d0300185407640040c007405e03506019684a080a200512807603206640b0510ba1150030710228044a40f00c11080b148805440d0090703c94000b00030603100340c000961350115502032284503540656001c04100718003500d06c640030543c10719601c1c92041003503114500240f08680c40c0803c0c42c2e0305101c4401d00c99800781040120740d4002500601420505c2c0b00200b01d01d071810094203024103422808005120700860800d8283c0029a1000c3c0c1c80d000807800301d4101d503000ca808214400c0c80b50a03164003080203041c00e62520a40081041404036560740c1d190041d45c6d1b0031100b1700c1050003a030958000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 422254802 1250 422253552 422253563
    0x5070608040b06091909020103060806070207030b01050301090203030306060d0b0a0b09031e120c0f0618190210080a090b0412020c040908040302090c1b06010311120c040e120304 78
    0x60300e801c2c1000d10101200818091260030300e00c0030000c914030035601c0056045490b19001842c4201da20058004100c0d81d0045800c3e84a150100800940d001038440b042e03c2c461810031220781d07aa501418240c64003510020341c5900300740b0020380c01c4d09090b0b0150001c00c007203d901240c000c4000010600c111078580101c0031494000074604000d0a0400480840b041c000d144005c0a55070750420a0319a92044403811071400000350403074080b2070403c850540e42079020181c2d035241c2400c08000b001010002255003080c0541c61311002400f13140c0103005030103500a0141c01040ca4290002c4403041e07002000307000034903503858024010503000c410b060701c1144075814100e84001500e402910b06140e468803603100d203041402c170200190541082e9801c803a8156000300c81e0303840e10900b81c10360303000b280d1041850b050b0511041c0b000100001d0001d040764001c11047c081001c0d801d05200401500c0700d004c101c140d0040010725150709080c3c2c4000c00104001c42605c884003128019078000d544141d4090f82c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 422256052 1250 422254802 422254817
    0x504120803010e180c100203072301060f0f0506070c03050f0a052505150405091005010f0c0812041401020c07080d0905010206070e22050708010b090607060e0a050706 73
    0x210035011281640061034840c9004018046103146940d0b81202c0e415540500c86c0905510300d400d001700255600954805808050301250201d2082034050004544000f582400000100c40340100384c46001c1c2e44440181040003820103040c001c450344052812140350042540001c0480c40070300904c10030b154940051f080d0f0200da801d15628000b0341c84a40c1c108690528250302100c00c0381c06130b0804407001926805001766034907c402009002e0781d0302c0290400c00c51804c10907110540707010034059480c00d03214001c64051030942140c1c43c01710054028060720b0308001d904040f1030040070072030303210380304901c4608030b103100300009070030780e0415091412158400841400350034018080011481c07080e143c991055842c020000f0341d5082d02a0200d424010110b407a08216103882c0f202952056107143c42c14001061604100c004000c06c03585c00002620300000403800c2d4030483c3c11100c0d1a04010b200c1c504260b0315480d908018251010034a001c0d1180c440d1442c000388003400b106004040503240c042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 422257302 1250 422256052 422256059
    0x20a0905040b100b0a0903030309050a0b070906091509051207050415050a120f02120705091312081605210a050403200607030b1c05010507120902060f0a050412080301 73
    0x20300e44d08030020210b018044403e10300c1d4088610b100303c0307030546004100c020b1142811030800760600d0000e80182e010b02e0401c0125604090749500300c645a98821b2000e640d07071004558200d1500c0d800000041603072100700301034509010b060a00300d108100303441c84a0742d00c0e00050216100400329094251140c01e04000718a41050903d0050140c5904c0070004489a07644608500c56604020b226848040a05500c4101001000003400000c0e207000000d082c042d0510f076500d0b2241c1e404a41e805402c45910000c43e03c00c2034998051803076980b01c0c0102c040911415110341c0c0069070250246404600245421544a11114051807601500044a0134a030500401c07021620808648801d007442c1d0740080041e0004a142d800015840c1c001610007410000503c01035044942074014403000348140c0602a06602680c007607461a210051500b00650000c0b007920301590300650b004606000c0c44084504910051150500a240491800c1d444020140c803c42d20b591095840400110051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 422258552 1250 422257302 422257321
    0x4060e0f0d030b012f070f08010f050718170c0402030c07020a0614041a070203010e011d07120b07023306012a14010c180905010f0909020a0905040b 65
    0x5107811002e18100d401080d611001c4012a2504a42802005a0030814055041781400480041c0c00700341d65001010790344207191400380070f10203c5a01a07520303040104802e1400f948002d600019100075881810b8034100c0b07030340c1000d0300e5408031075001e000d06080700300c0380ea40d24030082d03101d410744081250320317001e02c4d005201030b0000e076401c000d080c801d845601c0b40e00142c5400136241110091840d95030700c2c01700000850464080c0300d0f0025015800c0c05c400403002c2c03a041d004100381c0342113140d01c4c00e9600000b01700103a072080c142c1700342d0b00328100894051000c6614540c1c0280c5c1304c900c2d070048403c2034500d040b0703c4c00c5006011800184060038992003501403407031184c1d079507005602403800500300c005402066102c24030503400c1000395180020b20f10200f041e4003407903600c41c030140740c02000600d00d1200c0290941010f40e66081046508540214003c00d1a1081506035113008030320745103040c01c144a0b44000d150080c0c0a9078040c882e4180010000360354001c4620591264056105509040620 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 422259802 1250 422258552 422258561
    0x2104050601080c0303160f0f030c0b06041109130b0a0305240601090b340c08030a05042612190f050d02070311030703020a05120301150804060e0f0d03 66
    0x40c507031030300702403e0b03007041d5079000082e0b03540404a20508190a816490031b4805100b404200414941c01103070807405040e048051f801c212409590070204907a40d600c00c1004031a1141c0f6810b00c030b05c80601164400d41007500c0c5181032051000d070006545208000091034940301e541c4102c0c1c030345d40000d4480410340d00c414100940c00307940207403910081c1801400600a4044e600036a4031070100031445298880c40191100d0490b0604000040b4011041c00b100b1032400001d503054800b0b0403080c40000da1000c00104968003400d642c1d82d0035081a00703000d2280f1400134419140241a040c003401d0342055602404070261034440708060390382e035010811812066141c821620b01c1802914000402c805410804403105403210030801656494685401c0d2204034001042461030312000c244907041540018200d0a003e0261049400d0740c01610252405807000740200381488038040c0132070300050300407807805030018440c0002140c14120342d40500d15080c00707440501e01c0c0364018840400348581500c82c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 422261052 1250 422259802 422259809
    0xc1e1a0702030f160c0b210106141804060303050904060803070c0509090f0129100c031803050304090b03121602010e010e0d050d0e0d030806060d09020904080409060b070203060406050a022104050601 87
    0x1c507c5001c0d0704d02880503024000b58801c44140100000c1c0c0b00344c1503007440c1c02d864011100204100420340e100d00300141a034100500140c083d52400201103004000041544d0700164400346010080381040140120540003620080040c4104429070504103020300950000d4001d201c1c1002e035498603c504815940782d00d21019004070720003d1600640e81e4410f007600c2c0d001d40c042c2401180d801c019000c1c00d10b5483c1e16803000d0304600001c540810406d00300d4001d81e444101c1141141c200105048a142e010711030404c15a090b83c041210090042d40901d00e415044001414101c58401092010520f00c04c01140b045603640c200301a628002c07504004440341c000c0c816107804800c0c240564014110360740c0545031364070400021401052200c09901302d650300c9940502003030b1843c1440d01c0c04500a0f00b0034040c00c8001410450041a9500c0c1c070010390391002e4005000304925111a124a0f0083c48050074060000d5000c02c9000c040341405070400312203403174020403090186850b0401d02d081400680 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 422262302 1250 422261052 422261107
    0x30619032a0b0c01050f0a0203192d1e0209130504020a03050313140f090708040c0806010b04031505250c1e1a0702030f160c0b 56
    0x600500105030003249103031103003a80c550085068a000d03040d40500310718550204054040c0010501c100041c1034101c80d01407044503a012040740c4440d403524040e400100c5a00d01345054140c540348803051250409100b983c0801900d00e000d05941d00c0d07250514202044008149486015002c800c10060180f20400011020f0460600c11408002120020503100b200c1400352290301240c191341d1500c480b0001550f215041b02d071350717480407000c9000304000340c805d920b2200f000f08140d40090070a803010595a11004003a22050790b01c111042e0b0b45640d002d0f005540d10000901c003c41c1c5c8440c1000124080e0880c90449902c440c910f1030080030340c10003040c441c00400c0c2880180409503550f1105c01c1d100703038011100451035000005040359000383c02c1001070480b540020340250b104103200018030440c0d010789050035680b611700c40d000040f09003e61701400103901c10007540c0c400c002110090002403503803c0451000070503d84444a610b0842d0308090343c801c00c00100744120380d148070040b20410700c448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 422263552 1250 422262302 422262349
    0x7080d0c0f18050604140411031e07170a050901020d290402070b010501030c0212071b0b12071220031e0c030109050406060519090c031e0216080f0306 66
    0x4001c1440c4d4041c500c030f11160100c40141026040c0c0da00c2d00245050043e80c04003a859203017180b50000c80b00900c2d4410b1030502c0d40207012030051071064500e0016070341081010400c81c1c5686151350300400004002407500d5500780810003a02d00302c1c3c06503403030032030500c01e0820740402c10030300002825000007281071045204008007000113140040b45811141c09080014103840b00003405c5c1d0408250101c58810b9010000b054006c002182560101c016000c2d003032104401c0d191a13180c078040c824540314807091107900c07002402e80b9104182000078040e800d10042841071514041c82c03020800b040001d43c0d6002d0220801206011940f105580b5000320481c1107807a007080400a030a501c0103000340c4091645030300c006400d10a080d003005000f40400f40001855072000016a00d11460302d006800e02c507800d00000c0680103100e40100012003540c0c0344001c420480d201004002035109441200070001045a8040032503400809001413042c094a000d58901e0031004108940c80421301c4010000820b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 422264802 1250 422263552 422263559
    0x60a021002090109031509030305010e040201120902060c010e03091203040f14060f0307110f0d1b063902010501060509210708010e06090c031207080d0c0f18 69
    0xc44005041048400607a21800780c80102d40c0d0604a0b040500300202c1200b0318080790845900c072204041c042c1e913042000d0398031040903001c510ba0030380f00680024a800440070300d00625501c06500b140c80180024600410540d6580c2901c1540342e4a04040c1c001140c0341c54a818006081c40c010b0b5a00e001440c076040c10a101c00107501458013034240c00c115940113038241a26181e040b01c20316108a100380e6180c5c03800c558001d002c2800d19130a40c4d0305009580c00841e0151000404090311102034940e1b001c450081b03400d50300c00c084c101400751016612100d201c044882503a808100d51081001e014404407000d42d4011401640780c80d14000b103a1400c001000903e0303105081e250781e248200d0318001e8040b412014080b801c3c4210300f40f00b8140c02043d50009400a0552002240329818030542d21582d4802e24503a80750001c000c1d00d590540c10200030449481c003d10b0042051500c58190b2505200288241200300c43d1138224820225030284000d08003070307400060026010009442c510703546400d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 422266052 1250 422264802 422264807
    0x705180a03030f05030907120b041b03020907032d0507090609150c060b040c0203130e010b03040209040317041a181b120a0c050406051c080711100306060905060a 71
    0x343c0c100c500b00308021020412005060000d68010607895400301981072180c181030740080010388044680d071009080b030860640782011003000f00c5c1e4008200b40060380d2294000e9000c1c01b140311151400d501c0c4503014107405212100300c1d40320103410700400503661070094000b808522058004500307101c03003c0c104000e200011102040319141c14600307641114480e2801c9005060740c040401c0d405418415001c0d00e0300c1e400405003842d4151241340e10b1800e540c070140100003c000f0b0050703071902e18040000802600b010700405820901c2454030101111014185032a0348005403011209001c080403450780c03036140d1100207500001c0c101c01c45038044031074024456130344c0b1030040701c41905010b2040000c081c0d551019204020b140b410b06031441c0380310514001c00007010728010386200c0c0d4a04030703005c111410681c0860643d02003004243c0e540401e2030300d500009800c608421a6030840c2d040b0f846a0315190324810070303000f01aa4074049861070501d4800784c46681a074000900803007041c480d1512403503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 422267302 1250 422266052 422266067
    0x160c060209300c2d0a0b0a030c0305070507030909230907030b0a1a09091c050415030e070306091104060602100e0c1008150405011203030c0801121b030b0705180a0303 73
    0x3018000700700c4d1034004440220344407000503401041c07850300100341e441c403568140c0c01500c564840d65804210359590343c1e42c1a5540d0191030300150014625100c00c3c030130505507030b004090034003035071120085580954520107007589080b110030002d030f00298410400c01c00e8112125800c071820000500c0a0307203c00184440c560b840e4502039105448006c007050b8030075000e124444642078040d000344a90411040c02600e56801440b401c0c849505803030072140c0c1648244150041c0e00e808001400c0860300c2e40e00c400c406410860025521101582c040c0d410700c1d916445408001c0040350080c142c6a1541180c9500b201d0302c00c0d8004d8455003058031184043d83e00c00103810b240101c141080040c1d81c542441c078041c0b034160f45a20507040361414001042000038440d00003140c82c400d0380d09000903600680c048401d16000c0c0701d07400005907034100140016030060360100070500310000000075141e0320f85035940303402c0080d0f4104001c00c1001038030b42d4007049000d45840d0840403d6440c49031982c42d6030380003030100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 422268552 1250 422267302 422267359
    0x7180609050f0c091801260f07050d03020f0a0b0f06041a1513030b040b01080f0a0204020c01090c1e270c1110020a08160c060209300c 59
    0x3c00300199100c529560b4003450110b10f00141d003510b68940e110790790800c81c01a103040b0361030305a085000c0078403400d0300082c1100b810840140a06141442c0070140280200b4440b012025401403504151010300200302440402e40101d01c07a40250034a1007150014840147c03c1d00d002c0d504101c0014040c00401890960700881560b643c1c24100125035440350078002c080c00c896016041c03640c000140100c51141a006074042d01131100f0b5a41c3e01d140d51a503a6000161407400340c0c101c05040b43c0586007541c0036007850310a810012503c0c5015035540c13071100c00140c208456004034107403a040019542001e0b2005000c1e0b549851440b0220070300030700040c004001c40d905d0b860362908a0b19610910582c0000000c0e10182e08031240340804d0100100650441c4420800203210b540000700b8200011741003900100e415190801e040c1c000d13442c3e100c041d6102c0681d1a400001855640320310080c0441511400c07843c0702d4900140e170094030460390034a0000010300748641035054128405035400e07615032048 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 422269802 1250 422268552 422268571
    0x3060402060a030605150d11030403080f0a0615020610050a0e041103070305030d0b010e10050306120132070512220204140603010b03030c100216020307180609050f 72
    0x100d0381040b07000c4010b41802d41150b500b0403424086007a90080d0035018088980034a030081c4400e400c046031540c0d19020889000e400504500c01003103e103103a1102054100780d8140e0049a10345c0c494070345512195103440e2250050348030f41e00700069180010045006840111409280c4610301003180b103560350050f0002e01a500c01103040304450b90200003100c0215071040c00e480d1501c0001201e0f00c020a00c03806d0340ca003c246404882c0d8080e00d03002c0000f4004094540320a4155140c10051020050040c00c465100d0b6584030034005402203070312449651a00c21002c00760001060000380d43d10030101803c00420310205000c0c032240c40078a4500690321011454203500384440250396410121104070000c0d4100d450400400700035690510f800c1d11480c030590003070120506480c14141d481c03041e02c0240300c2c542c01904484a1000c8150000c0c04000c040c2c000001c404655600060306103400350b48130704c1d04880031140ca03030111034060088100922210304200001d00d8400466844528010034445a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 422271052 1250 422269802 422269807
    0x41a040509100903050301090e060c160507031e02032b210218030d0207060206130303090b0109050405070e1b070302100504050c130203272a1c020306040206 69
    0x100c1281c2007102c0610000d00d00350034480d081d02404d000e8241c2d802170150102c1c8c6070070308094034461540020038038000c010714110286491050202174400106100701116107002c0d06100002003580c40d00558030404075110118800125841018075014084113640c1008444594040000c901d0041c54005688903080c00b514005101402c0a10002c40041c41c00c4070b11301c00706035000340d80103016003160000350039002c6400c40e012842c2d041e40d40710310381d200d81c01c0160711500016003015800801c40c1c40d524401c0c100400c0411941d903500400c3c00090f002210150303a43c504200a002081081e1401000e40c0c0c00c4080031403c0040040245904ca035a04035540600002c2010405100700305901010880c1103013007117541014500662545000189144208801c0701003943c40400d5208590040410244c0c0d0341e080500c0341e1190940c2c0ea6201850708240c05503190380041060400d445045810102c0c1c41414083c0700f8004101c40901d202d44400c805080e1500b0312001620001910350b00281c04440140c5c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 422272302 1250 422271052 422271061
    0x1206060f01021005010b130618030809040b120109030807080c12070509130b090702010c050904150806090109020a12030f1211070506010302031203041a0c19110c041a0405 75
    0x38940010100109019403500c000003903c2246400070340b80781d07e03490b891100940c1d5512007c8a45001d804a40041541d080304108005900c0400801450002500200b01102c00c24002000703540c0f50040b52950343d4480c10030000301540148459801007a60820590b281005140540e00f030007450481542c26150802140045000e0f50aa4011031001040c004041d2003003450407015000e0424128060801000815822801070140011403034049c1d17500b07428144003008000c041d082d032441080c03190a18800104640400303000a502c607004410010501c42c2651042c4507281100743d0202a01545204114000030350058191611607400c0c5010508481c40428880003072485003101942e4070000190202041030118220381228000c400355400008084154101c80c0700490b00104201800721010f00c07a4600101150341140b42d5850007410300c0c00c140300303030504851110100c030045450070020a240c22001c00103a40355000655083c02a41c80d42c0001c030001c4e056012003503100b9030b2182c000a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 422273552 1250 422272302 422272307
    0xf1d0c040b091306120201030f05130204091a100315050105150732210909070e04091a0a0c0f0c0809041b02070803040305070303080601121103090c1206060f01 70
    0xa41015400200441395030340e0300d00481c455021000700d012908004103803071041c2a41c4aa28443c1103101c8504035520b4043d400c00c0010310b100a01224050500214200d4010510035000c0c80b4240c0c039141844054150304054080d41180030300d030040c031420440144000c1c2c6030000900403200c005100e8644074003061a007003880781041c02407150101c14040009a414107803d82e401034540c070a40036140303400100350024030500100100d044901804005a001d107040003000a58400c0f82450121486590f040004042d12501d180980e034002156000c00310382407181c1c0c0e40c5604004450001c1059110051b0302406c03408801907103806100d143c3c08042c081c031081c0c070222042c0440c000e00411090b03000d0b04c0c00d403007141450002c9500610480b4808140c080c0b000044805507900b08000f84500c501e5598115070000f0010052030402810703103420000700c3d0903405261040303040c0b900301507100d1408400203071508a00603106071060040120303021080c1804140c03190058000e980314001c09602c003006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 422274802 1250 422273552 422273569
    0x20a210c0b03011e0b0720030a0302010b0103061a0a11030c0f03191b060209030703060f0501090509030703080c0f1c06080610030f0b07030905030d2307020c0d03020c0301060f1d0c040b09 82
    0x204c58140c05642d00d00c0341012f506622080030402c00b41c9040000d10b03251120580d250056100d610000d50040090600d000d0103181c00402c1c81c1c00d1501140d08c0d1082e0034081c10f04040c21031103005460307071000c12548903451145500421010441c0780801558250741c81d481f440e0341c000500900307407560005402202e6241400550301840d04540e0621441c460804440010442407140e04642490200401c030303803840100443d091290107a9440002d51100381c641c80c0940d000c01e5620100d0181040703e00c1c1302c25502034481a1030312200c01c00103003071454020b0301760038003200911141c0003a40801c414000200800802001e5503003016491281d503840945c00e80090201030381c085c140d40710120b954901d002880d00400b4411225021109a20a00311052240380700e090b24031707031701580140c40041c80790704140c0d491115190107481204d00d10448400882d0031540340e50080c100740803450100703008040840b109045224a0584284041c3c170707000070010b807103001d00c0c0180c400401001450040d030341d554424 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 422276052 1250 422274802 422274863
    0xb120a06050703020a0c150e0d110105070302071203151a071103070506120402030304260f030a1e0e040f0b0a0f050d0b100e0709030201020c0d020a210c0b03011e0b07 73
    0xc40f860441d4027503001c2c0c50007916010040107036007070100261869100b802551102940641107600100722101c094010300402400d078628200b0f07604001a00e000440c1c00a4400e95000d17880c5541c13500d05040072013070101d8040c0c400b8000e611000081040b601c0d4041210200c0c080c2d551038501603100c40c800a81148203540c080d05a00310045403080100817001e06c3e070030300008140d040340d502007500504c0c40d45074018002601c011800d030031710145200030588012550400300786462076240d0413503000201207400004c105000180e607206046007a00702850f03410060a4440c001003401c43c6000001005945600e60042c14034484002286403c0d01c03c00328000644072202e41030b8243e1607d03030001800f05855200590040c07180e0300c440405410658501d03041c3d99000340c6003020311030030014140b1070900d901592502c441d200b070382c080000c221040000b0000d003c2c941c200e80d80c0e0f0b514051010f0120740c501d81c040045100c030741d1020007402c0c4004049880701030748021a02c2c2244480f010340c1e04629a50070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 422277302 1250 422276052 422276081
    0x9040c020f01020a020304050a0905041110030912020c100804020a031101090b04091a0f1819090f260307080c040504020d0605090109090503041403010b120a06050703020a0c15 77
    0x300301d90100e8002c000f407c1030b01e0082d100c070310549984108030000d03224140d034090147c01140b40030340700700c3c24040303104032012410f403e01090152684e610b0360741130b20542e035000d4016002500c0c403001034130b003d5602030826140c501e802c1c491802c0c04d0700001c3c02c901c028440284000c0c20038038031004990051409000a2078112043c0ea100c55032401d80d4005410005410040c0e0003649050f62411301d8078810203c00e10b10094402880070302c030b5070031040c0b40c0300d03024000c0c825445001106d40f4400a00c2d010341450789110742d03000710642005280070514600014803201080313002401c40700518032800c051f1ba510000e00e103800841500d50f2040510940b2458003e1504280006041241800180c025108485064981c1c094507030744d403001c1c0e40c01c5072a0828002e21b246c2082000f040610466540c112074154018000100c0c4032800300080c04000324100c1d0500c00da0013007410901800f050384900c5a00c040c080c1030651a007460354600610080034120010a030300d2802c6420b0b86510324551250319502c03c0003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 422278552 1250 422277302 422277307
    0xc02030f030304110907170703060f080109050114040b1b0418050f1012030503060a0915032108041b08121b0a020609090a020d0203040803090d08010b09040c020f0102 73
    0x80d10800c0e01c0e42d000300c03415151454103403402051800c00c00b40e100c2c071496003a5a804005001020751300e0b88080e01400d134804040d10b591020690322509111a4000d001c5030000141c44c0080b49070103800e4031103516125007090192410400400c02c00c3e03d00a034420481d80c00c41c0c2c03078030305610810f581d00d000360703044140855203908403130310307045003a03880140162010f04004200e6911544042c00c4186d05018045500540c1c180c6840002c0c01400a940c1040c4000c0030254556114504002180c4204610790482c5c06006400c01c10300007082640018061110b4103504a0001400050b000081c007500c0100818841c03006540a58442803198014003010030685150b0003800c044220705070400a81d0540b001c8031a100c00ea450800080c9449281c2d0303020f07040da400d20b402c0c0760400c14070b6a0010050303c030140e020081800080e016100842c41a880742c1401904c0f8101031003400d10b4420041281020b10041100600510058806542403c00116400b141502d910740089041c003065030b9458540d980003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 422279802 1250 422278552 422278573
    0x306141c170f0a02010b0307061d011e020a0c0e0f15010c0507081b03010608120304020a08100f0f140105040b0f0405010f0312051c200711030c032a010c0203 69
    0xb000c000c01c20618158004d200d000189010140c8460180c0b1070100415030700000340d01510000c44080c800d5040506000c4085a541c02c030f444101000c4001400050f0080b0300c905041003c0800344402500002e00829020315102400c514014000f400d00010541c01240b003a15a070b1180a400b85001c0e4020305580c2420390700d4450595841c41030500c010b552a13003018900b02810144541d40888d110500207249110b459443c3c000795a00140c003d90700041e6020000c261100104520520f070004140001501400d60760b5031001c070341001d0f440708485402c0c12065a01c0034880c1401c54151801200d0014410840758005007058040199150300f11341001c00020782c400b5038502034800c50b4095107510070305450380001119203106c4c01012662112050711100c04040499110400c00f440e00c3c8808034400c00e18003a001d040b0341000000b1204605007406240a80c10140b2040c222800300b070f0003c0001000310248055401081c1d01035000300d4506103450840d03603220310141a0240d4000d800d40b01d00080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 422281052 1250 422279802 422279827
    0x30a0216140706030e1c0203072004050705190f030f090f020f03010b01021902060f03090a03020705030f0709021315080a1a0616170d0902010306141c17 67
    0x20400d03895074590180302c0d00001d28038040c0c0540762100401d100900180c2d0b0a5030500c2454101d9014010110712090005034000b4500b1850100d40d070a038001c00000d03400c0c203182007000b507401c01403a240402c10b080c881010400340c00c4841c0d014581041c14940034200c00b60104400400c00518080c01d12030600b0701d41d00030300c40c000481c00c1c0e03004d00a460324003070010a00141820b13601203c85290041e44401c10141408032031020f00c01a651000b06a14179244a20805c1540e94005568881030380e04209140020150100580700040c0070540241580e03c0d44e07007084607103d030140e100d0158043e80008d42441d401c0802d030342043c00340c992000c940c8203c80d001c90f4010800340c41201d000c0102031900d29040081102488070881c0c42e60010310140c03505201800c001014921010201c4540c0050801104054042c102038451400c44680004107030781107000040036541c0f00c4e03200348207031030140001031800d03282d081040e0040a140903064501500381c1c5481001e41051314a01d02d10000701080c802c08082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 422282302 1250 422281052 422281073
    0x1104060c060506060414061606150e092e0e010f091527030507022211030105130b06040e10050a08190b0a090f060e1c05040b030a0216 59
    0x90054400b040142e89080c107201032071149004a101d0509001a030403040d1919200803d10041c100301c1000d038050240d13985034141d440c0010714800d200d0491031b0130b0029280421410707a10035400710081164122001c105880d40e910410079a134552050000701145101c04d03002500d141c110a40200800d07462044214010f0949260403640c03605041144c0050080a0061038105810001c0603610a60012402000344080c44002c80c01c1c84028031003100542e94800352a808003901c0a030b5411300748642480d035000c03104800400d07440100c0900050040d038a50349250100030490030310000f0200c403181d000800f42d010302e90054450703424880804c82d482c511401040b04580055410640c40781d00c2d0403401d0345030440c00e00004080e500c4011210b0104289d5402e080e0044240b250000e0700000c0394842400000245000340d824588074402c001d02c0590811140000101800c958044254a80401011440390744191b000070741c4048041006042103a040340c80070727a000b8940401080c01c91800d1050308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 422283552 1250 422282302 422282327
    0xb180f1006020a11040c030f020a11160303020712170f0703030c0914040b0f03011812021f0e010209090a0902090901270c0305031303062708030a110406 67
    0x1404840d4002440c140005907480c2002e07401065440d11144407020722008004001c00001055110320018520607014401004d0020450342c1d1440b440d00742c0d504c19494080d039100b415440140c06941040860b6000c68402c09503a116034185000c601d141c203081019801d120600c1040b5580081c6500610b00301c0d00091002d14841d0b00c0c02c2c40309050802003075030000740501c501381d1182143d2400c10118038007a80070103c054001400c0380303203e100a50100342150341500c0c02030000304001840b1010302c080c0c144040081c2072588001c0c07800c3c6000155039110342d074503030b1341c10070b01d00d0707180c0e0340351100c0b4082901643c600ca04040c00c02140c62511850700d4000d0000c91030103a0180ea84180801c0490406001c4c010028a04103002d00c2075800400204c40401c4002d5016600100301590110014005000401c1ca40840d00c40b40c034225401d60a05004aa039151803c3e404001481001c481e280c0720707034040c12080c0d500700b64040d4880c0d0303030b048292000e81680c0c108181200000240420581d41120500110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 422284802 1250 422283552 422283571
    0x130e0c010e011b141c0801080d090e0109050406090b011404052d09070518071205060a2d0b09090f0601080606090d021207080706021b1c06020c0a0b1303120b180f 71
    0x41c6102700050329409901d00884c0d205001c3c2d840140700000706504506c0d081407254200180a0f0020384481203078102c213030010680041e17020400c290340d1a140c050981c220881e000c0351005090000c403c10b0740070020130040904040040005040d00005005004c001c00c00684210030700803160f400e10180c018100e8845000c5400450510800307145072240e83d00c03440002c0c004000c42400c264580c07082e1100315002181d41d49070040d5185001c086403813a4001014030400310b0380c07120341410400c401800300400c500000d400311410081507a900264054020200791052542d88501c007021800d00c01d8010800380d00101c555084c00b074415400180c40d0122040d0000340c50a0540701c1c10300700c0e143c1410403416000c01030b00c140c10b2086884d00304e0400b510014004280c0c0c99405096958000381d0300807540c984ca0355007092003882c0a02c00d4035a5000d0b444052455009914070701e0355000340c5101c4407500c4079524656500c604c0003150702c40500e14103e44003840c00c5c40d6403502d405c00c01c20b2039505040719032481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 422286052 1250 422284802 422284813
    0x105040f03080904110a021b2e02010b01050a02070306021605010203041407080c06040b0a200a02010f0305071704051905060a0c0806060f09130e0c010e011b141c080108 74
    0x340901c0314086e00d00400d0a98042d0000b2041000d071600003542d203a80c003030760000c07c03c41d82d0b100c0102e010301025040081898040c0c5075500942020f03007160f02c03032030449060280030410700000c40d50203d10002520781c80311006031164080d550941c0e41f1080c1d4580280b40d580300000744020711040c10442d000043c188412140c4e295160a00c01d600c4040074003007190052002c0c030092018030819000740161400900d042c1c2051001e001100c9003105480c110650550041c03800c4201303559100740e0385080f4081904050000382001e240080c000395070802c42c111350164050101c3d080001c1800764058203c400390400b240c1282c1410134680b6a142500d078400000d2a054245115600a5480c3e5100b6007000384150b04101341c0e26410b11056200389030041e440700d901d955034800700f1724620402028100702c000410086543e040050031850921031a0f5051100301c4540400789100ac4582204143e8001c016080814400340040d20701802c090002d00c202c43d050030194038103540034a4030350495a10904490 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 422287302 1250 422286052 422286071
    0x40b06030309030d140d1b1d0a0302130912030f0615020604020111010902131e0e120d060b040b09010906140307030b03030909150a061d0d020105040f03080904 70
    0x554034402e02e844035406401c50740c100c0355038900030032544482d0307400c88516910705550709096908a0380d400c0207048a5211104046c4605648a04083c540041d19400d40b05070703800c8040018404802444000d1003a41d00c40081d1484980d190031107403ca550006031104003041181d03024001d02440c00c1035810051402c1c0c40018003101c100309d0340c6420809a00645101e03190764004480d072004c0d225600c5540c2d900c40d101d15005840322038001502603d81c5500080b6000b011243c0458003000001c00b4258134141070031580c0c40d58020803803030892401e003000103681d03440c9125024042e1207180e100020504d80801c0000704c4c5211280100f4200300c0c01d0f602d13250401e8a591003620701c0e40620301c070140011800e000256450b400ba81c040d01c0c810600a0450381400d107084002044010100c54184c1494146000092181803400500014200382d0519140c1269004c0c1241812069032f2100742c4108051040441964041c400300d4000d020007680071542c00b03480f414058440e51118806c50b028074507015104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 422288552 1250 422287302 422287309
    0xf06041104050603010308033c0105030610151b29040c030b1e100806130f080318070902130605070b060f040b0d1b050301060e0703020c1203040b040b06 67
    0x4600ba12001800346045900315119184107400007040f4000541c031840c615684e400c92000c5112400600302207150740c800381c2e101808040c1ca81a0b00c1035010380c1c04003060000c900e035904494030607a580c1019240743d0481401e0b00722800004d03400682120308101a018050180c00ca42d0607140d0560381c8120a501d82909950701c21340001210058070005001605200141882041542042841010003d1045c1e00e0200b104428401c1e1401407442851b0300040201140501009621640c400ca8015151141c1c0c0c68540030b410109400034100c00c4004002212142c42e070259114119148046883c2c2c641c8410f0241c009500c10301680485e000b0a000c00500d01e03210320112842c840d4803143c283e41a8445409000400b900c40d170106501a4503401104e10300c1d2140c07450300310017501440000d00401000f01100c420f21078030b60485130090741004400c1c000d0a6a4411050700300040d40340040c0c2e00e010481c00507082c801c1705a850b408146000050000f440700b144030150065000d2020204680c0740c1c070041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 422289802 1250 422288552 422288557
    0x250312020d0903060e210c0f06090307030e0406080d0504030309140109090903141603030b150313151b112802010e030d02010e060f04050a0b0415050f060411 69
    0x7110300142d40050244001002e175081950782445071011203984104000d2001c000e088a1440350b502c0000228a40070b5006080145941c4074140030081c01c20342c01d0030350079141c0341e205400c40076050050104e0404001c0d140c55000400410f0014203a420f10003141000400136030040c80700b90001141458082587d1465412031441c80c18147c6410501601d40031400028001010041d4203101c0c450301c6425a014280d001417101d100c00e17194445280381545009000c0340c941641050050440c4114000c01110210441b80c01c008851182c1c0354030300540c900400120450985214898146110030040d01e82d90103855096018648a0b92401021001d05a0360381000741d0f00340035194481c000c10800401c2c0f004201440c1c500601d04920300c2103141011030f01c0d2080d41d14090f0b005130b5584904d6040350906002c0c0700e400100c01e01c064005810f1a44565642d0854694084e02141c0240c1c00b2400700000300700e02c1198010040f100b0700c201d203011079401c03c08000440343c490081341070441042e55001080c08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 422291052 1250 422289802 422289823
    0x2209020304030c05101416112d0a2604080a0804050f010c02030a03030c0e12070816080606220e011407020102071a071103040305160b190f0225031202 66
    0x40b03902e90f80d40611010500310301003000340a000d245507441d50780c420203000c0c10b409d070061060b191034055145030055100d805290103140d503a0b089030859200086115000c0d09c812008032159000609003d0005e40051040751301c4150140f1079071058030108071000d0040c0084480c110340c00340002110b00015500082d020b08000e526400002d8184c0000f13000354485580c40c0306901d40109910626000301c0c040808105199003140e0201c03208204283c820040202d80e048440e010322001442c000040d80c2d103400c040c0c40d00780f10304200c0803540801801c1e603144010b20340e01c40c4000d0155403249089607000b860100c001140c1107414070002505580140202c0310300c42ea03c0160480c1d034900300c640f00e411410018150004115070071156a03020141000608003660048001d410600d11700f0039840701c0b800c0240e12031000302006015660842030312405090f980344884c10f15040030400c3d030100f00d0078400303c48006404046a201c010b400d030205c0b034041d03005492240c007c0c08408030201d00c042e41d49403500ea0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 422292302 1250 422291052 422291081
    0x11d0105060318120a0c0c2405030a020d02160308070305240a050306090f0c0406050f060a0309140c041401030b0606070501060b1801120608032209020304030c0510 72
    0x2003882000440c0ba8491030f030a0391815603001c0c40d0822110815030303212010070400140c06410340307800d0000d9680480020b00441050601c4e6501200720300301c480c1c0c0129201000d114001c00014a14003954045852148820104664443d80e03020140100c41d07443e44140c00082c0d150000a10703c80c000d108850045600e41800107908901440d11074010450812294101040c490700003807507201000610b0003003000700060980c4040350b10501d4075040480800d60321890400b4010400d0740c030b402145611a02d015680c0c1030b071b1603007400c20036006005900e0008007260f8aa40b000c102e88900400c01c84007411046034284841b80da02c4e500074494490a01001d0403031030040c40851050702d0401d0007011032500c50000810003913a07410040c00142c10414500c581040d110140c02c031250392054840c02c4100800c001000140d040400702aa82c2c0503103441403198a9100c8206240b0f00108207444000384000c100a558a00e081d1a0081656003000b00886152050003410b23514200755004094607140c0c00b9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 422293552 1250 422292302 422292307
    0x3120206010b0d0c020a0209040f030f080c040b09010e180105030c0402030613020703110d023306040b010c020303070614091506010e060408010903080105030f0f06041101050405090f011d010506 85
    0x200c441c01c2c002c00700745060710150b1040600f42401072301d64107075880c4241c1c041d040c560766001341400e0150000c541d88601310104150030040020351183c580680f0103550031041901c1d240d5120f0030040c5c41500300c00d1355041d81b00420041c40702d1400c13502a49a0306136a016401d6943d07141c101d50500040c0e0005890031580542c07280f800c1d035030084580c0c1c064042e05010f8544110040b20821450b41044600c850074401604180042e5030407070b0005a03880b10b81103925040e00c400c801a001d0705a00c034a00900038521490300c51000c0481607104001700c000703a0741c004040da07566650360318114004102080713190071200c0461001941800011071081500e0050655826459560b40c00459007620505051a40004280b00100b90380e40e0900c60191082c0c0701e92030348600c6505007030415151030342050040700700d9400f8110b080c000c02e00c041340350368005038040041411a04114011b03074084c0115000283c008040008001464040e424494129011503a0204001c00009500c0d003505100b40112500300703004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 422294802 1250 422293552 422293567
    0x150c06230a151208071a0118060b0715090312020c031c091502090a030c080102030403030506060a02070b0d0e0f0a0606080304150806040b0402273f060a020403120206010b 75
    0x500000b030102e01e04c2015111102c5500802d00b05100346c0030703040380d00d40c410b00140240003040729104403000b802c41c050b0701c207092004541d1201000d6010f29142500c1d5511031211108060203003a00255481d540395040d510303080114103840e901d0304507074000c20036007404070710070f20800388148655080c41d42c100800180240c1d041813a440030358001021300d40c01c5002400000b02080c00c1c00e00302e030054803908001603540c4c10307d414009c0549202034400e62003030800304061f54000707400280c0d050071500340101c0b260f10360000c039140000804401c0a00011030003120300f2111200e10100f030018000380704100c1000040e444400640d030f01d01940c09480030060307140701c05200c00381c000c2d0380c2594403240c0104086050281040030400342c0e0054603101c10100910140c00c110519050703103c00e10700d2010780b0b803414240010341400b646038040703440b0302d00c3c210b01044c000002c8401820396041004400001c032070440c10302c0e0200e44d00a40c407e200a444c00703c1c2280003200994408035119040350640c0448608088a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 422296052 1250 422294802 422294813
    0x50907090608100302030709020705240a32010303080c130b030c271e06120601112e020306010c02040b0d020904080904060602030301150c06230a1512 66
    0xb0050011402d00c2c071003e100100603a010445032001d401c1551015880e1409031800c1d07840e100c841c3e03040d1420421842c072401c68030302c4a581c02030b41c41300008001080c00e00c15034901d000b15881105040e8418440c414010380203417441041c55040b2032080d42c40130140d90350280c105000340560f51045025080e20041040fa100d5642c0245401c0301071208481d1804512118846100081c0100d86031b04c2d0750110b10610062504088150040c810700c5695a104803001c0005041da101d00c0c10b503640c0c4000010b0103c2c4a607449000d00da14420803800c100c528035000c101200c1614038004400c07508640910079040700d0881203000356800ba401c1a104c0d40c031080126401c02003d440e145000c290421001c2c6100405a81d0700c1d662180243c4c02483d03a50383c4e65400390705110039901c00b50040f005650080004100240140c50b0550310442d0324a05400d55148a00c2d04c40054481c1d03000c410b0b0348601d034540c8419070382803408580d8060790b1840b00800c80c6400203180800144010300c2041854a000d010381030116a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 422297302 1250 422296052 422296067
    0x1a10050c030345010b060a080115030e060403090812070b06090a23100501050a0c110a1d090606010e01171b0406020703060f0506060f0d0f1d070509070906 68
    0x684101d488031600c04920b110010029a545142060003c10014245403100a1040020080080e6420703072070090890070181c24104184241e0651454903425010710038401d0740061030060440c4d00741c50090906080c000c002c2c98043c01010054019400c0380194004c184084904e120342c004403940c0340340d943c0001c1142c02e17080200344240140e119480748600c150310007845030b1420b410504020303050074001000c2a13440002e8104a050003c00c03c10090880d801042c0a0161039220008076030001081b00030501c0c458140d8800c403a115441d941c00036003a1b40001b1017602ca0084581154000e070f4400300119040e1240e41407040c08a030000881401c201410a100c5610403084a4910050101a44901045d40c8550f00250050b080010240304000b010f0140341c400c0c0c2180301040c025400c240b000246c185c852610025220b650010704259060102c0d00001c000c1082d4003c1000f0410b8200400c6030046204845803044d406100d60105003480c0c00114140980e03416600c500c9100d0602c3c03c00d64501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 422298552 1250 422297302 422297341
    0xb1312021801090e06012310170c0a030b041a10050903060c1b031903020c010b0d11131b110f070602010f1a100e0a091a10050c0303 58
    0x241c0000144103101e0781414500802d586000002c2034080140c06a04126041c2c1201598416008503d0015084c003070b4811200141220703004000a06000c0c140d0b1750310468003c600d0590402000c100c000340000006d000c800c0c682da01c040c0250904171082201720744000d40d02a0180e0f0407611290624105000542204400d40c28136038901240c00000a1600c8000c4070506c0112400040701230302c0c2010803551481100c41c02005505181640580c1d20b401011a01705104159010610f1507410300d09401c5802003890161034040c075000c080c10080d059500900c0e4079801081140030604803440907204981c1503100000c2000800c0d200c0300710032106805c03030311128042da200300c880b000fa01550038050800189420340000848010b51413200041d14107822840031018140e0300000c0c240d48035032181c0d411003101468050741200511300007030600100c5070801260b1070326280070b1182c500c80302c054030074405408072202c0284140d640002ca5151203600004c403c3c40d0400e002280c40000ca102c03001404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 422299802 1250 422298552 422298559
    0x31d2a04020d020c060105031207030906080c040e070305090d090f21020603130b130206030a051810021c09021f020c1003020d061502151503030a02030406090b131202 73
    0xc0907034600219040e6004046240d1040e01714100400191500700070303c54400d18a07032801424a0715548010341106c80c82c0c4901014000071800151484000307001301d4010b08250243c044041c104848020000e04080b11000031501c500504030758030314010000c0f401200c0d940c0c2d0344c4590050801514140c50714800d258001c2040c000201c1400690312040507510810802040003116850340c1006844640041c1c9400070b01480340f080240986c60715030489600560710351000c685c1d92144100e822109005503200006409104901d00780031214ad00140030114114401c0581c548995201c04200c0d03640c400002e501c000c001c100c0c0602c8180c50b1042480829890060700c001807207c030082200c44002507010300c00640c0c009403c080400061261402812a40d502c1d8800c0c02401400699201d03000303c6200e418402042c002604c64101c441100c901035009010789031079185800c1c1c01f035500e40090082c5004180e8910010404400300340a655030400c1c1210081c0c0c2c0a45080240c0b894608980c400f681c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 422301052 1250 422299802 422299807
    0xb0a030602072004060f0e07020a060e030c070e1012050a0b010f090c080402060d0e0a0c03030c050712021c021804050321090604060c180303031d2a0402 67
    0x11803958800360007081d00030680c10844070002030a0b62900c02c401e0300000e11a40c9880018444002c1410056081d80c10518800d1800c1c0c441d0741c001e03845c000340020001c2c134582c182001d1003030000340800605880b00c1c0c0e110131140e42c1a250840c0240040045036003203070101c0150001c000d00c40180f401081c84a009906481c180b5419843c0d0800c1030f40244c02c04000d02c402007400300811a40b030311449ca80700e04945410071107070a0581c00100c9521540c0001c00c1500d44605140000343d4040c420441d81c103904c004040b461507524580074040310305841040d600c40c080c200b0002160060b580c15041d25644c024148240c078075140100080c0b00303110510903600903070982a18401c9440d80c210b440d002e580030340d000b55201c2100b103080301d12014407070f00162003079490300703040c4003140000003416600103501900100f0341264030360381100c1e0030700742c0c540c0300c054015480380c000149030b05907001030001e0310b00c90b0704442c5050240d030840b82c2e2000200c200902808509100c00b00c0369001c503001055000c3c00900262 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 422302158 1106 422301052 422301059
    0x80418021b1c120e0a06091e0309030b070306050d0f0215090a09090515070807080c03060102150a11041806050a05030316060914010510050a0f090b0a 66
    0x7040c032443e403802e4200b0854a4020500589800041742c1c03007900e2078203000001d0185c0d8101030300c21040784204030980d001c400262464158141c0c407a19a400d207180d03501c1100080c001c1c09082090358860020449584540b40417038940d0041404134482ca080b40100418044010002101003404115400703143c2c84103070305003044842d5074000060500d403c0c280181440b0f02281c1d00b102906141c000c0085c0d10780c116444500511490b80c401302136a9030f00b00769007202d100960b41d0501680c0801d00d017800d1070f40040c210390f074400115400403490ac0c0001d2a240c00c0c50b00b0a400032130300c0921150ae0344c4c1205525104071030003070004480c01e8400c50f10781808a41c503846141c96039000755800040d40014849190030940c5143c1d4400e40980c10583e08a807045c1c001c0c03030203403540030012003100c00000b02c5107044140c000c10780b02c0410001588914000d001d01c01000058080c5802102071407000 = true := by decide +kernel

theorem cover : BRFrame.Cov 422122302 422302158 := by
  have h0 := BRFrame.cov_init 422122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 422122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 422122302 ≤ n) (h2 : n < 422302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
