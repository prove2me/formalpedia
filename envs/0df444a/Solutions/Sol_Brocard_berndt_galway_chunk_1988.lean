-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1988
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:32.376642+00:00
-- url     : https://prove2.me/submissions/45c1e69c-a623-4e0f-8613-ab893d972356

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 357374100 ≤ n < 357553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 357375350 1250 357374100 357374111
    0x60121150b03030702180901111306031d0f01060e011d04110406050a12050d08150108190c0e0301110c0303010b030a0603170c06010f080606220e031b0303010b040b0c01 74
    0x280401d0a0012603003d074440d003035003542001f604030030900a01c560440d01c0700c40503040403c0350b50610b49003042030141c18107054481e0800309480c5050901c649118010500301d0302a60804000c0d50300030b003e28003076000d19181e01000446c5080c000e07250075900002411001c011980c03262a032405446400c0411075015480b40c1001078103543d2500b41c034000d03101c0c8502d0540115120325041745410b071840d21031800d104014042000600340851800205042820304000341c2d9a0b040005540400b0011000302d0507140030100c020840e406140002070100a5000700160070700201103a9090080078152081d95004000602084a00c0e0300919000f8500c0c8001280840e2650703150490126440c120601c040307008100c01caaa84000c1000a00510395500004083c90800181d2038441c00b000b001036015100b0f1003d41c90300c1464280030014460f88152007001000203845881e42c487e440968031a030001c140c40d01140e89100c001c01100c0c121541442011725091401e450b604d000d030070080168905550b0799 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 357376600 1250 357375350 357375353
    0xa030b0102030405060406020c241902120d24180902040b0301060b0706111e03270c0108010b0406050702130e01020403081213050c060c1c02060121150b030307 70
    0xa1002d41b029001580142206100754801c0c01803c1c00d0340d00c4480c240c1c1d0401c03d80341013840c100307074111440d00d0000c0d40c1d10000d8004501080e49088a40319108010000c001004203d04e141d55001803172000500901c01c041350302441c2c211046046500400840c0c000115500b0000107103588140e20042c0b000c0c0000c02c600411000090865040da4080c92402034002a08010041c0f507200341192241890a541e082c92400706140040034072064140c60326800010100d0740d0030b02d540d2048040d06254006284180c141c2d5040d15440c0e0000b80c020902050701c0e5000031588d030080d40c0903101540c2c16030b96100c0c2040019000c01404400010154602995403042c1001c2c80034280028405180100001c90759140030b0341036110b94400040040c0c500b50552140ca20000710b012407488041003086504940ba081d001001074200320a0910110141c2c0e01c0c4150040d0290300031603030a04880c41c01c9203101089624594600625202010041017900440040a94451340d075004009900020f01101e0a0003501d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 357377850 1250 357376600 357376609
    0x120901140a230708130c12030924020303190b030109050706031413030c03090e0c0301061d0306071808010203130507050108090a0b070e060a020f1218120111031504061401050a030b0102030405 84
    0x2040b1f06078001444141c05216070003480042d80307200d00004656010220601d0700003522030001034524110b90310640d1500005880541002c4882140100200311001d1945000ca03a5074000d0320a4601190900d07402d00d20b40700e81c2e031903098825004c40b20000003000030b40e50206c943d640c200b0303011002c0c80080303680401e03042840b00c2e5041c0b2940994200c2680c9506191024080c0700385ea450003ca80130300186041c80c5500c000c101560003c080341000c0a181789045405040c00d20351350003100c8658801705c100b10a2040b02440200b041d40a074040e554a90b80b12001151021000c440d9086540d0140c25100001201d86000740d07448400d515140008591200020340aa400401d140c4010382c01130b110381d042100c00340007102c128000101c1141ca09200718095054060500003c1449222003942150b0789000039041104204003001c2c00e1960781c9404540c0644210105200c203004034030b441c802151082040104200086050b107580381400000c0358210081e05001c1da00c507046001c00d0000103916182d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 357379100 1250 357377850 357377879
    0xf0807090c0216030b0402180411040f022511040209030706080a18030512070905030a030309020d08070b0a0501091e0b012120040b120901140a230708130c 68
    0x3080304050080c6c20640100034103a1740c03000300050444103130b80c18040028005400700ba9001020744005c118040c000000314002d0107030681000b0150150341c010100a00d24a0b0584100380c07080d0440043c10780d164060004238011000019003680c01178800340007041c000c0c0e00d0310f5800f201d035000100f003100042403070054400c8010003c5011820105507198071400002056900010345c0c82d0090080c1d2a102c0020303502e46110038042d00781079468010b0001d54a8000c429101290041d06035541c0e103a482c42c0114180d041107600301c00c02485c0000102d8000c03614000d14100c00010100c01c0d91986854050b2401068003407003803410f1003001501c40c0760810500352041301151040400081b8024010100e030484000c051000701c8144007040144038800104c0e0660f000c400e0702c41ca1201066035160b8202c1c1c01007180392140315440c5200d60070803094000c1d94200c1c950415601c02105402165012003200c844000d0b65041c0114142c0b10000f428884181e60f07035800d603800380c80140c14281d601d0fa0704c0703004940c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 357380350 1250 357379100 357379103
    0x702030d030219110613030504080d021e06090a11031f15090501210309120c091a1815150c06160c0b07090503100501030201090f0807090c021603 64
    0x80c0c001c6040c60f074540c00b00841c0d001600d40303814941c0c1150092000580c0f210b80080c81c01000e4800c03100000e081c948108141e40250030381e48112042c9020703009019540b00040600c41400707400e000b14000c5140d40c08103030300e4003030403041c0000c1050200543c1ca0001d800c0d15011101c3d00361080340f1584095040584000e08044c0902100190400d049400c018401c8080e80021010a040c1401080400c0c00000d00c2c440440003060303030706030290061404035920515640300d840e09002d4402400e042c0501410fa0a00b1a1103514041110310b59401415218681607590503920210070b109020588016103405a4841e1031050b613a0319040760b0170001a011101c42910481c03a0001048960b140170040120707a8000b4001c1c1503030032007692401d000410b0489000c0c0d000340005840408200303414029010040a040010207503250034101d011800014082484160b001948401c000100401c1e03070b10b41701d401c0d54040c0d0050500780d420602007a01400075004514110b10400c4446070086c00d240c01d40d2030145 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 357381600 1250 357380350 357380357
    0x82b0207030c02190303090b0304080903070f0f0905060f040e01020c011d0d141902070e0901050a060f0f03032105010b1305030d050d0b01170a0b040e0304080a170702030d 75
    0xb00c080f40144200b5080c03494129a24404c00b100500206e504014120200c94030200015500e0790341d403400082c0e50088500281c0c0510882202054001016480344107882009174000040c948d1548201c09550f0144c4009801c02c00e12200010b1354282604606049094940003501d071500e40154103084940c3c0d50703100c21a40b04038102e100003c503000e211a0815001e9440c00040d030002000800740144686840d07401380b180c01102040c10180240825002010703041002969071501c800e06501170081111480c00c040c1c50b116011990740c90240c101021380c2e0a4014801c10b050442da4292180103c3c2241003044403103011400c07818824a010b183d0191072070200c040c0d01c0d20800e8280c103182040d940c010510940111501e241c8080c1c0c00825141c3d40100440c000c10351401080045e204d0b010351003400c01101400f001000040b44503a0040001f40340103403020448090000c045079120301407070050280d01d0f08000c401030003040c40c040c188041090f003000792a14004083e0300107403030082d0031910900031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 357382850 1250 357381600 357381617
    0xd020a17030c0c090c090d0c030b011409091506060c100f0608070b0901080f07030e0f03190c0b0f0907091a100509310203011d13082b020703 62
    0x10060901c0f90001c01a010f40f0f028a2a090600a05c041401150b807050300400b5607040402c24441c081d0309a070011500500c801c01c0550319007150303842590028070001c1c09803038071394007080c200400040c0c04011004211403500d041c1c0c0340c01041214540c45007042c90345a11404a101c18224194030a04586410141000424624005109040048552001d40d41c207100344016041039810070b0361154089a840e480c40fa90345e840c003d00790b0003040070100ca440944100b100000d5083c2000004041200445090300c0e00001060011541e807800508000c0614404901280d1680c012201d1180c03c001610107070b0340480d4442c03040c82d00302c82825800e2486e00c95180110003c2d82450300400b00741c2861450000d2800c00380a0100b03090b03040b1894520744d40c088034220100e0b460a55140005900c01c0e9200a56603942c0d02d4a680b0740741116240c2504140c0703c11b501082c1c5040b008001c1001c015804211641820402e1a090402c0791103030b405c1d0112120004246201d0031014402400001c2c0301351a84020b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 357384100 1250 357382850 357382867
    0x11030703110c07060509150a120506120a15060b2113260405150d06141f021009080a02010b0f030709050c0c07030503030702010e060609060d020a1703 66
    0xd6481251200c601d100301045500104103001c5443e41c203880081c1442566041a2070129262414009210b613103207a002c10716a911650041c184809403402c070400303000701d0700e600d0104200c001c00440c1142d41644211403040c0000d423050341548070009a04000180340756500480e020f107500003017074403504107441e01c1500300c0503000b5102180c1042c08591002e1310038081d55500c202a01c1c3d0f14808060960800342c40818040306241200c02800c0003600b0305150241e49030026031190400f4090303600003800d100307010034540020a0071100705040100f07840382c14240c821091890101100322203045000e280341f04111000135000b200c84182c072440310107548607140d43c4000e084444074070b142440344050100e841d040d554001560415107405400011789078490b00446640744c0b055444603c030f28069820000180080800507610a000540081c00f041c3c0c01d980c01140c8403001180c0c040c1e40604468082110342c106501c1c802c111a10150541d030b07a09403180c8208580c3d40079003a14040c43da1000407400c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 357385350 1250 357384100 357384107
    0x2070f1a090c0f01230d090213050714251421040612020d061706100305030d051503150105010f090e070509010c080a0903030806090402090f06040e01110307 69
    0x1984546810702800c0da141e56400011003241c904161a4104822000f204003501466011001c000100c5803900c0d50710802000c0c520003801402500b41c1c4114141c60889480721080d0040a214401c581e6a07030050315592081d0002036044000c005141d481e260382e003040c610140f000d6851560340984c03c8442150008810300b8545072071b46129180300f9101d1910f004150010201782c90655001e0704000c80c2901c0403a030345000901604615144a81c00c4c044000b0b540c11183d842111300302c413050207468107a5201040c0703031142100762000503e0b0340e104000596942005500182e00070010403805503c20180b400000e20b42010410b003190070348e040c94010421980c0000b11070742a22854108201601c1c0b404680915051004140c0c0080c081c0025002c035144e8400d0405001c02a0300c06101501d507540300300020b00350481400104c0209104101050183c500025498411507006041c403416a40300811400d100401621882e00a52101c00e0309108500030b0084e10011441c4801d9903880e0b18020f180203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 357386600 1250 357385350 357385403
    0x90723030d20010203010b030a11120601081b0f04060f050a1403130f051513110d11060304080c06060612040201140409090609020f0406050108160215130c05010f0909050a02070f 78
    0x203584c0d41d6010880190013442c0c0103d502d900190900703b24540e50f480a03000d40c00d5040c221a0b0040da200001002500607403148007502c250390641d80c40010307241c8111829202c03480346c0e25044002c1601003609034603102c240e400450b40300380c416800c40203000c09690350200e0309044890482d585d80120146101d100010002194440383e000b4800200300c1c216203c1310b03080c00600d0766541c0036001480002090100a403000000d0200241c4055501e20f86414410015002950410007901402c000f1802901d4003038160f03400750b1008900c12446072500c1e401075500c03103852622404034041c140400078640409114052819000780380104210001d44100050320210744901407040d031070721200340f11a03640210f01950141412001c00e148820902080c0d203881461102d21304109224010841000827040c1d0055500c0d21510000b1200d9880c0c10042d600c800b0400c3c40d0b500014000401005900041d801c0550020300d090340c0145401500d031162a0100103c0390305441c0b0200b9000144000f55814808 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 357387850 1250 357386600 357386621
    0xc081c020a02010221060d0212011107030801030b0717150a0906081506040629070b100e16140702190603061d01120f02040209030105090723030d20010203010b030a 72
    0x29101c0034035003400003c02140b40104042e0249c0124a0800c0c1c1c81a0b0035131040c09030060401c11a03450300894900205114003d000c201c0d41c8641c0040403441803401829039203203090800007201410341c0c40702511150301030714031202540520440400640e54400d8455003004d4034a42e030107000800d01d4403400403e07291002e001140101c0c9400701c1000140b42c1600b00d0320404c0000c1180040c00d081460007010307140603035000540307165000c0f414000320343c065403044000c0710505101c06101da0f5807074000c68006800703d1840c00c041600300c0e01481c06c2c40c010100030401a88000c082000201440300c86042080a43d0043e00220b42c0c0d40000340009451342900e0041e680d04280c09401c190304100502c041d8044103c8000c0c031002c407203c11541150768070b40584031003c90103002004286083c1206641d6400300740b04044803460b11880761021b0384440c00d07400c0d042a40c00340c02000c9051804008480d01840c1c2da403044c00500e039a00d1524039042d820300081d4001c0c09903142c225180e003400d0709a08100d8802e03804 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 357389100 1250 357387850 357387907
    0x609050f04091a011404060815070f0c0b0f09070b070804233003280201061e06020d0903030804060b060c031c0c0f0c081c020a020102 59
    0x4001958a220354030004800940d00418566203519000f1110f805804207a1070326210400045030b40d070104030703040040b10000c450500001d0f640780c400c00d488041000c0c3d045840168000000e444074001c0901a200082134038080d400c0b0091501c40c0b024941c415500e680060060f82c05104c0b40041c2000000043c2c02201100f902e4045035a50b00b0310184120320903020f04491040183e14006c030089003425000d00040d1008a40700d01107031810400300e14480c0ca6100100b07943c80150701400b00041501c06805010300000241c0d48240e03110080d002d08034110100f15902e98030089003100600280001c00b056540b07030380072442c1c01d0040180c10f141e001071015042001c0756000300082030380065043e03009500a580012040c0c40e0402090862280d4200079195110000304c4450058064081b000180943c0d0002c114051a41e54101d440200d0010781b00c0c00529000041c001064509009003280d003c00a24402601c0d0700ca05508144e0704a040d040d00541d6003c00e042d80420328031f603104403440d8080030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 357390350 1250 357389100 357389117
    0x506120304060210051306060e040c0905011a160c0303020d020f031309020c0c1e190302030601050913061107031d0a06051b030f1c0b1011010b10030608010606 70
    0x49000f544c030070009589840503600c600214030740c50000c060138214190040c0302441215200e4100ca001080150307803c540e0000744040000b92210a482094145c80aa081a001c0311250001c01505034000c800280c402844a4000000103405002e00100940c031030740240c003003081601c10180c10321000030030b850b031950402c0055602c0c0081c81811541660b2a60500507100d800c00f040242c80d00482c40300385038010f660f00c3c3c09c4030100021003c00b114540421500313403085446412180807142c055200007500f40e405480180300d01c0c6840048694824041d81c026034030080daa0700c61801303035414170f00350604001c40020f0b4041450f170f0007a03a00d040886090b038621b0704520f0b0480420342c070500750300c40e00c000c0000100d115030350801d00a407070210801c491802c80351076280c0803e002280d68000b0315070303040e00083e400440031141d20074044c0e1412140002c0408000001808003a02d4400c41003001030702c0c1d9541d80b940e860300744e0780f101c078a80010750b00d075a40020800e003031091003400c552441d084082480441c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 357391600 1250 357390350 357390359
    0x3070f031b060507030c20040c0210060602010608210705061005010809010e07030b0601090803040906061107060912020f030f0109060506040b030a06270f02090a050132060d0506120304 81
    0xd0401e641081e400034903405d01007e814003004900003010720040d4428201014080d48540c00680c0310b200ca0712160041040c00d99544050342250304d80d11603048990800310105440e03001d07050307000700c4003400c102100f460141655122410f06e94111401c1c40a502120380910580d40d120f1705080e80075000700000c01c0402da09844e03c4e5582c46051000420903810000000c404d64880c030803180041410700201d907265512807440c44042c00e81d60043c50001210780c44c000301000743c0060400100d4034039440d00030030242403c1c120b038550004884180d8002c10031a66400345a1410028078440f1451071000058542c698900346080d52005030040d8480c03401c0c158260111396011030001442c980c456000284000e20880f41c45180c04440c2d860101e42c2c8070000d41038103110f0071004c1255804d100300d03a180d20683e80c000c0503204460081c02811b000081c00d0301103008441c4880102e20a0780d091269200103d103103031001484035800503007100c00d4562281d00380b20203420a5500c03081054000c40217507080a040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 357392850 1250 357391600 357391607
    0xc0e0d05031204020f061305190b0f090418051f02030705040b0c0703020306011d010608252109110306060f01050d180305040311040614010e03070f031b06050703 71
    0x4a440d5150032100c407401103401c42d92030f807103070003118038020b080035407945001c264025a01426128149c000c260040800081480c0303240b03807001356200c0e20388190030300881141c46510b0750004000750745c115540c0d030b0088460461124298407501d100d600207241c0c54241102040c110310241d0381012556006006001d00d240e0480c05035800d40b506030102545412103011a1468407020364006509070082900100f28004c04405400c00305442c2000c405250740c0c0d42c14202d81507a402c54101020b1f1072440100e6003006018050020424102d16081da103c80c05480c200504806240c00c1e0a0300301c0d94bd010007020032000b0440c02e0b1103107a003200903081d646840300c04a40c0780d0703d20303c2100d4100100010402c408156650200c0182c4e0740e6070104d45016030182c600a07006502900080d1007420041941c4501c2e86800e0154000b91510744a048514184c00b80c01500d2001c4483ca19542c14000c511001c2030080140100303000031401408910320250a0b070b442d0f950000506d0300500c00b004002c1200d9004a500b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 357394100 1250 357392850 357392857
    0x1507120c140d0f0e010203060306100608010506030c0d0509071d040c060309021914090105030d0f03020f090d06091101024b0a020108060a0e0c090a0b0d0c0e0d0503 72
    0x7544a029620009410240002e2921840591000d4940140c0c603808510541c090352141c44103a0840f201600da400758108501c80610940000440c1e4000510071410404051900050075403002424000b10510704400c4d94011204c548180e0301c21081041011542046268800e0300b00010680c50b00740354a070130101d0140307801200285078581041e8805c548504404065000c54401c407024501c0e142e45080c01c13a00000d4440034461080c0c4170020070346240208908482031350700d0312248068124050709034065040034081d13000d00381080c010300c0c0d05500c6501281402a108540003e440d01c03903883d11b201c1c20260102a103046600000e0401740002d01240d000d0002c8400f000510411041500fa2014944100042204020b0f1806002001c900300042d0407941d94802d88413400c0a0b900d9405200d180d8516201301c1c801840c0c2d541c00b240b100b42d0100000e14500c0009403070400901d855094171201070b801030100c260101d683d900c800c150258007130001000d83c00106c0b407140c0c0150740340e15401c1e640d01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 357395350 1250 357394100 357394127
    0x114151e04051506031e06150706110903070e01080105010b04080a032a080304020f0306130803100e010f03060608060c07060c21060303030b040b01050307080403111507120c 76
    0x1580c071408540b14403d00c0031105860a4000c05040e0b0702e00d0041c4164506a401d0b848400301d01480d140480c0741c920340310590204041030003884604043d101d482d20f2020b032905203c0d0140c014010840f102c90358500707100324800b816103120342e20f4080d40741c141d90740e0031a181648280c2e40c0910030f010502031498040744184965401d80b03052009458402c0440c03000c900d01d040040d00c0968603104500400c00540d020794030540c0202e5103880310044903818540ca5080071101422560b4403280060009400703103002d1900000c207007032410032090300c8000444c552503013a00f180c064507a42c10340820412090303009617405070400c0e00152100b81814038040841e070040f500b00424642d25a1303009401d40d4824112408480c0150754140168078518601100038500da02003540003d0502070780c0c4106040c0760140710100e40c410394600d440c65440040c12110544e01800450822255140300d60701e06a080000058595020007028501c0c201900013070021a03104504c08500d60924a0171a0043e810994040f0086e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 357396600 1250 357395350 357395359
    0x5031c020703120302040e0f01060e04050103020328080d090b011d07050703021504150c02010510140a180203070818070905060d08071203180c0504020f0c0114151e 72
    0x18a0000d00b90080e01861f0401d02038040c00358100082060341e8003e9604840c0d4a0710b940f01d4006010041c40107481c000d02029400d6404010401c0003090360707513480190a502c810b02003c1000442e074507011240d2000301c0c4040c0b05500c400165060143c1076003120f00614441024816085c3d01c90004080440700420328010303c01c01103070707800605000344410411800c0300707040030000385402d01d401c8200c804a400525111443d08155104080c01449440d010b0048411603020032880c049140d106400c02941d03040d0002c1034010f0009804c6802c940302e00c1c00208181026881c0d04e04100020030710200104030b001c1880441c1c032100d40e8241c01081500a40e40714010100e026664803010800c2064039240060480310002144000d0001170341281090b014107542c00d00c4142c0e0800020201211410b42c00340c40000596000c200c58900b42e030041010220305202c042c14030013462012421502c0780300e031403003c145038030040225022402520a084000845400007504140c8038211070041400c1c0019014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 357397850 1250 357396600 357396623
    0x60108160806010e0a05030a1202070801110d0c05090d0317060604060806120c060a030e0f01020304080d02160c0801050402012003180d023d05090603130212010605031c020703 77
    0x1540700d605c04900540805000c40301c2480e980d1030000030303003000802000c0050194007000700c0c2c00c08040c0161035a10188416080c10000500c48241c002c2141300900410300c0002c1002012548a068030102020300980300e069200000e030b01a001c0814009280511640080000340b00f0f00d60417108054000c1e1007a500081c0c950282c0b40104c2c540a0b100d064182e10100104180ba07005e03505030065060504d94509a402402c00d140c2c07100d0a0740010380740104441002d015034038034202c444e40a0002500c54416042280d1666203400c01c1000da030b0b4120030941d035100c0082005558002c41d400b40184071000d15041c4020710b0b88801901c90180401420300d0030706c0713100c82400703035582c00c0d24000133560000c00820800c0e1150020490703408860001e500d840014802c14070010140c2c810651550030143c4407503240034090000c00249601c0100652841441ca040c0400543c46031150b1129000280000080d821f0034801018034110b03000381d8085040355103001500b0360700d03400b01c2c2c0302c0112540006daa204c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 357399100 1250 357397850 357397877
    0x62a0515090c090c0f070c09020f0a020f0c150c07090515090708040215070201051c020310081c080703090501151404020f0912030d180c09051b0307022406010816080601 74
    0x280d03c916480223009134008140d41c901042c40c10004d00d43d07440c10350200c540000003c07100b991900e000814041e8042c200c85114500d0f0640e0600412060760b8000643d113440d91a5a003030400c943e8240c0329800e40d420f1150500c940c0c0c5c200301143c0c80d0000042c0c03d0800b0380d031800740d0005040300707000106e4601c8104003042000840e4050810b030b400450b00d410040344490700360726040c0002d4104440c40b400100003c000020003280100e820080070b0009141c207461944011803d961076000501008205a41c824403400410828807030301d5208000d2481c040d480a207007076242c03204c14592442052145204004030b8854100b1441202c00c190400c1c0e610300410220000b0b014118005c0040040c0c0d028100104180c000c51201c00d104a02171051780f024004a40f101070304811120119921400384461422041302c035020000615401039062046484541c0b0031094110b014081442d0707485404100c201380041c641c1c01c00c0655500c800c825090743c20f100d900340d40082c065400075100506110640d0034a51 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 357400350 1250 357399100 357399113
    0x90c03070b090d020607060e070512062a07030c03020f0d02190309050910030203060c0f030711030f040806010810180803061c080a020c0a062a0515090c090c0f07 71
    0x40f14260000d142645070281820101c1c0a170142c80c0c2000118002c440303011455203852040c202c520105840201000d6070f0f280c2e2040c0d1740d9801c51650541c81c040803208071940a0b40e2100620300c5070300c40c0e51000c1020005103806403802e8986510b40b60300d40c02040300703101040e600060170a0901c00c001a038070f0448a041c1400c0d201283d50380c1100760000d00c108104000b55108076070350803c40307200390121001a513030148081e080b4000c2401030100900b0400106954a1149284021000d0708000344c07441c08600003a00009948554096025a00b1200040105240a12402902c40d10110382405208a940e401c42c61005646500503c001000710100b030160f181c4203501200701744828900c00e003902c042e0400c038000f9001701034810010302c10410519400d0802c509100300b01ca055031210801d0840103004a50303000c5140c0400c01c16150390411890104004010343d4881c0e203691016131101d800c01e03080c0740342025462410a4020441035081c0400da600000480340d05a0b00c00d02103586484480c034010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 357401600 1250 357400350 357400369
    0xe0901060c20030303011d0c0f04090c03060b1309060b0304020d0b0928020f010903120f030f14041a160e040b0301140a2a0810080a0309030308090c03070b09 69
    0xc2c3e40500c00440046410054045282c2c0da044020b14032000c01d6440584d5080c03248600c041c01135540b0b1041c0410800d604d502d0700060660710700c90a0100d1410340725200c1c0517058200702c0c1500394030a0301c44800c01240240384105c0c0c000e8000c0c180c11a26501c5d050b00490010000b200009000703010010000b84400424001e001e07144180901c102003c042c040e115044003030b094041640b06e501c81c90009281036010b16000c27070407658428048040000d540c94140c0c1c03001e20b091901824503855030300c0d0314202c0da918444c0440d510401c100406a03404c2c50b090460808050024200411040c02c084c00185520511803400055203458074014000341a000b06003d4401080182d4156091141007000d100603034107002d2003006400010800741040e121000c0b8006890070300005a2201010090101d5124010003607200c112541400c0003076581310ba03024030f0505034400942c000780e1044e03402d20800d68400c54040e08080d080e4002c01441c2d00c0200001e481d01d0261041304100c000014048680d0744914020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 357402850 1250 357401600 357401663
    0x20907080a4d04030303151202030c300a171c09080d0504050d0e0103110301090f02091c03140a1d040e011503140102041d0c090409030f0e0901060c 65
    0xb55901c42d40d0301c0c07802502a04000209106030b10700340c500491400c580000d60121260010001c020744030002c4244140c101040103406042140c2c41e13131800700904403000c4c01c40410155030081c0b01c2100c9505041d03406540344045001d10100800a070600b64165904840030f090046c1ea00144840c440d2814040728030400d01e0002e181402c00c01008113004010a007402d04207166262040c003100348200440c200c81515140500c81c100900041c8a0030074503920130507003400f00340c800500d461103071000240b01549149118011003e0088039a00300340c3d120703480510076400c089036241824024074029000d4002c4480c511005850321508810039543c40e0400504400e600c0001c01c18040d89854068207403215000540e4003180320400000381e020144200c1302121280d503900c2126224005000001510151000d03034a50800e00c43c5540903a1a0311480341035a100341c41c0e40350040d54000010300185a00c0003c40e10a0640b44010802641c21141c40c280700c03503010840100d41c40e41c1010502d02d4411080b0b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 357404100 1250 357402850 357403001
    0x3030f01033003020a110d020d0302090a03020d050f010c05040506030c090409060204060905011b03090b03040c0503240a0504050616020703170a1404061416020907080a 74
    0x100400b1280c050380105801029680d4181152205410260f5a2100028030340010391044800540c00b030300c00d0303028022450008000c1102c1d990782c0d4000500d0180b015070291001d41044a101c04000c00903c2940810046410f001d0300389860174000031420f0100410311031003d000050140025a91540b181200f030740e0090085449588508004120a500c0d016140c0410540510003817601500860410101d41c50703030700d0107d928205121503074680c2001c1c00844200c2d18420700070a0581d402e01c04103400310300c490810040154009a03c2d04120005045444034626000500020503008580075900c055004400040c24101c0d410483c90040b82e90f00182150a12020b560403001c0080b004013400030407a610208041e6003020030807031a10941c401c0e00041480d0540b0f04c03202aa000004c0d00e204020003202e1780b100c1c0800d801169441d07000b00c83c00c600007003c410800420704c43c24450080144080c1015078502c0900c00d0071072a4202203116412254001070500c120780740300c2800042e4000d01c4450 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 357405350 1250 357404100 357404183
    0x4090305070f120e040e030a0c0201090b031e34050d02071103060f070207030201230d05040c08030702010917010b060a0305090105150105032404091a070203030f0103 73
    0x903c00c02e40f01c0c0c468180300c009600380c0040a070520f454042c106501504201035454600310038000e0318200b600d035100702d040c04071a640000d029149a8081c5109000000020401120b6100412605940108480300485007269a281d142100d5035520b140c0c14012403280340207020341142503d45000e20b00350310103486d000251040403c03c10000500c00120150112401a200d20070400c1e1010070440e4100c00580c85400204090342c4200b911803000ea14840d0111a50120300e001400719a02101c580d005240d101e6080c401004128900040141000070195080200302e500091071140540b08001c207039804c031800b0058802003036020300c1d12400024185070b9039520800025028120440d030f0349920354a0b045c0004e540e50000701cac0301c000c01c2505a4445d0718640d1100700c1449010701e11800540380d940714450606158070740e4452526000c2c01405521440d42540c04c401c4110b03d0024420401c54005105018041600f0203000d8103607540100340640030300318010340500300500b0101c50145501c2c0c09 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 357406600 1250 357405350 357405353
    0x813030f030b04021b010c0302040302030a060b0d080c0c010e03010219030e01141e090714130605030613210c030507060207021005040905090c0303031801090228060305060d0204090305070f 83
    0x40708540c8103041703160002e10200641c240c0070b404074055444045d4140e0054140e070400a1202e6100c00900300000b0a110380340f0340746858812854008450880459010228080c6690b0b00002e04840ea404c01700d00035450018046e0154a241070001040c009058540e405d50032540320a40161146007101d140704020781c6803555607a28680500700c0c1400d03154003a040441c03030300031010901c0816101c4000c007211100c3d01070230601014008002269810355640da002281503038080c42400d014400340342d15200e010001d4105080350288c1ca4001c4020f482c21010741d040c103160402c000b05401505030900c036407528802d0400c140a48a80300b40290701c0305944215100c803581040103403081e0355940c10200311603070b070703e100d4180e94000284002c0e038142d005000103810304c104000300020380b6a5810010910b8450b81e4040b51205102e008481c4034005000590030000c0700c0b008100c402400e05150a2000f401c1407000305030f0500080ca4042c0c012a01e604684040c9400b0b10220340c2440e91201a02041ca041c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 357407850 1250 357406600 357406627
    0xe070308121006140306010e01110601080706110604020a1a0706020d0c140702030604110d05030f220b030a090c0e04050705030c0402120a0e1e060f01060813030f030b0402 75
    0x2140c0300c02c803070308480340040b520038400c04a014903403581044040c07442d03c84800643e0311003404640711b8100409299482c1c9a6001405518020300041d00200003030341c00c1500c0a015130300e2503250460aa0700c5101003001607079036118034074116000c00e8401c0c0c0024030511104091403050100140840b4000151403136503d83d035900c01201c800160341d40b440711005900ca0005680300e401d42c080e526a002d1000700d0085212070419441c040401800310a00b10f01550b901030854102c85240422030a0224040d1500b00003910300640d55811403024400300350815101045074040a083d0b600240e43d107074905820481500e010750081e000419004400f490f0030300d0003c5c0d80d5140c07409001c0c001c0c020071520052a09150017500c0d00d00300707030705882c6c5519a1030b246000010045a050b0400c10300c50030f44041a1030522542d0349503032028020103040280350041c1c455440308010b034003400800c1007000030014461a40380015013540e905251141c0a841c050104801900740c01124560152000941028490f06c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 357409100 1250 357407850 357407887
    0x90f0f07060e0a0305100b041803171e15040b0d15110c0c01030f02090a030b04050d020303071403070e09070215150f011b1502071401050610030e070308 67
    0x4540d4800e29445039071000e103e5103042c00e21004003d6030221028054400e03558002d400d4501000d44009104520350381e40041880070071030103402042c84200b1000d119503804a90ba80c1c4406141003400120110181c500481c0300d004000381c04120340f124043c4800c1d92181c101140a040040601d00e2079003403411300501d501150a00882e0076131800205e400c0798280c00e01a1110203200001a00c1003205c0e10300107401420940720000029039082025092540e03030302c00204080d5000c0c40e140f05041c907040c03510303600d01a503103042001558001d0003000011940301d005420200d4440000c5600c076207030301d00b0a64030420011a045d1340280e0110800911960015011891a40b9501510415284c07805400501107050000d1500580300400312205540920b214014018546001c2640043d190b1244001b0b00f4002c61030b051400e400041c4141030240d81c00c0c4224088921600810060410070005449050845084410f145d11805006034104050100000842d00028040d50b50344854448a41c0c0d100b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 357410350 1250 357409100 357409109
    0xa0f080325300c05120c0a0507080309120606060313080702030106080102090f040902090117070801060308040504064106030a0c08090601030507290a080108250e090f0f07 75
    0x603800c0c18100440c0d84200c110580040e0040c01900c05c8070340079801c09090b81d01100c0c3c00d20291040341d41c950009407003041500d0040600307601035520307060842c00f0081280300d81841521a83d100303006101042d075401f801c40b5044020000700c078210102c0b40c074010819009202010b5031551030a48001080c04041d001020801c1003110526080383c211000c100480710b134110003a40150f40d503401440200707103040340b09028081c1030046135104c540e1520381d80d0950750030350000c03126280c001c10300308098103140c0a482c01a15803a910491410754070101d1514084980324a03064114941304815601c080c20122400701800140ca40d03552850b0001009020b04031000500c00052a01800240c0c540d001080342816030380d2110241003078a240c001881d160900411544031042c1610342c40b49038404501e002018800d0980d2211910f540c50320803100e081c000c813142d862420140c03102901c130881010107100e2013903403100041e0400c5522144929482d04a1102c060702c568401c003002c099684800081752070446 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 357411600 1250 357410350 357410423
    0x1062a0201120507202404021c030e010207060302192106090617060103080d020c120c0124050a1a0d0905061909020d060b1504140a0f080325 62
    0x10000c0340c0c1c10740d46003843c1c0c1c401c01e492a14101b10740145200f0124054000340020b1040c20f80340385000300d000344500c281c6021000329114029000032542c052203000e00901040c2011824200c182000c00f03800f16548076003e040080000c001100d11400d080c100c0c5a00e410700f04200301d051340303c1c100f05d802000701c0d008550008000da15203a210001c0050201d050f01c4e4011906424061103210680203034210807a025114081e0f000200c01030b8030840060a012544040040340c04e075401400304c102e10800840c020305400042c0020b2220707480d9403940d001152107104000c5900c9800e1401000c1c54044d116516002504185030030382405000503080b4040d100200e43c0e003500000000b003510440c2c02606000390480c3c16040c00001042656000140c805006804040c00a884080b00006640290001c170321507414040c0b850b805d81881002c81e0003410304210004801070801c8a000c0d62401507840707280c0800311440d00b80450340c3d103210198005d140d0005507010800e0030b548140081508107910380011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 357412850 1250 357411600 357411647
    0x6050a060602120307020d0809010605031504060e0a11060c030c0a05070302090f07080411040b0d03020d0f0e13050709180f141003021e060c0601060801062a0201120507 74
    0xb001000710840c0d0240700d45c0d400030410b141d0a1082601c107403100810100c019541c44030f0000d529102800f01e020040246030352141c0c0b07403410389804004c40e03002100068103640041e181000144a5488880100e081201c07896292001055007a00c0c6118427020491039000b40c0c1c004500308040020441c05880c1b080701c3c03230b80450b510566080c4910204070f03248400181044041000318070041c074080c4911101400105e032111982010801d5090034042c11401640004507242d121342d4080211540d1050700c1ca412900311a00c07800080d00c5141d058041d80d441903907080850708007405410f81000030150608a102c520780100a204010320206030020481400c007980112501c3c1c1c41160300d441404034104440c64682076400340002c010268010394000c4081d40707080b11030303541c400000d80758828810b00101040e6052150007804071006910041c180700c541090040f03107280040c40c900c1c0381107945200140745017203800100c44000e54140d0401225107000c0c00d01140c03c0d400b400d0390030880b864400c900b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 357414100 1250 357412850 357412873
    0xf0a0503190c1d0601050d020c030318160b091309020d0501020a021b0303190e04150513110d050405070b0c06090c060f0d0f0b04110403120e100f030906050a060602 72
    0x610703d0300031210b0042d104600002112036020b1800362440003200500142004d0114101c40d1640e4025940308400c001240d1802081240800c100c5030300c010f5071440400e0380c5141c00c1005800303001e00c0d00c600e8400c0340e1286a8880c21441c60340301200c0243c0040940000c03504a05129000b9840000d0036801030140880c040b01c0300043d6003039614100c5001e07000b1481e16402d4101039034080303000900c8804020451402a0482d03981d80211400075413080149540e1078540410014501800c540b406482030800218692018541082e9240111045d4000c201c0c0d5032240341250508640341c000c0000ca1300003184110b0f41650000d66203210304500821900c011340d481c4208400c6008a0b0002c0c170b4500341c00c2090405180d01030300030034005105080302043d07001e0104000b074191050445001301c10301d0003107401c20a0002c41d40c810400010541072054140c030300361000c10b1602e00c2c82d0034090140303d880c00f1015a118481d60102c03240c56040b000410480c02c08440341c401404540c402c1c04010700c1501c00c0d01b038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 357415350 1250 357414100 357414119
    0x110601051c020d1109161805010504120804090c030207050f070b040b0c03190509090f0c0301050904080d050106210e0d0e060c030c010501030b13110f0a0503190c 71
    0x6040012144001d24140315076400c0010036552010b00f1149107051400140c41a110364803100c0c0114806c41d824112680c2c0c6842c001c2281290511a00403410070010400c00c60760850111415a0140341030041d0944990500c0f135940c1c403550b403001803564507000111103071f5a855406407514a113304203903010302d11800341c2683d8038445800f803030b01c8500042004100242c000700c001c142c420701d0202924180301074640c154101c0070701400b041000c03400c0001c0c0140a46807014070668072003841c2950b2801424001c800708a180070500400d801403420b00049000c1c0080c0f141035514141c810241807210b507031240c400503c2d56a000c0c030140c89842518840c035105030914000c00f05140f41c4140100442c82c04201300311943c030802094540c00c10020044044622400c0c4001c04e008000d0304e001140e154907601c2e0031032441d8001001801411079443c0c4040c0001d200c0c0c400c0e0691082d0845901041103140b80024800f0105603100c19818400e082044820341540c1601c100600c1c0a0411140f055541e042501d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 357416600 1250 357415350 357415369
    0x908102009010e010e030114100905060105130501030c12020d0905060c0702031b1801080d020c040e06070804170706091101030b031c0c0b010b0c0c010e03030d090204150611060105 79
    0x50b01083c1801c01e00407155105808580720382800600126140804101c0d91a004400340e0b0080c83c001852842408098120702905800000070f1902034900007844079044c0d140d48182c080c850416403103040620364507101d00c42e0102c0080c1400000c56a440e4020f03a464001c1c042c4040c125018003907180000c11080b00001900c41450700900a0440310412010b48015810480e40107030340003044c901102550012501450301a0440c04010041e0180301e540103460a5450813110b88921f081404c801e40351800800c0042d0042c482d418020039513151440c00c00d1441030690140c0030b00210101c3d4041c240140c40c0c120840e800e00404441e0012480f0800460030b5909250050340c06a21002d07002c03e140700b102042507020b100c0c600d007141242e100ca60b200d82c0162000e0b40700714410308000c80d00e411310307000901141a214800342411402c1c0d0008401084d02ea00615011819003a0703076042800540d206d42e080544000007295080100307680350440906840b0422603029407a02c41c0000228460400c00c03002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 357417850 1250 357416600 357416617
    0xa050705040311041b091409010620010b030d0207180504020d03080a1e05092401150c02030709021308060415020c0307062f0f1909081020 61
    0x14185042d00b1030301d80725252507808039155042551495840c500182e05802440244c0c02e50b0303542e1902c1460604481c610590008002c0d1042d20044010448190032000341c110700907501c025400c0c5441c07001e0000f80100543c04103240c150042420003186164003003114001d13035610422203041c4e010210010021140c085038002d400800312500c00c408640070381801540004416008034030701018003a01c0d5080c0d0507060081040541350030034412500c0c0d051003030305c00541d101c041000f41030440b580d800e101d0351410301c04e40098a014610440d805071040009400154001e070843c0c0460b907490a9801c025030104001c000c01c000350320b0010640130004100607020f59081441310041c8020603070310000a5120440038580c5202c10803071500083d030b450203103440c0000402550000c00d9005400d480c0d22a500d0b00c4850b04030303541040052040d03030b40740e425981d611044007040c904a0007401e5050b19000302582140b800c51040e0b403290840403803547c11a024204184846840100f000007100307500e401244070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 357419100 1250 357417850 357417857
    0x70801020313030c23060609011706160203090301020417061f140a0302040905070608160801030b092a0f0a060e01030905190302060f1012080a18060c0b0a0507 70
    0x108100880e1144c0c0080c1946070080140d40150140b50b845c0413550781600c03040c44860b40000082040600c0c20440c1140103200d0f070114110300c0c1100843d5035407210f00003403041062071520840010b141d44208155104850050001c40d0f9440c0c540c40030708400c01e00d6000307031076440c03280000080c2181b1084c6600444a0541c9e041454110305100000f00c01c0d0706406200340e00400324440c000096515402081d01160003040500803550404500030b100181c020141c41ca03c026021444000c15030265031181103d0b00001180c3d0f09444022005007000801520b03041359024043e0520000d211403412031a210000320340c3c081ca5500e20700f080c0a1461510700c00c0070042010707104a0b0704a94029042241078902c5442030724043c40340c1403009040c02907410b00c00c0d001a800305003000030a00d4a20384085d08508420303030720304100740742c42e04000081e040b01c500101510004188500f80b14000c480f420194401140550011921841c0040800b80844000d64410400380c022600413501840780078040c14241d034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 357420350 1250 357419100 357419131
    0x10b0f01020619020d14040b010b090a0501051b072c07050301060f09171609020306150d06150c1a09060a0c0c150605030d050306010e091503070b0406020708010203 72
    0x507540d001821512101c00009400b0403149651843d1740c4030b0950141c11683c85000c2504040c20241c0318136005070041604000100607141c074559815180b003085880910b0300755511100c0c4c20f01007160708808007400300140b050b0040400c0e41100c0307907401d407010342da2003114a02c2031210760300110518105603a2800410410030060040510909444807444402e0034003001007955600760030200c0c5020412255645c104040e001240000c00e135510001b08460703581903085083c041c0020f0864145021100001500001c0e00040088580c01550043c000c0011300f00e07501100c03200280c0030b406c18800841d4004000000071310209004034441c2c1c003070064a0000e103440d54841c0100c1004100b0280d101d006e000003118900f001420340c211904200c601c135503000c0f030100c0c600303130600d4645010141c1d440c0a210060080150999100d9210b0f2500d103000c680340030158860030442c28403a000d441c41c50b501030207601030200703000203e000108103c035031550888040c0c540d00e583e00b50807030006a0340303030110251a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 357421600 1250 357420350 357420361
    0x80f0a080702040c050c0604050319110c0405130b010e0402040c0c120e041409010f0c0c050d0503060a0e0906070801080703030503012904090f0f06050f090a06090c020c03010b0f010206 81
    0x90b0b000404c5a40c03281012854880c10109051030560111030488540d4030005500b10f0002e10340d2140610992681891701c40440304090b059190541190300c90b00032542c0700000b07401200300d1a24502e0302a00409000070303950710b4566156030500100e805038022410310803148901c1d031081c00c0310882260045a030950b0740454410440e1401e039118441030b40107031114554402c1e05698400c090240e02802d00019510318403c1c0c20800f510301201d900c800780310168552601050011a100c40c01c003801d0310709982e69556030381c0001d04241c400c0d040100682a40c400b0450a0400010040d000d08110f4555000a03a03071183c0142d1b488460303000042c00101d05200403c4016202d10b018940ba400c2d510134601c41c0d8030056074401e540c1d0000d0b4030011442c0e0b195812080603650a01c0744080718095258140078613820500803c030008403181046001d0714803100020034ac002158030500290a0044040c008100264002503032005403554140c425445c00005a80600d002d152002c1e1401e0182c02a041a5a46 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 357422850 1250 357421600 357421609
    0x1409030901030e10020d06030b0604110a080604020415020102130b0c0703060207060b03060f010611010b01091206200c070815061215010e01031407030c09020c07050d060204080f0a080702 82
    0x43c0b040c0829038070824080c80e100560034005800c882d0341e580c0000130b10902d5411725880044019001c240910300c0d0000c41c810308056481203c00e0f0340d6aa040000b00c80e120840070600a201e107038001c070360404581401102ea0b9078190000d01010502c41c1d80b45000d56190342c0c0c07143d014850381501034030340d9102d20750404c00100030f50090700321280903140000350868501d01013401d25408840740741e620034100005000c1250026100d1580c441c107040204401003c0d4400648040c24500410303011100000ca41001c20010f604014410b43ea01c048000412003603602020302c54200c040c072030610313001c2c024020550120008000b8500c10112061003142d0300c840080c0080070000b181c50517610b0003481010404541c1c4410780d14028040c0213a40c0806614500313181440030164100702015400c07004003000410103140c40c80d019180c0f8a48010380d241c80d5200e6481ca0f101082e40510b401c05600e80c4903005002035a4043d104580303032403007507940d505003440300c2c81e4496603400070080116a040c032140015080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 357424100 1250 357422850 357422861
    0x30b01150927020c030a08040201110f0a0201050306030a050f03040906120c120807060c05130e0f0a1508100e0f0303040c0e1305160602120406090e070509100909140903090103 77
    0x105590043c50840c141c40100c1c05d586c0a40046c0022460400030f000440d6800618010b070309800c40098012a1070722401561540b10030034020341000000700c00702d6800e60381030181c0c607031080d800390407100880c40040300c0d162aa00580700d0040b580307103000703400030303148018542410400b6070103611401218200018022060b00341282580d03c06014002280022818496885040241d854494840d0401000606103001c250004445a4400380a100d61200e80158440d0010180740b00487d0709a00b201e200c44413001c0aa100031082e20504491440c04039841c2c0c0701c2c10140c030a00d0241e40d214038400d1400da58038442070320024402c1d00e08010801a0341c22864030039810914503213115070300010360b40780d907413030003a0f02c10140c000a01c0c902070070052903070100b0003c112114031910060401303140079800345c1000a68460050030803080b0b000500443c0c4124101d44200c44c00400c00c40f030004038100000c01000c0b550141807002c1c1c1c0707802c81055503a801d04000c503100d464070100861034850000011400ba26 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 357425350 1250 357424100 357424169
    0x60f031f03020907051806070f170d11120108010c08040807020a05060703050306040501050a0b121b04030503030a050a05040807120903021c0302060c0708030f040f0507030b011509 79
    0x1a030421020005950b40c2c10f806010b801c19640f00e540703844240c0c00c114a5007120800b05072040e2005c1112000203800340e002c81000c039806c14010000360750290390b5000507214040b891000d4902c1c01c0d60043c417000c0c02102800a80e040501002100d80c0c81da0321b12801c072000c209070384003c00c60703044c0042e00040c22180188003d034401340c1021131503680c4502280381070700011000c401041c0f001c4200440c43c00c1074070840e40100012a80007628619040b0f41c00510301c640f900c0710382030b1051b4000040d07540142c29003130034001c0758194030503030717240d5490138042c3c0c507600700780d03581c0800c2401c10b00440d134900384601819005c0c1c0d410642e414a070800f00c0d40e940400f00510741c1d0001c20301243c03a40000160b6905007500c600d00f9020344821140781c003a03140081c2000300082c02c1d4a0542020b20100010030f00c84404d07a90b00041d00d0140703040a4a440c2400261010241e20042c42442106404001c005101220030304840c114800da1401da401c514060303c2c0ca48050055868128101e148010f800300e00300c10440000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 357426600 1250 357425350 357425401
    0x80a0b01090b030c130f030302010f050c094510030c050d0311010603080903010b062505030d0c02031b0a020904081b030705010204061b0b0403080c0d0c0804030806060f03 75
    0x1918130503105136205c04076800041490300b43c0908005250b0207010700804c080c0381030000c020a24080c0052851401b408040c58015200d40307460b0318410007401d20801d071038000c42800b219100301030548141c0903c50807a00b0300c2c03880c200300701040b40c0003543c4070601c042e2548105d03101c040c94104400e00600c298409001c0d800c0180103030844160586c00e1040e04059801428104c3da2900680281404e54a84440c0da03070107450104021404240540e0039010000402c41307520b0206007080c04d10fa4550b020752070400480c50b1601d03098400c07040d000001001101e900002c0c00c04136210215200e41c864202d4003020350072000410000300003d01140081152007030a80c0c0c10102070b0a0481c295281d03401451040f1107a030750009050069a030800c042c010b0a20f000b01068614000a598181c00311001500040c1400345403008140c400f40c00100b03903035101d00c005100300076000e1801c00051010400b07490581c0865201070104034030741024805c40e840c04000320040ca00c6c0d5152103200c008100386490104001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 357427850 1250 357426600 357426607
    0x2030402010905100804030906050a080a020d150b070501060501050a050318010e03040b3c0a09051810060e06160503090d0b0106110114070509040605040507020d080a0b01090b030c 79
    0x59075084851106003419582d40041486d15183c0646624480c1c0c20200c1400000e101c181c480c0e60b48540e81c294010345d0b0310405a05c40005c1380e8054041c02e04003140c1d00b4260040d4201085140086000c0c0c02064020802401030b11b46da80c005440740e11a0a81100002d5020400a0880a140003440b000c6401c064000906906007040803802d54015401402070f0a8000034103400011501c0c0004061640d09804031111140e0604130140d4a000c00071010088000403648034521400382c65050010900500741d041042a404c04a0389800c000712034880030343d0490300000c103101d44076500440c603100000d07160b1441c20150002c1d043d140f00340d0b90003c851900c820007090980d030300d0312070b02c0400d0766204801201d10317541003190180c42d100c91155071003031680c034005078821540109102c1d1500b208c5241019941c0e18642e001041c0900365541020342c00c00c1c240414410071a0740011030b40c40500007661041c0b116161840346905441280905900040740f00506209501c2684001c0d5000f48118807039615 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 357429100 1250 357427850 357427859
    0x150608040507180b01020c03010b18040501140a0c020610030c0b0c011107080304020a0806061302030702031b07090c030b0d03031131080f120d0b1305040c0e01060c0204020304020109 80
    0x20300e20250401c160740c64003440c1301656010070840220407011802401b403005035802103051504181c00114403090000d01080c2405401e61145901c01c0100c004c66004e454885850b101500c0103100c1c0500601c6100000303240501c4c001c819405480d84010180603152074020150f10542202c480060155a00c1186416260800004050f60ba2007580c407952245858010001d0340c44041e44003c115400178420827225aa03903500b1039010ba000c0c001d00680f0f03602c0b410812481c6016070241c030301d031031003441d841c0e101c458400017000409c54501c154103120302c01c03400c0340071000e03140c11424598000380b18880c1030000038000d40000c0d1284c00804521400c0204045800d03902c1410341d021181e8194121064034500d20340010f0f2a03005c2c082c100010099170091001c040c0d40c03450003036804134640b5000305400d00d101519800491210900810781030b021205540ca45000309801e403004c88080e44900030004000103480c81250490b140c61300c0c0e503040c42c070564003800f02030b40c4000c000f00d0400050302c40c01300c1d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 357430350 1250 357429100 357429119
    0x501111b0f031609090212120322050d080406060b070f110105090a0f0305060105040b18060303040f03050c10020d0f0e0103020d0f0203061915050c03072a0603150608040507 76
    0x4005014100010603583c211b40148401c103000400300100c65000b1290400d42c000b04101180d801140b1030782d0240010840c4041ca0520b042040c02c02060350141706848646198400c1942d4000da02a00c4108840c90f5200f181851a205101c0020004c50317042c030141c0007050142c206c2002c00d24041c102145000c5002000803201301140d0040d03032010100060a00c1801020000c1e0b90240605a03001c02c0030340907003c000b80144000702013000e81580340d840055030301d850a00a0b900102980c840b140003d68981c900307603844444922030300d4050700d02110101170302d500c006041c810221a0382c550000f0b60348d514508881103a003a0078044c2c14147c08001070035900c4024842d0082c0510b4241c001622410040f00308030440d040b0b032005803003052410b03000303108c4c2031900c0c030381041c0440860a100e603a0301e005030172113401e50142c481d01030607003003404c5079103000d00b203541040d0800c100042102c0d08140707486520541c1124000c082c4100c884c102000705020f818001d1500640050041c000c03620716698802004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 357431600 1250 357430350 357430393
    0x11011b02030a080a050618070e031c1815110f070e0108150c0d020711040204080a0c0902040806011205030c07090609060b0f0a030b1314010501111b0f03 67
    0x65005900016810342250b500c800f03500d411805414051205041c0000080ca44071901c02c800c55010081c0c0001c6181c19010300d801c101c1100c00a8265207008505203003203500c1c18140d562440100d90314000f103c01c40d402e070807041c10584251901c070403124000101c0443c0c10710f010740d0605c8100e108500b10030301c3c80f1401f000b2039002065802c00078200c0d51304101d10141009400501d4070751707482861060202444c0528156400c0094100c00143c0300c04060400101030310ba2a05000d40141c0b00080200318182c0218000b00308078052003081201c6944d90204204030711a9105a80a0380c02080c0144445031810481443e111f0144040b42e04001344010541c4c140f40c1d080d03000b0b18415540d030a00300040700150286100401600d07081c0c9003080a400e07101165407250420b03e104143c1c2d600c00c1d101c86965080c7c0c125051100035070041000e0248a0340c3c0c8030342a8070a00945010a0580d00007400d49140052025440b08000d0f1f8034a2981800c0c005022007405a034801560501a020b103e4106a0142014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 357432850 1250 357431600 357431651
    0x1c03020702150c01020717280c0f0b0405190c03110a0e0702100c11120918010f060e0a03120804020301020c10060914090615130207141e0a031101 64
    0x1130791440c0c58a440c40c1c0364460740030080e40c13501c400c0c421109207a0901c6808901c202c0c0b500b4000304030b0426030804442740c080c00000101a030701031039100e10500c8055911140b1451080048501c19503522514410801010304002c00d11105001d003440010340e0102808403824014200301c0c0002c0e2201e5088191103070444045d00141e001c00c0c0006200740080c05060200c40182c14812034034161a882c250f00d54042220702001b011002400c40b4841e00c030022031000010401040c0b074081c0d612a88010f107011010302c01c61002490000003004c1525008a11200701c0745d001e50b58605041c1004d00640300032000920a0f0382c195802c0c07003a081081018081010011210f0100190b0300d401c054008048404c0301c0c0b01000480070382c1041080384030703001444507084080d002e203031806c0c10b01401c0050040b81000d451421554000f180900c20491002824601c40f0b40003000c0d14075003102032140d54213a802441498005a10020368a8003080c0a148540c030b0308240c50001056244807140d20398441c0000d03502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 357434100 1250 357432850 357432853
    0x1401090509160e0916050f0c03131a1321080a020c0a0e0c040e0a0f0c0801031509231c05040e0106090e0105061b0624031c03020702150c 60
    0x80a0b9200d680c005015004a0022100c0382003d040c000040101c003c0c0f01c2410005001c00010074042c28816442600c0702c82d04104201c03596954801028000001180b14404018801c11103104079010b0036410f85840700300410692042c00e191444410008484404610007802c02510384030100c1c51140050010306000e40013890017000080510540d054507a0026540300c0303441d003d220400101c2411201214000c00c1005465254110641c0062516035001d0b4049032a0140c02155a5000a5964100c80c0542c81000b2400000648202507580340d0800414290f41180700c100030f401c80f010079012513818502190701c140d010200c603036451000c80054038003149000c601008111141601207002d480c880ca41000ca1514240c0b0304a1a00300601500384500004201900e4011504160002540c000401c41d1074034180800102d603100030446d100c408100240782c030340007036040000c1e0402c0c0040c205420f030201543c13082400c5000b500035400880c0e114011400c1c600d079a456000140510111600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 357435350 1250 357434100 357434131
    0x18120d02130b1c09020a270c030f0c02030913051b030a06080c030a0c0b0f22030201030c020a02062515020d0f060806180c0a080102250803011401090509 67
    0x610100d8850700c0f01408400e182041402c1c00140c0f6110410000c4541740a1981c180c40058a190402410b0032024042d07c0e41c0303420300c0381c2c52081c2c1c5030b000919144024038081000d54404c0c4001c07a200d01c1601c0d58150030441c400722207460b0b40520740c07200781d02c0100c1883c280f40c18800d0107400d203941d5006540a04010751510014400c1310024482d072040317604220001c214829469864024645591041034030b00200458402c40b07a07074842d0100c40704184d0842007149045c43d141c4507200e0111050100340d0000c0c1c90f102001445c1d90002505521643e001412681411a840b20300741d59680d645107100100c1c2d41000010740019041c0c14807040040b001913016840d403200348008402c4030468030071100707494240001040b26100c045a40b607004411003001c03145081c24150710700d06e84040100000d8206012890004100c68191301400f41c1ca00882c0c0080701110340190082d103208424000a010640d081004029040a0a615200c00001070406020345a600c00c0056200201258800c11020051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 357436600 1250 357435350 357435367
    0x5a0905070905010b070f0312180f1505150d150c05030a0b0303030408030415090c06021e01020405010f18120804050f040c0f230304030c0b18120d02130b 67
    0x3801401d014014451388035007045a2500c41c0507004070042030140605c0321031030b04458a10a0f5800240140c01074010301450308003580390000d8510048101941c1c20001c001c881072003813801c0c3c0a010300800f44201da070a807007554001041a501c90b03a03482114529200403c95a403c9d049019020350710071680c9030303941c40303160500d080010344800b8150140310350070400070440000c540e481500e4002c1c0c0c000c42090781b9481500d80703500050400101c09010031080c09400581141d0010303503020080107614011401c0c041c1640c4642c281d0013580207890108000404003810640b0840b038541001c200100761210382a0b58a0846010700c55680c0c0c241e5502c003001509021a041c0b00324030305010310007075404201c04122070b80d00900100411144d0b00803c0302403080e070b004035400d0300c0510035840c055051803a905c0c1003600d00948040140e540c103d525101200004801220310104800c80e00c8160001c2c04031031008044666484d031200c080284540c0c1e0a000302c0341d150f010f080e40031014060b081c00c0300c0ea8400303e8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 357437850 1250 357436600 357436619
    0x30e0601060516062705030418060503060103020f010c080c0a032a0308090f030c0d090e090a122c0306010801060506070b0a020415035a090507 63
    0x160007040900800300620300401410740060808107030041000a07104583c54007904038281c102c4001400030960340045024004040000c004a174840845d820481c00c00381c120100356806d82c4030b080d925802c800c004001504001070741040000051408821140455403911140d8110010b1590070307501c80459041059004440001050700c0c03610b0459040880175034214032408507000c001c1c200240d50b004116248010008003480003003080a803516400c3c080040ba95407180240041c0000707007510320004403a000b05140d0350003440507078080d03e108952604c0d005c6d0500c0007000804c0403c038a000c0b003440c1c43d548040c3c14101c40101564030901c1d146040040524101041c0c002174034592400c0401c100036552101151031981d480004a0940e0359100c9500c0001d0003175074001006081e68003200090704d989507000e5207140c401c0c0702107454580841c07141030380410101c40080229107001c0340940c0311480310501204d100198001d2021080080340440d40981c0c0c0c501d142100ca41d4086035080c00914007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 357439100 1250 357437850 357437863
    0x1b0305010f0608040837051e090105030c090102150c0c010606050a022503020406060503040501060b1e03271b0402180904060906231b0406030c0e0907030e 68
    0x58620307102c10f207414103840d460b24a110310b02d010b80014080d59601007004607448005100e00c018610344c802c0c501c40814003c2e100750b001070b50140781b90700314001c2148007031000001c3d10315a03c81a540c403421a03582484c03081e980e501c00303980e00e03040d0310885016101800e4000003103881044401851a181c0c0140100e803425590580c2240d82030080611a0200503613001440318010660340e166040c9035044546588294841900040d40050400c1c03c0402c045e41c00000460250788144000c02186a40d0a10004140215103000c90442c84404100041c548003501031a04a00058002102d440041148090f80710595190602c070b0b401400d90b0800030039044042640342c24042e02c2c00d51a21303188030048070807403401e030180390302c0351540b01d021a003032242c10380c80755404941c002002c100d85103903002640f044401c80310003407500d0840000021410221a07400c4408001d00c1a1030030300b041c4c2000307810b0f000b03010f024030010100a0842c2100310103980e02d00c406801100e1a88000a0410700c0c003418508000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 357440350 1250 357439100 357439109
    0x6160506060d031b02060f0c0607090f06091214100c020f060f0f04030207090f02040e0705090d0212030d11090906030a0507090203060a03140c030706030608120a031b0305010f 77
    0x304030040d0030080f0f90003070200003400c40c1c1590007212840e8a48001a402e008002441d40c00074404a80015101030005515000704075035101d1900c00307566900440d00c0041d050141400045a40e40200b20100565010a95081c4226001f500c5041c28900440c504150044803402d0b46441d01a291141c81c2c0611501d0308207946080a015149040d20984207503c402515090486407000000b4040c14420301510700502a8140d084c004100005509000380d0820f004080340b00c10405c0105050900600c11503490301c00180c030107840e0165540070446615000480074015010410500c1c10b406031fa807042c0343c102154031403016102e00c070b03030814400c03140001021140070340d01001e0b0700c501080b0000f40381000c40f006902e015070b4a68412021500721a06984002c140181480e00180e040d6404103103000041070603802c983c403144c0d603003800310140c80451141801c260020f4004031402c0d14504001c240420303907810046003524400c0096080d4101e40201400080e40c0c1c0c02c018090826108502e00050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 357441600 1250 357440350 357440359
    0xd11011d19230120150106020303071205060d030f02030c0d050c010b06161202070e0a1407140a05070204020f04030f050708011424040c0518030319050310050616050606 74
    0x240107540060325034004e02d2104811060004101d054090042002000c0c501c0707640340702605569a10341c041d5803074005a6640700810028041303c001c00410f80319103845008000e10706210440c0399103017924140300d000c16007000c60008002e2180409410400b00400003810f5031800e40d02d00392042d68a0071036454012040c41560208180018110368003128004281c010300c00a24100503010240e00d0944103600c240c802071021400c104800309143d101c80103c0d21031104480e001c0c1e9403400200e880c60580001d0041521051000444691080000d803400f6071005d8001403501000c1008510b180c3c02c075074400c959001160300780804000302030100c8070050030440024401d404610b442d03696051001080b88801c0e0545a140034030508a0100201e59030390b000c2d0003000f001035680001420340e8410003600c003031801491050280d900b0b0001c01c40d034440e40754045540e0081c1c4c89100448480d80081c0c0045004590034a0100d0966586070040580203240380d148100708a551a01c142007210052403580304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 357442850 1250 357441600 357441659
    0xc0f0315050408030402060c1f02030a1b0801120c1e050312040608040210030b0405090c1215010e060607170904060603090b0109020c030c06040b0601020601050d11011d19 75
    0x41e840401e1381c1d001030b811581941c0b68030701031403158607221050198403124440b03a00b40a079a500c80d58015402070704810401d10014a5908400f45640202e080c0f41000844035401001408403944003803038005d00c92000110000d0360340d192b00100c130344003030b10b100e10318086c00d24100000e10b0104030302c00c48030604d445402c0c20f0074504030018114410042000e0700400d42d14070304101d9107110f0350003480960801081040107080160000b80e680c01c112020034091803400c20012024003002901c45114410382c0104203c1b40c1c01c08185010000004d042c3c90741011080c041f040005036004440410f100000c80041d40b245010810401645c81c50392000c400d1501e030020ba01301140fa4a15602d0565108002c0941c0e9103001c420260304e1882070383c00c0d111007800356005000400000c2040c01e40070340740c268202c0302c80ea622a42003100b40e128a100041c101d10501014030b03905d500840146d42420781c83c540707006004860302c01141011500044450031002005414000710001c0b284800d0743c1c09003511501d10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 357444100 1250 357442850 357442853
    0x307021014181c050a030b04050708010302040b01090806060f01020a080f070501140c0a0e0316170c0315150a031406060907030204060207030602090609100f030b0319030807020a0c0f03150504 84
    0x4407843e8008440d001c220300011a0109a4026000781d000c030280580100603506d010003004144030380c2030100324803607810b2074850403003036106540041c25030364400003502c1c560709c0701c4c010400c1d02c448008242e07065010303c00c013200100c1c43c040050a009000c60480c035030b5950329803411600f10350306900c03100040c0c0300c40d0b0700307000f02041054107550300c0c1c40351400e24003c1c8a6201000910f000801000030301021241d400110b007407240e04401918880301c600440f01240c0e01c8104058a90303020340446140280180000358583d01d414107102040c21015050b040304545030344541220004542111002d58000301c244806410111181580401c8a1904508042c10040e0082d00c40300c007440040e000303680108100c942a03813800c084946180d4001e10021420f41001c00150018004ac1d11240120340740c00f2603e840d80c1808144014000340203c0c0c0c894000249541c2500c40071720140a143c114424260034034001a421400e100280c00c01420a030002c1d803440c645095490203030a1003a03201c80c2440c1c00d000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 357445350 1250 357444100 357444133
    0xb060406030f0312060b030108010605040f111e07050d03050114010809061603242903040311010905010c0201060512010e280c06210b090408030702101418 68
    0x101c01c0d40c0c54507160b0341c213604076004507001c1d11a5805c00781c0b401d5000800050445070543c00507040f20410384042c00b0b0798110310180411544034036a000d0700d401d401c100300c000d408544808a2191001d8128680c1460b0494903818601030300f680300000442d9072032006001c20b1803105003500380a64246880c40a900d05190059121300000e0308682440148610480d1014026000a050303014424000c5680100c907000060340204a442252161040d4008070701040035114005101c1030080000d9500d5030312a59009c0724605800b04601304195640c1074410001282802600f01e42c040503800401c0721828001046140d82c071564441c111070b0b150000c43c0d10407040100e51042c3c6240c00d10420821b400084e4503124021800450090500034640004103c42ea0441c9030607120400452880e140c1268144400302146c210f008030661102c074010009000402c03180c021a4403088a105581d807440341801d2201c242d81c059002843c150105400b003180d0b600d10456070407501072800d00101188140d186464 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 357446600 1250 357445350 357445373
    0x4030323041d16121512081b0706021c030f0203040501140601110601150e0a030b0901060b040608130611121803031b0904060e180c10020c010c1118040b06040603 71
    0xc010741345e1038003849489100031550403c0145418908608520340c1403400380708035031105848440848950b14658000f00303000446505440c0342d900100a10307505078000340c80d1920034840d40010103807506c82540240722345002450190b8492000071901981111900001c1d420081003241000074804882c01c1130000014071038115200589080c1c1415500d120803148030703446d1062a038000300300f65800401c2120305403a0364840c008280c000c00034a904ca45030503205108a00c50200021201004101c6000c2039002401043e4483d00001070b807100c420b0002c20b142c2d008260348200804141702004403c98040308a084401c0b50781010b5451072421441c804417409040318580c01e0601c002c116070b02c460f02e4a90181000e0414690351000900c5e00703090458607403401003494040d41c01038620072141820030540030302d0006100e40103400c011100100444a0080c6000b06407814041d540403013640392a10014140c199030701140e01c2119190a050900c07032020050301c1a8095850507504001159034103040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 357447850 1250 357446600 357446627
    0x1020102090a121a0c070b010f150810150f03050606070b011205100920030a0c0b07030905130606180e0103140a0209073204030323041d16 61
    0xc18400902030304145516000800310052482c2180c405c0c4150b000480000d0301290b403140544c1142e0f0703a2144d80032030303038190984a45001768030301111a81d1014040d05031207500c640a2aa01540c151790f031182c1e040402c07403210081001c2520240a5468607505006107a4002810b85165180c264141d95039a805034051090500454141c0801001c1000c184440c2240c0610b880090040d034020741050700c14124518810303080c81e9a0302c00d08820780e040100d045200c4941021503040f0441c070b480300324a0a540050012000c200c824030020400d66030b88141c648040060140000c5c078079007060005041d8181500301a68100045d0508210200c00d09007410f040d02e80c000040d42402c80184035441c0340c040c85c0f0304004c1d440f6500a0070450340e290f22a220701d0802c2c0042c030300c4849004001141c51590344500c02185107000d010041800400e000b04a040c0070714602000d500481d07203000c0030b01c0b4019080368002c01c0c450710f034200e4520401d402950304160048103001480c0c41e0660308540152102ca154400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 357449100 1250 357447850 357447869
    0x15170606040e100b0c030a030f09050a1410060f09060501021203010308070807080a080a0f0603051b0105071211011119120f11070b0f0603150c1b010e0c01020102090a 73
    0x110340e031070002c070340780010091115000c5e15038040300c0c0d80b42e0712500025944030029242040c8420100c08500400c54055040400b400a012894540c0c0d0011240040c200309140b0a12980000c4410a403245070000c040e0b18103991019824007034807405842d00755000c2d0341154002c100f0341459121000440b81140d40c45200c9030307911003a03803929030345501600b6030280030300d880458240800c5811011083c414a00d44070104031480e92203001c002194030300d01002e403041d4072884520380c00e200702d07841043e003080050509500b440f826561780540c40e11024806400078044a4070524041d0090080195109898000604049211ba94000c181c3e900b017041008201c00c0003140e0301d1441c00c940c0116004e82c404a000c1c44030360380805141d1055408440b08649400c1d400e0009480713081d11028190040e0001005400012007a0001c5032280d01c01901c4608602d804029441e0700c41560b42c4500051060b10002141103d45440300030704040185080905590041119229541e950b00d030010540700c000c61b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 357450350 1250 357449100 357449129
    0x414070225090e030c010c050f09040e0312160e01080c09040f090b0705070c0b0903190c051f1214061002100203013f0204050a151517060604 62
    0xc0d02001c85003a40e030110b1410391800400780e0038100301000500c05010040002d0150f000c800340119818031905016202207503051107044010302e010342000e6880d1001004480c1000b544114007890b01c01c05548140585a02030808116940c00401100b4800004d081443d00346ca04158061140e1060340100d074030a550f5242c0c0068000b00503400b038039142d0342040c0b0769500c0d03281203000940b0b540d01c25003043d02d25010003c000034000c8405800c0340c40c5181c01402401000000c041c0c10b101c082c3d454501161a0700700d212001c81c2c65150002c0080300d540b000900e500c2051b00030398001c0c022a00c0800c05192141c10310a003142d00003040918607412940a64440707405501a080890a18070400054000680000000a0006104000d01c070108014503404c070103000c02425400c0020420003004014801c0d101c0c0204054a000d81c02154001c3c0d4590001c500b54825070303103081989815030090340d90342031604407018080b54031407814007074078009849040c00c43c00c2c25000107410380110f1081d5140303400d207030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 357451600 1250 357450350 357450403
    0x503221e0b07120911090c07120306061103070215090303040803130302030d170a09110306090604031115040213021303050705040c08071209080c0f060604140702 71
    0x8a4240152800c5908003509010629000351200426155800040c8040e0b1400403950760601c80c68030840c1d40b081034200c203590418140a1700c100700420b0201c142d881130000300085030308082071642e00e1019540c001001810728a000c0d04141014540a5003541300b0b0003503000588506074a510741c1150301901e181c8584400001074550311031600108590301020030000380d414101c40040040d648210247c034030506003c4801c0382d400e100070206908845808010650503030103984651081d80c010141400ca401c0014003007881c3c401c09803804030072580030303100b00000e242d8480380005201123410060030783e01a0601c01c2a0041c0030140c8082e2080182507100310410010b03a04030b402203d00000c000c650301d5500d0a042d9201c0003c3c1c49000d000f00e04100100052030300c02c24596100703980607200d0182c0400013102442c0103110748030040362458820403a850580000300700e240d41c5140071a0040129181c088184800c0c0c511280c80c1900d150744000a1041464020070187c0e440410621342c10943d0004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 357452850 1250 357451600 357451613
    0x40204051b0a0c0c0812031605070b011d280e150f1801150b07031106010b041403060f160318080403050c0f0a06050c01110c010219050322 61
    0x41c2103092030240c10008901030320b140c0080680200d039008280204c00d8a81d5500707002e1315016199601480d0718030400015090a02036034003200c100c02c1038a411030401c0c6456603540800c4e0703402e0b08007ca8601104d903030149880c030800178540c0e0081216a50350780c1d2103211450f00010030510580604055122124007048003030401c00813081e45618a800307212414800e40200320b401d03040d01c030b0380901450798144540b9800140121100355145c4000c00000c0c501e42200c011aa0308040c6048040202d81203000300d0303240b4100300007030191129800d1203075114501060400044084040d4601039080f050801007078105100000354801c3c1c1c600e0389014143c485002c110001d003200e80816071128031100444003407012400c054000e49124004840401c58810f0802003280c448601003075011032001c00c14000c1d0303842074000e444001c081000104609030a244012010b40046d100300c1943c2c1c6d0b0206007070050004002010b0703400095810040d05e036003031500510840c103a185008840c00c000904150041084 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 357454100 1250 357452850 357452881
    0x4050714040b07030c060609050402030d0302130e041514061e060304060203060637020f101a03060c13211704170106080609070803070b07020a0206160519020904020405 74
    0x30f210030b0400c01300e52984230f030000800301510240c0c081e2288060400003507020b84200e0303850300080c4d90040c1c07509245c0b00c4803000d1904000c0c01102e00ca00d02112400070101039000d000d10690084c0341c941000d00e04802481058090130203c2c516407002101400300136100c0408880c2c0141e00030002580da59105008030700c00e48900d50001810282d100203034800c90355180c80000b10b086c8142c007941c030388584041080b0b03581c41c500328011665030004814803d6422165111385d000300303401410842520440d2000030300b00441114000700c5d0a00020340806401c1c0305071a250f01030300c0c05500740b80c90348810140c0e41284108111008200c16080104246200c0192007510300400012414008402c00c5e0140c89001c0c1c080782c8100b541920a40d0045a0100700203d60481a158124011800d00c942a1030760b04400401400701003c3d4092050660050385540008100740030602d100b03150040742900c0d0151070200c4070a900542c0c4440c3c2e01510b170041c2e44040340b02d90420340440c2e000c504d507110000001c16920 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 357455350 1250 357454100 357454103
    0x40e09012d0501050a0617220f05012a0c02031c0e04050114030309060d060b031003141c05030411040608010c09080102130e191a04050714040b07030c 66
    0x4025480500c030203052840c8481191007141c41c28416660381c0e03024442c1c03495007401190f001c60041c14044947d14420300e001d990200701c05042492440c01000c045c0e03d0a09961419540c0150241054007809000d0007900d0b000c0b820195480396500c0307120350139642d8080d102c44450810070950103800a40d40c08124803d41038062042444102d420600089c108000610341140228140000054240d0001307491f00078560b00034000d540751102e00000c0180681c051540013180c641ea0300800300700a10300030099440340009900b40d2241c5801c50501501181851070501c00585c4040802c2441200d90000d10002c0115030900c03d4036616646041140c904110900030740091601c00d00064004c8150460340210b0390070b44480b00c0c41915061014280d1103444404034020559203030801082c2d03c0000c201b0783c00715105c1c3c05844041c071f134000602c09841525403900c1d4a07900200091900303140602c034590b08092075041400d0810200e0780c1d604040d00842c031407040b4270394010480c0c80500d409044030b218071030b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 357456600 1250 357455350 357455381
    0x80301060e100801060e040b0d0b0103230601030c1a0c062a04050603040b0903070602071110020610090f1d0303090607260c1204050c030607090b040e0901 68
    0x968540c180100007201e2000038a10030101c0b003800c501401e004250060680f80241d94101c0521402010b200103848842040c40e08040c07440d040038046044454040c0c082c2d44641565011028034400a91135044200b0400c03400d07070400c800400002e036031035484c2c00440314107140d600390012108103542514025404540406d000700000c02c580340d01d0300801f0300d0702101c5640240c042c45808204044041c0100e01905400040070000304000ca207030b51101581c0895001c0880b032610301c0c56540e540a030703007100408681c034402da1141d101e95441c000d0410b151b94002407008000314500210a2215140c5a01c076001600e642e0784080702c003030100c60708081109000c841502c03c0b83c10704480402d40d282e00032102002d15000b4071010078103a81c41210160800c80040040344828948a01c8080c2301c2c4602070000064804100040b100465a0b502241c0c4074501610150882c21a080b00341804d121009005401b080354014013408503640131030a89058404000c055407007036840018050041c0014804600380c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 357457850 1250 357456600 357456607
    0x610050c0a0b010608070201060b040302060c07051011061501170615040303051305101403131e0c0533090301020309070807060e06220302060406020304080f030a020a02100c08 77
    0x144180d003002c09048400303585d02c99550755554a0202d08072000390140c1d0340c04181c100004c0015141a10260540543d10030507112020b030b5580c0060715a440c26170721540481c03d000c1c0104025401400110b83c00042141c0703121000664000090001419440c1c5c07022000d15030303000c6103154966150b101032a1400c14045a69140c89080240803031b004050180d0311124401e40c0030445050294071924030040da6120814140140140d1a80e5904014180503809a8000600303010419070720042c00300e6804c4100900300c41c28039041c51180c0041c00c0d040f1901a078001981386200340c2d41640800c40400424a031031001c0c1145c080d5414041c41882c44140e4198004001d00000d5007001c682030303084031f2440080b0b0340500d035990015110360ba40c1c01070300c0d540004180f052520020f944528400520542c68003040095140d50014025805c01d800020059002140c18000f4200030000203083d185440b005505180c0058002941c9032050388000380039001d014850b0a041d0b010301a403203c59035111802a45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 357459100 1250 357457850 357457853
    0x3034f051c02060a05130f0f170309040204120318060504090906060b0309011b110709020d0b030d081006030605030a03032d09021f121e0608030307170c030610050c0a 73
    0x5170350003580c658624201084000228001e8140700a0210351800720003102043c42c205000300d0207d0103040d080d070640400c02100c03d6664a51005001034000110581e040301b901d0f00b030040c00039085c01c10b074a1583c2940302c410300a0325080426641150006840400c0c52031161500344043c01c0982c0c010b030465540401030100740c950640043c8004000c40c80750143c1c1100010301161524400e0b140c0c40702c0c542015509102d200c0d41c5130010007405030000c1000c00c15004410100745007400c1a01800300084210317090042c02c84050210400a2505180030310030a030900700001d80380e000d2280020700741541c40110031030300d503051241245c6000d5406184048018100043c01c00340010304000c82c40348840544841503202e151203841090713003071a81c0716103907100d250f0540002040600c443e12124100c41c5001c803c001214004c3c080503002640245850741405403002d0400c0008010000d414913454007000400e00100d4283e0b5400b04007210943d50740d00d80051305540c03d02c1a00d07160030450180100c25070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 357460350 1250 357459100 357459107
    0x41d100f0507090303080c0a03060302090703090302010c050a1e0c080c160e160f09120305190e03030313020d0803090c010e01020f0a020f03034f051c02060a 69
    0x52800440c0612007a07640307030710480361841d260000402017036400700031580411403507024000e54002d908000031855100e400041d10030303004075084000030762103a044c0342c200b50342800707000d014a590f801c0c21414201e400f0005000c1030701c980c46403201c0c00882000c0c2502e10b48076003554800b0640002c49079994100220006841d01e2038020080603000410000154000901031540e21803110b00c61016907042c4046401c48410780000d45d140204075449070080f0b101d02d02d900042c640d0341d1003502c4669a50071100d90b1524200c085010301010711411003000c000540700402280e07403144d000e01415903604850310018003500803461b00a080320201008100000100259017013018100f40c950324404403111004a0351071521840d80c04d00307600f0031415540103050100305c4482c1e021004099a003010108030f1100384000300a8141c000d0090800d91030038103100c03032582c0e120188180040c000138903041c40100710800c010394071826003c0c010940140204052416100c0c802645c01441c00b0f83e00d0f4820361006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 357461600 1250 357460350 357460361
    0x80a0b0a0b0c01180c030f020f04110a080c0a02030307200d03020c16030c060e03150f040c082b03090c0603020301140d050d051308150103061103090c041d10 69
    0x2e502580303082c40407078000d001c5002e84c0401c140d00c20f048000e41400d40e51303844000c2c004240220381200d0000e51421040d40c0300d001c2c0c401500f6158110940307400407420010118900901042c070300031000c0000000066020007203d82c0700f038590034455541101d8804111513214a00034200f41802049201c601c4541d058000b000203410001c101c905848061100760420b100c00e10008040590042c01000020300424810f004110300234261110040420b1040c614102d0407510744009044090411007089902080c1d01c01400200c4000d2807170f8042040d0041b01c0d80728400074680ca40c0001400072090768480c0c1c0045003802e601204560000365a0b80005d4041d40080c0111445c514480040c010f8904141070001040ea81140081410760640c1c40c05440b1070b071000c0030040c001e03024482c001c28410f50405c00700c4034944560341e00350340303644c03440c21f00c1021100750100f5404039001c02c04c2400303d039250004104080f818102c0d8005000d280086d000c4641980c011420b13145070007401c0d41c1b19940751362540903 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 357462850 1250 357461600 357461617
    0x15060303080f060109140102070b03090304030b130503070b060a031b090c0f080a020a0905120a05060a090506070f020115090b040606030506010c24020c0109120801050a0501080a0b0a0b 81
    0x21851075840303a07842c295070340c1800c841240c0000d401e62010441c1404244c54003581c140c4c180182c8134541c0c2c95400c21030381913004582c40c80712688001400c0041040c4000d485502071903105c507910900341d0550355252207100d0310ba0040e051008840100d0425a601c00080c4000d507403003620003040301c0304c2c2d40542c800b070541807040440b520315010400c48010300030081c0c3c0d9500e24481e551500a0390b0350f07200d844000d40000040a00f00311a5907404240d5480f817140e48035003c45800d00405200c281440e0180c680741000301409261410f01220030700162000448503042170180c1488aa22444020101c0c0100120a070341c0c0c2c0c2030301c001c1c40000394100050b48410f0b00e442c0d00340c400784111502c0308829020b80b242031b01c256001030306003224000400d80b8100c0c05003918403450381e0052207140005441082e038008030311100341341c1d644400043c02c21213070421044030200e02c1d00f03201c88158034050004042050620840381403252200c0000c0307049070650301800c0500b6004220400e40c0382c450901954503007000c50b2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 357464100 1250 357462850 357462857
    0xb0304150506090c04030303021e0c030c0d1404030305160b241005030115031407051b0105090303060409060b0a080f070e060f010302070206090a0b0310050607200a0315060303 77
    0x2240c0b15080220070540305006883c03880f0711302860750390110001d5000d284608030941d141c03000d805415001600038070404040c00015030325000811840c1c1c0c02c0c480565940000e22180001a510203c0c0c0d00d0191006c03070f40c1504019840d02024a500303007290003060001084400c04004221807181c0d814400180c5103c901c424104105000041c071001c1824017040f003011400520040000c8510700c0d990403071903c2545004148025940300006802c2000d941d2031010404c00b2030811020078509a5500004024000078021402c080d01c803a070b241c0c4400380049006a440d1501d441c14000b0307542081c4880c0c0d501905111070306a41c2e800558841b078050751110594002c3c40c2d00010400c4500d85524003440300144900d001030603040041d002980000022a0030890600c80b513400380c0d90302892038000381240d000040c1d40e841d140c041c0300503c0055400507441114188800c4000c90802c0d0340310a0b61241c0c1c09070b68142c3c1c40c0b240c00000d0174a01207500041034111880c41d00c520202d002c2e002401164400e89 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 357465350 1250 357464100 357464111
    0x910050405011d060402180403020a0f0302060f0901090c03031b20040b0d033c08160306060503190b090403030905010b01030c17070504090c200a020a0b0d060b030415 73
    0x10085451381001d03038000e98420450f105031f141c41c900d4403e1007600b151090049500b82c40890742c418800b018078080507001f503040380003001508000c031040983d0100d00800200000e5000b69079001003e480303404050100840c00c205070801c0752003042c0380f00b03400d50846c10500d4080020040808503000c260900c030300550034100f4017480760030300402400803107515032943d500061180040742d141061070361852030003018614115440d09900701041e00107620559800d0424503107075180140c0141160340c0d000406241400c10441558010107483c1c001c0003884816035207001000720301014081d034030b030075640c8402e000081c80304040c0c155100c1c8406a100c2c200038002281010015000c48202001c0d0101050700160804142003414861340e5202c0c0d1a4204141055182da004004031140003410001090000440161405039104c0c0d045030402c05400404414489d42d0108074a86418407880700c0b40e103c085a6189050140d03004800607103c100c94242d1a4070702810104c08460341c4001c1a0017107440e2a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 357466600 1250 357465350 357465401
    0xb03010e013206060403060c030b1c050f030a0f080405030408011503030305061e090402040f050903130e01061407030306081b09090f0303060f0a030206191701030302070608091005040501 82
    0x20b4040c07803090300c00070400e509040c42c580702c1001501246595100f0940d4410f04000c0c941c0c0d60015031070700400b5a080445021202c0e01e040c9240031010025500c099009020154515622854107104c10003240703440d034030035240d130314205281d0300031500002915424949080102c00100303000f0030440e07002e0f950a02c4652600740c1403181c03581440c0c031400241304407441c1240c41d030b060621001e5002840900000754030660800c99100310344095072000c460360000611030000402030101403020b49080401d0b4a4194034198002d016100e01e611041542803010402c8000d16000f80d1100008102c03171303c103668004030503a010589a0512503440c52103804070401007103c15600090981010003990010342c5151a00e50802035030158004456070700c540040000700c01a100c640203406a4542510a40c4401c1118003014043c90421b10401c0a56009030b8010004664009241070494446080c41200760706ca10010b14201000180e442500c14103000078441000030550218402d590084560680010403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 357467850 1250 357466600 357466691
    0x30a0f0306050604090c1101050f0a1a03060105101107061e0809070302190302211c0c0f03030b0d0f0203010b0a030201090905071b030203030906010e04030f030b03010e01 75
    0x64020039802400074001070281c94102d5000161b0105035003000d1024050640e107583c25504101c4e0500b001600c40014006480003a000e500b0f00d250058030030810009004000c603503601814446c4511803154182c185d281d0501590702c0090b524030031007e070b48000d610b030340c0040d00f540c00c042c042d01c8006900c02052a88540b24241d1507001d0304e0300c00040c0101d83d10f103400b0411901c0984030480303034007000c4400010060b511405210341140f2051500103080707010114050400c031801c1840c65591034803040900c51103501802d507909595102c0e0201314041a5428201c0080c5107078258a50000d005050301e4051041c22200001000d01c220001c1c13005a1054003840440500740c03000901140c6903030780900550000350070003580425a860b2a08010408816246003580d0104098001d60400000d003d48404207101d0302d405043d058011300d00342d0810b590000c02600c811285a020960388150307001d0103a40c03e401822001150400911203c40d50a4103e200380c0c224400c40c3d001602400001b0a59107403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 357469100 1250 357467850 357467861
    0x103062c1b1909091a0f210604021801030b0a0e03210f0a150627030c080106050d150c0207050306160e04050903160c0f030b0a0524011407060608030a0f03 68
    0x1844249500d5032000d00a10910b4802c42c141c651f806000c0000103d1a06000d004800342c2c0e0740f0f800c0c020909420140103100f161410304042c4509415424014004070b040c00200c41d0308001c3c1100c000480f40181c0b9440360440c051001249100002101400e00131100e068a0341d010320852901031825031100084807044039813550907540401d41030b602c1003029a0160b072061426920104d00c2c400c80746c035842c003403c410800030b0f002142c020403882c50038080b11409101d4200075000c10741d83c0da82e04807541d489071180541c1060b04480c3c05500c52141e12929403080c055a0020710014045074003c0c10805007400d0300c4108048480b0008000340b55500310341c80d09020307541c094444200078500d0012940b40000810510403000c0d15542504032001400180c2c0c1c401083c021400b030b04460302e00342030410b0070300f040d00c82c058006134031a81d50b90040256070400c0f01d40700e00d802c0024204002800514401034804d2700410078081d101c81d10340000041c4510b000b000500103403145035540c441209018005608449 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 357470350 1250 357469100 357469121
    0x30f04030317061e0a090204080715030e0601050f0f1005030915010f050108040c1505120105030c0a170f030d020d200a030b0d020d0c050103062c1b190909 68
    0x480c00565051580141c40d000c0700c1d40001414214030b80f80c03100702546c241da120354007510303d0b80e101c0a010041c047e00f58030a58400341c0c00e80b030203005075103c1c9645d0711794420341030103400e00c5405040c2c540001c80d0340b402d14002000c03002400880300081406030203085600220351010740342c0581d04404d0341d46014049414180e0b2002c000d09816142044011608194000c0c02141d01c40c40689010841040c0801000f205840b580c0e1802da45d150b480407010300c1c000703041c1d1004e40640e019682c40d1402c1d907a003c003003406440007080b902d00c42d0400b0710012881c00010094400c51800300240b040120513284c0c0044c1800d00c0c0c0b0102c14005518003280760484071604a248001d20041800070041e01c80c0f10ba0040e100b00900100980d10a18280d00007403408190f51000310f681c1c1070f8041d0300300011f580500900c4000c2080760924941140c0c4140d02411140740103da41e10000e0043d0700080b900c007040f21103006041c03041c07004182c036805803180206403d140c45821a000c2184400000f8003500706000c0e100054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 357471600 1250 357470350 357470359
    0x10915091407030b040c050316020703050a11130b030618030d02070615050603090a0b090106030c15120c05070803100f17010515010e040c09050910141801051908030f0403031706 78
    0x107a842c40e27a50310725007803015014411800758840001c04581f081228200e028050003613414604090410000318000044142c0703c2e10307082c212500810742d404140b40307512424003038840a80302d800e034175001c1c207621903143c41840c0d240c400b192020a0100300d500507949152840c2412019644900800010f07020841c0d5000390360380031a0516000545800031150045c0642c000410141d880390307a00c3d86956810782001c0300b1484e0724a80c01043d5544215280d00340e4002c2841000020040380c4014107511580704060304030007000011500101801c06040028192541000d01c20381d2500e0415a100d0a12451a015503003840d0201c5c00141c0b545003081d002c1c400507110350301005001801c2c132028002d21501311080c01000d050014894451542c003921440e10641400803c40c140680c0b03050104038146681d000300c0c00345940d07160f42c42e040b803010381c1518011602c400c8400a0342003444020481c07a04454154000400c18041c441e0621002d001035034031175103400620b803441880031480c1120032150319501 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 357472850 1250 357471600 357471607
    0x15030901090c121e050a0818040f0e030a0f02030d020406031508071d0a1b0305060301110405090a0b0a03080f030403090b03040507231e1906020303010915091407030b040c05 76
    0xc000600c682640921311a0041c6d401d1504c107512011754a400c0034501101c0034800804c10700440c0740c180308011030301e1040e08003080700341000c0d26810b65902440c0300000034084004404036001c1e00170400c0e1044908400020f56980e5150080100940b0780d0841d00140f14040410101d41c1ea103002c65494159121ba270300e81101400c515104d01440103004d03142031800c43c3d0381e00c1c1101070825000406d08244185460100311820301c0760605007155882d07070909000c02030900c42800180d42c0c10310f00315041f0020b07003004664204c1450010742200c0e410b80c8000c2000c80001005800051160061807196000307468800041d59140f08040c52071100701c80040058025200c14402c1500080c410004503042c0c00248001e120b0300000320b0060040348460302c0890110018600c0186080410380760105150142a04810b103890000fa40c1d80c001030290b1f851132512401c5140c2d80d4000c1c40d4040c0014011500300380000495001e0300c40076000c0603a5024000fa05084282603181000d008074800f4100c13039554a4036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 357474100 1250 357472850 357472883
    0x2030c101a03010c08040b0c1204020d03021603060c14030402030a1401021b011b03020f070b040203030702130c0e1905040221070521010e01060e15030901090c12 71
    0x9010045850000c0601c180d1070200c1502c1c240300c2c4800d00c0d88641c58244490410307081500036510000c00c400842c02040080d5042095103200a5420590540c0c4900203004980340a03030038a0b401c07001d41081400c01042c008140725240e0030000742d10711551607000360801c0034035411102d4031084078044d4050f40306803090000124039004002240890b039000504100e8130550440032003601c01154010340e034440c6002c011144c82c00c0e140d104540c0c45400c0c11482c01414160b0000e03103000c3c0070710113080740d4040d0b000141513480c02d00484440c40d600800000c440c0360600028001030003400011400a044e02601881c1820050710308181d02c0050004402c0d12031800c1304201c00380d402503c152045032029203580d090350108031000d44c000d201e103071609a05d0f40e409030003140f102404c0220004841c4111001042200c5481200300d05440d90362030030740020401c060202d0305141021040009034034002082060f00401984040c00c170038401c806034606a60345002c2510803184440024006201c559440c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 357475350 1250 357474100 357474133
    0x4031b0c0513020c06091908160b0a06060f0f08010b0c10063002060703030c17010e1006020f06060609131a041d0a021009050a030804090c02030c 64
    0x2016510030aa03a10039507440c0c0011499280d140d80302510b240342c0200f108415040284041d603480f1007810000c1c808000d050f15507004010002c24042d0031008001003081400034100700700038100d07070400d103210100d05140d41c42030000d241501c0340b440050180e100c851045031007039072640c60b0446682d481001a07400c00402010a9000c07440d00140d40c070803a03407c955070203400c0c01400700409e1000d08002c00304080002c801c589002c01c0311500d22035a640301c10040142c1c0d0700f8058460f01a09407400140c644900001a681d100409007842d150b20005c81c00040c6440e0710896243c0f040700004403024116a0340c0000340ea07540480450301c03149403c9800000c0716400c054020b4600b0034801030625103040903038001c40e805c403029400901c494100f5540c09081701d040501411140d00c2459070403000800a85280c1e54403100141802842015501d80c140b1340f05108450382000360200801091616030b613840c0018480c0d2040c0b1405012504002d0980c00b410300100c20fa51409001700301a0404124401d03181c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 357476600 1250 357475350 357475397
    0xa0e0421032013051c050706080408180622032003102304060203150105071101030c030f020409020c1b090c070314120a141009180b09060a0b04050403 66
    0xd000700403e01c9001130f080e41d604110a0280030440720313002d907551060822605141c00c903000354082c410480c05010001e207090303017101d40c1c4100e20b5500808080c07080e0005281e038030503001c03460807814000100401800034400440203d07403158a05540100005680d89040540c801c4043c0d03041d042024203900c1c2e4001608400c035580204410014500a1115813203000201a242075417001e81c04020090241f41c802c40051101509003011801d098070781c0d442480c8810980c0781d0764105a203410813401780900a40082c12180c00c4c50300300751b469903141c02685000327402c800c581d40068820740b089503540d03110718084034480360b41c042c0c40200301d986c8058000090358003000048040000401034041400030007000380c1801d84050342d4800d217608040c1020001c0e200c03814000d810201580040c8500048220111022a0b0700800045010360102c094501c05800d0a04041e007285031401c100111507070089003191003509164801c010403496801408100e0f4402c0b50028040303401140022070001525010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 357477850 1250 357476600 357476617
    0x10b011b02040e0f0a030f08270a140f0606090919081611091f060c0812010603020703080a09081b010b120d021e0303070309020a0e04210320 62
    0x881c03100c1a000d01203260942c111100100c541000c4c0100c01019400022044842450310340700c17512742000702d09451040c180d100950700491080761b540000b11001e0007022215500100b01e072010300c000b8500700f5154403044250300214020b41000030880d24140034654000d20501004021003503903c0c40d002c00020542400b5180b21205011481001501413054159188143e904840070310410090204120019040110103c1d8201c800d50400b20502030003c110342407850f002260702d4860030100000d2141c510064000300c40d020000ca00b15825400a020891003662070445994a4040403000c960042c907004200020401c01509078004080e4454181030800c0c0000440042c940300040c0041c042000b4410346800c401039001e036131501440700700c0e03d50301d512050360400c40503501c0550f102d200c010407813428180d903464208150745801388504060030350b074881c035030081c20f041c1483c8411210b4100e0035030b03071440001d1040080314480c0c0580f03400c0306e50003000c40342d1141c03134042195000c1d080102d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 357479100 1250 357477850 357477859
    0x6090c120c091e04060f0c02030a0807080c04050a0b0301080c0a0b0301030204020d0f0c0c021c05060408030c041a0403170906030f15030102041403010614100f020c09041211010b011b02 81
    0x843c1550b42d9080080c50007944102800141c09007400d45c810140d40b4080703442410741d082446044080350700801000e901420314a400600c0765952440900c1038025500a103800c0000402c0120382624035074010342c10384035860106e81551004104100c1c0070301d000c0c024601400300600040005003002c1d005862014000d03540483e00c111060403600854201807114400201c1110f954800d50502040d00e034020020400c100c1c100c4015a1581d5a440c0c0020703000a00d9074900000084c0603071b942201740c502400e042c1d2036004411a00000d0000103400a0006480c1c1924845030380081c1018041110341e041c03006001c1506540e66420100d40c201d40c001e020115011052426500e503507020310040028080640c080440600300009050031500d4a4007c1e44469580241449150303598003520b540b1040c2c5440d1024030141e041d40124140101058010380100000b4140810040e041c1481c09048003581e6038400300e240c90310740c40e500b81c0d0550b51000740816031269005080c0040e04202c1190540040c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 357480350 1250 357479100 357479131
    0x10e0c060d0b011b060b100504051c0203010209090916050306040c050108040501060b0d090c080607090b0d1b05030a05101a0703030216030e090901050105060d020304031803030206090c120c09 84
    0x20703020100d0100c4c01040701c02c0e40d968a02c0c2052850480041001c582c0fa9285c00c81c1443d0609000c2016052001c0140c1300140e9822110b000310758003501125200400500300201904200306416500c10100050010034030640e40c01145074100040c00c24407681e0408009400315181000640d00c40c1c002420980b025501e6002c08604410301c0c41c012b1004c20802ca2000403443e14500305050240250340001590f608030030140300348203600284d2081518909401706a1300e40e4100e41d004002c0622403061826405000b10550700d041e00000554410f954010341403142e40e54850340300306038401074010a41d1004482001d483c0200002000e0103809101c4e0400524100c0d61580802c95013646403412030000300d075810400782c1ca050544181d0780204002000b400035505200002c0c80c58003e940346250015030200020b8185031051809a400410403a085103945850f41002529481d00702c030454a60700c81e42e003145000381001440303090841c00d030002034040742035417030100004848090070918415281d0b4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 357481600 1250 357480350 357480377
    0x30a020405010b0d150f271104051201090b1f03050f0303060f0909060a050a140916140105030604111b150a0207030e210f010e010e0c060d0b01 63
    0x28030507a40640181c0744070300e8441640b801c11000b624000c010000029800c003c2c10080000b16071311a0701030302c1c0702c0c4000145030176078a070394890b205012000b07502085080540c01c0f200c2c00d030408010001e0712000d998540c06082030310201401d0390300c508001008002c3d44800141c0d41c100740115a010203011500302c1491175501d0321010b281c0402e44110040341e400000902c85549480600c000142c9403e41c1d910324949083d543c2c0589800c0003c11010005031288001501615980e205030904442a444d0941c9030400ea100b29680b095a03120300720400792660fa01290b6102c3c0c034140b6a001210580da0181b03076658080c20320024007603040411005c420140012400002180a07443c1c0f2440418003d0080c41c003036008440050002030a592401346c810404140402d83c0101140114003098031a040c484141c110140400101d07600d0401c500d005241d40c518038140103410080301000b00c80020b00440c3d805c07802041d00c4041080c1061f40c410300800c14823050301401c2d0440b003d0072105041403d43e81d50704 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 357482850 1250 357481600 357481609
    0xa050f212809031808071d160f02031e1206150d0209040609051f090c080408090d080301141e1020100e0d030c0906030f090f0b160302090303030411030a02 68
    0x9411081003a0031100c828000b48250001d291f03a070440c00849040242003056070014003621404c1d110082080c1000608a16802001114410822210182e054258016860607950806030340d41c00c4031070030140402d245161500c04000c1062a2040c0382e13181488124003000290320520341690491340b40c0030001780c260720610540d07200720f2040c1c00002c01c2c07a19021490781000843d80002080e50b03c1e081150300560b034400c1e581e43d0305c40d600085013a80c0e00484000201508848a002080c800c1c0000004c20154100c0403000345209061300c50a08143c40c51414004141da250406504008509a0070090303600c680244102c0c108060740c0c3c4d02c2500841c0000b0b60070b00d081c2040384030030140c861031100a400401c202140c0503400c54641013011195070301c03000703000d42c0031880f54a04254440c5100342c01c5a00c03030b0344003200780c0f030784a52040c4c4a00e00614108201200445030110100c42850410202900900854440302c0d00200030303518507650703a519064000c401c9420583c00d4400c6c0c100300001601e5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 357484100 1250 357482850 357482897
    0x80916080d0c21020304060f05180f180c0901090506040b0a0320031302011706090601050d0f0510030308130c0302060307030f022706040612020a050f21280903 70
    0xf4154061940c1e0750412002402104503030040300d007000810804071000c0300c052268802d40d01ca00300e4001c1c01c0c80300a10000344248004403202c10288261405101203440c00030002c00540c5130a0301c81d2202c00d07549204100d202c3c040c030700ca0b0f0700c10001c0800243d44460b2280c2d00098540703442030240201d03006106c2c0d118140350812110510140305e9070003200155a000340407904404001c20322014940340110200c1c014960141429051020100f000c08640c641500a030084004a010401c05031401415aa11071510b80c8410f0300402c19950100e20b13540710202105103070a07009507165060341d1541c0c0c01c1c49015440204103804040d40d0309003198001e40c280c0010180b0824032680c0901d48840301140c0c1504120001059105d075004000412246401c44442c844041031018010303221076014000303403100d200e40145521040000600702d0078002019944030a12500ca44070f0b0201aa034252144040d00303500031010109150052000303e0003490740c0c100b44800d520030714005000700400d0418918040c2c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 357485350 1250 357484100 357484163
    0x30d0f1e060501080c03090312090f0a030e0a09060b0418110d020306030708010b0f1215040f0506060102062710050903071505040c260d080916080d0c 66
    0x54807460100035941e8012841e9070080302c9404910710b14100b0217082c2d5581e11030030356003071030091400001807069002803003c0c04031001007800307603001400030307150007030440003030004580c46007510320740218a0f20458828402034840040b03849103014180480020703c000b480000b203040644035802d0b210040311100190800001d6000d000d600c0742040d100301030500441c1d030040d61031607260880d000c4040c0d50302080e02300c0201e8240d42c1090380154a0249030306001c801c9441e40c9000d684101448100a060700140b50218090b1003521101d0711030800480c3c58000c240c420000305694800030850354000f00c000508480c2d9034400b25540140490090001e030356040f42c110780560030100c0d2000a2003a0403a030000c805441d0702c0200714900d450307681d0700c1d240c003d02c0c01100e000c0740f1040440c0c07101010461203170030090010300441d42507440300c080080101d502228004214090220040a0203c0440086095480b990041c090000790104205d80c42062203009860040c40c0340600740403244403145401048 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 357486600 1250 357485350 357485411
    0x30314060f13150e0601030e1203150d0203030a05120106170a0e0f070f15032313170a090605070c030303020306061b0105071803110105070212010213080c040608030d0f 74
    0x500c3d150001500300e9440103080019032700800c588844c01409102140e0b0312410503030008040002030703008100140509003000307400d4071000a140101d50707044000751840c03c0368140031807250f03038a901003101c440d5804550036041d4500d035000f0982c0e451a40e04800641a5400f08540302c1144d60800d05142071030551260038100e0305040280011014004030180740c4441f4102800300e08120741d42140d4211140f0a6440d042464201040e84441c2c0b648180b4030068000c14030003400392820300114529031042da0710b0f00c0852080c001c0010030b18041e1007070b00c104503041044541c1d1507217103450640280d40f008100b107900c10000c110002d0901c542d03004010340c00d0080800094a4904140090900d011242d00b00041a051881c20400160015280c4460400030f00c0c0441d00c03501e03248042070110b90044085138541d40080383c610203281c111208202203841c08011542e0002142c824801110014014032181d50010420803030740b01c4143e000f1040c40040e00c800020211840c0d4048280c0048801282d07041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 357487850 1250 357486600 357486629
    0x3050f071a07120204180b0a1a1306090503100e1204030c031709031f0207140f0c040c020c0d0f0602040e01150e1e1f0c030314060f1315 60
    0x10343c0e80000d004801c0c650806003180b6045c10000c82100c0156604180c222941c5c4070014184161a041a884020964060081c090710210f622094080d0070403581500041108030000404030f2061501008580014018050b40427a09038230001424440d8000c1850703126092450b401c20041200600045005000304220107081d813402045c039034100a1a0540f01000348411101c2d42e40104490102c2441440488514001d050b5210041e010b580700c040c03c00d402030400c03041402404a03c008464204406490315520158104404c80300006c04d90030042e403008a01c0e41a5041481061012500801c905218581c441c1d4450041ea80a80c200340152240c0100401c41c280300002c800d8081081401c00f040300d1422480440d5401d03102a800510600d10800740700e0140d211405812800c145c0181c80c4a90485d400c8000762030340c80c80f03c500700c0c0060b1074210184203400c03010046e107024190051072040c5040c0402d040019402510002a04a943e1180305409030404640482c3c01407006a524412 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 357489100 1250 357487850 357487861
    0x1051e1e07020a0b130209070f030b130b01020d02070b0f0c0c040f0c090b031b031306090606080d0305010513050910020a0906120e0c04050a0204080f030409050108070602060403050f071a 82
    0x5115005441640c070b08410f4405c4000598401803442e0b800b20144c60a00080d90340104220f0192504454a540100d010310f03442c040250241c008079812082a000c59156100002c4101d995050724400c0003004442805074012852a4200500d10414500d00b1111468040400102100d15604482004039511326002c500140c004919000400c80c103d096402c501e8400e041003245e1944042c420a00040000061441a1541500315101c1c2e0861f07410018100d0a140c480d006205600842840b4881c1041d40310401e486409114103980c400342900b0040d00e0381449040c09040e029007801c466014482d600183e00c010351010f81a10b035656920b20704c0013443c0c50400361a4080626407a5015824011084080000020080d41840d02507400003080d954070741586000f801242c1103200c460140b0b81145004550000282050301e02e405400c211607680c4008441c1d64031254032039540580c125400090109028401030700b0007120081c01c0c24605000c03565010501e0130350b02650070411102d50107004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 357490350 1250 357489100 357489113
    0xe152703010e0303221a18070b0a1209020a05331602190f06030e061302010c031419050d0b01030b0f12031306020a031101051e1e07020a 60
    0x940604078070340070f50b16604168038840190010a4200c80007803921540c0f070410001540340480842d8015441c4c40340f1410300503000c80f01010445079441c1c05100c0c0c1403001c51100c072110101c071180300e1251600322403001d1030044000500b190b440e00741e900002600780000c080d284c44d0b05040c0040405d5180c02d40400314901c03c3c0c1d0700e100e00340d40017640c4050700f03028501483d007c682121000c9a012120300110b985440c401c10795810040d0010041060701e0000001d0b03154264028030b24098448d000da1342d981d0b50703600c4c600c11182d514000103800101945860750109009551240300d4521600d215898804c555601c01e18030f10380024001d000400025030020901454429541c040b1030900c0c0074450154180c0000d104c00002a800d10710405d50840c011080d844100100e428820880740c1d14400389580d0031002c0c2d01c905201c40306901044030085000000c0c6010300c9068071410b0340f88410803402041140041c1181c5000b840e200843c00c00c1c80c03902050002200426110f410aa4024140701c00185000c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 357491600 1250 357490350 357490361
    0xe0304030308010e010303120b030a2109080307020109210501020a050c060f01031101050a210b01120e0706080c0c06041209302105030103030f0f0e15270301 69
    0x4d0380140380e1500500019a02c601d100c0000842c3e03000220740340522200083c24000c90607001000c1a0002d042240100c100c0750380858414026142d540c1026583c07102c0307584034410028003e0000f040c40328140800303c8501030b0489562030011054681840d10f40da0142280c2c410b810032808540089a0801c004004007e02c0d644104c102d0001c0302d00e945141c0d10740080c000300034410781c140200810075041ca01e1094202c0041d0b181042c803a01c051001c180d19405c002c00100720414000348401030f0419085002c1d0250a024a10740c0000380040381c87d2590854155101400d1402c4994042000c250009000c02c03d03c0d001d40e000d52030002c2954200344002c0d04850050340310300e9141c00550454281c8281c0300083c820361071340e50b00320210f506405251007000c2101c09100e40911506103607a0b191880d2b8024007a41c140c0b8800c0d110590048413a101c26110066011103034000122021321021450410308406003c01e40c0c2100118240806446986140070323a030342e100f4501ca51449502c00036403409000d00f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 357492850 1250 357491600 357491609
    0x6080f0a0b01020a0803060103110409051611061b09090a0b10032307090b0a02010c02060f2a0c030c01050406110304080307110715020c040c02010615030f0e010e030403030801 77
    0x2040540c040100213503c038440340001810168003c000141664025082040401030984819036903980f1030941c400245401c3d5001080ca0940d495900d41640c0214100f0303001c40d2483d4010500c9695080e40b41021142e541011101e4a006001d0012540ca610182034000c05d0040790224100821400780005c44942c0d850003c00c05050902440f034190703c103040781c07000540d400f408010759038861100b075820104d681e101c41e0075030900080405402d076045d840001c8100300340c3e003600c0341c0d51200c0c10540b050750b10039100a4a009001c005450350610740f50320f2104540180c030409800e2030943c11016080d908280c045440e165152001c000400c50b042c450032001c074009018050540c00c1c00d480b40c0110f80002800403050140c144052602544e0408c84a8002c151160f580346150b0104c1d8402500d400350b01c00014019420b040e910031816006004072019510803c00e542d0321038031007040450240c04442141702c241c85d55140480e032101000e01980c240c501d6120010b580d00e5145260041884005a00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 357494100 1250 357492850 357492871
    0x60b030d020c010f1101060503070312030b0f0906010c14010501090b190308041e0302031002070303050a290607020d0c1a040608010501120b182205060c0309070803030106080f 77
    0x2c0b8003a15a8005001d0042d142043c03a15002811003400341600509441e00900d6040c800c0800000400160316040351580f0308584c0c0a02c101c80c012820301104600700c0c08040c1d8480300c1000040c1e6203501c500d803042a107600800460b10318007441c14a0508494080e08040e0388989c85400c032503d50304043e803809100500140044494034a9920340c84054041c6c3e02925100c14041034007080f080b007a40002802454005064983c00c115440d0301c44029032101108501180c1040002546d0704401d2165243d0b0400b030202e40b4410506030b00510701028035081b032440e4005001d1010f0005030b02d4180c50b803030341d4921404165003524100a0000c84045c10300c9400700e00c51604001c00c2c80140d9001062a044403001c0c05d101d81410920150580504120411150415080c1071003407642c007107907000d00d40035a030301c0e20031080c00140c4854900d00c4514450000761140d400b50b0081a03140003444004c2d644070b40e6010036078100c0740e140da1119055a201303134030000001c2d94a42c02c0c00001d000320064981c1001d43d402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 357495350 1250 357494100 357494113
    0x130b130608190e070b0c030d0b060703020718060803040e0a051807031b0312090302040e0111072a1d070f170703022b1a0d0b0a020412060b030d02 64
    0x8030500030001d0441116419600d90f45142900c1d201009050054040c42481544880c01c2120855581c2c01c00001980c2e100d04141d03002085041000880314182d8141e4044d01400c4d050005110341400000d000c00d4484e942c41c3c60000b900135007440640040c0c1030031032074072049040562002060303c00103403003591030820001c1c80507003200c0b00150700f80869902183c04101070039101c0c40b10815440030351024080d01080c045000c000b507485040b03070050f42e00c02c45080060240c4890403078200e640d48015000b82d1101000b66001180304812003908a0980b0280c103a00b54200e001d01411210700b9074010b0900800c1d50b45084c1000103443c1a1503408082c1c2c0c40c1414102c03444203002402d07145101c142000050202b00802c0c545403180e0101c83d1104020420103051070f00c0b14a094407409000f0121035000d034a002007035101e040580417880c1803040c0c01041e80c4840000c0e41c8816400c1c8502030403051405600b000005801d1206421508403603000300d000013442046181030504101000254400710341110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 357496600 1250 357495350 357495361
    0x14041203030902030601170604151503030206061f1205060310090c210c050913060507111506010e010f0207030b010e04152723060403090b0c0c1005130b130608 70
    0x362194027603000104544a00406481500100000c0ea9080d0790754140e4080441490340024955000340425159007200419048510360300da241959581d00040000f01781101111858210300d810a100400303840a030001704c04440c044a810b084211100c6045210400070b5241e210b685141d0100744003500d0b40484455642c00b80700803102c0c020a841a20350b07202041c0303041c503142d207841c07081a8400010071003801d0512020b09981c01000002100d8411008012510a0030002041c060007040c1c444560140b002001034400d4030340c1007800760451144000020100b40400c0c2c5140c003c2c41c1001601c031160520341001801d103240c80381c1002801d030070103801041411454035440380c00c41c00c41c1801840c40499190904901a103505200d440c0c45070a01e40030009040030035624000d07446911149240340d507860300b01c00140121076004d032a0f5002068080040c1c1020000c980c8290507a00c3d09616150038410405c41030300713950304003200b0380c2008100ca0a20110a480c100701425003410a41c1807443e20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 357497850 1250 357496600 357496603
    0x702010b15160614161b0201050912060a060906120b06120c0d05101506080406020d06080d020a120302040b03040f050c09070203120711030a1404120303090203060117 73
    0x2964010a1122070010341807070820344400000501c075a00031800d000360b64403c04141d000080554522481903040210a4402070058103d518a14403080414038001c8140c0c00540ea1500034442103500103a90074010703681501e052103250b04c194100c80002070b0307490404a0600445206030040505c0844852040740412807012060764003d030115441103600c51019004d17410b2580094929402c081015203840420001141100c0810383c0e0031310401c540d942c618102e035020070b201d10441012a41c49000b04000c5611a001002e8500b0540340200f10250384070011031900c101050000010782064034940200142e10b59240d071695000c1c07030154280b80c14000e0700301d490301c0081c2000f80000e918000d82020014140400c00d007840300289074103080d20305040080d46a500080a002140048000040360079010341c2d420100c014002c401141003520351402a0356079180050342c40c0c0b00d000c0034480020b025264904101a2610a5602148003001da00c1491b1801e00306070091400b0005040c59199030700340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 357499100 1250 357497850 357497869
    0xd0504031a0c160305030109140105061209150c131505180307050a06080114040504080909131202010207140c1008130c09020403150b010206070c020102070e0109050601080702010b 79
    0x40c0c80ca01205615241c0b0365078840d00c901d80d4000740c0c00c8140c030451000e25400801940c100c1c0e5112a09220700c03400703101001960842400f8490344a0001d0114011001d400d0341c94590103070425040310307600c43c407203900c8032020b40084070007454003680010301c00d807031412156050340109907080f110301c02c00748100c2c0003621f1030281156a200c00311190012104540d010030000005250141403410350310740310800280110400d000343ca0000c00418504880303407d0601c603881c403454009850609040c000010004a510301418071019418100515400301c3c100d00781d001c44c42d0b90544c00048e0b5903c2d00d0b141030040c00182e26940740301500000401c60041d21400c1c80c41922403828604070701c09070340f01e441a40302106050005841d0550b41100071420f006580d0052050302d001d01c404650040b0003545201c241c9103002c0c1e6080c01a005100401e002e14002c0018a01041c03050058031003241c0c90f502c01c1c0701d0081090b84040030054803034003800a2075801414440d0000510305c0203100f0300340c480c00810003050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 357500350 1250 357499100 357499133
    0xc071b051c051213030602280c08180409051005070912020a0603020f0409090f1a06010e06090a03021201020909070c05030a0e040e010903020d0806010302090d0f02300d050403 77
    0x15100b0002100513090034060355101c803045440310024000ca101c502070003011040005807980c03c0b001494080e1030300c21621580311101d14600b04412050072958000d801c40281c000c0c4d01c1d21000c1c00002c5050251121200702c010000400780341a0100410500c21030380244000130060f1503510160300d80003031080648066040150b981d000300700526445208580c03100c071324a4540b1301e4181c100441d04032032421040c00b0340740400e2030642140110200010a0324628082042034000c049a4101040a0b00b140030000300040902c650f0b940110b0440210141940d1302079500140b078440506d03080c51050b4208003289016120a01c055030750036680e104480300003081c40045041840e00341d446c2d400803c072a4030003000a0295899a25020350340d04400350542010820400000340c50794401c3c401d0710b11340b000060560322285000d480302030300008843d20a0707800240c960100c2d0040f40f0039001100340b40c40303c40040c24680c1d412940c264240140d0040e59420404208000c00114003424403040001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 357501600 1250 357500350 357500383
    0x151b2010180c03110102010f02030f042a030b04061104050d2d0b090105060303090a0b03040f061401030501061a03060f0a180c03060f120b0c071b051c05 67
    0x21440d10341c0d4803020320311541c0042000b009403a0201c20860b404e00610f501100a070005e001000712010144241e000841d003014010000100140100d4000542003068081e07a89084006800f2440b98140d0003216410a0b2145049881440100a560710407403071a03101030344074941064104800030b00c1e0b21440050280001e1544100184074600c095500103200c510a42c0e1583c85038050f107008000c0100c00c48940c52254a00303800540942404004c80f03a02c550003c10403101c0030f0a00400c0700141e0806407058500090801418000825901c1030314051b21007204041506d600d18a0110300756502500036900484240c40c5101216041f070040e2900300504036080c0f1000035092000c82c900c2200340d0b0003080b15018013034520440d0380c40c5a000a03801d4040da501445559160000e507c1640c1d021b203d6040c100840c0c0000202060480d0151070300854100c40141ca0440c40d602c4101003031503403c7d51054401c103501401c02c4249042440400c04880703036203946900310340760f4468944840b070007020038914 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 357502850 1250 357501600 357501611
    0xc130504050f27010f0b031615030903030204090504030203091e0105030f042604050a0e0c0d0b012d0306050415060809100504050d020607051312151b2010 68
    0x100060041d0300b10795252003c000300300c01500c0d101c4440103412000b0009003c0c0c0201080400d40d0301c1e104c10107609980c0c03030100300381403e00d009600302d004003803804091f410980d00340f0010136071003400d020382e0303000e00d00070750055032a0b6800b10204002d03108000c1c280080f4450b040e0351820240d030460140c1b544194012a021400d83c0c4034203002d5410b480590011031592a40217424000c618002c000d030040c1d0ba000d03072380f110201e62107000e54214070105071031200d000d40c014024541c02c2042034001c0d00300d140c01071501d010950401c0c25140744a44410340100100c9000c1c1002d0101a9810b00c41c240060070111010b01000044400c42c0c900e099a901908041104c01e80003d1000f1804110800280268100800a80c58141005512032507034041d031600500880022400b031900c100191005544510326500c002868a10040d59400c01c8420807110500301807800c00d030b912210301c61100c48050003c41c65041200c900d00c000c104a010040784000305921854041b4610704c002507000ca103d03a2504000348 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 357504100 1250 357502850 357502891
    0x1060c02040915140411031203060f0f0d06020307020111180103051b0c010203060306060d0308072307150b0402040f03231f0e0a0b0c0703030e0102030c130504050f 72
    0x242404015000400307410071800030810714a12113058443c80c050041c501031801401c0402d0345868060000d60440304091011906c00d10348810711900f00d200040011788000c018201081c1844055141503980603401f1081150315a020301546003625070602c01a03203010f80d81402d121045016603040782c1055510800580e2810f001a101d40c19202e07070f0308209032a001ba06550320701035401101c2e403901900506c800314015090100004500b15850340301c5070580d98480d2030444014495040703168850951440000c801c100c840c000700b507018000c061b2280903c921007d4503003030715030740d000c403901462042004000d40e4004010703200540307901c00e204240c146410b841c1108801000c140c103040e00d01805001c0d02d407030f180800d00064004440c0390284a401b91071070200e07031503640309013024000314100d83c0001c001c4007803000142041c0340f003428001131801001d1145400ca03042181c0c10988441c0005100040b004249000002884121018441881c100010241700d11020b0480441c26091a28851 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 357505350 1250 357504100 357504113
    0x1c0b01060810091d0f0a03120c140f070b0a0f1a060a0e01090302030304060e031b0d06020f12040303050601110703051903021203040c0302090603061b090102010f06240801060c020409 80
    0x1240403003444d084a00402c2d80d0324003140c440200342c000300c01140101c554009201d0450040c621103080c240c42e0b10031410b0810554030495448000c5521500034104802c1c0000707803c1c0d052840c001d0080500001c0c114034080303600012280f5446421001c052185024800ca5540d0b00032202c801009103800b070070300190a001038801403d0b03900020343c14003002c240420510761115503401403807000c80440710713402440b0081c820422249141150046004040e88003c503c40303800034500c2c01803908416203010541d0700c0c10241180103070b40850000c0c1e2504203202e415a4010300a4040d00c100502620b05075286580c0c1c650344414085c109881e40032040b00351014075000f80441d80c4295150950a076072850585071211103040039000492240d105003020614a0400040e03040c441c0008199088020800c400c056440f6000400050304540d250f60b01000b84803c04d010701001013404030070a1034000903c0305142c01d00507031848007604201c201c0740108010b0364404080c000c1c5075016200000c1c00d04107800d020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 357506600 1250 357505350 357505391
    0x40602131a0319051612061703191b0609082205100e03070504050915161b05150406021c0f110a140a0513060c03090503030c07231c0b0106081009 64
    0x114102c180e030551305943e2001c0840140002b00b424651070840000000301950422205440030030788803003000c0450b000400681c01014220f01603140c40341001000c4040c0109404c40c074621094128841c03804024605100c40c012401840c1e500304100140034001c04607642d280780e0701c5928400d54403400458417910341400f28552035181049200c41610704000e80c080301c031200d103601768000707283c90781e20b520449111210101d04903800400740c220a18440340100c0081d00240060301c14540c2002000503910740001aa0b10b440300d120000b095000d0b0b40720544040300c60143e0200d4440400300b00f0342e110f09900501005540c1c00310b544542d00c80e050f001d01160746005240b0400440000072001080207600202c074000b456111b903840010f4645c8400625850303004140000c01075521259050216519140d01803010300c048040c000fa044080f940004ea003008582c0444036001006140c0ac010302c50f00010742805010705003030144c41414541b40c0c01c040405036128206e4040e86c0d52410780c0c048544c60142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 357507850 1250 357506600 357506609
    0x2040902041407020d170c03091e0706030b0a030206040e090a1e02090601020106030305040b090d150b09010905010602060403030b01020a050114010503010c110303040602131a031905161206 83
    0x20007100e1042c80700c0110960098035034601601c45da03030180c0c120074480c1c2c400d00078107400746c0003240361515100c01c004100d8101800c0030010b80503c0e0a0702010121030080034040c446681c0c01000568680140501220140c0c140180149410402480583c840300d08440850312101c50805c0c2c182d50380d52840342801c0c5000c10041040100000c58404d0001c0248140d1502e40200c900f5603450302c03103000581c01c03218580b100a01150040c441001900d042c0009030100d00c2000d4070308043e4980315030380c40300f1214500d46070340c000540e1100513491038201070640502506203030310104019410071102a40c0c500e00248018101501e61a0843d8240d01c240b09503089aa0300c030000344140c680c800b00a045e5460240580d60003586490001c1158510030300f00c682070420a4805035145417500d440d0b80000e036101c00403400304c1921036074002464210034105000007819080c810b60300d030700f4040c0d04845004034200c110307821181040207219240e0511a6a9036103442c041c109040d000b50003104010181441ea0b02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 357509100 1250 357507850 357507859
    0xe0c0d0f0803040807060b0102150730060e06121221190f020a0914010201060b04091509050105031b032a040b01090810020d020f0705010917030112020d02040902 71
    0x344001c0007800310107817000c035200f1002801082c3c030322401240e6841c050150220f4070030500004c2501c06009041203291000418040b000a04980c03854420168003022070028803540c596040001110300c070010354004d01304030b0b59001c040c030b0804d09083c0d580522661443d5018000075074000c50601c40400f80c1c0d42e004c013274034810495250004108020000105281c0c14107401c200070b90300c4202c524422100c202e01d00341c554801c907504018203040c01410980089055640e40c140101d2040490405000100ba0700e1300c3c08160044085e000f60f40004456228408550411005011580c0c004c203d010b121940e0002da86802804207000074541655000803c0b0981c4510810003006030060028900e0340c5c1c4186d505000d02141d5900444001c400d6102e09207042c1c2210180302c8101c00320760001c0c841680c5e1840050b04003509a0000350059018103011641070703568140b000100003900d092101400780e0400c207642158075200c140c1c03030341d26010400244600003190b00001150f80f0f640c0900e400c1c80c0c0140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 357510350 1250 357509100 357509107
    0x4110d03050d0b04150e16051908090f0601120c09140112021306180612081c092108090616050d1509060512010504052815060f06030e0c0d0f08 63
    0x40d510a0402d41955a80321941141f9119110700e4002e0742241c00c1c4013441c0384450803c1c803140404481000c40030300386a204c2c3c0580c624000403002c003004104d018040358104803203104030360302c4c205510b080c0d554810102c43c1e080000c44040a140d07039a019044612440250004241500c0040d09265401c0e18482c185031a145021402d500c0c600040c44450301200701c1000555240c56000070301032410640180300c10003c00401c0c00c00c040c40e030b41603103410800704130101e130341040b42d5100d211307103028803020400000e05188988000303a8004a80e039003015969001e8400c4e42014540f0248600d211031084044c48400556071100800651003c0700d0000c28604c50884181c03a541c030b160103840c0d588a071034800c3d0030000c4c0e039801410040c8200c80c003456101000300702c0002c00100000440b1714520b8894881c02d9401c1c16071006c01c2c11070441d109041d40041c000622a1b0034040e460180c0c0a01d50070613020140380c50512483e68900085c2c4115042d0211404034008000d0314015541c01c54181c80200303c2803011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 357511600 1250 357510350 357510359
    0xf0a08030603013801120608030901030c050c1e07090f020a17010e07031109130b0a120201021203250203070521090f060c0307080304110d03050d0b0415 67
    0x1000d1805448220002c0c04034044900c03111202c002e080780f20b00f42c4030848540c60b1429610604c0d41c10840034060401c000e0100c00700c81041d0454120354860f03980c03070b00001602c0d603003582d2610440e041741c545070401c1428100380350861681c500407041d007050128410101c10601081c00c002040003408103c1c030910118036200030010194010b100340c08041201c41c1c41782c499101c0620004c83c1a103c01c0c10700503c0075035554404a004c0c0a844514090f090340400c82d8092549a001d001740410f1401c04020a21440351400d10400302c1081e40090070484240070b14000507a070100311410032a03c42c0c3c030100e8a175115014040172030099502e034041a010030342030300002140c0220203414040d02603004d8440003900d50b8810b81004065462010258404200c8450705190003106003100c144054081801c0c9051400221715641c06580240d80b01100482040708010104001c4980004140d8101200700d8465502400b180075512109140d6030b2034101d4508240c8850703000c5180c0380c82030b041240c00a541d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 357512850 1250 357511600 357511613
    0xf0c03090b010509070203120703060302090a051503010e03090d020a0e042907050a0f0c080a0921030c1e0b0c040602300a021509010509070608060d030c02030f0a 71
    0x30101c841d42000d01c00000c00f40f0348030080620901407030b00698a030203503211a4000c40e071b40c014607190500d0358800300400542c954100d01071150340c000343d000905042c1250284c01c005251960948240c0c14640191200c074008000d4a0b0607c10541c0c40d40c104120702d2000405000c07082c0c002d28001c011440412003405105070b101c82c5a004141c0034402da034148400c2070301c25401c0072103100380414001c2140701002486264510350034022490404c01c01c8000741d40d030841d40d51110100f40d001030001c83d82480041e1a011810324440000070107100c000005130781c05400300c2c014810240514208e29201c40c00740b403d15009100e106d40c07001400304285000a2803814a40040c02480014801c400141050403500000310320710000c50880b820741c02f4a1018030180c01e130b009010740001c5000f01c121070b5032a04240d0b400703a0300840e90750001042519141402510b020503a60120b0200b051400c14001c036611401e21511900f41c00d8504602c07140c1352400030074078010f2110008002072142250f084c050000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 357514100 1250 357512850 357512861
    0x105070b0901140c040e01051323060102010f0b0f010813050a0302060403080a18081305060c0102090f061305041d03070b0708060f091f0302180411040e0604020409060f0c03 76
    0x1a190340c8035049854180384513806018501030305515181140040c400c40c80c00ca8001c6443c1d20250030003240040e03048406114182c000d04900ca007010709031003848801e6030280240c4039038201004c01000368138640c00004607003000800345c403810b00c03034203402180c66008081c81e40004160000121348a4458618000f55075034003c8030b050780002d144001003034400c0001e0007810288102d80c0040251048944c50391526903019030b00401910490400025007900d865020b401014000b0300010f032540881c009008034014003046181c0300350020440442c003000b031015103d0584005507070003e0601c1805120011400078490541824440418a6002c0042c0d552403144111000d90300c4c0829501ca40040c0030070203030700708001035006c92100c0c00100b0034604020040410702d103809811038803690302e40204808011290404640d51105403c110900c80d1303528801040700419541080021400504152110000350000b0b11a585810010381400032980203c0e0b6040c401c40e40802c00c240302c0910241c020318 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 357515350 1250 357514100 357514121
    0x15010305100305102a110709050709060f0203071a06031e03161e0506010611030307050a23030108010b0f03010c0c0210091203080106020f0a02060f07020105070b0901 73
    0xc0c1800c00140885409850034400c03640d004008210000903900c164026200701025800038600d100b0400200c8032104445d8050303d001c40d11600390280c8070300c15031030511042e0342002032001d040030203100720326a000741c550040f1041e91401c42c59807000494228150f21961350b0280c8941038452105144070b84000c80d00303000d9441102150300ca980c8400d220041101d04e6624144150000d12800d441c0140c4ce03100310340c3c030610072140c1e18012024050240148035540405403030315800b5400500016410810601c0440e0145000754150301d090440100710788260303888981004280460002807008400180300520b54528007192250f03100c01902d402011140c0d03819105907404480d00b40c45041c188141d441c400b0392550340300c2452840c6c0c3c083c00140d0380200e0b180710400c02e410400050049080c0b8101085905c03d60382d0304c2d03855150210081c9070040c0411544955004201500010b9442104036411400c1414181703844400b01c0c00140c5c1c4034081c445003d00381030751480402011017019800b038603d05c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 357516600 1250 357515350 357515357
    0x110301060f080103171615140106030506030319030212310209010b0703110f01090b0106050a0801062015011505180402030411032a01110c04050901060803031501 71
    0x80300c070080d044078001020f210141400c42c51105407007401c000d042c01802d054070031401c3d07035030359069640d9414081e219811421045680e9413000174090b82801242500403c160710b014489410181c2c00a42c0341d1060100a203007070441c008140714124003130b405a682d604c00e20076481d0101d25000c00c02d400f030505196019451b90090350785110740200005295900c00390040d1079002244c2c04d0903101c05455108030b809809003ca00c0401c584111001c015001030001e441001007400b030a03600d0075404d4150180c0090090000c140224444568802c82c21411180035180c01042a0f80c99079401180010701c10342814180180520b070820603d0f035682c454101c03030b0020041c6009280c901700454803402124255002c8178040219026240b4140d005107030054003540c180c0c0c80b6420070000003481e100c003a55130355114000c0d00702e540c000d5440c03144601582003404e0808080780440c0a01c0b01c0d07240e0340340d1b404c038912031a0b4034800310700300d40c0095110340061704110045a60341e0600780020160515200c1c01d55002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 357517850 1250 357516600 357516617
    0x11010c0806011e0c11030102271804120c0228081506010203180310051609050303030735190b04110f1b0706120b0307060e0d05070911030106 62
    0x20691240151243d9002c954a180841a45599074400301d101300c43d41c00c1d41503400b407065203d811090040c44182c4120300340304136031503001c0310107000c0000148100c074003403964002c08000224203c1c031000074000b102c134540314222510030700c00102c0c0428800ca032007800c0f2812080314001e0522006c0700c401030700d10480c102c40111103103020551948200b100e0650068109100d90b140d8442e207a220b102076400f0080c1036031540740c0c4020490013120011254014000707406920951071a1704445110043c2009602940c48e51a060001034548800008209100007010514200c42c2c0400c1903640900c030030740ca05410581c10300d90a2206414850030301e51017001d161805a010718509032260f4001d4094000c096403c1034001c010700546508414503401c03161140d059081400013080c030002015103069102e10401424251100e030440390006501802940031b036005000094102400f40485c1d103045603a402542001d182031800c08090758014651141019081e4000580c080041c0d81030380c03040d0303480d400d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 357519100 1250 357517850 357517877
    0x207050a231e07030b072102121e0114030a0501110307110a170f1b0607020c0103180f0f05060103051e1506010509041503050c120a0809010503060111010c080601 71
    0x36002c44069064681c0e0340103140802c00150100ca0b4250720603c1420406850851106100c0c1440021003000801130360006250007900b0340c0448080e04a401060310031002c40c034030005c1556608042c060310301401c904540400540c0c0d802c20400c0e40040c0e001d0020322110541c800c03142c81e240c03c140c41c01e4000c01c1b08031039280110b103400144007251a030442a021070004410760b40ca402c039404603104079440002046100c54514a1a0103e4801410007000341410301cac200400904011012008504160414600c96055041d100046130002c0d000052031807144000d10b00100340500400303005249000d10400001440804200c032070341a0f107600050240386039120103280d00d03101400010708045130b101e0301103003d5512400180291300700140c40001c03481042410800d5980c4954401c6800b0340c840c0520a095041c2000355903800020040200717880030550395089264004c1240c1e05040110100c00101581e200d1009041c6a84590303000700103078018804000c01012040715928041001761a0911 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 357520350 1250 357519100 357519133
    0x803040507080d0212090f1207030b0a0209150d02090a0e01060e0d0f030f26060a080c030d0305060a030803090109170405180a02071b090c0216090207050a23 69
    0x80c0c0fa100341c1c0d4050702c00390360120368004558101008490b00018507910140d032580b070b040350190640420307074010551149140340ca480c0194009200085c058014448451035071105000001e030814001d110944030b0003035103000c3e0000e00845006540c801840c07940000c8080b808024181614032603603c24044034001c200b4842d1607800c0b500014005a60b9090b0100480d01c9030741c11440c41c1c011071400030175180804440c1150742a240f100f444134025128140004c0780b410303180e02c10041881e500500406056100081d4550150a80d60410b050b00da10002d84c46688400c54503014580c80390200d600c0e420001d8210303000b00b410280840b41100365408501599803031000351421070703000901400e0f0105134240c500902460140001104039020700241c000507045d40d4201141404843e013550000780f9207019641a0741d0f8002009065400c2600c0d00c1a0200c100d0050005880c80d0a1000d6615405403410303601d09445100d01515426500076a030880c03072004600001e0402ca02d0040318501c101074848003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 357521600 1250 357520350 357520363
    0x3110c060a09050910031b080f120318010b03030706020712080c09010c031b050606010909060b04140d020a080309041a06070b04020a03060e030a030c050a080712020403050a080304050708 82
    0x4002c6408840c041040740341c01d442141d131004420340b00302c80301507980d56075804030448252074051103149000c0c2404045010010150b41c2c400203030090521540c1080340341c02510024040d00d0721020b4a40c548803200009402c000100701015048030f944040c2800d103a8002c1d004428116686c0c0343d4461004203091050484601803051405018a0910510015560801070000840038481c04071220740a0070000060801144c0c01100503000c0c900d4130000061041140c0d4111054862a0260138072920461109031015101c440d42d41000a64040e000100325006000000303512a0070b001001c509454044060072200409803014420405a02c105203580f46141035540d8000c04140050400306800420650b0060300182c1810900b035260b4465070152003124080c119554000192500210b030300d8407400d56403950701c4c80c0c103504000c881c00c402071504101504900030005620070b51480c5440e698101c0c2d00843c3c1c0401240d142549a00d0b20000c55002160107556602881400245146011401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 357522850 1250 357521600 357521617
    0x203060307060305070212030a0e0c19030f02010908010504060f1a03060406020f1b03041e0501080601080a0f062d061205040c050907020c030c031605040e1005010303110c06 76
    0x10302141420b240b001c070000c1000405030070840c481d91a031075114201200045000310f100400100700034609001c500e103881c607017020207130090301c1c200585441201402501001d496125a0321a24401d1a00040b283c10109030080812035103007009000c01c00c0090b0344400c100c02d05c0710310144014044609440101031240080d6505a0031030790000c0c00040b685c0d802082c0180f0030316452402e040349248441c0e01108280b081b42c0c01d031307480020240305010040c10300d0001d424042c0b40040c901c03420a00000d110308009003a1030305000c403c00124014148036040108140e034940d40400010b9585d907a000400c000150f00d400480e403040728070801c01c103028202a4103031049500d441c40030386515001000108001882503901d075001041c00300700c81c2d079042e400324060031069000705082c00849040608111389101d005210303600603103640002c0404150f410303044074403c9400180485940700365600b04100e248107464210b20b03020001c4105038100942954550002c2c0c11541d080c5024818800c4c2482090321 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 357524100 1250 357522850 357522853
    0x606040611120415020c060f090d060902040f09110402040f1206060305010c0f18030b1b0d090302060103120306270e01060b04150504150f0215130b010902030603 71
    0x14084680661104841014220226186040d0703140b0740300b10740d400030f8200e050b58078054406640c46079410040005040c100310b40c0da0340303080c0e482110140350340704107008a4090035070180c002d802c2c002a0391000c044d10343c01800900c04004070503c410300074404060704584801c004070501545007800d20030b0301e0655215044420303105007064a842e41da0200d00b03108541c0030341c4868010000403000e0013003c41a50542c1c071050b106d0b507101c0e480681010605010303000440281d46040001c01c0c0408a420b8002d0040c00c0c40d950324062003860b480c180c3c85109008440c1c1414180c44038100341d40007410b14101c80c02290004032540602c4400c800b612003610403000300344414100c204158042c030402d04c01003844214001900d0500408150030f44020b58004400210085002c000790350061003d0410b64086140c2245018180526030100908026204041241901400307521a00801c808502c2061302c0704410280d06d40006642041d10b03404008480c0344074032000006810b0350900a40e03005601c010f0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 357525350 1250 357524100 357524107
    0xc0302030c07170d02120f160903060f060e010e01080c01020625050c061302190b0d020723030307020715080f09120a030902041407121a0915030111030606 68
    0x450300c00c07071082c102c030103c14990f00820040406000030320041440c1d4000001007038a600c0c1c01c031024090040c00524a451100e10340380c107d2030031a880740901060341d500c07100c00201c110350746000500811094200343c0d284160f5100102d40300071103c12280c120f541d002c1c1158020070213a001284c4510080e1420b000810b0500c1d1495108040007411800c0030301286070440c101040c00440610b842810355007006180b0268bc50b00341541065a210703802081c003e040c070092140346c500b2200d814420480ca080706590b000c10b441c0300300312207a411540200100c507080035000080d9003069460390310590705c040144c0300b4084c00041d1070310b00c189220146401034503589955607546283c00d122503002804207015010302e02030601040504406002400c0c550f903030000d01d40105205010840328268440340c11403a0210070044a01e41c040d10744105900c140070041203040e030a50034200000002110380754802c0c180020011080e02110590000c80b108500a00002448441c0781c07a05200648000da000300080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 357526600 1250 357525350 357525353
    0x90609021201170c090f100602030a0203041202060706090b07110c01301803091d06010c0503070b0705091804020f0103091b06030509060108010e190203101b030c0302030c07 76
    0xc0b03207441c082403c00050791106401e13100018040e1004440c0c030030050b0b441c2010301c14034149521500010b48054001145000b03010b94010f541d038000d03407244600c203201c0030018400b152594070036218465800300040c0b065005516121102c000200e6064000641c862451200c4080010b45111143c4040c1c6030320300c3d24010ba900c000d40740d00b440525000700e0740000155042c4822180304003011800669800541300401d45001494414079901100c41144c3c81c0c0c18005080006055160f00700c8000d00f040007405d182c0e868505c1c1503004020000e04480411810040e000c0d42180082c050200f00b03d0340070426510045a241d00340c2d1054401a4101071a00b048915a500039849174059074065102401681200c0f141d6003040d1107030347c1100f40041c0d200c50034032410000070000c2c00c2c0580208c030001c1c07009008400c8040c1c0d90b000d07031340c800760f0a08100c00c12101c150345060082400381c1e10011018806800850038040c0c00c0b00d40361144100103481d124070305030b01501c0b0780f082e03d0023110809202450060302c5e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 357527850 1250 357526600 357526619
    0x70215091207081b03011b1b0b071218120806063006030613082a0f060105040b01210b090a050402010306050a051f18060207090609021201 61
    0x485886600003101c4400350001450810600d4010b01d154001444a0b440d05010003091000c0100600d010b0385c103003a10310320800700d400c0c9951080301e4903180c440e402841c6203140700f28100d14500003401c124070020038404aa03600010443c0f40c001428024403591040c1c1c8100071140e070036000f02801090000003012201c4e442040305a400160084c55107080c5000401c400d00c0d40c1c0307440014030303042c6a10b041210904044003200f840c0e02c02c00071805401e841c580320003a401c248142100040041d04005007815544203288807541e5400c60f040c0c0c0800300444107209850340c410f54006421001d10417500001081e00c1c0c1402144600141071b0340d040c41d140540002c09000c45192003104040c6c5485020b6180c06071a454a0b0b82d101d10644c400100b020300342400054100c4041c0d4002c203002d04064502400303503441e107400030301c0c01c610000765032050286114002c0f01c48a1128564900c60f01100b807001840300c0d070001d6030206541801c1000c1122036038665000c0200d10a074800c00e43c4103d440d80040014692 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 357529100 1250 357527850 357527857
    0xa03090302031309020714011b030e0312010608040b011a07020402160b0c070b07030c1b0303060b04091a0a080a080c010b040f05010810050402031b01090b1b0f03070215 74
    0x1003401168180151240c0854044000d0341001312541da02254290502c50307112212484104198000c1222450303419170317000b2140704010890103042d20355000302201c010400484440e054110314485071ba50b1a00f0f4004c0c0640300649054500c61905000800c18800400e0f0101540e464244454a8415541c2c00c0c00007940103030b0f007000078158403922071030042000c9141503445440d60345003055558400b071070060b40d00f40000d0315120030036103001c0d60039461941108401341d580c0e90344002e03105504940d25048002c1d000796048540440004140061100c003d504800e0364140c15036041060014540c05100705540d144c4689601940709040c035202155601e8000d040c9140d04000200ba00355902010238242ca190240c0c90286c90769580c01046000703024011164011401c840a00250038150001781e80e40d034540d0005d1000811803900c0c805268000c0001d140101020b400c01c40d02c7d0540201c141d0589280c0284100303050240e81a400040781002c81242c034602d5008207418002c007421542c0003000d40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 357530350 1250 357529100 357529103
    0x3150405090c0f12030c0d110d0801092705060613090c05061b0a080901030501060201020a0e091005180601020d08070f0503060d020d05010c1404050f0f06070212010606090510050a0309 81
    0xa04132605400018810300040000400b000b005180e03080084000404502003446e07a000c0d207400184151421642c002512411902800d00124800702d4041c2e140c0c0341d84801e0000d5400c10000d443c229010420b000c2039091166100300e070b044a20800c0011180c00b5a11012070060800c09144428010f92500c3d50290024642c11403c0321244002c8481051170551014001d5558180103e82108a076034180640c138050001031000754107012490b10060b2400031044034082c8506104c3c0d0018072584c10114448009040c010f144bc64003903002c03450b40b10340403000d49c1e10354014000c000c10801ca91b4010407075507005040a0743e8070508000651011a9a42c101801943d40205810315400260f52068000c42400d80601d00001c0e01c065000c601600034080ba1300c88004041003032004103e41ea980b08940c0c40f46007801e0703d0780c0610801c0b00000811501c5040002035004070240704074040c821055200105540c1c494030b82e610040d84030f001f0003100c1612207010200180040205102c8540719800244011707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 357531600 1250 357530350 357530359
    0x110d0507230418090b130203120a05160212010204030f05070909030206131e0302030a09060807020d0507020414040b040b090105060d030e01020f06010b0c160f230d0803150405090c0f 80
    0x4416aa80c101714207070507621603008420150744102540790902c6031000b100103041c0c0040c034044038032001404034040c0c0f20039885044101482c05043d515207060402d802044100210340d039a48074648088030a02400c801d03034091140e10004101d01d14036114000106e6050340042c5003c1d51500d04411202c10001c0302101c502c00b07440040c004510b417140584c0391103486900a9038070b41010703c334000e060341000e902080c100640e01c82070001c07268000c5021a0941c0e1640762103665540a800400d0140401d0b040d031100122007181000140000d88045038004d0384503000b2100c042c2c070b450080900340c660179240700d60f0007041d42c408a400a800385600303845a040600568144500540c181410710900b42d201c10201e402c00540d43d0301c055028807503079000700342c03510452003034030301340100491f440d0310700c0c001c0004a5101c500d02c5620b4041540c10300300307000c0c0000d00f000c000410707602d0000d44039081642c0799821191003e264034164034090180a1007020b0000003001c13020741e03807403c01080d40143c03805550403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 357532850 1250 357531600 357531611
    0xc15070f080c010f0b0913080a03151503091a1b09040b0405040b01092a050906130f0501080708090606040f180f0c1a04050f04110d0507230418 63
    0x1a038801c2c00341c8480620074001c0007808101c007500340030380910000d00d04d403012414031855500140c0c0d008d00740c039082c3c8264900060502241b43e4450b29401d0150080404003041c4403290705150780c190404101140710b2541d065403c465200c442404200030344510b155240002c076144034900200c2e0241c040b88000400109440e03ca541c003240840c1c000741d03001d40301c4114242c0144801142e0380202c20401c50460010f00d95413454100c0c00c144c44010b140e4030001c0202c0006d40c801207a4444003a26400c00d0b0502c5a1400996901c1c0d414001d088503219103404203112100040340c00e030142c00b14a10910010015208651311ba404000041003040360180e075481d0b8403103049403009c04c0000062038982c071030a041800c115050500c09458802540080d14441440d00400382c01100c4c102a10119a82a01e1501c00c00140400180161081c980b61a141c0724000c200c4074820441c0fa004140100d00a483d00103135011071400d444400043d103514900c51100400c030030003950301134244062001400b20000a01d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 357534100 1250 357532850 357532867
    0x1030b010c0209150f0105090f040504020d12051c1107060c03060f090e0705030109080a08040f0602031510050406020c0d14060705041406070209011503110c07080c15070f08 76
    0xc0a000d03501c0000c1c1c1301840c2d0412200342440703060140d80e100c1c2401c010307007490000c40016200e410514130a43c0a661210040750840d210309050f21a070b00e034042987c03c4c034860003110040c4030b82c00c011a0b120804c105108141d00d102494030602d41c0b045160001f5610340022602d07600080d041c02c90141d410166aa400042c800451580b01c3c0301400d0040b4020071060300445141c0d10b001c8568124034800d134508020720b00003415080856000e64414200501030341e0711170070094400300c48803d000c1c117500c2c000420007907400b0307a4a8003c4000701040b0742c4818683e50461080320940181d00800c00540d1110140c00b81e2403804240c0c414445105246140c4c0d80c512400c9414148541a03c52401240001c81d0602807400072030650030b1003240680719a4107221440e00090001e04040c402c5c0c0025101c41c2d20a134204501c250000c3c03503460041d4481503911405c1c041301e580d4a0f13140c0e00c1080128000c01d9451207043c9020348940301035403c401a80d03410700651780c5500d80502d510902c1100c00c003100b0044500c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 357535350 1250 357534100 357534109
    0x609050907051b3301060507020907091a2206081b0c070e010f12080f07150510080f010e030307030c050c0105040c06080a020702030703120c02030f07031406010608040201030b010c02 80
    0x404c00c401e51200d5030a0000d00001401c91421281d4030b0f4903c4d608006120482d1300c40140d6038580d4045400d90020f40304e00c4c40035603114085401c011050740c1040110080503030b500004100380310a6802000f0960070036104019003c03140c1c010280001c1c00c45002c41d80d0794089603070b0780e040d03001c0c0305502c14074205414460a1411542d40d22501701203800100420a050710480701c04020003a60700541d09a00007503a49881501c0b504c00c4910007450041100d0302480400814014800251802040f1030f04140e03030110721061042c0b24410303046c407545c101d4003c000d1041c000c00c552010b0307000041d41141c8030f80c20305a01030143e0014400800c601888406080c1201340111401107003c2c0d030300c0a4146040844c0200300120061002a1032801000020010385002076048101e9030044080f120360803003a1401c545c03020502c04080d6042c41074481e0b1980d00040403400030704983c4030700710410700311480c81c0c11652103003000d1090764041001c2c0300c000341c0994000e0f00030050300401454011b200c90202da0009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 357536600 1250 357535350 357535363
    0x70e040b011b0c0306050f070504120c120f0501050c07030203040512030c1b090705090603040f1106040b0d1a011d0105040e07020a03090e13031206090c0203070c0609050907051b 78
    0x50f81e0802d481d801c00c005000e200d200e403640020050718030f00000d24007c04007034180d1245200c1c20b0407a00744001824240112000a00054466a14142c140069500780113400307901c1e100c400e0322607501e8400401e11801d00784048403805079054026500306440c001c2044803804803181c030110240010464821528820301485d1007150302c45d60006501001d000601c4401d8400138400010310604100901c81e5554075425a903000c0e0740407403900d8820b1010301d464000c2c03090740302c80d040e049078000c0f030046074005031030001e8019044201410441096000e107068025013292016501007880703001181b500c40d03014440c2d22200700040c10454501030707407807103c2000034404a0390000141c001e44001e60800d98406986c0d00200110301d0700d114036090851071869000780c020380080601030544004401d5640640200004100601d030800c140141c504000e5102c1d4072401c0c0403121045400004107165001c0c0c2d401d1000c2c0e81300601a241c1a50342c1d034206981e26030090400100100c0c946506d0800c580042160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 357537850 1250 357536600 357536603
    0x1509050c070b01060c0b012610021e09090c0309150109140f241801080604140f1011131511030933040b03040209060108070e040b011b 59
    0x140d554969250509800b00001030b000242041000c10030000822150a0100d040d10031801d0f07071540fa8442e400e00d07040700010512000005006191011544d109141d01400c00d40040f403030034011419440e060f60742035201303000b00550b2111191001c0b601003810f40010750b034484588001c4400b103002789902c0070b42c6440243d000003441602d50440080200c0030b08003480e0001441d02c1039142e00c0c1046031210f8981c03c44e520805500c20382e40f880513080c1d0350b1213001440c150005000d4000e0b072540c40e10041e5441e94022242901c001c041c0c03200b120000b41000451142e504e0b0004041c04880d603d100c030b80340180103d07200d0f0503d050070500a01c4000c1322541e007014018098140c00d0b40800c2045603029003111881c40700607039240c1007400015125103640b040c0000c0c0300e0418850410084d503004042c03040700b0b40c102c418a8a101c0218011940484600042d0f014030b00031070301c41051f0b42d031b41c5c0011076010604482010015082d15950a40c5041a03084801d505505050407000d448100100a0241003000310 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 357539100 1250 357537850 357537871
    0xf04030b0118020313060c0903060908030718080d08040201092105010e0a020102060c0f04080607030506011b020f0d1514100801090203030a0c030203090d061d03090f04150905 77
    0x100440c00710a46920305280c10b00c1030a6003180f40c81c0d0708042c8080d01e00c0202511a580341c551401034070b4801c0000030061507201e042000303080b07694103040440d07803c102c611b180400c1040313824400105c3c03410a64411500300c03c00414185d018820b0032101410050000c07814018606404a145085070b1810030b0100d0600c440210741114508003142581d4003a4105c044039000f4040510250b42d002c96000d030311820500b0010707a01c2201300140041c500c82c03580a00c502d8003c5c0024031050a40c180c0009004070001d0740d071902260f003031001c84c8071030104036a8002c3d03222448004411184c14100c101a50391030090007100e841c00075801e030b8002560005088000c0340c6226008108001c01d0080318003002c0c09030070008004102c0780741c0c082a070341d114030020b203030a201d0040c0f5407074100b6100b0411903e980c1406041c49000b4811072801c4006000740c000314a0307118080d184080451311000080c1c841001004000082001e0301c04144001050f1a0440c0d20b034030802c46001052441321400741c0790140c002d244 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 357540350 1250 357539100 357539123
    0xb060c01090b0708010503120c0f030309061b03071205181f1104030b06011b0c0605030601110c010f0c050c09150307060f020c0603091501150f21020306060f0403 71
    0x42d003108420401000c0e4424006039400601181e1400600d441c4020052003500d940da4281c080c1651500d000c140b07440820384000030400c03086500c04100640144101070640c0e21034080b04c5125941400200e5030800041c0e1090030300c000c1c401107a044540c004180c14032001641c8141e6001c141415072001c2c9500c2c06195500c00030198070094407840000d00c101071340309424a030451b500e2b00301c0540d000c0d00031410459a0b4100706004401003064400301035202e6103d00e89541d4840001e08650001c0305d8241c0468075901a040068038007003500507522105940f4041c5285030544180c1726042a4241038402384074144180c94070f0340b190803204d809901803400040d101c3c00b9030b00070585030a2880d0000d03c1048002020014601d40015543c107017600c0c2240c03001c1d141d6440e448401e15068032202e860746030040e02c0000050101c0320f03060049400d2201e86c3c60380762103000e5400603182d03007524800505001d003400e01720390b0311240c0c1035003e5608803034020f213200d00e00000c0401d8001c1070341003500b003513400440340c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 357541600 1250 357540350 357540353
    0x1403072103030b0f12160602030403050309151209010603110d121b06050c0403020a060915030f0207021c05060127050a14150405010e0609040611042102031e0a080d0b060c0109 77
    0x2122600c6c005c1c950b1748025447c0a0030741d5074a5403240181102c0c1030041c907003440b140c5080d43d42581a07030300c030180c218000103240c038000c6c811a0103440688000c7d030340b0000301d11044c0d080c2d00701075a400c9046500311101c4040007400c50800c844040b40c0c103510149101240d0200c800140c024018980214812031aa0351074500b03500401c1882804c41d03200b401070000c0d4500400c0041c0c0c240c42c9007156041c0d142000240b22480880401c082c0c801e03114000d5100c0b2503000541c0b019600c101d0213031221030084007100c00b140e80f15400912200d001a80f40300102e901e000340c0300b400d0b0302d9a821140e171000c0e0700c2d100410a04200c3c4800e82d040d643c107580f568000707a0324840c0403820f400c02e48611401448107000c02c50b0307281013183c04104014005040030f0079031510b03181554010842c2c0800c0f01e00070452800b200c04411a00c181e0307581d018400e003108034480d008840152005030b610f030000501c0400490701501440307880d0742e030b2180f07030782c1c0443c03020014507894250a001d255036000c0a04048405500046501c1d40c59 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 357542850 1250 357541600 357541633
    0x11010212011715010e0912030702010f060506040602030403020d0c270e03030f0c090a03020a060302090406090203091903030908040b0d0b0102010915020d090c1403072103030b0f12 79
    0x40c0c00100065403080f031034007046200d10000349044644200c000c01c45500c0300c1752080d090001e0034855250910000050180704c1e03a05602c09410b001e80b428040108a0300c1c0d0003000013900c103d10888005038403c0c0000d00140ca448130805260303610402503244070710350b44e0311401009040c84205c0080028104041c0782001c009005000c551480440071310315500e0442404020944060400d464507440402c00d5003541c1c0b558011070001d140c0051158040369030b2080b00501a5101c2045140039074140600010396540500030341e070003102000e014102c1d907800500fa11074048e58080c01034080640307030b00148000c0b03018140200051302641440380e60310380c00382034200c05640341884400d04680c5003031261000b00340310107201c214854000c0409030391000360a0348a00640404040901541c0d05554002800070003c40c240216020a070260b403507d0b81c2c0c1c2c0e00c1d00500300c002c560103124002c042c0021040028882e500c4404c08400040c83d00c0c0000c0858800715150340c040d0303600e80c5890742c0401d5400310f0b118070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 357544100 1250 357542850 357542879
    0x14070c030216080a0b0601110f030a030b0621060d08040305010504060b19030210121b0f050403030512060a090c121d0703060b0303190504060807030614101101021201 73
    0x40942c1014507907032910f10070a0f034420100790090400f240c8000880c07000da100e512110100210385003128251181110903a0f121f40c00281c2c110f0102e4500300c07451280342442c1060350711514844224111214a4500c60070305608001c10305a48030341c00c6205000054182e078050406507006100000311442c0c02c1ca0000215820080543d109180c07418404a42d000c0030070b600420b0b170742d06840e00d18501104072001c1d01c1613454800e502010b1800c2c4034038050a280e041607880001c0c0d9003039940003d40d503106007050750721303203e503020190009030300700002001034600081c5580c100314003904484040d642c0d500102c0480f6110400d02000880c0c45120f10740e5900c0e140107190300d54510003c4800d2011810710070964610143c13000924950f11032040b41c0d07090350103105035116031080d00c100f84400e00040800500b554440c0c018003001c19038020200b04510b00c00d1040c1000e95100c90341c2c0c200e101d0f0a403010407044e171245000d900c040080c002903010911400b070014010921003600d01c64195418000682c4103c075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 357545350 1250 357544100 357544123
    0x5040e060d050a060c180e1e060a150e130e100501080a02090a11220f03120c060b0406080d03060801020a081f050d0b06131104060f0314070c0302 64
    0x1080c00d81c030000030840105804a81c9a80107000064501c0c54540a441804c40d11101d02c00b40c0c0710f07040000505041260100e84030310131440c802041a0176800183c00040426542c55802581a03182800700714429800c4401d65411400c100d8140058000001e19003880c40402070f003e251034804484100c0130810000b9504105144103120560510740803550380c00390008082d11408525022400c007616551012680d2000142030300d0340c40b14145003c07110403402610490441e40200c40020310151005d1080003641e9025003045201c00c0d280f00222015258004166140b680c1ca0000c401c0b1176aa5101d250020142ca0002d00300200d4001000340c1102c0301a440050b46074010880c840b0400e512440c0030354000000302c145940780d0360703100140240120741d4000c02d8100d80c00034800803d00c44500c0f00303640300302011a01d00b03010031880c02c1d5101c2503030710040314003004003014403051203c0f502a0030780710420ba00b1440c5c00105134402900049881d0702c1642d651021a06d050b85003002d15506100080642 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 357546600 1250 357545350 357545359
    0xe010e010c02060a0f020d14040203100504020d03081806070207080111090f06030c040b070b0a0509160b0c10140403030c081909030e0303030403020d020c0a080606130905070605040e06 81
    0x3051030700040d440b2800142a0942035a0310b2940c3d62051003943d068400f07401d582e035000c0154207001985000503000683d4103a00c20310401c4a02c0d20700c180d03075010380c5108036400b600310f480c04080d5960035240140060a00c600f944400b58900321b16400070030401348038400d2a80182700092809500e00e0171148003444445e10702c0800c0100c040706458190b400503820380240d40c02c907500c0d9a1095891003038001da81100e8404580081c941040c0051809124024018039008001c503869603440181c3d0782031100081c404250202e4820003100c180000507242114006003615100e8822564403003ca40c0c441c0343d100c43e0240d5010502c81456890700c1805440c01d094144002142030520ba440d184250580340c0002d040e0712680700b0030401d031241c0c01a02c0e15510103002c9070340320b04041c41e02a44440c10011020300503c00c01a50b02210302d021600c02c0c04407241c1d4405400c4a460381e4050000f0440040c0300e1b2000f0756129075071030300040c0080010100520300c03135841d541c40314200660f084e94000c010f010035108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 357547850 1250 357546600 357546611
    0x90e0117030405060918040602131401020c09060f030a030203041a04030302120c0a0b1603051b0412020f192103080a1d011503020310020406140705030d0204090e010e01 74
    0x2205030000882e41a03400c2162015110410b02e000144465144068040440350110030700041026680203011076070403407104000626140e0300c1d421003400720125601e005038080c94800c011402d0810401e030f003204000e4003c20f041a018008245080304030343c000c0300140d00018081000c0400304054009140d00103c490786018a1610b000750f81d000c00c0440209490000a11102c2624041228500141e44203044800920340151925009030301c0f169003502081c10440080c29140302d08480440701d00d100c3c03031034130700302820004031079010300d4440f00032038100c1e03009011044103130780e00c001c9803042d5000080f804000906000041c10a54504a042072400c0200703459071f030003e500030500981c009806800003680c1159083c507400c2024503445101015407802407040ca82d0605c040b0100c1c240d030b00030b80440d400310105041202c200d200e80d210b9500000d088601850b401d282c000020410b0380d0044044a040c140d1008a4400301e82c45a404407280c00e9031380601040014081c024040c0c0380702d24800800c807 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 357549100 1250 357547850 357547889
    0xb0909030d150b040b030903161104050601020a20241308060c0a03020c010f1103070201150803030f1b0a09170615060f3606040f0303031107020907090e01 68
    0x5180968045c4141040c00880003400b403113805c0081c1c4180c40c16002e45111044010b09004555a0001d10390311b00490401000030615400051282d8949600000340710709e406040c60048010600001070340d030300ca00a54440410340703005401c4000b52208138031029079140315501075020001c10540c0103156a030488c20801203502c03a2801039a0100f41f20b07042c05039076480e41051440c010841107401510310307490007507000078544403071001c1c5201d0f14094000704521a002078141e90764000900c101c041590007000050400c0da54070180743d0b082145508104c5184409001090203a0400f201100020305500740c20071074424142400e0040c0c14864001d0105824100340d454a009110a06240207a000203909141400060f040b40ca080110003807003c00100907000002c2249400c44082d0b408100361090304447e0700d4100101c4044030f04008110f8295881c50703030142d020b040202c184000c182030611810340540c5501e94801d02c1441c950755815001070401d260019080c0741130300410880e40c00040c0c03000c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 357550350 1250 357549100 357549119
    0x1a040c111002031315050405120702030307060b06040b040e04030206060d110409032c0306010927020a1211090702010b03070e0a0e010606020f010b0103150e0a0b0909030d15 76
    0x80c452103010070056500d42d039910402165900d0040c00038144c0b129180140714801c2c19900c8240918803900595030104c410020900c1a030044d0031020f903040e0000c2000c03e00050460b4821859504041c00e80c60629944403500300058101c0c3d40300d084484504d00810041650500c50580d120078116054000040e140c2c0324018101030000d85580143e9880143c10141030003610740c0e5403c40889102c1402d04040e80c402d05406941064000d40684641800880c04d6a1280100100694041801c540c81200000803095038040070f80182d0f0001e006010101e96660004110101d20b80940980400702d4a4002131001841d001420f140c21a45860304074801e035038000c1066021a903054080a840d6140e0f86400300040c8114503c115466180160000e5080d80101e880b02010102130020000b403407603080150103403071241600103000482c0240900c551600d9141c4142c0158040f040000c01381c0c80340d008100b1020094428080c19840400c1150040b041070040240d40f07020614040607551501c81d881 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 357551600 1250 357550350 357550363
    0x90106050f0a0c140a11060307080c0a05071a010303021b0307092a0206010608070f0807030e100c1d03010b060f0307020a1e1a070c14101a040c11 64
    0x40c41040000122010050300c03d00c2d4140c14a07400030720403950b03041d42c4c895507543ca00c0300303083c1116100c8040da005c0c0428034282c401d480c4180c009441d5a2440d40c0d45020381e90442d40240404070078000e050050002144c00101e220402030320b0350034480c42c507504604002c0d251081ba8800d91120300350000380c003021503e01194400c12151950300c04a110002220401c8400740300c014200500c0c0d03141c80c0103060450b40029800e040300e007161a13189564685820071900d249208400300041100403002c209014401c0d402824040703500c0c3d0a40d0b24238200c6580c40030540300e1410a480005e55244820141500c3c0015179004d80c403400c8008001c00c0e552800424028042c0501010011501100045200c0d00074400c800d0107940c4100d6188540d2542c0d150140800703040481170328070204901c10103800040f2500d859000d910f46807941d0b0710580030307581c901400b4056107655a03c6070049604c80152014940103205000180f04081c5d0075900400f03050000701c8031001419400c020a10001419160010480 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 357552850 1250 357551600 357551617
    0x1401020309120d200306040b01020a051510030f0309080f010212041e1403180607021e150406120b0a0e150f090a020a08011e06120b1906030b09010605 66
    0x1641d441c3c2214440450050042018840302600041ca10b01c000c001010015031090070111340400c0500040001240d80347c01c2040700078005c2d40280031001040b440c0e1041c4961081d410104d015000d030b1207548201550240440c100e0220300419814010040d040c4200006600560000c604110395044207420b1b00201400c0a0710003010302e8000c4a00a0403141c0f072500c5a80c0005800380c0e20301c0e00d83c004940d2940202c901c011400c005280400c55440d00314101c403005500200344c0740c41140c416030031201180d151410a9803100d00d25222100301046000039100800352921407040d80d0480c4901c130000e40303e00106403885108221000e0203441d560f00c0c25981c012a01c00c200b05001c4107140701044240346915086644a03110000b004105000e0f90010711021200d43d903030760800e990b6603100c3d00b02041a501d00c48010211040705000741442140300e402038956118010503132320481004200c2c1c8030207002008611000003002409502d8250054800228003500c41c0002503151800052050040040b0f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 357553956 1106 357552850 357552883
    0x210f0b04060f061a0c011e140a090c0b130801060e070e04090213020d06090614150901050a0c050109171b07050904080c0a05030f071401020309 63
    0x34a03030031140604062580b0301e031382c0c040e0001d075604120b54951441d075982ea8a50202107100380d0910f8900e00341d001c0000d030380181024001c820100104a40c03100790801c42d0f00300c00540c10504550444d00f07086c100c5500e628108840f080240155402443d6075820f203030011421030401002907000b03030116240c600d0204500390500050701d0303003004045d41c8086101c44240c0340076200d03002000d14500080001500720f84901c2034400b152465040754003801c0d4014400102820044500446070407180c04050500102a00007082031103249072000c20071001014a80402209400ca50945a4000001d4082e445611005601d07030b08035000c0003011000040d00c3c160f03400300c003103152000c0c2c80c00600824000d81e11500c600841c0d611030b43d22514140316400342a00804d0043c0040c024610be0084159030714501030070040110603200c40e5100803a417041091025a2100041c041c10742000c008 = true := by decide +kernel

theorem cover : BRFrame.Cov 357374100 357553956 := by
  have h0 := BRFrame.cov_init 357374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 357374100 ≤ n) (h2 : n < 357553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
