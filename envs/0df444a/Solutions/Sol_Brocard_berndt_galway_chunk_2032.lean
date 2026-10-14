-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:29:41.733169+00:00
-- url     : https://prove2.me/submissions/996a447b-369a-42d3-82da-c83f1a47fe9b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 365287769 ≤ n < 365467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 365289019 1250 365287769 365287859
    0xd02060c0d090516050f060304030203041e09020c0604020f010f080c0f120408040e13111e220b010e0a091e141f050a0501050c030d05070207030b01 65
    0x144005660015074481e98a007604e49601c046045107001c605010910b45481c02a034250f908941c1c062451401d03641c02500c074065445810380d0340c0021b8544226444500c1ca0083c003a0080782c0c4112349071061803174803a582c0d58094a01303a0041d000420400c41d01c0d40b10381400c2e044840c407070729061a9921450768130041544041d0908080300c1080c07100c10000e40e410600f03540660f0040c2d060a40751f9092405072917061030042c04441010462a030884005540c0000c40d5101c02011507a0b0182d00d6845000c105000e18464066035101a03450f04443c880950200c15a9088462400411441981400540e015480110346541c000c2100000f04200891074002c000702041d00c0a030148858241e240e000280d80f040010b01c900c0902c504204281440001410702010f001150403040715450300001c14203001c0c035400340703030f041040c0099040c100d00800c00c12100c2001080404021610b08414000c3d180c1d2403a0004940d036410450001401c1d144110100080c0401c0158a102c1b209405250101041c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 365290269 1250 365289019 365289037
    0x1506040b0702061303020d05060106110c010804021c121205060406030503030f071b030f1707090501030e16080319030203041109090f01060b03060123090d03090e04060b01110d02060c 80
    0x603001c100171006888281e003140c2403c4c4998002d141c90b5045c040c0250402d0b141648498032607101c0251a00713241c0e480704002e6001901550800b4410440c1c0d51010030072000254041c150004000c4880d48481e40a01d000c0b034002c040c00c5040289480d0442007206880207480f0240c080e85c028004150301840200d400e903040b071180d051548401d510b5840c0141c0221829205038040382d50902110101a044981c210400c041d180c0d0502c51807500d280e0103041d207815801460304050343ca551001d00c000341008118031100d0550701e80d12030280d4642d10580c1c0e95004544a0f440d2001900400409500a0003503031302071035012040b0410f0034004010320055401c000c00c550a2842000f04c0c029002d5028850a0068100e8000e050703171700e01d0141c001525803014504140d0080c00441103031351151140c4004d17980b00a00485507042c1000c074900313007141c083d0300c01c1d0820160600c9407000d01c8200445507001400244082c1c88808035100c81c42010703603e0741c140322903120160304000d0016417442d58807802400340c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 365291519 1250 365290269 365290297
    0x60506060d0c030209040b190b031005060d0b0a1e09020a26102126040602031e121611070f0f080102040b0d020c0c04141506040b070206 60
    0x40340c07040640c0540c0c01c428081004281d000940007102e040a0084907801c4c80141e5114101d08040500000050342c3c0d480760130302030000817012070003070116030001000400004003640c1e1550a40d01c029402841d010101c6807041103805000603113041070102c0c50390040000344400507040c0c6080b074260b0103036018007021004c00c13031b100c01d03400121210000d2110059580441c540607a00d02401c000700e816041d504603d0340e1107410074205440d903074004901e0a0180d8810380c0ea005600a640800c1c1081030681261000c48101040101d1b1055000002e408652400c4040e940003c0341c80000c5c800ca0721400180c2c051400c82c0c035001850324158000bd11000a202e444c204800718058800941042219000704404a4040c4030400a2200240800300581041c4000f1481c0a103045150805486158500000a50007180d211805031080c000403410311030203403081c803075500c120200c00707586172085441d1070045040e0031103801c0c1420100c0a850507500c40d01900c600c1c10300c0d0b40e02000301503003007100f40522803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 365292769 1250 365291519 365291527
    0x908060a151503092003060603030306060f0d0908040305030d0605010c080901210213080f1506010c050a0b15010813050705010c0c090606050c1005090703020904030c140c040b030606030a06050606 86
    0x5204095107206840007402d419170f20380d14100c00c0604120700500400d20a07441813062081e04e0341c4050846652a843d0302c1070070741d540302c00030160700680441000a009504046000814804088007c041036802d40c00e080280035194001507884480c200030107002180113200a4885500419160000c007003003a18202c1041500310400c0f0603603201c3c108400f8039008000f810010260100003000031069640090904070501030001101d0120080045040009030b0081209110040c406003110720b4000101600d140760240310405064200c0340c51900107007002000590613030000c1a04070300c50354010301400d00140740400448944035002c1084c0c0d6071801d15000055500035910a400080c12592070340f40d200d2075a045c0960800c03074071030100c140b901d040c2010050101004260603040d030f035044a030244180c5403800c0840b10742c403c419008000250001130b81c031620400082d5114408030850b01440943d01000171302d40c58075000ea0315550141c6c0003000280000b1000d810a03580414054102810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 365294019 1250 365292769 365292773
    0x1030f20030d0201061e1202220c051e0a020d230d0b19120201030507170a0605030708010e1b0411030f010504050a0501150f02011b0908060a15150309 66
    0xd02e01d048a80e00007503036440e10100001103004076028100402141501142440c024083e540144c41d0f810080c400d04c5d030b910030315205654403441803100b4003051030300b00b060681c600c0014040c0e40c04548401c10000c500010116031040b00e4048808211160340542400402024182c80013401c002034a00c0d1000040c4064503100396841c05130403182d80e01034010903a640800144070804000c0c403448110340d0740b403420601c0940c140d881040000d660a2074002210f80e00c58001b00d440300e00c0340024074036000741401130188210554202c401130ba003045050321186942c41c3c00e021b0807155403101c0440702d5005030b048030386000d130034080a41c2c0161024001140700c0010001c0801c07194411070344107001501000050085d802c1510680d9070025050714100915410000464501405e400754041001710586545485600c00c0d003008100301c03c8105298021100c00c1000f4140082e0750007803050921071100040c1c0390501c6409025011500c4d030350341c0d0a4481c103007440c010004074003c10007414075032503800d0100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 365295269 1250 365294019 365294023
    0x6010f0e01110d0201020d0e030403050703170f0319540c090507021911010e041b03111920060c07120c031b020409060504052401030f2003 61
    0xa480f5220350700050b940c19a100c038410894180c031408950326803081c0424000070724002080b50650381c101c031004030111506a5007014600c200740710b001452101105100005004291200c1d2008411209000c0900403807003002c000306900c42407810381c620030000d98074180c420b442c01b4204941d940034800020382658103a603485155658046070b080741c1c000c0e402c00c1081c03d68812150003d0740d6101512000003420054210040c4404002c0e001c2003040354a182a6802030411480c16440a40b091001121020000036242001800500031900b85100081c0301c5070600100d524281482252060200c5c88030001c4511030300c8804005100802d01d55120540c00701000903520444c0303000009035440c1d14034030b881068102100318010910101481c070b100000d4108209000030100d441000c07441801c42d00000e0050100490080e010500d000140070038800045044810303d642980451003900b00c1030940d400000003488080c00711034403140d98400041e445000c403545100f070070801d2071502101000080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 365296519 1250 365295269 365295283
    0xb040609050c19050a09150e032a0405010812031e24060304050c10090b070f14030418020307200706030c050901020a020f0613090e070e06010f0e0111 66
    0x1900a5102142400c540f1a40068070005895035107407031070928000100c043c000182d02d004215040e174244030790206440c0305503000085400001c0407a1001984503c142400c2d5007500240c44084042c50307a501841e083c503001e000d0494200400404960403c3e4211a62541002d00b1051001d52075484610304440c01c0b079003007401043c03480382c1c2d507190b9804940c07115480402500c00b10f008620900c00c1001240c80840d40015034081030f1450707480c03204130b060201c490792829048000211008a850028400e02035084c40c1c6441c03160340d03603007802c10100e0381d1280d4034003451051000106c480c6511070350700100740e0007454101207642400691003240004500f1751203a03120304403619502c0084108030301a0b141c0641c1341c02d11403e0034100c5c50080300b800002e46030200ba140c081d02484030895408103586401d011140c1c4607040345070074820181c480c800c12004e03050402100d4501d10500c0300c0800c0f00c100440c0031601525050f10340d0145010141000c0e10200900c4200314180902c001d200d10340031009022034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 365297769 1250 365296519 365296531
    0x12050f030114010905040902091f120c0807051c0f030509041b020114070c0b09030d050f010f1e0311040f02030108032a150901110721030b010801090b04060905 70
    0x2c0a020352000014502d0305641e100c613100383d081c8081c54026071500281145c000b08215409110001d80618203070b00c000300d961201c1c04003201d600d140c0040c425034460002c2960301050035202030f241e80f00100290b428500c40000003400c0d206503a900010759220001d2401486420500d08229500e0002070464010100745440c0a6031384614014056080c0300c2c42403030340010000024141000000100304080d2413200401c849180380101d000b1b41c50420a0340c1110101300414400303854000c4002442200078814034a000c10602404203211440c0481100c0c5605a03200c180e06051840d21040c41c020380320410241c205945410101d81d66074540021030180180d01d0041da92100648070010030441c48034181d540b0303000b0015040351809000b0441001d100e110702e519415540b10b000215005101d6a40307002d00401d030000d0688100401408200b090081c102c244025004542609800780e03158800101d0000f0640782c0148542509036001c80703800300003e04005450340d11a03952404444064038a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 365299019 1250 365297769 365297789
    0x9010612230a050f040b07030f1418150c0a0305192c1501090b01050c0609061e06090402060a030209090a0e07050a18020d1806090302070609030201090312050f0301 72
    0x4000e40c80c80c02d40140394001c5210700e201540d525168903614181c19001d0001e104050300d13044c0882143c0713000c0c1c000040447d201a103103071a5041888148410840300d0110300103d005500c0000210620030707020314801c1c149034800600d0021411822002070070005c0081d0060240c9061813090307407030340d44070300e4528015900711024681004100005401c07800325240916038800300e032030001c580e4161200c0e81114540035012807040c1c146001a6418024019100c059121311030401c40340711400101540140d103280303445010a880d00e00322112112048415903040300140d03001c2001418080020124050545001801c00c0448000101d40c2d1805866259000341c803454025075600061028400820049480c02c6c02e152810240030248008101e4590290358041440c01d07180b00aa0428102800e10380544641c50321a45080d400810781d800003a401840346180c0402e1090140c06264240c94058444000d22490750b0303240072591a0080707074a000c010040c0800c0c1522074bc0031014502030022803003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 365300269 1250 365299019 365299021
    0x2040b0111010e07090f02041a1e0a02010f0f09030806010f12110309010606020a05060f0a020f07120908070f050915041d010e0721051f02040905090a020901061223 72
    0x340806d40703080040c03c0b02568810401084603443e400756045100e01c151090940f150000c1404280801c0c008142e0f000c4001e0019505041a9040d4071100003131100b03000421031004204a0101252140140140400c4804000c20031540c014111115250301515000340d004036004003c00c15078214001e400994040407003170006060003030040dc00541498070050182c19100e0700c4550b034410b009000356000c240004042034040510380c0446030250303020b0701040d40d14100e501c0e10360b14961000c1000c40000303004e1880460003000110b5524119030103c640000400c0c03c100c20040c0c240d402034200ca41c5031481000c13039051a103031400f900380b0300c003240c2040480c14021560640d0950340c00e0000c103100394111980500c0b9241c40064100d043c140c054a0504201000e85080d83c50840e00e100b076100c20303251004080100e06101c1e001441038030201ca5051026445070008181e40c0e4254030782c000e51010a200040c0320785480f820202c610030009450202c0c90302c0d01c1c114992801264120200308201c1280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 365301519 1250 365300269 365300279
    0x103080405210321060d051518070e150307060f210c080402010f030204080624130f14060d0816080a0801090506010f020a03050306010309061506021c050702040b0111010e07 76
    0x244d4481d61200c0c0994610f40781d40c510b9600c8940301c14000080b90f001c210040b002c40c42c417400c03902c0a01c004410101c1110981515074281100d01101142c224400056402c000b003524140072070850304a428545500d070f920070034200161000300741102034010b00280f41c0822403009259000380d000b20561038846500500309400010000c880b2918a0303000d0500400c805c000e1000c00103a4681e00c4284084d049184400d00034030040101d02d00c006044c0e02c0700c036000c2c41c0055030003a648001c00c040785040c0c00308007080c3c400150044041080b188268001d89410058000c1021100101a92482d4a540900e540c04580d02d41d10f20350030070b081c02d0002458000050059a50b030344240d940100090806500c1b00b00076800082d42d03150014002000c101020010072600d0340242c0100b009580e1044051103410208041c03011302c00b04600c1200018410310501070408510344ac04030101d0b04495440c5403a00b0116000d100c00382c03204003510303030410000d481c0b9881026405c1c80368403080d10700400a08182803910f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 365302769 1250 365301519 365301577
    0x204050c03150105090a03050105332b051009050709060b090d080c07060c021513090b18090c0301060509090d0e0303161a070801030804052103 63
    0x2042a40351880400611401442400101e14000c1c003d00c1c005a03150025400300d0211049603000400c00d42c00d041c1402184051b403083d040701c640e10311411904884503102d004209030311540340707107070000e0790b182041d041c004100c04544400e030010300d00318410b14056612140b51504c0c0307003a05a03085940305140070410800307002c3c5000803c000301e410b005e013a0809520840700c4c410b1200e618402c681400200c02004516019692404024029650081d640760b40240c407560035907408900c01d10070100056000e05414043d01c1e4280700380c10060b01142d042207a51001890108485c5500000c6603c490548124140343c1030700c50001e02c00601a145540010301d0b081d01c0c0303150049840340001d0000c00c004040002540e1f80c1c0c06519142c81244140c502000c01d0851042d40c81406d00040c52000d0340c01404034003003081d00d01c120074440c1e0700c1281c0d403619003c6420304400e020040c481c420411080100c2d18115100d5106401e032001054262140c0311a030f40d1855014071090002082029009100003002d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 365304019 1250 365302769 365302771
    0x170403030912110105070303060f0612060b0f0318010e030406030204080f0a020f06130330080717150a17010b03010b060313080d05070e0a0b090904170c01060f03020405 74
    0x8030642000b0103121581c0700034a40b1400841141005800300320803081c54403d4002200410400c2203601c0000e403107010081001788000e1202031300300d0400b040041c480e901c00d07040701c1c4131044058000b030440d01c800480d2502d1072080481c1400310740d01c41c0707108540040180f0003840148400e403401a62140b801c1000d90800941c12040d41c081c0d04050114030243e25003501003900448200c40c0e440e52540f514040c5626802250000303403850342941070740040c600301e00705103c0310380309200131031340c045400d40d03008680340401261000e0000c0c440400d61440c4c1815404501d410100c40b2001d41140c090080c082010100c256100440344448555511140203003071007100e081d50701c02d4000340070300f00741c00021900320300c40907040d81c105818809080c010b1040c9581600c42407d00441d00380450f041036200207004281c010031b994450440001c00140640c2d40303a00f00c44550101400c08081d80e501c9031120382c03450400114075180035104008411020100307100702805440e441c1001440503007940140030890764 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 365305269 1250 365304019 365304029
    0x804060c08132a08060603010605030604030c120e0303070303090b060a0b09090703020702132c060708061215090d0e061215100201091b27091704030309 67
    0x1d2110500a20007850010414110740010768240341d5000c00821400703116401040e020071900d80e14010411a401090070340c01407804034000e004080d2290101916124107079030003008607840301002c1000480b02c2c141203500c40840d00300702e01a04200c9002c00e0450703000e1031040700042d0303544d8030700010011403560058000c041920120101d50031301d0444061440354045440c810500000090086c0380329030111038a2503806024100c400400c100c3e158043d14480200380c3c12512590070150114102d1021499a642000300401305a22030403810340d0f0910b006010346400034420710404150722401c1001c030001e0880420300720110320b0000101c600f00003c8000d25820801600450601a52000305940502d455424900801c0d06c910f10408074140b400b46015820042100b4414241754040d0b008070300341401090045002000c061102c40e9448840c041c48010f2440041a1844603a80c000c000c046039400e080001040700081c1c80d0f00f0b17107466004844c1d102c201d0000805200705984502c1300d800170700c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 365306519 1250 365305269 365305277
    0x3031404120210060b09014401051f050a0207050307080304140901060c03140909161b0b0a09030215042406051f0c210f08040506010b1b0601060804060c 67
    0x41c10314403e50840e02c9005c41107030420461041d5018223820309241500e41d40f80084003444d180003210700d54600d0024031140100c0e16134103080005003d0811440d10320144086480d000c4480301c1d10038003600c4035000030505604500c030f000d0010410f03803000c0280e44040c26050000710b0320346240102003180d0b101c2c0c54500d94081c0e10040c00401801d90401284440b003941401d001105001d03030a08403415000c1c10007195404500001440807030b0711a082140780c1c00f03030240e840c56030026449030146c0c18890040002003104c1c80755000103020794041d5002d41c1d03031030384680706039024014200742043c41c0000588094440b03042803440c500002103100010755807502140b038184a840d14160005400e8180000c1d55802c43c0b038402070414081d48640d11410000c0d41c44040b030706080d00e40c83d200295a99071900c088000c02c52914001020b140a0003030a40315551103030081c801a0b0900c07000c2206900220140c1403280502c1c051201162410f01441340600740c3d5a0707074000a484c0a0403c0800d0b194041c06103011302c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 365307769 1250 365306519 365306531
    0x3051c0b0a0302061c02130e090a0309031401090b0c190f02100b06040504090605010e1008030f0903011e2304150c120c021f06050a0e0403031404120210 67
    0x107464060428003201d030116002502e0b03079580d0407058840507906401d0121a8400240e0020304550842c01100b0307110440d40109450352204c504694407498220041c1c085031060b4020400603406001d400420b4603800004240f00d8a00d5a030b0584082040e5100352070210003103140132442015030740300c0d58129818500060303020b030895000f94490300d40807080e00e040c030b4945421602c140c817500102c0303005003c05032042001032241c1c28420020304c020b0182d40c002600f0703c004225010700048211050f244a40c018520300a206202e07c509640020100c07038043d500c840503001da403103500103000301403001c0325800308407a11281210350820004e10074450b9010050001d000100380014201c04000309008000030f10b0b8018040d041e01e0900ca00082880c60a041113008918a036010800c802052000d0181201c01508800032a058070000c3c001c0980014841c0420030001194401e1150080e001741000103032a04581d4241040b0b09040f02c050750110f8080c4001503605030304000f10700e1480b000c080e0801c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 365309019 1250 365307769 365307791
    0x612010e0606070f0b04060b0a0618050303031005010e0406091e0507021903110c0303030c0406020106050303040501050304020d1e0c03020f12070b0a110f0c130b03060f0a02120403051c 81
    0xc000030071310001d0060082080094100705266200000b5520028000400155200b1008010700c030340800340303803803038a0f40a00000c003030074004242c90040185c00281c3d8072903818280112203040081903c00e070311545a040000d182a12032040c01c0c04400c20142420b21a03a00710840020b495000e4903103400c540c401c0c945000740242c480070707140885925145c80f40503ca18020380740d15000ca00e03c4c03240d505010000500002201e14401402220b48a400030b2080a0b030790340805849000c0c51041501003001040018010f181402d804882e4521880410b0365100c0390520001c2200d0b01500c0880360707801444001d0083d0305c0e040d1048204290100c524081c2c000d80461082d0b22a000c51142002402003c92400e65440c00b42403e01c200203101030891700760300f0018240c0c2c0d0760703410004016802486111030405400741c050041001c960070217801050142c4503410741544141c401410200e01a5090082d65200002003001a0240303029594680d103400007601070704181400b803500c005419140071b8240c18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 365310269 1250 365309019 365309033
    0x2060f0604020a050903010e030c07050303070b0411060708071b090e100c0c02060c0d0e09070e100302070506070c110d150209010504080708100516051608090612010e060607 76
    0x15000d8401e880150301d681004609403018000d01c0603540d1715509100880d4003100001000e0882c03c034065003100e0113560759005064503441003050107003084048000207008500c1100e9955a15000030b04000c3c03420400d502c80b4002034015500031540c2401123010940950b64000c0403001500c0c110130300300304941d162a0700e15a50f845a031140e100340b60301c030924900b00750700844002115980140079503030b4030304016007000d0300c8000e81c00a1201142400c25144420b05080c3c8009101340e501e5100c105041042e0820040d80045855109041540030010710001550501400f0300503007468507526900041858211046418240d0080c001c6417824002000700307142480f900d54080c400d0000594030000200101c0d1240f00701d4000390f8042c072540b540003600135070000d030500160080302010080c2c2e4a40468201e0342101340220507002401c14041240c0c42e42c580b840010040744504006403910840d100841c1c0d11303030010442d0f440022142d0300100640b100048501b0341c0480e00305e9203180f070076416944a03c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 365311519 1250 365310269 365310271
    0x7030b010e04052d18030c10051b040b13050415060c020f040606020604210e010807110601140a0e07020a0305070c030203120306040e2806020d06080109050d02060f 72
    0x51059072030b01c2c00703c0c02154a0f20121042001a0705401024140d81303010050351a00546010100c4581612400d001d0340001c400ea1b01c5200d00da6001d0410031044240740384c0903044c0504040c15105207a07001d510701d200100300800c02002810040c2d91a001c5c0340218052a2080d54402400340c3e05110074140d410300c0d100e071000190356503810302c1e4400304090300101d8003030781d01e04480760340062515002041540d000641e05d031103140b10f44100d88600804443c05c0094090000525020070001021042c296024800c0640e10a00c10300e0480d40626175544240d240203820384c0212424202d0007000521070030046510005001e410b140d101050a0581d002980d51703824180142c01c01c00c011514200304846294a04025170b002421201520803a0f41021180d90041d10b00502c2145010700f2300c00c820401007003981d03141d0002d80c43d5409843c4c43d55008038980480203401c450255080210082d003003000d01c0b03800042c0c902c00740000346d075038061b1138483e2600c01c0300c1d040b6405560081c8100310900a0715840f032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 365312769 1250 365311519 365311547
    0xc030d02130e10050a18110c0f0607030207021003020304082a0708161502030d0c030501051806090601080702100e060106022103040f0201030908070b0405070f0b0306060901090315050a0507030b01 86
    0x1569035041c1982402c01020789a1100b120746e48000303100b42c0c4a88d0001074004c0304000560a0702c04a45444070242c04030711440c10001d4001c44000380c50740ba92402980599030050140102070304c1c00105001d600405401b03068050483c10b8654400546102c0400440001e02440d10050004184e40c0c440000c041c9442e100714028601c500c06035010a52080c801d864801c1080001441090f140b604064043c040c00d00499005500c1c0f1681000504500202103001790006401c9d10242d85442d070044902010003007081c02503100c0e000800c01c01d400340b48202020056440b001e410694100740f0028208500d5108241d1141d540e40300000320402d0407003c494010b0390090019440d010701e17100680103031000010180c4942c3e800706806003403003812074080c0e228502c01c0c0c080e40c0140e921080c9140fa1038500d401107441158092001402c6814030100030803044ca014106212010b9880d590381700707400032240611500341c0d100d03401c1c0042c02101c1c9c060b0580116842c00e0a0004802d1140001c0824a003d500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 365314019 1250 365312769 365312789
    0x706051809060604050607210c031209060e03040b0405040c030c17040c0e0108060403030c0915050904061502150f040209190b04020307030618021e0c030d02130e10050a 74
    0x11a505580d100308440c0144001b8041c0c640f103030300c2801c6c00380c04202c0000c6014031040c3d00115a40b401c038030410600d07009651540742d42c1c0319491074264000041207240d070211401c0d613407035800340e82001e0104040c1001788049801e0550319400c26082c001560420203181d01810b084c0000c2040c110b4011065001e24001c000c28100580c0d0b40f410302113540d603005e0b4030140001c0d552200114850700082007603449940207840512030048905012150340f0888e1140080d040850406602c1e980c4c410303002070888050081c0042081900c80111904000d0b00d0b04441016038400700d88850700d240b05210740d941c040e02c0024110715625260b00800c2c1410801020403003058600172040c2c10307428056011099656000d04215260b2500000c003030003c25080c000c00d001501d20a480b004288014000c541186809010540e5105581c14195886030081f0b415820303207010501400411400e01c0c40501145016031032001200c40c5420600161140040c0030b89500903075206081c8603035240da282d024100c46c14054 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 365315269 1250 365314019 365314021
    0xb040e07060807020307060f0902030c090c0901120209060307020102030612030c030a081909051f06080705210a080301180c080f06010e090a0e060921030a090b04060e0706051809 78
    0x3c100d00718450071100419483c0340403003d10703252406512145170306209504840303290341041300300710405204407054101d03000c0c01c1045110f50351045002d107a000305401d4025041100344000140181c00441c1c01a005030340c084201710091078505a41034062400710055840e0071120581503071a40700d0352240d1010302040c800402c1c0802ca0344801000136110200d010402150b0b6803400342c1c1c890420354240d104103c0c2c074810101d100c4030f461150301d04030391452004114240c6000140710855405004694084828086184030b81d04140b0402011912038460541e81c3d40c1054450400b06050201c0038507414070b03001e81c020419800c801d14907000001c11202007c155110707401200d040d10b0680c40c058000c1c0048052025100c0c00c0d40085940b46015001d840480d03880c01c0300c0558076001c0d0808a40202e006205002c0b4613900701000f19000440d22a0208440b0196241c001c90b4250035a070884107560348405070340311050107214880282900e45080d0b49448031015000e10071682000c4001d2141b0760100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 365316519 1250 365315269 365315281
    0x603090201050d0c1d011b0b0603011410031208070e01031d01110c060105100c0f05011103190507020d09090e01090501151e030b0705090301061e06030b040e070608 72
    0x2a083d2544090310340c0041c042e07551110720082003004980c506541130b214038a9956059030280c0c9455040000081800300c804029845015043c0d80c041c0c100c0d6095582c4101041882d90800d0015100300c0a182c4c3c40c4284624528103000c51883e007006007420090028240401c987c2e010005440c000c4003440d010501e000096882501601d80300b041192940c1f030215101001406600a4011486a0000d95500781c0c2e80b41d040c044000b0701c101300900000e00075686000091440d094070056240960300028040401e1080060b80d5401580c4409500b2100f151034092460907006d030039071105c1d60b0b1018258415111401402c103000030f0280100080d182d6a02400000c4258010f1581e20b400c0740007030000d9090803200240030b44460080c21811a034460882e03942c244840801c1c000c0b82e84c0130205903840d1755580b804031011380144003103ea242d504d52500007044418020303240f1003a80520f07580800e0500d4102d0103022125050740341402107040c20f00c2212051030209440c0100c0d420b07401c120340942c1d582 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 365317769 1250 365316519 365316527
    0x309050f013e03030402090c0703090807030b06030f01200705030f0f120106030506010c200901030615080a050d260c0d060b19030e0a051b150408070603090201 70
    0x1010101c8900759509003140000c5000d42c042c92094102c125003104800d000e140d00c0ca0703e0740300c1118043c1d00040d0385008900d0b0400950010000c00b4001e140074001c031601ca030105030401100b40e2094a04d980e00303409116a9107418030032201e2113440c0703100030410240020303c00155442001002c0c50401c4000c19418180701d828402c40e00d01095076008e1f542c0d40c2d0188001105181c0254855007142d460000010a0850081c41345a00a550503100c02100c0809595441c00c5004c040c2c000c0070041880e811610b100b44c440d115102c1c041c5100308008640c181d882035200400d80103da01c01e41c440e600100150b008500301186035110180e15180c01103074800c514070403c082d91424010002c2c4a8000030410502c01100d074080c00c0031800c0104144841d9583d030107150741500414107150a050380349480c0c17400d0140242d00050b854445103081e99851955921200d0030410958510780000c0b46031501c102807807402086060800e80c060401c1402c190614078205d6940c00640504020f048c1c2e00e5020201350380c02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 365319019 1250 365317769 365317787
    0x50a0203040f0f08190b010504091103010c170a0c0503061e0909030d0b01090e060f03100f05040b07020d1205102607060e1c060f0c1107060503040309050f01 69
    0x200500b0380c0c04695800025030160f00a04c202011800b500340c0b901d8142c649a441105041d8120001e000303281d08040c1040020802900212000c4421408120346501c081c05010403106c03454980044d0040010400c032002c031030042505060500d07101c2040340303007070300a0141c9400c0079040d56186130605803011218100a1001c0c0c0079a4098403c0e0200300084400100520017041c1c1c0708418840c15550b030006440d400080d0080c22004c20701c00300001c1290411500c84885400c0090460b00185041300c0c550080b21700c586100005e140e119400c0205008400310703056002041440100320401c0080001002c018a444001428644a0740419021140c03650b003600508070a480e00302403200011003481100340c0c4000e00e507815014a120010341640100040e400024010300030b842c2204401201403458030141100301c1f003540d52080744a100c5007140c070505040003c251074402015914400311403800009034095010044200100f1001a03071118030b2408a60003503c000c02c211854000613148015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 365320269 1250 365319019 365319029
    0xb16020d05060f0117060615090a050402031003021e01020a0b1815010806090c01021c03061a0307120207030207030b1503011a150408190201050705030a020109140d0f050a020304 78
    0x1c0b505052124858070341d204035049560010201c40c00001082e0115200e0008494059024500c440680502032200c0010414140010318a410551715a8002003c0341c2042c0c5a255414000d0042801141003680c1e04102000f00c000880000030305000000399212070428000300b58102e001d02140511040070f4110144c03030251300541e1b0f0559241403030708084107000d104880c15445000d0128a001f4001b1a2080480780181c0c0500358500c08000b444070031195162204040595404001404003502c0e11945000910020780596a0030f04030b0005019842d039550716100f031441004028002a000150401242c0e0b0041300441d49030345225000c0304400e5410211070305942800c3c1501182e0f1609002142d95150031100d40c20010b041009510142c007583c0203000321540f2072003541c060100d1358100050342c1d0b4070514280d1714000c0a50385680c1150008084400580c0d110b000c40c1c0d013080074503500d41000c00c01240c01446d54860301c3e1001424040390420f8030080c044005105030300240b00703008a902501d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 365321519 1250 365320269 365320273
    0xe030d0e031c0c12050405250e0a14220f0f0210080412020a08120c0412080702030106091112060609121506040603211707080a060f0b16020d05 63
    0x2240000c2002030400b0f204482c0006401d600c100d007007440c1a10982e80900e400034002c000c004420069680c85603800c40e2501079000b01d00100040c080c8003001610721540350305101140c8800310400d440c55a130f0018220381000d403c10210306c1000740c44c58101480e0b03950008414030401c1042c3c00d082c0c12160b020000079411610400d807881004c0d821181060103580716603441700c1080d1030100103e845006500000700056000c0200c080c0001d0080b542d20b0b00440a003005500d03150b80d81981d01070072031a840045036402c2e808a1400700f54a0203100f180300404c60b401060240c04507204c0200d0040c410303150858825941100400e0a54454030203803008500094080c1820180304218181d48104a080c0001c0e4000c4070000168181000e014410480394000c03000b90210401d155000b00b203a100c190481c00304200d407054010f41044d40399009000701c2c0c10ba141c80001d401c02918241c15a90b0b290489100701314050003c01528400104443c6104202403030132410008501c0040d40d41c820142d8054058 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 365322769 1250 365321519 365321557
    0x12030906020406170a06141201110c0d081b04050103020a180b07020418080a0c11060706141602030319060e010308091f0f08040f12050d0606030e030d0e03 68
    0x1031034101603103071a044202580485285d561412031025100706002c0c0f80e001c0700c2c403000c1a18181c140059110503201c0748200106100c807070314501c41c0c45a040170959180136400a40144001c40d00322100a4010b04d00c100145000098910b418800d8072480c42101e0416500044105210344603200d40c2c048020315420146905941e880000103c0d04800e000303a10031440e049070600a8025000c03c00d400d07941c86200e45050100454050b600f142c900700c0c0603202c5a0052400098503034a100051256511882001078019640100e000c00d8070802051040503600c3d030804004400c2d000401d0301d82c0245165000c4041c01c48124400018080503445014030340d20040010081003010800b4144900c0700b034a01c204551819140181d00c1042c1840c003501295140311f20300140740c440c110959009003c1d0800600c10541c42e9241c590031f9040802601c0080c0001c10baa0706120200c0c02080e00404241c074090100d010195181380d22807184040c2072141d036a8a490090b02d02c4410f000750b602c10300c1c03041741c0c00c03d071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 365324019 1250 365322769 365322779
    0x50604180e060c0c070605040e0609040201020f0a0803040614040b010b0901090807090605010f0912060f0b030d030b0901081203011e050316051801240e040c0c0507080d0c120309060204 81
    0x90303030000940111355004405011482c075106405a030115020203802c42e01c0740c3c50350414481038520260060381140034018901500345420419022818031944609a881c82d15040c0181141c0f800000c030000598110700313200125250074845819281c61003000c996a00703903440107a4141060798032804050040d8a400a8600d0499100208460082e2513840303005070307141c4007150068600d01a02d844d69000c2c1c000040402c7c2075030f1100341c0d11124100002086207c440000c0d02c0d1030351b0b80900c0d8000a48640100c0782c18102691094014100d41d0020f00c81c11107855188400d038001409144000c0c114000b420500c001e0385030004000303040180c1910008411305101c4489c00001e0300460b4024440d01440364140b400640f42103048504060b881c1e8110216000e40c003412484207e00d410411102c580301902c50350340d510620390703000166120540078201928050307003440d40340da001d00311540000b000f241e08160040241d1803074603840141c0038a815051a0140c000f04a1002c000d00080c1c030110f07000c11 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 365325269 1250 365324019 365324041
    0x50603161e02100614011d03240a0606030216020108100b0406120c18030602030a0608010c0903110a0303020607051c060b071406060f0609060904020d050601090e01050604180e06 78
    0x407a00c3c401581c00d101540d11400c030441c40841c2c0f450350500050358a45180602c403003a00500e808600b0080540b001c2c0360302d80700e121421104089042c810001d40300300340070325140c1c02d00c070b0100101070900382942000d245030b000711505020440080d060220207400220107640495410703025000c182c200940321030321007a005003010600600e120710103290003080c3d0300b10760040ca24a20165145400e41204a0442e03a0306000780d0000f0308201105601c1c0e020104040d0801c0c00380c3e030664021503039800082491410910410b1100f00001400741e4031950051000c2640401c2e41c0398000c1c110b0400d40e40d5806036210014420344c1e0103032102c0c1c0c0396160078404030b102e407503050050074000d0044043d042c00c001606007140c0c8401d410307540180d110700000e0b0000c038241003880143c498408000c0c01103080000040205080ea88441c4000d03580991b280208081580c0013091038002d030900d10032640c002e40c102408503d040c031075401251140120440d1203a4450031542080901120281c00da40c498204088500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 365326519 1250 365325269 365325283
    0x10031e0c0207121a2a0f0705120307020c0a1206050402030a080d06140102011b03230405071d01080601060c2d030908030901020c12030f030c040509060406050603161e02 74
    0x1069282c030700049182e01d000350210010484242c82c5c42c0c0320366116020020074507804001c403000c10705403d00883c0086401030103003402c82105556056643c0c600700f80e00a0412020b03031003441c400e4025880503c03075804003480c84440c080c0d1143d000682c2e510386000091501c1400070008140070340c0064008000d03ca590443c02c115514200c2085a607131286c00107a00780e078041c00182c1700d0780344015440b0070b41034825000341d00402e02402c0d080c00001c80e03003140100841e0040b40c041d5020351044c1020000c0113808040c003801c8140e03a59891200e54100324000f40c803030b00c4c18400e000800c040d01ca200c100740071007809484051014160142e003031505485050f00848011a0190042010700e20700040114012007140d06404c4164085d0081101880400841403aa80c0069005100c00e1000c02c0b1124103c0e4000e6000e02c008100b4507072074600c2d2004008010780c00819160150f410244100a2602c494080c3c0350809008144850402410b0404913009820729200c2e5800704107800d1408a00d5070085001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 365327769 1250 365326519 365326553
    0x506030102040b0f19030c0c020f122d0705180618040b0609061207030f1403040611010605060a09170f06190e0109050601050d060f0f02040510031e0c020712 69
    0x41145030604c3d41069044071a07e80d0300c440800c42e007194a100628205070300e010b10600c000e1106400444007100a0f151407ca8000a80128010080d8031101c1c071001004045420124006004050405000c520701c4030030b054a91350700641150224270700390741d01a404a0081c100341d4442600e46868100b86000740d100b036400f24000c0a000c030100d2240d00b0030f8103482d2882030003d0300405101d450b40d42d40c44a4520061402e84946040b2018400b0440c800e100510040c03603a640c501c1c80c03503407440c0902421280c060b0b001c51310807001084013000302d5420000030b001b154000001e00000c4aa540409400c011505694402a0054400300000349881000d1140c0c1c406151800b0080d010a0030b40305800c90b1100341c070140c180c2d4403041c0100402d1401c8000e60707020034403c0d00041903007040b0840517000c0e41d081000200d08243c0108062000d0f080c004001c0e001034480380740a014505211201c80b12440708070b408004d0707640c0c6408100c40120b000304500801015034140708014040349080035000d02d40d0345621 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 365329019 1250 365327769 365327797
    0xd0f120c170702092a0d020903010c091d100b0d090501060305012003010305030304020d02011206030317070206070c020f0d0206040909111f03020d0b060c150a020a120506030102040b0f 81
    0x1300f80b038841c43d801e082100d2003007140ca801c0040d0489103070704c08036000086c88401e41038080204031146d0b182030089000042e0341d621000038581c20200c00c205e140882c0c150300c03104c1ca912202003120100d143c544150403608184c500303030b81c2c505925201c54041c00503a20040c100750b00b007480020410a0551107451814400790345c6143c10140c08240c2c020510080c03002030030644c02403001c10050b1a20005ca0b06031144141002c1c40b00c51925018803040e207039254020b8021a0200c140d11441e030f00281200d40c1d01004520162001d850700f0300780502112601900a40101d0300100000f001d074540c1c41d0801c0b007250b002000c081e1140c2d92541610060314064a04680303800542034500d545007092800442044c202c09200c2181400c041e204030025081100c550007405d840312907080c51a142c01c401401c41c081c1120141030b01d42e4000310505041100a4290740c21240304200e450042c0337510030b0782c00003000d90b5820003151b00c3d2101c3c0000ba01a00541c1c12040000d41c0003d100c3d9209841203004200200000d14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 365330269 1250 365329019 365329021
    0x120911030f010c2102090307060f0f050a0f0e060c0102180312090603011716061205010f060e1e0a0f062307021306030b07030f0b0d0f120c17070209 65
    0x820709030b806420b504800309004d080014000324146050a8940002500060074040c04600003498018a41e00410100b14000e03104c4002c2030303200c1044038080c8180c0c00c103140f4120140100511181d0400d644208121065441c042c59607501d504072a4460401c074000d54842100880e03c02e86085c108445520038842c4009094400c076004040c0c890100c0000c00c1642983e01e0949030f08030950104140600324060306074a8501c00c640140ea0341c010b00000c1e074680e00d91161402c1064219007041e00890603043c500401004190783c000010f4040d424103441d070b917981e01e800b280803c42c3c41420210150380000c010402040100c42042c101088031202c3c3d03644400c0044d00070303e910380c61555510654607000104800e40c05820003043c0b8001c0e50004020024040f41e90f52030303485c59084261f4500380044d0b01c4100042c05104203000701c020702e0b5130881d99490440d05035510800742d001208001045000f0144000d51100e005042c00c90880380c000542010155440302c0742c21181e4040541248a906100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 365331519 1250 365330269 365330293
    0x1a030d0f02101b1206031e060b18010b0a0507020a0608091b0102101d0109030809120c0a0b040c0e0901020403030f020309030a030806030c06040306050105010e01020d120c12091103 79
    0x40102d50580300c242c22103044904100604681c2c410444134803404a54903000000300050a0002100340c8181c0108101a082030780d1800c9003c4d00c1000400c41d120715407406114910004098000e4112002c54080b10b90700d104d100d906562501910708060f61144a0100000c3d40c56000407005104410b04019512840070b00208840101000951140180e0101e05800400c00c03040d0700022500000b0000711407101e046002031b6095800c800c1c1c04900064666050110040040013083e140c0c180c0e00b1601800c000c440303100255201001c2e400607000789000800310b014030003000601c03c0a03085080501e5801c1c41d06c000f0743d40c0030390701502c0102c00242069900c0c0c803c061021040da412004010041e00c1450f0243e02e049603600405090303190b00d801030744000c0700703180c2c4c44400420046108003008181c542c03401c00050080b40065240f6415904080070340300b6020ba00101915100d0099000011100302581045803428000310340344500602c2e041440c001d0041003200d0381e2000c00c0460440d050b01c1600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 365332769 1250 365331519 365331521
    0x60109120b07090e070f021b01050304021917060f100b0306040f0204080706020f0d0302090a0b0a1b030c11190b0d11160303060902040e06041a030d0f0210 68
    0x144a0400002040c020600000d011000703201e40050141c5055180242c880143d12448001560840080340b202546401400c1c0c0610104a004510b20030340c00030020349500280461000400007441b542012000032048100e102d5044041c100d02105012480f10284d1007607a00c190960f0004010241c9400088648840e0403200301a40c422203541419615101d06100c00303000012001d007001030b000c0c000400d0a60b01045500001d0080d0781c02480a0107014a400c1d0a0820340c4112204040c010030140030161501d4000360102c0c0c1c0d0821440340d85880f581011113482d00184d8503002d840d0303040e00c02c85045c50b9011000d03a640d80e001c0c2c04034400d145500700810080009095451510b03103929202001074400030400b07030000310990440030500340302c541b5480d030300c42c0d001089113202c24980c500b002003072607414401c40300608000d0004600d40740c14038581220300000240300e0751155844600e03d4240e55030001c404400250301408588000001c01d4018081c82514190840103200d045018150340d402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 365334019 1250 365332769 365332787
    0x121b070305070f151107020a0b0a020a03140f04090605040507020c03120c19060e0609060402150c0c0406080c040f111204230c010e0301020c07140a05040f090b0601 72
    0x305440d018078000702c03503882e1940484a2501034034099040c0910008001c05401481122040855100c2c1e940c40c0520422480b9800b41d0000e1120040610101440d0350700001c4c801c100503010706048090054601e449880c6105800f144c07040c0e86804140015882e4583e040034065900c200c9080c4400d41c0c64080c226602c8080f00d0030700340d16502c45401069101c0c8024020071000021805940d010019940e210741003981001045549139038480d640340c00400d06100c510741280c801d4000e08001d0070660002100c016510542c400c1c0c5500010b5041e0141c201000001c0503003074060014480d040c2c2c0c401e05e42e51911820307001180544d083c00c5070503140700c415228110504a90f400c440f03082038060361078050340d07030340003803003110701c4050047d0004a155042d840b1001c0b1041260081407101c1c0c000380018420380e8244041406a030041c004440c1100012901c0401d480c2030505803e003621000d000204590090b51045d50098500740c40f9248816454000c41d81c094043e4040b0324594942c1e0004544d1051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 365335269 1250 365334019 365334023
    0x5030105040b03150708090703080403082a031c0f0f0b0f0d02010c0602070201030207080c01230601020312060616051c050f0d0f0f050114030c030d0504060320121b07 73
    0x9039100141085016651b41e039000010380c001ca0380d540b07803240d981c1c00403584190815280d504001c14070016841e2800c14440d0b0038620340d4404041030341c4000e00c01b03aa900400034002c455101c4806c180d000018150701a1a9035403114606100b55007240c024400280171280c9000c0c003e1044290101250804403540c81190758103035176502c10440207446a1009411012007281011380030002c5002140401c000740070b42d107909800019000110070644108000880351a8000c0da01c0e190402210341e8010041d5055200d100c0c80301401640c590000500e02e11564080b80205111585410f040c00b400046500b40c241a84119000d0445103620664040c02060f120800b010010880b40c1e8881d01c8942040301140044040401c0401e00021400d040c0d8400360030035805010f00340225240ca26003041000d2444406801a040494500c4c01c014001d214034045e80d420301d0b886041c2d440081d0404050704880700c00c403400d640e8454003584040445040103440c0d01010b100000c800c00e20002901341262379440e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 365336519 1250 365335269 365335303
    0xe07030c1121040306060b040e071418010c05060106050703020c03070b040303051c0908070b1602070501180902040f050915090103200d05061602010b0901050f12030a05030105040b03 80
    0x3240c00b007142c0c1101e00e00c8502d4845406800d0000000140541c010103000d0107494020a0712241400303103d007105030000701940100180341180000f41c1100d0021605c80190031190381c2c00c01c031510700050f1350b100c0540c01c00901a00c038803000001c0e1140e2103005040910312030360035202617420000c20980c3e506000e02a072207840c1800c0101b0800a40200d0081400707900005807200d1440654035107504542d6140420b4829400024010003003101070b11125030f0020b0905203a00c24600801402541e4803410300515043c040d200e80d40c01a85400401414000c204400c0c0a42d0350b5615101c09030302885243c0704980c060720124000c12142d03e00300120321140c1d0809081c0b40b15603880d645460b0392003800d0004040d0f00740c072144554085611214600c5000b98029001018182001c480700c0048000312584039085903d050790b0729410f03035104000141180d20031075260f60b007840c2580028006160403803003510f05200010700ba01102d600100034504a41c0116010001c54003e4010300d0b817502959102c0c1c190007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 365337769 1250 365336519 365336533
    0x818030c0603131a1509011e05060a030e0307080c010b01080c07080d020409180c06090e0c031b0a2105150d08130602010203101712220e07030c11 64
    0x100400025078083c0901440c11901c0c2d0700021340441002c0c0300151402c02c210903124400041e43c3c00c0554469004182c13805a80b040012084801307102100517025051140304002800603240340710360024a5511084c0f01038a0342c030a02490504107646c0310341241016542400001304666024280d1310740305000000415243c08950303a40d03200b10354440f0b00d040e40000d070309100c0400c400d00e441c4241d84000703100d00400001c00e00c403030411400a04056100008101404006201210021040c1600420b92126140d1251684075822150b108206288080c030030001c6043d56040c0d1340000d01d6032802c00c0c00414a02c801c00003032003032003c0d158110f441240105d9100007601032818000c0c8130701c03886405040181d090204078800d18100700d001303610100041c0c3d008014040082108500c00000740343c4007014140c0f034841c0310505c1d610351800028115584401045085070341c00c81d001e6131842045500650301c02e031740d141c6e114500e0000098800c0c000103490580c2171003d17075010b0300140352080e048200502d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 365339019 1250 365337769 365337781
    0xf0102041d01080312130303140a0228090501031505150417060402010e19090203100512010605090c070309030b010e040b0a090309050d02040e030f1b0114040f0f0c030818030c0603 79
    0x219041186c04070704269944160061403051888028040c2c100080003503510500d5a414002d4500401c08090041c0113440148661641001c904000c90b03100b820301094030916040da0403c16a80d0b584181d030411041245c031100914040002c1082d02e2900d45a2a80200210f0139140d40310b10840e4001c0c00f10701060140f10251412035086804402c0000c03990320b21a844032004070680c0c0090ba6101c1022480030340c24416032134401588440812403500820803585814005506048003900584002d0740c0003405400741885003215030301868100c040b61b106c5503510b503141e0079241c0d4110340654071042c0c0d40011a140f0011070041ca424560507507030300700d80181032000700036040c242c00c0c41c100d92003552001188221901417001d4102c40341a41c3e201929081e00b0f044411041e18030f5101c140e03044e454001000100c4080701030950301706421100c05882c00c0d45518040640c42403843e800380c031464038a4030000030001c1d03070300c020b00303051140c1942502802400c2041c150340b0400600c406600c52014400221 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 365340269 1250 365339019 365339041
    0x1080304060c0f080c0a0605150105131707031407031707020310020306060c0609060403080601020a20010509060c10060f081207060b0d080c060c04080307140f0102041d01080312 78
    0x20907500079503036140f50101703011425140012200d42210709980324808c0101200c02d40324030b055226402e0a04034038103040f0726a824400507030760084a400c51a03005a100c002d41c01040a0005075a10410700e01024081100300f03561880a440101c1d01c00b000c2020780306007840c1000039034048640c040c008081c10702411b003944029400c000c1c10f0540241040c00544401c0c0c500f000854040c01ea02400f60a06082501300203007030b10340040260303056601c03903217511001501c5c5404501c0903441500582030208807190040702c4510407004001ea0003d8080745281c517668002c2504089100400810400e0640c8c5580900d0504494481c0e55001e070480d5909940690a00b00203100481c030945000801a107000c1c006031040300490740507522420040344a40260004105068000003a021543e0625241603509d9680b072159030b4005148021030049400c5001c403c000d488105003000c4000d40d16a0b840300d41100c0303a000c0c2c401041000d01c001400000b90b40c1000f10844040c909454450407696030b500d50544 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 365341519 1250 365340269 365340293
    0x30b0106031b08041704030606080c0f10080c13061e0311180d0c0e0906060603010f120317011e05090412051b0d08040501050604110d09230d020601080304060c 70
    0x40d52011085e140da1070f802050354004c0005d10300c15040014a1801c001c0340b545010029580c1314003d1600420001555880e05550310245e0340c40d10700099a540c0301c4071400b0710350142d0408420111301006010a5030350b041003020416107042c00700d0110080e11200c04909035100c001c07254410000170043c5842ca100c8020400d10000e1024102c1d05c183c032040d588e0008083e80990240300448100002c0c002c1d1000709104141c5c01000450303000342103504181d4584840c890501c1020300c04940c1c2004401050b0158004400740341e2102c80f00f01d00c40d0313540c08040001140a201c8135a031045107480c0403940e85440720509024603000000c81c88a203446203c00d644550040e000110543d440000c0a0855002044014092803d503519480075081501c0c14a013551405802c10b4800c07800c3c40000d4085e00380000c180c9410510001d03000c00e581d03440c0d0070410701014460b84641c2258800c844914280400040c40440c120b107650300715421b5a03039074100c00340c6a01640c002e20001452042caa10080b0b0400d00090f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 365342769 1250 365341519 365341523
    0xf1815110706020607080c091305150a0906050316030809120f0f03090f040219031503020d081209070605090d171c05010609030503030604092406030b0106031b0804 72
    0x4900440c640d6a510741501948a840180d100780208488154031004030364115440d001080e080803226030000d10707650305003411b01708100d0359000001c90710011160354518031704014104031401074980181c64043c02032402246d00900c40c1c0400658102005055003040340e4200703903c82c0c00c040f52001042400805445519035500c92818005000c441c00c3c070180424203602001160740e00ca4050500650068180e800e900c01c40c41404070388801e649540d1341c101d200c5010b01d0001201400c9140b880c1c040803082d00041c0d0040e0542201e9410884001c1c028a2060381440300d019041d95109401541d030f810074000c00000800a101400481c1000102001c3c25071050300a0701a6841c181602c00303046d04a0014040488000c0c00b094100441c10312400f8051b2040b498400182400c60300c9943c0e50f440b0140c06540a2941c0d0640f40040c001c00c070071031a0710741a03040c241d1440701d00c050324000040c100340c4c001500c011050000002d1103034040d10650071109004000c503d228906410103686442c002001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 365344019 1250 365342769 365342777
    0x30209090c120c0108071b0204050c1314030105130c0e0c04090f020901030605190b1606020a0503040c050f090a0504051e0a0501291002032101060f1815 67
    0x381d040301c0d0b9071450342d81c40c1205810010b005918620000500460024041100740040e0481d42040503d40a000b8080d1a0b010b0300c4c086013684030807421201d1403044901d10b0a4840c0b65540c04540d0508218403c0903c010850090002d511030004045514403030b414024442a0f0000007088590401e400311507120500c540000d09007590f03020024151142851010740195001440704825a0580701c1c42c0301501d019100300501c8441100c1c0113103091b403a4025018485004120034040c0804101004003250340b0410654a800c04420050090780094408554400b403031003002c61241088001140161002800580c044e02c5010402e401428060815515030180781c582d010b981d48561040e401194101005141e0308900e41491421502c01c20041c4012100007210380105403419602960780703a400b00d918100140d50814244d20f948516204034546d80c0c0406403441160025041c000d040f1782c800c1c1c58003a101c4020082c00c0350140134000075200e0030541c081082c003411051403640c082950352410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 365345269 1250 365344019 365344033
    0x100c0201140c03070c1103060a0c020d020a0b0703020c120a0e090a0c05190203070506070e040c18150203120f0a0f0b031507090b040902030109150303020705010e010512150a1a0403020909 82
    0x10129041c003104482e0342704c80f59110002c044280b6030412104000640303a00c045c02a00d04142c1c0d07040301220020340303401d04050300810381c928018424441000d900c1e032080051a42c1d0140b40801402194860400e184107245440004100307070101d0150070361b5200d5a5858524000415040d02300070303c0380382c2d039030811480144a1000043e204019a40c01130440f82c507140481800c00c1e04010964041000b00c108001202e1000886120080e81030350945001d002540781071620070300200d00d940208080d940c00c10403440140170040600200141c0030303601c43d01c402e00c02005d1150009003511009440749801d607015400503442405104040c50700b0062615021010b03e640c6e00d84e00e005a00b250308a11400e40e4000010401031a00d441019454000410f0460700e592075610003075120880c51150906000c00214240700036803007002142c9580ea00c4114020260600d40445604015038070741c02c41c082c0d0030148001c00c00c00c00090032102050254130b202440c02c2c1c1580c0c2071113211400688642d0283c82414 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 365346519 1250 365345269 365345303
    0x10c1d010302131205101104081903031407030218010504060e09061c240506130908040f080f0c09060d020d15051617060907110f100c0201140c03070c 66
    0x1c01300c4443e0303005000618a145022900500f100c2c03200f181d1408010080004101d012070125100700750001c0842c5081c0545264141074001e00b001ca0842d40411010350104039285416501604840d13000300340d8507110700d50f07040064500744181e000d43d1010030301941c100f0100b4900303240c000341d0080380540020202040c165411260660102040b0741040032114542044c20790701600c440c0d06400000207000750305080d4003084151580166009410741c440e2445d400340f00d902400c8030001c0640c3c074030501840e50740e00030282d01ca003403c1000c0f020500400f8003040c41c0b40740c8420751500929004040d100c204807254208804008800d108985405203483d0340407160740c0701e00c51107102d020110101d01009440408c010100c81d4100e00c21420440300070203104454855200c031550021941c14074a41c0c240040c0c1c215442c0640d010541c0d14184201c0b45510415402c41d000381400c414581c009100480030000f0301481c0b40001c031203c4046800a20015040a00c0782c40d980340418000c0d0028440030300780c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 365347769 1250 365346519 365346539
    0x12120a0f15060c060f050402010e0d03031b0e0108160f03020a09030507030303141303050708031e181e0a020f01230702010f03090c0312051201090e010c1d01030213 72
    0x2075400040800c0343d401c154410311035a402103882d50250150300b004649840d80c0081c1c1440300d18401c083c001c1840740003103010940254007d0740e10f002444d03125001e210310410001c0408900344111800125500e01080d00d114110001b0340203620503403203e131a01d803e0880d044000750410311002003008401c200001c0415414800b00e0040d5000c0d55000c030b14a2040d076a51040508003500f1281c40320145207440740407039031180699000b247c2c8600090780c1ca0716510000c040b007103001c0c1c3e80c0f00d045c145030000780243c42001c202e50a07c2c040702c41080d00c0a44034841d480030580c48925650b0440c0750041070800f0014a0443c86800340b2010506106101c401500e02c4948004942400c1207040b28000070300034199078001d6550130320460186020b0201c107005664590b00307000e140c4401000c03044030f01c4100407803034081d06c184d07003042542c0e03000c0120030f60355035a10101514006003055820b51030070420b08a61442031080401d407181082040c8a070301c2c0a040110000e52103c241291038256204000c1800004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 365349019 1250 365347769 365347811
    0xf130f110c0d09060f08060a0815040203010b0307082d03070c0501020105060f06070f05010b0303121501050703080403050c0102210a0f0e0c0f031203090a0512120a0f 73
    0x3660a5a44800300006014a4250b54410303240a100c41403000b04410350707200503c0c01485a00303203070440b029203903007001c202a030b8515000080540514491026101a0000301501c0745008030000d1107900154000d00d91a140c140c019a178a6070011840321300c52034460f00080a110100980c0e0820062509034914256080040c0499030344101180421080d0b909000b016044181107560b0480100ba103000134055200f04c410007800020312001100a002d02940013442141d0082c0c10b686d591000f69140c854010320485594403070003000d150079900b6521a01c10783d454642d240d2a000c10b1921161010342d044d4002070714000ca15902046195032849640100071ba100d40c1071001c4d07851900300114180c0581c1c240101010b0307210300e00615100302d0710300010380440c2c60b0420784182e40a03038210780200342009141c200d441c649150000c2441007020002401c2c8103507600600c11741d0041042e43c44c0700c02e1305204450705080142c1d104804030b66911441c1d442015804140c0000194101468100c2c00400c4d403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 365350269 1250 365349019 365349041
    0xf0a0b03033f1608010b04061b0c060e0a0e01060e0909071203031d0604020a050f04090b090c120c0603070f0e0a0314070b120408070201050f030c04140f0f130f 70
    0x82e803042c0000303841c4044a50f0380b64075190404084035030400c0c1c0200340310f0140c0d200b03140070040e01946000402180401d61a5072a4018055181691f02c641c0e001d403010b1079107041c05000c1d0412002c0040c0114103102d003141030f1034155036804050440c0340d007002071800c4040c0000c0858051800c00285d0180101d0890488901c03e40380880ea4051820417404540000d130041e44c001c2d000b03142000016510748400300181c42d0110341c4002004603060100340100110b48005040389601000c0c800043c400150f079091802007124851010b05000300c43c1500d40c1c01085101340c2010003407000c00c1400703004030368005001d28149028072001e803e10000880f1803642c2e034403d075803900c0c200394482803a00303003480040040d00b4111103251608140751040c0e148080018009042241c012540c00304684c8500c040380c1f074955034280565164100125060305a070f1144c07140d1001c40750704c106001d04900380394200150303e8000414008118428009001032000c000701c0c010307003070f80d5150000040c1074014401d440280c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 365351519 1250 365350269 365350387
    0xe0f010603120801120203120c0309090a020d0b0a06090e0c07230f03040308030411240903010c0e0306040b06190303080405060106110d05160803010b030f0a0b0303 72
    0x400c2c002d4042c00b4010306030010500d070b654502091000d03850004988903080b810404055648018140ca43d0031801582c1d410f590100d03282c420302906441c907401a201003108403000f00300c801180010011026510300c609008103030a100700f0801d02c032117aa182ea5101ca071040f541c505c3e20076156100c45140c56241c05454490891320390070b24150b0420410780c3c0c1c0c0020310000075442c080c150f443c0c010150000900083c60600c103c4041c002603100c3c8002003084440d0030031003888a005400092480340c02c03003044076000e50b1074620450341c8640700380007801d00042d001d0301811941c2c607940c4440410344002843d080e00803c4001c3c0b403103201404510303c9402036000c0d55640c807007804c043c640b60b42448010b034040c00130481001200c0c041c118001c1351540e0b6110300c504040756a04020405207080012510000c2c0c10303190088000500c1c803040c0d00040d44a023100300b101d42c140c3e584080c0f00c1c0080750302240c0d880380c155005000c0290848003510403100d00170650034051101500d0204009071704045904200004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 365352769 1250 365351519 365351543
    0x10e130911030c030307020f0a03050d0801090f05190c141306031805030412050c0301110a020c0a06021c09050d12020d050304050c0d022710060810090e0f010603 71
    0x20100341c000c00c02400c0030481c0a44005000c3ea00065603c1c0102d40700079125000e005c0104100399a0b104401000310b60000c192800d5002c40c0001038210402441146100d40c108282c4012103a0309118061244c010b24407941040d890209801001b0700f00d40c80a80c0900108085440c02c1c43c0e03040002d81101d0f200301b401c4c541d1040c1007000c000e0907a03c0b4920103080380350788d12303200000182000c025102901d521140520310b180781c9040c180d14158660b01c0c0300d500355180002140c880310600f0020014103103140c0844450311610402d2200600c034501c52400103800c07800171012a402442c4040d0b0727004038585071112030786440384009603052800b0003048039a40814201c1981654041c085c0c0110141e280c10443c2c1145001c1d21103079110001c0c1c0c1c540502c2880e4240d074480441d50b480c0c80940d03603103401400c440e42d8080d0803e2104e071031400aa5003486425516840050168131a007409480b07240002c2d6590705852600044001070140701e4050700c014080c0700500c0117040824460400114040c800341500303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 365354019 1250 365352769 365352773
    0x30c020316080c070501030b0603040b04050a0f030509090609090715030908040b130e010b09100311030a050613020c120f09180709090b420d0c030203010e0411010e1309 74
    0x44c0861540c03006050505040e4549600d55801d019290b1094010190000c1d90782c891900c18100049414020b10000040c1c0c6001300349640308000d40380c11001a54185007646424003000f0306110101c450501c51b42c00f013802030000e40080c3c090b4481c9041d01c0c1c140419142f00b2980c4000c066042604104140c440c0460b440d210031000d15580e03030007481c0c03c0802c0c5a00f0350400442915503c5444c02c1d00e4002c046800841c0c0e00f03644170303500920f5901880d00c0c0c01500c0f820300c10240e402a02c0180c40c0c00740705610980c01d44424081600c203c40121600c24000c000701c951310003a403581d6801854030308800c01400d0203882e015072100705140e2481c081414520700a440e0044024003509240d030044002d2602d04042030304d841d100e45070f150b100c40c25040d06000f502c8515180103a80c8101e0f002c1e0452200f0f08030545080f51305180b03400780c402c03103182041c240010015104210105e000900c21202046000700104d00468a940103c1042c0c90041c94088131481d4a02c0100c4c00038402c031140c6001d19999902d4601c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 365355269 1250 365354019 365354023
    0x608120c01150506071704050d0614060303180f0f0d0503030a0608030f03040201031a1c03022401150507061103060f190603020c07030c0801020a09090b010807030c020316080c 77
    0x400ca0400c20055907400c00021a00c40e00070210020900b1000250f51b42e800c910f84010342d0001c2c80003d10500c281b411520b0210090070b00d4900311600c114010b000700c4c80c5454044156668800d8000500f491310725101c0402500c0c0701c05c106403c1d00310b502a4019090303910381541148031140214000e690b641400380c00c030030845455521680131a002884000b288528000459410170f409190105020a4000c820b816100d00814019480740c21b06248a1100181a1400300554040d0b025141011545486170340d82445240811004c80c00ca0001400104203c4000650b002c2c0740e494642c3c10844a984c403602203440c0d26506240582002c000c10a1501d40300c204ca00b00e030b40054074021034121581c00404030310b8a40b8012001810b03008070700c90610b58001c1200b08019600010020396440c0c2d10300e642030003075210407126400680d00341c2010800b500180a8020410741c10f940d0000300e590383d90760450040000041050840c001041040e0828a00380083c501007401181980d0383c1d03e48140b0074034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 365356519 1250 365355269 365355281
    0x90501020d0f050a1d0301090b0a14061f140309070f060f0e01120906110301060905060c07050108130506070207050301061a03010b0702012f07090203060f130608120c01 74
    0x208102c2c82c0941c05003600c2e03124003500d00c5110356090036019400306480c80c0b0900e1040c424426010340c0381c00104024000c04210850059000b40010448a0b4408034210140d00080300e0054000344918440100c0d110600d42d41c1c0000f00303c0d881c01c1142e00d8000403c00509520540d0224520390059074180301c2c0200c0c01c800f01c0f0050056040815060071000c001910210303813090030398107014401c40d230468030203490f802c9049070346d40c400b5080101000e082c0140b0001d070003c0c0140b0b40090078a100100316410180101c0d000c44008100800c0380c585480c004440201e00148120000e00545040f031001605c00c2100a001d042c5640160680c141080e089c10f007110401d07801800c8111014506031540d44240040340d041d55141d038205a612803107400140c440c14084248120300340394a040a05c10580c0a0140002908080702a10b004550301c0c8601d4044c0d000644016030301456203201d18206250102402c844441868808142a81da0788022414008000b050401c1a00c0c00540160300c0d400a100d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 365357769 1250 365356519 365356543
    0x1030c030b0f041e06082d03160c03020a0e04020f0604050d11030312070f170717040203160b070605010807141012061211090712020f040e0709050102 66
    0x20000c421010002644103890b0078003042c0125a1802165034050f000c403600164030440c6201880402e0342d560b983c2c2d80d28607801c401c00d0a01e401341a506411090700c0450161103c0c141c40c010b6003061100b080d030180d9041180d00031112340902020010044c1c840f00050401070120965284c1d85280c01d0052000641500c00c4040c0303e03540411052069a807010b000728809500813440f00b00790041c01000c0b074070394030540c0049203851148100300650343d035005c501c1014a040c503980300040344540340421041c0200c2580c0e158045104940c503041030312045107403954480d00081c1151540200001e04c640d901259400c6101d00c0c580001d0075805112035402120f004015807001040081d18116100020002240d90f051003602c0e0521007011032440b0b214816901108200100701c42555004080c0c689007140c00f0880700c0170501c030300c60460b40c40c0110181c3c2c0b2500782907e54191200c02941c1c3da000a40c40300c2c480381545070091001044240305c4c4400d081c428041d07a00e820000a0a141c0003903d49101d403070007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 365359019 1250 365357769 365357771
    0x61d0a0f1404090b01060f0509130e0d0c03050a081e010e220c06270e0a06140a0b0a0c150905070f15051b0a0302070e070e01020312040503041205030901030c03 70
    0x28200240350304c0d00490440d24180303005040b0040b01e850443e502d1080d010140c2d40440d07000042807010901d81c3c09070700002010802c0b1200c0004c0f11000f5612044001e50141c0850340512001005074022803140f64003204201e855007d0998401381e14840700000e820413207544a094082001d544100b151181d9904042c14042d2000d90155890003110000e038001c0350100013400c81010000f0408655400715404102023011195440d40741d0a80c01d503100701c07056000b0a0074a40002100c0c50003121340d442640021705204105406c00807645400d900c40102c8008003d8410354040201303e001c1d442403c1d01d001c180d0082842102d07030800a103003030302680012071445466401000b1840b40340c82e1400d05000b050808540352412180305001e608102c4000042038091145814101980443c81d6021790b120803c013100700d51140d8a0498150094850b0f0b2409a4010000c00324059411801950300c0ba202d00222840c1944034281c07c4620500120308540550020130381c4012503030140600b440880c01da01e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 365360269 1250 365359019 365359031
    0xa05010906140f130e060705091e010c020904150e2407021b04091a040309060908030409151205070e01080619020304060b030105190605030d0207061d0a0f1404 70
    0x400203c1031101002064411380c4031510241030001d00b60850f4180a605900f0386850385825003028101e5441200c4280c49211450a04004800e6003001c046100700180d5988100d02d8080d800e0102c44000588203860b8200c1031800e4400000b030740c0c0551102c19550f040500009004655500c45100e4031400056074104484100010b0f00e60000300034011b6021082c0ea1140e0790352600c0130400500c401400a058010115084281d081180f2031881c020740c401e9840164403552003030308440c140d0303290188200700d810810040011341041e402821000c440307004e00201403980c40402c2901105203001c200d5951700405000c1001001c01141795005019440183c585480e0170441a12080652300ca0750300040e0340440490280000c1c4d50040d0080c60b005002009141001112181501d00035110300e0b140741c0c201b8202098900303000c03690358280d01c0340d50014204541031010a5451079040d000344408260400da1048407562000045002401c1801070390201505006680302030051400d40640204c3c1408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 365361519 1250 365360269 365360309
    0x11101090b060d11100e011b08030105040b061909030318060818010f06060918020c1203040302120406050d0e010209010c110406120627030c02090414060a05010906 72
    0x240e2a9988220100c94003c5250032a280440c424004680c1003074021440c0440c050a4940150440e042c0c80c0d001d803a805004545a2210b01e0950148000189229820300041000341429000168001c400a1040342480301d4407501403800090003140000242c041c00040090607000b001e0751950290503642e01c240c4509100e000b402c0403002415990000400e8074001c25610360a504c132034802c40142c001032118903540d100080c8281c815001d0300340c010310500c20000c0142101e100311102c544011000d000c2d06c00340051109940d800051090741036010f024808058186540c006102404c480e03101d450304c503c1080c00c1801124800700c0110301d985e10400921180782c2c4c1010744c00d0441d5600810b65070300d8115002c0490f002e44103d51002e04031441c0f011203c0f04012041e001940c0540e4143d015022001d103c5c0443c1c00c00c002d0503003000e408100208100380241c101500c455030b016002e030b00d105000c038a64030106443c1110031104000c44903510320060101052074010745008004a85034443c10032488 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 365362769 1250 365361519 365361533
    0x1603081f0e0a0e060a060302011b1509050f030d021201091e0e07080a030e09090a0201080129030c0306091018020904060302030a050703050601091512020120010b01110109 75
    0x1030007218660380d00d500c0040c00010407070b0003244104001c3d10684001c0d04010b000e0201414080c00300303d02082c1d841c2d041c1c0c000b428104000140c1d0716040800c0ca50748189450a4400030040380c94240c49a00030304003808000441000248004070110000594400c001e8074450780c1000103800800b007a904000458079004021500c07035880b98158200020110541e540107440d080131a4002c100c2806020688024950420108101c921040d43c5904880e03450700c03880da032106070a40c2d000707000c100c00000522240c06c1c112581c07420240040d810320b00800100803503041e143c00450344d84411202c00402c101c105d044c07951441d504081c425804a401a09211290000360652001599442e0740030030020040e0b62150014030013940c004e801d4400c0603146051042e1500114082603902e4440c80d000020f4182ca60f100d0710007a0540c20075281c00e41030500d050b244880365090400d904001c1414081c0b001c842d400030000c0d608000c80000020314a07182d500140030036210381ea5101c040d03417410b2481c002090003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 365364019 1250 365362769 365362831
    0x6040317100311040f15060212040b1603110703080304020f03010b1c020a0317030f07050c0703140a0218160c0203070909020109080d050406030612020f0402130b160308 74
    0x300c205000808821600820000c0005917000a9241d0425502c502c0e824074074100b501c207aa4081c0d00ba11010303d43c003411181c02e0f1003588220001e0303590400c20175428107520754603480c0c1310784607181111006203110580c2c0d20303003001600143c8801400005100451902d501020f603004821b4000340122003070440020400d14a24507482d103014000c040c480c045507610b503641d8010f50342c8801c14004a5410403403840054000f25030360301200c840304000c5000c59001e0070581d00031050000007420b030f1504503a40c51a0132030316030f82681543c0c03069804c40c00040e510042d4814500d401241041c480b440e0201c400700c0b03450b0103040003c0911101c03060a90260310003003108415115845000b2a0020061004031800501c03544065064080c501c1480d002642c404010000c0756040c6d50140101c5480d1010f000e00c0001112000394041401203c09006083ca500a8400b5081c0c01900c04485507503104404d00301e5100c014039110b40b103c2e40d4241b804254100281b50340200301c541c19640030400003444841c490030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 365365269 1250 365364019 365364023
    0x2408100b09030a0b090c030105130b06040f0b0d120e060f0304020913080a020a020306060a0810110409020a02060912160602070602090d03081006020f12030901090b0108060403171003 80
    0x60018055407a502d0400c0744444566015a5585840c07400894503600d80702d0701c4490900c0b03942410041140a0b001c0300c0c42810064001203010900d0300c03100100310041103142a0092016100c18040c2e80d142e6821151840403405400c5a801061000d040142070190100403544203d20070f11903181c020a40340c007948c0d80b2541c141ea08200548030b07564030040c2d400c07440c4001013400c0000140c6040c603aa0100380b1200040c4250304540c0f50742c443d1410010090aa8060000d82d94800301010140c2c142c40d400200c003802d0816003035480e2944400105059034061b210120160b4000300c28484031982c1001503a0b50748000c0c544050074400c4400c9040c00d65001340e031000d03103600e0f004a00201400360580c115110100c0092030082c2a28180ca0090f10244044541c610040c02d1190001885400030880001d1040c3c81c3d800fa008030b5960f00c418101c141c00c0035118180359035031901d040000400b50205070b8080c00703803a8000d003200d1500c1c1c0b40003800100204400404c40c40000c050010482517502c405094030b0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 365366519 1250 365365269 365365289
    0x71e03030c02030114010b0403050111040b0f18100f08060402210c16060903080a0b030309040e100c020c09010b0a0903020121050f0a0b0406030b0f041407240810 71
    0x20420b0000a0240c49804400910348202a0002a440f103104008100f281d04c10170083c050744105404505080c0264407801e1504d90b4200301d02000000300ec00140600c032402d900c080c480c4203240c00411484440032401c400891044214900d005070420400c6901c00c008880540ca8034042d52404d07888020f180354903004030700350603001c5207080309100103949401038400030002d410241410b050700500134040f425070114a00b540442c804100ca40100f042d00040540214586903000090000804190900800c0380c00f43c01c0f00d5240401990003907013408081c5a008201c1c000704c100410614100691042c1000310f001c100342081550402e500c0c00c1142d070242407002e041d000403848607070341500300403404007000e2400d001c000c0a1081d100640740189103d800c10170203032280d01c080c4800c80b48540406404151840c001403c044040c1d1507642d4050f00c40c0400356640d90060f41102d140c8078042d04a94408400034443c3c980c02000e11145086528083ca044065801c1036910400500e0060160f800c1003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 365367769 1250 365366519 365366537
    0x909010f050c0306010329062a0c040f0c0c0b060103020409090503040503070b03011503051003060c1206120b1501050f0c010c14070809040b3601050303030403080a050601030902090414071e0303 85
    0x19018080030001e8020040c021927890700080d600c1c031501c5901c1c034100035115601e080744500c404603140c804c6207480ca90315100c5d40d00100c3c1c0c507250300c814460000c007d02d040680800c004205441c80740907258a5038412001140c0b9681070004050400080b9008100c1802c4140010040c15084d134850158030700c40c0f4140000c043e103900fa660010720078203820150145040c20286e000c003940c0400b82d11760684c900002001441d80b80c0312410003100794103c2c040e1074921184003040c9502c008003c015441d400c141880e40c03a040740d06121000b40d0308003142a02d82c5943d01c1450046550704505030b1210250135a060903e80042aa01d4210502440c0b04445c0925528a1481b2240d1141c87c0041d0301800e1020b104400710024044134580d21425017907000310b81c551000001983c1c280042541c3c065076064541441396600c140c0c2043c0240f90060201d8100750b01c8a410390f003d600c40315070040c01a40150800e070341401101d00b0040c54003015a202049400402480c9403e1402c0f400350f50090f280c2c540340801c52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 365369019 1250 365367769 365367787
    0x2070204230f010b0a0906081504051314030901120e0a1401061403070605030c0a03090804090603031b2a090203090115060f09050909010f050c030601032906 69
    0x80c10820030075829000c00040003007a924844890620514011500101c5603884181c0d42c03549001e0074036601c01190b0044000d2040f24019a02c0315442040307441c0c0074104000b4a4006402c0d100c1c25140c1102000c8807540320414881001e01d1001c83c1d400d400000d6192041c5000003d1a84854603c5a4001903540980c6102c0317100500c40c0e041c4071604018005290140030003014002d065a109130280400340e800c014080d8200440e03000c0444906882e45800c507501e8401104465101092020170980e56030840380014000b803000d40b01501c3c50100015901d402c5140203802080c08a0b42c011100381058055800554080b01040c402040303400d808a41c0d56221500c1c2c86415155000000d0031400401080280c500c15803000c201342d103003107140300c54040e61000143c4400305102903074800600403550a0029080c0002400d40086001d000090700100900341c4071f080b52001e40c0d40072001900041400b17003540c1e140c0034007030a41600208800c0c0d4a40e04802d6140e10b140c241e4402c0e401201c01141d9891 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 365370269 1250 365369019 365369021
    0x1407031e140105090607021b0a17100c05070209060103050906010b2b0c02070608041e020607080d14091609050c120403050a0201150e07030b0f0a0909020a090504021302070204 77
    0x1008880d1000030f00c6181451440c950721550b00721045401441481c03440c98034120418001034202c0d00c054505103915003004041070038a0030b00504a03c15218160030814902d07a2407181c0d8000ea5070640c0c0d9552907840510400024a0020b811a8105820681444840701c0c000c5070090440b00b0200b00f2070b80d1010a0314250302d02e4500040119030001002c10303903c8100b142c1e5040f80f80360054030b6003501d52064440e001924000c80030b80e406491044440340d490f0540c64020425102030340011700203803c2c901c03e82d94801781c59000c1812002c055450ba10315400d0120300c829056005040325001d00326140091590030301c030344c0180c400c0446080d102e00106100c00d44150071200c8658080e02403132001d2405007005007540d4001119080150f10b0f1080300c0c0c0100c040c1d02c0035401590528145c1d1030701074545034421405030504000c255808049003180c0c00a03a503400405030010080e901c0080342d12204d17401000400109a4421864641001d04020060b030300d0600e108651010400b0051300c0f0304507800414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 365371519 1250 365370269 365370293
    0x7050a12091113140903071e050a0c060e032808131220040b090721020c070602100209101d0603270703050c15090402161407031e 57
    0x383c2102c82c4444060080000d41c011031110b260840e0240920340ba460000c9540f4030542001501480d000040d0740154102d20749001c030b1305405101240c04c0721416440314400300c0c00350760020010803503103654041c090170240130b0501c40740d0441c170485021038a809040800d120403050001c201c0d400c000741d1002040f205401c2840900112000101384104601d450b40e100c0c078002594503180c0308100e02090452910f40a003a00c05640903000680c87d898050055950800c0c030f61a140309402c441c4d0851074000c01510107009a0000b01c0c0040c03400034940003000e0b003052011a424081c1c18010000c0c07811903100c0100010100d00f01e894440245800b010340c8080340d400c0010314651250b400801c4c440d0008078002c1c0442c41300805154441034403803500c0f40c56500c00306880300420f20303000322000300410f190079540640583e6803208440c0c0b80071140d00004049a0066162041c050081c042c04c2c820710441c50105a1a200840020120b017421500c0355030520202c40310390205c2c184891804c0c4200020b5603591 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 365372769 1250 365371519 365371553
    0x320010212070c0e0a15140105090d111302120f070207090c03050f0915041502090a031407060504060206011e0305011d06071704140a0b0705030108010507050a1209 72
    0x40d07403110b400386400b4110b500140308028103010b24102041055010744104c032591009060b0364043c452130122800302c00b0b18000f60781414031500b031005071807075260030f070f06500030903c02c0c000c4c405000c0300032007000f0600e058066101c41d41403060144014010000055681002d00702da0f00618a40c1c0740c407030407460300040b6040100c000d802c1c102c0b00a081138040d04010301408151400e003200355500c600c0702da84c82c9000000110030b16401030100d80420120810f03100f6079140b084000d443c12142a020926082c0d0981c0308070b441d0b03484949070700c11241040c40040007404061600314030305844c00a00a58695060094141003c513049840c0785502c2a00d9041008650060080c009030102c0401c561040c01000d61a400c940581400a00341038419000c0c045984500b402c2d000761610742c0d45591301258034020105140d8442c000b401000705480d6202c25119a14964a50366658100b000b0276003910380160288041c085e040c80402000b41c4c00c2040b808a540008600050036a600d051a0940c040c0707000b09 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 365374019 1250 365372769 365372803
    0x109090b01290c070f050103020a0203090118090c0c02040f151512050702031c0c02100e01060305031b0d2105070e0a120c0e04020f0d0c05060f07061503200102 70
    0x660030f558100424072508858510380c03a8124036984200540030b921881895500503007040284441c40c1d8003d540c82c100d445c902074450082981c540b450f801c2240d0b410121280032480003000311046281601071203c2c120b1400b402880104807000d12500104168002e0641d54602114460316152040404820400c2d09000502090604850194595110b205d80300e0a91070305030030610048185000c2c68400d540b4941c014620556440d080d00003c000400d018092035494a0000012410030006041210071504602400c450b030041c0ba240740075212405d01050002a1900d11488c8501c10402a51054a00800305d19a40c404e60106e4030607480c4120383d0351000c511342012039050408100000e80798864109020701517181c00c1040700b440422640254468002021075800e070070f04d4005601d8251042c05140e01041c0c603540018141c0d0001004a41c10407008a490420f1003071500504164070f821074220800c40b130843c2c07141c80001c4680807000f01c040740c0440c2c4e50209a4406c00012200300d00c4400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 365375269 1250 365374019 365374027
    0x5030601032a0f03020f0405090303150a0b211605090f0f090c030601021011160c090f0207120804051002032707030606080d1d0d0b15090109090b0129 66
    0xd414010324443c2d010030707801181c000c2801003060a00707210f02401500b180008604607926403504084c02c42d8080d60103a0070048107400010142e40007030141103200005002220902c0074201407a600d5080100400304030040c486061091613003040480740e40c214260303000182d603280c1c80c02051407a0304e0491600e03041a1840f0400c5401844100694081c010903803e49611003400f80d10141515183c20f03825103480010030054081d84596150700031040c0c4a10960400da581e640503a9048418080300e22000303640020300f101c2084442c01d40c0d0703440c1d80c006041c030484506164482647c2c0300ca1400400d0062035001010610100c103008000b980441c0c030010a0201076084101241c0300c0003280300840740300781413281c00308810703601050754a4400525501c0780c111880c4901c2c0340c500c030b80442d075015801481c0c003110745011034803c602507072040402420110620600c0c0083c0720310701350140e0104904a14107482003000400c900000350444585600603a0750310484050555200d0040c00d1085190300001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 365376519 1250 365375269 365375279
    0xc0405031902012c0d030c0b090703061103070f11070f0305010906200304080310120f110906010c0f0c0b1207090605040501140a030608030f1c0605030601032a 70
    0x40c03025841c4034401e0360307041480e4043d11103c8400030512403d81c903041000002410840c1003c40070314000d14005d140c04140d4081a848100341511705a0302080c09810414041c014044140690042d103200964130300d01e1883e001500030180c40c042c9080004000c1e420f0303000e4461500c20040c1d1800b5000303480e0b07052200707592854464001d001550742240d055082800d0340341c9914605d00c1c00c81100300002e266525581da40d984008880d80014060380a02c580b5050100d5580c2e201d60040c0382c0340b44100401c1c4c82c03248031424000900005085070901c03821111040102590b40080d50b01c2c40030740d01010102102c840c034a44000740c504250481d0300060b0b0049600a21060860201802070400d502c0700314009494000840e440d10540c020741c1c0c0400c0e5001c1c44184181000c400a0903030034558600003940340d4941010700d040d0390280d10318940c00c42c40480c0c2c10018190151510500c00000f110404c0440e00c0c00f00820b0301d52a05104c0900380304417200309a24400180900f50042081c480100c94006840d8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 365377769 1250 365376519 365376553
    0x3010801060e0603031317150f0106030e0115060318020303030703020714010e0d0507050a0209010f080f0c0d0602090a030c0e0414030a1e1206140f010c0f0b0c040503 73
    0x1c0c42601c100340e81d40b0020030300c03504003c805c9410540c00d0760040b42a29040600310019450880c1b0310030603512400c50305031444280702800d00d0194907000d41000080d40341000041c156007604c40241c5090349080b0b06c061581116403020385c101c0c0d41c141000b01d1440604030250200103140c00c4082d406020000c2000002540f550090041354819218001c606500c4144c0c42d0898981c800341c04142c5e8005080c1100041c018800340c008030780714108407120740a81d035012030391500003a48103003440a10751209101915060041d080a41c2c84c1c1c0000f40780e030f540144001900c1120f140300240400e6030024882c401038130340401d4071028541000342d11084950f550810441d00c08120350603103030045902c00c902100b000110840310011165690f600d1130a1401c07143c3c0451403c001c0d030030418410a01071003001d0140e036000d200010704c0d02d05c840303160a16104081c056802c0c00912100c0c100480a03a00400241090742000c00304c541000d1498083c0c5d42d4911041468462604070a5143c410440031101603551 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 365379019 1250 365377769 365377781
    0xc0703020f060903091306180506130b0d080a090f030507050a0b0403021e010908102c0303010902030a09060e060601030605010e060406050d0f15080f03070308060d0c03020603010801 80
    0x82a821645056000c1d030318661141c100742c0f625499504100700b601c4181c42c20880c01503c3c260b01072000513030a1307541d14000700f62032080701c01618a02e80350b408101d2245051001030f12662041c401c240010056034000a182ca00c0c0790000404136100031415103002c51007440000701a010440a00804507140c4c18401d42d00c8000c0d00c515803207078204040200b00b445441040d1402c81c4d9000c2d001d20340d807521000e072100c0724442500d40d140c100900300e0030000340703142d04200700c81b0b106070f000c200000d02840034503650b4080c00d10610315140c0c000a4520030080003200104503030450740c41c09070061312600c070590440003406941801915041c01c02d007884040650100d200c2e0300900742603d04204842d42c80d00103444a209002000d68000c00078003040100f40d0040000b00101250203000045102e280c080364021910304441c007440c884900708003445850410010f1009410600d8011420002c8595008010840c000d0600d40211107040301d10702004807030300406000c1d5500501182d12984c54234000350082c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 365380269 1250 365379019 365379023
    0x30901090b040812011a0406030903121104090e0d02120705010e030a09081009030f03020d0f11070b010e04110d150e010e0c010513270f05060f0f03060f06060708030c07 74
    0x141e610000100081c0c0390711400380e0030f66420b06e0141410f00d0008140c00030241d17030302c003981402040403050100038040c0c030402c804000c01c002d2442c4c5a40c00d010a68044981010207004280e01c6218000fa140e9000592080184d404048071551003001c0e107401b50151088200703035101c920020070081501030b00700403244140c81c510000c480301160a210f02c1825035500401c00740c0843c1c092041000114440d40081c0311581c0e60040200341c0000706454013003100c02500c24190a031502013a54010060000f81050052026820070415401c0ca502d55100a9078964051441112031410080c00c010003204400409070110800300b04804800a085000c0c24011503e0481801303584101045903002d1401c2d1b6543c0c001600700305210f91b007000540c1240d810848a00300200c1c600c0482011148240c0c0a10181921103003c04651428200c040c8820080081d61180c441c0c001c01140c00419203000801542c0312700704519100e81034681030046800e51203001409010705e43d0000400c04100198002802e45e14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 365381519 1250 365380269 365380297
    0x415020304051c020109120531031202370506190b10120507030b0d06020901030b0406081911060403030c02031e0706050306061213060e0610050402030901090b0408 72
    0x100440c004a0032500701b44c00091280714805440082c1d984078030007500f000460b00303444c030f5116461030310706400700020228960b0389201000e5081c4100b00d11064010003201c100d000400c100840314181507150035503034a6101390b01b1142c00c5102c000000407600001d006400c0010340342a8100600d076541107012003400c024001d41807001c40e002a04000581c005d202c0c02950ba115180c1202d8022040640380c09010001015114554260199141110003503800d01c515001a03640440e40009070a50705030251203445a40350490820a0707010106013803801020082a03513070146003130b10f031202120340600402c0d42c0003603001c1004804c05030810603040c2d12500840c2260f030320b560440d10028a0440761600d82180340c0085a003000007502a6001d981c01400050a071424000c68480d8445415400c072005d20810030181840d0091141d1446188040216040549031300e10b003855550040b0011446900e010740d60010000340100b8003075106540c0c49074800030030011400e080c1004425038000f80c140c02030007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 365382769 1250 365381519 365381563
    0x414030c03030a05070305091f020d090906030f0210021e0f0601050409020102071e0312030c030e1b0118030b0106030b180f0606160c0803180a03050601050405041502030405 76
    0x103480d00100b91620a00f2503540c1c0745c58417000f50742c00c880310b8003d062083d800420008803d0340f2003107200000940480b40742d00620a0600c0b860300141010010b80c000352207a4a0090240003242e41c41d68452991501034450345c2d00364440282c200d00d41010000354a607002031074006205514001304200d51120107580c2220016600e410801c01101c03501d54000b40583d0100c071003000550900003150743c0ca0b400a4155003030641da01d455010080e0386600c54280029600c41c2c1c055043e0703170507100740000040030030010300107428081a03040000705081e03149410312040c1128541500b58081c49540507550000c0900003d580d40c80c0082e015004500c24188551031181d05030015510390316200d8401e4502c038640d09065250035060000641c001689881c594001d0340a420101c1c00321030051008000c0000190fa4640307001040d408040e82d215503003486064184020004240000740440c19a00d007254000ba003070300c03185821160401d140c405c1c54541c90000c41000244800030660465811050301c42d03682c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 365384019 1250 365382769 365382793
    0x507110a1506140a031e0506040605250f0305061315090c0516060507030b041d070b2106040e070902030406050f13060b010e03010e0309041b021207020303040506041403 74
    0x2103000c03070783e81d0903000902c8003000c1001c982031850051a9030032071141c041c1101c81903201c3d6030901c502140c041c0c88040c1c88001340682500c0051240c540303000300c507080882415242e01300a101c1da00d910f102d0003c068442c40414070760b03522003400d44100800ca02d1f0400c8203504070b4030b912888034454442c15064a1410300490b855038041d030103c801607c2d0300b0010080241c0c090355417200400020302600308165031000c45004c9030300d66104485014580700c64000d4160703000c6140c60302c2d00e640c64000d0040810140312002c0003428901c074410003114000080c01301d9a490030040350040c4405806c000c610b10409d140001c10803c0344c0c0c0118000d500401c024401590741c074120a41885095800c640122541640400072036003d80c0300c8030901405151400f201d064000c006825604810500030250b0000541c0c5405494540304000f012040e428248141c00c00e440e8019489000c60859460301200000d4031108540c7e042c1308503409000010600d545a030344031004409c0511603040c0a6010744540d0390403010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 365385269 1250 365384019 365384039
    0x3031b0309020312031f1e06020d02032706040b0a110304060504030809150d0e060f060f310b03010f050103021509040e0307050a20030a060507110a1506 67
    0x100081d0007800070700d00354a2911a2000b44c2e880200340310407681e01b0103007810781c81d84100c4508004204003405100500c403030284662200e490381c2d20400a56026003d01004250040309584000784a4406141a030039800742016080940616042d44103100103004142c1601100280c00d413400b01d81e5900ea0f240000546040e030381d01c03c90045c20b000c100180700c104001a00c1c1002001c2c9144094040004003c00340240b052a4028119482075540c03105581041d40c0000c0218580c0140f101c0e91200150400c0c1c1c1c0450310985801d004280900007544c28155203c0e030b140340b01c06000c00341c8a20510060802c80c1c1074401021483c10302c503c01d5080641c2c071034038490b0303034060b060580741c00034500c44217508001d8507000964001d0340540d17001604c0e00458004020144003400500d40a100644001100d0f403414400080b0382e015074403a18400d4000b030269075100014a0034023030750b01803c000b0b120b440ba0750040c1c5044d201c01e038010320144501c51a180c01c10150030707004010800e240b4004c3c03150079141d41c4040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 365386519 1250 365385269 365385281
    0x20d050f0a0b0c0c15061c20040912270305150702160501120902041a0913050c130209031c0216060c02130b0306011e170604060f060f0303031b03 64
    0x7043e16808524040b4105c1645c60010340c001d4801002e00074480902030403107141909040381610310307090191000c1d00e1070008001103200701204480c10401c1f28016680c58100c44040d11600d0708000c2c00d0712180560300c1000c01c8082014425111265005949140c001d43e2440900d4001c0446031003031010890140c0005600f5603500c603804a0290402d06010045401340384203c1ca48135943d80742d05003000940c889204000309003912814a03c4000340302800c0c02500c690141c21068a5480f0f0100c81d4003180c404541c00d55940f104403801d032a0300481c1680403000c1c0c01085140390341401030300e40107044401c035000381001c10010740d0255400003040c5410070844042030300c1a80081040200c0090041c0b625901c0c10420345168000001d00b107070307018042843c100d0247c00c10740300b005140d1811000c034801101004002c00c02c4003003081c88102000c54664555102900007030003941c45000b0525451020b4000001520032403125600c0c0d40e641e03040042c05440003042013840002c002000110091080c0106 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 365387769 1250 365386519 365386537
    0xe090a0c060e09040f0302030f2101080c0a0b03150402180906011d060702041401060503040c0f060f0c170a0c060e010b060901110705060d0204140102012007020d050f0a0b0c 76
    0x4102d5a921511075450000c5d503014110210300041008401002d50301002d030810148000c981c240442c0045c00506125030107800c61202544100364450995590864040699002c014501e440382c48023108040c410303141a9000368414004616503040285103a549100c0b503104aa08580c00d440302801034403e80542000c20760141c280f91800010750030000c0007014003500c0940000380c8040341c1c6040300c0362140300f81c0200000420000901c4144040341d64182e0282450b030001120302450302c90090504801050a4818005840d459006000681c5100d042c4011480c000300d50320406420000c0524031113040885015182c10420900c20805100380240c43d0006083d080c0380103102001550760a00c0207401410600c240500410700303440705070140141700102c901c090307191030600c8010004481981d80d000d0441e85010045203803013001c21000000d02d003001e4580d07650f4520500201c0d01840110001030114400c500d5480c0101d040041c2c154105405400080a940c40d0000740b05010700c00d09401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 365389019 1250 365387769 365387779
    0x402060f0a050708040303020717010c0e010807112e0b060f0c030c160303080f1006050a03021317010b18040210031d070f08030f04030f05070e090a0c060e 68
    0x8400c90448812009000c1d2014908180d4200303141c07035441240d2548540c00407001078109810400600d03031440407180c410b01c0b000d0002d0203e15415103005110030f00c0500c038541004070100108016900484548050f214104c041c0d51200b015a1044440700d40061901c0130300d1100b80e0340f010b60000035485645031f03c0c034004240030b20304003258489030640d4001199400841c0010003c00c81c00d02c03010000103a0013800d419205511700d20b1410701a040300b80041502d180d02030000c00300000c0707140b8104020300360745403401c00d01e80f11884110110000c0c0a119404000c8142c2014045840000610850003414006009008825041c0188808115120b55035691011040c2c04600186040c0109807110301240c40d00092203104004c0301d1701c5080f0301018155603900029001e0040054032000000601915001185480640e00400c1c5d454442c5103c082e00038402154400304000c1c05102d0807000340740d1040d54103103900300001d2007a2140c681d8042112540c5400f03a0015085000b030b480c8100014000f80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 365390269 1250 365389019 365389027
    0x3131a0c0312060a05030601150e010504030b07120219030207140703080304030806040f0507030b010f021c030509030f030106210501030f0221062a040509041b18020d050609040206 79
    0x2e1003011900001c1c00440c1d002200440118450b1000c00c2100c0c000c00f250050300d424051004406003600718400c0c0e0340c42c108882044148041041c201517980c210340c0303914161800304461048a002409040c11102c1ca007000450403409041d1f0540151070640d000340350584618401c10080c40d9103200500c40141011014000200468080ca00d500d6114001410104044442c4107082d011588100d8070300340826514200101c641d6808840601c0040f550300040540c4070000c0604040e184900310032100f05611100016007120b0148140e5030080603585200e600c17540c580d6005000509510241c00c04e9031152200c59449601c0c90040a0407039401800e030300b000540903024440b81d00101440c030b03070540d0644480c0440d200020084a44503900d643c001d5282c00040928100c0d102d00744940a01840c02c2c04d0006106684d104038085c0e0304660b215a01410100144030801d50444281c0d00942c403040100315513a44000c500d400400400c2c084036010082540c408080060010054030f0103904940c01b80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 365391519 1250 365390269 365390287
    0x3030905091b0a09030206040906060e040506090a09021c030801050909120313080702030703060213050406030809040c17040605041e050a1115030406020703140a050d050c0c03131a0c03 81
    0x1a00816440c001c0746480e8012649903004a600e40c1e200e0342c000000c9d140c0e1000200401948500030541081c000ca40070b00540c10203c00040f810b11025103542c0355a995410402c04543d0b86001c0b00c04103068040c1e440e29102001d0501400211003441501e00825440c40010000400812180c0c0c0c8071075030744100c50640d2594004c014111084441c00c440d040360810034180580c1c3c040007031000451291074096a5a040c4c80514078052044d5030056008605120062000034103042c161414a201035a00091202d00780070300300d4810303e1008418400e07140b03103000d00c401c0c8038880d0000ca01c140d001d200041341074901c0800d0008180d8400c10081d05c07d8105800d45c82c00074601d04480301204100030700b961121080e854030801c0d143d100303503000ca60305540002c82c18101500000c2c40c80204030351003141402c1454910b0090950312900001c0b08510740c0d5280040c40701502503007a00d0100301c400d421640c0300e201e01c0d01c00d1001080140a000030640704094031a0390f0380e02c4c460031500b92070402000f850400e4608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 365392769 1250 365391519 365391571
    0x31608070906180b0c1e010911040f0b0604123305041103030a021e06040201051806040308071b0b0301123c0c05090c03151201150303090509 62
    0x43c541c0300007800c0506000107880003201001c0c05400b03449030050696400300b4032004002103c0c0070001031669060000306404500c1c40e001d084480d007425240404d960f030400c0b5000d0004d010319480c1e1907104002150104903c07540400c080d254038403c090000b12118644a0254641240280c40f4a040d0080c092401d44c0764484d0441a0404e1080c038075540003407c81c0b40040c0c15a0450070510005030b20a001001400781511001c034131314496500a0441c504082c2c00007040381c40b80d1011205103c400c01812010354680904880045803c07005040e200c3ca0107242182c1f403403440041d1489080400b010128a800003001140d040300c10b40319000b54908030340d650b69103150a0884111410f2081c2003011034078102c2e1007420b0b00034048102160300342e0191915161a80400303d411050140030501d0402c80c18007010011650845030011621510841990008020041454641010b54202020503403d0900c080684040c0c034442c0c0c075190b2025888105201508100302c1c2d44442285085684019001c44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 365394019 1250 365392769 365392787
    0x13020102010b030d0e03061806011a0903101b0f0219240606080c0901020a0b13140f070602120403021903080a0e041a010c0803061305010308031608070906 68
    0x4103000114540940400003410035048001400c08170b0034549207031142e4602881050f51014845c00104004000564419a18101405030072504400901c5084d0b0000d40c1d1025940d60075401401c0b10150740c0311110000c054807d00e10a80d842c0c070f08a80a110000e40144154006001b080c0e0003010118107d001d51310800444120507190a44084a83d4a00400102d5400703400b030a20720012985034a0b020300242107403402000c007410700c40c3c103101c9110982c2c0c1c08244e050780aa0484010006030b1206811384041c1c1c032a50100420307a8440034803c007090030001c00c4240040c0c1000050394081956444142e0300d540001e1310303c4503091010041400145009025001c0c401d41400d4500360160f240d55500e0100c0e40b01300346200c040b840070406202030349020f000764401d101031105403090300d414800002e46402000c840041a05102100041c5075440d00c0d0000b0312250a1208107001a50350780c20204c070254419110000743c04504941c1602c0310340607005d841d000d210305036990103a0344c0c075001c01100c610300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 365395269 1250 365394019 365394023
    0x613050604090803040f020a0f121212050a060905061504030602280315120302060403080604150f050a0b040f0e06011209060c0f0926150f04060b03010b060313 70
    0x159034014080032600007005144144c6c41203840311a4507800740104002a60158002e0704e0346e6040f04400c0c003001e1540030780341003001c4d402440b0700c1d1068060300d001e441010000e4580240240b50104000c0505140e800510407509520340800030382d200c503800d00c40c80c4000c403101000344140c100001c00c002207c50b8000c01d400c02012003248607001a146d203940000c107000c441c01c0300090300d4003101c034440402104400c008200c4d140c8072403540442550080d486038001031000d4180910900005d8003a00c464106041c04810360b203410382d80c50703240d48031141951305a0045074081c00c808000419203104070b1b802c440903540302c50242c3c29114078010f9030130764107000289503904011030300c0c41e00c4903111990702809120521600001c101d202c40d0140c02041442e015a4500401c07440f45010403498452a984203003031802c4c04144000140c80764a59450b00c0401d20116203103041040400083c1c8410782c04080c0503612603101402910f205030101403d0320742e0038016940c85081000484c40090205024280c900c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 365396519 1250 365395269 365395271
    0x1a011e0b09120703140105071e080603010615170105030a0c030b0403050405090a0218100801060c050a0b0c120703060503030f030601170c0d0f05010f0308090310320613050604 77
    0x40320070100309003064030130380c001c071058040d25225407904a0207008265012541d49007500204c2d810a0142e100785003c580d8090602c5558000300d41980c03801c1d04288007405c421002c0c201c00c00c0c1d4280e0f00400c994508030501c0c500c0c001400c00492189000300d0703c0c640054002d803649111600359281c1c90585400034000303c0c01d02404000014154644208062240c940c80e4001a2141000401c0b1064000c80480441c4602c400c2140240781d181c100c8542c9055610a181003542d42e0b000d85009441d203003045c4d90140c02c2421130700421401842e107000402c00d004980c400f0201a840c0c4070b40a03025608640105641034006101031070301004d482d00990b80c010b005140c2110103d0801d040040013810a0b85e01114444002409100c80381c0b6502440040044440c8200000d602d130400004600d00c49000c0201015000190009503a801700803030342c45000901820018403504e00401c60103003882440080c00308540d02e46510107030909280240c420394020340700a80d014000d19001c0000c003001001c0348d41c49 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 365397769 1250 365396519 365396539
    0x11d090106111908040e011401090e0901021b06060a050901080a060203070c020d050a03030c0e13090f080a080402270703150902070b0f0108010603050d0e060d091a011e0b09 76
    0x3c2036a00c6084076004002d480e541d1800c164141b6441c5005070441030801302108001e44e6540d0380460340000310384440440207401d881e29200c3c0380c060b100305802400000c0c40080d10407281403010409900030310003102d80f000100d41e20001d00403021400d214000c52600100d22981c0805d81c19001907a2108a40c54650008800c507400541590505c07082074030143e018089880400d900743c41031511151507402e11945000f403100005050300d40707840d101141d854461a40300101300007041c080ba410395106070481d880741607104000b132181400700c0e4240d100301c041c1c206c1301c0900071880c006138041c100c10055050059560010550280500140c40c0c402103401c902d0005070b107240d6201030b1661a1180020007801e007841c005814002c001170300525010b924008003000025800111009002d5076410700c6d04400300c07040b0004004c2d02a11001d503241908081041c5c04020007202c14541c070000d6201340b0304090f41c0b110700501549808900c0c000748401003900902040355003801900c05044010450400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 365399019 1250 365397769 365397793
    0x90201020c100309050f070f030303270821040b010302370f0f06230903070f03060e0a02100507080c0d0e1203030403090611010e1506011d09010611 65
    0x45250142c0b05040000e80d1081000b00300309041c003020300c01e9082200100300d142d0400f11850711140d040d200003014580e0300c25184402044440b442d164508802e0f00002a950b11030401119551002101c4126095024002e50200b00702d190030500968220a07130002036030031982404005148807040c9070264408080291803550034103161401c022025111403000703898035100c8512141c9503001030b0f04e5170111800502c00180d003c00c103d090183c4031580881301b0038440740c0c0d461082c0714403028a5050301660700041407103009100c3c400c0450f0710070700c020004035100c281080d40b201c0c10b05900030b51010707402c3d6007294a90f100d83c02810030740d1300034100945070150002e40c89292010401c101c0010a4520040c10064500400030a09039820b00c00550310351f00d85642c00030020304c018000d01060000c020941221361000f540600e0a0324581c01c02c07205441c00c07003a030082c0d401d141240c01900103940c2100056041441240c0c0408201e805422840241d0074050187c4564243c4500003003688109808811 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 365400269 1250 365399019 365399029
    0x209090309100207080c0904051c0504030c03120f030b030607080601031d0d080105190902070c030b070806040608010c020303011208070507060509040507030225020f0301140a0c21090201020c 84
    0x80340e4003150000d08000746040b40c01410601a1080a441f60501d030f01004081400071900903c04030741d203218010f4540310b500d401e4030280140e80004d007283c00c08030030100400c40034900c1416543c0f507648030501d03c800744090450a6440c043c4030260950000303404940031900904001d07805c038030141804101001c1e42404403031004a0941d01850b9944004941d20989401c5403e050242406485107080c2d001c003081d064076002c8643c40b03101980c030350025842e0240890003c100e405540c2c0446a080c0d1401c1012005001c910143c0301c0c1840f40d4a0940d0026400c1c1d014850b003411540c490f00550b0071a8a0074031a40c2502d81d003030fa803c1e18101001c00c4110001481484040007030016030310703101c0d1510f48400500044600003842602414410084091203030f200c0c1d541c081064004c2c2e41c80002c40716107440805e20a4100c0c5958a03055030808010404c000303034400c00d03503205500300c2804102c540403100301111140c09200748200f6101071946d64006441183d00301c00c03003240c01130041715225940080030031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 365401519 1250 365400269 365400289
    0x90d031b050a02151603140f030114010207051f120209060f04211703190509030406120515060d180303090b1602121c15030b130b040209090309 63
    0x110795400c8201c9540440c508401c9400e0701c4408a04e01501700603140c02000240504090050140b01007445102d90090200003240e51101c00360369456100c0d41e45841160a03505080c030341c00c5c0940950840403031603041c0340702105d0101c0080780f15401c2e00f082c608810703070790155070000c000d8440d80c0800003a007850304d443d001170203480781d030f284480d0341c5500d40b0318171100e43c00b2400165650701c40034401090100b0800c0102419048504140c4d6940b0f4603100c4060540441140095040c3d504100c00c01140100210107801290a0340d222007000c41985003031082110781c00c854038071a40120400d1781180f400c000003d080f80b183c0001000420b1000708102204940810703108400103030b00e90103d40104948070344d0fa2a00a6540e6003500984da64601c0060348075803000d58881d1502c04080b80030b141804010104001c8070b1021081000380d10b103450329810581c522800192405080300d000f00f0010520500b450781c1103078010040c03600c55100c036801c01015413009001007103d44428081100140e5401e0482 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 365402769 1250 365401519 365401523
    0x1060503011b0807032d1b0818010204081b1302030f071b120f02070905010b0c121201031118070305090601060e03100504050a08030a091106090105090d031b 69
    0x80700ba07a0b16150801012070302c00910400c205410308079905004068045802c54038140408207001c5040401740010060840e40926002e00d09050040003040b034104407100d009415481001c2042224800c1050a034411031040d03003896441547c41c00c02581c8003049450008000405060581c4921017007030003a40c00c00d858074078984c0d00500901c040e25070801c0081558140703055069074020b00ba40c441090b0100c9043c02c64050009521441940320720910203034000d402134080070403072940c6419040b1400d4010700304100300c0c0e20501c00742c1450181c200b02610040e250034200750300c40703038255900c56407050180f28044d40c002c4201d404903c081e8400c890300c9803203813119076400225031400803c07280c54000d069000c00107009156100042a0b01c010501c003044a8038910007007100c0e165480c20034500b01c0320040141c400075001c401d2109802594118009042c0641601400d056200c0b0801c207651003460140d0380451810072100c221800c00703181e40c401c0c80f0b0103030805440c1c145d0380c030200402c81c85040c101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 365404019 1250 365402769 365402801
    0xe0a0507081b0f0d0b040c15120b040203060306071b0c080309010201110405060708090a0f060f1206050109050409060e030301062a170c0a02030313030203060906070206070e030106050301 82
    0x41c2540110301c2007002900b5008403416410240d00e000407544103101c1d9070001c0d0890f80c980001034288603428414500038210780e04107013041c513a012002800d40310b12803221030500d404c0c0740440c0110f03c1c1ca40281c1b8001c10b801000703000503440c0c070306054411264200c80390840980039030707404021400414281c0d00804201000c1c0d03940e1103000f00024212200214913002d0040280000e00050b210b201c142e554160340602015a00c0703143c04001071140205a0120404c0d0013108000700d002980500d23001c0e5110aaa1a00c80080c0030f0070075100c00342e541070f014207400030f48800410002450181c000c0000349018070000281223940380c001604544c001d800000201c1d0440910340900c0314a03100341c40c00183e03803030602c0f10300c0031550380d800c149036000d50b143c6901c441010a401c40030017000d002160050341d004040b42c0d0344045001030b204414000b840164032901030704000500100001c40c0c16882103150303034043c0a00703555515060761001207400113240c2540d62540f010a42d40c400744101e44030b0902000e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 365405269 1250 365404019 365404033
    0x130b100c0b0906010b0a1101021b0a0308090604020d120e0a030503090a1d041b0b0d090b0702061501080925090e03070809060d090209040b07030b220e0a050708 70
    0x8000700149005080754800d54032140c0100204900c0d903013610464840352401c8404250512041806405030030ba415100d0031051040c450840b400080e164034061090726a001e00d6640e1100160b224002214040d41040c01402040000303084201c0c800115800343c2405075030340034607a0100d4842e0041b90801c603030a5100042811700d0f03140129591000388060700017100c03c0c1d9003004041d0004480a00010200a0340e901e41207600c2c41c43e04000009419014425925805045054000341403094002e442400441340030844c100d1003c611203206040b166940e84540304903000449807903200414050503406041c4524001a10030510314003c1601d40e80190402401d000031442100c103034034030210303090b4030400ca00d60006500f00c044c2c44c65a8001c072161515906400c00704400f1b8540c1000003503100481030b00b0041007200100c600b80c001d800ea6941040954000010f210085001284000070800400150140300310650820386080021606807441e40d0344a0b0b40b00e03840e00d14180c000f43c51680040c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 365406519 1250 365405269 365405273
    0x15050d0203040f151a1201110315010905060c1e1006060203180315280207140f010203060607060915020703050409050609010605031501030e030a020a171305130b100c 73
    0x841c1e000d002e404020f0b03040111001560202499059980341e581c0246c10070307000f42d101c125003948035400070003a000e2216942d2810108201101845a1505010a40d90400800d0b94100b0000351070700100644002e01528050703508244e40080c003a001000144510301c100080b6802c24007518005246540080d91a4420a050040200000200079002c2d605c445404445c00502807007e07504200700f88818041b514a945040241c0080e4000e40a40c00e400003074586c04102c04442c02d482c3c085201d10944902600c1180c16a0903484166034159102c02d040c04500d01044250340080a0103108003444030140b080c880802003660085101907001c51004a0b08101044c110b00400f0fa204404444d42a01507040c80c6002d805404042c0010300c04010090403440305902a90201c8045100002207030340b01c02c40140000c1d40c0b180f010500725514421007500c821240000c0041c0c520003090380d01c00d00c07181e80c00c100522210740807201020340f400c1e4a811070400e054941c18030440700c249540d81c45810382c0c400c81c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 365407769 1250 365406519 365406533
    0x60306130e0c091303020d08090703060911030f01060501021b120d030608100204060206040311011410170604023a050d03060b030403080105190504020c0d03230115050d0203040f 78
    0xa240c000718013141c0000a001a50108248400c1d03901424000703215156212240e00c0c110fa550001401035180c948210240401c83c612884860b1341142140c0f802c112813102c16098800911910f03002d81c0c040660104c291410401078509a20b000c0c1030120f8050340399030300301c1c6010034140044000c29529081800944010f114048110500070003d514141c60210001c0d922a4018005010845a010000100c140079005016088034113400b400301030414281c0c01301c5200180c41040c0c000d00702103000030070024020a56900c190b8001b0001d8400c601e0340e080c00d04031500190301394081070f00f0114141183d002d102070b400d69250700031002803a030601083c1d005811102c0710780244010810078020080080d0384007006a06446054410301c3d103558144030542c054500b00c1c1c21280d07026002041d404140d0b8000100e500030801503540c140b010b21011001d904545038030315021070018541b03200502004108c50308008080405142007480c02c850b020007402242c100340e40c21a1174450b1840d03050144446 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 365409019 1250 365407769 365407771
    0xf0403030c080702120d021207030c020706090308040b070311030711030c0607210e18150a0f030311030904093c060921110f03030c030105060306130e0c09 68
    0x140b400d01014600307010402a42c2d13240140198450584002158040d80d603060b01610103002c0812108005030812080150182020543d000018820000006401d912031301a00c0202c0b034000c451305252a00f481001e4445034070015081d401c0c480300903401c0c141c0d807108000a0500030b0140d400e2036100a03a0400f0107003440b0ae00c1c0c600721702c28041804038401180000c2c0d01810307610507071800c0019804000c80c1c2a40c00d00f8101c03145a901c10111140500c21a90916116100e102c0007034024000c07206003c02c10100d11054010007034240702002c070620000b4000c0e0b100450031a90401103c0c1000c1852000900340c031006601110b0b000c0a600c284100c0d084c0c050400f650341070250106041c070345000143c41d10301129601e80540f1140d10f0316402e00c2401005002684074075400103a4040c40c41074020003905480311401c020a8512407140400d580f0b00010042d2805050300c0580203245902e800c00b00320080c0c1010f0402035111208960300042e5605034404c1c4207001d130501001d45030b00c240c12010095140c1c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 365410269 1250 365409019 365409041
    0x4081c121b031508011113210213091b17011b03020906280f020a0f0f02030327010908070305030a03150e09010603350a03140f040303 59
    0x10420744105455000e188040041100614000408022070881d5100020542d88502d5965280c80201c1c0d1610840348020b0501025516800c900e2503a1080c4500e1300d14003800c07e10354031045001882006103030000c07100022aa0441012a41000f907894003656001e50b08541400c0a22000b4104685640c94500c085400b59520007004000481000403c90846410940c005c040e80060300c80c3c080c0d0746580c241c41c004241e02c2d450209410406000c089541812070124010a0354440c0064241780300250000146a11603800c0201c0311040c0d5440c3c150551048007264103000c140010124280d03121820103030881e184080040c101c00f010009801c40303101da00101ca00b50801c2d10f062011070342c000110307150100c01d1b160018403040034040004600507182c210410116403c0309000c8007810540140342524050928400d010040301036031000415401000781000101030140c1907441d040c0c2000c1c02150b40b03a4180030a0700030725202d0001d4500c40440d00c11840040c44818081415494420134481103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 365411519 1250 365410269 365410271
    0x5070e09150102150901021b0d0305060d2013050f10060c0201021216020a0305010b15030405100e010f0c17090102030c19090f03080d050a110f07060204081c12 70
    0x44a00750000751902400504c2280c502c00031804581c80d054254115441200741d1440170501408428410781c50700152540400040e0400000c141185000c40f440b450081d400111f14203030404020300411030b0b0325042c40f030640c440f01c80f10220b03201012501449201c0c825088456041d45000f1131440300e0b00301c541d00100d04100c0c54015030801070340c0004501c9844032440c032501c0c0c2c0360b407581a1485000c00b801340c0d00a400990000e8000200401504000004e003012105a003006189581007910360204542c041c049511500c0016494520ba03800b003802c5001c00c000100300f2941e004040026290368468002c0000c07942c8040640190001550035001401c0100a62030b50502012040c224041d543e03049015003024850b4900315405400303694010500100b501c4081541c9040446c06508400c240b8102e580c2020b001440710150b45c030a50071550708515100c4e041200710201c840385074200005c2100e82507404c020101c0d644100b04408002c441c005803a043c603c243e00070300100b06240480d0704511103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 365412769 1250 365411519 365411551
    0x1009030e04061502120306040b120f070e190f06030c17060f060102150705120103080d051005011b03030207050a0605010303021203060a060813060f05010504060b040e0a02090d0605070e09 82
    0x4244d010840002c02680c3d003141c00c0e2aa25400d001400500800e0308055110000e0300702c0340c168078004113480b80c202c124bd00903501c03107540d0f4032894200320340d040304c003805a000040511102c040c0d21307034011712241030710b0a000a165626035a500c219075449030030218040c540d540390380d84508020010759070b003e80200c69551050030f040d03002079603030044c0c1c000742e41c0c1d0036281c40002051184184107075840d820710942c40c050b80d5656428120381d81c0d03102240b40b43c1c69a0400b8001031003000019401d0b000ca80040e540c85100350b01c41128000c2c95450198214100341d02002520041181004903d22050207104009021351551802910300702e900b4810642890b421f00070803003150341e2808944103c4109040480090b035034000f11000c050040c8070010311107071500e0812842055241e201c42d0684105070f034104299070f01da65518000380998850341c040300b45108000fa8944041d50041c165607503020b800c00f26400103030703918801030781c4e0200d81c0d0000103200300c15034240c589051000d0940180301182c2140302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 365414019 1250 365412769 365412809
    0x928020901050f12030d09110102060403080109020c100908090a05120a030e010509030f07060909090c1206020c0708010c08060d020f09060111160302040c020f030d0b01021009030e0406 81
    0x216103014490030740309401002d541c03c20740c0c031200762002e052070700714085d680e4405004042c20014501e0f40c5040c2d403008580c0c003134420725500004440c1c0c0140d404d0344442026070302c6c2100704000381d070060a11180c14000c504086044018038000e600c0c04a109100c003036280c02d20750061021602059012904c07d070b8540d00d030499500d0000c030344407501a405142001d141402100140d900c0e20464200712303050310070141424070219021484078250350b006d640709041180d91309188020b07245450f00240201f5a80742040103500c0c0c4542c0302400082c8107500140c01c0100d542d02090801d02c1503405215140d4680c0103506100b9886840b50b94002c20445140b4520b070703065004101c2c103840c410a5030b8014403c61003c11480d030b004441401c01c0710103950880302090104400c02c40c0c103100c00e1004034004c034141555a80c4050000c500c0c1400c0b0781102d8015030511910341c668001038865242c0c0503040d4002d4007940b5143c2c4095004040b1070b5406038440200929103601030104607403643d448444529a00d0100c030076 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 365415269 1250 365414019 365414029
    0x3121608010609060804030513140108070302031603091b0303050d0605032a1306060309021215041212050a0203160f0801060c08040806040506090601090908042309092802 75
    0x8190754480c40d01c1030b0305607031b80d01c0c003a6254400c802029540c09880d0200048030324080c1c0741e100d1000000c0c1c2c4ca40a041d04d80302401d60990205540312a2131900d0418407904981c0b00360f201c5c00703549018444a41c0300c1004801c0191920f10a03400940000e00c001880b02216500d6006e0b10006007c04e4005000414203441e500d002c080c6c0405c06803e802668250141850765030140142c010700040b0010002d43d950b03000007500414201c4400c90090403031401c0061000d4003c51f01031841213102c040c20240e42d56503659406030803940032900082c0602c05000e0781000c0d80b284141886134245000059807400e10b0501c2c40894000c8240b103004014508000c40007040d4441001811140c1c2d07400c1140d5102c2c0107207040e2a050107a81c000c40b80510842042000340280040c1d40d90142d07690105455250f45c840f03141006648070420040c0c8202400c200801200c080f5101d00b9030700d8910388040400106880001514811041e545a805a40a034039401400003031002c4ca0701100c0d030329041b0200100c48aa000c11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 365416519 1250 365415269 365415287
    0x30703060b01020f16080d11060a020c19030221030447070e10090605090a150207050a0f0e06060d090b012904051806040b03031216080106 61
    0x4041039192400c903070041c0d0080200e840002010b00548600c00081028211008201e10070444544104c0d0742d60f1160354051402c91000c07140450181070103659907228580654031103003002c126845442c032101c0600840c41412122a0f04c25400f4210752011115400f407401d03804500c01c40e40030f1040040c0300000c1c00d42c00d40014176008160324500010091520004002250514010b114668640c0ccd0403035100100c0e9400d02c107000300e44440210000820a0202861007142c04001241044000f802114010009041c00da40d00030410701a00341c075002d50441e0f2810000020300580d00000c403e00031840c015a0440107040d060090f07003120717480c2070a10744200d100a4642800707100300284120b1412a00d420103a56940c00075550480d0b544d6a41c0502910380204811400190004c6949a00092070004a80480c0c50083c40c14030400302158072013800c000054511607000da69000f02c03c081d0f490a00107484400d030840d4900f030b15840c1c07181413203204501d070584000c02c003d1407070014400c50b9040300c880 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 365417769 1250 365416519 365416523
    0xa060305240a17010f0501060207050d200a230301020a0230030f180a0b0703020c01140c0d050604050c03071428030b01021612030309020d06020403140309030703 71
    0x18858400214124505a8003c10000301c1d80a50386003840005420600407420301210800240ea66100120707241c0d0441d0048a610001c906000d00100703152106200b00c411b40c0041104686501c10300003050344501c5e60180c917160f414049030a007207900001a405440500307030002c0d80b904401c200d0003500d5010038a09148595049002c40b2010082d0141c50f04084100c0c80406640b400e002e401c400752540b00321003030307090f900100180e10318000300400d41d0340b12103a0080205c422501c9100e001d0b4042c0d009008030b40d0a0b590380c1d80084840340c44400400b4000d414502d412951030100740c010344155000100500c0c000c0e0f00b80310070300104004080c1165070260041c5800c0c01003200c02492483c2e00c0c0701c0c4c54641d24490391003c004e5402501da0509914010805c2d0b00c0800416044030016611103810001c00e1180340910282013007402c0c1d071440c2c4001e25903c41d240c0010030280542c00580305c0d402410007a10000d5020a061080040e00341c05100641102c200541c1010714103070000c4d40d100c09078000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 365419019 1250 365417769 365417821
    0x4090f031706150a050f070b010314030a050f0a0e04090c050f04020309030306150403060504051e010b01020c010f120203040602070209062d010903120215130f26030c04050a060305 79
    0x10860110788203d01b5211105107294441c1e03a24099030400814082d400c1c04240c460010400b400c18200c500082240c0385140e1544078141400441804000940c005400300014000355480c8040c4654440c803508014038420704800800508000c01d101403840d05910240c0114410801d001e488000082600c1d44500100c1d00403441c05803a0201c1c00782801940d200070080d60500040c170080050110340c0c0c4401d40c02103142c400c240d00c208061b02d801c1e80c500502c1c3e6030158101c0280503040c0d520501c0000049840c504140c600c12812106010881c0e00888050346d42e80e50200300c1070f0441c03a00c5020a80c00880860b0b80c0e140c691105812801c640706c6034500d8000c1d90304ad1203c000041d13402f0700c02482c01076411084043d001c2c1e882000c06901e40c1a08010303a0f4510485a000030446100300381d4074005690400340d0ba40f1180130656440a034800d18560074018908034112f42d100e001d00c400000c40c4100e8a498a0310380b900d10340030030f01c50304848903002401451300300001c02c4040051808004100c4040c410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 365420269 1250 365419019 365419027
    0xa0f0c1b080c030c0102040e0705030112110102030c031303060608030a021005091c03090627030507140303040804080705060913021e0a031d03030403081603020904090f03170615 78
    0x1d0619a5446542e00b0210300340400300c0c1c1c4200d1550198041e0080f0381c030019480e1540e81c3d600d40129450710090084940c1c1569109193300410b00d006c0c407030400d01006004072490700c00f00008440c6580c014071101c5004003102b10b0113004102c0c280c0030f9040142100d60007181800d010010207521485184110002e0540d03590002d2002101001800c01502900c03000e1408451941c2c4024040c1241c04801d035807050400303814002e10341802001030340d072050858144082e030905543c1213405a000c1c0100ba603000b09c100c07160f090145414002140224450003403540d41d2850080510b060108a82c40a489480180044a00c0ea152001d11003000d0f4407510740142d859004d841c1c8400b008000140d201c0c020500421110b280b15015800580440c589610390f40c4942e9030003c80540d00d1004640003000a896034000c42c2c080404658010b0a1101d13605004d410040c03a00081011504a20815101040c0d40c0090301e050640010750800c0980d07000303001760b20707034641100450518240b00d001403003c404002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 365421519 1250 365420269 365420273
    0x11100f08090a060c1710061407030e09010e070906050c0a0809010302190323011818080c030d060503030304210309171206060a0903030f11060a050a0f0c1b 68
    0x1201081c15240c2c0841d040003001308800d802018034000e10745500f9400318030070200708404102ca04d030004840b21a615890b10b08605000c1c460140c0006508805115511544180703660b034022071035002c3c1071107194072100c034502410f0040a4031030b00e034801018060300308100312000c40c010038103812454000146076541c03081440120024403990040720b4000c078000c402c074610301d903054020480000342d00125642d08404207034120481c02081c4505030402d52201942100018160031281d01e01d246c0410311603100c24242c44503d0f040d072145480c95500e400014021110003000d21501000c0d01d410381c025403e5251503620a178921041507410f44070302d030980b51042d03c4284607810185070a6400b2113900c003401455001441a034101e041041e0105854100084403400d080c0c05441c0d4142c5556030f209261407171502e00f669201910380074003042110402c1c5035801c48200300801401082074600c0040c0170719041070541e0480c1c4c0020704840c0c2c628200040c1b9070312194801225011105c0c5111300400c510114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 365422769 1250 365421519 365421523
    0x20c010e0111010c0201051503010209090a15051003020307031b081f0f031104050a110f03101502060907061407030e060705070608040302070f0b16050f01051311100f0809 75
    0x70520324040c1d600b040c030340d15521036040d0015070123031161090200317012600004050a03400343c101090740082c1c82e500000c9091140340c00801c280d03d00d10076650041a11900410300520b07070a843c600112350004148000540d00d4895050311b1200954003801800c0381c041b0040c00e48601400c201e107205a041e80e005002d10070081c002c40205142900c203960340c3d5984c0b50003642128020341040c0300e28031b0240044c401100e07a0045a03040f00000d07000030300d00010340440e88141e0f0030150102950f096401e1010070104801e08140c50300c0c3d0000c0e00144810701d8900d6685141c0100e40c1c00081c100305030001c00444040c215403e655440c5c0d41070400c1030629007041c0100b1018001c040c0702410f0f5202d601c8001483d590440f080d01d0042d4000c0c1d0944044d01d480b540c21070b10302069445500c0d0700b41c200300710210b00c850380314070b501041d544a6416110800400e0803c2402d454054810342400c904442c42c140420a407102e4001103413005a843d90103220f226880030717103407100021103d41030150500001c0d0342e140e41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 365424019 1250 365422769 365422787
    0x40302090a090516060f021e0601030f0c0905070504092a050a11120408120a090b07050c0d0c050f0405040f031b1a070e01180311120a0803040201180303020c010e01 72
    0x402c1c4d844007a0950f9444010080c0f81e0280d901d030054011034000c07410001c00d0821103c0c0c20718161004000030f034a50b907240000c0c0c0b101c001c030a40e07000d0b000d0345e404103003051940216800341d016a5a80c941712802c0023254004c4640b50810300c500d600003081c11201a400485811200004508056071908041131064500c40c071005800c5c0901c2c060003c4011201d03081c14060819644010112400d40c80795100151852040380c4682d004615504030400c07507480d138400100002c510070016030701c0005082c404100466044041169601000c050600150400001204060004413001c0c0450708198480f0208044102ca0190811040740b4201101d88440307012001125440028504018071118024000c4c05094580d02c1c001741092100302103940c030460b2481c5101007240c0c05240860f156544205101c0403030b001c1c05400921482c0d0000c078110061090748000d5001d0a0496500d107828800180b4445110700154262803190300f05102080c2c0c0010174103103203442800d08040016600340141d0300001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 365425269 1250 365424019 365424043
    0x206090c06210916170a0b041106360f0f041d010504020406050603013c0306050613060b040e0a02090d050d080a021c05040c031a01061103040302090a0905 68
    0xd07142d810300400070300c0001d43d042c102580c143c80340b11054950301000b624000300c0001c00740343d07882800818041184c41c41700326045446a40c0001d10380007040c0200700d298120720280307000b02240c203140d14403080b6503119400c0400c0108404602d43e005441c0007a0030b081d42d69222038081e40105050f16101c0c0c0f101c2c0d10481c0c841d40800306450710f1442c07492265003e45000c40c0c7c100c0c0903505081c00043c150500d4400d580c1680d00e403034a2038483d070078034402d01c9881251102140e50140350104884082c1c000041104002d180600c3c40440c00b8602a010311104440310091090801d10380340e03007080000c5200040d1029503c0c11840302506031903600284c0042c0c040c0401c2c0301d038030190103840c0c60100324001601842e092442c0d15190040c0d0341c0c51a601c802ca00420b00321598940710f011100001a080d94041036215100c2c49402c00d4441d00d0740c4862000258007803018003201c8081005010440c0c02c0b1140120010481e00254030702815580070400c2208060100c151840c2c550b04410304102c070602000803800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 365426519 1250 365425269 365425327
    0xd0b0a0b12010305190b06040f0b091303020105060a0b0a050a02010902041a0f041e0b0a080d051b010911010309062d0e0106080d2708010204150206090c06 68
    0xc5070380c031076403468a100b0303c07084902e489510022200c1c01190480c00e403000e03801110b18441c5650b2401840003424921080c543d6555607100b140340141d035080b10361406034014510074a038951381864041d00b15200900310034410084a0410840c161440c4119071b4507960301d25115490320b440f0813003a8090100028029406401c0a801c00021100ea0314026071500d001c0316100504071308032091104403405280c24000080c24100f40441c589407580054007801703405800003035a55900c01c400723402e10740310b8100030740091400650608101200703152004600c146070020403941c0450b649208845110307103000e80c149a200c480017001e001d51f640c00710305440a0401c6041824881e00c8114070180512907040c214180303490200c0381c42c80070500c14403095550303c03002001407009590b01a01c5c0003e402005c5202c41c0c01c008007136440c010305a103180c0000c0281c500050307140c17410940e07001c000c01800172400702150710440c20060b1600c0f0002e400350b1020b0701074458642d6140c1284280090b0341104070541c05035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 365427769 1250 365426519 365426527
    0xe030316140c0307061b081501020307050f160602030406050414040617060a06141302070203190f2102030a0309050c030a200415091a180403090602060601050d0b0a0b 73
    0xb80000f0008000f101c1c421074003000a0150030348030540003203503403200100040c0c1c804006000c1d07004a6a00e00800841401101d041a0540c1d54413440d1030852a031200c9240c01000c4000150f120a010a030080c10007030016604180c2406070041c00d40c0218850f0032149040030038902c920340c40341d900400c0540801000d003c0c0c1d9034440300d00140d44201c00e46d140b400d0289803010024250109034546c0c08a202d000317041008a843d03075090b0380040e40018000b030783d0502800e000c1805660b804645000b010b807041904030b200d0383c0c150905404210740c0c0f80c8910100e100441d1400e0086901200301c038840ca00600f00010080c2460901d0361402d140242400c1e01842060741001c00e00500503480700c042c1040c01c5000c041da8561a05010503940a000406100c00100c542072204c20525040075098023044102034440e04030360000a03050102c0308298880070080b15080c001403503402008440601075600080c1464103003a0002010340c032a44080c4034826990300750b0340050313540300b0b120f0200400c4640f0000f91a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 365429019 1250 365427769 365427787
    0x90f08130b041706090d021906020d0e060f06010807050a1b060e011d0703030f080a0e0d0804050613030912020604150302210403050a112a030f010e03031614 69
    0x314484003240c8001c2c1c0f20380c0c000680303038400004010300d418001d68050180c0802d040045403100b02c8540f01160490303024004612f00441034403481210400010040c181424403171031110950b800640380c0780c1082480f008125000350044102c0781c00c0d026031303d072948140e070500c1845424200c0c00100180b025003890111540740308150040c500c0c0e014407030019281c04100200c00341e030700d0f100380c48010081410030100320308150141511076840400d804010603544642c0d11900e040086149003040811802c600744000d10104100003580000132121800c0d4102594901400d491a07a108034514040c0e6031400c0c004544a00003660b0050018080c0b03034200e0040d03980090f01a41200c1d104240199101c25041003402d03036a4440e50045805460305483c0c00301002085072040b01001c120b00c1d15200d418a405103c0c03084102041d40407404c0744910781004c0e2203004050500190014105150f8186102c0010075100442100e40204404101102e01074080d5070940d5250084965841c2c06403011401c0f800e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 365430269 1250 365429019 365429039
    0x9061c021801020703150213120803070314130204020306031203010f06171009020f040b0706090b060d20010e10020d12141801150b0d0f090f08130b04 66
    0x488000c80c0581c407500201e60012039035488a44005403141e580304e0702070755441c401d660060044c1c550180241e4040d9031115961410a00c843c207040760450b40000801c610b49900d071147d01688188528040d5042c03c04000d0301810780d14804002c2e20a5a001011500685e0b04000403420718100740315813034603980e584081c00800c440c0c5100d07a60109103501c0800b0071003d00b619000f4441d20b901a03174a01c1c03503800c00080d50020340100c1c01043c80e20008010114420001002800c0c1ca640702d0f20002c107a0a110b8500f034648940003030550350007410b0f4407031041e0001e0544001a04110007034a40e40030304418910040350300b82030104c40c0c075400a00c0f0b81070820081d5400308130804002e000d5100d1011311b07035a50701c0758401c0b5001340c4c0080c2041580b04010071003108000d444001c84244800001c0b81c24044007019200da1900390b48004014007000684c9050300f034140c010004100c0c00f8203070400c4810b01c1521001d4448800741d40060811800080072ba61220b00a40040064103ca009540d100e9441e109801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 365431519 1250 365430269 365430277
    0xc1b0c050310090203190809041b0905030102182710030303050c030103030801031101021f0b01181217040918020301140601051603050c0307031707050702011409061c02 74
    0x74024001c02614100100c0c8070b000e00d8070390b264060000c002d0103040001c01009003100000482d43c543c410010201c071503541d0700038002c0d26450032040c3c0c54052194003028081720703442d41c01b0f2802640184008210565010314181040b001070340c9220780d401c01c03030070700024090411045c031034040a0740c2e041c043c48aa20541d140d007581d00c65103080049856a060205290009107c01400258030384014800503420400404800c1810300450380644c2a001c0800d22075154500461200355039110050700319a8008594013800102e620000c8155051030a281d4542062410150002d000008440c884041960407079006040380070b02007080c011065110342000e20302400c00e034800d600b419200c44002e440c00928a0149805071203da00d400c0c0c040a00c880d84500c80e00c01501801418001ca01e103054040c8014800b0b075100c1e64520249040400420148540261012040000c10302003d00180d0b0040c840b00c002075482e0000c6038171011440d00103611482102c2c20080618103542010700320341401d8010b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 365432769 1250 365431519 365431529
    0x31a130902010f0c0b04031419020f0d03060b090f0d05030c0a02090609060f150919062007030f0c08010f0506120d080609040c03050307030203030103030207050402030601120c1b0c 79
    0x3d089080482c401103c2d6420300c1c48000d0201d100d4200031a000a008941d400031064100078664200403020a081e88100340c120000805600400410040c401042c00b03203104840030303418100800f07410581003442ca1300441e1056802444c0440e440700700360391060050300019600c03108a0341d03205240c0c8030007510b444070050104e00820402000c20007501d00518190f06c281e50142120161407a110100411980000590018035804001190036911045071140c2d21500c0190310501d0140340c500300500001d801500d245000b440d5008005500102140ba80b04481d006011414140703428201095000016480003031198602003e41580c02d0560301301d540b01c5c22084441030b000f0030303148401544940458400100252242d00080c809207005030081d1f80180c010100d0f02d030600d403280c1d95917145901000c3d069015074000300040040517070402429010344816201503046090020010f00340f9110f98446030701c8240c495100500e2540318841c2140e000f405142190507141d80c034205424405542d02031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 365434019 1250 365432769 365432777
    0xd0c021c0e0306070e09040f110406030602030402130e0712020a0b04060e01020c01020c10120f0930050d0f0b062109010204030b040f030915050306101e031a13090201 73
    0xd9405001d14840b05c00200c001d001d0000e9983d0b0b41e584d042002c0101042290302c051030001e00070f01b544451003a08065885284010390721309088c010040d00203510070701c0d81202c0d0f060006020780c0034408114402140e1002c0800040241548000307a903804098120750f54041001c00c00140e80d41e80013084401c0c154080c0c09507400404120b00498885d60382c80b1070207400c140600c0800305003500c540414000888005400034501c01c2e09004403080d51420001501d064036142c905207140c1104441c58640c20900300340150152040441c0a0103e004000d100228030f035035160703400c0c078010050700f01d01003041009090741e954014000c181e50030350007403040d104220001000001d8000d01c05108a4003601c0d0002d5105029030b44c1c0780d0b0b5513902214a0f82c811010071520b52800200c05140c0e605441c0140603a4031096200d1400f82e007071054107010503040a0400a600098444070030074a08203400d8180c1c05d2401084a41c4005410245580c45814442d00680030542502541d00035502c2120154802d0742c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 365435269 1250 365434019 365434021
    0x70f023703050c010c0611120403080c03061305090a02151308060910021b01020409060314010b2805030303041203060e1608040606030f05100608030a050d0c021c0e0306 74
    0x46803240a0348540002881940300c559602d8080d80600c0b0340783d0040c0d20a80d000300d01c520b1901d0780c90324550030913424015004e034403006010030550800002d5903c0716080715a2030440c5410350000d60703012004070b06002403541d940e01084024000313001c40c09205030098040d00185110003455000c6521a0361301c0d41100c40c05440100d0300c1200490103901078080c0c0d078001c100000340401d14000a600800c2c1d0448180b03c0c00c81301304420242070000d000103084501c000140d840c550305010421401048241c05140d1410780011516962030a0461048803071303500310b0740758001c0b616106106184582016516203c048200020000007030001640c039490b0b07075401d01c02d80d039961411480c0000305403074181ea00c141c0942c001d2201c0d44140443d0b0390284c0106000316507d6a03d0301c803422401c1d22010309032190740003480d910804030154051003004111441c0250f192000b4100020300c00d006150721420000c0c0c49039068443c561003040f02c0665001c0101c0303040c8418040f410f02901e00e5581d109494041c1c01110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 365436519 1250 365435269 365435359
    0xc05090307050f0307030b010f0303030f0905100b0303040801020423011731082101180203040f0503131a070f030e01110d050c0618030708070f02 64
    0x4094a06400024006000d11410502080401070780c0340d41c100c2d01407140b00000800301c0e01000c0010700030b00c81e1041d0110703000e0031410014243d558086518004034181003090340040c0d00001d0034030000010240004010003a000001d045101d0b903407096050798004100460001310494500e00c2004004980c400407095060040d01c40348100c441040ba10007507000008c0301c50418020000c0c0b10307207069800c0699500d0003040c01200410586d400d5078408004141c107149900800e060000d800c090b0070920b40d4661501d000c007400550300100c006005a00407020604004100800444e010f134008141c0351a0349503e20a807082c1e00c41e40c03190304d402d80495182407001d8a140c10844180ea90082c20011382240c00752000d494041c031310341081d4100031960710a291403d1003405101d4203e604c0d951100c0c2d0350b200e0381352030500c0c01c10301030701840e034405501c90110481040042141c540b554130a140300d07142d14031400c0076051600010f6020790001207030a61241c00040150005829001d188a6100552004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 365437769 1250 365436519 365436527
    0x3010b1b0606060406181e09051803030115031116020a150c060c210606030c0921080f1201090e1b0415050607060c0e101407080403060e100c 62
    0x140d40c220f4015900f04814844680302d420044655122107400f6446da5540302c01803004041ca484091132102c404000034044000075006580c1c2081c0300d6072003039030f102010301e039490b80702d1006114049a407403218031811442402a005000001042c144880d1510b5580e0441d0400d441481c000320711529921380082280c6072a040c20450a034059610f00305490040c3d560f01d001414002c048034180700d0001240801035600ca400d005280a200501007000c910b000405016100c0c2d9090580c240102c456051100b03d050030303003c4200110a64890411549608020b04907109000080002d00d10018400401d100c40060260407940c04c04010801d0981d0041038a0319203004825000403101e40a4401425180942110706d03e6601440c8140045070b89100082070703075100c06401c80d0b8054842200740d4545402240307410090f50305448140d056456140700074045540380c03414280544010440e8414171180304252070255500600c1008003804d500c40481d80c52008040c2500000d05150f1070562182c82 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 365439019 1250 365437769 365437771
    0x2120d09031403011a16020d0609140a320d110606330d140609070203040b0f0f0714251404051914100603060f0509040201030f0203010b1b06 62
    0x94010b030540320b40c0b18440d15944d002c01e001041d07440c150310f1080c01607654623450440e0a4070901d000681803115242415041e04004c5621907030307420091500c030104000e0f40102c3c5011901401032100314501050a02003180071452800d1140b190345040c8101c55000079903400c031a9030801c1210019550503040001c90612110001c80100100758001300f5660507075054081540400140b5003002c14188440041798010071141445190301e90900c059810071a8805401801c1440038516241c2031400c03041d410b20075542882d42b407250000e1481c0c0421402415100159404210402c1d01255480099982c070840c08681c045000386045c01341040508100a000322410303104e141c0503041c25402004001c110013400c0400c2e5890000c1011301c590407130b01c1403142d201e540c000800503600b0001c00350500c1144541048052500d000f805106005c4580348482c2168001c440a0f03801d941c6601c0101e0140101103d200800c600100011502d4813910021b801d80840206021200c030341c1c49400300b0340e6804 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 365440269 1250 365439019 365439029
    0x1f0e0102160602161506030b060f101d060d05150118090c020118050106080d0c03080103020f19170d031a062a030307080705090307060f02120d0903140301 68
    0x1004020040c000756480d0044c01491040e0b8080182a203a140c0360450000020380f00b03180080e6684c88140104030305003605980058041d0f0725207001c0d60b20500400c422488240c81c42080c00800c030401d00400305014402d811490024008139224030401c10300d50f005c0c2000342e038803100c400e101101c00c04441d4400c4001451900b050f00d00d0401e09483c20340c03000000e007800c20241d0f003103549031030300700c1e104254101c165155035100d600002402c920304078403c1d0420440d42111000c000c2c01d110000c0110781d01803030050640b42c04030303160f0140031241c200092001150166031603c200505000140c0d4440c1014404110000030701681d90400586000710225018482c1605100100a01110301c0c3d042500142403101c2011954901d8004400d4462000854513640005507070300020401c02e0083d0f00410f4160003400d6410864101441c04001a072034844078006d1104001c0f10864001d600340c03080004800e041c6401c011581d580382e400781c1300303000341294000c1500030401c40c0d1004102080b2040031a41219 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 365441519 1250 365440269 365440297
    0x501021c050610080a020f1c0605060a0507080d0e0a140c0316170f03040b070201020d1d01030f0f090c050f01020706080c0705031b0303041a010b18030f1f0e0102 71
    0x1400c030035203d040000d40810705045e800c2c03095440ca01c0401f001454401428000031541007103154078282500c0350364010310b01912051003e85d24440d000015a281c03140e00c4222203444183c0402014001c05503003207415401d00c50b0a9010060200070282d907036151001009940c66042d00d0000d01d03540703503074a81b80ca03d9800c2103085c1c10001c0a0348a00c42410f016490300a0701c0d085c01030280410b24541050704a102840000500c0508660f010401903c0d0501c1c0c0b030034500d04c103000f00c80d50b000b181d002d4032046d136050513141c46c100c1c4000c4a242d4081c8560398000001000302901d075040820145d0703a60f000d1103024459260b00c110b8258000103c00302246c8440d50340c90055914820100d050342c0011034121460b203c20f100700d220303440f681c000e5800c020040b43d0085450340352a080410307030842c9401500d508242c107080140501c0341c00c1011940c038600000d0040c1882c1550b440400c2c81d24000b08600710003402840780302603051404503c01034800319185018055503624294180c200c0c0b1a5001c1c440080f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 365442769 1250 365441519 365441539
    0x5010b180607020316240201181212020409060f08030702090627040b0901152301091d041202150112060e060a0c020f0303010308040512070803070501021c0506 70
    0xe140c460002c2540300d10160566002000850b080c5401654a030004401d4400b50700e240600064203403c035a1000c40d07148001d01c0360b01c41d040c0d103105010484190107030408a140c414082594010303c80400070040c2c891085503102d5903001e071a002080c15020744021720004200c005004000042a204001c0e001412040191242c8040000e44928001c52103807803c0100030380a4580500441c0610a50160580a526103042d01c015401c503481184080011306e943c10bc00c0c08403a01d8040602281074045504903c15501103006840d0321840e648040c400f5800c04465208801910715094003a82c81101c00c80d044561440c2e0903600c0c0c00210708607811003004140100f001c0805a12013110b4240500d00005095503002e450508105003120354201e41c544035180c0c82c4880381d040020400e80301d20f1001071400c65045076503119071071059108881c404d081da24004803c1c114207222100c01002c0e4a8100e903a1036001d4a030081c080d4000c0b1801c0444443c500c0e14004070306c0c413a80901d42c81188010700d2240b407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 365444019 1250 365442769 365442817
    0x90e0c03010e04020a080f0c04111204110109050409060c141602040b04240513020c0309060a111023040209040b07020705150c120f0703050c0307020901140405010b 72
    0x424003000340f0a80c1e00440b55100000c03d2041405020f4007111400c2c0903120036a1204180800e4420404460003050010030042d600b81c802005100d80003130f0b0140d1540e000b0103d6100403200321f081c80e04000d51180ca40141c0d9402c00c00c041c1e0000e6062032854848a00c00c2a0600d0794842d01d000b220038071074041e08803500300c10040c0341039405000102c00007000000c4401d6a150300c1c441901590016400850340040240103510b0503990f18104015083c41c00d6142074104019540c076801070489060003074a001c01e280c0706c0da40c05042c9048901c0c440300d08a640c640d29030356890005d0042020300c00104030914000c0035034140410f41042c030a030f03005440d0804689031039035482a840c800034150006c500604001059076034a100d1545190780e80103251584980000160030704090140c0139012038110100008000c014545003503520342a00360529079291100f40000030304511400c20025801454440082258112000c0583c4201002d4500300300e1aa00d440c9480d145101d80c21058195400d0000c050360 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 365445269 1250 365444019 365444039
    0x1080a0515091e010906050a0e0c040504020307090c090e0907120b070c020603070905030c190303080a02040b030106051c060501050f180603160f09030b0604050a0b0310020a090e0c0301 81
    0x28100700709000f21039581540780a0807542d0040f001039a001e90351205488003e000e010b0080c19040606401c041141c01c3d02d101010340e036440c88800f058040e603201d000040555405200c84e400404001b20148200318820600a203810001d01034407599018120100c0d91010000039400180c1d905180b0703c03040038180762190000a040207000000b0040c0c0700540200503180d01e00510701840381c640390701001c80c0c1070604060070400ba44070001d0007401c3c6030001c54480e403008448103040b6601030038414004d8550b074074001c02a201c0e03500404c3c6a004000000036646074048024030125100d14502282c0c0c079040c508480580b03655100341400103405000f0103818003810320082440800042c0300c8040000f0050124070541c20855011b204514044502440950030505060701c10101e881c103a0842e60075541c504942100c00307031555001d103130341d42d0020308140301350340c0010758041c001004c403600e035001c10003208041e512400c00340d070004081c407100003880c1806000190085501d01e09050a6038280480e880d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 365446519 1250 365445269 365445271
    0x1a03040b0c0f0304081b0703030305090d031103150112091101080105180c0f0c0105010909140d081b040e16021006061b08090604030609020a060c0201020d1215120b01080a0515 77
    0xb100b8007500e1072000440c8881000311f04002c0d8482e460100342440c1c04042c840c14924403240c80303001d150401070300040010313410b03040700d610517140003c00c00ca50950400413900b14000c80d40da4030000d0f1a08a0030003d11510295846015009a8550007242e0700c1e481480038179100740e040ca0b0030115042002c2445800350202078816011649003507424111545921421b603042030340650503642d91014400c3c18440101c8520301010302c0702e001010074004030740008103d848002c02c08107030b0054040c00368000540641c101d800401920b50903012074100038072480340d0300703004403012005807060b01c1107022920110b0182d001295029201c0d0703142300021105100d070818480008481d100c404100c1c40c03600380d80f113501400103180140300000b001c4040d4030600144620702d400541c1032100c10500680141e0380042e0701042c100d05071505185d00c622075440721010344030016540340c1042d943c880106541c2020380c6400c80d071500508910300942d99071031445440e0100b01001918a82200500042e580c0801c40c181d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 365447769 1250 365446519 365446537
    0xc0f020d0f11030711030606040606080c0703092403140112080309031905211618050603070e01120b0d080c070803040312080906010e130602041a03040b0c0f030408 72
    0x4542031160b0140e105056600500e401c5800c82e0b280d00c2c541c1c619041c100429907005c00103843c1000300500381800646812001401c08502150006648040610421071500181100481842c0c203000d40001c000351121500700010000c1d14000040720750710198140745049a4038484200250821520741c0e21003944020125903e82c0b000b0400510019601e003203400d138003111540c545403113004c3c1190400a42c0d2803080c40c0000658441d09100c2d0055955252800a0143e4103201600c8241a880c85001d0415684440d50103240402042102c1d07030003040001521400b41d0711004c00c0340f022105d90044940e43c403440ca401280c462402400207007000700804c83c041c004001c0300e4110350344149891542c0c1c01504102c40091100101043c42034010100b540c03c81c40140149c1001c0d03051400c0d5000c0d40c44024407d01c80070b039504403504c0911640713a04413009001624401e400510512442c4821584152400c44000749401c0000e00314042c0c100c190f0701d20041000c02c1c1d510355121a10380e17900f103070030510007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 365449019 1250 365447769 365447777
    0xc0503070c09090c090e0c040e0a021f0e0604030c06050c10050717090607140f070b0a0504021c110409170a200c03030702060703170907030203010c0f020d0f 69
    0x4050106040000500c01803081c440045031091941c0f404800c1310006502c03d01300242003111183c001000403811010405041d075002a6500982d0003d528206404101940000c4085203000c2c00041408140b10701440a48030340040c042220284249446640b001401c000c4c0012801d0100c64441c04c01080c0c030951400480381040811441042207500a54030800400c10001101120300c2c440031201c1d03400308038100501460b1418100240c151a1540c41b504c0070780d0400907960f14a05000f00507541d085401c0495183c00d45404990000180816603080c3c0c818180101d50070b01045882c240490800d50143c42c28040c15060800d00000d8207840c81c00300c034072203100c5151607182c2c0610006860300c580c00b81d5505c0e690100c551000920080380542c0e01100350030207000c4070081d4600000b240e16260b419101aa9181c80e00e040c1201d80c050910840301c3c841201323130140703c1c02a0000400e0300c2924000c400030043d40e04501002c0e2107003400d8821000240e080084800c600c0d6004060101c5e0500181c20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 365450269 1250 365449019 365449027
    0x112020103060302030f0a060c110d0f030e0709230c04120f020d0602090f09070e130b030303090d020706020601050a1205010b19030b0c030105180a060f120201120b0901060c0503 78
    0x40002d0400031b021a1030800317079200d814001e0070b000c1c5a004118051000d410064000c807040041035031a0503204e802d010a00000500f0107100d1882303940411000240d640a035800700707407501a4000176210a202c042c1c00d5007840380d41c220000800c15510b41c0281642100b41e032419140c00b18489404200c1c0109403040e01c48414054096240c0d550800b5520744528801a034440c038803401c10036000d034900c040c4c501035401030041004640e0440020701440c1d00440c2d5000c0300764120103900c005062020309094050001005000c500d050004444035503032503d07000d44411076140d1308100e980785005d1080c0c0d903100c03041c083d081210341c03a0210541d1207507010720004035542d58004042280c042450641180380451040c0400500611a1465821a441801e46071955240c03400003454074402200441800c441000402c070321643e144c1c041c0c801000306031007144005582d540d458061000c410020b9020a4040040041e000000c2c419410000001000400c2990a12504544580c0450800c503020301c0104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 365451519 1250 365450269 365450273
    0x2030730031806081f0e0a0b0f0d0309050a1508151c1103010606020303091b180403020a1e03020706050f040b1201032a05041e0203070f091a0301120201030603 70
    0x40805002d0041511406005d00700701005ea41107010b0f041d0440150700704110203001590210040340c2c1c10503202a000300b001c080c0c900026152040da5070b0a142d008113001c046c0010140c2081c3c503d0100c03441201c00a07a5169520b055164010b001d210003000070760200e00140d9204031f080750b004148000a8460100603032030710902650030a0035802901c1765011100410b00910342401004084d002d14405942103080502c10706036240950380c0c20f038084160301e0a0300c0d5515101c03a0038121740c104c0741c41d4064000707040c2400c0c00394481d102540103452500380150008280031341104403510980e0f00d58010b00c4030624021003200c0ca50060032007464011010070001440c20b0090300030b03001940310b80b07180050551451810f811200000c40d01400d0720500910605181400f4051540465000340d8010541000003440410007040141e40c41590368804001e001c11140e2003641a04248031139182c407500103441d81c02c120a07509262a003150101c40800c01403000c660038400c5000c00d0f41c0b0606001c10031036129 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 365452769 1250 365451519 365451557
    0x105161a0103020a0b1218031309020304120c03020c0103050c04051905030105220807021c06020c060105030609030406031107080412120e0901120215160203073003 72
    0x4440010031440100184150700d40790b08507070020305016821038600a05446034183c07404000300807030103007403401940000080091040f40d07c01d54004500070f5249860f80d1051000750401d64003030702d100014501c1e000b10030340a030315a5200c45800d50014443e40d5249030044000e08402050104c105009000000c1c0640300c0b44011018050f041981192050420052508450340181000ac0e4030b5081c3e085041c031003200c0003480980e0741e0020182c0350350324a20b0010030507403054014001450184002101c041c851680e0180c414801c03950b064400c10713666001050342e909016210419070350000c100c2002118007a5002e144401c14000705e45003021035070b0b140d4800b943c10981c04041d0641c0e00302d00e08410402c1d481d62414043c805414001e60000e45200454002181405241042126030400005554811b54411a0303420881650355842e0030a00f1401c1d84001448812800b9206c3d40703201003804102d1941e079584084401c00e0712440c0c43c003100300c50011110f440744d0540c2484106000702160700c2d15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 365454019 1250 365452769 365452793
    0x5130c02070f080a14121e040302182409070c02040b0604060201020a0f020105010602070e130609050d090b030c090904032106060e0d05101d03030f0103020910060e010516 75
    0x1400000e8003131280241001014001c0181d84c554040c3c011810000b0404809026644000070030440d680c004140c0c4031420718030340314981019622074001c400003010690305581461265260403140c54043d241501c3e850344809862008641c842100d800054909100e41340803c1c0c0c0900081020480b841242c011a40d5940315403c80030050750001030210b1500d40200741c42041499900c000c00240d03151a0000b91501100d01030100c0d03e850301d00105488546006100500c00e4201004019911079860301560746c1079203c6800740421122800056000c802c01c080d40d00c918405c070703c01464200c10504200c005500100100d0038403101d10340c0c1558681c4258128081394503500343c00170705503080803030241c14800740c80241e501c2180202288000a030000c9400340c0079103103210010407034a000400c03409440c0f500503803800341403002008018450100b41240c504a034001c2c0c072243c100ea155004001d81e00c0c08540031741408501c0b07000350707105203500c28401040faa020502c0b00c1c007031200712652004004c180b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 365455269 1250 365454019 365454029
    0x9020a0509130c030b0906060108010f050d062405011b0b0408030c12070e030606060a0519021c020105042604030305360909010c0212030613051e090705130c02070f 72
    0x172030904000204104000194000b603090a09007117943c0340042d092100e4507907000c0c00340100307103894040c01000a55082401ea003680b4001009050b82c00c400b4240c1088418403d25000a45042001158800150f500c240881d04a00d003a1407650350bd4403240300d0750344007620320001801c00f003100b0740c40052411b41c09401079486580c1c04900b403840c0b41c10140342c0b0300d0160242e813144504101e0380c450b458100c022640b0f520001c50300d1001c52222410b0503814007400c442030030300310051618644001d42d419070025105034400c2e00040150030588030140038590000103564a034100802090000c84c1c05140030f48050b8502003149034448451000380c521001541c0c80812507113405a007170450794036010201544c41075150f00200072540178028000d54801e080c0c54820104240000400c01c2a140c201a051003401c8808080c0304034100403184d0748100456150800071419480702007102c1200104d506001c4401c000c001e000e040310041da0840080c50b000f0318000c198489c603040020200c142003c1c1c640102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 365456519 1250 365455269 365455283
    0xd18052b14060f01060c02010e04060806102102030307080f091309140c0102030a0e0109081c02070611060408090103090f150f0b0a06081305030c070302010306080109020a0509130c03 80
    0x1c1902080a00c0c044001c2c0803094a01c24140050003482d43c0041c00fa2000d0340c09203810f2491120305004100280240d4004940c1405050104201c0300480c40b5444202d66400c944d0210b054060341c6450041111240000d61640003084004003107404d21018044034510000d00c80d24001d20140098006041201d0090000761204c0e0400c061018080c03898500302000c4024103c0c151503100004d45910481d0b10580074002d10300344505043c0d100e00d00760780281c40d0240c1150300030009040d00840e0292101210401449030160100f59184500c9030100c0c0705c070741e8500400c00303915640c0d13882a49800207080c950405644010403800700703414010080105000d200000d80c9241081d042c3c0301030301c44810582c3c101900380740405800307441340b141c00c0c03045824501c0c101846482e19200640c1038094200060140d200100d2940c6041c0d4003c500c2c0b5040324400d0f01e081180b0f90307442c0c1d403981c2600c40507140a5444401c0310340811441c10543d00482e8402442c1601008410341680c61622416a641003a5807035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 365457769 1250 365456519 365456543
    0x2060f1c1503140c0a270f020403050610030804140d150b131802120a080a020c03151e15060f091207080a060906061d04050d18052b 58
    0x80b200000309010b038420144013a0038a201c0d94008a9603a030054410500d214200b259000102e018104589007208011a0240031810105440002a40203400240d0301d9000e02c1000c101c1c504010000382d030441341e112050900300791602d210a40d04205440310140c20410380c2c843c15000900380c072401c5612100362400081c040d90000d0500c90801d001039401005285400c11104401000200c4a4502a8103da64201000f441c4119604003140800028030955010072140c03116230f0086203604101005404035910400003241048440500343d5644246004040d0501c0d00000d444d4062580000c07500d01d030581201810011821543c0030321903400c050301000c030700d81c080780c64641006040e0740e08800041140b40e0500c0c1c0800d481303102064000300060b0ba03846450f410040706400c0b40004046c8a0a00f40b81c6442c04014038061040848003220a401040c101c650518080c01426070a000106072000c01e1904180500c4107081d1050000a11954441092802d03d6507255030001c0749441804855a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 365459019 1250 365457769 365457773
    0x3120b0a09140c130902130e1305060c390607030204080106080a020108061c0203010516030e06040b0613090611070213020f090906060d090501230402060f1c1503 71
    0xc610b60140c40c80c0e001550030070401034110413008101090f68034914005944050f00603c10003015280c0c0c0c0070300c1d001c204460800900e508c048420901140c020015580282c0d40c3ea0740c2000039100d02c184a02e00320713642c6010020f200c0aa4100c403020f5010456007640007280780071050789404005c4031200c00281d0005401d1080c40000e01030304005021482c004c0c240300d0420303800030301300e01c1000303080074001d21050b0b072501e101815804201408c00d4003e40200083c1c10081c020002155502c0c0d14040460306014444980000010741d50740b240d0b4000f0310144a07034840b00200f0500141400c581516a030312504441c2c00710b4201e1003080c400c054122442c07580e41c1035900c144100c002c0b0100302c0d0300d03d1500c14000c2c9a070805000c0c0c11594481030880314511503980d0800091030f5805401400031401c0d1820403520300b00a01548181b42d01c0c0100840c0400c220580c6003c050383c582c080360000e401c076400303201140c0d2051241d800340000d07018501016107c24400e84c0e01070300f281da102c1043c0480c01e64000c81001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 365460269 1250 365459019 365459051
    0x1e0d050f090c061e0a0203040b1c0b1c0b060303090303040f0501170c04060c0c15080403080a0b06040302040e01060e100f0b03012102060d090305091008090a03120b0a09 74
    0x3482d9081516000c2c2002c4032682034200304100030015041c100c00c001910b4603960b209100300c40141001250454943d03503022503c81085042101d5040310500d003140d520918038000550103410901c14407404030340102c540da0810742c0d00020304250b03010300c0144007091290350140017030000b038071940010030001884c0c41c00040414990f02c00404c0c5615504091280d840407800071202038071018142041200400c0c6042d200300310441c0d008061041c002d88540410584c04444e541c0501d009545022072500c602d090b600842e80308980c0c65520504c01c10080005007059041414503040c844000982c030f81e92003402d8461414200c1d5010505d101c0c0c85418401c0c035910700d1f1964050820448083e0031903050807a00301d40500b0000c014040304111501d000115590342044030000c3c803c55409100148031403030b0250450700254036a520070704130303074003561103c6102d0300646100e6441d040041c12055141d0b1001d56050b0101d83d501c0707441e20b03203c3c24846010303200c25860f040209508100051a684080d4070a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 365461519 1250 365460269 365460283
    0x2010c1b032612371b1110050c0c1e0610140f19090b0f040903080c160b010311040c030c08070f2a0209010603060501051e0d050f09 58
    0x1818200b0180101c44a2291110245030f01020452960300c0032183c0110880302d407403030041002c41000800011000d01c1090382c005541602c0300d0385c0b6040c80400301e441c0a0f60f00d0916440551a40e5208a0a2282c0302e07006421180d0046209280705181ca0301e1075035402c1c20f2402d50310000c8401c030065901c40f114103008101c0140d00c40046e40c550194117081c1402e40910542d5522124401d2204180c071512580c0e0720181801c002403e555407a100302c1d90340f0040c0740500001900d1911440e18a19800440d050070300030803140c0c6506554920160b95102c152140230f030880c03c2848030024100c82460001120f00b0a404e0107103006610a426000c1201e040200b0390b244045034a04044c141600300c2003040c5c108154540003141400c000e100c2100711a8112440c08003030b00800c3c113a84818a01c4030b80741850031180c00c030b00e40c000d88140300241c1c1ca48034198180c0f003075032051500040d401c0000f0f000802100d0480c1c1220030b15240501c1c50300a490012100340c50064461404400400040c0400210200021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 365462769 1250 365461519 365461583
    0x3060a020405060304120315081c050c07090203040318030c0306050a0e0a030f0e0a0e040605090f070902090f0d110405062b0303061d0103030909021602010c1b03 71
    0x552601d41440003003580380c0006040140080d400c400c01300e041c00e000c0c0e0400505040c0c41c261180743c40366038804596a91100840800c035460308009c04900036032003032040310a8035114000420115141c01580750096000800960030094030160700c28660380f106090714010760058081c41c42082c21810b0410485c0d10142c00240720f40e142840d403041c01b19011603d181119018281182d20141681c01600c082c2d0410420551045030228003241240340f80984900645c0220740410075962080300d81981d8484101c1074141030351001c20100103108880d002402040009000010001d0884022401403c0001c0003202c3d9848840e03518411810700c0c2c450030340d0104085441440b00c60520203c40c1000c941d900900041d1907506008505040c041d4000c000103010107001a41d0742018000d0381072443c0f0080c08100c00184a40341c001440350064001c0e25404151341e03140b042881c090b80d0054400c0341d24450100c40c030741e0310031030b454400301e4521034114010350140d08681c11400c81110160714004002a403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 365464019 1250 365462769 365462771
    0x907050a03030c020907050f0412120509150a02010609110307021005010506070807060225030305060312031618090609060e041a070905041d010506010918020901140c0c03060a 77
    0x400c00100f0741c0440c1e80420590150f45403041602c8200f02140c03d48500031009542e040c0c00900040c10b001002c550303140b500d00480192641c2d03028050304035114860700390945d42c0000482000b050b0100d00400515070240f11780000900c0598035480c220595010348118020003002104000f0b072260144800488607030460b10802076581032000141541c0181e0001510140000c00c0440401001d03504983c2141c006928144c104211840482c075840a80c41c2d0813000a42080003140190400050341015003038864184d5007503588420681740e00d0011020f6000400011803100c40c4c8450004902c40081c10030000c000c035102d81401e28600a5902e6540a0b10700c0c0111401040081194245001c400e41303a07402412185407961201224448a5a04015030180c584444a11544a00458820080728010080c402e41e49e880c40155005981c41c8520032090048501d108407036042d5500030629810141030100e04440d0000c40c40d022a081000c40e4030084d030201c014600c131850200800d903070006032080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 365465269 1250 365464019 365464039
    0x90c0e130c060f05070f05030301061812020d0204090606080723030606010f1205070314090109170309070e0a0905072313020d02070c0501121517070b0d05090705 71
    0x26910031070800a20442c2c00300440807a0680000e4400c10403111850380101c0d0346440c00a850610b00d84a17482885030300042281c848040d00c054191001007000c40d1007024800a08108580900002420b0306004036030140d0384602c4072000549500c42c0c2409803003a1740c018a043c0e81804800741026030560035600e04141c1d54041c00045641c00107800c0c0e4010400e00e072026100751102410340b9540d0300c20040c00a000e04080070008015455409540c0b900540904904640c0b50301190500f01c81c01e035a800340042404000c255424a2114000d5402021034021210016a10300b940c076407a240039909502c61584440703d5001784402041140c0280c00da042c10045420100300081c0316500442d100107000300305449160350049466070503240354180d000310a555034000c62070107203400b01403401404d0104d00000042048200c26104581c6030a28814403800c0203400d145403560104010032040c5000d1044500220302d40300c010303003c3c02042c08007010202c0e00f401c01f0b0300d026080481d40c1d00950b0007400049 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 365466519 1250 365465269 365465273
    0x40b0708091b060d02121602100204120308090c0d05012901091503060911070308070318080d0204120317060102031903050603010b03250e0f012304090c0e13 69
    0x3000a008102d42250150340e070b035082c00041d601034001e208a2040a0014100f00416071440440c040d00e403041517030944140342c08006100003240124000d209200c0a07600314000020b010f851081d40042c0084101c0d03181001d0f440001d07004507010882103d00d80d4403074801c1c0d1886c020b50302500c14050440207452800d03c055400080a11000e446038104a0b02c2030100088101d01962240c4040d0840d41c4041c041c406425054480941c000b080490000d0305182c00180401c0c460b102e101003102c010851750402c10016180c603030054100040801e41c09600300800948401510011021035101c3d4807007022b40c5051032010400b80304000e00e5541950410068245142089946140e140d00f031803c3c00102500d0741c002003401841c021190355014030074141c642060003013842203244001c0280140c660603940b64580c800c001c1409a030200a0905000018410711690036040b18000c0c96020403205881c2030617001405490140f10140c402ea1240c0100303004940f10425099803000d030841c02011446015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 365467625 1106 365466519 365466553
    0x3020d121e0207050d1713080f0307021c031806110c0307030f02040902010507150b1e011d0120011515020604030c1703040b070809 58
    0x4044810494007440c0a000034010940c1d0182000703500c1c0000f4090800f0310704000700c5180701d090079800690700d80303c000740298401c4016054219480e00381c00a080440c1d40041d2a015001084650003580721900c1e2003040480310041c2942901c03007030408545055000c1d0641ea0390108a03c0c1c005203150f40080585e1110101c40d003502c150741c0c40b10701059500e0180c1d100081c00c00c2d036180340c460058a4181d00c400c15031030042c10280e2404c8003e175580040005540d15040701c850f919180030b406800d050303100703141d101d1400382c80e08944080e0000190031801180040846810003d101c0c1000b41d01c503800d007281001c0119071294000904a1003240a00076a10021740c1100c500f6100007a80341008030820050348068004d40900d485075201110030401346c0d102610001d800d5065004504e240000451243d070150088e01030509002800519441c405002c44819521490201c9065840 = true := by decide +kernel

theorem cover : BRFrame.Cov 365287769 365467625 := by
  have h0 := BRFrame.cov_init 365287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 365287769 ≤ n) (h2 : n < 365467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
