-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0150
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:07:26.022286+00:00
-- url     : https://prove2.me/submissions/67cd1c6a-1095-4964-a43b-7f58df0a1c55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 26798567 ≤ n < 26978423 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 26799817 1250 26798567 26798573
    0xd12080106030c0906020307081602060d020c0c04020c0c150d1505040f09032a0f030509090f070f180305010203010806010317042102030715020115050a06080f09010612 74
    0x554000d001d25070110f803070120050641c41c00313030001c44211130855005510304a450741d030f0703452940c10040d024003180c040a6403010051ba550006007125100b40400140c0741c0c40b048031900c0c9070030960403200f405144100b020403404080465409076204082d5401c4e17203c441006aa400c540c45166800321945107041c60080b415030141c264079007224801c03682400050380d038422140c00c98418060060109514000648060048401030940125226840460700c03003542c945c071011000c1c1c080c0480002c0c00004460440d890040d44150f001042e0741800407092800c40c0014001141400d0a40103100c04649040c1c4101c881c01901d9020b0341c1c0c0308000b075489503984c25006a64440a01048031407000d141e08400700c0240050940e81201c0440010880d588400504000709003040c00c0180d070035000d03c1c580881c12541200145a403140541d000090702e40b21403c010740d4594140d0002841241c01c0341082154590003100c40d5000082180203086903126900140d0041030541e02918082e03040c0180c0c0418 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 26801067 1250 26799817 26799827
    0x20310030204050915010612060807060903060c08011a07080c0a0b01050102100507080a0513140313140f100c0c32030a1401060302030a110a06050301081b0d12 70
    0xc0320701c02e8509000c0c50300c48400154503400d03032076903280c010310090740104074140c4078a03000d030b100d06481c44000540a031a45d4120341041a1500000080b820051042080002134803900d034401260f880c0c0382100e541014119184c61030640200036000c1c50105607201402207880072a00740440c1c520480e900045213150850048900740701d00c0d40540212502025001070b1801054410900b5070382d000c401e03580e0700b00c3d030741c0c01031a01404038500c81c80079040d984001303115100881511007140c0021610340e01100d480307141c0c1103000e42207088000482500411203031a03141c202418a002116a50890545882d048440c074104a5003c0d2a400314880b000416400625955030080340b10703c1e480f030305007000380c1465030144085905c0305d81550011034100c01113403110b1142c03038850481c00700114204d66a0340001e86081e100031001d82c0c2c41c13205c1d948100441e02d03148022071300600c16030a20504540c50402080e0300c800040a20702000d0000212a03607050303450300c000e601c0d1960320511a540c000156100141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 26802317 1250 26801067 26801069
    0xc010b06040f0608131509080d0c120609060305030909040807021c0201020c0f0d030804083a05040b0a050402040207060507030b01030605040612080706020c030406050d0c0f09050405060d0204020310 87
    0x1c50f2104c004141000340d100889100a6049500110100404c0781400024480c03030000750b821500c20310403119503142c203006042d800c0780190364072000003e816801c842126039907400621540e1815800b040025004010745c2e0030010100c0e044e010940d1903080041542c490020005d41c0685410b0001d20002002d040005100303000303034200d42d48100444207010003080e9000b0b5140e44200c02c03c0c0001c0020380318244080e0301c58450b44429040c203426249603110303920f00c555001c0f070f06041c002000305912140e040c40083e07a201070b44280309904150b01c500d503c4110141420f81c000740c4038000601076450715011241d07000d03400700d01000145005035006004000360300c000c60002c0e041081c0025986840e0083c0020b0b00c08203103105500c0d41140d510b401d10340e8044075080320f041c0d4003841400c401507000c2c006000100302031307151507a03640c1410f243e51040f101043c41c2401802a050140004980d203e41d4800c01c2d034030180c4001500d074445400007500c0e100300e080c0003544540000f04000a040c2004d00b114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 26803567 1250 26802317 26802329
    0x60a080a0b09070f0509041203140a0605031212160e090408030708090109050601230d0b010501091d071d030706110705030105060d08090a1701020a0801060203030405070603020c010b06040f 83
    0x90851515031446040c3d03690344d807040560212003980030801140084002d045055401d05002841c90f4810030b106501d494202c0344840d16941d901d00c204954202480010042c54401444030f2070100750030f00704190001d01a004480707018109460220070790040780c003d042181c005140c2c07129890145002c020076801228540f001035181f5011804440050050300303400c4e42c6c01300c040c00040c0e00b0304941030310103450441d050140c0d0824842404103501c4003035401110318000e90007c2007035810303c40050b00302d100c035602000c0c079885402c000c0c0700d940251349201070300282540352800008e21441e6018043c2c0d01d251440b55807500401c0b00016245410101d00c200703030300d03070700307061381c10ba00c0ea80e004141c01c8480c202e40c5150172241510540700010b807140000e00000200601c0c260b00540c44c0c0380c6c0d280c0c010040e400e07560b60980d400580240240d41081400b401085144015855440c050380c40980743e000510a400c141600802d04072150202074002001180c4007800107034803240e4440114140003042d00c4ac1c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 26804817 1250 26803567 26803573
    0x110f07030c06030605121203060105160c0512150103030503060103091401051f03030503180708060702030c0610080a060e0705040221010902070c0e130f03030b030d080105010c0803060a080a0b09 85
    0x4082c24040901e06c0ba5a0510b809081140d00016440c0b1081e440102414100507007006a01c842000c04072080c01090b000e05400c0d4240c9081c5018840711f2042c040700d01d4a40c0e800300702003210440500212506480d81840c001e0b48030b0321014010b034094007109000a007408619062689848415440207204025109118529101c501240c3c04240594003010300010820800680a1018400b100c610011200300b1130303040b50303900d2225a05040041c0c4201f00103810004041503c0082000200c0d0040341160b2042d07642403421005c10f58955500000904681c6c66040703684070380c0d20906c65400185800b90007550346000e00b500d00c40074001c00c1c000c0e03001922010000421140102d10a075961940d0082c040303001c6500784a00c1707070701111004102c084104e00c0000703d400000d00c004544540c09202e5100400c1ca540110308050a000181019004011201004100c20782c0e220383c180c54050780007195280c0e25203a0101050394006550840e011510840080c0c104000070000c065210355802c3c1c0039 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 26806067 1250 26804817 26804819
    0x110901090203011a130305030c0a03030609140402040b0d02090c0702090f01050f0d210903061b0503070f0201060308031e01090c09060809190b01090c030b060a110f07030c060306 78
    0x3651040740400e0041d903401d103268002e400322400b641002411a010305009040d9503c0e82d0390749044c5954850503242c1460307008040c15808054040c01210040d105007541800000c841e504200008240148081c1c883c07a15500410110384400001c407041e9a00a010a50545005c0084c403a6651120808900403211140058082c1c0c90b0040307104d05940e0010410790304014800200048030341c40d0714040d1001081b8861202e000030f035004020024003455103601103920701d5030800c1030403a61014071403242e20080d45001c1440c60740c0003045980c411500d0410000d400c100308412401410540c100400e804800000c1c050039100c80c20503454907140b050b01955617682c88000d1442032703490052586000c0f54018000740407960203043c8a0340d00100b4441186d034160350400d0041d200b1803892038203489201d042c0300140140c28090192005130303552400c0078899a514a40401c144d40301d400303100c1040001e00038aa040c102024003003280c18140c8401101c14507526424500c650344540d110710f001083c54258 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 26807317 1250 26806067 26806079
    0x3020307020f0105090a02150f030703050a180c05011101060807080606090108211803060403030f0f02040609050607060603150506030c010e01022e020f0706180f030309050a0602030103110901 84
    0x713414455484c0741e000d40f544041079070a0103d0390740c2c9400750103844401032008101000383d003000f85101d0190303030b900403900e0304042840c030046401c124941001d882c03ca4a03071002141000840000b154802e2800080c0c14400951241c010445500506c2d410301607108005180a0b002601c01d010340f00890f1111080e907a0b03100d000f0364402d500001c1c26611803040d503c1c100718285c108060071844214002010078188100006400c1a8048034100c01081d503c00039880703000c060344078501569076814411482d0a0a005002d0080040d80c4203407842403030005550020848a070f08140010340d804918000281601580c12000d4601219218024402c1c1015041c2642c892000203500d0030040c5c0150008402c00c4003400310307004424040f805481c1c107000c41c030500000c80348000e103955000c0321162611034156107094030503561030790640101606016034200110b2104a4001c1c04039030300d414001026419450140d04100d020f9002500300d500c040300010a00200500c000010402198446281c0c0e803109 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 26808567 1250 26807317 26807321
    0x207080d0f020903070b0a0e090c0d1505010e0f0607080a05180d021c0606080304180605041a090403090f0f080f0f060112020a090903170c120601030f1b03020307020f01 74
    0x10b41c1a43c59171000108002440c0441c00a0214450916109059aa11201145496805a41c0c841c41c0d18800a0b02c9a10b0020922400c0184076603620188092450540000d140d41c400600e0584500385c8000724400c56590003084405c1c41d68420030590325801d4950025205030007420010030000301010a45085280404038290040d138010030301529002e260072031000703045540d0411610b141d40c810010407440810805080101224890402d012040d072120301d041e111035510007400755040002040521810200c0003411910580d840c03c01c0b07a90741d05048600318001e03403100b1043c94052401240107480b086c074190503220302d0003c072058a01da01c2c01640c0e80c0c103550b0740d0440703550300020014030001848501d603104850000303000901d8652180490004c840010400320042840c1c5400000765514400031182c0c03140f1031015541c1410000b0482d4625500010601c9040550380d51040b06804880e40c84503031083c003403410803513041030b818330054000c0d070043d00d2001c0903103e81030800c080a5414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 26809817 1250 26808567 26808577
    0x403050f071d04050f070b030a0605040501050306070c03050f0a02010c08060d0f0b07030b120105090601050a03050706230c010e12040807030b04050f0d081501050a1706060d0207080d0f02 82
    0x102c0703074055036140c404078400309a03140600121514000c0c4600c82044003810842d0740c004d0244186540e0366410081010000c40f0441c2d8402400349080c00300410040d68085100c5030b03c1f000c10304203203086c10b4181c90107c0f0075100d1912290038000010810100381c41e41584804000413407030300c4442c1107445140401544807000f8070f009007070704000743c1c50700c0004003408205074108219041c0402c031016800000362009414442440c0c5a039034544c06c2044c0e4410800c1b15a0040106403020b05180b4115181c0c240c41d80041d0244909225520894101680c200c44030786400034101ca10381030329041c0b0345030814040c1c40301410181240c4582454000d000c0d801004450880b080e01008041c0503107181d039103080344032006205580c3e60040441007802c0f4281840415842c1d496903503000c1c01440c080d041105820107943c4454100030050014001e2103030000200744c1e01d001d943d1f10003903850b5910030000d600c92061591070082e0307500100710b5200308041000500101d52074100b0138001e2400c6483d01408a000f6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 26811067 1250 26809817 26809829
    0x4050a0b0906040b01021612050c04060302060f07020a050a0905090d05030c18030a02041407110604030504060804020a080f0c04061707030b07050702030102040b0301060e010903022101090506010b0403050f07 91
    0x40307804980c40345080e034400b160041c818015180e0202503404e40d071041ca071596000c0880c041690f100003082010501400c20301c8201100d0030011542940c022a540740902d800c1e1010322140003a0207401d642d511488003000300790041c0300841072500ea000034006048240e070781c0c8602e84900300d4507555140c000c1e0140ca118101844216081140d1680f1b0801030102c211010b6815004001100c80962200d015000d2002e4640e85c02d40280d003001240140000d50f0324542d68002c0d0091800c0c4400070b940b02040341c0c03c40342540303807001c4182c44a000140c0c40a07016801000a482590180544600702060080031510304032410440b03250396504440f464a1a504800410341107541c05000140e403201c807098200400b40b400b18100201580030900b264040c0d00a1001010701200400031036501c101c10a04180b000e29010940c5031840d40803883c0510349100f40c501c1c50081ca010001c0b000c80c02d40c02500342030b030480112445540d461070710300e105910600068030705005440d01e130040080006901c1c012150 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 26812317 1250 26811067 26811079
    0x60c031a10050a0302190504031505060f090601120e3406030e0f032115090a1a0402040312020601050306190902130f1a0f0105070602090d0c030b040204050a0b 70
    0xa4585007281e00f030f4800207840e01419400e025810007400300c0102c00b14a0049603d90955032404e40c00d00b03420001500b004044103500344401c120f002c0e00c0700d09050300701741c1040e40c01180d151111001604c0c0340e03c058201200390b03482c1200d40001c2d5400010300b005105849a108681301e9003002071030002c000b100700b01c40800d026480c402c0041c944a5400000284a21815151000503d070b0030141180d02c00020014400c5154002c10b0541851840c07007034009801032036040c00f002d05040800e4419000400d04a40c0ca03070795991145112040d41c03040c07808400e0003842113544540f030380707001e080c56103000d02d40a0040c0301d2440003050702e00f00081d4030350040105602c07080301030103072440c15400b40014100403038000f08070b0244c500320421240a103100013510782c140415044a40005803a45d460004102c0c0e205c1c4001ca104800b40d40d8101c000c842c0d03141e0f0403010160351a10103c000c1128078800440060050840c808004140400100942c0c01030b44200c034140702c6a111054030300150345002051b294049 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 26813567 1250 26812317 26812339
    0x240a05011707020106030206030403123206010e0a0305010203010906060201050402030319050912060a0f0c05070b0408070206070b01140303121303030906020d020409110309030708070f050a060c031a 87
    0x1c40080c020381c404428400402c400c0d407660702141981c0c0041d1402c07400300b042c91034540c00c9182140180340040362141c4124400003980f4809408166030440850210b11024010808a9110790288003408402401b142010307952450064000d50092080380011842c0403004900107106024090096400500440c1052100392041800741c0d40c4a0012007404400c0055001ca600c8038401040d064101d1405000b0915244810b44162003103100b440d800a07203424600c210b219000070580351710b40e0f0051000d15036551249401c22242c8100c0e50080d50060010482070304000400c50510b040c2d503254040001007404080030b2592345d00451100c0100a401140081c444a80302c102181540c0e00910300481c07070007a2900c8000413a4004c080400e02030750001804d008030403803805180991107030310a0151540c9400c0007a203441b80941c4200038004400000c0031414481d2140c514407401d90480192601e48005280ca8402031029610b00d802082c00c20040e0040f4891070002e031a164040544078007004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 26814817 1250 26813567 26813597
    0x12050f0706170a09061e1a090703110c01020f0403050d0c020906010311070b010303020c03070609080303010504050403051902030406031103090703030f0c0c030b1803040b090d0206070605240a0501 86
    0x10b03031005201503c4607071380f4109000860a00d001c0c803110000c0740600321b142d2151420403c001d66070000d05200c0c110303410548249058030f66900d4140c2c026014a40002c0c4041c4404800e1528030485050307465075800402d40e0100007518000a0003124850012194664100081a9030504203460043d51100c1110006403075540645c2003161030003152100c1d0b40c942a5541c2d11107202103c01e0304207400503400504801c1141c141002007c01030140781c00c04468403494409040c1d85c0340710500981d809103813a00c012404042c040e10944450920701e00e081d0a040303d120303400942d250072603c41c0e880080d0a140c03a0501c203403110f6080f240111034140140c805e19045440941d520b0028001c07c4c002c01160804100225909400380400b651103050907401900f0b000c43c2007504c0d001450300b10107582d00204001c1003080e1048040700c400102c107440b4035a00542d0381c00020303601d0043c00005480103060004024000b007000391429204a62030304042880414a818400482240e004590110340b02d50b004003c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 26816067 1250 26814817 26814857
    0x100902090103111308060717040623180106061407030c1403070302030c010e030405010206070e031606020d09090c0c0201030207020d06020a0206100603090809010503071812050f0706 80
    0x341000c1818081080c03070b0008003540e5203520206035a641c02030802414000c1c07030414041c25810101303070701d00040a45603c100015010b0303009070009225503540d001c91044009804407014400130982003034061440d202d40c0c0205a00900a10b0103242d51810002007401405503003030685907044a11071908190b00ca0f0b9050360440c500e50410785010402d0b40041e908980c04100615032a4401c2c3e018503121140e8401441c251140076071408a01c0e042030000b0f00c02030f41c0c006242c9070700600c41d240c0081c00a84010210303007014000388020760b03000400c0700c0100b12170b0340000f181c1100007200da4031049903603a10310224040b40c285034242e40021340100301d00c902541c826005424030340e00050151404070280e50341e00c012680181c401c1d0000d46c0290081002c0000e181c00e6007030043c442400e003440490400e0355114558441c0d20012414024040081402c180c410780003403800001040b4440442601c644484001032040c2108840038803941404407440403001c00d00d9400c8501a4030f0740a400300c004144045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 26817317 1250 26816067 26816077
    0x32d040e060111010e0a1502030405120f0c030403120807020106031101030209030f01090c0f080604080304060f090605010f0f060e0306040f02030f010906020d050c18060d060b0f0409050f100902 85
    0x10403c8030124040c42110b00a20034149641c048600601c585006468520b510690441c09000c125106000f0040800d20101d8a410256044920565140075000c01850180210040324006220104003c03081189803003000045640325140c42c21b02d03a48200c022802d842880c00001c4c0700c103030303105280605540030360080c00000000606481914103405526404c48141c1c0d00e080d5501e0762581d00410955038058244405011103102915052400b51204a140d1102500045c034440e5100c2c01c40000188944c0851021580300c2c80038062075a4500c0300d00d5a0b04450300a05c4040484d5050004016014071140100074201501502c7d0603680c5855449681c0c08000044e60503029001191f802c9103400c0c40307041c03c0c8a10401d40141c941801c0c6075038100300c0b90020a040040d00c010080003100aa8400341d000322801c0454105c2d944a92320004d89000d1312507640416040540442e840c01c00803a110050805e07206a4a0208115900c0c0e000c01800721005030b030301110340304480e942440307046a160000c20f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 26818567 1250 26817317 26817319
    0xc02030c0604050106050108070207030b0601140d09030905090a02090a0e0a020f0a030204031104090b04061d0712060c09030206030a09050718020a020610061b061d032d040e06 77
    0x2424510900002400e211040741c04460a1759a40020b000030360f08013403659000021407004040c080d040d56148209a20003070f0803541402040c001301c0c003d501e8054200c4e04058120a03007400010150300e00a03000d8110750007100d10415081001800103506072003174400c0c03031134020301005446141c541c6070200309d031001c3c0c50300900c19000c2190600b44d803a580000d09601c02d15071340040e43c030740c512705003069101103181c1130510403820000b0440106541c851801e400942000707001031030804d4200d0002c202c00c1341d482e8442c0203000f2208001035065840201c0b40300326004600510109146460855025110b4003000b03502c140700388007040100d82d05a20600902e4490000c0f980080d44500d241c80c0b00240501da20003c6131780010ba814812070f4180903190f003101e060a04c0d10b04803418260003900700e0240e0100c28113021011201041880090f421492103642010720304001d4000c40e807081922507000c3c00d9801c075240420041c0810000400300400d42c28410001084d0905052a05201d0024809401c40e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 26819817 1250 26818567 26818573
    0x607180521061e01060201050c04090b030f06010f05090603060c0406050706020d181202010b03070911090d0602030105180103020306191e0204080708070302060405010507020a0320090105040510090c02 88
    0x151031107004101681c001d001c01000380c49040b04424207907808040581141d01164149002c3c00a012011400d0340c0503619000c00200b140f4504a0203c0d1408000081c240c07114801c500c0002160040701c0412030a6a2003901c25020306d43d11728080c507907650343c2034130304400310f0750208401c00850f449403000c1c1078420f118007009032810900b80500403c0e036014070840c900c04440000000200071100c0105d10890340c1e680002c1c400c5981e0705000940b150b6151240000c070503120b0b40080c80007007000b41282c0750410b0083c21280c00c500d0501f0018001e40003402074a0103000c0115005075075100ca40c50560480754018014901c940c0c650401c0c0039041d0052b0303101a112034035443c004808629410300d0b2084096802e00043e02d0728582500c107071522b02d19910548807504852820710140c2c5840048406071103080c20034565a02440c40402d4188009500160401c85001121402860101050007842a04a4140e0701d140d8a6000700400c4600542e61392014801c03000f420480e142c030681000300850074038010303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 26821067 1250 26819817 26819869
    0x70308031902040602100506011106190f050a05040c0602160b0f0403140a1b0e060904110618010801050609010c020f0102120a08090607020601030827061b06071805 72
    0x15007402c0c2d070000e41001e40940c100040e045500a1345101d103a038854024600110100c800320503c648420b0041c005040b540e1400207141c24400a0781c20004807005c00107070411061030500041001080f064504440c00c40d08090005001840050f400f10018207008060764103910304503110000d58803041d111904040300b40f000001040c1c01d1500454400c000d84058400074401e031400944044000784130345041c100b01c0e60240014011505190750080058482304c0c5a61540e042c800c1c3d022004105059100c000003422800c50140d020b00503405410030b803030b01c08050340c0760010807520b8080ca60704180090340300c59110000d4684145175080d091418016075400c101120825685580320b609603201003641c0d1001d000605408215140d40001c4910107411254111356441c80e00c1e00c10312024002540310b0300c180c0078a52005c8074852180501c010085a80c0e014007a0304001030341225070300c00f400703400b8910000e50010300410824019524141c0140c2a107428501044003485000c0700002c0156141d905d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 26822317 1250 26821067 26821111
    0x509030c100512090102031003140307121e0201020f0d090c1505070c0b0c03090118081603300c0c09020309073b060f040903030204050a060c0507030803 67
    0x18641d00c0d01c0c1420341e02e10b607403000000481c1400a502400002a0fa0704c104200070b0005000066030066960241820000030306c0140c6141c654003d03c40e02611020b40c51200e1070070f4503000071810804003001d219101c0e101d1145c5e0000da01300d008180684441c4030042218900c006d42c142d01034805184920100d294181c1c49170649600100c02e00d04070301c04682c00041000502030701c802508001e0580c00005e92401c000780024944901071080394505001a13200c5294100440c180f800d0090150701d03044900705807090803c110100a684001d0b2007a050f0310100c840f00b0561480ca100306500b91580910044146600c12200c2044525043d6512000c0d00b201040d03140c541d00046000d00c3e00c0900400d081c80c00d2050311140245940c50001520300b040507060540c0d08a0105c02c08900721261050b861903988002103220800e80d10461139000f0300d07140c03002c020980c155010784240c1d0b802f5204640c08980340c000c240c42010480c0c20241a50780402d80410002d00101c004661101d003504404030030b80d0401d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 26823567 1250 26822317 26822329
    0x70c020d0b0a0204080f0102190c1505090d0801060e0312030703141f0b070b0c0901050702130509060105060a051801030b0a0b070203010b060313060c0513060206040c0503010501060503070509030c 86
    0x150b054a03082c2d800042c1004104410003010202c4880c0d50300031850308100c00000d9030a00e80e40d030825805c1c465120191410310041c819903032954a1110301c2840185003035044240c49102c032401c03490109c0c945000125400780325180501c2044400380040c8030074054080202c4980c0c000914140405846504070b105804032780310703250300510180c600c0c00030307000039040103003840085c0e508043c1913801c040c0260b8000c204841203c41c2c1284070001c1030382e82c64210a0040310b00c0d00c9411000b0b07400580060307621008a1160340228442e0601a00355001341e41c99000b008103610a583d095000a042400b900240c0061a4041000c000c01410000781c00406c00011a03100d911030f522001c045080450074609600b000e0084540344181125820314614001e007408421340c0360030303401405041e80c0700c0068031094020303c200d80b000140701e0042c01c0019521000250b544804071801c85400c900d07000d0000c2d880c1014029036041c0c43c0d840c0c4440f402c1d65104002124650800d9040c158184103240302d550080d2100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 26824817 1250 26823567 26823571
    0x203010e01140a06060212031503070b161a09100506121204140a050a0603050702160b0703111917090d06020a030e0a110f06040e0c04030308090703020108070c020d0b 73
    0x2041c01d19005140080e0f004044803150b921020a5410400b10609000041c070120703030780020030f581c035241c0c03805505003c64a8031042d5001040070000003d2182c50201001d210b031b0680c0d610800c103540e00440d0600b504c40780540282d40c080016030007216410940718040c1c2001c2e6201e54003420b03400034141106031051030601c0640302c130300719000300007400d0001d8800001e410380c6108041d54480212482c080224003c01058414101050795480c00300b03d402e0301c06c1c02040d88018000e0420701295850303807081500c542c00344208802242200555040680e00842e5040c90541050140f540740500740e250103490a419003a19403841008200c502c1190303840790044c807400e0b40070b00c3c00103850341c1c9049405400c030380c103034030902202c3c2d40000031b0a00010ba460902c4a0311072800d8540489410f02c410115208d4029600201e01c04c1c0d105004114801c04500040c20880e80a9038a0050980315040810384403280350102034005130290300010b801ca0701654003005c82c14030203041d01c6601110794a80303154260003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 26826067 1250 26824817 26824841
    0x30f0105010909031b0b010302060c1606050d0f06120b04020d06050702030406030c0809100e01020702130c020c0a0e06011b0803040c0e06121b040608030c0114150609010305040203010e01 82
    0x78980c3c1580606501054880e90321038008041da81291491b03c55204002c01440024032490340028400d407418001d00804040e40944c01c159031030076884182c040d0440e0001103024a031549400d81080c000d4440e40a414215425084062040070007900d48502c0c0040080060344c0141200c8050400200540308140c03003204c80b0380c083c43d1180d0030038030010180c3d541140880204464001401070500011450303c103030090304a80001c0c0b4092210406029000381413004c4e500c024108402006c0003c0b0785c105400c4040540d00707440c11102480100400c07008a401908a9030020000042c4e00717501500034a0b40700880d0f41c401d09000c004a9070340081c035a00c11102103a03a990001d00400400c0d100c04071701c580095044405c031510100b001d10b2260385102251000101d03e83c0b040328500c141e2076617400303203016007a0042581e546244081c3c4c4a8060150600603e451035038400000c0c3c069104004c6d8200e00d0307840188414030300150640110302070003005d807090340e05540c0d95026021502d024890303c100c54803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 26827317 1250 26826067 26826071
    0x1b08031222080d0507110a03080a050f040c030f030903021302070209060609030312040f0b0f09060606120606030618070c030813020a030b041a01060504090b0a0302130b030f01050109 80
    0x103090709a000098903480c0d540807840101622450018405030300796403986001c8040050380b070307641210454443c40c003058540210b0141c00707440801d141e0f2002d080da100e0700d03510f00306015607240c003e0601b02240c3e045802034032144079000148005200340c42810717180c501915081c100c02e5200d4000480d0029a80001944158009035400440c1401c4000790f62080341100c182c0c1c20480b0040100b9143e10410b41ca1649503002c10000a04103c9546142c4543c030b41c01000040f6140762081161207424410b0303960303180e944281000641c581c585041200c001003d090304101003912514240240b0741c102070509548408400381c4d5144521440da49107128491076aa001410361042c1009032456201400c2490381c40042c030302240c00747e1180760850f0704981d80811a0764941e525400d10461a442d10001210041404000051026032060151081d99170281d4200005918038041100313040365880025000700308448520080c076800d90200280050140a0321560f10b8880034050840d6801d800203a107482e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 26828567 1250 26827317 26827321
    0x61803010c03050106081303020f060a05061f050a05090d050a08090109050406030203030909040212010e0607090603051b0d020c0601030f170703020a0f0c2418060504031b080312 78
    0x1160901421103a0501d50404000742d504103480200b036064004c0811100350300d282c8021040500c01c0156518450058058440d9418100b5014010b4582510214800c521411101250900c0030f007019141d500c0f2a00c034030b2315090407244140c80580121712613690211141c0800e80100300d051058044a51044001940d0398403150005440b144080d0000e41c01145028028001070324008111a0b0455003228004a41d07922440029007804070303800101000d509024000aa01100041c068041c07049921520354450304ea2400320200c0d030040750004100780300c01800f544071400910042c44080e194040c050700e0401849c5142d883d040e000c0e44210303010560340001406001c0114221601e0a542e0b0040074505050382e00c3c000c0d43c071240250094600c0d105c0074201c03010410920000c038000c0c150040031a40c001c81000e01140e000180f40c03070000204600c6c400016a9821544840702900c0031501d805003010308588452440510a86121200401c1008046000b410410140801444d4812203203045c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 26829817 1250 26828567 26828569
    0x3080108010c320702180103020f0d0201080f040203030436020a080408030c1309020d0e010c1d0d0618120e060306190f080f0c12061902090618 63
    0x1604940300305000c000898540520112005405900c0d03a2040340d02c0c014140c41100c83c0704240c4c483d01d44025031003120350b038518807085951407150f4100d81c000c98035110703c20707500350a10098480012000380010300400000c0c2c1d900c2c0c0090a400e40141c0050200c80c145510340c0b000c89140b40f03501c5215a00442043c05c100c603482560381c000003890362044010350070000040e40c0035005ca10050001060084040b0010b004401c5900658140140740042042d00a6443e41407600030760180c000b911f84a8140000c4541605050081152240603a0390700ba0300f10604a0350421044030080110364400318141840011032a13a0003002108451030002c01c281c2c400928020303a20440424060b814000000a0103143d50790300410740303600010556400c00103076100c6420802c050341c40c0e08021815035240e5408540044009030023800c41c42c2080407140d0b8601e80e0b60810104066820181d403240d40980001841c08074007111071507010103101005400d1807a070070f0004185410a040e0305541c00700c0b4010300005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 26831067 1250 26829817 26829821
    0x2209021306030b15031c0c02130f05130203030301060c03050909070206160201050f010b0706020904050702030a0e0603061e2b0308150a031103030c06010f03020a08071203081b070308010801 83
    0x544d840c404210411303201d070082519800301003000c4483c030310440a445030040c0100c2d1400307102940204814040301034100100d0050001d00e02c0700750032600d0300c8001021000072108080816030005e00031411a0310b071106c01c91700c20104046c11010804144030360507240e1903a4401d14004c95403600501100d1030501449c0040e454219400402c5a04260500240d94030700003841c2e06454600500c556a0003450a200c0064801d903686150058681010044401d9011000c0c00c0d99140d00da031000113030107403001080b20601003682c404d03a0044084260b0010003190600800704d0306800b400441c4001600c60505914595851050404100c40507405040580c007030100c42d80200c805402c04003008555000c2088808140001071240341c0c1d216003480d0300c0c0d804009940540c0780b8001240c0032503031940f565003c0008584005c038010700710b00c00b0114a19501140000c107940111801840103200703074404441103c00a070400b5144860128282c8a681c0744c1ca0007013014601036125500254500884142 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 26832317 1250 26831067 26831071
    0x507030209070c030c020409020a0803031005090c0403030210020304240b01080a060602060f0907081b03160303020a080310050409030e1908030405040e010b0d120305010806062209021306030b 84
    0x2000f01d030040810000f900000840c0391190140c4000411510a10200c0c00c80c03480e6401c240110311010040000140860703040c81c065074015a40700344180c407514140003850089010040c0560032400754841046499400766500a006000f0800709103000c81880c2404208040441306094850710940f00e1940c0000c143d43d0030003600181001680d03c0e00500030b44559018050411045051001c1a41020f0800011015004800590310001058003c5035440c0c080320f40b50a011303002e02c00307200004040e803944030320490b50550003924003800306d90780e003001c01c0d0320003804540c007420041c00203c2d454a91b48142003034644a42c98284051060301d0402c403000881d1440e409845034400800e1010031400704c02d4504a5000761004109504410000c80c050200a823a0b507411070750b40c1400000380f02035250800e0404100ea1010400746c1d89580403e0344030700c1e040390040d41060f41813081e4a01849903410242200086420009417403090b82d002075003902d18010503c4445c0c0d1550418410b10555807060740e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 26833567 1250 26832317 26832331
    0x4030615150c0809010c02040b04020d061e06140309010906020a0801050f040b01050406140405100816050408031b0f060103030305150a08060703020306030a0b04060c0e01050903100203061302070507030209 90
    0x10780202050341c3c4003000380c03050100103410018a01143c00454480384c10030910540c00800645d01e8222154143c002042c0303910500e0100c1031820844c82c0700799846980081914072903510915900000a8030004903400a002412107642e28010440407884600c05810494030907614240194946010044c010b44641ca91038881c038540b01c0c800c3d4031aa004021101281c07500c4c10304d20401502c41710008181e004541c0507580001e100989102c0301c692000180b03100b0303109540700801515082104903400c1c0158014009950303c20030004e0600c0c1010001081c00e0541003045440304020407036218100403080e403080f0017103601d5109100003550201c1c10b41c2e5003450180c481860030352038440455510740d406400001455030000114240362402d0280300842a0080940300d000c1c00e05141003030040210300421000220b192140003425803141c0c044820080c0c0c01030080c00c0c02661407406034000c1d80040c003095804004e80b40d51910080c03035400034118450050002d00700072499801800405a0014201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 26834817 1250 26833567 26833577
    0x30605060a0e0103050a020c010509030306041410060c0609051507020c01020307020a03020d02030307050a03020f0105071716021903030209090c040e0a02030709030803040609140f03041a0403061515 87
    0x18007442d600c03032045154401e003442c01041c81d896022400009100c0c0c0600002c1c80d5092000308204498000000e5018180540e410881c0b1003041c40501c10b00c0506490070440d0740c50380e41040141e2032140304080842800344e600020300300a02e82e5183d10700860b1500c0c4c01100d00507a410403000302d80601015440d0b030401e0010303601e0a0102d500180c61210507000003481103080385001020741d1010016244020707403100c200d40003104a414040c2d60341240f000507410660802001609d604c0c401d100340f000c10102c1c0003155005803036081c000c030241480e03401140110b2107150802c2903580161042c66401c2402074500517036032943e030010701840c0c440040c200281910100020044001054460be0744515a124010303240d0b1a414000c40d8890803652029100b01341c04010f10060040741e07403112030f42c0e500c600030b8401aa03030b03002e8807543c445d4203025400c100c0e0740050204200c611410b00e2000c0c4600c0418000030f1400b6180c1d0350707144c202c2d2a4420081120056001e00f0703c81c41487c880100e211039a64146 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 26836067 1250 26834817 26834827
    0x30f0412020a060203040b09090c070f030512090106060c020405070c02032e060f03030c050a06050406050105130506030303160306080304080f070b090a030807080d090503030a140408040e1009091203060506 90
    0x50101c4034441e80c031a1030300500d5203270009181611310300d042d80c00c440d51200301c2000d176011509004000d034010074445403a03501c00c0d20100e02a904148100c104483d42c03601c8080c10310601d17808110003000001d14100a0080d60480031b0010390f02888400030803030b03004d079400c0548001b02c41044680013039000b0b50015107140050a000d0800840c03c16400c50340c0c103203400d0591194904d0b0883c104201800010b10541c2480207000401825400080c1601c10542c1e0b00c80039100f42e0002d100994000342c40c0b0710342640080000c01c404103a03442c2d62011140c083e0402140d242e6031110103601d141d00690010543d604201c101d1030140c0014050342008bc054048d0041c00c0c04a0038000940521162000905586000400404100182c8d05541a0500401d000c004502c05420f1041c2c03a030f40704441100110307242c0008422040c0d000ba00c4180580d4001c5c0d103050a0034109040703401c0b400f2018100c1c82540201e504c0c0095201310728050301e250184220390308541c03481d21071800b030150340c929081180b0034882442 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 26837317 1250 26836067 26836079
    0x90123010507110d020a1d01361a0d0506060447060a0903030809030a09090207030504030f050a02040c14030a0510080f06150405040f14030f0412020a06020304 70
    0x50f000450241221401d0300707200306100091482d0210b90000e40f0a0b840e49507185c4c0a29a2109514100d81d00e08801c007006030026091100320112034581c0d131b119240e4140d104a9041d41e2944450301d0701d084070100d440e05000e00f9001880e0303801180c10480f07a035840b0804018407401d150060700e800d07200031420040704180000076500e00080450306654111205a00680c000100e01081090315002070509035072040014401400c1800d00e00094001ca400e001c0070a105c00380c00400c4a61040746540e50005440c10a680a40650300c030000c01d40801509020100c00320310345648075041144948001c043c412068414001592408078016050040707100c030300b480382d000290449a0103608103000141c207a48000751000c2203803158100c03100300d2051000c1c01c0003002c80001c5071400b4081c40c1c50000d000f944000200010b88100315401000060706801040000d134007800700360312184016040d00e0814050f40201040742c3c10940c0140b50000e4010782400650403d2240040609203501c051450941480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 26838567 1250 26837317 26837333
    0x60203060f0d1208070306030c080a1704050f0105090d0209130605060405010303080402101107090c03061502030a080705040302060706060302010806091014010509040507020f071403060c07060b090123010507 91
    0x2103c1d001070003104d40000d4007445c801d60101c0046c5a10120008000f0b03111600c82c0d590b0064031001322401c640f51030380d04102814800690f800c0700e500a0440b00315403a19401152035400468805801003001100f480050303490b006d171184074016903070088400800a003080301c10b60f0400b07040c080c0074a01d00001440400d500c55007940d881070301503d002285584400d0f04032282140301148070355a000c0e0010201d1102c45940140303801c0081d5690a012240d22000380b0401008905900341c0581c7c0304004070700c0010300400310581d0140036424a5400c01e82d5039008140d007944010f00071109282d45507820710840d80c01c503481640008003540c480c00207152682d500000b143c2c0301e00032513880e406003501410b01e51380310320b00702c955401c40035106004a040207d406551400c07042d940c4e24003030241e80b401080c0c520840c40d044060450040040c915030703c840140e42c0082c1c0c040318054a4007516426105101e44800c81014024142c0209481d60305c207011404070086000311000c5410071104100145c00318030340e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 26839817 1250 26838567 26838593
    0x15010302010c0b0c090414090d18030303050c0f03070e120c010c060b03190606030204050705030702060c0d060915050102100e060c0a030b0307090b10050403080d0f18060203060f0d 79
    0x21191003030035180c035005401c1078000d05c07200660150800c120500c15403040e5482500849100c400c43e42c0c0c51800c20001e54045c0890414244e4035070950104102080c880c0d085544c015080a04051506450900c0d00070960310031034000740070542c4620701911074100240d80c511007074540400341c400c502c500000200903401100300902202c0d16140c0d1100c41d69018410944402901c21106c800844286001e501411a505c4140e02c01c0d03240c000001c03445409071040328850700169011b401c403039454030b41e03240760340d04407000e65944140d980301d0119210280348943c11786484100d02c008a001d19100009142441000039611224240b98401103600710000b0745e1604146d42114154030b0b031402c01001c400414484241c10760510901c40b00180226661b84502e000510585280042030f0300007009407001d21072440300401d101402c0104c1015072806a2052142040f8124042034070744c10310f004416420034142c0103481031a40041448694a0100007449a1000580f98903002181507101c8040400306 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 26841067 1250 26839817 26839823
    0x9081b01020a030e0301060b040e0103061b08070f0207030b040812071b08030c091f0e010e011209240e0610030b06061b0a03050702100206310507060206060315010302010c 75
    0x40013828501c3d59082d0848005844129025600e03035a461000812210080c07000792075052806000314900c1d902c40c1d00d101c1ca080c003581c8481119886869007110131030205041001140603120000c00018201540d4038000d0740210407040d22501c0c001c0e0105e81841010b00301d80180203072100710b07031415142e001030004c40310740043d00281c581d901c51034030012503c50300203030a41c8002d098000345201c0e00d010025500c07041d00d641ea03010350444560300545823003030002c0b00345011884506000029103459004810081e10070038610704503c14200100ba18002d00718140b090305074844c0900c18541b201000490b9101d11140210345c0850300d15200c0003d6028080c00d80c5024200002e0301070f03501340100c811960110122002c4030302540c035a017030041c610740054208901c6041d030000b030b003c0e4480c0300080d8207000714039051a0061150b00031030906440788000000c100c0031008428030308007080701440902d004141c0364000d0545864074900301808c040e01d0440c407032440b2000c0c400610250360321038140e0001540c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 26842317 1250 26841067 26841077
    0x1091802040909050106031502030105010806040509030706050708071103030103020d0b1003050f0106050a140a060e03010b18090601060206040317071b030c020108060a0806041502040f0609081b01020a03 89
    0x145499400191156411924240d4140307100e00c000c104056004904503400b52072180200c60403014101c0a0788820300c80d9a00189806000c42c0b11490103911107500602002d00316864105542c1e0344109441c02220718401140700320040020340740d000f040034032241213100301940c80d540c1554000fa2600e10140f00241402d10140001040c404180074904041c5422004845401440c605018068500b5004031801900d03030440016054800300001102190000c1040c1805400d106048903804040403080d40d240d92540480750860b120b071484000c40d400d04400349019407070020300705c40c40c099043c0c1c42402190700c5101008040f90b8050f5481c18647c00c01c1100061984691004844488007000c003c0010b000c5603d82c102059084401000418802c0e258406295502810172030340c0c1300e4030310800e40950084800500040d48840010140c0c62030300c40018205912222400c0100c9155001074010440d415410701c0100c00402c400400320001c50f02c001d41058001c40000c0d103c3c5241107000f001e100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 26843567 1250 26842317 26842349
    0x30e12030907030b040503030a0f020924040b0c01020904180b0708060109030c0803090a060f090303030902060708040305101514220e1609020306090408030a1b110c0306060109 77
    0x1a07050018000950300710b101407446007418100a80c80364020b41d103e00701540b0b014944da40516441c000d0f62801c4000410124a01841869180d001c040041104d00da0803420000490440c84d00006448200311010005848816000900040300d4400c1c10500126802c004410005003c80380b0103580400d2074034100f8003a840d04401a5000c040a810007400c0309403540010559207400005000162000c59208000316552003080e03400035840c41c40c40d00013505059092010902903000990b02030300c0a00150b1500101d0307200c9003001d8115400848070390b08a40f050144031401401a0b038200200c403200c401c45c182c41c0070f04181c00c1c08208802c1500030b0408002c030300328114822a4000398111840c1051000200003483d554958000034cc41d820700f4203d845010407000c042e482561b00c9010058070707a0380561210707105c2c5041a0401000f15800984665112420708080400d0002c803042688070901c50850000000b4100110ba44405000ea400803042182607079000b00c131001120382d0610052424 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 26844817 1250 26843567 26843581
    0xd0f0303021207030c020d210c020a0206040603050403020d14041203110a0c081005040c050411040902040807060905090f01090218030a260a0c06020f0903160f06030e1203 75
    0x10340500301d80300305201c06140c1000f15042e0507422044507000640d0039165036500c4144240c031800c07407010486000c4e40c21012049030500d01d690020320403549500445800240c903074006002644950050000a9211420b10003015010007261503d0002c034240042040e44841754000070340210702c180281f0203a000301010a0500030208585450803800507580d0310007190400001d10300943c07240d060700d4803c100744517880070014854140121307805180d04442a1401081002800703107400041032002003000005501e8505100a000406280d0041c1c98654680013025041da00158440e5000307514032070804c0a8400c800c180303070381506c0e400d40c00183c49400d80a1801c103071300032030611103416100c0c0c0c82d170650a00c0345030100140212301850244001400b581c1c80403ea50140c070b40098081780d811f070041030028a45d0340240252003481c198150419170030000081c50500c141803210b01000c4400001d200e0581451102c8000e000e0b1400d00b880400842c80c50969107c2e2030b02010002c40704048040f03508 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 26846067 1250 26844817 26844821
    0x150e070602120702010e040b0402071a180304030b071107080106060e0d0b0a0507270305010b01032003040302100f0b010e0402190c020307030204020a1e030506060403060509010605030609011a060403020d0f0303 92
    0x8c421002d04115150109842c0c003c0719000032007070541d42c580d036040c00500c601d824150100d200400403800385040c1807655481c4e032048030014003400144084a400009050b0702080030f880144034600c000f150b02ca00c0c00c00003a0101300c7c0c0908042c05072550341c10301d102140c030b40c10040740c201d07203220301c00038a0365540d007022511b070031406451890040603203010b00b40f0b00840702411800c0d01d0181008105145600c2c00541c112400c0d9030303002c802000310680c00c150270446d1001455010f4003a00603203040d80b03607800a18089807901c0880d459801d0f950ba007184a01c5d64818030044901a05840851502c01000c071002c4800305100082010031400e802800c0464805022000085501900654846811b94409080140039482030407403000645401e031440d074840c0c000d00e0302070103000d000c1c24901415900c5100140030014a120708541d21203000040544040084521410800c000042d0049a01180441098100400c64886e400a100a0001d40d075580c0c003001c0c2140e44203218000c011071514007580 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 26847317 1250 26846067 26846081
    0xa050903010e12040812160f14060703050f09070303080a09020a120501050612010207080f0a180b0a0f090b03151201111804091109060409150e070602120702010e04 72
    0x1c402d015520509042611400c054001d0f00d0b080d0742031b2030304242884196401e80c00b850248551403207090510704003080101c2c0c1c0f503186107030040d011008101d10001c10030b0316084098543c900025540c0081001c0c5405100703902d03400004c0e070005810b01d00c2c80c2d40c40003000351001a0034010040d91314805801150f445807003071001451a818049ca200343c03c0c1c24081e00a240464a203030040a82e034007202000d038018821200ca459101626506050600410003100d400c24507202040c85072041c0c0d054407400c02d100084000306504150b81d40d0f034107065032006201d000780c100700005110359400e040c4074109d0424182c80d03006c80407004a41c43d071201140014162200080c040b1078551914845040c1c0603c2c05004040b05a605401303140004010070501c0201c80030100701424500c00f68905034000d00d0a4040340c0d40128004102280b003915985504516040c0074004000003030f5100107803007543da03082c07000c84000e0601d030000c1c1101c2e000750901603005126205c4000d042003c40301201045a4503584900 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 26848567 1250 26847317 26847341
    0x601060f0c06110406020705061306050310030b040609050c010e01020613030203040308030f010306060501111009020307050301020414090609040c0603151809020a0e011a03060303090909030a090b0703050a05090301 94
    0x408800c030484050320b030f154414060607005000790b10010800d030512400b12640ca00642000b00f42261400d1821030356508090800c15600c1100e84000000c6a00c800303036a405a4010310002400358654a4464136200015200d141405650030300740f51141e80120b0b19640c0801681000d542126191404030f06600c603a40004103400310100901c4085d040342c3d01c000b8162407141008008068607900192413070306003072980c3d401c907170f020003040c0d5404940340d00304590340c1d40301604552116440b08006826a04160045040c51070011000701030f910304944d039150004030076900c01081c0c0c100303030303c0b9845164264020002450748824012854280040c644401803d42c14044a40c41030000092009400005030992141412074804580403603003071041412039200741041091070400301841110780d000100950b926000512001c200c544070b07490240d00c5801c103000695135403200100054103c0e155a0807501081c0c00034445080003c5e00f1004a410414071814110f440702c182400083c054844102d402e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 26849817 1250 26848567 26848571
    0xd050a14070e0a0603080a0c05150702150f010e06060f0904061203031409280204090807020a0b0c0a060e0a02030708010515030f0706140f040e0f06090402030601060f0c06 75
    0x91425510100d80c05050b00c0b074400c05036510f501d5048412041e5079076400301030800c9504106d2405542c1c0521200001207100341305449401c1d101d030704c0c1c040c1125021900f040c003603045914510000500e00301034540c001d4040c40d44a016506019025890071070042c511030080314002562a1021a5102986c1907007000030400d20841da00c455080c1c801c5c0400100031404a03082458084e0f2003e21501c030740380300b20003840045c035441207082c0c40080b002c40d40194500c50f400ba030a02040150700c0e00c1c020940054015110b06948120600c140501820b455000f0620607c040c8404c01c0c000c034000ca5600000b680102c0c0c0850741d20000d8a50324140222000c000b035240c4900040000c0e00c0303074103400c13640c0714a070450655100c801c0c030700d0103040c6c82e01240350420751a900315800038880c40380904104000c00c41c2e6240c2c3e160400403d62102c421035803080c1c200742129545071007003018900f51000705a40c03020042d120503119040503130119982c1d00060081c4410320141c00c0256100364031404c20809081c0d000501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 26851067 1250 26849817 26849843
    0x19080c01020a030902040509010209010816030603061107020307050315070309080909040f031206031104051b07030c0b060a060507060b120a11030c090105010f030507050d020409050a0f0b0307050d050a 88
    0x20280c021301c00c2e00c0d0b01700d0240c1c0c00e040010341084c41c18426a0007002040e160030b680e5955005100096010b1401074106040e83e40d94084049100d91050500c100b5004484c0d81d1344034031500406142452075403216201e42d0209800b03907218015404003940040e0241004034101011b432820034120f00441c03018540003020131041005001e1a40c0c0703a502d000d8020303110100f0100d104017104003954020b0001503c644101c10703d222103810140d10948c1c0c000481002510403984400260f001c42d4000c01c1c01b540003070700241b080c1e0140310060414941003002107038403c003114603000000e042c60088690103042196036941c9103407140c6800c0d2070150714182c0481aa0080ea21902d8154000c001c40ca070b515010b40304071001201c031410003000c04e03410b80f40141c441c85994210301004502504e0000c1c0b58104101c42444462444a020b001030000b40c110100c0120b840e140c0304012604641a0700c103000791340e5040101c0403800e40c9010550606440059445540d03040303450030817520301608204000e04890002c49 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 26852317 1250 26851067 26851087
    0xa0801061a1602090c0a1d01020307030c0f05010e0a0516050a03140a02030102041701050a0204081e07030503120a14070f0320030114011101020a0e01110c090103060203090c01020a0519080c0102 85
    0xb080380c1c0140b80c5402e4805881f90900c02d6890304021802805a44104034800120b030150080004c00307803040428003031000169880a0941d0b00100e00f41100e980410f00200030404244162070440740280c00302c0040c0c6181c1380004000b4070040c80090200b600010f103d6110b0101071258104a80d0058002c1d0340c2ca613521200004000440d4510030499403a010218032110702c18000c4070100c610100080000341c5400012440c6240d0410101009114005c1e00100013001480606585052507044c0c03501c61401e03401181c1a14000c00d1100d4542d44003104114480742c0000c9403e18102c8146000980ee1008254404801140f41910b2071005004800015a108615900d00780304030280e0703070310b043c004943c0c005d81d0903801103007040c2c00890841c420070440e0394451465440b80740c1d40403049928070808000030a11004080c1c105403000c0d0380000070850030b104c04000c0980d10180a00c006d01c0300407180d4503440c2c1c50710600420304005460098a52040c040584161180308400308021582d03103031259 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 26853567 1250 26852317 26852341
    0x4020c07080f070f030203030706050c19051c1b120e06130512030c070209060406050d030207090c090b19020309060c0307030801050906060702040b04020d0e0106050a0801061a160209 80
    0x10042c0321240c403903c80c0214800348607242150407254040c0c011402c182c100c1d40c03880d0107071100511840038940103020303040e80c00c40c204420030300c2e201a6881d0182c0d17440b2145008618040b0148446101a0500400c10303030410841e0942c40c0074200a1811243d540c52400722500645040940c031041c51080d2401c0c01000c1a6402d1403002c500e21403400c4803055110b90034040802d0000b142c914000d0351050040d0700250802c00190342c0d120600400004620b034071500040c2c001101c10320f041d00141c0c401c031800e10076a10140321701c0442240b170741800e042484ca8040c0c2d5540074401d001000e8112001d500c5c47c10700c00c500810640c2c00e4444000e00c503a80313400030f92080d44e56940080d1030940008110000005841c01d0505045001d1f102c050100d03841c240154003804060300344a1185a007145d401c0204000c200c0840c4110810908081d00101d0a580f4010030030541e1140d0760010760b120b901d000d00400448881c440c1909082205810340780c0c6a0a111804d04108414468042d4000c14a0800c20100007003207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 26854817 1250 26853567 26853583
    0xc0415030905240105102109030c02090c0310080105191a0d050d020d050313020402070f0c14090a0c020a030804050a020a030c05010809071406130b04030503071a06100c0204020c0708 80
    0x3500c10a04210000c8021031b501f00051005240ca02d510782072600b600034254000126243c02800d1042005409a000c1184410101c404400515000c400c0c04400704040b09014010018000240102d01b8045c84403400c00802e100e0302c0c2d11b0301d40d40f521f410440103240e1104007420100180781030248901400d2440c1c45024610300440103010b4080b000d42d949005105070ba005060740c0c1200c0c0d65400c0c00b40c3c01d1000a501685050724101d40e908070110001d00d440704000054400b150755501000c4001040c01451040504413000130f0742405d0810f12a160b00144644400d0340501e000941c589036820316a00300403181c10040c0d0041400c102c00320a2081c01040d48003240e0013a42d803018070b90382c3c3c40c41d440e40341e42e1540101c6402c01000b500b01101843c0040252092091403201c9040c003d540b01c082c0d072070660096004441680000c100b00e4280410301d100461842c015850a0040f440c04500007112041640030301e1040c0013070365510744295240da50598018004400c111049192511031380d507901d00c44 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 26856067 1250 26854817 26854819
    0x5090301061a07031b08071202030912010e070801140f06060f0a081506070b040305130503071206050606030108100903051603030506030c030a0c05060901180303030c080c0415030905240105 83
    0x41c0c01014140c03101700400c0b0808042c3c009880c0d44c20007c6541d200203c80c0341e420413080c214407091060140c1542e401720807036601604e0b03000009503000140b40ca1030814006510400310350f45450200160303240950172643c1e01011109034000107582d03280004080f40a030103199100c5a10100e55440b2954020303140d0360003400693b00c1c40c10102c01030030820609100321030006000c200c1c0400030400107401031000d0300701c0d00309605800070344070384030008a03241013060391002d2001003c8055242c1408003521441d0380010003622000c0c074641c104141699502102c440944089564000d40c605140c0f043c800c0d46d051000030307074808140e807900f420300601408041c1d8100d403217030085100344a010714000606101c401e40c000001c24081c0d15110402c08160407010b0900d040c409a14000c0e51710019041245001d18807a45000840c010358003c02070004200030507100340c40340c0400051027900c0607e03c5c0b007c051081403501003120001840c01030b09010000b9450106020f000149030a1071803000061816140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 26857317 1250 26856067 26856077
    0x20f04020415030e0705090411100905100c1707050a120201020409091203050c13030311070509070216060905010909051f060c02010e03030406080c030417031005100905060a05090301061a0703 84
    0x14403401001f201d0102a10000c20980b0b10124150440c02c1416105501e0503050915444040c1e81b4004512a1802403c4020004036142107180030040300d5141d014048141e80701c3d8a05207042581c1c2e580d40d40c0d1824030301600000c1da07008030f940160320075012900541a040e030184a07404042ca400b1817110103d0f01c910011074205000280315036494000d490072203581941c0788079118034640b015030703060040030900c0f0307410b02850801141d1074540c84800d07406a00e65500502111079041d0301c04404010030340000042051008007080217a0303014151009030358903014005002e0311903003001c0600e420010800250b004c050039000806540000650740c2c007034002c4e01d92012a103140810142c6070711450240070049040e203030100d03102c0c15048000d1a0f1182c40f5481d8074800c0d03401113010030700f039400484807032105c040c3c1c400c0107000c1420124440203d034101410101c1c0301a0400000641034051546a203041202c0424150520755007500500d000749084072054070304500c444c00c480c215500080081d00404c2c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 26858567 1250 26857317 26857319
    0x3071202010e22020a0201020d0c0f081005010801060503060d0f0302010e07050402030103020604090c0c050307110f030109030210050c120f060f06030405060109020d0207141005010602010c020a020f04020415030e07 94
    0x105200c2d00d002548242081c580e503840c10700344075450083d004424548215903091065400d10400c9100d0000c032b41c0f80c10b456000c46a03240340c0c001000003000400c0440040c1e1501c00810071660000c450364107542180c00c001e0f40741d07587e5001182804200c5138024111101d0842820203254065202c0748225140e103081c0c0c0e60482c3c458003400240d110a100094122600308803c010341a081e9100b1400308a103171030095142003141d21000d1460f004210151201c0f40800003c5601f8640810b01d80798020040d0000e00241c0a1524040d46415030684025411500d900006034816030080c100c682e1150400e1252000d420074192502c1030b90000c803510381c0620009200a0b01615002c400c2d284225480b10040041c3d1b802c0c83c0d58280690800b144c51212940c003401480700094042c1c400c002145c896400034405150580b40444c00da59040c1d02c04030a6926010400d04203d5000c0713007408015030151940410514105e0129000b4404c640c06481920904514121b1a642c550802e481c0c0690f1201118041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 26859817 1250 26858567 26858569
    0x150108010c0c02030c09060406050a18050f040201020d0e060c0f030301080c0d0807030f030f020a03050f07110c060319021606061505070f020406030b1501031d070e0c0903071202010e 80
    0x10b001d140c40203981603100342c0c1d00e608245002900030358400b03006040403c10301da072240490b820f1211b9400c8040c0c81ca82c1c040d007004081c941031040d40d03482000030483c004282400d0300080d44405104501a0030805640c074031402d00d8561404a480082d2410211200e100c0030b4a0180c1d10303908203006602d035a000e080c00807085807070026803000d41d880d00400e6031807910380143c0d0152107840c0580c81d5282499140c990112036000c051015203541707101c03610045034074a0b050750200311500d0014503000c01e01c09600c08100500e000020b551013601015100705030341c0e448882040400a40c8645c00e450018000a01520810040300f09102c5040c4a03540c03d00c0f06035100c5401ca400c000082c41e21100145040c448c210100c0d200351411411240054000240141c490f2a007540c11303601281c05020103102060400714a50349807041a54200c65034684c3d042056880c1404d80c2ca8200ca0700c640c40030230130080003007042000c140040728a5003600604941c1c8083e599038100141c4180420140d011036800e1611141c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 26861067 1250 26859817 26859827
    0x9030408150702010f1a012003030601050702130504030224070806090601030209040e0d12050c07080310090507020a0c06080f0118022505070602030708030a020d0e150108010c 77
    0x944100d103000d001076101040d110300788120002c01c0d0300119074035181503528480c007a109070166010342204d1030304103110b500c3c00900350880032044841104150005401510404400e07207411600c24030300240d0b6012203000003201c11000925a41c50b2034944811b00c001c0540020700c00c113020b0040b000d880c102e12621040a01005c1044a541c8040352140b00010a00d00d0070b94105a4000814100142095403000126007106c10b442c9496000f0341c0440c4000510702e8001e000f0146111070b0840070300203850702ea1114138441c010554024406100400401c42131076140030954054120110200003a10b00740c04000c0d958229250155050340b4100008100d061040c00ca4920540003090450116480e101d0b2286208104009440d160391f401d2091403161007404003110800702450840030781c4132240341000c504000280e80310703a0555000700019800a181913041d81d503c10405074005888078075100e069400b410b0901c50f0080a0302401c00c03820b4012074070b1900c081c1030741c03448802004100402c03141035075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 26862317 1250 26861067 26861069
    0x1d030a14071401020607020c041d010c1101110a020a020d03030b030d030209190e0711120c0102030103020a050406031a09010605060a020303041101080705161e0c0603050f0c03180106180603020306090304 89
    0x100680043c55240b108d41010781100c44480714420301e41c004500c0303040c080c0d0300b11100000407a0024242400d84030503030b00709024001562203d040303101d240a4100e200650b599800c0303400280030350b40c0d45140406150080d4040c2c4400d500c0641039407401c04d60090300900035030103640864441c00c00301d10800b4400310341d084120180c40b240d21444540d80c450b0340c400e641d05150428001403522031028486203603800400600a09601c0c800056140c0d4154410000308920340d4001c0303805240380207410000300d50740ca401000c030004122551006c40d00d481c1035180c05401e00d5082a5044000000c03078001540d400001984614050003200e40b20010030700044410420035203e01001030810300014000300e4070b1003544c00c800d41c86a080380080307a08000820745c81c11030072142030340e4107001030200b040002d4240c040d45520031182c000701c054516104200d00805c3c0030141290005013a001c0211040c90002d511820117003c440d403584000710002e4640d1320250880d404220b01a01800c0003085400c0ea002003514 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 26863567 1250 26862317 26862331
    0x3030c03140f1605100c0e010206010503060408031b0d060f050103051602071e05150a090602010b03070918021306090b0f0907050a021c0c03030e0303071d030a140714010206 76
    0x6454403c1000704280c1150a0140682d514003801d1115003414920340b150f41942080fa03159568003801241c000380c00d0484c1603008030b000350804000c2000180c10342c3c0459074030048121991100802c2c0004d0b040290241d03007032540380c4619000020400344800860041100d000b44c0c0d060046582e00c0d6244200220000034007005039215240901071460314001003514090f0040000c952030740c0e107000042d140e004a9007820402100007800c0010580d1040c02c0303101400c480e0000b802045807036030120740da49415215a581c1c0c00e81e0343c014019000d0488413001c0c0020f4004141d41011007030302000c1801041d103449408485442c10350302550070b043c04c00b610504030300000c254481c2a0784d0a1000e5880d90720041d96007045001c0c48920000e103044140b100301c0c091038503613103000344901c091074064212195001074001c5a4410300401180c030b039006003400000014074086da200a000440800c0c900071400340002c12411403910304854200000400314126070b481c0d5000302030318403604016a2208400d4502c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 26864817 1250 26863567 26863597
    0x90b1c020108040b0a0902150d0e07080c150c01150f0f0602070b071e030c0b06040b03060703090309090207080904050c040b16050a0609050d020c0105090a09150b0403030c0314 77
    0x2030003107000c5041c0344d58080032a45011072100015800101d03040024003940c0b00c82000400c2038461268148100341c10201541d0087c0b10541c10040c07850750b00c8541c01e01c1e4a1150100491a011054618051310405107400700284030355100c43c40e4210307505449004021020383c10b810005400d40304501c0308400c40d0100d401802d05103050545070f406907403000c2015134014401e01003140a0340100c621307040c1e510740241d44115003c4c0452500542c2c5410250080d84200c0c102103840000e03540224590750813034418100012010001e2070291b40e910180d1703001c21000c0c0d1002c1284001c5c0100706004203024102103c0400982d518410282594011350143c1112030000380826003006510064401800d8001c0d400c58207500d003141d9a400540f00e110303800b2a86504401986040346804204212902c0001d007469030901514a010400d003141c176101d0400600e484101902d80e04041480c40d1001d003c042c1c0c80d81c1c1e81c4944a0a01600001d00008120006419540c3c080310307200050382545d110030307000051 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 26866067 1250 26864817 26864821
    0xd0206090d122309100608010203070f050706151404050108061312050f040b040e090c0f0402090d0209010308030403140301060c03080403120603061505090408190216090b1c020108 79
    0x480001007950a20b00003a40b84190f80d01c100d503070010380070f281c45281144000e024944240b903044d01a0b0f105980074607000da0051050058030b9070400051050180e0b2460080c1e290f03515824050003800c1c04001c00340d2a807400500c00324000000d0702c0b0014049030709613001c5c022a640d840185a0b01e030400c40341240401e485508490001e40e18681d5848465411310301541000301c41c20503480b50350302c03d501070310851074005810006540c01c20015644210f910f005004418051710100311010741d0184014400c1e13500080030881940c43c14181e280e100e4010b40b181d2030968417441c04407510b170b10a0380c040d004070f818070006012140e01c540c01c0328140c46070355032030180056442e501038401d80e0f4007a104070180140079400d070780b984a9900c1007900550140300042100384900340c01d481c9400854209900450401c003c00002c03403403101c101c50b42c030301d01042c18a241c542420001c90400c1158410300c1080300520302c0018001e025a00110000b410880703507038980d8501c40400c04a01d035507080009020540400c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 26867317 1250 26866067 26866097
    0xc0201110c07050f13050112020f06090109050105030c0f1204061506050a0c03030204080604060f0b010c02060415030b100503040b0105060a0c031101020c010f02130b0301031a0c07020604080d0206090d 88
    0x16140503500c0c4064005c00e606a4440201d0054820980005012810080e407010542c50702d10300c60301c0c20b030340c007070750300920740500e080000303002440320b01905060140004c00f0a1150107240308070b444002d01c04038000e4944000c0d610482c00e206056505640700c1d4100300707580340f15811211501c01110411344507035107415600303138042c5c4803005652030a80c103059090000203680340048c000588540e01c160300000e9940c040d403000404968017082085c0c1040300d44000c070001a101d10b012902640e0241103540400007400c0d400303c0152482080041d080446218690303072294102001e18002c40c4240c02c40c0c4010ba0700c81041c01514060f80d6801400100d20030b5004c00400e010302c1010417a045104000340c80d092500032454251110304002c070907040d038001925109d806c00440501d02074008440340710303e1540f55454100ca0051603117001083c03800010040f611040100044500450340070700740c40d848680d204d044580750b02100c0c1003200940541c4000901941020612124010b402d80311200c0482406c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 26868567 1250 26867317 26867329
    0x60f0e0f100e07030609030c0201030e0705060405041512030909050606090114030901060314070303021507020a0209090106180501090f0903020601061b0813050112060308040b0306130f0c0201110c0705 88
    0x307500c407505000f114008404144240a02d61106010740c0320070040314910300c00181280e400d240c41100e2034015400a0086507038910440d002c64800315008185031001d904060089075141d403280d80406a18400c010816400001070400c85000003010030142c1d07105418808a0700c21491058001401d00c0e000c00c00410b00c4070080c6411207a884000501c1e1600da0b500c0c2001e582410b107181c800c1d90301502041040690410080c480ca18030101d460109081040c0d006c0d5561681000003441204c200303000910320002503010500504011084240354804040510010082809411015402c0c8000c482c5c50050700d0264400c1c80e907141d070007015140c1c81c242c0c0071038441100103c2d40d0f8a0004010103040450300840190105402d0112898103182c0307484000348c403209152800411081c01d0030340410100f4603a41c280d80403515401480d43d40c0b40c0c0c1e044002002c45e502100703000c90b62841d03c0e005e0702020303410364003040b403e280f00e400820030515100d607005000d0050960251883d80148810712040c2040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 26869817 1250 26868567 26868581
    0x14040b03060607061508010b0a08010b0306010326160c050906090402090c0904050f090f0706090303050d020d0c03050402090105060715020a0c0f06050403080f0f0a0903020f0a060f0e0f10 82
    0x9200c000030400202d10901780e4603001d1380e11060103a912a68503a05501d068414180200890f03802040065400808280c903803405200180c990603107444a000d0200d014150303000c0c09540c500070540c0d280f11132940700c99525001038064500054a410119130350802264050041e40c00074500e8440d0b0b84d45908000d14424014102030340900c084c098280c060f159405803d000b8120700840c0305080c03410b0031040d841c1c00b90301410040203074041d510800c5041e03081100007080e241c0505c0c1140c0d40d00f07080740000d000b038803c01c040301440a1401403204802641036103e14002c6200701c0d43e42d500750740d8610410540d4020080083c5c595110300302444200607196000b0065000c0342c1c101441704007280d803203045151480b18010746286486000700b208241c0d00c000059030002d00624000824101601c41949503140104a8070600b50703207820314028540200b181038009864034080318800c0a00780b0f41080a4100701001c00c0310541000d8141c98058008520115110040c500410b0508203010814000d4081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 26871067 1250 26869817 26869823
    0x3060d06060f090902090a05041a06040b060304080c070504060515071a0c0c12070b06040b0f030102030a0605010801091b0c06060803040b041d04051c17130314040b03060607 76
    0x9510340000e070100755030b14480700a103001c40700011841010f0062041c4200018810004e061902c82040700003003040c0d104e0f10080e868803902c2d11195550700d012074001c00900d10301035480200801000204902c0d80300500141801c501500c180d19035410911050761a140512030344000c1124444450000d002e001e007007094007400e144425a202842c454034003410681d12000c0c01180010002d00d030309020015480c6044905000e46d25022598440d0490032801500c602d100d0b9072100e80a01c9960b940e0300038020b02480c0180215600d0600b0549100200b00354460940451012000002e10700340d03920070700b10707541018032495170b0b2400c10f040308640ea456204001c40310302c0d0751081c0c04078a1880420180018081e490030440d50b450901880c1c0000091001c50501e1600a401c1000000b501c0451214415003d41c242c0d8180c1440200c02500c154054003201e411441c50300c402c00c40000445032002c1155402616503103400d03104221002d44501c250301403212808000c10215856003802c100a2840c140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 26872317 1250 26871067 26871071
    0x1050609010f0e0d0c030308010b0a1d01050c0f060a140903030a0b0303130303020303010504110c1507030207050a0605160c0506010608130501020a0c060b0609010206060f041401030507080601091103060d06 90
    0x2004600113460348043c000d007640d501584c4035041c0304164000091901610106502ca420640d00032801803520400c00c41c0480c4226555a1040d65a40204242c8a01d0147d40c4207440301b402d4943c81c02692507408841843e00d0794100741402c03107044010308503d80912044c0e00031398590b54800042e81c002d440c1007000b1036014030003049034030b18502100703074100c018611990203156294500002c00c01a540340440e08100d16108204003402c451002480f180005d40c0e150200c040d17507403a41c4041d8028040e03100040c0c210700420180008200c070b203501c07a5108041270019200c55000e006800c940b00d0004c0d5000410642c0540e0040c800700d4002c0f65103e500982804000107070507440d40d0b031a802da80203400890042080c12002400300249400740700d40149040d1052030a0600e2900000c1d0f0703601000c0c01040c0a60300066180000c3d88a0343c00140600c20301e0143c040304e5503074038941655902403600c20400c070781c01110004600c1051500074581c0481524035518210745603181001065507002004444442d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 26873567 1250 26872317 26872337
    0x4170c06150f09190b0114070609020103020f04030f0203010c02030c0d08060607020a060e0f0103020a020d031d07030b04060b01050a0c08090a0806010f06020c0607032a0605010b0a031401050609010f 87
    0x55500d543daa80700c2c459a154020790b010308144404152041844040c0c1442003c2880c0d052000140003502d0038503400240214280c0860700040c3c0003846000c4c0200424800040c01102f401194220510124403ea000700072040c1d205008a07124064050210383e95040301c6450021a4403c80d216900080c004202c0f0345061000d50005040d502c0300e511150100d11005c160701d0483c613081e491380e40004402e00302507140c610000002521512441413040134199244181c032115403810100c0010948000119122180c4070b040000a210003141d0848400d81409408241948580e007a030752a00c01e1074840020308005551040b150750490344c0c0d03c039040301c44a07200241d014410400607000b0301404824501d19820080f0080c00c00801c0800386005010810002c00043e50141e031551400007085030788030154401e50864201e070440c480015144608040011840000d07550040c40d011025803030410403400022040748003c0c80920606a00c20001c0c070058030039501031031001811800c0d40c0780c0302c8000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 26874817 1250 26873567 26873569
    0x20c0a1e030210050c060a0605011808030f0d0f0603050102070b0a02040e01091a040501090605120303090c1203040306020f0a0306080c0108040209070521010302010311030108191a070804170c06150f 87
    0x14000f2107121012035208c1c1800c1203035507001000844400c403042d02c03815040742402406540d070f10a2451107090250006130400c0e51081c180c0c847d452060f01a4400c3c00301d01d0356070a02e13500bc0c0d00001d20035034045070000081041106d00c3d100312000c48011703020b113603103a0380b804034400b00400e050111020f030740301f40d0501c0030b446a80305e2180c5070290000c0b08001032007c0c102030500806031a854600340107a40108140642510b00040107403500d982120b1184030710040301c2c0040c3c150701440d800140355500100d010401c186020340a8859640656000c10809680b01001681d03441100742a41c042169280420058100705401681c4a071150811030318144a070881410b21202c030201c0009200380e01c200510840da0b141c05450801c001d004d05081c1994100103900e40c455040108003807002c4d01d503c030b0342000c100518503c444a100400394554540c505210054000041241c04035a10304040e8600104254600e06491680c0c102c60010000d6940b060050480c035020305426940c03241c1c61310440011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 26876067 1250 26874817 26874823
    0x100e0d0303020f03090610090b0105070b0606040f062a0b0f060a180b09090c0a0605160602041e0504060b0703110111030103140d2a030e03030307020c0a1e030210050c 73
    0x501081700c01070409207480055959440c0b615008072940c0303810030f00081d8003a81c0c05003d0340c60f074036001208c0601130385540b40018418071655020390f941c01e1b1003200000ea100d400180300d844140d0310481c6c007110b072a83c0c90460000d03040703a284010640c410f0310011130741c20362040c0c4a20303600a1016160203a4070342c0340c600090b01900805198004a84c0b107120641d0141480313091542c0041401e0010000c50700400009002c0f5615405080c0c10000d0100d0200196407295008070029604220300319611625060b661020f0003007160b0170f03440e64502400c006040d05062041c0c401300c0d0b180e46509030412401d503030115040c03400c00040c000c01c2d6485024502c000c9030350100031030080d8451581003c598564030959400c0c03030000f80e0a1020f006200031050f0180c0c3c1b150b10428040190702150001d510010300d4203481c0103441c1c04203150144404070170001400c0d0001002503842800702d5032030140c1582c0790b2264025484040c5c03c03030b01500828508000506081301d10001d049642e08040d41070005c81c010280c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 26877317 1250 26876067 26876071
    0x32109040b060c07030507050604120f0303020f0d060302030d1103041404090c090c08090105010e010b0702010507050604120314060307050105070309090203070804021807020a08031e040501020d0506100e0d0303020f03 95
    0x10340d80100d1801c00400200b0040c7d00020141624080d04103032400b0307110322042408101c041c02c604403a6408204042c42075046840f45860f00311901e844801e40240b110050003207010485c0288502c03d40850207902400002c400d0b010341c00d00440c80c241c108000c02100c035403812f41c42500580c490280c00d00149030400100017070481c031440050903000820004020501c050007040b4540d15210052181071940070a0a064529001200b6035a04003480100c80900c141039001d0028040c0c0400d100070002c0b0000c00c1049241c1607602031040720912008205404801e84003580c2c15401000f0810040d4003c0d406802d0180c040c5c02c000a5040e660301203482a0781c01107400800045c0004104021880c1840321b0307100007284086024814580000c0c00303990303070b882c19001400660001c0005003455136020081240e180c07048001018501b86840c0c114042d4004c519005407a0f401d09002075002e051030015080313404510358030014019005028484011000c14040e4105074007000055a040001ca001314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 26878567 1250 26877317 26877337
    0x504060806090706090b040302040903110a0501050115050901170405070b03190c050306030c0f061c091101020c060d1512030f020c010302030613020d0603060e0607030b032109040b06 80
    0x5602e0240b14040c00c0c00007a80200c402d01414500074040601c40c6000d07241500d078103650004150390581002d40c0d40c00045120400c05104004e2044108041074010b80c5c102c900c1c0914030120218010002c1d120350117840061400910804803c81c0b5860b420662150001d029000741c401003921160b480019620840d84550416090007a084c12204c16109030346441d0084d01e400c904604044002a403525160340816100d03400c012003200c0c00d43d640e001101c641403041481d854400c00c01c0d04031180903100303260040c1c0760421541d15511042d400441d40d80308849c0001e000e01e1904c805600c10381c00a040b000364404091054000c04180014441400605c0c10300985400a0000074460028540050310107101d04140c010301c24820180c0b01c500c1d0403103641500c11805601d45808805440042c03d8541c4043e21003806e20008000041002c2603040c0610b849030740a21003480902c0034190b8030416800c0b0706c1d44580041080e681c2d0300741d014010b400c2032400144041107a1442d24001230035904211908 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 26879817 1250 26878567 26878573
    0x9021203041e05010c1703090c030d090302010e0402030f0106200d0809100c08131b032103020a0c02010c06140106080a0606090f050f0d0f0c050f010c0203210405040608 74
    0x107486042c02d401098001c04013403801c10800d9915070740e8403c200c0c41c0882c0304e03401e240010011401581d0706202c01c0700381d06005412a900000c29400082c81c60a451000768081000c5100f4a4813a080c14000c80f442101481280440707039103406411607052000304005600000141400d8240b140240141c00101c541e5a80350001d509060004030700b02101402500c2045107410942e4082c9278010941e540d100100d290300107c9034810b810511000a40845001c01c0d031907040d0307008400c000090f44a41a0a90440031240c0c40900790102a0120721031115500f010a2203004bc4c0d0303006610648616402501c5000c1c0403804120b100f22a400c00071080c0c00010200f48620700b0444801c03260703c00c820080202e49003415901e071500c07140e2825500280039141c040e028000006400d03450320154160b1155011410341103a60460400303c0001d0424013403180706845c1d0300c2d00d0b60441c0d840b5569000032075800078050719821900c00105440c41551f04108400520144400104e580da5885074500403c080405 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 26881067 1250 26879817 26879849
    0x906030602030117010504030903020f0307181b080c03041104020705010203040b04060c21050406060e01150f050a051206041d0c090112080304110d08160303050606030c07060902120304 81
    0x20103c4c8210b40710010307070b00c1c9a16000401003c80c0d44800340f0ba04981d01907070222403055005000c0303820000c00b80c020032410344400d284039000c1c01440c1e0040700040e0308910b50308081c504c1f00100725880401034859901200092004c2000700e50f0002c0b501300c40c4400240f0047c90034140366502420380c5c004580503a00c03030005204020610000f409040070041d828030308044030114000c0c9807081d905078a001400301c0c0355944006400c02c13505038003100280120004820f07031580e4440c080c080588005000c10002546810003516a902507003e03a68500da03d40c484030b0411200a0484803400070050005602984030144a8000c4501c1d2410300d15554500d0007134204079100c1b8060007501c100c10b13801101082d2a003809140441c2c2004160307034001c4d60000144c05c0e4050000e0005c0e41781c031813059000e0030a00c00050010a880d2844038040c0240d40300e41c6040c000c40c1c0d618802c102c0640011115498400030800051000844942c005178609100814000c42c050134210251301e590060340001c1e00d00035980c26 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 26882317 1250 26881067 26881079
    0x20720010e09060604060c0c050301050c130e0709060e010e190e090601060206060907030603080a08090d080415020706150b030702071a0901030c05070210080612030f07030c03050409060306020301 86
    0x125058840d01c2541c4500741414143d020400500c44e6201e0401003040c044200420091074501c400000c1c00c0c014002e103d182071082e0401c10701e0784031130100f0f01071004418001641110b00d551880c4507a595850740030900b4641481529044001122541004000112900155200018404019a50303413226403610b0030145150381c4090b015103003d070709a00410041188030750020b0f41a03406032042d1281c4440c0e450b1354400b42c014086c943c0000304583c4020680e0801250300400f424451582c0104603075221700c0c065404d45107540103680c05800c080322182d910002c40001c0d0001c2c04980d108210010b055402c03d200c0703409484154000389900400002480790319030f4100003410127420742c5000040c8489000c203103100d161145005040c18151500540803280340240e05407003006070094100081d40000000003409920200d0f003091040b90f00302940c10b045000001075800030080c008813a45411800e0704e06a403644900c00f0210104001007002007103404944c061107000314801d940140c1c8a5042c60 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 26883567 1250 26882317 26882327
    0x50105030705030a0804140604090e03030f0112030f140c010e0106141504030b070507060c03060603050106020708100e0c0307080304060212070209070309020f0406170c03030f0406030b01020102072001 88
    0x10b80414400c4e80301d45018404500b000044404460b07040410342020390759000032900c6805103a1200000c03130724051415a041c107010000f94030071206500f5214a031307038840c2e0304010b012a01e4200500080c030203481d105102405480d00b41301d0440c90014603404c1156258009003500c241030710402042e512580701b0020709031801c2d0340c4c0c54003d00032100c0400d0584c1f41204402140207910000d8070b1555a0f03c003241c0c02e107008000b10f80c02103411850a01a817000024058043d186610552002034a00400001c03001d20110781d80d025101c460303000d40008040c410301100505425603446401e4050403411031104e9904100ad04000c0c60b100015540b15480d200c0041c9c00d06012036003a81c4000810481400169186007a00e9440003050400149000b02c0340013041c41c0351074060900790003610f46032000c940c1c4440b14100d00a6a0004400c072400b1030980c106042d182d00807981013051800c001e010610045000342c010101104040c400103042c080561620324403a4076104290211500290765203620b56401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 26884817 1250 26883567 26883569
    0x4090515180316020a030204020d150503030a0507021e060a0f1701050607030c0303060308031f0b0c030415020f010204030c0503060702010606080a090321050610030504020d03050306180a0501050307 87
    0x4403441c140007428950216840744182c203100c50f2443c0400e0009000c5542d00c0446501954020303004540380e10b20a21a9001002c03035140c4100c600d08000d500041c5490700000300c510062542d600d40381011915030a1001071040c0d8280c02d11520301301c4245030b00075250400070b02920403a90b80d5004038000d07080d1000d84501c501122542d0052000b8006011a4036180704a515480d454074040990168505048008260f03d81000304071245c0001406901400010035600c0c00001c84200155642d490712520b07900c3c81514420f1840750000d1000b00244004641c03030012440b51801030380c40380450646e6143c02c80e80f00303400441d1810100c210078011402c04002d15940413100b80001c009160802d00d014065800003044039a4650322030082d607081510610076445030000c80b09080c040d040c10440c20001070301c4111105402401c141101c20b229034404d000d005c2c00366030054000341c008107040d00d0488141d44004c01171600300c07480100190056a00c4100c4912aa010050002d460750400040504000f00303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 26886067 1250 26884817 26884831
    0x102090a080f07030308090f010e030912150a0c0c0b040c0f050609030a060f020706020c0601080d080103170313020607050d080105040c021c0e06030c04210312150504090515 76
    0x441a015402070b800207082d0152a01420061200e594000e203242c540a02c030035401d0415400c040308044400000005060140e1084842d080402c0c80300301200d50341c0542d00a43c0307000c2d010500104020030401c3d4070414214030940303003a40c4c07007414a403248000f42c3c0c0b055900701c0e24000c070b01f5001c100800030929010b010f000d0071075030f0320b1030311406c1c00000c1d03599502004050311042d41c850a04034907501990454034501d42c00542903444600584200391200400d10416a00d4021002021011071048882505a95000741c40303004141450700c046849070002801d40c40022408840071005da43e920019100491107000180403114111000030054003060f448139000740c2c140400185140e070007040d0121004140354840c58000c4088204494941c4441e5009800c0100042849a4038100c40024416100700c1d02131102c145182c1032080090141c02e28010f40000c0c2d00c9014490403440c107801c14a410900100c401000f81e0310307840040c040b2511402c04070384560220316054405540b541c64541d020036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 26887317 1250 26886067 26886073
    0xf06050c16030e04061a030412030203060303180a09050a020c0f19060b0d060e16050613060f090503010e0d02010510120305070507180b0f0f0109090b060403080304050102090a08 78
    0x441c0400c0d0581601900c040102441080c02250405841c1d83e44030074018902a1100a17070070400c2c1d84004255481901d064806a03035221119083c60302a00881707010b44406802549024020341c0702e13070390440c5240c0c02c00c1d0b840300030b010000039481c600b4000c1c00d01801450000507903070314440321407518040119041e0100c54001e9294031462800c442020b405040d003120340400c2110600c800030341202048440103010303e2504c404a6075420000071506240c000c0400100f14035501c41c420001c2078025059000b800e10468001800301c20f00c642707120002c082c26810001d00b1a61070f40c00080c00d580c036071800300010342d10100e00c03404295824000c954001c060184004003550a19080c01c1c01d4480c041d4020301800340000b0941c0c1086000c20030716009168030121400e0000e0009a101c01404a2130305252140d0f420400d209800e1a00300010440540142c5411921614040c0c0e004c001d04601445079900c50007e110001c0841c40240003103102e24842c0c00010f03607442d01c1c03208000c0f001004d9080501c407a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 26888567 1250 26887317 26887327
    0xd0b030a021302070c05030102070c170c060a0f0e03010f020901090605030609180a060510060908060f01051005090d05011d030c0606040504210c050f030a0504090207030207080a0f06050c 82
    0x6194071494a100d00c4810b0300241e40e40030a41046001c0800c941c0c01590190f10000d885010300108070208800d490009200d21910a04e410090b940c03603041d03010301a4402010000c0a4449005181d00c54000f12181000c00c0041c40400000742115040c55043c0d00703198000580c61444c1d070f4041c2406010f80f00a0806e03e040d4144a0f0100b90001c0c4011309461111100a200b80902c0314100412603035281c3c420030074422407518502c2d45104140500c00d100200300c83c214049401d400c0810320034800d410f8443c0006540c0e10705001c11078050115001079081c448100407604882e20f41561160129000301d002081d805102c2c21354640b92440d103070740101c0b10f400078008654400404101c11307402c03800403640420240c5031b80c2008440103030560a04000010061887c000e840e400610520407640640300b03a890401240300c100d40c80f0b00c1380914410000360b0802040c8440074150b4090803040e80244122149503803100c000c0352911140ca482031f00c50b03401c1456120200300803030050326403041e40c80158900302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 26889817 1250 26888567 26888569
    0x1822150911030d0509040906090c080a030e0609060a03050709080115050307050109030317040305120106080901050609090d050714030f0d0e030f0702090a2c100e0303010308070602041503020d0b030a02 88
    0x2805105817107881030b42c039426800207201503500a1403e50f604248001440c50390340b0009940d8a2000c01c0031804241103580942152800000b13641c0c00790340141940707140040380001100208401400d8030b091040c049004144494240300349001444034644126019003064201071030414079070302003410072111b60001e000280d803000804c640c00d481c19505d00100d0703c803480c042e900d500890381601e841c00f4500c1c00004480d0740c450101c0d0b019907219002044991140c006004855104840910180c0c0c041c02010642074031034801822410f0190422070485c900c520500c50856225140d021607000011424440c01241071051708074920b00e05c0015450484000000c107164003600c00040e12a40a2a00151001c0c02540000380051391545e030034114021640300910f840e208100800039180b0641204107580156441500d5400c00356030000d5042d0b81c40d43c0e844a11a9000c150110b031400c4d000c0c04001000c54102e94141c2c400030444d200942c442c40d012203a8001c03164412141c034400c0e80980360300005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 26891067 1250 26889817 26889827
    0xf0308070606090c09030303051b1e0c03070308061e0f0105090103110d050105120307030905010804050c040603060203180a0f080306060c0f06010501080c030709090e010608030d0213051822150911030d 88
    0xd40a450704000205038000c0e40c83c070bc03103011b0160009039601000509804055100b017000e80300b418200c030b1220800c1490b10003400d2031244c0414468001030350310004656580100042c1c10f240c0320501d00400d15010b6000200c880f40c0190070a515510b8481c4c1c0148551301c1c10000c2c1800280d08440118246041d41e05d0040a00c00c05100d598140115100840c0074000c0030b03c203805030007801505c20711042c1da0b05c1c1b030404c000b50320844081c03c8903106c0e110812512200405c1500444e80c02401a801016207620b036187c83d6032000d400a90b00100030801c80380c0216043c4603904a680302c00028242942c507142c000b40004400502044000c4420010020140e41061100c8141c1e00d00950000d504012a0025401404035400c007402c148800300f50794004044540003045c0c440400c5060000080d503800500140700e01c2904107000904482001a0384000210b4500b0018525000035488208003911088403103100300d0314140509444030701240038022040c3c0c0b075a20911041d00180450300391400000c02c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 26892317 1250 26891067 26891077
    0x307051005070b060117041209050a050303030604050c07120804030212040501210f02040902030a0e03030f04030302090f15031609261011040f0509010f0308070606090c09030303051b 80
    0x1c1c814401c40841c074241d110341c02c1d48003007122640718406d0b141402e041a803941220454000c0015152910129181c00c05005c2c00c421500301600039411516441e007008050b000007445404490420f1051001041c01c1c1c03811296076008079251a0300c07908250500070705000c001d240100250104000800459a004030110140b10b40c07038040b07004217880700301050060586849407070f0000340041400f094890090b40158014803070300004000210340c08406030707124002101c0700048042c4500020780801c1c002e40003484003020060201154080440020751102c3e10b00401501c40701d0007008002c111401c501118a01842c1400d080e0a600c0c0380110341c004696085c07154140003c21034581d904850f4042003551510441030f5000d1144010300358004d9495002407241d62206581e1081c0002c807428410503440c10b0300c00100c508040c981c25a22100c59a82c8400c1c1c0485d03250b99140310014000f034081c42440401140c80d91030b4040e075499811b0003400e5801c090081c0c1c01d802335400700010095100c0049071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 26893567 1250 26892317 26892323
    0x5031005060f0f0a210b0306061503070c0503040b0301030602030604050a0912052107050309060132061207110d050909040b061c080d1b020a021207090603060506030705100507 77
    0x1640c1e50307001030044a8030f00c090441c1701010500120022414401c03604030b034002407800d408898490b40c4060400c86100711980c10540c8003002003002c0740c451480307504140441800b03401101d00d0035689580424240d8003d23030083e50065400300502c02c0d240b403e4060075401c440098010700811f582e03910396a00f41d00109640005010002903102844120010558030100c069600240c051521007005402680111010706d00d501841001294039400714548401c0e100c1703228005040c401000700002c580e10841c0c0c80c0194051404d200944007428009035103480748695986040151215400c01c500c0c103644680e42a06025003031051660640b40c50380266480790b0000e20044403912480c010554a075110f095000c1001000d10b240c80520010f03034018400c0c1c94003030004020324043c0280708018080c11480541c010780000008502603d4003900c402800c0c001841a213081640d181c00480440302280e104541c3d55840d001008030301c2c0340a01a0400909041e0703070010311340b41c0c0e001380140f1611070b4500003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 26894817 1250 26893567 26893597
    0x2090c0a03090203070909050c03030c060c0306040e100c0909181b03150c1206080c0405090106090f06030b010b0307170403031103090a06050c09060d020d0e03070305031005060f 78
    0x30300e84610940042007030315000390039109202e403071750b4000d07001d4803240700c05441920a0280f004810700b0000304841c03000e54000050315268440294605007540040c04455126842c1c50340d0001d08841070000a512214030b840000b501c4203002030180c1418070542c07008a085191032102c910400391501925800c940c000305190356013178005d41104119181d40c01c0645401c07000c0d1b5001c800351006a102103c101c0ba40d440d020341008404c0c015109852003070190401a410074516856603003460341206402c06100e100114a683d19520a5021191549200e18505441e4402041401030801c10640074141068006d0f145140c20103018002c03044164200750310340120b10000f030616220307601010651030748002150b41e904081c400260380d15803000050702d035989400d001c2420300b04401d007220b002d00005003c850a04402d100840700a410102c590001c0e81d407541c02c2010f2041d010b00040606a1207a29001d0f140e04011051000d520020f030025401000c04210740d02c1282c0f440000d46000444503541b0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 26896067 1250 26894817 26894827
    0x40506070f0f0b040605060f06040306051005191706060901060c0503090301020406050c01050a0603030210020a0917030a1701030804090c1718010b04020906030103030c02060c0f060a1802090c 84
    0x403070603085514000c0500351942a00e119010483c10380f000c140aa80564010302580c1c48800400011842d4510b081d0752004007048200f0005065420a0f548800d04220207c0340543c0c850200e42030300492010751841070703103041d410312800d07108030a69542084454020500d078909003020440324501800f070300003440340c0b800c0c6031020044104200c0300501d9000c0d00a54445980310001350083d0409103030149103508200000d2416140e41c81400304480c0c056000342412245251541c00039030029204800700b19500300007142c958115856150300c213140c040155660020110003d0500c03c2c1560740308803c500b003000401c0070031900000d0301c06403034180c180017445461a280544407401c1c0044100e1070801044100803005402c4107400301407588000003800354903103001c02c1200b01c0c4214081c05030f110302c1c240010300120303204040c1c10003018030181115191110360040c1d203103046e06403140d10703015034058005c10200d04c11034059038031a4515403880050307001d02d540c0000d150700c0c0c000340f01e94416040420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 26897317 1250 26896067 26896073
    0x9060f030a12050a090909050601030206031003141b01021f15051002011b020a020108010905090304080609060103110a0e07030c030b0a090e070605030c0d0207031202030a05092104050607 82
    0xc41c1200ca19840100540049034980015145400070b04006010941660340002d000f60a070158003203090744400039040c1d03a07082d41c1c2041129007002d050050000079002c004000500c1d20340d102c0e043c80901d0b80c010b09254800c000c0b010544c0e282007040904641004908050507120407801040d040c4a1410110b04040410038004c4182001d170300032941302d003503030350b50642240c3c040d0310009490130401d4030b0354544030142c50140e9450f005044001e0009080c040100329070100c6500150b081004082643d1400c1d9070354400350301d031140c165030140054004400410401210108260703401d0b4007a2050140b00c3e1500781e2402040200600c500245626141c100700c0440c8640e000c1e88091000400c5d40000c02d8491304a100200903650002c0f0700e6110707140002c1409406181902d2180001d0045e00d86040c0341d85003000069009030801700d0034403000784181018030115002440c460039a44400048a18144125510b0130b03207490081a0180741500e80300ca12078000304112001c3d140107070b40d07446d59103030b0520b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 26898567 1250 26897317 26897323
    0x40905071205040308040c08010b060f09030a0b07090f0503070612020d090803010602070608090a050c1507020402070605040b060d03022d07290415080402010c12050405041a09060f03 80
    0x1c80701100c1e5034500010401010b800c01c0040e4000c6000f900c0880c002030b203030018203088803106001b45074401030070712007506070305003a40050800c25805800d03200d000c25169511429504291005408654000011300c490b0120b12355840003040214020701100e03103851006410310181c01111002241c00241c040d851b074945801840700c07541e010008554030760f0744e900000c1d200c4c1064000c0d28000781100d8007040ca003120000c0c1c3d480c00650040d02070b000c0c0381511402c00021340c4030003104a4507800140103501c05079483c0e1001d8001c590280c0b40100d0f0500c1c0ca0314290500c644020a194400c01d0f80d441c0d154003195001443c1030380031300c041e440311100e01c5414030fa046a0b42c0310000640450301c251b000c08a101519a078143c900ca90b000004800701c6201440030080303d000b07034028025000050000301201500c6030843c2030700140103042c4166600400c0c0ca41e00341401d080b180031004200001800c02c403900340762240e1040e03000d00386816006e5125040000b2105240a0491841038040c2008001e440c0e07002c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 26899817 1250 26898567 26898587
    0x10509041b0306051f0e010b0714010614040506010f08010b03060f03010905030a03060803070305031605040b16030e040e0a0605040201051b01090210030501080d0c0602090301022a0f0304090507 85
    0x10740d010540d56443c18030060402210103280182d8919421903908218134440c0e4240d03014640e9030140c50307003080c40c804440c1d00f12250030360b41400050150308111000b80b298101626144002004850560042c44161100541a241004010190100030743d91018072141590b00035040c1c641e032512410300050310b0703400c41d02429070716507c6c19910b00100200080240342080280d14280549541c4a4103076490740900100a00400d0742080003d00c9071182000788448c07000703e0f080050809841d40440c0c0c403260040441a000484000d07844014150400b151944a0b04100c0f028880413000b003500c251130307030f5800720300400081d1103601140c1168051f00507100c14803a004607040d05c5000c14840720740a880313050300503406145000140d0302d0482c0719001d001c1c140d80c0401e00034228528105003c841c02c444108080c0d5050394240480881d91740e00703000819034564081c2d004042d0251039548111714220500d8585520340c27180444000042c408026201140c2c09407a00180503621068190391466003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 26901067 1250 26899817 26899853
    0x606010c080c070b040f050306160302030601031506031d030a020307080f0904050c03070e0303090d030e28140619211503050c090103020102060112170408060103021302070b01050904 80
    0x14805021030044d0012000c0c3c4200d415040c3d0b0b020115a0715000c2c55207a80043d01d4242c55804502e0a0a90450181d00103540001062600003150304400e0a1840100442d81181c000661549820040d498484072007074041c1001801840c6050b1050384069628031030800e00070468200410426240c80480c010390310301d681c0280c014407841c038001c4801300041e8411156000420304100180d05141400000d440c044103001d00814081040c940301076078140d2103080102d0b8402d0719020750001c5035a8507000314060380d1094843d0940c0712f040155a51004100203401d9000b1039042c40031400c8040302120750030350382e64075007000402a0400500380c40c219816070500d0203410305000c03c1082035924625008201c0e809102500c0490840100b000740042081c8406401a0b0090005100c5140d500c2c01103602ea911448100b44620103402070b0640f642c01680c8002e0340c6400c094010015420240c411481400c3e080c83c0462414256540310303030382e11406008490080c03031504005010000c040800c0180f03840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 26902317 1250 26901067 26901073
    0x50417070807091b0207030f1401020d0e010b0102190b07110f1b04050106180b0c24010e011208040605030c090301180204060f0b09060702030102120c0403060c0906020606010c080c 79
    0x6103403443c0d00c0c0900079655007503061188182071482140d1000c01d414040d607601042d4100140000e8079a00300480d1095140350840d54200802e1080c45a03031f201714076201c4514000450742c48640000641840c1407154100c0262074102c120100160740880481d80c410060b0800816110445080c1482d0008079813412005124443d28006c03038820142c644081d500d406c41d07013403180c0d03030f02c40f001110035141481101569000291080c44076100541c0034003800280c201c212001409203d05080725411078035a0201407041180050000c022540220340c0940b404005103030062100e80d803602d0151041748150801c101000c0f000c036420b60081d034200e03818584014001d01c04010007003c008000d80c181003040780b045243c01c01c0064004411754900c012581400d0f45141020301d42c005022035948078410499040d5800c01200041c9003090400c3d42c02007056401c595142c03811881c0841c225034007200c83c4410300004030001c100c0950b000409680c07049082c60310400523186460948842d010700c100340b501c940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 26903567 1250 26902317 26902319
    0x3100305060103080421020d0308060102122a0d020a11030c060301060201050a060602280212010203070804060f020301140111010f24050609090601080408090d080a0f020706050417070807 82
    0x507403072001c0c02c01d650118000c0200d00040305483c04440502d40c50023500301a402c01a900400d019960a079444141801a241114289210380e403559000ca04d8548a0543c1800c49036500a01c18014400007600c0c07030000d00d10340c0c0381c07960040c1d40c584c2d0b141401031101c1c0303840c01070740131035102805500702182d000390040e83c89584402c406800781400b00c0d05150a1890440c0000d02144006218078004c0c983c00c030107005884207003244080180c0301c0c400603030308000e01c940ca60508410900c02548140d50a079a0301890b818540340142c10380d001d52040c4060180180014001048056030320109c408090902c086001c1c1109002c034050004e5940100c9040d1620300c69412420a031034441000040180e040640d40ba15001041410b01480b080140c01010031000602c0d00d500405009400ca03009106080c20070580b44001400710071202d4044070400c2011407940c5881ea000120141000d800c2e0001c1c0c40c129051080041c03070380c0030354403809081f580c0341c800b2000e500c9411b11944000e40444c10a41e040a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 26904817 1250 26903567 26903573
    0xb0702090c0d0c0c1a070f050a03020705070b07330f150e0105010906080c030708060a090e01140f0609150402070c08070321020a06020a110312090c010e03100203100305060103 77
    0x2201401901c100e0081502490b844401c111891b10a0400c0d8030b031418101c0300001d044650750070561310041816400c21005010035005c200784002040c00781c0c001a52898186003811040011300c0c0f034000329200a41c4c80b0312071400b000320b03400d0344805210800a080810a441c400107882030040d00c004542d0759903004030384c5400917032000e4140d80303013031300c030014031030343d2160f044803001d00c2125181c0704c0c0441800032031030891140c00050f030080b00041c0104070a68451420900701c9181c10000302650303550341032044c0540c040c42c55150307003c00005401b602914140c404034280340c6000b020418444c4025981038030356603481d030541c1c0c0c0309034100c3c0800a4994072405d120b940c0d001b1074013080e1124132192002d00200f010b0640c01c4219030101c0d50107019000b01c02e0340c540010750004e002c14814044c0f0118640c0c0214410405460144083d4421075440e040079078019041401e520b83c0701e4100102040c040c5015103000941803064001c1e00001030390380d134030103086403a03907101c6400080c000c1c0541c038000014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 26906067 1250 26904817 26904827
    0xa03080d0b0f06091309050a0c0609060f05090609010c0303060b070b0406050a0b180405010207080f070204060509061c020f090112110907080610030e0607270b0702090c0d0c 76
    0x480042d200010040340041c01c01280340070f110031180c1e004140200e00102d50358540c00400c00544038000f102c04141d0555140015840d880c7c0140300042e545080402220754400792040900f81c103800c00c10302c0d02603c40d0103e14240300f2150100e0501074400a1034081621903070085009001c604c45040c0c86140a29020815035000d940549800e403c01c4017060b44600c161042049841005100c0c2d01050700700c4000c046400c80040c026a1555802c3c0502c40106c2c2d4060b0083c0070694050122030b640b03c40741c0c81008110f42140d00443c0c003440302802040069107034903115080d008040d40c03068002c1601440000e83c41005500b1468200c9000c900000701d07102400c0c10b10000710311520011032060a1042403120108040301c020000400200104600c1c3c1801c078460452010b003841c0100f4107141032608107180c91001ea5411700041c000000c10101c0074004004410f1092544042101032461720a03085a039004030080a840b42c074416021400300e0b100c1d00b013142d0b103016440a0a0001501e22640641 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 26907317 1250 26906067 26906081
    0x603030206011a04060f030b09010f03150e03030604090609020301060306050709090902010203030114041d0d0216050307051005040e150a050301050412082e03170406050a0507020a03080d 82
    0x40544920800400c43c0c0c00c0b8030245421180315500c1076030800f480d04d4400ca402e41c901408a600381a5110030f1031900751613544500f4060310440c18003259103869494000003100d20502304907201441c0402e94400c4020110460b03401071402c45d00880c3c03a90490501000419200200135030640c64810000100041e035000f00707114520302d46035021803558602c582d5041c1e4460710402401a0020001800503080310b070806113030304a000c1c10001d0b5201003000346984510407218141060b6001e00c0c0280c0c019a81002540603207151400c071040b9003464030002c40d540308000d004c0e0398030848c1910032002c0c009100e402603800800d00d5110120352401d0422220062108683c600c1c5d00900207940c000c903141c2414002c860007950320152828400c044203400302c40e0500c020308440d130380b1107101b00d0402041201c5845607400340000c617243c2626070300d141740c10b10717600c1880c1c80c0c0b00742140400d0004000c119000720945210b41000d00340103640d00704034400514640c581c1c0d00020200040420080030041480c0e110781d0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 26908567 1250 26907317 26907323
    0x10020706051605070503040306020f0d020d0b030f03090d08161509020f10080a0504150204080303060307080d02071215060305030d0c0912110607020913050c01050a0c03030c0c1202010603 82
    0x202d40d1050000c08488510404401801552042104000041e0315500520600c000e840c0d11500b01100e02c041501680e02a80a40c1e070301c46d448140c1260f482c5001d03c131403c01c28900000a6240181420103c0c80e003110900c4042d100a0000c40c1e820b00705101c05540c1090642d10640e542901c400e007038004001414030007001d0340509031808401a09080c0182d410702c1c0000280c0300c036032150340d07801d20781e00203020010003c9401e02c0c0c00b10524203402500e0300290001d00303d4031002d1500c1c0c0c036225080c0b5282c038a143e8000c189a501c4081800d54103500480e440c019548030304241d00500d81c41c1d003002201004610284903810380761aa0000034460080040c240c3c140d14580c0910034260422022241d60b502402100d102d02c416a2155001900b503125030070712994040c10130f80c10540a500080c02c026003c4450300032400340c0e2003c503410448140500c5c501a04c0900b08941819901c8074001c24004082000800b41640c904440c842140035078403181c0b025501142002c80e400b80c004c002800307007541740300c12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 26909817 1250 26908567 26908591
    0x30114281d1f060e060603090c030615090c0405060306060d0e06070801030b07030b030d030b010306030210090f0602030708030402010c050a05070b0c0c010206090a2a0801050411010e09040201030e1002070605 91
    0x1d0820000b90303014440c100c50b2a2400031a003030711a102048a2980050101000740c46070343c8441c00207031014495907109801101841c10000841000e000c4a242c0040070040c0c156400c100900c540e42d20031050700e40080080c0c0f00c0b81d44402403011303848010104000010241d118180402c001a58000c08984c141d0f84105601d400b42d0702d4009042c0d065032580112240d054000c0002130540b0303403080d4407030005110145004034141d580d07900428191014482c81000041440300140f100140c103081c0c19000301458030041d031a01c3c0040d02c032403640f030001900080c108079010401c40d0900104015561035035803c40103a80c5003540e01c8420254a9100041048a500858501022039070000c02c100d031140300024054400c1122a0381c802080140c1540c5106040320004104115080c02c2d034148405001100000101420f00303050128020408040003410040105400340d041d88401c0c05180d0130650a080105150286082c07140c1003800c0f403115000301ea480469135a092066941029000349401105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 26911067 1250 26909817 26909863
    0x3030106030c050a0212090604031502070201110a050c06030604020409050a050603060a0b09011502010e0a05030901080c0306010c0b10050d0515090a0224040302040f020702030114281d 81
    0x81a2a54004e207052000941c204a86c001000c101590090045000040c213240c6003a8407555540602800d03800c000d124540c5c013140c1c640c11941c102e0450f1190002c0600100b405544503a641969102c25411150240038080049802e60301e540e010348000d002c58007814401842d080040704000c00044402d1342c802d115500c045a40040c0c18030400c2981039000e0b001001c13507030805800720440803260300c9000440d075946030b41d800c0d1404240054030126202c0c0c009182d4075954813000600c05540a4001c030030002040060100c60303070700003401c90000340c0c0c80742202c401c2d50790b03645900e51b120b22145d0066030801c2075403070400c0c20080040b94000c408205000d82c00c1d00c0d906c43c0c1540d40d50f41e1000e0240250081c61410300340c1440070800001c0460340c1d0072501c80342d01e055144e03130224003038031210b9803000741d415004662002149801e002d020100080b00c4d20a40107031030800108400350303030b0351400e0904c07080840c4004042c40442c1d801c05c00402d08442600e100c3c990904504698954402d19012082600341075 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 26912317 1250 26911067 26911091
    0x9060609020307140304021804030801060305100b07030309031701140415050102060f0a0e1f0506030d0906030902010324060807030203130b06060903060a0f150308040308090604170303010603 84
    0x420703203001c3c4405507a4842d03544400034031070343c25034005042668482c43c05442990b0f041e030f008400038402d502c030341d440307410a51400030050b0546502034400c840c05080a0f000303000c06044881590080c80c1c05107801b081449081c2400d50742018818500403000140038004a0603421811448481c91810380341001010980c000341500e00c1707154000c580c01a0003540c0070501143ca85401c494100401c03e10005242c81e503594002c2c50721616801c400c0f03440402508007800c0450341e22400e58050360a0700030300844607a0013402800000c5d140200c50605540b07001c0501964442d074800244c1c40070140d0261114102c010b0003500013020741c440d1000150012001445003446402506e000390300c0240d40956007a05543c0c2c210702c1e600010300303040e0403d4040c010f0744000c1e07608100c42c4c0d000d20042c3c0000a0035200002401050700c0f0040341109150070041d10410000342600300325011290403620480c1c81301100c10001d021440b4940c401a0200b4029004d4040350401100650481e40c080e1403c2044403213103d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 26913567 1250 26912317 26912321
    0x1302120c031009020f09010c15021603030b010201051603020a0203040909050a0615030b0103020d0201050f1c05090d0c060b04020403120e1305010803120402010509120a0c0e010b03150117070309060609 88
    0x45c00c0341e5894401c0c01100c0c801d500403660340c01c9440c400d000300c88009900102032800c907045402c0c02c1141466850103002850b0300b511444100030320a1009006525142c2e440140c510100441031007016800501c07017074124401c0c0244e4001d0000000140440c5450b8140140c0d9401c1000058500d2460010941801c1051129a5080740d9010808002a03880d5808000154003019410b07418840c04010881c94403090100410b0310341001010001d19034410008081105c02c0207100d010642d0000038024992900802240041d40d1311400200352507041d01e000c100640aa03900061403148540194140290401a01180d041c030580340890081d61480314101515828402d03a43c1680080003400710303882c0390707500c8a039009006050482c600400b44000c10b070031400003015203820b83c00c40e00d0340034100000c4d80d031060000d0000d0b0040080c90f5040c038400101911010302810030311911220311003607503400f50004054840d020b02d40950589000031001d4060b0080002c2114610300e00180800c80d05594 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 26914817 1250 26913567 26913577
    0x15090301111c02040e04030302070f060504140106081f020c15010602060412020c0d080309010603150b0307090b010e120c04060303091e080601060c11040903051c05070e1302120c03100902 82
    0x1c0803045646c1c4503600e090b0020350000c3c0b42078664a810b030b584d00700030a40754000d680c01a44103103468040d08211000b840d086a4103500192410742205407080314180030b016899480c403420501c016a9031600c81ca019260500200c0303408400346006d000082c5450f00459002c0c401d500400c9944954a0400c1c82280c5440e20252180e6002c07480b01a414007140100028540c001d80080000030825241c1c1c9031410500c0700340032050005510b030725121500381000c3c04580020299071206110482010002810200069492502400101c0f4080e8500341c400c11022402d500d02400801c8100d441e0b04008010190034003864030203a6000d150300d01c2d42c4001d10000c504840b0501c001c0d0020ba42082004c0307941a002403801c0d5440d0601146c5031500d030f030382c600c80c070486c01d0f2086e2207203952001503010041c08070304a290003030180780c60041000003254000f82048000b86046903a4980070710441c41030030003070164106035190b0b0b100e03030030400140190000045000e00020415075a02070741d545031703e800703074498 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 26916067 1250 26914817 26914829
    0x50901080114031002070320100b0d020a05040213030f030503010609050904020d120e03120a02190c06081312030e070f14131107030302070605011a03040215090301111c0204 76
    0x2c804021a00400550f01900a180c420b2400100908590034400030381141c021569030a90800c00031a49e20b520b0500c03030080c0c018011f6640c01e19000068001079880c00e824844e050055070009208110031038098034890140d6884103103080f0030a9107007801040742c3c100b40104400314940f44404181ca00d0311101052089074010604121000301e61780706001030b0030400c03a400074440100a0305406640502c40c0c4402140c0781d50640e5154401524028540410041e10070041d1240485400100d0210503540c000c0c1ca24600b403080032501c03282d04400800d15190030250025040c03402170345a95901da0044e20310068040110344d026601d0364001d81703203c04c045c0b01c0c0c1c1003200c80301c0c01c2003155424003a01d0006d003091224000180c5541b501486203003540041d0084002a40c00901002003011700d11482c1d0142000c1412014198082005001030b40b00c00b92000e8410003c651a590211258800300c5010540180c002c0c000e0450a281d2070303000703411141018030310204c1301300301802d032408034429a812105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 26917317 1250 26916067 26916073
    0x1e230a05090603190309270609061a0a021905060a0b0301020901022109030601081509010c05040306150503030c0307030e0607020906091b03181509060703020d0b03010c05090108011403 81
    0x1318210b40307100f0a91004001c5050240406000682d6840c4035030a40e40c0c246c112603030540c0304804142d001f0480e04075820402d0414642202803003082c1540c0945040c805111051650300c684ea01030980c5001823404650280f900520340410401001080d194010f90341d00c9018444054050100343c01d0380150300398240168450380014040240048003611000344101182c4e10341220034010038180030017604440f01c03642c00950a190108100c1405981c0726079190000c21120041d008010400c2c072941c40041c100c1038880a10340c0c40c04c111000b800f0002d04c4020100da5440d08204062070300c80d00504025004641d403080c0018041c00c0c105e04503034489034001c040b0740ba90350b214010041d8a460141880100080d685074500f40340040d60b000398041c104024800150b00d141d0003400f03240c82c2c039100c10101c5800440d001e00100100000c1c50f107030000b0990501507107800303002c51080300800c1c101210690541c2820030030202c280c2c0000082066413420790720b601303071680c84808103c0034458486116400d64 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 26918567 1250 26917317 26917333
    0x1104230615040305060a1409030301030b01180b0a15020c01031112090f0604050106031203090309050103051503030f0919030506010501030c090806040c05030d020c0a1e230a05090603 80
    0x7180074040048549540030400d4282516610340e80d180c880c08641d0315400990f18102000b40c40b08040001d5482070180300110300e1036043d603503042010704040c0325906034012000b00d030303c20151007034000400c0003c0103083d9041c90313569080b4100400c8040c22200b40540100d0322000d090354400d000c0d001c0f504080020081c84d1400348a44111818001000c440060050380c07070543c81d41030103000d000e00843c0100000705d01c450850404091000b040001c81d010b0500d0f086031400065040a0100100ea00034200000e441d03880c00c10035940d481001110f80d9040c040040c0000720850303000003804011f1000c1c4e5100b20540300000340140d920800f07000c0170f840c0cee52020004118542c17003a089080021180e25103045002c2d0342d4814245041402d0318112002c5450010070b00050608201131013005416100405400081002042701c0b0b14590103a0040243c9140b014131803540c494010b0001055840407400c400312540140c0303100e159610314520310554102c44005040d107400d40d001c6000342030040c00f800f405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 26919817 1250 26918567 26918569
    0x201060b180102010204170709060504020901020d0c0219030303060e010803120a020f0706050a090209060405060a062003030106020304060e030604021008040f08030108030a110109030c03050f0c010911042306 91
    0x1030758100650504564081001182146442c0f10f0075900c102c4100081420f5801e201001e0146c4680c2e802050107184180442c03001c0d1380e80040c10202c03e0401e810103c68094841c000304070b00c00c00c00b01390002c819040034000410564943d0011003296400d0070082c445989401c403140d140c0c0b1404140c00382c080e040c1004500001c025500404911405540c0070749032901950b40e1005584045400342c10a940d0782d0810b4040d400d0040003140c0c0004211820080303407901000180032112140103410412800034001c08a9203401031035009266010b00441c2d0f103075a958000256258800d01030000080c0d0741c07401c100c0c00fa080006544c0c1c0101d0740101031040c0d20360320290840b1a440d000344283c61100d9081070040c00310350744100550181009030043c40d518442084054031801007140214403d80c50701e181030f000300c1c4d840000001d401d50306142c120359070040d11040c61098001d21841000d21351801c0c9100003008409030b1800300b0300c207007900d040c04900c6d5249402c4040562141c041c0030210032403070000b002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 26921067 1250 26919817 26919847
    0xf040305030708130204090308040506060d0804090c0302070602130302010f170c0315040903200c030d050a12140615120103021003060902030a050f060d1101030c0c0f050601090506010201060b 84
    0x1c005041c0000c484c4040311600002d0070344005100980200e0100c005110034042c05020241e485101030f68800243c1232555940032092203503200d15a2100e5940c11560030301ca22940444400c1904480103540361130807040c4d040074180d4240300890208000e21034021007140520503510401b10803413095461981c50b1701c800b0102c1d500041c400004004035055081041c1c2c1c0b6403140c0907056000c0e80c0c031230030142c030034030014120001e00700040603450740074400c030029540e000242c80d84c1e111801d1400c540c841d01c20b200241c0c0c280c2107440c203c03002e150810a090641ca00c5900c0028407909003112000384002208495210a1103259812405003d5800042c0003504000b03c40c01c032034440601d1f0000d030281d610907000c2c0c100d0300195039603500a40c403101172182d2100310246184d00400122884070b054203048d03642038a214290a0740506141e10b803505000340600034443c019699400078151040750025151490301c2c0d04090080a00c02841c1c41c0c049461540705120707807410386081020a0f03141083c81106018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 26922317 1250 26921067 26921071
    0x40803150a030515011701020f030402041515030e010506010e0120030d0c020a02100e010804030315150302031008060c0706020c101104030b01060806010c0605040302070506210f040305030708 84
    0x90050304030700c000000510200030709000c10b1100d05010f02a0350400c4c44070980f06400340711202d181d0380140140c05030048041e088a400542c103c40024680300707681040340c10307a0840d40c050703a9003680300c4444641154054010004c041c0c80c0340000c201c2540e41c44d0041d150170001d81c01c054009a103e4000c062544a0320081030001041102143e0504c1211840141511103a10710140140c2084c4800011400c000c2e0710b01c0d121058a003022054988040b00082000000810141c00c064580070b03924510303d480d0a242020309600c3c0d140b080c01d0000c20034050084e40c0150b41190b443e18220000040d110004241e0502410404042515002e01502d5040c003035044021080258003c0c0b803002c5120580318480c0448101c0000c140030346862039400d1200c3c4620f4140d0184003481182c80800c40c141c0c1cbe100e064200c65035406080042e49807100e0a003240b46c00404c2d04100d0300250002280c4a061702c031282c0425280c801031720b4203802d41c1c0e500207660b90408000e1710000d000c03030700074400b05030795078054003d540d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 26923567 1250 26922317 26922319
    0x80f0601091421031305031501081c050c070308120609010510032c0c1509010c0303090f0203061906060207031104020304030212070c0e0106021b010305090c04111b0604080315 77
    0x140c61603081c583d81d00d040d50f00c00410080c04d410301e01c100704198101409040e511030805200301045600d0031040b1034503101075035400b07110300315003980308201103000d03400f90303400380300340c4401c80780425120310384a02c49911800c050101110a003000520510b420100e00b030690310090f140c11001c0c010701c7d03800ea000e8584000c4440d503030281038001490000d60880e440103050070351001032280c1250007003400360050048240300704a0780104a900071a0f43c20103520414242d1601d40000d00c200c0034117115810145038007009516015020500a0a140e01c0310708a140001920301084107a070303908410f0742da40b401444014012207500c00d1a1141e4902035001d158000e019006a900c40b078030b02d400360000d82d0b00100c4110340390800c4000c1444418a1031500f5409000c1600003001102d02d110762090741001e0050341141015118000510510700c140070910a10720050030620807460640080c45207a0030040b55041061401d184d00e4048800015045000755040b288c01c9285454146802d40039405607102e81d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 26924817 1250 26923567 26923609
    0x4020d060909051e031201060c0303060308190f0504030c0b030a110c0307050d030509030306040f06120309081506060304060e0109200f0105040605041e0b0a080f06010914 75
    0xd00701c00c850049911072031103a8094030003815507803162040d001c2003e51049041d4021300400c0480340d26860083e040d03c00f181032032100f6905501e011030107040c1079040207004c0000810080410740b4404c00c1c18103540702c240c403810189034070f00c43c080f1540c0c002c1c0d100c0640342031204841007250144020040d40c11a2080201044003008001700441a0388003100b20b05007030b44000740802c00d2101c01d020b4404451841d190500890800040b016900d00002d090280f00f155542034031032190482d50300030340061242ca4900343c0a900c3c642800b91023140584500402c6010f0a542c101e14071961010047c03003004000e14844c107585a40d154070340100403c5455000d0381d0b40c0c031121400454403520060000c0a65071000f021044c1c0d001d0140100924454803041c18048180410f020441c4c0050644050341c914580740030030751001c0320901e01100a280e001640003040022940956980041035900c140a030421220154036010011180301c2e80c14404d5102442c1904409101e601d01001802818401c201034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 26926067 1250 26924817 26924819
    0x102030c0714061b07090501120b01030209090f01060b070303110a050a0c0503130b04090b0102150705160b090a030813030c06050712050a0605011223040201021e03090a0b0a020a0204020d06 83
    0x4115801320904114810503417001c88100b104521034001c0a014110544004811201300c0d51803141219043c080244600b02c2c2400107005040704200c40c00c45e45080e60000c5c04074650b103ca0f20b280c140d11107541a00003d0620814440201c849801c5032841704a03030703840c24038004003030400301c40f07408450f00300b105c0c603000130800c4052514600c52040c011f4409401000d90310391030700001408454440340741d14159001001c6c3c51412100181c1580c4c1c0c80965030a0941c2d65000440141e035505e03010a400500f81caa80b0f0301840b03000600002c156140d81d200703032608480741d1900c00c0e00104a000550f4024009025005103000040d81604100d030803103003504041c0c80415070309140d102511012900152800c1c0d550208200c00d603400030894584449900013040024060007260400f80308084141007569803d00c0480c007103910820100018840a0710007080f010031042455460380d00c6820751f54801e995245000c03d03069a2a01291009011a0020181600c0c590701f4003003e07400102c50409000d580d248 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 26927317 1250 26926067 26926087
    0x60c01020c060106030b0f010e01110102040803030a0c020f1906020a0512150406090209090f04031b0c0806160f030c0e0301060b0d05011202060417010f0c03050609060102030c071406 80
    0x9041560034000141182d503042800c000c048851450b4050b100c1c41850b020a2843d903000402041160350030300e05219600012000f19019200340d5000d074865120000030096034190135849004071007245e0382907a4601c903120006545d9030756228085440a400b01c40342c100050340c3e960080c40100500c2c1885814910908541d07800c411045403c00710f028584078841140c3d14080c410303100542404c4a045040c0020f04001c1585001c000786659480319040012034103040c003070942003044184280f56900303070203124035001540902e184240e09042c400e0401017030640b80004601d009080f8195156030303038040d00403022005089090b0515043c0040100d130722800351001c4c09070390f0240000703034a041c0c0d0305e207c502c1c015012604164130020b07001030590000001a41c51100311000c07a094001d410035100a04082d15004102c0314401d00e28880c076000403100041d0300350f0011841608105e45401341a6603003030059840388605448810540c128040600c5041c1080012860a0f00c0243c90141403425502d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 26928567 1250 26927317 26927321
    0xd08100302090f2514090301020903010501240e0105071e080a17060603101203050d1401080d0e1309140a0302070f0902041203030c05070b15011706091302060c01 71
    0x5118018a400b1040030004e0348061000d001a00580d03640454285039030301c05000f051040402915600c00340002880340e1143d03004d40582ea100c82c4010000c10803541e40d22200036907508541000005203520380251003009005074440e40c81ca0806071942c500c1d001841c0c1d10910b00702d49140c4484a501c0c1c3c4c4e8440e42000c02d1b143d00103020744103000e44500b0448035281c000e01d01c8c008401041c440c801c00d82001000b4084110001c81000c0b203032a007100282c00821850143c07003074020031056507104c40c17034580b030300101041800072141240e45139019114161410039003200c691280c41d4590f40c1000308600c502c084141f1660200040300e014009400d80000c450490341c0c2081020f40055005a020081c18442c40019552034001411060011403500349080340758044000900b0000d814035559034400003141d4003500c101c40d81c6540c49003030918a4540f807036108010360702c0c00c2c680c603000407851218080079800703602c5014001c603401040007449545000358401c9200f803649c1c040360088800d120345040041c0034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 26929817 1250 26928567 26928571
    0xe0604080904060e06100818190605010b070b0103020918030d020403030207051008150f13050403030b011d0f0402070209010303030e192004021620040902030d0810030209 75
    0x303000300603519110581003009480080c1c20078807a0410010a20211780c1c1c400b0f41d840700c0000c0a00b132a00344c40e611040c22a40c003d01ca040710741414090920120030001300035401406651090800b001035903241c0104e440300f0700844000800750040f07840184050b00e45800742da940541000124807082071600301e0070382190841e4840446145d00400c080c010142c041c00000082d040659800f014900355400007400f03480d0140c662841c1810004a0403815101e51920800094024044003020130352400180020a8100c4041c0c00091810380c404103030b0340c0f1940c4820f042c1b80380071041c4802d4680d0391081226140d0391034402e960083c3d0070402c1d03400603151010300340e000314000c0d10000f5121300402191801d061852039202907414203030150b000003c500704032800c100000709034120941141100454002d225000c401c400e801d000079542420807400c017190031140da8140024440049110061000b61001c840000b503240e0041c0c131a00c06950710030466254001d1101c40e4850710076940c1d0300410891601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 26931067 1250 26929817 26929823
    0x15040902180303090114070f02060a0c060606020606060702010e0301091b0303020607030b0604151701080309011419080703060506030112050c0108070801050f0604090f0e0f0106030201051209010e0604 88
    0x7148a01c2044964001e10300d2540c8181c01462401d58658002041d10703254526804400d42e000c902c180501c081600d0088540e81d01808036640c94044000240c907132084160112072903401c04a0116409201050150043c400038100ca030500d25180d0040d00c1581c900c02c18283c1540d070b100002804101e00002d4141004c0410154440150650400a0800f02d00508100a0505140c02c1c4151500c27080304840c200c50030040c8901c0300f400031000480c1d455402d60207006114000400114418101200600c4201001d03281d00c0c214a10044414142e40210115425640140c804810816015021803039028401e444d0000c3d42545920021350103400030b030441c50006024800c46410804200308500311101e090826900d030b443d00d541d00502d801814000c06024100c8001c3e00e42c02c1343c44500c00e071405454582818005249030005050041600f804548034a20411003041c18000041c4a407070292501a03541d01d1500500006020300311070050041240d641d42d8000c541e00e030030000e0110500843c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 26932317 1250 26931067 26931071
    0x140103060b030d090f05060c010906050903030604060509040503040b09010207090e0d0906030905070b0c0109080c0d08011502100203040201090e0403080109150b03270a080307080c0c031602150409 86
    0x1084061519041ca030f40418001d03c480c4d41070a0005a65a202001c210703581107400d160f0350409040800d000d000301220061006003800284020680301102540c0b140400380d50400c80c6070340c2c0b8410409110420303240500103800401c418451202e05000a001862040c0121024036603680e010800303c50110305603055542042d442c2004065001a65000400d880d02e010310005081d5201c450300d03a6420b125211801000007200d00043d04207400900c442908815a95180c585060007142c070307864151081d2001600090000c5004050b556036607003040d000c0e500810b66030340d078000004d0007548003502c01d906100e080d4400084a205020700184076520aa4920a00e5490302190f00c0c161110002c6060b800d400d000b1007030100a4815060741c0d0b208444048c0d000200d00d031881c60ba841d800d1003102500c500e0194105100901c044000114043c2e081607a4015071540d600c80401201d01421440b40b400750820800d0383c04a0100c8400d41c1710043c001425498020711044003020594415441100c1240d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 26933567 1250 26932317 26932331
    0x60203010806070e030309040504020a0b0408060103020a05120a0609020d0b040303020c0c0420130503150115080103110f011707030e010f050c031b0405060d09050d0908060105060c0114010306 84
    0x3541c00d004540d080441c50078018a900300080010fa160f020b8940b025014590701c600003010f56503060214801050840c860b0759845445200813070b141c010901059000300b0b51514000b03030504040311010740d00000b40000c1e00c00b8042c0c6540b4100544032400003a80d00c5128130b05010081100e2049490250b440382d100141c0c0c8020302c20380241800046130b5030340d00c11890095030007000444000d41ca02c01c811050315056130741d503450001038140c8440760001034040c4036040c1145910701520f0116410385144d0f103103250785002880d000720b40071002404014400401108041c0d41800d29042510700450141001c0350300300215803906154280880d82400000c0e159960000135010038403e40c14200300129041c001d6241c0000110035912000e4600c1a5150071603030a240d01d40510000c0e00c020b040010101c6686100c0004810f002d09040c0f01c09442a000308034100282030b015801510840e608503001d010141e18000800103241c00c414003d403800e54a90010741c4c4400b00e02e5038454061482028001541 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 26934817 1250 26933567 26933579
    0x71a0103020405071418060403050106080d08251b12020615030a0b01140604030b04050a0213050402100503060a050406080d02071707030f11030307031e0302070b0402040c020a0206030406020301 85
    0x180d24040e160b032050160710412221002019030441b000603248002d201c482040590110b0315030303c900c1d170000d4129468040702003140c1c50f02080b11502d040c40b940d0380556a84811914813244003485485241d10001c101d19440d4007030040302c0002d41c3c544a01009281144d550321025518640300e84400016040b0303078100310020748920054038120340107900804110059988004c4481c41c180204022250704143c002c00a5684408503005981c0c040e24180c1d40d4103091602d00d0303413900d404004911132009064038800e88003180c4100c901c269001481d2041003800c0060541d036030fa00c050002500030300d00b6200032810343c60700d00441006005480040444655180c0000d05051060300180d9010101c404030030300d03202d00003070769606580c1c10420310740341d12609103407540b0b4100020540c15054000850b201c014560041618200c0725a071180f01502c003008030000300d00300e12607107034014800620380d03000c1005400e107a40044a002e18a00480d001d40e04075400040060700211401c07180c0c10340010041c001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 26936067 1250 26934817 26934821
    0x905090d021e0604020f060c0f0c1c050a0222090803010905071716020a1709010207080102130e06030c15071a04020a120303060b03011203030b0f060909040305071a01030204 76
    0xc10480c402d000030500b02c0e4100c03083d1a05406803000e440b81400e0103101c1c0c000d40d5004111510090040b0444004569581e40162941c001a4146118500d100807100181c40c041603084001c580c0800980a913164a80c2000200031400c1d0141d0302da100c1000c040e20f500320703031845009040c0d40690f004c03e84943c5003030495800d40310010090420826184900070800a0200d1180c2c1c0000740309420341044048000201d01c1c010706d5403009040c3c1c090742d80301c00ba007000002c801805407500a909580c186512107a03002e0a0b849160704a5035001f484039801c2040d4428401d0361030704960002e003a00e9070001c0d0b50b00000c60703924016a1400208100060300400c004400200702e03202c84050b10080800d181076000250480c11510801e0100c0242610800425210381d00c10390252071000e843e641c40396104d116580c040c058911044020074a8485a580b4518001c5041c2c6600100206824900b01012040c0300c0030400140003213080c480c0520003400028004420061071014881080d00d2a601d54010442 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 26937317 1250 26936067 26936083
    0x80109020906150a05031f0e060909070b1b010b06030709210c09050c070204090c05040f0204050a0b130b07030302031e04050a0201110c0306010902040602010c0203040605070605100905090d02 84
    0x11207402d08883c02c0701c4034103800f015030380041240c1c28403a80341d07542d0881d04410303504004090040c0404c2d6500208c1c6800d0318240c514010b0205580f0b0306c05954490b2030255441c6810b016201030300c04140310148040d6440e1580d08a141e0745200046842448040890543d40069455030080348000c0c2d07003400340f210550600000700c5c0d2181103ea21034425622130b03064040c1d0b1030041201300c50300e40c0001030034240b4500c01c4440c119070140040150403140c0c1015a01d03030030a4052140304605000d10610000d1185c020b48041d10402400701000034680490389405034021404402d614952000014000c112400030342541806a00c004d42d030307403034542c1c2c3e01804414010719000e042d00d01c880130b0001183d80050704c1e002c0c1c4e40d82070803d03900c114851030b00340345843d40c1d84010365458407400f0b002207882c1f006034010b0804c680c441d400030b212460030200c041c3c0e2680194010600080c1c804d0001c0c901103022500896004045041074081c826203403c21042550821140201294005102c0400480c0d0402c5014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 26938567 1250 26937317 26937319
    0x90303040306050a0b0a0617130209131217060910081203040c0b040305030306040b03100612150b0102061603020d0e0309090121020d050316030903050c0109150f110304080109020906 80
    0x41619420f040003d00151104c2e640c510003052312200240143c206201c01440c03040e0000c00001e00e500d09141c154990300080e2108403904000a2460499540104c10110092155103501407184c3d40320802d014101d0001443c610360306c2d4003007100103480d0105200c080003804542a4080d40c91501b03062450394049942c0c04005800420401040032441c04003d49400c4001102c0200b07203c2d10000000c0d141c80354405048011502c1c140313001800e044032221031582c04d0312403075032170200c0d0744514880000c44050009040c00368007c0000070300d4011440301e0380e5040008504006080c83d901c40b20480c201e80001000c10203d910010b440d1103503162103600d450040124107920140d89140400800c101da504020083c062126401020108030003402500c0542c8904c000c080c0e000e007200c0c18000c1c401c038020b210a0312503001e400b002000c294480e060010a503a100b80a28002c284080012151a04030003030001c204082c46074003480c2010140002c2000307000010003c2101e542a0041019040d4040d0080d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 26939817 1250 26938567 26938579
    0x711030301140603060d080c0d0801080309030a030f0201150303050702090a0506060d0917030c03010302130207030f050702040b030a0804170105040c050d020a09020c010c1223060105090303040306050a0b 89
    0x410098000309001030310b0344030943d03285480761141800710300002e40d00c85004041d10000300b0780940712031001401030100881566080b0b05a6a18421103840780700b41841d10b81c040d08002030318800701380608a5201045003031301c000102c04621040840522046400440025100040030b0f0150f250415056407c420240b0b1b0820141c03c080c8002002c5c6d206203081000c0098841d00000c09001c0c600743e00c0f100c0104000c1206641e8130b000007045089900034002248990310711500030040708200e1007660302c0c41d98103444d4103141980ca80000c2d5440d800000040303074465101c1c0303501301d050b840a21481e44d907288a0030310a0f032546d00381140c0b500d02807500100d0100582c0351804101c04140c1000000c000c858064414110038941030020401d074280326044020a14000106086440415030016844034980d6940c00900713a5407030110703001e90700f00c6800c1c81c08860002c51950648442848580d8210700d050400901d03082c02200400e0943e0496401514082e54500c1042010642c601400140e400101c0349 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 26941067 1250 26939817 26939819
    0x6050a02180315011404090b01080709060824060609041805011803090905040c05030307030c0309050915120309150304021806010f050c0703140a031205010f05040513060608060711030301 82
    0x10102e0304081441001742e014072480050010780c4442d03020340c0b10b80d5000507404080d5030312407d009980d2155803040540c001d1401e04006814007001c82c014842c00c5200d0f40e00d4519032000b40140c8500d84001c0c0070305601020400ca00c004c80d541e80d2080084540c1414040e1414503810b0a1040c01c50703801d8000000c1d468032036a5450006039010b00310405660400e1740008943d169410075080e1222a074001030780611001640c0810701d44c020488549603131095030b58500d1281c950060124060b000c2d103000450000301c2d085915585040c811220a000115084030300784402c5400050754244423585124540d20008240320070760925200c181510510160804414144a00000d1030b0020307107985801080300208602d44d08290a0049400440e04058500c044000704880c2e01e44640d09010202c010890005030412002210b0140310304850405004030801440c0000740000351100a2001a0180f01c80541e017000900342d20410300071700310b2500200300901d440b0802900d1154241011b407003603807007400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 26942317 1250 26941067 26941093
    0xa0504061a0304060204030f0813080313060507060b0402031005120601030210110a0b0408120604050103170f22030308011703030a09020d05060a0509190807020103050c0706050a021803 81
    0x1000010070408400c03080e54980e15401c20304024080c43d0070082902032110f0304c0c8418404000007414042c0b600405082b41e2542e0740202a503284289100d40d10074045141003005120300403c0509a0107004810110712040894002812a881100c90340b03164500c100c0203108a0034011062400c0070443c070010320031941150000f909880d020f494810400c17089410b203a000f1384050092100c1d0503841842d40d84181000d00e0a005190005203082801500d4840000c9951a040c0540c6040380d800c1544541034004203070f02140554008200010040010030041e29250a01d0f0414044e04c0d400c448064166030661038018410b107010f80c05100f000035825040b1501d80004000c0301c0d0015208680020b54105502c00f103030b80800210b0005c3d2813405210208005c4030750382d0300030301c0c80750780c501054842e00d04000d0201d0411050221003d098000309010500055000ea8400d641244141c40c080d424441160f4811058410031104407a031160003107130b9034100300e115686c01c1c441e504084024080002c0780c0340d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 26943567 1250 26942317 26942339
    0x1508060109051e040f02122103100b0c0115150e060a03060909050105040203190c0b0906090a0617150d0308070318140706020f060f0a0612030e0a050406 67
    0x7015014040381d032200460a110380164801000b00e088501040961815080c2078402c00315408080e40a510210341a0020042c04140b4103410b6400c000d440e580031264180c401120380004110568403562804c000c900d03c4990000380c03428010050011902c80c282c0800d82040440c11b80c842d00844200341d00e00500345821510303403600c1c03a10a4620507164800c4c090300302e010742000c5e84080b103001e180c00003041c24050103421592286000b41c080351010b22000b0551101c0108501e00a0100c019500042c820481a0001002f07100c0b00104081e08100d00e038000035240c81010792000021a604c00b80800c817240c000c81213154448980c03101c0e401c1001601010403c11009050b0040810035030000140301c0038001c0c0e01419180182d155010480500e07484d01043c4192202c044c0080f5100701580001c000744005080300814442c040542400d44031400281394204019166901031501c030b410105800d0703001070310761031380c207000b982c030032048001c1c070018442440a131303800c024040c900302101844444401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 26944817 1250 26943567 26943569
    0x6060607080c010207020423060a05130213031202060a050912040603050a060b03011e09020a020705100210050a1415010912060216081b0105040209010e190606021015080601 76
    0x705034240da490054140c100c1c020300c12540c00940c021718080c00300603c042000c1c0f020b03a81076619a000b60703140c0c0f035210410101200c0ba100c0c3c1e940c40a180c0c07007020701b0300200340c001d007806450128100c00701e42c0d03d070f5464400606540d001c0d07000680c4007604015441c103a6015154112a20001070b1072035520b002c202507050321413402544185911000416002d2900707910040040c02d80a041030707180e585443d80c1c2840c0803030444281e400d11030b0300540070030540032504c01c6030621003a80d00280112442c0c0f000340040c0300c00020f44001940035551442851403114040c8034414401d120380091101801d0302d86110002d8060030211a940032420b2688150360005800e609640c1d41095500ca240a94a004c1e006031254150b8920780500c440384110801078104083e11202c51144058a1a920451101c900300d0f441110040d503c00b140200421894a4014025800880e00300752014400b0b40c0c5064141622501c0d4005030059004d03500040c8001858071074000003805400b1100d03445484c000c80b5956031241 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 26946067 1250 26944817 26944823
    0x80112020607030c05150a1a150d20030a050601031d060c0c0115030f0201090e09030d050a0905030c060f06040903080c0d0b12010507030f0504030f0c0203072d060206060607 76
    0x180070104001d01204201d03080984a4075080100c441c07404828000241c808094230b2190f0750b64002c514107682c58a0b80b80000e40151944259052509503a40c0c1030103880c54041c5480c20b062b901e803980b0402e01c106802980308645544d0045803909200d4001011103c55502945041989034007500059101041c3c81c1e401141c90540c65442c0c1c8075003d8a035005190300c40350440c9a4922100001c00c10290703d003400c0406000b600c5070351803555510a0104080f0f01213a00c0d074440c1d0810007040040b84081d070b0099400055400000440501a03902e40d842c582c460174a5910703d81c483c5c1d0401401e440030750b56242d48044155000c0c42400310643d0060101040a0081d410541001c500094a8003281d0702c0303103280440c0280f40342c01110102e1405802041c090703410100082c101804803225030440c0c0103203401036034150344d004485608041c0403296410703a120102d078503000f140800100011001d5180a402c0f940041c440ca000205520113103000500340c1c801c0702507400920170414107596000c20f8801442e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 26947317 1250 26946067 26946077
    0xc0603010b12090708070e011404090c2309010801090b0a110702041a060f04080106090603081207110708010c021c0219060204031e05010b04060f0501050c07030209010b0a08011202060703 82
    0x1c0f408011400c00115030008000f40c443c451000640c80146c04407141280c40e1501c2606103401c4010510041d5020007602509400300c885e8200213540e10f004100606010040c0e007170709104031a4000801c0c1e143e0030381c40150303260345039140c8006010450100301d40180044804000b040203200511040d406040c402038480d41d0344e0401ca0b0511003240f003a0390300cc158020042c50303451a08000c81d06040c0c002e402140d81d1741d07181c480b01103103222441c81a00305803a045161603044c89507141c10401c40040c001c000390204003a00c00180500ba904010b080b0103490100b0010817500c282c0c0000a241c140c4400c100c005c041000d404650882d60049680c1003131481d6a0715114912509041c004040c5c8525807005040d40d08001d071a6030b01030500101e07003d801340324100030312a40905d0410081070750b8160180d8001191407000400256016030010310541d5400c9050301e448690340e400080d06204240d001c402e02e07007400948100c0c0c0d0760f0301110f01409411510700d5030310200c2e00303500410312602030311300c0003030502c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 26948567 1250 26947317 26947321
    0x6030c150201020c0a0303020a02070f030203030f0306040902030d0f030c030204050a0303050306010c080a080402090106050a1409010215010311010e06030408120403051b0c100203040608060f0103090b010603020306030c0603010b12 101
    0x14403e404441c108001c181c100c5a48851902c3c1c01002507014902030001805100004102910701c00020800c5940080c0210700704542ca005404496001515060b4801c0e5a07410300c600607281840309113005010703511040106900100d002d070548501c1c40d4440101071041000f4480344d511a030141064030741500e450b98807551010b0042c1da02001c5039070094084c1201042d01300500b40c0c44907d0905ca42e2080d58a2115640e0b03418054486010b202d00200c08218100c4043c90003080000103402e40c0c050520465041c1c100c0c54550000310b880a82003598900030b6254054820f58000640703844942e03040c0c500925501d465211050b807409003c04180c00e454104020905041c4614107550049110b00030314840425920213866440d4542c0d4400341c040c50003c2280d0714050300100a850807110207455000f1950f580ca0708100401c480802c010b414195a82403da022030703c44880c2034060100382d00c00598a0901008251030100901c1546115980400050104960003000e4400e401c4000070040c0890f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 26949817 1250 26948567 26948609
    0x414010302071401060f0902090f011d0a06110c0f060f0f04032102010c2303040507030803180f0102040605160203010b061c0e0a031e030b0402030a0905010e0106030c 73
    0x3038402c0390000303805005925404514228103510460890311a610102152940d5003669401c4e405450700c62540254515101790607540280002d2160360a050350304480c804c24100041d4405805401600000e2010342815154200400141040340340880e442d004480d203244c00510305205049000345074000100d0b01001381d0851406441c00b443e0700103044881d0450140081402881c4103145030010b608055a08a8180c01b45103807150341501c80308803256401801d9100d803019400604201e0381413003400300010104030540c019500500140000300404d0300081144c03032402914068514581c0d104000810a2a41000441e8440c44900358800068042c600000c0e0041048902158010030006280070711014200710a54000c900d09008004c001c00302001d840c3c1d40c1103a40b05c0103012800649900000340e03504403c08002e01c20500d400f0601011710401b04044c0d0b0000d0341c0c0001d21507103951080007002428060325120754400743c001c004c0246561034104903414184034000390012070000040ca8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 26951067 1250 26949817 26949821
    0xc090106050f0f07030302070203210301060507020d0c03050619020a0503010501030c020c0307080705190305030d0e1006030b0a0e011a040b04140c0405030d02120711040b031015050a03020604140103 87
    0x1850520710284c49401c50b04000d4042e50041c40101e00c07c1c00380e540c000201c2c5011100103100044002c5545080d80c0c02c00d0320a50301540140f5007641c0c0300c41ca14800c180011548048480514850400350500e030800c080702800c944034014030050007a0050003051a019481026641156400d18000c5019444018140c0c01c0107103015142e60140074404000ca4880c0c7c0c00541c4200706d40d400e4a9120f078007000a911207440c1d46190100411540007000507400b004010f800026607811000f0940e820145048a83c0c0202c1e01e00d64000c0b0340529001c010810000510301c500300c54002d46a009021030604049402c0c4c0c031082140c409881030b95500900c43e8591200d40c000303000c0702c8021b008801c040c28100b0203000c45400c81e105030340c882d2180c0c00c0c001004920120b0102c46104180025609107001541c40b080e0321250540d0303d0342c009039100c02407180c0303541c2008080300348a100c4500040100110980541011858024a00845081030700b00f0060302c1e80421072342261450450305110500707010040300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 26952317 1250 26951067 26951077
    0x30f0f0e040b0a08010e1b0411030411040b090403020604050c0105070515190c050c010c0504050102060c0c010b210706030e07030b0a110403230a02011202030601110f0a0b090c090106050f 82
    0x4045d600c0c007054100038540c00124194142601c80000da440784c83d2000b0407003580d8031400300c0c01c15004107101040015808903540040c11a00520100b91030008801007251031404503400d400580c8901c0a010074040203022501000c00c00f072826901e000c0c080e4654540d00c13105a40c4007030f1400c00d060000f400441c803284240130302070503001c070901c1442e101110080140d04640078500c519460020710356000743c01001140c04941042e00078000d642e48880103140b06411444980d0f11075529145001295520500c51350912820012841c1080c24101c10903442d140300d9411140501d4a402a224802440040c211044a51140b80c40718942c1d62122801c002e0010633007001c44500c03010074044100011030841519080d403041203004051400c4a0a55071030400041c0170780410301c80c0d121b11034140d2254004690002c0e0605010310300c149807002941c40c000d10102080010342041c040202001b00c031310320154010020400030481c03000f094000540c1110103104820034010300240d6258050a5801510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 26953567 1250 26952317 26952329
    0xa080109110a1b141b0901030c1502030f0d020a030e06060105090f01020106051008040b0708070e1309050d081012050c0405071b0309031104180201050c0a060f09030f0f0e040b0a 78
    0x61a1004c04100c00c1d40d500001c890440301215004041800b50a00c0800179040301d401c4407010310000d25120942d10700206d2119007400314001045800700ca01403010061025048041c0f00607665240040020101d80c1e0350381000c0000d80010051050b00d0303078020180c40d440382003254041030004890340180d006046d103610994000b4016102c240780c8580204003548a0760003008080001d903202c42e0125000b0404481c12804035900d44203504540c1090020910240544040044c50900d2070700c1d070034605546140400005001442001040b4003921000c1c0c00906c0c4405c01c955800703c00c1ea55003602d81102c000c10318040c0c0da546000031340c850701c66031803100b1260074507030242c80114480c10014800f1405000582d06840c03c068039482070300b0544161100207075030380360060050704107a00448449d03201090a0010b4861100e04c1c1c80454940e11451000300c1d010440080c00d00010b00d006044858890440d5081c001d10303420515044d41c010341118142013003114006240103104001940151080e0050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 26954817 1250 26953567 26953583
    0x209011d06160501090605070c0c0308070305071b06090506070c0b09030102070c0914060d0305090120010606110c01050a080c0922020901080c0a0203070605090f0109080a080109110a1b 81
    0x1a01c00e0001c194405417a09001d1030060090f50f40703081d020303038100300c0924004100c003259101c10008920208007500710148a40740c03080c81c1ca4065211491481c94003002e030036951610081c100328041d0083d00c3c0400424050340c5160800c4000d03140d1400f01c07413042c0300e100d00e00080020281415036080d4100c0b00c21543c001c010041460710707620074000401c28101d10203071342d02c1c0560200b8103034640f800d07070480c07907aa065a4280c40d1541d2040111454441e0500d42c0300810120f81c5401c2c880700302802030310064942552102c0e0204c5004036420300c0c0040035884a418007904000c018400c5034000326081c2d114a1451045a945520b40701050503a9424001d0074070040e0040705c941c0c14100359130014508000c0c00da8441d04261546811346089204045039500540e00400001b00000d0f91900480c0d800f100110503650300303000c0340307085d03a084d2811000304551011000071200d50190700503504501400813080c0c1040182035004134644503104803400b04040c003121300d40c00450500342e00750001080d5404450 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 26956067 1250 26954817 26954857
    0xd030905011d10150b070201030e011407050c10050708012303010212010905060f1c05070b07030f020607030b010f0309020d021207050f0f1309080d060e0601120209011d06 75
    0x100b0780c0318840a10000700c0607041002e4a404c5110410400d0300792000c00d04503914000b1250700544c000d00c40751080400554990b58458041d20300d00407817078810b00d00b507210395980701000000d0724101a800d80c541700e5118600744c00c0c024455480541030b81501c02c0120280507040c1c4410072502524482c0d51002d0303166000040c00114074007030b410204d0413201c03020400e21458131080201314034034068520468002000c00c00c403039404062200410744240c015070944142e0380d00c50610b06e045500955040c1c0126215204415106a0400c09103074008000d107400c0000015141c0020f00000031515110201611510013105541d01c5807240854164000c10400c00c000e042100c0c10380700c102c0c9115141c4039024100c8070090900f401d16001c0d5a10318000c1100602c1700d0050818001014a0745080d02c2240302401048a4007040c1c0c481c1b44090489015000058600305000400d0680e00c58048102c0b20b0060145c4c10301030360868145c040c941103c505041c10700000c98041101070117061110010718044202c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 26957317 1250 26956067 26956121
    0xf090e0108030415030b031f0f180209010f08030901120209060d0f06080102091809010905030706090501110a020a150209060a03052d01090504061103010e0601020c03010507020d03090501 82
    0x38811600003c0682e4507202413104240c08495200aa01e5015045109410208164005002200e480c2c030315002841205400440040716541c40b0784251400c40c0244040943c900f018400f03006004921130310341c1a5044c580059124081c012100d811b000030300d10800341c0040703140c0684580510241066480b28282044070014001d40c5800c8100d540c9842c2010401e070a0600880d0100a400307442c00615013040351885c11401d0000340031a110f5561100c2010003c0c0c0c00340000c0c40007500400e80400c03003500605095084502607044110110703030800000d5402c54020400450031500300010400da0907140d02e0010181c442d048090f58040070000705040500c0c1c042d40f00c540039a0520300d45105054450080190484480300c5a20343c510003000100440c01458202e04d42c4180304180205401e04003060f090b03042e810a07007040c028064420104290303542d04220001034a041207000780072908040317001944414044400004060311a4804400d000094000c411035008010307443c0c080e800d10303203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 26958567 1250 26957317 26957323
    0xf050408070201080109020a020705010e04060e040f060b09010e04020d02030c030709060602060a050c040506250c05010201050615030a0e030c070603021b0a031227051f1a010f090e0108 81
    0x703104a0101c1d13203c500101e070360845482070700c001a0046c1c0051404a04000040da0390240301c10741c1a90081e210003000c5844250f404c85280558400c00c4003d140c1025490540e05581c20303465001c1c0038610f81c0b00100820301400d840580c02c99015a144500c9208a0010a0601c0f80c6840d043e030b014414250006502e2960707500241c11100994252030007611000100002c2d600161003910314000240b00038005890400024400c6020b6100460080c0400c070035200041c4020314001c0e07071004d61400c1c04000550702809110b601850888040100300f07050b40016655000142074003007001d9803140b04a014800800c11540d4002c40d02040f5070560380d540030000c0c0a07600041807481502c0c0d00c00120000803d001540c4944654075072910450b420030418130000820444500e600d9040900883c0300a400c81c002d408000c80b0b0046000d0b040c032010b41c200031030b140c0544c03508034110145013130000c40c0c0340c64818403d0605502c0902c0c1c40100c03030001c0320003100d03280303000d4000d2500500d0940002030151000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 26959817 1250 26958567 26958577
    0xb0705030d06060807111209040c0216080c1201020306010c06020a0504031e03110a050304090b010e1002011a0f0d060902030c06041e0605030c22080a050105010302090a02070302030a050d0f050408 86
    0x5555286c411a1700c1c05440c0d5120704c10500d83d0181042c05008000326450f058010004402e410310403612581202c400d00d480d0f0081c1030740701180c9034001e44203506aa04008050540d036801d090000d501c0c3d410903000080c02082d00490243c00e0580c0424500d4a191080c0c049a00171604032400c0560000f1140e003500c1c81c004562800c602150703044030002d01e0741c0004100d040c4595008400b1b14186481d00320f16402070004511814100a0321140a440564407482c02010b9980d66600001c2c16910b5015405241c0605114043c0b14455440c1c1c0c01d003813540e1701720076281d0b001e43c000b0000c1181045807010a20304020b21050307030b41c07240021502185440840800e404140c41c8a40e9881955545903025a001d100944911500c44010440b2003988002601080c41c0144d007041704500c0983d40751446410b003256000c5c202e0310b60f5100c00041080d450700796020340d00100d00e8075003107260450350359000e9981d2240d090540f013030040104c1e002c210385080764031000500402610602c683d103480d241c01d00d403c4d808 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 26961067 1250 26959817 26959831
    0xd090b01050306011205031804090c0801020c0d030b030705011b08030414010c03050408090906130203010b0a080903130e070c020301090602071b0501090b070c09020a030204030c060804030203040b0705030d060608 93
    0x3d01000007032551130480c0d40241e0b658001001c0c1d85800d60700c04a554803030118001540e080303a00d0b40c5591000440d9000c080d0014510913000580311902c000a190a090120715007804250400e1885002d82e500420f0023402c84009080a001803602a4010546801240000307003001c500071040105001c646054060a4080c04c40200f00344880d03442c1c107400700ca000baa00640421010b00c410308642c103041035017a80184000300000da44c00d460040800a0740d200340c00040c000c0b40086403400d201908040d4103904103041781c0245080c504101c4e400601c500051140b020582c00501c0070640e05030041d40d0188000390041c0081c450660b1170b060520182d4055001202c001c800010400e40c0714803000540f50130354605035504801140b401100c1e81c001d8100350010754010411f1940050789c40500d1000b0400c103100c540700075031200d03e1800c0c1a010700b0720319400030003400000000c010019602104480c2a581b940406070703200c84442c100b0501d03500130b040062004a20380080491425000b00d01180f00d0741c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 26962317 1250 26961067 26961073
    0x309140f0c011e12020d0b091807050109120605061f020c0109050f030706030b010e030a050c191a070309030f03080604050c040b030c03060102030705060709030302010c0318060b060d090b010503 85
    0xf01d040051991a00c0340e01c140d400201080301d05a000390742900145901d00204401140040c064030004585c981309131217040581c403400c0410f80c0341240902101c401003d090901850b614a01b0344042e4040d40b000d10b0041449540394005040750740c0b01c0e4074801920080090200c507520380c0c88000ba607908840c0903070b503000c40c4102400090368580348100c108034801c00380140020900d04403080d0007030300941c079101d81405048400e90001c2c0c0c4040060f43c0c030f0326001e034006040020310030050200f9141058000b0404407036040d41440140f41d201d0407102c58054a0305550f0740c031600c504040340c400c18580c00c000c0c680030f9108401c1d428558403190586c00784100b100d0400c00c0e42c894030303079810381d51155204503494a081400001e145010302405075600c1541130040d2464207165642c2c184c2449000ca40d5140842c0e280101482450390910800b40c1c440f10a0804001030b003018003480b01780c4203405000404841c0c68140740005600c0d10380c1a1f0340c90400c032046c02d104110803450f07e0761204c0d50074003500b030180c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 26963567 1250 26962317 26962337
    0x305070207090203060f040905030906070b01030b0708060102060412090909061d01020c070308070c05060406050a030b0306060d12030609020309010e1207080702010c0807080403061a0406060206070309140f0c01 92
    0x202d0940f003103d0041200804401c10080d1b100c05200c06081454000d0710b00380410f00c001d920a4469100a100d581d04c1003408021960451030214070181011b40300108100481c3d04100003640c0010b0703040d810541000282d80f8601c2c1e0060200d0b20b04001d44c11140e42c04d420540440c0411181d6005814000000001884100400d504850807402020400c0c181580804000c10218401e034008002c2c45005650062195803910007150312680598080000a1000180b060072654107128100c0641011406007070b9a007000da00003004a0301e494030182080c5000c00403502036900071b9000300300070090508103544900e04456994001d20441c1c450f601a801000000c0c00108007140440b040d00d50311240c034a0608105030011907482040b0300c01218859400c003c1030300420100070180c0300031446442c0102e400422442207480341d4036004070f0b59002d58140746081c031007640c01140d12a40f00c0041d10300090751403503900f001b00d28542c0200d4211000d020303024a59030381000205121003605005e8076020101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 26964817 1250 26963567 26963579
    0xb03061302210709150e1509040303051305060709080c010c05031206060c010603061a0603060901060e2412010b03010e070e0109030515060a140607020d0f120305070207 74
    0x80200300a009501c50a0509000080070840c00004403041c00b240842d03d455440f08642e4044401d0f0081030014840303605420000060b541c0c80140c1e10050782c03e1014441d259003400b29100881c003410042c1071503110707400101d05609070707401c480c03400c3d8105080302c40d2414018030150441e5698010508580624088080654003c0a034070f16a0769000c00218501044104406000d030409850b85a1201e802c020006c080c10090103194003550150b0000500c5d0100642c0c00c02c590152042c11a0060f6000d208112841d40c68003e01070454005040c070412002813900001c00d400040103802119116000c1c0390000d001c91000644074160126140d408181d80701c40ea1001540000d02ca5990710108150000d5a0507110b512107a00c0700f503046c105000c40700e40703981d9446d04003551168050a84012441004802d01d85405008020400306030000c400e50f00700d40100342c49105020010b0300038005805180708100100100540c4c00303411100c07076007e4960029000700070300f000380c445030014812000c0204407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 26966067 1250 26964817 26964841
    0xf0d090c0506131202030a05070306060501030b180a05040809040204120b07020105090a03180e0702060901060608010f0506071103150a050108010b010807110106050a08030d050108010903052203060f0b0306 90
    0x44280783c3c07050101c01d500d80314070070301d2000704d80c00120f8150003401e1005001aa081000b81c0140d031180c0808100035007000001070459589001d042d01c0345800c422243c100017408a95142c002520103008149035890b42400c0d2942c0c81103224850704a440000c000503529402c41164002610610340340304243c5400800702d098800c240c0d004280703078000030321400000c0d0040a0750a0740d942c200020321412176450b00918210300e01200c0c90400368000d8130420468520a00c6080050711007401c1a100715410140300d4440fa010303500840e40a1100001ca050a21408032031030705149000134100c5265840354966a52200300a842040701c9501703100001c40c14180600603400ca40300e043e52601e800c0c6e034902d00c0032103d50000411003190b80d5650074010501c0c3e140c03811804040e14107000199038480d09042e00208803001681b02c1c000907403408900b80001b95101040755582c1c2d100312811340008841d042c660346980c0300ca0780010642f82c503208080045c040c49403c44105410100e05881042d510324002c1a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 26967317 1250 26966067 26966077
    0x50409020315040317070804050c040c05030615040f120312020c0d0c030302070c08060105120303010b0304030f020f01140a06090e0c0103051305060a050901060b040b07170f0d090c0506 81
    0x15140d00400c5101650b000000c0300c403607010307009107000c1c82501450001c42025500c241c0340100043c41c10742c2003005100040011403840b4205440802402461181c001c1c001d000142942d07115036100000c81031a4403000b000c1d6805007840e5103920045a60720701031180c5001c3c031800f0450120b072200003280f200700340c14800d491008240b00c0191184400300c1c5000c8601c0c50910404900789a030a01ca418045400307000070002410410707000b06030b07550405080024081390a0003000c0d5541c01000140150303c8a40c09907500190705081030041c400307440c0c0c0c003a420451088c02c25038156180204e003104141011041d03038007a040e81c0408121607510790101c24260f4114403010000d070380c090503134140154800c0d030007141c0c00304403440c0085a044040c0d4404c0d00703040040d41e004529507120014000010800e1290500034901c0280352840d0600e481c840c11207030b004110700544580401508104c030703d524401250822103c1d88245603684002500d60402089a01d0056403c5100a1303404161810554100d070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 26968567 1250 26967317 26967319
    0x9011503080901050a050408060f04060b0a0609030212031b0a030e0a05100e03011d010509100b03070902030406020f0408030c161215020d02130e0c03010f061b1502090a05040902 78
    0x52038040e080005603a203510245e410002c1200c01c0200103600d05060041034040d6601c3c1d42c0034a0341e803d150070540c040d070b440620058070528402008101050f00888402c0889905840440c1d1641d040820207086005040708034854410b128400c131042c00001c11103800c0340c0c0c42910791120160780141030240039032840c01901c1d0882042507000a003a40110235001d0204401000401d28484a910070310513409541042200c2d60b44030005c0c840341c480e00b40500601d5110740c600c1081100840400a07503106068400e00c0304242d80040801c003070180c0303030b01180c410300005a0b8440d926603a40308801d503a944000145a154010030812180c0c00465161703200480e0b950740072241046840352162101200d6024080c100303070b0341c2000060b008150302d001400c20904035015490705240350101421490074000d00c0010714142c20801070107280c41154010080c1c0b01c191038482c0a055240102520312b01c6c06510107004e46180440110340c82c2203903002040070b0038054036050b5105550b0410710094514182e802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 26969817 1250 26968567 26968583
    0x3070f090602070e070e12010e0a021203030f16111b130e1b03030904050a050f0106080106020a03030207030e0d0506070f0503040507030206070f080708040f0e07090302011b150509011503 82
    0x41040b003032203078858040701b203070003449050711503c0c5452032821107000d045112455007281d046907055240007030341100b80000000140d850352400151082801d84020003046200031920343c00307110b26129042d0300d01c250041100302c90091b03414819000f401c1030031030040c911804070f00180303e0940720310340280b03003082310b104006141140e4140300c00080c48240f103070125054070060011103202d54503805030f41e001da201e03485c00041d03a080c04100f41d001148160011000c1c422240e0040040e550700241180c1116010b00d0016203581262400312510f202d0000400c2e4012801140e400078010046103040c007c2000c1d450340d98a042c1601340c2980d0758041114094040c0e00715480030009410108018118288180d21041c3c21410f182d0303582c4e0b207a4100b40402d684030f20300070806100c0b000c4a000384501908500034064004e1600d00802403001c00c09000c000d0404c50745445000c0714007042d800701501039900c02c20300d16542100e00e11120003040129071141e030b650300300510a4a101980811034060300e070840e2030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 26971067 1250 26969817 26969821
    0x120a0302060c2b0b041b02071809050102030405060604150315020a1103040807050a0b0f0d0c0302090d050307120c0c06030b06040314030307090504050c0d0f0e0303070f090602070e 79
    0xd031162600804600c1c001c120303a20120042030030596003031215141d4403c1e400140a144c0c0010700c0200c43c2c51b800c020541881c1e9546500c00075030001005403c44441c0c1003030443c4c4000310385108000e0308420780c00404940c008400c0c4000c002011034402c1c860082070b9402c1100300b55141d505452141180b01c00f9152013600000300d91560007075002485144003a00704900000d8040d117449140d6805644410581d80140700213000030302c0e00d080c291001b8a8980006402d1001c41d5410551604c11010905e207425603444001c04070328000e406550f040d0348024030300501403900b8240f05440e944004003c981031b003011040e419095000318142d8960039084050000c80504000f016002403103002c8040e54071a20601000001800154000141558000185840c1d003040207001d02180c0b0b16401103482107003844100225484408141c3d9818520a0004203080c41040d40325001029540000c01c442d00001007000b10300c54010901c0c0810302c807036560314500f0395502c41e012030321082140100d2038192600b00c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 26972317 1250 26971067 26971081
    0xb121f0308070f0c0303050304050f0102030f0c0901090e0a020903060f16050d200406030b040b1324030b010f060206090a030c1406070e0a090902060301120c0f0311120a030206 77
    0x3002d4030310284142030321824541d4035107800d81e103140aa070040300020b600000304070800800740011a4140080c000950960802d003a119954503401888a0003e520220307011a40344c0c813451007600140614081aa5541011882c20003c0e40c4107006c140d010344560804140081d8510503078504c10700302d4442049041c040840c04680590003182c020000c1c588441501d101c2060445a04804401c1581203542d11440d096002c0c0a5450300c0c403d90b4811440d1624034a0aa2204c200e0302d1404618403c00144038102c040208403204d21702d40c1c00e10561004a10b000c0208508095014180d41e00c0d4a02c4009035583c0c1d10080b43e030b416048841c128540c1040c0511800a402188110441031041e00700c3c0c0c110a501c00f5520303140c100111202000988801400310307003418460310900c003404d071450007801206041c0d008521244010310440c0d030f5000c1070420b0001801208007045000d000a240c600c0001c0da5681004e4000941844145108549582c070b0200c5c20500011540409603050f001350810750b076584 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 26973567 1250 26972317 26972333
    0x20303041203090f080c010f0e0105040b0403081f080a0606050a06050f09010504050613060917030f0c030705070308090307050109081c1101061205060c0c120705030708040b121f03 79
    0x4408440007403505400300f0009001c00c01400800b02c951000041c13207500c500c236060a841845242c501a40d141c901800301040040040d0b9074400d070542401e90b016111011000480000306402072410411303084041103004001c1161050785e8040c0e0b80034080541c86004000c18107611340700c1c40001c114100500c00ca10700f5030381301a1012180505000c0c2c00c0c282d80c0c0e408a00144d0280c19003c070000030304c6200303202007038221400b68090079808092034001c850130780c540307a5244141c201c6040a044041213154200320100200c600d01d943c08019594555940d25004421350032141c601c3e84280a041c00200300ea500c078140e5002110401741c01480100159688042c040d58001001c2040206040903501004000d00440000b8030210009900d80c0e0381c5810f1060410701e001e048625101010405100102400186244020707010084165180c0c92860060728510130f404004200480c0480e0000c0d5446050014001c90b0003110000e4030303190364540320031419034110441d51803120108034007403001c100e2003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 26974817 1250 26973567 26973581
    0x1080a09020a0504060b1306020111090d020a05120604060501080d050d020901300605030111030619080607080106020610030201080a0f091b210209150303120703020a0f020303041203 80
    0x909400c0300c0b00d8503500801c0036564990001071a4010000c0c05100440e26507565000814203480208000c6441c1d074041440c501c1900ca0941c464200d48586206541e940c1c00c464009203002424040e000c140d5140c919100c1004960940b10300d4a0000009020100410702d5904040c0315900c0c1440c0c40300340c3c0c0703400000750040303500f690400c01c00005a044460182e012421345200584206a004e103491240030152200d640081d8060390603c10708800c014948030503030303130051001c035828001003140d03c0918600c184258000c0c101d920442092181c41600880c199059a190750300f81c2d01e0580d2400300c83c07005049207110080c00916860002494250940e020341000c0e0806e45010031381d10515201c0201c2400301400c3c50302d6034548184104860b500749452031000740c41e04141000c011455400048000d60300801003821800216440650342da400d00031218200e90312088610103042000c4002d00070340005415102051128410701c20b000d000000356440380d58400860000a01d000008a02904503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 26976067 1250 26974817 26974819
    0x1e0604080a0e030a05100b04060302060306040903020f010903170108030313060b01020f0f0304090507081006080415090c08060c040308031f0f0e060901091109010f0e1002060103020a0605030601080a0902 89
    0x8110380c1800c5036001c0c000703121003d000e000103092046031081e407070f0212002c0e2600c1034412340c86d0400c200b0050302c9150690760b2207641202c001801c2c0042d03090a0342090020100d01e038480d441c02c0e006804140d00a0006114200791606c10200c985e00c401507555248000d4698a1308000750296243c0059101c1c0c005101c24401031040e110000e9084240625284032405001015000490180600c41c051701c29960f10100381c3c81d15542c80c1c10001c13921003422100b030040a04022900f8001000c2c844c4585402c59080c010107401c108503405424602006030503405013030051b0003402e0118071404656801c0e64260b07904010002e2440e243c0d00c80f0b8034080b801c2040e01c80442d101c0702100041c1008070041030401001c84202c02e041d203180540400030094016040011014940070200840b8003000d001d407410b12100707003000080c207000b42d801620b81d0380c0b0315103405510a00039014410700550200c2e8450403a032090f1101141c2a8031914140c640d0300044a01c3d40c0080c442c0400100400c0341c0c1d410660a00780 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 26977317 1250 26976067 26976077
    0x21215031c0206090d0c081207020106031406040b010803030c16140102030106021b061315110601080a020103050a09030e010c03050c01110c0f070302030d051c02040303020109051e0604080a 83
    0x600401e2946a0309400c81030240540c01c1081001aa0001413011113140b10341403510700980d030700540e9590014041c101a051005001e4000540194000d43c4a10051900040d05190a1616079401503944070100e40443d900280e00000140070200001a24012001c4110a5050681c003080c2c00514082040c0700351642051003e2446881c2003c1c0300a5001c0d2446034003a050722180741c800e8442e64885c000005000e02810001c0c80d4602d00303401d02c260180d50221b00c1c4060400e154500c12030310f02c1d0310710070349002a000308400010301c0a400984428203c5c400c2c0c90a000039078421800808a418200d0087c001c98945099014258490340c61280050b1003400c04a080c001031440503402c507444481043c214800008059042850030403c41d803509252600a10348a41560701017078540304054100c105002c000f00b44405400c10200101da440c0300c41c0a030454480c0e98034100240a84500141640c10f030060414850039607222803100008101c03140018a92900c4603543e10b403095121415100401c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 26978423 1106 26977317 26977333
    0x50604060e030307021008070f081308031e01060f0e03011e020306040b0d0804050f0625030e0d050703020109060918090f05190b06010302121503 64
    0x25030540740c1290060000c1c4042403079401401c500a5100040c1d022220190f580314032800c0c4a1074441d42e4140044480c3d62095680d4070094550400490103c80d603480890224001940c001c41100030310100040740f4589510054803c0c0c001030001488503007002610b59100b10411003a00e4114000c008000c020440c0c6c1d28a01548580b86180580100003d030003940d40f07512030341e04c0120142c0040e481004a1510310074a03406030280e103204444078841c207502814020141e40e0b0201004039202c98251404280d021117280612003101080619034055a0075258481144050392284005004407800c501c00904a080c95800c180104403506104002107a481c0b20105a5080ca855001801d05c2d118200240c800c01580d6000e4028070035031200c1c50000c0545880d0b00d0300f20b400344050311096140d402c01181688a0003008405c00c0f0f880314045130003206c048080280b1a0f0000741201d0320b007 = true := by decide +kernel

theorem cover : BRFrame.Cov 26798567 26978423 := by
  have h0 := BRFrame.cov_init 26798567
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26798567 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 26798567 ≤ n) (h2 : n < 26978423) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
