-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2883
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:01:22.14461+00:00
-- url     : https://prove2.me/submissions/3ee8c6b8-40a2-49ef-802e-484237bb1fe0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 518345323 ≤ n < 518525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 518346573 1250 518345323 518345339
    0x201060816050102060118060b04090207020a1e0501030f020903030a08160e01091502160b270919200703020c030f100b010c0c03060e070b040e0f0c0c0a0b01 69
    0x2407a8607500001c211459028000c03a40c001510504440302c82c05040080c03101c54200000030541d64000c0700d41514006000103c0000e10b402a144880c0201c800c81040d982e14107070381034010251103504068658009081150398000d50020201480e4030380054985041c0c00006400c59108444001c0428540741c2400041c0340d403034400902034905410278007040103100300003030025842d5219100c4c0c0d0a03022000050424424840403c0303443c50203100c0c03880161900650f2060780c02604280c4600d108dd00e0742035007220081041445440b1024180101a45900b804244809003911500b01040d448000c08070711038071303640b0002051380f003203000c45a200c64581c60004c0c02e00c40c0e140c0310948130780d02c40e08601d0900500418003405084040200045e154030840041c0c624031280d4501421030b40050f0800028010103403c6903403022001070540e0b00c195107c0c2046501c4d03000b240215a485070401d000111030258490344503811400700301503070b404c0c030b560020068501042480c0c11039035052644010407034a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 518347823 1250 518346573 518346583
    0xc030308090105071d03030c01060b04060212030c07021002031e1e1219150b130b040f06080a240602070501052104020d05070305250e1f1502010608 65
    0x14181d800248039500b05144014550380e1070710965034080c2c203905140001075408200b00c1e040240300c00000d1001d5942c491002c01e07290414801e0030054020103907181040c4000804980c45040b1082500f401c1400d260248407840366007a000e40c00350701c010041d41c80400759100c0310403900782c42c072001180e4903282c4018001c220b54140451000c11101840200803031610761042c04c7c0e210460f60240004d0310540d0380950050280d02c1e4400d0003124040501081314020b0351f008110303000e0207621210300c44d691035407503a2851040348103c218042c9092401d1049034400c615554200d16200008281030f10310000c44492221708410300e10f060764614104000d49501803041d5401003000342022402d09034a14030b044001c031040c808038004264082e000404664400840e400480d4200702160350071602c80c0340055136580036408132841d5501c3c222a00e1500701a1440c068103540441440c00443d0b16000c0707030b0030406041042d81410280d011324012030840f00c02440300311040115400401e405140c034055078181 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 518349073 1250 518347823 518347831
    0xf01060f030b130908040504060608101703030c210108010207122c181306060b094b1c0b0c0715090c080607020601150513050901030c030308 62
    0x1c0341c202800c600b1256640300a000f01d8800b00c1001245030080d038034215035a80719a0700156402850110045980c55209882501c108000419803c056444601072410090002240d00304d5038020000643c0b201c17501c4d03002c0d100100d1012100135840031003208951000e2001d820a000ba40e42c00314080091107000c0c03a41a0b0400f8586c1032010b61a04009000e0726030340138104411034404084091202c0e01d072a1000c040080e0010742054081508103d001d5103c0111151003d4424074109000441c80317858000c1211003110000f056242c082c0c18045a50b180e400d0322044a00560b2447c0304070007078002c0c130740b00400a00040d01c0c240d40c0107442540200075a90700141ca14600c060b804070000400940d1500381c454001074208009500c3c1e40091070305101d03c2c641403611003401c5081400b88000c1007125101d94043d685400300742d4055a95446089036a02c10034480c2c0d100444459503006521400741004000707403541514400e1403543c0303038030104000324800e030300858600204180030014954050100c6403c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 518350323 1250 518349073 518349077
    0x50406030305091905011b05030d0f051902090303070201111f0501060f0903050a06020f13140f010e09070806060405040614120706090312030b0d05010e0c0111070b09060f030f01060f 80
    0x205420040020800f994201d0b11f03848580109404409016041040c0e6501c035084000038000d5400d5407181e4400781006440602303644c1100f10080e6aa4201703030003a10b0700604054000d60825035581c00450b40381284e00e008a045001c0c120400a054003007075011507002050a07030110b03036945824002402890441404020401114801d00c002400410034542c21500400c01684074042106045401d00c00d0b550990705000898800040b69a941c02003041044022220f0741e00e2428a00010f481d41a030004405a0282e015000103050600480d1100d400600c00391a0904154440003c0740442c1c040e83c1000c0d801044001c0300300c1300c40c41c1c00024003004208240c083c2440914140c4050300d0308045000c000c5c03903a0040344c103106843c0e00c03a074071200f041880203040300c0b203118041c2480d038000c0848100211183c014107041c940154055500440744075050340082400515050000900742c005c0540da6a01400070401664055202c00143d03000b00000b0845600a501d40307400076011a42e10500401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 518351573 1250 518350323 518350369
    0x212010b01020303040f0503040f15080c0913091401020d240b0403031d0a030b0403020105010f0f05060705100c17011a0a030f0e071202091003050703081305040603030509 75
    0x40c0ca40d90200580e900907501424040d405c5c482440c0042c158013590304500015503100f50000b4900c030803030f08041024100703621101d20383d0b01c50a001004a03c0340b0601c071381d0403145650303040c10a10300300d5010400c187e00a0030712181a051401d440da09a07440f000c1c603480381c942c85e42810180d524030300703c420100c194065000d02c0400c0c40c015101c4028011440702600340961180748001c052049080d074124120010480c480040d1686080c0314882c5080d41d042e0019031900c400441c110a041040c00c090340c86016614030040e103840300700000c4d07a000e10001c80e9036001d0a201400c4050701c0d03004c0c07070540c1e00c8a61901c41d000c0c00c600240a080e400d050f802004200702c4001c41000500d482c00c11250400030714a40030641c002804d110341e024095515501c8a50301c03c00c031001855403544001003c4a51003261501016181c0b5800420b0002503400054800d402090040002070720220040c0b150000c0c4a0f5413038605035441001800301c41403a802a4041100007401a1641c645014003160085e00a0880e00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 518352823 1250 518351573 518351591
    0x50603030406141602150301091506051909030212061b030408090904052b030c030e070902220807060e01031b0f020102122406030405060703020f09060a0c021201 71
    0xd005943c2c040712110040b1001900d80b41c02d008101c1300d11328545d00585030070f2080b9100c041d001c115900900c1011a018500015100c213000d0014001080781c00c2503513120300b01181044184540c40c0500ca800e02480103200c1e0000040e122501da01c00c1210802d0054440391a10000150f00e01300001007440140900b08200310001740c1c050203030794403603400b0703500d14006a5561034540e19003e9652908010004429040180001d80a40c488a0148655428840e80a0750001941951038041442c01c4a81002c0f00900414100e0fa02611201c076485408240740150350000c0440200207070824040360b0460301040c40115003215001600d00c5003031a04000181407100c8801400c0c590214481c200640c2e10081050309100350180d0b03224076440000c0c0802ca081401060300d004015180c02d02841e81000710403001d0b4a031040603684102d0b0010090280c9585410048000794010a040c00240b0001d0000700c00320344440d8064a800a01905c5110070303851035004101c010090301841032030b240e0420602c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 518354073 1250 518352823 518352827
    0x30e07060503040602031305060a050405010c050c061807031b0807170c13020d060801050f160801140123090a0b04060c060b130903170703111b0c041e050603030406 72
    0x12070f841600b20000503102d0300e644040164000d02000090302c03500c10034040c0002c681c056030002c0d008500c550000c1140c0c40070b00344103442a0148e801d803c42560400d500050a601440c0201140040050240c1e409540c0325500d1601c55544411080d89101c946d80c4180101d50041102030041d204111060fa220511070700e0007551012034400c564003a091040143d405203855406881040380051400e02490761549682c0d402000304451030341c001315101d40441c4c2007064101c0c040b0b140b484940c1e11800543e003000d0a2001000080300070f0750401004801c0141715a40140300710114400b5012126951004035041024040c02a044207100d60010802003190907044060601d41c15406038020440c50481000100c505076085800c1000904000061040542c0981103a0b0788041c60009a01c540d1152030045044504221410520f503104001c8040801e4448170102000001c1408840c0c012a07620082806d941c0c854001c80e1020900101020111405000f01c662241c0240e00071400c09285c4000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 518355323 1250 518354073 518354077
    0x803180a0c0311040b12031e0a0507031b0503030117060912090d0602040906090e06070513140303190e0109050303090a030233210402130f021c020a030e070605 70
    0x3d01490307094855414940342da400c280b91140004008180007560b840c0c24540325848082407043c102d0110480101032a4800f0584140c900e07103660700360802d401c2d90b038242e40c548078200c001d0b010101c034aa07484000500400043d8041c0000007814104484244a514548100500882d40c00e8000102d080c0f14282c224056a21602d02185c11908410701070030014002d2003250030580645051205c00f04000d9403541114140801c040c04032052036035030003011681030068002140e11214a804200100d00d05100541151034006083e40d1034990645042000c002840b030104010440803a1170692940c1c1000f05840202401d4014500c6c0c440c0c2d1200244082115000080c490f40312921991a010802c00030701d038140280c40000d540204075030780481d025400c040482184c860803118102c0031740c448282c201e0702965014000c402c042180c102c0074030180c4050524498001d6003401440310814803c800c803940c05960500c0141d42c0d02c080000103003a104a012103c506501c030f40000c119181c0d109003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 518356573 1250 518355323 518355329
    0x509010c0312090203011a03070605070809040b1f0f0207050103020a02120f0705070b091309150b1c0c090e030301060207090e0304090f1a040b1c0507120803180a0c 72
    0x3519200103048020340c40001d000f607010294156103083e15442a50100400510200d0421411550480c0e95000215914458910010301d148024000144241001e4210004ca040010326284404904082e4003510f404480d1265001a03824190102580d8040c003089002e04000c0c81e041d460a0019903002e56503080d18941110740000004a230100040304000340c4610641c800256a0103030340d6100d1110040c3c1264080074881c40300c00001184141d0725104410354242c3c00307045a1240d01c00346d0f815000501802d804182c000f41c16030341c54801d052040351301500c1140302e04010442e150034000c201d81210802e00740c012072070380104010300c030183d0000340c140100c82c0c40320402b00359141441592810741c06036522451107c2c0c1844105100c0c240560030054065926044025410085078108004e03214120603580d0040201c19003040030400d400e9401424602030703000c81c0d41c0542d44016804607085096130940d0184400300905c4242003000c0b032400c041f4150720700201807100e0540c0b03443c0341280483c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 518357823 1250 518356573 518356577
    0x3060a030201210c050408060901140c160209101e0f0315140c09040c020109030509041113060806030f0d02030f0d0f06081c18030b07020a12020313060509010c03 71
    0x2159420084043e0f019803900034041d01c410700001598100203041608140100d01444c020400050028601441100e040346178000e100d0300302c6d442d0980411000d505c54200087c1d002e000000060240e1201050980110145001c0700006481d10800400c07841100c81c0d0391412000e103000401c911003a0706619070540350803e20803845500100c1003e0000d141c18a0b80a10021506040051509041c400b6143d9000192030901c085154004102d08841d8040e4005021810a200c84251818181e02c00303401e1940d408a460b150010030403440c80c6840e0554060000074542c5402c1102504003449143c203641c40c850700130f240c5003481850281d2603001e2503c00717100414010400d190b81c403915400c070204654006030204012500d692406480d0954151002e0406202c40315a54034581f0605100307030140c42d05e40810703042a055540b10070042030060071350011882840710407004605081c00c400020000d90300155946d5076440c5920b10504081d41c407840501a05116a8007141d810042041079a60f240c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 518359073 1250 518357823 518357837
    0x609040308060d0501091a06180f0907080708010b010e0913030309020d12080105030d025502040f020906090405060411071b0e100e092407080105040203060a030201 72
    0x2c000440d0110190b030300080c00c503608005024044c000a42041607191110107500070031680d0700400d01000c20000d201c1701c0d40401c490030005010041d241d007450f03001490001510700255880fa0800e19081d01500003411b80d942da01d9050742d5645e0841c0302c4051b1410b05450300c042910300354000041050f20342c88068189903d5500e00800c40d074818050031410ba50007100f2211709050454000c0052000b402030b07902a2240c050000610307400050b4000c01d01100c020308600283e04803401824140c07e040104890b2040a400c280703440126034007071034200090403018144c0000d140108010361b464240010102c40c41040b082d03060b5204d08013101c0406009840200721900c2c1c1c500405c000702004900c800c4122004181c070400c01900403554200c80c40113281c40c2d9010303920340310500b0781c5079400c0d100007004c0d100c40c0e03000b0000c13004950109c3d0340c0954100d050b5040c0c0e42101081c1c5120060400031250584900e00c100324110b03800200441c0500002d6808608602d80031010940c0143c0074000a41440700d4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 518360323 1250 518359073 518359081
    0x60406030504031403040b0a050c0412260c0d02070501030c0804020915030303010603020702030106080c0307150e040207111e010509060711060c030304021c0302060c090f2e05030609040308 83
    0x1e04103484c5000802007510340e68a0300b800e00c80f031031200a50f100001a030a03c40801c9021000100b0359041e07941d40c40e1226a00400b6907a40000b185401c014611100e0b05040400d030494500401b130854000d03a6000307800707034402c5840000d0400820390811030615161807030b095421070344400e119501680c141c8032140d260301c48030034042d03a100544554a515200010000c90705a41c90b4000d05a29032090b00288070650b2505485504c0398202000c0c0c03605540010300822150340711100c4140c418125003007641465002001240580e032082005864440d49001d401c1c1c4d107402c10030700c001c40103661400031003186c10641d40002c125214044d0b109105400c0840c000e014800e1052201404c500010403440e62020a4507101da202d4004440a9101c1e948070101100060745d406220800103074194090301041d40e0303221014900790001d00100760040c64003900300c1402c1d210000b0440640580c0070380840d12004140d00500408140c1d1540010070a040c824407100e5124180305d65001030b0703d03040007411aa2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 518361573 1250 518360323 518360327
    0xf0203090904060b0112050f16200703020901060f0909150806100e13081617030a06030b0105100e040c180308031608090c01200f0c0307090b06040603050403 69
    0xe80d14406034084441024401008003a07800314442e0301c000e8885a18109855450710304403542111041032424800000481141094030034004149141c04c01c01c0c0384010618000019800664500c802c075400a58207001354600b5520392401001549015500250101c2009010811510410b10203d07100c448000442c0d1555010b40d0152604000b21400e03840c02e41d80f4040c40280c1480b50250301615079011031118050004e004283c903400c07803030380303441c0440c03030301207403090040492007540c4484503050002070070044d5000850040c403600c0400f1a0060550605e0f1950900680c401c40c40345403c10302070020560071190b070a0713420304c048034009008416200d055a09600c0080408400443c9003004003c201140000e076001d5003100307008607500030303121405540e9984183c4042889502c0179241642c25071003100a001c5007041c1c078020140c420220507410707240420f070005840030b9420a050b0b080740c504040018100404400c0310030710401e01e960b00410a58800c40c042d4108064840001800f894 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 518362823 1250 518361573 518361577
    0x3010905060913053a0302071101020a0f1b05040203090f0c03012c03090301020a0c1b0e0a231e090c0d080c071d1f080d0f020f06181504120f0203 64
    0x8203000c241e41c004005d0200008000390322034801143d03003116514400e10385510001d683d01405a12003000140201d40b03442c0d03907698001c103800c4d03148401441c0d03c0200741d580b00d5001941c02504a03100400205032521801d908028441c100b140c082d80c50011a07811030a60f00124402c0740028840300680680044202d40c114440c0c1c81400340c2541c000501c24558540c40342c82d203840e41d4003813081c1c41d0702d21610041545918502e0720070ba07407041004801013802c441c13066000e644411724821a5804040c05400b42d122541400c40d07900b0410940c021088900c0e48501620035406905403020305040002c101c009818480490005002404046000240340344100312440c085e010500c00d05000c0b9079018001c40c1c4400c02243d68451040e0980300b81300841800c400040b0a60303281c00c003e043c1c0c010304410101c80f280c41c04505e07030003144201e50044401000c1440102d000d1001410301440342d00004a289160482c0400e45111418100c001c110128408600d00d164140292030403601c0940144001c0b4518 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 518364073 1250 518362823 518362903
    0x91005060c10090317010b0a02060114010309050a030306051305010e070503060d080c010c0e09070905151b0a05010c0503040b1b041509050406060221030a060b0301090506091305 78
    0x10703d001d21042c2491740044d80048425010700c2410416038940802400d18001d8406190140c0c0c4040014842c8844060015800032018500003c40d12101d0702c0325803805209100031b0703011943d240c2d000e005500389121411042d5400c40d2090003503515000c008002c00c50001c02820400c040030001c40e0903030b614541c4c640d0030990401c0c500e940302e82e64003440c01c0c0200038852481e008104800100d00c0a0304101f241d2078403c3c451038544415007031600e002d01024400310482c070500c07807008005541800c40511407060500c400ca1000b01226031180c904142152017100d034034018810306004010005611100c0705600245070300540d45807135003c54454209002d16005441d0a0300d44c28500503403558010703107407411140110340601140d640c0c1c88040c0d0710340101000c030031004407030f040404503070441d64001150045030800000400c01c1d0b03212082a00e68000381c00c180c1403c0e444d103043c03082d030349047c254007038000030114804803042040da175625a4401e41c80044444000724180c030b0266065283d41c05e0a05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 518365323 1250 518364073 518364103
    0x80403110f1e0301050f040321020f04080f06102402010603060903050c06450706050309151e04050a12020a020a090c0906080a020c0a03051206091005060c 68
    0x41084110324240d004542e14050b4000e41c071700000502103e107003020050045415440b09586020907005090190441c0e80b84a4100b0f80c00300041200640707100000e0004200d260082c011291885c1c000c5c50810348003502c3c4543e400848082800002c108a0710b01002e4241c00e000700202d030b0460082a4003600c095803019105915048420303040c1074020004100c42c103650000d1761000e0b13442420b010014060805100000c400e8038403403816a951590f0111a030403004055141e421075041d03515882c200c01d580084000581c04014005101800c200221140c03100c0003d20b811444e004014907030044486600c0a9010021000b0400b40001445450b5009400c00500c0700d00c4489404040d61325001e00000701d001d204100d1000900d4001c1d40308503841c0e286103559040000d4030b045800c9900070000b81422042d60f50030061400300420402c00e12082510903100d00b52100413030101004242c0340140a80c0c0a8141e0320b0030480b4151080405400b0f031541221115218a00d1220240c94010f907450500b007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 518366573 1250 518365323 518365339
    0x60e0115230f18040911060705210406080108120a030f0209130b0f0904050c0907090b03041101030518060423100506030c0d2015220b07080403110f 65
    0x121288141e001085054403c1024102e148040c5042c401221011500502001e1a45c00380c03c030f0901c0c11030014611240148119400404080010403a41e05840454040050001001c000641c4c10030b030058010422400a083c0907000105013264034403c1e400307002c080594540140d41d04443c2d40d4196002440041c1102c0341e5004911280001040d0b06680c032031140150805443c40f07461705401c458030031030380301003d401c518070200300384041c1d8440a400ca00510071403142c00f1540300d0503070300618422030052001c82d81001390840003504072600603008035075060001c504c014000c0f80004603640c000380d00803910040184d101c034410400c2e140c4038030f680016004883c0c41e445828465003000f801070394218181c40d0700010810800841c02c08141004004440e04591510351050f91042013100c003001400d03143e250381c2c2521103c01e5a03072100b00005101d0303104001030310f000b0440342c3e18140a040350000c4540303450219115034001e80150710006085008604641c005601e40d2806145405800303030003a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 518367823 1250 518366573 518366587
    0x60a050c030d060305101107060e03040503030d02030604050f010303050714030c07060203040e0a230402040b060a08181b0402070606030204140414030f030c0c07080f0a0204060e011523 81
    0x1a000d4240fa1005840f180b00d50034025045541e079119040700c0c642440f2042d07150075401e540d41400381118103011503550005000000301900c05200800303e010b0101da00681d40c1ca010801c02c401c60701c01524000607241004018000290030000715503d1b00d80100300b018082400d05030309441c520910780a14142d02501c0030020740e4940003c0540250791440c1400981d42d0b8a880342c0c5000c5901d841070100380c056400384004844001c0b1411980c00c2400607102142d00f52100c40130a0356940b02800758400545604200040705052009141d800c00ca11400b03050210195941141c00c448031207a95441164000347c5c0008101055001d02c0003980d001d00103004241a41200c10840a401c8405890145030f01d801c0e099100380200031030f03502008044481d0305681303441d010812503403c1005015140e2180000100f140705080100150861014004010380034451040c84140e424503403103048107803602801805400781500c880700002030603140400c3ca07103070b0140060003940e00700444240f00c100002814 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 518369073 1250 518367823 518367847
    0xf12100918080d06030804060f0305090f0307030f0e06040f150f09063507110102040f0b090103090213020409110c060103030509060d0c0509040b0d0b0a181a06010305070207080705060a050c03 84
    0x2703240910541c5003000395039260541140c484114140400c0190010031424002900a2441030700581180c50210300704480c1c58040303002d551003500312101c03980e1300480800c280491041e03502c0c04030071645040c00590a0851014140a100e4003880c007d100f041c41401e0b06240300c8221038030315078443c07040c10b22101d1300c01c480074820a03000381d4286d000242485240d15800405008172070445d01c4028000c050589800e030050b00a80000131541d0405840b001450301603a588480800b188541500c010b942c0c07842d1810450031038144200207000c18200740410500400046584e904498144c2840c9035902000c00c000307040d0744146584905441e290032071122416034080054000c42d0400c0c1d0f01000303654200f108000345071452150050801d040100003900043c00c58020400f202848201c0030034461880d80d039078010140d02d5802e00c0a803c0b050040003040d42c2d25000e4150080e000d40050410141403849050b00c50f40c8602425009150001d07060040c0c91040c411500d10155003402e4035118848000c1e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 518370323 1250 518369073 518369087
    0x803120a0e0f0a0c0e07090b0703140729060d050a020d0602090a06080718082a03030c010b04060e040807060c091a070201110105070203070311030f12100918080d0603080406 76
    0x2042c04070050580046c1481d030003143c20100340c1d180750042c0743c01e060660381d044450001402085075050400d00c01800000d0078440124a99400c42044501100a0680d09100380500070700c024402e500000150022900114203001081c0c6c050701c03000220016404c021000c0d124454455402c0710300c668000400301d40c40105203005418982c6c1e1004101c4102433042e0121b8401c0c010004190004480c0300c0240c0c6001090990341c100c9844a510303448003e800080c1950040904101103035192050f800307803841c0c148035000191001012044581c2490f48401c0301600503403500802c60380d03848071f403000e54600580d1184000d1403c5070008501c035101d484c40000541205000307e000c26031614039441e4004045c0102c1c0d1203040113500544c2400501d0710f0450b01c10700419515000c0b070204028a2800d00350301c0004011403c8100c0300b00c640c40c1091100c40c2e2541c1102d5210205881c50f280800d481c3d07070081180756041c0c40d00400c00e103844030140c18120700107008a40c00280301c0640003070005803a03500512 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 518371573 1250 518370323 518370329
    0x190803090312012702072a0b030a020c28030503041e0c08060703090b061c1a2a1204020315070e03010f180228120c0803120a0e0f0a0c 59
    0x20032000c00e211104d1140d051340184040100020718001c040e003100b003038400401b070740f4080208070142c03850350710607a401e410340c41030310010511600055070400030803080044c2d044894840990002d00302c00307510080d43c60380e000c9000134200300000000c0b506000f00601c00c04240441400e048003401c915107040903070380340107114040b0980500e01c0042d950601a11440810607013000c0b403200f00d0f070f60b0360701000b0070780103151011f0600b01c0c0505111008156203030312212000768011103010700d905200000384c840702201e55112461081c20036045170900e4032103003a240380b0482c801141c0c2d07080c1c80314070009041c5011224041740f5190800e0400c10003690001a80b16565425002001200406139007241991070002e20f042c603060f5644006001400c02e48483d180d1569424805162261b14115000364500c9030341c001401c2c43ea4480c84281400b00400c421001003414400451030140d0345140a0601030000b0a4954580e0b92600510742050051000d00c40102010b0107941e030b41c1d2001d2030901c060b912140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 518372823 1250 518371573 518371619
    0x80f0105100b092101020c061f15020705040c1103030a05040c0f12021201090b07050c01060e01060815060f1b01050708040308040b1f0b190219080309031201 69
    0x550005038112100101c0300c50301c1021308030f01410207503a264095821050200341c0707070743c0d903081141c00324540007400301d18000e041280c81c40340550b240040c0c03050300c940980c0000d0b25071080d03204000350381d540014001088400070799021a103500c0d13101c415120041c0a51415107a4040041040481c074220f0b40007502c528440d60070002e2641e07c8941f50711603a0110700034030711000410481e4002625043d4401c00d40381d2200c0300082500d500726950110b21110689404000c0340d0003281d881000f0343d00f802204041c08008038429584d6140640040081d500034205000c1f8075060329041c0c1464603024129100e4811001040b6030310304034004001d590352044a0400c1e0b49510b40004110001d00c641082c40c012a010740d103011542c1ca0b02d0701c1d007182e00c1801626000b2400b00d080c138081038401c40a8240b000610001001c0c030340322000c0018000c61048825a004111f400680b207440401100117270402c040fa81003284181c0341e0360b505041074034500ca46801d8441100d4004000581800c0d081c50103054502c0700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 518374073 1250 518372823 518372851
    0x2010b13060b0a050304080708070c030b060409020f06031009020f0d0b040603080f4602060925080609030c070806042102010b0d12020d110303010915080f0105 70
    0x361404040340d60714040c0e103036000d1041191203080d80c828009160040d0280c18a9032418a1035510001039600c0044c04468603140307541e00300140030101802c917500000948003801042c582c0d130300050005070054802845540080041412802d10700c1c0118081c1c040500e0441d5110b00c4140d600c5510340041110300d810a00300004c1118a0410f8041c1000712548010114181034a20030501d1403030700000c401ca00d40c58500000c010b07465a0800ca2503201c0d600126058100c56049100b01805000008200007558002001e00c1650300303000a00c490081d40760040c0307155143c0100d580035000c40c11540000d010b4031900b82880380070fa03004401410303080921001c03200c01c5c640e0342a0b0a03454050490300036080300c1882c3e07510b600300c00c0c114440c4000284144000102c0f0040c0d00002101003040400956880211810f01d4034445c8d01040840c0b5040120b00308000c28440300b00c040c07556032005008004110741c441c4c0103000031100c44043c1402034200401030f1880a9401c022240c001c0c08100c8201182c82e0700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 518375323 1250 518374073 518374099
    0xc030e0f030c06010e040807080f0301030c0b07050c01080c0408070f050109080d08011208070204051e0a0209061603030b090106170a09050c1e04180204060603140a23040302010b 78
    0x10459681d800b080024044917880c1003100c09080800420070340345e9480410459001415010082003440c960b115800c1d241c0d411400d01c0c03152444113030041001a4030070007007030340072480000e0412141082481d0100c102c2d07032840c036040300e03034040c43d07201e100648600c61001ca0707040308000901054400a80c1d5544016950307901c000c3d500e07004500003c0106243c40014002e00002c156808070442c028980c1c5494400264042400c5410440b03405690501c01001d84141c0c1b02041082908034080d04015400c00e0007440004803a44211444518041d1001c0440e8040500030b4000107114203008210f0030b1903681d1500702401040c06001000020426180040c50f40840e91242e102e02d01e40000081a61010354414000c01d03200414240052507000c054140d426074680c00b417480f590303208400c5400751551910601040e00c9203900306200303146c103140340c4031410804510402d600c403410300408034082c01c1c0d10351101108108014100003402d600010003040c140c05401864403200159203104400c46 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 518376573 1250 518375323 518375353
    0x6110a020c0f040605010c0308040201140a0e03100c1202070f0c06110d0804080f03070e03100609180201140a0c0f0c0509061906030e03040b0a080601140c0d03020705100c030e 77
    0xc2d06000d0704c6d010910051030000400e2255000c07507071003441814240c00120a210034011036400400350ba03c00622008a0500350342002c0c030000c051647c0d9114203010201904201410314102e0798445452203a000c0f03094018481021030030710308641c00985010f50a80c5880e0b0082403569100f9204100344038910385149410b11840b2800c2c481c64100c0c0b41c0c10309001079507443c0529a40082d03c1e0108204400d081000d40755002d0201c00161341801c900040d02514100480055a05c01c2e8032480484000507190400360f41c0003190a503100b03090900300c5580344c18412003600d0700d48801e4401742039002001420410050010725540503120201c601140960b681020004085801038826880100d55001049424000e0300140c000540305419642400d848951044040e00301e11003080000316074400340139055030880760a00565000e1640d092416540c41070056443c1011043d42c010564002a003609002c418010080e5440d040b0100384140e01c4010300080260801108100b0240102003107911300d40b03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 518377823 1250 518376573 518376581
    0x111030a24030c12020613080609070801060b0d09030212031e010e070e0603060d14060f1023280602010c0e0f1e0607081801052506110a020c0f04 64
    0xa50020700407694606016902c4d1480e1020348040703070031101c184800105201c1c1c1e09609805400d0100040040f440c02600c001d181445907400743e00710740d140c1903041c003500e50380b00c00300c4440008a01e800325130181d15140c200c2c07901035014041c9252001c08024010003400c81c0c0d83c805c084100c0f541144c0a2641c803041e17000601c1c4019180600030602c1505d005500b03080040c044c5500840080c0310054007481c0f500d40c4a640d07600c0c1c1c0003100198001008009a05504c1041035400203d9055603803603071400c0441e04c3c40e245100d1807100e907002e07000550500190f039601040c1c0740c03a018590944048040b010b41d0690200e0101c1c0900009542040143c1410710f2181030480154103000340303101c0d0002215004c0c0141c032046400100b20704d03103c4403003852030354440d42c00400005105036160b40d81c40e91404018031400c104c0f85540d50411204001d0543c6a0030000704400742d8522080103411006243c0c90210020104240000fa60305004903005a085070045046240880240c07078140c0220001400c0204403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 518379073 1250 518377823 518377829
    0x60c030203070c14070801090501140a062106020d110c010506010f0504050909011409031215010503010b0d09060c0507060609020c2d0114061009081e0111030a24 71
    0x9a40361203d0010424400c00c0c10311416600303003a24021519104464255030303c20340c0c1900c450391110740445841040303680c85940710785e40c0002088628140078490a0482882160f68000c0700007018220a0001e59030440312030071065042005400c44582d144240d07a0044c80098046503c1c150004116500940ca2004881a959a11807a02c1d0406042160754400039042900c00d41d691448001d59001f003d11041c041c2807080700843d240c100000c0c0c03034503609000501c1890351b9454058048907903600700301a207065500701070076103884400200c0090010310614030068051424085148201500a4000c04055000b000c00b440780e1501c41e9034042c240c0c4100d4014483c01d5001d41030703c0b8a240180403520a502c0c00b01e40055a4981a03104c1c46401d48000b48900814000c02005012142c90000c04480100e401c904244140c0b503d0146076544a00e070030600048100e608200c1248055000c1d44012920705200e000c0c0c644a0520307816040040100034891040d07076200c040d180c0750706002c0844410403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 518380323 1250 518379073 518379077
    0xc0e06030606070c0b04061e020f0303040f0f050715020c0402090307050103090203030f03010e0a14040218060a0b040906141c0303021e0a030c030f20130803120103060c03020307 78
    0x303507855000510180d43d201c00c500390340c00c68402c4404102e018070100200b00500f56540c407407001c0d5540c00207401111500c29660400c2d0f50190408201401c808001c0d070707502c0b41d0000c03e07507012440c8a04004880040d000d0008159001d103e4010441d08151190407502c40d100380c0c2295100c0e0001c0c0188012171040b00040c66040c1d000c81c2c0c08000a40c840e812400c4c09602c06400d99080c086101b022601a410a0b080203202c180042d003001411141846a10000302d484980c0d201a41082d8001c42c0032018014409088050342c1704c00607004e42c503140c564000a040d1616165659551040408001c0241d030081c519800f03000d80d800c049038602000c2d054202e959111100310980072a03501a0000d500c180084280302100c16440c2d05031742c0e01300c0f0103090319240365240495105412071008045070b014041c0c201550f4a009140c00c602c0b200030220300001d41d0006c10403503950b802d106a80e92003840607400a9040d01c00001c2c680000d03c80e42406d9030490384190010f00100590100540690200715a4440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 518381573 1250 518380323 518380327
    0x20109080906030405121908101d04020a150c14032a2a01122003060d02090915070c15090606030203070801091103121b0705040c120c0e06 61
    0x407141c508a0000d40c1c02502c60800c9890151000c0c0c13260b00150069155074084030491181912142d070450903182c1e02140030101c5803034480c10944580080b00034500c2e180c0c50044c403400024210b48800406402401001842c0610440019401480ea41c1100f034111064280c07408811440c14000041d50200c1a008150342e4030320b045118004003071048400380200501c074403441c1420901c0c1200b81d90420070100d015407030800c9180000036203c80e46080c800f00ca1140780040b0800700c48102c04416031114a038501580c0d8940b02d550000f4a000e44044d00031b90700031000303028402c0300400000c10105840c16440c2c24180e69849801c107a58602c101400503040d0070240300855401007007948014545445020f0000d000d9840350040b034902481908421a10781d03440c41403105100c042c002c8900e4251040300203080c40030911100a0316400340300c041c030844071040304059070170544c203201c4440580310180c0100024043d00000622614482001c03081442ca0701d40507003015885000c5000c2c0050010389014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 518382823 1250 518381573 518381587
    0xf070b07020f240a090510050a1715060705150901090b07030b0604121e050d1101061202100c05030f04060e030c09160c08040b040f05090f0a0506040b0303030a0e070602010908 77
    0x43e0241e4006505001004a90740740851556101c41c04e61941803000c1da240da484a6a04074050301c1400b00d09404580d20f0321080070054a0942c0004503028902d040d22400e855458a14009144c40806400390000040a10030840c2c92401507109005040c0500ca071601182c0f5000d005038211684101c62a4105000f0001400040da901d140f82d441c1500c103d040200b0045180314400c40031102c00c40c105c5068118494805100d41c0c45054154030a01250003008803901d420405040c031040f00780000d0080c1c110190511019004840e010003454000094994a070720301e04003010f0540c4580225004169002510301242c01c0c0001c400c0c0319041e0245c5541b61a40303031040e84d560101c4500d4090710400c4421154540020301c104003910042000340c0d0703801d0b2104d0808404902c02c00c40c81d0850782c0550103c2040101710902d40284542044140000050903200c2c400460302402c200c0300044c1c0c2612000040c4050080319901030030132072404c00c1c01c0d17408083d1030300022400d940c00e180c4054412181440b83c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 518384073 1250 518382823 518382889
    0xa1b060504032004090c0501110c0d0b2a0403052e050c0c0f010605150a0206011a0d021804050c0901021203100f180501060f120e0f070b07020f 63
    0x10040f5103001042a01000c5000320001c2c082c1c2e200e1000884002c41074100c10001941c0100c003910800f0100c01c050080c1ca8080070110710951715405002e015210144082900b6454000f40f0350a40c51000c804031b600320340d68216120380c07039200d03110880d024071510b0000d100009040040e11100c0554140b082d10300040800403901400026000a10a12703040041c401030796020010810800c5000c000400c202d441c0504101d808002e00d0044824020304100d02c0e00741c0b69000c00c6e014151030b034007000380c1000c0309244621802400790041002e8810f2000030102508038940c3d000440c0c00100319000e0020b552505603100e481c0c080c064185001d03900030281450040100780255900030414011042c140365510460050201c07141d01002d4840c1400d400d226100c4008d008650141c503031410880940d0940c401300901f500b00c64031413a0229079a5080c856080c22080c40800c07140c180200440d0701d000d8480e410400203038401c00049100d28441c04c0007036000d08002e100002200d6000d130545002e600307600c0341 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 518385323 1250 518384073 518384093
    0x1b0304030c120c0c0611120d0b0301050c18100e03060f060306060406060206010909031b080c0d0f02070e0403032003011707050d0303151a0904050106032f0c01020c0a1b06050403 78
    0x14002c42c9000c1c0794030090a080400c1c01920700c00c0c0308d840300030800d01700800600d82102d6016216038640842040001301c0014000f40346ca1050100356403050f0f081c8420b10040b100c1038940f082160345401883e06100c640350019030b00d80d00626045095400b1911580700300411900f051055101680100300101b2200050f680552105806800c06840507841c120b030003460350843c050308031031140b004180402082010885600c42c0b0026051522001c40b914501035511001782c410f0000e1070741c1070b82c005010540b00b038200d10a9150500d00701c04800c0b00c1000c240516410034040e5070301704192074041d901c0c803410020b0000120b82020381041004411914100c000d40142d441da8102569840340004100c0c0a6401c9a41304030807a08400e91500e1000041005a078070680c85001050304001103035140d41e6080095070f11126490b042000040095a5034002d03d020703036a5a84119440840d40d0400e100001c9550803000b441001c09058003954004007000c0300c4603500403a00001e10a00c010310005440d50300c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 518386573 1250 518385323 518385347
    0x9060c120e01120603060606080c13120f230c0411030a180b01060503060f22270b04060c030e03040b0a03060e0a0b10020d12051b0304030c120c0c06 65
    0x151040b022014001e60f90243c07001680120381c4680e8848040007040e07400004650001d04512400380344c031022a80d021b1078112603014071100c80c0c1d103045460f8100541040802040380e0300500d000d652080c040050f40e23101c040c2554017090fa010300703d010700c02d62903d4803440b00348008030400d00703056072101400207000301002c2600d9480711792010f4405001c00d480480d48c0e4002c10095491595034074084046c000300715480480d0b02d0040f882d0b01007070f0300c00c512442d03800e620314580d4500c0043c030b40142032050b0113221546003145183c40114140c81040c0000080854440ca0082106005410f4034140031401c503101504030041d650010720040c070941d140130303004200d8035030940b07408210251a9070981c0120441039891840700382c0d84184100c070b10306040900c040340d0b42c5076001400c8440c48420010784086402803003d42516276400005441c0d140b05824001c02c0b411030b0301110340f81c2c030b0649800780c1901c0c0c0300002950782c2841c130700d615040f10f40700b0708d88a03c0c11903003d0840c0d00d03042d00e080c0042d9003203131a1103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 518387823 1250 518386573 518386577
    0x6020309012a2a0b0702060406180302121e060919030314070906030c020606030718020403050f0c09090111090d050c090a0f0b01022d0f0111030709060c120e01 70
    0x2c03560002c240e0402d000280c01a000300c5002c102e11076a410002400c2c1c955008a5031000c0910400c0003682e100415203040b1840380c1400c09020032040031400d40c1c004e090b04001e41c00303400024290390311000000c030710b5a09541d1912101000f5001da00da41d541e50300442d04010f041d030011030120b4129a1603085c0600403446170030042814200c500090b02d05c0c400480e400c400040c001e410030090241d06005402100c05940064022814038601083c3c98052501500c1c2e0782070314401000240b00e45c5641210025070f0454259040d14800b0741d9000e842c1c18801780010b04c500409070115911030010b100f02d1f190a00115103881c070740815001848601120064203542e41d0042c01c901c190b490700d07000310a070704c10088110300141814000e22450116902612000c0c11507020842c100900d001c45242003185841e40c0d10740e401d00c0c0300c441c0302841c64402541040c04542d428031009080044484c0055401100613454644884e9282c0c101160100080394000d408003018101d0041c2c0b40c1d02420880701001018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 518389073 1250 518387823 518387897
    0x3110f0a05130c050d0f0515040507021005090c03030c060f09060108060121050a210f0905040b0a051507050d030c0509210f060a0506040908070803090a200405010602030901 76
    0x1451117142201c00010000c4005a00d800401c1490f00c00301003441048079084500300071605007880000c3d5a000e00303400c60030086940f200443c402a6042000310402c01c2d0003800ca03a901c0c1c40c1d02903129125481034a00950250701e84001c90380078400854000e06882c0580300415040c0c1ca01941c00d100300f2a00d001400010240d00030b449c0125a09100540003e80100c414030ba550300001082030003003000d080710008102080d000002d81340c0d0310817115002c0b54001c68001c81d850444100080c507501c40c5030711440d4046400240c051203417030820050010744e030280b42598402c0030b1001c3e09409549035628000e0014004000101052078005c050500700740781a6088001c0641c043c0580b440d06001c00c04002d9154008020440240c0140c02000d41c40344081d02c0610260311a9501c41070180502d0100900b0040040006422050100301108410b9001400f0080000b24402d280380034812020205029904040010074804e0001086800340e80040c0d44524000c110f040d40d5030380b1550481c013001200461 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 518390323 1250 518389073 518389087
    0x207110402040311030f0706020d0e03030d0e0d1b020906120f1209040509070e010b0a0e2709010605060d020c01020d0207030503010e1f1809060603110f0a05130c05 72
    0x60361014001840c032500900300c207030110104044c80c0c800703504418801540550b000340181d59000c10303000a004030509060351108100f000190960013110030004c2c2c40e40c46d20a02c140d4039080018002110103803510ba00003403140314000c0041c00f01c5102400781d080881c83d004205103041504000343c1c540700c00002d880d2014848448281032982c4000512190f00000c681598185800d1083e507410528610003040302c140751482080c1c0e5180705129a0b80c01c14008122242002c1c09078120b445032400003850038034416031000c090501c030390078170351003c0340005201c0005414240510030701c816110014a1642807500419940b00a50f1203640e20081d65502803003a24240403030360014051161103615055100d42c1032048545540100a03c00710420f0120076808201c0400c030100d450039a00a15114690040c001604c20082d00000070000c00f40ca150880000501c00510a14146600d045a810040c1e0880d2030030001c5a040700d000300740d409403241100c80d040141951120b00480194100311b070402403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 518391573 1250 518390323 518390329
    0x1b0e0f0d05061906030b0703020a020304090509030d060b0307120b0109030803040b04050d02031603030c141b0c0402040621090f1b0504021204020915030a0303060f090b13020711 78
    0xc1040c0c049849a20900500c540500a12004102001e81c0202000820300c0e54481c604a4100504541c0516500140420f8443d00c24403c5034003a1903154800d0225060003501755a07694820701700855a18540080820300b461000102c0b03009844940e04c400c2088800034691009203140c1d1080f90511511240020000c1c1c50b013000340d072003a0b001d8908001b0625060034494248040044200d0442d00304020802c03004821420841d41c0a4141c9030010308034045600903142c0844061010a0000020410b074241540d4840b1200303072810b032802a1001c44184005000c141c0c043ca00441d00818018050f8400d5008100710120881c1515800032601041e1a1030f081c0c072001d0104000e54070758010258014222035290b00c070b80005c100c1980d04501d04006e405905d1000f40c806480244100c0400f40890030040c510005040e1845008007941c0c0d0200c442d10380940109401c3c455120980089131000600c078031148184c41503010003500000300511564101c81c029805568100c401a003411140501d0351 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 518392823 1250 518391573 518391589
    0x1050a1d0324150a06020706030e0c0604240813020904061419050c09090112020301090803091509030a0915120603030f022a011d0d0b01050907031b0e0f 67
    0x10003555800e4902d0800c0c90450501c414003190b42c130301450710050100081980000c0c56422651513240004903094107040c4a0304110280c9001c984c0300c040850081030210b40165101d40154007440b0036000100304003000d07075a006040700c2c040406540f0413912409030410034000c65205118180018440c0c441112040310083c05541c02d110300c0110061101d40c4c200c10b4402c81e900042600022401e041b0344a002404105050003102500e9012004060071520250007070300403103030310103195516803902030700b220740da001e9008040388000d103000c0114001c0b82e400300498618040c590740e1404540e0a0490301c0600d031030342b818814100003c98100200400080c072444003c1c600c01c8d5204500300910031070080c500031141d4110242801c941c1c6502090418811b102b0f900e886080c280002d1000c407480e83d00c1301c0c207058074056a03002103c00b801882040808140f56040c5c4504844c640c1203902c6e0301d001101280c3c43c041c003601a5840c1c80000d28001c0e8019007000c1440740c030003401200d2503000d0f0300118102d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 518394073 1250 518392823 518392873
    0x30316030f050103110108180309270c0903010b0a05130504050a050609060a0605040c0c260c010e0d020f19080d0c091404090302120f09060a081501050a1d03 69
    0xc8502d017901758075030744615195008440e81101c1b14601c000104190349901c02d00304094032905c400c00310114884a048080203960302417500070b01c1c46140c40301c41c80385181e02840e1003501c40d5182401414551506444040c26650090005c080d4461860301c494001c000190003611180300305140c100c0041c008105540c85284d0b804c0c0130702441c0c01c003038003a0015500ea07604490301c01d030300300080410a03950064219050300d420080e081c1e052440c44800da0a2150000700781f101c60b01000078241c031885070540020015000c0c0d0340895184151080d8102d8589002007644500c0340c01140c820b040a04c2c640c80880c00c1680240907480c0303030502804c1440202d40000c00d48201040c03245030100b00032208448041c43c0b10100382c030140000300550303030001e403100607503042c5404004001c68901d071024020410340b4140c01001c0d100300d030381c0c072010380703001d80403e01c1220f41e0116040c02107548440c40d4401c034140c036440c41c110f40340c0e05090b690120811505a500400a60301803103402c5610705084040903c8280d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 518395323 1250 518394073 518394083
    0x14012c040f06050f090c0d03210209090a0c12022b091b0b0406080c0705010e1501060504030b07030b010c06230138071b050103050f09030316030f050103 67
    0x208a0791800c14181c40004015010122051040217881480801c8507035082801319803c6031003240d1443c05503101d20200582e1750207240b4900b0203c510071801d900904a0759021111182070783d40300096203043c1d402c0200f10b10001405060103000811443e000342001405800700c090b030b4002083d103c030403191015188414455102d46030502844020310202252861100342444043e043c400302170305501c66032040f00100442c490005011032100015510195400402070021302500380440d56214040744078407104c10400800080c0180c02641190121303640028031202c0341d664501e082c0d0040000354186814040024081e10000b01103210710695a1007101c002e404607014103403808004501604841c0c15040c41d5100825981e0b00c05456082102d1000001801c008d00154100410300680d4401000d5401c078540ca03813040d0b00803f1041095a8081c2c0c0c082185560380200c0480c1007400351040e18181d0003c00218075000d900c064003144181507414040b9000085e81c1c403d104803907090f441592 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 518396573 1250 518395323 518395343
    0xa14040b0d0b10022b02010608120319050105030a02010f201b04050c0d0b060409020c01020405040c02010b090c0904060b19020c01080906010b03040c1d0601030f14012c04 75
    0x24052414089030711581c1d03464802803017240035200c10522001400314070010b00c4008901d600170b22600c00d4100401500282040d140841103c600420481c0c006a505507549591549004040c0c620b501c00c0604a580c020001c100300d50203a00103440d810400344000c000c02814a05510000c0660f4030010700c1248a10000c000303244000c4802c184a10700094024481d0b4140300074460748000c2141514030b40c440c080710004010314070b01c0010b54103100d2903220340703080780c00800da07018008410360203402122000e035414080900c113920100d01701d07100f0b81d18640d441100b90300810113061200014050108001c1e1000403140e031a100d01d03a40c2900a005034400345c0190040301041c056042c001c401c0e103c01c0a0074031074181d0400c6000c007a129601405440109400071001400b03015002d5050310080401078240c0340901c0c0c640d44e4000d02c1c50300840710180828140075000d104080a48141c600340725803088841101c1c5d007407980c107100081d4941a4078880041c04040e0305c40c07803110341c83c009028910603d0230030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 518397823 1250 518396573 518396591
    0x22208061909080c16032607061508160815370609020706111e1c0504031115010609170c0432071e12060b04091a060a14040b0d 56
    0x20024118140c07000c0240010456210107c1c051a000e4660a42c1e204201040042080049051000340303131340a0a0a4801c0c03214004c1a4807140d00c9010584164000307075080381407000070840d50010181c86090081e0350310800ca00070080c8100115184080c2d00d50a070301c4440d0744080300b40950301e254005810540e4002100390421003184a61084550316200c7d150410548901c10040c2c00c006802c6070006020000e07600c12104d48940401c15210f40e090000c115a0400e81002808400d200c2040c00e090310075545404000000302044904032651952820807043c00d01e542600c2252409441112034403a0401000055030b490040540c1c00903180d82c01d4074062192401501300710300b06c94a81c4466407420041c8204158807018103280426141c00b080717442800c001d0219a80c00507084a107051a140c80008520450381c00001c100700c841024041c446c0618600d8804284440c004545512220070441003491900a400341c5950280100c001420250f8426a1005c04c1c3d102e146982c01c0207680d18060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 518399073 1250 518397823 518397833
    0x13021f020f0c060f030403030f15090b1203090d020a030f1a0705090a14061209011d01021812030c0d0309061d0718020904022208061909080c1603 64
    0xc0303005032469000901d05055030350046070700c504c40c440e202a450500000090107150213500101032080450104010010304007003541040c0c041c60003494007030b90400b00005464030302212910100f0100d1006945440401300030001091000b00c1d0403a0031150a04002001c10700074400c26030712034051002000300085c528111020007400400c000103104090082003619100ca050100a84030700110a20f06100c00ca400100c260040b40f400703841c0d40641204020700c500741074100742006480e80a68400000b00940c1d501d0907800307035a54989205010104183d864a0114507100c001c1c104407094900e000040110307031b410611046240300120361904034510801c90244254040c00c0b0f0650b484a10411019140b6921003255200380c0c40761804882c2d032801d50758030300e904407103482d50010302c115a034807544074462a4904400a43d04841035100400045905011540c5440744032407000c00c1411080345001030009041c030010664039610b0070301a0124414007084514100411405100b120740d18502c2c1c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 518400323 1250 518399073 518399083
    0x1909150503060c0f0a08220c050a0911070803070c05030a110709060e060f030c030307061e05010305120a02070905010608061518060d2021040f0b13021f02 68
    0xa6400e000303c0402c01c44e185031000c44142c40520402e4581840280c0351034018040b1040e450000140f280e0f512480c0c101001240c0710f042c42224426142c0003d5103503114810000c5681500031a52111401c03c042800200071340015640075203030b400c20300600301407034840f10304e15003040c80e00c0008a1480905200c3c40700d002c02080004004a1f08103101c2c650030542194108103000c0e144600501c502d10038021aa5800c1c031a50401c02d030060122519021507060001c0500515112590061404464800c1c0f140c2c1501036541030303e030002c0007044514540002a54181c0c0100284d00444c05640c101242174507a9006c2e0078000e000300c2d0b47d40c0d000f90078500200a0500e4103960004130f0307058200008140c00184000d0b044440c0c000304e03000e0b42c4030440d15030010050100108070a2450f6402c08056510a030440f014040880034059040c4079281584612459100e05076000380c0308194103d600c000181d0078007041640000405200b40d8808e01a41c08900b440c001e010021840850b080501c41c00c00390304120b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 518401573 1250 518400323 518400331
    0x2030a06060912080705030d1d28031b080309101b090515040806010b0c010b030f0c01050901031113170f0a02090901021317160e04140304120f02010f081005190915050306 75
    0x90a01104e081c010308201c04d030440e0805c010f05002c00707a07334410f400410b40c0400071b01554029010a40d07900e0031810f850b807103400740c40301442c6c0310303140200b50f0160b00c07034030f1032148190711580c0c4034462040d0400c1e040114480e0204410b10205208000228062105006d164000c1c001c00d5401502e9402540d0300e04d0130b550264441500a520092014105103000503010b54055003e0a0482d52a442c0000480281400a5418003045000140b0701070303031404061a141120b40540c40310400c0406006126101e40039049100080d03845007409001529200103a55005040f01d40014600410304c0800326a042e07055008003c5a900c60400b0f0044584c14800d8110881e42581e6041c0500e08100545c0541003010300302605080881a035040041c00c100129000f6001130868a05003c00901c0c140c103428404031022800945c1e0881c1e041d00550080c00002c0c0a5004d07070318100d03c1281464103110f0001e60401e500ca41010202c000002c0e244c5030740c402d240c8050b00004c559040b5504000515192440c00345c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 518402823 1250 518401573 518401603
    0x30f030d0504060c030e060105100309050604050a020307060801030b0a020307030615020d1209021309020301023703020306061b010b040609050f07090501170411090a02030a06060912080705030d1d 86
    0x1411b242d400c10f102186060540718100d0f20040068086042100102601d02e0010715a1040c501400140030300025407450340c0b4030880072280b01075141d91302141c1c0e41d00284402400c04d00b60702d0105083c041b6580186901100324a40003640d6030351030300d028492800042040026800c940c01c25800c3c19405001d0107680040c400050040b40490760200712a4030090780c84840d50b0340c2d0342c40303140e00315a42074040301c1151a5880303403401050f031758a540d580b3344440d40f002c42481050048040040c5070107402a2441200c00610040c108682c101480070500a030038407441c4195a42c00e441015541c86104080107002c1d0bc08000a5914206400d40c00310200031304068203001c01e0f81001c00142e81e01c0340c44110b90380108441c4221503103442c5000c0c280d55901c8042c0a600000301420001208965800380d0f00c9128150810b2080b5075490300d00350384a100030b00800c1e8104a551100350081500b035401001928454821640341001c1000d54104a4004040b008921140d003041117248210800030009440d01c21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 518404073 1250 518402823 518402831
    0x31418010e011b1106210a050603010b0d03051e031005030106140307061b0b04060902010e0d02060f07030e030709021903051315140403020d1404030f11030f030d0504060c03 76
    0x119140038180c2c8040080107094150040d0004805d84581e070541d00743c01c1d850303c034800140001d4610003040030801c0703c079070060031701e400000354181c9014003460340c58402c068110188070609842c1103c86502c4501001d080c8092040c040500407c00c034001c510556021035074102c110b04003010107003901d013294440c0040920524603540d0a90300410184225000bd090041c0100714a8044165580005001600d14090b81c2d08101c148481078008001c400d100340d84002001c0c61070750400c100862480341c043d402090034805e160318a404040100078160007070804c0d8030b08a11020001c1d150a4240e00b243d000c5076008140b95810205031400849040000e0405200d50f1605816141400e5502003000d01014903044443e040040c29174070a84020360b6051111540b85032504000e9900c62181d0504000224044494004020751000f96819a070b80300d144501c0140d001d8540005142000055642c14080d030481e40444100800040c940c651800d000401c1f203142600344102100c00880c0b0040a040c20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 518405323 1250 518404073 518404097
    0x42012030406050702150307020a021f1d18100306050705030c160804090c0305011e03050a0f02041401090509010b0604081c1202130302030105151c031418010e01 71
    0xc01034a0a0710b06620340580c41c1da5407400041c694008084500c0602c200000038010141c2d40403840a64030350007920404a04c407158040140741ca4a0941031f01c2c0003503101d13085640c442c2641008103014000043c5104245541d410301030100c1c0f02c06403008030301c3c0d40c1c200701d08000300f00c603078040c040d444485400c2050552038074180c5040c41788190814100700182d01c00700e40b0f042190301001d9902802c180c4504019000e20320701f02a0091200380280a00c0101c44187c245521040311480c03404d690b03001d006840711042c0c5545003401d900d21510704a80c40750715144116024031000c0b000230b008110040c8080388030708060300c0543c21150b507291428001c010400087c4100f46001452000214000404003940034140c01c0485541181c0c8011980180c00040d4042c0306400c0c5004aa0a1728001c5000300030645403110500b505488000140d5082010b0000d8450454415200b1144580c000d05180c50310900c004c0c44038016502001d48100707840c00d008241e6072156804901c940500800b82000c0f1150a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 518406573 1250 518405323 518405359
    0xe090c0301060f081e01060302072607150906020307051c0501060e1e09070c02040b102102070203241003020603010b130f0603060e0f040b04060e0a02090420 69
    0x85070361a80d1040c000200c011401707404102c448003481c50340d444542c070321a58440400034040d501c039001c02daa54058500f40c10f1700c9500ca03c10000c0b81078034900200ca15040103903803040d400e00690000c02c065595281c0c5041c0100345d06000447c030820240d546c00d69100904644120a100c101c1da0383c00c4802d1801d8014041a6044035140c2d03109202124510700e2044a01c500d01461124100d0413a0464211010700c040a5045096040041d200b200e0601280c9001d00920240e003600c00c403068001a1780441c090400341c800c01d80c03601038480c1c900015242c4011900400d01d405c600300411220034024036250030a407509541a9034001c40f2089482044a20b1500020800d000c180240111448000754003481120039a028070020107100d00426009592200d0150040c001031080d91115812079000605034281d07030104070310440d44080a00d0881d00d0700d0301c07070348001d01250501e401280b003014801300241e82d800100c544681d00c00c070b8080c8801d184000507910a4520440224082c00c80c12448050350b01e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 518407823 1250 518406573 518406587
    0x2030106081015030506040e01061e080312180f010513021c0b0601050d0b0d05010516110706032c0f1c02060109090f08040821070503030f04030905100e090c030106 72
    0xc0903904e00800ca41d103c10000500404034510640c52940c60304a000407800d44044008030144078502d0a0340c0c03040c1e55400b855842c0d00c1011503c0f18403c11841c00226401013030f415550b201c082c10300031100c10200c1c45d01d05c903003115019102c0000429801008400b10310f850001c20b0580e00f00c80514600580c1c1d540d070703900c029040180c2568140027001c00e1003a0310106582c890600304000500e030104c903155a081c0f19000b440b05032950204200901c0041c90814041c015003625414144020320200349041390803001044901c8880000020014102c7c002c001050380c0c8200150860b0b0240c00c0600f001d01d60b480c41c090b00c0c5c0c01c03e89049020000d005195a0700810801d0450b03e502d103000c1003084a915180361045140078006141c1c00c2c01040100d400300c00020088003041708070326186103040303416450301041e005254005160358070400004011244440c52701c1d800503c2420883c80854450700001c1510341c4604071000003031b11100010b003180c43c116201680150038081c030b0790303d15418100003d00341c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 518409073 1250 518407823 518407859
    0x80904050c0d090b040614091e0102090409061a012102030c040b07050708010b06090604032303191209020a0303050705030d2a020d0e10110a0501020301060810 70
    0x440d03445000441c401210300440d8091041c00104010618092070403803080f04c8161025100705107080080e400008107040c40c98064004213008004a454259292040500114040e14295000d00c1100303208e0b115401b54002c90791007501d012424108400007035480300410349010381000380224003800d03060301480c82d01c88000011480983c2e07075503500d08054023034400c44d80a1500094000303966001c1c0040407440364183c41094000b44088020002089014010018020b0303105100704410000070b0a45010380f141089007098402c0d07259004240755056070000044c9040880b031060450b403046501800311044a08a41000c20034080d550300030854030007803800020180800020b40d4024000100182c2e511003218400600584a6481036501404480c1d00094031008021039444212400866030b522001c0481c1eaa45c04043c05031401c04c240300c0c54a890320410322900e040202030b402c40034000c0b40c040790f01078000580d1302d5242c40c500138001c04000b0100c1d080c1c646a420103110508a0b07031031a03411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 518410323 1250 518409073 518409079
    0x1e180b090402070c0617010909050d08090c1f0908030315090417040909060c0c050d0813020916081e04060b04020909041a090a0c120501140112050709090809 69
    0x2100304040c0424000d00c206400640130f11091100050715550003202c24460243c41d40030360b44a030340e9646400080e01d03229180284a500311840203110725100f40b007071950008041007264001e00e07850740814150800010780c950309043c1d0003549044036401c8110000204004d8000354554600383d0000c0e02000065124244070322041c0700403400b4004070300000b020910b601001c450391f0703507a18002c040042c000d1490460740da504041c0c2074141c0900170700c0040d0f000340e0020054030602150000032281c03964010002c10001c4406a2210096290285110300c1041c603082c10700c005601005000c3d11010006050554003041a00e03100c032210404a445500b00d0341c4080c1c040345803100300f400074001e4000d00400d0f43d000150402000244039288852001802104104402903240c180104c2d8a85c024280050304201a008042103066624400300440b46d0040c0000203072440e1214110004503420b900110381c6003110900d04082c000c040c00000000d000407841005442c140d80d83d141d01c0c2340195410b080c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 518411573 1250 518410323 518410327
    0x1020a0515180706030b0307050405040f02041e11121b0703141e0913060f1202030a08040321180b091f030c1e051606060e071e180b 58
    0x10414607070034502c01d20200b410140c4441607102c210040080040900452092081e00400101800e040c411140115013108070344441e80501e4003884082c0021320700000300e03441080000c1a4400c0c4a100d00c1098079041c0445a41e074506002c01107103480405002c215841582d044040c505007d01c1c0c0855080f10741c141096000200b08113882c4c621802150940d0028042c1801c50a14000058008101090301101c164040700101008c94045468900070145200f180b007105101e03001920548000316403004003103500d420000d5035910321541065004640301000c0f200038058040c4140c4801d1b809000313525001d503c030360358042684000740f900e20038020b05e240009005c00443d250f00c031605074052006c02d18810b1156840c0d030018020074076814420009003130181c118441242c40010012044111b030398031414062446451024209c03044403c80702a80e840030009030340e07115105800d204884680b142c00b441210b0030301c05144050b80e403500408100318210706040b00c0c26901e044006440082c0d500350303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 518412823 1250 518411573 518411581
    0x6140a2106090203060c0307030c020f0309240c01020304020a0e06030a0f030e030109150b0a05030a0b06180f01031104020309070b13080102040e06030708030412080702040219030c030b01020a0515 86
    0x80014100b040029402d0b01402e000c100040482030001c50080560b0f95040141120010089031030b1075001c800320350150010480c3d002c0c3c074501800d00d071101c410000161905001600300d00070890388600684801650044100425882c0c2066103038000c0c104114203124a24003400002e442d11654040203000401128482045c54881c9100c1003a01b24003070000c100401751400c01030761101c00b20381020b403002e0a020a102e060304100c1e0f407a000b2100e000e0000c2032110051b56400111590060147c3c1d00102d1211740e1070080c84a0102283c0200d070f081860245550450500f00b082d0020102040d008500410074004501e900054010481d15455040303500e949000f184c0c43c480094a6222182a40c000710740031030f800c401c0000c0c1d207016242c00c4045464081d81c0e030031042e4580c000d5200701e00740b10000e01a0300c00820310b200c2c000c0c2640f505c020b00051420b080c00007045041e50014900c0d60019544038031001c0314a400d88150040d4510074002440441e1040d07070350f640d542404080702590611894003007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 518414073 1250 518412823 518412833
    0xb06040f02090d03080f01050604050108160e100e0103060e150906011e0e0306010e0f0a0207020103020409020301080105190536070e190b10050a020c0306010906140a21 74
    0x41c0314001c00083c0180201d00c0107003001019808141c400301e08813040c580002600b403410740d080310700702c4506854211450307030b0f9607503410b54201152501a05100f1450018001661038a156640c200003913203c10701d600b204800010105d901c035400c9101601ea42d1003e100e80c0e5511041070030700e00f4030700301d40240c42562003100486000b42c120301c2c2200c01403103062911300441e03003260f000000c01a0070760032030300d60740c3e80d03041000e0b0b4800042c0c44a421a403c5100403a001e01202d800500181c0d0041c11301600d0180d4130543d072401c0340c0c02644020740c16559001446603c020703d841034059088150030621860400c901c1c000c50f0151210140c0c00c2c4138444155400100120400c20004180c0610650315001c1e0b6428000000e0b43c000c544a40d410b0705440c0251400503618801e001d406c42001d4642009000713490800c1c0d50a40c45540543c0644c03080e58100107290703500b00240c50207010600c002081d100c0c5001050180401c44600c1a845106408003c2c4100e078500c3c00d8403100d25008180105619005040c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 518415323 1250 518414073 518414077
    0x8040801050a0b0f102c010e0d02010c171303060501060210090c210215040e09010204080606060a0c0b160210180b04080f0406031a0118050613080a0c060206010e01030b06040f02 78
    0x1d4450018100b2580c06c01c007800052180c0d00401086c2c0b9241113070501801041701c00346041500034081100340c00358034080781503404140d010025421240340b034004440d4000b4260340300341e40121038103602ca0b001030040c558184043c1d5031500b85c070742040c030a18200e5034801010700c03c5806100400100304545034900100040d00c09a17198024204000256440026080300d0b4080d0155205054a200101d101210705100b150102c5210308094181c9403910702c1040019481a800d403010000084400e202144507041194080d040190b030110000e00071103406410581c1002401841515059080c400c03240c104000313543d0715510404d509e186980da4a8060f00034050070424460150000c18003040051309907010048051040305801032a150040c0110740042c10001c601c90f40b1181910100003d04110001d80440038000c00340000040e01c8908031840c090b60a0001c0d03a40a945035820000c690b0188400c5000d40507501c07100c0000c0d81151107030820000081c112900403a81c0703007101d070000c5d102070381 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 518416573 1250 518415323 518415347
    0x603010f02040f060e06160201200d0309030806010c05030301150201060e10030b012304090501061a09090903041a0d0207020907080f0702010e1002220308040801050a0b0f10 76
    0x8540b42c40c1c039010392003c01c802c1405044042803031204401c07441d10b0139101356036031303d07806001e030b103036503645540c011105040085800c00e0000e44207400e25070040418800110159001d6800040c82d00f004c0c02d0041224901801d900c0c10301020384030342c4008c6132010048034191019448035000200165400320700400c441c0c0d012144000c941030622201d920080d41c1c000849001d0b0800c48650b03601e0704201410310040814903030255408903591001400d25412200d8114000c41c00015503d58a4441008140f218007145d00e0a0800248000007131408014098001c84008025828181011101c02038040c60820343e00001c040890240d080100e550101d564880c0c1c0a0b100c44418106020f014111480640d114440300c900000003a005501c144a002940134040e402030041c0004d16401c84000d5010301142000c0100341c440300c100c0c1d4801600c90b600214441c105a43c0d4031417134940c40e5070846d80044c024807110340c00c000b40c1ca40d80c0d54501c490408051800c40700014908203801c016036440010036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 518417823 1250 518416573 518416601
    0x23070314160314070f0b1603030608010e0f010f0515133c1506110a0609030c0b070c261204060b18010b0f03040f05031204141c08060301 60
    0x4404010031140f1040001e1040303012080350082d07078480c140d581003c50140580b01c9600c04c1441004200304500500c059124021f00b4001a42034440792803e003940d4140032400003c0c3e01580d0b0300d181e01c1c8002d00c60004d0090042008200d0790a10420a00b8801d000318143c2d8030424100e80903114107030b51035001c0c03200c0f0306410108444d040d04a40701d8001e2200e04a1800496800c0408123030506c2c00c260044c0e1800d4140040d0308503a1606108041d244000c6081c1c000700148945a400400030342c0511680c806240a41c64201307550103a80380c0004002c0d0001c14010030481e0105100000410500075440c000340701034076a411029911007224120b000b456002c0c2c0c407014820081c407062050745c0d4061644c02d00140d0792000500410080702c4100703c401e00c076804042c5010000c00b0b102c07021501c09181c00c03a1103100980c0d84180c0c01d03181c407451500008184099031b0000d005000411405c0801c891400700f000000d095820559401030709202c3c0403c42c01802d1001c100300042c03d075502940000b910803404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 518419073 1250 518417823 518417863
    0x6090c0d1a0a0b18220e0604060b0a03030206060105030a0b0d0327050d06020d2405100c08030a09020a05120307050d05030603030711060909040f23070314 68
    0x7101d1101c04510303420842405194030901c00300d40a0004003c55081003c454294111211504d090108a0003407103003441078a10060248003026501d8042c1107a6500b8680051406040c507042840889a140d00b646102d60480c22040000a40115034903a000e817007402c0642d101d40c0c403085600068100506145c1d03100d921960110101604a00c100407000340803402d218049408061980c1c011505010f076507807160000702d40900003081e0340c004205000b03d281020940110310f0888000c00700906543e90035040003c0000d02841c03c02c114450360240b00c0d13180c10f0300041c04545800c1c2e043c0c0700140140b1803440c0c844050006644600c11581e008000c040c000c0a030761a800c40d11282c5030341040c02c003100e5074010440b070081018498410f5900404006015616055495503010036035011041d5040d08840c0520544415a8902d800684039030b004003031a109000c070b9440e000c2010803518007001050b007954000c0e007036110b0300002e45000381c07944845903040c014034001751189801c40030080c00d10b4124207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 518420323 1250 518419073 518419091
    0x720030d08010f151215090e100507030204050102150a150e040303150b04030f050f0f0f060a050105010801060f02010f020f071101020703080315010507050f0c031c0c03050d02131707060e03030306090c0d 89
    0x143c10000030401c427004100ca91120f450860692040b0b10403280188e00a90807000c1040070045102c0d080400a080010320030109020782102c015240e004039007101c081c4081100b410303054014a12841a45034514084d43d040c010039000c41d000f28000034001e05040a140010004108402c0400c8081d040894440020312071242d81c0ea880c68507088042405001c0101c4d28420060041d207040e5032058440c20a81d81c2440310031200250360340f046c40115900c1e00701410702d0595a10081650700486003009039581254204860380c0707560300745100c0c1107602615081020601c2c0205807a04046081000001c40c4103000040743d140c0110003000e40107000d01001c0d211846800501d003480c940301a41601c48070000d000710508071201c4910544045481100b032980000c2c401c20040499149a00c40182440c0c1c21060400f0088143c0c2c000c080030943d107840b109030101003086604003c01c098030307140c541500004042501c074000a00814028041c0b0b0707001c554410110000e580100021460030000340b49 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 518421573 1250 518420323 518420351
    0x9040e0115140f0f030a0b150a0608090703080a020309060d0501080c10120b01090b03070f030509030703140304050a080f0a030614060720030d08010f15121509 70
    0x4281c2801c000308081c08900040c0e8000c1e840084903120401040c80041289000504c03050504044c101907050094400840006281094490140f10000074030500b02007640c040c4030004485410010a02842d10708110008800042200076294001c50060300c42900c0b1909900d540504a00075a1144003c0313604590400c141c0d0245040310714102c2159002d00070302081c0801c21600380ca0801c0003c1c400014008080126000440708080600d000070b007442d0394001c2085103400c1920710382e00289030003175105035195060150f5a041286d50018600d481442d5a024040308240310f009a880346e0044002011301000f03000b0b194080d0340001165a0f103007074415100d9031076801300324580b010915208000c60a02800c40000a22607400745c213040c50001552280c09114044586c00561031000c400c800b281a201030051100440302c9071180d8041c0c4d410040300340b031001c605401039041d5200040340d25002544c40080b60f0f07891a116140020307800c0a03512404010007141c0c10440d85030741024032014003c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 518422823 1250 518421573 518421581
    0xf01081b012a050c060a020601090e1f0c17010605040302090406020d05040318060e130207020f030d262a0702030102040311010806090118020a02030714010518210c0309040e01 77
    0x244504260341e030404c2c06000f08243c0380141079020300141d01010040c0005019a800410b0b1440070320111428880046c440d4100300700c0d0000d0010f07006450703d420980813600031612800c0c40d0b0308140720071015814000010007a00440c44042c2c072540c1c06002007030900ca0700742d0440e80301250701142404245030506000c1c0444c6101242d420000244400001d9020310902c0c02c42e0034448004c1040818100603010342c000380d00078030020b9034803203440050a0000d907802c008441d548005504c8007845940120350300c0d010030050b01ca10300c02d4606100c04000d004009042c03451809241c3c0500400d407040041d148031101e0042c0c1000079010747c4001004030a0010200f2201e03840c90f426070f07030881d56559110a0169000082c4039040c07850400c1e00c2d8000381288142c0103040c1e448110302c104c0e030500d410790320313140180d0380415065002655900d050100945040091039120740c00c4400400740070403015101351441ca504404184100380114400032068428411110081f500600600c0000c0300c48422500070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 518424073 1250 518422823 518422907
    0x141605070303020706020d02011a131803120c051204080a1701030f060b0301090c170a08030c1201051503130213090c060305061206010911090303040605120f01081b01 73
    0x1501c259903145011f2841402043c0b5800e000c144a81c403a42017005c144401c00007001ea010a030180c6a1030407441e820b00c41291030241c0340c06940c40c0e204a8103081000e8040f906030315440410010100401702240722a590303e1504541d001881d07a80d42c0c0380c03000d000c4491520010034012032544c4c0a00000510100000308011180507860412820294404140c200c0d610307000b004040741070420b403c02c00c6a139030003600102c013189032007901c04c641196a078480e2103501c111907080b2208404500020041920800e00b80981816030702c2c43c00703043c0206211916030000610141980c2c44160b030120440d101c0d03c50031303082215200001d03c10880b9514182d50549507a02603640060302d042c000a10a00d03010050b4219900d40c40054000c41e420284810042c082c035010a052f443c1c4100011035854504000070001004140d5401340c640d0400d00f07491581040240c02e01040f100340f1001404030300004502441140c0354800001000c01400c0c3c0181c0d640000c6000c0111484135510b802501d02144002032070311 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 518425323 1250 518424073 518424077
    0x1504050a12170f09060403120213091a04090f11010306090e01050610020c010909020d06030f0b1b03011a09030c1f180602070611010b060315040f060501141605070303020706 76
    0x540da10401c203415401d0071031384902d4030b42c0010080750102e0b001d40510401c20740381402c0589445400c0b80c404d10000c0480d80221041d649da41403101c1ca07003154650815046204550921486041c0d0b103c80c024038400e51005081c4980f285006d810381c1e8001c1d48101d00501220030103011081500d40301178002c14007158080d0050305000c03540c030305007032000c280a42c00c110161900d040983c240310011000b5000840c1c410055690340801101181d078035590048011700c030352001602d514050400f54189964904d102e0302c0030405000600c00e0303040d40c0ca0041030902403a00704a8450070072500080c640307906040c099801c807c074030310034108041d4181521010f070321050b00c80700c0b184003480d10726810b8800c41780f06500c010f03040040207112040c462102548130001503c004204c86500d1800100154401d440b848845161054010294142800341c95440f142c1e100042158924000000c1d0040c0c04005805016a00000b0708a14030480c0fa2074100c6a00c0c2c01c10708503600c05481340342c0a51348105501079040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 518426573 1250 518425323 518425367
    0xb0d1a0a0b01050316020a08030108010504030f0e030a2d061a09040807030e031e01020d05180606040c1b0507170714010c0c150e1002010e1504050a12 66
    0x4048251030081e000000d6043c1d64540c51a030f20811448038410f80901c02d04214003c0070a55000300e0304000140d8007074020013000145900305451b02902c0540d41218200a00004144000750b41d80c0c0480c5185035a83c01c000f15046160301400d10740c0c0c140e210900d00b60206410500d481d014044950b00000200c1c1c1c1c091000900d049030042081005401190000c0c010f0500f0480c42000a124240145100340d020b42129020942c1c55152001c01d0528820b080042c2e5001ca00e19040c00e006008640d0080c00c0000007803101c400550741c607901d5540041a003400796403903118034a0081d00c50300c0f80e1030070590707400040d41c64400c0d649481744e20340850348a11106411205072600c0c80e003001240c4042102c0703850310305030103820183d8015555401151410354103084001400100000c3c203144070301003c411a5505855641c600c002c00542c40310008002c41168174000034900d41c0704000039000020407191a03031041d250f4441c5042450130b00028002027610103d10549444642c0200e19034075504000c0c98003207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 518427823 1250 518426573 518426581
    0x60e0108030301300620070b011208070512030603010c111c050906070813051f0c150501081627020d2403061103060d020933030f03040e0117010b0d1a 66
    0x2001d1409129005042314103100010404000d00485600c0c110380300d00003031030500c401d64480c2800e10000fa4a41ea9102c940001080a00c0c0f8080c450781308004802e040003104002650105039480c12845500900d0000811980e50498060707002d0361180f140c001e282540d1441c0d9440c15a0550b0000d5080601ea411500b402003000c0c50403034006d0b07401090b14110345900c84c2030568200c880409003071090312090300c5248088821119400741a028040c1c2d130005101203803048400e444503c1c0035520890703203008048201a412044d80010605c004900c40000d40c450350720700c0300c110060082a5205507404220b001d49414200c4881c04901128000c4c842007161861400d80f0010501c800c80d108c0c0ea01400210035900186010142c5079040401c0307404960459400d20008013440113903640d180f000068044c1c1100c107c0c60200315030b0300d4034103c0001850426140046c4d455100c001801426407241d0060040440040c00350f000c1c40310318400500c50380e41d0b000c841c100020f000100710b40048209070854005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 518429073 1250 518427823 518427881
    0x60609030721061107380109050103020f181b09060307082203050a270605030627040305090d08180a1202010c06050a020c010608030904060e01080303013006 69
    0x50380c2c4241c0c005003071046c504040300700d48011000389410581d0001408480085584410311198041c05035041c0c00200b0f941540100441e024915110710b10940d03000d11134940b2245152105904400f02c1025442001d040050142c11402581c88840c1c01020100402907030a9229002c1c0340240064001301040c0206146043c1044040c1000038003c940104091410940720307082c0d0401500000d9440c040d0000214082003002005911910000e00084140281494002c44101c400c00000421080313030108030405000c0000000c001509000c0045040c0b04103482d1100d0340c0c9026036200d00682e655403180120701c0c2444035191380c00d80c062403c6400108007082284070048805405844541c000c82180e40c034903000e004020998100290240190480d0741d109028840c040c000d003801841d100d00100051004460301c079071107000745059640c010040c2c45d0012040b0f9046d11150900b4807400c0c2c0802c0c0c0443d15805008002400f400b118400c0c1d2018070119921a9016021140401c404601b1940d40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 518430323 1250 518429073 518429077
    0xb0f030a050a031803060c030603060606030204080a1104020f12100501210f02040816090f05010506040306112b0c0906020d030b0d060213031109010605030606090307210611 76
    0x80146680d11990440d4046409910500c0c1000440384c000e580c0c603030b02c0c0da540d40c003921030160704000401c1d02c5a1040c410002507010f03001c041d12881c039085040c80d00d03006800e03a588103135500190400b0307008103100c0001d41f00c58044031014480604269980c03d4603004041c1002411118208500352202c0080741c5c0750300c034528180f401c6940401c1c0e60441d000c0f907100d040040054400c0c90300d00660801002888440034490f100e0041d41003001c0ca02d020f8904030311881681c070049036444000749440d005000310f0703035003900303aa064a800c004001101c0c8820349956610f8455034441503002c0303407440700000c0143c1d911151100d108540d00b105024800001d6425031320521079004a801581003a9204030019110354465002032b5001442c9000c004215102c2c0412a40300c1d8045000482007003200740700740145039000d0811840241e4000c005980340000082050001a1450707120f41400580207005a07010483c00300605651040f84411800300d00b11002616840013040314590300b0b06221105441d210b0003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 518431573 1250 518430323 518430343
    0xf060302152113030e01020705031e0f030708031306020d02270d020f01270608180607080c0d02070b0f193c05010801140a150504150305010f0b0f03 65
    0x150806004081d95400c3d0382405100f52806d045224152000a880d502044070080c10180400144554120400c400e03040008081c207210710f9074820400c2000040046044946c030022843c044400440700d464544043d110311030800c00b0082c0045180f4040400070f001c4204050103c914604550141405008568202202c081d500c403180d441c420449501542d0443c02c0c14800002100c06a10f401103509546101900b100000440220402015840742da00000c445000500180964648800000e04800004020f81c42110020a001c42c0c1c800050f01a100c9040d4800e03c011010700d000382c2011518101100c8070014402041c10b40b4440181c07130321807007451170b0518100c200d170a00030701c2c3d40440070b80300c14010843c5040701150490340841c0ba031103054082c02c154400450300e019682c50154001d0700190000811524108001442d00218a5194216001503401154046141a0091511400d61b00142c169400c103c0400d80340d0030140e103c075105181c112ba80d41d96281c2050103242e0b4600b1208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 518432823 1250 518431573 518431591
    0x31906180f05101502010213150f050708180a051201051f1202090907050d0803090d1706010f1e0e0a1a0304110a0b0706021e090102100f0603021521 65
    0x401130003550b8002c000407610711a540009407400031248135a0400c0440c0f07a009030040040c160300c0150701944109035001e00d211701d28006040c50855181d030721a900c100c00000c4e00d141c141002da400140c840c0e8070002e00401c0000c00501c0d00760607203404180640000c6401d00211004c82c0c145080b40c04500da0b00b402610500c80c1e80000c40022036003407052030400580212114412040005884d545005441c02c0d031510a200440d03c908255089500e8080c1560150080c0030315955601a014100610349601803002d18054007503080b103103010303140800c1c810205c2e403494070010b8442e8613250700304110b42400d403030036508611000e40ea102d205c255610154820f24100200f000818003007807500c50040400741c00140700055050360758170880050b604c2440c0445507207030013241c003100b2510b0441a408400540388180c0c1d00e4582201c0000b91078068090382c8051581c2d641c0b50061051082d50b200c032020b0b590181c00c02e02d01c003101030400d0b2001e4011058201c0c5143c4018601403e2501812902d40100011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 518434073 1250 518432823 518432851
    0x49020705010309020d0204050c04060e041a010f030e100911030105010e04080c010209060a0f0f0e01050f0c0705090403031413030e1002010f09060b0a0e0912031906180f05 75
    0x60011070242c404604141c5e03200d500c902d0341c500569251721509003d0303410800d03465551890030300054900c811048045100d01d00d441001405103a80d0706880301e400e0800d00e0310a5409161030070660003805012080d030174034070450504254003031966110100150045030070980d115903840806003a030300c0034003540244240b82c20103d000919440080c2180c0c5500030000760270000924042901030700402c04001c0003c6030403000310342c050b800c006951044034041c40e040741c00d001e041d4000f812520414400d80c000000001d4500786980c0140f0070500036104c001c010141d5410a800c005001d40040210038520f6480d14020450403184d505801050307036410388a44480817083c44c1002509139680050f013042d03549030700c07016208000520a003c02c403171240740b00051581280f401d00840600070b030451400060134009001242c20000b9510030344889040e000e607603956528044075158180c1000b4200030505000021941003840501200c10840341e14007000f048200700c89007801c1e1401500c41c1c2405c8011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 518435323 1250 518434073 518434079
    0x1061a1903090305300a02090a0e06040603050a050607020610080c04020a0311120108010f0204050f0405040501090c0b0304050c0406050609040c02071a04031101022a03490207 77
    0x40e0300074140b600d009003032540c100404400c407450900104080b81c5038030009049502107031500221400d802101103807046060101c0e4102050610300d407801031030081c0300c040f00040c0440c0c5d203e80050000e1a4440c081e00c41c600554500281d0b190001c0d10030402602920700054000290a0140000c49410300e0040242280210034440254003144412040644039480340008224004c011315901e100c040c032401856160541d980d0849030201184c0d0502030040100304004d40d41c603001110b90080440380042c40744c583d80fa0590041400c410018130706048054005007209280340518412030040e0b069a9460400108020481d0b5407405040e5010741e040c020b85900e41020b505c100d4040d4854011140c445849240540040c0024949680d040400103010300400c080709410072010a001e000034210200c0907040790400382c4100d002183c0940d081400ba54a9a42c204803400d000301705103400904031340c10000c200300070040c184201140c01c040e420324159140b4540c0f550079500403095000d0406581 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 518436573 1250 518435323 518435327
    0x16020f0604030f030f0e03090a05030309060d05100312020f06010e073516031a240f0703030b01030b0109180e012009010f0903151805070801061a19 65
    0x5100d4185404050f501d20110803030203c14816003a800707003807000071908c4194010410259000d01e802c03442c0690000c1c4141c0303031a0f07240d5038251881e0400c04203010070705035160724104103c031071682e001400040400890381c030341355000b082441c0c1c810300c0741060752001da89869104074140d82c20350310a03001400002c071421441a880308042d0000450403a40800002c42c00c0803041d01c11400d481c00d851075410b18602141c1585c2612404c0725031300781c000c90f5400449030700002a019805401d074012410088000c8100000c000808441240c03034a0303113880c2e07110301c1c15043c000c006100d6200da0703a000c00c1ca0244042d010b50300032084101160000d015030201c0308603010b400380c00303070a401180134510342d00c9442c1c08455610041300c1d0109551030320b1282ea191010071000404c040000c3c602c84092004006091012030080030f107107505140b40c54030106405140d903415840790782401c000500907010390000443c4041041d0071400c1110b40b16840840c6003100c80d030702d0600a00c1003400c610181000d204072920703214 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 518437823 1250 518436573 518436587
    0x80103030f0e030f060a0c020f0604060c140f03010302120105131104140a02221a36040b031603060b010e130605150702010f120209040603030816020f060403 69
    0x1c000e252510300d416807030000c28546600e88201d41295000b540800c100d031800c034030070865203220320b100410702d211032450015100ca801074006010035403620f00800c1c1007406000c3c3c0780208030603608801e584041c0c801703800c05c50703030402e020480c410b0058201c000c0d0b005005001d07040c0180d861040f013103980c80803942c500f04400c501030400c9811585400e011006100c001240c503104161805001d641c4244500d00d070425600401482450341003001c400744a00c40701d003c81c2c1342c5400585074906598610241d501c10f50140044001c402000010070703012a0242103405801d00b848050b9400d120408404041540391206d90341d821050354000403007000400c2c043d400c142c4c0e285006052001d4122600d44c0442c094502810340080d203076858140c10821410318a440d030b081c00c20a10001810a025075000030081d41003020f90310204910140f00520848080d4110780034118010001c0180641d2482c018040f09412504486001a21080d4444590001c00c07a0f441d9624001c0142101d40e480d0360303064840b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 518439073 1250 518437823 518437847
    0x1902091f12080c0106120b04030c050705090a020901090f0b27120d110d080c18060c0c011808030406110a06021305130c0518030c0901120b09070608010303 68
    0x20501458002004940200d81c01400e90041900d9039407007041040541c00d45034241d0081001c4403030050408040340225a0b8076400075410b01d0f16a1540e50300d424027602d040c0c400e030090740d80245030380b042c0000c0403505e60040000601c02c1c2c0700c016400340d449260307444000842c0300f14620810204510240b4008200101011035051105100d00800807004502140280d91044190303a00600014203043e801025071581c8100c0d01d002405c20a0701c0c518002d1141e48040e00300e01d0b0b880b01c08181c00000701c0b42c2413204500c00c0c0d005401c503a1607032030583c103269850300f0b589441400304246041541e50b19407400d8035901030b169920000c2d40b034503103000d00441e03010340066440950f038040c1c0c825000c0081c403580024034010801841c01c0591034101030400c80401600303440103c040e403034501d000345115040300582c1c0c803e4030b0501800700c0c04d1981501182c01c0403d506c64840e4032462420021031071070584081415041d0140001560396601c0752046580c07103040b070140002140100c0010400280310b00c10721804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 518440323 1250 518439073 518439121
    0xa0f0e060d021309090b041e0510090f050d090f0503061b1317010507031d0a030809160b0a14040806040b0606070615030302010b0409021f110708010b03190209 70
    0xb942c89201d04101c6220100446e0340ba0740c0c80781808107020603201003584241148103102220305c10359440503550081612801c94035500c54102c20140070005464149082d044410303601a1106a031000b80301e0100d80c01192a8503568000200f610300340040c1e00c0303200750580803501018081b81c90b80c4600d41e03000010398091b82c00222070003103214070b10074540030296280750002003114180000c0c0501600d000032059000da104014000444050010706001d0322030301410421480c1d2a03007100c040c01c2003d5954141180c14055600160a184030700003008201c140e5030307815090154110100c2101c1c0719521510001c0d83c001d03000b01c2e0200d00c84401080d0440e40091800e49008019924001a01e0207070510081b1101440c0040050540a000d80a80500220350400913101030740c2c001805030303004042d0044042c3c900d17101910120300590240f43c010101c0c2d000c4079100e6130381d03c1e80c1602134420716002e1400780c028268032000328904040f01a44a5500a00c417001da070350341504038160408041007880c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 518441573 1250 518440323 518440357
    0x207080408030c010603110405150d1115040e07080f0f091009050102070c05062b02070f051e0303101518060f03060510090506070c03020306010b0a0f0e060d02 70
    0x140710501000240001e18805001140c41031440c2404001c3c0310008681600031400c100401c000c00c0d40e050b0981c1034a800880d42d0070789103401d50a000440310341100185810406258241c14407001010140c003c0700d500c002c0c3c011080d03445840458a4030402d8034444000c46a1401080001440e1855594065006400c941213401c1e0081da440070340f2300d042c01c00d480595001501c0c43c02e0108426051001d4181030f80d10303d18049242520300b814104400102644c2601e194071905c05052580481d424180c100324031a04003180e43c10015202e541044042e60a2285100403501540c80170041c0c91264000705e04a0301e10070b151100d003141103001ca948001c01c10445a003d025100c4081400c0701c082d045a564080001e5200640a0120740c425044503200c0c001d030007181c01c01254848040707401e03202e094030b1040e03c81d041454a0b010710b26140d04000c0d454068080080f62048015016110301d4045603500802000700c42c109980a06400310401e80282040081460b03800c6190001c000c5142e1000c2e10751 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 518442823 1250 518441573 518441579
    0x8120909070f111e161401030c0c170913051006030506010c06050106020607090803041a13030c030f0201080c03040f0210180803031501080907060320210a0e1002070804 74
    0x350400c2c1c12004201351801c1450f401c180d2104040003162503580342c821441c841c042c245a240405510004403560401d5116222000700c507200d440088071065004030300051200c0d9104400c04150055402c8070301910300c620700c0d40300014880c000d6a010300105955480340074200f00c400c401174036000f044503040c498010803180008410b071190900038620b6901920703442c200600001c081c5000f031740c420032080e0310511040c030000c078204400d83c01810a94810320f41d92030401d50b000d0010a11680050f140c4582030f440001440b800070001031555200340c0c2c4c0c0400980d5682c03c11340c401c1c0000d64020742040d0b03c0541110042c1010280051014080d01300b5400c40c0c0441d89079405a40308981007981e540d0804400c0c41001000c440074003840c50402d0a02180c1c61802ca5205640c814844c8904010141c50325900c02541c050980380300203802c031000103989c0e2401c0744131049084a0305001c4511b08020603000103083e40380304d4851444101541e60141250166203018100070390010310003541d50000802c000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 518444073 1250 518442823 518442857
    0xf0f0e040c2607021903120b0f1302040e010b0c0d0c1704090603050705030106030816021c11090109110702010e0a0806090708010c0302090f0415030602030c0408120909070f 76
    0x6803000102c2c01c504501d0b14900518004d0811040c0c075029101600c0700c0354100000b03030b003080482c803402c011080d001400700c48181c005507503403202d0031150303810500b6400d440c030712400c00c0d030000c02c01c2d2a030000303064035580d0741d92401d0301c040d1103018a03449658002c603195064061141c0211b40c1100e01504862a5914181c03c01350005c1e489540003091450b0342e90707002c10800406105650040030708070020441c0314a10303180d218182c81882c050a00d8031901517070400455544691740103c2e41a4a11031030759032642860307c01d1095410a0000f4422480c03503000040e40c5405000b4034480d440312405e494240751141d0700641d140380050b40f8545d0701003080c42010031001c00c20440d00b4410007400c401044c0c024507000f42e45084a1700e50504004041c01003104511075140d0100c0c075004000181c400003840c402c4081070b00d040d5015500002c00440c00082407141c01250000a40165400401950110043d88a44030310724818110002d4006d500d800000e0303415030149659009a21141c04c5c0f40d000308424a40c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 518445323 1250 518444073 518444117
    0x150e10110124180504030503060d0309030501050a06090b03071410050712020a031101091a07172a04030b0a09020a090e010903030b04140406020a0e06190f0f0e040c 72
    0x9000d04001d444081008401641c60f5408400c80c03048000f00300901341500c0003070840c44020603080c0200540d0b0814020076201c1c2c2d00240003181c0040082045c0d0501c50705c17401c0602442e10400841e0b50600010060503d0003150190850b10500458458290000c0074000b03080145aa4141803000502c900c10115840c00000910706195902400c41d036009450090126030502c0e100e8003042c2c1c0351400000c0050320083d601b51203600c9410f02d04200d56038130501250030300300d400150035402c4040c0007070002014260854044441c0c40c8001c641010b4500213542480c0d000b58403024102d5000c1c90042100c004065010840d1140081c18a40ca416207c9c00d00e5415155403d1581c0d9040e0341d20190007041c1a4544509110200122828403030a4552003503c00200f00240024004540c00941d80304042c4c003440c5950f20504000d00b600b511230840c0f14011540103549100b19001c03503140c5213250f0340144281000a08144542c948450064486007800003c103003920300c400c1880b81c105180002101c02e494 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 518446573 1250 518445323 518445371
    0x31b08040e15031f3e070f020402090402070615030201020601060c150f06030c030f200d03270f09240b0c1203010b0705010b01051c02070f0813150e101101 68
    0x210645061002c00000040008103407a840301d14403041c0006d000060345848000d102c980c04403070168481880c100010000e2142d80c100a1005181c148600c83d80d14950b41c48001b220300036000d0780c0300c5a80c3d982090b2100407091000038100c0c07007160b0b03c20450003d680e100c0c8408010b040000a211503c0f1795031075a060519800c1950302017607801a40d0100f1003c005c1407803c01d010100b074071503122202d90101e2080d40a043c030003014020301210a60504011000d06a00c48004010021010303540700c5403040109a03500902c1180c81c24100014080480751409540801da002942c0d2821441c2600fa050360740c1010800c4d2a01d40102c83c6084644622240594068102d056040380d48200d82d123001030842d000c030051603041c170030203120038104882c400d98000880c4145140140ea20713915803800c803108070300c3e079140140503d00100c0c015012302c11f403110003030589140308083c0081d03103608071007555910b20f40d8401c140d10500c15562141014807810341d2202c6142e4140003c62803a80c0040e1581801207101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 518447823 1250 518446573 518446631
    0x1303062a020f01050106051905030a1514010305090102031b0c2505040e060906010b210423190215090301090809030d0311090607031b08040e15031f 65
    0x55000d0702c1182083c0300b1580104000c1c02c2940c41c103003a10350341404181c4a81004001d124020000600d210a690041000c0b21984518046190741740c9401142060b04492342d64000f0b86080d0006588000502c21213004440f42540d54a011090103420303c450741c0600300d0450036005444020003181f0001716040201c0482504039a000790400c000c2c8001c64207103851344282e5500034001c0c8090032038040740d0141901e190303410b07a0365164a0401410a03003e04030b500501c0c260182000c02c014003201000454000010800e0070311242d0018082558943c68603092188500c1c040f0444001840c14003001070294020030262410104c26100003400c50743c1140c02550000000112603200386424003000c0540e080c81c2c14100f0041001c2c400041450003040e0a49004d80307000a0b540e0b062500600e4440c0e08203c00005502002c0d41350303c6c02c6c0d50303903800612500148010b40f1001c1007105425010f210080d15010300140180c0c07035842501590a00611400c68035aa41c843d920260b100c400003d050440302d802c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 518449073 1250 518447823 518447833
    0x80712150207060603152003071107180e0a1101030c0903020d050d031d060402060a0201062d0e010b03042010020a050c0402090d03050c1006031401111303062a02 71
    0x141441b5000041500840c071007186020751032604050003d83d103c2e2100d05481c051602c0781c0d6000415a540e80c800401400c1c0c910840d40001080350201d40030260341c014142c0f003804403281041010b651003050b03c0006207042c00034074540d410355101c2c1d44501307009901403402d100019529000f20b19107000d914001c0c0e1701074000d074015004aa802d4003540d6003010501007440054545c00c41040d481301d50140c002440b81c000000d480c87c2d0a4402d4000c0300143c50343d040104041ea001d072000d0800e5450388651140c079980c0203000040c6404d07200400d1412145404506451036450303030b850f41441402d404030051004a40f03581c0034a1901d4011000c1d601d0a0640c0081060500341d0902d285400160105c2c544500e00403c82c01d2000d441e41003450400c158141000da440f842d01040d000c2c10308140081c00c614a40c0303481400000d03c007082c1400c4011044160003003000940545241c00c0b20f200c0c10419100d51000d0b4042040061354030b03846480d00300c1c0d1400141c103003900301c2c0004601007000341d000c1c24016440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 518450323 1250 518449073 518449079
    0xb18041d06071b03050d06090c0203040602010e0a080405040e01150605120a1107080c070e070302040e0f1005221a1f020604032106080d0909060807121502070606 71
    0x100305158108109081500d0381d5010314103024045186143c1c000c0402c203001c100142c0311880707a00200d025200210f4103003d83c070644100203541f03410904c0790310010360820060780110480428403030300d9250414107061030603003480c3c1408041c0881418a220a40d81c0d00904a8445241c052700c2e0b01401c1c840ea9020761315903607000c100c150200e01420707455405140030240c482c0d220501302210400da6000880c2602c940015003001d050a4065020703c100c2c070507250411164580c5030f4014400d0791860480310758203450760f000b00e80c100e4004071403803405800e14a800b40410302e0306500042000c8032107841c001c4d442885042c85010f941140205010b00620b01c2070941c1d003072800110010030b814400d800480310707422408000759a068050000340520804100301c94880702200d25400f000c41f2011030031b020140e0780360384d01a520181250480c00040407800041600388550241400701d0310254000e00d007060030400041e801c801e2490040b10130310480c3c182c10b00d5050341400501501c030b004500000390326203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 518451573 1250 518450323 518450381
    0x90618010323070524120f010603052a18060f04050312030c070b060103060509070908060108030703090302040e01090f14100c08070c03110f030306040b040c08010b1804 74
    0x800658a43d4110f844180002e850380400d0681c650f28002d8545a100a0740c0309800c2e8600c03480700b076030742d0706143d140800c0350313141120f19028100c41c0540d8041245945881141e1684022010200c0d640040341d43e200b80040d48803005440400d4159080c12001112a00091107561111241c207401c400b02080c00c0105144c1400518422506182071900c1c41c80c04105d11460341c0301e000001440d55004601184036a480fa0348060081d090241c8403220030304000e82c018110304018030a40846200b501300100c4c5d007502c00300c1a202640c0e40b5840e803455184c115820003019107917074000548190350b00c102c5907020811200084c2201800382c0c1040020100351100d1500f08209000c00190381803c1107400c2091a500480c0d10780e0088041c076200c49040e0382407074101d803440c5d40c039180c00d40d5922800b03014141226002c0f0082d4080c4108440402640340c051050100399490600b4560100310500300403c660540440107001001210404003c60300c14400020200d9441510018503c10a81441d41d941e803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 518452823 1250 518451573 518451623
    0x9060b030109051005040c03080708030a1d07090207050309150703090603050106050d020c0a06020c0c0103140f010303140408010c080f0609010305061311030a030206220b060906180103 81
    0x24016002800268669114250703a54803840d00600d0041d130f40c00000c0d0074802c8484080003d1540200c0140d07540e0f001d4140187c10f034006650200d50b461500308910032020030003486082d0120450041c1450900d030404500007500800e82c02e235040d02080128401c29564040720502000940c0b44964a030001410010043c0f421508920241844c220041c4241500401500c0003090510409665004038410f01ca0402203810743c000c10950001c511101e400c1404502c0e5803100030700b07076420010b50200140c4481802c205680c2e03040710120503001400424481c002c05042d120780c4442c414545662844550308444481040d02d0001d051103090004036070b0f0712808260000700850700042c031541103480e90740d2210300241081507801e80c0107413414100210410410316940c8c0040075211140c0701414040d4a4800444213002d407a05091018440030002d01500714440c2d406c200400f029580e80c40910260250103440c60340d02099103450901415600c1559501071441242600c40c01031607850300203440303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 518454073 1250 518452823 518452841
    0xe21040e01060201111902030915030a0e0114070c0f0c03080a1b02150a09030602030f01060e01021b0d031e2f03030606030a0603051506030d0905010f0e031608010906 73
    0x16410452803502070700c3d0700b0086d41e2421250074080e070042d403c8160103a1640c81040f820903005844c1c810074004008110014501c60440c141c07003032084054208440c1d08a815529400d0a598002030110f44a140f1501a0030500ca20403400030781c008800c2e450700026440c003680122000f41c40066540c4c8910380c011240b01401002c6001140c2154075680010180300c3d03100706850b09e2050125441c480c084c4601e886030020340c3c10020443d078070306006c00307840c0c1200b0003402000f01140c02101038210a510001d6810401003a001640c0c226140307150800c190a0789108041c2c007000154000e41c00541c888000f04e0304001d0b105e8803450ba0300758642c80c2640a03a00200030100d00610422002800082d001c000c0342e9120208580f119230744e5986003c05402070156400142a40c4510003401801003c00040f1038041c1d1000c0f4200c944040d44450111502c03641070241500080e51405400c05150240050403620140201034903200848058525015540d13075000505070b0b9103072a409004d200d803901c184221 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 518455323 1250 518454073 518454077
    0x111804050c01202505060403050102090a0e0f010e0a0914012c070308090307030f0c03050106140a0e04140d17060303070c050909010b040203010306020301141905040e21040e0106 78
    0x2c0f0101440301070384a00b4a0b444801c88020001c1810400c00030040c040c00c05804010000c5403941d1301ca0811900035040285901d016034980880417980310388108910f8401c1031440e05900303840c1c0c03e15070610345824003d0b0007072034019103c05456000030320420300b907000d042c40b210002410341114090511416488010308011003940d5850201290780443d9107012f0703236003142d0855075800114001c04d280008036800902840b0001040408101c0c0200e00202101e000303030300074031040d9145c2c041c000003802100074071948040e50003400c000880044c0c04940c1d20a0107024224403004070213a0841c2024505810f103000a000c0d06400300d00900b5100290340c0082c01a401141400039590f40d244c90101a8020f40748503030700744000034440d01340c01d40052052407405081552603596900e44000031790401e000c1c44440c81c03030104403004907080544440c1440000e89000b010072500e810188001884d01d000b0084480c02042d90307142d4a42110354807075088130022092140d40324503003030310f00c605180180c00802c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 518456573 1250 518455323 518455367
    0x80a051302060f0c070b0705031b1204150c021816080603150c070807050c10020a030c060506060705030f0405010f0c030f0e040e061305011a01020a111804050c01 71
    0x903890704003d48142d4100350510aa581d05400c0856242c0340d2198049114044005942410020044003601c03c180640001b510a902c450900d107440301c62200c2101c0300c1034021f00c001c101d180810a0101518921800c062481d5911500441d0110300140032501d402c20484c4184040001000d42e0400004080e140c42500e130305204001a48803c0d80d007030740440c111078450203c0c0e1f000c21804102e0380816404004180d440040b4508540c5900458240301c2c480e1010321100c000241c00803448240d1183c1c15640c842d0004101d40e150b0000389005041550083c10074000080010b10400c02015104404014181c5441c07070b00000400100300c0c100c45804006a01c100c1e44002600074481907000174003414075075611440c40d00480c0041400f030f8940c10300c921440d000d000b00707200a840c204540b1405940240402d4440d6000f0300300c1b5130385020b099030050f4452406003000c1080224100c10000c0c0040070b2500340340c0300d08007003a002c0400740d80c2982ca135009260300034943d41c1c000c0b2414182d61901e0100030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 518457823 1250 518456573 518456611
    0xc01140a08010e0403091502070e0717040605070e0a1205190803070309052b02060603032d04080303010b1305091003030509030f1f0f02090d030c050f010606080a05 72
    0x6050780c0303041c8151080165042c000c102050f00464030341000c4c015070104e0902640d8825402983c5d90f5244c071442000c0b2400d2808a08110b10a40700302c1030800324481c4010b400c2d10389980b08001010010400d604224665190588a69a0341d403c60014100340d070711120120301310300708681031034080c08401e00304041e0318841c0f0340000d00360000e9070385c4240d60f810b00140c400701d04d081c4581403001c00140c0740f0641e031600302c2003241e002e444151300340103041c0b0f582201c80d941c3e91401070550300d2003103415408a4403020781d00c04611031a0030440c01000c843e440c03a0503081569070824a4a0354000b078002210300b500102e41d0307000152002058400419088642c00d086080c0300000d1400c8050710300011f820000d0001c2e5801040d01c0810031030801151100845603007600d801c241110601c00c11041805c0d4504066140e03070080314500945042c000010100600380c81203950550b00c01a0702d00b8110b686d4080c81c40203c0d0000020b01c1000018070081e04c40c4200ca1034081e2046044a500070425941c9c0c8009400702 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 518459073 1250 518457823 518457827
    0x10f0b0f1f0903081b0f060907090b03030403080328020f0426070e07030c2303040309031709120109030f030b03030d0216060c0206010e13140303090c01140a 69
    0x390301030151070840e40360581c01c840c0454040110b03400c041d05012001400292048420410240e40c1e00e044058a403282c00020382d09480d00c00c180c4040c1c0050340105400c0c0801c4100d5802513482c00e40090480c0d20340340e520354a0500c150022544020003080389a030b51921502c01d04100c04407092800300031403504995403500a1180520300030150401d00140741045803411030110300306429003441c00c41c0c20705c0b1382c0d54050030b1948104850060020b0300385240d0900c0da0740660f646000c04210072000003000000c41c1d407180290342000308290100701d04c8000020104040082d05030814000e0407040d96125841400e1062003181c940d0a40c0a980c5410b410300c0100b03501c8075a5085140daa403401080c6121035000013840e60144000e000d044501c005060080007082e084040e00c194071510091040c01244403080c1d89884007440792940c0c4038036880015451a500300c0700040054031070500040e0191020690a00e150404c90b4241d400358402110340900e580c00c008030352064203200c40c805180540810700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 518460323 1250 518459073 518459089
    0x1608090a080a0903021201290d080a14030103050a020a05010f0e04050a0f15090e0105040b0f070903170702180105061e0705061014041a010f0201150602010f0b0f 71
    0x80c0c0301100c08665501c1e02d07841034082000858004098422a89488803113078020002298444454841d20303030b0254408410804404036003000403c1c0720850541c0307031551403266108601410400020015103185240d01c000558003942c0680d00400000c0e0302441804500c001c0c03504001c0c1030040900c130b0f00d90800d62103000d03803a01c548190740110b003035200d01d0340d5000a03020080444554500b001c10310070112480c240c4210031118400e0050150000451145080301c00c1917401411858250b0700241d510081c1520b5250030005528094200355525260704081030b64100810703c01140001c2c070030003940303003080007940c02c600b480702c820181354980700000d882407181c40780401c004503c21002801d08070010007507945494104056030500c0c80c1c00018a16070741d40360f004601989c07400710064100e40c01d042c0b0405603007891031840702004200010040d42c2c5101d140380d841c0d04564032200c001c00c140781034180090080c8031540011a401d050640ca000a03503441036070060103020344540303981071a90b84500c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 518461573 1250 518460323 518460343
    0x1e022a0a080f1b30011a0f1c0314040321080f07080112051f0501081203010b2b0e0f010b01020a02030a020402030714030103051606021506060f160b160809 68
    0x1c11240c0140504001592951804c4000240d403a1455003600f8061500035000648011200302805005540400648222041c6441c104140e01c16090001030300409001180c011a03c0d1a10704241c0e50760341d5100805107882e4403000c1c140d0b0781e148111255400c0907000d0740000d03051060000a02e40b180700102125014030807107001c1a4a20080d405101048c80503d408a041d0117425008030080e000d0700c0040d040a100700e0300c1c0d61181072004210f1803094015203060b44c2c206403420f8500402c2140003401280044052000a8240d0200c4240d00d0814424100301034822401390100310484142282120701521059040d900050345120041e43c01213600c1160981c1105c0040c2c4a4480c40301c110f0310385620000b0504d40e01e600000200c144600001c95020001340f12800e1032096071241030880c0c5075200b0710312629096014201040d61442c0030300160600c3c4140e44006818114441000500300e003040d40c06032216250b4505004a000a080c15068504120305003803070b0904022032a507680306411a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 518462823 1250 518461573 518461609
    0x10306060c150b061b0105400804080129030109020d08070c080601171204080d030e0c130b03010e060403050d050901150e071e022a0a080f1b 62
    0xc0203102954400b0300392148000301264081e00d03141c480c005d1500803c000d644c4c5200141c0c4040448008952006000706141a904000d80311291400c00324044500d0070310b03080b50324550610001c920760100b44aa207620a110410500e045030b04070740074051484c0c0c4603607501d010b6414440080056180c90564880d00c5a202d260540da440709410a90b030007140340e4004665500402000280044410030308242406e080d00580741070b40241c086989451146218080c40c1c7d801c42c4203101c1e0590700a80c800c0030441001c0c8203881c1040725000014841d1003c0400b0700e44070036501c1980d048141001d109071241c4140b42c0004200c942810384010b0100e0081140101c0c1d015290360000d59650004e401140300301c1040701c1404511a100c030f8070441c400804031500740c00107500c04010203803035a498001421144940c0c0241050580d51220078081c85c00c042c0107009000b40107100c880c51754803161a500028800038000d0210180310b0300c8081d007000d81424840700e85e6030030040401d10300d642d41032442d28000280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 518464073 1250 518462823 518462831
    0x703140c01084c0b0301091802011b020a08031306030f090218100518090f070636030305090a09022a1014060f090f0403140c030f09010306060c15 64
    0x10461000844040400c1803410000301000180e402d04c0201640c160f881c0c1c804140071041440740c400020358403140300030b400511003c09042441c1501d5603400704036070000d02000103654940041600c1d40d404081080f844113042e6004200041d811f01c19810741c1f1340c0d014418082046560001100c10321322048200b05d810203540411003075825641d00702c1c003c21000c0e1040302c0344415620b407200404800c4442d140350b8024000c40d52500c10010a52100780d5009171250b054070111042c08841b4006114100007415046162a801010484440724001c511950b0354a80e150494028000c03c070001d513121003607050060102400c00380984d0004407501c0045403200c1d00c2e2501e011101d52500c101da40c04400302514015081070110551522140300300300c140c40740303424000a10244003225504444a1911050103004980000d2103a1075031307404056010041404d01083e042c00c242154802000d5461503400003544c1d81b40e650701401804000d106038200400c0d41c9540da243d10a24003803000c10b000c440760b59 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 518465323 1250 518464073 518464171
    0xc031b0810050a08151e07091410090b0a11150624090f0d0f060911060c0303042010020624061e16060204051e01200703140c0108 57
    0x40c0c01a440081c282410940040b82081f80010700038006e503004601c14542d07110340b001c3c5a0b051494802054183e9a1b8034140b03003910b445034a52240d009491643c04100d080741091031801820003030030004411001c07006401d4104841081700788a020040c101030300750711503a280d500140b04004c1e5003200c0c0b000d80e215254503000c80005142c1c01151003005201103002c65034441841860f510070303080c00c1d10500c901c01d02c0c0c1010404226150040c0700c003540090340100006400074003502490114140c04000402035085c4078000070380d46113010103050005a00c10300403c09001d84020341c5d650420341c1d402a12080040201c08a1024400c241c0e041848909811001d40000c0c0316100722690803030003600306c004001051400001961003407040512441100141e45582144c801c0c20020108058494840509080150800d400b801a006900c503020701440000425030104001c0448034002c0058082d00485a00140400801409081c4800200ca020455400608040511000d0392007d91108195 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 518466573 1250 518465323 518465341
    0xc140d03210f0f290a0506070606050402030106021609180f110907030e0601300807170415170c1b03040303030b0a090b130c031b0810050a0815 63
    0x51400c85030040c54220b154030450b050741d0001c0143c450042e100b40d11321039950f003040b4403918007984e442d40c88000303224108190303d020720007070103e07500c00d5502040ca9aa41c900180898109034040c0c000350304210000c0512841c296158406001038990400000042d480403000340ba280b0800244004d0134800160148503210f0061f40215200601840c1e0328900414000d01034282d680142480703100b0700d00041081c1010855076489410304011401048480302e411a600d080c00e0003040d41d1a100c10801078002c6403140f0a03000003082c143c84040d41e640d18050492081e5421043e00c0e000f081808448032000d000300840140d00100050345068440f00455402c12007a41c0083c88114a4400020008100b507016004880924070860744070b4000341c2d03100140310a03901d481a0a681c04035018821416080b895448180351001138500050464205464041c10390100303a07010b004602d240040140d400034510308440648130a680f81d07032100e898200b10035501c908604c148506140c032680018038283d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 518467823 1250 518466573 518466581
    0x112020c030f030a090f03271a220b07021003140703021b0601080105070314101517090606030f030f12040f0b0708010f0f06170703020906070c140d0321 67
    0x2501b041d2004142c2055107000b600360105100c400344c0011540301e0300b29090703000c2c48950b41112000800d03039464588011000c00e15500c804011901c49030855840c000d450007001c03142001c0c1400940e281e0b614081c1303004100803c00b1440c0b00400705030070104a003448903a40700074242c0006076801d01603210070b02031030281800285400740543c188610000010070f0307281501f045015070721a071002c000c0099220104162581e08130b90745140c24509010400141e401c0d561040c50000d118601090800031481c282d500490f400e84421400b03601500134440780f440e090003102041c40450f0300031842c1c500748504000407400b56a00c1d00c0e2020300150b0000d028000080300303030320728a503201411813542e1a080d01d0151a010003800340f4101c403010501e021407a20085610700090b900103032903110286801c4130101c91160030040600040540a01103c240b03a195000988090791080e0a4012440c0c286010303040c1024141800070320406412101c0700100e40c1244d142d02003401a44080801101108a410090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 518469073 1250 518467823 518467841
    0xc0a0b03240a180906050106090f150e10020c0108071b020409020f0607050604030201050609010f03080307020c0604151814100e090f1e01030c050402070507090e07050112020c030f030a 81
    0x80490189072018015a031303840340344002d11480c070801c035607601c4070310887e400e42c018040d00c050880d1205050059410030a0f044103900410b10303104a18008120100c3d61300804178101c82c1c01360340001c82c07044243da007020903241d0201d04d0380303444c42943c170355542e401c201541e02c154081d0203290303651300050964031a8480e8804c2c119026107021764840300d5182440d901d4000b01c07815001540381001041082c40c00f2244681254010112900d40701c0c02d41d12504410746c000760425041d44a400c01b2002c4640700c05000d000140f0740c40d40c8440c41140090320150140c1c0c81414964000a1086000e028880d001060149c4c00c010031baa12a08141049105640728000c2000d01644280d881040001150341036400520509030071240c0400b44c3c2d6206005801c03100207010003015180c504406008034241640503003181170144040300e0b00c071540c4103600d0040720008840c02c1d8098110b0030040c4402e50f040102d00034240e00c510350440c030b4440300c05801034886c003c0104a5545280c008042001007403103030002e80c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 518470323 1250 518469073 518469089
    0x6040c05040302031b0307080105040201080414010b1518040504051902031204150306050402090a050910170715090b030a0b130c0c120323130804080c0a0b03240a 71
    0x103c6600741100005c40310103c0d800744c0c401d00c9400000f0442800c107000e224002c1d80d06031100c0034103481e01da41340c01451085c01903050403507603a650243c0d021307620b503e100c0c005405450240d960754085603201c071401d07040c2c0000b054000e038245814013001420015134402d45040c034600d4641c80ca081440020300349042154444400d107800300f80421180008135030382c14008200e0300e01300203840e500e801b0b01c0164003841620b02d603c100504020041420041410750340901d85540040c2d00c1a115801c4560307200181442c5181a805450244503151a10014655400711401c00fa0030b16450038444c01b15a02c0700034a0b00c0e182c5501d84443c074210f81c841c8d0b20406001e940c040b01c240400444000021319513000d00c0750584cbc544400785914094140a44203036000f00a004003480002450b80c41109070805000c1c10034070075201790a1664001c03440180203400039040301e602070f24072104081d00704030b07204046400040340110208140840740756460000c821131041108540010000640092101c03050780d401254 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 518471573 1250 518470323 518470333
    0x8040b041a0412260a1518020304020f0d05030703050a0504050a030f050c010e1003020304081b06010e09060708010e1f0b0a12090302070b13050d030503041a0f06040c0504030203 78
    0x10800200841c1403a88060f0b50361078240352000c02e50308550300000c02100105a429100c0845d05040a03a041481e55841690301070040b02e58401400c15042e141443c020700313159022043c801140f4182c47e122040500c116038407151800c0b20748500751a0300c600e003001400e1100c00150303100c183d4015001da41c001e0030010a44641c5c2603403800c1024650042d0641201d044c00b4404c585240d5601401c0c1c14845408003501d4000742c4120094150020741c00604140e40d000414404007580ca082101c0d01d0001080c01c00149c21903501d4034a0307408508030058415180c2d40c01c0714003000b0b400340e44007a4140c115100e0044440301601d50f02001c910b0390f14140041041003441c584081617149441006000d106655683c0e282030407079034448007081307881942c1d0040041c0c01035101040047c5204028100c0720003200784088005544900003411030802e4081200415408400c00c0140082c2048403071051a8109280f09103160900c1180d5030344c100244090703c40d580d01d0b06500e0059214506940255901a0480c1e0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 518472823 1250 518471573 518471581
    0x6040317060301151202060702091609210b190501030302011a0a0e070819050a0b040b0f0109060f2705040e0706021504080702030a060e010b010f08040b041a 69
    0x284140c00348080d00010202040c0403038501d040510981100d0300300034040040c094140921100c001d804803100380da12000c2808400c005d642c0e0140c0e1310740101c8601c42085000151124041d010300440e50041350708608500c10f09400c10b031184001e00b40c10f94000c3c44950f583e500e84500c00040c202010720100780c0c1c3d01c0c080c008020190150720a1080f80782500300c21000040323010030000740c2201c60060303210708175100c000300b2915400340c2c0e0403640208041c2c040101a881603860b460031154121880d030426506e89000492500306441aa0848101620544130384a035810020303042200d1071088104200d000008045103921540c120620006011840190f4005001c861132080c0c0c5c0c54003070280f01d1340ca007c815401480c1d0008009089034015009003c44266000740e08116901c000c1040c0e5904108102c07a00040e90140084803201d0702c120800500c0005142b00b150860300d500848505000d00c4c0f900c5600c056402480700741d802307175000320001c100c1d03511031401400f41e52052000480c103485032001c0c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 518474073 1250 518472823 518472827
    0x1b0c0f0b271b1002150705070210120b0901030506180102090d0c0f050a03120c0c0b0a0302030a05060301270c0e0702030c01050705160f05010605031009021509101d03060403 76
    0x30502001480b28100030070001401042a80702c2580345507000342c0d009800120807510600d004503400541c43c20f03c141071658035004201082c1c000850703c800902091003170159150745201d05580d9000595000c0c810b5030561360740f40d940e4040507011502d40314a00b070480507080400d40440c2c0c40202e01800424248a241c036001c01c075036101e4050341c102c001082a001c12141022040c50003100d4214040c0d07035054003c0781042e074800b100e40c201624015030741c91021400841010017080c050041e55001a585c1c9401c1040d10304560000d054107102e641091459410f211248501c000d428420000d400880507c52170210303902c0d0201c0d0300c000740c8d0f008040100a440f54011002e080e40c02c20220003440b442d070b070700e40d402c5405106802e600406203065a20920114a42c00120500f151051000180e481d45680c0041e1a000c0b1005040d500700380c9411400003141010610800e00189000070300e4102035001e00001e008185a1040300304202c07141001ea441c1229036008842c0c41e140c00b4058400600301402c0c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 518475323 1250 518474073 518474083
    0x70e01230d0606230d020105071407052101051510141201030503040302030f06041a0a150f0f0f0e0f2d0a062313060b0d1b0c0f0b27 58
    0x5100c01c1e0200b6403801e14030317400d04180301e00300d00364142d40d03062030180030340d80da04a0f04400c2088411584660900451180c80300543d5401c01c591400001281d6041d051045094a80040641c0c6c0c40c0009001080000e450311640349400c44d08a04000c0f06909500030f048440e4010f941c508811528480c3c00002071000101c000c100303890007035003641e0804001481e401c5da00d400658000b45000c213101c11100d40a50504071072a002580080c2c045029905045049029069030304903070050044802c082010b404c03696010f500a00c2d540000680707107460426111a540c031300400b1a00c07103174030b403600085003072101110082e5001c4807034040015101090011740351140c0b04980c01030071185809808601c0d040c2c55a4510241919000c2e4a54440b0a11041c03282154909018512061720340c40702207038441e07850018010494852800044000200400402080c010103048040c0111006000041964005404200c64024654240688075680740300700c0060701c464054015445101850980200810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 518476573 1250 518475323 518475359
    0x7030c020c191a0c030d0906090807120f0f020606330909010e010b0a030e010609060b0c070b0a0c2607060b04051005010c020d061104060c05070e01230d0606 69
    0x28a8103c18280c0300d0680340540705081e4038000316401401018040c001d02c1d0420800782e4424100410829030302e40e01c1c3e80c00c4e9000010212014804c80850800540d4402548800812031340380c840681818a10040c3d01d8a0300503140d240624250810301c00c0758a00704910748125051201d560717407900c240565441c0071742c01004c1b040341308085403c00005c01e6103844940c81c0c180c40388950803a1400f80c004100b6002400c50350f0011b5202d540702d0344005456480751080800034035080c0d54140c0e841c0502e003100341c01e00304a40c0001c1450300c03081c0007845025034440014600103900a18a02086292000c444489424800c0031208440c00140140c108181c54200400c14101031710203005d02e86840340c00c100c010410b80100b600140400e17100c02c0261034155141040c1500407080001c4503580c0030f2092250740d000d034020001040000c5034600420100700b0542000345903c41d0307840c1481d41030404001c22017030520042c0900d1885404504103e681c1c4c0318001c05015444801007060560300c03803020100c141c0c808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 518477823 1250 518476573 518476589
    0x50307031206090911060310081204080f070e0705030703020c060c090f0d05030a0c020f040e060618010303020d0518100207090b0301051017031b0723030607030c020c19 74
    0x1040000f0380100d075000f4054600d9200d0409030b00d082000c4144051030300010070b05c18202c20840c00c0044c81c520b05103d41c03003281d035118080543d1070f0b0500c40070b10b140c201c0e280c95900c000e9010f51000c0244028801c42e5540108144c6056a90381c1c940580c120003078010054440d210340a0b050902c800c0c644d90400038600c41e041038922800c41d6103801d0820503480c074591005091904200200b00310f480c4900705a54840340f000340840700603075480022900304d0b070000040c0e4402c3e50002c1c05005162411000e0810b00c0f176030410792a4525811940c00075155030159480e81e090090100c1c0c08840c030510b103440380800100c09860b046042100c610020764078192032083c81200c51030803000990b41d00341070188a1269041030480c1000910349190701c2d0100c114650f0103940b40c041404100340300004151504003150545c8028500b06003000c80b0b03000528444804400c07504010091700d04541c0b00070601e16801141e80c00c00007041ca5680d2806d0382006628090b01c0c1d48450418040d880f030541c4600d892064400340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 518479073 1250 518477823 518477831
    0xc120a0801150807020615060705060f06121b01084303021315090f0902070c091b18050303070f15090c03080f0913020d1b1b0f0503070312 61
    0x40b0340545050034251401c00060300a440000e05034015205001c208483c00f505241ca06241500c6403401c01400f034450011095050003408154a0f182e130800c1796018075a00a4034031040001312000148480c104141d042c80034800000b18610307003000f11078403007980c0529111188a402240c0e0400c04104160b0488000310402c3d5541c0303030354800d2003038079400002490344505240c03d0208a107046c40034140c003101084902030011466800005207580100300452001d605c5d20118603101404607181d030010720726107213070001c01c00e003480c0740c500c1d10005c0782d1701c9007420200a40448880d548030740d601c1e00400c1e090703c800038540c8200440b00141030308480c0100c3c1030403008200e0406040c1600c006003400703031104511081c1480400e884100a1a800124150a0380b49c20b0202004c10504a544040b400070943c5c0071075507005020490080c44d5200c641c1910800300c000003004c0107041a9a03500d880400b442e8444200c6c0100404001000751154022048a848501a2600500203848140300324940b41c14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 518480323 1250 518479073 518479109
    0x61d01050108070b03180f0703110108060109030609061104080a050c0d02010905060c1c030b100c031d060405030a0b04020a0e0708070305071b0602180f0a03080c120a0801 75
    0x61103210305950001c00a071520b01e2406950000a80000e01034828840400480c1c82d0724042c108451241e207010350015201141c51420000c0b14002c20300300315410301c144002080300300ea82c042cbc24001903951000001078150402c0c18804010801d00c0840c0094143c0001c2c00305181c1400603420300094458021205604c00420600625441d26600240440e5946e14140960301d4254050501115074404aa50301348208540700b10004e4003820120200e40c0d5401c1159060404041c9a60007034020308020402d240713070755001048000c414144080900181c10002010342d0342c0301c01c560040c10b0003411202c50010f50f04088030030002c2514200d2207040e101c140055591103842e50b080c402d03041e54407590440d5440810503401b41900074094010040100403086905501c4c840f11405280181d10050f15101080c1056031100f00c1c4002c03440c89104051842444d41e81c8045d903501c05d6035030000400f5201c1b411198568a030282414031226660004030700310502e40da0000c4568102c0e056000304850f4500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 518481573 1250 518480323 518480381
    0xa06020310081c0807020f060f0f0f060d06151d09014a0a050a0c050d11040209010201020715090308150d020f032103010905060102030f030106030f061206 68
    0x3c040301d164038002c100f0b480e404843e240640349090b0304c1082030056410241d00203140a00f0004200e0303952250000003c2072154110340350300c2c26540310721088032001403405c240c40014450a050440208103a480d034450030b22401d980565280100051641d03001c840030071040b5040c1501080f03c9407902da6181008507002400c1401a0b0b189040c544019100d04031125034019021201c2040c40b0301d1912042400b029080c40d013001000446070041c0c000e0312000100d45008078003001a1b9104c02d101d0425541d51101061040700c5404ca004000c4400696074094600184e019004610015002e10b5004003501101405d9420844042e0310983c5c0d98000d03a0740d10340c0801c003c515844c140680010401c507501c0d0041c201288808045500101121010314041590031805840c81100d00702c0e030000800100883c620318010650440710034006941404840c1c40741c80084d0005128407000c1548828940c03048142c19400340000e40741800f41a07402460a041ca031020302002c1c821500c00710050014108988 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 518482823 1250 518481573 518481583
    0x20f060d0f0902150a0818031b060601021c0f03020c070801180b0901090c0b0d09121106060f030303040b1306020f0c060a1406010e06090a1413020a0807030515030a0602031008 77
    0x5d01141c8444003a920340410380780c0d01541101c40101e00b448104142d80a0416141c00d94007182c01c0c5000826203468040002070a10899010311510350086040c05402a40c104c00760f00d14845003461b0058070f03110100b01d40791820700250f01c03000710755280126003a5810025113001020901449004000fa10b5030500071b0700b200e10741800a001c18480841c1488a040000010010005c0c1d80801052701810b903150903606490b000900f00104583c2406000901000d100f80d69000c4000c80e200420f2104d1000483c0c0c43e444000c000814440c0407400056514002d410b07410049604400300715105e40c01c14812a02c82c0e4040000598584140400030700340381c00c1c500a114400d821816140610703100c9000540790060768580c0b05600a02c2803010300e0154407240d280034001c08502d440520040003080a100c1c01044245415010314010001ca80100c0c1d000b4040e542c10140600d00069140e03501400803110820044105900d400f4400c852824400346402a60255a41c0002090019a20b01c04c0c2641c1e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 518484073 1250 518482823 518482837
    0x40816060e011b1b091a03030d051b0f040f0510120c0219060501032d120507020301050f01060801080f1c0e03030d05040b0f04050a020f060d0f090215 66
    0x2400c01414050a5441081d040e0001003440100302d2482846580340c1d0007041340314400c0080507814640811101a00d030081c0301802d80000c1006081684901c0031946a10900d85006080ea440780c000c1803000d4024031207080d45200c10002262200c80d026907903001130f886031041c01032049100b0b101013550303c0d2212540c00300783c125441d4030190070124000880546000303000c0d402903000d804c03101c035011144045e05030030080c880d400c0043d0560552414180c0300703100407a4a05807030201d071369a1610040d4043c0b4402d4050300320520724821040c802c001c85503407140860080d0103501380f1003030000890a004000341079506503110650030f42c5e215603203956902409050b140705988048141c14038034414066252811040f442c052070303440191000710740742d64095100440340c90341ea6070030032061102503480e454110204864120a9048c6900e90603074462400304064441c909041f0750440683d5030781c080f502d003654040018449a05011800801003110310816400303000700c42d4000481d555004200c65007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 518485323 1250 518484073 518484077
    0x9180d030c05030f0705040512032107090e060a05060c010e0c0303030601140d090c060f030f09020f060c0c100908070e0f07080702010e030d05190b131a041104081606 73
    0x4507510280800c1d00310001071701c007005100c0b0400021801c0d403202207040c0707400b44011004641e0f666800644c1c1e180c0d5040c071008855854002020311081030f0348000c1400840c2d00c8a5008200c9407a403000007000710185502c51503101f40c0005070000d00c0300d81174000f081e1645035031040d1040700b100c00c000d041c0c9074441210302e24000362104640380d07000d00b003000280c404500b402c1000200720340ca90759031040034030b52608144041a841e44903074000d16850f0150100724a80c080052240311103560201d40602410807100780309003c041807111103928200400c07001060010268070581102401c0549035802901490f0380e00c0c080c4003400b00303c1c0003104082134042e680d60201403403140d0311030508558640d000b422000071075480c0d03100e5190700c0c0c40c10805011000000040010141014030103045c00d0b43d00c82034407441c4141440d80e20b405d5507a80f480e89407da0583c580011a020580b41c2c0307040010659190016403052500d0104901c0c920700d64041c00030340b04514201d580c4940c1c01800d0688020f010300c18800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 518486573 1250 518485323 518485327
    0x3060911241b06040b04050f0102040312050a02031c0c09080f0d0e130c020c01030e0a03020c13021e120c120129031303260c0c0c09180d030c05 63
    0x482481c0300c1c00106512158a59030364480742c1408020342c18680c05035010345d2044200f10900050000620023030403541020402149010b1850365401c0320a007040d280728051210114040300c80d64002e101310340401310f00c0c01e080d200500041c00702c50020035600c1c50000011318640c002145181d4001028400110150000c00c4503c20000d400ca5512102c548000c2d00581c0c808620800030015004464110017030382c0141940e00c1c8000001070032200b59400e81e070002d0344856100c40100c1d40200320080510000d0742d012203030001481c100c0c03010744104616000200f61540b5081c2818065102a08605482c80948200b98036612600703286409804809c02c4d0040187d8010071039080d81001584403d410b210b5900320340041d409030091345030000c81e81b030082301c0b90110518040503400550340100c0c030f42070000030310310320392020401c402d5440c024400c0d0021040040d041c91500c500704400001054014420091703480c00424181419101079405030041c400d003915603034840d0190184c00004c01c42556468 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 518487823 1250 518486573 518486629
    0x801060302010507110301230108011506081801021c0615031116022209020a0b030108070b07020a081618090f03030506241201090510060f0201140103060911 69
    0x5e0001c0256a6401d641991f0b1101c011a62501000301c8a2024041c111818120f43c5400d5220782503d1401c102e48280d810a250b041c000c00d5080031310b031a085445c01503c40c22002e83d070a1760500a20514641700e4125070251a0381030b00d0703421604548103a5076240840d00d00b10080b50000d0b415aa259002054981401e0110801c11030350b441d9000c000317500007802c400c0c9026495001403403100b660b680509059454501000660070841e071003100415049907460b1a6614082e019032712000389010f0b0b0401d2450004126095565510074103002c1c00442d0251200c3e14044802080e150b400c81c814203a054104210a0b2a5034455101e20803a6a0704946401001e801565044009000c01000e103540a841c0140c0e80840a00c2c130044506210030365071070942d80d00c5441e82c4401017003405a00015046e810201003040300400010a00121116807c00400400c108001607001d00604404a010400078000000a100c500e40250701c1d00c40c0900d0f00c00854003040301c103102189048140c00407804940c0d01d240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 518489073 1250 518487823 518487833
    0x503070f08040306020304140c1005181315061202070b06010c02180702030d15080c0f01050c03030f04020a0626090109020913121e030507032a0305010801060302010507 74
    0x110348030744240c2a8510302600c0e03079030b00c2040360800c0d9000d5499032600c41c2d00c458568420010b454a809003125041000e92090b00024158403407200d015103480c5161404451079101d200320f610402140401c10b128a040003d060320303030300d00103116420016520030114402c806503032084421180d080400029903070358682c0152004000c2c484102d81006130309140e041e080d10509181402840345501659a94a8012041003a110040210304880c08440410040c034000010112544036055600b0039175040351f8001130302c040c0105404006c00c1d002c000204070720b002070a0324091040384200c8a0410541d21003030203c2c4c001c90380082c1c403018144a60b009869480d440c40f02d06500600c2c2200215401c1c1145d40402c005510546402d008035003a16101e20030000d190a200c09600c0c0075140c61020391099110540f0b818540c0c03c24281815940c40c08142d181c2c2c801e4004054a0302040d42c10480400029208c01c400c1e007900c080c040c00240361000214400d58103000d200b0403a90140d441070f080240640758 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 518490323 1250 518489073 518489093
    0x507030311040902070302010603030806062a0a2a09091e02040f0c02030d0b1c06050702070f120515010b040b0f070204060608040c050406030305070b06010201090b0a0204140d050307 80
    0xc1e2440a842070000184080c6140010700203144250700202c0d8591543c54080d1105030041c06c1b20344104014000f070b0110300181c00075203842d182d5a4204202c20b0500d02840d070304004500201a1202c40c20307813000700164001d40f902d10600410b00c030010558550305c0c0482c03422250300940041003a41c2c0c44020044070b05000a191070080e00007040050f10b26400c805200448090300f6000d000f581000c10400c000301028400c0c1020214152400005c072140420290014011070400400d200d030b8078000710704840d1007002124040d1982d5100392400c0f5844134468140944420012035607845007000100b0350003001e007001760480f500c41c0340050519080c0305500045400440c00c03080e6082e414444100940c3d20307030140b2070052481da150a091418103007014640508581c010f80d0049003031650800002c2d81c48011911825040884d44249490f5400103e014203c46c0700b0180000124000f40049070810707038024401c44002ca4040ca540355505801e20003c442880d0303001e4542d805c10b11180021030480c0403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 518491573 1250 518490323 518490341
    0x70f08100803032a0c191104050703020c10140112031e08060a090b030d050d140c0a02070e06060307080403050c0a050a0b010501180b1804050f100f0605070303 70
    0x4545021503495060380d51454204031000b200d0380c0b02e9a104000011340ca208580c03019500c10348910b140c11032600d0b00310f550b41c09800c4004c6c55102c085485605102201ca105166040700074000d1049007404400100039420001c20822240220760100400102900ca658408001030f103c0031580e80c03800501c1d176103000f101401902408500d030011009070190440c0f031000300ca10790700c9010180c280082407110f10601034029403041440e000300310000395400242412600034610f01141c2c0c82c414a043c620181041d560282c0302a1845800e101c1c3e410054005800e8000c015401c40b0265036464900c8141c40c0b205450b2141c01107010004500018840c1918551050003801d101c0d18089594a0f4186840b52041050b40c207a000034800c001042480c0300300783c1c0101800d2030300c014011000305040c003003000640310780501500c00180d4101c4421502e1118490310800400412440c5400290000d824404036502c2c00709401080d070101d01840c1c050b0b40e0800340c44c025074a0307a003404201c3d41c0980090400341 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 518492823 1250 518491573 518491591
    0x90e220803071403391210080a06090b060d0804052806020d030f0614240715060b030f040609020d0f15151404090c030212030307090806070f08 63
    0xa4038204030000054019401483c22800d458024030141c4481100c4039108141e4a0700e6403100303481c4040360f0800300146c1d102c03030500c0103c4034016210440c2600c00d130125940651498003402242e6824000180d1107401d0700c80c02071482d0001a81c81401f00309030a80b880300002e100803400e000c1808030341007100300007555100407441402c0042c0850240f8031041030b598404001030344942240c00500754503005141c507696040c03c0500015040c0b016800c4400d0808004a0040421401603041c0c00030901148a040c0818030010350343e1074860511140360342080c44c0c0390000318106800003c884044004881c0301310803a549148031600e4659403a00903200540042c0e900008465005010aa6440303514800911501c90041002c0c20000581d0550341c8070422810b10b01c0b44441d003001a100f0610026803009022640010460b4861030425601300441d04060740200031b0408c0d080f99504000000c41c0038020301e80ba1005c2841d981c0071039079940c002c100d5220000036040c00051200c0b034010900544c01c40008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 518494073 1250 518492823 518492837
    0x1e020d02040e1003060b03010204140d02040f0236010207031e05100507080a060302060f1308030414090901090f141e030405100203040305060f1003080406090e22080307 74
    0x80c001800c08407030150303503d94040780300b42c10030010028180300e1290b803c442540254241842c2c00d65402261945001a43c082c0500d0b031500d004650307072a8050031030001c01c00c0085449485607200f030b211900d581c4400c1008454001140354600b050100c5440c01600140e0041c10f0b0b850540e80e500107107146e02c50903194901c203a1800d0000044082c40320301d1800c04039032000102d0f494551002041140040c12031100649001c2c070500140c0c807401c0441e02e4070703419034050a95070102c0c0410707800341d0f006651000c1d80b07900020130b0110b2144240c0b48441d04c210b00465141d41541c032100c40c00c034206c403650f14004000a200485160000340f0700c0510445190220781901d5485480300d2143d65215840000900c0030303000010217200078500b040328414000c3c0315200650130079080d030303450a666100185c849040c200400c80000c034500701c80d4028101465011110a4495503107450240c042c260901030f18000c0720034030780010044426000001001550b4070780b1250710030202d84803080700c0e07032000e81500c04000744 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 518495323 1250 518494073 518494079
    0x5070e030d1e20060106120f020a0206360312010b030702100b06091903060513030210181401090302010c0507050c010c050309120c041b0f1115010618091e020d0204 72
    0x1c141301407802005035444d1500c2a4075a06040801c50712a802c0c00c00040f441071180c1f00c0502e1340062201c0c0d02c540a48401c0160500301d41c800f0440c090003501d05200d00c080510b60554483c00030014202061810741500e41a0b601c40100150600084034110f0059001251034007a128054200d041c441030007808652901d2404004100000701034180e581082301030305020002c00003140701c0c05a1001e15900808400390a03560029141c46902c04045041500c4044904660000039213205000ba40000c500240c009800d0b03803940a0010840168055460091203001c500e00500803945040ea01c07402a04030b030443c8100540f400407003500e05441910007070007521030503260403082c80c0500040c100284040d006d40d0f420802511100702e04102d882411480c040f84c01c80d00500301c1030240322103013803500703100042c4c5140360f10300b024080e42d25000c240708030000121301e80c10441900030b50103003002c202a0a5240d21642c400d68032015000340510541c072500700590000c0780d001c1c01c8020005d807005450603039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 518496573 1250 518495323 518495387
    0x150402030a03123b1b01180905090f07060e010806040510180603061b050f0f0f0a050429190903170a021006030c0e0402040209030105070e030d1e 64
    0x501e0f01c00c24001d114080d51030300c404c14250980700124200042554418030032503841e0266003c14510705019200c4c0b40c0c5494411913032401030152910000130411854921f00c0c0d55a03c003c48190801c8a0080200108070700744601a00001b9110684900a864440b001400024000140340e441c3c40e03100f045011a04000500f01c45500e05a84040494903a046080038021620301c07080985141c5042c5031604422130f000320580e03441d942410000ea403152489400c25140b4401c01c801520702c079500081000000e03070884003520903141490383e09024104600b1041c800482c81c4411511503490911003185402a41c1a40c482002506c1c60f001045d60358a99802801c04940340403102c0307600303001c60761441d443e9040200305469900d458040c01a140307180c0750a490a03100c4c0c0034201c40c074000c90000900355216134044500d0008003a008000368541104010607510031032803c0c1d40b1a02500048603100c0c0e00c1010b511003070b00007038168220f0701c034034400054405101d0010409600e122640e00740b50f02c0c0c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 518497823 1250 518496573 518496611
    0x150402130303020c011d0a03030c030207030503130f05041a0f030f033004151a09090109030305061017070c0c23041a010311160c08150402030a0312 65
    0x54407903001040720824000014142c0c003c6005080044c2d170400056035047c0da0381c00140000c40c0d415061000e29020981412428911990000751061000140c152010ac030182000402c0320503290100303159680310820002920108050a203002510310501d00142c030301040c0a4000200040440d6600900c0b060940d0850700041d48100a103a100d0b00d12031900c810504a5801800920030041c0700b61416a84054525031400080b030180340e50744492414810070f50031813000c000b1004144050a14140c0301b10740c040d151039141280020f08100108402d410071119040a09406455280300e0160030100c0401c0c11034014885410021150700010202c0c031420800006004c0b90070042c04010304090500c07101c4441c4684aa009515110380d01c0130307000104c00307500300341ca07000d190110381d0305400c8040a030300340500c1040304840d035002410340080240512400d001c40348248180c507994280c4242c000d9416200700d501a42642201ea92480028414040070840341c40c11400029102a1803a22103220 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 518499073 1250 518497823 518497829
    0x72003070e06030d0305041e1104020f0a111902060309070b0f12250509010e040608101104030c150201181101020c0a081b03100c1709030f0315040213 66
    0x90404030040c80b400e0b05003808030155151180c203007070103a1b06013036485801d4100003e020098400c2c007211003401f04042c0310725125401c080240159101d80b4580ca5000c00ba52211b41d40310302107104421540d01c1d0000c0880c0c480100449424070003d081e1007a0280541c513400280101a0740c0100400450219140c0d0041c01c954850203003030039100e180010840800c5240500910b1f0403010399669609240d0105031040011001071400e107443c2c4481000585955044d00c0e15198010304190700072881100008000088200c4080140000e0140800000152080e8040030f08040c05907101404000c91601515044680320b1000180c03034161580c00501400385040c00315615036040b0012101503904101039a1019422103400040750715001200360343d41c0755001c40120b110740e40c0c44100d15580d070910104602d500210014000065007010080030503440358a500102003401020500c070700000000e8903042d400c020f01c03080c6180ca4128034a141400c0c01c17800b440d031081d0200321180b40c0350340b068950701c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 518500323 1250 518499073 518499089
    0x152007050607030c05010f2f030c0d1b020102030a0c0504140405090304030602180f0316030b0705040305030f09091608011211030312180102070209270d020303060f040c020307200307 80
    0x5540c896003888003c6620f00908c122004006120302c2c181c0c1c0e84104403900329441910f1641e59000c4111010060708002211030020302911400c98840c0703030103400851007610095010404400080b03c15103450055000d12890310640b506890150704156000030340003000d0008980c2000d950b40d44600c203a0f40805070f502c030008103d100068030340c00c0603015401c00c0390080b030151046408629601c0f0340d180f007900c8040c041c540700c4800320345864051f80440d40038541100650f43d44001004200e0350590003188514007485010340090120425201e0500900d0740315522000c0d90303464402c60301003200d0030400a40d1300b914481c01c4840c03956410002016560000000303100709207402100c2c0200e400c0304401c1c007040f47c5d0041203510f005aa450901c254060700001c486c08810180c100d40421034004400318400c24030030040c0b568601a00000614442d09046644030111300308041440103503a640203068000d6401402544001040a03820444045100e0610364000c075482d40007916000060703100340c0d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 518501573 1250 518500323 518500331
    0x30d050901060810090b280c09081504021002060402062209020a030c121a010804060b09010f1a0a0f0e03013b03042702070c152007050607030c05010f 66
    0x108140c6c061103613070041d603c030f0410341d01840d40b2040f00b50f481180440b440700c071075444510310101d900400000340a401041d00f101c40d0001c261108284022007078800b1f910803081c0da43d12903001440003802d0380c4569405412141440c2031480b2045c0c1c2c0382905c40240310405800340010808044030302c01f9196940c0b948c3d602240c4001420406801c0d86800b101e039100040c10264a02079020022242c05120b40080c0780004040da624144200240030848031554084581d00000450103402e40b4548251800c1c06421560350060080301d03080e91003900d255401003400724075030550041c007800800342c081d1009400420401050540d0401c1010344454583e072011507840300c044014142e103043c4407010503541c0250314203070030014100c82d104040c10621300c0a10000c0105c4164a80d41e80603505082da0040d040c46e075050312590721000000441c00c030013002907103025460284d610700144510030307440d800700504072080c1001d0038840b042e4841d0314241c0c240006081c1120002c2d20074414144028440c5074005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 518502823 1250 518501573 518501591
    0x70c0506030f071e0e0d0303060905040b070906030e0606011b050d020d030606051213020111060a02030402010813171e0f181206010e040f080309010f050a0e030d050901060810 77
    0x6000b03039402d8044d04541d10b0345180340c5100143c000203174100000c0c0072200710104003e1807808402400d030079000f881d244d0741005e051008000c10a03080d40c0c05180c00d40c4605403440c2d101c0508804071f07202507052400036403055001c92000d500444182841c00c0c005044000030403001d07150a07161817010340d80c1e44016488413900500081d490300c101d0000e050103140161810b07004049001c40044060403001d941c401540d600000c6a004400e0302d00b40d02d0403401980e21601c0c0440001c4001d400458040c0d0100c5c2d090000034151078030424031480c00d150b102c44401c8482e41341c420005161740180b000f41400c0e14030400142400c02c03140b0b02502282c002ca8101a949a0302c40d1084050f100841c030025000e01380c2509181d242000109070a17040d00c20380d00103520343d941d81d0304059801d8403881c000944588400414800b142c02d0640050080c2c001e5410700340426211841c1540866642000e00382c0250404e100d5040d2041c155045580c02069a0b80049042c5445092070340c24019084101042595038440032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 518504073 1250 518502823 518502827
    0xe030a0c0f120302061f0f03030e0102011d033901060510260c04090f330e0c07020405011e0b2a12040f0905090f0a08070c0506030f07 59
    0x240c80a04030189000780049556900031755909009041c00c0b00c5010b00c40d0104e00f1511214050f080202a10700415420981d01c0c00d020b8440b0240030002801542806024018a0400301d0341c111600c1c40c8070000c614024010403501c01d41c00c22812480030b030440c0d610b946002100301a2680504801c0c601c000503006151000300805840660101010701a45452220804281e08400c181c60089041c841c800c030368400a8200842c07107103810054940c0e1130404800b0340395880307500c4030b0f95543e080504164040d40c07401c012891450800002102c10318006001e0220702c8401000d80d07000340d02e8a4569003407215580c00071701620002d8000c4242c1119807a0824000c003007000000008000703020316240b420840207036049800107040d1450100b8015034400501000081041c84030002411200c15110742e202c00302d480da01f030000d108120343c4909007400f04202243c0420780104001041008207031042076a5075511b45070300403600c1500d85046040c00010103440f2100158464a54901ca0900500e0700c4040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 518505323 1250 518504073 518504099
    0x504020331080304030f09050415050405092107020a0e180d0c020a05060306010c060527031303030c050f011103040317070f080901020d06090608071d0a0b010e030a0c 73
    0x301c4240c004200d4804120721034116a000703901841d084c40307200d0f00d280702038070410107641c0000d800918040d144a04664500500300903120100e801348040e840e1440002c0d03460300780580300e2b45000300140400f4010b0340090001c0c01850301c0074111906140d03a804942450820491341c0c0c94401981400520301e010043c004001170f0511410326140710045c1340c000c200c0f4804540a00c502900d0000003141d40c582c002c0c4034000b501c80c0c4c82501804285045414040d5651480000c4c400541340760002c00c034160004010303540110744600000b0702c8a407554078100d6003165155026102c901903907074442c1007074800303014040d8030a211100451b41c90602c0d2600030202444d010300040007103d904140600c20354460880700041c030f12807804c80040e03282e084207540244240880b840c2094900300001450944d150000c000321034894050350b40c0280e444880032140240c542020682d600c2080000301074204551190040360018902004104503000104c2d01e8416450000d03a1001c410741c01c00c02080585180e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 518506573 1250 518505323 518505391
    0x100905030309160321030e01090614010b04030b0a02030705120a02040501140901080f04061503030207150516060938090304050d082d0301080d0201020f16020a05040203 74
    0x1500c003401c1884c544406aa00059007a02c641d2140c0246034820b08a10907081107521001038802000100c104c0d1802c0001440300900303c0f40d0004208000041d850781c0d11041e102200e400101d4044030b5038510100200075800202840144402801509090300310150300c144104410b4100507921801c1c08009480c12603940109003042d441041110100c1e40d001c0c81c1660403004441100e46c0648035498003001410401c1c48120070408660b10020615600040702002c5400c885241074188104042c215204d101368610103c5460300c000410300001d041d50f001c41501340c09081000124010031303002c0c90b0240603180c0c0010300c40401403038903400504c1008400e600918061f0045203414a407401050b10542c081e50040c10006020414001d2108040070a030704031210300c0da1245203000c0c04070b200f0030590400e000b07022a070300c0348800303401c011801403084908030302c0010280c0d4140502d005140400080c006800c0303801480c08040002d00e40c40758001b81d80900001d1011040041240c0020741603691150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 518507823 1250 518506573 518506603
    0x3030a0b06160b060f10020d030506040e0d0c030c0b0106031a01020d02060106030213030210020607080112320106060f121a1c12090504180201080c0309100905030309 73
    0xd40d0421002d90280807480c1e1101c42c2204035540e50002800035612020a0350700a04070089000d4070b1a804150280b140500f601c3c2082144c81c0d40041c4800c55401d030004120990040000400703c5004101c620300701c900c00d02c2e0113100d01c04c5903668a610a10280c1c00000825150040c03840711601080d60b91011090078030080c140c9080164001b59104810310400060683c00100c4441040506c81010051600540390a0794000e0050700250307582e400301c50000001e05c0c0f0400118615496003841440c16030800c01c0c500002100c005004018000c10204504c80400c200c05090720b0380c001c2c001d4000400e041c3d01e0310119400c0d41c080140c40342000c9900700e181c0c1c503c1e08100b000d80e40b00e181c1c80c6062020041e42c1c068030740c1c9035003c1201ca0303500c01c0200140984890b40190700c1026030013000300341500c10998003848012258404c200f150101c040c2c009022035800c10000d68112280009154002904c03030032141c88450a42c056000c45024a2050341d19810000c10401d15440810600300209241c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 518509073 1250 518507823 518507827
    0xf0d05010609090e1509030403050f03071a0417180405041a1803030412020712200906010e0909120703030f0b01080108030f2a06040218090d0c150203040503030a0b06 73
    0xb5146515074424003000d201782c00100011401002c07040060742c01440d4000204c070f1080018001c000c0d92a04004022152a0003028090030300741807562045009075400301c5409686c1c054074a01a05580026010b1044007191104103031650b655806110301642c040e422900c0008064030540340d600000401002208041b816001c040003000000c0740d50098011031200c5040000800c224207005da00d600c5081d42c1950031000e2800e010041c144c4034104d4502000203c013075400705c001d100c0b0b107280c11260540401d0165486502c10f09010038810340c0880c0e51030039504a101032103080545c075000310005600003a0350b2840b110120440d8418500501401d0902c90729541c9440d01d050741d04c1c8248a042000b281011400c2407507028041c241404207942c801c0ca4400e1070406050700d90380c94904407802d031300c81e00301e0300c4422080f9000807078840d0160980001403daa03a00042050707448654411044420b88039648003c42500d5003803014501440c49a000345036242407400c0035800b038640c8032035050f20900c41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 518510323 1250 518509073 518509091
    0x3060f0c0f140306030f070b03070f08010f330203070606120c0312030f0c1e0c0b011214030c0703050f0f03031b09042a0e0d0f02060f0d0501060909 65
    0xb807085621106030b19000c0d56a9582c100031a04220084160a0140c03050900c0840e0324134014001c1d42c0304600c160348001c6a40c0c8244001c480e0940301303114044220b2155181170043e40d41d0303001185250a4425104031101480000e0b40d581c1c080b18890314401038101203110b03020480a1b00480300200141c00c00c080c0d80c2d00040c0c442d03a40382a041c0c0b20013000280e5003950407110b00c4c041e4011080e40d10200404101c03000f00c4503400b5180c0280110252110b900e40582c0d00c00240c09654202c40407a04111905026070070403064005030308018500391120040180d100303021a40400c001c054211500014110152542ca005031070031080d00107000795038010752450955440700000780c0e40d005003800304400504406240d800d20b40e120b540c0026400a003028206c00415102120040695400d200c80c030f400000030383c43c116640c41c24190803541c49081c029510011070075140c0b81112135030000380b1280c54043d0030394640001d035107d640700c0228141c45200421104d074115181c275004001c0c0d11030600071280707 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 518511573 1250 518510323 518510327
    0x160f080c090105010522060918021303080f0409110c15040b060d0309150903050613020312130b031503010516050901080910060b040f0504090206121f03060f0c0f 71
    0x10050265130b041207008184211480075010f9241400c508550000c514a0380f2003000806011060084401c8100a880c0c0c49d86800344520032a001511204c001c4228503045a032458070f07561040001010f040340601010800c03003110300c921020090007400d86a0f541414003030450511311083c8240220b243d440f0704010208181120141d48007074121b07840c141d8000245001c0d590006250000c4a41d4044a0301c2218066004505101601d0180045598a40d20102c1108580c0d1403240001c2d015044100742080081d010009001c1441c11440c503800a151240100ba860f074008072080160704036208000700980c1400e1041641103141042c205401070000c0f88050704511401c02210704202c14080081c80301081404044060300d000d0b20f00703011880e40e810008229402c40e008070021003d071081c00198600d40340c0300c2c4420300c0b80c1c083d0549007001c4002c1c00fa9000000010310198000365800720344014548480590030246103e01d4000580c00b1041c1c03100703411100c2c001841d005014020022800280e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 518512823 1250 518511573 518511589
    0x306040e030405150f070b010e07021b03190602040512071403150606030601090801050703020403030306080d0c031b12090e0a090507150302070c060903120203040f1511160f080c 78
    0x41d00350034265210781c03217514145548260030014180f500207900108650140c406100d0190040303500701c80c2518a10314025120400d01c0404650650000903220101d01060700c10b07006d001c0c0510300040c1007590700c1d03000c607071288c82c0c40821105907000b000051040b040180302200305090145c00038008500d4014841e901ca000140c8098890079007c80041c849030300c40e01d540da001c0c0865a00902a0342003500c00034000e074115005c1140868148500450b0508001824200e07800d001d40c1c94007800e14954400b034540c0d0260413540c103c00c0c1440d105180100f01080c03c03800b41c044695852034074007490103803107211480c0042c0180c10754074104043d40300400e00014014060300d42034641420424410703082507000f84102580180001050600002e01c0ca03003000315070044a005803500c0401c01c5001c10101d8481c401c034000d42440002c0f55105120341d020a11401c00d0070748050420750340000e02c0441032803402c02c0c00d4100ca110092800001e10180f005454940014902100140000620300c00020410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 518514073 1250 518512823 518512849
    0x1403030613051306090807050d0e0301200702120a0c0b0a030c0c0201020c06250501050403030b0306090712080903150108070603090b16051308030c010b1813060f110306040e030405 79
    0x9601c17030080300140046002141d40c102c0d440021a1a0f1100d0040f0183c52035000200750f51203940b0305074421403e009000d48140408a014200c1e074640071681d8204000c84035242d81108945c801c04c1042800910554030300c40c003a102e041350440c2c4a40348004001c06030703401400c42104100035680b101b80140d80001d61507141d0301c030031201d09890300c0c00d003a002101c11a4030f840c542e00e905105204c0e5014040e0643c801c4d8052806035405025025110702415070390a015608046c4641c40703444100f191917116200003100074425440c0c1c91415800307500007858040603031684075001c2e03c0e4400401043d001042801700801039414248880c5400ba10f820041140081c81821180b030303880b141c44411441340b421a40710851040240440e1510303003181c0c40d44c0c0c2d0010b1846400d550304e450311545851403c040c0c0c42090070144409500299182001d100c1c813140850307400c43d4425120b01040c0e245141707500600c502d68503041c0b801c84e26441c186040100307850011038054000e41013000140081d48850399003041c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 518515323 1250 518514073 518514083
    0xa0506190501051204030e06070303090512041809061107050c090f0c0708030604021e03041e08030c0a020f011a03060a0603110d2607060e070b09040b0d14030306130513 74
    0x4142e61700e007001e40d03030150050301040d4003d00c0010780608154140c0d1101c2d20040c0500d0807105070f0f0f2034000007880c10744101c2c01100c01249580310f208000b4015034110600030741c428000030400d0300c3d181401d031115400429044401ba005130740c1111041c01d1001030075900480352241102c4600b00983d02c1c980030b00c604080a0800200040000e005403580d4044a6680445000703070b460311602c85069171207a40003500c08480000e8218a50400d0040504a070014280c02030341d03082c5107480d130080c803081e1940300d5945181540140900c07884280b02c28421704d080040341103404502503240b001058207146004100034003013880e00c0003c1c0049401d165411400c20010b594154221003e8209104940700d0182d8508080c0e0800b8228102900f094003e415124450382e014060715054000d0340792100c0b820b000e801e4810f4002d000d800c032149429040b0100c0d0000162038090600840d1329115030080b102403c88a10b5031001081c0042c604020320b11900c00d00c64080100240e0508603070094401ca940300000e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 518516573 1250 518515323 518515357
    0x2091b030c0a1b0501020a0801080a02030d050723011a031903230c01020a1b02032104080a080405120d0206040f2102060603100c022a090a050619050105 67
    0x22107030107410b1000da2500c4180003d58030b40e04030310b4558040d6000c9000d11000030482000042c0e03494000490300703c07480c2e0040203003d0034041e4000880707541d0000c036401c1d0b0b8203404801505503245c00312901404400050400460b000e080c0608002000f1202c88249000360301006122041840032a441c0d484190706180c40d40440c1481006405060441480c4000c000000103008000050541c02030840b16200c3c2c030340a6a905048400c400210002e0b140603406400401043c0303a41e4051100704094402c01200352800c142e110180c15182a900d18000c135010a00050203201e54904500e00b0a42c100c0c800b00140340106805000a40ba0000034000401c1c41800c50300f4181080032013480c1c40a00380c08850468483c4090810080d81e60a060303410368040e0040c21005a1a0420340c010221b01d05001e800910302110705020001c10b080042c41b0740707408080d203200c2c9641036a13154148240607000c03040c3c0103d6a400c040080042004000140c2c00c060342801c2000c02090b60010150350119064081200d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 518517823 1250 518516573 518516587
    0x6010f081512190b010e0105090403030507140d090b010504110a0e040b12010b010f0305010b302d240406030c080703060608030301061e0302070b070c02091b030c 71
    0x9091822800ca010982e01401c0510030f140014a040422518081c85100030542d0741c0341188001c64100780603081d04103130310100280109010b90031042e0410024540130708406400f689421746500700f82084001c007600e501200f41409881c00c00c0b5400b42038200c6041014001c54640044c0510030101c101e02800801c41420703040342c2d115804079041107000761001c00107510204e4000e00070a1250190350104965a044030540c038424402c0606844490320003502c0c3c0070300c440b07103070864003c2c05c21a5000d0f48210030301c1c2c201004003c254503000c0e04419058148103500a000051000281017104180014002c200300c41003102c1d40c010403c401a00c1c2000300000805c2010501500c5e40741c0010b002240c034520006401c6070700150290803240114010030000e81c03550200c0d9143e100c28031400b000118445040741680b01440100c080040d01820018900328547c3d80c1e90030011411904a00403d411480c82c4003541004040ca951001c0c542503907035070858090100081600000e40000c0d240040458a2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 518519073 1250 518517823 518517829
    0x1d0105040203130311120f0703030f0902030c1908031b060705090f010305040201050706060e01060212040e01060806011206090c0f03020712080c040f03080a0e0a0b0301030312180f050606010f0815 86
    0x140d1038a141d40ca86e081e40c8481400c0d009803680c1c405501100024a05403d14583c2070152081074049503004015001d840141e40030480800c0200300c40c89400c1092850019545130704100500304545105501e60fa4031182038041810680000d000d04103000701000224080c1d0355902c80c21015030400d007000640c9844034001222a17015031500241120f180610101d00803800460441c102c4015a007150042d468041d803025450003144034000315000c2d0280103000030350040400c10341c0084c061402400d030910703041c0144181c8205030b003e511001c0da01d0000b104c0103170b4440c288201d040d4003410154606403640e511108032200d444107007001c014101d402705601400200844d8010500f00c001e40340307015187d0400007107640c81342e4480d1020908410440d0050b0414500480840f0b43d42d45409007036a103140c81c156803281100710740c034903c181c4c1c1c6c914500890f1001c000d2000818054403c12009600501d4824038144d4090021418407651000c04140c00c0c0d44000c850740e02207841c811560070540f150002c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 518520323 1250 518519073 518519083
    0x24030603080c100c03020913050a0908070f15050c09130204080f1b10080f0a090f0803070324090207060b03120d06140117040f0c1d0105040203130311 66
    0x5012001c0040c440002040002c0e102101d0b580481042003140300c0088241c1c224441c503030480c3c1d08410031065030051440f6543c001070f8800c083c0c0d8004207203110199101d0810b84d0210f00100c4039012540c1c450b5080c0800d0000341c0f2680008a2400c1195050400400e241da0040104191040d01c10390b540341340d041e100740c050714014464401280d0300305002d800010380300c554040c9440e000708200b03018a003ca00d0100e1100c400282c4985410071141c88008070f02803c01c030018032402141b1786860341580020100a111520503020703803581e680b00d040064005003503440c800c20140c1f54444881c0b001e1011881402d01400312030710740c0070042e80c0d400185800070240c0f07504068160705000342802c0e1000700030381000404094000c1e0608001d07558071951208420416000c52900254814012922109072000419041802030301012540740e00c6a4444006410079004600c4107400354810180b0403c10058450150000701d80550840c0307020002050310203502c0301c1c05800c100c801b00008800b03040501c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 518521573 1250 518520323 518520329
    0x10b180411090a0c02010b03010b060405270109051609210501110307020601150504080d0804110a080313060c020f1921200d26070615050604240306 65
    0x110703482c0d10385851420304000b4100250a60059420117040e001140b5042c0304250903880c1c000e040c5403c3c241004280840310f83c01044003181c2a4043c5c1541e156155042c10081c02005154004941c0345460406910381c8030b00180345000348a01c071407050000e440110b941c501c500d0715080b051141000e0b641405800b4080062080848003000014841e81503800b040e4141600c1902c080c0c00324100555034212524401c900c24540e03160088018040e01c64462069190094082e04134a0b5103203010303400060010016510400d485e83c030005484004409a030400e40013040141440c40480805d9000700700105c15132080c1c54420200c8001c1c400806c040c00c031580014001c0b080c480c00b20781c6000315041c2050589404140c81030184d9020302c04540c00c405025007040030001d02014002d408a42da640c0204591055062100391078007070f1040607681c00300103011810f00800c4085102201840011107100c15034002a000d0402000103000800c11150300920302c80170680303209441e0f501413508034000d200e103070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 518522823 1250 518521573 518521579
    0x60f1b0f031d0604021002030a020d050d0e0318010e06130b07061d0a020301060b03060112090201030209040c0c0b060d12081312030e100513020f0f041b0e0102010b180411 75
    0x90441c4030402d00000d5007611880c42500c1503083c0740d221401c140d9030790140f0705801e00143d010340100c03001284200c02424412101200c0030924203002d207a000e0031038000403130002c0b0304818080000300c40d6a00c50403404c240b510a0310300c5403900101d0b400c2048100001c1c003440400710000079042040111990040100c54003490101c40301e1080c0c000d03515240c04e1944000d0b48a03609200d00428400c080760101d81c0100c20503110250401061504038021b0304c1280c1d000c4e03050560a00a81e10607407a03501540c0100034095075042501001844d060742070410107001c450240b45080c4000c1d00049021894406403a014200003c559071402000311103e258210000e00055500000081064154100280c90310b1a942503650540a1020001c05c448045440210320344a6011641c051b04001c0288001c0150252000c0c081814640205061b240c12034005040c488034440c2c1c82210310390100c907246940303070240f0082c00000e111500003420201e40d50301d0303600340b9042d001c0440c1c104400326640f43c071568170103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 518524073 1250 518522823 518522861
    0x20f180f030d0c1b05100807031d07030203011b230d020d050a29040c050903070f030302070e060607060b0d020d0c050406050303030f070f05040801060b07060f1b0f03 73
    0x1c20300400282c044502104c0c11040c003444034a8403503010900d40c054603406000b0031071520818108aa14000282c2392009240c3d6404a1380100000d0301100f84c641c0851a006151103071071481030600f107a40e0491041400f545082112058a40c007103159007800702c02240722205030510103880003c81c803d4a103540c09441c0b00141000e114031031500900e1041d1415a030800110903162403200c0b0388800400700804000b1043c100e03d007107107000d40c01083e0780c01d1180f80c030a052401c4000424901701030740e0400160040c09007010000c042c0e0410051010382141c001403115401c04101203816805a030300010030403601c40f0a801e0aa40310201d1041d04c01e0b80003440081d50405604140140011701d01030240101d05110b80840c4ac0d060000449019070101100400e060350340000c201c510308403500e002d90420408000004001c0402d001d600b01500b1001c00300d6541e1a010b140910840380354002a00c0868206007801c0e02c1d096005040c5404a00242480ca0000100c1c00c8201c000705541070039420320440c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 518525179 1106 518524073 518524093
    0x507110a050606040e01061208030405070f06210f02030708190902060d02090109030b04062f0d0c0e040e070f060c0210180b1206040b04020f180f03 65
    0x405c40002500544508102414510704002517034403080100030301091240c02e00400c1d0081c0342c94200e84030303c0f9242000140040d900e0300b504100e5894805925400100c2580104941c1b10b2003d500310341d24689401c3c0904450f10540e070145c01c00072801322110780c0e804a489111905500281403c1c00c040b20419103401030761003001d00504012043c4800000251511840340c0140c1c410705004c05e14030107117980304000d03d400081c01e2269241c90740504089040c03080449600600c0d803200400c140148902c06c1d90120181514290050700d00403d0b42c801d42004a003a109a40c01048806042e40c0d0b2034034100c4d07101c1e226210213540210441c0783c0440c0c0d280507201540003800501c80e00b513501c0755038040e01080e940000803400c1c00000800e04221031131800d40b142c02042101110114100402c0d41c084903240d001e50130154507543d94054051940f40c0d100413000c0d10703440c002400c03278010b188 = true := by decide +kernel

theorem cover : BRFrame.Cov 518345323 518525179 := by
  have h0 := BRFrame.cov_init 518345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 518345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 518345323 ≤ n) (h2 : n < 518525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
