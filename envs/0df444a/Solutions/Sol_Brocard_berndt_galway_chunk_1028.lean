-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:54:27.177673+00:00
-- url     : https://prove2.me/submissions/5365c40b-82a2-4edc-b032-3d5a8c9a3e56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 184712230 ≤ n < 184892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 184713480 1250 184712230 184712237
    0x1207090f1820060c011e1a010c0305070305120109050406060f061704020301020d0612200105040302010305090c04020c0708010501121e052a01020606010806131104050a08070501 78
    0x100c664091101c80a198048040d1641d60111076039580b42203050358042c1d2503240901824100100600301c1421074080c52a900c8250102660200e4100340034894601a030328419a00108003110400003000c40c598180010140301c400182d070420300d40100240e03040c100001440702980e40e122040080901030944d0112806414480c003c24203a00a0401c001135a880359075000503415843c400340500765000c0c105903013555007006820003039032039030040b10040c080042c0340d0180303460b0900c2c1c0800180c45d00d40d42c902c0900b4501d170088055a90010885048940910b0f011641d51107a1500c81d08080031070175001e501034400075000400c2d06011841e0700488101340000c0006a84e81c00742c5184000b481880186a1603450220400c005a6115245080c1d03003d4412501110040c0706003d1410b950900c1204070b2080c510b403024030941c0c2c1044107a40c80582031a282c1c4850801c040411082505c101210a00685034460f0000c0074041c2000e4600034a4001c02d80c800c90b555981480e51900c44c1c030700559000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 184714730 1250 184713480 184713491
    0x30c0d0507110c010201140604090f0804060512010e0405030d0509030c070e060a0e0108030a180312050301090f0b0904030318051e0c0a0312030f3206010f0504141207090f 75
    0x640c0188a11170703182030007035080b41f51540c0318000c000052409000885251880f40c6142c0c010620210143c030150072152a281d81c0c49940007410250030005900101600c0ca0780000c01c80000c20200c02c2d02d0340c140128101250075240c0080c2181980242c0c01e010800d4440e4110004100008201c1c05000321002d8480350617503602c40340032020000b001d0043d035401c0d91080042d070010900c02c010100310484444e41f50010b6031703141e644000742c44100240c400b0000720040014008102d0701c0c454451100b800310307020031517440f108000c5491908010005010f05603505003101010600d40c0c114030300d640e8070100f0355400f0a001055217900a0355807080c51090b03c0351940303281c101d0030024411005d49800038000e0784000540c240c200c001d040f6011142060540b40e5403000708000092070241244413002c3c4514540d1415840121078910008040030304000c44400b001d04150341003070441d025a0035040000801b03d50030404508a01103001a4042c54816030b900061100c00a0b4001107050600c40c505021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 184715980 1250 184714730 184714753
    0x506010e040c021b030703120503040201140c1b1f031e0b0310110412030c02030d0503010f05190b03090313060f0503070806040906061d0a150506030c0d050711 70
    0x11981824100b8025901c260244285140c1403062500c1000300141194402622070303540c80e1109200da50304102240c0084280030440da00041c290001d03051028407241010301c4144495606e0304081201c00801040d074441121584a2007035104540c0105418140418000032000300204106444e131142c48072402070004001e03100c0e01580941805c001c0042c00d494001100c004000d25600156021f12203040100013056299021464041c41c06a12030b4040c414240c0181810a80c0c141061000c0000410062000007110001c410503110103840141c000c1030b00003013407074100b06607820140884801000b088070a10000005250b0b48951000c4034507055138035071055903d0301035101c001010807028800540c88074403800f21a9440782d00100040f0b0558400e88408007183c2c06900600130400400c07030000c0c26802d1441003070790001003028040103242003101e8644289001401002d11132680000407481403003c3c85d00b5038100d1065104100002c0c10104006001d04021860808007030042c07501c07004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 184717230 1250 184715980 184715989
    0x60e0c040f05071e0302040f03120206090c060316090b030a020318010b0102190201032309191a27060103060f050f1501021603110405060a080c0405130f060506010e 72
    0x90090f401e079203a005004035400305000c05210351411034001c055007880000f605614840c62140191b0080c0c2d1004240000e0400003400d02400038148901680000e482d04101d071124003c0320303071040400144884034080c0d480f084132110703219408000806e10200034402a64420b070300460280740c810030700c2040107101c00000d901340c4050302e401c240540c110f1186a540011a0303450101d01520500d000030f01c1c28143c80c10500481c032401e000710090f184540030020b03050400c02500708060480c44c80034515000710741c4d0750382d6203d03030000300390010681e0034000c200c1402c0f008a8000701d01c051030900c803070ba10101e85800c9603200c000340f000b940c01508000f418900f540c00c40c030030540584035014180d0020381c0c90784403403050031381e1602c05541184140078409003402c040d0100400a144550380102ca80b00d004002c1009491000c0c151611400121100704035003080080d0017004140140c60100e690754803403c082043c0d000c40c0384040c1a0108103410b180410000b50700c00c0d481520240c81d0308a0f460400028007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 184718480 1250 184717230 184717241
    0x9050315130215071101180b04090213080706020307030201060501090b1b0f12040306050702120d0e0304050a12030206010b0309070501110a1e1218061b060e0c040f 72
    0x20203005405401003640414080c41d4a6006400030b0300c4140707100c0250345464181d500804064801d4900c04403040c10640c1c0c890758620f0300000403540c85206900f043c903803020340d00c00e5100c2c641e40294002030389204408130b20f003450028900780c4140c1d95203c1e80c400c40a91298020388044005500c0c102011613035600a880000a5401c3c0d030801c9401c000440c0d11644a001d0a4102c5031004e10078440b616007030040400c4210f0a074485c5a0a43d80c485145103440d03000e07102c0c090021019900801a418402010304041d1b40a0b101000d4010540f001207141070f0b402c620981d0005508000640d1001c00c1c00d202500d246c13946a4820340c00c880b000e03a41c981c0070b00c00c50301048e2402005c5402010003005658454104000c40c900c552064610b09246940c0d403042c011070000003050141000c0750444140708200d804141e07134003860f081111030807003c0304804281c5c501500810301440240260b80d114845800388680b69075070301c8102007154454400c200e80e03680311400c00071813055080c0f18070306155900c1d0340a00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 184719730 1250 184718480 184718503
    0xb070303050a020412031d04060f080c030f030901050d0b150a08100503030901050d02120a05060109170312090c0a03110f0604030804030b1e0a020406120e121b030d0b01090503 77
    0x1040e0a240c01b42d03070031188518503000b40e0300f00080c0849090b101d0f0390303036108000080c806d581107290080c3c60412014106482c03da4082e129400c604800d200030000032085801c1d08400746000b940c1c44860f00c46400051100085181d04582007141d01782184850300d0081c03030b00c203050f900d03010903558501e500003501c0c100ca030282e5601604248840c82084d401100540a42041e040c00541044240d458801030f0400c00c40d030000d800c40d1100c09000d240d507004240c1c3d20103490344804003034103840039130b041698a21610024914a10017900007031003005043c092207076284001000c03105081ea40e070916000e20003c403192503105d903681540c4002d59181050031102201d510440890805283d0707100d000d0001e1000b00800700140603105408104039002000a10a07502d10100507102d42c00e001005100c2c064142d40b001e800c2e482d02c803000007050400200703122601544142c00f5600d000850140c4640c81c0f030780e200ba009030311001c228500001c000c2d8002d001e000d138080c3d80d049940c6a64000301540c400360240d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 184720980 1250 184719730 184719749
    0x31e1905150609130201030e010608010213050a0e07050f0a1b03080103020103060b130e060415030f03090e01081504031e0314090d080c16080301120201080109020918060f0301060b070303050a0204 86
    0xc0704c00154040d804c46803031045560000200159240259400d80e8001c00941c030340313542408400c1c0807034900b401c0040b025045088401c5a107240c00c01000e00386215032150b400c10b06d400850b420203001c0c464441966401804422920b40390424034014112517401c1c00101c1c0440c1c14404080740d401c4041c0c042d1400301c8414071018008600d0a02500c0001d03801400e299002512525444042000f1100d40170045129100f000300410031400e0007080070341d150b003015048010b10b00c01008071500000384124070040d02554501c2c1c1c3c2c4c0f100d18082d240c2903c405886500040355884540329a50142d00409800c090105a00c031995502400e8603113076981034032210701203244031000c80c0c0601c0e9100050880000305080e9580c83d01019144d6186a81090344510103840345c1d06940340440d6171150403140140038925095080003d1400024004107400c8070b46294405c006000a00c19600c144c0c4080407020058000c21665448114580071540315510036401320341084003049c0348140920032241142c031b400a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 184722230 1250 184720980 184721011
    0x9040c050c0c06280809010c020304030c0902210114010207080a030206070c0c030b15040c1403060607020112050c040e070203040302030a2907031a0f031e1905150609 73
    0x401015030000c0c0340504902c10354858208034811300f10804151021113448201e010719190109609640300181c0d0300045410a00c01000011b60203403900c070540e0426800561602c8202d500141c2d4030302c007403130503615128401c000010582604400315521200a0742510030301e42d10390103150b6503041c5100340100182d11400008402030320516034100c041d8850007528800329640d032114a02c0f0030b01030300c0720020304c040b16249520902c0c152152507040c006c10304045c0282a010481d80300c150000500080c020403000880300110fa01c81d400c268468180105d0401ca5410120450540d54016000d03204c40108107001150360140008196130869500400030701ca0541030750340310314441c10340c00a1140498881922280700c2d000e5201c402d4815086941d0009550351750300756480450710003025403800b9a110400441d05c948001c5411031a1020718140c80d03210100e07041c0260b00d401505280120102801462081004404100804441610006280700e5124a0100280c0c568165070101c400c01900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 184723480 1250 184722230 184722253
    0x3020a0914090f06060c0a030e0a06080702060f06060c100203011a07150f020d090308060306010510050301090506060f0706020301031a0106020316151802180105011b1506030809040c050c 82
    0xc80f0010740c0880d0107800c25003403004014126190a8942000300d01099200d00c401e081f504010b00c1c0200140002e01d09528030f8101164065204e075005416076018600c20f0300010525101d410031120a8160081120702044180743d030311000790000c0c040c080310b60f00300001e4a154070a0070025902c5440c3c111070398001a0606183c20701c01440019020002c1d15006d001131000d400c403030b11508070f84034040d0721540710701d00e0404201400e000c0305800c214411044449442d01b95544081078034103442c21100000340c0c83d205d040016080780076010041d841200009800c0e8100000794010354100ea10406030b01c1001c00200e0004c0728a100c090007002c1c01a442480303400d4800c91041740b0750f500d160003661002121030310088080c056844402c06c2c0301d233510a6408003011401c0914030b01e9071820818180321240c0d418000003c001460407441e0b490416070306401d02082c48004640d00720020f007461010042240e0340e1416440d55004501c02e90702c103615016103411a81d0040040300c40c0800180d010340180820ba = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 184724730 1250 184723480 184723501
    0x606050409050415050f0703050703020310030308040c091d06010f0e0c07020409050f0c01270b07061118030c09010b0406180e15031c08070c05011401030303020a091409 74
    0x140300b507504d41400d500b00e68001400e0320071140134048000740c40c00103140480015040d200003a01d804201481001001120305400c4054800e5a13498030382400c013621903007428040b80040e50804074500d85031030b502d81c641d0500d0404c4d5440c80001d01c020307a20181e981e246800c54042c80380c41840031031890400010803c06d40340c80241036603403008000041c0d0420b503854140c85c00140f44c40c0014164001c1040400540c0c000440030b113110304180c4040240241c060500254010702c0c8a000800100880d03088200b0103182c10004065864a14642e15a0840f103185401040c1a445490090107031540003031003424500ca105040c1c4058101d01031901745000e03c200c42c0d819150074200042d5500503004038820080a81d140d0180c5c101c4041030031366404403800c0500300a40c000007400d41e1150154140c803016004060300b40c2c03004035400c010f0304051180c05c1082c05403020b040c0718070b910403091b00003004040e015405044200d090b6030f504c540d003584608000000707030541c811103540080c00d00001201e0348507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 184725980 1250 184724730 184724741
    0xa0612020c0d050405012307020d0f12172a160c03060204050f1e04050705090d0309061101020405011d1903080415090b03060d260309100606050409 65
    0x800400052030100e100700e219007060b902c401c003200001e000140400c40c42da4000f05000d000e40b501000035255507400d0b200c0c0d440034031504c0b100a01074810300c3c100c3c0080c00300d00018031524581080000000c81d00001c1c00919a080d03040504000c42011804034030808074011080e02e1040c2821110602c1c542d40c40b680a0458214983c5d54001d44007140c420700003c2d081d8402c04000b136100f06000342e2528280070070444c06480c1d0f0540140201c484078041d4411210707450329071345107000c20340b03000035140ca822804942c07501c144c00003280c0265213032029404150348041028203c81e01c035070318410400900c540d11400d0748664440c0e40d0015941502841403002c01e2800c401d002c072001044401e00e01d43d00301801121020310741c025200060081400c010a4080f001e591055040c00e01c0c191042030b052500700c03030b40c500000d000d03240690f269419060401c80381210007000d4428542040d042401c3c1c00380ca4500d00d0f80203c41881302d5000380d4010b40c054032524042c210654007a40c8802c8d0170b050600d45410300825 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 184727230 1250 184725980 184726007
    0x6050307080f0c0f0f0405040e010c09060c030903020a080303060301050a15170307121e0504030b01030803090a080301090207020406090606051902031309060e1e06120c120604020306010605090a06 86
    0x8004200c4000090218001020a1414240d01ca80c80d1b0f4500006c01048a01d10350007480141d050404201d441a84070310041c0603505142406291280d17203050888595505410003500043c01c258003080c16500080a1803140c24220000d0103141c1e68410341c1000d42e548030034143c540000340f07802031101444110000d150304d80984104c0e8102401926030425100700c031014500420141001030060405103060b06064101c2420024689480c41d41e03055070400c1c1c1444007921403040840841d61030071080c040514025080644107480f56100e6001c03000941c00000d0803842203240500c001046010790040c44220b81c0030307884e55801d106011100002024003130f020300086000c20040c0191410051901c20081d00002e000051000e0401c0650041c000f0040e0044900300c40f01141078183e103040d003090660041081c1c82428034821803119042c60103500c4400160303c0100144440d040607030002d42c040c07049008600f1201d2590f6640d005544910580c03507025080b031103845042c80302c41e0041c0101903007003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 184728480 1250 184727230 184727251
    0x50129030105010e18070c03022a15190203210615090307030f0809010801090b0a0603110405130b030c090c03040f1707030903050706020f0703060c1b050f060106050307080f 76
    0x1071030041710078069400c2150004081000084202c0a142d8100100101c280c0c0301030403946c0c03ca1044080b04002042c58941c18807900040020390010320b034120a8030700684040d044003542e40c5141030060f40b80d4010540d2509c00c2c8400c0143c014401d03d852992900a103405410300760b400082b4000c070201a80b001c040642c15100c4e50a000000801c840010000756000380c1005484d0750060b0001402158117034461164a41486501d00182e5242c07100e046c1201c0c800d003000a0450b505144092090203594082648003c8400070403180504035004086098800c50a680320b014642c8204542204266a01d04910600340300180c001041880d4811603d405005040301d0602c031340c0c2040999030301c000341c21800500280010410030104000120141c000350025002801e170a1014507583c3c0314030310002c1e02d15038075510080c034050b0140303441c0d0612046401d11813806090a003803076aa5480c2d450070704a258411a0300000e04688110b050fa80a9110f60347c513080039407941407d402e0b0051024020f140c19 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 184729730 1250 184728480 184728499
    0x6070b0c04030203100203150108060127050a0602030a02120306040b060703110f0c0d080d11040305031b060601092303060907050f03030406050a110a15050129030105010e 75
    0x8a140050900d12408880d04a1580c4508610505091075681590300c00c500b4011f00038498100001506405061000c0c64000d4190b030794403004035980406050903070020809050007941d244040e0000c007003500c1003900c0f400c40d0641d880500303d079640700e107600000c01a04800c455962220319035009542060b401400410a6010780001a403958041c4004030b002c80d028400b030410036401449120202160000035011940408010900c0104034450080130b054002480003116240c075400a00010b07691341c0c49507195078032864190307034940c8400024074a000d01046c8001c0503a2000583d284a013506039035100d80c451a0001c40646018440140320f07000074a01c00202035a101004a180705064150090001525040c2031150108812041d18003c0e0002c0009200280e0480b0448040e070b100f03072900b8075089039089a01c0b070808120307810041051501e460111000803964000506942d00c040b00b20f800d802c4412540341d0841c80d100041508031005100402003503004071a203101021000c1c0c060050b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 184730980 1250 184729730 184729733
    0x702030c15071107030201080a02070615080309031c12021b011e060609030503070f0f0507090204152f0a08070c0305010513110405070c05100c1b0218060607 69
    0x2003024001018000602880400c80302da54010070f808200c01441c80030344503003402c40d00000d11000d801002051030b01d40004400040040f0780d41b001c400c24142c8240410510345500d06151241d00000b9858800e01c110684003503d11031400d40403002d10b207180c8a0a0060316002451070181d00220b0044405201c13041c21110640c1080c0030340c402030b0040d02200801010041110022141c80d500100104a4808002c4c0b0014900004440c030454018101d80c9490303541d890b03c0090168080b1008102c0d01800c100054080800d0b0050700642e0481c45031141c00c480d048000b2a03203010013000c001d1220513034016007041d420f500400d038a2070205e40000d1300c211a64a89400c803050380801c504850068001c401002442428170580c0c1c0c004069803240b610940c1940c60f0722280426172000d80f4440c40e980c1002c941e681e4002d1590740004d661200507070782d0710b455141220b00241610855100801e40c4810b40000c4803025050207080150300800011817602c60440000c50b20100800280e00b18404200c40ea0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 184732230 1250 184730980 184730983
    0x61306080f1006090902090406110f0f070b01120308070c323a05040e0702010c03110c0a06020327280b0601030b010c08030112111905090702030c 64
    0x100344401c10006003014040050080101c84040e402a40c1961070403c20360b00594901c2c0c1c40720f80240d0003210106441c0040c20654043d4803038400d03031109031000010084184a5140c01a01c40d20b405951000b40e6aaa107030814269a410440c000b00015105d0f400180441c1c001c8a078904451701038101e050601074018402003544810074030b8043c142a0403103803a00603400403c00040702c0d040c894858850790350304140400c045201803c111070315000440706c5002c00c0d031240d0700b910000c1c84da0300409490303801c00d40c4029008048420006000034185481405404941011548070b40c60ba44020007100000e6110003000b500040c1c00368903440c80070200345504a4543c102c4018403030411001c6d10001c0411408a01c00d942d91900000c140c000c007503409004110030485056002a083c200850201c00600c0122040032085000400340710000c000803c6880c541d03144040d1051140c080c071801c8070403002c01c20800596040f85001c0ba030444240a00850800c101440d80051080c012282080400076449 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 184733480 1250 184732230 184732243
    0x50a060c02120703062409200a021009061a010e010e12010b03100c02060907050303071101020a020d0506060a050402030606030604090f080309210703170709120803010305010b0603070806130608 85
    0x1406e5a001a000c40816000540c2140300180b03030303903041085900712040c0900840400210005118500401d00a081074024840f010044c0003450082201103c50303d40000100f45000c00700d0300108120311607406c154000c4e5661200c0000c161243e644882e99a4100a4402c440202080705952220308800e22920108500f03200340c0490310011401d880b464900910f0a01d0042c4401c003180c2c01040100010b0b00c000c0704036024030f41c100e8405181d04608a0050745005501c1c80025004002e192001d01400000f00b00a03010303d0003200c2a40685642e0710800050b80001d80c1c840d54030040c01c0020a0031454143c5c00414110710800c2c4a6202c00d1140d02c4481080d0411190800a13801c80303144101d469455003010b4100d180907182003030800c0c4164078010700c0c2c41d00300441c424070f054200b00410300407401440200002e0100c143d0304001480d20b0700c0c203001150403c2c80210340c0c5600340500e01071940b42c0340090300d1098000e5590b07080c15580d1001008122800c1901c04040c01e0364800c00854054400d0005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 184734730 1250 184733480 184733501
    0x312070f03380616110306060a0308040b0708041215180209010e042102030d050f0712110906070317010902040e04060c050d062303120d11040b03010f030309050a060c0212070306 78
    0x21400c90281305c0003810308000c0300800c69446000002014030014100c007080d141a901d0240e00d09407a000c00d440d12035224440c03504468100740d07016031103200b04464820400182d008091041c030019620072251065a00b11400003540060300700c0c0140801900c080d40640e005000b6100c0300d030040c44010b20741d4445d11650280c200140c2000070080d43e051251300800d178001e82100200020743c904000000c001d1290720840c091030540301c0c01c03501d0b0081c0e10300081d1000104000c040c1075403007a1502d0050001406095051002d54050000140110440c42903c040303507580140603000d96141c0c2d4070140181004e81c4120b0a20406200132507809015108000142c00040c0c1640319843e0f010301c1d840c181881140c01d280c802e80c055408010380710014819500700035281c00300401d501790945450202c0340205d0f00099602d18010000003101840c0960007411030b4065142d800045d6111001d12a03a08268010310740800c425552001c010706124900300b030110b000c10103413044c468480c2d0f01c035025500c00310710 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 184735980 1250 184734730 184734743
    0x20403080a090306060b0301061b02010e030709140105060903070b07061e0e06180304140a15030501170c1c06090f050c040f02090a06050a020312070f03380616 70
    0x7001d0003001101d114080282c900c2050187c110b40c90540014030b405294803aa098090318404000110f90003038000c180345a0b001000da4600302c1d01c441e60100100074001907500a41845000041e543c24500d0442d03401280c040d02400d001400d000c1d202c1c001d070780944c00803240070f0341d6a0a0f12400740320181481c004807806100208101d0120354400e0300c0c120025214001c03a00c05284000c4010000004440455104461803201007420800042145025a000f4900d10303d4424501201c00e81c9036021606079a400d1460a0424903100403017561102e8003603250750000c0c001c44444030400c12034042042c18030302c1880d000c10b04500a41c1c511920481240e000c607090380c004207440c18145414007592000724454902181030240a07000a0901d8450b0304c520310030700000140000100c2d1003801140e0f032005080150803514105400018502c0300c460b41c40800091803c08003441000c848101141c00d201d01c40b001342d0622010111003024680390600440d0f201c00c040040e4000d4807071300d1840750300301350040c0c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 184737230 1250 184735980 184735997
    0x108010b010e0102030909041b090203270a050a080306060d1404020f0f1509010e030f1c03090b06011110141f0308030f15121f02031504020c01020403080a 68
    0x40000d03101d0b81e08040d500741990003d20034014240c42d242003450b070290300190070305420910144500c2c0700d504980c1004c00424000070400009210300d00096031380b8192030740380f00205000ca45040391150b41e4004001c210780c22054480e40420350190245800120041400745843c4000c40c8450480d182005120707012a8600200800d510700b07441040304440d01074039112225090000080e000041640c0c0104070b860020900c58083e9103d92180f01d03511001a080382d82195125210590320300315102c4110f00d000c01400401c079998483d016000f08a40e0052810030207840c1c8000656039684031006140552042820800700b11800c0e008216001c80400c010501301d0402d48101344c0c1c0403078000e03403540e01a070f01140c0800000e0f4124040325440301c4170854580e0303581c81e0f8401900342d00c001502607541c401480300d80f00c003401c600400c03080441c01444031a07208040980c580303402a404201c88204c401032f40d2007050380e4107080c40e8000b080c41c6000b0100045c40c0c03646a5589803100e4100c0b615440004a180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 184738480 1250 184737230 184737251
    0x1009240c02070905060303040612180803180c0a2d0f05010e0d0210050a120f0c02010e1b10020102070c0b041502010501030f23070303030209030c09101e0e010801 71
    0x18800741c0040c02c0110f00034001d9140039030100e90303a0300c07480c821281003200d21030002c406401c199002c0305040d6640401070080c01038508080b030103508161552501169244012a400d0380b00182c448003201d4058002c000040c501812120490501e01c01024445541c00c00d5441d440200b201c01c6c0054040c400d0440081d50922000508000d020441180101e0104020101507038400c100c0c040035641c0752030001d0381c4100548040f5642c40203010f9108441c0e0030104e18483d000300c2c03038000e60900c840c5036000700802000f41000c0c58ae9582902442c00d000300d24007519032920308008450811800880c000545450459612401340007079039400b1442c2000c000c2000c0c000001284042107040b60780c3d10081c0060b50660300c5030001d8512204c03000300071000b000c0e82d0407031034945028400555491a0240d403c10b0b566410040c02035400010708900c01d001c1c8007e202000c2c50900301241c041c00c82c50312054401802c00a10a10010f140340030303451400004400010844000d2881078080c01541c4000300d541d14a2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 184739730 1250 184738480 184738483
    0x30203070212040e0109020c03130f030204050a18060b0f0a090b010f0f09050118170604063204030905121c03050609190609020403030e0a0b04081009240c02 69
    0x40c002e42e541000c401c00c02005407002001915040d141d04074401030383c0c0c0c54240300c11440d6203c3d01d003024808446051002a01d250035a0150044034001e031740130300003551414104401c40d0301c2641c240007400712882c84500800e02c1396200c0400d041c0040d03c60034040c00c103d00080d455a6180c3e009002c0c1503200c030f0720801d0550f403014407400d59210b98100498001510980941903800d140646030402990041540c045403068103140c0c0141500f0501c403038003a1030300d401261510400c40e0240c44003424000f0414281d14841c03205c2000d5000307006a8000340314420419600e1640c050b2050b41080303120b001c04584c50781d440c200101d82895000041c421409101c0300114100d41c1c100e00c81007410f19000402400362a1440c61a51101340511501ca0703800d28a00424010800350b0001c28205201103000300030107410440d44070780d0440c11100036214a50b00ca400b040148514040c42d181d5402a641c544405841c1c2c7e0040d9a282e40b09244520f6203003850f499114841107003040e89020716403500800300c40e0940 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 184740980 1250 184739730 184739743
    0x40e010504110d08040e04080d0504060c030c020d3c050c15011412010f050702071a04050105070b0c070819030e07060f1d13020702011101020901120b1309030302030702 74
    0x800c1d1041e51808005481300e2605019500c41c0040d00c080c49030004081224210031100c2e506241c4404100301e04003402d0000041c410281e51002282c0ba019202110500004040d08424003a40c0c1e6510b400e8414040120745101a048508031900340c000d036003500d440d02c1c4082100c605550750743d03240c07078244401c407041c80e011807030302240001c00e400340040c412003001a400440c00f2000713540440250081ca9402c40c0105601011901124036240030f03c0f003815408901c000456514600c051429845c9824010961240c1d20800d4081101084884001200342d0720713665003c5800c41409040001c00e440b82d100e1075210810080e51003203c0d0000c0d044841e0140700710500c2a81000c01098010b00b00344014000621910090b418001c2c0d00c0d40e80d440e290340140050822510251030030300400072540a06004c1c1d00850003c0780071a030144800112000c2c140b00369a1000816510014150b0702c1c02212030081c203684c10016041062004000101c040500811160750b201c0e0b603005a40b03107424071000342001c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 184742230 1250 184740980 184741013
    0xa02010917160308131221050c0a030504150507050d0501140d061e0e0606010206070503240411070f0c080111071401061502060a0c03181101050405040e010504 70
    0x41c001e106060411030b4100c02c441c8160380c507040007160340c4c03508200100703241c1403c10010819940c40c0d119501d0694440c40d142c90b0100303814160415504a40080b00c25501c086032500c00581050012115491080d001a50082d006900e054070180646040000f611804c648401c0032800c0026810790800c42c5120b0203006000c00020300902c01403c0b000a1b251100702500039016a48070360b224980500c0801d2807415240c40c00004202ca9003014903041c0d200c20b070450304a400750103240000307030b00c00f400b80040341d00c20309490b901a136042d603004c45030f500b9003181d0002154100d5a940d14880400c8950f5005000507401008405690100d902e048425403c40b50415070b1140d0400414030318114500e01078510742c0b644142400c80d4000c100c0a000c0c014501980540d01101411b40030050064022680764012403890906204640400c04141c09880f860740b9014510342c40103810b040420740070b80c2c44401e20740701450498a0280c0e140f0015050f40c5104410740e043e6551403050208002500c011150302e107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 184743480 1250 184742230 184742273
    0x10b0a140c0303061009050a08011b03022506090c0b072001050d23010e070306050102060105062a0319170c091e030604030903050610050a060e030307020301020a020109 74
    0x400d01d01c02464503400080d041c24041c0006203403a002840c022004c1c2e5015210141000300000e07907840000d0f01034441409c1d01d10480c03813a0b81e0f061409500c24000c840d4845182082e1444c400315940b1a0030a040d0405000c2c0c8802d0b41d214680c600080704071081c10014aa2201c165490b61001d040440c141e0828005c403803007401945040d04c180b40d0300b01d000d9030f403200c2043e80300281100000240607a000c04c0395500c030100401c0c00c0c0010860342d102d04403c0d802001b4542c3e040181545990059a48000c28040c040d0b0003501440b2032803a002204070f00001d00241444100c03658014056181d280d600040000041d2240210562407129030201003280070710b03c1501074150234248168504800e20809125501800720240200d00d140c0162440c18007105000e003c42c0c0140c0390904006000007031602044071103024600110b4420108142140d0680d000142b803a1800ea00d0a00190340c081490a1803507090700041c000000981d03030a1020b003407160099000803d0090792840c062402d280d2203403100b08d84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 184744730 1250 184743480 184743487
    0xc0f03020f0111061501090e070201021c090206181306030305092706060c330f06101206030507090501080c0a0b040311063001080a0b16090b03010b0a14 67
    0x11060005840c85c0c02c9604203d00203042a10580100c03840c0d89903801049000c0400400e11a240b507055009000c02e104108080c3c0d2815802d42400e808d0307030100309029603c52000e110729404052501d8600c040c82c40014404400c0c5d0311404001c1068504503030050700031841c082121511070904804989198500c40300340005460b02880100d08641302800090080d1004600030802500801152400e007400e0601f10a5621055603014484000507034030407032031903c040200d2025500d10180c0340c06100000e00d85604680049002c48284079011070003030700161202c1001000c100244005000b0300b42c600b1000c5803d6041180c5249405ea80440040c02081d003010704002d900c0e02001600c06880d406807080b10042021000601e00d40142500c0e405200c1c1811b0038142c41c0402403516840030707061003541c60000c1e80d03071b00c000c162039408810b80501480381d2140090310380301803d08034496101c0309040a480781078403094266621b80090700581c03007204000550750501d54114054803070419030048001d29 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 184745980 1250 184744730 184744757
    0x314100812030c1e070c050f0108040b04061104031a011502121c0f0f050603070501050d050a06080f1b0306040309030308070221040306060b0f07031b0c0f03020f01 72
    0x503124418214100018004004180c6005400044501003809951488004d010140707004c48a0f60103e4421101480c00d0f02d400504e03801c02c0c04840710031200c140c40d00416940d50340c07900b90305400e00601c02ca805659808090407402c1c40d00c000340014500405000120b005540451581804180c005445a0f18184d40c42000d01d640001c0380c4100e5034881d051180c6902c1d50103040d282c01c5120b5194038031a43c0c2001c040d5007600c06107922141800c0071004080c00b040c2c4503a414540c5601c7d890003281d0009504105654001c07500750480c640000324050b001a005541c1d280c1c5905018080840311515081540c0c0140d5510003091429004901180070701440d041954014000148512008042c0800e00d000503005030300a01418410040400000101d10710b002904107203a80140401c80b061450201c0115441031382c2410348090702411002d070381c601a010344041d684210740e0081902055070002d80030001880c01890100201000305610107400e00714410020240343c0900e00e0380c10003441201009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 184747230 1250 184745980 184745983
    0x1008010c020c241615110309100b0a12150501091508030a17130f050601080f03070f0b0408040f08030d060e04020d030f050c01050c0d060f060203041a04030209040303141008 76
    0x1655244180b081e8036255600d03150400305c24060200c000e40c42d500d89516003400300345800c002e610070324010050355042308510504000b115407280580382c00991902301440000c030b6203c07910724030b01d018551000c10414248910021740d01300341c0010741110380300c480b0200884000c2d40c1c03420107003210401450400f44042c41c02400c140b5110044c0c2c24160314400440d10310506062800803454124401900200e05801c006950f00b000307100310446445a49040800e4407808070641d900b5640c01403d5801189aa49918801000c05082503420080401c00001c0c20100444039400804040c0081c5880e44000354205085a180754070400e9015541010400181d5441d40b29064955241c01e1050701d110b048a0215814020301c07011203103e42c039007424040300c1e080003c0903200c0c41070b9030303401807160644a28580c40c4010344e600c155005680240002d00410800f041681c24141c030000c201d5003401d640b6000214840e100765000d801090303a90030f40c3d0b0368441d1a80403081d40310100007079a000ca1403500741c025 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 184748480 1250 184747230 184747237
    0x90e01060503041509320a08030a090c05031c080604050f0402040f0b040207061409030c0307060203090307170c0c0a05030d0c060b03030a020601180c050406081008010c020c24 77
    0x404d0b01c40d030180c0c8880c0c1c000b5207520400f50b031500184000a00100d403507a0f64044940c0348602407046094030520040450000303140049288d01010060035902c0d89205500030b005031321001c86149211b0840800d05480810030313604a03c0b001d41440f507115030036690140c50120090030840c0103606203010408065106036000360020b074143c07400a524500351406500928500c0d40159210303000007004030911000d0381010041c8140c4003801d5100780c17190f84429a4134411220a00780b160014032441000c1032599015544c040300d03940641e40741800b1684c403c00700081e040c49041c08010003141d818621030301080807181180e41541c0c880892818100025030f9002a44004e000b004102e4610504100050300107403003d2030050116610340740b5045019403101c1c800d0040c1c0075005109035031024030b40d1841c0141d0f021941c02d516154a414200700c411030354140010682c00c40003166000010345600c0034403950419010ba031707012b0a010600c08003040f400c07804086c0c128914a45c44405009400c4da0038044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 184749730 1250 184748480 184748483
    0x20a0b0a060b0a0c0302120a0c06050105030328180b070b07140d0209010302040506030f070f14090906010203090d03050a020706110c04090314070b04020111030c060c2b060303090e0106050304 84
    0x92113080c100c80c6000ca181c0a00880c41c0a0040c101041d43c8071119000101d4004140c031a0105203d40d1783c84409240d5240100b8052000600035648600c600c0d507002c2f800303546400c040380b4103004150303103044044402601c0b0764413441a05400043c1d10080c01414070016811064925090031030b44140042010b0301d005003150b560f1107680c000344030b8015a0107503048800074200602600c0e168a013034a84501c00c401d04442d01c601280d02c2c803074010002e510032079907134500d42140f5586d00d04000000c411b00140da08000c0c45d150640c4000c01195400382c0c0d800c042070144512990300d681d5151194000282040c030a903100c18203104699202c90300d1404045481d605980701a180010f605a440c02e040b69401841c0c060201c0386000042c180041c000c40a0115200e28000c0e00c40c0c2401c8510400a0740e030724420503d00c82d0090700104081152024108000c01030040c20b40f400c61003240440f070b00035030861020301ca64200306039125020010036801a22140060546903140580d561400c4400782052000400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 184750980 1250 184749730 184749737
    0xe070504110412080d05010f0b040b07030e030a0f03090605090312090f060406030c20150a0e0114061305040308070c061404080307030e070f061209050d020a0b0a060b0a 74
    0x80141e01d1a01d0001510000c00d61800a5a1041c0c40d0b401d104c00140d0241c1d40400e036050409002003032110700410054100c032100120103151516000030f0031465040200218100a560360204010396070810076204040d002d2011b1000c001d0151402401889003548102c0611509011046c10f968000c01e454540e00c61406249544659000005a50030342c061022035200d1404030740401e950350301d50f110705d40191041d1249100200c070010100030500d081003902c2015444401c026840c8180580300d29042010a6004225145905901829038602c00c90489401d00c51504010702490700403154094500743e080108410300701928000d000040c002c28103400c1c4040d1003000c6041100e1940b08140160b030384a0f0990943c1864500403c041e441a2905000207041101048056002049000c00c0368003141082d8022032500100b42d846180d01d003081d042a0742d03a8001c81c0007040d010b1000200b54009503028250900c07052900c0d00c00d100001d00780441031880e1407802d100703a10b100001c980c1004d01c0c505 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 184752230 1250 184750980 184750991
    0x170f190e0f04050612070609090f0501050a030f0302210d05060409081b031603030b12010b0303040612060509010314061609030213090c0b090102070608190203040219140a090e070504 80
    0x130003040d06288841509191446070903c00101c0ca80d20000d040c0580308810003d010600000002800343c5d00d00b80a85c83d0301c060f00e00701c1003001030308000146e00210b20070b005641010034021005020070800700084070182030005010414461948290342e8000001c803030802c02d2100503255010203028002c09622504185048108440c5040040d101215a5555a0035246445280040150000b1480c0d036000e840d01c07100c224000b01e8107018820b00c0303c10140085060502d4280203d4444007042c03990000c2658a01c001320780381d1120138145010751700400b215005140481c00079490008010319803100c5a41c11054442c0b2a94815160411603404950700707200c42c00000d0800000300718080000701243d03500a00081c3c0c5c00a101c0203001c4881c0c0c00d03001d40f007c2650711300c0141c3d51224100e82174840052024440c5280d0101da501564009002900f1044c020321015003690b500000ca801c40c0d00744109140707000e41c46107843c0c48200d0281098081c240407011302e0544041c3d58102c0303400b44030b00c00c03a00e44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 184753480 1250 184752230 184752241
    0x308040311010507062c030703230412110f01170106030c030b0306070f02060108510103150b090f09010e1902040606030203010f030609170f190e0f0405 67
    0x400c01d8812960300004108900d107070f14603051a40980d020780c122a0101d0703804d1b00444101000c425102843d81544421010040710318046001e040d5030401000e1302d1105100105040700f280c01400303170981c41081070790101e00820040141d82c064150301c107410400c0b080b2042c4204c800c503000c1c2c1ca0448600c4d04020402c14507500054002e1704d419044550075106e04420000c2d41035000960b480c40311181d409070b81e0700380d03262aa000e4461844c00000861180a421075112200c0144034005014aa032200325113040c6440f061403052180d42c0d002030380c0c00c06064005005210004030300459104d603610040105400d0a004118202c0c0010b1188540c0000100061100304003900705295200d00081aa080801c21505100c90f171000c82c0002d1380a140341a0300844d15501a1003101c2c1618802d8412480003403655480b0b40280c10341040c11a400400c410400d4032462000004c0e02d900b8046080744c980300d00a03500031044114640d2400b030100000c1410301c020300e4a5241d145201c03a0411754002c155503492 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 184754730 1250 184753480 184753487
    0x1120c03060509130b070e180606040f2607060801030f170c0a06180209040f0602070510090302190c1809050601120213050c031303120905030919030804031101 70
    0x16a4031854109250380d0412405844401402d00320501c121700c110900c2d1a50641200e4848030f41ea6030a410940001e240e0a5441c003a8803051341c0100c00078403091419444201c1c54a5014042c0c0c0700d00002c00081071940d40601011005200502d42c60005143e8640f521000a000c800c0604c0040c080c0c12841003c0000e010034811612601004006010754440303258070869900e520a0005a4886191006805d1007014040346a210b55400602e040c3c0c40fa00d03240c0707451001e585054000c0726000d508121752000940103104200081201b004006081840e504000e03040002e06030b003594031800d410701e641c800198681c1c40101550380c58142608401180703018000104000c1d0f401a249101e21000000c4a90300e142c0d880070005d1007030300c1c41140030701e0f030700c0d4031005640c000e85680782840418800200e4500c50780a8005055001e0f2524184030513050643e6002c40d042a00c045c2e441e034000042004c460f0809030b40e2140048442003080300468956100d203545030040b4080103024004607000d02440d07a11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 184755980 1250 184754730 184754741
    0x509030f0106061d010c051203070210060303020d12020a0f0e0102030d020409020306010e101b0c0504140901150602030301050f03030f0d06050a09020a080a0f0e0a051b0d0201120c03 80
    0xe0304000300602d0361100c80141401450410016084403070403000201e5501c5084400c4419621500410070740004a80c3c564031508010711041c00c40c451012010305001d490b003d040c00441c0039801a00780e164150800503d0201c207800d030065054010807107481e0a0754010304913181d140c4e062511120303160f0b010380102d06520a01b00b500303807000c1c004980800c40b2170485d4002c5001d503409803985216481f1400c14001816884604080480c0d85d04190b9040b040b6a00c0d134800d4468401d985040010f80c4031000503085480e8031a0a031719000040e070800101007030900c1220342503200300803005481490054001d589101c14081c0900503480c81d940d0140c50b450400075922074081101c0300646500c0220b1244008141502c5407074800e4102c90300000f0101124801c031240710095940b0043c1d01d45c0e8116111000d011401c0f5240803041e0382c2c409880d0580c0050010f1001c0f0751040c8060590040303200c0c0c0d85034200c095051140d00c0355484034040740c0141e8121301250b10305211382c500811840341e50340703060b4010324 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 184757230 1250 184755980 184756003
    0x16021c211b0b0a0b0f0d110a030b07050c010c050415110703060c0c11011409010e03120f0a03050a1b081b040609150c33090b100b1603050903 62
    0x7140d5450741045420346200b48200d503900810888120f10108000003038001d820310a4000c1d0110300d442c0041003122500302e44005010300384543e250303529036990034401801c6648000040c40480e42030030a4400b8002c900b007100007480c03c01e00706403c00b00ca04450f003803068195020300400c00710090010400740050b20055030081400c100405940d0b40c0580640b007441000c0342d650945600403c9903600a500d0500075100701751360507040c0a14480150b40c00c0803000d41169041c0306080c0c0005480c28403900400002401e560803607104d1100c080c0c00b0f03082d900007502825010f802d00f01000022016000b1082c4180303101c0c6019061074840d92400c83c500e014a03d1604841d031000100072030380c0380e000400c0780101c40004800314007007524000111000000b86000626103003510200750b006000080780e248851241255890344200019a40801c8a200c3c00c411104421030404000c5083c44c2200d04800030070510080d14602440c1c075415414090751054000c0500c140070800e2413090324100b0001c01003d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 184758480 1250 184757230 184757267
    0xe010603060c0809070807050f0102031b03040906050901080606010810230a0b1204260d050405060601170f270714010201150509071416021c21 63
    0x1580c90341070400241201c29a85004560001c0101e4642a00020f080701103074070386400740c00710909003810407815001e580400c0f41144401d11a034415000140341c007143d1100854001c556562510140300d042d16201e510140c070400c00240100700603500401c107560322041c24a014407082e5100302c6d0030112001c030b41e000a00c00850303406240305200102e9898003860f40e070444e900c0c0702c241c1c0d554480900c20300c0f4414a500502c0000804100015003c3c00a04020050499042045400725441c40c0d0640c102d0b034101030401d070b10f420600060017400c1c0000c43e0092005e00e0f105145003090f4200b480307140d0002d0b00f9600030340c61160020307000d001076104a808055070207102e240c0c41021076000c1c82c0d03a08014000e10030400d034441e41d41c0520358014801d490010880307860141c0c400340b0700b000700198240c008140d02c7c02c8c0150101c80d00c6003144888000c264007568100c10140c480954018483c04203e160401c40c40c1400d5441c01c1d6001c126048400b40e00844600c402440d40305420508a500e07000f04605140798 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 184759730 1250 184758480 184758491
    0xc030b0f0405060c0a1d060c0f0105011d10030b04021309080904060f32030a1b0b13050904020307090c05090f0a0e011703090607060903081005060a0e040e01 69
    0x80c51040d505000d01d00a004031445034840350b10f80b110b540305030788400c008240e204440004415001030303a442c2031040180365506202080c0c11441c00d1003198611b031034103655503000501040b4004208000c407020740904850851070301d0003416201c5400340c0009404d403903001001400f1555142c1141c0c0f20f1075105082030107a4009440c0074000c0c2d40108040754030442c24a1000300d8020001c1107001e0895030040d00301c2120112000e548003901843c2c002e407450212500b604003103240c0f0100212050305214601c4100c1504040f000302829617101d07005001ca0190801c10517186d041f0342e00c080c1041e41c00440d420502e584070703840000d10341080d503884400251b040c851110f511a4220001e0903441005490840d00c1500308010051618054022121f11900e60001804181c06070030200701c042408a04983c03414000030006549604031540c1110301c6a00c48000e8400c160f84018240e400c01c0c1c01e001034503003040c100800078009000d0f84001c6001c00050902c64122951240c100c1111524040000c00c079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 184760980 1250 184759730 184759741
    0x604110919090b180a0b070302090301180507030219050108010501120b100504181404060902031203090a03030f0213090f020d060b09010206010501111c0c15050901050603010902030a0602070c030b 86
    0x100410104c414400840010416601c400d0000c1004282d469105504d030f04a680c451368243c4c02900b04250f195015035889100850440104d412080400e0265004082d01e40c51441009140c407006850300c01d0085841d10100310b83e90300008c0f0241074880900382074802003144034100c00104039001000b5807100b102004403600d1600503004200fa00c8030907001d0744880d2000301a101c141c5100c2d10162015801c82c100082c0800c0283c1d00092500f4801001d5568a01c2036409205064100f51074401f000d0b0040c007100f10415405104000001c03414100c02c1d0f0500701290102081201c41e80701c0c00d10305a45a103029601d00301d069045602040f01040100300e00c030380302e07821511281c0040450602510810001040325030040d004e03c080c4151407402000c1d0ba854070903085032050350702c004003030034000030080b40400152802018203030303510001000a420704d03240b82030f10300b0744034090000c5000c3d915203128840540c6006c212740302c03480e80242c5e016a8500c10740ca0041340b040c80e0781d48081d16114448080c0304 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 184762230 1250 184760980 184760993
    0x120605102108071e06060b09010c02091012050f0d090806040201030c121a0301050a0b0607060c0201060e0c0306010807050a17090708030714070e0c0d1a10020703020111060411091909 80
    0x21540740540317010040161240702000741c600c103410312a0b010401c14046400181b800300113640d4003904807810007c04642d500d500056800794040201e030942c22103080d40900410421280400010b6850030110f0716181105140e2102c8010b000039041580320062401030901901c1c0501c01d2840b0100104001c1c01e04144001c01680c50340b40303491123035081102151001c89107000d21994440e00801c460b00d00145c550b20000104100f03442107056540700c3d54005054060300341d1040c450283d42a00b15039070b01e00700b400100311003001803d481c01e10000b0b21120001e1980031084d0f4102c1d40c4240c02c03024190b101d541c2c0d0f5514100f03103a07000200300e00c0002995010040281050440800010100c0320981e44420322210259001c4513440481001440f455659607040e40291b103d4100c1c101c160043c24070078902144c0400c000c1c4041501503404400c080086590102c941c070100007440c0060200c5080a42d580030300c000407a400c1500c0307881d5030300c00b10701d80454001004100c8050b040c42008580100d01e4150b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 184763480 1250 184762230 184762283
    0xf031713020301050916180b03070621051605090f030601090e1603050d1b0c140f0301050c0304030c050f0106030507060f0c17210112060510210807 65
    0x324060f509100105130240f40c001264250303400503801501c040b5003000f42240d640b01010b04c203810301945450916076291400d00c003020190190350303658000d0414185500400b501001c8188280e035140001b002000c510280b070341000c2d400c0303503c0c02c1ea907240d03800340015065801100c49143d260090301c0002980800c50f0303000361003615025003526a4039102e40c0301907880850520016086801411041703950600c00d02c0c80e020b032207001400c2c020450f050b41c0c860602c41c01d082e81024031102410045c8c0d800c00d250580b101d4078002821402400b00c1e140c00179201816010140008052003040e42e1841d0801c40240848000034004100811010760f036400c2c030590b940700701c0c8176650101310340a4594000034402e54084034101c5d0400030080d006004200b1001e420743c4564a80c442c0c03c0c0356881ca1144103032403079212078000d0605180d049442009820b080040715405401c48500540c514002c21072300b01030214248140d03100c02e5011031843d4103418414000e2084a100810703400690b4a0001d010031a0310b0170 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 184764730 1250 184763480 184763483
    0xb0a0908180a050a060504150306080105041505010b09060f0a02070b0711090f060d17090402040b04090b04020c07090f140412080711100b031509030a1d06070f031713 73
    0x55501c01c3d94940912411015a00501001510030441032000900c1036802c40c011482c02d00e00004c0fa0f96440c403c56003110402d0707900b29014650b4203900c0781110564012903000d400c028658a20341022100003030640d2003010000d545840d8080b0750315010600030701040300280001c1420340e0f40ea40c160305e40b060141085e404020301c01c82214004c10f56241074a0307443c0e8407814014111720415a480d4441ca00901106020103d14070310400c100031864443d8005032009000400c40301e03840d1401d141407201039803481103606014520500c0445030203100000c0c02d000f101d1400e00c002071840e03900e10000c1d001d00890840420b8449000052100300304541014079005201e0b940c491030a6103502004503454a400c0740303241915849403500500e00c41c455845203c145200408480c049001700341d0540000904441c41801070f000031441c00f5511f0f410400c8244003226255441101c1c202c0c080025800f40250070010703080c0700c16054403208241c0289030301d107c49224031210700101c0c0340c0a0501c20344040c10220 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 184765980 1250 184764730 184764739
    0xa0b0d110403020d020112090206190e040c0c080307030f050408040e07030c091406040302041401050a0b0703020709110702090108010b1c02030601121b060203030403031112040b0a090818 82
    0x4810904408520940c0c1c01c0e01c1e0b004024581c1030f03030b40d038004541c1d20910181c01443c291395281c1d0303140180d980000424003604080b04a00d032200000310080c0800101c802038500560801500b0714429612119900442d40d00c818215184c0d21242d074118010104603440120840c03511082c07005003d6100b000e072084800c0a4080398095407407110490a86092445000c089803030541d05210044942c50301200012014050b81d0030303d540c0c1d40004081d203d01000d040d92441413900140074600304280300c10301078441049140e00c0e050880c2d030025034400c020320a036503200b0f50740e03490400070620650841d01d04640080c1400b1480d41c4400c1c040e4000d02d652101a84940c14040380400301030100c0c104a0075280d002006404a17a2806c1e079a40c0c0f0720104a0000c90300d44178889107445594245e07040c02400f401040e4003d540b00e14092078040c007222000d02d03200408401c00c0c00b0802f010082600c48a07406903020084c05030645a06e41c10401511003484000c04002022514a4000400900200315554200c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 184767230 1250 184765980 184765991
    0xe0106033806010507050a0b040203010b0303070b010b0a0905031e0607140904110906030a09110d050c0f04111c0506040c080f1306090515090f0304170a020a0b0d 71
    0x620800c03900390464888042040414103980a4100001071541d01c410306050140c94900250784040c00e0011040381190b400f60036500340401d50a09200d05005900194003d500e0020180c0b6041a19113052181011020f0006900d100940c45600046c0c002c0802504a900340840d506040344c04000c00481450304d032080c080014041403040c400747c2400c0d903810003803600e0154a401800050401e252504490140401c0007609503180d2200861064260080002d28401503140c041a586584100c3c02d1280e0750081200b0301140001c91180150300040b6241e644c0056014042409054440d040e60440302d80858400c0300d040c26010007000290b11850200320a0340c480c0200000c581050040c2d00004041030700041120092401c0c041c1c028503103100c0a00400c1c40c1f95105c000b0354501c20001c0350f0316004161468a030010041500390010201030180c000348501d4848940d80340650710031400d07101208035a249800c1001c2c170418250340d4000d041003600c2a203c94040c0341a034000c588922030f4520b0304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 184768480 1250 184767230 184767263
    0xd05060f0c0a0e09131406090c030307020105031609030204020a0f02062a031008010203040f030e0f0306160908030309010e07090902010e040e01020c0105150102070e04050601030303021c0e010603 86
    0x14007119642070300c2e91900e0b0300703890800c000d02100c0d860040c0344c40b4842d1902090180070455685046501250403001001e1078948083c40034204800c00f6001802640144069030040c0c1c3c010054a51001c808400d0403400d0619050449a5018076800030750401c0c80010900e04c0240c0c401d00043c50300549400711145a143c540e030403121901084011603210a80c000c0c2211300000c01001190000201c4103245443c07500c803c021400c81c1e000f620111400156005c91904241c3c0184418041c2041140d10301c5103c1d0300c140c042511610014207806500c511a80315146c024084d00f150400751644404581c1c491806081880c000c207074a1208500e98816001c001403001e4003801045920740d410394a0414841c0700506000103011003c0803030003595000e000000c0c64040c03d11805120360303034040d044400c4214650019040c40c8054028035250312503001000046400000e006044079811b1800581d56048201101c0f0002160300892010b1402d20214650151054000c0c00079a4040ca020201480c41c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 184769730 1250 184768480 184768501
    0x1c03020c0d091206020f1b10050a05040b0408090402130f0e1305032a0303070801030b06040c090b030402010e031509010522020d061806050108070e070206240d05060f 73
    0x6129410890b2416200d150004800750043c000102041b0740d60b504200e043c00307030b0200c22403403862100f171154456050210344407528003809420001d00e1204004074103203921603010040d001400030b031450800203800091512168111581d101d1503a1010000c5030700c94030a108007015912030740d98a0401c02011803195038a2403480700f402c0741d00030000c43c41c001c0500d847e80344500421190030a6200c400d00302c0b00030001d00b03100851240e20950382d000d8466040d40703490f018405000d0700142c015882c0242540702c9540000544003520300702d4046c641c69540390320040310449110001c40750180100c2c200240112602003a05001f0700e524802805584c0d01d80a111204071080c03012828040d030000586400341c10012001c5840c6e074040d000104110020700c03190013110b045050300711a01580d07000104002601445190040c08000a40a20300d09140300001d503140320180074040e100f001c07084c590b005030007100700c1d0410143c8041c00700080c118090408603284d003001c8599000641840c400a10141c44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 184770980 1250 184769730 184769747
    0x10c1b1701060e090312070c1b030303020912030a09030318050a080d12140c1b03040f05130c021e0c0d06020304061805100c0201240527060405091c03020c0d 69
    0x284140c46050039030320344000700c804e00101402910600d0309a28000220804c1040003804ac40c001d03100540c1c1d4614580034400300303409480500c0f070986c005108011100b0f0b0300080180849405d0316140e00810714040401508041d545d00c03181c2d110380766820001e085c07500484c0441032124103803901c2200145030b9040500351110f60000c11000d2080c040000c090704e20b8080944090078a422030700480c8000d40003000c5c990b40c40764216507211000c54004010a10349880000b11803401c0200510004100b007102a42c0c540d821200e11481111950341909041001c00c14005401c034000c1c000c80302d040382410403030020362003564190388160a03c074080e00703520080311200100c07540c050700030010341c51606030800c0102881d05a03201103548680000c0300000d00500324010481c03403201e100780380798544800c08c00b40050b8440380300140c1c402d5865000782e2000403050b0507480401a10049030360f984000c03005042030207030704003d1098003001d542d6100f500d074540c0c06402c00c0e081210031161640c1c8812000d0301d4894 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 184772230 1250 184770980 184770997
    0x609060305010311060a030b0d0b16030204080c15070501090309051201090b0106051c1506020105091504060908090303070f140a0203060406020a030b0901060305091002030105010c1b1701060e0903 86
    0x14040344181c409080010003840c02c031b01c0910300015095607610001d1000c41100d101654810101000d00c10200040c0034032000d07020082c101145050724116041e51180da000c2e2200d845030b10283e8034003c40d00100812204079551040c0200020180c9143c05480f0000d14001c2c140070f07080c0e0f000a03400d280814401c6512260300800306490130b80c0b0f80301044410b6800441c610754038144094030701e940391201d4041c603440e40b000030b00724465a0b0300700100242100c0e00200105101d50091444800c40001c160381550802d03080100420032030b241d8140900540300e01c0415a41601c400144041803290315401d0401c480e100c4d142c100344030080d51900a80d501c40401c80650f058100e0300124000460b00d0b4010403507031901d400c0109190010340001295070801b6440800803d0b15001041311104090181d0080040040c1085086504120000304180c1c0c00e108010203820080021141056200210400501c0068108942c03c1614103149010708498814041e404c5036000100d40b030725501205545003071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 184773480 1250 184772230 184772243
    0x105010f1d061e0a0807030203010b1f080603031b010506040b030303100504021606060605180a0315051e01060c050f07061707091d0103050c0907120c0201110c0706090603050103 78
    0x80d15950700300300c0d10f01100d0440d1400266142e0a01600e034458507100c44c0240300c040064089981b9500525094a01c0c595a96114401c05403010850707541802603104a9811460018099510b00012a10b036108a00440015015015414040a01c15003045100700810351f000e100104400040c075941c0d0005035003a0345580011001400941000e5000c1c203154641c180741d04c010044507445031400c84200350030100014030005284505c0110700c15034280ba140e0103556a2100624640344c0a01c40c66140407480680b030345610204414035041600220f507403143c0c696201040d41c2d90240500403070b031858030449007802054044001c516000c91528102e40722520765646405031b954080711540e10050005050080385140414882601514803004010402103c040e039415410403d25268006503024840c4c4412010010b105a201d61413503440b20702808041110b00c101c0a041c1d0242c4038180c0c1004c036880303020038030310304c8503e0015406084641c1e40e15143d400c0c5845550881c1602c10900016060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 184774730 1250 184773480 184773539
    0x52716060c0204060506030403090515030c040e13140319050c030403110102191a060409050a0b1018050f010501050403111e1201090507120317060105090901080105010f 74
    0x203441c0246809aa21803000303100107007440d1640d00060f1550401e0700d0580003e8200c01082c4054200000ba40a02d50103560003e41540340c1032081c0e805a100d540185041c050b4440c01050072074035042d6903224190780c440c1070040314003190f080c020b540390080348002c1d421941c0c510b401d02040e4021400c03601c1ca4240f02016624250468a0315040007501046d50f504502c1a4805d2500c42908090b003c050079200b040744030001c0942d0055850310f00400380240d882245042c1c5000002100002c000680c6d562050b11441c041c0e580204030700d490300b65503000b00c00514205811111064503071748058405c11000490001e903076292801181d4038041ca000050222106007030201052512180841078040c1c405c00d451200c1c6c44c2c01020941d10400320401c003200c1e0703442d00f50315801c0040502010000d40f00002207201c0741201d41d100180002075a030a004040d00d0321401140740c5910800403a09940c0000d0000d0640756551031259000300000d100f075901c1d1110310341000c280320074040c100402444034180c06500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 184775980 1250 184774730 184774739
    0x14060a0c090e0615120c040812030903121504090602030a15060c200604060e12060723040b0a020a031b030f050c0c121f110a050f0904052716 62
    0x2c2044e010f0b020601c00c000144400c1180303c486a8805102d07500d9100003c2d100c2d03180c2405d461401350700201921400400b4002c000c038003000001a80c40c07518103100640529211000c8010920710000103607a007250400c1c40010911103643c0045004030742d842d00800011048140455010107507000d850b0004920742e80d00808100070b4117829105802140d0750001038943c01002030500e0780540c6c0240b01242241880016038600207201c1c008001c40c0d88003900c11860300b0300009180000030018404811023640d00010400017a5054601400315181d44a69848801e10701035a2040e07034440403000603110410300b020030040d1a1441742d115505880e803908480e03212000b0360740c94100000002e000e124120481c040c55881525050189000b80042c003544840001015048040c00304138460150509620310b2241d1144801c44242181a1400b02d85a240501001c001441500880703980142041300b44408100780103000b8951074040002ca01c0c1f00c4070444400b0303481e81c00c1451111074440c1449401c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 184777230 1250 184775980 184775989
    0x30d050307020c04060608010e091203010911040503121308030a050a05071a18010c020318010309021c08090f0d03020a060b030a060501032117010504110714060a0c090e06 75
    0x58000302103005988070395400201003021981c5d00e921100c0050300210040002c802e03480c0c0000d03049903881003d4074114290700b852030090301c4184507143c036490b0b9480d010800400b80e00c06407000303010010192101c109403c582000d2541103140300f0300e00402203040c0014076200000c1122251065030319001d041460701d9005a80e00e40103e82e055821072000120011000c0d148140c0510807074024480003528105000c1c1d9608454650410b5001d560080090f00248403070040758400c100030910b0b001c0390b1804d0030301c0480c82c4030f1401c172000b4050081007580303d000c0000260261010f124142d0302c43d88003003030300b0080120040000c2d8011340560804815a00807034201d40000500c000301130304a030a5440d040d5250b00440e1402d1f40103841c01070b1500c245200c0c100b200d2400100031092403030507c0344458506030800c40c40748184265441150f0ba2010307400443d02a006903440c035030304024035a1100e5054042c0ca13850316402c45003c0409807400a5a01c42c0d1401080040c0075148103540b11000d9907907810600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 184778480 1250 184777230 184777237
    0x219080702040c0201140a14040f11090a1a0a0b070b04170d0f050c09060307030b04090804060f02070504050c0d020d0b060316020f06011d07030605121e0c030d05 71
    0x1618281010408030000d61070718000c00090310100e600006460b51410b0404680c3c030000781c45241268102201000700041c0d40c038290f43c110703410498000040c420303482d00d030001c5020b01d50420382002444040015000c2940d109502902070f000210810404140411140b40113501901e02030030824427244c40814200c80d5016805846800c031400120301001c0840401d03001055080c02c9141c890104071030004080c000c46402c10b51410089007004070303110005209001c010032110400d5665040301e0b10b0b5a403150020b0b59001e0b000700d450365440303841d4040100301e0050980e480700580b1038694002005c1c20f0512034240301d480041102d904000e40d072400700b0069403111041170200c1c1c0e00c4c0c04a2065960380e0314000d50041004111480b1800d540140c00303424150481003100313803130704040010860b0b006500340440d448507103411146555911142c050f0020070306500420780102c0b401031003000d810342c00155045443c000308079082c52001c124820580d112a84410740d50150041e00c402034646000318080c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 184779730 1250 184778480 184778483
    0x109050c032a1c060f0305031902070e010605031e0402010f050702040b040615020f01090309050409150504120318020609010c030c120509040509010c08060108060a03060203011509150219 82
    0x501d5000c0e0910040d8405904181291101c03d090449140c0c10300c030003445040c00038046010076440c22803a5850751500c902072181c61072455401ea1200760b40c3d0724400c0c811600035181d40c0784800d0903542c4980c402446c40e0021a040ea400001d489920030740a80b40c501b9840c8038a45c142c1d980b0400d1103116600311000d40040c10201e80003600c404101c1000d41c0c4600882c006400302e1041803414401480000386040143c6800c1c0400da45840c9010021030742c130080f0401500d07020b442c0480c541181d45050302101d4240ca141565452a040920040202c540401e21020220f42c0d011b0285075031030601e115101c0500d020007036015034204502c4595501400b59101c400d40a420080c48041080e00c811510016680c503c03000203100040380c0025103010310501d90046039a8000304408000038101a19185006c1c00c01c506003c00400050420355612140001560f44100159229652001c02002c8403003401c60090200781c0d00d0001140d500101b10100440c0c010f07036401004203542800d00c405946815680 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 184780980 1250 184779730 184779781
    0x30804030e010219021e0303070602070c05180a09080903010203090d030b0a0501090306151205010501081e100b031606020619020c060c13050402070506060406080715030b030f01060b0408060109050c03 88
    0x3246c02c00390303414809442d5071170240387d026965440c01d240400c448510358002030b108280381440c451900301c07206041c5602c400388010024007007145082c400200e00071050419032540c0000108407a0b00b801040400380d203151500c09001070068032040296248160103034038000ba01c0d1602c2040811706030740121009601c00d03079201040301e8441224400080c8008003d8a00d03039141d000401210404000329003e0a102c880e003988440d81c8a00d040f43c403a0345000e4030301d844a49998041c2002e545c1800404403080c4080e82e264a110754851010b9201c010072100780c0d004c08106074000c001c134010390084554100b0003002505942e0b840000360b071042d807c82c50411214104450002c10103803a90b10082c0340d001d00480007404146403401c100320589403541c01000994220345000c2012400750381c4440c06c401c40506010491502c0310700401c0c500101c1280f422919800c00360005401d5180c0d00080081c1c0c1d0580e41902c0780350ba201c0a019040d501c0503210031200030001c20008101179030031030000142d00348851 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 184782230 1250 184780980 184781029
    0xd050a11161a090d080105040204050607030315050901090905010506040b031504080702090a1a0a030503030a0216020607030302040302011101140103030c0503120708010906090504080f0c0a0f030804030e01021902 93
    0x1c445000e001c101d0700314040e13a0010700701c1c40c04240c100f1081801880111030542c9854144404070780d550059050040c00c1c11307203030541140e51090045420380a01030140601d40d00d583d4527801c03c1f000d0462800203075200c1d444c1001203032182c286801261603414001d0300404940c45080c07650f020340c01c8000c1090b82c1020040c08104011380c0c40003c464080c1200e0304000c245018141c039103660888021490911605080a040002910110542c0c0e484030703a1a10041c0c44001364118240c1c200342008000b580120009800f01c10541c2503406402503d000383d9a06038500010002607088807103a262018100c24040700420000340710301c2c031035000d2034441d806581c10481032081d914460030701582c440c00420041c00041c000c480c802d1044800030500e900d03080c0642d00b0503031580540c5102c0c03030240e003800640c0081c014081d000208640c034502c950207611140c0d07031040e5040003000c0700429102140025103119034000380750310000d90820340000c15005291940015030030821408000005841d2101411 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 184783480 1250 184782230 184782263
    0x5040b030405011b0c1a06010302040b040815130c0e070c0b0a050105010f020d08060d030c050708060f0c0a050d0b0f03012a050c030a2607050d050a1116 67
    0x84015601581c4100c001041200500d5022040c4081c600000420007000344038030f0700400d0304480d0b050300113084801c2d40210340d294040120080d124030f401c01c0c01000400103000910038000690340c0340c3d59014452612140d2101000070031013851600700946003a0310b23a481445000c0c0011386490300501d01c0c0c203056030700c1d12307065580205c1d00e4000c6a0802d071181d902c400420503540c106500151411146c805401000d070008000b078101c03080504000d0103080c0722060f407810076000350799011205401000701c0d00482d0341c60200e40c2d5202001c64600c910680e1010100d01e56007100d0f030a0b1341d204000364540508141401941c0d000511041500e160b104225018a6a841e2003e00c500d109070304080e02503a0345841c8450000c00307041d40d200a0003041101c03c004d0118094000b1082e111200064a040c1000b603951303154401000c170000c0c0305103d40c2c3c03012a041c490b41503040710041071142c41200e0f043c04141d603401035400484d41c0203001100b000004114141c502171014400c41c2006204030b1102a02d1904c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 184784730 1250 184783480 184783499
    0x60403060609200a0504061110090c08161208070204091b050301050907051804030309080f04050414010320060705120306090f010303021504052b0323010311010504 72
    0x1d5a00109141d9a252481c2c40c0d40141d4010403070b56152101c40f510700e0711504060040c841c0c440c520030b1100704003890010400c984414850074014490706001408030307000c24201031041c60820b1003400e109100300c0d642e804005280e1804e0f80122011045103440580c1c1f282c5800c100c0d40d00c0450102d034010b03035030640c2c440080c0000407180d0f4510000d400a540007410401030508482015080c4606070740101010000c660303402c10544151000000b000c0300d141c44518040e0301518951500400824010a5007100f85019001501c12078604070703014000c00c0c01000312035000080078003028044005602d91220000e140c000000740ca0b05000d862140b504516450f03103030400689980d0810084800800e001d15460701d03018854004140c40000d101c40e51440e6006566000000310000d0b8003403104000405001c011b02c046000b03030f101001c0c2c19010003e0b5010f40c003001c141120454010a2401051400070705100201000000060f100418141d00b5902d8107040f040d130480516040000421000c2106010b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 184785980 1250 184784730 184784741
    0x17180f070b13050105030c2a031204021807020c10050912010203070e03030a051204030c05010905060109050109021e09040e10290d140f030a02150105030d0f050906040306 75
    0x880700a803545038010300d5040d240c044455030009041000030b10601c00c40301c0180044545d40c15051407400b041446d101e00040100701084c0c0e91507403901011450501400500a0032803166108a0b07040d280714007106405180900c0c00d03035101005134403001550381c0a081141d142d10201c18039051490903d9203110028004480c05241000b042c1d40110500c1002600302d2000c5a40c24000c901860800f102d1400c028400c0c029007070306941080e012004101818041c040c401081034114009001c50b40309420119643c100a1080c1d29070203103882e0001619510600c2500c0d07038401480b0351080840c400008000480e00003039011640966070782924090760104200d0100c009000c8030001c41c2d840000100500b040c044420080108608440f100030555180c0d0342d0943c1c61644282038118850f0040c0c080f40c50005800401c031034910000804981d11074000540c042441c0c04070810203a60703030b00c500c281912a40a030501802203000074800c0c404e00c500890140c034000c00c0c0646080d040950b00d844000030b40b035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 184787230 1250 184785980 184785989
    0x30206060103150b18040f020702010203030a0b0103021b0c09090f07062729090a0b03180304090212150d03052104060b0102010c08040209060d031103070c05010f17180f07 75
    0x1a42e00140000030b0070a4000c2d64007d280b0003604504140082e0000b07501d91100905440003595a0030305141e046e0300907819184291100c181c44441c007803240c6138281d60b884036035542c240b2610110700014245500010788a1a030035006010b00000703850041e0a64058a0043d189040454441003038072101c80403001101c014035442d0f040f005214600010b15402c0e141c0391000c0742010100b0003821103640c4800700355004442900c18900c0da00d0361404000c1d80e005240400c01d4085010000d00012036a417903401400350016132106994440d141c1640300e0321007d100e1624981c00607058040d00001c00e001b60050300d0386855002d1315040790502c0d00e81c1980801030846084400030354841c64040156424411129108080c1c2090035103800c00380c0001e0042c0e207004000510458200c48001c040510034828806002c2c0400101c5e81c68034041e14080442080ca4003442d400200b40410344c02c0303405d205480c0b816001d0a815031040141c3c4892055001c104402d00042c081845601003100610f070040051300d000780b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 184788480 1250 184787230 184787257
    0x50d08040b0109140c1b010603110a05030c030a0f0206130305060a0e0d020c060a0203120c0705060f01030f060207030c0f06060e1014190e04050304030201030c0507030206060103150b 80
    0x240351a2902032078150043c0c12054209180c0b4460322100c00d0200000da4208140b603180e6070b1610302601c41091200010222040c0c1542400c000208005040050281c0d030303d4121040d4028907218070a04d0303a180d145480c480d40c103030f005091200104050800c0741c982d40b800584031a10708050020038140070fa1403948219038690102d810455410080e00c6407605101440c0c000e80400c0c40b40703079070080d5104610354249219110010714061040e0007081161f28800700000310100500e070400300541140c0002c0010750f9240604400034000160380c554580c1031301d1f03001e00854000042c90710341c20000e420941044042c082006040c2d804212071004501c0700768421040032403090b0818149c4590143c0160042c807424081c000d0602c074504a081c0d1080e19210203403110004802e8884003020001819481050f00086040c141b0082c03150100007401074034000e072001e1224806031041200e5a100f0300e180540180c000001250790744d88aa0031180c0e0701c840701c001d0f140d5501e07198400f80400c0e602000710484031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 184789730 1250 184788480 184788497
    0x40312080103030f08041208070207150908010e071d13140102090f010207050303041703090406150807080720010902150c0f07031a100f030602040603150b190c050d 72
    0x100f640c420b40303455015a9514081d02d03036080c80d90f500034141e0640e19508060104420001c1e80701c2e80700300480303801801481501c0000b100c08002c003803e4031726980601442d55081042d84840c81c0400034030282100c00d200740d140500c11480399410502c02c0d01911213481da0342440403120200d054464541049015400010790300c50f12502000503c45d9030442c2c00341950040c00e030070004d690b000720507901101c8055442840386011488404d086102d803000702c65100380341c114040385c091501d2000740e01480380d035280c0d441c8540720390b801036884610894101001034035000f584802242d0b1100000b011070080c00001c40d00740415400281110030701d82c82007500d20008a04170f5030001080024020494151001d808e80d01d0442d11285907400c1301c12500080400d054001c41c400080003000c401c020a85003041b110b48540720719001011398028800c110019051052940d410080d8138030084c1107801501c0c09624200c6055511a1807004080b110f1080c4031101044c1130200704144001c010b00f4200340e407008030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 184790980 1250 184789730 184789733
    0x20c03120301170a031b0224120a110703031e090818180414070315140f060a0501080712020301140a1e0320060a11060c0c150408040312080103 63
    0x310711020483c00980d50340f02180d85008240c1180d224081040c1010001c4c00c00869070001c204040c185091100380d00d45801301c8007420f003c000c0040e14414000b41811049621041c3c8081d0035102c4030320020518010420001d0006802a0712601c001c0c000110f6203009c107402c0c020440111a0660425600e07568000743c0404103c0c0c540148940032001151942c603c40400005441007410081c030051010307035050000280102d081000308011030340103e014000b031504103250405071110210b00d0b0801025640071902c00000080d502d40700f2840603140603803440c40d00004482041d4007411680a10405a0400d044c0182c0350000b14060070aa0910307513081044101403101c5848150300582c14200c4aa402c0c20700c480d00341580008894101c11049040c00300e1901113074a413100030340c910364814400281d000c00540c10000307803540403c420041d03400781c0d60f81300f025420381d02c62100c80350002d82042000090b45580c00003001d4010740103003041810310752030f0380e41d04c0c0460701100782d01030114410000420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 184792230 1250 184790980 184790999
    0x6063105010906030c020a060b12030d1a040b01170c0d06031b150917030d0c02012307020a060e0f030a09031106122e060f0801150207050105030403020c03120301 71
    0x42c0208420700e42005015148440251070310b4001d00000e01c529148d00c1c8080041c1c0e55003512150012051003070325510070141c0d41c140001c0c01c1886080c5101d032000c0c2182d460320701e0148541c0d070b0f1046068562010702c2e104180700d480c2c100401816180350450034403200884c82410721540303010394410150015682980b007a11404c0780407992000030303003800002e4000560f95004a010b1701f10340d4006a21403030062246c1d000c41c20350264190440c03505180c22450100143d05405c0300441424080600318242d01250300300712015011100180564840c0c2c03001d03000140542c0c0515101412301d404d507154102c62201190a40c0d000051300300c006414010701f881404004002051480c408545142c60030201e15203048400c800105880702c1c800702c10000340401155000c00150321040d40f006409219140c0d20b0140202f0001048000010007002c004112000040c1484c5080c02c3e05400400380c207071810004490a41c4010411401c50194560151107510300700080d41600c2446042141c0f40d604103911407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 184793480 1250 184792230 184792247
    0x180c0706050a021e0f0705100b040b240a140307021e071d0901021216030b01080603031812010c02070626150111150a140f0606310501 59
    0x42d1030f4410414500a21180340c0c0d00c0000c0c400c075111850712950f045040c102c190003081005020f42c081d00604c00d1840c05a40d020710b100c15004c9804000c0307000c0c0c403000e00c6a60494501000d41142c400740b0050b1540304840040e100e14691490091104548800000c0d5203420588581000d03170310140c040000c42c042803400302070a03110040180042440d04800803808624031044607a5403c0d80710119040c40f8080d0103c508500c00001c0704a46410910071030035000d05011140c00010703240c00c50b030b00100d6101c1d07110140104002001036003040b114480c0750600e0500c81d00340783d901a84c2000c49020401d02070242082000243d000742c00e40d1490501d000e803031260140000c08200100d003c81e034020050700000c03e9000419892080201c81c0c540005a0300303080702c803074004524800c5c54400010559103008d104d200b1060316909001000220003900d410920a454404503001c4c9500021010700300403024101d1011310328201c0b280c07840c1d8141d001c4100344250000182c9011565024091540c000045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 184794730 1250 184793480 184793491
    0x10203091504030503070c1110090303230d0b06070f030c0501060506040b0d0b01050d0e0304050f040608030a052a15061504090905030f030c040603050a0c050a0c02180c070605 77
    0x1140740910740ba540051013440f004003075501744101c6056200074000c11211a050b12a03015000c40620710718500051f00c3c00d050752104600103420304100700074002c40c541c0e0351502035020b05000d42c14018001e8a640152550b85a859040503003444040003154290031812003240c000c3e00c400c40c1e60070b5541401429148641c00444c00741c0c90401c410044040c0c62400c9468007000303040000341001501c401215944200c4400b48071003170410b44122002c4030044010400c580c0211403040100c640d030020300c030503101e241c0708880c0182c00a00028103070138000d0000f0404458060140001c603202c0304540c2985015610490015500202900700c08040090741643c003c2021034007000c07004000b441e8402a031045020303c40c901a2030b03064020802100304251880102110240c82e100c0c82c04551109098100f0f200b107400090502c800300700703d400e80d481a0718680300e40c0d035543e5141c901c40800560700e081070010103d0700f213004c11820b029401c0300c002c1e038a0b000d0751040d154140d642e000e50400e2015900058032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 184795980 1250 184794730 184794763
    0x6270c170604020d020105030711161701050105010f050304030c0f0f05060a15050f0f04050a050712090c0b071103070e0601020d1b030e01020a15020a09080d090e062101020309 77
    0x284400f580d035003400f24018560900c0d00c5992035031103200440304444007501d003406a00c24105080c54940080c2c03084026141c1d07841c10410042905c81c2030398281d6100f0311410f808601002c88001c0000d1180d4015035005001c1d0900440d4581d081d9100405914032032030a42d41c0d0300c00a0440c0d001c020090140f944c1102074080c0c10300000890060480d24041140f0501d1310640c00ca0a128220b521000e10290040e800100308103c1c07460150342c9423003d00422540680001c1241c149202e40b0486c5100b5040c016410103800c40c1c005003002941503640d4006441aa8410030728401d5100950341080703c5400780c0301082c500c214905105c030002e49000141200a42070200d0200c008591030403140c481b180c080d40501e0701510b034840200060b4100a07008001820400c45d8224603200c0e01d003960024000c48100341e40300c50400d07907200b880b60384502e607120f514000224010b004120001051128607000500145220307603000d0306184404c03006d480d0804c03a070540d035008410400c0811003407082d02c540c1d084065 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 184797230 1250 184795980 184795993
    0x5090106020307031709010902041802100908060c09010c080a0f032f070f0203071401090501050f0a0e280513020301030803010b0d0f23011e0306270c17 67
    0x15401740c0b1441c109200c0440719000200060000102508035105031500503004125101036070780c1800d104070201c54242c0c000e08c070104010280724412181a4203c903910300103807600d13480b5410700c041a0313807001005504000104030540301240c0380b54010020484583c40b01441c2a40d060030180c169104c1c801e07410546030340083d140507001e0240c0c0544480340e203c1d4075415924040d074686241d8810642401a40520030a8800318541105090010000340700741c907802c0050382c0e107000455180c0f04165918455100034000d200d80e00d8040d0b20000c0b0509001031411090400f00c0d400c5015a207072115003800800e95141c01001203081c0266036041c104082c1809620f95030441d1207070384e028401132203a030b4850000003601c1045013145500c013448034842410103100c80360074800c030720410190031b0801e030f01c080d0326010000404003078614040d051100e0000200e602e0600d10344586004001c0c4038600d00c0d41c0513a000050140d42c606414583d060740c4500d80662503075040c0b8204201c400d220b0b00005c5541da2091 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 184798480 1250 184797230 184797233
    0xc030309010f03020306061303050706090e0403050702040e100c0905270c0304110a030b0105101d1003020409051f090509030d020c0307020406080f0c04060b0301030201052109010605090106020307 86
    0x19850708000e01a5060240c0e5a0306c503040030640c60b11403c94a08100c05a010300802009404181c0e034045a0701541d0b00c0e0700e15502d41460700b00051040c1c400401141e03041042380010b041c01c0d00102010001c1406640c039030072840c07800800f03031801c986043c40014188070081c00949489200589a200345071500c1b8a0701e100780148090000c03000c2e1144004502c0400000c0c100100d442c00219032080107444045519580d2410032403a00b02801317020b00c5072181c0781c0210440c0340b1809a075815501d4481a03040c0010745001030011001b04010326000b099000c000200e4000143c2c01014040d14440c138141d005100455000000716165810100700b0a040c6428882c0039240042500c84400c1400401a075802d075001c1c88034039611070110000c0d04141401e9001450070004151441007101c000203850b4a4845001000100c0e001401005411042800140059480386001d484541400c1c281c03131007900000d04080300baa940071030394101c15031b444060502c680e041007888513004003032900045040c1a103d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 184799730 1250 184798480 184798487
    0x1e01030b0708130609030801030c0e0402130b010e0a08070510181a0702030f071a0703020604111c14010c1103160602090d03051201060c020915030a080d0903020c03030901 75
    0x5030012080000b014003084803840014103c854042d0311141c1007280a100d85009403050100344400d0700c0c1e00304003030ac00088800005d0000b40c030840d4020000ca900000040510004010039030b002c7e810803180c0c1003440c4050704d070100101c0c0500259401480810328003030400101e01e40200f554010401c04040607400401614542800c1d504403000c6840421f4002084040034041d8400195151054402080d641070001c1280000c1d2000203a4003c55241c49540112491141c0300c002801a03000d400080e0120b80c51020f02c1800503801050100345549110428000201c00d02007942ca0280c40c1c8184040316109200300b40781c0071b0349828400c2501114050f443e80b240a0b0850700c2903603142d164842e1040004a81c12515541001052545000f016043c010203940007480300d044400c0404002007680d900400d07100341856401018030807140d803640c1401c00042c4103030b41140d405114441c1030100050302007014100f081d0700a5000141da00850070001c2c50b000c1e001c240c90340243c208010100c13103644e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 184800980 1250 184799730 184799753
    0x2e0e0a120f091202030a0206030f070801150215040c050d120e03010b15090a090c020a0c17071a040b0a0f030b040b0f060a020f0304031b080601120609140d05031e0103 73
    0x10030f80c2c8101c420018008242001d00500e002544000004100855202035590441c007030009995000c20a80e200c4d4181e0848585e10b410141c0940d20824245a018207000c0e8400d504c00d1090100441c0c141d0355401203a6010240b0904981070041000c1c40e414150f0700c42d41d034a08101040300207200d100307180000b00d0350010000421114001000a511209841c2c2d11002c0b0001c0c684c01c0030030480c0c058600002900c035402058102d50f0040f071580001100030707212000a0b030744801340b406007140c0340c40c0040307002d00740340307501c03a444800d50080c080051480015005002404060382311011824203580d4002c040712042a4000d10845c5410440401e94131642d00c0310000104c29540c03c3d5681519807000d1f480c1c480921980f942c070348030005020041045003404029461540e04100d21995180c1503c1c50321001d09000c1c126191140803d02404a001c541102d5a414040c01175800c071203050340d942c0d505106d40c0c405000c3c0070502c000705020b0180e55607090024a000541d1401e1040d5045070f03103d111010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 184802230 1250 184800980 184800989
    0x1080c160f050a05070305010b0a0801090b0f07020a1b090608010203160e01091e0314060c07020f061909080c011d12011104030c030c090504052e0e0a120f09 69
    0x100c0341c000a810420100495070781650400c049489031941c03441d20501a20b0340503689400340e000101d000030528014020010305903400068550b0039030320f020364401500300c0108000210301ca000702200200b201071100395003658070100f043c8030541c200107461080c5c5201d60f1040920fa8070400401c9080d480c9050481d146074918540395030060b81c91030049130b0710380540e0450301d18402c600030300d05500d0300f0042e031400881c0d02c940418050756003c1c60782d568032640212040741030518104903040061a24401c42204506c0080040d424441e094580c5954800c9103e02d00000c030f140080144182c802c04c000c000640c500074602251001d0782c5504080000880400540c0034210704074588801100039001907490038480380300305484695904007039841950506c015220702c88158408a0700340306c2401580e200325040002440c4500300c0d90565007607445000511032400c0b40a01d0721200840f41401000c038010207110080124051604002300c0b00200da03010101030049400d10360203442d802c02800d80c2282c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 184803480 1250 184802230 184802243
    0x402010c030e030d0804050111030601091208070b0906040c0803040f03021905120a03080a0b150c15091b030307021f0905040f0509060601020610140f0415030201080c16 74
    0x88001d15054401594201a0543c98051104000c402c260701001c1c0520607801107009200a1641100c0180d0701c0c823090b51080c1c00181562b80901540600d03008002003a4801c540301460004140c0340c4030100d80c401d40d00c015454002600740b10a205189268002401c8048003840c80c180c980095901000171070f210090081e2030701c0c1c00d00043c0303255030340c0c484008010217071070031205602440d503068032002c147c0803c40115241c8000f050110ba424400d101c0e00c0c560182440c20400071851003d10180c005100c502078500c1005075510440803881c146038011851a002000243c0709102030252440761806818080c2e8024071601000d691606500700b0611710060311000950455041240c803200e540c0c1043d9000b9003072421b44480500154402c0e4440e041c00700944072113880c1c00d0012601d88a0580700740a021120020901c0880d000d1a0071081c0c042004044080600d00c100100b002d4a10302c0c180740d040c9046c0c2030f00400c15960802d4006034010220000d0074500320141d600d1501207001c0e0308001d41074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 184804730 1250 184803480 184803497
    0x1e01110304030209090303062407060b040902120c04110f160c0f270513080313020a090204060315081903050f071202010606020102070812070e13020409060518040201 73
    0x1042050048401840c1c0160400303555140c4040800d5a0358026209140500c1500980c10f00c1c000030200c2c0c41d00c28850003a860340c5062600d03114440a0510125040c0d4000e50342c2005200580e1030b410042404424036000c0d1004032001400c20040319422014110007a074200500030a00c0701010440789501008401041c5080860524240d0054540c00089034942c541001181d40f8480b145140c2502410300c40b01091040414a18000d07100c003601c119101c041802c503c680050f0089010f5076001c01c468cc8507500c07504164000400c4032100754084850194002414002c0e11f40c50b01401c0010202c1d0703420300c164549042074041c1d4411300b0381d030303400f40c611030615a16003010322410444290210509209032204810300789114004441c1540c0400341d8030f86480040c2c042c2c010300a4814185e000464207081010030f080059901000078600801c1002d0503417461441e541d900300d114904040100c0042c4c40703134142050300048920a81115208001c0c0042c10142017074100750155010b41e082c64510f00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 184805980 1250 184804730 184804757
    0x6030414030408031e090906010305060402191119030f0f050427060504050c22080123150a0611010603060e0a230d081b03010905070206061e01 63
    0x18034090003450340c180c000000c0000380c0f580004082e05036049964559408010094070400c0b80b440b403034200c0f80c0c100e17910100041c400d602a51109a01c4070b0050405403401e20121003809183c0c01d0882c9000104140c000a448a180304000710200c50308104207440e90182c80351070242c480b282d042149003c2000d419a82984a0320410656009010a1425143c9169203d0100c0e800320648a04a22450f00d007541c000750510f454001c0c28013600041c1c0c00703a49400310039031400c0c1c05603500001c00d40340e0480d044800101d00da0309114402480e08002c0b1850440ca030710944000c800340c0003818010002100400c10602d41c0d4601c20f00d0403c850310303824045081140035050a0240126900281a041ca0050b12410f06400800c02400d20740c4290652443e003801c143c03482441c02e5481240c04110362103030302a400050f0240c40403641043d80c40e880107401c5500b42c1403640da035910903001900003a031038138180032482c2d030101f1400d0b030010b00072203140700b07d0b918540c0100341c5070380192000b504000041c00c0004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 184807230 1250 184805980 184805993
    0x506070b0f100e010b030708071e231308060106050903030a030c110d030507090b03010b1602150d0b15030f0a05130f0c06021c09030b0403121e0e0714060304 69
    0x4001c10f000b20b400c2500e50f94490b40402144c004882060200d284040010b0301e080c40740e1040300c2c0b0315210404848070040101300488407200c20081c1405444008580e50303000c4a109006010b1952001041c1c020407420003000074140001030380040e0501c0310501c2200302c06e5034048141c500c80e404034500010074140701e0000b01c0c3d61141d00301942489000c0c0311030032052281e16030003c030b00c204807a84580703403400ea0790310410301680720901c54090269401d000404030529100c50305074000d40010704401e801c0100e1143d26816604c00c0c9101d4100c3c41c2d496003490180d00781034121900c101190b22020341145810340da01d09038907070010040000f071580c1c0d0001030004034101c40d94081d070380e421141005185116143c40c4144010740d000e080094402d1008000000402c40d0100ca03009015545400031a455541c98068908010700210305000c8100320400810b09a44111054050f10100f034100c030032000a0600c08030754400c0010901500280e03024410b00401c1d055182115005030358080d5269164140390 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 184808480 1250 184807230 184807261
    0x2030a050301031e2009060a030305030c0c010e070b092b0f0305040801020f030105040e07030c03080306040b0d060504020f01030203130803061302190e06120a0e12040602030d060506070b0f 83
    0x42922041740d12004806180da4004552502c00340e0b0004556254641082031110b002d100040004178100300046c0b0000320702025190b0f0075600340010654072003082c07000742400e210360440c400c0c005c0007240d8013500749055845007007070304103942451002016415420721106d104820107012840743c441080d041520078806c40b001040e03074200854450844035408a610b45c4203105186c4034a041c080b420900324804601802103e03800311030511103900d10b40d42c200054000a1025500075039a041c100b00f1394540481c030051044c49104000741a241910421046000321094141010710600810410455000004031210342019041d0385a40c0c4010005005951700d900100c1c01c1d600100e140280812841100d500104082e198540b002c0149401d2120701c1c0160310b103401109100d600410300c0120581c2c40b404400030070206440da010100385400800381d04c80d038051030060303000040c10019810a40325040290070210740300c81c42e1002030744410344240b40192036200c1d00070941d000304401c0b50032210b18 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 184809730 1250 184808480 184808483
    0x902011206090902040509070506091009050d0b0403030e0601061409060708070c0e012c06030a02191403070803030c09011e050a0e0306070206010e060604030b0a020903070602030a050301031e 84
    0x9005841d110080c00d0042c0c58000300403070203507082c06c0225900501c049080c40030350700081c0004c2c3c14141803108000c03011003640c502c00140120b1400126a54071500400e40d4110700071007a600641c01c03d840d000341103601c6050fa010460300007000500041e07038000c22505180c2e15421095880325440d600203010b900c1181c0b002012940001444420401d11510b64000c44101d2042c00c48140c1e69150050069a10304040c2c00c00c60000c034680420030703001c4141c0c1035044600541224103004040e4040786000a03001008401c40c50b03040c00070003031104c0c2c0c0c17a01e81104410940181c0b6400d4030703001c1040d94038000900100d4400202140b07800d02a482403013004001f0310032444400a4514900700039006a100213511000240d00f44601e1895080008009001d0725040d4000e0015030300e4010740004070000501354a501403420040080440d213208001c600440d208040141c1e41c0c41c1a0041500c0c0051651010065400902c41148a1350f0044241c0341143e410041c0083c045841c008003132450b6031038000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 184810980 1250 184809730 184809767
    0x61d12070509010f060923060f07020904050606091303210b0303040f080d0806030307030c0501110c07080705010c380406020a120e12070c05100c0b0a050f0703090201 73
    0x34184c240c5a00c071200302d400f55242c0e11410358944214404007078180705000c4000fa00c1d0075030b0a8040c204400100860b04411690508100c8103034002190100195010b0b5915840581070000d140f404021154000c18801c1810005334181c0c4c2e0080c000c845902c1100c04041e2100e4403c00c8111080c0d0400310100300300400356981c0d5603c0d4040150410110300030800760b403040c20b92480d0518014502d41d402107000800643c1404241d540031030303007441000c2d0216550b540f80c581d0841c100107404003400b00c0302a0003001e481c070340b070910702500d2604406522a41c10803441c0c0b4001408114600c030310074554055016140303040d040c2c960003402c08518926440c604450004100400c0c44410360241507580c20596495408404644802c0d042d01c040c165004480e412981461510903452001030550300c0c4115502d245041c4d564000403103c081c060900d801107101d1114450800070070104280d4400038480c01004541000700f00c00340c0c4010000c04540034595a041140d0640e80240d8001140c0303800883d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 184812230 1250 184810980 184810999
    0x7030c0303050705010c0201090201090528091a030a0b06091b0304140d110706030c0e03060106050405031504050703020f041d0c01030b030105041a19180c061d120705 73
    0x2030002c0550b4012542a40d0365442c0c101341e400c2040c0306014440e200c54059445210300303414181000114900c0e002c648046100c14419150201c110b0b80d4070fa0020405110f00151544078400034503c0c01010f881414469081088091300140d15464000d40108080da00f404090341d64800d40e02e1003070080e00c81c01c195a2070100410003040900c0080d0f884c4522104152203180b40c0c4513100ba00c404280e4a4259815000b8000612401e44aa840604048002e02d0300c40d0984449101184c20028281c00400000c2c00000d8140304178101081141260300c40d0b221450b6451034261126600c0f4841e82c04005d00c50200c1c522041d09030760703ca401c8003030170501045026046080090003290303125128003141303000c40c3c100060b640c034616040c4a00c510803500031190b151031140b200d1a80c048480000c21110003540c20320f801540c1192a445010324610385840f0032240c1c24050304040c03008141e158002d02c1080954214000c242d40c0c46045810f20307103029110070703e1012004c1e161608000e080c1e00155040201d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 184813480 1250 184812230 184812233
    0x22103280c03110a0206010303050a0c020409060905070b0f0720030609010504120c150e1204120c0f030231110405040c02070f03112427010212070507030c03 69
    0x2584840724425240d00c0400074004030440461003806003804241c0582c00020040010a01405c000c3c50084180d140c0a20500c1581d80003500715903600e0410340301c00341ea55103071000f088000c02c08107000c3d002d22a040d605002c0201402c0c0b040e4840c01d000201a240c586644400f61312a120300c001d21210010241d0f800c43c501800900d00030502140c09441d100c00303038429028110300a2007888a0507801c0b8100301c2c001c850307005070038000d04042060b0000c070b4414200c5000d015030344a0040d00180c11030850018260156041403422038000b41c0010182010351841000143d649000a48a0845a06400311500b10ba0303280b1840c1d05d0301e81c45040510908120342c5070300c0b8101050051080d9141202d00f04485020400220381c2c0c2c0c0024003a010580150b00d5007400070803410889400080801050f4060007010020440e80c40c05440346840d07400500403d00800360003200d4243c072a248441c0d0306142000010000007075075040242287d000d070240000e42e42041c030400317000a602071078020310340518440c0e0380e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 184814730 1250 184813480 184813561
    0x20a0c0b0d141501031406060406140409020a02061504060b030f0402040f111b03042907320105090304120606080607020606120606030304030b070513061e022103 71
    0x90400c504e0000f440c08211440060000e41190b004079400b0348100e0415041038801c5d251000407120214622105000c00190f1040c140020420b103016940580740c9030904030722104901008020b014400d81c00c005082c400b40a190301501d030302903041030940429032a640040380003400e074541c00f40146401c00390b07813080c44003810000301006040c0d0001400200096440d1688a014502944a84800401c001c48502021540d0040c507a281d40b010030349845800e54074011000098240b92009401400c0a910704030202c040146408540c9402031010f45450800240c0300c0c030039030003800070100740555180140101907000d1000b900d0031400f1290241480321001e5510344c0d003103440740c3c4100e0100031480001080424128025a4054015810701e4207590f5598000800100319004100d000d100d10303c04008185030010041146803240c44a006440e02c544003908801f019400a66009110b03c1d043c1e2100e20050128034080e4180c281d48a03217034141c0c55406800402d8040c160005017101c40c04c3c02040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 184815980 1250 184814730 184814761
    0x80315100201060620070909020316031a1f2d090501050916020a030e0609040507091a0a02100c0302210907060903020108070c0311030c0f060601020a0c0b0d14 70
    0x500d484550f103007542c9030390091791400318070307008101600058402c10000040703420658400f0320080a0711241a090403141200003d25441643c0d9040550100f13601042c0746c16100b500304400004450785601008041c001c400f0b030600c40c3c40c0030b0081c28401c08629000c4030703403411090742048071007035101642c03420030340003138a020f000e12446016480d0210b903481c03c407404d1a030324600c80c607000f070b080740b8034691001c0c0c0d5601e00121a01d03070004020880c4071255a914410300340708002940b5042007150811400565049000541220211040107054400d640006604203032a80f0884045581c4900800c01c030040e0003501841d24507580415065460b4007a110a000d03c00e80001c011950150741d901812169459a448042c0c0416010400f04101ba44501c2184070b0703040c02410b104040c1481600306610719440b5034481422600105840e08a90a0034091140c00c0007091008042d0800e0716280c0c0d180c1461981b0a60080d0f00d8005801065030a0743d0300203a42400841410220a180c400a40299000f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 184817230 1250 184815980 184815989
    0x606090714040303111c1409010e060406170f100302090c0c0303270622050f030408030903070f08150403020111030408090913170a020703080c071e0803030408031510020106 76
    0xa01c0302c840303854041c659085868554260f8824240c1f80c2c01c1c180c181e65551050070074504021031800c0031415610b9410003800102000e0f41e9504030a4140f00354a00741c0b070009401d04460100003070902460512064003141941d4049641c095140c94607062000700d44140400391845000210402400950031304401052021820071180b80322417100020352101012201260a02c1c0280e45818119026080310307000140b04004550f034018080044a12310b40055006050760b03440002c24900c282401c0c4441d00040c41d4203000400c0c0ca0303042c41c10981d221020154812404400d00700041d05261003500a4166041130210319940d03418075040c424856402003518500a14440e030100380d800400f80d0580c034015800200240c00401c2c911402038280d803085003180d045210b80040800403440440c003c114009003400249481850500340d0701000055215150440305403003400c0021000201c2281d44c040e03480003109036a6a666032084840101010317626401c2030f070b04904200f00540541c0315109a6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 184818480 1250 184817230 184817233
    0xc0f0c0118110306090303010303050f030a090f0507180b060a08041a0705070b16020d1101090206040f05090f0c0a0509010903080a080108010509010b060d112104020901090e060609071404030311 85
    0x17940c0e40703403074aa5071744000c1c23000400040301080007251020004000d180c010850703410104004100351100d503101915503d0945542c1c11110041190aa0714480c006500000a609006600025000400902882c2035444c20b004000700001c0c104100d121b9504000f03004a003051035603003070400c0f004013107070009601200d80840b8a00440e8100010010201c0f00301120b500400e85c04240040844051b100146000c3c45503498405620041c0d48910141002e48032840d00a444070340741004009007800701402823110b41c208802441207802e094011942c00300c1d583c2c1801591414440c0040328052240d40c80903110f002c02140742c00c400b544c4812024122100c0500a200c940c482c880d203a0b080300e414103002540103108102005502c840d9801c800411030b11200100e05200f0700b401009111002104800c00c1403004000700b10440c9001c51516024100400040214000d43c00802e41e5480d40500001c2c4204819000038112a100320407401d05e2038040044a80c845540307180240640310800112002d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 184819730 1250 184818480 184818493
    0x3050106081305061f1502011a040212072102030106020309031c0c03080c041e030318050603040807020a05031609052a1c1b12050c0f0c01181103 64
    0x112803042d42c601c02c04540181c090000740e1030304418130000c4d1444101e11140d011480000107500d030065034014214440c01d0300007190a030380c400030103510441050030052140b841030244a28140a10f04030303070b80c00902070821008103010448071940e0080803801d03141d442400013001186090780480946008001a02258040c0d079200500021510120404034009a001c03042d10000c64820700300356400080c03100d00c5901c1c3c20303100d07140d0700244031814840a01c1d00803e130728100201031f440382542c40312050341c1600e0300c0c0385824480015240d1001510141ca031540c0418918155650350a1840003420000c0882c0c441000e001c4401c00c2c514014420766200da450b00000500302d209111524050140c0c10191a06001c824045110960041584035000201480014050080c184100b605000f83c0da1440c941c0f804805900410f00018900d42e0300c9494140424044110307010402c0c2c03a101d504504500762140c02d80201c0a005000d5038410595540040111788140501051444c2e4040c000b03030700b80ea55 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 184820980 1250 184819730 184819741
    0x3050a08180d090e0f04050d030c03021312030f05030622022214040e100c110d03150506090f10050d050c030915070c0209060d050a03030f06120327050607030305010608 74
    0x140017a0489014001e40c00007043c3c100a00e1003076000740c0406105060060030714a408030042c0482a46030402c00d00c244010141c802455009078180f100550540b40003499440d0160200d440550700081040740f607182c00c46804c00718021138040e00c428a4900c8070300c5c2583c030703000700880c2c5030f1485500c20121480c0003d89050308909040c02403020382d0000e80c0c000c098150380c44030500010b20b0210000b80802c080614002c038143d1080c04202d079007512a83c1c003c55180c0d5000341c00c0803103941c1644450312902d0208101d01702034484000701205008100c5080c00038520001c000d841a20400c1c1c40010030900e080c007005a20040040903500039468442200c55280603846001043c0c030080d50404041205c040341480180791a240540d8810005043e07044a80056074985140c42c03850082140440d45544135002e1200251003a880203010303011000640c0703903098070080c081c105900b680b04048280c0c82b09141c0b10400502c0181c00a19000d0061540c070b40c19070800a0040c6001e018020001e02e89070003107035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 184822230 1250 184820980 184821001
    0x1c092108220914040f110a090f15210606080703050115290a1709030a17061311040f0e0a060b07080a051c0507031a03010903050a08180d090e 62
    0x403820341c41495401c2030384ca503500c9500341c0711401503044034440f444001c410010344074000e0300801801044000700e1202905101e600a455404500789400400703088100300c02c040715013280e00c007a15800c07882c104981180c00c0c4400601481d421895107031080b040c0020030400154000c3c80180d0080ea070b2480ca068407000c030003204418030701c900414100c200c3c2440c030414803450002c1601000504000600000c1c0286000802001f01d42075401600045400f80006804c01d00d00008042a4504d110741ca140080c0081d0209801003101050b456031109140c120702c001ea0120b8000d0580420081d52480d0307100304008003010115020f580c00c6040810008101c200242912030303203070b401100c841c05d080d4000400c59207a04204402001c1c1d4403900d4028030882082e210304c46c050701c00d594010410503034101c424940c203030003071024602070f0b07240407050300101e6844410b4030103050b00f524280016031500d80b001c00c0c03c900019500b0031140140660302c540e0030b40090180c03048601d51095401c1c1e030b80d6211b1030031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 184823480 1250 184822230 184822241
    0x203070f110c0a0611060a05070f030929041202010b060711040b13051b09030d080c1308011d010b0f0906060c010203040f051c0921082209 61
    0x1150003205200103550240000a400e9114101102c2008440400152940d4040d910000100300510112610300f01d09120a46c0d00c9980c1403814080303410451001402c540f41403805030100369481003102c0c2000144108001110240c07640c442041d4045e1040c401181400e44040781c0a0071051100300026006009035104000001c2071b80d800c120403a1100480800d150100030750003680c4e981c00030076940d12440803c201c041550780c0042c05103010103480f6404503021051001c40407050003400740c03d680014428110030424076064200b5150f411601c1c440d401084003c10001002040c08a590101540805002c2c6d43c00130000c00c0110352803040300d007240c0030052030603040303514504405424140103141c141c20040241c01d00380340010315540b02e400c90b003040c1c0c1e046551488848440052000400000c82072505c40704c40340c1c1d0300c8000b2401c0600302201921584480454101e801a0394031000070320a064150448403155640c000c44030100c0c2510302e101d21030380001901140204582040d03200c1e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 184824730 1250 184823480 184823491
    0x601020d020705040504080d0207050106171b0f0d08030a0e15090303040620120103061d10200d0c090e01080c04021c06030f0605011401080c090d050d020c0102100203 73
    0x10b00503403803d01c1d0500c40a000b004005942c820010011680d0380d4101d07100924216000e4000064111300b440c4e044500440720314408000b551206240305030b448601c070050030901d5422560110843d11400c00b1582d4191a1500a00321010110400403503e88a81090504042c021f050b203090300700f00c1851100c2a842030701c4400780ea40c801d10005000507056444204101140300c10b80c2c03010f64503200350449581c00f4034803141e10070300c40c0401001044102c0c02010588500c1c0070088041c00414900107170780e04c03204442c00b40d045440d10f0200d1002e402c4200041a00c4201080d0035541da98601540e80242880240e68400a041d402c00020703080b13510400541038420b114080d15090b40100c0810029401c4407040300713180d055603084006c10145510a10b0000e501c00c0b2455040741a40c0d04101c02100c505030b105400e0300c051258111403584c0d000c0c0403558400e03501c1180702c3d00c805055000c2500b40c406144028040d11a40c0346000c078a9030001403500e04088244e00320303883c18ac034142c034100690100307071507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 184825980 1250 184824730 184824733
    0x30103080901050706200a080c030606070210030b0402040e0601020606101d060912010e0709020a080105011412070206150616020120070e0117010e060a020d11120703050601020d02 79
    0x10050741c1d07600c904014504503014000224040c0a14520210070403440b882003074a806000551100650b00182c120380c4c8506010700d51030031071400901003001e0b0b22a800c1e009100343c01401d42c1580d8140243e201d202c00302009031045445946449480c0c184a40503035030103000d485480e0020b404c030328000220200442c03943da105c0030b00300d18401d039242190700364034072881c2c4c000414044400c0381d031144042e00f06111090307400401c000007a10a20360628509401640c012801084450080c80d000036017941103c07000e10f440e405600d03200c10242120302500d80038405440e82002030007003c0303900181d424010100940801243c9000c4010008284560f41044600c0409a00b0200140d03004104000e114880ca010000c0028410a500c5050148940140758515003510050020783c0303045103541d0103405114007c120300c09120f0380307455545070028002840740e0340000311100003445680104407101240c4070030a0b00d49001c02200725030701408641040c00030380f501d13000402641c400908102c94016680 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 184827230 1250 184825980 184825987
    0x9070303030e03181e0402070c06090806072307020d060606091d010902160b0403020a150c051615060905010512010c0906031812020c0a0e07020c040b040b040501030b01090b0603010308 81
    0xc092100005100f162405c035583e5400200003152610300003040d03454400d010f5011071604240001d8071307041e034680110540d64080020020300c180c0042c00c0740020b10580500d00044400000c940b4403a00c02c0e0240290000483c0d0f001c1c104016458104100b913403104e031908c403012600c42044c040040c6a80d070842c01c0b040241e80041010007000d07402402ca044c0307907e502c0c03ca500143d840f0f44081d024140d0b01140140d003c1d524600903c550020410481000714205100c4e480d508071004106021710540e4600d1001180044020001d003110007004050103030b5001e0005564aa98000080c0303024401d01d4012100004100c09042041c4120030725594151201d191440c20510704800a056064120410070b040248481c00710340060300c0c503580c8482c0c0d60b0045c03550300b9064040c000c68078555808103004a80c464284506503801182078500200213072030008010301140d001901906018034640c1d0414507040010090000c3e941c0c0382416035290202c00e00022481c04140441403009120142a000051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 184828480 1250 184827230 184827277
    0x401b05030c07110d1e03080112020906040506030f06160e041112180102190f09060801060f03110a030605030712121b0606060809011d10020a140309070303030e03 71
    0x851608030b81e103c0103021035007038108503542c8041c0c003400084c1c5403403010010811141090b601c484294050306500324031017490260340c1c0c00303d004480301a040c0c130b103d55151000299513440401a0065408240b82182d40b03070704100141d9141c0c03916005d04040095612103220440d810240030301c84c0d003280120003180c0340400c0c20022510040e00502000380482500300030b0a4003041c2400540b405041c5000050300384170320340c000170300104030f0b8218200c00d004803084100009908840501c0c1110000d003040804a9240401280141701000100da40d0440124400110079495032108054560903411140300d607440d00000310101e01500e46c0207100a8003a450441050b108440030b03482c6200360380d800f152000c02582c8100540c0e0303168000d400090368140800507a0582405455804a40c160a02d440d4140100965072611b040c1910042e1254000076041c1c1458461880c80d5000b500c9240c0321912810003801007a2603880324070059001900300ba04035410500040200c81c0c4035078480c40310b1940c4100c5c0c1e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 184829730 1250 184828480 184828493
    0xf060b27040320030c030d050711100b0103180506060312042d08030d091b030309050f061201060906020114150d060e03071505100302401b05030c07 65
    0x4124510000e0035000b900c912103c441000540201001c14000d141c41c0c03452a03494600300d44005001104000208000141300075000c80d01940d206100c4038081107016246005074081c00c01900500e80716074903c1c5003035090000c040340c9a4000d4100b1000d403400c6e40c3d8103454042803030066005080f4091044095030310703001004540c240900070000081aa8650345400e0300d8210b8000c14039245010791a51217400030407803021034208000f5000e440c0080c40b41c0c15a100201341c100300e40561401007400001d018110764a03c42900c0103000712440c000590740e1a0305004080041724410440550f0a21004881000e1f5000d0a588a5440c001a41035900c0c801c03000c00200112410007543e00355551005a04045014401002003501489460300060408440c48086410007401c0c40c0e18092466028030042e5036095a00c0090111901003210b580004445036104c20f20411203148102a40d0b6000b2000320081d40145101c001150410a510f4640c10402e5805200489210024240812070440000e81c4d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 184830980 1250 184829730 184829747
    0x20a0c0e0403140403080c0724050d0e0a080a140405010e0904021201020d020403030e030f030a08040507080625020a03020303070309060b060703030b10030204030b06040e03070f060b270403 83
    0x1030710340126540314000c3d6001580d8481d0b002500c4400c0000344120303501a00700442801402082000d80c19608040313030313190030002ca03142d184040000c0065840c0c3d0703410705038001110340c00d007400c2a107801c40014500381c6802d80c0080e11403000328642c00700c80b04603038008800352400c680d410384800e00201d80013010400e02c91002003080341d0006004104a02c27111091002d024071240001005a480d41141800f42c04000c5404590f4840c1d840b0b4644840d43c0c070701c04810349400c00e82d00d003006d42c1c881d1241d00d01142000000d40061030700384160820805035102e03011a61418501c3d000300e13600e46c3c6501007022629010a80030250140e442003010401c480e12a5003e21129401080c0002cac85c1d041043c00030341a640560000d83c000ba8803548200d8071460899088105003049090840c601890740c0d41e9002c3d2070340010800c5101301da880d255a03180c0341e010b0044035072151b840100801c4036040c5140c1f010003400700285560044002580100000054aa150380c1da0514401c0a440300e540c1c03503404644030300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 184832230 1250 184830980 184830983
    0x1514070b0405010e0115291b070b0c0706110a05150c070609080301090c080906072a061a0609030a081b0610090c030506060a141c020712020a0c0e04 65
    0x10b60303c1c59084c5442d4000c0c843d001c890b4012407080301c0154582100e4410500d82e100d6900c01c042c08180039880e6812000c0c048030318506040341b24030002140028124100002c6038410307080c641000071b00007940314000c00c02405403070780394807036150040411910030742e20700307165400404c03a81c06500c5184d01002c20f5401c03241e00c4607401e05010320b89045951160240c5072000d104642e40320f00800140440c481e41c0c043c82000c00003c1c60310f041a45001e200242d99004080d00d210103000d15007940385c10780c00c02180040321035908000c84944520962510800422004d0751244940910781c0c94115240380584c119a1203500041c02054461940d448840c2180d0258440c80c4114194103114803034094107004940c4a6500340c0381811305036103488268029a40b016a500d01014070f00010060f10f59103820640b03040d082946400e04145140419801d450f00c141e4801e13114007a800c04641c401c6072016001400e48510403030b03012640000d07202d800d0780e680200041c0104901d4009500f40800c40242c418143c2c0315 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 184833480 1250 184832230 184832233
    0x904050604150803030628030f05030d02040605070c0515070803060406090501030b0711070308222601060506030112121e080106030c08010b0a050c10020f041514070b0405 75
    0x6002e090002502c40c15541c08049a90004003c1107980d14002d01803490f4514181c440d40722a070170035586484000058000100285046004442480401c10903151094000e0304115500d580703401000d0000e4200d001c08507460400d0340400310b09810b0916a030141420318400d02803c1400560780c103002030700020105030b0069650b8000040c903129034010940294061038110b0b00c80e045c650780c0105450900701901145900c4000c3c2080042c030302d20202c0c3c15441c0301c0d400002204e0103c0f00d0000c01d154043c1c2c00b00f10507140880c0d440c2110400504840c07070040390100200141d550721014001207000912a0742148690b000555000c0303100d945c6c0b60200ca01e800d183c208542121000340100300922460520009404203005100d880c0c0c00d44280e00e100c201c0790030300042d00d61402030326007034920500d109101008004103004c01024410040507945544091066450312101a80041c1e150801d00c210841d010300b043d4030308680c45c040c402700524181c00f80d00e01d030b00d00206d40e240d112a1040151049903503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 184834730 1250 184833480 184833491
    0x20316050a021c0318060e0405060102150c0307110f070603020c030c030304060609050f060906011b02180a1401030c090203040c0320010e011b060908040f061707030608030904050604 80
    0x103a892001c1c5203500b514203a411403d101c0941001440080c10040442200304c4014051264030b410000d4186074803401c5601058a03660b42004030304002d500e200640560300031500b840460800100610300c2041c15640d43c40a000307003500c03101e990b0180810801c4841d0440a0b0030b00c0000e10a800520400100308101e80c501200948000d1440d0f000b1202a5540c5681706d00501900c03640d4060550088a140140346490410341e0010b4920308001c2c1526060040c121410140030b2500e49401c01119001055252000600d00d05900803013002c0721122107030751911003080440c0c00e00026180c1a00d4121303243c01c41d8a0b00303100000300258400b52080e1618121071a002001408400b01010111410100c01a51006120024084041012040d03042c4404420030b100c05c42c4e035100c51100d0035604600c000c03d01d04800e0903c041c0920442d00209400c0040e6500482c1181c0c12000c80c1d42508640042035500796280712046048600701d006030070315a04204912072291400b60071858001310300400c001b96 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 184835980 1250 184834730 184834733
    0x3020703050d0203030108190b060f030c031b0405070315031202101e051027110310060e0102160303030b0a0b212203050a021501030f05100c020316050a 67
    0x182c0039501088000680c8000010b0180c148140040074494200c00c3c203031200110169a05001001d0080030391b17015500000f0022407503a02001140714121020382591020a4024a183c180f911424038640c01a400c000c085007409101c1c0c81206440d6019007507110056055035a0f001a400c0c1e4032880c00c04601c640b0001346940c890754850740c040e009444003140c0e401840c45280c2002e0381c200414406500f4000c1104200b120b48501c03c910f500b100f8440c0c2e581690748a24103520042c501da05407401100c9001c010800406040c4600380181d40c065221201810140f5004a85d1240c0c190f000c8418000c2455040001230300070b800c0100400301c010000d0000a03200c0c08a034900b5013000e0843c07804658403507480d2030b01a030340e1024030f0381160041224104091075601e084880000f0084010108080024000c501909c05e101e401da804d0400e068004295940b0708003241400c1441c08151000c1c0210384545003113606503c21050700b250241c01450030b20f26003c90800c0844400c2c1010749403406503001e02d40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 184837230 1250 184835980 184835983
    0x70506210705190f050f0a021504060501030b0f011401030c110d0305150906032e020723010b0a0512070506030a020307080c040608060d0c080f06090c010c1703040302070305 76
    0x144540003903039480343c0302c10005000f00c2158409405490a004441c203e040d01c40303074044111103180d180c00d1151642d48400450407450100d544141c0250388061030244400c110749500558103c0e40035081c41c400e16241d849400c81d8010b000c0c4a038100102c002071002e0540c0d4041c0e007000c03a505095040031034100d421034080b039081c00e6030303446000c002a40d1001004494101c00301d10030903200d000d81e4280b03403d2500708007013680c81c076030004071400a2010807148180c00e0381c890007050030070660a9042d520303207055240c40c02a550407130001d094080c0007185074200c0c1540500c503440003003100800300c0d0f19141c174010602c1482c0305000f4080c1502d0040c05004075851710f50710011401030380c10301001070741c03480d00f80702c010501040508200584201008200000b551058020740c0010b0201d5101041c0002c91421034802d4850794810700c0c581c068400441403808000ca41c2520403010513050720700c04402d0000441c1c40b00300e00c0e5001402d0540c035500c083c242040005c040e41e44030b8402e00449844933226129039 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 184838480 1250 184837230 184837297
    0x308030702011b020c01090504110906041203030606080402180c0f0a02030306040606020c130f18030206040201181809080706060806250516031e091a070302070506 72
    0x120140c0e448102c14281c0b000c3c4403a50428180c45440604001d450f080002805180036100c1d50b4417940d15440740f60303504400b400440301d10600061046560301d039946005200e01d2000b5405030046490170f580091054001e402c401e1007554001c001412170404519200c080304000781c4240c000706010f003c10031006012800800d005d40300d03900207503203034a030100802043d41e00c50303000002190802d00d0480d001f5103904500c0c0035450300ea11340c007103800138070b48014a0041c41c4a080360206000c04104550038141c01040301801039000303076074800e5103146825040c0b42c0241e10b44a00b000d031a0010035035205000c40c0d82e0102c03060511914120340f802c0950780710304040c0c8005270402041e40d0000030511000182544840400d040c2030b20480700340d219101d0f006403660150f9141d803546140d640001b401050312468003600c8000da0840321128003659100000c00c05c03c0d050103a0948118600740031814040700a0603107140c507a1690082c07440a050100307104075038000402c59182c0d000c3c00074031070b004030128001c0e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 184839730 1250 184838480 184838491
    0x70609060513020319030f11281406090c0f0303120a060501110d0504062609030a091a0301120f05060c03040209060409020334080d02010b030d050a08040804030803 72
    0x110010b000c01d401054100140e69038400500b209041c1e50400183e0480407400c7c00100030b08014282d0051031020505042d07500e503050040c4820040f07010003070003d00000c24000350003240e50a95410014540c190303110001d41c1d1009040d130241d00d841110346044c54100d00443c81c0036080c3d904003c002e0b040c0b415025026154103907a251555411301265034001c03101480b5024000040c07051310301450015041d41f0840c001e4400b0440c642503060354a034220b20109c0e80202c0091b24905003851311040f6039850750081c00c0c0d03100c000b031900c21000440503915984501c06200107842c032403840c1d10f42000d0500c2110609030854800180510100110300c06120580c401d0208030040d541c0ca190510421002d4500105803034866460541d0400c09610002101d04c981c200c4400146028a8200c0400c121940100a14545009102c3c804220560080740d80a401c4681e0f400900804000b0401c054031b5200c040120b030001001480b00440182c4201b04650b00705000e802018030301902ca4071054a2075100b101d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 184840980 1250 184839730 184839751
    0x522031205070e13061d041a060402210411062811070305070f0e090d0c021c0303060f090203040b0f04060f060308030711010c1403090f1e0f0d0905060706090605 71
    0x7000c00c40743c5d445050071b902482c2c05070325240a525150340d03030031082c290070400242203003a06130004039242c881c1e82c1201d07003128003148005001d504071018440341c54801c56007140c0400071400b100c10305051030402d507589181604011070003c4501e90314080388094841421080180d4650bc503080400c00344580303409140508007034281517007000400100a000d5620910008448078104501030030b020030404420304007864841c0c000d140300d00009020004003168404020324180180341050307050b520540032500d90150f4001c6040e80c54030036008a00040324060304070103504000581410004000c154420b1184400140703141e81e00303005400f2101f20b900110380c006400024000300f550440d24045003603003003000038080224508001000c9000e0145aa62500d9012010030b0340348600380043c40d00f48005104070384108158420320328024004103032105047c0206011aa0400c42c00b041200e58048247c48002c0707141d140c4010b102031a03005580560706155070743e41002c0090b0302c60051501030300305c080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 184842230 1250 184840980 184840991
    0x14030a060b030a0f05071a0f0406030b220f05010b070203032208030417060a0614130605150910090e0f04050a0c0e07021213033002010522031205070e13 67
    0xc1c0c000c49100e00c440341828030500c0a000c02303c8036400b8401260241d0b8500d207400314802c2050800f2400303d01070340300a1000d813000030110444040881d440698041c1d01c0360428422030340d950510350801e216402c2c000c0e4068108110040720302e0544130500c40107001003045030304050b41d2614110b055030015040303c6126801c14842920f4600d0030040990030080c410402c100c000d1401e00842c0400440501513801070010103410004040d055011200420028081c80020001040e9120081c4e0043c64024810b140d50f18440e21401d20524400c400d6501c0e4042803291502c0300086240c840f040100200c0d10b51080d0482d20303000424102e02103004007080600501d05042c14030303003c0e003801140e8040c80d2100740d003484600d030030040c00040c0504a0360802d01d2200014065407101403940310349100d6544005207000303419210b0703905500c0543b1a490310690198410b0444654240f0b030f116201000d00040c00b04081c146401d04a588a550484102e080c00032118200102040c0c4e81c101010000310003643d9070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 184843480 1250 184842230 184842239
    0xe07030903090b03060102060a150f1806170304120807081b0d030c0e06030402010e030303010b2724090a0e040c080105060901030f08071a04020a14030a060b030a0f0507 74
    0xc0000009080900300c151308526040c00003e55400000304403610954a5210941d4400d5090080078040d00c3d400700641450380d00c0740c401d48031021185013a408450300d800b00018001480c5140c1d040071244481c043d618061402c3da50b9031115050b40c0e03003a035542500700049000a0303600c800501d0302100c0c022086040020034200c240c1050300f841e00d0042418200b180104450b503000e0000580118200c42513500e944950004036104920740014070380510000002040f00480c240c0134140c48480002c0281e4a0b0f9200d003000d00708800e201010580201c0d940888105141740e507401d42d040150f10104c00c501b440c20100c0003030119040d0b03500c481c903100308010900041c4800901e5010207005003000a0100e810302001140440605100150110303209a010000b0030441c903040707807002d640004814007a6511840310754443c01050350200d104a4810320001150500c4221200c2c01100050181280080f1a2a03c83c003808111410b140c1c180540a00b01c030028888290712080c0a011300c0040100a040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 184844730 1250 184843480 184843487
    0x6060f0d1b050a08100b01021c08131719031506080604110310032d02090a020f0406091809110607051011031617010501320903010c030204031e020a0e07030903 70
    0x180c0b0306c440c1107404c125001c446009030031944503609100d9192186c001d5a400d03d075070142c1d1100b2035000741040c0a084035418014a40d001901201d588114800303441c060300307941a03040301e03c1451140b2003030380d080008100b074038043c41e00305901c0300d070180c00403c072200010144c0409610441f103030304400070008418000d202d0075072005c1d4a18010000030b044500403d240d030100352800100028410920741c030008980a400740c040c2c1d01c4041c0002183d41e10b03603071501400303030055165020350310081888100d8040015094050800702d181c00031291400c0b825035030f05200303280d888004140c901d4459080d080c89905c00d0391150001e02416002629140e0600400f01400281e010348180704000e403080f4101882c40c03030340201e1411501d0900f8010074800b1480ca40342c59401400c1014858942685000c00c041d605000c010921600304500801107180540300075012402a804060074154030265910001d40c4041224009503000800e0303120b01558400320301a4202048955200082d191500311042541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 184845980 1250 184844730 184844741
    0x1060f050f030105042a0c0b0702060f01141801090c0e09040314031509040f02040609020f0f0708040e0106050702150c0d0f0e030a0606030506060f0d1b050a0810 71
    0x4145400c07450424120207200e010300040c0185803041d80d6603080e0001001e284007054400460b1780001000c10a500900684590003e51080da540d20f2580f0000711032500c0403590602c5812903040305e000c507908248002004540e550800b42d001000c000c100407880085181d030600800f540d0a01003000f0011640c0100408800c0e0603081c02290644140000660000e0990802503481c0b0000360710703507490320302022034411401842c0341c000c107400b4103210074440186002c0d08540e009540611940d6034a0071010120f00c6220340c032103054401031003d10240740c8400c00820095000750100e6090a171280405101d540081e40304002007940026840c0450406010a0006400000d241d0782407201c00210a9114664501c1202c100184100d040d8102401094100542c072006012501c2001c25450f0500082c07410340400e4566101e820000341144c509094540401040601960030a0b0010f03604c0041a0344011a480307004550700c440403482d9115601184000c100800042c100703080704e043d54208444 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 184847230 1250 184845980 184846007
    0x50a08010b181017010203070305160c0b040218010e09070801060b0d090609051b040f050c090112020906030c0702090f04021c0c03080a020109050609030c0d110109060c05030106 78
    0x3410100c0d651031640e11280340d00d500c000a0864040c807035840c1014805440f0064000c0940c44424442000d01c0a2055026500c203040320f403410083d541750341024120400402d10278000040e0b0444403000091104200700340c103d4030207403500d254614201440c903004682608214806c52102040007000007003008004020120007000304880e5023401d0342c14445102d9008089442d03070315007072030b0020010242d000071500b60300001a900c41850040c80c0280c00d41945450714403c506005012450002c01c0c07040c2c40c040c1007545000da240c0101032006480799990411101400740d401e000041b41604d03504000d43c031680041040d547e0390783c011301c1002403080000d03040c0e0300d01d0f103200380801006071104c21143e00f410440c6018010320420500c2d0444814819800042040c103000c149103010b160150011601c640c070403400e039034803640d4041e2590703903900451012032910f502052210b000725005500d40e140140509001154008103611164140c461200c100c9000841c00001045505d034401056103120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 184848480 1250 184847230 184847233
    0xc14040b0a03020306130e060106390c0306051e0903400e01090506030a0b040204020901171305100c090306050907030c0e100911031506130906050a08 66
    0x160806405a4060007502440400d0550000108002d681c980180003a1031000c05010702c070000c3d003245107d4540f03d084c820328000c500c00500c5612105c6d0044613440c41c7d50108403003c40d03111902c0004c0010344c418240706445010300b4500100c0460000d007c3c0c1842680c0e21810300c00c510200841c402c081c540024501c1e4051340040c00404622086209054a0560324908062070041a40282e048a0341403880c543e00e8492103600000e1f0b01d2190401f45412200800e000300050b548240034141c86100500c001007080c51a0000030700145065800703040c2510040c94104000d000f0750020b1080701c0740544051380d02003040070b1004100503040201c2401c84100040030701c5481044503000d0807d0f500b0f40401009280c0b140c0000e170014a0400a50340203680051106920540d80c00403021620b8094418005106540001080180f442d014000c1070b00309004074a403075651070307034901c4c4190081d2011581c1c1c8044100811210810111142c0f40901a90480005d58030f00e0002000f150102d6540800a83e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 184849730 1250 184848480 184848487
    0x20d030204050907080405070b1308010c0c080f031003020d110f10051b16030f05060a0c090b09011e27031211010605100903030810050901050105090402090d03030c14 73
    0x6866141103c0c1e080910350801700203588607480c1890503d40a031304000d0006130302080b051000c0710100100300440d500d62000308024000c4420444031002250310280c81c81000300a5141d04151000c020b40d030040c11a03681107842c0d84c50758000781c1d000bc080c890907101d00c080001e01007401c0c5081d420203440c65408860b008501845820040c08034018400b09030340d402c18046904070307000c00500412007215034144840c60103c1e143d1414142032a0400d200303a030188229400214210260b10904a09204036210060304a140074030303903c025845000751a0404c480204035920105a03081d500744000c9054841c01b000501404071118608104600009010fa2540082001c10301c0001003003410311491400081038520000018050f200c1c03039001c0c0e60085009501141603d03403002002c2c09aa2003079a03000c1c565100c5500030700005e003260240c00d5000c01c00b403004220543c000e0b401015541d0010340003504054144001800345038821106070042602c40c40a050740c039610040d04c41a01c4001b9169505 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 184850980 1250 184849730 184849739
    0x4050a06080601090209060c0601030c08061602030301050d02030a0501090308060301180f061d0304030308010f0e06010e130b09100518040506271b12010c02100f11030f0403020d030204 81
    0x550b00300c1803003003038451070340062040304a131915400c481000748002c0032900103580d00d01d4406004019880707400d95502038440400e00e0701020300403403607190b061b41c1e0085041d64281020070186022110040b0303071502c968406140012002c1c011200743e103000342c58000aa00d000c1c02410f081d0341030b000ca02c0c035042448200000c000b40300f00c901035201c0f40d0407010004905091840170300c950b12141080b650365110100e0000101584000c14506951003030425294107555010810010b01c0151100ca001c181000310214944c00c0081885803c54080ca101194003081d0714003060385003805450342101020713170040601c42e5080803900c0e160007130b07280d04020046140c1502c4e03158880101a00c071b000003981c1101405208000030054004112242c002c0c1c1b01c41107030000002440c80d80c40000c690151034000d9a101345080180305034505014141c015001c00c02420361f812008000583d40e04026568420000c02410308010195103d04000e410f89402418281406443c1501078090b140405004000a11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 184852230 1250 184850980 184850983
    0xf1a0102071202130203041b080307020406120f0204050405010b0d05010212070504120803040507030b0a050603010c05041503051906150306091b110f0d0c0c050405040503090d1b0b03010504050a0608 87
    0x10b0258103621401606d07500e42d8a080c04550b00b5055050707001c4003a0369004030f01310001000400030319100b21420883c9660b0392007060070a019a480280041b0100c1c0202005401c107074101560143c450b100005144801500050640c03003011810380e5140e601003440ba0110404200f41500541a030502c241040c0c60314070f854070003101e10070f0010300c07a90f004400b040800904010100196901840c180550f00d030070406007004000880e05103100758200700c0710390700c501d00480c1110203079403001900c03012130804814150050200a402c0701e010307004000d0940c503503a08521803c4040c2021070900080c2c0044410000c0c1503408541022a2540c609546900c17260703055042485103c50074200b002c030810a4031803550828a5150030686180102d07400800029030241c10f5a15451085004558443d00c603010b2008441c422280140700390b00c20042d04416260003290b8072441c41c42510398402d1030440381d902d00c140102c10384c00801c84540c01b10050010389068064240d00c020501c108100302890007207441d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 184853480 1250 184852230 184852249
    0xc0a030f1803050f0921010c08090303060d03020708100204150504080703020108070203120108010b15120103030c0503071505071b05060606030a14042003060112080d0f1a0102071202 80
    0x80c24090b00140b01c50404100c00f05596248070010050540d4806440c10301b1041c83c01304003280015440c0c00c00005009009000c494096511030700150b0455480405110200d52990f1040e807d40c410f51400180202e03040007400607000900303c01584461411078007003a40a48190f0840600038184014841241d000a284045070b0702413a044059490380201641544185843e088074840060004213401005400a0300e0030001a19021000c542c07080c0040054041c811b1100c90500c0340c1d500400200e880b4000091405002d00d090307e1506665588410b011140700d2070445913542c8444c00c001e9051b801200d0703907140c819100c0203440e03603100c82c0d650142c44800040038988a4400400801c00c03409103035202141d5014805186102400c150400f002e9a02c2c1807070204080b5805006005141e00707010840300c0c102c807000701a080c0c0524140c2e960041c207410040f4690105130307450b0500b1190011a00559600300140800c0d030202e030503580c0c002800c4c1045600243c58241a20341000c0040e01e40b803008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 184854730 1250 184853480 184853483
    0x91101021f02210a140601090f03150216030206010f0b030925050a1806060c08031303120204060f0f08100e04080415211808090109030204050c0a030f18 67
    0x10f036034040b203400700e2103640b0b408030f81c1e0344034002e0401c10030581d00101d82c040c401201aa1155a070a5580c80300110340c0014903000348050710409040400c0050103070000546a1140c4a20150410b291342600b401e240a022400b900142e0040380101b00200c40c00c0e0200d0054a16440c010785585440160280e540706528814481440d0050088406180c5a50040b014000c000c2150004e41e42c5c8030004a640c030307407684c8440c221914100001a116004000c844000c82e07218070010700b141c2e03c5000502a00344501702c142c0920180c0c0c07040c0407008000c0d100501c003902e901d44800c0c0c00b026000c01c00a20400004a0b408148405507044c000500c81101480c000c94444204820041c3d4071450114120b0203aa40803141101848151440342e68001100c4800e28006121a04c070494040c04100203175008514450444070180d8003003008580e0140041c41664018101920340c00d03074070b0340442c08846007200c1e402d101c0207002c40d070613000c139900d07000342400340c3d503000c0e014800034968a904e0325045608040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 184855980 1250 184854730 184854793
    0xa0c0b2a070201020c1201020c0106050d020109030206160b0103081803011e0e030c0a1103120a0c02060703110601030b0603010e0c0f0d15020a0e01110115090b0a0e040609110102 78
    0x1c00c0d40c21680b003000343e480c0601001d0116401e0600c03281c42a4040d4221000a1299508061010569082107244940401c0c0c059507000d0703030035145809010240e440000401c0205000300c0400c0085002e8a071514000e51140c4506582c41c060605240c4140d00c0140c10340f0b1013641000390200041004a4450300c5809440d075001818a44031400c052a5105405060141c0e00a400043d01480a20078940091130310a41c21f03030b03100c9000d01415003401d2080f041082d0110300c0b01752340e400250400b407000d002e0031846030403e0000212507000841c9480740c00d91044640c0c403414410880903080a004102011a0380001844201d11100001da0502600203032a401200c454444406101070995500342c401c0034010215a0740d2a4070304000c1c0042c00100d2000c0c0070034003148011642810506c00c582c030b400c151210580039141040569005000d004030703440c1c0e01c80c0ca041000b15426441302d1086000d9441802d001440400a2030491030f404140450b450540d08000818180c2c0994080c400c3c4940d241000f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 184857230 1250 184855980 184855987
    0x1021b0f010e0409060605040501080a0f030f05090315070e010302040807030b0a020712020d1404030b0609060103060b0a022407050708070f0b040524090703080c0a080a0c0b2a 77
    0x6004031610102c1e19075030303075209080c16108010301500d548a081911f80580d000d0000343e8842c0c0c09595258800c0074000d00d07007505400c2d8140441d1040c00110400d103200e00e805032404158100103850420b01051440c1010380c05400c0c0850550028840d00040a0a0906609061400340e07240d4035501107200180110628038002034500816034105d4401d00c0d0f00000c55581c2410701c40c2c000355036241100482d030108103070b03500d00360742d410241050301d0499501c40700034003860303480d642130060340390000c1c018505050f1280d4003c00d4150195020b41075909081e4020072040c0d5404402c42500382c440768070b825103450120180444558000210b80d4110340041d0402e5440d4a68503100748000140e01025203903140010900c001c1102c007090800c1c100090200002c4520b04506003084c0d555402d076000d658940c424001000041c0000010b0000100100300f1b881030b02070280c95461880d40031003150f60005034014501802c2204410359150040102070b02c4c40445079119600b40080c000384008141c8078031010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 184858480 1250 184857230 184857259
    0x60c02060f040902280e0904030c05100f0212100501020c150f0a03140703051611010603051507020706050f0301090b040e011d0d03090510020307050409150608010501021b 75
    0x101c01c640c010032140074115610700d0310030300d45120341d10a41d814a2480034906550b507009441224616103402c401401d05c0095129540e050b65200340a034011a250301030050818404103c0d44070b103008082c8401c202594406116040e2103030148001d0a15007182d24050003800240d0340000d0310000c2c0384d030a491b101806d09140c081d50103140140d04540303d011800055030bc5010307605810080c0b0030a20700408505a8652032004d4064403001c48101c6d0f4000303000d0181c00d8a91303124549007c0d41104003000010701680b252a400d003000501d959100010940c9000d1007090f43d0304000c600010031f060310b8000c2c1080c5151648911910040c410318003038946802000565564590020301e411841d10000c00a1a175280181c8000c40c003503101c05003540c001d4101100c40ca0307000b4060201d00507070040143c019144112944002500003904500800c10180f1010840107241d105401c7c174500c0f0703000b02c600c00ca031800000070b143d43d1058004504540005c22110700340004d51001e18014141160544071100c0103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 184859730 1250 184858480 184858507
    0x5070507050d12060501031806020f13030b1b2805160605010302121216030309020a0305030c070f0b030a09020102030913020904051501050a03020d1407120e07060c0206 74
    0x30304101820600503a000100c0c8150840c40780080c0001d500340a002c000c1d40c0d10019811141d42c3c0d10040403940200b9110740c006071031a401002000c090400c020b08001424810038850401500100c031a2942b540c280002c10104c0c51002e2012103e03032840910304080840328112140030790582d011103041e01c094603140327240601c0580711815004040300800486504018014107800c1c44180c0c015414000340c0c1c3c0392408003240b00d85034815100788442c0f0307148035201c4690221381c54900503000c0550b5030800c080180c0c1c0704d400e40d2004600503030085484100b41d818090801c0e030507511642e410b16103810100803084081040e40c6c0d1040403010f00191a076001d000513030452181e15252a40071a0340a000c80a80340c01b907019000c1c02100f40c038204074503511210b101100c5071503588030a001c50801e00c03e00500c40d1281d00204045a41480041400d007840081d800d242c600507191040423a030b401c060107202411520030700c0030103000c103c010141246002d1016103128031882002c4c0c01810000751a180941c031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 184860980 1250 184859730 184859737
    0x14061e1e040b0f0601020d020c0d08040e0c03040b090c010c020607060f0e0304090e030f1c06090203040803071b21140a0c0b151c02031e070503070e1603050705 70
    0x1901440e0540520381441c1c5003244600c2111081c1e000d5552001140140d44001050b05403c00660020f103183c65a000070448482c0220608a5007204208008588850010362040c05003410904a5490f41094030b042d40203a0002001c01b12581d01028100c0a90382c1d004400d0100160107880003503461001c0e007842001350404000c10600c0508080100c01201000801442181c00e00c103010004080801d204544911481d440010024000e00004a8050329028150389024100d4000500a540c1d0795240c4140d070821501558107613070110402090317941000e941d41503e40b240d0041c26070002181e4a041031005030b020200c0c00d50186890b00c14000340a10b001000b6810a200c5d02511141c0c0503100a00c440301c2154100d801184a03400b107050302401d920881ca815800500e070383c9007042a002c584a100b440c1410aa1f410b01c03d032187c0c45010400d0405c040c44000d042006411107500b48400d040c501181c039408625680b0f070540c10014420f8480c0030511450003249808600d40e1590718044440e1302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 184862230 1250 184860980 184861021
    0x1615090b040c1701020423030307140604020a0504090c030b07020a0f0b101d010311060f0307080a060815060d0501060e0108160f0b120415110714061e 66
    0x40403090105100b0070307240e140100c6220a1440100d603140e06041801d0b40510300c41c40c8a0311500c0040c90860b42d49524090074102d50250490f81401c02c5511180703880b83c00a54036040a8000f2401c0c4020740c10030181d0440907040550b024019100d00303a6650411030307814031000d07008a24003030101d10741920031301c4803006181d00328030509130380307000c43c20004606482038403e00c800e402403070300018808252000c050112103035101d071555960300c0e40e21140a03c01c40441c0250348840104074004000109101444c050703e071035512064685003501000017102c0c015000f05410b41c0c800c400c40c80e508921204165400003041e500c0030749170052840c045003d0729240d004501d44002800000c10340010004010141c1c4e07000710040814070f644d5421020b0021140e002d001c01c00c06040100c00c2c43d4150318035915030402d105022416242180d50100c400b10740d0a00860404460001001000d0080c4842ca06003540e1000380034200c0341c100f40300a1a04406460280e0640054840008000d00c03900052442c13082c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 184863480 1250 184862230 184862243
    0x16031716020a030309030e1801170d020d0e063901020309030d0207080c07030305030703060e0106080402060a020c040e070807080724030209040c03090203010c08010b0301210f06050601080c161509 86
    0x100696403235503e102000740902c1d40000800028129000c80c0010005020480341e0050302c810000c104c41100c982641e020722a4102034104144980244545402602e01101e90240702c41010070201000505050b4000000603a00600c14441746060201c212680550000300043e9105064a0b1489550080c42c101e9006805542d038000107064000c4020b6209142c01d5030104031442d161500311042d5042800b4150005460a000600505000d0010160044640102c80d604041c036000075060360074051407000360b500812010040700c6000c0000501421044020788001030528250f452000c42d0810100c4400a2085240c503072180241e04452443c8400f52080c00840e14015000d0060b2540c554105d0280d883c0600034032026200b031a02a050701c03144240075241d82d1034080c410100800e06c01031041c2040689022a0005a9640030804803030701c42e40c1c01050300d16000001400101c0020051900404100301c41000455041c001050203640541c24440240d000348414004101d8081c004060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 184864730 1250 184863480 184863499
    0x504030302130e09031c09020a290c030306040b1c0c050a0b03040b04080c0f16030611031009050a020d0e07050406140a031716031716020a030309030e 66
    0x905a158006042148682e44008a0700ea078440b01c001155904a0706107082c0d0b08180450269540030b00c0064a10001000340820031103499000a504c445659015514020303403c844120040e1000c031507401512000b14045042c9a02d906101d03849100c0248080d00c60350b40c407080615195580b00001080c02690a00c0074545412450f0408025205014003481481c40120004925100e13a04a130f1213141d021080708a0b9403955035500005801c403200d203c91034001c5103100803815404000c0d848009420010081c0000c0c40c2d41800d00484000031000c0400c95000c04c100003d0321001042d5004546605c40d00042e16035440003450000e01403900e8400e102414901981494040010780c0300540300300321010040c1d10754030700510b503200c40c20031041604072507113150420104018501d0080c4a40b110402d00d40380031520241180c401c013200074100d001c2814001011f0f054820609000d600040d501090340c20f4a10034400695101003603040141010345686945c4201403081d80780b40405140607022191 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 184865980 1250 184864730 184864733
    0x1303020f121c020313030809011e1b090302030706120f0216020f03010605010e150714030409050708011d150301020c070509130f230a110310050403090b07020109090504 74
    0x4941c809020071000c0c0c00b140301da050000d5214404c4134001e0300070aa408003007051a55055400321030041071060360f0b5503604402500c1072020b9009124000040303400280c00261401c02a0101903030704140010020160b0003400162400281c050607290a0f0038020351124036465120040c00400c501010020300106030010400032102c0c0c6407400a108844200700047d541080c9400c0740d20910036a070002c1c0c039440c101c100508007011400018041c00500510303001d4581c4134415540e10303034090003880340c0c1b0004080007007d005200f03c2d40c100d51146040802540340c911486210f0454a8a601100e4180c0300030550885103600102e100c080080c0c02076445007040c001142d00c2e10036500c55240070f04000800903560040c3c0d8241d5005850703000440414000711038a548030101c07400c0c0040900d40d180700c090b00f0214802000032581440c450015800448540c0f4145400c100404504101150400d014000081c0e040880d2006446460403125180ea0603800101e980000faa884001450b182109000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 184867230 1250 184865980 184866013
    0x5150918010209210d020f070b0a1403070e0a09090201080403050a0c0203120d0606140a260a090c05030d0801140d080403050607020c030312130f020301020a0e030c010201141303020f 80
    0x10040c044c01410349248801e0200180e0301e032000c1000c0350b500ca4000520501041e513081e40076000700703c4945031101d1406002c07540f131440c660099402c0c1c000700307a101e41600603d04d0321241980c040c0c03a40100500041c5510ba0019010b0a409400101803240100380380c2d0586108100d14020340785c00030100d40303491a6800604819074000e645140c28641881070104490b400b454a1301d020381c06609440349403500c0e1030b0040700e0340c640c82c40c3d582900303080c015150704600580200c80d6004080015001982820314502600b1907101c5a008600a4000c0e03030000b80c241d90000900e5046071590140c2281800440e400a00210040c81c801032030801c020030003009015000500d02d101c0d08498003282d621000c000304169403030041000440c42c2c001003500041c5030605428a40e582d19120703454000d41c02003144d00007404d9812840400d00001c0e18894030701c5031898100070034604981e0a0000304042410000030703030540000200700d051409808400441054402c01092a5543c90902681d1004802c10041c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 184868480 1250 184867230 184867279
    0x521070e1002070e0a05070e09070e01022a040509120a0809070605340213020d14190e0c030105010f3f030909180605150918010209 58
    0x10700815844180c03141e2540001041c00a41c0c1200c041c5039000c0c0d48011442c009040020400400c00950590482464440c5c0c04064007405090b11071503880181100024501051000401c13034039901640d903440000c039100f810704c074882ca0039540450b40c0e41d1240030641ca0203103c06c600320500c0c80d00040302034450b030384103002318040c07400402900c2c501030340d4200494090040e011000d040c1000000e005202d905145e02159083c01c3c056460000c2480c1c54000810700340c001d83c81c294107280c0014244070020001e1080000c005070180b0505241e0070320703001421001205402c1820304655502c11a001c2c4041088070224142c00100288055a152031000c62a0079140c8918500e2180011055240d405403101501100030100820043c80171181c1241090100290060b414420680b1011452040320300400b0044d40611a0800000ca911309d00741c0c0450300004c0000f200c540283c0c00c2280559104161240c01c035102c5c0010a850094100502d8024400d07030301c0d1154054105984001d018840b18000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 184869730 1250 184868480 184868507
    0xc05030d0b0a171203090a15060e07020f0c010e0a05040213050307120f0b06061b07170a020a031101050d050411040b010305040b01050120031315050a050703052107 72
    0x402c00e401d941c0d00c14043d0f00c290b0700b5401c1e1046410041c4044092081c04e00599400785088044620011080d00e5400040d504d8070700c140c0301551600c000340102215012020b4101001744014041c8006a652980e20b0b80714a07041641044200f1110100c1c6945200d0440040c0034002e100315a61800f0400e201042d2545200e054000d02a04200240a200d49001000420341240404180000030743d05c0d4420980000c2603264849428008507900d5130f002c003c4040140e4083d0000e055650800300000300964061401e41d045030f0080403400700607150040050700b141ea02002a0941c0103000c401078480c0e005503d8440c4480b4600000c0005004001c1c0c43d00001c0c1c441034804100340328950b001102695800c84007c0c00a52001004201e15481015120002c0c20101007500c4c42c0744880303e0040c10b41e071001c1380303030341250315820402d1004e81c440160301c0c0f183d2107160401524017550001c0141841c000d12001505004012070030b102003220341402480c4500c4082030800d242d140050000d00403c0c44e4030ba0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 184870980 1250 184869730 184869739
    0x91c050123010504090201200c0909070501120b040216030305040204060608040f20100e090601020703120e0307090207050a0611160b040204020903060702150a110403060c0c05030d0b 80
    0x1080025006011003541c034011036209100c0d00d0ba00388800d12000c0d0405480c12410030004401e0307a406850400041c4500780507940c00761100551031402c00503a9038025010500c540c000c0300040050f80c0e08800200003440380c0c40c802103140340703418000038000c4c040d80c034044010b9148910410300309507040e4041031040e4821101040006d449920450f0001402c5800405807610700003a0f00100c0d1801c0319400155880b99140050740321980b002c1440107040090040104e1061700e008c1009140c602d044170f0f4801c5007072008054191458036000c403400706055241c07061003100c1031620340c581c40c244002c034007401d0415025959424107203404c99442e08906810344000c4d00c0d03c0800c1c10b5000990701211b0000e00150088801e00c08640c40f282c00d440400341049078040c2e42040650395035142031100611840958010707081414241e82400c4841c2402000300b500356280184110512640d001903805498101000182d01c96415030305503410000c4480c0038056100c045444910750101d908500c454400555 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 184872230 1250 184870980 184870991
    0x30307080c0316230f09030c040c0203160309080307080301090f06030335010611060c0c12092206090f0603020609010e03071a0703080105091e0c091c0501 68
    0x181c51a94900056840c00c10304a05442d031810140e10a6030184903010141803c07082100c1e603402e480c403155200080d03840702003e0200d03040c6028034060011080004040d5018030111198420094591080e100018441c80d00302c1e840c5001e042c441c000c0c040240c61440201d903940c103c10309081280d90004d02c51401c905007440e220303541c203880c40e000e04401c0b00d43c161908403003d03e030f02c00c02805111014a00221640915110b0303111031000e04155402422a074a92604c0411250100360500900810001e00031341e04210360b1440036400544003450740d50760030845440d5005040080d129144000740151002c2440f444500c00b11901c1c0d03c4001215a021000c1005518446409013901c81d14440654400c000780400074840d409140e840c50800c000405968180b41c4410f0111001c1d5103003110a0603c050104900003090b401c80c40407805041b00300c46410044c80d000810f401030302010b00280c01c8824101001c00c000c1100c520a940c2546001800141c501c0b400d030307003a0b40a0720440305007a00c0542c01c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 184873480 1250 184872230 184872241
    0x5090a050f01060e160f080702012301060f0503010b0a14091825050d0e0111040311210c011815023a0f090f17070e0610030f06030803070203030708 65
    0x2151444d241d025440c2e00003002c040b14001e403032480d03002345100155525440d0451044004002d0703006500c0c14081014030750b50401000030302e55001e00c0d86150078440c00700700501040d120641601c441c98100c0c941105c1c851900c0800e4030050003050003254110071a030000c0c02c90030425006082c800c400003420f400c00b07846d10f02887d83e03041c0390303401c07111010031420012840c1034055500304035546480c581c0042804884584ca524103540140d01c04e076807140c1c289049260340e150100b4170702d85c29208554001c6110707499240084d100d100c3c01e1070090501c00c40500841807051080c0081c801000b01d5900c18084000f1584041d4599403003221000303041e020007000400c4d54001c00c844001e0701c4202c03103070600c910f2061942616200c08501c80c407003d02440c100000b403184400306040c405018601c1030008445851240b0501c0c2400941003030810901b01d100300069900d41c049441221040c80c6404900702c071780c0d06141c42c0180032a8001030702e0200004200f06010360000000c602a010035aa103a24a0f82c49 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 184874730 1250 184873480 184873501
    0x6020d1e0b0f010c020604030f12080601090b03071d090a020705060a200f070503041202011e121d0109111305090a060908091e100e09040605090a050f01060e 69
    0x1d159a29500507416001d1002e20351182d0007411040e44054081c92500d030301ca4813141d54172131049404aaa800403c401e05a4442c3d0000340c0542050082c00c00d08626810000b011903176010041c003610811002c03404406605140380440068500090b1241036075081014951029501450040d1740b0740c41103001244007002d00b8442c0440e802d02190700344081d4520383c85401c074690b11010000d103600d2010300c104400b1580070301c010f0000b006c5d5140038841d11504da20000d002e1900101c0c07211829085003000d0381000d5000300205401d044031501c00101030f507100605da10b01001d2420902c0c1a5072030801100d0400031903000c10039108030126450b0180392941d1a01e0015100116084103445d0040d100f00d80004115030042d00d41c7c144103650441c00c100e16000442c0e0351018101c0e008940c0c0c0e44007004c04030242454543c0801c00b07040d40ca04105804800380100d000c8000151006007040d079140006064900b051008900d0b03158800240d0f24201400c9101e00d000c6e1000e8001e00104400043c0070130108900d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 184875980 1250 184874730 184874741
    0x3020a0809030a0c082107020904020609010216060e1f02070b0c0f01060320030f030d05040f02030105101802121306020405030a0b0f0606030601170406061701050109060e01061d010302040306020d1e 87
    0x1401271040d400b9503900d900380102d0360024201d0707505520510009030400d2461180b07801c080c0c072440d6582d01c030f4242500d0810580d0810840029081e03c0c1c4a0422503d941c0c0c0451001c00303071180e6954140d500c41d1075180080c6011030045001466502c1d000020081041408040391920a0441c1c1040020310341010151261007101001d030042c2d000300302503111003826401c0560b21900488001c648224070f90080ba007510301c2198889200d140d80741d0180324540c0c881c1c1112544a5582c82d045040213080040c1407140640940b40304c141101035421902009130580449011701400b40644c0ca030102903150007030b2848020b42d4004070702c1a40300000380060a002090f24440d090594581407a4100102c540c00e040c82d0240054403120384420001c02d42840000b038114170342c8180800060b081d85040d8039013040303455a40000c3c1c18030b012080101315040d402403404e03c5516a90710079070701c0000c004005900a11a50380000c09032400450300320303064103141c0e2040c02c1c504808003a0b4401791080b07000d0b0208544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 184877230 1250 184875980 184875983
    0x60604060f0f030f0501090504170301050109030201080c0c01150303020f03180f0a05120a1a040203033103030c020f0f060d15080f0a120c03020a0809030a0c082107 72
    0x14041900104814464850012100742c1420700190380c03403040003040280c550980210460ba0303154014441044000c0550000e03031400120007900f55414a00002c0101c841807002074108240c0c10041603660b49010100d03004007503000c000b0044c0e407000b01401245001244019800740c0241800400f4158021088801c13902c0c05541d00d0301d102d42803908000e0b5466045a15a0f009908040c0110317a945541191128400b01040189446c07209031403e0307000d034201400c004139038502e030400b0b00c001030300c00000755002008038000d155060008a14040342c0030181c807801c03c043c82030b035840000500d034000d80c3c0d0282242c0241c03603c8010b00190381c1841800d120011440e078011404001c0300995000c0380e8804141e0025504203c2651a603841d5200e1404100884821440c0c014412410420182c0030107a65841003d00b801010106142c030b0194585e1506100a8814000020705001c280e074180706070411154003440002c1c4807030b00e44100c191358000315000e0000e083c0d01c0792120543c07508040d041da8940c9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 184878480 1250 184877230 184877237
    0x80c0f0316030219091806050a033009063020030c0d060f06140a0e06030403080702060c0708090f03010603081c0b0f030d0c02030c0607030503010e06060406 69
    0x5441d400c00ca40000c0810040200c01c066003400f40100b42c615460030940c4218a95070381e80c02d1075082402c1e5101c0d42450500c2d40c0380c61490082c0400240c2c40708618441141e40040307042143da416104000c0511079091003000300503d840d00078402e0782d80c118440300195001541c2c0e1031821400e4098201e00e10b0144c0d858845640441c0d4008400150b071600509441c0d1078000c030341c186c4050035010051b41a00700b03171940e000b540008901607a076810584a8000241841c07907564409500e13001e400340c50f0400d0522001404c400c0000c3c0c22000c94081c0011175201c2c0005020940e9134034050900600c014800d42d0039200601441006c13401c500d8050301a02c2d20940c01441113071400310040200100d00700d80046031902365403541c40c0000400c0802c270141c0807000401000c1426100704074105001c680e05030b84811310403584910300d8805601c0c001041c0240d86a02d0520203009070a500010789010a405980e0f0352043c80010507108041e40403000c3c40c100da42244107a011500c41004111860185000e02c5000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 184879730 1250 184878480 184878487
    0x1a07021005072f0328030501060807030203091501060806030f0607020d0c060f090503132102040207020a08030c07090e030a02061b040504090b06010f0c02030309040218091303080c0f 80
    0x12044501d0b05505652219001801c00c6000070f110942503402021000b505050001e1040c44400c0410056140103891403038200059814084050100013024081404141d80800003400900041102a20723015010004a0680d82d480070014803c00381220414040c0c0900003821448070350004146004040640245c41303240b01c49034041304e052442080035250903031560382c1e4480c40c49880c402c1e5091580510301843c0c0e60a009100111110b02d541d0200840a03043d00c41074400368150000380a0880e812100940d0f10500e0340002601c010440d040842d9500001a01280d0020001055011a41c12000c240b00302100c0480071b81c0c4a00a540c0c000025030801c4001540c541109415603001880d110401400c00e40c80d00c1c0820101c401c43c80c01120419100c0f42408255030700b044200c41c0c0310030a403619152251859010a07124001c1c102d0050040740c0205d0142e00410074151500c550340341c003074011007a80c81c0803481c846800c3e80d4800142c0115a00300d011600d0030fa4200111070107445007105484c038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 184880980 1250 184879730 184879757
    0x6040501050c0c04090506010303020607020705090112030522080c030c1003020c0715030f0e0105070212031005131a010c08031b0f0c060f130c0306050606071a0702100507 75
    0x100341d03202c41100000c074021400951020b507998032605810f14020300091101e0341c1945406860840064010020342d808110100210390340d0140c094159040000700d0744100e0181d144c15189801410a0b110306400400000034609200c404828100d800b80001c80395202516028142c40ea440b843d070254200c2c0202800c0900c0b240250010f01d46441090121442e095480e01f0301d14080c00100e4110703000a0f100d581d00e011800302c0d801005440b41c2600000c2001d4141340201958551034501a40101440400000c0341c89a150507840028000600040307010307640018000c0090a02400c0c034140362111f8404030005500c1048a02140340e840109140386860708801160528040492201c03080020805040b154221070060003038481144003e0107182000100368000d10001031001400700000c6002c140400d40c24810041100e8004e400010140c4a920104032180f180380b90141040420014199483c00b00d844068443d0003103a0941c1d010070305041c6820140d4805580100004041c81380614 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 184882230 1250 184880980 184880987
    0x50109080c06030c0c0f0309010806150901120b040608071d07091205240406060e090a080d1b020708010506040605100e041b090501091502060f07020f010f05040614010506040501 78
    0x140c01102d000c100d0783c20100b07045171035440c01800042d03004180e0004200000d0039604200701542001003202c030101000201c1c030141c0500c0c0101a0024104480c2c0c03c041c5000226581c44030944990140c030500030140ca811825503150814070030b0303c21140c0001c3c4008010640d00000c030340070741300981e10520304518200c5100721090701700d0800e0f50103004400b00c80400710180005800d125003031840c594524909400c0242c00c403000c1e40d105d4040b00200c1d1f420015a84030200c2e12075006d1380c0c40103515071516400d204100050242000c44d1000c003000347d000d0710350703281c0001e080c004036200c1c0c00003172289035034520030300c4140c540a1081d10b03013006100f42d940c40c902c1d0044502411030b100c064800152400e40c181114440c03440680300b0360102c1d503044024002e41d64040f4550740602503000901c030503000d114000a42d100d00007056000c0a130000401b02e40317040e01c240308031070306455001c000f8800582585140002400156400c4031050715002c203040b61250401300e040d0494100a00c400d040038640340055 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 184883480 1250 184882230 184882237
    0x2120712032001020a0c020909060402060306042c010608060c0702030d0807051204080406030e120403030e1909050612010b0310021305041107060b0105130b16200a050109080c06 78
    0x6001041d4000c6840310890b00744040c040f241d441d50303580c0c81550114010311008110180c550390058010508210158403080d0031a03801400030798000504942520001c4801c81e0104030f40610f181003802d0039200c2802c150404d034165030b001001d45000d5210361004650394070510320002e4240e0400c003900b00e4443d004800035580204035003000e52802a405840303200c042c038211021909444042000e101c080d40c07501c03403c2860381c00c95006110790304102c041040207005920008041103007814041c22603413506140c829405408550441180740c848021001800003210002c3c0501c120700880340122405000c2d80009280241c064610b1910340481c4002035404003500c1d20000d522302c032000074181c03180e00c9810250041095940d80310410791030584141c442c1c0c540b24504001d814000305203118a8146884101c0301040b6005503500100303422000f10001c0c960000d480c0898080b40140d005c43d81d0000310186a40480703072031516685500c01901c50074910b004000d055440700300c4405035428020001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 184884730 1250 184883480 184883507
    0x607120203040c120f0302070b07030e0d06021c050403030c052a010e0312090106090501030b0a0504021507050a050f030319020c100615110d080406092109030212071203 74
    0x100da03504c2d00d502c10f005400b94520300485029036a070600009050f4140004d0020340100480b80740307003041c00c0d1001404045841d0304244180506400c21042021542c1150f54500050b10745140c445441d1800100811040302d041e0301081c00c1140000b45036128204803140c00108040c20520443c401c03880c2c1c00070104811814243c0d650b100d094004100c0100050a4500300d072050b0b043d0140380c107000c0a03003580e07200e131300c04092941000300600c005851403170f40700d9000b082c00500140c00da9490000a840481c0580d03c0c030f40c8a0000200f8406205000c100700003554094400c650042420070340e5550750348001c8400d0004c8655000c8003c02c134502940080000071850f00c1280c060b64150107000081324100d5100d80c1c00c2c0c41d64400002c0320180c10041d003802c00c281181c080c04a0400244000d401c40748010310040c48959510310613002c216007030500c01c00340f00341c2c40d00704030a0746002c2d44007030300880e0640402d0388940d010b44150040088005034540640305180900e041524645c0c0c2e0540e40c0c00c542e80781 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 184885980 1250 184884730 184884743
    0x509040b07081b130303110f0309060a051e0a0f14090f1306080601060216120201031806050a02091903050d050c0703050303150406080303090d12140a050406050702060712020304 78
    0x40308140043c4180180404040b103440000031640b42d0300e001740c04081105a4440241c01071800f1031001c400203c240c40301c0c0c0c941030700c1c109d5403000d204104441c1440b51051014509604c15086000800c1120181c50038400c1501d40341d0401c01c0c49101900c80c011102050404454108842c00a0b82028600302c0c1e00300344040c06410f40c106080d03070714005070b420680201c01140e00440040005c80d81c1004980c48007202c6507843c107511404c4c81910010a07103103001c0a810715403242c105d00a6540c4e180c50f901e658a411070401c1296041a005d40f602a41c4003100e524030a407190003c2c40d1401c00d1503000013048036440b400030b107140030400718140c41e117810428480e000340c058020004042801840254400c0c001907025010701d51000040104403000b80d000352680b41d10500c204203042800160140105402c0d0600c1c0341e4200d09074610300e001d84020500b01d00c403003c4020510905a481d500400c4c0501d00c90315080c001951440070880c0d035503c0c100c030184001030343e41030000d0404d20603600440d0020301800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 184887230 1250 184885980 184886011
    0x6040b0a0e0f060a06050a0c03030c09030f050a0b0a181511070b100909151a030111131208030f040c030209070507200a03021912030c05070509040b0708 67
    0x12041010480112882031080782c1d2001009050700c4d010603c01e000e8480c6040c51030415030702c0c00f0004c01c1456948001420b0541c1c860b0604100c0740140004801168056401c146c0c0030700a2420301d444d5012b4007021660381d203030b00011541ea0344650041815400701009800004003254992040d440c50a1940c20115642c030909180d41080400007006080e0003262036504909103010f086000600550150030300a1401c41120006542d203201d204900007041b0b00071032642507180400c200e0003200210198158a1301c20320381d240541103c090220f01092001e442c81c00c2c3d503280100f003000d0b002e41030300034100c0c0340402c0000c00c113402d8804400e8105005106410380c144c0c40e030340400d51a2400b40c503982d01040000c00d141e010414403290704100660840400c8050001c00701c08920f40c060386010092003080e4407503030200300300d410509a9000b811544442d4019038410704020300b4010710f0342c4040c1c5942c0200900450345040058005014540c06501044030340c1d60a0001c07500c000700030b48915010107464 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 184888480 1250 184887230 184887239
    0x41811070b01030b010f090c0801030308090c1f08130309120303180305071e0302071701020d0f02030924060402091906050306010306050301060f06080403021608070e09011406040b0a 80
    0x1008240a11312940d8030024950400680660304030181d4402c01c00241459006640b0b00d5001c05118116135040c20200d00f90744a94076a5400c0180203a606900003448180340c0c0362003460080d20640200c25504c03208019207841d604100c0c0380c170610038054013081c2c502c0310801c405850004101d4900b4028580020006012070201c1d1780c0b0003c200c0150002040400d1040c14080c18284640c2c6031181c03491959900e00720355502944440c058801c0360920145104803100040742074040324944d00d036440d0200021050580c8010080d00159000c203131a00c07660300c0c50300080d071200048820950381140d44150968a20b400c01c00030b580702d00d488a4200860b0004804500480301115000c0d0140380c4070b140e100e14200000504968403a03010342e11aa04003e420031080142c0309510050b100c41d880c0629003980d960500781d2034640c51840203100c1e05203200300040d10b5038004c61081e06441901c80c000005444080d4803609072612001c061000040901c0400e0142c40c05a1023042e108a0181070610001d03540d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 184889730 1250 184888480 184888493
    0xd0f091223030d021e03042102030705070e04140604351602040e0327031e1c0f0e0f03010609020a03050405010c020307200307030215071704181107 65
    0x40c0031902c3e41c4540200d0008260710300c00381a40f01c02c0014034406030443c07404c3d45404440d0081800380310500903d038050b240d4114400e00c104c4001310f4001e4212000b20755108001040c884049401b03071450104159800b04520b404581540611780180c15a042501281001a4a10207a48052800035040e110103800b02503401c001d003144140302c0e50300c90985565401480203450300c00002d4840c0c0e8008000184a05074941c0c1a910032000b220310025844041d02c000c2890305090426692a00510169284d081580058031010002c580f10385070158002c030510031360f121100d0012030700c0031403403485d900707c050304015110704102c1c1c5000f400403400c640e46407120780c220380c0312180083c0080c0c0c40d4800c11042c040240030314142c00310188011484c00c0742c0c580700c65441314885e62030301000c220740d02d0710307000e450b5401c05c190805550010011250740d400c11500300003c0c6c0c0701c40e004851940d07003441c086508018010544c3c04884c0104048500c050043d85181c0c02070061214841010006028802c0403500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 184890980 1250 184889730 184889737
    0x4050d12080c041a0706090b09060103050f210c0709050c0903150403090b030a020705031204051009020f0d05030c030703020f102306120f0d0f09122303 67
    0x65404030380095444000815800d07000300700642c1e020707040000300008450b8403003111044689032052900c4507181e00d000006024110b00103402003124609100c406480030401904030b91045040b43c141036450215562208501c6031b91032030504a4005068418941c40010102006d80000707460000d40c4801c00b103012545c00350b40d0f01e40710030707004a0281c290303040410000007003510303040441916250a550062001c046401031074400c0c000840498081c0100350113548400703a00c00b040e25140c002d40280c4200803001100c5c00e9800740704100004050a905202d100ca0040e0080c02c407400110b80c40c418410111021001180c4174801040b0140b090a02480504002441780d03000c1c204200b181055245081c64410000003003a16150305520300e40103402c07001351100c07154540301c142035440b03400240e9000044074414125005143c0b600524400c04104842c107003109441c0c1035042c206569040344c0f502d243d405049150a48005c1c010041265605003050780200030040030341c4200300413455400d540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 184892086 1106 184890980 184890983
    0x20310060f050c0d0e09010902070203150c04030c0e09070e090a110103060503010f060503010e0a03120902030f0a030203040e0609220507050a14040615050406080c04050d 75
    0x9010340165140700d103d00003500e660381200c44000e04081e0103552107070712a0f8441c00001c900b8140500c03c0c2d81c50560060000c1036640c1c04202ca01d00d20303000c00340c0682c1d5113050074031000002900d0f012100c809840060351441c030505040303085034645401904102a21071601040203c410000100c0b4404540c02442c1502224180e0340123a000300215013001350154208051a03e11981ca070b00701108590098000b0014503038020045038803107048000003400901e1442c0d090901e00e1841d049490320390300040039591040c000085441c80e0003008082100541c002003410040d8007916100703030364020400e4461100610b090544246a280788141c606c0d100c005429000f41800b10801601001d03001c054002464a0b80360301780c403082c07950700c403001d14805c0c3d0170714002003244004000f92a141b00e0464070b0b5581020b050100030b130380c072150052040211751000c0c440002e0701d5450659a45495 = true := by decide +kernel

theorem cover : BRFrame.Cov 184712230 184892086 := by
  have h0 := BRFrame.cov_init 184712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 184712230 ≤ n) (h2 : n < 184892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
