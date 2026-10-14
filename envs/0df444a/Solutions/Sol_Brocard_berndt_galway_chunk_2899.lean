-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2899
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:04:40.288157+00:00
-- url     : https://prove2.me/submissions/5412e552-aea7-4e5d-b3f7-a674edd52505

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 521223021 ≤ n < 521402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 521224271 1250 521223021 521223023
    0x506160212100e0f10020c0604030521150405070e030718140a02070507060c030215090102070c030503031e0c0a1808070303210504020a0e060409020d1b06050c0714010c 74
    0x1900c0c0056048104201044c0c02500c0a60f101c01e9402506082c0d01850490003500d1890030154800301c00100001d00540040552038145401e00e002843c00901c1519030b50700071100b00203010450594451303d42464040d540d00880c2c0c034200440c200f1481c0c1c01080d6101050b11075049806a241d01070040202c050340032007802840f50b142401c06281c038094101c0030f50f0194004071510b00c107949000849034490708206052540c154090840011341190295003004043d180c56a80d5508104900004c0e42c50034a1000552164000c0c1d6164038100a00394215483c018803140450792000030400342030040421a46e030f100182c10314030082145440001d0a103280394215180a00c07820f0b070080107054102c0550394038100500304d10310b41c000c1000c48210588074155002900200314250030701c004280c814100c0d50108001d00000f46c0c0d202950002520a008801c0c151201749404c03039640c139100428a441000f411041c101185000c11901c2c1c00380e40d4855030712030701454000400140e07995a100ba41401c0c101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 521225521 1250 521224271 521224303
    0x21021602030109050a05071a0a0807210f06050d02060301120f05250b0414210312060f0a060c06090501150e18120f031906030b07090506160212 63
    0xa44041c03400c2c030790303c5c402085c040e20548204400000ea9018541414a000a4030700d41a8145103081c401524002c0020b030420040c89010200100d211000d45100c404000f0200400718141c9035000410044078081d4000c40c0c060491191031101503110602141c0c11201300f09000d40070420740d41400041c900340d10350000d1080c01240c00e000901101e004103000d280c0c0c414022000706659031031001681e03102d184a00301034070040e42c2d101d414528110300604440b0b42107400c402415005441158110b5000e680358840c40f100307900a11040d82041500f2600111054880c0351505091910290185a038000000c0c080d640b115520003c00400f074021541d00200410240d00075034440403180740080048650381c1c0603c2d228aa1a035485400281c180c2000c81503145051400e1022070b04205a60f0000b020b01100c01c43d80e2407082412a298402c1c14010750269501e81c0f10790a02070310041107041940d000030320610742800120581001c0300704405586074101c0c0c007203200045600008d810407a50305d04007040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 521226771 1250 521225521 521225531
    0x50403020925231206130906020a0f0e04060506120408040306050f06092a0f090a030602070212060c0d0c120509011a010507080d050709031b03030e01210216020301 72
    0x801500009400300f100c201281d0020088500701c2c11403102d000d0404014078601c5608041500b0741031403541d03611601552500890b80789540d45550090b0780c4120741440014030701040da00e1101c0c0e40007000707102059007220f00784001d5240c0303000903c16010340c1c0c100714180402c50000c02d0401142104880080d170380038205015a181c0160f115103c1c5808965003030041d0700200006000d03032464418100d02a000b0f01c0701000a15625100f144241c1041000c41840c040400a81c40c40e580e801003194001c601c0f82c0e50241c0d4514091051220300040c41c285170790b4036444002403028109070b0500707840d400c1c940c606000490140341c0074112640081031084010261030041030085030b04044d00800f030645101c90861165520480c0111250301c1810000f40c50520300740500ca0150b580380d04039a411030110701d0f1811855481b80c44041c03005032204051400f032010300b5020010036411030180301e01964242450910301c440c44200c030440145580a141005500042000403000003918049040342c0140007040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 521228021 1250 521226771 521226841
    0x5070609060902120109030c11060d060b0a11030a0219020a090f151203050f030a0e2b0e010e0405040507170a020301060e060a03061107080703030f0509030a0504030209 74
    0x410009030b0a0b0300a0350b0908082c2c15143c4140a0344000b0307645030741c42200d00c001c0340c0c482c4a190542c070051341c0c0e80800c5c104559205000d050240001510038045000c0d540e142c0d911000e84082c140388442c0342d11340c00c10300040b00800e03000f01d810000c1003019042100b090344540f000619030b0030243c10983c1c5041c81d2000c48544c0014a80c080c4d8940c01e039082e030141803a61114608032007500e13022070060001e031080004d000c2000c50000910782003009000c003c00c01880006d080c0b428400404034174808921866903006c7d001c501c0e891182090780d2582400001c6180040009002007114410316000b40d40300c802140401c682007202c580202128040b41c0d00e000000c9500c15120846c0f00d405a20940c2003e002003125802c1d90080780c09280018003181d022842c5695400151201e0402c01150640610404020680070402030494078860380e000100610407902000480f98050099242c03544184001c5001581180445007a030307404803000301882c0d40c2c044101c106134011100155000c00c1004020f5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 521229271 1250 521228021 521228033
    0x9070c020a15050c0c0103021804091704080a05010b010f08180c03030c0d030605060313020d031218050114040302071a0d090b010608010e041121160f05031c0e0105070609 75
    0x3092810f910150f40c0340e20b185e10300440c141d0240041400c00588802c8141c48149410391003c0142d61080000001884188010810603001588140c40315003017050180104074083c03047c0d540559003400e1001c1a80080c001c024544080140250307900c0708000541c00c8080c0c4100544074041d40020101d942d9989030b6460642c440d40070420103c0032a0415071b0101350752070103c007a030748140c15451514859616940820111041c80c1070160103000281d0084003860b105070140d4454403403841448400130605150070b50840784c103150341c915651580c0040c040081e9000c5420000c403132007007502e90701404c80038507a10380302d1090078030100c50740d8a005102001c2007080d200c8030781200e51546503010180c2e60361078030b121141e80c1281e005103803c9504441c064503242c40400f20541d02c02484c0d10322208400f1190340b80c60803418800031801035002038010007108481e1031268020388000d1300a002d07032201d5024840704000405202030b061007000c000e5400d45900c61001e0301c1034160441418401c001860507d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 521230521 1250 521229271 521229277
    0xc03040f031715100207210213050c03040b220803060f0a2405040f1a0906120412020a0206090d0503120c191b11040608030a02010f0c030b09070c020a1505 68
    0xe50240404d800a000c1241c008134110044680103401405061910b82e06900c41c1c0b011007608a07402400303081c802010407428802c0c1841803e104a102d99641810b041801c0c00510082030382c92421030190051640c00c0070f0703a4514844030343c8200d4064613903d81000142d40e044036521480c0d00318852550002d59020142d0f1603203142e640d021040480480740c139408560038030036401480e0301d007a0600c0c410032a6070b541c4031032100b0750307602c0c451180d080100150009804d0b600601807103107480180300900091180e149410644c18061340010031600e5280c0c0e000c5901c0740621000d00b80304020004240040c02001e1044500391032000302054403d1a188500c8141a0070805d003820b000500c0d88582c481850042a8054030300a9203010444040c0540d0740351402c2035408024550071944440c00020504801c00280c15800095000030942c1d00d240366484007210000c800000406003061640c010a4482050b400e810000300e192060f4582c030180042007007031a01d0f42c04094031451650b5411403544d40031001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 521231771 1250 521230521 521230561
    0x3030e030d111b0c0a0e040c180903020c0321071e1208090c0901090e120d0c14160209070512040317130507050103020d0b0306040501140c030c03040f0317 68
    0x101c07404002c40ca40380541d22011364440607000f2041000a01081900204483e4414480e1500e42a03c548421440c040d50994910082515407107004810030150140310b0000464401c0d4020550940c4012034144440b1090440960a601c0083d92038140015104104422060001c080c903000341149010060444010701a030f00090105c004554180d2002c6024100e0840051000070f083c1d080c0410b0200502e5214901c50280c07182c13076502604648076502800040310710707440004020141880151040c80c1c007884d1546610410800b25030303c96580c084010b06550151800c010036174814206a0f210b2103215a40040d03c00010100402c160303000c404001c880301c0103200880740f5144c484a81001e040050700c02440f5030000201070089503c01ea02410aa9940caa8081548900300005ca801e1100c2950705482d965140d400388107507004084c0441c1c0e00861400300092842c6440e41c94001c60f03010280c40200703246d0084030608181480703801d0a0080945201b0000ba00d820580741115188940340c1c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 521233021 1250 521231771 521231797
    0x11040306140f07020102030108030d05131205130b03060307060e010215190e060702071401020304030b160206010506070b0402010c02010504150e0f240702010315060323060d03030e030d11 82
    0x4203024411b00a8a0484403010020360819003a107641320060301c030083c10104150881c2c0d46ca54013180c00c000004446445503241d00341c2e16401c1c810700c48d40028098002d054006000c2090100607100011040101c071003515201c4800918040104c1c1842ca00c0500202c554041301d00380250300c038119201d01c00704030f00c80104006e01c88903040344546a036811601980941c201e03520800c001c0850007807a8040800500c1502c0c68aa01c2e6519011484000c0d0b448220308207280100b4000d050301081802c2c0540030480e50103040c20342c241d42e54043c0c1000188024100138003040388408590165003581c01404104584018049030000002d007071170070080c0c1b107910842c0d151890220038240f14a0071050808003003481045c1480c48580005940d03c820000c90406a4a92090820312401044800075054070b59000c2016141c0705408448500a5190741980b0140038051202590b00c80c6660001c1030ba0508000c1070007403c490000b0f055000d240b4108207030605143d03860066041c104000e00e44006508 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 521234271 1250 521233021 521233051
    0x209040b09070507021504090207051606051e0d0b0409050a150b030a081b0303040507060e0306103f1b0b03071d03150a1a131104030614 60
    0x30041122203101502c0c502c01190301042148003505121094120510503188454585a50790541008a0f0b0014105886640240542c901a02680001c400081c1a40c1c43c0150a00e1141d030003c04005d40303000c02c003462031203000410080184864000800c1c65200500130004100345061154688501c5142192004400148032440d80200c1c0f02d03d1006c458040c0003007040d84010351380c1c00030562107851003442100146d40d40c161011400c00041d44198032410240c15202e1601c1c00180100c60500340980c869041001003200001b80741a420b0201c40d2030441c1d50215420104990020340e00307028410102002061103440920704000745505070501c02c0c0707405205405c0c502d44150040c007050140c2c055282d030800200d00340c1403043d10480300000b0062070407801d006a0b5400285071941001c413003c4281442d1080041404045c440c406030060318030b5801200f2001040007a54880911545103450b581e5603c580081405e81410b64014590082e0300b00803407100049440040c03030040b103165275009210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 521235521 1250 521234271 521234291
    0xb0304110a030320030d02040b04050a0b1c090f05011a01090603020705060106140d091a070305060d15150b0706060506040308120c07210806010c0b040609030504150201020904 77
    0x86420440c3c1c0c15a44840111541c0100e001d10482c02404d951030620090022401d41c00c4584000c1c030041c1000404641d40d20316180a201104005138000d1744101014000210f0383c0d54078420240e4840081480010454082d20780740040420648014000d03610f002580d0502c552140413003102c1a0003600c600841c170b65500d00840030b9100300d84000701560030403001001168094206111058003140b0340341e00300803500d840d14080761050300080d9a683d00100c16a10b54400005455030050310702d00e8140001e150960100b443d0035800200203100d0310741010702c01d001b08200d0f0302c02491405080120011070b81e980088021a400120050b1401898910000f0b000e03c1e050041703070201c1c0c4c2d100d0980383c05d09540c44031607045007000038000290038908021090014402240703a00314001540414249414442001821100014812418489005000808a45004029030307210ba4812008903605240d494101d50500850740240d447e0303031b40c1110105a031501900034002d1810143c0d0200540400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 521236771 1250 521235521 521235529
    0x7110406050a061d28030303060614390f060a0243060c03050a05060d080702040b22140c0301120201020a15090b010902040815150a0b030411 62
    0x81d00c03d09020034804000500c4c201c003103490310482c10720001c00b030038440401c510340c10704440c1c004104540b40036082002442090b404d1700c6400058401403814504122540004042920030320100b07112007210307400340083c0c401c040f0b81509100800503030450446214000015541c43c2c0c4240c1c54983c5018110004030080103d20a032281c1c14410900031030002c401840815402c044004011f00b0148840a074030440404400c0f1495414464100000e000014080090459001070308184c400c90800040c4810303070391500c442498158122001540d03e01680c40010001c194103c45241c100108813603c00300d40091140189500e03507040028800680e441d45111034007501150702803c04241440140981209103a19464030b51040c0104d941c9490161101c4503000405004c46100075201e0f0b40300030400c40481c41d403600518100d40b040d82024203000300c9a80b540f104131b101103403081c156000540e0b132125452840341c00d02005442451007036210007001d201503000301c90030768075040300710010011424 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 521238021 1250 521236771 521236789
    0x509071a131707051f0c140c0904030e100306050a06030b0d050d03050f0c09090103080d330504020301080c1c12020a02040c0e0907111e030909091912140711040605 72
    0x62540e40790704038100e881e503400381407c207608240c2c8410700c40c02595004946407044d80a0255000b9103900701100080da041014081c1ca8544031030406040c103904128688905900c10241c0d01c031424086111442d08022910071421200c0242c500d05c502d6581600e03160705540601d0090030b4030400007078580e03506902107100e8800d1820480d0400354034001000842c03107040103000703c4140c02d0b00114803a003451a02d42d2407400c1140d075640f03042119903c082c00d00d150070080300e001040103450550641d850680742c6034a5011100c1030b9070181401608102c000c40f8200310380c0740d845902a0507200d0468805000a586e100f9032542203001d07501e00071760100c1540c0111310f107416929006018000c182c1d02e048080310700750b05241d6a03001d039100c0c0801c020322042c542084140c880a509008680b15003c0b00e04001c0f051001030403006890700070390141d5055a012040010b045504104a040504007a200c200d500c3c8070a943c0b48280d445010070244200306e580c2114240b1440226024000e0584500800403868 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 521239271 1250 521238021 521238079
    0x30506011a0d0209041e0e0d0f0e0904021906050a0e150304031d0a060c0b070809061308041512050a050732040609090509071a13170705 60
    0x1281440001d0610b11240c004240d0b516000d000494601c05072000c0340c4585a20303615808610b40c0345d0001c1080d08000b008001c00c035200d2490b106082c11806c00c0050200d02203a00788078001c14402d0001070564030341d400c440d403010103d00240010150b90b254001c11941180051000043e41d010301e5462070300d4000d641048031141a00c0d914915102c0303070740c280c0d0713000c2d4510050704080d1408580840b4594035030300b43c00c0007410107440317a8110594510b014050610010141d100f8440d4120501a4000e400648070354040c0b4a80703080550206a8207100c0c072580915400303189092002c002020846905c050001ca034224070004c00c0c011502c1d0981c0e40420b40d40d040314040005000d03a401c1070049884002c56250a031441286c042a0000c000c0b001b10703055009030007000128200c017204200420040c400c09071320451301e0000c2e018060400304900300704510180040d500c0400801c0c415251007106500f80010a0136615601c028004044490f86588079171040350312905041d0110f22843d84141043e00c254 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 521240521 1250 521239271 521239319
    0x18062607110f0a03270503010501080309040e03070c050d260408101b0309060b120a0209010f03020a23030601090b1215180f0a0b180a0c090c0c060906020403050601 72
    0x117050151843c0c008040f0582d44c03000444444a00055207031020b129690180a01801548d500e011000620064076045480b11316103910410090f00450134801d03100d4281c0e1011078450442ca05541042c51a522101072130440241007407464408420414000b001140c04050a6890b10180034960004170340d0751101011290212203001503c4034400ea02c13078610140701d5040007404c0703881e04021032420010155800301c0390b4081032358542036203409100240141911103881d0244d50440d40031030300220b883d2142c41e101d5120111150744224038542c04c9100001c002e0100c1d0625a91458034070b01a01900000a02900c0c116a4040490b1808608190042850811042076440d5503440c19030040591500c1041401101030b18010b4043c14011550300600504040e11581000c6042d40b95404d04900526469841800c01c50002140c1130b05803011181c460304001500b47c0b246d8426030380c4006011008115030703c1c1c1803d100400040364094011740f40a0710403204d04e80e0300c1d10812000c00c0c04e0f59680e80c03c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 521241771 1250 521240521 521240537
    0xb1e0106080612031e030a0f06030f1407060e040c050405030a030801030c06050c06010506090a03080f090406062604140304061205010512190305040909080307030c18062607110f0a03 80
    0xc0102d00c14029a0130242041c8000307004200303a1807000c2101d2161304100c0300d0702f140d503481d5410b100440d015030851400450141011074909071024040c1142242c03000d000e151a107001c0d1a02c10f000d1015200241030160658a2904042c0f42c000c2c10320740240412501500b000c0320219680d0312900661392803030b130721030010087ca9007440e04025903a00000d24079603001041010204c00540403c0181454159440d1500e8940b07104a080009544403500f12070300300700000b01c1c81a040280e40c22442207a0300c2d00c103005041500e0320308010011403400c3c41e82c04200c0c4000180055403d501407101c4114203010b000400c401d0f40c955042111800d440032031401796501030140c4084002c640989841000d210b414801d20706a41c03044205c2c10380c1c00806040e10381e540044108503030300d90140184c01c03103110f0a1400301030104070010fa03100120300302e000e00d004105080c0d20305065240004801d5048401100c1400341c145002100204a03245074492142c2c18024036880d4490407070300180203408154140c442d00743c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 521243021 1250 521241771 521241817
    0x18021b150a0b030718110415030c0311070b1b0316030e1b101119060b0f0120030d020c03071e12050a052a0c010e06070b1e010608061203 60
    0x81e81c02d40d00c030141d844666400c0c1d4240c06400302c6004000801000c008588070442800001c0c003203441d8120702b04241130408a895560704405c1d002c407482c0c0c3d41e00000c0c50800d600d4070520914150f400c202010324641c0c00006114990884541e4000c2080e40c541d02480959509000c003515a0541d401c80c14140707515261440403450821621100300286e407400c04090030200340b075103151880b00c0c0f210f0981e030f03c420142d6105001c81d60290703103800710301030341d10034a00004403000a01401d0900119000310900454002004006204030b070300d00b1070000815529401f210103100d803680d104200444005421000018901e1107046142440340d400560000d0012083c2c0010394080e8400c40d1140f04100080011070a04504203103424401c0303c2c004070358a208603d403c1a0f03441c7c5030b1054100390502060310060700c0c180e0b60300012070f090030760301600c6462191601e04a21000070b0b0b03d0070381445d00b090703c17400114003a50300600f9144121401c031070605911030000c44907a120f208480044036068460300b140c01e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 521244271 1250 521243021 521243039
    0x80a060b0913020703050c060103240c0f0320070803010f061707050a0c020306090d020f0a0c12052a03060708040b0a0908090a090e0f0f0718021b150a0b0307 69
    0x11004c03034007a0404901d0424030100f41402e04909030800ca4210301354800301c440344400414500d03c04d6079162010041c65010550160210071603440c020205070300d42c070302d2500050707034480070b800600d49050300151a40807a1508000640090207045407a10080d17000290440c401d142c084030b8240001102e80050f1589041126254450346c59039043c0803040740c12a0060720100400e0b4402e00310320b000707402c034000c5400f8000d0070300340050341c1040c45a00c200e0030480468072040e000d0702150716401c1841e40142143c0740c00c07411303c81c1080b50415603000c00301d005000d540408a44100c800e0048007610340c140d8881c1320a840b803001c01c2d50041c06a5110f0000240c1d2101e081e0300910380705002e501d0b61810080e203400050050710b07980d044500310315241e581186102e902041030303060000c0494060040e443c3d0000c807007555080319114424442100704c41100c0d404080c1da0454a049007850424040c20725160300e001d9a8003007252040308101800780000304201150b04c20000c2d001c0300140544445480e10300d0039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 521245521 1250 521244271 521244277
    0x60604030f020f100309060e07080304051909110c150c030a090501060e07020f0114011a0307120c03271e02040e06012c0c030c0f0712080a060b091302 66
    0x1280c129455190143c0150384010600d40c103448517550110b0107500354034245060310131190700390740da5910042090140500110549055402c190f6030329030751596a51591114a216500011116107820465100d40c02c4480042291200020031148004219030322641d0310181190011070700e100600101d07800e001e440c0c0003d08901c3c0150000b040058403920780203007040c81514010050303403001e282096400c500780141c00c802e0503560070640c81c030b615000e03500c5240b0000c0501e800381524004001511940181d9248041a01c800001c001d41c1c2e072000c03405801007241e0b00c4241d24540380807007034401e01484501c00c0c0d500c85602001802001e41903580e040340540300c01900f01c0e4050703110400725401034800c100da54000d0800196558001c00650b5203004507601643c00210003480071020000c4003c41d0b00102c036009860307180078903500d103003000811301c25008880f0020b11080201d0400b01042c4d900c60006400355819160400106980c0e0005895500c41c540d040d60300490340315036a02d5014004e0380070b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 521246771 1250 521245521 521245523
    0x1514090102030a1d0307171e0c0108061504091d01091a0601030b0402070609030f0c0b161b050105090714131a0a03030c0303110a17040503040f0603091a060604030f 72
    0x100001304c0450718002030420403035400c4411101c0c0050809401094200f206400060789400100c00b1043c61a07801d90300c4419000d01181071000c0c40c00410300070340310614403400301000c100c102a1100d4490002c0c01c003611031a0300c40340440800603200c07900f0707030b078188104c0800d181d2000301622007501c6801044041040144202c0c1070503604c04007460700343c889000034210300d13200d500c2c00a8011850b160140c803029900e44401c0801c6408540035001602482e00b041e046400b101c2151071502102408455040d0440700800c520000d0300f40c01c104110b41508a81c0c09001e000b400d94604c15120b07118a0f000401c0014030540c40305a54072000704a0129501003051142d400f52803102c8070480e20041000d0318410350040740091040c1c00103000b410741c50300ca03000c6000440d40102d4905071159500800c41499808055448000240400d04211040044400408500080c00030741a0303a82805002440d114005640c0030884441041c440c00320381c203020388103001c02019241001c0c25511881e01c481e90001d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 521248021 1250 521246771 521246807
    0x1c02030304200d050a0c0602010b01080a020f0405041b0809030910030e0c180f06041514040905010c0c0311062e051914120303130f0c1514090102030a 66
    0x290032269260705004003000f5000e01c0040092204525041c8240f4695900504c210f900d4040000e03100e83c0c2c40701c0840d401c40d401920143e1640ca0200841806224a60046901514100302402c6480c0740000a500e82000d980300d40c02a0340d01d50709032903264417603a4007159025204000146405000754040f00e08000040115020300c403621000c40e000003400c460240d00d626810080280f09004405000e234403107803d46003880203081030050303040d906805000d0401450080d4003050368a840e964040700600d50094001c0c0a02c07090280060200d00b81c0c0d01041c0c4c00070b0500000c41003682000510396008004c00e960085000e40021107022400c4101e07c10615000080f541c0080c5070350380d0030078141001118200018030a072426402340c4010030840e50041c0244430300c14030b025480701e0205c19264040300444a8445d00780c100d241c10000c1c2e0031a518014054000f810011a581c1d02010840d10300c907210740c680001c0c101c441d01e041e40c0d580c0203000343e242c0180d02c01c120350000343d8840c20380419100c0c0008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 521249271 1250 521248021 521248073
    0x9080f010e0d030e07260d030e03090402160f080d061d010504050712020a0e0f010c02130b120307080405280303200f1f0b2d060c01020c1c02030304 65
    0x1100c00c4119200785902814010b9106c110a039120280300c8688280075508003040800724000d10b0f1520307402400f000e20310550b404180809820b00720001e03901d04940c0b0038801141c0c1d00e11303842e001c0860780107440000c489070310340030300442c8400c1041e41080d85910391550500c0c01340e107041c00308409840c00504200402407048000503000c912030020f8418255240c032021080d80059091141c50428032a059040203d4684800c0c0561581c44180495440c103840100303841c500200810030030f2440102244445c0300005800042c02140c4028100342e5800b221407075035590402c8202a11040c20034216054005200820030009000c4d80309a198840c0904415180d0401c001600c3d0900840083d0a2880d0f040070b054620062002d03503030301c158200387c03e00030000c1101420101c1c1c2e1540700b5543c00006840702d000007006901d23050750780800d041002042c240d80d62038004003042c041d40181146040c144a058074420140040d40390081410400703034001c41c11541c1e140c540005d094018086644441412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 521250521 1250 521249271 521249279
    0x30b060d08030a0b1813061a0a140901090207080a1b0609030806130c200c030a0c03060b061e1804050106020a0521030c070507051009080f010e0d030e07 67
    0x102000c2e42c4168200c3c0000a00004000c06101d00100c0140d2100c02c2c98800030304212140c108054224070064110400141d1b070754208010681d180c1325041a0f5602441382c62000a80c0d031305140d0b01c6020203009a454058070b907a6201c960342a4001c40c1d01c01051020240100000c407885a181031150b40d1261045924900360381c3c0354401100c00c10b448c01c4d4001000300c02048902d0500333a46e801079034081c0c00010800b040480c1d4008250792007020b50b001c44d100d071f501d0140d420780c0d500300800303d05503c008043d1414030200386410308840d4028841240d040d41420368983c032500d00401038800c101603004410900c918441c5252905074454501e81c190301d035000140f5a1141c80d1840388a01030041c1da002401c44c0443c908010385840915030b19402080344041c1c80405a0311180141c91300011a6040951901c07100c2c13408a0800748140c2010b41c0040c414a001108036500c41504011126100300790303545c035140c803000c0c54240c038004401c000850744400300040c08184690b0011840b000400300b40c5030f8998031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 521251771 1250 521250521 521250533
    0xb0a11010906021209013615140702070f0605030a110d0c112b0c1a100512010c1d1306080a06060e0f0403031104051c0c0b07020a030b060d 61
    0x31203c021660b070f254020485d10060921600c00d5030082c0403000c1e0241c0d035079040140348440c200d005d1251007420b6016044108641b0300005400c0380301c040e506000d80c42038400388881d10030341180d200005106000e17000a400b0901010714046d52201c0d944c403850366640040441c05030031080d24520080908011445054400e032040030310300b4043c2d90720f070b8084420102241c0c1c0782c13031311510261007550b481001300c602e03070624240f120090800c135041c1000400101e05000c140c1000cad81c02d4403203c0e40c40b458204150000c900c041601940c8045840442d07030020225614201d034000010000840c2d8150303040724112009514502c8443c10080c100361094070210101415200c95521441c4980d2200d03105600700801402100c010f4100003001801030b281a02d100701c0c2c85e0074040c00190905542e0103044070008045802c46000e444050020009402d00c903004d20b840ca200500f0545100804070700100f98050128200c610050b00100410741603411034842c0a80c020b009070a031a4042011a150342c00171304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 521253021 1250 521251771 521251777
    0x5240c130815010e010b041404050c1603030e12030114010305090c040c08041118070f0203070b01172806111e070501110a050307030b0a2d0f0b0a1101090602 69
    0x80000d41d49840b0b5403408101d0702e10302c00180c0103c191a0300511091000002c17002c5090340088085a02060b1078441d94807482540c807404800c00f91403030b07143e00f140c2c2c140341d09508081c081032040801c40318456000011000c5078002805a90011500c040d10f482e0306602c03d40000d40c122841c1420fa0340503a009100141c1210b120325507101c0401c8018013004280001c50740e08214054064505404052030101800d403002801001c0400b032019443d84a29500c0c820800e030780b1400e50054000c20596180c102c4076481b403c0c100c0c0e00740c00c60300c200420025281005846020800040568203034515500d607254000b40901001d4020f81010500080402e0b601d0300111030301d0341c2c8400307141983e0342a00e82070aa00303542103081c0d40008440308009404d4008e50103021a0751101d4145000201d803201e0100241211a0302d50042c40000d4440030180410600c620300039034800c1103413100f2034845a481c0b1803034141c2c2c005c910640c9502d12090108800b020700032801d5210b003030344903400007801a00d40d0391641c003260 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 521254271 1250 521253021 521253043
    0x150c1b15020d06060801050a0803070206030406090b04030306140102211b031207020d0201090503030112020f030d20060402030d0f1206080102040303031a150c2805240c1308 76
    0x1603200c0c24104013003908600c81d14003511003918840455420004280da0320300c240310303000303008510000001741482040d5001003203d5900c108250b8042c146420014083d00071801045003242c22000d2f041501c0d070001071201140c4018501f8032000c13071244044407905800014202c0800141441d2100d11083d040c40202904480a024842a4149050000c1c50590390072034a500756850484d030040030400000c2542d044404641c5010728200030351011925140100c030349a40c0501c190030341300030348a4110800740f16044c49080311a500200000100c1d0382c65805950294140d04208242d400c0303180304000500c0780d2041783c10301c0d021880155440004943d102d80c02644c040e54082002c3c0201945070048041440c2820341003548140300d00002410b500c1150300e03101900c000050048840b0500b4080782c550700d50303458030054198580c501005c4c0c407a0b00c0c0090803282d0f801280c2e08444c0078a502c0a01a0a0919000c0e40c45101e40e01d4042150640d4401c032513155080030510000141f0003802c105150b610 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 521255521 1250 521254271 521254297
    0x606011b063201061b02010908030313150c0903060b190b09030d0504062c040920010507051009050a0f050d08060618041109040203010b07150c1b1502 66
    0xc120030800141041000c640c02c075540e11009801003160716070041840c0081e850313802c480c0842030741d6071006882040c01eaa11140060101004200c07041d00203045a440c1c05010344011440481010a40b00072115001089004582c4040060000c54419881f40b5403510028000640e462103001d00c51070b00c0c07540c0703511602130b808000664810303600b02800000170503111810123600f05407e0802c050000d000e50111403185080900780f079003900080c041100c000102c054020022040b40b410148000d80025100340700500c030329000070099501c140120b983e8103401001403c1401c05e80d10301300e030240681071025142762003041304442c08511000702004443d44594000e00380300c045c0010181c0740c507100a0034940b042d8001d0041514503100380480c5040741c801241d000500f10a000a00700b401c3c0035010a554001e81b0200010500000740c40007131000b00c0c0101a03456024468042a80035103900041d8400001d40b80d882c5450314440707902c110403041e4411185040307660800740d140f20498001002100c94 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 521256771 1250 521255521 521255561
    0x70f0c0e01090e0309090105100c06110406020115030812040c05100e0102010b0306040506070311160609020a14180703090b0f010f1205060c09010c0c0f0905180606011b06 75
    0x882c220361151900207454600030314101440d0200151b00c6800502c102c5009a80798041091040c3c070030145030382c0d81c3d41d1103141000081d4841009040d160031502482c0050743c138140e503910b801074182002e80e04070780c1d005103800d1030f0074006903c0300306200010b00115240c5001c8400401e00355a90440c11822a07501e55501214409050009080d5085603c1c2c1c3c1e8001e030000e1090001194000c03540a911071024280420005506000924244206546005403d95a1000e501002015001010600e00840d5070590098940c903201c90020340110259520440e010542080c4500c92000e140c5d010401d824009140501505c9825405000f00ca4051139142c0000061018031403003842040030f0140205443d40d40c1e0116550241d031030300040e00f0f0501058011a40060b103a204545081082e13900c1030f0646103241e80d0f13004a15841d1018010409064200800116980000001c3d14100940c507002800141c566400640d4500e2800c10581035800c0052507160116600740200000c0085a04e08619 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 521258021 1250 521256771 521256779
    0x30112030203131e0905100302101b0b0105040518030711040905010c0903140d081503160314150702101a150304050c10020307140312070509030d111002070f0c0e01 72
    0x41e82d2100b0317000007020f246810140004030540009000a0301da040e150203c124100c0708041c8d5880164002c40c0c0e24400044040e40308100c1d0381c90355079040b10829242888182c80340125480559030500000a96900900c47d00020403142c0c9103e80a107500030380001030088240d2109402d4840c0448640003182c0401020400c00441d07665a401001750748028003104003551400600a10001c0c0500310118021003a0722400d23a03080c05008008684d000007242560351303030710f46902c1ca250b1600203e49036029065441554501c210903030340c810348560b0301515400d05d2100020004060400804011600740c403900c028549078507445440340705441d070780e071707034591415142043c6000742d003034540c0b40a0318140d48441103a6800100307030745619a20805881e0384072040041d15107140207075a000d004154000060000f6a80c01034000d040d11304060b01030307a100e076143c03400c262074411100c13034108803030351103100c040351076920b40c0d03001e4420302d441407580d10b43c0c2c40000d40780c0303500a030b8841e005007800804042c0100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 521259271 1250 521258021 521258069
    0x1090911090a0501050c030a11010e0601080d0206150d0308070e1005071e030509060a0c151a090c0a0f0201020d02041707060801030f06020a0302070b0109062903011203020313 77
    0x4401843c092030140d2600301d1200f410303600c0f4000d40500350306011410320754100201e02034006921900c03808080b600d071503135941f4100c1d0303035403400f000000d01600038603010a540c0003082780344244100e40070b459a041207240f40d034100c8200600511013000c2021070720481703449507204e9a031a0b26805107a40c4072078490f59030b0b0601c4403010800300d078100854110f145a1000003a0001c0948800b110202e4600c1e17100c1203c6502601c4607425404018110042e029a5020948459011048000944000d0860500b20105200641c2d2064896400a560910480b80c1c5580f20300e03040c0e14100144e200140c145201008107405981183e0444000065a0140d540c07074403500b009000c000b401945051400d55140d80c903001c64030181200007826031500001c80b10078460103a011218456030104039000d05603500c04800000748154014016030842e4409102441c40050686003008490085d85501d140d1801042d0001c1e070f44240001c41c25400f0a1140c100034448141400c00140390f001c1c102180e800300401c01d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 521260521 1250 521259271 521259289
    0x1e0a0f060e06041d0a080a050d0204030807290a0e0111070c17030315010c0c26100207050606191701050105030d0c210302040f0b190c120e0109091109 66
    0x1200b480e0781c1c2540d5403e41c21500045001c0c4054200d124555507c44402040b40c0038896620700c011820300001c0c2c00410000d44900516405000b800400000e0110714030b94110207e81c01d22081240381c8980210700200c0b5950301003542d40c40400d000003a0981144072014541d0800c06050f1201c80800d07030700b003040039440362904003d000102e014502d0f500c0d003814011842d0b10400d209074100b040100000c2d040041d08440344028045090708100d00740b9504081104440442884016500a10b196030034000c0081c029541741c1030f840400790a180d078942d0b0601503600840941045040c501e09000540d1240448881e064120be500000c01c103036050400b8145840001140e80041081003656140868401503402d10030b0303042d10703010035074001d20302c1c504a010340525005032804241c070001c00591510820000e00c2c1c041d5000070302c0c4024443d0f5003002c0e280c850f1594000303030481e140b01100142240c03188101840c800c41c141001d406242d21024034604880321074003410b0100c10005059540c0d445c0c1900707a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 521261771 1250 521260521 521260541
    0x321020703050a03030903050d050c0706060602070518041a070c0302010b0324090a050102130815061503070212040f05010809010c02120702040204150e09010e1e0a0f060e0604 77
    0x3054050714607580c850f92a20011000b13410160380f600403034101849002221a0340002e050180600d09015034040003c5d480b140044400a2400000080003800071440c24102d4000400d048035028450804446810005004a6803100c0242c0c8800b001000c0860b4240500c3d02c0750b032a910b039200300b45006821901c80e8081c0d60b20030350000e20400075000c03100003004103085c9103c003482410744542901d02c0c41e150603000020400d5001041311000d8100082c0218100c03a19441103600e5144440100400b1104c19a04c103600144000034007600c0c410703107600840d0016400d104460403042d400c4800091034000307810215081d0300f9000c0400c6950f0340140c400f6001b1400070003c0251440081029540c2d0070b84000a4103240c4010404070150340c0ca41d81500c0c0107200015504200509880009060700d070343d1484180703d088880008640c50301400b014034410454114241245010034041c601c3c0c00c00d000b08032404103915100082c61511060158100401a00c0c0000e112070424108102c06e81d004455 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 521263021 1250 521261771 521261773
    0xf0715021b06060d030c02120d0810090504050307030302160b0103050105071d030706080712051503011d120310150908010e0a0309050d050307050304080a060b0d020f12010f06032102 80
    0x424400b05541d13030303008440e1990740350402103080da00314404103501c0038800022841c28082c0c404004143c43d00500000c1c4070350226580100c29030784501c02c0030100c8030150340c050b08550062200c0400a4026130040c0101c003070218040d102d0780115507451030301e01000d03041203500e03035100c0050065054000714600d01441044907270a03107945903000441e03982c5000784201d00c10040c1d082d01041545000b4141e0040e01629030130103000b40d02c1c24102c01213800c40c0140d24680690b10f069100d51f444000f514505034034028403005098216480c2c22084182d80010f0501001d404004200040d2401d89012403950507040d61a50209103107003400d04c50850300d00a00d0704030307190048044003001075409801d140c156102101c2c3c1d002c0d54207440c14024a5030040e500014007520001802048510740010740544c818410b00703082c0480030118051141030740e00000000e401080f00d0045a4292503e9007000004c550701368000035004d40144084410358406500694408610b0742c800c200c03407219913904800c0804140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 521264271 1250 521263021 521263033
    0xc0f0906031f093b01110c07080c030d2703050606010201140c070308090a23060603030406080a09020f10050711030601030b2e06050a02061803040b0f0715021b 70
    0x24030038007000ca0348050b900300304001045582c4410080f0144c440302d8007100500801080a149007102c625602c2910801e0302c9204628001441c03420000e03801006540c0580542811005420165000f04040303911032502e80c90340d003010200310405040c1c03000550140c2c00401e460304141002a003143c80641a01512044c41010048842031800407a1040741e410320301040103a586c81e48213420410076a000030103411341c41c01a003908844260f10b40a04401c254103584640d143c107010144d07a4441c0d8810304000c605001c0c0043c801d5481d07079100520b5540017400d8100d0000841d00000d8040c41c01d0002d11010810204a040a104052000c001c03148003d40c010101075045850b0030400030320003001400c100541e846114100181080564801d01081310301001a80d1a05005005034000c0c0071100d005204008c00600300d00d0369103416021090b17078003001c5c2d4070709800c20548040c00c0d400310600081c00181040310100241da4001012901d02d108040183c56914450800540707482c0c908030801d00764010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 521265521 1250 521264271 521264291
    0x5090601030228030c14011706010801050f40060b03042607030f0e0d020f0f010c05070902041401020303100618150c030801120305030c0f0906031f09 66
    0x18095410000c03081c44010b45110159101201e0f050075504000c081080c1e14000180c400c9a0f140c449441c1d10090300c90198558a031160b0400c041e0003101c041d40064070090041046003001c0848a48090018140d0202013000c0d21106054a1114002c140700b01070540b6910030110312144258407510074130609111280c134001d070602c0c0030f00011b03002a02c0c6081000880d40c00c588043e03903014100c0b0b0800b8034182c8035456420086c00007140c0d588050f021946040b0442d515181202d05e80101a9006000b042008003034824001e2032148040c2880c1401190b00b502808541d04100d280020940e039100980c4d11400d11460310b91001e1001d0890381594020b006210004d400004003905903030040c0f034512172200d13645120780403401c0342d41d0220f014400c02c107001c50085503018101d00d034244c0c02a00d4201003641d03907010709034180f11884d5001c1c002480601c00306a805485a00400c41041101c07401400d0002c035100144066000f80c0701c40c0d040c01c0c80c2c3d122154102c03d44050600007003031019001c02c544071b81 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 521266771 1250 521265521 521265529
    0x70806040803090a0c030507060e0a08031e130e0103020f1807050c0111030106020d090b03070c0f0f12021501150e100903060c09031401110906130e19050906010302 72
    0x10140c030081c549000480001d196110420044030001e42000d4410901e035584e0034030680304c0844d40070300700c0041c0150303980d9002410951100c804590350b00000303500d82645041c6503034160b0105141e01c100b800e420486400c500c0010044400905142031081c440c40d4554810085031580302c5840314010740c407500c0e14007040a40f051100b03030b10086600307045a0710b0031100c03442c03401401120700800b00014040004503c03590700141c201250724503034544040b407030340b142150751060101701c408c107000500601d80718000401044820305000e00c60700740003200049903a210b416031a88840400c2c01688581c0341051944032140701140103140301c40503000400ca00c5600180261140c841c01809812000a210401485a05064002c2d130304042c0c100f1100b0000d1100908112091105548020612880b00000c010611502904c0000e5540c0c4601d4007034078809109c540c0c0c00c042140b680b01c40c042940000d0b28880d483c0e58601c2100300c52504c071035540607071100804451000e003070141c45134401c1d0014001a11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 521268021 1250 521266771 521266783
    0x402010504050108070e0a0308120702120a050703031808090306130b0610050c0f0105071101110d0e0a050d030b010906080f2806140906060708040e0408070f0b16020708 74
    0x10003844d10208640c1d40d48070541e480c2135081d40f2181c0160509000100344106100074046910346250340303d820781c03252442260386100c079000d61090000100100ca1030503004000a140461080c10003141c00c5803000340e0403c03001d00380c180523107610100042c4150646000c0c031420b58040d144202c0c0c080504000d49440f29001c0c2d0080226002c1c0f200103407101c1080e4020411f40d03c0c4881d40d01c08560000021000d828003800054841134007241800302198440700c0103026448405103090385841c01c00c020229054054540c03a2841c901d18068401c121001c1002072051a0301d40c40a500c010402c200c00d43e0004000c040c00d580510708220f000002c1c801d288442d003070303013036000014924a0314584e050a404132110380d1020340e0858840d4604035000900884075400760107010012905031000e41c0c0c4250a0141601c94031000919103c0700300002d03c410303100c1c00c80903604280222441820300055a4600e0106080004141c411420b02e20400c240940310180f04c0d40d206820b84003400220b440c08400d507691301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 521269271 1250 521268021 521268029
    0x17040b0906070f0203010203040f020a060507050c1302210609010f080303160306090e07080601080f070303110a0206070311060709080a032a0804030510020412110a0e0910140402010504 81
    0x39400040b40310074003000103848800107030010300840d66400c0c071f071405214900d13506408070b0056140000004240340218162200150090080d0640ca00240108100c60031200f5070107000ca44d080c0b002c0800d02648403440c00c6802035903a10f4a04a05080081015942050b032060000c0d4030040003c2c051340c1c10202c01d0301e820840b101c044c4051200c10346030560240a068114041582c60f01112603000703940050007204440b9444155441641c0b40d060490700e484c1c103251400f0755980251810000248a803401805000320310080d00c420484c07907070019065600200703003900002c0c000400385038000c81c24040c05030031080ea030038a001ca079464032008989440a151020341800761840110302c4d6002030402c42001d029489170344a080a0f090301d00a48250810300041d06c00c1d219017030104052681d5442243c0585911041f5500c440c0402d6070791860700c082220310150040d207801000034049400900c0d490241c1010f03005000c45a05415444003111076140355156000084800c1c000540d80010440f0261 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 521270521 1250 521269271 521269279
    0x3110f03160213061806060305150d021323070e03060123150406030510120f061d010f0e010e0601030b0114030a05030d05150d150209040b03070b040317040b09 70
    0x80f00d544103244000700440c0c2d200c0761504030500085c800e545815800ba000361081510200065266500c0c1c1c4040050610555500200c0c0d611a00d0054542240c01528450300c003c2d010a15004c154510710340030004000e81e2268a0044080c0140c087d0400c1d0700007441e01003a40100000d40c500b069481c070805200d0300c11074050001c4047e84000352039214026210442100502d50381d01d9803510b0043c02410100e03011078030b0442100e03010550743c060b240b1400705c0c5034000c2c0c20720000075815152075006090100d0301e5030400d40000341101c030202c02070003440c00f50424080b002920120600c860790079200340c04960400d5802c142c00500020f604070080c1419920380c81e40c08204420b8041c00f0034540f00c8d4600000d01244408907842d0a06409500098400d44c0c007071045d1454003a050007408028010300b0f5000b009001e202d245401b000c1e4003903001d804212001000400d0f0003003020f01290130b1814039002170800100004045c410302400d605c07000040a024021185020310745020080e4900a000e50b140c41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 521271771 1250 521270521 521270539
    0x6160f030b120c0a050619121b0c0204051b0706020a0203040f0b040f0e01030b0a27050a060e1f09050c04020d050a0c180e0c070b0403110f031602 64
    0x64032980c090a0064409000742d03600041001040795642c40c5048410b00c114061000031406003031090580380e58041d030043e98030300c4251419040c1e5040500d0300220f0711496550035150041d908640190301c801c0b14030740366583e101c032803801444195503009201d00101d03138103842c1140e034450010045541c1141c100c440144c84d901c0680080342103104951040b080d09003401404241b000b200f00042c411920010b6030768980f40d5070f03480301551041c070910000c0e00421003000018070340e900342c9d00964007408100403141c03c07000c020020a20845c00c0c2c0701c41592540d1050907080c080000a10642e40c1103c41103006021552030083d070405106650601e50110390303143d90a40b41042800c001890468100900c29900c903007900b103100009200441e1515030150030102120841800740e202c0e00180701c101c00b8803d42e01400c0c43d214012900740a091a00351078000c12981020031441c025141c0074074480d80e83d62090541e02c5035500d20b0014181380031a600d4100300304090514046088405616905a840c002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 521273021 1250 521271771 521271797
    0x4080901031b090302091801020c0f070e06061213170d0f0504020f1215010b121005010504090902010e18040309151d060d0e060109060902090a0b0f07150c0f020616 72
    0x144400421221f00d840d13600114081c0355400021a05a4001c0c05840403224541e070b641c09a046d6883c2c090b280b80d900008108101c488000c4120502030748003d03c00e590000c0d20050365900e80c0c60010b044411030070941d01007800c40d54480e1500030418015080b03e03043c08581044e400081c0d00701d80205105104600c030500c022000348003402802070882c1c80210411880d0b0303407240b10722250713130080701d000c5000c030107030000541044403c045810589106a462609107410600908010401903100368103018030050401c840b669800e03a000c4440b0295140c1d071405003001e180282ca041b40350f030018029140d030450080500355011004440340080600c99100325200100441d82d540320f1071100c014102e041062480d980c00340020014100c07583c81c54100829980c0c2c0c50031000302d0050086d01c0340c4c0444041c1d030422000301c1c0900a000152254420300e0300e0700b8920f60b1592000c901c201982c8903a61b48801d800c20045401c4400d18111041c0f60028158514003001d1598032091400b036080180100c19032441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 521274271 1250 521273021 521273041
    0xc0522050f0d050d2a0506061314061509130e0105180c0603070c12020703030f02120405040203070203040e0a2007050a020909160b19050a0c080a0e0904080901031b09030209 76
    0xb03103159200f45d01003810725116040c25a11a1030498045009056418003590300104502c11106280b980c001000a6030300c80604208005580c64500034045409004018140ea18119441c000742d03c807180002d4941c00d010b15040c25148018030900142c910740c5d4008940d4280484d41060060703089036110382d66034600c1415544a016020b02500c500d03140c8400300382181d000900070003941d000b40ca400c04d1034520001e08a03a95020002100c00c0031406100800841c1051340140d030300304825005803405c02e5103600309502c81c82d00880311031b0f000c00d440304606030328400b501240c1e100c4040190310039031402c20380e91038056807862180b10080c0500c0100002a44203c424490a8400c0420030340200c0466950f50054901d5085401984241c02181041c07902c0c0d42e001d601140d540141c15202c0000111803a00d91a2003a0031a40650f0140b105001d030070001c96a4030741a691040784100d940c2c5858000700c2000400720380c04490344441c2916100c824104540c0c00c807000f00110307941120070f15140d5454203000c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 521275521 1250 521274271 521274317
    0x503041406070b070210150510032003130309080613080d200a080f0403020a030f030e030a0503010e130c0b07170c070e0901051501030c0522050f0d050d 67
    0x2070650403c0c4402d1248007070340401c4007180703d00d404000f800301814040586204100c544107440e0f01c483e0703155006010307901903003003ca41d2010140d40098a480468a44025a4412943c0b8400c0381d4617004102c1c10190004c010a018000b01170003840d16180160952016460140c0054001a808910b0303400c5a6416042264011184060344000d00100f4010390540d1b08039241d40c0d80820030b00000625418028070080c1d1240390941c0c01800f4509294400f41ea50b0030010a9174010992110301001c05400200000c01c22604159102a80d9624050041080c6203001d820540100030b00400321022902004030303003040e60b241c1d0540c0c1d03a07211440c1c5006d049072100c6250758415507801090244c985980841c1d031900b00e41e042c001c40c074895036074411900c0c00c0343c2c1c0446905813541ca80d22a06000355209602c10700b4807100ca0f003000b0f40f5140440d0000590000b410304503c1d8100c1411200b44941d05190000c0c0c42d5030303003058880540c810340075910151070302c07020002801000802201040c03402849194 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 521276771 1250 521275521 521275523
    0x40f0501180b100527060a1e0f080c030d1116030c03020a1205031602011b050105070915020a02300a05151e10210618050304140607 58
    0x41034944002524080c149220b00f00c80d00c0c0140040c3c010300052504041070264006240c42c428290300b0311070070035000d010300005403009801c00a00c1d40c0100d14400c4400310201e030006409a090100361801c200d1140d10f000d140c002520b00d4000303079400b1407691000a04c44510b960b6600340481a81c65804103103141c41d120380f00c0704181c1d124040d03000041c46003540d221010b5170300035202104004e440345480b100755111103500401ca58000c015541c1c1e0404002e1000060500c14076003108203100026110088811044054605941d210f0034448a603030000d46130030050510101151204c4101c0001075200c13a000d04000e40180c60b9150460034014000c5803001110f1114070319600c005d82d5502c0855910100c0358801c403141d103d000c101c88202c031403142c1180d1041c0c0700209501d404a800082885078104060031050301c82140348000705881c12019401280c407104078441a40400c142d040405c240c40303d04040c4106c51003030120f05400304001000f1a02610801170009080012150100d1007a11950344 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 521278021 1250 521276771 521276801
    0x61f0e12010f020a05090307080a1709010203040302180601020616020d110307080a02030a0318020d030f0c080a031a041b0503090a0803040c051806030c10050c0607090f0602030301050306040f0501 86
    0x41c0b64803011740c0080281441503025000c42e145e407900c404444c0ea803a404400084c001c40c400c201020444101d11000b0010342e003042c4180c0382040d035030340e02182500c4541c88403000c940040c10108201940d0400880360321121007000d65826100c00d0360702945a40303201e10603000b001074103080142c00ca1001c200711184260b00407280d079507a40ba4140c0094484c0c00440142000030709212551074144c1e441914508080e03001841140081690355060798a030141590350b20038080c40c11031141c0415181000380070700c0e070400d40740804c1d20a07045c45411540084851428810740c985140c0c0c1c0100540c2c0c10308540c50081ca03003001035036a01e40202c1c0d02e10700f10301b807507008200a43c008104000c001101e80c1a00440f0000d42e0413004918804a01082c0c3c0c95040303c6640e0554403584803070b4503620b040035108041d003066080c00d034509030601e08101c0c1003020498414003c03032502c2d682008000301c000d0701e58008000600c040c40c1194100300000b074032060090400791039003480300004418000c081d44120038002d0040c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 521279271 1250 521278021 521278027
    0x70503030a05031902030603070b0309010f050c0a020d050f031506120108010f0507030902152b02070b061e0918061003031d0d060216020a0e061f0e12010f02 69
    0x640000c0c129401141d030354021281845a80011320703218000e5078018840113028043c203506044000040b82c200a101c00015900d0b282c4010202d0680c0c4030300d5014891485d1000d59a03001e042c0040c0c40e0400b60021001044000c10130f40e100040003c05890304000c00c00580c49900c0314038000101e090040090041c046c05104c0f00001e400001503000808800c011202400745030764454003903049400485010303400c03262081015941085210040034484008804440b8010070b5003240341c0e200880d88543c0d003500d5400503440040c0050391320120344c824000c41c0c3ca4055048603010400d88050310081c420300655003800442c601100f812410120250720b1003c80710340d03103402c0a1201d0401618401070300421100a500c1480340c0b60084410a0302a01500701d100000c45a91224000d512101c0003d0720710051180c2c101c016070380c4600000040400500081c0c460914400b00558000c2032041e5251312086a00c01601d8240c0042c00d410051300304580b01d4000c5821804030310b02603c061180546018800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 521280521 1250 521279271 521279287
    0xb09070305070f08011d101809020a090204030203190213020304030305070e1e0105030a020f04060801210f0b0402030c09190e0c09160504081002030a0507090b0a0c0507050303 77
    0x552115202d80010fa8030080702e00d0900710141c1d20b0003800e004d5281100c0d101840030100303c3d5034070b00301904559800f20f20815141d4601d100054401d441101d8400c007903e681c4440d0951a01e0315108002d444c03004411032a1a103141d001a5840d002e802d4440030840c070584170b1609554607120178440d004500381c401c1d592442c29107002402088100c40480200d00b01d51002c5286003441210703158101d14142c00c10040002c3c010040d030b0a40c2009110a910700d80030440040145601c0c0c02900007003070161200303a40d0394108403501c04c00f10f070202c4110030a60b1810080d030020034bc070140558801d0f500280ca0600310780759800440c0c00c090010f00050340003151501406003141e42d1004200400d440142300308822080650555240c05482040c9a4441159000b04030750380e5940580602c000f4030b909003540b400f55038100160505804801400c0c1c40c5a010003003188506842c002c2035401625031400400040c1426030168180c010701000c4c004100c0602240400c01c81e00300301c0c0c0809090018120782c2c8030f90318 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 521281771 1250 521280521 521280527
    0x1c02120a0f0f02030f060408040515090301020d15080d020304050907180807080d0513031e0b0f0a110903151305030304050604050f0d0219060f0e01140112020a1403010b0907 76
    0x10b800d8100d0080c071400e00095085400031403d207008a80c031035041d5240c00e01e04001c02109031891f150155440b0810403030064542c1d000d100424010b003c200001c01d00072141815103600d1001603200c400310b600020010800143e0110031141514001c1341c02001540b2000030459040940ca401d014025151000c0411500d40000350201100c140f0002c84112628000d400c07581409607028680c44980035200900005440840135003014134400d040940c41c002d25129241c01440c213650b003842c0d0501d59000e01c034136414240200207821091100b100e00d06854440843d5540001d4002d10303003040c5501c03003c2038200030350000b540c041a4009049035102c0c2442e050164580c001503070308860703511a103916103410010104042400c555240c0281c00361260202d1100303004000220121801030b503e8240b984584624854850001e01d00740001800594401c4e980c2842a0103801844203102c1040034940142c0d1440540015a01440c056900c44204040403e0151111f14440ba134002d45036000c020b1600e83c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 521283021 1250 521281771 521281793
    0xd080a181506150512240612040210080f24060f1b06061f02150711060f15010c060b0411031b030106051812030a09030c051c02120a0f 59
    0x50000394001d943e04100c00c03d5800744900c00d4914100d14141c2c00103481c0110102000d40341c02c80ea4585031702c100c40c00d400010b82c982d101003400501c100d52a0240710a604100d0611049803406080001741c0d0300b001e07206994071481c000c10070708a130703281c98510341c2580040112802c28510040d21040d04c0e030280da580030075550040c001030b000810f04690102101d584c0090300314029076000d8080380b50303a202e40d0340c0c130740014002100703490540c81210890f8403e104514010b0b4801e4036144e850495141c0f04500140c00c00101401103421700c2c1c00c106c1481807030795880c526000010424200541c0d048168500070014003507240b072265000e80380c8190079110560040086100307400c10082c411401428004502060000303000760000280180900e9010141440070032500b80e8004041c40540180008c4443c0745030b026007009000242d501c0400c00c204060110800090181112813404125180701d0000e000d207030000e0042e11031540c08440d8104602d09200e0121029001104089040860b061000c007500c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 521284271 1250 521283021 521283029
    0x18032104051e0127080709050f0901150b16050106060503041208091005040204020d06030809010e04090b0f07090f0b1b0105071403090c1c0309080d080a181506 70
    0xd03080d03010b5000d0301503604801e90020030058544150300c120940305050001c8407003468104000681d00003196150b02002840d0080c084070a01260f28503100c200b5801c141d4001c1c0c50076440340c0c100416203038001c40c00310301c000940d84518825500d43c16841440030005208540c00350155207041130110f001a03101000714410f41c000c45060500340740b48207003200c2d1490100c403c03495a404c20965001d0f0842c05800694109000030000750800d00652480001c48185a00c00c0f00d280f040064049410b5802031032000d43c01c6812503040100014030f46841c1c00ca900002c01024418001400041d4800e020b0800070000d030000051114289468220340c243d5903000100688002540710210032030300c9014001e072442070b1a150384641da40400c031466941560005002e80700315020b0500301d00301035101c1c10340c1d4000508000f00061f42c4203180b8100034240c49156084000250842100c0c400300c180c0000c41c40e90019084800002c2d412410a11260900800c42c030080c9410030b0561185581003280c3c000384169 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 521285521 1250 521284271 521284279
    0x12180a0e1005180a2013060e030c06031603090f050a0302063102360705030103172d0a0806030d0f08061c0f0c060c03051803210405 58
    0xa0b9220001c2209008240410201401c0044002110454150031034004040d851440d48280e80c5e080400c501142c01a44414401101c810810004160b10444c1c821421405502410036407005201290031031000404502e001d032440701050b0015842a4880720701141c00c00d000c1e501d40e107078501d0030b25100e00c001082900184911800f10308860001956803440c00200700b6400c00a100341d882a02c002c420014099034090312016040e1212000007c0a0301d2240d8040d4046c18040d6000d541c950340444017902a508210042c40180002100860a182c030149d000781c01c04d4881c000440900780440c01c003404d6400111400c0d0f81000813180040103003c21103101c0d2203055641c1d03a02001e05917282c01120b0110700040114085981c07140c0504005030700030382e02402c01c00c082d61500d802c1011300c2c0224181200d000d00040f0541e03003031180911141c0e002c0c0c011071138421303512116601d0041c803600031040c5601c10445002e640750f88603601040009041c9020103008655112820410036075a0803a2040c0ba0027 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 521286771 1250 521285521 521285551
    0x51f0b0406030e0c0a15141c11040e061519030902041d0616050409060308040e1f3b0a06080609071707080307060b012012180a0e 57
    0xc041e8011501480490004e442003050b203143c0791a406d030000c8400342ca10184401d2161410011034035000034003020344050f4011414003180c0c90941c04803800d8500245150318140400c1c00344554501420b0b4011904941d101c081c01410300c0002514412240000184164441d13801d00d0b8a2300343d000618818021a403c0000a41c0c100303c1d5035144980008522240d049400001d1103801a148481c04107505031403c2410542c8541c9120200c40741030300107650080c000f0800300302d98804545046d5021020701559800044d03c502c070021117601c40c0c0108003400703441d400500f82c100a2142e01d850003c3c400b00040801032113000c060b0416a030251901c42c03190307003046e8000c501000d000072968001c0d68294000c1a0091a0810103000508421408071a03401031050002e54007000700301810f040c6000705030020380c08a0401c0054945100c110701c1c4170481c0504084054040c8000c07600c94403020810300700b666500c038001380030b8021080d5121034603440002510b02142202c400188188518082040004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 521288021 1250 521286771 521286791
    0x21e07110a080a03020709240e010e1b030705070206070503030f090105070306060e0d0203010e0706020f06070c0201050d05040305090a090b0f01050c03042306030106020c0a14010c06051f0b040603 86
    0x185501405401134050303440000b00300030100d001d41c000100d9200d50a143d03403401000140f988014051588403031140814840144107500c184840030360881c91042603880380d052034100c140024000109880d003840b201040c41c00039074940000320b84405512009507079581c500030750001030011003511904055032902d00014030b11406849044103076a0580c8502139001004030405c002303803400b507004a805540312515000c102070701304021005025036130098016508041081d5161001c014501001c000708500301c1c0740544d810004075a4a14041000800c450380d0b141002d540c14411750304210780006a24034001003c250030381c0301244000080790b5140580d505800111010b0040ea8198456904200310412002e034020b1400708820364060b814080b91403030b12001075642c0d00300364050710140c2c003d048407040924042601c440509640c40e45070315002c802900007403e0400c8510000c01c800d0755100807512080400580501841e03c440040400d02c2e00d40d84e140109030490701c540e002003818158410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 521289271 1250 521288021 521288023
    0x9101b0e0f010e040905010b040203071214061f02160605041703070b0f0a18060e010c08010602060c1b070f03171c02090d060e0132010504021e07110a08 67
    0x1c448244141e442c0c841c91010641000002c1c134a0320011249990b0b5100070140b280c8460010310f108001541342c4286001c2001c8190098a1000103501c0302d803801d2504110b20b030398034110a50050514281d181c0d02404412400303030705c0c100b0a00356011900106036000520b10760b003c40200155502d465601d01c0840701204255905d0003984401440c1303083c400000303174454581d080102d9024a1901b004a4401c00c407034105510440d4620f8180c0c0c09a4807070400c441584024050310068420525241f200d5614160300292a20005819a40d0b58034000415a00094821822940e002d0290341a0341d074030b503078440c601d81c04084c6912017260f071f16104e44c26803107021813000142e030045841020b00700c0000300d5500c0303190004d40c011070071030b9842081040c0460206010740310b0084042e5010380000381465410484810705032000b40c18031501481e084103100494025652241110b90654026840d400a46103040048440c0a03440d42810400f060303000038000441959a1541403c0e21414001e0351501d60039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 521290521 1250 521289271 521289289
    0x90b030c031f030602040b13062309030106030212011a01050a021902010507140f010e010b0a03060b01110a0302071e080a0b0406020f0c0f0606030d0f0809101b0e 71
    0x180d00304010500008440d021829048010015840300d800c0445440c4c3e034840080b41c10a030400c04443d40003140407221071024880180281c4001c0c1030580d0705a10700240c00c6107500d55401d54910502000c1340f8810703940c41c250001c07000340d54010403000103d4401d0507254020400764100761400e1511350740c40f50070340d4003400c00c8459030901d503405405881d484403410300b140798400c0c0c3c04034108030080243e0404101ca0484800b4041c8072034000c1d0005c500c2c040b43d00c50950740002c1034600070364034040c0324480075620094030030110ba134081c0000c80c0951050005960b0490381000081444c003c072590b180401d0b5020410005450b00607100ca0140340d522291030250120502401105030701120f259004107260b6140107074428481c520141c94849084003212a981100c00440b42c1c80e07106035000c0311401814040190b1204065008007040048540b00502029481c04404144581e18000c209812000d0000460130b010740030040c030015005051480c405843e104180d0001346083d88954654a0040c0704 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 521291771 1250 521290521 521290531
    0x70b101205060a0c120906020a0807021f050411101e080f0f09010914010c02070b182b1a0a0908042601050f011e05060412050109140d090b03 62
    0x2018555664000c880007094114140018001000b161a0481440307001d9002c980748a47c10243e01c03403d41102c09400c00c00040c01b110300395000301010f8180c105218080da43c680340154000324058850341400e05c52600005004c981014884601c0005217400020f401c0d250300c10401e18203008450b0039011210f140080d9010b01014802001042d000249100001d42203032600000003042c060707503034038104007140001c8280700703903511245100c00940e01402030342c0040080f040424905051a5001c0040e10100c2d000c41d8851406802c0c0c2050306130200500c1e0000c003203020314840803a490741c00e100c00242100d150b013541054070080041c2469070a07000b01812550320400c51070400f0b050804c008060141c20901d42ca81e04030300c2d001c40a503105c0034000c2d01d000316081c102c3d280d040e504100f903401c285044d010200440c0c910380e00040001da1500d208031000c0790300c03401c1034204000c031625120380581181e48000d0410149080c280c820307032901141c03920000f4420f031038035155681d41e01e4002445000c2220 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 521293021 1250 521291771 521291773
    0xd0e0312070b180f0a1419050a0219090e0303010f0503160501140702030105040c05010306120c0303050915070c0603180c15020708060a050105031b06030a090611070b101205 76
    0x1003c22980031240c1c48008003415a14140c1d141c03014110002490074416040035158105049480300590f40b051008202074840c0f5440d0741c2c040006038032025941d2a08020081c0190b005010711196400e400314468040c000c0600b00784003144e01103040d590b07a50001e01840c040d801788c2100004840c90001000c401304440440084002840c000040d562048540140004440200500c000583d42841102d200d60700c1201880c90041c20300000504403403035078000c0300c0080307070080c0301c0c0d0045642d26100b00c013229411701d00300e595030700703014080369405000d580034000701800401c1c036008000164000c00d090b940e1540e0204004000c0d4072242c40d00c03d918000103400107050039070500000d0148102052182c02e180100c4110903990240f1525140b02100d0310501709a0b03800c014001ca15091021950007840ad0600704103100c612400540300d03100c050607460056507a4032800081101a821600c03200041003c1d5980741c540303504202e400303540300f141d9410301071003050004944420324444108100c0e40100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 521294271 1250 521293021 521293043
    0x409090c09060608060d150207032006010815060a090221060103061220030609060f0a060f270c090e0108030c070b031e0c07060c0e01022802030d0e031207 68
    0x14050040c0700380942d506941340a11031811f00f040000c03034002400d2041c0b19698031129182c103080d000402e2446d80f40e10400681001004003e000740014540801d030007000c40048058032a44001000040103511015244c6e0000c600102c0890000d03112012965003c010031032240d41e010011001c81ba1980600985000520304080100d0f01c181c8602168404486c0d8507a440302154000a140200032581c002c2d090f40510100504481c0b1091140d0700700070200c00c24031000d41031409441a2007440d0080a0b031040940700002e03d142c0c102ca070304403810003c655007000022240d4800400c0c05100c0d02034203070002c01d804000941203a00008541003002a00301610004c0e08180d0040400e07032015281a50100350800c1d4080e541805140007406015442041c5580304102d1030142c0540c2c400115440a010720ba0b2814440c81e40c010503034040441c4032401d001d0000d4919904003110401042e800f0750980f10b00380e0a512041d0300449504400c00040b000c840c820540c140e5907004511409070010504144a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 521295521 1250 521294271 521294281
    0xf0f03030c02010b130f0b04050c07051c0e040506210303060a12020303070b0c07050f0106051c0218070507150221041e210c0b010f03020a03081e0409090c09060608 72
    0x1d030340701b1101000c00c0400460103805042c002010749406130350000e0407013000610300040007402c0255800382e0040c89520207400303040840103000c8050760300c0382c5c0b0300950301d520014100f691450500c50703500744030000c409044500304100c035039a0b410031990f46000d0504100702240e80c07044005550010396004008620701030807a504c8002c1e010b0050004203840380180842c0000840030b1140741c40024000c0000911245014100f003002001407000701e41c840c1e15039440f1000350f2240c074041242c101c9210800d40c400e40791140100e40b0b603c15500c02030440d4044034009840d192480c0c00070404802c0e22405214060311760b0040403078210050380d005194510340031216040c50a01c10020340150b0281881341c40b0465280c1e000c180f40c4000204010016001108036800c01501148180c09001741002080d10a420b55001c0340161255000150000102240c12854280e5005000988002442d0b107aa12184e94101301d0018120f900d4048540034508000841c44204d43d100e000100c80d12565501d00c03c1d00e0f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 521296771 1250 521295521 521295559
    0xa0503070b0c070302060706050a0c030203060d060509030f0d0e0c0a060512040c0b070b0f09030a0207051216030311150f0408090f1c060518280f0f03030c02010b 71
    0x811002c00180380150b0b200000543e440e600a0030443d80114404100b602c1d140468030201c0d1822035001003494414028000240c83e407084012549a1191000440d0303101c86501a24500030f00032806c0c0410000190411005030f40e4204881110f128022905604c05140030445042581d0180d100001d02c18000185a44c0c44c1100c90b070380107801a00c140521a80b01c070034001440d485500142e4662001d1018001c003a84421002548020701401460802c0000c00c00291a40500e10509210f20801e030780204542c0d20501080100003030000414601560b0b9140280c10800c0c0c00320003d841c3d000749030b82242240002d200e41d40c81004508003500704c035030f1555542c0c0383c290821020326812810022020740182c442c001c00155510a000940c025003c81d40f500303006494000703210742d07888984803018646408002a405101540c600d010a22900c6c48188c68507801400c1840034110302e0f0122001c0d003d0240e181c4000b1080c6010b994240300d2021000010380c00c0e242d020350550707002041e2018454800e50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 521298021 1250 521296771 521296777
    0x60414040b04080f0403060b1207050109050621010e0726061011011e2004050f0619080a0b1f11071e052b080f19090501030b0a0503070b 60
    0x7201e500f04904201e00c103a9680c481c0c1d04990011110142e0300e59402c0c2061510082509007a0071180007000c09131b04050009091001a101d801c0c051400420104c1c20441e030f01c0d002c03400100c100560f0401a6a40d08505180494256000e8001c00c4c000714050702d0300b01480300c1018006424004811480c0c49950034000302c1041296128208604185006a520310078021190801005040e0b4868480d030302d0104000c40b202260114030400500d07264007059030020050f241140c20407150800654000004941c45219040c090640440c01c80c00c9102c0e02034006440f1405106910010000342810a007400801c4091006043e10100408410141c1034481d904a00340d03543d40b02c0036944202d5075900a00d0030064148031a40924a4900c01800103003003940d6203808a400d0301082c41100e1441045000d001401d42801a01c4040c00040b000000e2001e1806c1b40c8280c030f02245540d002c0c060036a030007000d0600714010140064184a00d5680502d452680281a80d5000b0040c090151514000c646603078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 521299271 1250 521298021 521298023
    0x90f02030f0c04212307080c0415090221090706260f181603021002010b0108070c0c0b040321140906070507051002030408191a07120509030c06060414040b04 69
    0x4101d03282020701010280c1904040d100740c0c401020346d82e042208a90800140800d0a4001c0e45441c42c82444244081540003c035003440000590f0790701c40310032501418410072020344903661aa01031088800c80011200d00f1216942e407010f1910240d4208800d8001e608200410b1001c2150b01103280f8285030345030190044140700716284a00c2c0030080460030304c080c0b4520701c1010716003000100113600341030301c0c03002c00342090303200030000c24240d880060200000540a4000c00c07114860f048204800300d0b5894000e0107640200c0c58407665a4a040300c170900781681d8210901d5944500c442440740100360001000032002a000e00b0903080205101140d044040305651a200c3d1150004690703c2d2109076080342c50301503010356500ca0420440d18508088920f4108880c1503030710b00e82000c502803050a0603546039043c5110800c1c2c450b003c0485030f0040c07080b90740b0b015030704c0c180902089400020003040c070b007109078007031315041d503510700c1000215500000314030303030031201840020300081c060000560300c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 521300521 1250 521299271 521299283
    0x307030606170121051f1506020712140313080f0f0304060e0307120326150405041b0603020421020a090b030f01051009180c0b09030304090f02030f0c0421 68
    0x200003522032a03d0f004800034801c1108042c0402031aa2000d980101c9095040e008200e051f0a860924000c0d1740381810f00c24010185c83e01409402005950039410204031b4240084a81364910501c02450796801e9100d1184c1903c50300001c405c58090200308040d001d2885005103003841d103880001c0d2034044512200940c1809804000705010040072200d280d00c03070195a8500900585100c8039800c1800b41f4000d010b0207821a0401c0390100500c140b030204003c3c19540491591190700d40354400000e80d0b0f04a80b110142800041006640365014100f210300383d0100014803281c4000e61380d03c0c104041c1000c0e420051110040c06038020071780182080100240403541a02c0004158508441c41130f0b406c030000840d074010804c05620383d40a02c0d11080d07d9a0350707001e02e030b40d8180d0705e4101c00a0688a04159610040341c414440da03000d1040d00c0c02042400d200f0b010000000110500940c41250f02800720010900410303801c04021040d2030642c2c04030f0500710711051440da4903103035150482d401203d103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 521301771 1250 521300521 521300579
    0x151d1c05060f07080f0408090f0f120d020723151905071110080718050303210a02270303040306061206050901020f0702090c0c01020f03070306061701 66
    0x98410490306108035582d04103010079060040f0000e110103000ba08002c0100102418480800c4185040b912051401c440560080d2002e10100b0b045210211015038007640c442241c142813000400c100030740c1c80341607003521900c07920342e00c1010240740c51070148060038001d2014846142400b207400c7c8074142005a049003020007001c51403110140e401c1c41b603800142e001c00d030710781041a181c88034410307150121185e40c4c0305584a24010b01e180001800e08041041c100f0030016640b09840e200e1000d050040d080c0ca65924041540f40aa512070b9007809886007503880015010f040f06100755031a20b1a4008140ba1282c40c0140c13032203042d818a03a190303506003c10400040010030504c586401408007000640d540b61050800d80c0803a10010800c00300e903401084030000750300c00c032002c83c0e0103168101d5018100b0385403c0e0292440d4040e14044d9003c42d840014850050340d03241014520645090382c1c00c1c0401030315039100300c070103851402210310039004030350041c4200600b4820221120a9600000369 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 521303021 1250 521301771 521301773
    0x12020f1201021603030b0306130f02180c0714010e150903040e0a06030330020c0708010c08040209013201030207200f0103021303030f110d09151d1c 65
    0x4226441000740f54403003103c9261541c10144c0500840d00a01c3d001c0700545040e24042139440185180c41000600040301036060307104554a001403600f50226950442d0034514000901d028180d000e000107a03400c8505401c41c0e001108140280c45900c480ca0015161000700c80034100e50100002c0d1001085c1d00041c4800715820a402c08502d00c558103540f000309100c0d107981400391100e000301040b41c40121184c8040004041c2c205c3c101c0e20440d02070f500041c0e41c0c0c50300510702d030300305003983d08200069424181407000282c1c1c4016203500450003181c4405907666980c0480070a40f072a0340e02003640008240c1c0e205ca100081c564003214280e0181070240c40e0814941c2c504209c1c0841052840ca000314820342c6401609014078683c103224030071309003140b6107008214001030140340e0748001002c0290058908c628944225031002000050b4412207294903500c0c4c8014046030030f5800b55400d001d0405040c00c544038404e521118191408048003e5620b024100b48030f152a044808400104400e41c6210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 521304271 1250 521303021 521303023
    0x305030d090f0b070203030709080115290d0f0e15130309051206010e01090c1d191502010b0f011e020f0a03021015060f050a180303081b0412020f12 65
    0x1504c0fa640315806581e8030b20740004050420410307600a110580e15006000b0078a8034542800c0342540c0c0d116a00414010140b188000070100314840d8045048002c14a840d0001258110842110454105110701e0024404140d81c540d81d503071280c21001240000314511104211a1050050081c90000c82072500e07a0082001c00c40e110328400701c16071001004011075080c0400c194058910540c0610000051440080030a91250b9001ca1403d1035000c0c5282c09950718110121110300110540300811b0f42d408041012410590f28800036500b4003e81091520701002c5540d01c01038161101910600840005001d41e82c085d44201d0541c4248505140042800c00aa02960717210303500400648021000400c25245140240014200381400600207250002c0d0340e11141e8425140064407088420720403544280d01e40ca00300c44101181c4c10100c145580f12100602c10801c00040c20b45149045405003550b00c11881559500b0045480c0741c401481d01c1c80d0360b000d50420042800c81180840781c845 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 521305521 1250 521304271 521304293
    0x402091c0f0f2102070b0909100f03240203130b07270f140102060c0a090b0a0c061a060f0912160e01060201090506070e062110050a0305030d090f 64
    0xd40d80c1031819a24070b418550820f1141c0b01401c003e10290030114508400c0e01036501900d54420b00c50168280003411120121301d10340003e000d2000300104140c1e889c02d14010015180c41e00310500300c110000c114005145000312405007645034104c680c0c0da0b0302d40e00d030000c00d240c0c00341c41e81003000400c0c21840816007498100021030304c90011111803082c9007040740c48401c0c02a03400b1146080c4007401840d2160380108401d81d001c0d171054060703995020940c504960a030a55046044500c2c404a6548010355001c44c024800707074841c400400000001190360141804400070349a40400e0400600040300104809401070401c0034100c070440c2c41c0345017006424181c2381e0b02c01c0050618562405c001c2e034014420014018420307030000300304404091725141d0726040700501590500819001d08040d64941c1000ca0790101080c0c8a9410420740b40c500c00004510140d9160008000105011a0b20318154941c0001c4a0340070004610702000789401c4006821b40394030680300b00c03207603503506004580c00c0808 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 521306771 1250 521305521 521305523
    0x607050310030f0311060f06040614150307020a050d050a0f020303240121020304030e2205150d0506090d260703110a210b03150a020f13140402091c0f0f 67
    0x10247da4a80341d000e110454109611900c0b44030441c00c8201c80644030203440301d1001595440c0e995407503031f03501020b0340742811410340144284214000580d00c1c5038400c01404402c0c3c06540c034901d884e440c008080f80d80c0e0009075425030401089141003140b00a4001c0301a0345001c0c10304182900300380301c0035070218030030121412414140d00001008101a40800c001c165854122850480058030300701801220100e6000180441d940e40081207802104000851030f429000341482901c0ba800c0c40c000d5140c02054990805500c10302c038402040034028003244000c407442c86407503100b0050103507410140c1c03840580074005055440514044180001000b008440c0c0c2584505032207915410015041d40c01195060005070700d01064030310303160350100f000c0f2003a42c021003a180c0280c8944200300028864910303400390605002030801304000505401400b2103500210031007002c00320710140000e0b440b401107000c0d4004125105042070203031a00c003e03119039004080104401c0c0181c1d80d046020040414 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 521308021 1250 521306771 521306791
    0x2402010b03010c050408060606070f11010e0409060912050306030a110d050f07060815090c0d290f061801080c1201032307050f01030f0b03011d0607050310030f031106 73
    0xf40501001c0707030401c047c541040003621900c0c50460f03075490b00c1d42440069540200701070900f04400c0b0359070b8410b610320001100000c00400408180b803508000802c0b01c0740c02258a0035003002c4003201503000c0c2055a02c6480042c0142000a02680d0307000c2d888104245c80d642d01021042e20b25002c104104201d005400f6080c0040c008141060000350440c040200012601111074006d1603c58940d40c51064022049181d05521204c0000100000c0c00c0b444003420403844000400c038188000344e81c2030f10641038060700c84e1071009000e2018000c3c0c0b4852414503098008000301c58032904d504c9454600e41c1300611020303217030409060032500310084000303078401e6400000040300c00f003071041451504580d4907044c10090002600d07280114802080c0791080a0505903200303203441c030a4010750810481810000d00030025100d50682d05241c4043c21342428089105000014611a000b001120701030410304c2c203d0078000c3c0c0703160303940c0a04991000d400c40400c010080e0149410f44104881402204244 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 521309271 1250 521308021 521308027
    0x309042a08040510020306010518030a0f082106030705010f090b07032015010302060d020c0102070804151115070504260d0c0b0a020708040806010e0717012402010b03010c05 76
    0x10420f20710f040c03404070742e1141c0c07030b1310402c14410182c1c0c000045800449500c1c03145214021060002400d10340a180040c0114103003001d0003040040200c010b0000c90030b2001907890180080049440f880c00c201e0308150140d00415060110750b010b40c0b5921810251441c01d00300325501c6005192032900034130411404211064001c414046201140d811040c04190040581d224000740c050307021001840041d00801e070000c1c0c030101c1040e050f01110001c85c0c1d440d000307555880c02494180480d60141c403c07842d0303d041005004074a94411461400c1004280c07004080c21804180b07245560140502240b050144c00c10001594002e8a01d48940803a842810340403164150601941003002e84c1e801c64040140d5000c2c0c0b900051740a00c9541d070040c02e854401610b0300154a8003840601ca9500540014072651000040410408006a21900d0260343e15038122845c0c0101040c280005c4c0101d4190b039440300c000c4640008030501816250400344000316103031080a0100713084402d41d00d41c000000d0300c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 521310521 1250 521309271 521309273
    0x20304050106172113080c1801030b0f07181d0702070b040e0c0903070305060a150501090501030b1305100321050304140f03120f06010e030309042a0804 67
    0x20b1240c00c004000b1a00c0c844281c0740f030003220649994801c41c400f0424005021210b180600040503140c855030000005400c43e92141031550360748498441c4503100d00c034060015242d00542c04802030489a02c8901d45078542c0f6990440403e1140052001040107500324030001c5a00500c240c1400524142c01009160b0f6031b04e0106400d0840c00502070130655000450401420071410100c81c12940c0d2600400f0003600d418040308110320824481690520402e080401845408540d841c06000d810740704014200c0020b48108217040144102d0780030600307845082120354040d802c8103070400720003802c00881646c002141404c0b14025962502d414003c4001402001000c600c14030751101801d503408094235281070000c000d48002400103080c114400d111110b50302c1c08004140144810406032600d502c031000c00301400d54070071039030307604800b0191002c5410755000700c4140c40d0049019014514140014040c84013620004c85401219080c003210100c0b81144541d4640d01a0081d6442540c0c5e0300741 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 521311771 1250 521310521 521310523
    0xf030302120c091806130e1608060f1005090f0711101d070e010b070f05010203160e090f0703050903161b0e0c120a0f0510091b0c0803101802030405 65
    0x4c080440c0515102160601c0300c80e542c0e520f840721062038103540c0484c10341200c0c0c3c40c01e801c114106290500110413000040f902c24004a24a84500311802e0741754502c0c1d03210b10100301a62460320940d50851440300204001d082a520201d0380413120f4108900003480070fa804500d4035030689003000e0040c0ea100d04140c0305040000d41130112450400090840e14142a0311300130f0880c047c0302d2589404030010300754081007610030f042c08125800ca0000c5480c3c0c6000840540e400782c2e01c0e2807000000c0c1001003907a40714502600c10502510420b221004c0994844000754024500076001031034901c02800401c4a0700d02a64420304564422404140310040b49084c2c00482c03140c036005000303006c0241080080003440b01064800e400f0b5020001001a10b440754011300501d1580c0010386000c0c2000100110f07150040302c0d0b030b021541c948004004142c04035040140603010b00c141c4a001410404022001c02e071254061500407a01d151030005690760307402034441c100c544921486116802000f00302c18004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 521313021 1250 521311771 521311789
    0x3051c020615030601050603070311070b04021906020c0409020a090e01202502010306030611070506070206010503102012010f050a2103090e0c040911090105070f030302120c09 77
    0x20440c449810782d41120400244c465805000d118098880400010744084c4290000c41c0b20300b659881035581d0b0903881c00e02e4241e01c41c0c2284c09a008002060102c4401d48140c4000421a49c0c03907800707812280362440410010700b003054401d9a0007a108500070a070703160f450bc07416512904140000070791000c1e898081d01c1009440031005804075090210000b84508007800984a181e80404545c5044280c0b0041c0c0040c040c0750005064189001c0a180422a5240081144d180500121500c560b50b004040340d4410b001d014868160300b000c2034891801c0b90342c0c1c100c00c0b110f00b81c1030f0083e1021907460304050303482d40102e0041d1002060030780042000000600700341002c2c0c07500399410350509080084510541c0b80a034100c05103507816004440038980303d0007809026000714040c406003401d1081656956401a000342c1d00302038540943c1c141e5850754202107d03955181030710346900f00310351622403028101d0104030a506042e0200524907500f0010b904046c811207185000e03a440320342c40014450560 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 521314271 1250 521313021 521313031
    0x120f060906080a020d02010c0c09090b0406051008070b0d0e0607021e07060e0f0d021e010e030106031104110d0c0207031208040c18110d0c0e01020d05030a051003051c0206 75
    0x24000c180d083c000b50311400f080d82c0c410358081c2002d84000c0e150740342900d80c080080d8441160a85000f006034104109804000e010740c0c00b4280500c01500c807031603064100d88251040b000158031071081081902c4281016060030115090b00040c00388a110b00c0340d0609030b0444039080140c02040340044101c3c07001c01030548103028540104016810003030f0140c6001302d0882500d21038041c5c1100300500ba5a12084a4650743e409031980c901101c441c0031107107910701d070080510b02203083c0d01c41c140c4031410144141000c1303076004801909410000740a10004189054513407d1a02c0c08021010f0340361014000d2250002c131035401400114518100411494030741343d2084204001e0900340804074500800c407000791a4a5a2800101400906008024900001c2501c6100c0c00807038080c50900740d0382d1188113803200b0758032100f96030b01d2600012a2551030401000740426410b2002c50440e40c0544e20055100c41080d40b41011140c0320b488252410b105810548544031a0b240704416003036050140940103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 521315521 1250 521314271 521314273
    0xb04050d0f050408121602031c0e040c140f041706010608010906151404230405060303030f070e041103010b0d06050f0102030a0c0809090906040302010e150115120f06090608 76
    0x844d0501e200240c0b02c246079040c11308408004614020b01e944000003c00125500030111010464007880c640c4c1d08000441030300010450314000c040e20303420f2600554100c070741182c0d51051941111020110b554100c80044126003400340008031f00000b4403148441954201002032800b903140c080003c0030710405030081d0308402d04042040182c0f10900d43c003082246c005040401c03401221814a070200c0c0140d81c40584102842803c0001c2101c0011302da618140b415901441217640343c00901d592840700b80e815806907001d190008000a1103034030b4826071440300410210300b1103243e021a00c103903002078200188007400010380881c112054414240100000d550a0944101040001c0e440e4010740a0f60b80c10b11800000172820404a071044481c600d600030f21031080343c00d0051040d40c0d180ca04607021030141d03203000f0b80380401000004400c000705c140c1d21712541c6960b01700901421101300c4802d2000520031b41000c5038a1004850141c1000f440e004030002400c1842c0c88400b105840b6954040d20701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 521316771 1250 521315521 521315527
    0x1208040b0903091807030906060f0501020f24040f200f09060a0603230718080c060708070510050a02090f010e03060c1b030a0c030306090203310b04050d0f05 69
    0x36032100f007013800d0b1003076412503000220794940d03405901401e00b64600a00882c0352141c00704146062140c0c403006e90780d081e0308072a180f04084d00c20b19656071a10354403a4240d24100c00c405c0d8209100081c0640c8544a82e203000d14401d403907512045c10b4450007400e55800030a010514046040038032281e000950201e17010b08150a1101c007140500d03006006a004058561030010f008030000d20442d08110214130030138000386094039001340340400c41c042d0140c0d10208000c00040041d80040c8003c0e892000401e401d00c2c0c25804d68a0400c0c5031720003801250f25005404107500c84c40101d21480d0701c00e024001d801f5a64405d280c0810401820040d001410b100010340c0c201095100001c1e02c0d50711403580300a50b940c03050840d034074260700c1c411100d416031030713100c0010024451a8400d441d19180c0388203450601156407501c10081c02e90004550700444044580d0210281c501c1c03050842d894039032000000300761014ac03910fa409000c5070403a1300b5500e030b503c82d0b440b07038500b90350000500380070f07400c4c910301281 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 521318021 1250 521316771 521316787
    0xb03011401030209070203160c080114070504050447010207140f1c062007021003110d090602090f0603071704031b0605060102010f15030206030406091208040b0903 72
    0x14140e803040c040a40100300348000511124000c00894146080300300e01444000068503000c4078004907805043c1595082102c511410001c000f91503016600c6a19410304050410090100034040c00c02c0c07501031050040903440d200c1107020400c05d00603120244200900c801c0c244940e41801429401070704561058004100300c0c1e259003036480440320115040c012a03000000040c01038a240c2100c0780010945107076442c1000300c180d20281003080d0030401c0300c10f001c1e0f24091500c078070b010b03001c40650000002018448182d02c264040440c824844000c10300b444142c44104080f2085204115412075001401400c2c6241c074404400045904440c00c504d107160104000b000801081010710314524008041030426006051004c1c4e0402d00c4221144100300c80e040c1003002d081c003540c1003409946414002c0320407180c0c50081e480080050b40110900300c0c41c40e070a00140b64030040c01a1042039841d00d01c1d000040141c120035010a030f150f915010b583c201418010708810010380608216030080000301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 521319271 1250 521318021 521318051
    0x10c171306020d09050402030c04050306012705060f010c0c0f080106050103050604020405060714100c200a21020708030d050717040b010911090907020f071d130305070804080d030b0301 81
    0x113015201c0944002d6100c0c0c42d80c2090380c41c14060b9400c00f070340c98000c540010901d0101071801d001844035424031960620000440d44040b65402d45038940c20514140b14011513500400141c114144104034803001e4558a11780c2002c440956000b0310020b945803d010006036a0502800750060012242140f5092030800054898454940002c10300e04980e204201440e03c103003e542c40720b140030385060203000c0c02d5007801084005003d0441d0110020380035164608034002070b14110301640240418841580314192031420b10ba03c81401c011407003000b01c081b4550000b1300144c9501c42c00050082001e0070a100302500d26480002d40c1403d10203206c08101c00315801c0d91640c0c0c11035506000c00070344206103041002207849503492007034214501506010b08a03a0007c1d0b488031502c103500030303650303e80c0d280d40a8a00d05e210404592034000e01000c089070000e80c1401410b19258401d04050340360030040e580344d6002e03804c10741c8103104582060181407a180d13054000d0000c4050101d008004036840a4204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 521320521 1250 521319271 521319287
    0xc02010b100c081c0f060b09090a1808130627120c0b07151a131817030601030609021204240905011b2c010c171306020d 53
    0x80410440380b215900340401c01084901c240c2c00e641c2401e800300c1e038034808940030380010621140b007607180c40c0c8009203000c0c01105448034508020040f88060b01c0e1b44040c03001500c5455015100750542a24071000211010024403151050356404800d107403604d0030207441d59080c2c500d56207100041c80b000e1080106124515000d80d031401c20048100703a0385007450000083e083e00111442d03140000c4400c01d002c03500b2001ca001c000d0300142440513a05d840c150340d400440a00880f9003250250705081048489a000342208a03900603044118881036140e02d540c0099540c29000c4104001091082c0c3d941c0c98090980a08841e6000f5880d0492006064069110080001d4101c40600d421070650304444005440ba0209a4400748140d80c001d040030750091050340b90180000e01800d440e504454090002d40384603a410242c11491203010302c1c0c5289003450601a1075040112501440c40001d4034071030b01c8140c0801c3c1ca0869506c5695a40302000980000d2b00010306640c01400c0b500c0b0400c0e031101d20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 521321771 1250 521320521 521320549
    0xf0304120c060f020717031903090209070221090420030f07050316050306031c11280308070212120411090f070507020d060e240f0c1602150d0c02010b 66
    0x201c10343c181500304070182035008003a6003070030020300401e15545150f27041d000440c140c0d0007101c1074801502c0e04241641e8445450000010080500300351314900050900030b0500348001500204201624510700001c42c400c03003007081c03002013012050084100312282095400042410400e1a43c101000c5011106040c24603290030401c0010011307945072000c0c00b2000c80c015450480440e28080c40b5009028500040c20300e8440f4820241e03102610702e0881940f6440701070244038103032030780c82e103440032210031200600395002d6200d800800b00f01000e80381c0c0200380c003000d40b040360745030350a00d4503020038810036540d2182e1007840c1e000f05008006038080c40071a04004103003082696907440c0d00c0401ca06900010b4007078426490f18810040004002c5200750b8000301411842104520004036a285030030300340d6518803800c0030900051174210007034000704584030605407144820300d200e600180e0030f203c03070301c941915070200810030005c0210103009482140e5002e000030301220122002280f403100c3c80c042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 521323021 1250 521321771 521321789
    0xd02040203060d050d20011b0804030c0807080702010905010305060907030510050a0914402f040c0c021302040e0c04061704050604020d02030f0304120c060f0207 71
    0xc00300c2c4266039210100c1c0300c01940b003820394201000c0031001030603041d1100b034585c458000d00c10094684403018440c4200300d24410080f00400d10311401c04aa03000c4000303004805000b1104100720114a902000d407041e03c2c40b50803032995a240b036100062032045164003080c14542050140141a591a03960903070000b00c80c90006096a13440b18004400302942c1d0259400542c445400b2031001c00c50b030010640e000301281002c0309916080ea10820002d480c00c00000118114880e00c0f0140040d5058003584404450740140c00849984541c40740c14604040c126003a10500030301c4100180d22543e00d8100c1800301d80030800c3e1060124060060940d5900083c420040400001c03440c4929034151009086009142c840034900158182e000764003501414000c81c08404400e01488200500e0b94801c0303610002078807450711541e0030300001160000d0102d0341409a43e103603144186c8200050070061400c038107100000030711801c2c20304945030641c0220003040b4140c01c202c0542a0002031080481d400c0781 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 521324271 1250 521323021 521323027
    0x10b0105071a040302100c0201020705061b030103080c011e020c070b0c07060e0613031b33030605030105130213140c0d020426010c3608030703031d010b0d020402 71
    0x494103c0c2041b00c020700001019103024415803009a056000d0900c4900c24402c40f54180c840c10003070422500e520304031001010f41000180b001a45000c050072540d24503800210300812400810f540d800701c1c190181c0c0c04d10f0381c00306015034601d60402800004101c443d0b103c503d42a580c107981c507101d036500c1c000ea5003032000355250041182c07680c41c111060481142020009141c992820303528550041100c04001c8e00007400105200b0b4800c5c0c860b2903412000c98408049121440c1090803201480603000c040c142c0da000c00260f152028054144241c284440400100c0524810000c41380e13016512102064500500491201028200b40750000740008141d038503207441041c248081c1c42190412a1040d600d40c080b407402805010207107a2850304403000b4441e010f40d220007200c013000740191508100c2464080c120120055801303d40c0d510340040c121201040d112041940303542e004600480000e551221120f50142d15003e4a0ac1505c05100088c00910700d24000108840242140030740700b15400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 521325521 1250 521324271 521324273
    0x3120b100e1507052406060406030b1239102102070602070b0a020a0207060e0a080f060610020d120b1c061401120c0e090f070f0305010b0105071a04 65
    0x340c0480d40c00b0051920140340e8a00b407602c3e00c5602c425109100c0e800c42402510b00107103401c66615124828039000c2c2040f0305081c509a03048001c0c140201c0d09640228400503d010425414410403404c0400910516890641d0304025071070b03403800d001004842c1c0354024011801d541d603503134006028001480c1152010391000b401403200a4104408581d9038800208c4030b0411030590003138412a4059600303074030350f40d0750191190280e01c10001030f44010381001e50284507075401000c000c01041c401402480800c0e0316100002d01c0e144091103117000c55406001042003501c0c10b04600820040248090000000039040103040c04484dc100304051039101c0034a0340540c1c035020422500eaa038484882c0038241c0807814507500034004004041555103030b45001241c902d045032140130b00d040c2c1c880003d041092800c140c42d2104980641780003503500605803600c0e04144200500c10140a50f0494070086a1861410608542c20b42ca21181230000c24880784020a407000d42064014405040e440c2c0c0355507031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 521326771 1250 521325521 521325529
    0x414011407050a02090c03040f06090615030507150c0c0e040f0b01060e041406180901021e0a0f0f2c0603012c010b0a1101060b07030c03120b100e 64
    0x45405031400102010421005200e800240a0200c40c02501d03c048103845a104d641400d103c00c66003e04180a6006c12310009010f0341d00500e502402039000054003650151000c000629070351040e180e40c1c1c040c01c03041c0040f250301000c481010506050204540080ea44c5000c5204018445d00c2d2800002c000054140070680c102d1400f00c0350303c810941c03015038407400003804151141560b079004d5813400002100038244080503a0054000038000743c00103d8034401000070400003080145607540900c11400d50440012203091101801c001240d03c45100500c003d00b12510701440c0810810035a02c0c04044a4000361440d64030040d65405140089510b0f1060a410220540494110100100000c0d480b4100d803041012150504c100401e2034034810752800075064280115800010204003c1402074040c1861009001c181e1001041c203a540b0300a18409401400c81030300482c0b1007a84c00c6003016132108625998400c0707400308000300300030840413890303d85114141400740103824420203500d5403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 521328021 1250 521326771 521326787
    0xb1e09010c0c12021c050a03050702010e030906130801050108030418060e06090402030114010f05040e01020f0f2a03090909010c0909151e050f010903030e040213080303070908071703041401 83
    0x10318012030404601c244107001b1300701e034010440080041e10700030100d00c00078810f0280041c0da41d9160000c50500070000300700f046940c001c00444503441420280010300d80030a0040b24000d202000242d51614540b68565110600b1300030004d41c1c1d00c0c5001014404000380c5c040c0f40360444d8055858000c00e0b0303100e20100b40101440d00c1c0d10007001410900001d0084a4141101d0a54005860920004682001607030a030b00403888440c4004605011080580340480301904070341c03106001240421014089140c42e110076000c192007071390000200f030105070034182c0e2001d4015040074000c118181b5159802807003030401d800303410b0f41c50751030b00d070505d225460b1051584080c04002070800c820028140f80e5290103c01d502c941401030180c4502e2030607070b41c000c203502421203800d41c40342004414032408120080d4009e000b00450b0780c007513807004110400c1c01c02c040c6208100035125229400e040100c0c25150859944c0f04140021003418030010307565001c800d039000c82d01802a4821041201340060325460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 521329271 1250 521328021 521328043
    0xb0a050a090803091605010201060806060409050705100c02090c040b070308060613180e0114130c120b1b04051003050603071a130b07030c0f050a0b1e09010c0c1202 72
    0x2c200802071110700c0320081940344406190b00034240300c0a03a01c00059003690418071a08005030070500010303000d4100750b00f040318114410f00039280f1241d00d0b00000303043c0355506001c0100084111200304218144030800c29080500c034071900c1d05041c030340640103140e8070130041c1c01000c1204000100f51191203d00581d005d082410141d00031258403607001e0707110ba51b211004042500d040070700c4803202d00c406110320700e01040d03e150558802c0d503800001d19000b80f40c40c3c00c11102a03611990008040c4000c0070900b4a4510584d120703216820441c3c2d800021504401442c0794139079080104011581d5029200092060305003400325140c0e80300c030300103800d03c1003640c444509202c150350001c0103038a21400801104604061031440f90b92602c0540d40c1901401d103000f404101c031700e00d04902055022a821614a00c00c0c0215641c1c2d41d240d03903c00300250029200c058070201701c40c40ca000c0d0100356103942a03016103081d008100f0340d1440c640041c1019160400a0301e002400960a1005842400078101c55 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 521330521 1250 521329271 521329283
    0x30903140d0f2702100210060603051515160f020a0303030b030f120a111e030903070503191e060e06011403030a090603020a0c020a0b03090106050d0b0a050a09 70
    0x1034000700114005015010300603455039241030300c02225070180a011080d103010251421a400c00e07a030742403094103c0c44150440a601c0742c035000030303845001801400042c050356038021800c1d003440050448245200b50926114000300841e0b8250220f601055400f0700400030942d4032685811b0512030141c641e03e600113504500030b03010200926030950403d450b181c1c0240c0481d6803c0f400e0000c500c0c0c580c1e858100310340380100104241e004043c0b1034258107402c00d581e0815246400140300b01d0703104d40c2da031410000350700d50400306a80b0910b00e0280200c00c0203040640280100780f10300c4843d0440c0031001c1c01c000700303d001d0002c42c5002e034220103201c100a141c0c3c407407020400d11180c1c000d00e60340c0748400d118903040030b0503034000d900c6c440c01c01200ba181907451039200c2d460100d04107903003580650464013511040081c40140c020241e51142d12100003004a403000c5550307070814124503401c0d80d41c10f41003980524000c50340100020ec07a104c1c0c80b54484130904000456844000d01c8201030205840d0207001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 521331771 1250 521330521 521330527
    0x711010807140d050f0c040f0302150c011a090109150b0c28020306070e0d0b06190306050907050607020a0303050309010603080c0102090306012709020315040813050604030b04020103090314 83
    0x20100391300844c0905000d03402c11444d43d441b200401407034840c42c020024109601c41e010001070918103070403503806004104840c2400b9001da44a402c603940701041e103400e00d0000c0c0e107118440c145040d005000d407035a140c05200740c18940748603e91a1200344544689021f0000f124540120180702009000c1c10001b00741807452401180c204080ca100e50080c1e05c40d01030000410005030007000440e03500d070006003412000320308035200c03c06610f1006210540024194240710103031200d001c0500085c500c95100010941807000e4418076220a41d080303030f80600d80030042c10000d030303a600100f041181e0381840c0c0f80740d40341d403084000b44c09070001e03500061000320007040e00e16000c05c040d00a05003480c0254100c2d80580e0780d984007440006004c03441c0c48217540d544082000310500a80041c400c10303002404540f0681007255900740380300300407a03060740c003583e000c203060780c08915141041d001004100c4400e800c0505540b00d1151401018000a050540c0c0c0ca060f0303805c0500851440f500c0807418600b050b2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 521333021 1250 521331771 521331787
    0x6020f0304060b06042303010917130e04020f061b2b17010b0a030b030a0b06180702070b0c100c080a0f05040510020f0d06060314060105071101080714 66
    0x801908161001c4402c20f0500300445058100101524100c50300d9820300801455204c014000302036403101c0040c0c01d03540f1044170740701040d1015142141c001e00903001079a00d0b98a055079500740c00141e0482c02c070f4140420140405070b0b503001071030880c8950458031503564952105204144a100c811403145600800e164401072404400901c078003042c0700101000c60b403d4440080b5414075220740719603d51070304000188880c01e0100090600300c08035040c00100b0103503480000b417a000500d80101c034021850703403c108276410042d040221400d0341c4541607405044c0340101079220031041c05581015003001c114290103c0040041e00c00000040104210b10560200d004004500444001201500305010404280a82d114091095030421b0150141000b415030031030182d4098070003c140c0c440241700c0d480d0a0f4229200d203200070807040d2170010b041c109100d40000b0f01007004007541d0500100340400804030310003014001800e282440c00390442e039584103065442110004170042c4032030020407590 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 521334271 1250 521333021 521333047
    0x90c03140319020703061b1e020307081c0c02030f120a1b021b03030c1507030b0909101d030a030c02030c01060803040801051b0d020706020f0f0304030f02010b0d140a0602 75
    0x4400d030f80c040d04060000307429001d542c013010003803450081f001403881c5607000390100701140c140c04605250b1050701d151050301d44406942e60400a1a141c100c8100d8892200c500d45070f201d10401d0002d140080c1d414610758907801e040c10b0143c0704211094004082c001b03818524968045500c42101030040d00f02154242c0009650b261441080348002c4103440c0140c115280000684401c01103000c010701c402010b4480c04808450040c0c040418592144442c0545a0390043c0451050521500522403011010f4002060741d0b103040d90560b41140b12000d03103030101004402c82d08100490308001c13070381d0340120788224518071407921462165460094080b0354060007000900c11241c10800910803601d1702420790360251079640486003041401c101030050001030380c018100840c050040142840300402400080381e015039089816802d000080108141d00076a00e0011301000d4802009404c654001003129503040c402d0107007800c000404a401d445c40e0400020040a51141080d500c400d0815016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 521335521 1250 521334271 521334283
    0x509030901030b0109270b030133050d2006130503150c0a1d040c03020c101103221203140703020c2116050d090504090c0314031902 58
    0x341c002418900e0b9000302c2d601c41d0303174400d003501d50140c440c4481800c842411284010240d60f100809916880601400e40d020300c100c0c003421102c0c0d2610700b5480700121234014180201c24001004964805003071045848941801404551003030340d528000c402059084c900c1c1d40d28140039030740404001443e000c401000b80350441160016000c8a841510741c104040704010101c621388015807041c86820041c41c4101c070060030342035003000041156042e07140418140c81c2e400044001081e000200300b034600c0b10401c5000c00517085032000300150690800300d4880d51002601a03422121008030004283c200c104081c03048030b0b0700280050181c0b00116000c1d001e403a0741e0992003804108200004da58900034001c44d011050b0100192550079890844c0c0e1900384042d44a011b000710050000000ca442c01e14410203174180254000c10030711100b02002003c018076904001e00403030400d00c001c00000c804418080070340358049200c50240312940e40087c514011a060003c028800580c0003541c90340214071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 521336771 1250 521335521 521335537
    0x1602270c21010308030a020919230d030906120f020d06050103050105030a260c0109030e09010504060b07060209010516060c020607030b011b0206040906090b0301060e0603030a081009050903 83
    0x603034a82000480c1c14401000c802d20000c0c0401e4410800541c0c0c5446a500030446040000d02101103800801c1e0007803c0d5621a40040c1c5104e078414201d9200b6140c0e281c3c0135040460101d0b140b410980d440d960051680780c0c0761180c3c03c280440700d1480171004516030072003400d100c101041152105101010392000d09411b205280c042450140081030a0602180a41c10240c0283d803c007c1d014500031031845621600114040c14141072004c030482203000e0042d002c0c0c1a000796109a0800040030802141a0040e440240304911b4820100700704184001510f034415008080181c503842d1560042c0c2e42403245480401d01240080c13105030030000070307520008001a103a802c5a54a50b07030003000790200c541000c0102c2c0814a54007500394440c64000d10000003078800f900c0c0700c0c2490346e10184482500d038070b0381251103641d86803800900f190609102d60740003040000304002d03541c01c01c107006c82e40328400d0351500420069210006521800c0950302c00d40102903912040085140015420f5140d410003c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 521338021 1250 521336771 521336797
    0x20706020415140f03041e0b0405011505010f1b14150c0909150d020a1d1b03010506180307030602030a0f050903030105040903030f09080307080106051602270c 70
    0x8103101100d4031400040481400c090803082c03410403841400c130820380004104945400580314003480102071404041441d1380701d401032000b103092501e0050300f0340780207100041d0380003000007080025a030310035100e0018207138a041c1181207103403001240d40d160103c02400751005400740d01c11001642c0001e0900f0303c0301e00d0b5034040d04c0607407641802000781e8428200120f0b4042014404180c2d03078800703560200486040144440d055483e154007050b84406903600412503c00c011140d00c185002c0300081c0360b4860441162400c0110294440442038017040c02000e014500104c1c85501590f08840800e0b07503004010304580e01181d0300e140c0301001c0d602c00c80704400d0231418200020201406801254019108903000e542980e00340418003004100c10801a800c05072a01c1c0c03425003040c643e104040c4001d000c0c5007100d5403483c0c9a1005041544180d1091042010800c040031304440c452040c04201c0da412201641d2840e600c00c0f0180d0080d808040c0c882d0700003522002d01285502030002032025442e001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 521339271 1250 521338021 521338049
    0x20f040e28170703050f0f1308030316080915040503130906140d150b1c050a06050709080a1b1706090d11060a050c070c060201050f2212120207060204 66
    0x100b900102e01400000a01203582480007100e10800c28000d00021100f0b040355504181c600074200c5402c001a90046a068000105000c0218a9991560603540300c40c1400d8090b030601004556596105010500e2032416031004102040340600803240c424508420407881d9580b900103801c0100740c20300c0b0701d110b01207007140005140c2c14810f10841798140c0054010301c014001103100d00241040d124256448200d0b84d801d230b044042592040451240100010320300045240740403402c43d82e001c0c01030001c1c8811440e0412524100140e540c6100d60b00c901030000c020031004400107203002c241c101c032098550452602880c2e590001e803ca01c40c0c1203030011199070223406d0405035000e4410070300d0b940c41c50700640d00051304608181c000c6074200c821215017900c0c04902c0e4945804800e41c4e5004640143d45030402d00c0365502c03481d001c00c0e0700092100141103c41005480720740d910b03018054028040702c0c0480d04008207500520030105452603441c415903844015140400003540540640c0d01514154 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 521340521 1250 521339271 521339303
    0xc0907090e040b07050904060f03020a06030b03070303030b030a0c060305070905060c1e1519060923060f0406080c0301050a05010f031401021c27020f040e28 69
    0xe25660012038480340001061a02d440d16012060f00c401410001130010030080e119150312107209503401020341c4800c644001341580b0401101010f207030700400402d400d22006006503034021448a080700d03410304000440c1c80320000400c3c02c00c00380e000003400b00300740281d00140c202d070585c21151050107141d03101c030100d5464808006c290301600c1c0c00314809500210400c0000f41d010010300f200304a04e03000301d4800c411030407140c039182007044813544c040403205a004205850f083c05100080c06185109010851982c01e18444211810307007040d51140385400072845503111400d4000403400050b00900040b40c4622045a486000040e614020740c604400200d5050b03c0d88281c6041c0d5414011140c0300d0b0340345480b00071211810b04900c50084d503003041200c540318a0004078500301001c443e804100e484000c002c41e08070300307a007c2980d03110080d54161600182d46803c5a00040041128001149182c5940251600300802420440d51001c200b20100508001004800503032140200310200c0f0ba40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 521341771 1250 521340521 521340527
    0xf03010903050417150103060e0f1c03051503010f0e0c01050301050904020d03021c020607030e060709030813050402030f06030106060c150f020d1d0c2b0309080307050c0907 76
    0x280034050001a0240000c0c4140c2c4109241c452060000c501191104e05540d40801c0c00008282e10448140c0d030742e00340081c145030007440340401e240c0243c809800071410072850070a840326940c020008140e0b0701c00001303040c5100007407106840d08000c0c0003041180c2136104c1010060649980c0d0302c0c402c1c030801e000d04103d98414011207050300c0b8040c000050135216030b42030010842e0140002c90540c0210302c111042d13030b001d584080c0310680b0123900409150404107805400c481441c8803100540d00000100000c81d40c00423503100c00c407507001040540d2401f8642c107141625100d82c20807039000b0b000009102c02d8118000c900c07402404110b00810446030f41d03020541d20011180d0004019420f1390303807103c0c0d2990440d44030101e5206944d83c094946500ad04010301259034110421881d2a540100c03110403001c10865600155420b0700c2184a0905040400d810042501000c100180c13071886080c0805100b690003070020302400c811641c031000e2030b107865070321844407001e140e004162110001c2c20042c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 521343021 1250 521341771 521341781
    0x120804031b08040306020304020d021c03080c0408030a08090309040e0a06060510171f15020124090b030c03030f040314010c080f04110901061101051006020309091f0e060f0301 77
    0x41e1060b0290301d000d1850382d0b5000650002801070380d00000c403240c49809a01d40705240c1054040201440c0b0703010380545406440d01002606c0398103584420b01c414480c80c1800030803116800d24030304040c020703a030b5030040301071451050a10300b0390420b080034100000c103d00001c0c80f02d0240d02c15507041c0015515001400f501e140030100d5240080c00820902d00c2e0a001006015046141504103500e0020300b5100c0300203034495640b182030108901604840000e0b420b2080c20000c5020114544041c07510b11340080d9801004c1c0107291b550b030782c0c41014009541d0100242450203034050180e0340c540d10300e0340802c183d80d005844181c44064020049404111040c0b140107102241a103c8551580341c4c0207003001500030003841159440d00205004d0a40d5a03101c1059000b080290740c4c0d0002c3c0041001c0709400c1d2040901284600800180207014071500441a00d4500c58192001e172410396071041e5a48075640c90060345d1080d851071405c00700d040805000d005100e25001c0d035a1002d5250b0070410f0500301c0d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 521344271 1250 521343021 521343023
    0x6070203070e0c0d0216021c050c010e18090304030c060503090d030b0f090a05070906030b1309030912060903091e0e06120f01020910020d0503070813120804031b 71
    0x40c00041d802d10140c1902d04007140c01c55010500e040c144944006500300701d80c03150b00d0821120081c1001442107240c08400c50f00c1008901d080e04901007d103076141c0b943d50b2125001607050044170700c0280c1c01c0d500c0b4810303100c44080742d480b400880c038108804220344075403050205640015000328049541801041141d00035148140208034411250500301d008085614050b90700c1140c00e001480b42e60781c3c4940041c056014104005075a051000d005000000280d1121060504120008885540740700e0b6946443d20703403c40219088943d45011129200c55400180b0805c1d4281c0c400001d11007242c1c44008224400c2d1150104c00d078440d07140d1244803d09000260600c1d410301428880549003100e5030b9007104010302900c180c1015807010608140340200320604613940890607480301d20f000201c1c2e034100d0500c1e00151808444243c401051440010420700c10710455802050b0b481c4081003044140c030340c0000c91010503e40c8460002e100030030a43e000d800041c4411042d135406140700710703070307107411 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 521345521 1250 521344271 521344273
    0x506030f0a0c051e060c06100f030b1f0f120302070905090c01030c0306120311010b0f0d0303020903160314120928050406082a0906040b0d080a030204060e06070203 72
    0x1910741410001d0070302042d019413071420301c5011890820384801c1c0c0a49001003022029100c5c0e0b2410784014000500c1c3c0354001c60b000b043e6500200041003600f1020342e003005410700c030307108950a250104490241c003640b00c0644c0641c182c1c8000f40b11131440742c4143ca00d510035401d98240d55a00c40c5c3d20010b444042c0d40c950340c40d8000700c003003080940c002ea102c400b5080040c1030100e61030313a4841103030460120b0030b4002e03030200e2621090503221040038414445149411146118414100310200c1c0d42d000b03543c08010b061507400540301d0040d0360108060300001c450094001d034290f8492400c900081c0310060402424400e507220300d10141100c6090390707804c2c0c01c042c201901c090984080a0840c99110a40d00103049170307960301103140d40fa1409407602504c6018010404018202081e0080d103c1c0b82550b51144d203400707078240704550707a29050b107a0000400c4801042d84008103002a44a2245901c024844240060391070b5559815801030001c039401902c2d03000000b071303c40c01400700134410250001c0d45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 521346771 1250 521345521 521345543
    0x705091e0102011401090c2703150908030403050d0e010605060904020f04090c0f111f0f0219030606020f0313060503070216030f2307030b0c070b0a0506030f0a 70
    0x400080300c0d01100d04a80510021926020a60210341d81c0301d001c0e00000000c64031511035207101c0350015100e0350314501c0e54108580d0b1071440440818003404900000b800422220113500354074015400014001e40c0221045549082c1840d000e04541d05c42c0101d444540c1c01c209581146035418801c4001300c0d10041e00b014a4425103404220080d40211424001c0d1074080c480812502003030311a148804001c0e49074014075008800c40074144040306034000000794021050324800191072940c100c00c3d10002d907004940f141c6000c9201d40a406038505a440c0c40c2c194041c0000031561640041040350310f16003d9402c130300c800380c201607160304c2040140c04109141400c03c10010384614011070744202c4a1042d80c5c084540c5072248041d44035183d0040d03c5c05810021030300b0901503a0310280a004020014502c0511001c3c0500303510740000740700240c2030040d050002590b045400003150041640807103180c8039440c040e42414001c00d000d440c00c40c02032240042250400b800010400105904100c510030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 521348021 1250 521346771 521346799
    0xb0c15060d0b09010b01201b011106090304091b12021309051005090a02090303070809120322060c11010e210604060c030908070f0305040302060a050a08060114040e100e040f0605070509 81
    0x944070b24000090401501c01028a8ac1c06010300081d802841080e02a43d43c55140407150000c0e01d00a070304000508600840494000b03800040801d81403543c0b081c0542c0b140c09200c800860b000c3c7d04d91181c0381240c10710041100409400303140f14250740c000c40b0424020749a0501003c00ca0141f850380c6a019402044014007150130000078119000c001444042c6605900aa007401d60f00220b175040341058001090b6514040280143d8001d02003a25100e50710840d09d40747c4030304c80b64201041505104201030001440d840b440710084100a40707083e082505909042d5641c0e640e2821101501d40070315005007988030368820f00600c445035410081040c2068a191100098036824180450500000300400030041c0c85440140025442e25280c240e2608480400641421401000c550400040e45003005030103200400b030b5000c2c0c80d000e040300042a03070360f200740301c9010b510350304844811a011800c10042202c01c3c84104d1440e0303c140e0302441241c80302001903031180038192129030300a1602003150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 521349271 1250 521348021 521348053
    0x3020309070b03101214010627050f0103020d171c0506100801030b10231c03020318010201020c0f0330040305070614040303060503070b0c15060d0b09010b0120 70
    0x1c5c2180d000d124080300202c80c03c101d050031246154060740154144103020301100310f4001444442c043e081f0303001d0005150903089082c444805010083c46a0440c800c5182448200c000075100c0f000002c00c020754582003c05170606440300300b500c4444641c2080d00081c064200407940c180091000d441c8d07000540d08541d195500c45800038150b03042c2c40703240c4200068480c0500e0341294091000da00e1080c0c6014407005100314600d0b00f2141b041540024002040040c0d400001c40f99a008241c0d81c8803a00c0044900413806071003070301c0e00c104070740c45201c692400404000c40217140480d82c03410b44141c1201c900042c1c10b0001310421000c03004035010000140442e000b0b0005000380c5104160029030540809050f03940b00342c05540550000c0d548803000e0140d420100180d5010f061050991402d154010f484070b9600c0c1c0d411034042402c91003031000f00310503895900400e1400c56021895584500c0c01c0c4107045d000344200d03160075000812600c408001c01001c103e40071301403075a400c0501103e0f56014008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 521350521 1250 521349271 521349299
    0x7021c031e091403070c0e07030b0907050c0a02091602151e0c0706050a0b01020c01050708090d03210b030606010918050c090d050a1a010e010314070f0603020309070b0310 75
    0x2680c14861610009040c14010b00041ca8084d200305c3c5a19403042c282407020b803447d40010305a105161516038401c105940b40607000350310124034500a0b94401c0d81850003802c01e50b98120080d0444280000c0c008010b01d0301cac40f0060b08242c5a42210082c0041008544c6114410307136415014034104a42d0f40008415210100d80c0f040d40400064035108c01c0390b542e802212400c661104480f80d95104012a944e4103100c3c800010b00c003443e00a003402c0181e212441c4900c83e0f10f00603445801c410050008040c0a00e8100d41c0c2c41c1c000c085e80d0200d00441064060140c00380088840c441d029040005d42c907580109818000c0c2c80351030600300e904003c0071005130010440502030320458001071050550780d030340c0c405007080018841c0c0058104928240790a404691440c15030b076556074250f0006009107030b04c01c4105811a9000010001d401050510150600c100d50708490000c9640d100003041054144d0010340c014510201260012541c99180800a00003500d02408203e40c0d41c6080110070141101c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 521351771 1250 521350521 521350523
    0xa08040605030a1e15061409040b0406080f060109110a091707031202030d0b0a05100503040303090503030f06010e0108090309010e031e01060f080105100905040503070b07021c031e09 80
    0x28490106015845a5034100341e43c1139021911780039807035400d070325080c00c1c04000d00480c20007000348551007130900c41d0340c000c1d404441e01a9688030003030a0a9a2250000382c000c04429080c0c1c1d1422021980d5183c607180c00340110300301d01e400c028840501500342c0085914002c13031640ca81d11080d013040702d00012550303082c1074000f1911800c074000c0003143d100c0821082e4258590010344d9220307030906401043c0c030786c0b21043c18030440403580c0400854484416003003a46041d0b10707210b6666550742c0f0b07050b40140405c40c00900703a880007000300804148062500c43c01518240c0b01c0700c10a640b01001116459011078a0000a8000380641ca40950280313441540b241c1c001015603180a18a2400003e6445504200c0326140c0d10f4410402002d01c5c0c098078100582304102c02840306180a141041200c1070700d1240b03d0419503203500041c1844002d0050700c070901d912014074041800d12000007584d03a8403054003400c0c0d003a4241da080550601901c110344001c40c040c1c0b04078641c1c40d952410b4000070024000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 521353021 1250 521351771 521351791
    0x70e070c03020a2f1905092a030414030a0917070b07060204140604080c01051c020a0807020606032406150310090f020906031801020f0d021b0a0804060503 68
    0xb00020341800190040b44040340464504180089a81d407900c1c000c400043d024050110862002040c1468508140e6005680201440d19041024001c48d8407860400100c5403220b5440c10344601804000c50280c0d02030100440b02e06482d0801b26200d204086410000c204080d10400000c82c11294001c00d1105660543d50300d03664448410040703510100040380c00701da00050900c240304011140b5030840e042600c0003420700d0b00700b696080d0f41f0f00d20030600905008010501422520081c0440304d0308450b414406d646403584020041c102c0318080e036496005d4041c1d800003e0560400103200d1142000c000020000340e070815000400710030000d03107015003080109a0b01c42c14401c41d60011030107141591441c4442d98501940003040382d40049481e03c03458010000262246d6130801034940101c00ca410000f90301828280081c028851003050007250040890031503e8078502d540a4459048003125010600544109164880b0f52080d402046503806110602149104402869010342a00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 521354271 1250 521353021 521353033
    0xa0b03030d0e070306150b0307180b04080a0b2a03060f030304031b0b0307090e1e070306140d120503040c05032b0e01021b030a02190f08070e070c0302 66
    0x300000705441a03864040e400c0c0d03110f0031007041044146d102c0d51281c0304224901281890500741800b40e584400b5088204024010000340d041c00f80b03d01c030340f100400d805618565500e40c1ca041c01034988030340c84c605448003076039100094101002d1b00c0380e911440d03070401d81c4052b1100c204850300c8582d03000500540d0700310342c954031441c0550320200700a10286018146480454000c0840c0141001c0d0703a8020481621050082c0b1000c2600000440c05a5204806031081e030346d80d402a25922041c1e500f5102c4040d03e619051001240e00f41c5e0010b400d803004000c5c1c06040c22207400c00d009143c000c9010040101e5250301701500c08601c640059a0081d20840c1c2c2e040203141d585001038a8018940c104114140c261403075212401e5161194003540c6409082030400941c0320340c0040d4a50040a030350340d010b03440c40c1960340c501c0da4060000c2640f403940205000c00c0e08420701400184201c030750113440d68407030300c041c0045207420000071503104685014065108954900c4011951040030340403c07425886a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 521355521 1250 521354271 521354287
    0x1030207050c06040b03010f06020a03050405010804030c05010908090103060b040506070b04030909020a0816020c01080c03100308160c080a050606040f0b04020c06060a090608030304260a09030501060b03010b030a0b0303 96
    0x60f81c0200001d003054000030b80c50f541404210021841d180d4400d20a660002140d00e0000740c000041d14201d83c02400d120b41d059441c1e05064a070200c9404000b071865103030641c4c41080082c4140a00181c4000783d0f0104526a140c25409901f4855406030990120061114030002042c207080719074410301c87d26001940c1a40c5074880820b0742c0014000d48080784080c0c04101c00e42001c0e100320401208a88000e08204480e500080c1802002030002d40708003000000003860705078909202c4006580c008100c0d03545e85c52a820f0024811b41081e411142c078a8011400200c051000500c03484182d000006031005ea2190001c0000501c04500304007440390700e510140840b55140d01c0502228122440680000d242481c100021414583c0110034000e02d003850a005032000041640d0740254400440051450304150314200d1045000c99508002d0001075600c000307130f50001d01c40c0b00b164031036402400304076200c42958049002c24017a05940d043d00344001000f00b68960020040d203d00a0192460207201d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 521356771 1250 521355521 521355529
    0x7150c05030f0403031d130b12071e060906021002030717041113060b070305070203100507123c0e0712020a211515170613030e01030207050c 62
    0x12040344082c481102181c10418140c00c64040040e110f8881084260010741e540080c1030361103100c00c0000302560b01c01c88030401e42c5468243e03001e418245012140c242d503880d1000c00040250b41603c045500300144001100d031b01500e049170036941250050940402080c86210080d0402404081000024590952600c406007007070383c0128064a0400c9601815030b00384941c4420702c082c0b1601092400008010442d0300d5415a200107505150071a6111541e00000349040542c40304509201c0c03a01061003011a0000e1a40701180312128080c0700c41110980000d200f20500a02c2c0c410b43d510031820020390200294440d050f5031841100000d0002045501b580745c05141c0e08040c00d044000d40080056150030a210b400801d102d03458580c0d16801108d80e91980321940d48010018042e022001014185a400030070740721000b42d4607601c290381d0702c0051114920074991064890300441002c04d100083c04000c4541da69010b8907035048141e42e00c00114000d50000f6025580ca0041104028146e07035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 521358021 1250 521356771 521356777
    0x21603170906240a0b04080c03391203091306030f1502070c15030b09090d1817010c090e040b0712020405030307060b01030b3705040e010c030c0905010207150c0503 72
    0x1040500103844074181f5030000e1500c41d1003944984241c0c03014614203140d102120f01001d0602a40000f010a009451b410340910071100140c0750b44240c548010484051002000d0556403008540c0c84402d010201c2840301280c00c28000070300706840031031240010848440889001201800740140b50080136150002c0c110741e960850b001000340055414032082c0e040c0103c4c2903010040301d00d200e00303003460001a0b5480e40c505518409100061940905080070b00e0031641c0100404010f2100c8510444810750083c0442482c0c1c00108035451780100f94180e20200043c4580e60108803414152070f00c002c10784074003600c00030401581d078003084041143e89040c00540415443384902140e40c908100003d4242c2d2108006103024901110b00307041509400a003041d101c4d1041c0c081c44c8003600c0f40000700d1801801c0c5400040c0c00c54106000c50b01041c505500441135040503030342c01c105941150100b100d4200c01072103003034016880301000f4400c17100c401c0a002e03412002410f103003081e49010358990341150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 521359271 1250 521358021 521358029
    0x1d060f040c0816052814070803011d01050d0209090c100507060e2a04020909010e040204110309030f0c1c0807092124021603170906240a 60
    0x50601d4080c006003500004610424a4031818054103151402e001d02c40c8120b148031707070b10581c52151051104868080d0a00065040342080441c0d500c0029003800304590b4000c0c0b00381d9500c4c0314440545044440c020060a0580c3d500901e0038000c020203808025143c04080c0c8090803c1c040d502c151030307180d5180c05200351078540588400b6183c425606007003003115038481400000e81c020050380c50740e8459407861100b015101041d180b520031a29000b16001f401409042c41d08401f2920000c50100c0d881680b0307503c1240700710360510059809800e040b6650105440101c40c0798028000040000d100e2005042448650021a9a05c01c2c9411140110704808200840403407503600601266552015000002d0030481d2403031450240c3c42c07004504034000001024020f10091841c40440c0380740b03940107099107034100c04155262040403550080000864030100d0106040c5c500908040018500ca0361107190880050600b0f507840e80c0c204a548161119000744540354110001d215541e800040c5001e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 521360521 1250 521359271 521359277
    0x181d0304090c03050609011d040f0b07030e0115030b150d0c0611070905010303020304090c0215010314010b0108060a031e06090506060418021e040213091a01091d060f040c 75
    0xe02c0b41480c0a0100c5a015003160700404130200140240441c0d200500c03540000c100421119a4507800d101c0c4480c0d541c1c0c40000e28826008042c40f41d511b505401685503c1d130400c000708500c0000e05202810310280381300042c07000c4183c0002840c49880d40d50041d06680019040b102c0020044c0e440a02c0d013901600031102103403001c1c1e850b240070a4204588000741c01c0ca0401004a54150307100607550380140e01c68490001e444406640400c0e1091050340003410b05580d030000e44e56103a00e48a001c03080711400c1e5040e603610301060300c0940d62280402c0c60040d900600000a101e00315180c110003195a085a101060b02c8403003510001400380c804c1050403405100035100c2d50074038404200c1078a4a00f45007625004068519801507a41c1c4604401c504205a0204203071240d0030010801a001d2840301c01020340e03c60b0380019001c105034000100c2071801c0c200649500320018015280301415005002c648460200d0108011a814441c6500700e00000c20f413500403480b0000280c1500d03d200d1881d000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 521361771 1250 521360521 521360531
    0xf050903130b041202060904020405041b030e070e01120503090621060a1d040303060f060306030c0f0b0f0901200a020a0501031b030b0a08151807181d030409 69
    0xa00c00d184070090014002010a081c41d16141c851408006014200301a101c0c1600082406507581c42e0741c1280c3c000c0502400c24000d12900024103c90240301c06000300100f030a207110000d01100100d0350000b91514a042080c6603401d1050034a4441c0240c0b00450f41071104202c1c4100700d588200242070820b5800d19803582044800c0560118031102620b4240242031202d01488400024038000b400250108400403481d6158202180600a5544848030a54401c1004244a94190818015a030081c04d00c40100742d51810070107816031861060001400302403060b00c8904803180010701b440e01c01403505a80c680d0658007112480380300d00c0400c0c1c0e1294041c2007a0000c5041404201d030061200342020400030f01500d0340c2843d001007440030501055a108104510f0b0343d0b4001e2141c01400400c4115400c0c6040c20300c1d4440e603000195152303648070810a980c0e5020301d40025401060741c0c43c200c41c0301d01d8114440c1c0c0300405448403040d0307519410003454903000044001c102500003001c0d0143d0207d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 521363021 1250 521361771 521361787
    0xb30010203101706040b0402012111070c050f030303040f060e0d031e050609180109050d0810080601081f0b030d08010519030210110a0c03050a030801060c031706040f050903 76
    0x145000108003c140760442402c200100d030090200382c0e8030540a00741001c5c2c2c103a440741c0b80c0c0f41c91100340604134041441d00c2000846e800c0240c01900c9801e100c0d503075640c080b40d119400c001e4414441481c2e03c2d0700d80c1c010800140020341d00c04558054a108103804601d12801c490a507080c0009100c1030340010f03030380c3c0310156140d8070940c08c0c126890650b004200310505111020400e074040046c0380c400000200030411003008001d6211482c4182c1010645515110039600140140d400351100010084503c0d80480c00580104e5001d04070744000c00105001d01c0c1c0702e404000c100302100c1c05005255652031543c07005440c10300c28075030741411703d0366480840c0d0b04250070001000c0c4c3c9081c0c15038044012260600040c0c540340004508075030745003040200044110041e42c640140c1400007007031075810700400010084005543e15415200b511201c0706680c0b070740003c8480b00c150120140c00154041c0891801c0c0f070300340000c16088a0040c1c03000c5102c10303840d11a8410750314241c840c401d4540c03002501103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 521364271 1250 521363021 521363039
    0x60c05120106050a021c050d110405031515040b01031d070603242313060501080106050711040504020f12060f060607020105030a0b0a091415040b3001020310 69
    0x58007604143c03d09a0038a40b149200950f01e03d9080c00458000c000c506034142e4483c0201c00f500c11004681805110110001d05210156041485040e009101c0c442d4204009803248030610b1140d03440212810b48081000b04000180017403a29480c14165103a00034401c0e125812584814184010000c3c4146071601078020101c039003800045440c038200750394a4500c40c0c0003e416608072541e40e03903a030707200a031004414544881902d0f0000c3d8442501d5000701c00705016904080225042629020700503030340d03403405444601c11902c0040c01031589083d0302803c0c0c40c2951007107800c14000b501c2d8801103044039011030f11030dd000707010202281e4003440030498010404680d0b2a440781d402d03a00c0a08002156001070038034040600840b003c1034807200d9001a42c0c40f4803801c20020155941e09000e5010798910f14084000c0c1603618410040e0707c0c0103201c81c039091070b0054035071014002d081c2c0310f407120000a03c00004640c43c0164141d101590900d111100000d00265010701d40607103074a01564a003000031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 521365521 1250 521364271 521364307
    0xd06080c0f011b080c030f0301031203050f0c040510030905031303140c0307180905030d0506011b02060301090b030a1b061205010602060a02090607051c1115011a0403060c05 76
    0xc1030400100d4010403d045014000d141d1070079500c500101e0b200c40001c1840740c2035018101d11604c00280120000080c00b19819560040040d00d460400c416120040b980c11000341c111100d2003050b404101c01c0001c1d00745001e042d84885c3d01da00d030000f40a105a551a821075009540c031800e102401d1000b0f10621a0648010340b608420400901500d1072003808242c848040e80302d420780c0307400410b40c84d4001c0b01c0290402c1290300e40c82800e0701e030344401c1d50450000400080e1005030005103601540103a02c10311419440070140c0090400e0b085030b00e401ca544004c0c0000c2032200360103000300c00c908000240e10b400038214400400358121030301414088010950350840488404150801c401040404c0c0c001c00c1480d08000140000f50b50381690801140e0b01d4450300400826910541b0010b00c419181c51341c42c1c11070323200c155075200c0c420071000d091542d072030240d443d01610f401c0000c4010010403007291412501a48518000d81c24599280c5500085505d80c00010f40071270750008d010315100d00301400c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 521366771 1250 521365521 521365549
    0x60b0a1811090f0f01110703081201121112010b090109060503191109040c0503030d05010501110c010503130f0b040305032508041106040918020f091603050c0d06080c 73
    0x300d00c1c140400c0a000a100c4100c994219004181c50b5a413518103074450183c0c100503000c481c007242d00144c0d488c40c00d01d055521490785e002110200c440040b4603400d40302d600d00d4000742c0200c4402001400300b0700300302400c40d644007042c103150b50b6103014801b50f40318060124020718407843c000603841c1c48d10041c1818240e1110701c200c82c910b880301c0c5c00070008030b908100d861074140c03d50701c4142568640c5482c00c440b00e403580016503d84400301d40e0b0194102c0c142c0025060700c8081c0d848407503a01005506942e50940c171460140490002e000245c40040031440800340c1701c0c0100c01113141084142c03035604505005607419000101c0000030008102c1b000385003041c00c40358003102038881d038900c41002091414041d100030f2010303510542e804c00654954043e03c0c090a950388003008201c1018495060140d09400104c0c0036410450740204185802c00100d031044800300b101d60121a206101200108001492602e03042800d011501c0d00038410301c910380103003070048000c0c6040d1028404010303900345a208 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 521368021 1250 521366771 521366801
    0x120311120a090b0703031e02070311190611090d03050301030b1513020307020a0230030a0816020708011a0f0a06050901050f04122301020c06060d060b0a18 68
    0x35180580303902c10840001c88a040c0c8501c1d4690500d4507003240606072079441450b8201c00509500d001d40d425500412000b4441d0302d07419404080c070a040c940b510710100e1050020400f550341070700407403402d030841c1d0125035503d007040e89046004400242d4016501d60b0650000d00c0100050042192200319503410a1195182052039508100015400d00405215901c03240c0c002c030205040500810032580e129a00a0000226603801316405194012900c070126103004540010034101d81e010041380c0b0281150356402ca06643c40440c96441004000c00c14400c40c030418038000380381c403028407481038030025182842d529000d40404028285000c0b4101e41e1044040e007904004035508401104d03890700c8282006e540316005580c1c6d40300180190350000004410301110304040145107116203406040c08100303000040300c0452450308030300078008030040507401140030a80c0d6180113005c14550902c43d40c00400e6050100700030803180d0b246540580d618a4080b07080e003803d45a41c0c042c661051030810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 521369271 1250 521368021 521368027
    0x50a140d020f070501050a02160b09030705010516030e1503091024090b01111501080d09030b011e170d0306050102010b0f041104080a080c1005060102030a0f0912031112 74
    0xa201107490340f15500c075040c140240000e0105a4900130b00c004840c5040b018500500a03a0383c3c60500d415920000310f80d407280c0200e00000c900c2d0360154099072102d21000203c1c4021030103540d800e803111407000e03071000c1d400000d0041c004007500d40c1d040154410000800903000394030340b03117000c030083d14000700004140902c0c8580c0310502e82e000300868000c0b200040030224a40360f04200580e901100121108818020740301149606d903030801c0104e040710f01510443c1c05401c01100112606522400002c080510101c0100042440c10042126001050107030740900c603a54071701c03c0c59140100d00040c0c0b076a04900500c0c1c2c007082e01131095200801c000c0c0001d0000030151070024a030110410b42003482140c0d2082046112718440d01603802420710201144c5004005040510458001c55500d0709103100300105840b41ca85c0c1406080c0c0103a1060300198200040d03003000742c03040816503481108008899030700281d004115134036041c01c1c0c0d0098640d040c0144400d1801360034121218141c0340031540030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 521370521 1250 521369271 521369293
    0xd15050105120c0f04060201020903070b1306081e0a09030f02010608031e040909030512011e1815291303081303020303070b1812030a0216050a140d02 66
    0x300c0b400600c220400c0110350766000c20f071020f1070042071610001d001c404200454002d80550041405040803400c8a80c02c0e992041c04180ca44522000e070b45500c8868403040100300e0180c0c8400e9000308202c40b522244640082100440c60401c5814001507034031015000305140d08402d940800600c140300912846080682d0039a60384101001d200c40d1846030340c1005401d02010041d0340c080d206074042405402c109040c010030581010408000040864000080010070702c00001006511034112207105450300f00410071105440300d0b40d6800c951103160f2404900a4120306101500c02e050741c140f0803480c1c810041d40170030f080012107041000200704007280300c440e15894000b16a070007103c0d2943c84820007158864040e107684001d41611000c104002000110010184104180150368065440240711240d0700e0088541e1041500001c001003a5140f646e60010000d410340460346481c002c10039940c1c2460088030b4034041c2c0e0303a101d200c03003000400c00d4240017181c0c0640d160f1004050120300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 521371771 1250 521370521 521370527
    0x61503050609011e0e01090e070902090a030206090409330603021c0c230f0f010f030e0f120705060619050d171305010f0318020d0321020d150501 64
    0x18014203180944c10249400b00040304804000589118a102c0100b96520f48112026016000070040035019510020a0754031007172003541c1c078241e07000307091908680ca03640034403980f5400801c40d0340c0c22030346035400000400d0100c001c0720354290400300c03901c100048500125045000d420350310003540b410240d003040540c0d20400740e0000442410500c2d224a00c07145006c1d40800c0c02c5510260305664001c807518001503540c001901c005506464174070140c6145400c00c0000b00e2110660b602103241c1e1f800c00c40c0c1840c481d03401804034140b04411644140c4400c00d98a00e00700601d24015030708400044e070002084028044180c020100340e03485112181c00d0400c2c80755016407400742034090f07105482c00d44140f1800e4992500b03c0007120440582c1c8801c40001c04190811038084d207800301d0081840d07070100c1446072003100020f045403960040010040c1e070801007103540080c025410048506984102c000a4810b0800130720504800181d48030b240c00c5228041e40e1507903401c80c0c40540030000400007660 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 521373021 1250 521371771 521371789
    0x100e0c040b041d210a0512040311070f090b0402030f040f03031529090109031b0506040e041a0601050d0902150307120501051e121504060615030506 65
    0x2021030300411001c0c00200420001c1086184565402003003052501c0310700d9010030402c0305900062007001411207006806045032141c010b549002900c00c001003d141c8114084030340c0c00500c2441d049400c2c400300c042003454082d03030382c02c1030b81c03040340085040040029600c10b20268040070b69095045103072826102c80034400c01013000d002e142c40000c1201c200740c0b00b41c0c480c1d800c010300c1c00c00350241c458403041a490b8ae4100c080064516a2030b030030a900e02c0705c1c2000d0503140d03092016568111140d00319135411040960845c401000080c88810105850f41c03590060030180c005251444003500e403d0805001100760300b2a403d04504140e0207115441e6800030840c0c1461408420218409100f840880c40c001011040c400d5055070120503c00e0341c690202c84503801032034a00c1d0501c142d03601e440800202982d6844280c50500307401c2801c40584c10501c00306440c110201041c2c5200b10241180b50145c030038101c1e01101c4c000c2d070700e085c14402041c0e184038400c0c650915250030005498184d0100d82010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 521374271 1250 521373021 521373043
    0x1080109080306090c09090c0414030c0f0d020312030a090c0b0c0c060c100c021606110a0311070807030606030b16080105121207060f1b0c080a0309021e03100e 70
    0x50800c00601c1d5540c01c05c048405140000c2d1450f50103180040741001c040c1c00c070780608141180c60701085800d900d00095150418080101a036a4501600081218070f0049100072a09070165044903a1105c0c0150055441900c40050105a200c807910b0410400c414540103000c6801c41800300c1c0c2600c00000450131500340c0203980441e9103425058100d454080d151108002890400b101108400c2e400301c0c801c1850350b800f2080706035103611040152590860210010040d6205080c00808244a0781c40c2404452a10301650b001944030403074607043c012181c0081e075110fa120348040040100c00c642003a0b010340a030000e992441d0200e08010140300701032003a02c2c440c030065641300c83c400d0024021b0b10034540b000314185566064501d0325401030034070016591000782c40e0882c0c070100170009218240d0445101d41e01d04041c0031541e035944140d0340140c1042010150380c0d40900f401601c407a42604910461100b0214851000c03404243c90421580c00c2a014907003801946803200c1c8001481c145c0ca0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 521375521 1250 521374271 521374279
    0x1c0f020a080601270207082109122a070602060420090a0c0504080307031d09040f030c0507050d03020a0606080712031b1704031a0606070f030c080a090e01080109080306 74
    0x41340e880107210203805915005001d00000123216060180c1e0940c24205480800710132010507914484040d480308800781940300e10880070445200842054400280071400706010300c1d24100309441030614100345600a0400b581c4040148814803441c030040c900a502010326140d100d24400c0040380c0010030180c6801c80107034a031415074202900030011759001d0310090301100e031180000d041c01001443e80300d01c0300500c00c0c20f01d0740b030705510f040c00b065403881580c1141c200505101a664210b4003112011425101c0380108240420706030340d00c0171801c43c5140264000d0103600300d607003841403c803821a0f1200c1055409204100800c240d41c0d04021015030305414600c0c15240c5903089940b10782c0f07810100400d0500030044504020103100c01130401d590146c48000946a008621042000b20640302035a100f10140182d40010744200c0d42c2c0b40f15203100e80f5003041400095602c1040903000402c0d444017080080324144103034602c400c2c01c1801001440024030441c40151103202c50351001078580c03030107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 521376771 1250 521375521 521375579
    0x717060d030c0f08031f1403060609040816080307261902220303020d0e1c0305070213050a180c060e01091706010f060c050601090b1c0f020a080601 65
    0x1032141020990400342c4d0481340c02c66030380ca00600790441140119140c00140030407003802080c0c1840d01c2444407408840a0010403154036403001304030400900410444002c0c504200301300b6107181d0300035a56503140c460f00701c80c0e031a410400c0d0003404d261403003403000301c103048880740000a10301a000303c9a006689145803c14031050164180c001c0e101d1404610300c041c00001540501915a201507001ca90080d800c2d541000b500e403070708640c4c0b00089805503521150044201403040d0382c4030300c126021071081c1801803810103681c0c0418044e20255a24a80305503403901007204060050080004440b00b81003c50318a203030350782d210120003606018810410002352200c1c481a4001c16000d406030560182d000044415002e03807583d50711007405806d0480c80c1c811130019200c0e001d119a4041e041d070180107049076a007400041e40051815031061035001e1520405482a6800f80c1840a0707003d0141d03a00d140c0442640c010700800d045181d2114a69601820041141050594401400303008200c01c03209 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 521378021 1250 521376771 521376773
    0x3080a0f0605040e0604170a0221090d06060e0a020901021e010b060d1a0a0b0a180b0409060f08060702032506020c01050604060b2b060e09060717060d030c 68
    0x401c030326085550001d02d045810900b0400004015201e98886c140300907160009030b061012034002c0d16602d8002d40d01041c0d601441e4811498407a43c0086091a084e081005080004489803e00402920740d1a51030006214113011144401d9000c40e02071410361030060041c000035640c94040c1d0240e007a40b011210010388001d000c1d00411105030008040c0750321018441c0400000f0b11200301e4a291a02c443c407080c4107141030003551402200c1c0e0544485007000346151054030a07c0402241c0c095410882101080718603e00c0c01800c050101554005052818001c1811308406150800312103940a181088500380c5d0020450b5605c0c040e141c9000c0d00f0241200c04030b0500218100c0040c20320307002151449402c0070540c001442006c08072814421540e44405e200070030702c201000c0d00083c0b0500180c2c3c6032030003007204104070f0740804517030001012a61403c001200c1c4200b80e0381d5481076003090051024059000030b071702c44008240c47c2046145d003002800601001d040403402000e0156482c9010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 521379271 1250 521378021 521378051
    0xa0806040207050d081602060f0402060a030e06130203070e0f040f11030d0f0f080903030a0b0d05190c091b0c03030b0d05011d070305070e090f03040902030703050f0403080a 76
    0x19982c0c503844000c9038000c03c600c00024080d0401110315041c0b2840c00c0c02245841c07840054918040c0080b21481d0b241600e498081c810a54040010142410f84403031202c8030744501048a24440c95007151542d941d040140b0416041c4112a840b0303d01c129242400d1014106131500d04170f400a0344903a02c0400b000242c60703c0c030031035a048400700d0b0b403601030300e801c508801c0e030044011030300840e00b55240114220180c10035602203100b5116445598018000255041e9555100c43d0110318000d1144003d4541c0d81e55091900c1301c50480c091b010000206950304021407040840c01a2000e02d0b020b1100e400400319027007103000e05807040300800c4010003a100516000c0c3e80b0442210801501c2c3d01021001420200c5c0038004a00020128804460510b0844500450100280c0364031402922415140c03102c012118a4050001e035440d004201300b03200d50f820100024801824940c50250b00e0b0710701030324060120307403006080c00c904007040d804000c00a03903c003280c43d5100f180c4020004801080152203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 521380521 1250 521379271 521379277
    0x2070203100204030b010509070c21020c0310090309050102030f190e040203041101021e031e27090a1404030804030e0a0e0402040e07030308133f0e060a08060402 71
    0x1d80003910005001c001e101d204404103068450a81d528101511a0f040441d03000c0c880345000740042e881c0c000942c5296200038481120488076104580d108d07580f000c0001d08040742080d0344c85d5a20350341c983c00000c054214100c076008000c02d0010b5401c006030140300d240548218905008081c92500031106041d008440300030303080002800454581c50300d894000c030544d240030102070151040300784501d0440c09a407921841288180007540c101440460105020260307070b41c040044103020311190040503217141070300c1004401882295110400c0c43d06008102c1001303410b85040300e0500328929000c00c5e081001da9001640341ca01000659200d0a00300d5003280d240034101e5200020040c0080c0803141c0d400300c00e001da0b000702c600b01700c2209441d9440b035031a05c04d07100080104080d00d000030001e6408016841031039001e415000300000d100411003524004a81010282d00018032000000012240a803801050b6500300000310300113800000b4070502410342880708000306040001c80584950b019 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 521381771 1250 521380521 521380543
    0xc03083304230f25260709091806020c07091803053705041409011514070f0c080d090f0b0a0c080a050406080a050c0f03090115060504051302120a02070203 68
    0x30b13502e810710754501c010695038140800c41070703c400004207812040404112240156165124110540d02e050341c550301134008810035020200c0340b0031404011a40900007003152807105e17005002503e0401006004489001800d40e1a44405010160020750070a00300c4440608503145681d0851140c0d00290082c040c0f1a035440f50507000803102d54a041e0844003400075260300754455100c0507941c0302441981c45091003101c04c10704486200d078a459020b200180c1c0c58580c142c1c42a07241a8481d180c10111381d28420007124103d4500c80200202101484403e2103100e003881c0400c005840e002d0720074003102d203034006d08610220002e0441c0a540c00341c503c101501749e00c0b070301280d20760541490140c01d541007071244402182d00310300040c1c0740300c40c2403146612030540e005009040a00220a461164000070440b042c659601c00740701d07030624140b0f5880c0000303001c9613490031b58aa00348810702108144604228103214014811940b0031034601c0c0c01c0d1507000318074030001a00c60410b400024502181c00803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 521383021 1250 521381771 521381821
    0x1002070b0307050d1e1d0a120305090a060213060e0301021602040b060705070306060906080d1205070507050f0d020d11070b0c01060b0d0c09050109060c03083304230f 73
    0x4050889402c0380c518086c1d06240c012030114001d26982c3c9503001c0400041060003540002d1001501070762045800480501c21168019010750f184002c907401040f010300c9414000c0010048103a026484210241040e40294245500121b2407021840c04180c003d200b90740302c050084481d281c8205840145400004803042595242032210040c9511f0041c0010103081940224080900143c40b045400482e603c195030340841c0300030301004003030103040c0304108001080340d40045007040007001c1094100b0009001482d10314403000e803030a440c907e029001c0c084223044001c2502c90105501e0211240b100c1c0c142c0e0350305280b500250040c10785400c291813084003c50030991603030103548829040c3e00d036a114034a030036072038500646007080a4030404002425106426001174800c01169403c011080040044a07403800200c0b10081849036002c8000440041c90310304510b42070060014500341030f20042c3c0300199050403003000020092407110290702d03003408229040d08040c606482c0c580212 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 521384271 1250 521383021 521383061
    0x50d2301090605150603091c090308070821150607110a061106060102060c0316032901140c1903020a051c02060907140d03020703021305061002070b0307050d 69
    0x22078540b004082c2940e003021041011496a1403174141103045074020b00405000700b406042d80079581a240c04258016400c000807207038008005804800941403281c818000309486007203c02e440e044150142030090941c01c000c00900c0341c00311516409206410040d107100d41c0d00c040380e040c01c211a00d41030300025000301103400c0004506034001707261405c80140000f41c60b0700341c81d40d00049995080c284e50910300301804001044603040c4800c1c11000c201c501d801c01003110802194690141c1b080440e42c0c032155151148800d000c0d42e800026202d104c1c1c41801c11900f00320090b490b00e55101d080d24001c401030990818103c040c1030081104861a45c0e00c0b000300c0d2098401d0ba1001440f094400f1241400b510854005c60b00c0118041213880030b940c0c1d61064450b0394038a1034100520035000040075821b50150280100c0542c0301d41c11030088500c0c0c04180401d90341400000d04c000040f400c00c8440c03c6403c6281c0078000d40840c2e00460350080820b107807031a200d00c4403403030040003803014840c40360303453b28a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 521385521 1250 521384271 521384273
    0x3110310080613031205040f0204110408010e1501030f080403050102040603020702010e03030a0c02060307110f01021801050412030e1c0f0c0602011e020d1803020c19050d230109 78
    0x403064400907161000c041d1042c07a11045402900c0405120300100443c1494a03010070b10501640125405801040d100503107841940100b41140d81d40c151000e045100081e0074402e0790000d020302440d03a00c0040040c45524022400501050b5041c00000c1c4901d2301d4002d10783c240030004080d2070246401000071583e5aa40b00c0c4054000d60000c60100d010607010000b003409441e012084c0c4004803ca6110651640d5881e0308010465100611800501c254079040f82e400071801c0085030b01e0000080c0c00181e441c1011306401000c0080080c40c1410000100024085004903c0c5401c03401c13030341810071040f60b41e200c0700052942885103040500e01d5465039095002c2c002044a0907a81c18083d00d02000442c0e00c941040382640c2d5071110000030400d00c1c1c0e0380075269000503130050203181000313000011464076840c3c907000701d548000e009900590107d4541710b040e1400c0007002d180f05100b00b16003118189044042141c5248140d009801018060301200c40f0400355005811407641641c005c001c41d61503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 521386771 1250 521385521 521385541
    0x602210919030b06011103181201060906030b010905091e0304050d060b1306050a1806030b1801060906150309030201061517090102030f0f0a1b080108161a0a031103 72
    0x10030302c0709440c4200c020300071a016500a4901d05c0303100414901441c9410301c03001c505818141403020300d54110785000c642464034102849190b0161901c89404240c651960405802001040c0c100c00c0c0c10b0b80c0b909080c403860b140c00082010704a07075070380b5800c943d24120b007103890306501459010a4001007400e045904100584d800881013405c102c03210381d40c044511902c5c2c4101c0f10f980c001d003504903a00880611070000c2d90084003000111580f400301d2403070307201d40e0750004040055404e00034459040320401030740c58080c01079401406803004100311080c81d0084010a078209030b51100141a500d4002d0000c1c036100b034001001600c8605441c00b00210505002022882001e20114070201d210012458054060003205c0c022101d0b1820303c145078403941401c0747ca0540180c90b001589540300a400701100c0030415105105000f82c6580207651315000c0341d6401d004040ca0410700c10046c1c43d00900072088005180c81303541d00180030850315a040703524190700400c48010302c615034000c0482004100c2a07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 521388021 1250 521386771 521386819
    0x40b1807150809120a0315050d030c12050a020607080601120501062105160e030f0f0a0b01050f0102100c090f1401020d08070503061003091b03120906022109 69
    0x4115603444441c0e40e9100300c0d143d2904c100310f0541d241d00740c042008650b824402e80180003101d0303a450a040c032070780e07a1780f000841002d041001100802d5a401080c000d200c070301245068015081e0030000e14141182c2c0c0c00030340f10307031002301100c00f031241d41c50204090340d00c1401501c15000b4002000c02c0296103a0901030070b0f2410b8082002940c44074102c04a031800702a01a81c0d01802801d180d01d01c0020301220140d8200c0c440240450301441105c071620070140c3c041001c0c101410100020305400029820f0241000300160003850042036032030011180380c0d9000400501e48403203c00f001420081c810811540d14070143d010b23107036005040002140e1b000500903c610300440903000c4503101c1084d0082075a00300d82c111034602c04102d040c8002410b03801c00315281c804d01032040c40c0c0050901c42d02d50700d001140150354540c480c803c94252040c400c200d41d01d68909003017485424190202d5107810300c002d64480940c501c900da1111301070894007a680d41201030702c0410200420805500e001c004003003e00384 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 521389271 1250 521388021 521388059
    0xd171603050c07022e2f0c060703030504170903060601030507020c0411040503150c0d0b011b0b060301060506030114060c0c0a0803030f0f04030f050306030a0605010b0a0206060414040b1807 83
    0x19101c418590080c0100000c1c4078248080d41c1e03056840c0c01c210001204240030f1b40c00e074100c074007a2800b0350449540b217500805010340320303480c0000c1e10b00700303400e103022481204171070000040340030040d9043da50380020395650b001109103004036059803094012410181503440080e001400c01c00d40c0c908035104c001c0640183c0303a003a02281d01c02d21384c0b41031040f0b6808090324044840380d030030807404034000120340003030f810000b040c1003000c4509184107031200c1030ba03081002640c4c0e0603005014480c4514080c064000103042c201d92040c00d6506010b4a040d9038128240224400c040015200c0c0e0024001c4c40000c07515400185544060342d5100c00d99500d962046482115021511000804055039900d48a01440d0543d0ba0103440140310107059841e6400604241e9140c442c05800d00c00245150040e24081c145080801d500c2c2d5042e400080d01e085405810342e846035003858088a0500c80e2000d04a503c0b03500700811010701d0712401d07158040c4400c2110b6681440c05000008030b000c90314041481c0e0f6078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 521390521 1250 521389271 521389339
    0x10513090c290406080403140705061501030b03010b030c01030f0608030f0a020f19030c051903020106090b011b020904020a17010614060c1015170d171603050c0702 72
    0x1c2c0c9914804034402d900461001c107084c01c1c042408240b086419490524000c41035515150300da4554503d498003c4500002d030140e9001c0725001960b05000d800e030850400d40091100014490000f51148102001c640c105130340c0700e507a107181c449207070000b500a2802c103040e40c1c0d4400500b55100b0075603205040850141c0310305501c4010307a00c0300082810101c0d0301d964000603214000c2c0c0e401c0300e210000c01e40988952086040200402000d0000301400922130f40000440e545072142200907900e0400e0400d0511020520032180b042c180200802d06540c110ad5000c1960707a140700154400010381c101d2180b840040920312402c00b815403084040e145c04840c03c44c0c00d44042c104104141c410028018000d401503007400080c41d40b10b41014000391461903420100b55181e20400702a050b402c29000606d50000341d11400e00d903044540d00208a9100b000c015280c43e2400069802d030782d00426000401d0740d160000303000b0440f114243c81c5200cad8020046c920020912828103004501c502244c010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 521391771 1250 521390521 521390579
    0x90a120c120b040303180b10150e0a030206071e06140606041401120b0312030f01090504020114030603010b0a08011e05070909180507170c0612010513090c 68
    0x54111441440c2596a000080d011543d603155070840103000d111103003a021001009a00b0002070800c001d003440360100541c00e8150300d01d020812112802d01000e0300091120f2044044400e0701c07900000f50960b6010744805a5605180c94000d040700000000300961494410051041180700c5d0440002c440703080c00d406849489050412107107100b540b058a0350b00c0d03a2480c4e010302e294010420040080c454000000e00100c1000c0400d0604000f00c2c02c0d200b044030004200319264120403011405801c002204010501d46540081d266030544d4554554082c0302000107440c0c1e650940014482e02005024192516510221680a403052481c0b84042610004080d03a03154001e00c03441c0d01c605003d1380d5034181c6901c0c1031a649c004000c110385082c089420490b041d4041401000810000d185000e201e03214480e5100009040031903003041140b00d10010002e4484c08411090194151a41183e42c210410310038001c420051000200003002940201030019407000b1201c41e42400c3c2002c2d000c1a50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 521393021 1250 521391771 521391779
    0x32006010e0a0f0c050a081003051e011b021e03040803040b0c0c0f0108060d02011202070323090904080306190902030108010f0207080a0e011b061e020703080705090402090a120c 78
    0x106541349190b100d00000c200b400301c3c07018244250b08035600444111600a180398481d2600760420500c0c5c0714040348401c0403a11030800030700034030030002410200f00c05104260180c44c03000303482c0c4a4080c90b00c11a0043c24588009400040c07040b203005004003000c032070390740c4e549001080560704158440440d0380a00c002d6140541841e00042c0d0300d4190503581c0300403603990602000740c2e0b4040420103070704000640d94010917514480c0b000f0030b15540207448143ca01c40c8185017450441e0321008915858200c24010462140c40348030700715411541c0682c52541b43d50b0382d8004568002c00c0301844402c09403540303800050211440d0f00841c182e8000f00000d0001c0310b5600d4004099101d81000180003030410000d294017113104200f1600720450500d40003080c1d610401343c03504680070105080e03800c103503558000004400250050410403001c10710030760500c101600e01420003400100100240301e0002070400096a0b150304950203850000e20303968015032120030700001c42c060100116255052104045 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 521394271 1250 521393021 521393051
    0x92a03020414062101090c0b07110312030a050402180a0906060504110910050702151201050f010e100917060916210309050616030f110a032006010e0a 66
    0x183c0b1072078002d0180c100580313511103044100c8100710070102c01556540c05102c00948a091504014a4090030040c0c803102d05061403194181501103003442a0710040000d8805003401c410360758420401e410014881c0c0d51800440c9440041100301c81c003043c0710b0000c00802c41459030007404200c1c0140010000303240c803070040c8412640c0c4503014611120041c03103250700d0391a0003d2140d0b1030191038a4541d041419960100b001ca171541d4036019003840d00451140003034404450007500420381110031640b56900c032400601031040c4c80c00a00d003d107110200c40c400490240e62150f00600400760703020140c0c003070082041d0b2604010783d0381071141d0140054f230303003198507801c8030f40426101c44030110b07001c08038003288a00e04c1c0c0400c05012030500514000025140da82d240240450001c3e1050b203520b441103038680148015111443c202c14003584010100e5480e200064440040b6070504003215020801182ca100390049410350b4281e40c407940c0b0002c20003a00943c1000c0c010b8071901e0702070106414042d104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 521395521 1250 521394271 521394311
    0x40e040b09011d0304030204091505010312082a0306011e05070506090c101b050106121e1e060e010e07290909060f09010603270c09092a030204 63
    0x4212130f8400c0c407082c4094030b0320340d0004030a2840703000902c55500071101000e055842c241d100380c810603080c0300d52001003904071242c0303688420840091124142c52401d81003109035110b481504940000c00014a00e0f4041c020340e40030740244408032401d0030b00050008001c0e03130150310110389a0044102007054100005003813150154001c04240c601c1134440000c84804001c1c002c0819980d84022100001c55000e1013280082c2045907010003c1e00c01909200341460032003103655100000b070320b403000d02203000141c1190802a20200c0c10414a1003401d2901c0074004c950341601c02540707008080004480002681c0e81100c0c004026480150b40c001804810b8000d40a14036170444402c00001c3d01c1031071301408155002c2d10080c0061002004a804105007800903001b04010079a07a5140407401c41d0b14031803a80703052449020420501742207a80c1c200c440f00f454800d0080c8141c80d091070b00100076240c42c0075444100b40100c050940e091032100c1c4521084280300590140f032415100d4465988281c2407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 521396771 1250 521395521 521395571
    0xb030105030312130f20030604150e0102130f0e060d050c040c090b0d0c1103070510091109091b09070f0c0c090c051804150605030c040e040b0901 64
    0x2d9418914040241c900c0400f0003404140403907200d80d18540016080d41c5180c1100e030094520585602040186071411200031072428460341c4040208030000b1840369a01c1507441c0e076414042801c2241451042c064017030780446106140c07800320f0102d21025614840d00c100d5000d07140f03a03541c0380c81d0002804485224111b0242058000304400d64050030650481c048581d610b2602c041c1c02543c1c1d41080d616a00002a21120117480e4404500309a0744450080414200d50f8003651500d0616a00c01e66620142180c4122080d284c020304824031440300e4800801c000b000e031080e1036034603200f00000d80b107014240210150b2560381040c4a914203001070b00e10722658140c0c46807040c034060f96400791031503540d50908980d08045581c0c0464040b031640a00c1c40301d1801d50311600d8949072220f036504c14903100c0a4480307009510301240700d140b43d400240c00070b00700c4006040041d52512000035910b00c511640d00b010030018007203030500c001c001040b4821481419444000c000c501c803400e0700301c5407241c14214 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 521398021 1250 521396771 521396773
    0x10501030b0d0803061c030201020703020f06070f080a1d1c080112110f120a26190207090212070314150f04021608091305010e04080d0e120904060b03010503 69
    0x3660000710704000845d000b0710020108080500300480864500400c450308400607500400d0400c02c15070104003a003102c04002d4060300032460031540c0106009041800e404c10009810701003020340c40c6680c400340c2d5000c48a0211042c16400c0d901941c0e40d5205100f00c18100c0b00315089a90700d09208800a0b0b05850031901d1030800408a500c45030180c10081300b525520026504152010b50380344000480300c440312501400025455080070f5941d0040000180d822600203a0b43c190300a00b000112800c0700c1159607617070a05040308608a2522075107401a50f101d501c00244c402d940059084094841c0011355018045013400010401c80c902098503003008261950302008110f14256607000c042c0303500980700504007183c003032540302d103134061940c141c44070b0100040b10b82d09400c00079110240746581810902140d40b40068030420480001d0001c1e01500020030440b5008041750080c2c0f090348030031400c40345004694200301840380d110b44448c6106c1ea1800100250500864050b07034101c600085c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 521399271 1250 521398021 521398039
    0x6160527180103140d08040b0a2003070306240804020f041401090b03060601090e0402010e0607080a020106051f080417040815090d110c2421010501030b 67
    0xc00c100d825400000280d1000d14101008903855849041e5402940035204d03110000d0840d004060422485504540400c5041741c1080045150f501d00780b0707004200e0f001c00142588000903040120201d054540c022540000240075440d90705800c00d20aa07006078050303041420100d1002c890714640d000920340424200b80008000d450700803001801400d0240000c904080400d0303102440000980141ca60a035440b20080f00b6070034100800c0f5440003013030800300c101500b4062404404040104000d0421140303400d0f10641e622030388140c51940f0380c8403241c1034a48400d400080d01900030b5000e100e020301800c02d40010802030b0582c0400e00d200c0035440d451401e88603500ca114400b0450014560181400c000028000c2801c0110b00c0c40d0310f4010b4501c803203500f0712603801e034207180d0340d40080d00810689188280350345801180000c1d60b41001c4420310307041e04904c80c0314403c1106103c038110500070081000c0040401d140710b01200a4141c4030780b44505c6c1c1c1c8800065003141c070100d4856400031628 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 521400521 1250 521399271 521399317
    0x110319030905182a04080307060f0501090b130b03120a030506011211040915030803070f0908010204060e0d02030f060c120c0c0a020d11040f0b1815131508061605 71
    0x1900200d20001c0c4d55022442c01e40c4862036145160300900301100e00795501e01c10200f03000407500c9200d001d4103070041c0a10440703840400140008a58000108510382d94501d241c40c503541c104940d0740c040d51036050702c50311440b10900c05401041d084038034901007550441c4026003980d6900c280d00c070820010940d1410b02c4c0c1040c590b84005c2900d003484000c01c004080340800411440c0024521851407591100d056585c4c170703100107000c40d00340e03402074009a00611040c03101c0d40d0071500101e952041030f118098110f500d0f0001a10302060111201b440380034040074070812118440c01415041003c40c0d80d0303400c0b502e400003101840e2041000031810307900280b9917640103180c90100c0c0c4812600070011005005400000a012035005624080c0001c0d9502040340550038000714a400c440702502c1140240d140010494030302501d0480c0c507921510320301c849025028083e901c4444080e201461140c480c0392144060f41d51440243c0d80f0100e010f0125850001042c800c2d811030310000902d0b503041a0035043c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 521401771 1250 521400521 521400571
    0x80301170c0301050c03160309170f090a080d141306050f040911030a0605091303050c1504060207060b0913020409060e010f0c0f05041211031903090518 67
    0x50341080c1c0105a101d001c030707550902a40c0d0055080c4103040e607807400c3c80902c2c0d60807040e04544503000c2c1401c02d0b05034000320b0782100b40703031100c04c690f0040c1660300d15103490305264030f02c514240150704c142c0f840408580d200c030000746540404190345030310080d400b41841c01503681c0100030007800c0c914031240080c00050310810250881c80c085000391810241c9490300b900c2074034001078148000305030200401112245074058000100419503c811450400c0c40c0c5100c000486414080c0c18050001a0401748000c10402500810070b914108402c3d424185090400381d40456001e4406134104082c407912481c11041c818020800c200c031038000398140358288005800d04600941d0850b96a02035078001071020701404902d1401c0800004400d007241c10080e120784030300c00380c0d40108001071205020030101128051006034201080b0001040c1703a400003840c11a51010000000e4403c140c1d0508064122228000303440e01140c901c03c2e094046040400c00341070407280452803079000b07a0300c3c40c1040e903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 521402877 1106 521401771 521401799
    0x50115060503070f031d0a030314060604050306040b0a02090411031009020406140c1213150813020405070207050604060c0b01050d08070206030c040e0406020d0c0c080301 75
    0x82c040d0300181480c800404c100145a0b5486141885032407181312039404181c0e882c1140d05030561460001d028040c8103a84070f050201850104030a4600b64050750709a030000341c010665035555071180d00418001400302020282d0070070601d1402c0c0c446000e0420100c0f80d00040c540d403420030341d4510044010503840070303d4451060201380140741c1d000700c131010010100c1c00f801e0f03291028468440d00f4480080e01c0001040400918014540074800b4034204459141f0a04000c10100f000c0545e42844200c2d164102000030081240062820381d005039084a032910403603213141e49610110320107520a820081c00308281c03c2001e005c02074450f15040c09404280c030800100b4500f030361420000d00448100034400c0c0400720014a40801d51070517240103042e626200000d84c2400e0620070000d501c6908084141408c0c1120464480d00031350344c1c8249554407402e0649542c1c03030704030240c2d0644 = true := by decide +kernel

theorem cover : BRFrame.Cov 521223021 521402877 := by
  have h0 := BRFrame.cov_init 521223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 521223021 ≤ n) (h2 : n < 521402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
